import Lax3Proofs.SolveConcreteStages

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
variable {L : ℕ}

def concreteParentSBases : List String := ["sl.u", "sv.n", "sv.m"]
def concreteParentABases : List String := concreteCoverBases ++ arenaBases

theorem concreteParentS_eq (j : ℕ) :
    ctrName j :: levelScalars j = concreteParentSBases.map (lv · j) := rfl

theorem concreteParentA_eq (j : ℕ) :
    concreteCa j :: concreteCo j :: concreteCm j :: levelArrays j =
      concreteParentABases.map (lv · j) := rfl

/-- The cover's external syntax interface: its actual writes preserve earlier
levels, and it produces no output before the final verdict. -/
structure ConcreteCoverSyntax (covC : ℕ → Com) : Prop where
  vars : ∀ j i, j < i → ∀ y ∈ ctrName j :: levelScalars j, y ∉ (covC i).wvars
  arrays : ∀ j i, j < i →
    ∀ a ∈ concreteCa j :: concreteCo j :: concreteCm j :: levelArrays j, a ∉ (covC i).warrs
  noWrite : ∀ j, (covC j).NoWrite

/-- Finite ownership pools obtained from the actual command syntax. -/
noncomputable def concreteLS (S : Setup L) (covC : ℕ → Com) (j : ℕ) : List String :=
  btScalars ++ [ctrName j] ++ (concretePrep S j).wvars ++
    (concreteRead S j).wvars ++ (covC j).wvars

noncomputable def concreteLA (S : Setup L) (covC : ℕ → Com) (j : ℕ) : List String :=
  [botNa j, botFa j, botEa j, botXa j, (arenaNames j).tab] ++
    (concretePrep S j).warrs ++ (concreteRead S j).warrs ++ (covC j).warrs

private theorem concrete_scalar_scratch (b : String) (hb : b ∈ concreteParentSBases) (j : ℕ) :
    lv b j ∉ btScalars ++ prepScalars ++ rbScalars := by
  have h : ∀ b ∈ concreteParentSBases, b.length = 4 ∧
      b ∉ btScalars ++ prepScalars ++ rbScalars := by decide
  apply lv_not_mem (h b hb).2
  rw [(h b hb).1]
  decide

private theorem concrete_array_scratch (b : String) (hb : b ∈ concreteParentABases) (j : ℕ) :
    lv b j ∉ prepArrays ++ concreteReadBases := by
  have h : ∀ b ∈ concreteParentABases, b.length = 4 ∧ b ∉ prepArrays ++ concreteReadBases := by decide
  apply lv_not_mem (h b hb).2
  rw [(h b hb).1]
  decide

private theorem concrete_parentS_prep (S : Setup L) (j i : ℕ) (hji : j < i)
    (y : String) (hy : y ∈ ctrName j :: levelScalars j) : y ∉ (concretePrep S i).wvars := by
  rw [concreteParentS_eq] at hy
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
  have h4 : b.length = 4 := (show ∀ b ∈ concreteParentSBases, b.length = 4 by decide) b hb
  intro h
  have hh := wvars_prepCleanCom (S := S) (ℓp := concreteLp S) (hbf := concreteHb S)
    (co := concreteCo) (cm := concreteCm) (j := i) _ h
  rcases hh with hh | hh | hh
  · exact concrete_scalar_scratch b hb j (by simp only [List.mem_append]; tauto)
  · exact lv_ne_of_level_ne (s := b) (t := "sv.n") (j := j) (k := i + 1) h4 (by omega) hh
  · exact lv_ne_of_level_ne (s := b) (t := "sv.m") (j := j) (k := i + 1) h4 (by omega) hh

private theorem concrete_parentA_prep (S : Setup L) (j i : ℕ) (hji : j < i)
    (a : String) (ha : a ∈ concreteCa j :: concreteCo j :: concreteCm j :: levelArrays j) :
    a ∉ (concretePrep S i).warrs := by
  rw [concreteParentA_eq] at ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  have h4 : b.length = 4 := (show ∀ b ∈ concreteParentABases, b.length = 4 by decide) b hb
  have hlev (c : String) (hc : c.length = 4) : lv b j ≠ lv c (i + 1) :=
    lv_ne_of_level_ne (by omega) (by omega)
  have hq (c : String) (hc : c ∈ (["cq.d", "cq.v", "cq.u"] : List String)) (k : ℕ) :
      lv b j ≠ lv c k := by
    have hh : ∀ b ∈ concreteParentABases, ∀ c ∈ (["cq.d", "cq.v", "cq.u"] : List String),
      b.length = c.length ∧ b ≠ c := by decide
    exact lv_ne_of_base_ne (hh b hb c hc).1 (hh b hb c hc).2 j k
  intro h
  have hh := warrs_prepCleanCom (S := S) (ℓp := concreteLp S) (hbf := concreteHb S)
    (co := concreteCo) (cm := concreteCm) (j := i) _ h
  rcases hh with hh | hh | hh | hh | hh | hh | ⟨k, hh⟩ | ⟨k, hh⟩ | ⟨k, hh⟩
  · exact concrete_array_scratch b hb j (by simp only [List.mem_append]; tauto)
  · exact hlev "sa.u" rfl hh
  · exact hlev "sa.h" rfl hh
  · exact hlev "sa.c" rfl hh
  · exact hlev "sa.o" rfl hh
  · exact hlev "sa.t" rfl hh
  · exact hq "cq.d" (by decide) k hh
  · exact hq "cq.v" (by decide) k hh
  · exact hq "cq.u" (by decide) k hh

theorem concrete_freshS (S : Setup L) (covC : ℕ → Com) (hc : ConcreteCoverSyntax covC)
    (j i : ℕ) (hji : j < i) (y : String) (hy : y ∈ ctrName j :: levelScalars j) :
    y ∉ concreteLS S covC i := by
  intro h
  simp only [concreteLS, List.mem_append, List.mem_singleton, or_assoc] at h
  rcases h with h | h | h | h | h
  · rw [concreteParentS_eq] at hy
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    exact concrete_scalar_scratch b hb j (by simp only [List.mem_append]; tauto)
  · rw [concreteParentS_eq] at hy
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    have h4 : b.length = 4 := (show ∀ b ∈ concreteParentSBases, b.length = 4 by decide) b hb
    exact lv_ne_of_level_ne (s := b) (t := "sl.u") (j := j) (k := i) h4 (by omega) h
  · exact concrete_parentS_prep S j i hji y hy h
  · rw [concreteParentS_eq] at hy
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    have hh := wvars_readSegCom (caj := concreteCa i) (coj := concreteCo i) (cmj := concreteCm i)
      (pa := "rd.p") (ma := "rd.m") (da := "rd.d") (tsb := "rd.s") (S := S) (j := i) _ h
    exact concrete_scalar_scratch b hb j (by simp only [List.mem_append]; tauto)
  · exact hc.vars j i hji y hy h

theorem concrete_freshA (S : Setup L) (covC : ℕ → Com) (hc : ConcreteCoverSyntax covC)
    (j i : ℕ) (hji : j < i) (a : String)
    (ha : a ∈ concreteCa j :: concreteCo j :: concreteCm j :: levelArrays j) :
    a ∉ concreteLA S covC i := by
  intro h
  simp only [concreteLA, List.mem_append, or_assoc] at h
  rcases h with h | h | h | h
  · rw [concreteParentA_eq] at ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have h4 : b.length = 4 := (show ∀ b ∈ concreteParentABases, b.length = 4 by decide) b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h
    · exact lv_ne_of_level_ne (s := b) (t := "sb.n") (j := j) (k := i) h4 (by omega) h
    · exact lv_ne_of_level_ne (s := b) (t := "sb.f") (j := j) (k := i) h4 (by omega) h
    · exact lv_ne_of_level_ne (s := b) (t := "sb.e") (j := j) (k := i) h4 (by omega) h
    · exact lv_ne_of_level_ne (s := b) (t := "sb.x") (j := j) (k := i) h4 (by omega) h
    · exact lv_ne_of_level_ne (s := b) (t := "sa.b") (j := j) (k := i) h4 (by omega) h
  · exact concrete_parentA_prep S j i hji a ha h
  · rw [concreteParentA_eq] at ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have h4 : b.length = 4 := (show ∀ b ∈ concreteParentABases, b.length = 4 by decide) b hb
    have hh := warrs_readSegCom (caj := concreteCa i) (coj := concreteCo i) (cmj := concreteCm i)
      (pa := "rd.p") (ma := "rd.m") (da := "rd.d") (tsb := "rd.s") (S := S) (j := i) _ h
    rcases hh with hh | hh | hh | hh | hh
    · exact concrete_array_scratch b hb j (by simp [concreteReadBases, hh])
    · exact concrete_array_scratch b hb j (by simp [concreteReadBases, hh])
    · exact concrete_array_scratch b hb j (by simp [concreteReadBases, hh])
    · exact concrete_array_scratch b hb j (by simp [concreteReadBases, hh])
    · exact lv_ne_of_level_ne (s := b) (t := "sa.b") (j := j) (k := i) h4 (by omega) hh
  · exact hc.arrays j i hji a ha h

theorem concrete_prep_owned (S : Setup L) (covC : ℕ → Com) (j : ℕ) :
    OwnedFrom (concreteLS S covC) (concreteLA S covC) j (concretePrep S j) := by
  constructor <;> intro a ha <;> refine ⟨j, le_rfl, ?_⟩
  · simp only [concreteLS, List.mem_append]; tauto
  · simp only [concreteLA, List.mem_append]; tauto

theorem concrete_read_owned (S : Setup L) (covC : ℕ → Com) (j : ℕ) :
    OwnedFrom (concreteLS S covC) (concreteLA S covC) j (concreteRead S j) := by
  constructor <;> intro a ha <;> refine ⟨j, le_rfl, ?_⟩
  · simp only [concreteLS, List.mem_append]; tauto
  · simp only [concreteLA, List.mem_append]; tauto

theorem concrete_cover_owned (S : Setup L) (covC : ℕ → Com) (j : ℕ) :
    OwnedFrom (concreteLS S covC) (concreteLA S covC) j (covC j) := by
  constructor <;> intro a ha <;> refine ⟨j, le_rfl, ?_⟩
  · simp only [concreteLS, List.mem_append]; tauto
  · simp only [concreteLA, List.mem_append]; tauto

end Lax3Proofs.Prog
