import Lax3Proofs.SolveConcreteAlloc

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
variable {L : ℕ}

def concreteLp (S : Setup L) (_ : ℕ) := S.depth
def concreteHb (S : Setup L) (_ : ℕ) := 2 * S.R + 1
noncomputable def concretePrep (S : Setup L) : ℕ → Com :=
  prepCleanCom S (concreteLp S) (concreteHb S) concreteCo concreteCm
noncomputable def concreteRead (S : Setup L) (j : ℕ) : Com :=
  readSegCom (concreteCa j) (concreteCo j) (concreteCm j) "rd.p" "rd.m" "rd.d" "rd.s" S j

def concreteCoverBases : List String := ["cc.a", "cc.o", "cc.m"]
def concreteReadBases : List String := ["rd.p", "rd.m", "rd.d", "rd.s"]

theorem concrete_cover_arena (b : String) (hb : b ∈ concreteCoverBases) (j i : ℕ) :
    lv b j ∉ levelArrays i := by
  have hh : ∀ b ∈ concreteCoverBases, b.length = 4 ∧ b ∉ arenaBases := by decide
  rw [levelArrays_eq_map]
  exact lv_notMem_map (hh b hb).1 (by decide) (hh b hb).2 j i

theorem concrete_cover_prep (b : String) (hb : b ∈ concreteCoverBases) (j : ℕ) :
    lv b j ∉ prepArrays := by
  have hh : ∀ b ∈ concreteCoverBases, b.length = 4 ∧ b ∉ prepArrays := by decide
  exact lv_not_mem (hh b hb).2 (by rw [(hh b hb).1]; decide) j

theorem concrete_cover_q (b : String) (hb : b ∈ concreteCoverBases)
    (a : String) (ha : a ∈ (["cq.d", "cq.v", "cq.u"] : List String)) (j i : ℕ) :
    lv b j ≠ lv a i := by
  have hh : ∀ b ∈ concreteCoverBases, ∀ a ∈ (["cq.d", "cq.v", "cq.u"] : List String),
    b.length = a.length ∧ b ≠ a := by decide
  exact lv_ne_of_base_ne (hh b hb a ha).1 (hh b hb a ha).2 j i

theorem concrete_read_arena (b : String) (hb : b ∈ concreteReadBases) (j : ℕ) :
    b ∉ levelArrays j := by
  have hh : ∀ b ∈ concreteReadBases, b.length = 4 ∧ b ∉ arenaBases := by decide
  rw [levelArrays_eq_map]
  exact lv_notMem_map (hh b hb).1 (by decide) (hh b hb).2 0 j

theorem concrete_read_cover (b : String) (hb : b ∈ concreteReadBases) (j : ℕ) :
    b ≠ concreteCa j ∧ b ≠ concreteCo j ∧ b ≠ concreteCm j := by
  have hh : ∀ b ∈ concreteReadBases, ∀ a ∈ concreteCoverBases,
    b.length = a.length ∧ b ≠ a := by decide
  refine ⟨?_, ?_, ?_⟩
  · exact lv_ne_of_base_ne (hh b hb "cc.a" (by decide)).1 (hh b hb "cc.a" (by decide)).2 0 j
  · exact lv_ne_of_base_ne (hh b hb "cc.o" (by decide)).1 (hh b hb "cc.o" (by decide)).2 0 j
  · exact lv_ne_of_base_ne (hh b hb "cc.m" (by decide)).1 (hh b hb "cc.m" (by decide)).2 0 j

theorem concrete_cover_tab (j : ℕ) :
    concreteCa j ≠ (arenaNames j).tab ∧ concreteCo j ≠ (arenaNames j).tab ∧
      concreteCm j ≠ (arenaNames j).tab := by
  exact ⟨lv_ne_of_base_ne (s := "cc.a") (t := "sa.b") rfl (by decide) j j,
    lv_ne_of_base_ne (s := "cc.o") (t := "sa.b") rfl (by decide) j j,
    lv_ne_of_base_ne (s := "cc.m") (t := "sa.b") rfl (by decide) j j⟩

theorem concreteRead_rank (S : Setup L) (j : ℕ) : "cp.r" ∉ (concreteRead S j).warrs := by
  intro h
  have hh := warrs_readSegCom (caj := concreteCa j) (coj := concreteCo j)
    (cmj := concreteCm j) (pa := "rd.p") (ma := "rd.m") (da := "rd.d")
    (tsb := "rd.s") (S := S) (j := j) "cp.r" h
  rcases hh with h | h | h | h | h
  all_goals try contradiction
  exact lv_ne_of_base_ne (s := "cp.r") (t := "sa.b") rfl (by decide) 0 j h

end Lax3Proofs.Prog
