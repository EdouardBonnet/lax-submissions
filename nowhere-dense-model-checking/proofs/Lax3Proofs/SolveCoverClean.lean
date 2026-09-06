import Lax3Proofs.SolvePrepCleanState
import Lax3Proofs.SolveSweepAugBuildPeel
import Lax3Proofs.SolveSweepAugMachine
import Lax3Proofs.SolveMdCharge

/-!
# The clean cover computation

The augmentation core supplies its actual final deletable adjacency. A final
heap peel computes the order, the original arena graph is rebuilt with that
order, and the live-prefix sweep emits the exact centres and ascending rows.
Array contents are carried by `ArrWords` and the actual execution, separately
from the reservation lengths. The augmentation-round count and the sweep
radius are distinct parameters; the headline uses `3*S.R` and `S.R`.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax3Proofs.Driver Lax3Proofs.CoverRoutine

/-- Read explicit rows from the meaningful prefix of an arena's padded CSR. -/
theorem ArenaStW.agCsrRows {nm : ArenaNames} {Λ n₀ ℓp hb : ℕ}
    {A : Impl.MArena Λ n₀ ℓp} {σ : Env} (h : ArenaStW nm hb A σ)
    (hot : nm.tgt ≠ nm.off) :
    ∃ (rows : Fin A.N → List (Fin A.N)) (off : ℕ → ℕ),
      AgCsrRows nm.off nm.tgt (σ.vars nm.nS) rows off σ ∧
      (∀ v, (rows v).Nodup) ∧ ∀ u v, u ∈ rows v ↔ A.G.Adj v u := by
  obtain ⟨rows, off, hc, hnd, hadj⟩ := graphCsr_agCsrRows h.st.csr
  refine ⟨rows, off, ⟨hc.off_zero, hc.off_step, hc.off_last,
    h.fits _ _ arenaWs_off, h.fits _ _ (arenaWs_tgt hot), ?_, ?_⟩, hnd, hadj⟩
  · intro i hi
    have hv := hc.offsets i hi
    rwa [arrs_winA_some arenaWs_off, getD_take_of_lt (by omega)] at hv
  · intro v i hi
    have hv := hc.targets v i hi
    have hs : off v + i < σ.vars nm.nS := hc.row_slot_lt v hi
    rwa [arrs_winA_some (arenaWs_tgt hot), getD_take_of_lt hs] at hv

namespace CoverClean

def ca (j : ℕ) : String := lv "cc.a" j
def co (j : ℕ) : String := lv "cc.o" j
def cm (j : ℕ) : String := lv "cc.m" j
def ra (j : ℕ) : String := lv "cc.r" j

-- These names agree with the augmentation core's final adjacency output.
def ao : String := "@aug.adj.o"
def aj : String := "@aug.adj.t"
def dg : String := "@aug.adj.degree"
def mt : String := "@aug.adj.mate"
def od : String := "@aug.order"
def hp : String := "@cover.heap"

def arrays (j : ℕ) : List String := [ra j, cm j, ao, aj, dg, mt, od, hp] ++ plArrNames

/-- Reservations alone; no initial rank, heap, or queue contents are assumed. -/
def Alloc (N j : ℕ) (σ : Env) : Prop :=
  ∀ a ∈ arrays j, N * N + N + 1 ≤ (σ.arrs a).length

theorem Alloc.mono {N n j : ℕ} {σ : Env} (h : Alloc n j σ) (hN : N ≤ n) : Alloc N j σ := by
  intro a ha
  have := h a ha
  have := Nat.mul_le_mul hN hN
  omega

theorem Alloc.run {N j B K : ℕ} {σ τ : Env} {c : Com}
    (h : Alloc N j σ) (hr : Run B c σ τ K) : Alloc N j τ := by
  intro a ha
  rw [run_arrs_length_eq hr]
  exact h a ha

theorem Alloc.reserve {N j : ℕ} {σ : Env} (h : Alloc N j σ)
    (a : String) (ha : a ∈ arrays j) :
    N ≤ (σ.arrs a).length ∧ N + 1 ≤ (σ.arrs a).length ∧
      N * N ≤ (σ.arrs a).length ∧ N * N + N ≤ (σ.arrs a).length := by
  have := h a ha
  omega

theorem Alloc.peel {N j : ℕ} {σ : Env} (h : Alloc N j σ) :
    peelScr N (fun _ => cm j) 0 σ := by
  have hd := h.reserve plDd (by simp [arrays, plArrNames])
  have hr := h.reserve plRw (by simp [arrays, plArrNames])
  have he := h.reserve plRe (by simp [arrays, plArrNames])
  have hz := h.reserve plDz (by simp [arrays, plArrNames])
  have ho := h.reserve plIo (by simp [arrays, plArrNames])
  have hc := h.reserve plCu (by simp [arrays, plArrNames])
  have hv := h.reserve plIv (by simp [arrays, plArrNames])
  have hf := h.reserve plFl (by simp [arrays, plArrNames])
  have hm := h.reserve (cm j) (by simp [arrays])
  exact ⟨hd.1, hr.2.2.1, he.2.1, hz.1, ho.2.1, hc.1, hv.2.2.1, hf.1, hm.2.2.1⟩

def rankCom (j : ℕ) : Com :=
  mdPeelCom (arenaNames j).nN ao aj dg (ra j) hp
    "@cover.h.s" "@cover.h.t" "@cover.h.x" "@cover.h.y" "@cover.h.k"
    "@cover.h.d" "@cover.h.v" "@cover.h.z" "@cover.h.i" "@cover.h.r" "@cover.h.w"

def buildCom (j : ℕ) : Com :=
  bldCoreCom (arenaNames j).off (arenaNames j).tgt (ra j) ao aj dg mt od
    "@cover.b.i" "@cover.b.u" "@cover.b.w" (arenaNames j).nN (arenaNames j).nS

def sweepCom (R j : ℕ) : Com :=
  peelCom R (arenaNames j).nN (ca j) (co j) (cm j) (ra j) ao aj dg mt od

def tailCom (R j : ℕ) : Com := .seq (rankCom j) (.seq (buildCom j) (sweepCom R j))

noncomputable def tailK {N : ℕ} (G : SimpleGraph (Fin N)) (R r : ℕ) : ℕ :=
  KmdPeel N (nsOf (mdChain G R).toGraph) +
    (bldCoreK N (nsOf G) + peelK G (mdPerm (mdChain G R).toGraph) r)

/-- A fixed name with a different base prefix cannot equal a tagged name. -/
theorem lv_ne_fixed {s t : String} (j : ℕ)
    (h : t.toList.take s.length ≠ s.toList) : lv s j ≠ t := by
  intro he
  have ht := congrArg (fun a : String => a.toList.take s.length) he
  change (lv s j).toList.take s.length = t.toList.take s.length at ht
  rw [lv_toList] at ht
  have hl : (s.toList ++ List.replicate j 'z').take s.length = s.toList := by
    simpa only [String.length_toList] using
      (List.take_left : (s.toList ++ List.replicate j 'z').take s.toList.length = s.toList)
  rw [hl] at ht
  exact h ht.symm

theorem fixed_ne_lv {s t : String} (j : ℕ)
    (h : t.toList.take s.length ≠ s.toList) : t ≠ lv s j := Ne.symm (lv_ne_fixed j h)

private theorem rank_names (j : ℕ) :
    [(arenaNames j).nN, "@cover.h.s", "@cover.h.t", "@cover.h.x", "@cover.h.y", "@cover.h.k",
      "@cover.h.d", "@cover.h.v", "@cover.h.z", "@cover.h.i", "@cover.h.r", "@cover.h.w"].Nodup ∧
    [hp, ra j, dg, ao, aj].Nodup := by
  simp only [arenaNames, ra, hp, dg, ao, aj, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, not_or, not_false_eq_true, List.nodup_nil, and_true]
  repeat' apply And.intro
  all_goals first | exact lv_ne_fixed j (by decide) | exact fixed_ne_lv j (by decide) | decide

private theorem build_names (j : ℕ) :
    (arenaNames j).off ≠ (arenaNames j).tgt ∧
    ra j ≠ (arenaNames j).off ∧ ra j ≠ (arenaNames j).tgt ∧
    [ao, aj, dg, mt, od].Nodup ∧
    (∀ a ∈ [ao, aj, dg, mt, od],
      a ≠ (arenaNames j).off ∧ a ≠ (arenaNames j).tgt ∧ a ≠ ra j) ∧
    (∀ y ∈ ["@cover.b.i", "@cover.b.u", "@cover.b.w"],
      y ≠ (arenaNames j).nN ∧ y ≠ (arenaNames j).nS) := by
  refine ⟨?_, ?_, ?_, by decide, ?_, ?_⟩
  · exact lv_ne_of_base_ne (by decide) (by decide) j j
  · exact lv_ne_of_base_ne (by decide) (by decide) j j
  · exact lv_ne_of_base_ne (by decide) (by decide) j j
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨fixed_ne_lv j (by decide), fixed_ne_lv j (by decide), fixed_ne_lv j (by decide)⟩
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;>
      exact ⟨fixed_ne_lv j (by decide), fixed_ne_lv j (by decide)⟩

private theorem sweep_names (j : ℕ) :
    ([ca j, co j, cm j, ra j, ao, aj, dg, mt, od] ++ plArrNames).Nodup := by
  simp only [ca, co, cm, ra, ao, aj, dg, mt, od, plArrNames,
    plDd, plRw, plRe, plDz, plIo, plCu, plIv, plFl,
    List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, not_or, not_false_eq_true, List.nodup_nil, and_true]
  repeat' apply And.intro
  all_goals first
    | exact lv_ne_of_base_ne (by decide) (by decide) j j
    | exact lv_ne_fixed j (by decide)
    | decide

/-- The tail's finite array-write envelope, shared by every level. -/
def writeArrays (j : ℕ) : List String := ca j :: co j :: arrays j

/-- The actual scalar scratch pool of the heap, build, and BFS/regroup passes. -/
def writeVars : List String :=
  ["@cover.h.s", "@cover.h.t", "@cover.h.x", "@cover.h.y", "@cover.h.k",
   "@cover.h.d", "@cover.h.v", "@cover.h.z", "@cover.h.i", "@cover.h.r", "@cover.h.w",
   "@cover.b.i", "@cover.b.u", "@cover.b.w",
   "pl.a", "pl.b", "pl.d", "pl.g", "pl.h", "pl.i", "pl.j", "pl.k",
   "pl.m", "pl.n", "pl.p", "pl.s", "pl.t", "pl.u", "pl.w", "pl.y", "pl.z"]

private theorem rank_warrs (j : ℕ) : (rankCom j).warrs ⊆ writeArrays j := by
  intro a ha
  simp only [rankCom, mdPeelCom, initBody, roundCom, mpRowBody, chkCom, heapPushCom,
    heapPopCom, heapUpBody, heapDownBody, Com.warrs, writeArrays, arrays, plArrNames,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
  tauto

private theorem rank_wvars (j : ℕ) : (rankCom j).wvars ⊆ writeVars := by
  change (rankCom 0).wvars ⊆ writeVars
  decide

private theorem build_warrs (j : ℕ) : (buildCom j).warrs ⊆ writeArrays j := by
  intro a ha
  have hh := warrs_bldCoreCom _ _ _ _ _ _ _ _ _ _ _ _ _ ha
  simp only [writeArrays, arrays, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hh ⊢
  tauto

private theorem build_wvars (j : ℕ) : (buildCom j).wvars ⊆ writeVars := by
  intro a ha
  have hh := wvars_bldCoreCom _ _ _ _ _ _ _ _ _ _ _ _ _ ha
  simp only [writeVars, List.mem_cons, List.not_mem_nil, or_false] at hh ⊢
  tauto

private theorem sweep_warrs (R j : ℕ) : (sweepCom R j).warrs ⊆ writeArrays j := by
  intro a ha
  simp only [sweepCom, peelCom, peelInitB, peelSweepB, peelStepB, peelSeedB, peelPopB,
    peelExpandB, peelResetB, peelDelB, peelDelTurnB, peelP1B, peelP2B, peelP3B,
    peelP3bB, peelP4B, peelP5B, peelP6B, peelP7B, Com.warrs, writeArrays, arrays, plArrNames,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
  tauto

private theorem sweep_wvars (R j : ℕ) : (sweepCom R j).wvars ⊆ writeVars := by
  change (sweepCom 0 0).wvars ⊆ writeVars
  decide

theorem tail_warrs (R j : ℕ) : (tailCom R j).warrs ⊆ writeArrays j := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact rank_warrs j h
  · rcases List.mem_append.mp h with h | h
    · exact build_warrs j h
    · exact sweep_warrs R j h

theorem tail_wvars (R j : ℕ) : (tailCom R j).wvars ⊆ writeVars := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact rank_wvars j h
  · rcases List.mem_append.mp h with h | h
    · exact build_wvars j h
    · exact sweep_wvars R j h

set_option maxRecDepth 8192 in
/-- The cover tail uses neither input nor output tape. -/
theorem tail_tapes (R j : ℕ) : ¬ (tailCom R j).reads ∧ (tailCom R j).NoWrite := by
  change ¬ (tailCom 0 0).reads ∧ (tailCom 0 0).NoWrite
  decide

/-- Every level's arena arrays are outside the shared cover scratch. -/
theorem arena_arrays_free (j k : ℕ) (a : String) (ha : a ∈ levelArrays k) :
    a ∉ writeArrays j := by
  simp only [levelArrays, arenaNames, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [writeArrays, arrays, ca, co, cm, ra, ao, aj, dg, mt, od, hp, plArrNames,
      plDd, plRw, plRe, plDz, plIo, plCu, plIv, plFl,
      List.mem_append, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true]
    repeat' apply And.intro
    all_goals first
      | exact lv_ne_of_base_ne (by decide) (by decide) k j
      | exact lv_ne_fixed k (by decide)
      | trivial

theorem arena_vars_free (k : ℕ) (y : String) (hy : y ∈ levelScalars k) :
    y ∉ writeVars := by
  simp only [levelScalars, arenaNames, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  all_goals
    simp only [writeVars, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true]
    repeat' apply And.intro
    all_goals first | exact lv_ne_fixed k (by decide) | trivial

/-- Cover outputs of another level are outside this call's writes. -/
theorem other_cover_arrays_free {j k : ℕ} (hkj : k ≠ j) (a : String)
    (ha : a ∈ [ca k, co k, cm k, ra k]) : a ∉ writeArrays j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  all_goals
    simp only [writeArrays, arrays, ca, co, cm, ra, ao, aj, dg, mt, od, hp, plArrNames,
      plDd, plRw, plRe, plDz, plIo, plCu, plIv, plFl,
      List.mem_append, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true]
    repeat' apply And.intro
    all_goals first
      | exact lv_ne_of_level_ne (by decide) hkj
      | exact lv_ne_fixed k (by decide)
      | trivial

theorem centre_var_free (k : ℕ) : ctrName k ∉ writeVars := by
  simp only [ctrName, writeVars, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true]
  repeat' apply And.intro
  all_goals first | exact lv_ne_fixed k (by decide) | trivial

theorem rankClean_free (j : ℕ) : "cp.r" ∉ writeArrays j := by
  simp only [writeArrays, arrays, ca, co, cm, ra, ao, aj, dg, mt, od, hp, plArrNames,
    plDd, plRw, plRe, plDz, plIo, plCu, plIv, plFl,
    List.mem_append, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true]
  repeat' apply And.intro
  all_goals first | exact fixed_ne_lv j (by decide) | decide

private theorem keep_arena {B K j k Λ n₀ ℓp hb : ℕ} {A : Impl.MArena Λ n₀ ℓp}
    {σ τ : Env} {c : Com} (h : ArenaStW (arenaNames k) hb A σ) (hr : Run B c σ τ K)
    (hca : c.warrs ⊆ writeArrays j) (hcv : c.wvars ⊆ writeVars) :
    ArenaStW (arenaNames k) hb A τ := by
  have ha : ∀ a ∈ levelArrays k, τ.arrs a = σ.arrs a := by
    intro a ham
    exact hr.frame_arr a (fun hh => arena_arrays_free j k a ham (hca hh))
  have hv : ∀ y ∈ levelScalars k, τ.vars y = σ.vars y := by
    intro y hym
    exact hr.frame_var y (fun hh => arena_vars_free k y hym (hcv hh))
  exact arenaStW_of_eq h (hv _ (by simp [levelScalars])) (hv _ (by simp [levelScalars]))
    (ha _ (by simp [levelArrays])) (ha _ (by simp [levelArrays]))
    (ha _ (by simp [levelArrays])) (ha _ (by simp [levelArrays])) (ha _ (by simp [levelArrays]))

/-- The three actual passes after AUG, with no incoming rank hypothesis. -/
theorem tail_spec {B R r j Λ n₀ ℓp hb : ℕ} (A : Arena Λ n₀)
    (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (hr : 1 ≤ r) (hB : A.N * A.N + 4 * A.N + 4 < B) (hrB : 2 * r + 2 < B) :
    Spec B (fun σ => ArenaStW (arenaNames j) hb (Impl.ofArena A htab) σ ∧
        DelAdjSt ao aj dg mt (mdChain A.G R).toGraph ∅ σ ∧
        A.N ≤ (σ.arrs (ca j)).length ∧ A.N + 1 ≤ (σ.arrs (co j)).length ∧ Alloc A.N j σ)
      (tailCom r j)
      (fun _ τ => ArenaStW (arenaNames j) hb (Impl.ofArena A htab) τ ∧
        CtrArr (ca j) (pctr A.G (mdPerm (mdChain A.G R).toGraph) r) τ ∧
        ClusterCsr (co j) (cm j) (pfib A.G (mdPerm (mdChain A.G R).toGraph) r) τ)
      (tailK A.G R r) := by
  rintro σ ⟨hA, hAdj, hca, hco, halloc⟩
  obtain ⟨σ1, hr1, ⟨hrL, hrV⟩, _, _, _⟩ :=
    (mdPeelCore_spec (B := B) (N := A.N) (F := (mdChain A.G R).toGraph)
      (nNm := (arenaNames j).nN) (ao := ao) (aj := aj) (dg := dg) (ra := ra j) (hp := hp)
      (hsv := "@cover.h.s") (tv := "@cover.h.t") (xv := "@cover.h.x") (yv := "@cover.h.y")
      (kv := "@cover.h.k") (dv := "@cover.h.d") (vv := "@cover.h.v") (zv := "@cover.h.z")
      (iv := "@cover.h.i") (rc := "@cover.h.r") (wv := "@cover.h.w")
      mt (rank_names j).1 (rank_names j).2 (by omega)).run
      ⟨hAdj, hA.n_eq, (halloc.reserve (ra j) (by simp [arrays])).1,
        (halloc.reserve hp (by simp [arrays])).2.2.2⟩
  have hrank1 : RankArr (ra j) (mdPerm (mdChain A.G R).toGraph) σ1 :=
    ⟨hrL, fun u => (hrV u).trans (mdPerm_val _ u).symm⟩
  have hA1 := keep_arena hA hr1 (rank_warrs j) (rank_wvars j)
  have hs1 := halloc.run hr1
  obtain ⟨hot, hro, hrt, hW, hWr, hVr⟩ := build_names j
  obtain ⟨rows, off, hc, hnd, hadj⟩ := hA1.agCsrRows hot.symm
  have hm := agPaddedCsr_mass_eq hc hnd hadj
  have hM : σ1.vars (arenaNames j).nS ≤ A.N * A.N := hA1.ns_le_sq
  obtain ⟨σ2, hr2, hord, hdel, hba, _, _⟩ :=
    (agPaddedBuild_spec (B := B) (G := A.G) (π := mdPerm (mdChain A.G R).toGraph)
      hnd hadj hot hro hrt hW hWr (by decide) hVr (by omega) (by omega)).run
      ⟨hc, hA1.n_eq, rfl, hrank1,
        (hs1.reserve ao (by simp [arrays])).2.1,
        hM.trans (hs1.reserve aj (by simp [arrays])).2.2.1,
        (hs1.reserve dg (by simp [arrays])).1,
        hM.trans (hs1.reserve mt (by simp [arrays])).2.2.1,
        (hs1.reserve od (by simp [arrays])).1⟩
  have hrank2 := rankArr_of_eq hrank1 (hba (ra j) (by
    intro h
    exact (hWr (ra j) h).2.2 rfl))
  have hA2 := keep_arena hA1 hr2 (build_warrs j) (build_wvars j)
  have hs2 := hs1.run hr2
  obtain ⟨σ3, hr3, hctr, hcsr⟩ := (peelCom_spec (B := B) (G := A.G)
    (π := mdPerm (mdChain A.G R).toGraph) (by omega) hrB hr (sweep_names j)).run
    ⟨hA2.n_eq, hrank2, hord, hdel,
      by rw [run_arrs_length_eq hr2, run_arrs_length_eq hr1]; exact hca,
      by rw [run_arrs_length_eq hr2, run_arrs_length_eq hr1]; exact hco, hs2.peel⟩
  have hA3 := keep_arena hA2 hr3 (sweep_warrs r j) (sweep_wvars r j)
  rw [hm] at hr2
  exact ⟨σ3, hr1.seq (hr2.seq hr3), hA3, hctr, hcsr⟩

/-- The tail preserves the reusable scratch-content invariant by execution. -/
theorem tail_clean_spec {B R r j Λ n₀ ℓp hb : ℕ} (A : Arena Λ n₀)
    (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (hr : 1 ≤ r) (hB : A.N * A.N + 4 * A.N + 4 < B) (hrB : 2 * r + 2 < B) :
    CleanSpec n₀ B (fun σ => ArenaStW (arenaNames j) hb (Impl.ofArena A htab) σ ∧
        DelAdjSt ao aj dg mt (mdChain A.G R).toGraph ∅ σ ∧
        A.N ≤ (σ.arrs (ca j)).length ∧ A.N + 1 ≤ (σ.arrs (co j)).length ∧ Alloc A.N j σ)
      (tailCom r j)
      (fun _ τ => ArenaStW (arenaNames j) hb (Impl.ofArena A htab) τ ∧
        CtrArr (ca j) (pctr A.G (mdPerm (mdChain A.G R).toGraph) r) τ ∧
        ClusterCsr (co j) (cm j) (pfib A.G (mdPerm (mdChain A.G R).toGraph) r) τ)
      (tailK A.G R r) :=
  CleanSpec.of_spec (tail_spec A htab hr hB hrB)
    (fun h => rankClean_free j (tail_warrs r j h))

/-- The AUG reservations have the same concrete capacity as the shared tail. -/
def CoreAlloc (sA : List String) (N : ℕ) (σ : Env) : Prop :=
  ∀ a ∈ sA, N * N + N + 1 ≤ (σ.arrs a).length

theorem CoreAlloc.mono {sA : List String} {N n : ℕ} {σ : Env}
    (h : CoreAlloc sA n σ) (hN : N ≤ n) : CoreAlloc sA N σ := by
  intro a ha
  have := h a ha
  have := Nat.mul_le_mul hN hN
  omega

/-- One honest AUG seam: bounded array contents and actual CSR semantics are
inputs. The output is the computed chain's adjacency, with syntactic frames.
The command and its numerical budget are chosen before the word bound. -/
structure CoreSpec (R : ℕ) (sA : List String) (c : ℕ → Com)
    (K : (N : ℕ) → SimpleGraph (Fin N) → ℕ) : Prop where
  run : ∀ (B j N M : ℕ) (G : SimpleGraph (Fin N))
    (rows : Fin N → List (Fin N)) (off : ℕ → ℕ),
    (∀ v, (rows v).Nodup) → (∀ u v, u ∈ rows v ↔ G.Adj v u) →
    N * N + 4 * N + 4 ≤ B →
    Spec B (fun σ => AgCsrRows (arenaNames j).off (arenaNames j).tgt M rows off σ ∧
        σ.vars (arenaNames j).nN = N ∧ σ.vars (arenaNames j).nS = M ∧
        CoreAlloc sA N σ ∧ ArrWords B σ)
      (c j) (fun _ τ => DelAdjSt ao aj dg mt (mdChain G R).toGraph ∅ τ) (K N G)
  warrs : ∀ j, (c j).warrs ⊆ sA
  arena_arrays : ∀ j a, a ∈ levelArrays j → a ∉ sA
  arena_vars : ∀ j k y, y ∈ levelScalars k → y ∉ (c j).wvars
  clean_rank : "cp.r" ∉ sA

/-- Root-carrier reservations, with contents supplied only by `PrepClean`. -/
def Scv (sA : List String) (n₀ j : ℕ) (σ : Env) : Prop :=
  CoreAlloc sA n₀ σ ∧ Alloc n₀ j σ

/-- One quadratic reservation for the finite pool supplies the whole scratch. -/
theorem scv_of_reservations {sA : List String} {n₀ j : ℕ} {σ : Env}
    (h : ∀ a ∈ sA ++ arrays j, (n₀ + 2) ^ 2 ≤ (σ.arrs a).length) : Scv sA n₀ j σ := by
  have hcap : n₀ * n₀ + n₀ + 1 ≤ (n₀ + 2) ^ 2 := by nlinarith
  exact ⟨fun a ha => hcap.trans (h a (List.mem_append_left _ ha)),
    fun a ha => hcap.trans (h a (List.mem_append_right _ ha))⟩

def com (R : ℕ) (core : ℕ → Com) (j : ℕ) : Com := .seq (core j) (tailCom R j)

theorem com_tapes {R j : ℕ} {core : ℕ → Com}
    (h : ¬ (core j).reads ∧ (core j).NoWrite) :
    ¬ (com R core j).reads ∧ (com R core j).NoWrite :=
  ⟨fun hh => hh.elim h.1 (tail_tapes R j).1, h.2, (tail_tapes R j).2⟩

noncomputable def cost (R r : ℕ) (K : (N : ℕ) → SimpleGraph (Fin N) → ℕ)
    {N : ℕ} (G : SimpleGraph (Fin N)) : ℕ := K N G + tailK G R r

/-- A schedule-only coefficient supplies every word inequality in the tail. -/
theorem word_room {B n₀ N R : ℕ} (hN : N ≤ n₀)
    (hB : (2 * R + 6) * (n₀ + 2) ^ 2 < B) :
    N * N + 4 * N + 4 < B ∧ 2 * R + 2 < B := by
  have hq : N * N + 4 * N + 4 ≤ (n₀ + 2) ^ 2 := by
    have hh := Nat.mul_le_mul (Nat.add_le_add_right hN 2) (Nat.add_le_add_right hN 2)
    nlinarith
  have hl : (n₀ + 2) ^ 2 ≤ (2 * R + 6) * (n₀ + 2) ^ 2 :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hr : 2 * R + 6 ≤ (2 * R + 6) * (n₀ + 2) ^ 2 :=
    Nat.le_mul_of_pos_right _ (by positivity)
  exact ⟨hq.trans_lt (hl.trans_lt hB), by omega⟩

/-- Encoded inputs supply the same schedule-only word coefficient uniformly. -/
theorem word_room_mcB {n₀ R q : ℕ} {G : SimpleGraph (Fin n₀)} {x : List ℕ}
    (henc : Lax11.GraphEncoding.EncodesGraph x n₀ G) (hq : 2 * R + 6 ≤ q) :
    (2 * R + 6) * (n₀ + 2) ^ 2 < mcB q x := by
  have hnx : n₀ + 3 ≤ x.length := by
    have := henc.length_eq
    have := henc.vertexCount_eq
    omega
  have hs : (n₀ + 2) ^ 2 < (x.length + 1) ^ 2 := by nlinarith
  exact (Nat.mul_lt_mul_of_pos_left hs (by omega)).trans_le (Nat.mul_le_mul_right _ hq)

/-- Whole clean cover from the AUG execution, with all remaining passes concrete. -/
theorem stage_spec {L Λ n₀ ℓp B j hb : ℕ} (S : Setup L) (R : ℕ)
    (A : Arena Λ n₀) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    {sA : List String} {core : ℕ → Com} {K : (N : ℕ) → SimpleGraph (Fin N) → ℕ}
    (hcore : CoreSpec R sA core K)
    (hB : (2 * S.R + 6) * (n₀ + 2) ^ 2 < B) :
    CoverStageSpecClean B S (mdOrderingRoutine R) hb (arenaNames j) A htab
      (ca j) (co j) (cm j) (Scv sA n₀ j) (com S.R core j) (cost R S.R K A.G) := by
  rintro σ ⟨⟨hA, hca, hco, hcoreAlloc, htailAlloc⟩, hclean⟩
  have hN : A.N ≤ n₀ := arenaN_le A
  obtain ⟨hquad, hrad⟩ := word_room hN hB
  have hot : (arenaNames j).tgt ≠ (arenaNames j).off :=
    lv_ne_of_base_ne (by decide) (by decide) j j
  obtain ⟨rows, off, hc, hnd, hadj⟩ := hA.agCsrRows hot
  obtain ⟨σ1, hr1, hAdj⟩ :=
    (hcore.run B j A.N (σ.vars (arenaNames j).nS) A.G rows off hnd hadj (by omega)).run
      ⟨hc, hA.n_eq, rfl, hcoreAlloc.mono hN, hclean.2⟩
  have ha : ∀ a ∈ levelArrays j, σ1.arrs a = σ.arrs a := by
    intro a ham
    exact hr1.frame_arr a (fun hh => hcore.arena_arrays j a ham (hcore.warrs j hh))
  have hv : ∀ y ∈ levelScalars j, σ1.vars y = σ.vars y := by
    intro y hym
    exact hr1.frame_var y (hcore.arena_vars j j y hym)
  have hA1 := arenaStW_of_eq hA
    (hv _ (by simp [levelScalars])) (hv _ (by simp [levelScalars]))
    (ha _ (by simp [levelArrays])) (ha _ (by simp [levelArrays]))
    (ha _ (by simp [levelArrays])) (ha _ (by simp [levelArrays])) (ha _ (by simp [levelArrays]))
  have hclean1 : PrepClean n₀ B σ1 :=
    ⟨hclean.1.of_arr_eq (hr1.frame_arr _ (fun hh => hcore.clean_rank (hcore.warrs j hh))),
      Run.arrWords hr1 hclean.2⟩
  obtain ⟨σ2, hr2, ⟨hA2, hctr, hcsr⟩, hclean2⟩ :=
    (tail_clean_spec A htab S.one_le_R hquad hrad).run
      ⟨⟨hA1, hAdj, by rw [run_arrs_length_eq hr1]; exact hca,
        by rw [run_arrs_length_eq hr1]; exact hco, (htailAlloc.mono hN).run hr1⟩, hclean1⟩
  exact ⟨σ2, hr1.seq hr2, ⟨hA2, hctr, hcsr⟩, hclean2⟩

/-- The entire cover callback at every admissible level, with the machine order. -/
theorem coverAllClean {L n₀ B : ℕ} (S : Setup L) (R : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N)) (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    {sA : List String} {core : ℕ → Com} {K : (N : ℕ) → SimpleGraph (Fin N) → ℕ}
    (hcore : CoreSpec R sA core K)
    (hB : (2 * S.R + 6) * (n₀ + 2) ^ 2 < B) :
    CoverAllClean B S (mdOrderingRoutine R) ℓp htabF hbf Adm
      ca co cm (Scv sA n₀) (com S.R core) (fun _ A => cost R S.R K A.G) := by
  intro j _ A _ _
  exact stage_spec S R A (htabF j A) hcore hB

open Classical in
/-- The heap is charged at its real degree sum and logarithm; the sweep is
charged at its actual weak-reach fibres, with every linear/constant term kept. -/
theorem tailK_le_sparse {N R r D : ℕ} (G : SimpleGraph (Fin N)) (hr : 1 ≤ r)
    (hD : ∀ v, (Lax12.ColoringNumbers.wreach G (mdPerm (mdChain G R).toGraph) (2 * r) v).ncard ≤ D) :
    tailK G R r ≤ 200 * (N + nsOf (mdChain G R).toGraph + 1) * mdLogFactor N +
      70 * nsOf G + 306 * N + 286 +
      640 * Impl.sweepCharge G (mdPerm (mdChain G R).toGraph) r D := by
  have hm := KmdPeel_le_mdLogFactor (nsOf_le (mdChain G R).toGraph)
  have hs := peelK_le_sweepCharge G (mdPerm (mdChain G R).toGraph) r hr hD
  dsimp only [tailK, bldCoreK]
  omega

/-- The actual AUG core reads the canonical arena inputs. -/
def coreCom (R j : ℕ) : Com :=
  AugMachine.com (arenaNames j).off (arenaNames j).tgt
    (arenaNames j).nN (arenaNames j).nS R

noncomputable def coreK (R N : ℕ) (G : SimpleGraph (Fin N)) : ℕ :=
  AugMachine.cost G (nsOf G) R

private theorem aug_array_prefix {s : String}
    (hs : s ∈ ["sa.o", "sa.t", "sa.c", "sa.u", "sa.h", "sa.b", "cc.a", "cc.o", "cc.m", "cc.r"]) :
    ∀ a ∈ AugMachine.arrays, a.toList.take s.length ≠ s.toList := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem aug_var_prefix {s : String} (hs : s ∈ ["sv.n", "sv.m", "sl.u"]) :
    ∀ y ∈ AugMachine.vars, y.toList.take s.length ≠ s.toList := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> decide

private theorem aug_arrays_free (j : ℕ) (a : String) (ha : a ∈ levelArrays j) :
    a ∉ AugMachine.arrays := by
  simp only [levelArrays, arenaNames, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro h
    exact lv_ne_fixed j (aug_array_prefix (by decide) _ h) rfl

private theorem aug_vars_free (k : ℕ) (y : String) (hy : y ∈ ctrName k :: levelScalars k) :
    y ∉ AugMachine.vars := by
  simp only [ctrName, levelScalars, arenaNames, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl
  all_goals
    intro h
    exact lv_ne_fixed k (aug_var_prefix (by decide) _ h) rfl

/-- The full, landed augmentation implementation discharges the sole seam. -/
theorem core_spec (R : ℕ) : CoreSpec R AugMachine.arrays (coreCom R) (coreK R) := by
  constructor
  · intro B j N M G rows off hnd hadj hB σ hσ
    obtain ⟨hc, hn, hm, halloc, hwords⟩ := hσ
    have hmass := agPaddedCsr_mass_eq hc hnd hadj
    obtain ⟨τ, hr, _, _, hDel, _, _, _⟩ :=
      (AugMachine.com_spec G (arenaNames j).off (arenaNames j).tgt
        (arenaNames j).nN (arenaNames j).nS R
        (aug_arrays_free j _ (by simp [levelArrays]))
        (aug_arrays_free j _ (by simp [levelArrays]))
        (lv_ne_of_base_ne (by decide) (by decide) j j)
        (lv_ne_fixed j (by decide)) hB rows off hnd hadj).run
        ⟨⟨hwords, halloc⟩, hn, hm, hc⟩
    rw [hmass] at hr
    exact ⟨τ, hr, hDel⟩
  · intro j
    exact AugMachine.com_warrs _ _ _ _ R
  · exact aug_arrays_free
  · intro j k y hy
    exact fun hh => aug_vars_free k y (List.mem_cons_of_mem _ hy)
      (AugMachine.com_wvars _ _ _ _ R hh)
  · decide

/-- The concrete cover uses `3r` augmentation rounds and a radius-`r` sweep. -/
def coverCom (r j : ℕ) : Com := com r (coreCom (3 * r)) j

/-- The whole actual cover budget, independent of input words and word size. -/
noncomputable def Kcov {N : ℕ} (G : SimpleGraph (Fin N)) (r : ℕ) : ℕ :=
  cost (3 * r) r (coreK (3 * r)) G

theorem Kcov_eq {N : ℕ} (G : SimpleGraph (Fin N)) (r : ℕ) :
    Kcov G r = AugMachine.cost G (nsOf G) (3 * r) +
      KmdPeel N (nsOf (mdChain G (3 * r)).toGraph) + bldCoreK N (nsOf G) +
      peelK G ((mdOrderingRoutine (3 * r)) N G).order r := by
  simp only [Kcov, cost, coreK, tailK, mdOrderingRoutine, Nat.add_assoc]

/-- The real whole-cover callback: no semantic machine premise remains. -/
theorem coverAllClean_machine {L n₀ B : ℕ} (S : Setup L) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N)) (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (hB : (2 * S.R + 6) * (n₀ + 2) ^ 2 < B) :
    CoverAllClean B S (mdOrderingRoutine (3 * S.R)) ℓp htabF hbf Adm
      ca co cm (Scv AugMachine.arrays n₀) (coverCom S.R) (fun _ A => Kcov A.G S.R) :=
  coverAllClean S (3 * S.R) ℓp htabF hbf Adm (core_spec (3 * S.R)) hB

theorem cover_warrs (r j : ℕ) : (coverCom r j).warrs ⊆ AugMachine.arrays ++ writeArrays j := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact List.mem_append_left _ ((core_spec (3 * r)).warrs j h)
  · exact List.mem_append_right _ (tail_warrs r j h)

theorem cover_wvars (r j : ℕ) : (coverCom r j).wvars ⊆ AugMachine.vars ++ writeVars := by
  intro y hy
  rcases List.mem_append.mp hy with h | h
  · exact List.mem_append_left _ (AugMachine.com_wvars _ _ _ _ (3 * r) h)
  · exact List.mem_append_right _ (tail_wvars r j h)

theorem cover_tapes (r j : ℕ) : ¬ (coverCom r j).reads ∧ (coverCom r j).NoWrite :=
  com_tapes (AugMachine.com_tapes _ _ _ _ (3 * r))

/-- Every arena scalar and centre counter survives every cover call. -/
theorem cover_vars_free (r j k : ℕ) (y : String) (hy : y ∈ ctrName k :: levelScalars k) :
    y ∉ (coverCom r j).wvars := by
  intro h
  rcases List.mem_append.mp (cover_wvars r j h) with h | h
  · exact aug_vars_free k y hy h
  · rcases List.mem_cons.mp hy with rfl | hy
    · exact centre_var_free k h
    · exact arena_vars_free k y hy h

/-- A cover call preserves all earlier levels' arena and cover output arrays. -/
theorem cover_arrays_free {j k : ℕ} (r : ℕ) (hkj : k ≠ j) (a : String)
    (ha : a ∈ ca k :: co k :: cm k :: levelArrays k) : a ∉ (coverCom r j).warrs := by
  intro h
  rcases List.mem_append.mp (cover_warrs r j h) with h | h
  · simp only [List.mem_cons] at ha
    rcases ha with rfl | rfl | rfl | ha
    · exact lv_ne_fixed k (aug_array_prefix (by decide) _ h) rfl
    · exact lv_ne_fixed k (aug_array_prefix (by decide) _ h) rfl
    · exact lv_ne_fixed k (aug_array_prefix (by decide) _ h) rfl
    · exact aug_arrays_free k a ha h
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact other_cover_arrays_free hkj _ (by simp) h
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact other_cover_arrays_free hkj _ (by simp) h
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact other_cover_arrays_free hkj _ (by simp) h
        · exact arena_arrays_free j k a ha h

end CoverClean
end Lax3Proofs.Prog
