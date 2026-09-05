import Lax3Proofs.SolveSweepMdPeel
import Lax3Proofs.ProgCoverCharge

/-!
# Sparse augmentation machinery for the deterministic chain

The arithmetic and partial adjacency region lemmas below are reused from
wave w63. The former dense candidate scans are removed: round work must be
charged to actual arcs, transitive witnesses, and fraternal witnesses.
The sparse dictionary stores its occupied keys explicitly, validates reverse
indices before reading payloads, and requires no scan of its reserved capacity.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.CoverRoutine
open Lax62Proofs.Codegen (getD_eq_getElem)

/-! ## §1 The bit calculus and the witness counter -/

open Classical in
/-- The indicator of a proposition, as the machine stores it. One
canonical decision procedure — every `if` of this file goes through
`agBit`, so no `Nat.decLe`/`Classical.propDecidable` mismatch can
arise between a program's stored cell and an abstract reading of it. -/
noncomputable def agBit (b : Prop) : ℕ := if b then 1 else 0

@[simp] theorem agBit_pos {b : Prop} (h : b) : agBit b = 1 := by
  classical simp [agBit, h]

@[simp] theorem agBit_neg {b : Prop} (h : ¬ b) : agBit b = 0 := by
  classical simp [agBit, h]

theorem agBit_le_one (b : Prop) : agBit b ≤ 1 := by
  classical
  by_cases h : b <;> simp [agBit, h]

theorem agBit_eq_one_iff {b : Prop} : agBit b = 1 ↔ b := by
  classical
  by_cases h : b <;> simp [agBit, h]

theorem agBit_eq_zero_iff {b : Prop} : agBit b = 0 ↔ ¬ b := by
  classical
  by_cases h : b <;> simp [agBit, h]

theorem agBit_pos_iff {b : Prop} : 0 < agBit b ↔ b := by
  classical
  by_cases h : b <;> simp [agBit, h]

theorem agBit_mul (b c : Prop) : agBit b * agBit c = agBit (b ∧ c) := by
  classical
  by_cases hb : b <;> by_cases hc : c <;> simp [agBit, hb, hc]

open Classical in
/-- The number of witnesses below `k`: how many `w : Fin N` with
`w < k` satisfy `P`. Both a degree count (at `k = N`) and an
existential accumulator (`agCnt_pos_iff`) — the machine's inner scans
maintain exactly this one quantity. -/
noncomputable def agCnt {N : ℕ} (P : Fin N → Prop) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin N => (w : ℕ) < k ∧ P w).card

theorem agCnt_zero {N : ℕ} (P : Fin N → Prop) : agCnt P 0 = 0 := by
  classical
  simp [agCnt]

theorem agCnt_succ {N : ℕ} (P : Fin N → Prop) {k : ℕ} (hk : k < N) :
    agCnt P (k + 1) = agCnt P k + agBit (P ⟨k, hk⟩) := by
  classical
  have hsplit : (Finset.univ.filter fun w : Fin N => (w : ℕ) < k + 1 ∧ P w) =
      (Finset.univ.filter fun w : Fin N => (w : ℕ) < k ∧ P w) ∪
        (Finset.univ.filter fun w : Fin N => w = ⟨k, hk⟩ ∧ P w) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨hlt, hP⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
      · exact Or.inl ⟨h, hP⟩
      · exact Or.inr ⟨Fin.ext h, hP⟩
    · rintro (⟨h, hP⟩ | ⟨rfl, hP⟩)
      · exact ⟨Nat.lt_succ_of_lt h, hP⟩
      · exact ⟨Nat.lt_succ_self _, hP⟩
  have hdisj : Disjoint
      (Finset.univ.filter fun w : Fin N => (w : ℕ) < k ∧ P w)
      (Finset.univ.filter fun w : Fin N => w = ⟨k, hk⟩ ∧ P w) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hw hw'
    have h1 := (Finset.mem_filter.mp hw).2.1
    have h2 := (Finset.mem_filter.mp hw').2.1
    subst h2
    exact absurd h1 (lt_irrefl _)
  have hsecond : (Finset.univ.filter fun w : Fin N => w = ⟨k, hk⟩ ∧ P w).card
      = agBit (P ⟨k, hk⟩) := by
    by_cases hP : P ⟨k, hk⟩
    · have : (Finset.univ.filter fun w : Fin N => w = ⟨k, hk⟩ ∧ P w)
          = {(⟨k, hk⟩ : Fin N)} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        exact ⟨fun h => h.1, fun h => ⟨h, by rw [h]; exact hP⟩⟩
      rw [this, Finset.card_singleton, agBit_pos hP]
    · have : (Finset.univ.filter fun w : Fin N => w = ⟨k, hk⟩ ∧ P w)
          = (∅ : Finset (Fin N)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false, not_and]
        rintro rfl
        exact hP
      rw [this, Finset.card_empty, agBit_neg hP]
  rw [agCnt, agCnt, hsplit, Finset.card_union_of_disjoint hdisj, hsecond]

theorem agCnt_le {N : ℕ} (P : Fin N → Prop) (k : ℕ) : agCnt P k ≤ N := by
  classical
  calc agCnt P k ≤ (Finset.univ : Finset (Fin N)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = N := by simp

theorem agCnt_pos_iff {N : ℕ} {P : Fin N → Prop} {k : ℕ} :
    0 < agCnt P k ↔ ∃ w : Fin N, (w : ℕ) < k ∧ P w := by
  classical
  rw [agCnt, Finset.card_pos]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (Finset.mem_filter.mp hw).2⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩

open Classical in
/-- At the full range the counter is the filter card — the degree, for
an adjacency predicate. -/
theorem agCnt_full {N : ℕ} (P : Fin N → Prop) :
    agCnt P N = (Finset.univ.filter P).card := by
  classical
  rw [agCnt]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, w.isLt, true_and]

theorem agCnt_neighborSet {N : ℕ} (H : SimpleGraph (Fin N)) (v : Fin N) :
    agCnt (fun w => H.Adj v w) N = (H.neighborSet v).ncard := by
  classical
  rw [agCnt_full, Set.ncard_eq_toFinset_card']
  congr 1
  ext w
  simp [SimpleGraph.mem_neighborSet]

/-! ## §2 The builder's abstract layer -/

/-- **A dense `N × N` 0/1 region**: cell `u·N + v` holds the indicator
of `P u v`. Every intermediate object of the chain is carried in this
shape. -/
def agMat (a : String) {N : ℕ} (P : Fin N → Fin N → Prop) (σ : Env) : Prop :=
  N * N ≤ (σ.arrs a).length ∧
    ∀ u v : Fin N, (σ.arrs a).getD ((u : ℕ) * N + (v : ℕ)) 0 = agBit (P u v)

theorem agMat_of_eq {a : String} {N : ℕ} {P : Fin N → Fin N → Prop}
    {σ σ' : Env} (h : agMat a P σ) (he : σ'.arrs a = σ.arrs a) :
    agMat a P σ' := by
  rw [agMat, he]; exact h

theorem agMat_congr {a : String} {N : ℕ} {P Q : Fin N → Fin N → Prop}
    {σ : Env} (h : agMat a P σ) (he : ∀ u v, P u v ↔ Q u v) :
    agMat a Q σ := by
  refine ⟨h.1, fun u v => ?_⟩
  rw [h.2 u v]
  classical
  by_cases hp : P u v
  · rw [agBit_pos hp, agBit_pos ((he u v).1 hp)]
  · rw [agBit_neg hp, agBit_neg (fun hq => hp ((he u v).2 hq))]

/-- The flat pair index is below the square. -/
theorem agPair_lt {N : ℕ} (u v : Fin N) : (u : ℕ) * N + (v : ℕ) < N * N := by
  calc (u : ℕ) * N + (v : ℕ) < (u : ℕ) * N + N := by have := v.isLt; omega
    _ = ((u : ℕ) + 1) * N := by ring
    _ ≤ N * N := Nat.mul_le_mul_right N u.isLt

/-- Splitting a flat pair index is unique below the row width. -/
theorem agSplit {N a b u w : ℕ} (hb : b < N) (hw : w < N)
    (h : a * N + b = u * N + w) : a = u ∧ b = w := by
  rcases lt_trichotomy a u with hlt | heq | hgt
  · exfalso
    have e1 : (a + 1) * N = a * N + N := by ring
    have e2 : (a + 1) * N ≤ u * N := Nat.mul_le_mul_right N hlt
    omega
  · exact ⟨heq, by rw [heq] at h; omega⟩
  · exfalso
    have e1 : (u + 1) * N = u * N + N := by ring
    have e2 : (u + 1) * N ≤ a * N := Nat.mul_le_mul_right N hgt
    omega

/-- Decoding the flat pair index the machine's `div` computes. -/
theorem agDecode {N k : ℕ} (hk : k < N * N) :
    k / N < N ∧ k % N < N ∧ (k / N) * N + k % N = k := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · omega
    · exact h
  refine ⟨?_, Nat.mod_lt _ hN, ?_⟩
  · exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hk)
  · have h1 := Nat.div_add_mod k N
    have h2 : (k / N) * N = N * (k / N) := Nat.mul_comm _ _
    omega

/-- **The trigger key of an unordered pair**: the flat index of the
copy at the *larger* endpoint. Symmetric, and below `N²`. -/
def agKey {N : ℕ} (u v : Fin N) : ℕ :=
  if (v : ℕ) < (u : ℕ) then (u : ℕ) * N + (v : ℕ) else (v : ℕ) * N + (u : ℕ)

theorem agKey_symm {N : ℕ} (u v : Fin N) : agKey u v = agKey v u := by
  rcases lt_trichotomy (v : ℕ) (u : ℕ) with h | h | h
  · rw [agKey, agKey, if_pos h, if_neg (by omega)]
  · rw [agKey, agKey, if_neg (by omega), if_neg (by omega), h]
  · rw [agKey, agKey, if_neg (by omega), if_pos h]

theorem agKey_of_lt {N : ℕ} {u v : Fin N} (h : (v : ℕ) < (u : ℕ)) :
    agKey u v = (u : ℕ) * N + (v : ℕ) := by rw [agKey, if_pos h]

theorem agKey_lt {N : ℕ} (u v : Fin N) : agKey u v < N * N := by
  rcases lt_trichotomy (v : ℕ) (u : ℕ) with h | h | h
  · rw [agKey, if_pos h]; exact agPair_lt u v
  · rw [agKey, if_neg (by omega)]; exact agPair_lt v u
  · rw [agKey, if_neg (by omega)]; exact agPair_lt v u

/-- The key determines the pair: the two endpoints of a key are the
quotient and the remainder. -/
theorem agKey_pair {N : ℕ} {a b : Fin N} (hne : a ≠ b) {u w : Fin N}
    (h : agKey a b = (u : ℕ) * N + (w : ℕ)) :
    (a = u ∧ b = w) ∨ (a = w ∧ b = u) := by
  rcases lt_trichotomy (b : ℕ) (a : ℕ) with hlt | heq | hgt
  · rw [agKey, if_pos hlt] at h
    obtain ⟨h1, h2⟩ := agSplit b.isLt w.isLt h
    exact Or.inl ⟨Fin.ext h1, Fin.ext h2⟩
  · exact absurd (Fin.ext heq.symm) hne
  · rw [agKey, if_neg (by omega)] at h
    obtain ⟨h1, h2⟩ := agSplit a.isLt w.isLt h
    exact Or.inr ⟨Fin.ext h2, Fin.ext h1⟩

open Classical in
/-- **The partially placed graph**: the edges of `H` whose trigger key
is below `k`. The placement scan's loop invariant is stated at it, and
at `k = N²` it is `H` itself. -/
noncomputable def agPre {N : ℕ} (H : SimpleGraph (Fin N)) (k : ℕ) :
    SimpleGraph (Fin N) where
  Adj u v := H.Adj u v ∧ agKey u v < k
  symm _ _ h := ⟨h.1.symm, by rw [agKey_symm]; exact h.2⟩
  loopless := ⟨fun _ h => H.irrefl h.1⟩

theorem agPre_adj {N : ℕ} {H : SimpleGraph (Fin N)} {k : ℕ} {u v : Fin N} :
    (agPre H k).Adj u v ↔ H.Adj u v ∧ agKey u v < k := Iff.rfl

theorem agPre_zero {N : ℕ} (H : SimpleGraph (Fin N)) :
    agPre H 0 = (⊥ : SimpleGraph (Fin N)) := by
  ext u v
  simp only [agPre_adj, SimpleGraph.bot_adj]
  exact ⟨fun h => absurd h.2 (Nat.not_lt_zero _), fun h => absurd h (fun h => h)⟩

theorem agPre_full {N : ℕ} (H : SimpleGraph (Fin N)) :
    agPre H (N * N) = H := by
  ext u v
  exact ⟨fun h => h.1, fun h => ⟨h, agKey_lt u v⟩⟩

theorem agPre_mono {N : ℕ} {H : SimpleGraph (Fin N)} {k : ℕ} {u v : Fin N}
    (h : (agPre H k).Adj u v) : (agPre H (k + 1)).Adj u v :=
  ⟨h.1, Nat.lt_succ_of_lt h.2⟩

/-- The placement step **skips**: no edge of `H` has key `k`, so the
partial graph does not move. -/
theorem agPre_succ_skip {N : ℕ} (H : SimpleGraph (Fin N)) {k : ℕ}
    (hno : ∀ a b : Fin N, H.Adj a b → agKey a b ≠ k) :
    agPre H (k + 1) = agPre H k := by
  ext u v
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, lt_of_le_of_ne (Nat.lt_succ_iff.mp h2) (hno u v h1)⟩
  · exact agPre_mono

/-- The placement step **fires**: the partial graph gains exactly the
pair `{u, w}`. -/
theorem agPre_succ_place {N : ℕ} (H : SimpleGraph (Fin N)) {u w : Fin N}
    (hwu : (w : ℕ) < (u : ℕ)) (hadj : H.Adj u w) (a b : Fin N) :
    (agPre H ((u : ℕ) * N + (w : ℕ) + 1)).Adj a b ↔
      (agPre H ((u : ℕ) * N + (w : ℕ))).Adj a b ∨
        ((a = u ∧ b = w) ∨ (a = w ∧ b = u)) := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr (agKey_pair (H.ne_of_adj h1) h)
  · rintro (h | h)
    · exact agPre_mono h
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hadj, by rw [agKey_of_lt hwu]; exact Nat.lt_succ_self _⟩
      · exact ⟨hadj.symm, by
          rw [agKey_symm, agKey_of_lt hwu]; exact Nat.lt_succ_self _⟩

/-! ### The offset function and the partial region -/

/-- The degree-sum offsets of the built graph — `DelAdjSt`'s own
offset function, in closed form. -/
noncomputable def agOffF {N : ℕ} (H : SimpleGraph (Fin N)) (i : ℕ) : ℕ :=
  ∑ t ∈ Finset.range i, baseDeg H t

theorem agOffF_zero {N : ℕ} (H : SimpleGraph (Fin N)) : agOffF H 0 = 0 := by
  simp [agOffF]

theorem agOffF_succ {N : ℕ} (H : SimpleGraph (Fin N)) (v : Fin N) :
    agOffF H ((v : ℕ) + 1) = agOffF H (v : ℕ) + (H.neighborSet v).ncard := by
  rw [agOffF, agOffF, Finset.sum_range_succ, baseDeg_eq]

theorem agOffF_step {N : ℕ} (H : SimpleGraph (Fin N)) (i : ℕ) :
    agOffF H (i + 1) = agOffF H i + baseDeg H i := by
  rw [agOffF, agOffF, Finset.sum_range_succ]

theorem agOffF_mono {N : ℕ} (H : SimpleGraph (Fin N)) {i k : ℕ} (h : i ≤ k) :
    agOffF H i ≤ agOffF H k := by
  have hsub : Finset.range i ⊆ Finset.range k := Finset.range_subset_range.mpr h
  exact Finset.sum_le_sum_of_subset hsub

theorem agOffF_last {N : ℕ} (H : SimpleGraph (Fin N)) :
    agOffF H N = nsOf H := rfl

theorem agOffF_le_sq {N : ℕ} (H : SimpleGraph (Fin N)) {i : ℕ} (hi : i ≤ N) :
    agOffF H i ≤ N * N := by
  refine le_trans (agOffF_mono H hi) ?_
  rw [agOffF_last]
  exact nsOf_le H

/-- A live slot of a row sits inside that row's extent. -/
theorem agOffF_slot {N : ℕ} (H : SimpleGraph (Fin N)) (v : Fin N) {t : ℕ}
    (ht : t < (H.neighborSet v).ncard) :
    agOffF H (v : ℕ) + t < agOffF H ((v : ℕ) + 1) := by
  rw [agOffF_succ]; omega

/-- **The partial deletable region**: `DelAdjSt`'s degree, slot and
completeness clauses read against a *sub*graph `Hk` of the graph `H`
whose degree sums fix the offsets. At `Hk = H` it is the region. -/
def agPart (aj dg mt : String) {N : ℕ} (H Hk : SimpleGraph (Fin N))
    (σ : Env) : Prop :=
  (∀ v : Fin N, (σ.arrs dg).getD (v : ℕ) 0 = (Hk.neighborSet v).ncard) ∧
  (∀ v : Fin N, ∀ t : ℕ, t < (σ.arrs dg).getD (v : ℕ) 0 →
      ∃ w : Fin N, Hk.Adj v w ∧
        (σ.arrs aj).getD (agOffF H (v : ℕ) + t) 0 = (w : ℕ) ∧
        ∃ s : ℕ, s < (σ.arrs dg).getD (w : ℕ) 0 ∧
          (σ.arrs mt).getD (agOffF H (v : ℕ) + t) 0 = agOffF H (w : ℕ) + s ∧
          (σ.arrs aj).getD (agOffF H (w : ℕ) + s) 0 = (v : ℕ) ∧
          (σ.arrs mt).getD (agOffF H (w : ℕ) + s) 0 = agOffF H (v : ℕ) + t) ∧
  (∀ v w : Fin N, Hk.Adj v w → ∃ t : ℕ, t < (σ.arrs dg).getD (v : ℕ) 0 ∧
      (σ.arrs aj).getD (agOffF H (v : ℕ) + t) 0 = (w : ℕ))

/-- Sub-degrees never exceed the offsets' degrees. -/
theorem agSub_ncard_le {N : ℕ} {H Hk : SimpleGraph (Fin N)}
    (hsub : ∀ u v : Fin N, Hk.Adj u v → H.Adj u v) (v : Fin N) :
    (Hk.neighborSet v).ncard ≤ (H.neighborSet v).ncard :=
  Set.ncard_le_ncard (fun _ hw => hsub v _ hw) (Set.toFinite _)

open Classical in
/-- **The bridge**: the partial region at the full graph, together with
the offsets in `ao` and the two slot allocations, *is* the deletable
adjacency region at the empty deleted set. -/
theorem agDelAdjSt_of_part {ao aj dg mt : String} {N : ℕ}
    {H : SimpleGraph (Fin N)} {σ : Env}
    (hpart : agPart aj dg mt H H σ)
    (haoL : N + 1 ≤ (σ.arrs ao).length)
    (haoV : ∀ i, i ≤ N → (σ.arrs ao).getD i 0 = agOffF H i)
    (hajL : nsOf H ≤ (σ.arrs aj).length)
    (hmtL : nsOf H ≤ (σ.arrs mt).length)
    (hdgL : N ≤ (σ.arrs dg).length) :
    DelAdjSt ao aj dg mt H ∅ σ := by
  obtain ⟨hdeg, hsound, hcomp⟩ := hpart
  refine ⟨agOffF H, agOffF_zero H, agOffF_succ H, haoL, haoV, hajL, hmtL,
    hdgL, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact absurd hv (Set.notMem_empty v)
  · intro v _
    rw [hdeg v, Impl.deleteVerts_empty]
  · intro v _ t ht
    obtain ⟨w, hadj, hval, s, hs, hm1, hm2, hm3⟩ := hsound v t ht
    exact ⟨w, by rw [Impl.deleteVerts_empty]; exact hadj, hval, s, hs, hm1,
      hm2, hm3⟩
  · intro v _ w hw
    rw [Impl.deleteVerts_empty] at hw
    exact hcomp v w hw

/-! ## §3 List plumbing, branchless predicates, and the two scan rules -/

private theorem agGetElem?_of_getD {l : List ℕ} {i : ℕ} (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getElem?_eq_getElem h, getD_eq_getElem h]

private theorem agGetD_set_self {l : List ℕ} {i v : ℕ} (h : i < l.length) :
    (l.set i v).getD i 0 = v := by
  rw [getD_eq_getElem (by simpa using h), List.getElem_set]
  simp

private theorem agGetD_set_ne {l : List ℕ} {i k v : ℕ} (h : i ≠ k) :
    (l.set i v).getD k 0 = l.getD k 0 := by
  rcases Nat.lt_or_ge k l.length with hk | hk
  · rw [getD_eq_getElem (by simpa using hk), getD_eq_getElem hk,
      List.getElem_set, if_neg h]
  · rw [List.getD_eq_default _ _ (by simpa using hk),
      List.getD_eq_default _ _ (by simpa using hk)]

@[simp] theorem agVs_self (σ : Env) (x : String) (n : ℕ) :
    (σ.setVar x n).vars x = n := by simp [Env.setVar]

theorem agVs_ne (σ : Env) {x y : String} (h : y ≠ x) (n : ℕ) :
    (σ.setVar x n).vars y = σ.vars y := by simp [Env.setVar, h]

@[simp] theorem agVs_arrs (σ : Env) (x : String) (n : ℕ) (a : String) :
    (σ.setVar x n).arrs a = σ.arrs a := rfl

@[simp] theorem agAs_vars (σ : Env) (a : String) (i n : ℕ) (y : String) :
    (σ.setArr a i n).vars y = σ.vars y := rfl

@[simp] theorem agAs_self (σ : Env) (a : String) (i n : ℕ) :
    (σ.setArr a i n).arrs a = (σ.arrs a).set i n := by simp [Env.setArr]

theorem agAs_ne (σ : Env) {a b : String} (h : b ≠ a) (i n : ℕ) :
    (σ.setArr a i n).arrs b = σ.arrs b := by simp [Env.setArr, h]

/-! ### Branchless predicates

Every comparison the passes need is truncated-subtraction arithmetic
on `0/1` cells, so no pass but the placement needs a conditional at
all — and the placement needs exactly one. -/

/-- `agBit (m ≤ n)`, as an expression. -/
def agLeE (e f : Expr) : Expr := .sub (.lit 1) (.sub e f)
/-- `agBit (m < n)`, as an expression. -/
def agLtE (e f : Expr) : Expr := .sub (.lit 1) (.sub (.add e (.lit 1)) f)
/-- `agBit (m = n)`, as an expression. -/
def agEqE (e f : Expr) : Expr := .sub (.sub (.lit 1) (.sub e f)) (.sub f e)

theorem agNum_le (a b : ℕ) : 1 - (a - b) = agBit (a ≤ b) := by
  by_cases h : a ≤ b
  · rw [agBit_pos h]; omega
  · rw [agBit_neg h]; omega

theorem agNum_lt (a b : ℕ) : 1 - (a + 1 - b) = agBit (a < b) := by
  by_cases h : a < b
  · rw [agBit_pos h]; omega
  · rw [agBit_neg h]; omega

theorem agNum_eq (a b : ℕ) : 1 - (a - b) - (b - a) = agBit (a = b) := by
  by_cases h : a = b
  · rw [agBit_pos h]; omega
  · rw [agBit_neg h]; omega

theorem agNum_not {x : ℕ} {p : Prop} (h : x = agBit p) : 1 - x = agBit (¬ p) := by
  classical
  by_cases hp : p
  · rw [agBit_pos hp] at h; rw [agBit_neg (not_not_intro hp), h]
  · rw [agBit_neg hp] at h; rw [agBit_pos hp, h]

theorem agNum_and {x y : ℕ} {p q : Prop} (hx : x = agBit p) (hy : y = agBit q) :
    x * y = agBit (p ∧ q) := by rw [hx, hy, agBit_mul]

theorem agNum_or {x y : ℕ} {p q : Prop} (hx : x = agBit p) (hy : y = agBit q) :
    1 - (1 - x) * (1 - y) = agBit (p ∨ q) := by
  classical
  subst hx; subst hy
  by_cases hp : p <;> by_cases hq : q <;> simp [agBit, hp, hq]

theorem agNum_gt_zero (c : ℕ) : 1 - (1 - c) = agBit (0 < c) := by
  by_cases h : 0 < c
  · rw [agBit_pos h]; omega
  · rw [agBit_neg h]; omega

theorem agEvalSub {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m - n < B) :
    (Expr.sub e f).evalB B σ = some (m - n) :=
  evalB_bin (op := .sub) he hf h

theorem agEvalAdd {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m + n < B) :
    (Expr.add e f).evalB B σ = some (m + n) :=
  evalB_bin (op := .add) he hf h

theorem agEvalMul {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m * n < B) :
    (Expr.mul e f).evalB B σ = some (m * n) :=
  evalB_bin (op := .mul) he hf h

theorem agEvalDiv {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m / n < B) :
    (Expr.div e f).evalB B σ = some (m / n) :=
  evalB_bin (op := .div) he hf h

theorem agEval_leE {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (hmB : m < B)
    (h1B : 1 < B) : (agLeE e f).evalB B σ = some (agBit (m ≤ n)) := by
  have hs := agEvalSub he hf (by omega)
  rw [agLeE, ← agNum_le m n]
  exact agEvalSub (evalB_lit (B := B) (n := 1) h1B) hs (by omega)

theorem agEval_ltE {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (hmB : m + 1 < B)
    (h1B : 1 < B) : (agLtE e f).evalB B σ = some (agBit (m < n)) := by
  have ha := agEvalAdd he (evalB_lit (B := B) (n := 1) h1B) (by omega)
  have hs := agEvalSub ha hf (by omega)
  rw [agLtE, ← agNum_lt m n]
  exact agEvalSub (evalB_lit (B := B) (n := 1) h1B) hs (by omega)

theorem agEval_eqE {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (hmB : m < B)
    (hnB : n < B) (h1B : 1 < B) :
    (agEqE e f).evalB B σ = some (agBit (m = n)) := by
  have hs1 := agEvalSub he hf (by omega)
  have hs2 := agEvalSub hf he (by omega)
  have hs3 := agEvalSub (evalB_lit (B := B) (n := 1) h1B) hs1 (by omega)
  rw [agEqE, ← agNum_eq m n]
  exact agEvalSub hs3 hs2 (by omega)

/-! ### The two scan rules -/

/-- **The accumulate scan**: `av := 0; wv := 0; while wv < nm do
(av := av + e; wv := wv + 1)`. The summand `e` is evaluated at the
entry state's arrays and scalars with only the counter moved, which is
exactly what an inner scan sees. -/
private theorem agSumRun {B : ℕ} (L : ℕ) (av wv nm : String) (e : Expr)
    (Gf : ℕ → ℕ) (hav_wv : av ≠ wv) (hav_nm : av ≠ nm) (hwv_nm : wv ≠ nm)
    (hLB : L < B) (h1B : 1 < B)
    (hbnd : ∀ k, k ≤ L → (∑ i ∈ Finset.range k, Gf i) < B)
    (σ : Env) (hn : σ.vars nm = L)
    (he : ∀ τ : Env, (∀ a, τ.arrs a = σ.arrs a) →
        (∀ y, y ≠ av → y ≠ wv → τ.vars y = σ.vars y) → τ.vars wv < L →
        e.evalB B τ = some (Gf (τ.vars wv))) :
    ∃ σ', Run B (.seq (.assign av (.lit 0))
             (.seq (.assign wv (.lit 0))
               (.while (.lt (.var wv) (.var nm))
                 (.seq (.assign av (.add (.var av) e))
                   (.assign wv (.add (.var wv) (.lit 1)))))))
           σ σ' ((e.size + 11) * L + 8) ∧
      σ'.vars av = ∑ i ∈ Finset.range L, Gf i ∧
      (∀ y, y ≠ av → y ≠ wv → σ'.vars y = σ.vars y) ∧
      (∀ a, σ'.arrs a = σ.arrs a) := by
  set I : Env → Prop := fun τ => τ.vars wv ≤ L ∧
    τ.vars av = ∑ i ∈ Finset.range (τ.vars wv), Gf i ∧
    (∀ y, y ≠ av → y ≠ wv → τ.vars y = σ.vars y) ∧
    (∀ a, τ.arrs a = σ.arrs a) with hI_def
  have hbody : Spec B (fun τ => I τ ∧ τ.vars wv < L)
      (.seq (.assign av (.add (.var av) e))
        (.assign wv (.add (.var wv) (.lit 1))))
      (fun τ τ' => I τ' ∧ τ'.vars wv = τ.vars wv + 1) (e.size + 7) := by
    refine Spec.of_exists fun τ hτ => ?_
    obtain ⟨⟨hle, hsum, hfv, hfa⟩, hlt⟩ := hτ
    have hnext : (∑ i ∈ Finset.range (τ.vars wv + 1), Gf i) < B :=
      hbnd (τ.vars wv + 1) (by omega)
    have hstep : (∑ i ∈ Finset.range (τ.vars wv + 1), Gf i)
        = (∑ i ∈ Finset.range (τ.vars wv), Gf i) + Gf (τ.vars wv) :=
      Finset.sum_range_succ _ _
    have hcur : τ.vars av < B := by rw [hsum]; omega
    have hev := he τ hfa hfv hlt
    have hadd : (Expr.add (.var av) e).evalB B τ
        = some (τ.vars av + Gf (τ.vars wv)) :=
      agEvalAdd (evalB_var (B := B) hcur) hev (by rw [hsum]; omega)
    have h1 : Run B (.assign av (.add (.var av) e)) τ
        (τ.setVar av (τ.vars av + Gf (τ.vars wv))) (e.size + 3) :=
      (Run.assign hadd).mono (by simp [Expr.size]; omega)
    have hτ₁w : (τ.setVar av (τ.vars av + Gf (τ.vars wv))).vars wv = τ.vars wv :=
      agVs_ne τ (Ne.symm hav_wv) _
    have h2 : Run B (.assign wv (.add (.var wv) (.lit 1)))
        (τ.setVar av (τ.vars av + Gf (τ.vars wv)))
        ((τ.setVar av (τ.vars av + Gf (τ.vars wv))).setVar wv (τ.vars wv + 1))
        4 := by
      refine (Run.assign ?_).mono (by simp [Expr.size])
      have hv := evalB_var (B := B)
        (x := wv) (σ := τ.setVar av (τ.vars av + Gf (τ.vars wv)))
        (by rw [hτ₁w]; omega)
      rw [hτ₁w] at hv
      exact agEvalAdd hv (evalB_lit (B := B) (n := 1) h1B) (by omega)
    refine ⟨_, e.size + 7, (h1.seq h2).mono (by omega), le_rfl,
      ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [agVs_self]; omega
    · rw [agVs_self, agVs_ne _ hav_wv, agVs_self, hstep, hsum]
    · intro y hy1 hy2
      rw [agVs_ne _ hy2, agVs_ne _ hy1]
      exact hfv y hy1 hy2
    · intro a
      rw [agVs_arrs, agVs_arrs]
      exact hfa a
    · rw [agVs_self]
  have hloop := Spec.forRangeZero (B := B) wv nm I L (e.size + 7) hLB
    (fun τ hτ => hτ.1)
    (fun τ hτ => by
      rw [hτ.2.2.1 nm (Ne.symm hav_nm) (Ne.symm hwv_nm), hn])
    hbody
  have hstart : I ((σ.setVar av 0).setVar wv 0) := by
    refine ⟨by rw [agVs_self]; omega, ?_, ?_, ?_⟩
    · rw [agVs_self, agVs_ne _ hav_wv, agVs_self]
      simp
    · intro y hy1 hy2
      simp [Env.setVar, hy1, hy2]
    · intro a
      rw [agVs_arrs, agVs_arrs]
  obtain ⟨σ', hrun, hI', hwL⟩ := hloop.run hstart
  have hassign : Run B (.assign av (.lit 0)) σ (σ.setVar av 0) 2 :=
    (Run.assign (evalB_lit (B := B) (n := 0) (by omega))).mono (by simp [Expr.size])
  refine ⟨σ', (hassign.seq hrun).mono (le_of_eq (by ring)), ?_, ?_, ?_⟩
  · rw [hI'.2.1, hwL]
  · intro y hy1 hy2
    exact hI'.2.2.1 y hy1 hy2
  · intro a
    exact hI'.2.2.2 a

/-- **The store scan**: `pv := 0; while pv < nm do (bodyCore; pv := pv + 1)`,
where one turn of `bodyCore` writes the single array `dst` at the
counter's own cell and nothing else outside the scratch list `VS`.
Every flat pass of the file is an instance. -/
private theorem agScanRun {B : ℕ} (L Kb : ℕ) (dst : String) (VS : List String)
    (pv nm : String) (bodyCore : Com) (Ff : ℕ → ℕ)
    (hpv : pv ∈ VS) (hnm : nm ∉ VS) (hLB : L < B)
    (σ : Env) (hn : σ.vars nm = L) (hlen : L ≤ (σ.arrs dst).length)
    (hbody : ∀ τ : Env, τ.vars pv < L → (∀ y, y ∉ VS → τ.vars y = σ.vars y) →
        (∀ a, a ≠ dst → τ.arrs a = σ.arrs a) →
        (τ.arrs dst).length = (σ.arrs dst).length →
        (∀ p, p < τ.vars pv → (τ.arrs dst).getD p 0 = Ff p) →
        ∃ τ', Run B bodyCore τ τ' Kb ∧
          (∀ y, y ∉ VS → τ'.vars y = τ.vars y) ∧ τ'.vars pv = τ.vars pv ∧
          (∀ a, a ≠ dst → τ'.arrs a = τ.arrs a) ∧
          τ'.arrs dst = (τ.arrs dst).set (τ.vars pv) (Ff (τ.vars pv))) :
    ∃ σ', Run B (.seq (.assign pv (.lit 0))
              (.while (.lt (.var pv) (.var nm))
                (.seq bodyCore (.assign pv (.add (.var pv) (.lit 1)))))) σ σ'
            ((Kb + 8) * L + 6) ∧
      (∀ y, y ∉ VS → σ'.vars y = σ.vars y) ∧
      (∀ a, a ≠ dst → σ'.arrs a = σ.arrs a) ∧
      (σ'.arrs dst).length = (σ.arrs dst).length ∧
      (∀ p, p < L → (σ'.arrs dst).getD p 0 = Ff p) := by
  set I : Env → Prop := fun τ => (∀ y, y ∉ VS → τ.vars y = σ.vars y) ∧
    (∀ a, a ≠ dst → τ.arrs a = σ.arrs a) ∧
    (τ.arrs dst).length = (σ.arrs dst).length ∧ τ.vars pv ≤ L ∧
    (∀ p, p < τ.vars pv → (τ.arrs dst).getD p 0 = Ff p) with hI_def
  have hbodyS : Spec B (fun τ => I τ ∧ τ.vars pv < L)
      (.seq bodyCore (.assign pv (.add (.var pv) (.lit 1))))
      (fun τ τ' => I τ' ∧ τ'.vars pv = τ.vars pv + 1) (Kb + 4) := by
    refine Spec.of_exists fun τ hτ => ?_
    obtain ⟨⟨hfv, hfa, hdl, hple, hpre⟩, hlt⟩ := hτ
    obtain ⟨τ₁, hr1, hfv1, hp1, hfa1, hd1⟩ := hbody τ hlt hfv hfa hdl hpre
    have hkB : τ.vars pv + 1 < B := by omega
    have h2 : Run B (.assign pv (.add (.var pv) (.lit 1))) τ₁
        (τ₁.setVar pv (τ.vars pv + 1)) 4 := by
      refine (Run.assign ?_).mono (by simp [Expr.size])
      have hv := evalB_var (B := B) (x := pv) (σ := τ₁) (by rw [hp1]; omega)
      rw [hp1] at hv
      exact agEvalAdd hv (evalB_lit (B := B) (n := 1) (by omega)) (by omega)
    have hklen : τ.vars pv < (τ.arrs dst).length := by omega
    refine ⟨τ₁.setVar pv (τ.vars pv + 1), Kb + 4, (hr1.seq h2).mono (by omega),
      le_rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro y hy
      have hne : y ≠ pv := fun hc => hy (hc ▸ hpv)
      rw [agVs_ne _ hne, hfv1 y hy]
      exact hfv y hy
    · intro a ha
      rw [agVs_arrs, hfa1 a ha]
      exact hfa a ha
    · rw [agVs_arrs, hd1, List.length_set]
      exact hdl
    · rw [agVs_self]; omega
    · intro p hp
      rw [agVs_self] at hp
      rw [agVs_arrs, hd1]
      rcases Nat.lt_or_ge p (τ.vars pv) with hlt' | hge'
      · rw [agGetD_set_ne (by omega)]
        exact hpre p hlt'
      · obtain rfl : p = τ.vars pv := by omega
        exact agGetD_set_self hklen
    · rw [agVs_self]
  have hloop := Spec.forRangeZero (B := B) pv nm I L (Kb + 4) hLB
    (fun τ hτ => hτ.2.2.2.1)
    (fun τ hτ => by rw [hτ.1 nm hnm, hn])
    hbodyS
  have hstart : I (σ.setVar pv 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      have hne : y ≠ pv := fun hc => hy (hc ▸ hpv)
      rw [agVs_ne _ hne]
    · intro a _; rw [agVs_arrs]
    · rw [agVs_arrs]
    · rw [agVs_self]; omega
    · intro p hp
      rw [agVs_self] at hp
      exact absurd hp (Nat.not_lt_zero _)
  obtain ⟨σ', hrun, hI', hpL⟩ := hloop.run hstart
  exact ⟨σ', hrun.mono (le_of_eq (by ring)), hI'.1, hI'.2.1, hI'.2.2.1,
    fun p hp => hI'.2.2.2.2 p (by omega)⟩


/-! ## Sparse key dictionaries

Only the occupied prefix is initialized. The inverse table may contain any
words; a lookup first checks its candidate index against the occupied length
and then checks the key stored there. Thus stale entries cannot create keys.
-/

/-- A sparse dictionary with capacity `U`, represented by a distinct list of
occupied keys and its validated inverse. `words` is a word bound on the
otherwise arbitrary inverse-table contents, not an initialized-content oracle. -/
structure AgDictSt (ix ky sz : String) (B U : ℕ) (ks : List ℕ) (σ : Env) : Prop where
  nodup : ks.Nodup
  key_lt : ∀ k ∈ ks, k < U
  size : σ.vars sz = ks.length
  ix_len : U ≤ (σ.arrs ix).length
  ky_len : U ≤ (σ.arrs ky).length
  words : ∀ k < U, (σ.arrs ix).getD k 0 < B
  keys : ∀ i < ks.length, (σ.arrs ky).getD i 0 = ks.getD i 0
  inv : ∀ i < ks.length, (σ.arrs ix).getD (ks.getD i 0) 0 = i

private theorem agList_getD_mem {ks : List ℕ} {i : ℕ} (hi : i < ks.length) :
    ks.getD i 0 ∈ ks := by
  rw [getD_eq_getElem hi]
  exact List.getElem_mem _

private theorem agList_mem_getD {ks : List ℕ} {k : ℕ} (hk : k ∈ ks) :
    ∃ i, i < ks.length ∧ ks.getD i 0 = k := by
  obtain ⟨i, hi, hki⟩ := List.mem_iff_getElem.mp hk
  exact ⟨i, hi, by rw [getD_eq_getElem hi]; exact hki⟩

theorem AgDictSt.length_le {ix ky sz : String} {B U : ℕ} {ks : List ℕ}
    {σ : Env} (h : AgDictSt ix ky sz B U ks σ) : ks.length ≤ U := by
  have hs : ks.toFinset ⊆ Finset.range U := by
    intro k hk
    exact Finset.mem_range.mpr (h.key_lt k (List.mem_toFinset.mp hk))
  have hc := Finset.card_le_card hs
  simpa [List.toFinset_card_of_nodup h.nodup] using hc

theorem AgDictSt.lookup_iff {ix ky sz : String} {B U : ℕ} {ks : List ℕ}
    {σ : Env} (h : AgDictSt ix ky sz B U ks σ) (k : ℕ) :
    ((σ.arrs ix).getD k 0 < ks.length ∧
      (σ.arrs ky).getD ((σ.arrs ix).getD k 0) 0 = k) ↔ k ∈ ks := by
  constructor
  · rintro ⟨hp, hk⟩
    rw [h.keys _ hp] at hk
    exact hk ▸ agList_getD_mem hp
  · intro hk
    obtain ⟨i, hi, hki⟩ := agList_mem_getD hk
    have hp : (σ.arrs ix).getD k 0 = i := by
      rw [← hki]
      exact h.inv i hi
    exact ⟨by omega, by rw [hp, h.keys i hi, hki]⟩

theorem AgDictSt.of_eq {ix ky sz : String} {B U : ℕ} {ks : List ℕ}
    {σ τ : Env} (h : AgDictSt ix ky sz B U ks σ)
    (hi : τ.arrs ix = σ.arrs ix) (hk : τ.arrs ky = σ.arrs ky)
    (hs : τ.vars sz = σ.vars sz) : AgDictSt ix ky sz B U ks τ := by
  refine ⟨h.nodup, h.key_lt, hs.trans h.size, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hi]; exact h.ix_len
  · rw [hk]; exact h.ky_len
  · intro k hkU; rw [hi]; exact h.words k hkU
  · intro i hiL; rw [hk]; exact h.keys i hiL
  · intro i hiL; rw [hi]; exact h.inv i hiL

/-- Lookup reads the inverse entry, then validates both range and reverse key.
`tv` receives the candidate position, `hv` the membership bit. -/
def agDictFind (ix ky sz kv tv hv : String) : Com :=
  .seq (.seq (.assign hv (.lit 0)) (.assign tv (.get ix (.var kv))))
    (.ite (.lt (.var tv) (.var sz))
      (.ite (.eq (.get ky (.var tv)) (.var kv)) (.assign hv (.lit 1)) .skip)
      .skip)

private theorem agEvalVar {B k : ℕ} {σ : Env} {x : String}
    (hx : σ.vars x = k) (hk : k < B) : (Expr.var x).evalB B σ = some k := by
  rw [← hx]
  exact evalB_var (by omega)

private theorem agEvalGet {B i k : ℕ} {σ : Env} {a : String} {e : Expr}
    (he : e.evalB B σ = some i) (hi : i < (σ.arrs a).length)
    (hk : (σ.arrs a).getD i 0 = k) (hB : k < B) :
    (Expr.get a e).evalB B σ = some k := by
  exact evalB_get he (by rw [agGetElem?_of_getD hi, hk]) hB

/-- The dictionary lookup costs a constant independent of its capacity. -/
theorem agDictFind_run {B U : ℕ} (ix ky sz kv tv hv : String)
    (hvs : ([sz, kv, tv, hv] : List String).Nodup) (hUB : U < B)
    (h1B : 1 < B) {ks : List ℕ} (σ : Env)
    (hD : AgDictSt ix ky sz B U ks σ) {k : ℕ}
    (hk : σ.vars kv = k) (hkU : k < U) :
    ∃ τ, Run B (agDictFind ix ky sz kv tv hv) σ τ 20 ∧
      AgDictSt ix ky sz B U ks τ ∧
      τ.vars tv = (σ.arrs ix).getD k 0 ∧ τ.vars hv = agBit (k ∈ ks) ∧
      (∀ y, y ≠ tv → y ≠ hv → τ.vars y = σ.vars y) ∧
      (∀ a, τ.arrs a = σ.arrs a) := by
  have hvs' := hvs
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hvs'
  obtain ⟨⟨hs_k, hs_t, hs_h⟩, ⟨hk_t, hk_h⟩, ht_h⟩ := hvs'
  let p := (σ.arrs ix).getD k 0
  let σa := σ.setVar hv 0
  let σb := σa.setVar tv p
  have hpa : p < B := hD.words k hkU
  have hpre : Run B
      (.seq (.assign hv (.lit 0)) (.assign tv (.get ix (.var kv)))) σ σb 5 := by
    refine ((Run.assign (evalB_lit (by omega))).seq (Run.assign ?_)).mono ?_
    · refine agEvalGet (agEvalVar (by simp [Env.setVar, hk_h, hk])
        (by omega)) (by simpa [σa] using lt_of_lt_of_le hkU hD.ix_len) rfl hpa
    · simp [Expr.size]
  have hbvars : ∀ y, y ≠ tv → y ≠ hv → σb.vars y = σ.vars y := by
    intro y hy1 hy2
    simp [σb, σa, Env.setVar, hy1, hy2]
  have hbarrs : ∀ a, σb.arrs a = σ.arrs a := fun _ => rfl
  have hbt : σb.vars tv = p := by simp [σb, Env.setVar]
  have hbh : σb.vars hv = 0 := by simp [σb, σa, Env.setVar, Ne.symm ht_h]
  have hbs : σb.vars sz = ks.length := (hbvars sz hs_t hs_h).trans hD.size
  have hbk : σb.vars kv = k := (hbvars kv hk_t hk_h).trans hk
  have hcond : (Cond.lt (.var tv) (.var sz)).evalB B σb =
      some (decide (p < ks.length)) :=
    evalB_condLt (agEvalVar hbt hpa)
      (agEvalVar hbs (lt_of_le_of_lt hD.length_le hUB))
  have hex : ∃ τ, Run B
        (.ite (.lt (.var tv) (.var sz))
          (.ite (.eq (.get ky (.var tv)) (.var kv)) (.assign hv (.lit 1)) .skip)
          .skip) σb τ 15 ∧
      τ.vars tv = p ∧ τ.vars hv = agBit (k ∈ ks) ∧
      (∀ y, y ≠ hv → τ.vars y = σb.vars y) ∧
      (∀ a, τ.arrs a = σb.arrs a) := by
    by_cases hp : p < ks.length
    · have hkeyB : (σb.arrs ky).getD p 0 < B := by
        rw [hbarrs, hD.keys p hp]
        exact lt_trans (hD.key_lt _ (agList_getD_mem hp)) hUB
      have heq : (Cond.eq (.get ky (.var tv)) (.var kv)).evalB B σb =
          some ((σ.arrs ky).getD p 0 == k) := by
        exact evalB_condEq
          (agEvalGet (agEvalVar hbt hpa) (by
            rw [hbarrs]; exact lt_of_lt_of_le (lt_of_lt_of_le hp hD.length_le) hD.ky_len)
            rfl hkeyB) (agEvalVar hbk (by omega))
      by_cases he : (σ.arrs ky).getD p 0 = k
      · have hmem : k ∈ ks := hD.lookup_iff k |>.mp ⟨hp, he⟩
        refine ⟨σb.setVar hv 1, ?_, ?_, ?_, ?_, fun _ => rfl⟩
        · refine (Run.ite_true (by simpa [hp] using hcond)
            (Run.ite_true (by rw [heq]; simp only [he, beq_self_eq_true])
              (Run.assign (evalB_lit h1B)))).mono ?_
          simp [Cond.size, Expr.size]
        · simp [Env.setVar, ht_h, hbt]
        · simp [Env.setVar, agBit_pos hmem]
        · intro y hy; simp [Env.setVar, hy]
      · have hmem : k ∉ ks := fun hm => he ((hD.lookup_iff k).mpr hm).2
        refine ⟨σb, ?_, hbt, ?_, fun _ _ => rfl, fun _ => rfl⟩
        · refine (Run.ite_true (by simpa [hp] using hcond)
            (Run.ite_false (by rw [heq]; simp only [Option.some.injEq, beq_eq_false_iff_ne]; exact he) Run.skip)).mono ?_
          simp [Cond.size, Expr.size]
        · rw [hbh, agBit_neg hmem]
    · have hmem : k ∉ ks := fun hm => hp ((hD.lookup_iff k).mpr hm).1
      refine ⟨σb, ?_, hbt, ?_, fun _ _ => rfl, fun _ => rfl⟩
      · refine (Run.ite_false (by simpa [hp] using hcond) Run.skip).mono ?_
        simp [Cond.size, Expr.size]
      · rw [hbh, agBit_neg hmem]
  obtain ⟨τ, hrun, ht, hh, hvars, harrs⟩ := hex
  have hfa : ∀ a, τ.arrs a = σ.arrs a := fun a => (harrs a).trans (hbarrs a)
  have hfv : ∀ y, y ≠ tv → y ≠ hv → τ.vars y = σ.vars y :=
    fun y hy1 hy2 => (hvars y hy2).trans (hbvars y hy1 hy2)
  refine ⟨τ, ?_, hD.of_eq (hfa ix) (hfa ky) (hfv sz hs_t hs_h), ht, hh, hfv, hfa⟩
  exact hpre.seq hrun

private theorem agList_append_getD {ks : List ℕ} {i k : ℕ} (hi : i < ks.length) :
    (ks ++ [k]).getD i 0 = ks.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hi, ↓reduceIte]

private theorem agList_append_getD_last (ks : List ℕ) (k : ℕ) :
    (ks ++ [k]).getD ks.length 0 = k := by
  simp [List.getD_eq_getElem?_getD]

private theorem agList_length_le {ks : List ℕ} {U : ℕ}
    (hn : ks.Nodup) (hk : ∀ k ∈ ks, k < U) : ks.length ≤ U := by
  have hs : ks.toFinset ⊆ Finset.range U := by
    intro k h
    exact Finset.mem_range.mpr (hk k (List.mem_toFinset.mp h))
  have hc := Finset.card_le_card hs
  simpa [List.toFinset_card_of_nodup hn] using hc

/-- Inserting a key changes only an occupied prefix and one inverse cell. -/
def agDictGrow (ks : List ℕ) (k : ℕ) : List ℕ := if k ∈ ks then ks else ks ++ [k]

@[simp] theorem agDictGrow_mem (ks : List ℕ) (k z : ℕ) :
    z ∈ agDictGrow ks k ↔ z ∈ ks ∨ z = k := by
  by_cases hk : k ∈ ks <;> simp [agDictGrow, hk]
  exact fun hz => hz ▸ hk

/-- New keys append to the occupied prefix; existing keys reuse their slot.
`tv` is the resulting position and `hv` records whether the key was present. -/
def agDictInsert (ix ky sz kv tv hv : String) : Com :=
  .seq (agDictFind ix ky sz kv tv hv)
    (.ite (.eq (.var hv) (.lit 0))
      (.seq (.assign tv (.var sz))
        (.seq (.store ix (.var kv) (.var sz))
          (.seq (.store ky (.var sz) (.var kv))
            (.assign sz (.add (.var sz) (.lit 1))))))
      .skip)

set_option maxHeartbeats 500000 in
/-- A complete constant-time sparse insertion, including the allocation,
word bounds, inverse validation, and preservation of every array length. -/
theorem agDictInsert_run {B U : ℕ} (ix ky sz kv tv hv : String)
    (harr : ix ≠ ky) (hvs : ([sz, kv, tv, hv] : List String).Nodup)
    (hUB : U < B) (h1B : 1 < B) {ks : List ℕ} (σ : Env)
    (hD : AgDictSt ix ky sz B U ks σ) {k : ℕ}
    (hk : σ.vars kv = k) (hkU : k < U) :
    ∃ τ, Run B (agDictInsert ix ky sz kv tv hv) σ τ 40 ∧
      AgDictSt ix ky sz B U (agDictGrow ks k) τ ∧
      τ.vars tv < (agDictGrow ks k).length ∧
      (τ.arrs ky).getD (τ.vars tv) 0 = k ∧
      τ.vars hv = agBit (k ∈ ks) ∧
      (∀ y, y ≠ sz → y ≠ tv → y ≠ hv → τ.vars y = σ.vars y) ∧
      (∀ a, a ≠ ix → a ≠ ky → τ.arrs a = σ.arrs a) ∧
      (∀ a, (τ.arrs a).length = (σ.arrs a).length) := by
  have hvs' := hvs
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hvs'
  obtain ⟨⟨hs_k, hs_t, hs_h⟩, ⟨hk_t, hk_h⟩, ht_h⟩ := hvs'
  obtain ⟨ρ, hfind, hDρ, htvρ, hhvρ, hfvρ, hfaρ⟩ :=
    agDictFind_run ix ky sz kv tv hv hvs hUB h1B σ hD hk hkU
  have hkρ : ρ.vars kv = k := (hfvρ kv hk_t hk_h).trans hk
  have hszρ : ρ.vars sz = ks.length := hDρ.size
  have hhvB : ρ.vars hv < B := by rw [hhvρ]; exact lt_of_le_of_lt (agBit_le_one _) h1B
  have hcond : (Cond.eq (.var hv) (.lit 0)).evalB B ρ =
      some (agBit (k ∈ ks) == 0) :=
    evalB_condEq (agEvalVar hhvρ (by omega)) (evalB_lit (by omega))
  by_cases hmem : k ∈ ks
  · have hlookup := (hD.lookup_iff k).mpr hmem
    refine ⟨ρ, ?_, ?_, ?_, ?_, hhvρ, ?_, ?_, ?_⟩
    · refine (hfind.seq (Run.ite_false ?_ Run.skip)).mono ?_
      · rw [hcond, agBit_pos hmem]; rfl
      · simp [Cond.size, Expr.size]
    · simpa only [agDictGrow, if_pos hmem] using hDρ
    · simpa only [agDictGrow, if_pos hmem, htvρ] using hlookup.1
    · rw [hfaρ, htvρ]; exact hlookup.2
    · intro y _ ht hh; exact hfvρ y ht hh
    · intro a _ _; exact hfaρ a
    · intro a; rw [hfaρ]
  · have hnewN : (ks ++ [k]).Nodup := by
      simp only [List.nodup_append, List.nodup_cons, List.nodup_nil,
        List.not_mem_nil, not_false_eq_true, and_self]
      refine ⟨hD.nodup, trivial, ?_⟩
      intro a ha b hb
      have hb' : b = k := by simpa using hb
      subst b
      exact fun he => hmem (he ▸ ha)
    have hnewK : ∀ z ∈ ks ++ [k], z < U := by
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hD.key_lt z hz
      · have : z = k := by simpa using hz
        simpa [this] using hkU
    have hroom : ks.length < U := by
      have h := agList_length_le hnewN hnewK
      simpa only [List.length_append, List.length_singleton, Nat.add_one_le_iff] using h
    let ρa := ρ.setVar tv ks.length
    let ρb := ρa.setArr ix k ks.length
    let ρc := ρb.setArr ky ks.length k
    let τ := ρc.setVar sz (ks.length + 1)
    have hrun1 : Run B (.assign tv (.var sz)) ρ ρa 2 :=
      Run.assign (agEvalVar hszρ (by omega))
    have hrun2 : Run B (.store ix (.var kv) (.var sz)) ρa ρb 3 := by
      exact Run.store (agEvalVar (by simp [ρa, Env.setVar, hk_t, hkρ]) (by omega))
        (agEvalVar (by simp [ρa, Env.setVar, hs_t, hszρ]) (by omega))
        (by simpa [ρa] using lt_of_lt_of_le hkU hDρ.ix_len)
    have hrun3 : Run B (.store ky (.var sz) (.var kv)) ρb ρc 3 := by
      refine Run.store (agEvalVar (by simp [ρb, ρa, Env.setVar, hs_t, hszρ]) (by omega))
        (agEvalVar (by simp [ρb, ρa, Env.setVar, hk_t, hkρ]) (by omega)) ?_
      simpa [ρb, ρa, Env.setArr, Ne.symm harr] using lt_of_lt_of_le hroom hDρ.ky_len
    have hrun4 : Run B (.assign sz (.add (.var sz) (.lit 1))) ρc τ 4 := by
      exact Run.assign (agEvalAdd
        (agEvalVar (by simp [ρc, ρb, ρa, Env.setVar, hs_t, hszρ]) (by omega))
        (evalB_lit h1B) (by omega))
    have hixτ : τ.arrs ix = (ρ.arrs ix).set k ks.length := by
      simp [τ, ρc, ρb, ρa, Env.setArr, harr]
    have hkyτ : τ.arrs ky = (ρ.arrs ky).set ks.length k := by
      simp [τ, ρc, ρb, ρa, Env.setArr, Ne.symm harr]
    have htvτ : τ.vars tv = ks.length := by
      simp [τ, ρc, ρb, ρa, Env.setVar, Ne.symm hs_t]
    have hszτ : τ.vars sz = (ks ++ [k]).length := by simp [τ, Env.setVar]
    have hlenτ : ∀ a, (τ.arrs a).length = (ρ.arrs a).length := by
      intro a
      dsimp only [τ, ρc, ρb, ρa]
      rw [arrs_setVar, length_arrs_setArr, length_arrs_setArr, arrs_setVar]
    have hkeysτ : ∀ i < (ks ++ [k]).length,
        (τ.arrs ky).getD i 0 = (ks ++ [k]).getD i 0 := by
      intro i hi
      rw [hkyτ]
      by_cases hil : i < ks.length
      · rw [agGetD_set_ne (by omega), agList_append_getD hil, hDρ.keys i hil]
      · have hi' : i = ks.length := by simp only [List.length_append,
          List.length_singleton] at hi; omega
        subst i
        rw [agGetD_set_self (lt_of_lt_of_le hroom hDρ.ky_len), agList_append_getD_last]
    have hinvτ : ∀ i < (ks ++ [k]).length,
        (τ.arrs ix).getD ((ks ++ [k]).getD i 0) 0 = i := by
      intro i hi
      rw [hixτ]
      by_cases hil : i < ks.length
      · rw [agList_append_getD hil, agGetD_set_ne ?_, hDρ.inv i hil]
        exact fun he => hmem (he ▸ agList_getD_mem hil)
      · have hi' : i = ks.length := by simp only [List.length_append,
          List.length_singleton] at hi; omega
        subst i
        rw [agList_append_getD_last, agGetD_set_self (lt_of_lt_of_le hkU hDρ.ix_len)]
    have hnew : AgDictSt ix ky sz B U (ks ++ [k]) τ := by
      refine ⟨hnewN, hnewK, hszτ, ?_, ?_, ?_, hkeysτ, hinvτ⟩
      · rw [hlenτ]; exact hDρ.ix_len
      · rw [hlenτ]; exact hDρ.ky_len
      · intro z hz
        rw [hixτ]
        by_cases hzk : z = k
        · subst z
          rw [agGetD_set_self (lt_of_lt_of_le hkU hDρ.ix_len)]
          omega
        · rw [agGetD_set_ne (Ne.symm hzk)]; exact hDρ.words z hz
    refine ⟨τ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine (hfind.seq (Run.ite_true ?_
        (hrun1.seq (hrun2.seq (hrun3.seq hrun4))))).mono ?_
      · rw [hcond, agBit_neg hmem]; rfl
      · simp [Cond.size, Expr.size]
    · simpa only [agDictGrow, if_neg hmem] using hnew
    · simp [agDictGrow, hmem, htvτ]
    · rw [htvτ, hkyτ, agGetD_set_self (lt_of_lt_of_le hroom hDρ.ky_len)]
    · simpa [τ, ρc, ρb, ρa, Env.setVar, Ne.symm hs_h, Ne.symm ht_h] using hhvρ
    · intro y hy1 hy2 hy3
      simp only [τ, ρc, ρb, ρa, vars_setVar, vars_setArr,
        if_neg hy1, if_neg hy2]
      exact hfvρ y hy2 hy3
    · intro a ha1 ha2
      simp only [τ, ρc, ρb, ρa, arrs_setVar, arrs_setArr, if_neg ha2, if_neg ha1]
      exact hfaρ a
    · intro a; rw [hlenτ, hfaρ]

/-- Resetting a dictionary costs two steps and does not inspect its reserve. -/
theorem agDictInit_run {B U : ℕ} (ix ky sz : String) (σ : Env) (hB : 0 < B)
    (hi : U ≤ (σ.arrs ix).length) (hk : U ≤ (σ.arrs ky).length)
    (hw : ∀ k < U, (σ.arrs ix).getD k 0 < B) :
    Run B (.assign sz (.lit 0)) σ (σ.setVar sz 0) 2 ∧
      AgDictSt ix ky sz B U [] (σ.setVar sz 0) := by
  exact ⟨Run.assign (evalB_lit hB),
    ⟨List.nodup_nil, by simp, by simp, hi, hk, hw, by simp, by simp⟩⟩

/-- The mathematical effect of streaming a list of candidates through a
sparse dictionary. This definition imposes no order on the input rows. -/
def agDictUnion (ks xs : List ℕ) : List ℕ := xs.foldl agDictGrow ks

@[simp] theorem agDictUnion_nil (ks : List ℕ) : agDictUnion ks [] = ks := rfl

@[simp] theorem agDictUnion_append (ks xs ys : List ℕ) :
    agDictUnion ks (xs ++ ys) = agDictUnion (agDictUnion ks xs) ys :=
  List.foldl_append

@[simp] theorem agDictUnion_mem (ks xs : List ℕ) (k : ℕ) :
    k ∈ agDictUnion ks xs ↔ k ∈ ks ∨ k ∈ xs := by
  induction xs generalizing ks with
  | nil => simp
  | cons x xs ih =>
      change k ∈ agDictUnion (agDictGrow ks x) xs ↔ _
      rw [ih, agDictGrow_mem]
      simp only [List.mem_cons]
      tauto

private theorem agDictUnion_take_succ (ks xs : List ℕ) {i : ℕ}
    (hi : i < xs.length) :
    agDictUnion ks (xs.take (i + 1)) =
      agDictGrow (agDictUnion ks (xs.take i)) (xs.getD i 0) := by
  rw [List.take_succ_eq_append_getElem hi, agDictUnion_append, getD_eq_getElem hi]
  rfl

/-- Stream candidate expressions directly into the dictionary. The body reads
one candidate and performs one insertion; the reserved key space is never scanned. -/
def agDictEnumerate (ix ky sz kv tv hv iv lm : String) (e : Expr) : Com :=
  .seq (.assign iv (.lit 0))
    (.while (.lt (.var iv) (.var lm))
      (.seq (.assign kv e)
        (.seq (agDictInsert ix ky sz kv tv hv)
          (.assign iv (.add (.var iv) (.lit 1))))))

set_option maxHeartbeats 600000 in
/-- The priced scan rule for an actual candidate list. Its charge is linear
in `xs.length`; no power of the key capacity occurs in the budget. The
expression hypothesis is just a local read rule, discharged from the input
in-lists when this combinator is used for a transitive or fraternal scan. -/
theorem agDictEnumerate_run {B U : ℕ} (ix ky sz kv tv hv iv lm : String)
    (e : Expr) (harr : ix ≠ ky)
    (hvs : ([sz, kv, tv, hv, iv, lm] : List String).Nodup)
    (hUB : U < B) (h1B : 1 < B) (ks xs : List ℕ) (σ : Env)
    (hD : AgDictSt ix ky sz B U ks σ) (hL : xs.length < B)
    (hlm : σ.vars lm = xs.length) (hxU : ∀ k ∈ xs, k < U)
    (he : ∀ ρ : Env,
      (∀ a, a ≠ ix → a ≠ ky → ρ.arrs a = σ.arrs a) →
      (∀ y, y ≠ sz → y ≠ kv → y ≠ tv → y ≠ hv → y ≠ iv →
        ρ.vars y = σ.vars y) →
      ρ.vars iv < xs.length →
      e.evalB B ρ = some (xs.getD (ρ.vars iv) 0)) :
    ∃ τ, Run B (agDictEnumerate ix ky sz kv tv hv iv lm e) σ τ
        ((e.size + 49) * xs.length + 6) ∧
      AgDictSt ix ky sz B U (agDictUnion ks xs) τ ∧
      (∀ y, y ≠ sz → y ≠ kv → y ≠ tv → y ≠ hv → y ≠ iv →
        τ.vars y = σ.vars y) ∧
      (∀ a, a ≠ ix → a ≠ ky → τ.arrs a = σ.arrs a) ∧
      (∀ a, (τ.arrs a).length = (σ.arrs a).length) := by
  have hvs4 : ([sz, kv, tv, hv] : List String).Nodup :=
    hvs.sublist (List.take_sublist 4 [sz, kv, tv, hv, iv, lm])
  have hvs' := hvs
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hvs'
  obtain ⟨⟨hs_k, hs_t, hs_h, hs_i, hs_l⟩,
    ⟨hk_t, hk_h, hk_i, hk_l⟩, ⟨ht_h, ht_i, ht_l⟩,
    ⟨hh_i, hh_l⟩, hi_l⟩ := hvs'
  let I : Env → Prop := fun ρ => ρ.vars iv ≤ xs.length ∧
    AgDictSt ix ky sz B U (agDictUnion ks (xs.take (ρ.vars iv))) ρ ∧
    (∀ y, y ≠ sz → y ≠ kv → y ≠ tv → y ≠ hv → y ≠ iv →
      ρ.vars y = σ.vars y) ∧
    (∀ a, a ≠ ix → a ≠ ky → ρ.arrs a = σ.arrs a) ∧
    (∀ a, (ρ.arrs a).length = (σ.arrs a).length)
  have hbody : Spec B (fun ρ => I ρ ∧ ρ.vars iv < xs.length)
      (.seq (.assign kv e)
        (.seq (agDictInsert ix ky sz kv tv hv)
          (.assign iv (.add (.var iv) (.lit 1)))))
      (fun ρ τ => I τ ∧ τ.vars iv = ρ.vars iv + 1) (e.size + 45) := by
    refine Spec.of_exists ?_
    rintro ρ ⟨⟨hle, hDr, hfv, hfa, hlen⟩, hlt⟩
    let k := xs.getD (ρ.vars iv) 0
    have hkU : k < U := hxU _ (agList_getD_mem hlt)
    let ρa := ρ.setVar kv k
    have h1 : Run B (.assign kv e) ρ ρa (1 + e.size) :=
      Run.assign (he ρ hfa hfv hlt)
    have hDa : AgDictSt ix ky sz B U (agDictUnion ks (xs.take (ρ.vars iv))) ρa :=
      hDr.of_eq rfl rfl (by simp [ρa, Env.setVar, hs_k])
    obtain ⟨ρb, h2, hDb, hpos, hkey, hbit, hfvb, hfab, hlenb⟩ :=
      agDictInsert_run ix ky sz kv tv hv harr hvs4 hUB h1B ρa hDa
        (by simp [ρa, Env.setVar]) hkU
    have hib : ρb.vars iv = ρ.vars iv := by
      rw [hfvb iv (Ne.symm hs_i) (Ne.symm ht_i) (Ne.symm hh_i)]
      simp [ρa, Env.setVar, Ne.symm hk_i]
    let τ := ρb.setVar iv (ρ.vars iv + 1)
    have h3 : Run B (.assign iv (.add (.var iv) (.lit 1))) ρb τ 4 :=
      Run.assign (agEvalAdd (agEvalVar hib (by omega)) (evalB_lit h1B) (by omega))
    have hit : τ.vars iv = ρ.vars iv + 1 := by simp [τ, Env.setVar]
    have hDt : AgDictSt ix ky sz B U (agDictUnion ks (xs.take (τ.vars iv))) τ := by
      rw [hit, agDictUnion_take_succ ks xs hlt]
      exact hDb.of_eq rfl rfl (by simp [τ, Env.setVar, hs_i])
    refine ⟨τ, e.size + 45, (h1.seq (h2.seq h3)).mono (by omega), le_rfl,
      ⟨by omega, hDt, ?_, ?_, ?_⟩, hit⟩
    · intro y hy1 hy2 hy3 hy4 hy5
      rw [show τ.vars y = ρb.vars y by simp [τ, Env.setVar, hy5],
        hfvb y hy1 hy3 hy4]
      rw [show ρa.vars y = ρ.vars y by simp [ρa, Env.setVar, hy2]]
      exact hfv y hy1 hy2 hy3 hy4 hy5
    · intro a ha1 ha2
      rw [show τ.arrs a = ρb.arrs a from rfl, hfab a ha1 ha2]
      exact hfa a ha1 ha2
    · intro a
      rw [show τ.arrs a = ρb.arrs a from rfl, hlenb a]
      exact hlen a
  have hloop := Spec.forRangeZero (B := B) iv lm I xs.length (e.size + 45) hL
    (fun ρ h => h.1)
    (fun ρ h => (h.2.2.1 lm (Ne.symm hs_l) (Ne.symm hk_l)
      (Ne.symm ht_l) (Ne.symm hh_l) (Ne.symm hi_l)).trans hlm) hbody
  have hstart : I (σ.setVar iv 0) := by
    refine ⟨by simp, ?_, ?_, fun _ _ _ => rfl, fun _ => rfl⟩
    · simpa only [vars_setVar, if_pos rfl, List.take_zero, agDictUnion_nil] using
        hD.of_eq (τ := σ.setVar iv 0) rfl rfl (by simp [hs_i])
    · intro y _ _ _ _ hy; simp [Env.setVar, hy]
  obtain ⟨τ, hrun, hI, hiv⟩ := hloop.run hstart
  refine ⟨τ, hrun, ?_, hI.2.2.1, hI.2.2.2.1, hI.2.2.2.2⟩
  have hlast := hI.2.1
  simpa only [hiv, List.take_length] using hlast

/-! ## Actual demand lists and their exact charges -/

/-- A row family enumerating the in-neighbours once each. Rows may be in any
order; no sorting invariant is assumed or priced. -/
structure AgInRows {N : ℕ} (D : Orientation N) (rows : Fin N → List (Fin N)) : Prop where
  nodup : ∀ v, (rows v).Nodup
  finset : ∀ v, (rows v).toFinset = D.inN v

@[simp] theorem AgInRows.mem_iff {N : ℕ} {D : Orientation N}
    {rows : Fin N → List (Fin N)} (h : AgInRows D rows) (u v : Fin N) :
    u ∈ rows v ↔ u ∈ D.inN v := by
  rw [← h.finset v, List.mem_toFinset]

theorem AgInRows.length {N : ℕ} {D : Orientation N}
    {rows : Fin N → List (Fin N)} (h : AgInRows D rows) (v : Fin N) :
    (rows v).length = (D.inN v).card := by
  rw [← h.finset v, List.toFinset_card_of_nodup (h.nodup v)]

/-- Existing arcs, enumerated by their heads' in-lists. -/
def agArcCandidates {N : ℕ} (rows : Fin N → List (Fin N)) : List (Fin N × Fin N) :=
  (List.finRange N).flatMap fun v => (rows v).map fun u => (u, v)

/-- Directed paths `u → w → v`, enumerated by `v`, then `w ∈ inN(v)`,
then `u ∈ inN(w)`. Repeated witnesses are retained in this work list. -/
def agTransCandidates {N : ℕ} (rows : Fin N → List (Fin N)) : List (Fin N × Fin N) :=
  (List.finRange N).flatMap fun v =>
    (rows v).flatMap fun w => (rows w).map fun u => (u, v)

/-- Ordered in-neighbour pairs of a common head. Diagonal pairs are counted
here and discarded by the graph-emission guard. -/
def agFratCandidates {N : ℕ} (rows : Fin N → List (Fin N)) : List (Fin N × Fin N) :=
  (List.finRange N).flatMap fun w =>
    (rows w).flatMap fun u => (rows w).map fun v => (u, v)

@[simp] theorem agArcCandidates_mem {N : ℕ} {D : Orientation N}
    {rows : Fin N → List (Fin N)} (h : AgInRows D rows) (u v : Fin N) :
    (u, v) ∈ agArcCandidates rows ↔ u ∈ D.inN v := by
  simp [agArcCandidates, List.mem_flatMap, List.mem_map, h.mem_iff]

@[simp] theorem agTransCandidates_mem {N : ℕ} {D : Orientation N}
    {rows : Fin N → List (Fin N)} (h : AgInRows D rows) (u v : Fin N) :
    (u, v) ∈ agTransCandidates rows ↔ TransLink D u v := by
  simp [agTransCandidates, List.mem_flatMap, List.mem_map, h.mem_iff, TransLink, and_comm]

@[simp] theorem agFratCandidates_mem {N : ℕ} {D : Orientation N}
    {rows : Fin N → List (Fin N)} (h : AgInRows D rows) (u v : Fin N) :
    (u, v) ∈ agFratCandidates rows ↔ FratLink D u v := by
  simp [agFratCandidates, List.mem_flatMap, List.mem_map, h.mem_iff, FratLink]

private theorem agSum_finRange {N : ℕ} (f : Fin N → ℕ) :
    ((List.finRange N).map f).sum = ∑ v, f v := by
  simp [List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def]

/-- Carrying the old arcs scans exactly `arcCount` entries. -/
theorem agArcCandidates_length {N : ℕ} {D : Orientation N}
    {rows : Fin N → List (Fin N)} (h : AgInRows D rows) :
    (agArcCandidates rows).length = arcCount D := by
  simp only [agArcCandidates, List.length_flatMap, List.length_map]
  rw [agSum_finRange]
  exact Finset.sum_congr rfl fun v _ => h.length v

/-- The fraternity loop has exactly the source's sum of squared in-degrees. -/
theorem agFratCandidates_length {N : ℕ} {D : Orientation N}
    {rows : Fin N → List (Fin N)} (h : AgInRows D rows) :
    (agFratCandidates rows).length = fratPairCount D := by
  simp only [agFratCandidates, List.length_flatMap, List.length_map,
    List.map_const', List.sum_replicate, smul_eq_mul]
  rw [agSum_finRange]
  exact Finset.sum_congr rfl fun v _ => by rw [h.length v]

/-- The transitive loop has exactly the source's nested in-list sum. -/
theorem agTransCandidates_length {N : ℕ} {D : Orientation N}
    {rows : Fin N → List (Fin N)} (h : AgInRows D rows) :
    (agTransCandidates rows).length = transPairCount D := by
  simp only [agTransCandidates, List.length_flatMap, List.length_map]
  rw [agSum_finRange]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← h.finset v, List.sum_toFinset]
  · congr 1
    exact List.map_congr_left fun w _ => h.length w
  · exact h.nodup v

/-- The scalar key for an arc `u → v`; division decodes its tail and
remainder decodes its head. This is an address, never a loop bound. -/
def agArcKey {N : ℕ} (p : Fin N × Fin N) : ℕ := (p.1 : ℕ) * N + p.2

theorem agArcKey_lt {N : ℕ} (p : Fin N × Fin N) : agArcKey p < N * N :=
  agPair_lt p.1 p.2

theorem agArcKey_injective {N : ℕ} : Function.Injective (@agArcKey N) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  obtain ⟨hu, hv⟩ := agSplit v.isLt v'.isLt h
  exact Prod.ext (Fin.ext hu) (Fin.ext hv)

/-- Dictionary deduplication preserves the exact meaning of candidate lists. -/
theorem agDictUnion_arcKey_mem {N : ℕ} (ps : List (Fin N × Fin N))
    (p : Fin N × Fin N) :
    agArcKey p ∈ agDictUnion [] (ps.map agArcKey) ↔ p ∈ ps := by
  simp only [agDictUnion_mem, List.not_mem_nil, false_or, List.mem_map]
  constructor
  · rintro ⟨p', hp', he⟩
    exact agArcKey_injective he ▸ hp'
  · exact fun h => ⟨p, h, rfl⟩

/-- Fraternal graph construction removes the diagonal and keeps every
witnessed pair, independently of the order in which witnesses were visited. -/
def agFratEdges {N : ℕ} (rows : Fin N → List (Fin N)) : List (Fin N × Fin N) :=
  (agFratCandidates rows).filter fun p => p.1 != p.2

@[simp] theorem agFratEdges_mem {N : ℕ} {D : Orientation N}
    {rows : Fin N → List (Fin N)} (h : AgInRows D rows) (u v : Fin N) :
    (u, v) ∈ agFratEdges rows ↔ (fratGraph D).Adj u v := by
  simp [agFratEdges, agFratCandidates_mem h, fratGraph_adj, and_comm]

theorem agFratEdges_length_le {N : ℕ} {D : Orientation N}
    {rows : Fin N → List (Fin N)} (h : AgInRows D rows) :
    (agFratEdges rows).length ≤ fratPairCount D := by
  rw [← agFratCandidates_length h]
  exact List.length_filter_le _ _

/-! ## A scan with the sum of the actual per-iteration charges -/

/-- A counted loop whose body has a different proved charge at each position.
This is the sparse nested-loop rule: it sums row lengths instead of replacing
them by a maximum or by the carrier size. -/
theorem agForSum_run {B L : ℕ} (iv lm : String) (body : Com)
    (I : ℕ → Env → Prop) (K : ℕ → ℕ) (hLB : L < B)
    (hbound : ∀ i, i ≤ L → ∀ ρ, I i ρ → ρ.vars lm = L)
    (hstep : ∀ i, i < L → ∀ ρ, I i ρ → ρ.vars iv = i →
      ∃ τ, Run B body ρ τ (K i) ∧ I (i + 1) τ ∧ τ.vars iv = i + 1)
    (σ : Env) (hstart : I 0 (σ.setVar iv 0)) :
    ∃ τ, Run B (.seq (.assign iv (.lit 0))
        (.while (.lt (.var iv) (.var lm)) body)) σ τ
        ((∑ i ∈ Finset.range L, K i) + 4 * L + 6) ∧
      I L τ ∧ τ.vars iv = L := by
  let pref : ℕ → ℕ := fun i => ∑ j ∈ Finset.range i, (K j + 4)
  let J : Env → Prop := fun ρ => ∃ i, i ≤ L ∧ I i ρ ∧ ρ.vars iv = i
  let Φ : Env → ℕ := fun ρ => pref L - pref (ρ.vars iv)
  have hmono : ∀ i, i ≤ L → pref i ≤ pref L := by
    intro i hi
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hi)
  have hdef : ∀ ρ, J ρ → ∃ v, (Cond.lt (.var iv) (.var lm)).evalB B ρ = some v := by
    rintro ρ ⟨i, hi, hI, hiv⟩
    exact ⟨_, evalB_condLt (agEvalVar hiv (by omega))
      (agEvalVar (hbound i hi ρ hI) hLB)⟩
  have hstepJ : ∀ ρ, J ρ →
      (Cond.lt (.var iv) (.var lm)).evalB B ρ = some true →
      ∃ τ K', Run B body ρ τ K' ∧ J τ ∧
        1 + (Cond.lt (.var iv) (.var lm)).size + K' + Φ τ ≤ Φ ρ := by
    rintro ρ ⟨i, hi, hI, hiv⟩ hc
    have he := evalB_condLt (B := B) (agEvalVar hiv (by omega))
      (agEvalVar (hbound i hi ρ hI) hLB)
    have hiL : i < L := by
      rw [hc] at he
      exact of_decide_eq_true (Option.some.inj he).symm
    obtain ⟨τ, hr, hIτ, hiτ⟩ := hstep i hiL ρ hI hiv
    have hpre : pref (i + 1) = pref i + (K i + 4) := Finset.sum_range_succ _ i
    have hp1 := hmono (i + 1) (by omega)
    have hp0 := hmono i hi
    refine ⟨τ, K i, hr, ⟨i + 1, by omega, hIτ, hiτ⟩, ?_⟩
    dsimp only [Φ]
    rw [hiτ, hiv]
    simp only [Cond.size, Expr.size]
    omega
  obtain ⟨τ, K', hr, hJτ, hc, hpay⟩ :=
    Run.while_potential (B := B) J Φ hdef hstepJ
      (σ := σ.setVar iv 0) ⟨0, Nat.zero_le L, hstart, by simp⟩
  obtain ⟨i, hi, hIτ, hivτ⟩ := hJτ
  have hiL : i = L := by
    have he := evalB_condLt (B := B) (agEvalVar hivτ (by omega))
      (agEvalVar (hbound i hi τ hIτ) hLB)
    rw [hc] at he
    have hn := of_decide_eq_false (Option.some.inj he).symm
    omega
  have hIf : I L τ := hiL ▸ hIτ
  have hif : τ.vars iv = L := hivτ.trans hiL
  have hinit : Run B (.assign iv (.lit 0)) σ (σ.setVar iv 0) 2 :=
    Run.assign (evalB_lit (by omega))
  have htotal : pref L = (∑ i ∈ Finset.range L, K i) + 4 * L := by
    simp [pref, Finset.sum_add_distrib, Nat.mul_comm]
  have hΦ0 : Φ (σ.setVar iv 0) = pref L := by simp [Φ, pref]
  have hΦL : Φ τ = 0 := by simp [Φ, hif]
  refine ⟨τ, (hinit.seq hr).mono ?_, hIf, hif⟩
  rw [hΦ0, hΦL, htotal] at hpay
  simp only [Cond.size, Expr.size] at hpay
  omega

/-! ## Reading the actual in-lists -/

/-- Padded compressed-row storage. Only the meaningful offsets and targets
are constrained, so all reservations survive repeated sparse rounds. -/
structure AgCsrRows (o t : String) {N : ℕ} (ns : ℕ)
    (rows : Fin N → List (Fin N)) (off : ℕ → ℕ) (σ : Env) : Prop where
  off_zero : off 0 = 0
  off_step : ∀ v : Fin N, off (v + 1) = off v + (rows v).length
  off_last : off N = ns
  off_len : N + 1 ≤ (σ.arrs o).length
  tgt_len : ns ≤ (σ.arrs t).length
  offsets : ∀ i, i ≤ N → (σ.arrs o).getD i 0 = off i
  targets : ∀ (v : Fin N) (i : ℕ) (hi : i < (rows v).length),
    (σ.arrs t).getD (off v + i) 0 = ((rows v)[i] : ℕ)

theorem AgCsrRows.mono {o t : String} {N ns : ℕ}
    {rows : Fin N → List (Fin N)} {off : ℕ → ℕ} {σ : Env}
    (h : AgCsrRows o t ns rows off σ) {i k : ℕ} (hi : i ≤ k) (hk : k ≤ N) :
    off i ≤ off k := by
  induction k with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact le_rfl
  | succ k ih =>
      by_cases hik : i ≤ k
      · have hstep := h.off_step ⟨k, by omega⟩
        refine le_trans (ih hik (by omega)) ?_
        rw [hstep]
        exact Nat.le_add_right _ _
      · have : i = k + 1 := by omega
        subst i
        exact le_rfl

theorem AgCsrRows.off_le {o t : String} {N ns : ℕ}
    {rows : Fin N → List (Fin N)} {off : ℕ → ℕ} {σ : Env}
    (h : AgCsrRows o t ns rows off σ) {i : ℕ} (hi : i ≤ N) : off i ≤ ns := by
  rw [← h.off_last]
  exact h.mono hi le_rfl

theorem AgCsrRows.row_slot_lt {o t : String} {N ns : ℕ}
    {rows : Fin N → List (Fin N)} {off : ℕ → ℕ} {σ : Env}
    (h : AgCsrRows o t ns rows off σ) (v : Fin N) {i : ℕ}
    (hi : i < (rows v).length) : off v + i < ns := by
  have hstep := h.off_step v
  have hle := h.off_le (show (v : ℕ) + 1 ≤ N by omega)
  omega

theorem AgCsrRows.row_len_le {o t : String} {N ns : ℕ}
    {rows : Fin N → List (Fin N)} {off : ℕ → ℕ} {σ : Env}
    (h : AgCsrRows o t ns rows off σ) (v : Fin N) : (rows v).length ≤ ns := by
  have hstep := h.off_step v
  have hle := h.off_le (show (v : ℕ) + 1 ≤ N by omega)
  omega

theorem AgCsrRows.of_eq {o t : String} {N ns : ℕ}
    {rows : Fin N → List (Fin N)} {off : ℕ → ℕ} {σ τ : Env}
    (h : AgCsrRows o t ns rows off σ)
    (ho : τ.arrs o = σ.arrs o) (ht : τ.arrs t = σ.arrs t) :
    AgCsrRows o t ns rows off τ := by
  refine ⟨h.off_zero, h.off_step, h.off_last, ?_, ?_, ?_, ?_⟩
  · rw [ho]; exact h.off_len
  · rw [ht]; exact h.tgt_len
  · intro i hi; rw [ho]; exact h.offsets i hi
  · intro v i hi; rw [ht]; exact h.targets v i hi

/-- Read position `iv` of the row whose vertex is in `rv`. -/
def agRowGet (o t rv iv : String) : Expr :=
  .get t (.add (.get o (.var rv)) (.var iv))

/-- Read a row element and encode its ordered pair with the fixed endpoint.
The Boolean chooses whether the fixed endpoint is the tail. -/
def agRowKey (o t rv fv iv nN : String) (fixedTail : Bool) : Expr :=
  if fixedTail then .add (.mul (.var fv) (.var nN)) (agRowGet o t rv iv)
  else .add (.mul (agRowGet o t rv iv) (.var nN)) (.var fv)

@[simp] theorem agRowKey_size (o t rv fv iv nN : String) (b : Bool) :
    (agRowKey o t rv fv iv nN b).size = 9 := by cases b <;> rfl

/-- The actual in-list scan, including both offset reads that load its length. -/
def agDictRow (o t ix ky sz rv fv kv tv hv iv lm nN : String)
    (fixedTail : Bool) : Com :=
  .seq (.assign lm (.sub (.get o (.add (.var rv) (.lit 1))) (.get o (.var rv))))
    (agDictEnumerate ix ky sz kv tv hv iv lm (agRowKey o t rv fv iv nN fixedTail))

private theorem agEvalRowGet {B N ns : ℕ} (o t rv iv : String)
    {rows : Fin N → List (Fin N)} {off : ℕ → ℕ} {σ : Env}
    (h : AgCsrRows o t ns rows off σ) (v : Fin N) {i : ℕ}
    (hr : σ.vars rv = v) (hi : σ.vars iv = i) (hiL : i < (rows v).length)
    (hNB : N < B) (hnsB : ns < B) :
    (agRowGet o t rv iv).evalB B σ = some ((rows v)[i] : ℕ) := by
  have hvB : (v : ℕ) < B := lt_trans v.isLt hNB
  have hoB : off v < B := lt_of_le_of_lt (h.off_le (by omega)) hnsB
  have hpB : off v + i < B := lt_trans (h.row_slot_lt v hiL) hnsB
  have hiB : i < B := by omega
  refine agEvalGet (agEvalAdd
    (agEvalGet (agEvalVar hr hvB) (lt_of_lt_of_le (by omega) h.off_len)
      (h.offsets v (by omega)) hoB) (agEvalVar hi hiB) hpB)
    (lt_of_lt_of_le (h.row_slot_lt v hiL) h.tgt_len) (h.targets v i hiL) ?_
  exact lt_trans ((rows v)[i]).isLt hNB

private theorem agEvalRowKey {B N ns U : ℕ} (o t rv fv iv nN : String) (b : Bool)
    {rows : Fin N → List (Fin N)} {off : ℕ → ℕ} {σ : Env}
    (h : AgCsrRows o t ns rows off σ) (v f : Fin N) {i : ℕ}
    (hr : σ.vars rv = v) (hf : σ.vars fv = f) (hi : σ.vars iv = i)
    (hn : σ.vars nN = N) (hiL : i < (rows v).length)
    (hNB : N < B) (hnsB : ns < B) (hNU : N * N ≤ U) (hUB : U < B) :
    (agRowKey o t rv fv iv nN b).evalB B σ =
      some (agArcKey (if b then (f, (rows v)[i]) else ((rows v)[i], f))) := by
  have hfB := lt_trans f.isLt hNB
  have huB := lt_trans ((rows v)[i]).isLt hNB
  have hget := agEvalRowGet o t rv iv h v hr hi hiL hNB hnsB
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, agArcKey]
  · have hp := lt_of_lt_of_le (agArcKey_lt ((rows v)[i], f)) hNU
    dsimp only [agArcKey] at hp
    exact agEvalAdd (agEvalMul hget (agEvalVar hn hNB) (by omega)) (agEvalVar hf hfB) (by omega)
  · have hp := lt_of_lt_of_le (agArcKey_lt (f, (rows v)[i])) hNU
    dsimp only [agArcKey] at hp
    exact agEvalAdd (agEvalMul (agEvalVar hf hfB) (agEvalVar hn hNB) (by omega)) hget (by omega)

set_option maxHeartbeats 800000 in
/-- A concrete compressed in-list scan, at `58 * row.length + 14` steps.
Every candidate key is computed from two current vertices; the scratch
contains no precomputed link or output information. -/
theorem agDictRow_run {B N ns U : ℕ} (o t ix ky sz rv fv kv tv hv iv lm nN : String)
    (b : Bool) (harr : ix ≠ ky)
    (hread : o ≠ ix ∧ o ≠ ky ∧ t ≠ ix ∧ t ≠ ky)
    (hvs : ([nN, rv, fv, sz, kv, tv, hv, iv, lm] : List String).Nodup)
    (hNB : N + 1 < B) (hnsB : ns < B) (hNU : N * N ≤ U) (hUB : U < B)
    (rows : Fin N → List (Fin N)) (off : ℕ → ℕ) (ks : List ℕ) (v f : Fin N)
    (σ : Env) (hC : AgCsrRows o t ns rows off σ) (hD : AgDictSt ix ky sz B U ks σ)
    (hr : σ.vars rv = v) (hf : σ.vars fv = f) (hn : σ.vars nN = N) :
    ∃ τ, Run B (agDictRow o t ix ky sz rv fv kv tv hv iv lm nN b) σ τ
        (58 * (rows v).length + 14) ∧
      AgDictSt ix ky sz B U
        (agDictUnion ks ((rows v).map fun u => agArcKey (if b then (f, u) else (u, f)))) τ ∧
      (∀ y, y ≠ sz → y ≠ kv → y ≠ tv → y ≠ hv → y ≠ iv → y ≠ lm →
        τ.vars y = σ.vars y) ∧
      (∀ a, a ≠ ix → a ≠ ky → τ.arrs a = σ.arrs a) ∧
      (∀ a, (τ.arrs a).length = (σ.arrs a).length) := by
  have hvs6 : ([sz, kv, tv, hv, iv, lm] : List String).Nodup :=
    hvs.sublist (List.drop_sublist 3 [nN, rv, fv, sz, kv, tv, hv, iv, lm])
  have hvs' := hvs
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hvs'
  obtain ⟨⟨hn_r, hn_f, hn_s, hn_k, hn_t, hn_h, hn_i, hn_l⟩,
    ⟨hr_f, hr_s, hr_k, hr_t, hr_h, hr_i, hr_l⟩,
    ⟨hf_s, hf_k, hf_t, hf_h, hf_i, hf_l⟩,
    ⟨hs_k, hs_t, hs_h, hs_i, hs_l⟩,
    ⟨hk_t, hk_h, hk_i, hk_l⟩, ⟨ht_h, ht_i, ht_l⟩,
    ⟨hh_i, hh_l⟩, hi_l⟩ := hvs'
  let xs := (rows v).map fun u => agArcKey (if b then (f, u) else (u, f))
  have hxsL : xs.length = (rows v).length := List.length_map _
  let ρ := σ.setVar lm (rows v).length
  have hlenEval : (Expr.sub (.get o (.add (.var rv) (.lit 1)))
      (.get o (.var rv))).evalB B σ = some (rows v).length := by
    have hv := agEvalVar (B := B) hr (lt_trans v.isLt (show N < B by omega))
    have h1 := agEvalGet (agEvalAdd hv (evalB_lit (by omega)) (by omega))
      (lt_of_lt_of_le (by omega) hC.off_len)
      (hC.offsets (v + 1) (by omega))
      (lt_of_le_of_lt (hC.off_le (by omega)) hnsB)
    have h0 := agEvalGet hv (lt_of_lt_of_le (by omega) hC.off_len)
      (hC.offsets v (by omega)) (lt_of_le_of_lt (hC.off_le (by omega)) hnsB)
    have hs := agEvalSub h1 h0
    rw [hC.off_step v, Nat.add_sub_cancel_left] at hs
    exact hs (lt_of_le_of_lt (hC.row_len_le v) hnsB)
  have hload : Run B (.assign lm (.sub (.get o (.add (.var rv) (.lit 1)))
      (.get o (.var rv)))) σ ρ 8 := Run.assign hlenEval
  have hDρ : AgDictSt ix ky sz B U ks ρ := hD.of_eq rfl rfl (by simp [ρ, hs_l])
  have hxU : ∀ k ∈ xs, k < U := by
    rintro k hk
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hk
    exact lt_of_lt_of_le (agArcKey_lt _) hNU
  have he : ∀ τ : Env,
      (∀ a, a ≠ ix → a ≠ ky → τ.arrs a = ρ.arrs a) →
      (∀ y, y ≠ sz → y ≠ kv → y ≠ tv → y ≠ hv → y ≠ iv →
        τ.vars y = ρ.vars y) → τ.vars iv < xs.length →
      (agRowKey o t rv fv iv nN b).evalB B τ = some (xs.getD (τ.vars iv) 0) := by
    intro τ ha hv hi
    have hCt : AgCsrRows o t ns rows off τ := hC.of_eq
      (ha o hread.1 hread.2.1) (ha t hread.2.2.1 hread.2.2.2)
    have hrt : τ.vars rv = v := by
      rw [hv rv hr_s hr_k hr_t hr_h hr_i]
      simpa [ρ, hr_l] using hr
    have hft : τ.vars fv = f := by
      rw [hv fv hf_s hf_k hf_t hf_h hf_i]
      simpa [ρ, hf_l] using hf
    have hnt : τ.vars nN = N := by
      rw [hv nN hn_s hn_k hn_t hn_h hn_i]
      simpa [ρ, hn_l] using hn
    have hi' : τ.vars iv < (rows v).length := by omega
    rw [getD_eq_getElem hi]
    simp only [xs, List.getElem_map]
    exact agEvalRowKey o t rv fv iv nN b hCt v f hrt hft rfl hnt hi'
      (by omega) hnsB hNU hUB
  obtain ⟨τ, hrun, hDt, hvt, hat, hlt⟩ :=
    agDictEnumerate_run ix ky sz kv tv hv iv lm (agRowKey o t rv fv iv nN b)
      harr hvs6 hUB (by omega) ks xs ρ hDρ (by
        rw [hxsL]; exact lt_of_le_of_lt (hC.row_len_le v) hnsB)
      (by simp [ρ, hxsL]) hxU he
  refine ⟨τ, (hload.seq hrun).mono ?_, hDt, ?_, hat, hlt⟩
  · rw [agRowKey_size, hxsL]
    omega
  · intro y hy1 hy2 hy3 hy4 hy5 hy6
    rw [hvt y hy1 hy2 hy3 hy4 hy5]
    simp [ρ, hy6]

end Lax3Proofs.Prog
