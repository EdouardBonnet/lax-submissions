import Lax3Proofs.SolveMachPrep
import Lax3Proofs.SolveFrameStages
import Lax3Proofs.SolveChainRestrict
import Lax3Proofs.SolveChainCover
import Lax3Proofs.SolveSeamTop

/-!
# F6c13 — the child-building machine pass, discharged

`childLoadParts_of` and `childLoadPartsAll_of` discharge the complete
child-building machine pass.
The supports, profile, colour and isolation stages are composed below
without a residual machine specification. The rank scratch is still zeroed
per child and is charged honestly; the final almost-linear assembly needs
cleanliness threaded through the recursive invariant, as described below.

`SolveMachPrep` named **`ChildLoadPartsAll`** — the per-centre machine
pass that builds the child of centre `u`: from the loop invariant at
`u` (counter at `u`), leave the level-`(j+1)` regions holding the
assembled machine child `machChild` — the isolated restricted CSR, the
`recordProfilesMS` colours, the composite renaming, and the canonical
channel `prepChan` — with the `ProfileTablesMS` witness carried
existentially, the level-`j` cells and regions untouched, and no
reallocation. This file discharges it with a real program:

* **Batch assembly** (§5–§6): zero the rank scratch, copy the centre's
  cluster row off the cover CSR (`ClusterList`), mark the cluster's
  ranks, trace the parent channel's row `u` on the cluster
  (`{u} ∪ ⋃_e column_e(u)` — the F6c12p batch), build the padded
  width-array through the sorted enumeration, and clear the marks.
  The identity to the abstract `batchFn` runs through the pinning
  hypotheses `hpin`/`hpinE` (the parent channel holds the canonical
  `pathSet` lists at the recorded graphs — F7-suppliable, since
  `htabF` is F7's parameter and F6c12p made the target canonical),
  the `genSet` indexing lemma, and the strict-mono uniqueness of the
  sorted enumeration.
* **The five landed stage lifts** (§6e–§7): `restrictCom_specW` (the child
  regions at the `(j+1)` names, the channel filtered write-once),
  `bfsCom_specW` at radius `2R` from the centre's child name,
  `supportsCom_specW` writing the NEW round's column (index `j` —
  the constant-`ℓp` discipline, below) as the canonical gradient
  lists, `profilesCom_specW` at the pre-isolation child (the
  `ProfileTablesMS` witness at `preG`, the campaign's oldest hazard),
  and `isolateCom_specW` writing the final CSR at the `(j+1)` names.
* **The colour write** (§6d): the `(j+1)` colour region at
  `recordProfilesMS S.R childColR Dp Dc` — old colours and the marker
  copied, the profile slots thresholded off the `pd`/`pu` tables the
  profiles stage leaves.

## The constant-`ℓp` discipline

The theorem leaves `ℓp`/`hbf` free, but the machine restrict keeps
the round count and stride of the arena it is run on. The pass
therefore assumes (all F7-suppliable — F7 owns both parameters and
instantiates them `ℓp _ = S.depth`, `hbf _ = 2R + 1`):
`ℓp (j+1) = ℓp j` and `hbf (j+1) = hbf j` on the run levels, room
`j < ℓp j`, and the history length `A.hist.length = j` per admissible
arena. Channel columns are indexed **oldest-first**: column `e < j`
holds `A.hist.reverse[e]`'s recorded list, column `j` is the new round's, and
columns beyond the history are pinned empty (`hpinE`). Under this
discipline the filtered channel lands at unchanged column indices and
the new column is written in place — no stride conversion pass.

## The scratch-cleanliness deviation (flagged)

`restrictCom_specW` requires the rank scratch **clean** (`A.N` zeros),
and the pass's fixed precondition (`CLInv`, which carries no scratch
cleanliness clause) cannot supply it, so the pass zeroes the scratch itself —
`11 * A.N + 6` per centre in `prepK`. Per the design this zeroing is
charged once per node; threading a cleanliness clause through `CLInv`
would remove the per-centre term but touches landed files, so it is
recorded here and priced honestly instead.

## The seam lemmas (F6c12p's mirror, §1)

`cdist_eq_ballDist` and `cdescend_eq_descend`: the abstract canonical
kit (`BatchCanon`) and the machine kit (`Prog.ballDist`,
`Impl.descend`) are formula-identical mirrors — one filter-decidability
transport and one well-founded induction. They are what lets F7 pin
`htabF (j+1)` (stated on `pathList`) to this file's `prepChan` (stated
on the machine kit).
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning Lax67Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.WalkDistance

variable {L n₀ : ℕ}

/-! ## §0 Helpers -/

/-- Reading a cell as `getElem?`, from a `getD` fact and the range. -/
private theorem getElemQ_of_getD {l : List ℕ} {i v : ℕ} (h : i < l.length)
    (hg : l.getD i 0 = v) : l[i]? = some v := by
  rw [List.getElem?_eq_getElem h]
  refine congrArg some ?_
  rw [← hg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- A subset of `Fin N` has at most `N` members. -/
private theorem set_ncard_le_card {N : ℕ} (X : Set (Fin N)) : X.ncard ≤ N :=
  le_of_le_of_eq
    (Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ)
    (by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin])

/-- A child never has an empty carrier: the centre is its own cluster
member. -/
private theorem zero_lt_childN (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : 0 < childN S A π u :=
  (Set.ncard_pos (Set.toFinite _)).mpr ⟨u, self_mem_cluster S A π u⟩

/-- Row-major row disjointness: a cell of row `v` is a cell of row `w`
only for `v = w`. -/
private theorem rowCell_inj {F v w i m : ℕ} (hi : i < F) (hm : m < F)
    (h : v * F + i = w * F + m) : v = w := by
  rcases Nat.lt_trichotomy v w with hvw | hvw | hvw
  · exfalso
    have : (v + 1) * F ≤ w * F := Nat.mul_le_mul_right F hvw
    rw [Nat.succ_mul] at this
    omega
  · exact hvw
  · exfalso
    have : (w + 1) * F ≤ v * F := Nat.mul_le_mul_right F hvw
    rw [Nat.succ_mul] at this
    omega

open Classical in
/-- One centre's row of the cluster CSR, with the next offset and the
`N²` bound: `co[u] = base`, `co[u+1] = base + |X_u|`, the row fits the
membership array, offsets stay `≤ N²`, and entry `t` is the `t`-th
local name's parent name. -/
private theorem clusterRow_read {co cm : String} {N : ℕ}
    {Xf : Fin N → Set (Fin N)} {σ : Env} (h : ClusterCsr co cm Xf σ)
    (u : Fin N) :
    ∃ base : ℕ,
      (σ.arrs co).getD (u : ℕ) 0 = base ∧
      (σ.arrs co).getD ((u : ℕ) + 1) 0 = base + (Xf u).ncard ∧
      base + (Xf u).ncard ≤ (σ.arrs cm).length ∧
      base + (Xf u).ncard ≤ N * N ∧
      N + 1 ≤ (σ.arrs co).length ∧
      ∀ t : ℕ, ∀ ht : t < (Xf u).ncard,
        (σ.arrs cm).getD (base + t) 0
          = (Impl.restrictEmb (Xf u) ⟨t, ht⟩ : ℕ) := by
  obtain ⟨base, hfit, hbase, hrow⟩ := h.read_row u
  obtain ⟨offC, h0, hcoL, hco, hstep, hcmL, hcm⟩ := h
  have hbase' : offC (u : ℕ) = base := by
    rw [← hbase, hco (u : ℕ) (le_of_lt u.2)]
  have hgrow : ∀ i, i ≤ N → offC i ≤ i * N := by
    intro i
    induction i with
    | zero => intro _; simp [h0]
    | succ i ih =>
      intro hiN
      have hci : offC (i + 1) = offC i + (Xf ⟨i, by omega⟩).ncard :=
        hstep ⟨i, by omega⟩
      have h1 := ih (by omega)
      have h2 := set_ncard_le_card (Xf ⟨i, by omega⟩)
      rw [hci, Nat.succ_mul]
      omega
  have hnext : offC ((u : ℕ) + 1) = base + (Xf u).ncard := by
    rw [hstep u, hbase']
  refine ⟨base, hbase, ?_, hfit, ?_, hcoL, hrow⟩
  · rw [hco ((u : ℕ) + 1) u.2, hnext]
  · rw [← hnext]
    have := hgrow ((u : ℕ) + 1) u.2
    have h2 : ((u : ℕ) + 1) * N ≤ N * N := Nat.mul_le_mul_right N u.2
    omega

/-- `Forall₂` respects append. -/
private theorem forall₂_append' {α β : Type*} {R : α → β → Prop} {l₁ l₂ : List α}
    {u₁ u₂ : List β} (h₁ : List.Forall₂ R l₁ u₁)
    (h₂ : List.Forall₂ R l₂ u₂) :
    List.Forall₂ R (l₁ ++ l₂) (u₁ ++ u₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons h hrest ih => exact List.Forall₂.cons h ih

/-- Pairing two maps of one index list under a pointwise relation. -/
private theorem forall₂_map_map {α β γ : Type*} {P : β → γ → Prop} (f : α → β)
    (g : α → γ) : ∀ (l : List α), (∀ x ∈ l, P (f x) (g x)) →
    List.Forall₂ P (l.map f) (l.map g)
  | [], _ => List.Forall₂.nil
  | x :: l, h =>
    List.Forall₂.cons (h x (List.mem_cons_self ..))
      (forall₂_map_map f g l fun z hz => h z (List.mem_cons_of_mem _ hz))

open Classical in
/-- An all-zero prefix, in the `take`/`arrOf` shape the restrict stage
reads. -/
private theorem take_eq_arrOf_zero {l : List ℕ} {N : ℕ} (hN : N ≤ l.length)
    (h : ∀ p, p < N → l.getD p 0 = 0) :
    l.take N = arrOf N (fun _ => 0) := by
  refine List.ext_getElem (by simp [hN]) ?_
  intro i h1 h2
  rw [List.length_take] at h1
  have hiN : i < N := by omega
  have hil : i < l.length := by omega
  have hgd := h i hiN
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil] at hgd
  simp only [Option.getD_some] at hgd
  rw [List.getElem_take]
  have h3 : (arrOf N (fun _ => 0))[i] = 0 := by
    have := getD_arrOf (n := N) (fun _ => 0) hiN
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at this
    simpa using this
  rw [h3]
  exact hgd

/-- The degree sum of a graph on `Fin N` is at most `N²`. -/
private theorem degSum_le_sq {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] : (∑ v : Fin N, G.degree v) ≤ N * N := by
  calc (∑ v : Fin N, G.degree v)
      ≤ ∑ _v : Fin N, N := by
        refine Finset.sum_le_sum ?_
        intro v _
        have h2 := Finset.card_le_card
          (Finset.subset_univ (G.neighborFinset v))
        rw [Finset.card_univ, Fintype.card_fin] at h2
        rw [SimpleGraph.card_neighborFinset_eq_degree] at h2
        exact h2
    _ = N * N := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]

/-- **The channel contract, reindexed** across equal round counts and
word depths: the stride arithmetic is plain and the per-cell lists are
pointwise equal, so the stored region satisfies the contract at either
indexing. -/
private theorem histArr_reindex {aN : String} {N ℓ1 ℓ2 hb1 hb2 : ℕ}
    (hℓ : ℓ2 = ℓ1) (hhb : hb2 = hb1)
    {h1 : Fin N → Fin ℓ1 → List (Fin N)}
    {h2 : Fin N → Fin ℓ2 → List (Fin N)}
    (hfun : ∀ (v : Fin N) (p : Fin ℓ2),
      h2 v p = h1 v ⟨(p : ℕ), by omega⟩)
    {σ : Env} (h : HistArr aN ℓ1 hb1 h1 σ) : HistArr aN ℓ2 hb2 h2 σ := by
  subst hℓ
  subst hhb
  have hfun' : h2 = h1 := by
    funext v p
    rw [hfun v p]
  rw [hfun']
  exact h

/-- A tagged name never equals a plain name of its base's length unless
it is the base itself at level `0` — the one-shot form of `lv_not_mem`
for a single disequality. -/
private theorem lv_ne_lit {s t : String} (hlen : t.length = s.length) (hst : s ≠ t)
    (j : ℕ) : lv s j ≠ t := by
  intro h
  have h1 := congrArg String.length h
  rw [lv_length, hlen] at h1
  have hj : j = 0 := by omega
  subst hj
  exact hst h

open Classical in
/-- Isolation never adds edges: the degree sum only drops. -/
private theorem degSum_deleteVerts_le {N : ℕ} (G : SimpleGraph (Fin N))
    (W : Set (Fin N)) :
    (∑ v : Fin N, (Lax12.UniformQuasiWideness.deleteVerts G W).degree v)
      ≤ ∑ v : Fin N, G.degree v := by
  refine Finset.sum_le_sum fun v _ => ?_
  have hsub : (Lax12.UniformQuasiWideness.deleteVerts G W).neighborFinset v
      ⊆ G.neighborFinset v := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact hw.1
  calc (Lax12.UniformQuasiWideness.deleteVerts G W).degree v
      = ((Lax12.UniformQuasiWideness.deleteVerts G W).neighborFinset v).card :=
        (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
    _ ≤ (G.neighborFinset v).card := Finset.card_le_card hsub
    _ = G.degree v := SimpleGraph.card_neighborFinset_eq_degree _ _

/-- **The windowed contract, recast** across equal round counts and
word depths at fixed carrier, graph, colours and renaming: the region
data is identical cell for cell, so the contract holds at either
indexing (the level boundary's `ℓp (j+1) = ℓp j` transport). -/
private theorem arenaStW_cast {nm : ArenaNames} {Λ n₀ kk ℓ1 ℓ2 hb1 hb2 : ℕ}
    (hℓ : ℓ2 = ℓ1) (hhb : hb2 = hb1)
    {G : SimpleGraph (Fin kk)} {col : Coloring kk Λ} {up : Fin kk ↪ Fin n₀}
    {h1 : Fin kk → Fin ℓ1 → List (Fin kk)}
    {h2 : Fin kk → Fin ℓ2 → List (Fin kk)}
    (hfun : ∀ (v : Fin kk) (p : Fin ℓ2), h2 v p = h1 v ⟨(p : ℕ), by omega⟩)
    {σ : Env}
    (h : ArenaStW nm hb1 (⟨kk, G, col, up, h1⟩ : Impl.MArena Λ n₀ ℓ1) σ) :
    ArenaStW nm hb2 (⟨kk, G, col, up, h2⟩ : Impl.MArena Λ n₀ ℓ2) σ := by
  subst hℓ
  subst hhb
  have h2eq : h2 = h1 := by
    funext v p
    rw [hfun v p]
  rw [h2eq]
  exact h

open Classical in
/-- **Retargeting the colour region**: a windowed arena whose colour
rows move to a fresh region at a new palette — the CSR pair, the
renaming and the channel carry over unchanged, the new colour region
enters by its allocation length and bit facts. -/
private theorem arenaStW_retarget_col {nm : ArenaNames} {Λ1 Λ2 n₀ ℓpc : ℕ} {hb : ℕ}
    {A : Impl.MArena Λ1 n₀ ℓpc} {σ : Env}
    (h : ArenaStW nm hb A σ) (colN : String) (col2 : Coloring A.N Λ2)
    (hnd : ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String).Nodup)
    (hcolN : colN ∉ ([nm.off, nm.tgt, nm.up, nm.hist] : List String))
    (hL : A.N * Λ2 ≤ (σ.arrs colN).length)
    (hbits : ∀ (v : Fin A.N) (c : Fin Λ2),
      (σ.arrs colN).getD ((v : ℕ) * Λ2 + (c : ℕ)) 0
        = if v ∈ col2 c then 1 else 0) :
    ArenaStW { nm with col := colN } hb
      (⟨A.N, A.G, col2, A.up, A.hist⟩ : Impl.MArena Λ2 n₀ ℓpc) σ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or] at hnd
  obtain ⟨⟨hot', hoc, hou, hoh⟩, ⟨htc, htu, hth⟩, ⟨hcu, hch⟩, huh, -⟩ := hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hcolN
  obtain ⟨hcolN_o, hcolN_t, hcolN_u, hcolN_h⟩ := hcolN
  set ns := σ.vars nm.nS with hns_def
  set ws1 := arenaWs nm Λ1 ℓpc hb A.N ns with hws1_def
  set ws2 := arenaWs { nm with col := colN } Λ2 ℓpc hb A.N ns with hws2_def
  -- the new assignment's five values
  have hw2_off : ws2 nm.off = some (A.N + 1) := arenaWs_off
  have hw2_tgt : ws2 nm.tgt = some ns := arenaWs_tgt (Ne.symm hot')
  have hw2_col : ws2 colN = some (A.N * Λ2) :=
    arenaWs_col (nm := { nm with col := colN }) hcolN_o hcolN_t
  have hw2_up : ws2 nm.up = some A.N :=
    arenaWs_up (nm := { nm with col := colN }) (Ne.symm hou) (Ne.symm htu)
      (Ne.symm hcolN_u)
  have hw2_hist : ws2 nm.hist = some (A.N * ℓpc * (hb + 1)) :=
    arenaWs_hist (nm := { nm with col := colN }) (Ne.symm hoh) (Ne.symm hth)
      (Ne.symm hcolN_h) (Ne.symm huh)
  -- the old assignment's matching values
  have hw1_off : ws1 nm.off = some (A.N + 1) := arenaWs_off
  have hw1_tgt : ws1 nm.tgt = some ns := arenaWs_tgt (Ne.symm hot')
  have hw1_up : ws1 nm.up = some A.N :=
    arenaWs_up (Ne.symm hou) (Ne.symm htu) (Ne.symm hcu)
  have hw1_hist : ws1 nm.hist = some (A.N * ℓpc * (hb + 1)) :=
    arenaWs_hist (Ne.symm hoh) (Ne.symm hth) (Ne.symm hch) (Ne.symm huh)
  have hfit2 : FitsW ws2 σ := by
    intro b m hbm
    rcases arenaWs_some_elim hbm with rfl | rfl | h3 | rfl | rfl
    · rw [hw2_off] at hbm
      cases hbm
      exact h.fits _ _ hw1_off
    · rw [hw2_tgt] at hbm
      cases hbm
      exact h.fits _ _ hw1_tgt
    · rw [show ({ nm with col := colN } : ArenaNames).col = colN from rfl]
        at h3
      subst h3
      rw [hw2_col] at hbm
      cases hbm
      exact hL
    · rw [hw2_up] at hbm
      cases hbm
      exact h.fits _ _ hw1_up
    · rw [hw2_hist] at hbm
      cases hbm
      exact h.fits _ _ hw1_hist
  refine ⟨hfit2, ?_⟩
  have htr : ∀ (b : String), ws2 b = ws1 b →
      (winA ws2 σ).arrs b = (winA ws1 σ).arrs b :=
    fun b hb2 => arrs_winA_congr hb2 σ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the carrier cell
    show σ.vars nm.nN = A.N
    exact h.st.n_eq
  · -- the CSR pair
    refine graphCsr_of_eq h.st.csr ?_ ?_
    · exact htr _ (hw2_off.trans hw1_off.symm)
    · exact htr _ (hw2_tgt.trans hw1_tgt.symm)
  · -- the new colour region
    constructor
    · exact length_arrs_winA hw2_col hL
    · intro v c
      have hpos : (v : ℕ) * Λ2 + (c : ℕ) < A.N * Λ2 := by
        have h1 : (v : ℕ) * Λ2 + (c : ℕ) < ((v : ℕ) + 1) * Λ2 := by
          rw [Nat.succ_mul]
          omega
        have h2 : ((v : ℕ) + 1) * Λ2 ≤ A.N * Λ2 :=
          Nat.mul_le_mul_right Λ2 v.2
        omega
      rw [arrs_winA_some hw2_col, getD_take_of_lt hpos]
      exact hbits v c
  · -- the renaming
    have heq := htr _ (hw2_up.trans hw1_up.symm)
    exact ⟨by rw [heq]; exact h.st.up.1, fun v => by rw [heq]; exact h.st.up.2 v⟩
  · -- the channel
    have heq := htr _ (hw2_hist.trans hw1_hist.symm)
    refine ⟨by rw [heq]; exact h.st.hist.1, fun v p => ?_⟩
    obtain ⟨h1, h2, h3⟩ := h.st.hist.2 v p
    exact ⟨h1, by rw [heq]; exact h2, fun i hi => by rw [heq]; exact h3 i hi⟩

/-! ## §1 The seam lemmas: the F6c12p kit and the machine kit are one

`BatchCanon.cdist`/`cdescend` (the abstract canonical batch kit) and
`Prog.ballDist`/`Impl.descend` (the machine layer) are
formula-identical; these are the transports F7 uses to pin the
canonical `htabF` to this file's machine channel. -/

open Classical in
/-- The canonical truncated distance tables agree: `BatchCanon.cdist`
IS `Prog.ballDist` at `Fin N`. -/
private theorem cdist_eq_ballDist {N : ℕ} (H : SimpleGraph (Fin N)) (s : Fin N)
    (d : ℕ) : Lax3Proofs.BatchCanon.cdist H s d = ballDist H s d := by
  funext v
  rw [Lax3Proofs.BatchCanon.cdist, ballDist]

open Classical in
/-- The parent candidate sets agree (a filter-decidability
transport). -/
private theorem cparents_eq_parents {N : ℕ} (H : SimpleGraph (Fin N))
    [DecidableRel H.Adj] (D : Fin N → ℕ) (v : Fin N) :
    Lax3Proofs.BatchCanon.cparents H D v = Impl.parents H D v := by
  ext x
  simp [Lax3Proofs.BatchCanon.cparents, Impl.parents]

open Classical in
/-- The canonical gradient walks agree: `BatchCanon.cdescend` IS
`Impl.descend` at `Fin N` — one well-founded induction down the
distance gradient. -/
private theorem cdescend_eq_descend {N : ℕ} (H : SimpleGraph (Fin N))
    [DecidableRel H.Adj] (D : Fin N → ℕ) (v : Fin N) :
    Lax3Proofs.BatchCanon.cdescend H D v = Impl.descend H D v := by
  have hpar := cparents_eq_parents H D v
  by_cases h : (Impl.parents H D v).Nonempty
  · have h' : (Lax3Proofs.BatchCanon.cparents H D v).Nonempty := by
      rw [hpar]; exact h
    have hmin : (Lax3Proofs.BatchCanon.cparents H D v).min' h'
        = (Impl.parents H D v).min' h := by
      simp only [hpar]
    conv_lhs => rw [Lax3Proofs.BatchCanon.cdescend]
    conv_rhs => rw [Impl.descend]
    rw [dif_pos h', dif_pos h, hmin]
    exact congrArg _ (cdescend_eq_descend H D ((Impl.parents H D v).min' h))
  · have h' : ¬ (Lax3Proofs.BatchCanon.cparents H D v).Nonempty := by
      rw [hpar]; exact h
    conv_lhs => rw [Lax3Proofs.BatchCanon.cdescend]
    conv_rhs => rw [Impl.descend]
    rw [dif_neg h', dif_neg h]
termination_by D v
decreasing_by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2.2

/-! ## §2 The canonical channel family `prepChan`

The child's per-round column family, canonically (the shape
`descendTab` had, at the F6c12p objects), oldest-first: column
`e < ℓp j` other than `j` holds the parent's pinned round-`e` list
filtered to the cluster and renamed through the sorted compaction
(write-once-filter-down — `Impl.MArena.restrict`'s own filterMap);
column `j` (the new round) holds the canonical gradient list of the
canonical `2R`-ball table from the centre's child name in `preG`;
columns beyond hold nothing. `htabF (j+1) (childArena …) = prepChan …`
is F7's seam (`hhtab`), reachable from the canonical `htabF` through
`histGraph_eq_map`, `BatchCanon.pathList_map` down the strict-mono
`up` chain, and §1's seam lemmas. -/

open Classical in
/-- The canonical channel family the pass stores (module docstring). -/
noncomputable def prepChan (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N) :
    Fin (childN S A ((ord A.N A.G).order) u) → Fin (ℓp (j + 1)) →
      List (Fin (childN S A ((ord A.N A.G).order) u)) :=
  fun a e =>
    if (e : ℕ) = j then
      descendCol (preG S A ((ord A.N A.G).order) u)
        (ballDist (preG S A ((ord A.N A.G).order) u)
          (centreChild S A ((ord A.N A.G).order) u) (2 * S.R))
        (2 * S.R) a
    else if h : (e : ℕ) < ℓp j then
      (htabF j A
          (Impl.restrictEmb (cluster S A ((ord A.N A.G).order) u) a)
          ⟨(e : ℕ), h⟩).filterMap
        (Impl.toLocal (cluster S A ((ord A.N A.G).order) u))
    else []

open Classical in
theorem prepDescendCol_eq_pathList {N : ℕ} (G : SimpleGraph (Fin N))
    (s : Fin N) (d : ℕ) (v : Fin N) :
    descendCol G (ballDist G s d) d v = Lax3Proofs.BatchCanon.pathList G d s v := by
  have hiff : ballDist G s d v ≤ d ↔ WithinDist G d s v :=
    ((ballDist_ballTable G s d) v d le_rfl).trans mem_ball
  rw [descendCol, Lax3Proofs.BatchCanon.pathList, cdist_eq_ballDist]
  rw [← cdescend_eq_descend]
  exact if_congr hiff rfl rfl
open Classical in
private theorem prepMemFilterMapLocal {N : ℕ} (X : Set (Fin N))
    (l : List (Fin N)) (z : Fin X.ncard) :
    z ∈ l.filterMap (Impl.toLocal X) ↔ Impl.restrictEmb X z ∈ l := by
  have hm : ∀ l' : List (Fin X.ncard), z ∈ l' ↔
      Impl.restrictEmb X z ∈ l'.map (Impl.restrictEmb X) := by
    intro l'
    constructor
    · intro hz; exact List.mem_map.mpr ⟨z, hz, rfl⟩
    · rintro hz
      obtain ⟨a, ha, h⟩ := List.mem_map.mp hz
      exact (Impl.restrictEmb X).injective h ▸ ha
  rw [hm, Impl.map_restrictEmb_filterMap_toLocal, List.mem_filter]
  simp

open Classical in
/-- The new column uses the newly recorded graph at root names. -/
theorem prepChan_new_pin (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N)
    (hmono : StrictMono A.up) (hj : j < ℓp (j + 1))
    (v z : Fin (childN S A ((ord A.N A.G).order) u)) :
    z ∈ prepChan S ord ℓp htabF j A u v ⟨j, hj⟩ ↔
      (childArena S A ((ord A.N A.G).order) u).up z ∈
        Lax3Proofs.SplitterWin.pathSet
          (histGraph S A ((ord A.N A.G).order) u) (2 * S.R) (A.up u)
          ((childArena S A ((ord A.N A.G).order) u).up v) := by
  let π := (ord A.N A.G).order
  let f := (childArena S A π u).up
  have hcentre : f (centreChild S A π u) = A.up u := by
    change A.up ((childEquiv S A π u) ((childEquiv S A π u).symm
      ⟨u, self_mem_cluster S A π u⟩) : Fin A.N) = A.up u
    rw [Equiv.apply_symm_apply]
  have hmap : histGraph S A π u = (preG S A π u).map f := histGraph_eq_map S A π u
  change z ∈ prepChan S ord ℓp htabF j A u v ⟨j, hj⟩ ↔
    f z ∈ Lax3Proofs.BatchCanon.pathList (histGraph S A π u) (2 * S.R) (A.up u) (f v)
  rw [prepChan, if_pos rfl, prepDescendCol_eq_pathList, hmap, ← hcentre,
    Lax3Proofs.BatchCanon.pathList_map f (childArena_up_strictMono S A π u hmono)]
  constructor
  · intro hz; exact List.mem_map.mpr ⟨z, hz, rfl⟩
  · intro hz
    obtain ⟨a, ha, h⟩ := List.mem_map.mp hz
    exact f.injective h ▸ ha

open Classical in
/-- An old column retains its history index under restriction. -/
theorem prepChan_old_pin (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N)
    (hLen : A.hist.length = j) (hlp : ℓp (j + 1) = ℓp j)
    (hpin : ∀ (v : Fin A.N) (e : Fin (ℓp j)) (he : (e : ℕ) < A.hist.length)
      (z : Fin A.N), z ∈ htabF j A v e ↔
        (A.up z) ∈ Lax3Proofs.SplitterWin.pathSet
          (A.hist.reverse[(e : ℕ)]'(by simpa using he)).2 (2 * S.R)
          (A.hist.reverse[(e : ℕ)]'(by simpa using he)).1 (A.up v))
    (v z : Fin (childN S A ((ord A.N A.G).order) u))
    (e : Fin (ℓp (j + 1))) (he : (e : ℕ) < j) :
    z ∈ prepChan S ord ℓp htabF j A u v e ↔
      (childArena S A ((ord A.N A.G).order) u).up z ∈
        Lax3Proofs.SplitterWin.pathSet
          ((childArena S A ((ord A.N A.G).order) u).hist.reverse[(e : ℕ)]'(by
            simp only [childArena, List.length_reverse, List.length_cons, hLen]; omega)).2
          (2 * S.R)
          ((childArena S A ((ord A.N A.G).order) u).hist.reverse[(e : ℕ)]'(by
            simp only [childArena, List.length_reverse, List.length_cons, hLen]; omega)).1
          ((childArena S A ((ord A.N A.G).order) u).up v) := by
  have hel : (e : ℕ) < ℓp j := by rw [← hlp]; exact e.2
  have heh : (e : ℕ) < A.hist.length := by omega
  have hrev : ((childArena S A ((ord A.N A.G).order) u).hist.reverse[(e : ℕ)]'(by
      simp only [childArena, List.length_reverse, List.length_cons, hLen]; omega)) =
      A.hist.reverse[(e : ℕ)]'(by simpa using heh) := by
    simp only [childArena, List.reverse_cons]
    exact List.getElem_append_left (by simpa using heh)
  rw [prepChan, if_neg (by omega), dif_pos hel]
  refine (prepMemFilterMapLocal (cluster S A ((ord A.N A.G).order) u)
    (htabF j A (Impl.restrictEmb _ v) ⟨(e : ℕ), hel⟩) z).trans ?_
  rw [hrev]
  exact hpin (Impl.restrictEmb _ v) ⟨(e : ℕ), hel⟩ heh (Impl.restrictEmb _ z)

/-! ## §3 The batch, from the pinned channel -/

/-- Membership in `genSet`, by round index. -/
private theorem mem_genSet_iff {n : ℕ} {r : ℕ}
    (rounds : List (Lax3Proofs.SplitterWin.Round n)) (v x : Fin n) :
    x ∈ Lax3Proofs.SplitterWin.genSet r rounds v ↔
      x = v ∨ ∃ i : ℕ, ∃ hi : i < rounds.length,
        x ∈ Lax3Proofs.SplitterWin.pathSet (rounds[i]).2 r (rounds[i]).1 v := by
  induction rounds with
  | nil =>
    simp only [Lax3Proofs.SplitterWin.genSet, Set.mem_singleton_iff,
      List.length_nil]
    constructor
    · exact fun h => Or.inl h
    · rintro (h | ⟨i, hi, -⟩)
      · exact h
      · omega
  | cons e rest ih =>
    simp only [Lax3Proofs.SplitterWin.genSet, Set.mem_union, ih,
      List.length_cons]
    constructor
    · rintro (h | h | ⟨i, hi, h⟩)
      · exact Or.inr ⟨0, by omega, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨i + 1, by omega, by
          simpa using h⟩
    · rintro (h | ⟨i, hi, h⟩)
      · exact Or.inr (Or.inl h)
      · cases i with
        | zero => exact Or.inl h
        | succ i =>
          refine Or.inr (Or.inr ⟨i, by omega, by simpa using h⟩)

private theorem prepMemGenSetList {n r : ℕ}
    (rounds : List (Lax3Proofs.SplitterWin.Round n)) (v x : Fin n) :
    x ∈ Lax3Proofs.SplitterWin.genSet r rounds v ↔
      x = v ∨ ∃ e ∈ rounds, x ∈ Lax3Proofs.SplitterWin.pathSet e.2 r e.1 v := by
  rw [mem_genSet_iff]
  constructor
  · rintro (h | ⟨i, hi, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rounds[i], List.getElem_mem hi, h⟩
  · rintro (h | ⟨e, he, h⟩)
    · exact Or.inl h
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
      exact Or.inr ⟨i, hi, h⟩
private theorem prepGenSet_reverse {n r : ℕ}
    (rounds : List (Lax3Proofs.SplitterWin.Round n)) (v : Fin n) :
    Lax3Proofs.SplitterWin.genSet r rounds.reverse v =
      Lax3Proofs.SplitterWin.genSet r rounds v := by
  ext x
  simp only [prepMemGenSetList, List.mem_reverse]

open Classical in
/-- The stored oldest-first channel marks exactly the abstract batch. -/
private theorem marks_eq_batchSet (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    {ℓpj : ℕ} (htab : Fin A.N → Fin ℓpj → List (Fin A.N))
    (hpin : ∀ (e : Fin ℓpj) (he : (e : ℕ) < A.hist.length) (z : Fin A.N),
      z ∈ htab u e ↔
        (A.up z) ∈ Lax3Proofs.SplitterWin.pathSet
          (A.hist.reverse[(e : ℕ)]'(by simpa using he)).2 (2 * S.R)
          (A.hist.reverse[(e : ℕ)]'(by simpa using he)).1 (A.up u))
    (hpinE : ∀ e : Fin ℓpj, A.hist.length ≤ (e : ℕ) → htab u e = [])
    (hlen : A.hist.length ≤ ℓpj) :
    {t : Fin (childN S A π u) |
        Impl.restrictEmb (cluster S A π u) t = u ∨
          ∃ e : Fin ℓpj, Impl.restrictEmb (cluster S A π u) t ∈ htab u e}
      = batchSet S A π u := by
  ext t
  have hemb : ∀ a : Fin (childN S A π u),
      ((childEquiv S A π u) a : Fin A.N)
        = Impl.restrictEmb (cluster S A π u) a := fun a => rfl
  show (Impl.restrictEmb (cluster S A π u) t = u ∨
      ∃ e : Fin ℓpj, Impl.restrictEmb (cluster S A π u) t ∈ htab u e) ↔
    A.up ((childEquiv S A π u) t : Fin A.N) ∈ batchRoot S A u
  rw [hemb, batchRoot, ← prepGenSet_reverse, mem_genSet_iff]
  constructor
  · rintro (h | ⟨e, he⟩)
    · exact Or.inl (congrArg A.up h)
    · by_cases hel : (e : ℕ) < A.hist.length
      · exact Or.inr ⟨(e : ℕ), by simpa using hel,
          (hpin e hel (Impl.restrictEmb (cluster S A π u) t)).mp he⟩
      · rw [hpinE e (by omega)] at he
        cases he
  · rintro (h | ⟨i, hi, h⟩)
    · exact Or.inl (A.up.injective h)
    · have hi' : i < A.hist.length := by simpa using hi
      refine Or.inr ⟨⟨i, lt_of_lt_of_le hi' hlen⟩, ?_⟩
      exact (hpin ⟨i, lt_of_lt_of_le hi' hlen⟩ hi'
        (Impl.restrictEmb (cluster S A π u) t)).mpr h

/-! ## §4 The sorted enumeration, characterized -/

/-- Two strictly monotone `Fin`-enumerations with the same range are
equal (the least element is forced, and so on up). -/
private theorem strictMono_fin_eq {m k : ℕ} {f g : Fin m → Fin k}
    (hf : StrictMono f) (hg : StrictMono g)
    (hr : Set.range f = Set.range g) : f = g := by
  induction m with
  | zero => funext i; exact absurd i.2 (Nat.not_lt_zero _)
  | succ m ih =>
    -- both restrict to `Fin m` after the shared least element
    have h0 : f 0 = g 0 := by
      -- each range's least element is the image of `0`
      have hmemf : f 0 ∈ Set.range g := by rw [← hr]; exact ⟨0, rfl⟩
      have hmemg : g 0 ∈ Set.range f := by rw [hr]; exact ⟨0, rfl⟩
      obtain ⟨i, hi⟩ := hmemf
      obtain ⟨i', hi'⟩ := hmemg
      have h1 : g 0 ≤ g i := hg.monotone (Fin.zero_le i)
      have h2 : f 0 ≤ f i' := hf.monotone (Fin.zero_le i')
      rw [hi] at h1
      rw [hi'] at h2
      exact le_antisymm h2 h1
    -- the tails
    have hsucc : (fun i : Fin m => f i.succ) = fun i : Fin m => g i.succ := by
      refine ih (fun a b hab => hf (by simpa using hab))
        (fun a b hab => hg (by simpa using hab)) ?_
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        have hx : f i.succ ∈ Set.range g := by rw [← hr]; exact ⟨i.succ, rfl⟩
        obtain ⟨j, hj⟩ := hx
        have hgt : g 0 < f i.succ := by
          rw [← h0]
          exact hf (Fin.succ_pos i)
        have hj0 : 0 < (j : ℕ) := by
          rcases Nat.eq_zero_or_pos (j : ℕ) with hz | hp
          · exfalso
            have hj00 : j = 0 := Fin.ext hz
            rw [hj00] at hj
            rw [hj] at hgt
            exact lt_irrefl _ hgt
          · exact hp
        have hjm : (j : ℕ) < m + 1 := j.2
        refine ⟨⟨(j : ℕ) - 1, by omega⟩, ?_⟩
        have hsucc : (⟨(j : ℕ) - 1, by omega⟩ : Fin m).succ = j := by
          ext
          simp only [Fin.val_succ]
          omega
        show g (⟨(j : ℕ) - 1, by omega⟩ : Fin m).succ = f i.succ
        rw [hsucc, hj]
      · rintro ⟨i, rfl⟩
        have hx : g i.succ ∈ Set.range f := by rw [hr]; exact ⟨i.succ, rfl⟩
        obtain ⟨j, hj⟩ := hx
        have hgt : f 0 < g i.succ := by
          rw [h0]
          exact hg (Fin.succ_pos i)
        have hj0 : 0 < (j : ℕ) := by
          rcases Nat.eq_zero_or_pos (j : ℕ) with hz | hp
          · exfalso
            have hj00 : j = 0 := Fin.ext hz
            rw [hj00] at hj
            rw [hj] at hgt
            exact lt_irrefl _ hgt
          · exact hp
        have hjm : (j : ℕ) < m + 1 := j.2
        refine ⟨⟨(j : ℕ) - 1, by omega⟩, ?_⟩
        have hsucc : (⟨(j : ℕ) - 1, by omega⟩ : Fin m).succ = j := by
          ext
          simp only [Fin.val_succ]
          omega
        show f (⟨(j : ℕ) - 1, by omega⟩ : Fin m).succ = g i.succ
        rw [hsucc, hj]
    funext i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · exact h0
    · exact congrFun hsucc i'

open Classical in
/-- **The scan is the sorted enumeration**: a strictly increasing
sequence of `m = |X|` cell values that lies in `X` and exhausts it is
exactly `setEquiv`'s ascending enumeration. -/
private theorem scan_eq_setEquiv {k : ℕ} (X : Set (Fin k)) (w : ℕ → ℕ)
    (hbound : ∀ p, p < X.ncard → w p < k)
    (hmono : ∀ p q, p < q → q < X.ncard → w p < w q)
    (hmem : ∀ p, ∀ hp : p < X.ncard, (⟨w p, hbound p hp⟩ : Fin k) ∈ X)
    (hcompl : ∀ x ∈ X, ∃ p, ∃ hp : p < X.ncard, w p = (x : ℕ)) :
    ∀ p, ∀ hp : p < X.ncard,
      ((setEquiv X ⟨p, hp⟩ : ↥X) : Fin k) = ⟨w p, hbound p hp⟩ := by
  have hf : StrictMono fun a : Fin X.ncard => ((setEquiv X a : ↥X) : Fin k) :=
    setEquiv_coe_strictMono X
  have hg : StrictMono fun a : Fin X.ncard =>
      (⟨w (a : ℕ), hbound _ a.2⟩ : Fin k) := by
    intro a b hab
    exact hmono _ _ hab b.2
  have hrf : Set.range (fun a : Fin X.ncard => ((setEquiv X a : ↥X) : Fin k))
      = X := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (setEquiv X i).2
    · intro hx
      refine ⟨(setEquiv X).symm ⟨x, hx⟩, ?_⟩
      show ((setEquiv X) ((setEquiv X).symm ⟨x, hx⟩) : Fin k) = x
      rw [Equiv.apply_symm_apply]
  have hrg : Set.range (fun a : Fin X.ncard =>
      (⟨w (a : ℕ), hbound _ a.2⟩ : Fin k)) = X := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact hmem _ i.2
    · intro hx
      obtain ⟨p, hp, hw⟩ := hcompl x hx
      exact ⟨⟨p, hp⟩, by
        ext
        exact hw⟩
  have := strictMono_fin_eq hf hg (by rw [hrf, hrg])
  intro p hp
  exact congrFun this ⟨p, hp⟩

/-! ## §5 The pass's names and programs

All scratch names are literal (bases of length 4, so the `lv` name
mechanism separates them from every level's regions by `decide`-level
facts); the three profile-table families are `lv`-tagged fresh bases.
The pre-isolation child regions live in scratch (`cp.o`/`cp.t` the
CSR, `cp.c` the colours at the parent palette, `cp.m` the slot-count
cell); the composite renaming, the channel and the final colours/CSR
land directly in the `(j+1)` regions. -/

/-- The pass's scratch array names (fixed). -/
def prepArrays : List String :=
  ["cp.l", "cp.r", "cp.b", "cp.w", "cp.o", "cp.t", "cp.c", "cp.d",
    "cp.p", "cp.x", "cp.v"]

/-- The pass's own scratch scalar names (the routines' pools ride on
top). -/
def prepOwnScalars : List String :=
  ["cp.s", "cp.n", "cp.i", "cp.j", "cp.k", "cp.y", "cp.e", "cp.g",
    "cp.z", "cp.m"]

/-- Every scalar the pass may write, short of the two `(j+1)` cells. -/
def prepScalars : List String :=
  prepOwnScalars ++ rsScalars ++ bfScalars ++ spScalars ++ profScalars

/-- The restrict stage's output names: the pre-isolation CSR and
colours in scratch, the renaming/channel (and the untouched table slot)
at the `(j+1)` names, the slot count in `cp.m`. -/
def prepNmR (j : ℕ) : ArenaNames :=
  ⟨(arenaNames (j + 1)).nN, "cp.m", "cp.o", "cp.t", "cp.c",
    (arenaNames (j + 1)).up, (arenaNames (j + 1)).hist,
    (arenaNames (j + 1)).tab⟩

/-- The isolate stage's input names: the final colours at the `(j+1)`
colour region, the pre-isolation CSR still in scratch. -/
def prepNmI (j : ℕ) : ArenaNames :=
  ⟨(arenaNames (j + 1)).nN, "cp.m", "cp.o", "cp.t",
    (arenaNames (j + 1)).col, (arenaNames (j + 1)).up,
    (arenaNames (j + 1)).hist, (arenaNames (j + 1)).tab⟩

/-- The profiles stage's name bundle. -/
def prepPN (j : ℕ) : ProfNames :=
  ⟨"cp.o", "cp.t", "cp.c", "cp.w", "cp.x", "cp.v",
    (arenaNames (j + 1)).nN, "cp.m", lv "cq.d", lv "cq.v", lv "cq.u"⟩

/-- The isolate stage's output retarget lands on the canonical `(j+1)`
family on the nose. -/
theorem prepNmI_update (j : ℕ) :
    ({ (prepNmI j) with
        off := (arenaNames (j + 1)).off
        tgt := (arenaNames (j + 1)).tgt
        nS := (arenaNames (j + 1)).nS } : ArenaNames)
      = arenaNames (j + 1) := rfl

/-- §5a — the centre's row bounds off the cover CSR: the row base into
`cp.s`, the cluster size into `cp.n`. -/
def prepRowBoundsCom (coj ctr : String) : Com :=
  .seq (.assign "cp.s" (.get coj (.var ctr)))
    (.assign "cp.n"
      (.sub (.get coj (.add (.var ctr) (.lit 1))) (.var "cp.s")))

/-- §5b — zero the rank scratch on the carrier prefix (the
cleanliness `restrictCom` assumes; module docstring on the cost). -/
def prepZeroCom (nNj : String) : Com :=
  .seq (.assign "cp.i" (.lit 0))
    (.while (.lt (.var "cp.i") (.var nNj))
      (.seq (.store "cp.r" (.var "cp.i") (.lit 0))
        (.assign "cp.i" (.add (.var "cp.i") (.lit 1)))))

/-- §5c — one pass over the cluster row: copy the row into the
cluster-list scratch, mark the member's rank (+1) on the rank scratch,
zero the member's batch bit. -/
def prepRowCom (cmj : String) : Com :=
  .seq (.assign "cp.i" (.lit 0))
    (.while (.lt (.var "cp.i") (.var "cp.n"))
      (.seq (.store "cp.l" (.var "cp.i")
          (.get cmj (.add (.var "cp.s") (.var "cp.i"))))
        (.seq (.store "cp.r" (.get cmj (.add (.var "cp.s") (.var "cp.i")))
            (.add (.var "cp.i") (.lit 1)))
          (.seq (.store "cp.b" (.var "cp.i") (.lit 0))
            (.assign "cp.i" (.add (.var "cp.i") (.lit 1)))))))

/-- §5d — the centre's own child name off the rank scratch, and its
batch bit. -/
def prepCentreCom (ctr : String) : Com :=
  .seq (.assign "cp.z" (.sub (.get "cp.r" (.var ctr)) (.lit 1)))
    (.store "cp.b" (.var "cp.z") (.lit 1))

/-- §5e — the batch trace: scan the parent channel's row `u` (all `ℓp j`
columns), and set the batch bit of every cluster member named. -/
def prepBatchCom (histj ctr : String) (lpj hbj : ℕ) : Com :=
  .seq (.assign "cp.e" (.lit lpj))
    (.seq (.assign "cp.i" (.lit 0))
      (.while (.lt (.var "cp.i") (.var "cp.e"))
        (.seq (.assign "cp.k"
            (.mul (.add (.mul (.var ctr) (.lit lpj)) (.var "cp.i"))
              (.lit (hbj + 1))))
          (.seq (.assign "cp.y" (.get histj (.var "cp.k")))
            (.seq (.seq (.assign "cp.j" (.lit 0))
                (.while (.lt (.var "cp.j") (.var "cp.y"))
                  (.seq (.assign "cp.g"
                      (.get histj
                        (.add (.add (.var "cp.k") (.lit 1)) (.var "cp.j"))))
                    (.seq (.ite (.lt (.lit 0) (.get "cp.r" (.var "cp.g")))
                        (.store "cp.b"
                          (.sub (.get "cp.r" (.var "cp.g")) (.lit 1))
                          (.lit 1))
                        .skip)
                      (.assign "cp.j" (.add (.var "cp.j") (.lit 1)))))))
              (.assign "cp.i" (.add (.var "cp.i") (.lit 1))))))))

/-- §5f — the padded width-array: scan the batch bits in ascending
order collecting the set members, then pad with the centre's child name
to exactly the width. -/
def prepWidthCom (width : ℕ) : Com :=
  .seq (.assign "cp.k" (.lit 0))
    (.seq (.seq (.assign "cp.i" (.lit 0))
        (.while (.lt (.var "cp.i") (.var "cp.n"))
          (.seq (.ite (.eq (.get "cp.b" (.var "cp.i")) (.lit 1))
              (.seq (.store "cp.w" (.var "cp.k") (.var "cp.i"))
                (.assign "cp.k" (.add (.var "cp.k") (.lit 1))))
              .skip)
            (.assign "cp.i" (.add (.var "cp.i") (.lit 1))))))
      (.seq (.assign "cp.e" (.lit width))
        (.while (.lt (.var "cp.k") (.var "cp.e"))
          (.seq (.store "cp.w" (.var "cp.k") (.var "cp.z"))
            (.assign "cp.k" (.add (.var "cp.k") (.lit 1)))))))

/-- §5g — clear the marks (the rank scratch is all-zero again for the
restrict stage). -/
def prepClearCom (cmj : String) : Com :=
  .seq (.assign "cp.i" (.lit 0))
    (.while (.lt (.var "cp.i") (.var "cp.n"))
      (.seq (.store "cp.r" (.get cmj (.add (.var "cp.s") (.var "cp.i")))
          (.lit 0))
        (.assign "cp.i" (.add (.var "cp.i") (.lit 1)))))

/-- §5h — the restrict stage, with its four input cells. -/
def prepRestrictCom (nmP : ArenaNames) (j : ℕ) (Λj lpj hbj : ℕ) : Com :=
  .seq (.assign "rs.k" (.var "cp.n"))
    (.seq (.assign "rs.l" (.lit Λj))
      (.seq (.assign "rs.p" (.lit lpj))
        (.seq (.assign "rs.h" (.lit hbj))
          (restrictCom nmP (prepNmR j) "cp.l" "cp.r"))))

/-- §5i — the BFS at radius `2R` from the centre's child name, on the
pre-isolation child CSR. -/
def prepBfsCom (R2 : ℕ) : Com :=
  .seq (.assign "bf.n" (.var "cp.n"))
    (.seq (.assign "bf.m" (.var "cp.m"))
      (.seq (.assign "bf.r" (.lit R2))
        (.seq (.assign "bf.v" (.var "cp.z"))
          (bfsCom "cp.o" "cp.t" "cp.d"))))

/-- §5j — the supports pass writing the NEW round's column (index `j`,
oldest-first) of the `(j+1)` channel region. -/
def prepSupportsCom (j : ℕ) (R2 lpj hbj : ℕ) : Com :=
  .seq (.assign "sp.n" (.var "cp.n"))
    (.seq (.assign "sp.m" (.var "cp.m"))
      (.seq (.assign "sp.r" (.lit R2))
        (.seq (.assign "sp.l" (.lit lpj))
          (.seq (.assign "sp.h" (.lit hbj))
            (.seq (.assign "sp.p" (.lit j))
              (supportsCom "cp.o" "cp.t" "cp.d" "cp.p"
                (arenaNames (j + 1)).hist))))))

/-- The `pd`-slot index pairs, in writer order. -/
private def pdIdx (S : Setup L) : List (Fin S.width × Fin (S.R + 1)) :=
  (List.finRange S.width).flatMap fun b : Fin S.width =>
    (List.finRange (S.R + 1)).map fun a : Fin (S.R + 1) => (b, a)

/-- The `pu`-slot index pairs, in writer order. -/
private def puIdx (S : Setup L) (j : ℕ) :
    List (Fin (relPal (S.pal j)) × Fin (S.R + 1)) :=
  (List.finRange (relPal (S.pal j))).flatMap
    fun c : Fin (relPal (S.pal j)) =>
    (List.finRange (S.R + 1)).map fun b : Fin (S.R + 1) => (c, b)

/-- One old-colour writer. -/
private def colWOld (S : Setup L) (j : ℕ) (c : Fin (S.pal j)) : Com :=
  Com.store (arenaNames (j + 1)).col
    (.add (.mul (.var "cp.i") (.lit (S.pal (j + 1))))
      (.lit ((isoOld (Λ := relPal (S.pal j)) (mb := S.width)
        (cap := S.R) c.castSucc) : ℕ)))
    (.get "cp.c"
      (.add (.mul (.var "cp.i") (.lit (S.pal j))) (.lit (c : ℕ))))

/-- The marker writer. -/
private def colWMarker (S : Setup L) (j : ℕ) : Com :=
  Com.store (arenaNames (j + 1)).col
    (.add (.mul (.var "cp.i") (.lit (S.pal (j + 1))))
      (.lit ((isoOld (Λ := relPal (S.pal j)) (mb := S.width)
        (cap := S.R) (Fin.last (S.pal j))) : ℕ)))
    (.lit 1)

/-- One batch-profile writer. -/
private def colWPd (S : Setup L) (j : ℕ) (p : Fin S.width × Fin (S.R + 1)) : Com :=
  Com.ite (.lt (.lit ((p.2 : ℕ)))
      (.get (lv "cq.d" ((p.1 : ℕ))) (.var "cp.i")))
    (Com.store (arenaNames (j + 1)).col
      (.add (.mul (.var "cp.i") (.lit (S.pal (j + 1))))
        (.lit ((isoPd (Λ := relPal (S.pal j)) (mb := S.width)
          (cap := S.R) p.1 p.2) : ℕ)))
      (.lit 0))
    (Com.store (arenaNames (j + 1)).col
      (.add (.mul (.var "cp.i") (.lit (S.pal (j + 1))))
        (.lit ((isoPd (Λ := relPal (S.pal j)) (mb := S.width)
          (cap := S.R) p.1 p.2) : ℕ)))
      (.lit 1))

/-- One colour-profile writer. -/
private def colWPu (S : Setup L) (j : ℕ)
    (p : Fin (relPal (S.pal j)) × Fin (S.R + 1)) : Com :=
  Com.ite (.lt (.lit ((p.2 : ℕ) + 1))
      (.get (lv "cq.u" ((p.1 : ℕ))) (.var "cp.i")))
    (Com.store (arenaNames (j + 1)).col
      (.add (.mul (.var "cp.i") (.lit (S.pal (j + 1))))
        (.lit ((isoPu (Λ := relPal (S.pal j)) (mb := S.width)
          (cap := S.R) p.1 p.2) : ℕ)))
      (.lit 0))
    (Com.store (arenaNames (j + 1)).col
      (.add (.mul (.var "cp.i") (.lit (S.pal (j + 1))))
        (.lit ((isoPu (Λ := relPal (S.pal j)) (mb := S.width)
          (cap := S.R) p.1 p.2) : ℕ)))
      (.lit 1))

/-- §5k — the per-row colour writers: one store per slot of the
`(j+1)` palette — old colours read off the pre-isolation rows, the
marker constant, the `pd`/`pu` slots thresholded off the profile
tables. -/
private def colWriters (S : Setup L) (j : ℕ) : List Com :=
  ((List.finRange (S.pal j)).map (colWOld S j))
  ++ [colWMarker S j]
  ++ ((pdIdx S).map (colWPd S j))
  ++ ((puIdx S j).map (colWPu S j))

/-- The writers' slots, in writer order. -/
private def colSlots (S : Setup L) (j : ℕ) :
    List (Fin (isoPal (relPal (S.pal j)) S.width S.R)) :=
  ((List.finRange (S.pal j)).map fun c =>
    isoOld (Λ := relPal (S.pal j)) (mb := S.width) (cap := S.R) c.castSucc)
  ++ [isoOld (Λ := relPal (S.pal j)) (mb := S.width) (cap := S.R)
      (Fin.last (S.pal j))]
  ++ ((pdIdx S).map fun p =>
      isoPd (Λ := relPal (S.pal j)) (mb := S.width) (cap := S.R) p.1 p.2)
  ++ ((puIdx S j).map fun p =>
      isoPu (Λ := relPal (S.pal j)) (mb := S.width) (cap := S.R) p.1 p.2)

/-- **Every slot has a writer**: the four chunks enumerate the whole
isolation palette. -/
private theorem colSlots_covers (S : Setup L) (j : ℕ)
    (d : Fin (isoPal (relPal (S.pal j)) S.width S.R)) :
    d ∈ colSlots S j := by
  have hd : isoEnc (relPal (S.pal j)) S.width S.R
      ((isoEnc (relPal (S.pal j)) S.width S.R).symm d) = d :=
    Equiv.apply_symm_apply _ _
  rcases hs : (isoEnc (relPal (S.pal j)) S.width S.R).symm d with
    c' | (⟨b, a⟩ | ⟨c, b⟩)
  · -- an old slot: `castSucc` or the marker, by `lastCases`
    rw [hs] at hd
    induction c' using Fin.lastCases with
    | last =>
      refine List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ ?_))
      rw [List.mem_singleton, ← hd]
      rfl
    | cast c =>
      refine List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ ?_))
      rw [List.mem_map]
      exact ⟨c, List.mem_finRange c, hd⟩
  · rw [hs] at hd
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    rw [List.mem_map]
    refine ⟨(b, a), ?_, hd⟩
    rw [pdIdx, List.mem_flatMap]
    exact ⟨b, List.mem_finRange b,
      List.mem_map.mpr ⟨a, List.mem_finRange a, rfl⟩⟩
  · rw [hs] at hd
    refine List.mem_append_right _ ?_
    rw [List.mem_map]
    refine ⟨(c, b), ?_, hd⟩
    rw [puIdx, List.mem_flatMap]
    exact ⟨c, List.mem_finRange c,
      List.mem_map.mpr ⟨b, List.mem_finRange b, rfl⟩⟩

/-- One row of the colour write, sequenced. -/
private noncomputable def colRowCom (S : Setup L) (j : ℕ) : Com :=
  (colWriters S j).foldr .seq .skip

/-- §5k — the colour write: per carrier row, the compile-time writer
sequence. -/
noncomputable def prepColCom (S : Setup L) (j : ℕ) : Com :=
  .seq (.assign "cp.i" (.lit 0))
    (.while (.lt (.var "cp.i") (.var (arenaNames (j + 1)).nN))
      (.seq (colRowCom S j)
        (.assign "cp.i" (.add (.var "cp.i") (.lit 1)))))

/-- §5l — the isolate stage writing the final `(j+1)` CSR. -/
def prepIsolateCom (j : ℕ) : Com :=
  isolateCom (prepNmI j) (arenaNames (j + 1)).off (arenaNames (j + 1)).tgt
    (arenaNames (j + 1)).nS "cp.b"

open Classical in
/-- **The whole pass** (§5a–§5l in order). -/
noncomputable def prepCom (S : Setup L) (ℓp hbf : ℕ → ℕ)
    (co cm : ℕ → String) (j : ℕ) : Com :=
  .seq (prepRowBoundsCom (co j) (ctrName j))
    (.seq (prepZeroCom (arenaNames j).nN)
      (.seq (prepRowCom (cm j))
        (.seq (prepCentreCom (ctrName j))
          (.seq (prepBatchCom (arenaNames j).hist (ctrName j) (ℓp j) (hbf j))
            (.seq (prepWidthCom S.width)
              (.seq (prepClearCom (cm j))
                (.seq (prepRestrictCom (arenaNames j) j (S.pal j) (ℓp j)
                    (hbf j))
                  (.seq (prepBfsCom (2 * S.R))
                    (.seq (prepSupportsCom j (2 * S.R) (ℓp j) (hbf j))
                      (.seq (profilesCom (prepPN j) S.width (S.pal j) S.R)
                        (.seq (prepColCom S j)
                          (prepIsolateCom j))))))))))))

/-! ## §6 The budget -/

open Classical in
/-- **The pass's budget**, closed form per centre `u`: the rank-scratch
zeroing (carrier-sized — the cleanliness deviation, module docstring),
the cluster-row pass, the channel-row trace, the width scan and pad,
the clear, the five landed stage budgets at the child's dimensions
(radius `2R`), the colour write, and the glue. -/
noncomputable def prepK (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp hbf : ℕ → ℕ) (j : ℕ) (A : Arena (S.pal j) n₀) (u : ℕ) : ℕ :=
  if h : u < A.N then
    let π := (ord A.N A.G).order
    let k := childN S A π ⟨u, h⟩
    let cns := ∑ v : Fin (childN S A π ⟨u, h⟩),
      (preG S A π ⟨u, h⟩).degree v
    20                                                      -- row bounds
    + (11 * A.N + 6)                                        -- zero
    + (30 * k + 6)                                          -- row pass
    + 20                                                    -- centre
    + ((30 + 30 * (hbf j + 1)) * ℓp j + 20)                 -- batch trace
    + ((30 * k + 6) + (12 * S.width + 20))                  -- width array
    + (14 * k + 20)                                         -- clear
    + (20 + restrictK (Impl.degSum A.G (cluster S A π ⟨u, h⟩)) k
        (S.pal j) (ℓp j) (hbf j))                           -- restrict
    + (20 + bfsK k cns (2 * S.R))                           -- bfs
    + (30 + supportsK k cns (2 * S.R))                      -- supports
    + profilesK S.width (S.pal j + 1) k cns S.R             -- profiles
    + ((30 * (isoPal (relPal (S.pal j)) S.width S.R) + 9) * k + 6)
                                                            -- colour write
    + isolateK k cns                                        -- isolate
    + 30                                                    -- seq slack
  else 0

open Classical in
/-- `prepK` at a carrier member, the guard discharged — the closed form
the assembly's final cost bound rewrites to. -/
theorem prepK_coe (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp hbf : ℕ → ℕ) (j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N) :
    prepK S ord ℓp hbf j A (u : ℕ)
      = 20 + (11 * A.N + 6)
        + (30 * childN S A ((ord A.N A.G).order) u + 6)
        + 20
        + ((30 + 30 * (hbf j + 1)) * ℓp j + 20)
        + ((30 * childN S A ((ord A.N A.G).order) u + 6)
            + (12 * S.width + 20))
        + (14 * childN S A ((ord A.N A.G).order) u + 20)
        + (20 + restrictK
            (Impl.degSum A.G (cluster S A ((ord A.N A.G).order) u))
            (childN S A ((ord A.N A.G).order) u) (S.pal j) (ℓp j) (hbf j))
        + (20 + bfsK (childN S A ((ord A.N A.G).order) u)
            (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
              (preG S A ((ord A.N A.G).order) u).degree v) (2 * S.R))
        + (30 + supportsK (childN S A ((ord A.N A.G).order) u)
            (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
              (preG S A ((ord A.N A.G).order) u).degree v) (2 * S.R))
        + profilesK S.width (S.pal j + 1)
            (childN S A ((ord A.N A.G).order) u)
            (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
              (preG S A ((ord A.N A.G).order) u).degree v) S.R
        + ((30 * (isoPal (relPal (S.pal j)) S.width S.R) + 9)
            * childN S A ((ord A.N A.G).order) u + 6)
        + isolateK (childN S A ((ord A.N A.G).order) u)
            (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
              (preG S A ((ord A.N A.G).order) u).degree v)
        + 30 := by
  rw [prepK, dif_pos u.2]

/-! ## §6b The write sets -/

private theorem warrs_colWriters {S : Setup L} {j : ℕ} :
    ∀ c ∈ colWriters S j, ∀ b ∈ c.warrs, b = (arenaNames (j + 1)).col := by
  intro c hc
  simp only [colWriters, List.mem_append, List.mem_map,
    List.mem_singleton] at hc
  rcases hc with ((⟨x, -, rfl⟩ | rfl) | ⟨x, -, rfl⟩) | ⟨x, -, rfl⟩ <;>
    · intro b hb
      simp only [colWOld, colWMarker, colWPd, colWPu, Com.warrs,
        List.mem_append, List.mem_singleton, List.not_mem_nil,
        or_false] at hb
      first
        | exact hb
        | (rcases hb with hb | hb <;> exact hb)

private theorem warrs_colRowCom {S : Setup L} {j : ℕ} :
    ∀ b ∈ (colRowCom S j).warrs, b = (arenaNames (j + 1)).col := by
  rw [colRowCom]
  generalize hl : colWriters S j = l
  have hall : ∀ c ∈ l, ∀ b ∈ c.warrs, b = (arenaNames (j + 1)).col := by
    rw [← hl]; exact warrs_colWriters
  clear hl
  induction l with
  | nil => intro b hb; simp [Com.warrs] at hb
  | cons c rest ih =>
    intro b hb
    simp only [List.foldr_cons, Com.warrs, List.mem_append] at hb
    rcases hb with hb | hb
    · exact hall c (List.mem_cons_self ..) b hb
    · exact ih (fun c' hc' => hall c' (List.mem_cons_of_mem _ hc')) b hb

private theorem wvars_colWriters {S : Setup L} {j : ℕ} :
    ∀ c ∈ colWriters S j, c.wvars = [] := by
  intro c hc
  simp only [colWriters, List.mem_append, List.mem_map,
    List.mem_singleton] at hc
  rcases hc with ((⟨x, -, rfl⟩ | rfl) | ⟨x, -, rfl⟩) | ⟨x, -, rfl⟩ <;>
    simp [colWOld, colWMarker, colWPd, colWPu, Com.wvars]

private theorem wvars_colRowCom {S : Setup L} {j : ℕ} :
    (colRowCom S j).wvars = [] := by
  rw [colRowCom]
  generalize hl : colWriters S j = l
  have hall : ∀ c ∈ l, c.wvars = [] := by
    rw [← hl]; exact wvars_colWriters
  clear hl
  induction l with
  | nil => simp [Com.wvars]
  | cons c rest ih =>
    simp only [List.foldr_cons, Com.wvars]
    rw [hall c (List.mem_cons_self ..), ih
      (fun c' hc' => hall c' (List.mem_cons_of_mem _ hc'))]
    rfl

/-- Every array the pass writes: its own scratch, the `(j+1)` regions
(all but the table), or a profile-family region. -/
theorem warrs_prepCom {S : Setup L} {ℓp hbf : ℕ → ℕ} {co cm : ℕ → String}
    {j : ℕ} :
    ∀ b ∈ (prepCom S ℓp hbf co cm j).warrs,
      b ∈ prepArrays ∨ b = (arenaNames (j + 1)).up
        ∨ b = (arenaNames (j + 1)).hist ∨ b = (arenaNames (j + 1)).col
        ∨ b = (arenaNames (j + 1)).off ∨ b = (arenaNames (j + 1)).tgt
        ∨ (∃ i, b = lv "cq.d" i) ∨ (∃ i, b = lv "cq.v" i)
        ∨ ∃ i, b = lv "cq.u" i := by
  intro b hb
  simp only [prepCom, Com.warrs, List.mem_append] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
    | hb | hb
  · -- row bounds: writes no array
    simp [prepRowBoundsCom, Com.warrs] at hb
  · -- zero
    simp [prepZeroCom, Com.warrs] at hb
    subst hb; simp [prepArrays]
  · -- row pass
    simp [prepRowCom, Com.warrs] at hb
    rcases hb with rfl | rfl | rfl <;> simp [prepArrays]
  · -- centre
    simp [prepCentreCom, Com.warrs] at hb
    subst hb; simp [prepArrays]
  · -- batch trace
    simp [prepBatchCom, Com.warrs] at hb
    subst hb; simp [prepArrays]
  · -- width array
    simp [prepWidthCom, Com.warrs] at hb
    rcases hb with rfl | rfl <;> simp [prepArrays]
  · -- clear
    simp [prepClearCom, Com.warrs] at hb
    subst hb; simp [prepArrays]
  · -- restrict
    simp only [prepRestrictCom, Com.warrs, List.nil_append] at hb
    rw [warrs_restrictCom] at hb
    simp only [prepNmR, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [prepArrays]
    · simp [prepArrays]
    · simp [prepArrays]
    · simp [prepArrays]
    · simp [prepArrays]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · simp [prepArrays]
  · -- bfs
    simp only [prepBfsCom, Com.warrs, List.nil_append] at hb
    rw [warrs_bfsCom] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [prepArrays]
  · -- supports
    simp only [prepSupportsCom, Com.warrs, List.nil_append] at hb
    rw [warrs_supportsCom] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [prepArrays]
    · simp [prepArrays]
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
  · -- profiles
    rcases warrs_profilesCom_subset _ _ _ _ b hb with h | h | ⟨i, hi, h⟩
      | ⟨i, hi, h⟩ | ⟨i, hi, h⟩
    · subst h; simp [prepPN, prepArrays]
    · subst h; simp [prepPN, prepArrays]
    · subst h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨i, rfl⟩))))))
    · subst h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨i, rfl⟩)))))))
    · subst h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨i, rfl⟩)))))))
  · -- colour write
    simp only [prepColCom, Com.warrs, List.append_nil, List.nil_append,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    exact Or.inr (Or.inr (Or.inr (Or.inl (warrs_colRowCom b hb))))
  · -- isolate
    simp only [prepIsolateCom] at hb
    rw [warrs_isolateCom] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-! ## §6c The batch-assembly loops -/

open Classical in
/-- **§5b's zero pass**: the rank scratch's carrier prefix is all-zero;
nothing else moves. -/
theorem prepZero_spec {B N : ℕ} {nNj : String} (hNB : N < B)
    (hnN : nNj ≠ "cp.i") :
    Spec B
      (fun σ => σ.vars nNj = N ∧ N ≤ (σ.arrs "cp.r").length)
      (prepZeroCom nNj)
      (fun σ σ' =>
        (∀ p, p < N → (σ'.arrs "cp.r").getD p 0 = 0) ∧
        (∀ b, b ≠ "cp.r" → σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ y, y ≠ "cp.i" → σ'.vars y = σ.vars y))
      (11 * N + 6) := by
  intro σ0 hσ0
  obtain ⟨hnNv, hraL⟩ := hσ0
  set I : Env → Prop := fun σ =>
    σ.vars nNj = N ∧ σ.vars "cp.i" ≤ N ∧
    (∀ p, p < σ.vars "cp.i" → (σ.arrs "cp.r").getD p 0 = 0) ∧
    (∀ b, b ≠ "cp.r" → σ.arrs b = σ0.arrs b) ∧
    (∀ b, (σ.arrs b).length = (σ0.arrs b).length) ∧
    (∀ y, y ≠ "cp.i" → σ.vars y = σ0.vars y) with hI_def
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "cp.i" < N)
      (.seq (.store "cp.r" (.var "cp.i") (.lit 0))
        (.assign "cp.i" (.add (.var "cp.i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "cp.i" = σ.vars "cp.i" + 1) 7 := by
    rintro σ ⟨⟨h1, hile, h2, h3, h4, h5⟩, hlt⟩
    have hraLσ : N ≤ (σ.arrs "cp.r").length := by
      rw [h4 "cp.r"]; exact hraL
    have hiB : σ.vars "cp.i" < B := lt_trans hlt hNB
    set σm := σ.setArr "cp.r" (σ.vars "cp.i") 0 with hσm
    have hr1 : Run B (.store "cp.r" (.var "cp.i") (.lit 0)) σ σm 3 :=
      Run.store (evalB_var hiB) (evalB_lit (by omega))
        (lt_of_lt_of_le hlt hraLσ)
    have hmi : σm.vars "cp.i" = σ.vars "cp.i" := by
      rw [hσm, vars_setArr]
    have heval : (Expr.add (.var "cp.i") (.lit 1)).evalB B σm
        = some (σ.vars "cp.i" + 1) := by
      have h1B : (1 : ℕ) < B := by omega
      have h := evalB_bin (op := .add)
        (evalB_var (x := "cp.i") (by rw [hmi]; exact hiB))
        (evalB_lit h1B) (by rw [Bop.apply_add, hmi]; omega)
      rwa [Bop.apply_add, hmi] at h
    refine ⟨σm.setVar "cp.i" (σ.vars "cp.i" + 1),
      (hr1.seq (Run.assign heval)).mono (by simp), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [vars_setVar, if_neg hnN, hσm, vars_setArr]
        exact h1
      · rw [vars_setVar, if_pos rfl]
        omega
      · intro p hp
        rw [vars_setVar, if_pos rfl] at hp
        rw [arrs_setVar, hσm, arrs_setArr, if_pos rfl]
        by_cases hpe : p = σ.vars "cp.i"
        · subst hpe
          rw [getD_set_self (lt_of_lt_of_le hlt hraLσ)]
        · rw [getD_set_ne hpe]
          exact h2 p (by omega)
      · intro b hb
        rw [arrs_setVar, hσm, arrs_setArr, if_neg hb]
        exact h3 b hb
      · intro b
        rw [arrs_setVar, hσm, length_arrs_setArr]
        exact h4 b
      · intro y hy
        rw [vars_setVar, if_neg hy, hσm, vars_setArr]
        exact h5 y hy
    · rw [vars_setVar, if_pos rfl]
  obtain ⟨σ', hrun, hI', hctr'⟩ :=
    (Spec.forRangeZero "cp.i" nNj I N 7 hNB
      (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1) hbody) σ0
      (show I (σ0.setVar "cp.i" 0) by
        refine ⟨by rw [vars_setVar, if_neg hnN]; exact hnNv,
          by rw [vars_setVar, if_pos rfl]; omega, ?_, ?_, ?_, ?_⟩
        · intro p hp
          rw [vars_setVar, if_pos rfl] at hp
          omega
        · intro b _; rw [arrs_setVar]
        · intro b; rw [arrs_setVar]
        · intro y hy
          rw [vars_setVar, if_neg hy])
  obtain ⟨h1', hile', h2', h3', h4', h5'⟩ := hI'
  refine ⟨σ', hrun.mono (by omega), ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact h2' p (by rw [hctr']; exact hp)
  · exact h3'
  · exact h4'
  · exact h5'

open Classical in
/-- **§5c's cluster-row pass**: the cluster-list scratch holds the row,
the rank scratch marks every member with its rank `+1` (zero elsewhere
on the carrier), the batch bits' cluster prefix is zero. -/
theorem prepRow_spec {B N : ℕ} {cmj : String} (X : Set (Fin N)) (base : ℕ)
    (hNB : N < B) (hNNB : N * N < B) (hbk : base + X.ncard ≤ N * N)
    (hcm_la : cmj ≠ "cp.l") (hcm_ra : cmj ≠ "cp.r") (hcm_bb : cmj ≠ "cp.b") :
    Spec B
      (fun σ => σ.vars "cp.s" = base ∧ σ.vars "cp.n" = X.ncard ∧
        base + X.ncard ≤ (σ.arrs cmj).length ∧
        (∀ t : ℕ, ∀ ht : t < X.ncard,
          (σ.arrs cmj).getD (base + t) 0
            = (Impl.restrictEmb X ⟨t, ht⟩ : ℕ)) ∧
        X.ncard ≤ (σ.arrs "cp.l").length ∧
        X.ncard ≤ (σ.arrs "cp.b").length ∧
        N ≤ (σ.arrs "cp.r").length ∧
        (∀ p, p < N → (σ.arrs "cp.r").getD p 0 = 0))
      (prepRowCom cmj)
      (fun σ σ' =>
        (∀ t : ℕ, ∀ ht : t < X.ncard,
          (σ'.arrs "cp.l").getD t 0 = (Impl.restrictEmb X ⟨t, ht⟩ : ℕ)) ∧
        (∀ t : ℕ, ∀ ht : t < X.ncard,
          (σ'.arrs "cp.r").getD ((Impl.restrictEmb X ⟨t, ht⟩ : ℕ)) 0
            = t + 1) ∧
        (∀ p, p < N → (∀ t : ℕ, ∀ ht : t < X.ncard,
            (Impl.restrictEmb X ⟨t, ht⟩ : ℕ) ≠ p) →
          (σ'.arrs "cp.r").getD p 0 = 0) ∧
        (∀ t, t < X.ncard → (σ'.arrs "cp.b").getD t 0 = 0) ∧
        (∀ b, b ≠ "cp.l" → b ≠ "cp.r" → b ≠ "cp.b" →
          σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ y, y ≠ "cp.i" → σ'.vars y = σ.vars y))
      (25 * X.ncard + 6) := by
  intro σ0 hσ0
  obtain ⟨hs0, hn0, hcmL0, hrow0, hlaL0, hbbL0, hraL0, hra0⟩ := hσ0
  have hkN : X.ncard ≤ N := set_ncard_le_card X
  set k := X.ncard with hk_def
  set I : Env → Prop := fun σ =>
    σ.vars "cp.s" = base ∧ σ.vars "cp.n" = k ∧ σ.vars "cp.i" ≤ k ∧
    σ.arrs cmj = σ0.arrs cmj ∧
    (∀ t : ℕ, ∀ ht : t < k, t < σ.vars "cp.i" →
      (σ.arrs "cp.l").getD t 0 = (Impl.restrictEmb X ⟨t, ht⟩ : ℕ)) ∧
    (∀ t : ℕ, ∀ ht : t < k, t < σ.vars "cp.i" →
      (σ.arrs "cp.r").getD ((Impl.restrictEmb X ⟨t, ht⟩ : ℕ)) 0 = t + 1) ∧
    (∀ p, p < N → (∀ t : ℕ, ∀ ht : t < k, t < σ.vars "cp.i" →
        (Impl.restrictEmb X ⟨t, ht⟩ : ℕ) ≠ p) →
      (σ.arrs "cp.r").getD p 0 = 0) ∧
    (∀ t, t < σ.vars "cp.i" → (σ.arrs "cp.b").getD t 0 = 0) ∧
    (∀ b, b ≠ "cp.l" → b ≠ "cp.r" → b ≠ "cp.b" → σ.arrs b = σ0.arrs b) ∧
    (∀ b, (σ.arrs b).length = (σ0.arrs b).length) ∧
    (∀ y, y ≠ "cp.i" → σ.vars y = σ0.vars y) with hI_def
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "cp.i" < k)
      (.seq (.store "cp.l" (.var "cp.i")
          (.get cmj (.add (.var "cp.s") (.var "cp.i"))))
        (.seq (.store "cp.r" (.get cmj (.add (.var "cp.s") (.var "cp.i")))
            (.add (.var "cp.i") (.lit 1)))
          (.seq (.store "cp.b" (.var "cp.i") (.lit 0))
            (.assign "cp.i" (.add (.var "cp.i") (.lit 1))))))
      (fun σ σ' => I σ' ∧ σ'.vars "cp.i" = σ.vars "cp.i" + 1) 21 := by
    rintro σ ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, hlt⟩
    set i := σ.vars "cp.i" with hi_def
    have hiB : i < B := by omega
    have h1B : (1 : ℕ) < B := by omega
    have hbase_iB : base + i < B := by omega
    set e : Fin N := Impl.restrictEmb X ⟨i, hlt⟩ with he_def
    have heN : (e : ℕ) < N := e.2
    have hcmLσ : base + k ≤ (σ.arrs cmj).length := by rw [h4]; exact hcmL0
    have hlaLσ : k ≤ (σ.arrs "cp.l").length := by
      rw [h10 "cp.l"]; exact hlaL0
    have hraLσ : N ≤ (σ.arrs "cp.r").length := by
      rw [h10 "cp.r"]; exact hraL0
    have hbbLσ : k ≤ (σ.arrs "cp.b").length := by
      rw [h10 "cp.b"]; exact hbbL0
    -- the row read
    have hread : (Expr.get cmj (.add (.var "cp.s") (.var "cp.i"))).evalB B σ
        = some (e : ℕ) := by
      have hadd := evalB_bin (op := .add)
        (evalB_var (x := "cp.s") (by rw [h1]; omega))
        (evalB_var (x := "cp.i") hiB)
        (by rw [Bop.apply_add, h1]; omega)
      rw [Bop.apply_add, h1] at hadd
      refine evalB_get hadd (getElemQ_of_getD (by omega) ?_) (by omega)
      rw [h4]
      exact hrow0 i hlt
    -- the three stores and the bump
    set σ1 := σ.setArr "cp.l" i (e : ℕ) with hσ1
    set σ2 := σ1.setArr "cp.r" (e : ℕ) (i + 1) with hσ2
    set σ3 := σ2.setArr "cp.b" i 0 with hσ3
    have hr1 : Run B (.store "cp.l" (.var "cp.i")
        (.get cmj (.add (.var "cp.s") (.var "cp.i")))) σ σ1 6 :=
      Run.store (evalB_var hiB) hread (by omega)
    have hs1 : σ1.vars "cp.s" = base := by rw [hσ1, vars_setArr, h1]
    have hi1 : σ1.vars "cp.i" = i := by rw [hσ1, vars_setArr]
    have hread1 : (Expr.get cmj (.add (.var "cp.s") (.var "cp.i"))).evalB B σ1
        = some (e : ℕ) := by
      have harr : σ1.arrs cmj = σ.arrs cmj := by
        rw [hσ1, arrs_setArr, if_neg hcm_la]
      have hvs : (Expr.var "cp.s").evalB B σ1 = some base := by
        rw [← hs1]
        exact evalB_var (by rw [hs1]; omega)
      have hvi : (Expr.var "cp.i").evalB B σ1 = some i := by
        rw [← hi1]
        exact evalB_var (by rw [hi1]; exact hiB)
      have hadd := evalB_bin (op := .add) hvs hvi
        (by rw [Bop.apply_add]; omega)
      rw [Bop.apply_add] at hadd
      refine evalB_get hadd (getElemQ_of_getD (by rw [harr]; omega) ?_)
        (by omega)
      rw [harr, h4]
      exact hrow0 i hlt
    have hbump1 : (Expr.add (.var "cp.i") (.lit 1)).evalB B σ1
        = some (i + 1) := by
      have hvi : (Expr.var "cp.i").evalB B σ1 = some i := by
        rw [← hi1]
        exact evalB_var (by rw [hi1]; exact hiB)
      have h := evalB_bin (op := .add) hvi (evalB_lit h1B)
        (by rw [Bop.apply_add]; omega)
      rwa [Bop.apply_add] at h
    have hr2 : Run B (.store "cp.r"
        (.get cmj (.add (.var "cp.s") (.var "cp.i")))
        (.add (.var "cp.i") (.lit 1))) σ1 σ2 8 :=
      Run.store hread1 hbump1
        (by rw [hσ1, length_arrs_setArr]; omega)
    have hi2 : σ2.vars "cp.i" = i := by rw [hσ2, vars_setArr, hi1]
    have hr3 : Run B (.store "cp.b" (.var "cp.i") (.lit 0)) σ2 σ3 3 := by
      have hvi : (Expr.var "cp.i").evalB B σ2 = some i := by
        rw [← hi2]
        exact evalB_var (by rw [hi2]; exact hiB)
      refine Run.congr (Run.store hvi (evalB_lit (by omega)) ?_) ?_
      · rw [hσ2, length_arrs_setArr, hσ1, length_arrs_setArr]
        omega
      · rw [hσ3]
    have hi3 : σ3.vars "cp.i" = i := by rw [hσ3, vars_setArr, hi2]
    have hbump3 : (Expr.add (.var "cp.i") (.lit 1)).evalB B σ3
        = some (i + 1) := by
      have hvi : (Expr.var "cp.i").evalB B σ3 = some i := by
        rw [← hi3]
        exact evalB_var (by rw [hi3]; exact hiB)
      have h := evalB_bin (op := .add) hvi (evalB_lit h1B)
        (by rw [Bop.apply_add]; omega)
      rwa [Bop.apply_add] at h
    refine ⟨σ3.setVar "cp.i" (i + 1),
      (hr1.seq (hr2.seq (hr3.seq (Run.assign hbump3)))).mono (by simp),
      ?_, ?_⟩
    · -- the invariant at the bumped state
      have hlaA : (σ3.setVar "cp.i" (i + 1)).arrs "cp.l"
          = (σ.arrs "cp.l").set i (e : ℕ) := by
        rw [arrs_setVar, hσ3, arrs_setArr, if_neg (by decide), hσ2,
          arrs_setArr, if_neg (by decide), hσ1, arrs_setArr, if_pos rfl]
      have hraA : (σ3.setVar "cp.i" (i + 1)).arrs "cp.r"
          = (σ.arrs "cp.r").set (e : ℕ) (i + 1) := by
        rw [arrs_setVar, hσ3, arrs_setArr, if_neg (by decide), hσ2,
          arrs_setArr, if_pos rfl, hσ1, arrs_setArr, if_neg (by decide)]
      have hbbA : (σ3.setVar "cp.i" (i + 1)).arrs "cp.b"
          = (σ.arrs "cp.b").set i 0 := by
        rw [arrs_setVar, hσ3, arrs_setArr, if_pos rfl, hσ2, arrs_setArr,
          if_neg (by decide), hσ1, arrs_setArr, if_neg (by decide)]
      have hoth : ∀ b, b ≠ "cp.l" → b ≠ "cp.r" → b ≠ "cp.b" →
          (σ3.setVar "cp.i" (i + 1)).arrs b = σ.arrs b := by
        intro b hb1 hb2 hb3
        rw [arrs_setVar, hσ3, arrs_setArr, if_neg hb3, hσ2, arrs_setArr,
          if_neg hb2, hσ1, arrs_setArr, if_neg hb1]
      have hvarsA : ∀ y, y ≠ "cp.i" →
          (σ3.setVar "cp.i" (i + 1)).vars y = σ.vars y := by
        intro y hy
        rw [vars_setVar, if_neg hy, hσ3, vars_setArr, hσ2, vars_setArr,
          hσ1, vars_setArr]
      have hctr : (σ3.setVar "cp.i" (i + 1)).vars "cp.i" = i + 1 := by
        rw [vars_setVar, if_pos rfl]
      have hinj : ∀ (t : ℕ) (ht : t < k), t ≠ i →
          (Impl.restrictEmb X ⟨t, ht⟩ : ℕ) ≠ (e : ℕ) := by
        intro t ht hti hcontra
        have h := (Impl.restrictEmb X).injective
          (Fin.ext (hcontra : ((Impl.restrictEmb X ⟨t, ht⟩ : Fin N) : ℕ)
            = (e : ℕ)))
        exact hti (by simpa using congrArg Fin.val h)
      refine ⟨by rw [hvarsA _ (by decide)]; exact h1,
        by rw [hvarsA _ (by decide)]; exact h2,
        by rw [hctr]; omega,
        by rw [hoth _ hcm_la hcm_ra hcm_bb]; exact h4, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · -- la cells
        intro t ht htlt
        rw [hctr] at htlt
        rw [hlaA]
        by_cases hti : t = i
        · subst hti
          rw [List.getD_eq_getElem?_getD, List.getElem?_set_self
            (by omega), Option.getD_some]
        · have h := h5 t ht (by omega)
          rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne
            (fun hcontra => hti hcontra.symm) , ← List.getD_eq_getElem?_getD]
          exact h
      · -- rank marks
        intro t ht htlt
        rw [hctr] at htlt
        rw [hraA]
        by_cases hti : t = i
        · subst hti
          rw [getD_set_self (by omega)]
        · rw [getD_set_ne (hinj t ht hti)]
          exact h6 t ht (by omega)
      · -- rank zeros
        intro p hp hnp
        rw [hctr] at hnp
        rw [hraA, getD_set_ne (Ne.symm (hnp i hlt (by omega)))]
        exact h7 p hp (fun t ht htlt => hnp t ht (by omega))
      · -- batch bits
        intro t htlt
        rw [hctr] at htlt
        rw [hbbA]
        by_cases hti : t = i
        · subst hti
          rw [getD_set_self (by omega)]
        · rw [getD_set_ne hti]
          exact h8 t (by omega)
      · exact fun b hb1 hb2 hb3 => by
          rw [hoth b hb1 hb2 hb3]; exact h9 b hb1 hb2 hb3
      · intro b
        rw [arrs_setVar, hσ3, length_arrs_setArr, hσ2, length_arrs_setArr,
          hσ1, length_arrs_setArr]
        exact h10 b
      · intro y hy
        rw [hvarsA y hy]
        exact h11 y hy
    · rw [vars_setVar, if_pos rfl]
  obtain ⟨σ', hrun, hI', hctr'⟩ :=
    (Spec.forRangeZero "cp.i" "cp.n" I k 21 (by omega)
      (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.2.1) hbody) σ0
      (show I (σ0.setVar "cp.i" 0) by
        refine ⟨by rw [vars_setVar, if_neg (by decide)]; exact hs0,
          by rw [vars_setVar, if_neg (by decide)]; exact hn0,
          by rw [vars_setVar, if_pos rfl]; omega,
          by rw [arrs_setVar], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro t ht htlt
          rw [vars_setVar, if_pos rfl] at htlt
          omega
        · intro t ht htlt
          rw [vars_setVar, if_pos rfl] at htlt
          omega
        · intro p hp _
          rw [arrs_setVar]
          exact hra0 p hp
        · intro t htlt
          rw [vars_setVar, if_pos rfl] at htlt
          omega
        · intro b _ _ _; rw [arrs_setVar]
        · intro b; rw [arrs_setVar]
        · intro y hy; rw [vars_setVar, if_neg hy])
  obtain ⟨-, -, -, -, h5', h6', h7', h8', h9', h10', h11'⟩ := hI'
  refine ⟨σ', hrun.mono le_rfl, ?_, ?_, ?_, ?_, h9', h10', h11'⟩
  · exact fun t ht => h5' t ht (by rw [hctr']; exact ht)
  · exact fun t ht => h6' t ht (by rw [hctr']; exact ht)
  · exact fun p hp hnp =>
      h7' p hp (fun t ht _ => hnp t ht)
  · exact fun t ht => h8' t (by rw [hctr']; exact ht)

open Classical in
/-- **§5d's centre cell**: the centre's child name (its rank) lands in
`cp.z`, and its batch bit is set. -/
theorem prepCentre_spec {B N : ℕ} {ctr : String} (X : Set (Fin N))
    (u : Fin N) (hu : u ∈ X) (hNB : N < B) (hctr_ne : ctr ≠ "cp.z") :
    Spec B
      (fun σ => σ.vars ctr = (u : ℕ) ∧
        N ≤ (σ.arrs "cp.r").length ∧ X.ncard ≤ (σ.arrs "cp.b").length ∧
        (∀ t : ℕ, ∀ ht : t < X.ncard,
          (σ.arrs "cp.r").getD ((Impl.restrictEmb X ⟨t, ht⟩ : ℕ)) 0
            = t + 1))
      (prepCentreCom ctr)
      (fun σ σ' =>
        σ'.vars "cp.z" = (((setEquiv X).symm ⟨u, hu⟩ : Fin X.ncard) : ℕ) ∧
        (σ'.arrs "cp.b").getD
            ((((setEquiv X).symm ⟨u, hu⟩ : Fin X.ncard) : ℕ)) 0 = 1 ∧
        (∀ t, t ≠ (((setEquiv X).symm ⟨u, hu⟩ : Fin X.ncard) : ℕ) →
          (σ'.arrs "cp.b").getD t 0 = (σ.arrs "cp.b").getD t 0) ∧
        (∀ b, b ≠ "cp.b" → σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ y, y ≠ "cp.z" → σ'.vars y = σ.vars y))
      20 := by
  intro σ hσ
  obtain ⟨hctr, hraL, hbbL, hmarks⟩ := hσ
  set t0 : Fin X.ncard := (setEquiv X).symm ⟨u, hu⟩ with ht0_def
  have hembF : Impl.restrictEmb X ⟨(t0 : ℕ), t0.2⟩ = u := by
    have h : (⟨(t0 : ℕ), t0.2⟩ : Fin X.ncard) = t0 := Fin.ext rfl
    rw [Impl.restrictEmb_apply, h, ht0_def, Equiv.apply_symm_apply]
  have hemb : (Impl.restrictEmb X ⟨(t0 : ℕ), t0.2⟩ : ℕ) = (u : ℕ) :=
    congrArg Fin.val hembF
  have hraU : (σ.arrs "cp.r").getD (u : ℕ) 0 = (t0 : ℕ) + 1 := by
    rw [← hemb]
    exact hmarks (t0 : ℕ) t0.2
  have hkN : X.ncard ≤ N := set_ncard_le_card X
  have huB : (u : ℕ) < B := lt_trans u.2 hNB
  -- the read
  have hread : (Expr.sub (.get "cp.r" (.var ctr)) (.lit 1)).evalB B σ
      = some (t0 : ℕ) := by
    have hvctr : (Expr.var ctr).evalB B σ = some (u : ℕ) := by
      rw [← hctr]
      exact evalB_var (by rw [hctr]; exact huB)
    have hget : (Expr.get "cp.r" (.var ctr)).evalB B σ
        = some ((t0 : ℕ) + 1) :=
      evalB_get hvctr (getElemQ_of_getD (by omega) hraU) (by omega)
    have h := evalB_bin (op := .sub) hget (evalB_lit (n := 1) (by omega))
      (by rw [Bop.apply_sub]; omega)
    rw [Bop.apply_sub] at h
    rw [show (t0 : ℕ) + 1 - 1 = (t0 : ℕ) from by omega] at h
    exact h
  set σ1 := σ.setVar "cp.z" (t0 : ℕ) with hσ1
  have hr1 : Run B (.assign "cp.z" (.sub (.get "cp.r" (.var ctr)) (.lit 1)))
      σ σ1 5 := Run.assign hread
  have ht0k : (t0 : ℕ) < X.ncard := t0.2
  have hz1 : σ1.vars "cp.z" = (t0 : ℕ) := by
    rw [hσ1, vars_setVar, if_pos rfl]
  have hvz : (Expr.var "cp.z").evalB B σ1 = some (t0 : ℕ) := by
    rw [← hz1]
    exact evalB_var (by rw [hz1]; omega)
  have hr2 : Run B (.store "cp.b" (.var "cp.z") (.lit 1)) σ1
      (σ1.setArr "cp.b" (t0 : ℕ) 1) 3 := by
    refine Run.store hvz (evalB_lit (by omega)) ?_
    rw [hσ1, arrs_setVar]
    omega
  refine ⟨σ1.setArr "cp.b" (t0 : ℕ) 1, (hr1.seq hr2).mono (by simp),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vars_setArr, hσ1, vars_setVar, if_pos rfl]
  · rw [arrs_setArr, if_pos rfl, hσ1, arrs_setVar, getD_set_self (by omega)]
  · intro t htne
    rw [arrs_setArr, if_pos rfl, hσ1, arrs_setVar, getD_set_ne htne]
  · intro b hb
    rw [arrs_setArr, if_neg hb, hσ1, arrs_setVar]
  · intro b
    rw [length_arrs_setArr, hσ1, arrs_setVar]
  · intro y hy
    rw [vars_setArr, hσ1, vars_setVar, if_neg hy]

open Classical in
/-- **§5g's clear pass**: the marks are removed at exactly the cluster
cells, so the rank scratch's carrier prefix is all-zero again — the
cleanliness the restrict stage assumes. -/
theorem prepClear_spec {B N : ℕ} {cmj : String} (X : Set (Fin N)) (base : ℕ)
    (hNB : N < B) (hNNB : N * N < B) (hbk : base + X.ncard ≤ N * N)
    (hcm_ra : cmj ≠ "cp.r") :
    Spec B
      (fun σ => σ.vars "cp.s" = base ∧ σ.vars "cp.n" = X.ncard ∧
        base + X.ncard ≤ (σ.arrs cmj).length ∧
        (∀ t : ℕ, ∀ ht : t < X.ncard,
          (σ.arrs cmj).getD (base + t) 0
            = (Impl.restrictEmb X ⟨t, ht⟩ : ℕ)) ∧
        N ≤ (σ.arrs "cp.r").length ∧
        (∀ p, p < N → (∀ t : ℕ, ∀ ht : t < X.ncard,
            (Impl.restrictEmb X ⟨t, ht⟩ : ℕ) ≠ p) →
          (σ.arrs "cp.r").getD p 0 = 0))
      (prepClearCom cmj)
      (fun σ σ' =>
        (∀ p, p < N → (σ'.arrs "cp.r").getD p 0 = 0) ∧
        (∀ b, b ≠ "cp.r" → σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ y, y ≠ "cp.i" → σ'.vars y = σ.vars y))
      (14 * X.ncard + 6) := by
  intro σ0 hσ0
  obtain ⟨hs0, hn0, hcmL0, hrow0, hraL0, hra0⟩ := hσ0
  have hkN : X.ncard ≤ N := set_ncard_le_card X
  set k := X.ncard with hk_def
  set I : Env → Prop := fun σ =>
    σ.vars "cp.s" = base ∧ σ.vars "cp.n" = k ∧ σ.vars "cp.i" ≤ k ∧
    σ.arrs cmj = σ0.arrs cmj ∧
    (∀ t : ℕ, ∀ ht : t < k, t < σ.vars "cp.i" →
      (σ.arrs "cp.r").getD ((Impl.restrictEmb X ⟨t, ht⟩ : ℕ)) 0 = 0) ∧
    (∀ p, p < N → (∀ t : ℕ, ∀ ht : t < k,
        (Impl.restrictEmb X ⟨t, ht⟩ : ℕ) ≠ p) →
      (σ.arrs "cp.r").getD p 0 = 0) ∧
    (∀ b, b ≠ "cp.r" → σ.arrs b = σ0.arrs b) ∧
    (∀ b, (σ.arrs b).length = (σ0.arrs b).length) ∧
    (∀ y, y ≠ "cp.i" → σ.vars y = σ0.vars y) with hI_def
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "cp.i" < k)
      (.seq (.store "cp.r" (.get cmj (.add (.var "cp.s") (.var "cp.i")))
          (.lit 0))
        (.assign "cp.i" (.add (.var "cp.i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "cp.i" = σ.vars "cp.i" + 1) 10 := by
    rintro σ ⟨⟨h1, h2, hile, h3, h4, h5, h6, h7, h8⟩, hlt⟩
    set i := σ.vars "cp.i" with hi_def
    have hiB : i < B := by omega
    have h1B : (1 : ℕ) < B := by omega
    set e : Fin N := Impl.restrictEmb X ⟨i, hlt⟩ with he_def
    have heN : (e : ℕ) < N := e.2
    have hraLσ : N ≤ (σ.arrs "cp.r").length := by
      rw [h7 "cp.r"]; exact hraL0
    have hread : (Expr.get cmj (.add (.var "cp.s") (.var "cp.i"))).evalB B σ
        = some (e : ℕ) := by
      have hadd := evalB_bin (op := .add)
        (evalB_var (x := "cp.s") (by rw [h1]; omega))
        (evalB_var (x := "cp.i") hiB)
        (by rw [Bop.apply_add, h1]; omega)
      rw [Bop.apply_add, h1] at hadd
      refine evalB_get hadd (getElemQ_of_getD (by rw [h3]; omega) ?_)
        (by omega)
      rw [h3]
      exact hrow0 i hlt
    set σ1 := σ.setArr "cp.r" (e : ℕ) 0 with hσ1
    have hr1 : Run B (.store "cp.r"
        (.get cmj (.add (.var "cp.s") (.var "cp.i"))) (.lit 0)) σ σ1 6 :=
      Run.store hread (evalB_lit (n := 0) (by omega)) (by omega)
    have hi1 : σ1.vars "cp.i" = i := by rw [hσ1, vars_setArr]
    have hbump : (Expr.add (.var "cp.i") (.lit 1)).evalB B σ1
        = some (i + 1) := by
      have hvi : (Expr.var "cp.i").evalB B σ1 = some i := by
        rw [← hi1]
        exact evalB_var (by rw [hi1]; exact hiB)
      have h := evalB_bin (op := .add) hvi (evalB_lit h1B)
        (by rw [Bop.apply_add]; omega)
      rwa [Bop.apply_add] at h
    have hinj : ∀ (t : ℕ) (ht : t < k), t ≠ i →
        (Impl.restrictEmb X ⟨t, ht⟩ : ℕ) ≠ (e : ℕ) := by
      intro t ht hti hcontra
      have h := (Impl.restrictEmb X).injective (Fin.ext hcontra)
      exact hti (by simpa using congrArg Fin.val h)
    refine ⟨σ1.setVar "cp.i" (i + 1),
      (hr1.seq (Run.assign hbump)).mono (by simp), ?_, ?_⟩
    · have hvarsA : ∀ y, y ≠ "cp.i" →
          (σ1.setVar "cp.i" (i + 1)).vars y = σ.vars y := by
        intro y hy
        rw [vars_setVar, if_neg hy, hσ1, vars_setArr]
      have hraA : (σ1.setVar "cp.i" (i + 1)).arrs "cp.r"
          = (σ.arrs "cp.r").set (e : ℕ) 0 := by
        rw [arrs_setVar, hσ1, arrs_setArr, if_pos rfl]
      have hctr : (σ1.setVar "cp.i" (i + 1)).vars "cp.i" = i + 1 := by
        rw [vars_setVar, if_pos rfl]
      refine ⟨by rw [hvarsA _ (by decide)]; exact h1,
        by rw [hvarsA _ (by decide)]; exact h2,
        by rw [hctr]; omega,
        by rw [arrs_setVar, hσ1, arrs_setArr, if_neg hcm_ra]; exact h3,
        ?_, ?_, ?_, ?_, ?_⟩
      · intro t ht htlt
        rw [hctr] at htlt
        rw [hraA]
        by_cases hti : t = i
        · subst hti
          rw [getD_set_self (by omega)]
        · rw [getD_set_ne (hinj t ht hti)]
          exact h4 t ht (by omega)
      · intro p hp hnp
        rw [hraA, getD_set_ne (Ne.symm (hnp i hlt))]
        exact h5 p hp hnp
      · intro b hb
        rw [arrs_setVar, hσ1, arrs_setArr, if_neg hb]
        exact h6 b hb
      · intro b
        rw [arrs_setVar, hσ1, length_arrs_setArr]
        exact h7 b
      · intro y hy
        rw [hvarsA y hy]
        exact h8 y hy
    · rw [vars_setVar, if_pos rfl]
  obtain ⟨σ', hrun, hI', hctr'⟩ :=
    (Spec.forRangeZero "cp.i" "cp.n" I k 10 (by omega)
      (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.2.1) hbody) σ0
      (show I (σ0.setVar "cp.i" 0) by
        refine ⟨by rw [vars_setVar, if_neg (by decide)]; exact hs0,
          by rw [vars_setVar, if_neg (by decide)]; exact hn0,
          by rw [vars_setVar, if_pos rfl]; omega,
          by rw [arrs_setVar], ?_, ?_, ?_, ?_, ?_⟩
        · intro t ht htlt
          rw [vars_setVar, if_pos rfl] at htlt
          omega
        · intro p hp hnp
          rw [arrs_setVar]
          exact hra0 p hp hnp
        · intro b _; rw [arrs_setVar]
        · intro b; rw [arrs_setVar]
        · intro y hy; rw [vars_setVar, if_neg hy])
  obtain ⟨-, -, -, -, h4', h5', h6', h7', h8'⟩ := hI'
  refine ⟨σ', hrun.mono (by omega), ?_, h6', h7', h8'⟩
  intro p hp
  by_cases hpX : (⟨p, hp⟩ : Fin N) ∈ X
  · set t0 : Fin X.ncard := (setEquiv X).symm ⟨⟨p, hp⟩, hpX⟩ with ht0_def
    have hembF : Impl.restrictEmb X ⟨(t0 : ℕ), t0.2⟩ = ⟨p, hp⟩ := by
      have h : (⟨(t0 : ℕ), t0.2⟩ : Fin X.ncard) = t0 := Fin.ext rfl
      rw [Impl.restrictEmb_apply, h, ht0_def, Equiv.apply_symm_apply]
    have h := h4' (t0 : ℕ) t0.2 (by rw [hctr']; exact t0.2)
    rwa [congrArg Fin.val hembF] at h
  · refine h5' p hp ?_
    intro t ht hcontra
    have heq : Impl.restrictEmb X ⟨t, ht⟩ = ⟨p, hp⟩ := Fin.ext hcontra
    exact absurd (heq ▸ Impl.restrictEmb_mem X ⟨t, ht⟩) hpX

open Classical in
/-- **§5f's width-array pass**: scanning the batch bits in ascending
order and padding with the centre's name leaves exactly the abstract
`pad`-enumeration — cell `p` is the `p`-th sorted member of the bit
set below its size, the pad value beyond. -/
theorem prepWidth_spec {B k width : ℕ} (M : Set (Fin k)) (c0 : ℕ)
    (hkB : k < B) (hwB : width < B) (hMw : M.ncard ≤ width) (hc0 : c0 < k) :
    Spec B
      (fun σ => σ.vars "cp.n" = k ∧ σ.vars "cp.z" = c0 ∧
        (σ.arrs "cp.w").length = width ∧
        k ≤ (σ.arrs "cp.b").length ∧
        (∀ t : ℕ, ∀ ht : t < k,
          (σ.arrs "cp.b").getD t 0
            = if (⟨t, ht⟩ : Fin k) ∈ M then 1 else 0))
      (prepWidthCom width)
      (fun σ σ' =>
        (∀ p, p < width →
          (σ'.arrs "cp.w").getD p 0
            = if h : p < M.ncard then (((setEquiv M ⟨p, h⟩ : ↥M) : Fin k) : ℕ)
              else c0) ∧
        (∀ b, b ≠ "cp.w" → σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ y, y ≠ "cp.i" → y ≠ "cp.k" → y ≠ "cp.e" → σ'.vars y = σ.vars y))
      ((30 * k + 6) + (12 * width + 20)) := by
  intro σ0 hσ0
  obtain ⟨hn0, hz0, hwaL0, hbbL0, hbits0⟩ := hσ0
  have hMk : M.ncard ≤ k := set_ncard_le_card M
  -- §A the counter zero
  set σA := σ0.setVar "cp.k" 0 with hσA
  have hrA : Run B (.assign "cp.k" (.lit 0)) σ0 σA 2 :=
    Run.assign (evalB_lit (n := 0) (by omega))
  -- §B the scan loop
  set J : Env → Prop := fun σ =>
    σ.vars "cp.n" = k ∧ σ.vars "cp.z" = c0 ∧ σ.vars "cp.i" ≤ k ∧
    σ.vars "cp.k" = (M ∩ {x : Fin k | (x : ℕ) < σ.vars "cp.i"}).ncard ∧
    (∀ p, p < σ.vars "cp.k" →
      (σ.arrs "cp.w").getD p 0 < σ.vars "cp.i" ∧
      ∀ hw : (σ.arrs "cp.w").getD p 0 < k,
        (⟨(σ.arrs "cp.w").getD p 0, hw⟩ : Fin k) ∈ M) ∧
    (∀ p q, p < q → q < σ.vars "cp.k" →
      (σ.arrs "cp.w").getD p 0 < (σ.arrs "cp.w").getD q 0) ∧
    (∀ t : ℕ, ∀ ht : t < k, t < σ.vars "cp.i" → (⟨t, ht⟩ : Fin k) ∈ M →
      ∃ p, p < σ.vars "cp.k" ∧ (σ.arrs "cp.w").getD p 0 = t) ∧
    (∀ b, b ≠ "cp.w" → σ.arrs b = σ0.arrs b) ∧
    (∀ b, (σ.arrs b).length = (σ0.arrs b).length) ∧
    (∀ y, y ≠ "cp.i" → y ≠ "cp.k" → σ.vars y = σ0.vars y) with hJ_def
  have hcnt_le : ∀ i : ℕ, (M ∩ {x : Fin k | (x : ℕ) < i}).ncard ≤ M.ncard :=
    fun i => Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite M)
  have hbody : Spec B (fun σ => J σ ∧ σ.vars "cp.i" < k)
      (.seq (.ite (.eq (.get "cp.b" (.var "cp.i")) (.lit 1))
          (.seq (.store "cp.w" (.var "cp.k") (.var "cp.i"))
            (.assign "cp.k" (.add (.var "cp.k") (.lit 1))))
          .skip)
        (.assign "cp.i" (.add (.var "cp.i") (.lit 1))))
      (fun σ σ' => J σ' ∧ σ'.vars "cp.i" = σ.vars "cp.i" + 1) 16 := by
    rintro σ ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, hlt⟩
    set i := σ.vars "cp.i" with hi_def
    set K := σ.vars "cp.k" with hK_def
    have hiB : i < B := by omega
    have h1B : (1 : ℕ) < B := by omega
    have hbbLσ : k ≤ (σ.arrs "cp.b").length := by
      rw [h9 "cp.b"]; exact hbbL0
    have hwaLσ : (σ.arrs "cp.w").length = width := by
      rw [h9 "cp.w"]; exact hwaL0
    have hbitσ : (σ.arrs "cp.b").getD i 0
        = if (⟨i, hlt⟩ : Fin k) ∈ M then 1 else 0 := by
      rw [h8 "cp.b" (by decide)]
      exact hbits0 i hlt
    -- the bit read
    have hvi : (Expr.var "cp.i").evalB B σ = some i :=
      evalB_var hiB
    have hget : (Expr.get "cp.b" (.var "cp.i")).evalB B σ
        = some (if (⟨i, hlt⟩ : Fin k) ∈ M then 1 else 0) := by
      refine evalB_get hvi (getElemQ_of_getD (by omega) hbitσ) ?_
      split <;> omega
    have hcond : (Cond.eq (.get "cp.b" (.var "cp.i")) (.lit 1)).evalB B σ
        = some ((if (⟨i, hlt⟩ : Fin k) ∈ M then 1 else 0) == 1) :=
      evalB_condEq hget (evalB_lit h1B)
    by_cases hmem : (⟨i, hlt⟩ : Fin k) ∈ M
    · -- member: store and bump the pointer
      have hcondT : (Cond.eq (.get "cp.b" (.var "cp.i")) (.lit 1)).evalB B σ
          = some true := by
        rw [hcond, if_pos hmem]
        rfl
      -- the pointer is strictly below the batch size
      have hKlt : K < M.ncard := by
        have hss : (M ∩ {x : Fin k | (x : ℕ) < i}) ⊂ M := by
          refine Set.ssubset_iff_of_subset Set.inter_subset_left |>.mpr ?_
          exact ⟨⟨i, hlt⟩, hmem, fun hc => absurd hc.2 (by simp)⟩
        have hlt2 := Set.ncard_lt_ncard hss (Set.toFinite M)
        omega
      have hKw : K < width := lt_of_lt_of_le hKlt hMw
      have hKB : K < B := by omega
      set σ1 := σ.setArr "cp.w" K i with hσ1
      have hr1 : Run B (.store "cp.w" (.var "cp.k") (.var "cp.i")) σ σ1 3 :=
        Run.store (evalB_var hKB) hvi (by omega)
      have hK1 : σ1.vars "cp.k" = K := by rw [hσ1, vars_setArr]
      have hbump1 : (Expr.add (.var "cp.k") (.lit 1)).evalB B σ1
          = some (K + 1) := by
        have hv : (Expr.var "cp.k").evalB B σ1 = some K := by
          rw [← hK1]
          exact evalB_var (by rw [hK1]; exact hKB)
        have h := evalB_bin (op := .add) hv (evalB_lit h1B)
          (by rw [Bop.apply_add]; omega)
        rwa [Bop.apply_add] at h
      set σ2 := σ1.setVar "cp.k" (K + 1) with hσ2
      have hi2 : σ2.vars "cp.i" = i := by
        rw [hσ2, vars_setVar, if_neg (by decide), hσ1, vars_setArr]
      have hbump2 : (Expr.add (.var "cp.i") (.lit 1)).evalB B σ2
          = some (i + 1) := by
        have hv : (Expr.var "cp.i").evalB B σ2 = some i := by
          rw [← hi2]
          exact evalB_var (by rw [hi2]; exact hiB)
        have h := evalB_bin (op := .add) hv (evalB_lit h1B)
          (by rw [Bop.apply_add]; omega)
        rwa [Bop.apply_add] at h
      refine ⟨σ2.setVar "cp.i" (i + 1),
        ((Run.ite_true hcondT (hr1.seq (Run.assign hbump1))).seq
          (Run.assign hbump2)).mono (by simp), ?_, ?_⟩
      · -- the invariant at the stepped state
        have hwaA : (σ2.setVar "cp.i" (i + 1)).arrs "cp.w"
            = (σ.arrs "cp.w").set K i := by
          rw [arrs_setVar, hσ2, arrs_setVar, hσ1, arrs_setArr, if_pos rfl]
        have hothA : ∀ b, b ≠ "cp.w" →
            (σ2.setVar "cp.i" (i + 1)).arrs b = σ.arrs b := by
          intro b hb
          rw [arrs_setVar, hσ2, arrs_setVar, hσ1, arrs_setArr, if_neg hb]
        have hvarsA : ∀ y, y ≠ "cp.i" → y ≠ "cp.k" →
            (σ2.setVar "cp.i" (i + 1)).vars y = σ.vars y := by
          intro y hy1 hy2
          rw [vars_setVar, if_neg hy1, hσ2, vars_setVar, if_neg hy2, hσ1,
            vars_setArr]
        have hctrA : (σ2.setVar "cp.i" (i + 1)).vars "cp.i" = i + 1 := by
          rw [vars_setVar, if_pos rfl]
        have hKA : (σ2.setVar "cp.i" (i + 1)).vars "cp.k" = K + 1 := by
          rw [vars_setVar, if_neg (by decide), hσ2, vars_setVar, if_pos rfl]
        have hins : M ∩ {x : Fin k | (x : ℕ) < i + 1}
            = insert (⟨i, hlt⟩ : Fin k) (M ∩ {x : Fin k | (x : ℕ) < i}) := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_insert_iff]
          constructor
          · rintro ⟨hxM, hxi⟩
            by_cases hxe : (x : ℕ) = i
            · exact Or.inl (Fin.ext hxe)
            · exact Or.inr ⟨hxM, by omega⟩
          · rintro (rfl | ⟨hxM, hxi⟩)
            · exact ⟨hmem, Nat.lt_succ_self i⟩
            · exact ⟨hxM, by omega⟩
        have hcntA : (M ∩ {x : Fin k | (x : ℕ) < i + 1}).ncard = K + 1 := by
          rw [hins, Set.ncard_insert_of_notMem
            (fun hc => absurd hc.2 (by simp)) (Set.toFinite _), ← h4]
        refine ⟨by rw [hvarsA _ (by decide) (by decide)]; exact h1,
          by rw [hvarsA _ (by decide) (by decide)]; exact h2,
          by rw [hctrA]; omega,
          by rw [hKA, hctrA, hcntA], ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- the members clause
          intro p hp
          rw [hKA] at hp
          rw [hwaA, hctrA]
          by_cases hpK : p = K
          · subst hpK
            rw [getD_set_self (by omega)]
            exact ⟨by omega, fun hw => by
              have h : (⟨i, hw⟩ : Fin k) = ⟨i, hlt⟩ := rfl
              rw [h]; exact hmem⟩
          · rw [getD_set_ne hpK]
            obtain ⟨ha, hb⟩ := h5 p (by omega)
            exact ⟨by omega, hb⟩
        · -- the sortedness clause
          intro p q hpq hq
          rw [hKA] at hq
          rw [hwaA]
          by_cases hqK : q = K
          · subst hqK
            rw [getD_set_self (by omega), getD_set_ne (by omega)]
            exact (h5 p (by omega)).1
          · rw [getD_set_ne hqK, getD_set_ne (by omega)]
            exact h6 p q hpq (by omega)
        · -- the completeness clause
          intro t ht htlt htM
          rw [hctrA] at htlt
          rw [hKA, hwaA]
          by_cases hti : t = i
          · subst hti
            exact ⟨K, by omega, by rw [getD_set_self (by omega)]⟩
          · obtain ⟨p, hp, hpe⟩ := h7 t ht (by omega) htM
            exact ⟨p, by omega, by rw [getD_set_ne (by omega)]; exact hpe⟩
        · intro b hb
          rw [hothA b hb]
          exact h8 b hb
        · intro b
          rw [arrs_setVar, hσ2, arrs_setVar, hσ1, length_arrs_setArr]
          exact h9 b
        · intro y hy1 hy2
          rw [hvarsA y hy1 hy2]
          exact h10 y hy1 hy2
      · rw [vars_setVar, if_pos rfl]
    · -- not a member: skip
      have hcondF : (Cond.eq (.get "cp.b" (.var "cp.i")) (.lit 1)).evalB B σ
          = some false := by
        rw [hcond, if_neg hmem]
        rfl
      have hbump : (Expr.add (.var "cp.i") (.lit 1)).evalB B σ
          = some (i + 1) := by
        have h := evalB_bin (op := .add) hvi (evalB_lit h1B)
          (by rw [Bop.apply_add]; omega)
        rwa [Bop.apply_add] at h
      refine ⟨σ.setVar "cp.i" (i + 1),
        ((Run.ite_false hcondF Run.skip).seq (Run.assign hbump)).mono
          (by simp), ?_, ?_⟩
      · have hext : M ∩ {x : Fin k | (x : ℕ) < i + 1}
            = M ∩ {x : Fin k | (x : ℕ) < i} := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
          constructor
          · rintro ⟨hxM, hxi⟩
            refine ⟨hxM, ?_⟩
            by_cases hxe : (x : ℕ) = i
            · exact absurd (show x = (⟨i, hlt⟩ : Fin k) from Fin.ext hxe)
                (fun hc => hmem (hc ▸ hxM))
            · omega
          · rintro ⟨hxM, hxi⟩
            exact ⟨hxM, by omega⟩
        refine ⟨by rw [vars_setVar, if_neg (by decide)]; exact h1,
          by rw [vars_setVar, if_neg (by decide)]; exact h2,
          by rw [vars_setVar, if_pos rfl]; omega,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have hv1 : (σ.setVar "cp.i" (i + 1)).vars "cp.k"
              = σ.vars "cp.k" := by
            rw [vars_setVar, if_neg (by decide)]
          have hv2 : (σ.setVar "cp.i" (i + 1)).vars "cp.i" = i + 1 := by
            rw [vars_setVar, if_pos rfl]
          rw [hv1, hv2, hext]
          exact h4
        · intro p hp
          rw [vars_setVar, if_neg (by decide)] at hp
          rw [arrs_setVar, vars_setVar, if_pos rfl]
          obtain ⟨ha, hb⟩ := h5 p hp
          exact ⟨by omega, hb⟩
        · intro p q hpq hq
          rw [vars_setVar, if_neg (by decide)] at hq
          rw [arrs_setVar]
          exact h6 p q hpq hq
        · intro t ht htlt htM
          rw [vars_setVar, if_pos rfl] at htlt
          rw [vars_setVar, if_neg (by decide), arrs_setVar]
          by_cases hti : t = i
          · subst hti
            exact absurd htM hmem
          · exact h7 t ht (by omega) htM
        · intro b hb
          rw [arrs_setVar]
          exact h8 b hb
        · intro b
          rw [arrs_setVar]
          exact h9 b
        · intro y hy1 hy2
          rw [vars_setVar, if_neg hy1]
          exact h10 y hy1 hy2
      · rw [vars_setVar, if_pos rfl]
  -- run the scan from the zeroed pointer
  obtain ⟨σB, hrB, hJB, hiB'⟩ :=
    (Spec.forRangeZero "cp.i" "cp.n" J k 16 hkB
      (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.1) hbody) σA
      (show J (σA.setVar "cp.i" 0) by
        have hempty : (M ∩ {x : Fin k | (x : ℕ) < 0}) = ∅ := by
          ext x
          simp
        refine ⟨?_, ?_, by rw [vars_setVar, if_pos rfl]; omega, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_⟩
        · rw [vars_setVar, if_neg (by decide), hσA, vars_setVar,
            if_neg (by decide)]
          exact hn0
        · rw [vars_setVar, if_neg (by decide), hσA, vars_setVar,
            if_neg (by decide)]
          exact hz0
        · have hv1 : ((σA.setVar "cp.i" 0)).vars "cp.k"
              = σA.vars "cp.k" := by
            rw [vars_setVar, if_neg (by decide)]
          have hv2 : ((σA.setVar "cp.i" 0)).vars "cp.i" = 0 := by
            rw [vars_setVar, if_pos rfl]
          rw [hv1, hv2, hempty, Set.ncard_empty, hσA, vars_setVar,
            if_pos rfl]
        · intro p hp
          rw [vars_setVar, if_neg (by decide), hσA, vars_setVar,
            if_pos rfl] at hp
          omega
        · intro p q hpq hq
          rw [vars_setVar, if_neg (by decide), hσA, vars_setVar,
            if_pos rfl] at hq
          omega
        · intro t ht htlt
          rw [vars_setVar, if_pos rfl] at htlt
          omega
        · intro b _
          rw [arrs_setVar, hσA, arrs_setVar]
        · intro b
          rw [arrs_setVar, hσA, arrs_setVar]
        · intro y hy1 hy2
          rw [vars_setVar, if_neg hy1, hσA, vars_setVar, if_neg hy2])
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8, hB9, hB10⟩ := hJB
  -- the scan pointer holds the batch size
  have hKB' : σB.vars "cp.k" = M.ncard := by
    have huniv : (M ∩ {x : Fin k | (x : ℕ) < k}) = M := by
      refine Set.inter_eq_left.mpr fun x _ => x.2
    rw [hB4, hiB', huniv]
  -- the scanned prefix is the sorted enumeration
  have hwbound : ∀ p, p < M.ncard → (σB.arrs "cp.w").getD p 0 < k := by
    intro p hp
    have h := (hB5 p (by rw [hKB']; exact hp)).1
    rw [hiB'] at h
    exact h
  have henum := scan_eq_setEquiv M (fun p => (σB.arrs "cp.w").getD p 0)
    hwbound
    (fun p q hpq hq => hB6 p q hpq (by rw [hKB']; exact hq))
    (fun p hp => (hB5 p (by rw [hKB']; exact hp)).2 (hwbound p hp))
    (fun x hx => by
      obtain ⟨p, hp, hpe⟩ := hB7 (x : ℕ) x.2 (by rw [hiB']; exact x.2)
        (by rw [show (⟨(x : ℕ), x.2⟩ : Fin k) = x from Fin.ext rfl]
            exact hx)
      exact ⟨p, by rw [← hKB']; exact hp, hpe⟩)
  -- the pad phase
  set σC := σB.setVar "cp.e" width with hσC
  have hrC : Run B (.assign "cp.e" (.lit width)) σB σC 2 :=
    Run.assign (evalB_lit hwB)
  set Kinv : Env → Prop := fun σ =>
    σ.vars "cp.e" = width ∧ σ.vars "cp.z" = c0 ∧
    σ.vars "cp.k" ≤ width ∧ M.ncard ≤ σ.vars "cp.k" ∧
    (∀ p, p < M.ncard →
      (σ.arrs "cp.w").getD p 0 = (σB.arrs "cp.w").getD p 0) ∧
    (∀ p, M.ncard ≤ p → p < σ.vars "cp.k" →
      (σ.arrs "cp.w").getD p 0 = c0) ∧
    (σ.arrs "cp.w").length = width ∧
    (∀ b, b ≠ "cp.w" → σ.arrs b = σC.arrs b) ∧
    (∀ b, (σ.arrs b).length = (σC.arrs b).length) ∧
    (∀ y, y ≠ "cp.k" → σ.vars y = σC.vars y) with hKinv_def
  have hpadBody : Spec B (fun σ => Kinv σ ∧ σ.vars "cp.k" < width)
      (.seq (.store "cp.w" (.var "cp.k") (.var "cp.z"))
        (.assign "cp.k" (.add (.var "cp.k") (.lit 1))))
      (fun σ σ' => Kinv σ' ∧ σ'.vars "cp.k" = σ.vars "cp.k" + 1) 7 := by
    rintro σ ⟨⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩, hlt⟩
    set K := σ.vars "cp.k" with hKd
    have hKB2 : K < B := by omega
    have h1B : (1 : ℕ) < B := by omega
    have hvz : (Expr.var "cp.z").evalB B σ = some c0 := by
      rw [← k2]
      exact evalB_var (by rw [k2]; omega)
    set σ1 := σ.setArr "cp.w" K c0 with hσ1
    have hr1 : Run B (.store "cp.w" (.var "cp.k") (.var "cp.z")) σ σ1 3 := by
      have hidx : σ.vars "cp.k" < (σ.arrs "cp.w").length := by omega
      exact Run.congr (Run.store (evalB_var hKB2) hvz hidx) rfl
    have hK1 : σ1.vars "cp.k" = K := by rw [hσ1, vars_setArr]
    have hbump : (Expr.add (.var "cp.k") (.lit 1)).evalB B σ1
        = some (K + 1) := by
      have hv : (Expr.var "cp.k").evalB B σ1 = some K := by
        rw [← hK1]
        exact evalB_var (by rw [hK1]; exact hKB2)
      have h := evalB_bin (op := .add) hv (evalB_lit h1B)
        (by rw [Bop.apply_add]; omega)
      rwa [Bop.apply_add] at h
    refine ⟨σ1.setVar "cp.k" (K + 1),
      (hr1.seq (Run.assign hbump)).mono (by simp), ?_, ?_⟩
    · have hwaA : (σ1.setVar "cp.k" (K + 1)).arrs "cp.w"
          = (σ.arrs "cp.w").set K c0 := by
        rw [arrs_setVar, hσ1, arrs_setArr, if_pos rfl]
      have hothA : ∀ b, b ≠ "cp.w" →
          (σ1.setVar "cp.k" (K + 1)).arrs b = σ.arrs b := by
        intro b hb
        rw [arrs_setVar, hσ1, arrs_setArr, if_neg hb]
      have hvarsA : ∀ y, y ≠ "cp.k" →
          (σ1.setVar "cp.k" (K + 1)).vars y = σ.vars y := by
        intro y hy
        rw [vars_setVar, if_neg hy, hσ1, vars_setArr]
      have hKA : (σ1.setVar "cp.k" (K + 1)).vars "cp.k" = K + 1 := by
        rw [vars_setVar, if_pos rfl]
      refine ⟨by rw [hvarsA _ (by decide)]; exact k1,
        by rw [hvarsA _ (by decide)]; exact k2,
        by rw [hKA]; omega, by rw [hKA]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro p hp
        rw [hwaA, getD_set_ne (by omega)]
        exact k5 p hp
      · intro p hp1 hp2
        rw [hKA] at hp2
        rw [hwaA]
        by_cases hpK : p = K
        · subst hpK
          rw [getD_set_self (by omega)]
        · rw [getD_set_ne hpK]
          exact k6 p hp1 (by omega)
      · rw [hwaA, List.length_set]
        exact k7
      · intro b hb
        rw [hothA b hb]
        exact k8 b hb
      · intro b
        rw [arrs_setVar, hσ1, length_arrs_setArr]
        exact k9 b
      · intro y hy
        rw [hvarsA y hy]
        exact k10 y hy
    · rw [vars_setVar, if_pos rfl]
  obtain ⟨σD, hrD, hKD, hkD⟩ :=
    (Spec.forRange "cp.k" "cp.e" Kinv width 7 (11 * width + 4)
      (fun σ hσ => by have := hσ.2.2.1; omega)
      (fun σ hσ => by have := hσ.1; omega)
      (fun σ hσ => hσ.1) (fun σ hσ => hσ.2.2.1) hpadBody
      (fun σ hσ => hσ)
      (fun σ hσ => by
        have h4 : (7 + 4) * (width - σ.vars "cp.k") + 4
            ≤ 11 * width + 4 := by
          have : width - σ.vars "cp.k" ≤ width := Nat.sub_le _ _
          omega
        exact h4)) σC
      (show Kinv σC by
        have hwaC : σC.arrs "cp.w" = σB.arrs "cp.w" := by
          rw [hσC, arrs_setVar]
        refine ⟨by rw [hσC, vars_setVar, if_pos rfl], ?_, ?_, ?_, ?_, ?_,
          ?_, fun b _ => rfl, fun b => rfl, ?_⟩
        · rw [hσC, vars_setVar, if_neg (by decide)]
          exact hB2
        · rw [hσC, vars_setVar, if_neg (by decide), hKB']
          exact hMw
        · rw [hσC, vars_setVar, if_neg (by decide), hKB']
        · intro p hp
          rw [hwaC]
        · intro p hp1 hp2
          rw [hσC, vars_setVar, if_neg (by decide), hKB'] at hp2
          omega
        · rw [hwaC, hB9 "cp.w"]
          exact hwaL0
        · intro y hy
          rfl)
  obtain ⟨hD1, hD2, hD3, hD4, hD5, hD6, hD7, hD8, hD9, hD10⟩ := hKD
  -- assemble the whole phase
  refine ⟨σD, ?_, ?_, ?_, ?_, ?_⟩
  · -- the run, at the stated budget
    have hr : Run B (prepWidthCom width) σ0 σD
        (2 + ((16 + 4) * k + 6 + (2 + (11 * width + 4)))) := by
      exact (hrA.seq (hrB.seq (hrC.seq hrD))).mono (by omega)
    exact hr.mono (by omega)
  · -- the cells
    intro p hp
    by_cases hpM : p < M.ncard
    · rw [dif_pos hpM]
      have h := hD5 p hpM
      have h2 := congrArg Fin.val (henum p hpM)
      rw [h]
      exact h2.symm
    · rw [dif_neg hpM]
      exact hD6 p (by omega) (by omega)
  · -- other arrays
    intro b hb
    rw [hD8 b hb, hσC, arrs_setVar, hB8 b hb]
  · -- lengths
    intro b
    rw [hD9 b, hσC, arrs_setVar, hB9 b]
  · -- scalars
    intro y hy1 hy2 hy3
    rw [hD10 y hy2, hσC, vars_setVar, if_neg hy3, hB10 y hy1 hy2]

open Classical in
/-- **§5e's batch trace**: scanning the parent channel's row `u` sets
the batch bit of every cluster member named in some column — the trace
of the row's lists on the cluster, in rank space. -/
theorem prepBatch_spec {B N ℓpj hbj : ℕ} {histj ctr : String}
    (X : Set (Fin N)) (u : ℕ) (W : ℕ → List ℕ)
    (hNB : N < B) (hlpB : ℓpj < B) (hhbB : hbj + 1 < B)
    (hposB : N * ℓpj * (hbj + 1) < B) (huN : u < N)
    (hlen : ∀ e, e < ℓpj → (W e).length ≤ hbj)
    (hval : ∀ e, e < ℓpj → ∀ x ∈ W e, x < N)
    (hctr1 : ctr ≠ "cp.i") (hctr2 : ctr ≠ "cp.j") (hctr3 : ctr ≠ "cp.k")
    (hctr4 : ctr ≠ "cp.y") (hctr5 : ctr ≠ "cp.g") (hctr6 : ctr ≠ "cp.e")
    (hhist_bb : histj ≠ "cp.b") :
    Spec B
      (fun σ => σ.vars ctr = u ∧
        N * ℓpj * (hbj + 1) ≤ (σ.arrs histj).length ∧
        (∀ e, e < ℓpj →
          (σ.arrs histj).getD ((u * ℓpj + e) * (hbj + 1)) 0
            = (W e).length ∧
          ∀ i : ℕ, ∀ hi : i < (W e).length,
            (σ.arrs histj).getD ((u * ℓpj + e) * (hbj + 1) + 1 + i) 0
              = (W e)[i]) ∧
        N ≤ (σ.arrs "cp.r").length ∧ X.ncard ≤ (σ.arrs "cp.b").length ∧
        (∀ t : ℕ, ∀ ht : t < X.ncard,
          (σ.arrs "cp.r").getD ((Impl.restrictEmb X ⟨t, ht⟩ : ℕ)) 0
            = t + 1) ∧
        (∀ p, p < N → (∀ t : ℕ, ∀ ht : t < X.ncard,
            (Impl.restrictEmb X ⟨t, ht⟩ : ℕ) ≠ p) →
          (σ.arrs "cp.r").getD p 0 = 0) ∧
        (∀ t, t < X.ncard → (σ.arrs "cp.b").getD t 0 = 0 ∨
          (σ.arrs "cp.b").getD t 0 = 1))
      (prepBatchCom histj ctr ℓpj hbj)
      (fun σ σ' =>
        (∀ t : ℕ, ∀ ht : t < X.ncard,
          (σ'.arrs "cp.b").getD t 0
            = if ((σ.arrs "cp.b").getD t 0 = 1 ∨ ∃ e, e < ℓpj ∧
                  (Impl.restrictEmb X ⟨t, ht⟩ : ℕ) ∈ W e)
              then 1 else 0) ∧
        (∀ b, b ≠ "cp.b" → σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ y, y ≠ "cp.i" → y ≠ "cp.j" → y ≠ "cp.k" → y ≠ "cp.y" →
          y ≠ "cp.g" → y ≠ "cp.e" → σ'.vars y = σ.vars y))
      ((26 * hbj + 26) * ℓpj + 8) := by
  intro σ0 hσ0
  obtain ⟨hctr0, hhL0, hcells0, hraL0, hbbL0, hmk0, hz0, hbb01⟩ := hσ0
  have hkN : X.ncard ≤ N := set_ncard_le_card X
  set k := X.ncard with hk_def
  -- position arithmetic
  have hblock : ∀ e, e < ℓpj →
      (u * ℓpj + e) * (hbj + 1) + (hbj + 1) ≤ N * ℓpj * (hbj + 1) := by
    intro e he
    have h1 : u * ℓpj + e + 1 ≤ N * ℓpj := by
      have h2 : u * ℓpj + e + 1 ≤ u * ℓpj + ℓpj := by omega
      have h3 : u * ℓpj + ℓpj = (u + 1) * ℓpj := (Nat.succ_mul u ℓpj).symm
      have h4 : (u + 1) * ℓpj ≤ N * ℓpj :=
        Nat.mul_le_mul_right ℓpj (by omega)
      omega
    calc (u * ℓpj + e) * (hbj + 1) + (hbj + 1)
        = (u * ℓpj + e + 1) * (hbj + 1) := (Nat.succ_mul _ _).symm
      _ ≤ N * ℓpj * (hbj + 1) := Nat.mul_le_mul_right _ h1
  -- §A the outer bound cell
  set σA := σ0.setVar "cp.e" ℓpj with hσA
  have hrA : Run B (.assign "cp.e" (.lit ℓpj)) σ0 σA 2 :=
    Run.assign (evalB_lit hlpB)
  -- §B the outer loop invariant
  set IO : Env → Prop := fun σ =>
    σ.vars "cp.e" = ℓpj ∧ σ.vars ctr = u ∧ σ.vars "cp.i" ≤ ℓpj ∧
    (∀ t : ℕ, ∀ ht : t < k,
      (σ.arrs "cp.b").getD t 0
        = if ((σ0.arrs "cp.b").getD t 0 = 1 ∨ ∃ e, e < σ.vars "cp.i" ∧
              (Impl.restrictEmb X ⟨t, ht⟩ : ℕ) ∈ W e)
          then 1 else 0) ∧
    (∀ b, b ≠ "cp.b" → σ.arrs b = σ0.arrs b) ∧
    (∀ b, (σ.arrs b).length = (σ0.arrs b).length) ∧
    (∀ y, y ≠ "cp.i" → y ≠ "cp.j" → y ≠ "cp.k" → y ≠ "cp.y" →
      y ≠ "cp.g" → y ≠ "cp.e" → σ.vars y = σ0.vars y) with hIO_def
  -- §C the outer body
  have hbody : Spec B (fun σ => IO σ ∧ σ.vars "cp.i" < ℓpj)
      (.seq (.assign "cp.k"
          (.mul (.add (.mul (.var ctr) (.lit ℓpj)) (.var "cp.i"))
            (.lit (hbj + 1))))
        (.seq (.assign "cp.y" (.get histj (.var "cp.k")))
          (.seq (.seq (.assign "cp.j" (.lit 0))
              (.while (.lt (.var "cp.j") (.var "cp.y"))
                (.seq (.assign "cp.g"
                    (.get histj
                      (.add (.add (.var "cp.k") (.lit 1)) (.var "cp.j"))))
                  (.seq (.ite (.lt (.lit 0) (.get "cp.r" (.var "cp.g")))
                      (.store "cp.b"
                        (.sub (.get "cp.r" (.var "cp.g")) (.lit 1))
                        (.lit 1))
                      .skip)
                    (.assign "cp.j" (.add (.var "cp.j") (.lit 1)))))))
            (.assign "cp.i" (.add (.var "cp.i") (.lit 1))))))
      (fun σ σ' => IO σ' ∧ σ'.vars "cp.i" = σ.vars "cp.i" + 1)
      (26 * hbj + 22) := by
    rintro σ ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hlt⟩
    set e := σ.vars "cp.i" with he_def
    set q := (u * ℓpj + e) * (hbj + 1) with hq_def
    have hqB : q < B := by
      have := hblock e hlt
      omega
    have huℓB : u * ℓpj + e < B := by
      have h := hblock e hlt
      have h2 : u * ℓpj + e ≤ (u * ℓpj + e) * (hbj + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hulB : u * ℓpj < B := by omega
    have heB : e < B := by omega
    have hlenE := hlen e hlt
    have hlenB : (W e).length < B := by omega
    -- the block base
    have hkexpr : (Expr.mul (.add (.mul (.var ctr) (.lit ℓpj))
        (.var "cp.i")) (.lit (hbj + 1))).evalB B σ = some q := by
      have hvc : (Expr.var ctr).evalB B σ = some u := by
        rw [← h2]
        exact evalB_var (by rw [h2]; omega)
      have hm1 := evalB_bin (op := .mul) hvc (evalB_lit hlpB)
        (by rw [Bop.apply_mul]; exact hulB)
      rw [Bop.apply_mul] at hm1
      have hvi : (Expr.var "cp.i").evalB B σ = some e :=
        evalB_var (by omega)
      have ha1 := evalB_bin (op := .add) hm1 hvi
        (by rw [Bop.apply_add]; exact huℓB)
      rw [Bop.apply_add] at ha1
      have hm2 := evalB_bin (op := .mul) ha1 (evalB_lit hhbB)
        (by rw [Bop.apply_mul]; exact hqB)
      rwa [Bop.apply_mul] at hm2
    set σ1 := σ.setVar "cp.k" q with hσ1
    have hr1 : Run B (.assign "cp.k"
        (.mul (.add (.mul (.var ctr) (.lit ℓpj)) (.var "cp.i"))
          (.lit (hbj + 1)))) σ σ1 9 :=
      (Run.assign hkexpr).mono (by simp)
    -- the length read
    have hk1 : σ1.vars "cp.k" = q := by rw [hσ1, vars_setVar, if_pos rfl]
    have hhistσ1 : σ1.arrs histj = σ0.arrs histj := by
      rw [hσ1, arrs_setVar]
      exact h5 histj hhist_bb
    have hyexpr : (Expr.get histj (.var "cp.k")).evalB B σ1
        = some (W e).length := by
      have hv : (Expr.var "cp.k").evalB B σ1 = some q := by
        rw [← hk1]
        exact evalB_var (by rw [hk1]; exact hqB)
      refine evalB_get hv (getElemQ_of_getD ?_ ?_) hlenB
      · rw [hhistσ1]
        have := hblock e hlt
        omega
      · rw [hhistσ1]
        exact (hcells0 e hlt).1
    set σ2 := σ1.setVar "cp.y" (W e).length with hσ2
    have hr2 : Run B (.assign "cp.y" (.get histj (.var "cp.k"))) σ1 σ2 3 :=
      Run.assign hyexpr
    -- §D the inner loop
    set IJ : Env → Prop := fun τ =>
      τ.vars "cp.e" = ℓpj ∧ τ.vars ctr = u ∧ τ.vars "cp.i" = e ∧
      τ.vars "cp.k" = q ∧ τ.vars "cp.y" = (W e).length ∧
      τ.vars "cp.j" ≤ (W e).length ∧
      (∀ t : ℕ, ∀ ht : t < k,
        (τ.arrs "cp.b").getD t 0
          = if ((σ0.arrs "cp.b").getD t 0 = 1 ∨ (∃ e', e' < e ∧
                (Impl.restrictEmb X ⟨t, ht⟩ : ℕ) ∈ W e') ∨
                ∃ i : ℕ, ∃ hi : i < (W e).length, i < τ.vars "cp.j" ∧
                  (W e)[i] = (Impl.restrictEmb X ⟨t, ht⟩ : ℕ))
            then 1 else 0) ∧
      (∀ b, b ≠ "cp.b" → τ.arrs b = σ0.arrs b) ∧
      (∀ b, (τ.arrs b).length = (σ0.arrs b).length) ∧
      (∀ y, y ≠ "cp.i" → y ≠ "cp.j" → y ≠ "cp.k" → y ≠ "cp.y" →
        y ≠ "cp.g" → y ≠ "cp.e" → τ.vars y = σ0.vars y) with hIJ_def
    have hinner : Spec B (fun τ => IJ τ ∧ τ.vars "cp.j" < (W e).length)
        (.seq (.assign "cp.g"
            (.get histj
              (.add (.add (.var "cp.k") (.lit 1)) (.var "cp.j"))))
          (.seq (.ite (.lt (.lit 0) (.get "cp.r" (.var "cp.g")))
              (.store "cp.b"
                (.sub (.get "cp.r" (.var "cp.g")) (.lit 1)) (.lit 1))
              .skip)
            (.assign "cp.j" (.add (.var "cp.j") (.lit 1)))))
        (fun τ τ' => IJ τ' ∧ τ'.vars "cp.j" = τ.vars "cp.j" + 1) 22 := by
      rintro τ ⟨⟨j1, j2, j3, j4, j5, j6, j7, j8, j9, j10⟩, hjlt⟩
      set jj := τ.vars "cp.j" with hjj_def
      have hjB : jj < B := by omega
      have h1B : (1 : ℕ) < B := by omega
      set x : ℕ := (W e)[jj] with hx_def
      have hxN : x < N := hval e hlt _ (List.getElem_mem hjlt)
      have hraLτ : N ≤ (τ.arrs "cp.r").length := by
        rw [j9 "cp.r"]
        exact hraL0
      have hbbLτ : k ≤ (τ.arrs "cp.b").length := by
        rw [j9 "cp.b"]
        exact hbbL0
      have hraτ : τ.arrs "cp.r" = σ0.arrs "cp.r" := j8 "cp.r" (by decide)
      have hhistτ : τ.arrs histj = σ0.arrs histj := j8 histj hhist_bb
      -- the name read
      have hgexpr : (Expr.get histj
          (.add (.add (.var "cp.k") (.lit 1)) (.var "cp.j"))).evalB B τ
          = some x := by
        have hvk : (Expr.var "cp.k").evalB B τ = some q := by
          rw [← j4]
          exact evalB_var (by rw [j4]; exact hqB)
        have ha1 := evalB_bin (op := .add) hvk (evalB_lit h1B)
          (by rw [Bop.apply_add]
              have := hblock e hlt
              omega)
        rw [Bop.apply_add] at ha1
        have hvj : (Expr.var "cp.j").evalB B τ = some jj := by
          rw [hjj_def]
          exact evalB_var (by rw [← hjj_def]; exact hjB)
        have ha2 := evalB_bin (op := .add) ha1 hvj
          (by rw [Bop.apply_add]
              have := hblock e hlt
              omega)
        rw [Bop.apply_add] at ha2
        refine evalB_get ha2 (getElemQ_of_getD ?_ ?_) (by omega)
        · rw [hhistτ]
          have := hblock e hlt
          omega
        · rw [hhistτ]
          exact (hcells0 e hlt).2 jj hjlt
      set τ1 := τ.setVar "cp.g" x with hτ1
      have hr1' : Run B (.assign "cp.g"
          (.get histj (.add (.add (.var "cp.k") (.lit 1)) (.var "cp.j"))))
          τ τ1 7 := Run.assign hgexpr
      have hg1 : τ1.vars "cp.g" = x := by rw [hτ1, vars_setVar, if_pos rfl]
      have hraτ1 : τ1.arrs "cp.r" = σ0.arrs "cp.r" := by
        rw [hτ1, arrs_setVar]
        exact hraτ
      -- the rank read: marked or not
      by_cases hxmem : ∃ s : ℕ, ∃ hs : s < k,
          (Impl.restrictEmb X ⟨s, hs⟩ : ℕ) = x
      · -- a cluster member: the bit is set
        obtain ⟨s, hs, hsx⟩ := hxmem
        have hrx : (τ1.arrs "cp.r").getD x 0 = s + 1 := by
          rw [hraτ1, ← hsx]
          exact hmk0 s hs
        have hgread : (Expr.get "cp.r" (.var "cp.g")).evalB B τ1
            = some (s + 1) := by
          have hv : (Expr.var "cp.g").evalB B τ1 = some x := by
            rw [← hg1]
            exact evalB_var (by rw [hg1]; omega)
          refine evalB_get hv (getElemQ_of_getD ?_ hrx) (by omega)
          rw [hraτ1]
          omega
        have hcondT : (Cond.lt (.lit 0)
            (.get "cp.r" (.var "cp.g"))).evalB B τ1 = some true := by
          rw [evalB_condLt (evalB_lit (n := 0) (by omega)) hgread]
          simp
        have hidxexpr : (Expr.sub (.get "cp.r" (.var "cp.g"))
            (.lit 1)).evalB B τ1 = some s := by
          have h := evalB_bin (op := .sub) hgread
            (evalB_lit (n := 1) h1B) (by rw [Bop.apply_sub]; omega)
          rw [Bop.apply_sub] at h
          rw [show s + 1 - 1 = s from by omega] at h
          exact h
        set τ2 := τ1.setArr "cp.b" s 1 with hτ2
        have hr2' : Run B (.store "cp.b"
            (.sub (.get "cp.r" (.var "cp.g")) (.lit 1)) (.lit 1))
            τ1 τ2 6 := by
          refine Run.store hidxexpr (evalB_lit (n := 1) h1B) ?_
          rw [hτ1, arrs_setVar]
          omega
        have hj2 : τ2.vars "cp.j" = jj := by
          rw [hτ2, vars_setArr, hτ1, vars_setVar, if_neg (by decide)]
        have hbump : (Expr.add (.var "cp.j") (.lit 1)).evalB B τ2
            = some (jj + 1) := by
          have hv : (Expr.var "cp.j").evalB B τ2 = some jj := by
            rw [← hj2]
            exact evalB_var (by rw [hj2]; exact hjB)
          have h := evalB_bin (op := .add) hv (evalB_lit h1B)
            (by rw [Bop.apply_add]; omega)
          rwa [Bop.apply_add] at h
        refine ⟨τ2.setVar "cp.j" (jj + 1),
          ((hr1'.seq ((Run.ite_true hcondT hr2').seq
            (Run.assign hbump))).mono (by simp)), ?_, ?_⟩
        · -- the invariant, stepped
          have hbbA : (τ2.setVar "cp.j" (jj + 1)).arrs "cp.b"
              = (τ.arrs "cp.b").set s 1 := by
            rw [arrs_setVar, hτ2, arrs_setArr, if_pos rfl, hτ1,
              arrs_setVar]
          have hothA : ∀ b, b ≠ "cp.b" →
              (τ2.setVar "cp.j" (jj + 1)).arrs b = τ.arrs b := by
            intro b hb
            rw [arrs_setVar, hτ2, arrs_setArr, if_neg hb, hτ1, arrs_setVar]
          have hvarsA : ∀ y, y ≠ "cp.j" → y ≠ "cp.g" →
              (τ2.setVar "cp.j" (jj + 1)).vars y = τ.vars y := by
            intro y hy1 hy2
            rw [vars_setVar, if_neg hy1, hτ2, vars_setArr, hτ1,
              vars_setVar, if_neg hy2]
          have hjA : (τ2.setVar "cp.j" (jj + 1)).vars "cp.j" = jj + 1 := by
            rw [vars_setVar, if_pos rfl]
          have hinj : ∀ (t : ℕ) (ht : t < k), t ≠ s →
              (Impl.restrictEmb X ⟨t, ht⟩ : ℕ)
                ≠ (Impl.restrictEmb X ⟨s, hs⟩ : ℕ) := by
            intro t ht hts hcontra
            have h := (Impl.restrictEmb X).injective (Fin.ext hcontra)
            exact hts (by simpa using congrArg Fin.val h)
          refine ⟨by rw [hvarsA _ (by decide) (by decide)]; exact j1,
            by rw [hvarsA _ hctr2 hctr5]; exact j2,
            by rw [hvarsA _ (by decide) (by decide)]; exact j3,
            by rw [hvarsA _ (by decide) (by decide)]; exact j4,
            by rw [hvarsA _ (by decide) (by decide)]; exact j5,
            by rw [hjA]; omega, ?_, ?_, ?_, ?_⟩
          · -- the bits
            intro t ht
            rw [hbbA, hjA]
            by_cases hts : t = s
            · subst hts
              rw [getD_set_self (by omega),
                if_pos (Or.inr (Or.inr ⟨jj, hjlt, by omega, hsx.symm⟩))]
            · rw [getD_set_ne hts, j7 t ht]
              refine if_congr ?_ rfl rfl
              constructor
              · rintro (h | h | ⟨i2, hi2, hi2j, hi2e⟩)
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr ⟨i2, hi2, by omega, hi2e⟩)
              · rintro (h | h | ⟨i2, hi2, hi2j, hi2e⟩)
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
                · refine Or.inr (Or.inr ⟨i2, hi2, ?_, hi2e⟩)
                  rcases Nat.lt_succ_iff_lt_or_eq.mp hi2j with h2 | h2
                  · exact h2
                  · exfalso
                    subst h2
                    have hxe : x = (Impl.restrictEmb X ⟨t, ht⟩ : ℕ) := by
                      rw [hx_def]
                      exact hi2e
                    exact hinj t ht hts (hxe.symm.trans hsx.symm)
          · intro b hb
            rw [hothA b hb]
            exact j8 b hb
          · intro b
            rw [arrs_setVar, hτ2, length_arrs_setArr, hτ1, arrs_setVar]
            exact j9 b
          · intro y hy1 hy2 hy3 hy4 hy5 hy6
            rw [hvarsA y hy2 hy5]
            exact j10 y hy1 hy2 hy3 hy4 hy5 hy6
        · rw [vars_setVar, if_pos rfl]
      · -- not a member: the rank is zero, skip
        have hrx : (τ1.arrs "cp.r").getD x 0 = 0 := by
          rw [hraτ1]
          refine hz0 x hxN ?_
          intro t ht hcontra
          exact hxmem ⟨t, ht, hcontra⟩
        have hgread : (Expr.get "cp.r" (.var "cp.g")).evalB B τ1
            = some 0 := by
          have hv : (Expr.var "cp.g").evalB B τ1 = some x := by
            rw [← hg1]
            exact evalB_var (by rw [hg1]; omega)
          refine evalB_get hv (getElemQ_of_getD ?_ hrx) (by omega)
          rw [hraτ1]
          omega
        have hcondF : (Cond.lt (.lit 0)
            (.get "cp.r" (.var "cp.g"))).evalB B τ1 = some false := by
          rw [evalB_condLt (evalB_lit (n := 0) (by omega)) hgread]
          simp
        have hj1 : τ1.vars "cp.j" = jj := by
          rw [hτ1, vars_setVar, if_neg (by decide)]
        have hbump : (Expr.add (.var "cp.j") (.lit 1)).evalB B τ1
            = some (jj + 1) := by
          have hv : (Expr.var "cp.j").evalB B τ1 = some jj := by
            rw [← hj1]
            exact evalB_var (by rw [hj1]; exact hjB)
          have h := evalB_bin (op := .add) hv (evalB_lit h1B)
            (by rw [Bop.apply_add]; omega)
          rwa [Bop.apply_add] at h
        refine ⟨τ1.setVar "cp.j" (jj + 1),
          ((hr1'.seq ((Run.ite_false hcondF Run.skip).seq
            (Run.assign hbump))).mono (by simp)), ?_, ?_⟩
        · have hbbA : (τ1.setVar "cp.j" (jj + 1)).arrs "cp.b"
              = τ.arrs "cp.b" := by
            rw [arrs_setVar, hτ1, arrs_setVar]
          have hothA : ∀ b,
              (τ1.setVar "cp.j" (jj + 1)).arrs b = τ.arrs b := by
            intro b
            rw [arrs_setVar, hτ1, arrs_setVar]
          have hvarsA : ∀ y, y ≠ "cp.j" → y ≠ "cp.g" →
              (τ1.setVar "cp.j" (jj + 1)).vars y = τ.vars y := by
            intro y hy1 hy2
            rw [vars_setVar, if_neg hy1, hτ1, vars_setVar, if_neg hy2]
          have hjA : (τ1.setVar "cp.j" (jj + 1)).vars "cp.j" = jj + 1 := by
            rw [vars_setVar, if_pos rfl]
          refine ⟨by rw [hvarsA _ (by decide) (by decide)]; exact j1,
            by rw [hvarsA _ hctr2 hctr5]; exact j2,
            by rw [hvarsA _ (by decide) (by decide)]; exact j3,
            by rw [hvarsA _ (by decide) (by decide)]; exact j4,
            by rw [hvarsA _ (by decide) (by decide)]; exact j5,
            by rw [hjA]; omega, ?_, ?_, ?_, ?_⟩
          · intro t ht
            rw [hbbA, hjA, j7 t ht]
            refine if_congr ?_ rfl rfl
            constructor
            · rintro (h | h | ⟨i2, hi2, hi2j, hi2e⟩)
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr ⟨i2, hi2, by omega, hi2e⟩)
            · rintro (h | h | ⟨i2, hi2, hi2j, hi2e⟩)
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · refine Or.inr (Or.inr ⟨i2, hi2, ?_, hi2e⟩)
                rcases Nat.lt_succ_iff_lt_or_eq.mp hi2j with h2 | h2
                · exact h2
                · exfalso
                  subst h2
                  refine hxmem ⟨t, ht, ?_⟩
                  rw [hx_def]
                  exact hi2e.symm
          · intro b hb
            rw [hothA b]
            exact j8 b hb
          · intro b
            rw [arrs_setVar, hτ1, arrs_setVar]
            exact j9 b
          · intro y hy1 hy2 hy3 hy4 hy5 hy6
            rw [hvarsA y hy2 hy5]
            exact j10 y hy1 hy2 hy3 hy4 hy5 hy6
        · rw [vars_setVar, if_pos rfl]
    -- run the inner loop from the initialized state
    obtain ⟨τe, hre, hIJe, hje⟩ :=
      (Spec.forRangeZero "cp.j" "cp.y" IJ (W e).length 22 hlenB
        (fun τ hτ => hτ.2.2.2.2.2.1) (fun τ hτ => hτ.2.2.2.2.1) hinner) σ2
        (show IJ (σ2.setVar "cp.j" 0) by
          have hv : ∀ y, y ≠ "cp.j" → y ≠ "cp.y" → y ≠ "cp.k" →
              (σ2.setVar "cp.j" 0).vars y = σ.vars y := by
            intro y hy1 hy2 hy3
            rw [vars_setVar, if_neg hy1, hσ2, vars_setVar, if_neg hy2,
              hσ1, vars_setVar, if_neg hy3]
          have harr : ∀ b, (σ2.setVar "cp.j" 0).arrs b = σ.arrs b := by
            intro b
            rw [arrs_setVar, hσ2, arrs_setVar, hσ1, arrs_setVar]
          refine ⟨by rw [hv _ (by decide) (by decide) (by decide)]; exact h1,
            by rw [hv _ hctr2 hctr4 hctr3]; exact h2,
            by rw [hv _ (by decide) (by decide) (by decide)],
            ?_, ?_, by rw [vars_setVar, if_pos rfl]; omega, ?_, ?_, ?_, ?_⟩
          · rw [vars_setVar, if_neg (by decide), hσ2, vars_setVar,
              if_neg (by decide), hσ1, vars_setVar, if_pos rfl]
          · rw [vars_setVar, if_neg (by decide), hσ2, vars_setVar,
              if_pos rfl]
          · intro t ht
            rw [harr, h4 t ht]
            refine if_congr ?_ rfl rfl
            constructor
            · rintro (h | ⟨e', he', hme⟩)
              · exact Or.inl h
              · exact Or.inr (Or.inl ⟨e', he', hme⟩)
            · rintro (h | ⟨e', he', hme⟩ | ⟨i2, hi2, hi2j, -⟩)
              · exact Or.inl h
              · exact Or.inr ⟨e', he', hme⟩
              · exfalso
                rw [vars_setVar, if_pos rfl] at hi2j
                omega
          · intro b hb
            rw [harr]
            exact h5 b hb
          · intro b
            rw [harr]
            exact h6 b
          · intro y hy1 hy2 hy3 hy4 hy5 hy6
            rw [hv y hy2 hy4 hy3]
            exact h7 y hy1 hy2 hy3 hy4 hy5 hy6)
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hIJe
    -- the counter bump
    have hbumpO : (Expr.add (.var "cp.i") (.lit 1)).evalB B τe
        = some (e + 1) := by
      have hv : (Expr.var "cp.i").evalB B τe = some e := by
        rw [← e3]
        exact evalB_var (by rw [e3]; omega)
      have h := evalB_bin (op := .add) hv (evalB_lit (n := 1) (by omega))
        (by rw [Bop.apply_add]; omega)
      rwa [Bop.apply_add] at h
    refine ⟨τe.setVar "cp.i" (e + 1),
      ((hr1.seq (hr2.seq (hre.seq (Run.assign hbumpO)))).mono
        (by simp; omega)), ?_, ?_⟩
    · -- the outer invariant at `e + 1`
      have hvarsA : ∀ y, y ≠ "cp.i" →
          (τe.setVar "cp.i" (e + 1)).vars y = τe.vars y := by
        intro y hy
        rw [vars_setVar, if_neg hy]
      have hiA : (τe.setVar "cp.i" (e + 1)).vars "cp.i" = e + 1 := by
        rw [vars_setVar, if_pos rfl]
      refine ⟨by rw [hvarsA _ (by decide)]; exact e1,
        by rw [hvarsA _ hctr1]; exact e2,
        by rw [hiA]; omega, ?_, ?_, ?_, ?_⟩
      · -- the bits, folded to `< e + 1`
        intro t ht
        rw [arrs_setVar, hiA, e7 t ht]
        refine if_congr ?_ rfl rfl
        rw [hje]
        constructor
        · rintro (h | ⟨e', he', hme⟩ | ⟨i2, hi2, -, hi2e⟩)
          · exact Or.inl h
          · exact Or.inr ⟨e', by omega, hme⟩
          · refine Or.inr ⟨e, by omega, ?_⟩
            rw [← hi2e]
            exact List.getElem_mem hi2
        · rintro (h | ⟨e', he', hme⟩)
          · exact Or.inl h
          · rcases Nat.lt_succ_iff_lt_or_eq.mp he' with h2 | h2
            · exact Or.inr (Or.inl ⟨e', h2, hme⟩)
            · subst h2
              obtain ⟨i2, hi2, hi2e⟩ := List.mem_iff_getElem.mp hme
              exact Or.inr (Or.inr ⟨i2, hi2, hi2, hi2e⟩)
      · intro b hb
        rw [arrs_setVar]
        exact e8 b hb
      · intro b
        rw [arrs_setVar]
        exact e9 b
      · intro y hy1 hy2 hy3 hy4 hy5 hy6
        rw [hvarsA y hy1]
        exact e10 y hy1 hy2 hy3 hy4 hy5 hy6
    · rw [vars_setVar, if_pos rfl]
  -- §E run the outer loop
  obtain ⟨σ', hrun, hIO', hi'⟩ :=
    (Spec.forRangeZero "cp.i" "cp.e" IO ℓpj (26 * hbj + 22) hlpB
      (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.1) hbody) σA
      (show IO (σA.setVar "cp.i" 0) by
        have hv : ∀ y, y ≠ "cp.i" → y ≠ "cp.e" →
            (σA.setVar "cp.i" 0).vars y = σ0.vars y := by
          intro y hy1 hy2
          rw [vars_setVar, if_neg hy1, hσA, vars_setVar, if_neg hy2]
        have harr : ∀ b, (σA.setVar "cp.i" 0).arrs b = σ0.arrs b := by
          intro b
          rw [arrs_setVar, hσA, arrs_setVar]
        refine ⟨?_, by rw [hv _ hctr1 hctr6]; exact hctr0,
          by rw [vars_setVar, if_pos rfl]; omega, ?_, ?_, ?_, ?_⟩
        · rw [vars_setVar, if_neg (by decide), hσA, vars_setVar,
            if_pos rfl]
        · intro t ht
          rw [harr, vars_setVar, if_pos rfl]
          rcases hbb01 t ht with h0 | h1
          · rw [h0, if_neg]
            rintro (h | ⟨e', he', -⟩)
            · omega
            · omega
          · rw [h1, if_pos (Or.inl rfl)]
        · intro b _
          rw [harr]
        · intro b
          rw [harr]
        · intro y hy1 hy2 hy3 hy4 hy5 hy6
          rw [hv y hy1 hy6])
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := hIO'
  refine ⟨σ', (hrA.seq hrun).mono (by
    have h26 : 26 * hbj + 22 + 4 = 26 * hbj + 26 := by omega
    rw [h26]
    omega), ?_, o5, o6, o7⟩
  intro t ht
  rw [o4 t ht, hi']

/-! ## §6d The colour write

One row of the `(j+1)` colour region, written slot by slot by the
compile-time writer list: old colours copied off the pre-isolation
rows, the marker constant, the `pd`/`pu` slots thresholded off the
profile tables. Every writer of a slot writes that slot's
`recordProfilesMS` bit, so the sequential list lands the whole row at
the colouring — no distinctness needed. -/

section ColourWrite

variable {L : ℕ} (S : Setup L) (j : ℕ) {kk : ℕ}
  (f0 : Fin (S.pal j) → Set (Fin kk))
  (Dp : Fin S.width → Fin kk → ℕ)
  (Dc : Fin (relPal (S.pal j)) → Fin (kk + 1) → ℕ)
  (a : ℕ) (ha : a < kk)

open Classical in
/-- The row's target bit at one slot. -/
private noncomputable def colBit (d : Fin (isoPal (relPal (S.pal j)) S.width S.R)) :
    ℕ :=
  if (⟨a, ha⟩ : Fin kk) ∈
      Impl.recordProfilesMS S.R (relColoring f0 Set.univ) Dp Dc d
    then 1 else 0

open Classical in
/-- **The row-state precondition** the writers read: the counter at the
row, the pre-isolation colour cells, the profile-table cells, the
allocation room, and the word bounds. -/
private def ColRowPre (B : ℕ) (σ : Env) : Prop :=
  σ.vars "cp.i" = a ∧
  (∀ c : Fin (S.pal j),
    (σ.arrs "cp.c").getD (a * S.pal j + (c : ℕ)) 0
      = if (⟨a, ha⟩ : Fin kk) ∈ f0 c then 1 else 0) ∧
  (∀ b' : Fin S.width,
    (σ.arrs (lv "cq.d" (b' : ℕ))).getD a 0 = Dp b' ⟨a, ha⟩) ∧
  (∀ c : Fin (relPal (S.pal j)),
    (σ.arrs (lv "cq.u" (c : ℕ))).getD a 0
      = Dc c (Fin.castSucc ⟨a, ha⟩)) ∧
  a * S.pal (j + 1) + S.pal (j + 1)
    ≤ (σ.arrs (arenaNames (j + 1)).col).length ∧
  a * S.pal j + S.pal j ≤ (σ.arrs "cp.c").length ∧
  (∀ b' : Fin S.width, a < (σ.arrs (lv "cq.d" (b' : ℕ))).length) ∧
  (∀ c : Fin (relPal (S.pal j)), a < (σ.arrs (lv "cq.u" (c : ℕ))).length) ∧
  a * S.pal (j + 1) + S.pal (j + 1) < B ∧ a * S.pal j + S.pal j < B ∧
  1 < B ∧
  (∀ b' : Fin S.width, Dp b' ⟨a, ha⟩ < B) ∧
  (∀ c : Fin (relPal (S.pal j)), Dc c (Fin.castSucc ⟨a, ha⟩) < B) ∧
  S.R + 2 < B ∧ a < B

open Classical in
/-- `ColRowPre` survives a store into the colour region (it reads
other regions and one counter only). -/
private theorem colRowPre_setArr {B : ℕ} {σ : Env} (h : ColRowPre S j f0 Dp Dc a ha B σ)
    (hcol1 : (arenaNames (j + 1)).col ≠ "cp.c")
    (hcol2 : ∀ i, (arenaNames (j + 1)).col ≠ lv "cq.d" i)
    (hcol3 : ∀ i, (arenaNames (j + 1)).col ≠ lv "cq.u" i)
    (p v : ℕ) :
    ColRowPre S j f0 Dp Dc a ha B
      (σ.setArr (arenaNames (j + 1)).col p v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15⟩ := h
  refine ⟨by rw [vars_setArr]; exact h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h9, h10, h11, h12, h13, h14, h15⟩
  · intro c
    rw [arrs_setArr, if_neg (Ne.symm hcol1)]
    exact h2 c
  · intro b'
    rw [arrs_setArr, if_neg (Ne.symm (hcol2 (b' : ℕ)))]
    exact h3 b'
  · intro c
    rw [arrs_setArr, if_neg (Ne.symm (hcol3 (c : ℕ)))]
    exact h4 c
  · rw [length_arrs_setArr]
    exact h5
  · rw [arrs_setArr, if_neg (Ne.symm hcol1)]
    exact h6
  · intro b'
    rw [arrs_setArr, if_neg (Ne.symm (hcol2 (b' : ℕ)))]
    exact h7 b'
  · intro c
    rw [arrs_setArr, if_neg (Ne.symm (hcol3 (c : ℕ)))]
    exact h8 c

open Classical in
/-- **Every writer writes its slot's bit**: pointwise down the parallel
slot list, each writer runs from any `ColRowPre` state to the same
state with its slot's colour cell set to that slot's
`recordProfilesMS` bit, within the uniform per-writer budget. -/
private theorem colWriters_forall₂ {B : ℕ} :
    List.Forall₂
      (fun w (dd : Fin (isoPal (relPal (S.pal j)) S.width S.R)) =>
        ∀ σ, ColRowPre S j f0 Dp Dc a ha B σ →
          Run B w σ
            (σ.setArr (arenaNames (j + 1)).col
              (a * S.pal (j + 1) + (dd : ℕ))
              (colBit S j f0 Dp Dc a ha dd)) 30)
      (colWriters S j) (colSlots S j) := by
  rw [colWriters, colSlots]
  refine forall₂_append' (forall₂_append' (forall₂_append'
    (forall₂_map_map _ _ _ ?_)
    (List.Forall₂.cons ?_ List.Forall₂.nil))
    (forall₂_map_map _ _ _ ?_))
    (forall₂_map_map _ _ _ ?_)
  · -- an old colour: copy the cell
    intro c _hc
    set d := isoOld (Λ := relPal (S.pal j)) (mb := S.width) (cap := S.R)
      c.castSucc with hd_def
    intro σ hσ
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14, h15⟩ := hσ
    have hdlt : ((d : Fin (isoPal (relPal (S.pal j)) S.width S.R)) : ℕ)
        < S.pal (j + 1) := d.2
    have hprodB : a * S.pal (j + 1) < B :=
      lt_of_le_of_lt (Nat.le_add_right _ _) h9
    have hsumB : a * S.pal (j + 1) + (d : ℕ) < B :=
      lt_trans (Nat.add_lt_add_left hdlt _) h9
    have hv : (Expr.var "cp.i").evalB B σ = some a := by
      rw [← h1]
      exact evalB_var (by rw [h1]; omega)
    have hidx : (Expr.add (.mul (.var "cp.i") (.lit (S.pal (j + 1))))
        (.lit ((d : Fin (isoPal (relPal (S.pal j)) S.width S.R)) : ℕ))).evalB
          B σ = some (a * S.pal (j + 1) + (d : ℕ)) := by
      have hm := evalB_bin (op := .mul) hv
        (evalB_lit (n := S.pal (j + 1))
          (lt_of_le_of_lt (Nat.le_add_left _ _) h9))
        (by rw [Bop.apply_mul]; exact hprodB)
      rw [Bop.apply_mul] at hm
      have hadd := evalB_bin (op := .add) hm
        (evalB_lit (n := ((d : Fin (isoPal (relPal (S.pal j)) S.width
          S.R)) : ℕ))
          (lt_trans hdlt (lt_of_le_of_lt (Nat.le_add_left _ _) h9)))
        (by rw [Bop.apply_add]; exact hsumB)
      rwa [Bop.apply_add] at hadd
    have hbit : colBit S j f0 Dp Dc a ha d
        = if (⟨a, ha⟩ : Fin kk) ∈ f0 c then 1 else 0 := by
      rw [colBit]
      refine if_congr ?_ rfl rfl
      rw [hd_def, Impl.recordProfilesMS_old, relColoring_castSucc]
    have hclt : (c : ℕ) < S.pal j := c.2
    have hval : (Expr.get "cp.c"
        (.add (.mul (.var "cp.i") (.lit (S.pal j))) (.lit (c : ℕ)))).evalB
          B σ = some (colBit S j f0 Dp Dc a ha d) := by
      have hprodB2 : a * S.pal j < B :=
        lt_of_le_of_lt (Nat.le_add_right _ _) h10
      have hsumB2 : a * S.pal j + (c : ℕ) < B :=
        lt_trans (Nat.add_lt_add_left hclt _) h10
      have hm := evalB_bin (op := .mul) hv
        (evalB_lit (n := S.pal j)
          (lt_of_le_of_lt (Nat.le_add_left _ _) h10))
        (by rw [Bop.apply_mul]; exact hprodB2)
      rw [Bop.apply_mul] at hm
      have hadd := evalB_bin (op := .add) hm
        (evalB_lit (n := (c : ℕ)) (by omega))
        (by rw [Bop.apply_add]; exact hsumB2)
      rw [Bop.apply_add] at hadd
      have hlt6 : a * S.pal j + (c : ℕ) < (σ.arrs "cp.c").length := by
        omega
      refine evalB_get hadd (getElemQ_of_getD hlt6 ?_) ?_
      · rw [hbit]
        exact h2 c
      · rw [hbit]
        split <;> omega
    refine (Run.store hidx hval (by omega)).mono (by simp)
  · -- the marker
    set d := isoOld (Λ := relPal (S.pal j)) (mb := S.width) (cap := S.R)
      (Fin.last (S.pal j)) with hd_def
    intro σ hσ
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14, h15⟩ := hσ
    have hdlt : ((d : Fin (isoPal (relPal (S.pal j)) S.width S.R)) : ℕ)
        < S.pal (j + 1) := d.2
    have hprodB : a * S.pal (j + 1) < B :=
      lt_of_le_of_lt (Nat.le_add_right _ _) h9
    have hsumB : a * S.pal (j + 1) + (d : ℕ) < B :=
      lt_trans (Nat.add_lt_add_left hdlt _) h9
    have hv : (Expr.var "cp.i").evalB B σ = some a := by
      rw [← h1]
      exact evalB_var (by rw [h1]; omega)
    have hidx : (Expr.add (.mul (.var "cp.i") (.lit (S.pal (j + 1))))
        (.lit ((d : Fin (isoPal (relPal (S.pal j)) S.width S.R)) : ℕ))).evalB
          B σ = some (a * S.pal (j + 1) + (d : ℕ)) := by
      have hm := evalB_bin (op := .mul) hv
        (evalB_lit (n := S.pal (j + 1))
          (lt_of_le_of_lt (Nat.le_add_left _ _) h9))
        (by rw [Bop.apply_mul]; exact hprodB)
      rw [Bop.apply_mul] at hm
      have hadd := evalB_bin (op := .add) hm
        (evalB_lit (n := ((d : Fin (isoPal (relPal (S.pal j)) S.width
          S.R)) : ℕ))
          (lt_trans hdlt (lt_of_le_of_lt (Nat.le_add_left _ _) h9)))
        (by rw [Bop.apply_add]; exact hsumB)
      rwa [Bop.apply_add] at hadd
    have hmem : (⟨a, ha⟩ : Fin kk) ∈
        Impl.recordProfilesMS S.R (relColoring f0 Set.univ) Dp Dc d := by
      rw [hd_def, Impl.recordProfilesMS_old, relColoring_last]
      exact Set.mem_univ _
    have hbit : colBit S j f0 Dp Dc a ha d = 1 := by
      rw [colBit, if_pos hmem]
    have hval : (Expr.lit 1).evalB B σ
        = some (colBit S j f0 Dp Dc a ha d) := by
      rw [hbit]
      exact evalB_lit (by omega)
    refine (Run.store hidx hval (by omega)).mono (by simp)
  · -- a batch-distance slot: threshold the pd table
    intro p _hp
    set b' := p.1 with hb'_def
    set a' := p.2 with ha'_def
    set d := isoPd (Λ := relPal (S.pal j)) (mb := S.width) (cap := S.R)
      b' a' with hd_def
    intro σ hσ
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14, h15⟩ := hσ
    have hdlt : ((d : Fin (isoPal (relPal (S.pal j)) S.width S.R)) : ℕ)
        < S.pal (j + 1) := d.2
    have hprodB : a * S.pal (j + 1) < B :=
      lt_of_le_of_lt (Nat.le_add_right _ _) h9
    have hsumB : a * S.pal (j + 1) + (d : ℕ) < B :=
      lt_trans (Nat.add_lt_add_left hdlt _) h9
    have hv : (Expr.var "cp.i").evalB B σ = some a := by
      rw [← h1]
      exact evalB_var (by rw [h1]; omega)
    have hidx : (Expr.add (.mul (.var "cp.i") (.lit (S.pal (j + 1))))
        (.lit ((d : Fin (isoPal (relPal (S.pal j)) S.width S.R)) : ℕ))).evalB
          B σ = some (a * S.pal (j + 1) + (d : ℕ)) := by
      have hm := evalB_bin (op := .mul) hv
        (evalB_lit (n := S.pal (j + 1))
          (lt_of_le_of_lt (Nat.le_add_left _ _) h9))
        (by rw [Bop.apply_mul]; exact hprodB)
      rw [Bop.apply_mul] at hm
      have hadd := evalB_bin (op := .add) hm
        (evalB_lit (n := ((d : Fin (isoPal (relPal (S.pal j)) S.width
          S.R)) : ℕ))
          (lt_trans hdlt (lt_of_le_of_lt (Nat.le_add_left _ _) h9)))
        (by rw [Bop.apply_add]; exact hsumB)
      rwa [Bop.apply_add] at hadd
    have hread : (Expr.get (lv "cq.d" (b' : ℕ)) (.var "cp.i")).evalB B σ
        = some (Dp b' ⟨a, ha⟩) := by
      exact evalB_get hv (getElemQ_of_getD (h7 b') (h3 b')) (h12 b')
    have hcond := evalB_condLt (evalB_lit (n := (a' : ℕ))
      (by have := a'.2; omega)) hread
    have hbit : colBit S j f0 Dp Dc a ha d
        = if Dp b' ⟨a, ha⟩ ≤ (a' : ℕ) then 1 else 0 := by
      rw [colBit]
      refine if_congr ?_ rfl rfl
      rw [hd_def, Impl.recordProfilesMS_pd]
      exact Iff.rfl
    by_cases hth : (a' : ℕ) < Dp b' ⟨a, ha⟩
    · have hcondT : (Cond.lt (.lit (a' : ℕ))
          (.get (lv "cq.d" (b' : ℕ)) (.var "cp.i"))).evalB B σ
          = some true := by
        rw [hcond]
        simp [hth]
      have hbit0 : colBit S j f0 Dp Dc a ha d = 0 := by
        rw [hbit]
        split
        · rename_i hcase
          exact absurd hcase (Nat.not_le.mpr hth)
        · rfl
      have hval : (Expr.lit 0).evalB B σ
          = some (colBit S j f0 Dp Dc a ha d) := by
        rw [hbit0]
        exact evalB_lit (by omega)
      exact (Run.ite_true hcondT
        (Run.store hidx hval (by omega))).mono (by simp)
    · have hcondF : (Cond.lt (.lit (a' : ℕ))
          (.get (lv "cq.d" (b' : ℕ)) (.var "cp.i"))).evalB B σ
          = some false := by
        rw [hcond]
        simp [hth]
      have hbit1 : colBit S j f0 Dp Dc a ha d = 1 := by
        rw [hbit]
        split
        · rfl
        · rename_i hcase
          exact absurd (Nat.not_lt.mp hth) hcase
      have hval : (Expr.lit 1).evalB B σ
          = some (colBit S j f0 Dp Dc a ha d) := by
        rw [hbit1]
        exact evalB_lit (by omega)
      exact (Run.ite_false hcondF
        (Run.store hidx hval (by omega))).mono (by simp)
  · -- a colour-distance slot: threshold the pu table
    intro p _hp
    set c := p.1 with hc_def
    set b' := p.2 with hb'_def
    set d := isoPu (Λ := relPal (S.pal j)) (mb := S.width) (cap := S.R)
      c b' with hd_def
    intro σ hσ
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14, h15⟩ := hσ
    have hdlt : ((d : Fin (isoPal (relPal (S.pal j)) S.width S.R)) : ℕ)
        < S.pal (j + 1) := d.2
    have hprodB : a * S.pal (j + 1) < B :=
      lt_of_le_of_lt (Nat.le_add_right _ _) h9
    have hsumB : a * S.pal (j + 1) + (d : ℕ) < B :=
      lt_trans (Nat.add_lt_add_left hdlt _) h9
    have hv : (Expr.var "cp.i").evalB B σ = some a := by
      rw [← h1]
      exact evalB_var (by rw [h1]; omega)
    have hidx : (Expr.add (.mul (.var "cp.i") (.lit (S.pal (j + 1))))
        (.lit ((d : Fin (isoPal (relPal (S.pal j)) S.width S.R)) : ℕ))).evalB
          B σ = some (a * S.pal (j + 1) + (d : ℕ)) := by
      have hm := evalB_bin (op := .mul) hv
        (evalB_lit (n := S.pal (j + 1))
          (lt_of_le_of_lt (Nat.le_add_left _ _) h9))
        (by rw [Bop.apply_mul]; exact hprodB)
      rw [Bop.apply_mul] at hm
      have hadd := evalB_bin (op := .add) hm
        (evalB_lit (n := ((d : Fin (isoPal (relPal (S.pal j)) S.width
          S.R)) : ℕ))
          (lt_trans hdlt (lt_of_le_of_lt (Nat.le_add_left _ _) h9)))
        (by rw [Bop.apply_add]; exact hsumB)
      rwa [Bop.apply_add] at hadd
    have hread : (Expr.get (lv "cq.u" (c : ℕ)) (.var "cp.i")).evalB B σ
        = some (Dc c (Fin.castSucc ⟨a, ha⟩)) := by
      exact evalB_get hv (getElemQ_of_getD (h8 c) (h4 c)) (h13 c)
    have hcond := evalB_condLt (evalB_lit (n := (b' : ℕ) + 1)
      (by have := b'.2; omega)) hread
    have hbit : colBit S j f0 Dp Dc a ha d
        = if Dc c (Fin.castSucc ⟨a, ha⟩) ≤ (b' : ℕ) + 1 then 1 else 0 := by
      rw [colBit]
      refine if_congr ?_ rfl rfl
      rw [hd_def, Impl.recordProfilesMS_pu]
      exact Iff.rfl
    by_cases hth : (b' : ℕ) + 1 < Dc c (Fin.castSucc ⟨a, ha⟩)
    · have hcondT : (Cond.lt (.lit ((b' : ℕ) + 1))
          (.get (lv "cq.u" (c : ℕ)) (.var "cp.i"))).evalB B σ
          = some true := by
        rw [hcond]
        exact congrArg some (decide_eq_true hth)
      have hbit0 : colBit S j f0 Dp Dc a ha d = 0 := by
        rw [hbit]
        split
        · rename_i hcase
          exact absurd hcase
            (show ¬ Dc c (Fin.castSucc ⟨a, ha⟩) ≤ (b' : ℕ) + 1 from
              Nat.not_le.mpr hth)
        · rfl
      have hval : (Expr.lit 0).evalB B σ
          = some (colBit S j f0 Dp Dc a ha d) := by
        rw [hbit0]
        exact evalB_lit (by omega)
      exact (Run.ite_true hcondT
        (Run.store hidx hval (by omega))).mono (by simp)
    · have hcondF : (Cond.lt (.lit ((b' : ℕ) + 1))
          (.get (lv "cq.u" (c : ℕ)) (.var "cp.i"))).evalB B σ
          = some false := by
        rw [hcond]
        exact congrArg some (decide_eq_false hth)
      have hbit1 : colBit S j f0 Dp Dc a ha d = 1 := by
        rw [hbit]
        split
        · rfl
        · rename_i hcase
          exact absurd
            (show Dc c (Fin.castSucc ⟨a, ha⟩) ≤ (b' : ℕ) + 1 from
              Nat.not_lt.mp hth) hcase
      have hval : (Expr.lit 1).evalB B σ
          = some (colBit S j f0 Dp Dc a ha d) := by
        rw [hbit1]
        exact evalB_lit (by omega)
      exact (Run.ite_false hcondF
        (Run.store hidx hval (by omega))).mono (by simp)

open Classical in
/-- **The writer list, composed**: every slot named in the parallel
list ends at its bit; unnamed cells, other arrays and every scalar are
untouched. Duplicated slots are harmless — every writer of a slot
writes that slot's bit. -/
private theorem writersRun {B : ℕ} {colC : String} {base : ℕ}
    {bit : ℕ → ℕ} {P : Env → Prop}
    (hP : ∀ σ, P σ → ∀ p v, P (σ.setArr colC p v)) :
    ∀ {l : List Com} {D : List ℕ},
      List.Forall₂ (fun w dd => ∀ σ, P σ →
        Run B w σ (σ.setArr colC (base + dd) (bit dd)) 30) l D →
      ∀ σ, P σ →
        ∃ σ', Run B (l.foldr .seq .skip) σ σ' (30 * l.length + 1) ∧
          (∀ dd ∈ D, base + dd < (σ.arrs colC).length →
            (σ'.arrs colC).getD (base + dd) 0 = bit dd) ∧
          (∀ p2, (∀ dd ∈ D, p2 ≠ base + dd) →
            (σ'.arrs colC).getD p2 0 = (σ.arrs colC).getD p2 0) ∧
          (∀ b, b ≠ colC → σ'.arrs b = σ.arrs b) ∧
          (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
          σ'.vars = σ.vars := by
  intro l D hF
  induction hF with
  | nil =>
    intro σ hσ
    refine ⟨σ, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩
    · show Run B .skip σ σ (30 * ([] : List Com).length + 1)
      exact Run.skip.mono (by simp)
    · intro dd hdd
      simp at hdd
  | @cons w dd l' D' hw hrest ih =>
    intro σ hσ
    obtain ⟨σ', hr', hcell', hkeep', hoth', hlen', hvars'⟩ :=
      ih (σ.setArr colC (base + dd) (bit dd)) (hP σ hσ _ _)
    refine ⟨σ', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Run B (.seq w (l'.foldr .seq .skip)) σ σ'
        (30 * (w :: l').length + 1)
      refine ((hw σ hσ).seq hr').mono ?_
      simp only [List.length_cons]
      omega
    · -- named cells hold their bits
      intro dd0 hdd0 hroom
      rcases List.mem_cons.mp hdd0 with rfl | hdd0'
      · by_cases hmem : dd0 ∈ D'
        · refine hcell' dd0 hmem ?_
          rw [length_arrs_setArr]
          exact hroom
        · have hne : ∀ dd' ∈ D', base + dd0 ≠ base + dd' := by
            intro dd' hdd' hcontra
            exact hmem (by
              have : dd0 = dd' := by omega
              rw [this]
              exact hdd')
          rw [hkeep' _ hne, arrs_setArr, if_pos rfl,
            getD_set_self hroom]
      · refine hcell' dd0 hdd0' ?_
        rw [length_arrs_setArr]
        exact hroom
    · -- unnamed cells untouched
      intro p2 hp2
      rw [hkeep' p2 (fun dd' hdd' =>
        hp2 dd' (List.mem_cons_of_mem _ hdd')), arrs_setArr, if_pos rfl,
        getD_set_ne (hp2 dd (List.mem_cons_self ..))]
    · intro b hb
      rw [hoth' b hb, arrs_setArr, if_neg hb]
    · intro b
      rw [hlen' b, length_arrs_setArr]
    · rw [hvars', vars_setArr]

/-- `Forall₂` against a mapped right list. -/
private theorem forall₂_map_right' {α β γ : Type*} {P : α → γ → Prop} (g : β → γ) :
    ∀ {l : List α} {u : List β},
      List.Forall₂ (fun x y => P x (g y)) l u →
      List.Forall₂ P l (u.map g) := by
  intro l u h
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h hrest ih => exact List.Forall₂.cons h ih

/-- The writer list has one writer per palette slot. -/
private theorem length_colWriters (S : Setup L) (j : ℕ) :
    (colWriters S j).length = S.pal (j + 1) := by
  have h1 : (pdIdx S).length = S.width * (S.R + 1) := by
    rw [pdIdx, List.length_flatMap]
    have heq : (List.map (fun b : Fin S.width =>
        (List.map (fun a : Fin (S.R + 1) => (b, a))
          (List.finRange (S.R + 1))).length) (List.finRange S.width))
        = List.replicate S.width (S.R + 1) := by
      rw [show (fun b : Fin S.width =>
          (List.map (fun a : Fin (S.R + 1) => (b, a))
            (List.finRange (S.R + 1))).length)
          = fun _ : Fin S.width => S.R + 1 from
        funext fun b => by rw [List.length_map, List.length_finRange]]
      rw [List.map_const', List.length_finRange]
    rw [heq, List.sum_replicate, smul_eq_mul]
  have h2 : (puIdx S j).length = relPal (S.pal j) * (S.R + 1) := by
    rw [puIdx, List.length_flatMap]
    have heq : (List.map (fun c : Fin (relPal (S.pal j)) =>
        (List.map (fun b : Fin (S.R + 1) => (c, b))
          (List.finRange (S.R + 1))).length)
          (List.finRange (relPal (S.pal j))))
        = List.replicate (relPal (S.pal j)) (S.R + 1) := by
      rw [show (fun c : Fin (relPal (S.pal j)) =>
          (List.map (fun b : Fin (S.R + 1) => (c, b))
            (List.finRange (S.R + 1))).length)
          = fun _ : Fin (relPal (S.pal j)) => S.R + 1 from
        funext fun c => by rw [List.length_map, List.length_finRange]]
      rw [List.map_const', List.length_finRange]
    rw [heq, List.sum_replicate, smul_eq_mul]
  simp only [colWriters, List.length_append, List.length_map,
    List.length_finRange, List.length_singleton, h1, h2]
  show S.pal j + 1 + S.width * (S.R + 1) + relPal (S.pal j) * (S.R + 1)
    = isoPal (relPal (S.pal j)) S.width S.R
  rw [isoPal, relPal]
  ring

open Classical in
/-- **One row of the colour region, written**: from the row-state
precondition, the writer sequence lands the whole row at
`recordProfilesMS`'s bits — every slot covered, everything else
untouched. -/
private theorem colRow_run {B : ℕ} (a : ℕ) (ha : a < kk)
    (hcol1 : (arenaNames (j + 1)).col ≠ "cp.c")
    (hcol2 : ∀ i, (arenaNames (j + 1)).col ≠ lv "cq.d" i)
    (hcol3 : ∀ i, (arenaNames (j + 1)).col ≠ lv "cq.u" i)
    (σ : Env) (hσ : ColRowPre S j f0 Dp Dc a ha B σ) :
    ∃ σ', Run B (colRowCom S j) σ σ'
        (30 * (colWriters S j).length + 1) ∧
      (∀ d : Fin (isoPal (relPal (S.pal j)) S.width S.R),
        (σ'.arrs (arenaNames (j + 1)).col).getD
            (a * S.pal (j + 1) + (d : ℕ)) 0
          = colBit S j f0 Dp Dc a ha d) ∧
      (∀ p2, (∀ d : Fin (isoPal (relPal (S.pal j)) S.width S.R),
          p2 ≠ a * S.pal (j + 1) + (d : ℕ)) →
        (σ'.arrs (arenaNames (j + 1)).col).getD p2 0
          = (σ.arrs (arenaNames (j + 1)).col).getD p2 0) ∧
      (∀ b, b ≠ (arenaNames (j + 1)).col → σ'.arrs b = σ.arrs b) ∧
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
      σ'.vars = σ.vars := by
  set bitN : ℕ → ℕ := fun dd =>
    if h : dd < isoPal (relPal (S.pal j)) S.width S.R then
      colBit S j f0 Dp Dc a ha ⟨dd, h⟩ else 0 with hbitN_def
  have hF : List.Forall₂ (fun w dd => ∀ σ, ColRowPre S j f0 Dp Dc a ha B σ →
      Run B w σ (σ.setArr (arenaNames (j + 1)).col
        (a * S.pal (j + 1) + dd) (bitN dd)) 30)
      (colWriters S j) ((colSlots S j).map (·.val)) := by
    refine forall₂_map_right' _ ?_
    refine ((colWriters_forall₂ S j f0 Dp Dc a ha (B := B))).imp ?_
    intro w d h σ2 hσ2
    have hb : bitN (d : ℕ) = colBit S j f0 Dp Dc a ha d := by
      rw [hbitN_def]
      simp only [d.2, dif_pos]
    rw [hb]
    exact h σ2 hσ2
  obtain ⟨σ', hr, hcell, hkeep, hoth, hlen, hvars⟩ :=
    writersRun (colC := (arenaNames (j + 1)).col)
      (base := a * S.pal (j + 1)) (bit := bitN)
      (P := ColRowPre S j f0 Dp Dc a ha B)
      (fun σ2 hσ2 p v => colRowPre_setArr S j f0 Dp Dc a ha hσ2
        hcol1 hcol2 hcol3 p v)
      hF σ hσ
  have hroom : ∀ d : Fin (isoPal (relPal (S.pal j)) S.width S.R),
      a * S.pal (j + 1) + (d : ℕ)
        < (σ.arrs (arenaNames (j + 1)).col).length := by
    intro d
    have h5 := hσ.2.2.2.2.1
    have hd : ((d : Fin (isoPal (relPal (S.pal j)) S.width S.R)) : ℕ)
        < S.pal (j + 1) := d.2
    omega
  refine ⟨σ', by rw [colRowCom]; exact hr, ?_, ?_, hoth, hlen, hvars⟩
  · intro d
    have hmem : ((d : Fin (isoPal (relPal (S.pal j)) S.width S.R)) : ℕ)
        ∈ (colSlots S j).map (·.val) :=
      List.mem_map.mpr ⟨d, colSlots_covers S j d, rfl⟩
    have h := hcell (d : ℕ) hmem (hroom d)
    rw [h, hbitN_def]
    simp only [d.2, dif_pos]
  · intro p2 hp2
    refine hkeep p2 ?_
    intro dd hdd
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hdd
    exact hp2 d

open Classical in
/-- **§5k's colour write**: per carrier row, the writer sequence — the
whole `(j+1)` colour window lands at `recordProfilesMS`'s bits. -/
theorem prepCol_spec {B : ℕ} (hkkB : kk < B)
    (hcol1 : (arenaNames (j + 1)).col ≠ "cp.c")
    (hcol2 : ∀ i, (arenaNames (j + 1)).col ≠ lv "cq.d" i)
    (hcol3 : ∀ i, (arenaNames (j + 1)).col ≠ lv "cq.u" i)
    (hnN1 : (arenaNames (j + 1)).nN ≠ "cp.i") :
    Spec B
      (fun σ => σ.vars (arenaNames (j + 1)).nN = kk ∧
        (∀ a, ∀ ha : a < kk, ∀ c : Fin (S.pal j),
          (σ.arrs "cp.c").getD (a * S.pal j + (c : ℕ)) 0
            = if (⟨a, ha⟩ : Fin kk) ∈ f0 c then 1 else 0) ∧
        (∀ a, ∀ ha : a < kk, ∀ b' : Fin S.width,
          (σ.arrs (lv "cq.d" (b' : ℕ))).getD a 0 = Dp b' ⟨a, ha⟩) ∧
        (∀ a, ∀ ha : a < kk, ∀ c : Fin (relPal (S.pal j)),
          (σ.arrs (lv "cq.u" (c : ℕ))).getD a 0
            = Dc c (Fin.castSucc ⟨a, ha⟩)) ∧
        kk * S.pal (j + 1) ≤ (σ.arrs (arenaNames (j + 1)).col).length ∧
        kk * S.pal j ≤ (σ.arrs "cp.c").length ∧
        (∀ b' : Fin S.width, kk ≤ (σ.arrs (lv "cq.d" (b' : ℕ))).length) ∧
        (∀ c : Fin (relPal (S.pal j)),
          kk ≤ (σ.arrs (lv "cq.u" (c : ℕ))).length) ∧
        kk * S.pal (j + 1) < B ∧ kk * S.pal j < B ∧ 1 < B ∧
        S.R + 2 < B ∧
        (∀ a : Fin kk, ∀ b' : Fin S.width, Dp b' a ≤ S.R + 1) ∧
        (∀ c : Fin (relPal (S.pal j)), ∀ v : Fin (kk + 1),
          Dc c v ≤ S.R + 2))
      (prepColCom S j)
      (fun σ σ' =>
        (∀ a, ∀ ha : a < kk,
          ∀ d : Fin (isoPal (relPal (S.pal j)) S.width S.R),
          (σ'.arrs (arenaNames (j + 1)).col).getD
              (a * S.pal (j + 1) + (d : ℕ)) 0
            = colBit S j f0 Dp Dc a ha d) ∧
        (∀ b, b ≠ (arenaNames (j + 1)).col → σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ y, y ≠ "cp.i" → σ'.vars y = σ.vars y))
      ((30 * (colWriters S j).length + 9) * kk + 6) := by
  intro σ0 hσ0
  obtain ⟨hnN0, hcc0, hpd0, hpu0, hcolL0, hccL0, hpdL0, hpuL0, hkpB, hkjB,
    h1B, hRB, hDpB, hDcB⟩ := hσ0
  set IC : Env → Prop := fun σ =>
    σ.vars (arenaNames (j + 1)).nN = kk ∧ σ.vars "cp.i" ≤ kk ∧
    (∀ a, ∀ ha : a < kk, a < σ.vars "cp.i" →
      ∀ d : Fin (isoPal (relPal (S.pal j)) S.width S.R),
      (σ.arrs (arenaNames (j + 1)).col).getD
          (a * S.pal (j + 1) + (d : ℕ)) 0
        = colBit S j f0 Dp Dc a ha d) ∧
    (∀ b, b ≠ (arenaNames (j + 1)).col → σ.arrs b = σ0.arrs b) ∧
    (∀ b, (σ.arrs b).length = (σ0.arrs b).length) ∧
    (∀ y, y ≠ "cp.i" → σ.vars y = σ0.vars y) with hIC_def
  have hbody : Spec B (fun σ => IC σ ∧ σ.vars "cp.i" < kk)
      (.seq (colRowCom S j)
        (.assign "cp.i" (.add (.var "cp.i") (.lit 1))))
      (fun σ σ' => IC σ' ∧ σ'.vars "cp.i" = σ.vars "cp.i" + 1)
      (30 * (colWriters S j).length + 5) := by
    rintro σ ⟨⟨hnN, hile, hrows, hoth, hlen, hvars⟩, hlt⟩
    set a := σ.vars "cp.i" with ha_def
    -- the row-state precondition, transported off the entry facts
    have hpre : ColRowPre S j f0 Dp Dc a hlt B σ := by
      have hccσ : σ.arrs "cp.c" = σ0.arrs "cp.c" := hoth _ (Ne.symm hcol1)
      have hpdσ : ∀ i, σ.arrs (lv "cq.d" i) = σ0.arrs (lv "cq.d" i) :=
        fun i => hoth _ (Ne.symm (hcol2 i))
      have hpuσ : ∀ i, σ.arrs (lv "cq.u" i) = σ0.arrs (lv "cq.u" i) :=
        fun i => hoth _ (Ne.symm (hcol3 i))
      have hpal_pos : (0 : ℕ) < S.pal (j + 1) := by
        show 0 < isoPal (relPal (S.pal j)) S.width S.R
        rw [isoPal, relPal]
        omega
      have haux1 : a * S.pal (j + 1) + S.pal (j + 1) ≤ kk * S.pal (j + 1) := by
        have h := Nat.mul_le_mul_right (S.pal (j + 1))
          (Nat.succ_le_of_lt hlt)
        rw [Nat.succ_mul] at h
        exact h
      have haux2 : a * S.pal j + S.pal j ≤ kk * S.pal j := by
        have h := Nat.mul_le_mul_right (S.pal j) (Nat.succ_le_of_lt hlt)
        rw [Nat.succ_mul] at h
        exact h
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h1B, ?_, ?_, ?_,
        by omega⟩
      · intro c
        rw [hccσ]
        exact hcc0 a hlt c
      · intro b'
        rw [hpdσ]
        exact hpd0 a hlt b'
      · intro c
        rw [hpuσ]
        exact hpu0 a hlt c
      · rw [hlen]
        omega
      · rw [hccσ]
        omega
      · intro b'
        rw [hpdσ]
        exact lt_of_lt_of_le hlt (hpdL0 b')
      · intro c
        rw [hpuσ]
        exact lt_of_lt_of_le hlt (hpuL0 c)
      · omega
      · omega
      · intro b'
        have := hDpB ⟨a, hlt⟩ b'
        omega
      · intro c
        have := hDcB c (Fin.castSucc ⟨a, hlt⟩)
        omega
      · exact hRB
    obtain ⟨σ1, hr1, hcells1, hkeep1, hoth1, hlen1, hvars1⟩ :=
      colRow_run S j f0 Dp Dc a hlt hcol1 hcol2 hcol3 σ hpre
    have hi1 : σ1.vars "cp.i" = a := by rw [hvars1]
    have hbump : (Expr.add (.var "cp.i") (.lit 1)).evalB B σ1
        = some (a + 1) := by
      have hv : (Expr.var "cp.i").evalB B σ1 = some a := by
        rw [← hi1]
        exact evalB_var (by rw [hi1]; omega)
      have h := evalB_bin (op := .add) hv (evalB_lit (n := 1) (by omega))
        (by rw [Bop.apply_add]; omega)
      rwa [Bop.apply_add] at h
    refine ⟨σ1.setVar "cp.i" (a + 1),
      (hr1.seq (Run.assign hbump)).mono (by simp), ?_, ?_⟩
    · refine ⟨?_, by rw [vars_setVar, if_pos rfl]; omega, ?_, ?_, ?_, ?_⟩
      · rw [vars_setVar, if_neg hnN1, hvars1]
        exact hnN
      · -- rows below the bumped counter
        intro a2 ha2 ha2lt d
        rw [vars_setVar, if_pos rfl] at ha2lt
        rw [arrs_setVar]
        by_cases ha2a : a2 = a
        · subst ha2a
          exact hcells1 d
        · have h := hkeep1 (a2 * S.pal (j + 1) + (d : ℕ)) ?_
          · rw [h]
            exact hrows a2 ha2 (by omega) d
          · intro d2 hcontra
            have hd2 : ((d2 : Fin (isoPal (relPal (S.pal j)) S.width
                S.R)) : ℕ) < S.pal (j + 1) := d2.2
            have hd1 : ((d : Fin (isoPal (relPal (S.pal j)) S.width
                S.R)) : ℕ) < S.pal (j + 1) := d.2
            exact ha2a (rowCell_inj hd1 hd2 hcontra)
      · intro b hb
        rw [arrs_setVar, hoth1 b hb]
        exact hoth b hb
      · intro b
        rw [arrs_setVar, hlen1 b]
        exact hlen b
      · intro y hy
        rw [vars_setVar, if_neg hy, hvars1]
        exact hvars y hy
    · rw [vars_setVar, if_pos rfl]
  obtain ⟨σ', hrun, hIC', hi'⟩ :=
    (Spec.forRangeZero "cp.i" (arenaNames (j + 1)).nN IC kk
      (30 * (colWriters S j).length + 5) hkkB
      (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1) hbody) σ0
      (show IC (σ0.setVar "cp.i" 0) by
        refine ⟨by rw [vars_setVar, if_neg hnN1]; exact hnN0,
          by rw [vars_setVar, if_pos rfl]; omega, ?_,
          fun b _ => by rw [arrs_setVar],
          fun b => by rw [arrs_setVar],
          fun y hy => by rw [vars_setVar, if_neg hy]⟩
        intro a2 ha2 ha2lt d
        rw [vars_setVar, if_pos rfl] at ha2lt
        omega)
  obtain ⟨-, -, hrows', hoth', hlen', hvars'⟩ := hIC'
  refine ⟨σ', hrun.mono (by
    have h9 : 30 * (colWriters S j).length + 5 + 4
        = 30 * (colWriters S j).length + 9 := by omega
    rw [h9]), ?_, hoth', hlen', hvars'⟩
  intro a2 ha2 d
  exact hrows' a2 ha2 (by rw [hi']; exact ha2) d

end ColourWrite

/-- Every scalar the pass writes: its own pool, the stage pools, or the
two `(j+1)` cells. -/
theorem wvars_prepCom {S : Setup L} {ℓp hbf : ℕ → ℕ} {co cm : ℕ → String}
    {j : ℕ} :
    ∀ y ∈ (prepCom S ℓp hbf co cm j).wvars,
      y ∈ prepScalars ∨ y = (arenaNames (j + 1)).nN
        ∨ y = (arenaNames (j + 1)).nS := by
  intro y hy
  simp only [prepCom, Com.wvars, List.mem_append] at hy
  rcases hy with hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy
    | hy | hy
  · simp [prepRowBoundsCom, Com.wvars] at hy
    rcases hy with rfl | rfl <;> left <;> simp [prepScalars, prepOwnScalars]
  · simp [prepZeroCom, Com.wvars] at hy
    rcases hy with rfl | rfl <;> left <;> simp [prepScalars, prepOwnScalars]
  · simp [prepRowCom, Com.wvars] at hy
    rcases hy with rfl | rfl <;> left <;> simp [prepScalars, prepOwnScalars]
  · simp [prepCentreCom, Com.wvars] at hy
    subst hy; left; simp [prepScalars, prepOwnScalars]
  · simp [prepBatchCom, Com.wvars] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      left <;> simp [prepScalars, prepOwnScalars]
  · simp [prepWidthCom, Com.wvars] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      left <;> simp [prepScalars, prepOwnScalars]
  · simp [prepClearCom, Com.wvars] at hy
    rcases hy with rfl | rfl <;> left <;> simp [prepScalars, prepOwnScalars]
  · simp only [prepRestrictCom, Com.wvars, List.nil_append, List.mem_cons,
      List.mem_append, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | hy
    · left; simp [prepScalars, rsScalars]
    · left; simp [prepScalars, rsScalars]
    · left; simp [prepScalars, rsScalars]
    · left; simp [prepScalars, rsScalars]
    · rcases wvars_restrictCom_subset _ _ _ _ y hy with h | h | h
      · left; simp only [prepScalars, List.mem_append]; tauto
      · right; left; simpa [prepNmR] using h
      · left
        simp only [prepNmR] at h
        subst h
        simp [prepScalars, prepOwnScalars]
  · simp only [prepBfsCom, Com.wvars, List.nil_append, List.mem_cons,
      List.mem_append, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | hy
    · left; simp [prepScalars, bfScalars]
    · left; simp [prepScalars, bfScalars]
    · left; simp [prepScalars, bfScalars]
    · left; simp [prepScalars, bfScalars]
    · have := wvars_bfsCom_subset _ _ _ y hy
      left; simp only [prepScalars, List.mem_append]; tauto
  · simp only [prepSupportsCom, Com.wvars, List.nil_append, List.mem_cons,
      List.mem_append, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | hy
    · left; simp [prepScalars, spScalars]
    · left; simp [prepScalars, spScalars]
    · left; simp [prepScalars, spScalars]
    · left; simp [prepScalars, spScalars]
    · left; simp [prepScalars, spScalars]
    · left; simp [prepScalars, spScalars]
    · have := wvars_supportsCom_subset _ _ _ _ _ y hy
      left; simp only [prepScalars, List.mem_append]; tauto
  · have := wvars_profilesCom_subset _ _ _ _ y hy
    left; simp only [prepScalars, List.mem_append]; tauto
  · simp only [prepColCom, Com.wvars, wvars_colRowCom, List.append_nil,
      List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hy
    rcases hy with rfl | rfl <;> left <;> simp [prepScalars, prepOwnScalars]
  · simp only [prepIsolateCom] at hy
    rcases wvars_isolateCom_subset _ _ _ _ _ y hy with h | h
    · left; simp only [prepScalars, List.mem_append]; tauto
    · right; right; exact h

/-! ## §6e The mid-state contract (the P1–P9 milestone) -/

open Classical in
/-- **The mid-state contract**: what the discharged §P1–§P9 prefix of
the pass (row bounds, rank zero, cluster row, centre bit, batch trace,
width array, clear, restrict, BFS at `2R`) leaves at the supports
stage's door — the pre-isolation child at the scratch names, the two
size cells, the canonical `2R`-ball table in the distance scratch, the
padded batch in the width scratch, the batch indicator in the bit
scratch, and the allocation room the four remaining stages consume. -/
private def PrepMid (S : Setup L) (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N)
    (σ : Env) : Prop :=
  ArenaStW (prepNmR j) (hbf j)
    ((Impl.ofArena A (htabF j A)).restrict
      (cluster S A ((ord A.N A.G).order) u)) σ ∧
  σ.vars "cp.n" = (cluster S A ((ord A.N A.G).order) u).ncard ∧
  σ.vars "cp.m" = (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
    (preG S A ((ord A.N A.G).order) u).degree v) ∧
  (∀ v : Fin (childN S A ((ord A.N A.G).order) u),
    (σ.arrs "cp.d").getD (v : ℕ) 0
      = ballDist (preG S A ((ord A.N A.G).order) u)
          (centreChild S A ((ord A.N A.G).order) u) (2 * S.R) v) ∧
  (∀ p : Fin S.width,
    (σ.arrs "cp.w").getD (p : ℕ) 0
      = ((batchFn S A ((ord A.N A.G).order) u p :
          Fin (childN S A ((ord A.N A.G).order) u)) : ℕ)) ∧
  (∀ t : ℕ, ∀ ht : t < childN S A ((ord A.N A.G).order) u,
    (σ.arrs "cp.b").getD t 0
      = if (⟨t, ht⟩ : Fin (childN S A ((ord A.N A.G).order) u))
          ∈ batchSet S A ((ord A.N A.G).order) u then 1 else 0) ∧
  n₀ ≤ (σ.arrs "cp.b").length ∧ n₀ ≤ (σ.arrs "cp.d").length ∧
  n₀ ≤ (σ.arrs "cp.p").length ∧ n₀ ≤ (σ.arrs "cp.x").length ∧
  n₀ + 2 ≤ (σ.arrs "cp.v").length ∧
  (σ.arrs "cp.w").length = S.width ∧
  (∀ i, i < S.width → n₀ ≤ (σ.arrs (lv "cq.d" i)).length) ∧
  (∀ c, c < S.pal j → n₀ * n₀ + 2 * n₀ ≤ (σ.arrs (lv "cq.v" c)).length) ∧
  (∀ c, c < S.pal j + 1 → n₀ + 1 ≤ (σ.arrs (lv "cq.u" c)).length) ∧
  n₀ + 1 ≤ (σ.arrs (arenaNames (j + 1)).off).length ∧
  n₀ * n₀ ≤ (σ.arrs (arenaNames (j + 1)).tgt).length ∧
  n₀ * S.pal (j + 1) ≤ (σ.arrs (arenaNames (j + 1)).col).length

/-! The remaining four stages, composed at their actual windows. -/

local macro "prep_name" : tactic => `(tactic|
  (try dsimp only [prepNmR, prepNmI, prepPN, arenaNames]
   first
   | decide
   | (apply lv_ne_lit <;> decide)
   | (apply Ne.symm; apply lv_ne_lit <;> decide)
   | (apply lv_ne_of_base_ne <;> decide)
   | (apply lv_not_mem <;> decide)))

local macro "prep_names" : tactic => `(tactic|
  (simp only [prepNmR, prepNmI, prepPN, arenaNames,
    List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or]
   repeat' apply And.intro
   all_goals prep_name))

private theorem prepPN_ok (j mb Λ : ℕ) : ProfNames.Ok (prepPN j) mb (Λ + 1) := by
  constructor
  · prep_names
  · prep_names
  · intro i _; prep_names
  · intro c _; prep_names
  · intro c _; prep_names
  · prep_names
  · intro i _; prep_name
  · intro i _; prep_name
  · intro i _; prep_name
  · intro i _; prep_name
  · intro i _; prep_name
  · intro i _; prep_name
  · intro i _ k _ h; exact (lv_inj rfl h).2
  · intro i _ k _ h; exact (lv_inj rfl h).2
  · intro i _ k _ h; exact (lv_inj rfl h).2
  · intro i _ k _; prep_name
  · intro i _ k _; prep_name
  · intro i _ k _; prep_name
  · exact lv_not_mem (by decide) (by decide) _
  · prep_names

set_option maxHeartbeats 4000000 in
open Classical in
private theorem prepTail_spec (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N)
    (hlpEq : ℓp (j + 1) = ℓp j) (hhbEq : hbf (j + 1) = hbf j)
    (hjlt : j < ℓp j) (hRhb : 2 * S.R + 1 ≤ hbf j)
    (h1B : 1 < B) (hn0nB : n₀ * n₀ < B)
    (hn02B : n₀ + 2 < B) (hbig1 : n₀ * n₀ + 2 * n₀ + 1 < B)
    (hRB : 2 * S.R + 3 < B) (hwB : S.width < B)
    (hlpB : ℓp j < B) (hhbB : hbf j + 1 < B)
    (hhistB : n₀ * ℓp j * (hbf j + 1) < B)
    (hMw : (batchSet S A ((ord A.N A.G).order) u).ncard ≤ S.width)
    (hpalB : n₀ * S.pal j < B) (hpal1B : n₀ * S.pal (j + 1) < B) :
    Spec B (PrepMid S ord ℓp htabF hbf j A u)
      (.seq (prepSupportsCom j (2 * S.R) (ℓp j) (hbf j))
        (.seq (profilesCom (prepPN j) S.width (S.pal j) S.R)
          (.seq (prepColCom S j) (prepIsolateCom j))))
      (fun _ σ' =>
        ∃ (Dp : Fin S.width → Fin (childN S A ((ord A.N A.G).order) u) → ℕ)
          (Dc : Fin (relPal (S.pal j)) →
            Fin (childN S A ((ord A.N A.G).order) u + 1) → ℕ),
          Impl.ProfileTablesMS (preG S A ((ord A.N A.G).order) u)
            (batchFn S A ((ord A.N A.G).order) u)
            (childColR S A ((ord A.N A.G).order) u) S.R Dp Dc ∧
          ArenaStW (arenaNames (j + 1)) (hbf (j + 1))
            (machChild S A ((ord A.N A.G).order) u Dp Dc
              (prepChan S ord ℓp htabF j A u)) σ')
      ((30 + supportsK (childN S A ((ord A.N A.G).order) u)
          (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
            (preG S A ((ord A.N A.G).order) u).degree v) (2 * S.R))
        + profilesK S.width (S.pal j + 1)
            (childN S A ((ord A.N A.G).order) u)
            (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
              (preG S A ((ord A.N A.G).order) u).degree v) S.R
        + ((30 * (isoPal (relPal (S.pal j)) S.width S.R) + 9)
            * childN S A ((ord A.N A.G).order) u + 6)
        + isolateK (childN S A ((ord A.N A.G).order) u)
            (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
              (preG S A ((ord A.N A.G).order) u).degree v)
        + 30) := by
  let π := (ord A.N A.G).order
  let X := cluster S A π u
  let AC := (Impl.ofArena A (htabF j A)).restrict X
  let kk := childN S A π u
  let D := ballDist AC.G (centreChild S A π u) (2 * S.R)
  let ns := ∑ v : Fin AC.N, AC.G.degree v
  have hNn0 : A.N ≤ n₀ := by
    simpa using Fintype.card_le_of_embedding A.up
  have hkn0 : kk ≤ n₀ := le_trans (set_ncard_le_card X) hNn0
  have hkkB : kk < B := by omega
  have hkk2B : kk * kk < B :=
    lt_of_le_of_lt (Nat.mul_le_mul hkn0 hkn0) hn0nB
  have hnsn : ns ≤ n₀ * n₀ :=
    le_trans (degSum_le_sq AC.G) (Nat.mul_le_mul hkn0 hkn0)
  have hnsB : ns < B := lt_of_le_of_lt hnsn hn0nB
  have hndR : ([(prepNmR j).off, (prepNmR j).tgt, (prepNmR j).col,
      (prepNmR j).up, (prepNmR j).hist] : List String).Nodup := by prep_names
  have hndI : ([(prepNmI j).off, (prepNmI j).tgt, (prepNmI j).col,
      (prepNmI j).up, (prepNmI j).hist] : List String).Nodup := by prep_names
  intro σ0 hσ0
  obtain ⟨hAW0, hcpn0, hcpm0, hD0, hw0, hb0, hbL0, hdL0, hpL0, hxL0,
    hvL0, hwL0, hqdL0, hqvL0, hquL0, hoL0, htL0, hcL0⟩ := hσ0
  let σ1 := (((((σ0.setVar "sp.n" kk).setVar "sp.m" ns).setVar "sp.r"
    (2 * S.R)).setVar "sp.l" (ℓp j)).setVar "sp.h" (hbf j)).setVar "sp.p" j
  have hr1 : Run B (.assign "sp.n" (.var "cp.n")) σ0
      (σ0.setVar "sp.n" kk) 2 := by
    apply Run.assign
    have hv : σ0.vars "cp.n" = kk := hcpn0
    rw [← hv]
    exact evalB_var (by rw [hv]; exact hkkB)
  have hr2 : Run B (.assign "sp.m" (.var "cp.m"))
      (σ0.setVar "sp.n" kk) ((σ0.setVar "sp.n" kk).setVar "sp.m" ns) 2 := by
    apply Run.assign
    have hv : (σ0.setVar "sp.n" kk).vars "cp.m" = ns := by
      simpa only [vars_setVar, if_neg (by decide : ("cp.m" : String) ≠ "sp.n")]
        using hcpm0
    rw [← hv]
    exact evalB_var (by rw [hv]; exact hnsB)
  have hr3 : Run B (.assign "sp.r" (.lit (2 * S.R)))
      ((σ0.setVar "sp.n" kk).setVar "sp.m" ns)
      (((σ0.setVar "sp.n" kk).setVar "sp.m" ns).setVar "sp.r" (2 * S.R)) 2 :=
    Run.assign (evalB_lit (by omega))
  have hr4 : Run B (.assign "sp.l" (.lit (ℓp j)))
      (((σ0.setVar "sp.n" kk).setVar "sp.m" ns).setVar "sp.r" (2 * S.R))
      ((((σ0.setVar "sp.n" kk).setVar "sp.m" ns).setVar "sp.r" (2 * S.R)).setVar
        "sp.l" (ℓp j)) 2 := Run.assign (evalB_lit hlpB)
  have hr5 : Run B (.assign "sp.h" (.lit (hbf j)))
      ((((σ0.setVar "sp.n" kk).setVar "sp.m" ns).setVar "sp.r" (2 * S.R)).setVar
        "sp.l" (ℓp j))
      (((((σ0.setVar "sp.n" kk).setVar "sp.m" ns).setVar "sp.r" (2 * S.R)).setVar
        "sp.l" (ℓp j)).setVar "sp.h" (hbf j)) 2 :=
    Run.assign (evalB_lit (by omega))
  have hr6 : Run B (.assign "sp.p" (.lit j))
      (((((σ0.setVar "sp.n" kk).setVar "sp.m" ns).setVar "sp.r" (2 * S.R)).setVar
        "sp.l" (ℓp j)).setVar "sp.h" (hbf j)) σ1 2 :=
    Run.assign (evalB_lit (by omega))
  have h1arr : σ1.arrs = σ0.arrs := by funext b; simp [σ1, arrs_setVar]
  have h1var : ∀ y, y ∉ spScalars → σ1.vars y = σ0.vars y := by
    intro y hy
    have hys : y ≠ "sp.n" ∧ y ≠ "sp.m" ∧ y ≠ "sp.r" ∧ y ≠ "sp.l" ∧
        y ≠ "sp.h" ∧ y ≠ "sp.p" := by
      simp only [spScalars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      exact ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1⟩
    simp [σ1, vars_setVar, hys.1, hys.2.1, hys.2.2.1,
      hys.2.2.2.1, hys.2.2.2.2.1, hys.2.2.2.2.2]
  have hAW1 : ArenaStW (prepNmR j) (hbf j) AC σ1 := by
    apply arenaStW_of_eq hAW0
    · exact h1var _ (by exact lv_not_mem (by decide) (by decide) _)
    · exact h1var _ (by prep_name)
    all_goals rw [h1arr]
  obtain ⟨σ2, hrS, hAW2, hns2, hD2, hp2, hlen2⟩ :=
    (supportsCom_specW (B := B) (A := AC) (nm := prepNmR j)
      (pa := "cp.p") (da := "cp.d") (D := D) (s := centreChild S A π u)
      ⟨j, hjlt⟩ (ballDist_ballTable _ _ _) (ballDist_le _ _ _) hRhb
      hkkB hkk2B (by omega) hlpB hhbB
      (lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hkn0))
        hhistB)
      hndR (by prep_names) (by prep_names) (by decide)
      (by exact lv_not_mem (by decide) (by decide) _) (by prep_name)) σ1
      ⟨hAW1, by simp [σ1, vars_setVar]; rfl,
        by simp [σ1, vars_setVar, prepNmR, hcpm0]; rfl,
        by simp [σ1, vars_setVar], by simp [σ1, vars_setVar],
        by simp [σ1, vars_setVar], by simp [σ1, vars_setVar],
        by rw [h1arr]; exact le_trans hkn0 hpL0,
        by rw [h1arr]; exact le_trans hkn0 hdL0,
        by intro v; rw [h1arr]; exact hD0 v⟩
  let AS : Impl.MArena (S.pal j) n₀ (ℓp j) :=
    { AC with hist := fun v p => if p = ⟨j, hjlt⟩ then
      descendCol AC.G D (2 * S.R) v else AC.hist v p }
  have h2arr : ∀ b, b ≠ "cp.p" → b ≠ (arenaNames (j + 1)).hist →
      σ2.arrs b = σ0.arrs b := by
    intro b hbp hbh
    rw [← h1arr]
    apply hrS.frame_arr
    rw [warrs_supportsCom]
    simp [prepNmR, hbp, hbh]
  have hlen20 : ∀ b, (σ2.arrs b).length = (σ0.arrs b).length := by
    intro b; rw [hlen2 b, h1arr]
  obtain ⟨σ3, hrP, hAW3, hns3, hlen3, hDpB, hDcB, hPT⟩ :=
    (profilesCom_specW (B := B) (R := S.R) (A := AS) (nm := prepNmR j) (ba := "cp.w")
      (xb := "cp.x") (vo := "cp.v") (pdF := lv "cq.d") (vtF := lv "cq.v")
      (puF := lv "cq.u") (batchFn S A π u) (prepPN_ok j S.width (S.pal j))
      (by change kk + 2 < B; omega)
      (by change ns + 2 * kk + 1 < B; omega)
      (by omega) hwB (lt_of_le_of_lt (Nat.mul_le_mul_right _ hkn0) hpalB)
      hndR (by prep_names) (by prep_names) (by prep_names)
      (by intros; prep_names) (by intros; prep_names) (by intros; prep_names)) σ2
      ⟨hAW2, by rw [hlen20]; exact hwL0,
        by intro p; rw [h2arr "cp.w" (by decide) (by prep_name)]; exact hw0 p,
        by rw [hlen20]; exact le_trans hkn0 hxL0,
        by rw [hlen20]; exact le_trans (Nat.add_le_add_right hkn0 2) hvL0,
        by intro i hi; rw [hlen20]; exact le_trans hkn0 (hqdL0 i hi),
        by
          intro c
          rw [hlen20]
          have hcN : (AS.col c).ncard ≤ kk := set_ncard_le_card (AS.col c)
          exact le_trans (by change ns + 2 * (AS.col c).ncard ≤ n₀ * n₀ + 2 * n₀; omega)
            (hqvL0 c c.2),
        by intro c hc; rw [hlen20]; exact le_trans (Nat.add_le_add_right hkn0 1) (hquL0 c hc)⟩
  let Dp : Fin S.width → Fin kk → ℕ :=
    fun p v => (σ3.arrs (lv "cq.d" p)).getD v 0
  let Dc : Fin (relPal (S.pal j)) → Fin (kk + 1) → ℕ :=
    fun c v => (σ3.arrs (lv "cq.u" c)).getD v 0
  have hlen30 : ∀ b, (σ3.arrs b).length = (σ0.arrs b).length := by
    intro b; rw [hlen3 b, hlen20]
  have hcwin : arenaWs (prepNmR j) (S.pal j) (ℓp j) (hbf j) AS.N
      (σ3.vars (prepNmR j).nS) "cp.c" = some (kk * S.pal j) :=
    arenaWs_col (by prep_name) (by prep_name)
  have hcBits : ∀ (a : ℕ) (ha : a < kk) (c : Fin (S.pal j)),
      (σ3.arrs "cp.c").getD (a * S.pal j + (c : ℕ)) 0 =
        if (⟨a, ha⟩ : Fin kk) ∈ AS.col c then 1 else 0 := by
    intro a ha c
    have hbit := hAW3.st.col.2 (⟨a, ha⟩ : Fin kk) c
    rw [show (prepNmR j).col = "cp.c" from rfl, arrs_winA_some hcwin] at hbit
    have hidx : a * S.pal j + (c : ℕ) < kk * S.pal j := by
      have := Nat.mul_le_mul_right (S.pal j) ha
      rw [Nat.succ_mul] at this
      omega
    rw [getD_take_of_lt hidx] at hbit
    exact hbit
  obtain ⟨σ4, hrC, hc4, hCfr, hlen4, hCvar⟩ :=
    (prepCol_spec S j AS.col Dp Dc hkkB (by prep_name)
      (by intro i; prep_name) (by intro i; prep_name) (by prep_name)) σ3
      ⟨hAW3.st.n_eq, hcBits, by intros; rfl, by intros; rfl,
        by rw [hlen30]; exact le_trans (Nat.mul_le_mul_right _ hkn0) hcL0,
        hAW3.fits _ _ hcwin,
        by intro p; rw [hlen30]; exact le_trans hkn0 (hqdL0 p p.2),
        by intro c; rw [hlen30]; exact le_trans (le_trans hkn0 (Nat.le_succ n₀)) (hquL0 c c.2),
        lt_of_le_of_lt (Nat.mul_le_mul_right _ hkn0) hpal1B,
        lt_of_le_of_lt (Nat.mul_le_mul_right _ hkn0) hpalB,
        h1B, by omega, by intros; apply hDpB, by intros; apply hDcB⟩
  have hAW4 : ArenaStW (prepNmR j) (hbf j) AS σ4 := by
    apply arenaStW_of_eq hAW3
    · exact hCvar _ (by prep_name)
    · exact hCvar _ (by prep_name)
    all_goals apply hCfr; prep_name
  let AI : Impl.MArena (S.pal (j + 1)) n₀ (ℓp j) :=
    ⟨kk, AS.G, Impl.recordProfilesMS S.R (relColoring AS.col Set.univ) Dp Dc,
      AS.up, AS.hist⟩
  have hAWI : ArenaStW (prepNmI j) (hbf j) AI σ4 := by
    apply arenaStW_retarget_col hAW4 (arenaNames (j + 1)).col
      (Impl.recordProfilesMS S.R (relColoring AS.col Set.univ) Dp Dc) hndR
      (by prep_names)
    · rw [hlen4, hlen30]
      exact le_trans (Nat.mul_le_mul_right _ hkn0) hcL0
    · intro v c; exact hc4 v v.2 c
  have hbP : σ3.arrs "cp.b" = σ2.arrs "cp.b" := by
    apply hrP.frame_arr
    intro hbmem
    rcases warrs_profilesCom_subset _ _ _ _ _ hbmem with h | h | ⟨i, _, h⟩ | ⟨c, _, h⟩ | ⟨c, _, h⟩
    · exact (by decide : ("cp.b" : String) ≠ "cp.x") h
    · exact (by decide : ("cp.b" : String) ≠ "cp.v") h
    all_goals exact (Ne.symm (lv_ne_lit (by decide) (by decide) _)) h
  have hb4 : σ4.arrs "cp.b" = σ0.arrs "cp.b" := by
    rw [hCfr "cp.b" (by prep_name), hbP,
      h2arr "cp.b" (by decide) (by prep_name)]
  have hlen40 : ∀ b, (σ4.arrs b).length = (σ0.arrs b).length := by
    intro b; rw [hlen4, hlen30]
  obtain ⟨σ5, hrI, hAW5, _⟩ :=
    (isolateCom_specW (B := B) (Bar := AI) (W := Set.range (batchFn S A π u))
      (nmI := prepNmI j) (oaO := (arenaNames (j + 1)).off)
      (taO := (arenaNames (j + 1)).tgt) (nsO := (arenaNames (j + 1)).nS)
      (ba := "cp.b") hkkB hkk2B hndI (by prep_names) (by prep_names)
      (by prep_names) (by prep_name) (by prep_name) (by prep_name)
      (by exact lv_not_mem (by decide) (by decide) _) (by prep_name)
      (by prep_name) (by exact lv_not_mem (by decide) (by decide) _)
      (by prep_name)) σ4
      ⟨hAWI, by
          constructor
          · rw [hb4]; exact le_trans hkn0 hbL0
          · intro v
            rw [hb4]
            rw [show Set.range (batchFn S A π u) = batchSet S A π u from
              range_pad (centreChild_mem_batchSet S A π u) hMw]
            exact hb0 v v.2,
        by rw [hlen40]; exact le_trans hkn0 hbL0,
        by rw [hlen40]; exact le_trans (Nat.add_le_add_right hkn0 1) hoL0,
        by
          rw [hlen40]
          exact le_trans (degSum_deleteVerts_le _ _)
            (le_trans hnsn htL0)⟩
  have hrC' : Run B (prepColCom S j) σ3 σ4
      ((30 * isoPal (relPal (S.pal j)) S.width S.R + 9) * kk + 6) := by
    simpa only [length_colWriters] using hrC
  have hr := (hr1.seq (hr2.seq (hr3.seq (hr4.seq (hr5.seq (hr6.seq hrS)))))).seq
    (hrP.seq (hrC'.seq hrI))
  refine ⟨σ5, hr.mono ?_, Dp, Dc, hPT, ?_⟩
  · change (2 + (2 + (2 + (2 + (2 + (2 + supportsK kk ns (2 * S.R))))))) +
      (profilesK S.width (S.pal j + 1) kk ns S.R +
        (((30 * isoPal (relPal (S.pal j)) S.width S.R + 9) * kk + 6) +
          isolateK kk ns)) ≤
      (30 + supportsK kk ns (2 * S.R)) +
        profilesK S.width (S.pal j + 1) kk ns S.R +
        ((30 * isoPal (relPal (S.pal j)) S.width S.R + 9) * kk + 6) +
        isolateK kk ns + 30
    omega
  · rw [prepNmI_update] at hAW5
    apply arenaStW_cast hlpEq hhbEq (h1 := AI.hist) (h := hAW5)
    intro v p
    change prepChan S ord ℓp htabF j A u v p =
      if (⟨(p : ℕ), by omega⟩ : Fin (ℓp j)) = ⟨j, hjlt⟩ then
        descendCol AC.G D (2 * S.R) v else AC.hist v ⟨(p : ℕ), by omega⟩
    simp only [prepChan, Fin.ext_iff]
    split_ifs <;> try rfl
    omega

/-! ## §7 The pass, assembled -/

set_option maxHeartbeats 4000000 in
open Classical in
/-- The real child-building program satisfies the verbatim parts contract.
The hypotheses concern channel contents, allocation lengths, word bounds and
fresh names; every machine stage is discharged in this file. -/
theorem childLoadParts_of (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String)
    -- the constant-`ℓp` discipline (F7 owns both parameters)
    (hlpEq : ∀ j, j + 1 ≤ S.depth → ℓp (j + 1) = ℓp j)
    (hhbEq : ∀ j, j + 1 ≤ S.depth → hbf (j + 1) = hbf j)
    (hlpRoom : ∀ j, j + 1 ≤ S.depth → j < ℓp j)
    (hhbR : ∀ j, j + 1 ≤ S.depth → 2 * S.R + 1 ≤ hbf j)
    -- the admissible history shape and the channel-pinning seam
    (hAdmLen : ∀ j (A : Arena (S.pal j) n₀), Adm j A → A.hist.length = j)
    (hpin : ∀ j (A : Arena (S.pal j) n₀), Adm j A →
      ∀ (v : Fin A.N) (e : Fin (ℓp j)) (he : (e : ℕ) < A.hist.length)
        (z : Fin A.N),
        z ∈ htabF j A v e ↔ (A.up z) ∈ Lax3Proofs.SplitterWin.pathSet
          (A.hist.reverse[(e : ℕ)]'(by simpa using he)).2 (2 * S.R)
          (A.hist.reverse[(e : ℕ)]'(by simpa using he)).1 (A.up v))
    (hpinE : ∀ j (A : Arena (S.pal j) n₀), Adm j A →
      ∀ (v : Fin A.N) (e : Fin (ℓp j)), A.hist.length ≤ (e : ℕ) →
        htabF j A v e = [])
    -- the batch fits the width
    (hwidth : ∀ j, j + 1 ≤ S.depth → 1 + j * (2 * S.R + 1) ≤ S.width)
    -- word bounds
    (h1B : 1 < B) (hn0B : n₀ < B) (hn0nB : n₀ * n₀ < B)
    (hn02B : n₀ + 2 < B) (hbig1 : n₀ * n₀ + 2 * n₀ + 1 < B)
    (hdepthB : S.depth < B) (hRB : 2 * S.R + 3 < B) (hwB : S.width < B)
    (hlpB : ∀ j ≤ S.depth, ℓp j < B)
    (hhbB : ∀ j ≤ S.depth, hbf j + 1 < B)
    (hhistB : ∀ j ≤ S.depth, n₀ * ℓp j * (hbf j + 1) < B)
    (hpalB : ∀ j ≤ S.depth, n₀ * S.pal j < B)
    -- the scratch descriptor's length clauses
    (hscrA : ∀ j' σ, Scr j' σ →
      n₀ ≤ (σ.arrs "cp.l").length ∧ n₀ ≤ (σ.arrs "cp.r").length ∧
      n₀ ≤ (σ.arrs "cp.b").length ∧ n₀ ≤ (σ.arrs "cp.d").length ∧
      n₀ ≤ (σ.arrs "cp.p").length ∧ n₀ ≤ (σ.arrs "cp.x").length ∧
      n₀ + 2 ≤ (σ.arrs "cp.v").length ∧
      (σ.arrs "cp.w").length = S.width ∧
      n₀ + 1 ≤ (σ.arrs "cp.o").length ∧
      n₀ * n₀ ≤ (σ.arrs "cp.t").length ∧
      n₀ * S.pal j' ≤ (σ.arrs "cp.c").length ∧
      (∀ i, i < S.width → n₀ ≤ (σ.arrs (lv "cq.d" i)).length) ∧
      (∀ c, c < S.pal j' →
        n₀ * n₀ + 2 * n₀ ≤ (σ.arrs (lv "cq.v" c)).length) ∧
      (∀ c, c < S.pal j' + 1 → n₀ + 1 ≤ (σ.arrs (lv "cq.u" c)).length))
    (hscrLvl : ∀ j', j' + 1 ≤ S.depth → ∀ σ, Scr j' σ →
      n₀ + 1 ≤ (σ.arrs (arenaNames (j' + 1)).off).length ∧
      n₀ * n₀ ≤ (σ.arrs (arenaNames (j' + 1)).tgt).length ∧
      n₀ * S.pal (j' + 1) ≤ (σ.arrs (arenaNames (j' + 1)).col).length ∧
      n₀ ≤ (σ.arrs (arenaNames (j' + 1)).up).length ∧
      n₀ * ℓp j' * (hbf j' + 1)
        ≤ (σ.arrs (arenaNames (j' + 1)).hist).length)
    -- cover-name freshness
    (hcovA : ∀ jc j', ca jc ∉ levelArrays j' ∧ co jc ∉ levelArrays j' ∧
      cm jc ∉ levelArrays j')
    (hcovP : ∀ jc, (ca jc ∉ prepArrays ∧ co jc ∉ prepArrays ∧
        cm jc ∉ prepArrays) ∧
      ∀ i, (ca jc ≠ lv "cq.d" i ∧ ca jc ≠ lv "cq.v" i ∧
          ca jc ≠ lv "cq.u" i) ∧
        (co jc ≠ lv "cq.d" i ∧ co jc ≠ lv "cq.v" i ∧
          co jc ≠ lv "cq.u" i) ∧
        (cm jc ≠ lv "cq.d" i ∧ cm jc ≠ lv "cq.v" i ∧
          cm jc ≠ lv "cq.u" i))
 :
    ChildLoadParts B S ord ℓp htabF hbf Adm Scr ca co cm
      (prepCom S ℓp hbf co cm)
      (prepChan S ord ℓp htabF)
      (fun _ j A u => prepK S ord ℓp hbf j A u) := by
  intro k j A hdiag hAdm hbot u
  -- ### the ambient objects and bounds
  have hj1 : j + 1 ≤ S.depth := by omega
  set π : Equiv.Perm (Fin A.N) := (ord A.N A.G).order with hπ_def
  set clu : Set (Fin A.N) := cluster S A π u with hclu_def
  set kk : ℕ := childN S A π u with hkk_def
  have hkclu : kk = clu.ncard := rfl
  set kc : Fin kk := centreChild S A π u with hkc_def
  set Gpre : SimpleGraph (Fin kk) := preG S A π u with hGpre_def
  have huA : u ∈ clu := self_mem_cluster S A π u
  have huN : (u : ℕ) < A.N := u.2
  have hlpEq' : ℓp (j + 1) = ℓp j := hlpEq j hj1
  have hhbEq' : hbf (j + 1) = hbf j := hhbEq j hj1
  have hjlt : j < ℓp j := hlpRoom j hj1
  have hRhb : 2 * S.R + 1 ≤ hbf j := hhbR j hj1
  have hAL : A.hist.length = j := hAdmLen j A hAdm
  have hkN : kk ≤ A.N := set_ncard_le_card clu
  have hkpos : 0 < kk := zero_lt_childN S A π u
  have hNn0 : A.N ≤ n₀ := by
    have := Fintype.card_le_of_embedding A.up
    simpa using this
  have hn0pos : 0 < n₀ := by
    have := (Fin.pos_iff_nonempty.mpr ⟨u⟩ : 0 < A.N)
    omega
  have hNB : A.N < B := by omega
  have hNNB : A.N * A.N < B :=
    lt_of_le_of_lt (Nat.mul_le_mul hNn0 hNn0) hn0nB
  have hkB : kk < B := by omega
  have hkkB : kk * kk < B :=
    lt_of_le_of_lt (Nat.mul_le_mul (le_trans hkN hNn0) (le_trans hkN hNn0))
      hn0nB
  have huB : (u : ℕ) < B := by omega
  have hlpjB : ℓp j < B := hlpB j (by omega)
  have hhbjB : hbf j + 1 < B := hhbB j (by omega)
  have hhistjB : A.N * ℓp j * (hbf j + 1) < B :=
    lt_of_le_of_lt
      (Nat.mul_le_mul (Nat.mul_le_mul_right _ hNn0) le_rfl)
      (hhistB j (by omega))
  have hpaljB : A.N * S.pal j < B :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hNn0) (hpalB j (by omega))
  have hpalj1B : kk * S.pal (j + 1) < B :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (le_trans hkN hNn0))
      (hpalB (j + 1) hj1)
  -- the pass-scalar freshness kit for the level counter
  have hctrn : ∀ s ∈ (["cp.s", "cp.n", "cp.i", "cp.j", "cp.k", "cp.y",
      "cp.g", "cp.e", "cp.z"] : List String), ctrName j ≠ s := by
    intro s hs
    fin_cases hs <;> exact lv_ne_lit (by decide) (by decide) j
  -- ### the precondition, unpacked
  intro σ0 hpre
  obtain ⟨⟨⟨hAW0, htabL0, hscr0⟩, hctrA0, hcsr0, -⟩, hctr0⟩ := hpre
  clear hctrA0
  rw [← hπ_def] at hcsr0
  obtain ⟨hscr_l, hscr_r, hscr_b, hscr_d, hscr_p, hscr_x, hscr_v, hscr_w,
    hscr_o, hscr_t, hscr_c, hscr_qd, hscr_qv, hscr_qu⟩ := hscrA j σ0 hscr0
  obtain ⟨hlvl_off, hlvl_tgt, hlvl_col, hlvl_up, hlvl_hist⟩ :=
    hscrLvl j hj1 σ0 hscr0
  -- ### the parent channel row `u`, read off the windowed contract
  set WL : ℕ → List ℕ := fun e =>
    if he : e < ℓp j then
      List.map (fun z : Fin A.N => (z : ℕ)) (htabF j A u ⟨e, he⟩)
    else [] with hWL_def
  have hWLe : ∀ e, ∀ he : e < ℓp j,
      WL e = List.map (fun z : Fin A.N => (z : ℕ)) (htabF j A u ⟨e, he⟩) := by
    intro e he
    rw [hWL_def]
    exact dif_pos he
  have hhist_no : (arenaNames j).hist ≠ (arenaNames j).off :=
    lv_ne_of_base_ne (by decide) (by decide) j j
  have hhist_nt : (arenaNames j).hist ≠ (arenaNames j).tgt :=
    lv_ne_of_base_ne (by decide) (by decide) j j
  have hhist_nc : (arenaNames j).hist ≠ (arenaNames j).col :=
    lv_ne_of_base_ne (by decide) (by decide) j j
  have hhist_nu : (arenaNames j).hist ≠ (arenaNames j).up :=
    lv_ne_of_base_ne (by decide) (by decide) j j
  have hw_hist : arenaWs (arenaNames j) (S.pal j) (ℓp j) (hbf j)
      (Impl.ofArena A (htabF j A)).N (σ0.vars (arenaNames j).nS)
      (arenaNames j).hist
        = some ((Impl.ofArena A (htabF j A)).N * ℓp j * (hbf j + 1)) :=
    arenaWs_hist hhist_no hhist_nt hhist_nc hhist_nu
  have hhistL0 : A.N * ℓp j * (hbf j + 1)
      ≤ (σ0.arrs (arenaNames j).hist).length := hAW0.fits _ _ hw_hist
  have hblock : ∀ e, e < ℓp j →
      ((u : ℕ) * ℓp j + e) * (hbf j + 1) + (hbf j + 1)
        ≤ A.N * ℓp j * (hbf j + 1) := by
    intro e he
    have h1 : (u : ℕ) * ℓp j + e + 1 ≤ A.N * ℓp j := by
      have h2 : (u : ℕ) * ℓp j + e + 1 ≤ (u : ℕ) * ℓp j + ℓp j := by omega
      have h3 : (u : ℕ) * ℓp j + ℓp j = ((u : ℕ) + 1) * ℓp j :=
        (Nat.succ_mul _ _).symm
      have h4 : ((u : ℕ) + 1) * ℓp j ≤ A.N * ℓp j :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    calc ((u : ℕ) * ℓp j + e) * (hbf j + 1) + (hbf j + 1)
        = ((u : ℕ) * ℓp j + e + 1) * (hbf j + 1) := (Nat.succ_mul _ _).symm
      _ ≤ A.N * ℓp j * (hbf j + 1) := Nat.mul_le_mul_right _ h1
  have hWlen : ∀ e, e < ℓp j → (WL e).length ≤ hbf j := by
    intro e he
    rw [hWLe e he, List.length_map]
    exact (hAW0.st.hist.2 u ⟨e, he⟩).1
  have hWval : ∀ e, e < ℓp j → ∀ x ∈ WL e, x < A.N := by
    intro e he x hx
    rw [hWLe e he, List.mem_map] at hx
    obtain ⟨z, -, rfl⟩ := hx
    exact z.2
  have hWfacts : ∀ e, ∀ he : e < ℓp j,
      (σ0.arrs (arenaNames j).hist).getD
          (((u : ℕ) * ℓp j + e) * (hbf j + 1)) 0 = (WL e).length ∧
        ∀ i : ℕ, ∀ hi : i < (WL e).length,
          (σ0.arrs (arenaNames j).hist).getD
              (((u : ℕ) * ℓp j + e) * (hbf j + 1) + 1 + i) 0
            = (WL e)[i]'hi := by
    intro e he
    obtain ⟨hlen_e, hcell0_e, hcells_e⟩ := hAW0.st.hist.2 u ⟨e, he⟩
    have hwin : (winA (arenaWs (arenaNames j) (S.pal j) (ℓp j) (hbf j)
        (Impl.ofArena A (htabF j A)).N (σ0.vars (arenaNames j).nS)) σ0).arrs
          (arenaNames j).hist
        = (σ0.arrs (arenaNames j).hist).take
            ((Impl.ofArena A (htabF j A)).N * ℓp j * (hbf j + 1)) :=
      arrs_winA_some hw_hist σ0
    rw [hwin] at hcell0_e hcells_e
    have heq1 : (WL e).length = (htabF j A u ⟨e, he⟩).length := by
      rw [hWLe e he, List.length_map]
    constructor
    · have hbridge := getD_take_of_lt (l := σ0.arrs (arenaNames j).hist)
        (show ((u : ℕ) * ℓp j + e) * (hbf j + 1)
            < A.N * ℓp j * (hbf j + 1) from by
          have := hblock e he
          omega) 0
      exact hbridge.symm.trans (hcell0_e.trans heq1.symm)
    · intro i hi
      have hi' : i < (htabF j A u ⟨e, he⟩).length := heq1 ▸ hi
      have heq2 : (WL e)[i]'hi = ((htabF j A u ⟨e, he⟩)[i]'hi' : ℕ) := by
        simp only [hWLe e he, List.getElem_map]
      have hbridge := getD_take_of_lt (l := σ0.arrs (arenaNames j).hist)
        (show ((u : ℕ) * ℓp j + e) * (hbf j + 1) + 1 + i
            < A.N * ℓp j * (hbf j + 1) from by
          have h1 := hblock e he
          have h2 : i < (htabF j A u ⟨e, he⟩).length := hi'
          have h3 : (htabF j A u ⟨e, he⟩).length ≤ hbf j := hlen_e
          omega) 0
      exact hbridge.symm.trans ((hcells_e i hi').trans heq2.symm)
  -- ### §P1 the row bounds off the cover CSR
  obtain ⟨base, hco_u, hco_u1, hbase_cm, hbase_sq, hcoL, hrow⟩ :=
    clusterRow_read hcsr0 u
  rw [← hclu_def] at hco_u1 hbase_cm hbase_sq hrow
  have hbaseB : base < B := by omega
  have hbkB : base + kk < B := by
    rw [hkclu]
    omega
  have hvctr0 : (Expr.var (ctrName j)).evalB B σ0 = some ((u : ℕ)) := by
    rw [← hctr0]
    exact evalB_var (by rw [hctr0]; exact huB)
  have hread1 : (Expr.get (co j) (.var (ctrName j))).evalB B σ0
      = some base :=
    evalB_get hvctr0 (getElemQ_of_getD (by omega) hco_u) hbaseB
  set σA := σ0.setVar "cp.s" base with hσA_def
  have hrA : Run B (.assign "cp.s" (.get (co j) (.var (ctrName j)))) σ0 σA 3 :=
    Run.assign hread1
  have hctrA : σA.vars (ctrName j) = (u : ℕ) := by
    rw [hσA_def, vars_setVar, if_neg (hctrn "cp.s" (by decide))]
    exact hctr0
  have hread2 : (Expr.sub (.get (co j) (.add (.var (ctrName j)) (.lit 1)))
      (.var "cp.s")).evalB B σA = some kk := by
    have hvctrA : (Expr.var (ctrName j)).evalB B σA = some ((u : ℕ)) := by
      rw [← hctrA]
      exact evalB_var (by rw [hctrA]; exact huB)
    have hadd : (Expr.add (.var (ctrName j)) (.lit 1)).evalB B σA
        = some ((u : ℕ) + 1) := by
      have h := evalB_bin (op := .add) hvctrA (evalB_lit (n := 1) (by omega))
        (by rw [Bop.apply_add]; omega)
      rwa [Bop.apply_add] at h
    have hgetu1 : (Expr.get (co j) (.add (.var (ctrName j)) (.lit 1))).evalB
        B σA = some (base + kk) := by
      refine evalB_get hadd ?_ (by omega)
      rw [hσA_def, arrs_setVar]
      refine getElemQ_of_getD (by omega) ?_
      rw [hkclu]
      exact hco_u1
    have hvs : (Expr.var "cp.s").evalB B σA = some base := by
      have hsv : σA.vars "cp.s" = base := by
        rw [hσA_def, vars_setVar, if_pos rfl]
      rw [← hsv]
      exact evalB_var (by rw [hsv]; exact hbaseB)
    have h := evalB_bin (op := .sub) hgetu1 hvs
      (by rw [Bop.apply_sub]; omega)
    rw [Bop.apply_sub] at h
    rw [show base + kk - base = kk from by omega] at h
    exact h
  set σB := σA.setVar "cp.n" kk with hσB_def
  have hrB : Run B (.assign "cp.n"
      (.sub (.get (co j) (.add (.var (ctrName j)) (.lit 1)))
        (.var "cp.s"))) σA σB 7 :=
    Run.assign hread2
  have hrP1 : Run B (prepRowBoundsCom (co j) (ctrName j)) σ0 σB 10 :=
    (hrA.seq hrB).mono (by omega)
  -- σB facts
  have hB_arrs : σB.arrs = σ0.arrs := by
    rw [hσB_def, hσA_def]
    funext b
    rw [arrs_setVar, arrs_setVar]
  have hB_vars : ∀ y, y ≠ "cp.s" → y ≠ "cp.n" → σB.vars y = σ0.vars y := by
    intro y h1 h2
    rw [hσB_def, vars_setVar, if_neg h2, hσA_def, vars_setVar, if_neg h1]
  have hB_s : σB.vars "cp.s" = base := by
    rw [hσB_def, vars_setVar, if_neg (by decide), hσA_def, vars_setVar,
      if_pos rfl]
  have hB_n : σB.vars "cp.n" = kk := by
    rw [hσB_def, vars_setVar, if_pos rfl]
  -- ### §P2 the rank-scratch zero pass
  obtain ⟨σ2, hrP2, hz2, harr2, hlen2, hvar2⟩ :=
    (prepZero_spec (B := B) (N := A.N) (nNj := (arenaNames j).nN) hNB
      (lv_ne_lit (by decide) (by decide) j)) σB
      ⟨by
        rw [hB_vars (arenaNames j).nN (lv_ne_lit (by decide) (by decide) j)
          (lv_ne_lit (by decide) (by decide) j)]
        exact hAW0.n_eq,
       by rw [hB_arrs]; omega⟩
  -- ### §P3 the cluster-row pass
  have hcm_la : cm j ≠ "cp.l" := by
    intro h
    exact absurd (h ▸ (by decide : ("cp.l" : String) ∈ prepArrays))
      (hcovP j).1.2.2
  have hcm_ra : cm j ≠ "cp.r" := by
    intro h
    exact absurd (h ▸ (by decide : ("cp.r" : String) ∈ prepArrays))
      (hcovP j).1.2.2
  have hcm_bb : cm j ≠ "cp.b" := by
    intro h
    exact absurd (h ▸ (by decide : ("cp.b" : String) ∈ prepArrays))
      (hcovP j).1.2.2
  obtain ⟨σ3, hrP3, hla3, hmk3, hz3, hbb3, harr3, hlen3, hvar3⟩ :=
    (prepRow_spec (B := B) (N := A.N) (cmj := cm j) clu base hNB hNNB
      hbase_sq hcm_la hcm_ra hcm_bb) σ2
      ⟨by rw [hvar2 "cp.s" (by decide), hB_s],
       by rw [hvar2 "cp.n" (by decide), hB_n]; exact hkclu,
       by
        rw [harr2 (cm j) hcm_ra, hB_arrs]
        exact hbase_cm,
       fun t ht => by
        rw [harr2 (cm j) hcm_ra, hB_arrs]
        exact hrow t ht,
       by
        rw [harr2 "cp.l" (by decide), hB_arrs, ← hkclu]
        omega,
       by
        rw [harr2 "cp.b" (by decide), hB_arrs, ← hkclu]
        omega,
       by rw [hlen2 "cp.r", hB_arrs]; omega,
       hz2⟩
  -- ### §P4 the centre's own name and bit
  obtain ⟨σ4, hrP4, hz4, hbit4, hbito4, harr4, hlen4, hvar4⟩ :=
    (prepCentre_spec (B := B) (N := A.N) (ctr := ctrName j) clu u huA hNB
      (hctrn "cp.z" (by decide))) σ3
      ⟨by
        rw [hvar3 (ctrName j) (hctrn "cp.i" (by decide)),
          hvar2 (ctrName j) (hctrn "cp.i" (by decide)),
          hB_vars (ctrName j) (hctrn "cp.s" (by decide))
            (hctrn "cp.n" (by decide))]
        exact hctr0,
       by rw [hlen3 "cp.r", hlen2 "cp.r", hB_arrs]; omega,
       by rw [hlen3 "cp.b", hlen2 "cp.b", hB_arrs, ← hkclu]; omega,
       fun t ht => hmk3 t ht⟩
  set t0 : Fin clu.ncard := (setEquiv clu).symm ⟨u, huA⟩ with ht0_def
  have hkct0 : ((kc : Fin kk) : ℕ) = ((t0 : Fin clu.ncard) : ℕ) := rfl
  have hembt0 : Impl.restrictEmb clu t0 = u := by
    rw [Impl.restrictEmb_apply, ht0_def, Equiv.apply_symm_apply]
  have hemb_inj : ∀ x : Fin clu.ncard, Impl.restrictEmb clu x = u →
      x = t0 := by
    intro x hx
    have h1 : ((setEquiv clu) x : ↥clu) = ⟨u, huA⟩ := Subtype.ext hx
    rw [ht0_def, ← h1, Equiv.symm_apply_apply]
  -- ### §P5 the batch trace over the channel row
  have hhist_cp : ∀ s ∈ (["cp.s", "cp.n", "cp.i", "cp.j", "cp.k", "cp.y",
      "cp.g", "cp.e", "cp.z", "cp.l", "cp.r", "cp.b", "cp.w", "cp.d",
      "cp.p", "cp.x", "cp.v", "cp.o", "cp.t", "cp.c", "cp.m"] : List String),
      (arenaNames j).hist ≠ s := by
    intro s hs
    fin_cases hs <;> exact lv_ne_lit (by decide) (by decide) j
  have hhist_arr4 : σ4.arrs (arenaNames j).hist
      = σ0.arrs (arenaNames j).hist := by
    rw [harr4 (arenaNames j).hist (hhist_cp "cp.b" (by decide)),
      harr3 (arenaNames j).hist (hhist_cp "cp.l" (by decide))
        (hhist_cp "cp.r" (by decide)) (hhist_cp "cp.b" (by decide)),
      harr2 (arenaNames j).hist (hhist_cp "cp.r" (by decide)), hB_arrs]
  obtain ⟨σ5, hrP5, hbit5, harr5, hlen5, hvar5⟩ :=
    (prepBatch_spec (B := B) (N := A.N) (ℓpj := ℓp j) (hbj := hbf j)
      (histj := (arenaNames j).hist) (ctr := ctrName j) clu (u : ℕ) WL hNB
      hlpjB hhbjB hhistjB huN hWlen hWval
      (hctrn "cp.i" (by decide)) (hctrn "cp.j" (by decide))
      (hctrn "cp.k" (by decide)) (hctrn "cp.y" (by decide))
      (hctrn "cp.g" (by decide)) (hctrn "cp.e" (by decide))
      (hhist_cp "cp.b" (by decide))) σ4
      ⟨by
        rw [hvar4 (ctrName j) (hctrn "cp.z" (by decide)),
          hvar3 (ctrName j) (hctrn "cp.i" (by decide)),
          hvar2 (ctrName j) (hctrn "cp.i" (by decide)),
          hB_vars (ctrName j) (hctrn "cp.s" (by decide))
            (hctrn "cp.n" (by decide))]
        exact hctr0,
       by rw [hhist_arr4]; exact hhistL0,
       fun e he => by
        rw [hhist_arr4]
        exact ⟨(hWfacts e he).1, (hWfacts e he).2⟩,
       by rw [hlen4 "cp.r", hlen3 "cp.r", hlen2 "cp.r", hB_arrs]; omega,
       by
        rw [hlen4 "cp.b", hlen3 "cp.b", hlen2 "cp.b", hB_arrs, ← hkclu]
        omega,
       fun t ht => by
        rw [harr4 "cp.r" (by decide)]
        exact hmk3 t ht,
       fun p hp hne => by
        rw [harr4 "cp.r" (by decide)]
        exact hz3 p hp hne,
       fun t ht => by
        by_cases hteq : t = ((t0 : Fin clu.ncard) : ℕ)
        · subst hteq
          right
          exact hbit4
        · left
          rw [hbito4 t hteq]
          exact hbb3 t ht⟩
  -- the bits now hold the batch indicator
  have hbatch_pin : {t : Fin kk |
      Impl.restrictEmb clu t = u ∨
        ∃ e : Fin (ℓp j), Impl.restrictEmb clu t ∈ htabF j A u e}
      = batchSet S A π u :=
    marks_eq_batchSet S A π u (htabF j A)
      (fun e he z => hpin j A hAdm u e he z)
      (fun e hle => hpinE j A hAdm u e hle)
      (by rw [hAL]; omega)
  have hbits5 : ∀ t, ∀ ht : t < clu.ncard,
      (σ5.arrs "cp.b").getD t 0
        = if (⟨t, ht⟩ : Fin kk) ∈ batchSet S A π u then 1 else 0 := by
    intro t ht
    rw [hbit5 t ht]
    refine if_congr ?_ rfl rfl
    rw [← hbatch_pin]
    show ((σ4.arrs "cp.b").getD t 0 = 1 ∨
        ∃ e, e < ℓp j ∧ ((Impl.restrictEmb clu ⟨t, ht⟩ : Fin A.N) : ℕ) ∈ WL e)
      ↔ (Impl.restrictEmb clu ⟨t, ht⟩ = u ∨
        ∃ e : Fin (ℓp j), Impl.restrictEmb clu ⟨t, ht⟩ ∈ htabF j A u e)
    constructor
    · rintro (h1 | ⟨e, he, hmem⟩)
      · left
        by_cases hteq : t = ((t0 : Fin clu.ncard) : ℕ)
        · have hx : (⟨t, ht⟩ : Fin clu.ncard) = t0 := Fin.ext hteq
          calc Impl.restrictEmb clu ⟨t, ht⟩
              = Impl.restrictEmb clu t0 := congrArg _ hx
            _ = u := hembt0
        · rw [hbito4 t hteq, hbb3 t ht] at h1
          exact absurd h1 (by omega)
      · right
        rw [hWLe e he, List.mem_map] at hmem
        obtain ⟨z, hz, hze⟩ := hmem
        refine ⟨⟨e, he⟩, ?_⟩
        rwa [show z = Impl.restrictEmb clu ⟨t, ht⟩ from Fin.ext hze] at hz
    · rintro (h1 | ⟨e, hmem⟩)
      · left
        have hx : (⟨t, ht⟩ : Fin clu.ncard) = t0 := hemb_inj ⟨t, ht⟩ h1
        rw [show t = ((t0 : Fin clu.ncard) : ℕ) from congrArg Fin.val hx]
        exact hbit4
      · right
        refine ⟨(e : ℕ), e.2, ?_⟩
        rw [hWLe (e : ℕ) e.2, List.mem_map]
        exact ⟨Impl.restrictEmb clu ⟨t, ht⟩, hmem, rfl⟩
  -- ### §P6 the padded width array
  have hMw : (batchSet S A π u).ncard ≤ S.width :=
    (batchSet_ncard_le S A π u).trans (by rw [hAL]; exact hwidth j hj1)
  obtain ⟨σ6, hrP6, hwc6, harr6, hlen6, hvar6⟩ :=
    (prepWidth_spec (B := B) (k := kk) (width := S.width)
      (batchSet S A π u) ((t0 : Fin clu.ncard) : ℕ) hkB hwB hMw t0.2) σ5
      ⟨by
        rw [hvar5 "cp.n" (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide),
          hvar4 "cp.n" (by decide), hvar3 "cp.n" (by decide),
          hvar2 "cp.n" (by decide), hB_n],
       by
        rw [hvar5 "cp.z" (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]
        exact hz4,
       by
        rw [hlen5 "cp.w", hlen4 "cp.w", hlen3 "cp.w", hlen2 "cp.w", hB_arrs]
        exact hscr_w,
       by
        rw [hlen5 "cp.b", hlen4 "cp.b", hlen3 "cp.b", hlen2 "cp.b", hB_arrs]
        omega,
       fun t ht => hbits5 t ht⟩
  -- ### §P7 the mark clear
  have hvar65 : ∀ y : String,
      (∀ s ∈ (["cp.s", "cp.n", "cp.i", "cp.j", "cp.k", "cp.y", "cp.g",
        "cp.e", "cp.z"] : List String), y ≠ s) →
      σ6.vars y = σ0.vars y := by
    intro y hy
    rw [hvar6 y (hy "cp.i" (by decide)) (hy "cp.k" (by decide))
        (hy "cp.e" (by decide)),
      hvar5 y (hy "cp.i" (by decide)) (hy "cp.j" (by decide))
        (hy "cp.k" (by decide)) (hy "cp.y" (by decide))
        (hy "cp.g" (by decide)) (hy "cp.e" (by decide)),
      hvar4 y (hy "cp.z" (by decide)), hvar3 y (hy "cp.i" (by decide)),
      hvar2 y (hy "cp.i" (by decide)),
      hB_vars y (hy "cp.s" (by decide)) (hy "cp.n" (by decide))]
  have harr60 : ∀ b : String, b ≠ "cp.r" → b ≠ "cp.w" → b ≠ "cp.b" →
      b ≠ "cp.l" → σ6.arrs b = σ0.arrs b := by
    intro b h1 h2 h3 h4
    rw [harr6 b h2, harr5 b h3, harr4 b h3, harr3 b h4 h1 h3, harr2 b h1,
      hB_arrs]
  have hcp_s6 : σ6.vars "cp.s" = base := by
    rw [hvar6 "cp.s" (by decide) (by decide) (by decide),
      hvar5 "cp.s" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide),
      hvar4 "cp.s" (by decide), hvar3 "cp.s" (by decide),
      hvar2 "cp.s" (by decide), hB_s]
  have hcp_n6 : σ6.vars "cp.n" = clu.ncard := by
    rw [hvar6 "cp.n" (by decide) (by decide) (by decide),
      hvar5 "cp.n" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide),
      hvar4 "cp.n" (by decide), hvar3 "cp.n" (by decide),
      hvar2 "cp.n" (by decide), hB_n]
    exact hkclu
  obtain ⟨σ7, hrP7, hz7, harr7, hlen7, hvar7⟩ :=
    (prepClear_spec (B := B) (N := A.N) (cmj := cm j) clu base hNB hNNB
      hbase_sq hcm_ra) σ6
      ⟨hcp_s6,
       hcp_n6,
       by
        rw [harr60 (cm j) hcm_ra (by
            intro h
            exact absurd (h ▸ (by decide : ("cp.w" : String) ∈ prepArrays))
              (hcovP j).1.2.2) hcm_bb hcm_la]
        exact hbase_cm,
       fun t ht => by
        rw [harr60 (cm j) hcm_ra (by
            intro h
            exact absurd (h ▸ (by decide : ("cp.w" : String) ∈ prepArrays))
              (hcovP j).1.2.2) hcm_bb hcm_la]
        exact hrow t ht,
       by
        rw [harr6 "cp.r" (by decide), harr5 "cp.r" (by decide),
          harr4 "cp.r" (by decide), hlen3 "cp.r", hlen2 "cp.r", hB_arrs]
        omega,
       fun p hp hne => by
        rw [harr6 "cp.r" (by decide), harr5 "cp.r" (by decide),
          harr4 "cp.r" (by decide)]
        exact hz3 p hp hne⟩
  -- ### §P8 the restrict stage
  -- the four input cells
  have hcp_n7 : σ7.vars "cp.n" = clu.ncard := by
    rw [hvar7 "cp.n" (by decide)]
    exact hcp_n6
  have hpaljB' : S.pal j < B := by
    have h1 : S.pal j ≤ n₀ * S.pal j := Nat.le_mul_of_pos_left _ hn0pos
    have h2 := hpalB j (by omega)
    omega
  have hrK : Run B (.assign "rs.k" (.var "cp.n"))
      σ7 (σ7.setVar "rs.k" clu.ncard) 2 := by
    refine Run.assign ?_
    rw [← hcp_n7]
    exact evalB_var (by rw [hcp_n7, ← hkclu]; omega)
  have hrL : Run B (.assign "rs.l" (.lit (S.pal j)))
      (σ7.setVar "rs.k" clu.ncard)
      ((σ7.setVar "rs.k" clu.ncard).setVar "rs.l" (S.pal j)) 2 :=
    Run.assign (evalB_lit hpaljB')
  have hrPp : Run B (.assign "rs.p" (.lit (ℓp j)))
      ((σ7.setVar "rs.k" clu.ncard).setVar "rs.l" (S.pal j))
      (((σ7.setVar "rs.k" clu.ncard).setVar "rs.l" (S.pal j)).setVar
        "rs.p" (ℓp j)) 2 :=
    Run.assign (evalB_lit hlpjB)
  have hrH : Run B (.assign "rs.h" (.lit (hbf j)))
      (((σ7.setVar "rs.k" clu.ncard).setVar "rs.l" (S.pal j)).setVar
        "rs.p" (ℓp j))
      ((((σ7.setVar "rs.k" clu.ncard).setVar "rs.l" (S.pal j)).setVar
        "rs.p" (ℓp j)).setVar "rs.h" (hbf j)) 2 :=
    Run.assign (evalB_lit (by omega))
  set σ8p := ((((σ7.setVar "rs.k" clu.ncard).setVar "rs.l"
    (S.pal j)).setVar "rs.p" (ℓp j)).setVar "rs.h" (hbf j)) with hσ8p_def
  have h8p_arrs : σ8p.arrs = σ7.arrs := by
    rw [hσ8p_def]
    funext b
    rw [arrs_setVar, arrs_setVar, arrs_setVar, arrs_setVar]
  have h8p_vars : ∀ y : String, y ≠ "rs.k" → y ≠ "rs.l" → y ≠ "rs.p" →
      y ≠ "rs.h" → σ8p.vars y = σ7.vars y := by
    intro y h1 h2 h3 h4
    rw [hσ8p_def, vars_setVar, if_neg h4, vars_setVar, if_neg h3,
      vars_setVar, if_neg h2, vars_setVar, if_neg h1]
  -- the (j)-regions and cells never moved
  have harr70 : ∀ b : String, b ≠ "cp.r" → b ≠ "cp.w" → b ≠ "cp.b" →
      b ≠ "cp.l" → σ8p.arrs b = σ0.arrs b := by
    intro b h1 h2 h3 h4
    rw [h8p_arrs, harr7 b h1, harr60 b h1 h2 h3 h4]
  have hvar70 : ∀ y : String,
      (∀ s ∈ (["cp.s", "cp.n", "cp.i", "cp.j", "cp.k", "cp.y", "cp.g",
        "cp.e", "cp.z", "rs.k", "rs.l", "rs.p", "rs.h"] : List String),
        y ≠ s) →
      σ8p.vars y = σ0.vars y := by
    intro y hy
    rw [h8p_vars y (hy "rs.k" (by decide)) (hy "rs.l" (by decide))
        (hy "rs.p" (by decide)) (hy "rs.h" (by decide)),
      hvar7 y (hy "cp.i" (by decide)),
      hvar6 y (hy "cp.i" (by decide)) (hy "cp.k" (by decide))
        (hy "cp.e" (by decide)),
      hvar5 y (hy "cp.i" (by decide)) (hy "cp.j" (by decide))
        (hy "cp.k" (by decide)) (hy "cp.y" (by decide))
        (hy "cp.g" (by decide)) (hy "cp.e" (by decide)),
      hvar4 y (hy "cp.z" (by decide)), hvar3 y (hy "cp.i" (by decide)),
      hvar2 y (hy "cp.i" (by decide)),
      hB_vars y (hy "cp.s" (by decide)) (hy "cp.n" (by decide))]
  have hAW8 : ArenaStW (arenaNames j) (hbf j) (Impl.ofArena A (htabF j A))
      σ8p := by
    refine arenaStW_of_eq hAW0 ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact hvar70 (arenaNames j).nN
        (fun s hs => by fin_cases hs <;>
          exact lv_ne_lit (by decide) (by decide) j)
    · exact hvar70 (arenaNames j).nS
        (fun s hs => by fin_cases hs <;>
          exact lv_ne_lit (by decide) (by decide) j)
    · exact harr70 (arenaNames j).off (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
    · exact harr70 (arenaNames j).tgt (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
    · exact harr70 (arenaNames j).col (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
    · exact harr70 (arenaNames j).up (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
    · exact harr70 (arenaNames j).hist (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
        (lv_ne_lit (by decide) (by decide) j)
  -- the restrict stage's name kit
  have hdisj8 : ∀ x ∈ (["cp.o", "cp.t", "cp.c", lv "sa.u" (j + 1),
      lv "sa.h" (j + 1), "cp.r"] : List String),
      ∀ y ∈ ([lv "sa.o" j, lv "sa.t" j, lv "sa.c" j, lv "sa.u" j,
        lv "sa.h" j, "cp.l"] : List String),
      x ≠ y := by
    intro x hx y hy
    fin_cases hx <;> fin_cases hy <;>
      first
        | decide
        | exact Ne.symm (lv_ne_lit (by decide) (by decide) j)
        | exact lv_ne_lit (by decide) (by decide) (j + 1)
        | exact lv_ne_of_level_ne (by decide) (by omega)
  have hpair8 : (["cp.o", "cp.t", "cp.c", lv "sa.u" (j + 1),
      lv "sa.h" (j + 1), "cp.r"] : List String).Pairwise (· ≠ ·) := by
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_
      (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
        (List.Pairwise.cons ?_ (List.pairwise_singleton _ _)))))
    all_goals intro y hy
    all_goals fin_cases hy
    all_goals
      first
        | decide
        | exact Ne.symm (lv_ne_lit (by decide) (by decide) (j + 1))
        | exact lv_ne_lit (by decide) (by decide) (j + 1)
        | exact lv_ne_of_base_ne (by decide) (by decide) (j + 1) (j + 1)
  have hnd5P8 : ([(arenaNames j).off, (arenaNames j).tgt,
      (arenaNames j).col, (arenaNames j).up, (arenaNames j).hist] :
      List String).Nodup :=
    List.Nodup.sublist (List.sublist_append_left _ _)
      (arenaNames_arrays_nodup j)
  have hla58 : "cp.l" ∉ ([(arenaNames j).off, (arenaNames j).tgt,
      (arenaNames j).col, (arenaNames j).up, (arenaNames j).hist] :
      List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm (lv_ne_lit (by decide) (by decide) j),
      Ne.symm (lv_ne_lit (by decide) (by decide) j),
      Ne.symm (lv_ne_lit (by decide) (by decide) j),
      Ne.symm (lv_ne_lit (by decide) (by decide) j),
      Ne.symm (lv_ne_lit (by decide) (by decide) j)⟩
  have hkn0 : clu.ncard ≤ n₀ :=
    le_trans (le_of_eq hkclu.symm) (le_trans hkN hNn0)
  obtain ⟨σ8, hrR8, hAWc8, hnsC8, hAWp8, hnsP8, hcl8, hrsk8, hraL8,
    hraC8⟩ :=
    (restrictCom_specW (B := B) (A := Impl.ofArena A (htabF j A)) (S := clu)
      (nmP := arenaNames j) (nmC := prepNmR j) (la := "cp.l") (ra := "cp.r")
      hNB hNNB hn0B hpaljB hhistjB hdisj8 hpair8
      (show lv "sv.n" (j + 1) ∉ rsScalars from
        lv_not_mem (by decide) (by decide) (j + 1))
      (show ("cp.m" : String) ∉ rsScalars by decide)
      (show lv "sv.n" (j + 1) ≠ "cp.m" from
        lv_ne_lit (by decide) (by decide) (j + 1))
      (show lv "sv.n" j ∉ rsScalars from
        lv_not_mem (by decide) (by decide) j)
      (show lv "sv.m" j ∉ rsScalars from
        lv_not_mem (by decide) (by decide) j)
      (show lv "sv.n" j ≠ lv "sv.n" (j + 1) from
        lv_ne_of_level_ne (by decide) (by omega))
      (show lv "sv.n" j ≠ "cp.m" from lv_ne_lit (by decide) (by decide) j)
      (show lv "sv.m" j ≠ lv "sv.n" (j + 1) from
        lv_ne_of_level_ne (by decide) (by omega))
      (show lv "sv.m" j ≠ "cp.m" from lv_ne_lit (by decide) (by decide) j)
      hnd5P8 hla58) σ8p
      ⟨hAW8,
       ⟨by
          rw [h8p_arrs, harr7 "cp.l" (by decide), harr6 "cp.l" (by decide),
            harr5 "cp.l" (by decide), harr4 "cp.l" (by decide),
            hlen3 "cp.l", hlen2 "cp.l", hB_arrs]
          exact le_trans hkn0 hscr_l,
        fun t ht => by
          rw [h8p_arrs, harr7 "cp.l" (by decide), harr6 "cp.l" (by decide),
            harr5 "cp.l" (by decide), harr4 "cp.l" (by decide)]
          exact hla3 t ht⟩,
       by
        rw [hσ8p_def, vars_setVar, if_neg (by decide), vars_setVar,
          if_neg (by decide), vars_setVar, if_neg (by decide), vars_setVar,
          if_pos rfl]
        rfl,
       by
        rw [hσ8p_def, vars_setVar, if_neg (by decide), vars_setVar,
          if_neg (by decide), vars_setVar, if_pos rfl],
       by
        rw [hσ8p_def, vars_setVar, if_neg (by decide), vars_setVar,
          if_pos rfl],
       by rw [hσ8p_def, vars_setVar, if_pos rfl],
       by
        show A.N ≤ (σ8p.arrs "cp.r").length
        rw [h8p_arrs, hlen7 "cp.r", hlen6 "cp.r", hlen5 "cp.r",
          hlen4 "cp.r", hlen3 "cp.r", hlen2 "cp.r", hB_arrs]
        omega,
       by
        show (σ8p.arrs "cp.r").take A.N = arrOf A.N (fun _ => 0)
        refine take_eq_arrOf_zero ?_ ?_
        · rw [h8p_arrs, hlen7 "cp.r", hlen6 "cp.r", hlen5 "cp.r",
            hlen4 "cp.r", hlen3 "cp.r", hlen2 "cp.r", hB_arrs]
          omega
        · intro p hp
          rw [h8p_arrs]
          exact hz7 p hp,
       by
        show clu.ncard + 1 ≤ (σ8p.arrs "cp.o").length
        rw [harr70 "cp.o" (by decide) (by decide) (by decide) (by decide)]
        omega,
       by
        show (∑ v : Fin ((Impl.ofArena A (htabF j A)).restrict clu).N,
            ((Impl.ofArena A (htabF j A)).restrict clu).G.degree v)
          ≤ (σ8p.arrs "cp.t").length
        have hdeg : (∑ v : Fin ((Impl.ofArena A (htabF j A)).restrict
            clu).N, ((Impl.ofArena A (htabF j A)).restrict clu).G.degree v)
            ≤ clu.ncard * clu.ncard :=
          degSum_le_sq _
        have hct : n₀ * n₀ ≤ (σ8p.arrs "cp.t").length := by
          rw [harr70 "cp.t" (by decide) (by decide) (by decide) (by decide)]
          exact hscr_t
        have hle2 : clu.ncard * clu.ncard ≤ n₀ * n₀ :=
          Nat.mul_le_mul hkn0 hkn0
        omega,
       by
        show clu.ncard * S.pal j ≤ (σ8p.arrs "cp.c").length
        rw [harr70 "cp.c" (by decide) (by decide) (by decide) (by decide)]
        exact le_trans (Nat.mul_le_mul_right _ hkn0) hscr_c,
       by
        show clu.ncard ≤ (σ8p.arrs (arenaNames (j + 1)).up).length
        rw [harr70 (arenaNames (j + 1)).up
          (lv_ne_lit (by decide) (by decide) (j + 1))
          (lv_ne_lit (by decide) (by decide) (j + 1))
          (lv_ne_lit (by decide) (by decide) (j + 1))
          (lv_ne_lit (by decide) (by decide) (j + 1))]
        exact le_trans hkn0 hlvl_up,
       by
        show clu.ncard * ℓp j * (hbf j + 1)
          ≤ (σ8p.arrs (arenaNames (j + 1)).hist).length
        rw [harr70 (arenaNames (j + 1)).hist
          (lv_ne_lit (by decide) (by decide) (j + 1))
          (lv_ne_lit (by decide) (by decide) (j + 1))
          (lv_ne_lit (by decide) (by decide) (j + 1))
          (lv_ne_lit (by decide) (by decide) (j + 1))]
        exact le_trans
          (Nat.mul_le_mul (Nat.mul_le_mul_right _ hkn0) le_rfl) hlvl_hist⟩
  -- ### §P9 the BFS at radius `2R` from the centre's child name
  set APc : Impl.MArena (S.pal j) n₀ (ℓp j) :=
    (Impl.ofArena A (htabF j A)).restrict clu with hAPc_def
  set cns : ℕ := ∑ v : Fin APc.N, APc.G.degree v with hcns_def
  have hcluB : clu.ncard < B := hkclu ▸ hkB
  have hclusqB : clu.ncard * clu.ncard < B := by
    have := hkkB
    rw [hkclu] at this
    exact this
  have hcnsB : cns < B := by
    have h1 : cns ≤ clu.ncard * clu.ncard := degSum_le_sq _
    have h2 : clu.ncard * clu.ncard ≤ n₀ * n₀ := Nat.mul_le_mul hkn0 hkn0
    omega
  -- the frame across the restrict stage
  have hfrR : ∀ y : String, y ∉ rsScalars → y ≠ (arenaNames (j + 1)).nN →
      y ≠ "cp.m" → σ8.vars y = σ8p.vars y := by
    intro y h1 h2 h3
    refine hrR8.frame_var y ?_
    intro hmem
    rcases wvars_restrictCom_subset _ _ _ _ y hmem with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
  have hfaR : ∀ b : String, b ≠ "cp.r" → b ≠ "cp.o" → b ≠ "cp.t" →
      b ≠ "cp.c" → b ≠ (arenaNames (j + 1)).up →
      b ≠ (arenaNames (j + 1)).hist → σ8.arrs b = σ8p.arrs b := by
    intro b h1 h2 h3 h4 h5 h6
    refine hrR8.frame_arr b ?_
    rw [warrs_restrictCom]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨h1, h2, h3, h2, h4, h5, h6, h6, h1⟩
  have hcpn8 : σ8.vars "cp.n" = clu.ncard := by
    rw [hfrR "cp.n" (by decide)
        (Ne.symm (lv_ne_lit (by decide) (by decide) (j + 1))) (by decide),
      h8p_vars "cp.n" (by decide) (by decide) (by decide) (by decide)]
    exact hcp_n7
  have hcpm8 : σ8.vars "cp.m" = cns := hnsC8
  have hcpz8 : σ8.vars "cp.z" = ((t0 : Fin clu.ncard) : ℕ) := by
    rw [hfrR "cp.z" (by decide)
        (Ne.symm (lv_ne_lit (by decide) (by decide) (j + 1))) (by decide),
      h8p_vars "cp.z" (by decide) (by decide) (by decide) (by decide),
      hvar7 "cp.z" (by decide),
      hvar6 "cp.z" (by decide) (by decide) (by decide),
      hvar5 "cp.z" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact hz4
  have ht0B : ((t0 : Fin clu.ncard) : ℕ) < B := by
    have := t0.2
    omega
  -- the four input cells
  have hrb1 : Run B (.assign "bf.n" (.var "cp.n")) σ8
      (σ8.setVar "bf.n" clu.ncard) 2 := by
    refine Run.assign ?_
    rw [← hcpn8]
    exact evalB_var (by rw [hcpn8]; exact hcluB)
  have hrb2 : Run B (.assign "bf.m" (.var "cp.m"))
      (σ8.setVar "bf.n" clu.ncard)
      ((σ8.setVar "bf.n" clu.ncard).setVar "bf.m" cns) 2 := by
    refine Run.assign ?_
    have hv : (σ8.setVar "bf.n" clu.ncard).vars "cp.m" = cns := by
      rw [vars_setVar, if_neg (by decide)]
      exact hcpm8
    rw [← hv]
    exact evalB_var (by rw [hv]; exact hcnsB)
  have hrb3 : Run B (.assign "bf.r" (.lit (2 * S.R)))
      ((σ8.setVar "bf.n" clu.ncard).setVar "bf.m" cns)
      (((σ8.setVar "bf.n" clu.ncard).setVar "bf.m" cns).setVar "bf.r"
        (2 * S.R)) 2 :=
    Run.assign (evalB_lit (by omega))
  have hrb4 : Run B (.assign "bf.v" (.var "cp.z"))
      (((σ8.setVar "bf.n" clu.ncard).setVar "bf.m" cns).setVar "bf.r"
        (2 * S.R))
      ((((σ8.setVar "bf.n" clu.ncard).setVar "bf.m" cns).setVar "bf.r"
        (2 * S.R)).setVar "bf.v" ((t0 : Fin clu.ncard) : ℕ)) 2 := by
    refine Run.assign ?_
    have hv : (((σ8.setVar "bf.n" clu.ncard).setVar "bf.m" cns).setVar
        "bf.r" (2 * S.R)).vars "cp.z" = ((t0 : Fin clu.ncard) : ℕ) := by
      rw [vars_setVar, if_neg (by decide), vars_setVar, if_neg (by decide),
        vars_setVar, if_neg (by decide)]
      exact hcpz8
    rw [← hv]
    exact evalB_var (by rw [hv]; exact ht0B)
  set σ9p : Env := (((σ8.setVar "bf.n" clu.ncard).setVar "bf.m" cns).setVar
    "bf.r" (2 * S.R)).setVar "bf.v" ((t0 : Fin clu.ncard) : ℕ) with hσ9p_def
  have h9p_arrs : σ9p.arrs = σ8.arrs := by
    rw [hσ9p_def]
    funext b
    rw [arrs_setVar, arrs_setVar, arrs_setVar, arrs_setVar]
  have h9p_vars : ∀ y : String, y ≠ "bf.n" → y ≠ "bf.m" → y ≠ "bf.r" →
      y ≠ "bf.v" → σ9p.vars y = σ8.vars y := by
    intro y h1 h2 h3 h4
    rw [hσ9p_def, vars_setVar, if_neg h4, vars_setVar, if_neg h3,
      vars_setVar, if_neg h2, vars_setVar, if_neg h1]
  have hAW9p : ArenaStW (prepNmR j) (hbf j) APc σ9p := by
    refine arenaStW_of_eq hAWc8 ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact h9p_vars (prepNmR j).nN
        (show lv "sv.n" (j + 1) ≠ "bf.n" from
          lv_ne_lit (by decide) (by decide) (j + 1))
        (show lv "sv.n" (j + 1) ≠ "bf.m" from
          lv_ne_lit (by decide) (by decide) (j + 1))
        (show lv "sv.n" (j + 1) ≠ "bf.r" from
          lv_ne_lit (by decide) (by decide) (j + 1))
        (show lv "sv.n" (j + 1) ≠ "bf.v" from
          lv_ne_lit (by decide) (by decide) (j + 1))
    · exact h9p_vars (prepNmR j).nS
        (show ("cp.m" : String) ≠ "bf.n" by decide)
        (show ("cp.m" : String) ≠ "bf.m" by decide)
        (show ("cp.m" : String) ≠ "bf.r" by decide)
        (show ("cp.m" : String) ≠ "bf.v" by decide)
    · rw [h9p_arrs]
    · rw [h9p_arrs]
    · rw [h9p_arrs]
    · rw [h9p_arrs]
    · rw [h9p_arrs]
  have hda5R : ("cp.d" : String) ∉ ([(prepNmR j).off, (prepNmR j).tgt,
      (prepNmR j).col, (prepNmR j).up, (prepNmR j).hist] : List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨show ("cp.d" : String) ≠ "cp.o" by decide,
      show ("cp.d" : String) ≠ "cp.t" by decide,
      show ("cp.d" : String) ≠ "cp.c" by decide,
      show ("cp.d" : String) ≠ lv "sa.u" (j + 1) from
        Ne.symm (lv_ne_lit (by decide) (by decide) (j + 1)),
      show ("cp.d" : String) ≠ lv "sa.h" (j + 1) from
        Ne.symm (lv_ne_lit (by decide) (by decide) (j + 1))⟩
  obtain ⟨σ9, hrB9, hAW9, hns9, hlen9, hdle9, hBT9⟩ :=
    (bfsCom_specW (B := B) (A := APc) (nm := prepNmR j) (da := "cp.d")
      (d := 2 * S.R) (t0 : Fin APc.N) hcluB hclusqB
      (show 2 * S.R + 2 < B by omega)
      (show ("cp.t" : String) ≠ "cp.o" by decide) hda5R
      (show lv "sv.n" (j + 1) ∉ bfScalars from
        lv_not_mem (by decide) (by decide) (j + 1))
      (show ("cp.m" : String) ∉ bfScalars by decide)) σ9p
      ⟨hAW9p,
       by
        rw [hσ9p_def, vars_setVar, if_neg (by decide), vars_setVar,
          if_neg (by decide), vars_setVar, if_neg (by decide), vars_setVar,
          if_pos rfl]
        rfl,
       by
        have hL : σ9p.vars "bf.m" = cns := by
          rw [hσ9p_def, vars_setVar, if_neg (by decide), vars_setVar,
            if_neg (by decide), vars_setVar, if_pos rfl]
        have hR : σ9p.vars "cp.m" = cns := by
          rw [h9p_vars "cp.m" (by decide) (by decide) (by decide)
            (by decide)]
          exact hcpm8
        exact hL.trans hR.symm,
       by
        rw [hσ9p_def, vars_setVar, if_neg (by decide), vars_setVar,
          if_pos rfl],
       by rw [hσ9p_def, vars_setVar, if_pos rfl],
       by
        rw [h9p_arrs,
          hfaR "cp.d" (by decide) (by decide) (by decide) (by decide)
            (Ne.symm (lv_ne_lit (by decide) (by decide) (j + 1)))
            (Ne.symm (lv_ne_lit (by decide) (by decide) (j + 1))),
          h8p_arrs, harr7 "cp.d" (by decide), harr60 "cp.d" (by decide)
            (by decide) (by decide) (by decide)]
        exact le_trans hkn0 hscr_d⟩
  -- ### the mid-state contract for the remaining stages
  have hfrB : ∀ y : String, y ∉ bfScalars → σ9.vars y = σ9p.vars y := by
    intro y h1
    refine hrB9.frame_var y ?_
    intro hmem
    exact h1 (wvars_bfsCom_subset _ _ _ y hmem)
  have hfaB : ∀ b : String, b ≠ "cp.d" → σ9.arrs b = σ9p.arrs b := by
    intro b h1
    refine hrB9.frame_arr b ?_
    rw [warrs_bfsCom]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨h1, h1, h1⟩
  have hcpn9 : σ9.vars "cp.n" = clu.ncard := by
    rw [hfrB "cp.n" (by decide),
      h9p_vars "cp.n" (by decide) (by decide) (by decide) (by decide)]
    exact hcpn8
  have hcpm9 : σ9.vars "cp.m" = cns := by
    have h2 : σ9p.vars (prepNmR j).nS = cns := by
      rw [h9p_vars (prepNmR j).nS
        (show ("cp.m" : String) ≠ "bf.n" by decide)
        (show ("cp.m" : String) ≠ "bf.m" by decide)
        (show ("cp.m" : String) ≠ "bf.r" by decide)
        (show ("cp.m" : String) ≠ "bf.v" by decide)]
      exact hcpm8
    exact hns9.trans h2
  have hlen90 : ∀ b, (σ9.arrs b).length = (σ0.arrs b).length := by
    intro b
    rw [hlen9 b, h9p_arrs, run_arrs_length_eq hrR8 b, h8p_arrs, hlen7 b,
      hlen6 b, hlen5 b, hlen4 b, hlen3 b, hlen2 b, hB_arrs]
  have hw9 : σ9.arrs "cp.w" = σ6.arrs "cp.w" := by
    rw [hfaB "cp.w" (by decide), h9p_arrs,
      hfaR "cp.w" (by decide) (by decide) (by decide) (by decide)
        (Ne.symm (lv_ne_lit (by decide) (by decide) (j + 1)))
        (Ne.symm (lv_ne_lit (by decide) (by decide) (j + 1))),
      h8p_arrs, harr7 "cp.w" (by decide)]
  have hb9 : σ9.arrs "cp.b" = σ5.arrs "cp.b" := by
    rw [hfaB "cp.b" (by decide), h9p_arrs,
      hfaR "cp.b" (by decide) (by decide) (by decide) (by decide)
        (Ne.symm (lv_ne_lit (by decide) (by decide) (j + 1)))
        (Ne.symm (lv_ne_lit (by decide) (by decide) (j + 1))),
      h8p_arrs, harr7 "cp.b" (by decide), harr6 "cp.b" (by decide)]
  have hDeq : (fun v : Fin APc.N => (σ9.arrs "cp.d").getD (v : ℕ) 0)
      = ballDist APc.G (t0 : Fin APc.N) (2 * S.R) :=
    ballTable_eq_ballDist hBT9 hdle9
  have hwcells9 : ∀ p : Fin S.width, (σ9.arrs "cp.w").getD (p : ℕ) 0
      = ((batchFn S A π u p : Fin kk) : ℕ) := by
    intro p
    rw [hw9, hwc6 (p : ℕ) p.2]
    by_cases h : (p : ℕ) < (batchSet S A π u).ncard
    · rw [dif_pos h]
      have hbfn : batchFn S A π u p
          = (((setEquiv (batchSet S A π u)) ⟨(p : ℕ), h⟩ :
              ↥(batchSet S A π u)) : Fin kk) := by
        show pad (batchSet S A π u) (centreChild S A π u) p = _
        unfold pad
        rw [dif_pos h]
      rw [hbfn]
    · rw [dif_neg h]
      have hbfn : batchFn S A π u p = centreChild S A π u := by
        show pad (batchSet S A π u) (centreChild S A π u) p = _
        unfold pad
        rw [dif_neg h]
      rw [hbfn]
      exact hkct0.symm
  have hMid : PrepMid S ord ℓp htabF hbf j A u σ9 := by
    refine ⟨hAW9, hcpn9, hcpm9, fun v => congrFun hDeq v, hwcells9,
      fun t ht => by rw [hb9]; exact hbits5 t ht,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hlen90 "cp.b"]; exact hscr_b
    · rw [hlen90 "cp.d"]; exact hscr_d
    · rw [hlen90 "cp.p"]; exact hscr_p
    · rw [hlen90 "cp.x"]; exact hscr_x
    · rw [hlen90 "cp.v"]; exact hscr_v
    · rw [hlen90 "cp.w"]; exact hscr_w
    · intro i hi
      rw [hlen90 (lv "cq.d" i)]
      exact hscr_qd i hi
    · intro c hc
      rw [hlen90 (lv "cq.v" c)]
      exact hscr_qv c hc
    · intro c hc
      rw [hlen90 (lv "cq.u" c)]
      exact hscr_qu c hc
    · rw [hlen90 (arenaNames (j + 1)).off]
      exact hlvl_off
    · rw [hlen90 (arenaNames (j + 1)).tgt]
      exact hlvl_tgt
    · rw [hlen90 (arenaNames (j + 1)).col]
      exact hlvl_col
  obtain ⟨σF, hrT, hQF⟩ :=
    (prepTail_spec B S ord ℓp htabF hbf j A u hlpEq' hhbEq' hjlt hRhb
      h1B hn0nB hn02B hbig1 hRB hwB hlpjB hhbjB (hhistB j (by omega))
      hMw (hpalB j (by omega)) (hpalB (j + 1) hj1)) σ9 hMid
  obtain ⟨Dp, Dc, hPT, hAWF⟩ := hQF
  -- ### the whole pass, composed, and the postcondition
  have hrR8' : Run B (restrictCom (arenaNames j) (prepNmR j) "cp.l" "cp.r")
      σ8p σ8
      (restrictK (Impl.degSum A.G (cluster S A ((ord A.N A.G).order) u))
        (childN S A ((ord A.N A.G).order) u) (S.pal j) (ℓp j) (hbf j)) :=
    hrR8
  have hrB9' : Run B (bfsCom (prepNmR j).off (prepNmR j).tgt "cp.d") σ9p σ9
      (bfsK (childN S A ((ord A.N A.G).order) u)
        (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
          (preG S A ((ord A.N A.G).order) u).degree v) (2 * S.R)) := hrB9
  have hrAll := hrP1.seq (hrP2.seq (hrP3.seq (hrP4.seq (hrP5.seq
    (hrP6.seq (hrP7.seq ((hrK.seq (hrL.seq (hrPp.seq (hrH.seq
      hrR8')))).seq ((hrb1.seq (hrb2.seq (hrb3.seq (hrb4.seq
        hrB9')))).seq hrT))))))))
  have hrAll' : Run B (prepCom S ℓp hbf co cm j) σ0 σF _ := hrAll
  refine ⟨σF, hrAll'.mono ?_, ⟨Dp, Dc, hPT, hAWF⟩, ?_, ?_,
    fun b => run_arrs_length_eq hrAll' b⟩
  · -- the budget
    show _ ≤ prepK S ord ℓp hbf j A ((u : Fin A.N) : ℕ)
    rw [prepK_coe S ord ℓp hbf j A u]
    have e1 : childN S A ((ord A.N A.G).order) u = clu.ncard := rfl
    have e4 : kk = clu.ncard := hkclu
    have e5 : restrictK
        (Impl.degSum A.G (cluster S A ((ord A.N A.G).order) u))
        (childN S A ((ord A.N A.G).order) u) (S.pal j) (ℓp j) (hbf j)
        = restrictK (Impl.degSum (Impl.ofArena A (htabF j A)).G clu)
            clu.ncard (S.pal j) (ℓp j) (hbf j) := rfl
    have e6 : bfsK (childN S A ((ord A.N A.G).order) u)
        (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
          (preG S A ((ord A.N A.G).order) u).degree v) (2 * S.R)
        = bfsK APc.N (∑ v : Fin APc.N, APc.G.degree v) (2 * S.R) := rfl
    have m1 : (26 * hbf j + 26) * ℓp j ≤ (30 + 30 * (hbf j + 1)) * ℓp j :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · -- the scalar frame
    intro y hy
    simp only [levelScalars, List.mem_cons, List.not_mem_nil, or_false]
      at hy
    refine hrAll'.frame_var y ?_
    intro hmem
    rcases wvars_prepCom y hmem with h | h | h
    · rcases hy with rfl | rfl | rfl
      · exact lv_not_mem (by decide) (by decide) j h
      · exact lv_not_mem (by decide) (by decide) j h
      · exact lv_not_mem (by decide) (by decide) j h
    · rcases hy with rfl | rfl | rfl
      · exact lv_ne_of_base_ne (by decide) (by decide) j (j + 1) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_base_ne (by decide) (by decide) j (j + 1) h
    · rcases hy with rfl | rfl | rfl
      · exact lv_ne_of_base_ne (by decide) (by decide) j (j + 1) h
      · exact lv_ne_of_base_ne (by decide) (by decide) j (j + 1) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
  · -- the array frame
    intro a ha
    simp only [levelArrays, List.mem_cons, List.not_mem_nil, or_false]
      at ha
    refine hrAll'.frame_arr a ?_
    intro hmem
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rcases warrs_prepCom _ hmem with h | h | h | h | h | h | ⟨i, h⟩
        | ⟨i, h⟩ | ⟨i, h⟩
      · exact (hcovP j).1.1 h
      · exact absurd (show ca j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).1
      · exact absurd (show ca j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).1
      · exact absurd (show ca j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).1
      · exact absurd (show ca j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).1
      · exact absurd (show ca j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).1
      · exact ((hcovP j).2 i).1.1 h
      · exact ((hcovP j).2 i).1.2.1 h
      · exact ((hcovP j).2 i).1.2.2 h
    · rcases warrs_prepCom _ hmem with h | h | h | h | h | h | ⟨i, h⟩
        | ⟨i, h⟩ | ⟨i, h⟩
      · exact (hcovP j).1.2.1 h
      · exact absurd (show co j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).2.1
      · exact absurd (show co j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).2.1
      · exact absurd (show co j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).2.1
      · exact absurd (show co j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).2.1
      · exact absurd (show co j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).2.1
      · exact ((hcovP j).2 i).2.1.1 h
      · exact ((hcovP j).2 i).2.1.2.1 h
      · exact ((hcovP j).2 i).2.1.2.2 h
    · rcases warrs_prepCom _ hmem with h | h | h | h | h | h | ⟨i, h⟩
        | ⟨i, h⟩ | ⟨i, h⟩
      · exact (hcovP j).1.2.2 h
      · exact absurd (show cm j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).2.2
      · exact absurd (show cm j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).2.2
      · exact absurd (show cm j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).2.2
      · exact absurd (show cm j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).2.2
      · exact absurd (show cm j ∈ levelArrays (j + 1) by
          rw [h]; simp [levelArrays]) (hcovA j (j + 1)).2.2
      · exact ((hcovP j).2 i).2.2.1 h
      · exact ((hcovP j).2 i).2.2.2.1 h
      · exact ((hcovP j).2 i).2.2.2.2 h
    · rcases warrs_prepCom _ hmem with h | h | h | h | h | h | ⟨i, h⟩
        | ⟨i, h⟩ | ⟨i, h⟩
      · exact lv_not_mem (by decide) (by decide) j h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
    · rcases warrs_prepCom _ hmem with h | h | h | h | h | h | ⟨i, h⟩
        | ⟨i, h⟩ | ⟨i, h⟩
      · exact lv_not_mem (by decide) (by decide) j h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
    · rcases warrs_prepCom _ hmem with h | h | h | h | h | h | ⟨i, h⟩
        | ⟨i, h⟩ | ⟨i, h⟩
      · exact lv_not_mem (by decide) (by decide) j h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
    · rcases warrs_prepCom _ hmem with h | h | h | h | h | h | ⟨i, h⟩
        | ⟨i, h⟩ | ⟨i, h⟩
      · exact lv_not_mem (by decide) (by decide) j h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
    · rcases warrs_prepCom _ hmem with h | h | h | h | h | h | ⟨i, h⟩
        | ⟨i, h⟩ | ⟨i, h⟩
      · exact lv_not_mem (by decide) (by decide) j h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
    · rcases warrs_prepCom _ hmem with h | h | h | h | h | h | ⟨i, h⟩
        | ⟨i, h⟩ | ⟨i, h⟩
      · exact lv_not_mem (by decide) (by decide) j h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_level_ne (by decide) (by omega) h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h
      · exact lv_ne_of_base_ne (by decide) (by decide) j i h

/-! ## §8 The headline and the admissible channel seam -/
open Classical in
/-- The complete pass at every admissible encoded input, with the verbatim
`ChildLoadPartsAll` conclusion. -/
theorem childLoadPartsAll_of (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String)
    -- the constant-`ℓp` discipline (F7 owns both parameters)
    (hlpEq : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → ℓp (j + 1) = ℓp j)
    (hhbEq : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → hbf (j + 1) = hbf j)
    (hlpRoom : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → j < ℓp j)
    (hhbR : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → 2 * (Headline.headlineSetup C hC φ).R + 1 ≤ hbf j)
    -- the admissible history shape and the channel-pinning seam
    (hAdmLen : ∀ j (A : Arena ((Headline.headlineSetup C hC φ).pal j) n), Adm j A → A.hist.length = j)
    (hpin : ∀ j (A : Arena ((Headline.headlineSetup C hC φ).pal j) n), Adm j A →
      ∀ (v : Fin A.N) (e : Fin (ℓp j)) (he : (e : ℕ) < A.hist.length)
        (z : Fin A.N),
        z ∈ htabF j A v e ↔ (A.up z) ∈ Lax3Proofs.SplitterWin.pathSet
          (A.hist.reverse[(e : ℕ)]'(by simpa using he)).2 (2 * (Headline.headlineSetup C hC φ).R)
          (A.hist.reverse[(e : ℕ)]'(by simpa using he)).1 (A.up v))
    (hpinE : ∀ j (A : Arena ((Headline.headlineSetup C hC φ).pal j) n), Adm j A →
      ∀ (v : Fin A.N) (e : Fin (ℓp j)), A.hist.length ≤ (e : ℕ) →
        htabF j A v e = [])
    -- the batch fits the width
    (hwidth : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → 1 + j * (2 * (Headline.headlineSetup C hC φ).R + 1) ≤ (Headline.headlineSetup C hC φ).width)
    (hq : 1 ≤ q)
    (hB : ∀ x ∈ mcD n G c w,
      n < mcB q x ∧ n * n < mcB q x ∧ n + 2 < mcB q x ∧
      n * n + 2 * n + 1 < mcB q x ∧
      (Headline.headlineSetup C hC φ).depth < mcB q x ∧
      2 * (Headline.headlineSetup C hC φ).R + 3 < mcB q x ∧
      (Headline.headlineSetup C hC φ).width < mcB q x)
    (hlpB : ∀ x ∈ mcD n G c w, ∀ j ≤ (Headline.headlineSetup C hC φ).depth,
      ℓp j < mcB q x)
    (hhbB : ∀ x ∈ mcD n G c w, ∀ j ≤ (Headline.headlineSetup C hC φ).depth,
      hbf j + 1 < mcB q x)
    (hhistB : ∀ x ∈ mcD n G c w, ∀ j ≤ (Headline.headlineSetup C hC φ).depth,
      n * ℓp j * (hbf j + 1) < mcB q x)
    (hpalB : ∀ x ∈ mcD n G c w, ∀ j ≤ (Headline.headlineSetup C hC φ).depth,
      n * (Headline.headlineSetup C hC φ).pal j < mcB q x)
    -- the scratch descriptor's length clauses
    (hscrA : ∀ j' σ, Scr j' σ →
      n ≤ (σ.arrs "cp.l").length ∧ n ≤ (σ.arrs "cp.r").length ∧
      n ≤ (σ.arrs "cp.b").length ∧ n ≤ (σ.arrs "cp.d").length ∧
      n ≤ (σ.arrs "cp.p").length ∧ n ≤ (σ.arrs "cp.x").length ∧
      n + 2 ≤ (σ.arrs "cp.v").length ∧
      (σ.arrs "cp.w").length = (Headline.headlineSetup C hC φ).width ∧
      n + 1 ≤ (σ.arrs "cp.o").length ∧
      n * n ≤ (σ.arrs "cp.t").length ∧
      n * (Headline.headlineSetup C hC φ).pal j' ≤ (σ.arrs "cp.c").length ∧
      (∀ i, i < (Headline.headlineSetup C hC φ).width → n ≤ (σ.arrs (lv "cq.d" i)).length) ∧
      (∀ c, c < (Headline.headlineSetup C hC φ).pal j' →
        n * n + 2 * n ≤ (σ.arrs (lv "cq.v" c)).length) ∧
      (∀ c, c < (Headline.headlineSetup C hC φ).pal j' + 1 → n + 1 ≤ (σ.arrs (lv "cq.u" c)).length))
    (hscrLvl : ∀ j', j' + 1 ≤ (Headline.headlineSetup C hC φ).depth → ∀ σ, Scr j' σ →
      n + 1 ≤ (σ.arrs (arenaNames (j' + 1)).off).length ∧
      n * n ≤ (σ.arrs (arenaNames (j' + 1)).tgt).length ∧
      n * (Headline.headlineSetup C hC φ).pal (j' + 1) ≤ (σ.arrs (arenaNames (j' + 1)).col).length ∧
      n ≤ (σ.arrs (arenaNames (j' + 1)).up).length ∧
      n * ℓp j' * (hbf j' + 1)
        ≤ (σ.arrs (arenaNames (j' + 1)).hist).length)
    -- cover-name freshness
    (hcovA : ∀ jc j', ca jc ∉ levelArrays j' ∧ co jc ∉ levelArrays j' ∧
      cm jc ∉ levelArrays j')
    (hcovP : ∀ jc, (ca jc ∉ prepArrays ∧ co jc ∉ prepArrays ∧
        cm jc ∉ prepArrays) ∧
      ∀ i, (ca jc ≠ lv "cq.d" i ∧ ca jc ≠ lv "cq.v" i ∧
          ca jc ≠ lv "cq.u" i) ∧
        (co jc ≠ lv "cq.d" i ∧ co jc ≠ lv "cq.v" i ∧
          co jc ≠ lv "cq.u" i) ∧
        (cm jc ≠ lv "cq.d" i ∧ cm jc ≠ lv "cq.v" i ∧
          cm jc ≠ lv "cq.u" i))
 :
    ChildLoadPartsAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm
      (prepCom (Headline.headlineSetup C hC φ) ℓp hbf co cm)
      (prepChan (Headline.headlineSetup C hC φ) ord ℓp htabF)
      (fun _ j A u => prepK (Headline.headlineSetup C hC φ) ord ℓp hbf j A u) := by
  intro x hx
  obtain ⟨hnB, hnnB, hn2B, hbigB, hdB, hRB, hwB⟩ := hB x hx
  exact childLoadParts_of (mcB q x) (Headline.headlineSetup C hC φ)
    ord ℓp htabF hbf Adm Scr ca co cm
    hlpEq hhbEq hlpRoom hhbR hAdmLen hpin hpinE hwidth
    (one_lt_mcB (three_le_length hx.1) hq)
    hnB hnnB hn2B hbigB hdB hRB hwB
    (hlpB x hx) (hhbB x hx) (hhistB x hx) (hpalB x hx)
    hscrA hscrLvl hcovA hcovP

open Classical in
/-- The channel seam is needed only at an admissible arena on a run level.
This permits the canonical transport to use the reached arena's monotone
root renaming while keeping the exact `ChildLoadAll` conclusion. -/
theorem childLoadAll_of_parts_adm (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (chanF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      (u : Fin A.N) →
      Fin (childN (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u) →
      Fin (ℓp (j + 1)) →
      List (Fin (childN (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u)))
    (KP : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ)
    (hhtab : ∀ (j : ℕ), j + 1 ≤ (Headline.headlineSetup C hC φ).depth →
      ∀ (A : Arena ((Headline.headlineSetup C hC φ).pal j) n), Adm j A →
      ∀ u : Fin A.N,
      htabF (j + 1) (childArena (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u) = chanF j A u)
    (hparts : ChildLoadPartsAll C hC φ ord G c w q ℓp htabF hbf Adm Scr
      ca co cm prepC chanF KP) :
    ChildLoadAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm prepC
      KP := by
  intro x hx k j A hdiag hAdm hbot u
  refine ((hparts x hx) k j A hdiag hAdm hbot u).post ?_
  rintro σ σ' _ ⟨⟨Dp, Dc, hPT, hAW⟩, hframe⟩
  refine ⟨?_, hframe⟩
  rw [hhtab j (by omega) A hAdm u,
    ← machChild_eq_ofArena (Headline.headlineSetup C hC φ) A
      ((ord A.N A.G).order) u (chanF j A u) hPT]
  exact hAW

open Classical in
/-- Compile-time consumer fit for the actual program and honest budget. -/
example (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String)
    -- the constant-`ℓp` discipline (F7 owns both parameters)
    (hlpEq : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → ℓp (j + 1) = ℓp j)
    (hhbEq : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → hbf (j + 1) = hbf j)
    (hlpRoom : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → j < ℓp j)
    (hhbR : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → 2 * (Headline.headlineSetup C hC φ).R + 1 ≤ hbf j)
    -- the admissible history shape and the channel-pinning seam
    (hAdmLen : ∀ j (A : Arena ((Headline.headlineSetup C hC φ).pal j) n), Adm j A → A.hist.length = j)
    (hpin : ∀ j (A : Arena ((Headline.headlineSetup C hC φ).pal j) n), Adm j A →
      ∀ (v : Fin A.N) (e : Fin (ℓp j)) (he : (e : ℕ) < A.hist.length)
        (z : Fin A.N),
        z ∈ htabF j A v e ↔ (A.up z) ∈ Lax3Proofs.SplitterWin.pathSet
          (A.hist.reverse[(e : ℕ)]'(by simpa using he)).2 (2 * (Headline.headlineSetup C hC φ).R)
          (A.hist.reverse[(e : ℕ)]'(by simpa using he)).1 (A.up v))
    (hpinE : ∀ j (A : Arena ((Headline.headlineSetup C hC φ).pal j) n), Adm j A →
      ∀ (v : Fin A.N) (e : Fin (ℓp j)), A.hist.length ≤ (e : ℕ) →
        htabF j A v e = [])
    -- the batch fits the width
    (hwidth : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → 1 + j * (2 * (Headline.headlineSetup C hC φ).R + 1) ≤ (Headline.headlineSetup C hC φ).width)
    (hq : 1 ≤ q)
    (hB : ∀ x ∈ mcD n G c w,
      n < mcB q x ∧ n * n < mcB q x ∧ n + 2 < mcB q x ∧
      n * n + 2 * n + 1 < mcB q x ∧
      (Headline.headlineSetup C hC φ).depth < mcB q x ∧
      2 * (Headline.headlineSetup C hC φ).R + 3 < mcB q x ∧
      (Headline.headlineSetup C hC φ).width < mcB q x)
    (hlpB : ∀ x ∈ mcD n G c w, ∀ j ≤ (Headline.headlineSetup C hC φ).depth,
      ℓp j < mcB q x)
    (hhbB : ∀ x ∈ mcD n G c w, ∀ j ≤ (Headline.headlineSetup C hC φ).depth,
      hbf j + 1 < mcB q x)
    (hhistB : ∀ x ∈ mcD n G c w, ∀ j ≤ (Headline.headlineSetup C hC φ).depth,
      n * ℓp j * (hbf j + 1) < mcB q x)
    (hpalB : ∀ x ∈ mcD n G c w, ∀ j ≤ (Headline.headlineSetup C hC φ).depth,
      n * (Headline.headlineSetup C hC φ).pal j < mcB q x)
    -- the scratch descriptor's length clauses
    (hscrA : ∀ j' σ, Scr j' σ →
      n ≤ (σ.arrs "cp.l").length ∧ n ≤ (σ.arrs "cp.r").length ∧
      n ≤ (σ.arrs "cp.b").length ∧ n ≤ (σ.arrs "cp.d").length ∧
      n ≤ (σ.arrs "cp.p").length ∧ n ≤ (σ.arrs "cp.x").length ∧
      n + 2 ≤ (σ.arrs "cp.v").length ∧
      (σ.arrs "cp.w").length = (Headline.headlineSetup C hC φ).width ∧
      n + 1 ≤ (σ.arrs "cp.o").length ∧
      n * n ≤ (σ.arrs "cp.t").length ∧
      n * (Headline.headlineSetup C hC φ).pal j' ≤ (σ.arrs "cp.c").length ∧
      (∀ i, i < (Headline.headlineSetup C hC φ).width → n ≤ (σ.arrs (lv "cq.d" i)).length) ∧
      (∀ c, c < (Headline.headlineSetup C hC φ).pal j' →
        n * n + 2 * n ≤ (σ.arrs (lv "cq.v" c)).length) ∧
      (∀ c, c < (Headline.headlineSetup C hC φ).pal j' + 1 → n + 1 ≤ (σ.arrs (lv "cq.u" c)).length))
    (hscrLvl : ∀ j', j' + 1 ≤ (Headline.headlineSetup C hC φ).depth → ∀ σ, Scr j' σ →
      n + 1 ≤ (σ.arrs (arenaNames (j' + 1)).off).length ∧
      n * n ≤ (σ.arrs (arenaNames (j' + 1)).tgt).length ∧
      n * (Headline.headlineSetup C hC φ).pal (j' + 1) ≤ (σ.arrs (arenaNames (j' + 1)).col).length ∧
      n ≤ (σ.arrs (arenaNames (j' + 1)).up).length ∧
      n * ℓp j' * (hbf j' + 1)
        ≤ (σ.arrs (arenaNames (j' + 1)).hist).length)
    -- cover-name freshness
    (hcovA : ∀ jc j', ca jc ∉ levelArrays j' ∧ co jc ∉ levelArrays j' ∧
      cm jc ∉ levelArrays j')
    (hcovP : ∀ jc, (ca jc ∉ prepArrays ∧ co jc ∉ prepArrays ∧
        cm jc ∉ prepArrays) ∧
      ∀ i, (ca jc ≠ lv "cq.d" i ∧ ca jc ≠ lv "cq.v" i ∧
          ca jc ≠ lv "cq.u" i) ∧
        (co jc ≠ lv "cq.d" i ∧ co jc ≠ lv "cq.v" i ∧
          co jc ≠ lv "cq.u" i) ∧
        (cm jc ≠ lv "cq.d" i ∧ cm jc ≠ lv "cq.v" i ∧
          cm jc ≠ lv "cq.u" i))

    (hhtab : ∀ (j : ℕ), j + 1 ≤ (Headline.headlineSetup C hC φ).depth →
      ∀ (A : Arena ((Headline.headlineSetup C hC φ).pal j) n), Adm j A →
      ∀ u : Fin A.N,
      htabF (j + 1)
        (childArena (Headline.headlineSetup C hC φ) A ((ord A.N A.G).order) u)
        = prepChan (Headline.headlineSetup C hC φ) ord ℓp htabF j A u) :
    ChildLoadAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm
      (prepCom (Headline.headlineSetup C hC φ) ℓp hbf co cm)
      (fun _ j A u => prepK (Headline.headlineSetup C hC φ) ord ℓp hbf j A u) :=
  childLoadAll_of_parts_adm C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm
    (prepCom (Headline.headlineSetup C hC φ) ℓp hbf co cm)
    (prepChan (Headline.headlineSetup C hC φ) ord ℓp htabF)
    (fun _ j A u => prepK (Headline.headlineSetup C hC φ) ord ℓp hbf j A u) hhtab
    (childLoadPartsAll_of C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm
      hlpEq hhbEq hlpRoom hhbR hAdmLen hpin hpinE hwidth
      hq hB hlpB hhbB hhistB hpalB hscrA hscrLvl hcovA hcovP)


end Lax3Proofs.Prog
