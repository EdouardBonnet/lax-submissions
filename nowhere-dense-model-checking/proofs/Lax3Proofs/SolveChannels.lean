import Lax3Proofs.SolveMachPrepRun

/-! Canonical history columns and the admissibility invariant used by the
recursive machine. New columns are gradient paths in the recorded pre-graph;
old columns are filtered through the child embedding in their original order. -/

set_option autoImplicit false

namespace Lax3Proofs.Prog
open Classical
open Lax3Proofs.Driver
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences
open Lax12.GraphClasses Lax12.NowhereDenseClasses

/-- The unique local name of a root vertex, when it has one. -/
noncomputable def channelLocal {α β : Type*} (f : α ↪ β) (z : β) : Option α :=
  if h : ∃ a, f a = z then some h.choose else none

@[simp] theorem channelLocal_eq_some {α β : Type*} (f : α ↪ β) (z : β) (a : α) :
    channelLocal f z = some a ↔ f a = z := by
  unfold channelLocal
  split_ifs with h
  · constructor
    · intro he
      have ha := Option.some.inj he
      exact ha ▸ h.choose_spec
    · intro ha
      exact congrArg some (f.injective (h.choose_spec.trans ha.symm))
  · simp only [false_iff]
    exact fun ha => h ⟨a, ha⟩

@[simp] theorem channelLocal_apply {α β : Type*} (f : α ↪ β) (a : α) :
    channelLocal f (f a) = some a := (channelLocal_eq_some f (f a) a).mpr rfl

/-- Pulling back an embedded list preserves its exact order. -/
theorem channelLocal_map {α β : Type*} (f : α ↪ β) (l : List α) :
    (l.map f).filterMap (channelLocal f) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem channelLocal_mem {α β : Type*} (f : α ↪ β) (l : List β) (a : α) :
    a ∈ l.filterMap (channelLocal f) ↔ f a ∈ l := by
  simp only [List.mem_filterMap, channelLocal_eq_some]
  constructor
  · rintro ⟨b, hb, he⟩
    exact he ▸ hb
  · intro ha
    exact ⟨f a, ha, rfl⟩

theorem channelLocal_comp {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (z : γ) :
    channelLocal (f.trans g) z = (channelLocal g z).bind (channelLocal f) := by
  apply Option.ext
  intro a
  simp only [channelLocal_eq_some, Option.bind_eq_some_iff]
  constructor
  · intro h
    exact ⟨f a, h, rfl⟩
  · rintro ⟨b, hb, ha⟩
    exact (congrArg g ha).trans hb

theorem channelLocal_restrict {N : ℕ} (X : Set (Fin N)) :
    channelLocal (Impl.restrictEmb X) = Impl.toLocal X := by
  funext x
  by_cases hx : x ∈ X
  · rw [Impl.toLocal, dif_pos hx]
    apply (channelLocal_eq_some _ _ _).mpr
    simp [Impl.restrictEmb]
  · apply Option.ext
    intro a
    rw [Impl.toLocal_eq_none X hx, channelLocal_eq_some]
    constructor
    · intro ha
      exact False.elim (hx (ha ▸ Impl.restrictEmb_mem X a))
    · intro ha
      cases ha

variable {L n₀ : ℕ}

/-- Canonical oldest-first history columns at the current local names. -/
noncomputable def canonicalChannels (S : Setup L) (ℓp : ℕ → ℕ)
    (j : ℕ) (A : Arena (S.pal j) n₀) (v : Fin A.N)
    (e : Fin (ℓp j)) : List (Fin A.N) :=
  if he : (e : ℕ) < A.hist.length then
    let er := A.hist.reverse[(e : ℕ)]'(by simpa using he)
    (Lax3Proofs.BatchCanon.pathList er.2 (2 * S.R) er.1 (A.up v)).filterMap
      (channelLocal A.up)
  else []

@[simp] theorem canonicalChannels_empty (S : Setup L) (ℓp : ℕ → ℕ)
    (j : ℕ) (A : Arena (S.pal j) n₀) (v : Fin A.N)
    (e : Fin (ℓp j)) (he : A.hist.length ≤ (e : ℕ)) :
    canonicalChannels S ℓp j A v e = [] := by
  simp [canonicalChannels, Nat.not_lt.mpr he]

theorem canonicalChannels_pin (S : Setup L) (ℓp : ℕ → ℕ)
    (j : ℕ) (A : Arena (S.pal j) n₀) (v : Fin A.N)
    (e : Fin (ℓp j)) (he : (e : ℕ) < A.hist.length) (z : Fin A.N) :
    z ∈ canonicalChannels S ℓp j A v e ↔ A.up z ∈
      Lax3Proofs.SplitterWin.pathSet
        (A.hist.reverse[(e : ℕ)]'(by simpa using he)).2 (2 * S.R)
        (A.hist.reverse[(e : ℕ)]'(by simpa using he)).1 (A.up v) := by
  rw [canonicalChannels, dif_pos he, channelLocal_mem]
  rfl

theorem canonicalChannels_child (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ) (j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N)
    (hlp : ℓp (j + 1) = ℓp j) (hhist : A.hist.length = j)
    (hmono : StrictMono A.up) :
    canonicalChannels S ℓp (j + 1) (childArena S A (ord A.N A.G).order u) =
      prepChan S ord ℓp (canonicalChannels S ℓp) j A u := by
  let π := (ord A.N A.G).order
  let child := childArena S A π u
  have hhc : child.hist.length = j + 1 := by simp [child, hhist]
  have hloc : channelLocal child.up = fun z =>
      (channelLocal A.up z).bind (Impl.toLocal (cluster S A π u)) := by
    funext z
    change channelLocal ((Impl.restrictEmb (cluster S A π u)).trans A.up) z = _
    rw [channelLocal_comp, channelLocal_restrict]
  funext v e
  change canonicalChannels S ℓp (j + 1) child v e = _
  by_cases he : (e : ℕ) = j
  · have hec : (e : ℕ) < child.hist.length := by omega
    have hnew : child.hist.reverse[(e : ℕ)]'(by simpa using hec) =
        (A.up u, histGraph S A π u) := by
      simp only [child, childArena_hist, List.reverse_cons]
      rw [List.getElem_append_right (by simp [hhist, he])]
      simp [hhist, he]
    have hcentre : child.up (centreChild S A π u) = A.up u := by
      change A.up ((childEquiv S A π u) ((childEquiv S A π u).symm
        ⟨u, self_mem_cluster S A π u⟩) : Fin A.N) = A.up u
      rw [Equiv.apply_symm_apply]
    have hmap : histGraph S A π u = (preG S A π u).map child.up :=
      histGraph_eq_map S A π u
    rw [canonicalChannels, dif_pos hec, hnew]
    simp only
    rw [prepChan, if_pos he, prepDescendCol_eq_pathList]
    change (Lax3Proofs.BatchCanon.pathList (histGraph S A π u) (2 * S.R)
      (A.up u) (child.up v)).filterMap (channelLocal child.up) = _
    rw [hmap, ← hcentre,
      Lax3Proofs.BatchCanon.pathList_map child.up
        (childArena_up_strictMono S A π u hmono), channelLocal_map]
    rfl
  · have hep : (e : ℕ) < ℓp j := by rw [← hlp]; exact e.isLt
    rw [prepChan, if_neg he, dif_pos hep]
    by_cases heold : (e : ℕ) < j
    · have hec : (e : ℕ) < child.hist.length := by omega
      have hea : (e : ℕ) < A.hist.length := by omega
      have hold : child.hist.reverse[(e : ℕ)]'(by simpa using hec) =
          A.hist.reverse[(e : ℕ)]'(by simpa using hea) := by
        simp only [child, childArena_hist, List.reverse_cons]
        exact List.getElem_append_left (by simpa using hea)
      rw [canonicalChannels, dif_pos hec, hold,
        canonicalChannels, dif_pos hea, List.filterMap_filterMap, hloc]
      rfl
    · have hec : child.hist.length ≤ (e : ℕ) := by omega
      rw [canonicalChannels_empty S ℓp (j + 1) child v e hec]
      rw [canonicalChannels_empty S ℓp j A _ _ (by change A.hist.length ≤ (e : ℕ); omega)]
      rfl

theorem canonicalChannels_length_le (S : Setup L) (ℓp : ℕ → ℕ)
    (j : ℕ) (A : Arena (S.pal j) n₀) (v : Fin A.N) (e : Fin (ℓp j)) :
    (canonicalChannels S ℓp j A v e).length ≤ 2 * S.R + 1 := by
  unfold canonicalChannels
  split_ifs
  · exact (List.length_filterMap_le _ _).trans
      (Lax3Proofs.BatchCanon.pathList_length_le _ _ _ _)
  · simp

@[simp] theorem canonicalChannels_root (S : Setup L) (ℓp : ℕ → ℕ)
    (G : SimpleGraph (Fin n₀)) (col : Coloring n₀ L)
    (v : Fin n₀) (e : Fin (ℓp 0)) :
    canonicalChannels S ℓp 0 (rootArena G col) v e = [] := by
  simp [canonicalChannels, rootArena]

/-- The history shape and local ordering hold at all levels; the game
invariant is needed only through the finite recursion depth. -/
def canonicalAdm (S : Setup L) (G₀ : SimpleGraph (Fin n₀))
    (j : ℕ) (A : Arena (S.pal j) n₀) : Prop :=
  A.hist.length = j ∧ StrictMono A.up ∧ (j ≤ S.depth → Inv S G₀ j A)

theorem canonicalAdm_root (S : Setup L) (G : SimpleGraph (Fin n₀))
    (col : Coloring n₀ L) : canonicalAdm S G 0 (rootArena G col) :=
  ⟨rfl, rootArena_up_strictMono G col, fun _ => inv_root S G col⟩

theorem canonicalAdm_child (S : Setup L) (G₀ : SimpleGraph (Fin n₀))
    (hwidth : ∀ j < S.depth, 1 + j * (2 * S.R + 1) ≤ S.width)
    {j : ℕ} {A : Arena (S.pal j) n₀} (h : canonicalAdm S G₀ j A)
    (hbot : A.G ≠ ⊥) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    canonicalAdm S G₀ (j + 1) (childArena S A π u) := by
  refine ⟨by simp [h.1], childArena_up_strictMono S A π u h.2.1, ?_⟩
  intro hj
  exact inv_child S π u (h.2.2 (by omega)) hbot (hwidth j (by omega))

theorem canonicalAdm_mkSetup_child (C : GraphClass) (hC : NowhereDense C)
    {q : ℕ} (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)
    (G₀ : SimpleGraph (Fin n₀)) {j : ℕ}
    {A : Arena ((mkSetup C hC φ hφ choice).pal j) n₀}
    (h : canonicalAdm (mkSetup C hC φ hφ choice) G₀ j A)
    (hbot : A.G ≠ ⊥) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    canonicalAdm (mkSetup C hC φ hφ choice) G₀ (j + 1)
      (childArena (mkSetup C hC φ hφ choice) A π u) :=
  canonicalAdm_child _ G₀ (fun _ hj => mkSetup_width_le C hC φ hφ choice hj)
    h hbot π u

theorem canonicalAdm_mkSetup_eq_bot (C : GraphClass) (hC : NowhereDense C)
    {q : ℕ} (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)
    {G₀ : SimpleGraph (Fin n₀)} (hG₀ : C n₀ G₀) {j : ℕ}
    {A : Arena ((mkSetup C hC φ hφ choice).pal j) n₀}
    (h : canonicalAdm (mkSetup C hC φ hφ choice) G₀ j A)
    (hj : j = (mkSetup C hC φ hφ choice).depth) : A.G = ⊥ := by
  exact mkSetup_eq_bot_of_inv_depth C hC φ hφ choice hG₀
    (hj ▸ h.2.2 (by omega))

theorem canonicalAdm_mkSetup_leafChild (C : GraphClass) (hC : NowhereDense C)
    {q : ℕ} (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)
    {G₀ : SimpleGraph (Fin n₀)} (hG₀ : C n₀ G₀) {j : ℕ}
    {A : Arena ((mkSetup C hC φ hφ choice).pal j) n₀}
    (h : canonicalAdm (mkSetup C hC φ hφ choice) G₀ j A)
    (hbot : A.G ≠ ⊥) (hj : j + 1 = (mkSetup C hC φ hφ choice).depth)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    (childArena (mkSetup C hC φ hφ choice) A π u).G = ⊥ :=
  canonicalAdm_mkSetup_eq_bot C hC φ hφ choice hG₀
    (canonicalAdm_mkSetup_child C hC φ hφ choice G₀ h hbot π u) hj

/-- PREP's child-channel equality under the same admissibility contract
that supplies the recursive leaf guard. -/
theorem canonicalChannels_child_of_adm (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (G₀ : SimpleGraph (Fin n₀)) (j : ℕ) (A : Arena (S.pal j) n₀)
    (h : canonicalAdm S G₀ j A) (u : Fin A.N)
    (hlp : ℓp (j + 1) = ℓp j) :
    canonicalChannels S ℓp (j + 1) (childArena S A (ord A.N A.G).order u) =
      prepChan S ord ℓp (canonicalChannels S ℓp) j A u :=
  canonicalChannels_child S ord ℓp j A u hlp h.1 h.2.1

end Lax3Proofs.Prog
