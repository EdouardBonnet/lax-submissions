import Lax3.NeighborhoodCoverBound
import Lax3Proofs.Augmentation

/-!
The two halves of the cover-computation phase of Grohe–Kreutzer–Siebertz
§6, each stated for data the program produces rather than for an
optimal ordering.

# The cover of an arbitrary ordering

The claim `Lax3.NeighborhoodCoverBound.isNeighborhoodCover_wreach`
supplies the cover of any ordering, with its full proof in
`CoverConstruction`. The existential cover theorem applies it to an
ordering attaining the weak coloring number; this module applies it
to the ordering the program computes. Given any ordering `π` whose weak
`2r`-reachability sets have at most `k` elements, the fibers
`X u = {w | u ∈ wreach G π (2r) w}` form an `r`-neighborhood cover of
radius `2r` and degree `k`. The local `isNeighborhoodCover_wreach`
forwards to that concept claim, so the algorithm and the existential
cover theorem share the same proved construction.

# The ordering of an augmentation chain

The second half is the engine of their Theorem 6.2, their Lemmas 6.5
and 6.6: after enough rounds of tight transitive–fraternal
augmentation, a degeneracy ordering of the final orientation has all
weak reachability sets small.

Write `Arrow D u v` for "`u` is `v` or an in-neighbour of `v`" and call
`c` a *meet* of `a` and `b` when `Arrow D c a` and `Arrow D c b`: one
vertex fanning out to both ends.  The path lemma is

    a `G`-walk of length at most `2 ^ t` has a meet in `D (3 * t)`
    on its own support                            (`meet_of_walk`)

and it is proved by halving the walk.  Split a walk of length `2 ^ (t+1)`
in the middle; the two halves have meets `c₁`, `c₂` of `(a, mid)` and
`(mid, b)` after `3 * t` rounds.  Both `c₁` and `c₂` arrow into `mid`,
so one fraternal round links them; the winner arrows into one of the two
far ends, so one transitive round carries it across; and if that arc
comes out pointing the wrong way, a second transitive round links `a`
and `b` themselves, whereupon the meet is an endpoint.  Three rounds per
doubling — the augmentation "halves" a walk, and the two `Arrow`
lemmas `arrow_or_of_frat` and `arrow_or_of_trans`, which return an
undirected verdict because the process does not fix the direction of a
new arc, are the only facts about a round the induction uses.

The counting is then `wreach_ncard_le_of_augChain`.  If `u` is weakly
`r`-reachable from `v` along a walk `p`, take a meet `c ∈ p.support` in
the final orientation `D R`.  Then `c` is `v` or one of its at most `d`
in-neighbours; and `c` is `u` or `u` is a `D R`-neighbour of `c` lying
`π`-below `c`, because `u` is `π`-minimal on `p` and `c` lies on `p`.
Bounding the second choice is exactly a back-degree bound on the
underlying graph of `D R` under `π` — a degeneracy ordering — so the
count is `(d + 1) * (k + 1)`, the shape of their `2 (d + 1) ²`.

# What the program supplies

The greedy chain of `Augmentation` (its own degeneracy orientation of
`G`, then per-round greedy orientations of the fraternity graphs), the
in-degree bound `d` of its final round, and the vertex order produced by
one last bucket-queue degeneracy pass over the underlying graph of that
final round, as a permutation, together with its back-degree bound `k`.
`lowDegreeVertices_toGraph` is the reason such a `k` exists and is small:
an orientation of in-degree `d` has at most `d · |S|` edges inside every
`S`, so some vertex of `S` has degree at most `2 d` inside it, and greedy
elimination turns that into an ordering.  `isNeighborhoodCover_of_augChain`
is the one-line composition of the two halves, with `2 ^ t ≥ 2 · r` rounds
of slack for the cover radius.
-/

namespace Lax3Proofs.OrderedCovers

open Lax3.ColoredGraphs
open Lax3.NeighborhoodCovers
open Lax12.ColoringNumbers
open Lax3Proofs.WalkDistance
open Lax3Proofs.CoverConstruction
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation

variable {n : ℕ}

/-! ### The cover of an arbitrary ordering -/

/-- **The cover of an ordering** (Lemma 6.9 of Grohe–Kreutzer–Siebertz,
the parametric core of their Theorem 6.2).  For *any* ordering `π` whose
weak `2r`-reachability sets have at most `k` elements, the fibers of weak
`2r`-reachability form an `r`-neighborhood cover of radius `2r` and
degree `k`.

This consumes `Lax3.NeighborhoodCoverBound.isNeighborhoodCover_wreach`;
the full construction is proved in `Lax3Proofs.CoverConstruction`. -/
theorem isNeighborhoodCover_wreach (G : SimpleGraph (Fin n)) (r k : ℕ)
    (π : Equiv.Perm (Fin n)) (hk : ∀ v, (wreach G π (2 * r) v).ncard ≤ k) :
    IsNeighborhoodCover G r (fun u => {w | u ∈ wreach G π (2 * r) w}) k :=
  Lax3.NeighborhoodCoverBound.isNeighborhoodCover_wreach G r k π hk

/-! ### Arrows and meets -/

/-- `u` is `v` itself or an in-neighbour of `v`.  A vertex `c` with
`Arrow D c a` and `Arrow D c b` is a *meet* of `a` and `b`: the
configuration the augmentation process manufactures along a walk. -/
def Arrow (D : Orientation n) (u v : Fin n) : Prop := u = v ∨ u ∈ D.inN v

theorem arrow_refl (D : Orientation n) (u : Fin n) : Arrow D u u := Or.inl rfl

theorem arrow_of_mem_inN {D : Orientation n} {u v : Fin n} (h : u ∈ D.inN v) :
    Arrow D u v := Or.inr h

variable {G : SimpleGraph (Fin n)} {D : ℕ → Orientation n} {R : ℕ}

/-- Arcs survive along an augmentation chain. -/
theorem arc_mono (hchain : IsAugChain G D R) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ R)
    {u v : Fin n} (h : u ∈ (D i).inN v) : u ∈ (D j).inN v := by
  revert hj
  induction j, hij using Nat.le_induction with
  | base => exact fun _ => h
  | succ j hij ih => exact fun hj => (hchain.2 j (by omega)).mono _ _ (ih (by omega))

/-- Arrows survive along an augmentation chain. -/
theorem arrow_mono (hchain : IsAugChain G D R) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ R)
    {u v : Fin n} (h : Arrow (D i) u v) : Arrow (D j) u v :=
  h.imp id (arc_mono hchain hij hj)

/-- **The transitive round.**  Two arrows in a row become a single arrow,
in one of the two directions, after one augmentation step: if neither is
an equality the pair is transitively linked, and the round covers it. -/
theorem arrow_or_of_trans (hchain : IsAugChain G D R) {i : ℕ} (hi : i < R)
    {a c b : Fin n} (h₁ : Arrow (D i) a c) (h₂ : Arrow (D i) c b) :
    Arrow (D (i + 1)) a b ∨ Arrow (D (i + 1)) b a := by
  rcases h₁ with rfl | h₁
  · exact Or.inl (arrow_mono hchain (Nat.le_succ i) (by omega) h₂)
  rcases h₂ with rfl | h₂
  · exact Or.inl (arrow_mono hchain (Nat.le_succ i) (by omega) (Or.inr h₁))
  by_cases hab : a = b
  · subst hab; exact Or.inl (arrow_refl _ a)
  rcases (hchain.2 i hi).trans_cov a b hab ⟨_, h₁, h₂⟩ with h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

/-- **The fraternal round.**  Two arrows into a common target become a
single arrow, in one of the two directions, after one augmentation step:
if neither is an equality the pair is fraternally linked, and the round
covers it. -/
theorem arrow_or_of_frat (hchain : IsAugChain G D R) {i : ℕ} (hi : i < R)
    {a c b : Fin n} (h₁ : Arrow (D i) a c) (h₂ : Arrow (D i) b c) :
    Arrow (D (i + 1)) a b ∨ Arrow (D (i + 1)) b a := by
  rcases h₁ with rfl | h₁
  · exact Or.inr (arrow_mono hchain (Nat.le_succ i) (by omega) h₂)
  rcases h₂ with rfl | h₂
  · exact Or.inl (arrow_mono hchain (Nat.le_succ i) (by omega) (Or.inr h₁))
  by_cases hab : a = b
  · subst hab; exact Or.inl (arrow_refl _ a)
  rcases (hchain.2 i hi).frat_cov a b hab ⟨_, h₁, h₂⟩ with h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

/-- **Merging two meets.**  Three augmentation rounds join a meet of
`(a, m)` and a meet of `(m, b)` into a meet of `(a, b)`, and the new meet
vertex is one of the two old ones or an endpoint.

Both old meet vertices arrow into `m`, so one fraternal round links them;
say `c₁` now arrows into `c₂`.  Since `c₂` arrows into `b`, one
transitive round carries `c₁` across to `b` — unless the new arc points
backwards, `b` into `c₁`, in which case a further transitive round along
`b → c₁ → a` links the two endpoints, and whichever way *that* arc points
its tail is a meet of `a` and `b`. -/
theorem meet_merge (hchain : IsAugChain G D R) {i : ℕ} (hi : i + 3 ≤ R)
    {a m b c₁ c₂ : Fin n} (h₁a : Arrow (D i) c₁ a) (h₁m : Arrow (D i) c₁ m)
    (h₂m : Arrow (D i) c₂ m) (h₂b : Arrow (D i) c₂ b) :
    ∃ c, (c = c₁ ∨ c = c₂ ∨ c = a ∨ c = b) ∧
      Arrow (D (i + 3)) c a ∧ Arrow (D (i + 3)) c b := by
  have e2 : i + 1 + 1 = i + 2 := rfl
  have e3 : i + 2 + 1 = i + 3 := rfl
  rcases arrow_or_of_frat hchain (show i < R by omega) h₁m h₂m with h | h
  · have h₂b' : Arrow (D (i + 1)) c₂ b := arrow_mono hchain (by omega) (by omega) h₂b
    rcases e2 ▸ arrow_or_of_trans hchain (show i + 1 < R by omega) h h₂b' with h' | h'
    · exact ⟨c₁, Or.inl rfl, arrow_mono hchain (by omega) (by omega) h₁a,
        arrow_mono hchain (by omega) (by omega) h'⟩
    · have h₁a' : Arrow (D (i + 2)) c₁ a := arrow_mono hchain (by omega) (by omega) h₁a
      rcases e3 ▸ arrow_or_of_trans hchain (show i + 2 < R by omega) h' h₁a' with h'' | h''
      · exact ⟨b, Or.inr (Or.inr (Or.inr rfl)), h'', arrow_refl _ b⟩
      · exact ⟨a, Or.inr (Or.inr (Or.inl rfl)), arrow_refl _ a, h''⟩
  · have h₁a' : Arrow (D (i + 1)) c₁ a := arrow_mono hchain (by omega) (by omega) h₁a
    rcases e2 ▸ arrow_or_of_trans hchain (show i + 1 < R by omega) h h₁a' with h' | h'
    · exact ⟨c₂, Or.inr (Or.inl rfl), arrow_mono hchain (by omega) (by omega) h',
        arrow_mono hchain (by omega) (by omega) h₂b⟩
    · have h₂b' : Arrow (D (i + 2)) c₂ b := arrow_mono hchain (by omega) (by omega) h₂b
      rcases e3 ▸ arrow_or_of_trans hchain (show i + 2 < R by omega) h' h₂b' with h'' | h''
      · exact ⟨a, Or.inr (Or.inr (Or.inl rfl)), arrow_refl _ a, h''⟩
      · exact ⟨b, Or.inr (Or.inr (Or.inr rfl)), h'', arrow_refl _ b⟩

/-! ### The path lemma -/

private theorem support_take_subset {a b : Fin n} (p : G.Walk a b) (m : ℕ) :
    (p.take m).support ⊆ p.support := by
  rw [SimpleGraph.Walk.take_support_eq_support_take_succ]
  exact List.take_subset _ _

private theorem support_drop_subset {a b : Fin n} (p : G.Walk a b) (m : ℕ) :
    (p.drop m).support ⊆ p.support := by
  rw [SimpleGraph.Walk.drop_support_eq_support_drop_min]
  exact List.drop_subset _ _

/-- **The path lemma** (Lemma 6.5 of Grohe–Kreutzer–Siebertz).  After
`3 * t` rounds of augmentation, every `G`-walk of length at most `2 ^ t`
carries a meet of its two endpoints on its own support.

# Proof strategy

Induction on `t`.  A walk of length at most `1` is an edge or a point,
and `D 0` orients `G`, so one of the endpoints is a meet.  A walk of
length at most `2 ^ (t+1)` splits at its `2 ^ t`-th vertex into two walks
of length at most `2 ^ t`; the halves have meets after `3 * t` rounds,
and `meet_merge` joins them in three more rounds, keeping the meet vertex
on the support. -/
theorem meet_of_walk (hchain : IsAugChain G D R) :
    ∀ (t : ℕ), 3 * t ≤ R → ∀ {a b : Fin n} (p : G.Walk a b), p.length ≤ 2 ^ t →
      ∃ c ∈ p.support, Arrow (D (3 * t)) c a ∧ Arrow (D (3 * t)) c b := by
  intro t
  induction t with
  | zero =>
      intro _ a b p hp
      cases p with
      | nil => exact ⟨a, by simp, arrow_refl _ a, arrow_refl _ a⟩
      | cons hadj q =>
          have hq : q.length = 0 := by
            rw [SimpleGraph.Walk.length_cons] at hp
            simpa using hp
          have hqe := SimpleGraph.Walk.eq_of_length_eq_zero hq
          subst hqe
          rcases (hchain.1 _ _).mp hadj with h | h
          · exact ⟨_, by simp, arrow_refl _ _, Or.inr h⟩
          · exact ⟨_, by simp, Or.inr h, arrow_refl _ _⟩
  | succ t ih =>
      intro ht a b p hp
      have ht' : 3 * t ≤ R := by omega
      have hpow : (2 : ℕ) ^ (t + 1) = 2 ^ t + 2 ^ t := by ring
      have h1 : (p.take (2 ^ t)).length ≤ 2 ^ t := by
        rw [SimpleGraph.Walk.take_length]; exact min_le_left _ _
      have h2 : (p.drop (2 ^ t)).length ≤ 2 ^ t := by
        rw [SimpleGraph.Walk.drop_length]; omega
      obtain ⟨c₁, hc₁, h₁a, h₁m⟩ := ih ht' (p.take (2 ^ t)) h1
      obtain ⟨c₂, hc₂, h₂m, h₂b⟩ := ih ht' (p.drop (2 ^ t)) h2
      obtain ⟨c, hcw, hca, hcb⟩ := meet_merge hchain (by omega) h₁a h₁m h₂m h₂b
      have hround : 3 * (t + 1) = 3 * t + 3 := by ring
      rw [hround]
      refine ⟨c, ?_, hca, hcb⟩
      rcases hcw with rfl | rfl | rfl | rfl
      · exact support_take_subset p (2 ^ t) hc₁
      · exact support_drop_subset p (2 ^ t) hc₂
      · exact p.start_mem_support
      · exact p.end_mem_support

/-- The path lemma, read at the last round of the chain. -/
theorem meet_of_walk_le (hchain : IsAugChain G D R) {t : ℕ} (ht : 3 * t ≤ R)
    {a b : Fin n} (p : G.Walk a b) (hp : p.length ≤ 2 ^ t) :
    ∃ c ∈ p.support, Arrow (D R) c a ∧ Arrow (D R) c b := by
  obtain ⟨c, hc, h₁, h₂⟩ := meet_of_walk hchain t ht p hp
  exact ⟨c, hc, arrow_mono hchain ht le_rfl h₁, arrow_mono hchain ht le_rfl h₂⟩

/-! ### The weak reachability bound -/

/-- The candidates for a vertex weakly reachable from `v`: a vertex `c`
that is `v` or an in-neighbour of `v`, together with the neighbours of
`c` that come `π`-earlier than `c`. -/
noncomputable def wreachCand (E : Orientation n) (π : Equiv.Perm (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  (insert v (E.inN v)).biUnion fun c =>
    insert c (pick fun u => E.Adjacent u c ∧ ((π u : Fin n) : ℕ) < ((π c : Fin n) : ℕ))

/-- The candidate set is small: at most `d + 1` centers, each with at
most `k + 1` candidates. -/
theorem card_wreachCand_le {E : Orientation n} {π : Equiv.Perm (Fin n)} {d k : ℕ}
    (hd : E.InDegLE d) (hπ : BackDegLE E.toGraph (fun v => ((π v : Fin n) : ℕ)) k)
    (v : Fin n) : (wreachCand E π v).card ≤ (d + 1) * (k + 1) := by
  classical
  refine le_trans Finset.card_biUnion_le ?_
  have hterm : ∀ c ∈ insert v (E.inN v),
      (insert c (pick fun u =>
        E.Adjacent u c ∧ ((π u : Fin n) : ℕ) < ((π c : Fin n) : ℕ))).card ≤ k + 1 := by
    intro c _
    refine le_trans (Finset.card_insert_le _ _) ?_
    have hpk : (pick fun u =>
        E.Adjacent u c ∧ ((π u : Fin n) : ℕ) < ((π c : Fin n) : ℕ)).card ≤ k := by
      rw [← Set.ncard_coe_finset]
      refine le_trans (le_of_eq ?_) (hπ c)
      congr 1
      ext u
      exact ⟨fun hu => mem_pick.1 hu, fun hu => mem_pick.2 hu⟩
    omega
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  have := hd v
  have := Finset.card_insert_le v (E.inN v)
  omega

/--
**The weak reachability bound** (Lemma 6.6 of Grohe–Kreutzer–Siebertz).
Let `D` be an augmentation chain of `G` with `R` rounds, `d` a bound on
the in-degrees of its last orientation, and `π` an ordering under which
the underlying graph of that orientation has back-degrees at most `k` —
a degeneracy ordering.  Then every weak `r`-reachability set under `π`
has at most `(d + 1) * (k + 1)` elements, provided `2 ^ t ≥ r` for some
`t` with `3 * t ≤ R`.

# Proof strategy

Let `u` be weakly `r`-reachable from `v` along a walk `p` on which `u` is
`π`-minimal.  The path lemma gives a meet `c ∈ p.support` of `v` and `u`
in the last orientation.  On the `v` side, `c` is `v` or one of its at
most `d` in-neighbours.  On the `u` side, `c` is `u` — or `c` is an
in-neighbour of `u`, and then `u` is a neighbour of `c` with `π u < π c`,
since `u` is `π`-minimal on `p` and `c` lies on `p`; those number at most
`k` by the back-degree bound. -/
theorem wreach_ncard_le_of_augChain {t r d k : ℕ} (hchain : IsAugChain G D R)
    (ht : 3 * t ≤ R) (hr : r ≤ 2 ^ t) (hd : (D R).InDegLE d) {π : Equiv.Perm (Fin n)}
    (hπ : BackDegLE (D R).toGraph (fun v => ((π v : Fin n) : ℕ)) k) (v : Fin n) :
    (wreach G π r v).ncard ≤ (d + 1) * (k + 1) := by
  classical
  refine le_trans (Set.ncard_le_ncard (t := ↑(wreachCand (D R) π v)) ?_ (Set.toFinite _)) ?_
  · intro u hu
    obtain ⟨p, hp, hmin⟩ := mem_wreach_iff.mp hu
    obtain ⟨c, hcmem, hcv, hcu⟩ := meet_of_walk_le hchain ht p (hp.trans hr)
    refine Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨c, ?_, ?_⟩)
    · rcases hcv with rfl | h
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem h
    · rcases hcu with rfl | h
      · exact Finset.mem_insert_self _ _
      · rcases eq_or_lt_of_le (hmin c hcmem) with heq | hlt
        · have : u = c := π.injective heq
          subst this
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (mem_pick.2 ⟨Or.inr h, hlt⟩)
  · rw [Set.ncard_coe_finset]
    exact card_wreachCand_le hd hπ v

/-- **The composition.**  An augmentation chain of `G` with `3 * t ≤ R`
rounds and `2 * r ≤ 2 ^ t`, plus a compatible ordering of its last
orientation, yields an `r`-neighborhood cover of `G` of radius `2 * r`
and degree `(d + 1) * (k + 1)`: the fibers of weak `2r`-reachability
under that ordering.  This is the statement the cover-computation phase
of the program cites. -/
theorem isNeighborhoodCover_of_augChain {t r d k : ℕ} (hchain : IsAugChain G D R)
    (ht : 3 * t ≤ R) (hr : 2 * r ≤ 2 ^ t) (hd : (D R).InDegLE d)
    (π : Equiv.Perm (Fin n))
    (hπ : BackDegLE (D R).toGraph (fun v => ((π v : Fin n) : ℕ)) k) :
    IsNeighborhoodCover G r (fun u => {w | u ∈ wreach G π (2 * r) w}) ((d + 1) * (k + 1)) :=
  isNeighborhoodCover_wreach G r _ π fun v =>
    wreach_ncard_le_of_augChain hchain ht hr hd hπ v

/-! ### The ordering the program computes exists -/

/-- The ordered pairs of adjacent vertices inside `S` are at most
`2 * d * |S|` when the orientation has in-degree at most `d`: charge each
ordered pair to whichever of its two ends the arc points at. -/
private theorem card_pairsIn_toGraph_le {E : Orientation n} {d : ℕ} (hd : E.InDegLE d)
    (S : Finset (Fin n)) : (pairsIn E.toGraph S).card ≤ 2 * d * S.card := by
  classical
  have hsub : pairsIn E.toGraph S ⊆
      S.biUnion (fun v => (E.inN v).image (fun u => (u, v))) ∪
        S.biUnion (fun u => (E.inN u).image (fun v => (u, v))) := by
    intro q hq
    obtain ⟨h1, h2, hadj⟩ := mem_pairsIn.1 hq
    rcases hadj with h | h
    · exact Finset.mem_union_left _
        (Finset.mem_biUnion.2 ⟨q.2, h2, Finset.mem_image.2 ⟨q.1, h, rfl⟩⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨q.1, h1, Finset.mem_image.2 ⟨q.2, h, rfl⟩⟩)
  have hbi : ∀ (f : Fin n → Fin n → Fin n × Fin n),
      (S.biUnion (fun v => (E.inN v).image (f v))).card ≤ d * S.card := by
    intro f
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ v ∈ S, ((E.inN v).image (f v)).card
        ≤ ∑ _v ∈ S, d :=
          Finset.sum_le_sum fun v _ => le_trans (Finset.card_image_le) (hd v)
      _ = d * S.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) ?_)
  have hA := hbi (fun v u => (u, v))
  have hB := hbi (fun u v => (u, v))
  have hsum : 2 * d * S.card = d * S.card + d * S.card := by ring
  omega

/-- **Small degree inside every set.**  The underlying graph of an
orientation of in-degree at most `d` has, inside every nonempty vertex
set, a vertex of degree at most `2 * d` there.  With
`Augmentation.degeneracyLE_of_lowDegreeVertices` this is why the greedy
degeneracy pass the program runs on the last orientation succeeds with
`k ≤ 2 * d`, hence why the cover degree above is `2 (d+1)²`-shaped. -/
theorem lowDegreeVertices_toGraph {E : Orientation n} {d : ℕ} (hd : E.InDegLE d) :
    LowDegreeVertices E.toGraph (2 * d) := by
  classical
  intro S hS
  by_contra hcon
  push Not at hcon
  have hlow : S.card * (2 * d + 1) ≤ (pairsIn E.toGraph S).card := by
    rw [card_pairsIn]
    calc S.card * (2 * d + 1) = ∑ _v ∈ S, (2 * d + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ S, (nbrsIn E.toGraph S v).card := Finset.sum_le_sum fun v hv => hcon v hv
  have hhigh := card_pairsIn_toGraph_le hd S
  have hpos : 0 < S.card := Finset.card_pos.mpr hS
  have hexp : S.card * (2 * d + 1) = 2 * d * S.card + S.card := by ring
  omega

end Lax3Proofs.OrderedCovers
