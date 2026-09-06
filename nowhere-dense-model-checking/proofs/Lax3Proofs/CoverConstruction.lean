import Lax3.NeighborhoodCoverBound
import Lax3Proofs.WalkDistance

/-!
Neighborhood covers out of a vertex ordering: the construction behind
Theorem 6.2 of Grohe–Kreutzer–Siebertz, via their Lemma 6.9.

Fix any ordering `π` of the vertices whose weak `2r`-reachability sets
have size at most `k`. The cluster of a vertex `u` is the fiber of weak
`2r`-reachability
over `u` — the set of vertices `w` from which `u` is weakly `2r`-reachable.
Three readings of that one definition give the three conditions of a
neighborhood cover. Its *degree* is the wreach bound read backwards: the
clusters containing a fixed `v` are indexed by exactly the vertices weakly
`2r`-reachable from `v`, so there are at most `k` of them. Its
*radius* is the length bound on the reachability walk, reversed. And it
*covers*: the `r`-ball of `v` is contained in the cluster of the
`π`-minimal vertex `u` of that ball, because any `w` in the ball reaches
`u` by going back to `v` and out again — a walk of length at most `2r`
whose support stays inside the ball, where `u` is minimal by choice.

This proves `Lax3.OrderedNeighborhoodCover.isNeighborhoodCover_wreach`,
the core used for the algorithm's computed ordering. The existential
cover theorem chooses an ordering attaining `wcol G (2r)` and applies
that concept claim with `k = wcol G (2r)`.
-/

namespace Lax3Proofs.CoverConstruction

open Lax3.ColoredGraphs
open Lax3.NeighborhoodCovers
open Lax12.ColoringNumbers
open Lax3Proofs.WalkDistance

/-! ### Reading the definitions -/

/-- Membership in a weak reachability set, spelled out: `u` is weakly
`r`-reachable from `v` when some walk from `v` to `u` of length at most
`r` has `u` as a `π`-minimal vertex of its support. -/
theorem mem_wreach_iff {n : ℕ} {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)}
    {r : ℕ} {v u : Fin n} :
    u ∈ wreach G π r v ↔ ∃ w : G.Walk v u, w.length ≤ r ∧ ∀ y ∈ w.support, π u ≤ π y :=
  Iff.rfl

/-- The minimum defining the weak `r`-coloring number is attained: some
ordering has all its weak reachability sets of size at most `wcol G r`.
The defining set of bounds is nonempty because `n` bounds every set of
vertices. -/
theorem exists_ordering_wreach_le_wcol {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) :
    ∃ π : Equiv.Perm (Fin n), ∀ v, (wreach G π r v).ncard ≤ wcol G r := by
  have hs : {k : ℕ | ∃ π : Equiv.Perm (Fin n),
      ∀ v, (wreach G π r v).ncard ≤ k}.Nonempty :=
    ⟨n, Equiv.refl _, fun v => by
      simpa using Set.ncard_le_card (wreach G (Equiv.refl _) r v)⟩
  exact Nat.sInf_mem hs

/-! ### Support vertices of a short walk -/

/-- Every vertex on a walk of length at most `r` is within distance `r` of
both endpoints: cutting the walk at that vertex splits its length. -/
private theorem withinDist_of_mem_support {V : Type*} {G : SimpleGraph V} {a b : V}
    {r : ℕ} (p : G.Walk a b) (hp : p.length ≤ r) {y : V} (hy : y ∈ p.support) :
    WithinDist G r a y ∧ WithinDist G r y b := by
  classical
  have hlen := congrArg SimpleGraph.Walk.length (p.take_spec hy)
  rw [SimpleGraph.Walk.length_append] at hlen
  exact ⟨⟨p.takeUntil y hy, by omega⟩, ⟨p.dropUntil y hy, by omega⟩⟩

/-! ### The cover -/

/--
---
conclusion: Lax3.OrderedNeighborhoodCover.isNeighborhoodCover_wreach
---
**The cover of an ordering** (Lemma 6.9 of Grohe–Kreutzer–Siebertz,
the parametric core of their Theorem 6.2). For any ordering `π` whose
weak `2r`-reachability sets have at most `k` elements, the fibers of weak
`2r`-reachability form an `r`-neighborhood cover of radius `2r` and
degree at most `k`.

# Proof strategy

For the supplied ordering `π`, let the cluster of
`u` be `{w | u ∈ wreach G π (2r) w}`, the set of vertices from which `u`
is weakly `2r`-reachable.

The degree bound is the definition read backwards: the set of clusters
containing `v` is indexed by `{u | u ∈ wreach G π (2r) v}`, which is
`wreach G π (2r) v` itself, of size at most `k` by hypothesis.
The radius bound drops the minimality clause: a vertex in the cluster
of `u` reaches `u` by a walk of length at most `2r`, which reversed puts
it in the `2r`-ball of `u`.

Covering is the only real argument. Given `v`, let `u` be a `π`-minimal
vertex of the `r`-ball of `v`, which is nonempty and finite. For `w` in
that ball, concatenate the reversed ball walk `w → v` with the ball walk
`v → u`: a walk of length at most `2r` from `w` to `u`. Every vertex on it
lies on one of the two halves, and cutting a walk of length at most `r` at
any of its vertices shows that vertex to be within distance `r` of both
endpoints — so the whole support stays inside the `r`-ball of `v`, where
`u` is `π`-minimal. Hence `u` is weakly `2r`-reachable from `w`, i.e. `w`
lies in the cluster of `u`.
-/
protected theorem isNeighborhoodCover_wreach {n : ℕ} (G : SimpleGraph (Fin n)) (r k : ℕ)
    (π : Equiv.Perm (Fin n)) (hk : ∀ v, (wreach G π (2 * r) v).ncard ≤ k) :
    IsNeighborhoodCover G r (fun u => {w | u ∈ wreach G π (2 * r) w}) k := by
  classical
  refine ⟨fun v => ?_, fun u w hw => ?_, hk⟩
  · obtain ⟨u, huF, hmin⟩ :=
      Finset.exists_min_image (Set.toFinite (ball G r v)).toFinset (fun x => π x)
        ⟨v, (Set.Finite.mem_toFinset _).mpr (mem_ball_self G r v)⟩
    have hu : u ∈ ball G r v := (Set.Finite.mem_toFinset _).mp huF
    refine ⟨u, fun w hw => ?_⟩
    obtain ⟨p, hp⟩ := mem_ball.mp hw
    obtain ⟨q, hq⟩ := mem_ball.mp hu
    have hpr : p.reverse.length ≤ r := by
      rw [SimpleGraph.Walk.length_reverse]; exact hp
    refine mem_wreach_iff.mpr ⟨p.reverse.append q, ?_, fun y hy => ?_⟩
    · rw [SimpleGraph.Walk.length_append]; omega
    · refine hmin y ((Set.Finite.mem_toFinset _).mpr ?_)
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hy with hy | hy
      · exact mem_ball.mpr (withinDist_symm (withinDist_of_mem_support p.reverse hpr hy).2)
      · exact mem_ball.mpr (withinDist_of_mem_support q hq hy).1
  · obtain ⟨p, hp, -⟩ := mem_wreach_iff.mp hw
    exact mem_ball.mpr (withinDist_symm ⟨p, hp⟩)

/--
---
conclusion: Lax3.NeighborhoodCoverBound.exists_neighborhoodCover_degree_wcol
---
**Neighborhood covers of weak coloring degree** (Theorem 6.2 of
Grohe–Kreutzer–Siebertz, via their Lemma 6.9): every graph has, for every
radius `r`, an `r`-neighborhood cover of radius `2r` whose degree is at
most its weak `2r`-coloring number.

# Proof strategy

Choose an ordering attaining `wcol G (2r)`: the defining infimum is over
a nonempty set of natural-number bounds, so it is attained. Apply
`Lax3.OrderedNeighborhoodCover.isNeighborhoodCover_wreach` to that
ordering and its bound. The arbitrary-order construction is discharged
by `isNeighborhoodCover_wreach` above.
-/
theorem exists_neighborhoodCover_degree_wcol {n : ℕ}
    (G : SimpleGraph (Fin n)) (r : ℕ) :
    ∃ X : Fin n → Set (Fin n),
      IsNeighborhoodCover G r X (wcol G (2 * r)) := by
  obtain ⟨π, hπ⟩ := exists_ordering_wreach_le_wcol G (2 * r)
  exact ⟨_, Lax3.OrderedNeighborhoodCover.isNeighborhoodCover_wreach G r (wcol G (2 * r)) π hπ⟩

end Lax3Proofs.CoverConstruction
