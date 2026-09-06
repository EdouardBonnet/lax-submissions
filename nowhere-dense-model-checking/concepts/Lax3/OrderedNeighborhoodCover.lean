import Lax3.NeighborhoodCovers
import Lax12.ColoringNumbers

/-!
---
title: Neighborhood covers from vertex orderings
type: theorem
---
Any vertex ordering whose weak 2*r*-reachability sets have size at most
*k* gives an *r*-neighborhood cover of radius 2*r* and degree at most
*k*. The cluster of a vertex *u* consists of the vertices from which
*u* is weakly 2*r*-reachable.

This is the arbitrary-order construction of Lemma 6.9 of
Grohe–Kreutzer–Siebertz. The model-checking algorithm uses it for the
ordering it computes. The companion theorem
`Lax3.NeighborhoodCoverBound.exists_neighborhoodCover_degree_wcol`
uses it for an optimal ordering, obtaining the weak coloring number
itself as the degree bound.

# Formalization notes

The statement is per-graph and class-free, with the ordering `π` and
bound `k` supplied explicitly. The cluster of `u` is
`{w | u ∈ wreach G π (2r) w}`, using Lax12's weak reachability sets.
The hypothesis directly bounds the number of clusters containing a
given vertex. The radius condition follows from reversing a weak
reachability walk. For covering, choose a `π`-minimal vertex of an
`r`-ball; every other vertex of the ball reaches it along a walk of
length at most `2r` whose support remains in the ball.

The claim is discharged by
`Lax3Proofs.CoverConstruction.isNeighborhoodCover_wreach`. Both the
existential cover theorem and the algorithm consume this interface,
sharing the same proved construction.
-/

namespace Lax3.OrderedNeighborhoodCover

open Lax3.NeighborhoodCovers
open Lax12.ColoringNumbers

/-- The fibers of weak `2r`-reachability under any ordering `π` form
an `r`-neighborhood cover of radius `2r` and degree at most `k`,
provided every weak `2r`-reachability set has size at most `k`.
This is the arbitrary-order construction of Lemma 6.9 of
Grohe–Kreutzer–Siebertz, used both by the algorithm with its computed
ordering and by the existential cover theorem with an optimal one. -/
axiom isNeighborhoodCover_wreach {n : ℕ} (G : SimpleGraph (Fin n)) (r k : ℕ)
    (π : Equiv.Perm (Fin n)) (hk : ∀ v, (wreach G π (2 * r) v).ncard ≤ k) :
    IsNeighborhoodCover G r (fun u => {w | u ∈ wreach G π (2 * r) w}) k

end Lax3.OrderedNeighborhoodCover
