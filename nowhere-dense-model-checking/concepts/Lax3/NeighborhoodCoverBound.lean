import Lax3.NeighborhoodCovers
import Lax12.ColoringNumbers

/-!
---
title: Neighborhood covers of weak coloring degree
type: theorem
---
Every graph has, for every radius *r*, an *r*-neighborhood cover of
radius 2*r* whose degree is at most the weak 2*r*-coloring number of
the graph. More generally, any vertex ordering whose weak
2*r*-reachability sets have size at most *k* gives such a cover of
degree at most *k*.

This is Theorem 6.2 of Grohe–Kreutzer–Siebertz (via their Lemma 6.9):
from a vertex ordering witnessing the weak coloring number, take as
the cluster of *v* the set of vertices from which *v* is weakly
2*r*-reachable. On a nowhere dense class this composes with Lax12's
subpolynomial weak coloring numbers to covers of degree *c* · *n*^ε
for every ε > 0 — the form the model-checking recursion consumes, on
every arena, since the weak coloring bound of Lax12 is uniform over
subgraphs of members.

# Formalization notes

Both statements are per-graph and class-free. The arbitrary-order
form `isNeighborhoodCover_wreach` names the clusters explicitly and
accepts the supplied ordering's weak reachability bound. This is the
form the model-checking algorithm consumes for its computed ordering.
The existential form `exists_neighborhoodCover_degree_wcol` chooses
an optimal ordering and applies that core with the degree bound
`wcol G (2r)` — Lax12's `wcol`, not restated. It therefore composes
with any wcol bound a consumer owns, including the subpolynomial
bound for nowhere dense classes.

The arbitrary-order discharge constructs the cluster of `u` as
`{w | u ∈ wreach G π (2r) w}` and reads the degree bound off the
hypothesis `(wreach G π (2r) v).ncard ≤ k` directly; covering and
radius are elementary walk arguments. The existential discharge uses
this claim after showing that an optimal ordering exists. The
*computation* of such a cover on the word RAM — including computing a
good-enough ordering — is proved in the algorithmic layer and is not
part of these two claims.
-/

namespace Lax3.NeighborhoodCoverBound

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

/-- Every graph has an `r`-neighborhood cover of radius `2r` and
degree at most its weak `2r`-coloring number. -/
axiom exists_neighborhoodCover_degree_wcol {n : ℕ}
    (G : SimpleGraph (Fin n)) (r : ℕ) :
    ∃ X : Fin n → Set (Fin n),
      IsNeighborhoodCover G r X (wcol G (2 * r))

end Lax3.NeighborhoodCoverBound
