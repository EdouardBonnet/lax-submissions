import Lax3.OrderedNeighborhoodCover
import Lax12.ColoringNumbers

/-!
---
title: Neighborhood covers of weak coloring degree
type: theorem
---
Every graph has, for every radius *r*, an *r*-neighborhood cover of
radius 2*r* whose degree is at most the weak 2*r*-coloring number of
the graph.

This is Theorem 6.2 of Grohe–Kreutzer–Siebertz (via their Lemma 6.9):
from a vertex ordering witnessing the weak coloring number, take as
the cluster of *v* the set of vertices from which *v* is weakly
2*r*-reachable. On a nowhere dense class this composes with Lax12's
subpolynomial weak coloring numbers to covers of degree *c* · *n*^ε
for every ε > 0 — the form the model-checking recursion consumes, on
every arena, since the weak coloring bound of Lax12 is uniform over
subgraphs of members.

# Formalization notes

The statement is per-graph and class-free, with the degree bound
`wcol G (2r)` — Lax12's `wcol`, not restated. It chooses an optimal
ordering and applies the arbitrary-order construction
`Lax3.OrderedNeighborhoodCover.isNeighborhoodCover_wreach` to it.
That core names the clusters explicitly and accepts the supplied
ordering's weak reachability bound; it is also the form the
model-checking algorithm consumes for its computed ordering. The
existential theorem composes with any wcol bound a consumer owns,
including the subpolynomial bound for nowhere dense classes.

The discharge shows that an optimal ordering `π` exists, then applies
the core claim to the clusters `{w | u ∈ wreach G π (2r) w}` with
the bound `(wreach G π (2r) v).ncard ≤ wcol G (2r)`. Covering and
radius are the elementary walk arguments proved for the core. The
*computation* of such a cover on the word RAM — including computing a
good-enough ordering — is proved in the algorithmic layer and is not
part of this claim.
-/

namespace Lax3.NeighborhoodCoverBound

open Lax3.NeighborhoodCovers
open Lax12.ColoringNumbers

/-- Every graph has an `r`-neighborhood cover of radius `2r` and
degree at most its weak `2r`-coloring number. -/
axiom exists_neighborhoodCover_degree_wcol {n : ℕ}
    (G : SimpleGraph (Fin n)) (r : ℕ) :
    ∃ X : Fin n → Set (Fin n),
      IsNeighborhoodCover G r X (wcol G (2 * r))

end Lax3.NeighborhoodCoverBound
