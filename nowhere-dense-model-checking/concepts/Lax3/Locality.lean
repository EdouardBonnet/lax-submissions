import Lax3.ScatterSentences

/-!
---
title: Locality theorem for distance logic
type: theorem
---
Every formula of distance logic of distance rank (*k*, *q*) is
equivalent to a boolean combination of *local* formulas and scatter
sentences, all of distance rank (*k*, *q*). This is the locality
theorem of the source note (arXiv:2606.23180, Theorem 1), in the spirit
of Gaifman's locality theorem and of the locality theorem of Grohe,
Kreutzer and Siebertz: unrestricted quantification is eliminated in
favour of quantification inside a bounded neighborhood of the free
variables, plus finitely many global assertions of the form "there are
*t* pairwise far apart vertices satisfying β". What distinguishes this
version, and what makes it usable, is that the rewriting does not
increase the rank — and the rank it preserves, distance rank, controls
the radii of everything the resulting formulas mention.

The theorem holds for every scatter choice; which one is fixed is
invisible to the statement and decisive for the algorithm, which
evaluates scatter sentences by running the greedy process. The
companion statement `Lax3.NormalForm` — the analogue of Gaifman's
normal form — instantiates the maximum-size choice and writes the
scatter sentences out in the logic itself.

# Formalization notes

The boolean combination is reified: `BC α` is the type of boolean
combinations of atoms drawn from `α`, with an evaluation map and a list
of the atoms occurring in it. That list is what carries the side
conditions of the theorem — "all of distance rank (*k*, *q*)" is a
statement about the atoms of the combination, and a bare `Prop`-level
equivalence could not express it. Atoms are the sum type of formulas
and scatter sentences, so one boolean combination mixes the two kinds
and `Sum.elim` supplies their two evaluations.

Effectiveness is not part of this claim: it asserts that the boolean
combination exists. `Lax3Proofs.LocalityFun.localityBC` consumes this
existential using `Classical.choose`, fixing one decomposition for the
scatter choice, formula and ranks before the input graph or environment
is supplied. Proof irrelevance makes that choice independent of the
rank witness. The model-checking schedule uses this fixed decomposition.
The headline theorem quantifies over the graph class, formula and
positive exponent, then asserts the existence of a word-RAM program and
time bounds that work for every input graph. This quantifier order lets
the decomposition be fixed with those parameters; it does not assert a
procedure that computes the program uniformly from them.

The statement is an `axiom` on this concept surface, discharged by
`Lax3Proofs.Assembly.locality` in the proofs package. The normal-form
corollary and the model-checking decomposition consume this concept
interface, whose proof is tracked as a separate dependency. The proofs
package also provides the chosen decomposition and its specifications
in `Lax3Proofs.LocalityFun` for consumers needing a fixed function.
-/

namespace Lax3.Locality

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences

universe u

/-- Boolean combinations of atoms drawn from `α`. Disjunction and
implication are the usual abbreviations; the empty combination is
`tru`. -/
inductive BC (α : Type u) : Type u
  /-- An atom. -/
  | atom (a : α) : BC α
  /-- The empty combination, always true. -/
  | tru : BC α
  /-- Negation. -/
  | not (b : BC α) : BC α
  /-- Conjunction. -/
  | and (b c : BC α) : BC α

/-- The truth value of a boolean combination, given a truth value for
each atom. -/
def BC.eval {α : Type u} (v : α → Prop) : BC α → Prop
  | .atom a => v a
  | .tru => True
  | .not b => ¬ BC.eval v b
  | .and b c => BC.eval v b ∧ BC.eval v c

/-- The atoms occurring in a boolean combination, with multiplicity. -/
def BC.atoms {α : Type u} : BC α → List α
  | .atom a => [a]
  | .tru => []
  | .not b => BC.atoms b
  | .and b c => BC.atoms b ++ BC.atoms c

variable {L : ℕ}

/-- **Locality theorem** (Theorem 1 of arXiv:2606.23180). Fix a scatter
choice. Every formula of distance rank `(k, q)` is equivalent to a
boolean combination of local formulas of distance rank `(k, q)` and
scatter sentences of distance rank `(k, q)`: there is a boolean
combination whose formula atoms are all local of distance rank `(k, q)`,
whose scatter-sentence atoms all have distance rank `(k, q)`, and which
has the same truth value as the formula in every finite colored graph
under every environment. -/
axiom locality (choice : ScatterChoice) {k q : ℕ} (φ : DistFO L k)
    (hφ : DistFO.DRank k q φ) :
    ∃ b : BC (DistFO L k ⊕ ScatterSentence L),
      (∀ ψ : DistFO L k, Sum.inl ψ ∈ b.atoms → DistFO.IsLocal ψ ∧ DistFO.DRank k q ψ) ∧
      (∀ σ : ScatterSentence L, Sum.inr σ ∈ b.atoms → σ.DRank k q) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
        DistFO.Sat G col m φ ↔
          b.eval (Sum.elim (DistFO.Sat G col m) (ScatterSentence.Sat choice G col))

end Lax3.Locality
