import Lax3.Locality
import Lax3Proofs.BCAlgebra

/-!
The locality decomposition as a *function*. The endorsed theorem
`Lax3.Locality.locality` is an existential: every formula of distance
rank `(k, q)` *has* an equivalent boolean combination of local formulas
and scatter sentences. A consumer that `Classical.choose`s it ad hoc gets
no guarantee that two use sites at the same `(choice, φ)` pick the same
combination — but the formula schedule of the algorithm (algorithm-v2
§8 step 3, §9 O2, D5) must depend only on `(φ, ε, C)`, never on the
input graph, so the decomposition has to be one fixed function.

This file consumes that claim through its concept interface; its proof
is `Lax3Proofs.Assembly.locality`. It makes the choice once.
`localityBC` is the chosen decomposition; the three spec lemmas split
the claim's conjunction so a consumer takes exactly the clause it needs;
`localityBC_irrel` records
that the rank witness does not enter the choice (definitional, by proof
irrelevance), so every use site at the same `(choice, φ)` sees the same
combination. `localAtoms` and `scatterAtoms` read the combination's atom
list apart into the two kinds — the data the schedule construction
iterates over — with membership lemmas returning each to `BC.atoms` and
with the claim's side conditions restated over the lists.

Nothing here is computable and nothing needs to be: what the choice
buys is a function, not decidability.
-/

namespace Lax3Proofs.LocalityFun

open Lax3 Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality

variable {L : ℕ}

/-- **The locality decomposition, chosen once.** The boolean combination
of local formulas and scatter sentences that `Lax3.Locality.locality`
asserts to exist, fixed as a function of `(choice, φ)` (and the ranks).
The rank witness `hφ` does not enter the choice: see `localityBC_irrel`. -/
noncomputable def localityBC (choice : ScatterChoice) {k q : ℕ} (φ : DistFO L k)
    (hφ : DistFO.DRank k q φ) : BC (DistFO L k ⊕ ScatterSentence L) :=
  (Lax3.Locality.locality choice φ hφ).choose

/-- The formula atoms of the chosen decomposition are local and of
distance rank `(k, q)`. -/
theorem localityBC_atoms_local (choice : ScatterChoice) {k q : ℕ} (φ : DistFO L k)
    (hφ : DistFO.DRank k q φ) :
    ∀ ψ : DistFO L k, Sum.inl ψ ∈ (localityBC choice φ hφ).atoms →
      DistFO.IsLocal ψ ∧ DistFO.DRank k q ψ :=
  (Lax3.Locality.locality choice φ hφ).choose_spec.1

/-- The scatter-sentence atoms of the chosen decomposition have distance
rank `(k, q)`. -/
theorem localityBC_atoms_scatter (choice : ScatterChoice) {k q : ℕ} (φ : DistFO L k)
    (hφ : DistFO.DRank k q φ) :
    ∀ σ : ScatterSentence L, Sum.inr σ ∈ (localityBC choice φ hφ).atoms → σ.DRank k q :=
  (Lax3.Locality.locality choice φ hφ).choose_spec.2.1

/-- The chosen decomposition is equivalent to the formula in every finite
colored graph under every environment. -/
theorem localityBC_eval (choice : ScatterChoice) {k q : ℕ} (φ : DistFO L k)
    (hφ : DistFO.DRank k q φ) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
      DistFO.Sat G col m φ ↔
        (localityBC choice φ hφ).eval
          (Sum.elim (DistFO.Sat G col m) (ScatterSentence.Sat choice G col)) :=
  (Lax3.Locality.locality choice φ hφ).choose_spec.2.2

/-- **The semantic gate.** The chosen decomposition does not depend on
the rank witness: two use sites at the same `(choice, φ)` see the same
combination. Definitional, by proof irrelevance — the existential being
chosen from is the same proposition for both witnesses. -/
theorem localityBC_irrel (choice : ScatterChoice) {k q : ℕ} (φ : DistFO L k)
    (hφ hφ' : DistFO.DRank k q φ) :
    localityBC choice φ hφ = localityBC choice φ hφ' := rfl

/-! ### The atom lists as data

The schedule construction iterates over the atoms of the decomposition,
one kind at a time. `BC.atoms` is a `List` over the sum type; these two
functions read it apart. -/

/-- The local-formula atoms of the chosen decomposition, as a list. -/
noncomputable def localAtoms (choice : ScatterChoice) {k q : ℕ} (φ : DistFO L k)
    (hφ : DistFO.DRank k q φ) : List (DistFO L k) :=
  (localityBC choice φ hφ).atoms.filterMap Sum.getLeft?

/-- The scatter-sentence atoms of the chosen decomposition, as a list. -/
noncomputable def scatterAtoms (choice : ScatterChoice) {k q : ℕ} (φ : DistFO L k)
    (hφ : DistFO.DRank k q φ) : List (ScatterSentence L) :=
  BCAlgebra.rightAtoms (localityBC choice φ hφ)

/-- Membership in the local-atom list is membership of the left injection
in the combination's atoms. -/
theorem mem_localAtoms {choice : ScatterChoice} {k q : ℕ} {φ : DistFO L k}
    {hφ : DistFO.DRank k q φ} {ψ : DistFO L k} :
    ψ ∈ localAtoms choice φ hφ ↔ Sum.inl ψ ∈ (localityBC choice φ hφ).atoms := by
  simp only [localAtoms, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hxψ⟩
    rcases x with ψ' | σ
    · rw [show ψ' = ψ by simpa using hxψ] at hx
      exact hx
    · simp at hxψ
  · exact fun h => ⟨Sum.inl ψ, h, by simp⟩

/-- Membership in the scatter-atom list is membership of the right
injection in the combination's atoms. -/
theorem mem_scatterAtoms {choice : ScatterChoice} {k q : ℕ} {φ : DistFO L k}
    {hφ : DistFO.DRank k q φ} {σ : ScatterSentence L} :
    σ ∈ scatterAtoms choice φ hφ ↔ Sum.inr σ ∈ (localityBC choice φ hφ).atoms :=
  BCAlgebra.mem_rightAtoms

/-- Every member of the local-atom list is local and of distance rank
`(k, q)`. -/
theorem localAtoms_spec (choice : ScatterChoice) {k q : ℕ} (φ : DistFO L k)
    (hφ : DistFO.DRank k q φ) :
    ∀ ψ ∈ localAtoms choice φ hφ, DistFO.IsLocal ψ ∧ DistFO.DRank k q ψ :=
  fun ψ h => localityBC_atoms_local choice φ hφ ψ (mem_localAtoms.mp h)

/-- Every member of the scatter-atom list has distance rank `(k, q)`. -/
theorem scatterAtoms_spec (choice : ScatterChoice) {k q : ℕ} (φ : DistFO L k)
    (hφ : DistFO.DRank k q φ) :
    ∀ σ ∈ scatterAtoms choice φ hφ, σ.DRank k q :=
  fun σ h => localityBC_atoms_scatter choice φ hφ σ (mem_scatterAtoms.mp h)

/-- The atom lists inherit rank-witness irrelevance from `localityBC`. -/
theorem localAtoms_irrel (choice : ScatterChoice) {k q : ℕ} (φ : DistFO L k)
    (hφ hφ' : DistFO.DRank k q φ) :
    localAtoms choice φ hφ = localAtoms choice φ hφ' := rfl

/-- The atom lists inherit rank-witness irrelevance from `localityBC`. -/
theorem scatterAtoms_irrel (choice : ScatterChoice) {k q : ℕ} (φ : DistFO L k)
    (hφ hφ' : DistFO.DRank k q φ) :
    scatterAtoms choice φ hφ = scatterAtoms choice φ hφ' := rfl

end Lax3Proofs.LocalityFun
