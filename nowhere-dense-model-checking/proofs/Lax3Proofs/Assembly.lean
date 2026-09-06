import Lax3.NormalForm
import Lax3Proofs.SyntaxLemmas
import Lax3Proofs.SemLocal
import Lax3Proofs.Separation
import Lax3Proofs.FarQuant
import Lax3Proofs.BCAlgebra
import Lax3Proofs.ScatterFml

/-!
The locality theorem of the source note (arXiv:2606.23180, Theorem 1)
and its normal form (Corollary 7), discharging the two axioms of
`Lax3.Locality` and `Lax3.NormalForm`.

The proof is the source's structural induction on the formula, with the
rank obtained at each step by inverting the `DRank` derivation. Atoms and
boolean connectives are immediate; the two quantifiers are where the
imported machinery enters.

* **Local quantification** `exL r g ψ`. The induction hypothesis turns
  the body into a boolean combination of local formulas and scatter
  sentences. Scatter sentences are *sentences*, so their truth does not
  depend on the bound variable and the finitely many truth patterns of
  them may be enumerated outside the quantifier — that is
  `BCAlgebra.exists_eval_sum_iff`. Under a fixed pattern what is left is
  a boolean combination of local formulas, which `BCAlgebra.interp`
  collapses to a single local formula (`patternFml` below); the
  quantifier is put back in front of it, guard set and radius unchanged,
  and `BCAlgebra.pullOut` rebuilds one combination. This is `exL_step`.
* **Unrestricted quantification** `exU ψ` at arity zero. There is no
  variable for a guard to be local to, and the source's answer is a
  scatter sentence: the collapsed formula `ψ_τ` of each pattern is
  satisfiable exactly when the distinguished scattered subset of the set
  it defines is nonempty, which is the scatter sentence
  `⟨4ρ⁻(1, q), ψ_τ, 1⟩` — of distance rank `(0, q + 1)` with rank witness
  `i = 1`. This is `exU_zero_step`; the equivalence itself is
  `scatterSentence_sat_one_iff`, where maximality of the distinguished
  set supplies the nonempty direction through
  `ScatterCore.exists_withinDist_of_maximal`.
* **Unrestricted quantification** `exU ψ` at positive arity. The witness
  is split classically at radius ρ⁻(k+1, q): a near witness is a local
  quantification with guard set `Finset.univ`, handled by the same
  `exL_step` (the radius is admissible by `rhoMinus_le_rhoPlus`); a far
  witness is separated from the tuple by `Separation.separate` with the
  capsule split `e₁ = Fin.castSucc`, `e₂ = const (Fin.last k)`, and each
  capsule `β` is then discharged by `FarQuant.farQuant`. This is
  `exU_pos_step` and `exU_far_step`.

The normal form is the locality theorem at the maximum-size scatter
choice, consumed through `Lax3.Locality.locality`, with the scatter
sentences written out in the logic:
`ScatterFml.sat_scatterFml` replaces each scatter atom, `BCAlgebra.eval_congr`
carries the replacement through the combination, and the five bridges of
`Lax3Proofs.ScatterFml` turn the scatter rank the theorem produces into
the five conditions the corollary states.

# Formalization notes

The always-true formula that `BCAlgebra.interp` needs for the empty
combination is `Separation.alwaysTrue`, the atom `x₀ = x₀`, and not
`Lax3.NormalForm.verum`: the latter spends an unrestricted quantifier and
is not local, so it cannot appear inside a formula the theorem claims is
local. This is why `patternFml` carries a proof that the context is
nonempty — at arity zero there is no such atom, and no formula is
collapsed there either, since the sentence case produces a scatter
sentence instead.

`Separation.separate` and `FarQuant.farQuant` both conclude with a `∀`
over the graph and the environment, so the objects they produce are
chosen once per pattern, before any graph is fixed, exactly as the
induction hypothesis is. The choice over the list of separated pairs is
made with `choose`; `farQuant` is totalized to a function on all of
`DistFO L 1` first, its hypotheses moved inside the existential, so that
`choose` yields a function that does not depend on a membership proof.

No tactic here is handed a concept-side definition: `Sat`, `IsLocal`,
`BC.eval`, `BC.atoms`, `ScatterSentence.Sat` and `ScatterSentence.DRank`
are taken apart through the clause lemmas of `Lax3Proofs.SyntaxLemmas`,
`Lax3Proofs.BCAlgebra` and `Lax3Proofs.ScatterFml`, and every radius
inequality goes through `Lax3Proofs.Horizon`.
`Lax3Proofs.FarQuant` is deliberately not opened — it carries its own
copies of the `BC` clause lemmas, which would make every use of
`BCAlgebra.eval_and` and its siblings ambiguous — so its one export is
named qualified.
-/

namespace Lax3Proofs.Assembly

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality Lax3.NormalForm
open Lax3Proofs.Horizon Lax3Proofs.WalkDistance Lax3Proofs.SyntaxLemmas Lax3Proofs.SemLocal
open Lax3Proofs.Separation Lax3Proofs.BCAlgebra Lax3Proofs.ScatterFml Lax3Proofs.ScatterCore

variable {L : ℕ}

/-! ### Small inversions and environment identities -/

/-- An unrestricted quantifier of distance rank `(k', q)` has a positive
quantifier budget and a body of distance rank one level in. The companion
of `Lax3Proofs.SemLocal.exists_drank_of_exL` for the other binder. -/
private theorem exists_drank_of_exU {k k' q : ℕ} {φ : DistFO L (k + 1)}
    (h : DRank k' q (DistFO.exU φ)) : ∃ q', q = q' + 1 ∧ DRank (k' + 1) q' φ := by
  cases h with
  | exU h => exact ⟨_, rfl, h⟩

/-- At arity zero a binder makes the constant environment: the newly
bound variable is the only one there is to read. -/
private theorem snoc_zero {n : ℕ} (m : Fin 0 → Fin n) (x : Fin n) :
    (Fin.snoc m x : Fin (0 + 1) → Fin n) = fun _ => x := by
  funext i
  rfl

/-- A guard over the whole context is no guard at all. -/
private theorem exists_mem_univ_iff {k : ℕ} (P : Fin k → Prop) :
    (∃ i ∈ (Finset.univ : Finset (Fin k)), P i) ↔ ∃ i, P i := by
  simp

/-! ### The local formula of a truth pattern

Once the truth values of the scatter atoms are fixed, a boolean
combination of local formulas and scatter sentences becomes a boolean
combination of local formulas, and that collapses to a single local
formula — the one a quantifier is put back in front of.
-/

/-- The single formula a truth pattern collapses a boolean combination
to: `BCAlgebra.collapse` read back inside the logic, with
`Separation.alwaysTrue`, negation and conjunction for the connectives. -/
private def patternFml {k : ℕ} (hk : 1 ≤ k) (τ : ScatterSentence L → Bool)
    (b : BC (DistFO L k ⊕ ScatterSentence L)) : DistFO L k :=
  interp (alwaysTrue hk) DistFO.not DistFO.and (collapse τ b)

/-- The collapse is sound: it holds exactly when the collapsed
combination evaluates to true. -/
private theorem sat_patternFml {n k : ℕ} {G : SimpleGraph (Fin n)} {col : Coloring n L}
    (hk : 1 ≤ k) (τ : ScatterSentence L → Bool)
    (b : BC (DistFO L k ⊕ ScatterSentence L)) (m : Fin k → Fin n) :
    Sat G col m (patternFml hk τ b) ↔ BC.eval (Sat G col m) (collapse τ b) :=
  eval_interp sat_alwaysTrue (fun x => sat_not x) (fun x y => sat_and x y) _

/-- Locality and distance rank travel through the collapse: they hold at
the always-true atom, are closed under negation and conjunction, and hold
at every left atom of the combination by hypothesis. -/
private theorem isLocal_drank_patternFml {k k' q : ℕ} (hk : 1 ≤ k)
    (τ : ScatterSentence L → Bool) (b : BC (DistFO L k ⊕ ScatterSentence L))
    (hl : ∀ ψ : DistFO L k, Sum.inl ψ ∈ b.atoms → IsLocal ψ ∧ DRank k' q ψ) :
    IsLocal (patternFml hk τ b) ∧ DRank k' q (patternFml hk τ b) :=
  interp_prop ⟨isLocal_alwaysTrue hk, drank_alwaysTrue hk k' q⟩
    (fun x hx => ⟨(isLocal_not x).mpr hx.1, .not hx.2⟩)
    (fun x y hx hy => ⟨(isLocal_and x y).mpr ⟨hx.1, hy.1⟩, .and hx.2 hy.2⟩) _
    fun a ha => hl a (mem_atoms_collapse.mp ha)

/-! ### The atomic cases -/

/-- An atom is its own boolean combination. -/
private theorem exists_bc_atom {k q : ℕ} (choice : ScatterChoice) {φ : DistFO L k}
    (hloc : IsLocal φ) (hφ : DRank k q φ) :
    ∃ b : BC (DistFO L k ⊕ ScatterSentence L),
      (∀ ψ : DistFO L k, Sum.inl ψ ∈ b.atoms → IsLocal ψ ∧ DRank k q ψ) ∧
      (∀ σ : ScatterSentence L, Sum.inr σ ∈ b.atoms → σ.DRank k q) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
        Sat G col m φ ↔
          b.eval (Sum.elim (Sat G col m) (ScatterSentence.Sat choice G col)) := by
  refine ⟨BC.atom (Sum.inl φ), ?_, ?_, fun n G col m => Iff.rfl⟩
  · intro ψ hψ
    rw [atoms_atom, List.mem_singleton] at hψ
    obtain rfl := Sum.inl_injective hψ
    exact ⟨hloc, hφ⟩
  · intro σ hσ
    rw [atoms_atom, List.mem_singleton] at hσ
    exact absurd hσ (by simp)

/-! ### The local-quantifier step

The scatter atoms of the body are pulled outside the quantifier, each
pattern's local remainder is collapsed to one formula, and the quantifier
— same radius, same guard set — is put back in front of it.
-/

/-- **The local-quantifier step.** A boolean combination equivalent to
the body of a local quantifier, at rank `(k + 1, q)`, yields one
equivalent to the quantified formula, at rank `(k, q + 1)`. -/
private theorem exL_step (choice : ScatterChoice) {k q r : ℕ} (g : Finset (Fin k))
    (hr : r ≤ rhoPlus (k + 1) q)
    (bc : BC (DistFO L (k + 1) ⊕ ScatterSentence L))
    (hl : ∀ ψ : DistFO L (k + 1), Sum.inl ψ ∈ bc.atoms → IsLocal ψ ∧ DRank (k + 1) q ψ)
    (hs : ∀ σ : ScatterSentence L, Sum.inr σ ∈ bc.atoms → σ.DRank (k + 1) q) :
    ∃ b : BC (DistFO L k ⊕ ScatterSentence L),
      (∀ ψ : DistFO L k, Sum.inl ψ ∈ b.atoms → IsLocal ψ ∧ DRank k (q + 1) ψ) ∧
      (∀ σ : ScatterSentence L, Sum.inr σ ∈ b.atoms → σ.DRank k (q + 1)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
        (∃ v, (∃ i ∈ g, WithinDist G r (m i) v) ∧
            bc.eval (Sum.elim (Sat G col (Fin.snoc m v))
              (ScatterSentence.Sat choice G col))) ↔
          b.eval (Sum.elim (Sat G col m) (ScatterSentence.Sat choice G col)) := by
  classical
  have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have hchi : ∀ τ, IsLocal (patternFml hk1 τ bc) ∧ DRank (k + 1) q (patternFml hk1 τ bc) :=
    fun τ => isLocal_drank_patternFml hk1 τ bc hl
  refine ⟨pullOut bc fun τ => BC.atom (DistFO.exL r g (patternFml hk1 τ bc)), ?_, ?_, ?_⟩
  · intro ψ hψ
    obtain ⟨τ, -, hτ⟩ := mem_atoms_pullOut_left.mp hψ
    rw [atoms_atom, List.mem_singleton] at hτ
    subst hτ
    exact ⟨(isLocal_exL r g _).mpr (hchi τ).1, .exL (hchi τ).2 hr⟩
  · intro σ hσ
    exact ScatterSentence.DRank.antidiagonal (hs σ (mem_atoms_pullOut_right hσ))
  · intro n G col m
    have hw : ∀ τ, BC.eval (Sat G col m) (BC.atom (DistFO.exL r g (patternFml hk1 τ bc))) ↔
        ∃ v : {v : Fin n // ∃ i ∈ g, WithinDist G r (m i) v},
          BC.eval (Sat G col (Fin.snoc m ↑v)) (collapse τ bc) := by
      intro τ
      rw [eval_atom, sat_exL]
      exact ⟨fun ⟨v, hv, h⟩ => ⟨⟨v, hv⟩, (sat_patternFml hk1 τ bc _).mp h⟩,
        fun ⟨⟨v, hv⟩, h⟩ => ⟨v, hv, (sat_patternFml hk1 τ bc _).mpr h⟩⟩
    rw [← eval_pullOut bc _ (fun (v : {v : Fin n // ∃ i ∈ g, WithinDist G r (m i) v}) =>
      Sat G col (Fin.snoc m ↑v)) (ScatterSentence.Sat choice G col) (Sat G col m) hw]
    exact ⟨fun ⟨v, hv, h⟩ => ⟨⟨v, hv⟩, h⟩, fun ⟨⟨v, hv⟩, h⟩ => ⟨v, hv, h⟩⟩

/-! ### The sentence case

With no free variable there is no guard, and the source's answer is a
scatter sentence demanding a single witness.
-/

/-- A scatter sentence demanding one witness says exactly that its
formula is satisfiable: the distinguished maximal scattered subset of a
nonempty set is nonempty — otherwise a vertex of the set could be added
to it — and it is a subset of that set. -/
private theorem scatterSentence_sat_one_iff (choice : ScatterChoice) {n : ℕ}
    (G : SimpleGraph (Fin n)) (col : Coloring n L) (r : ℕ) (β : DistFO L 1) :
    ScatterSentence.Sat choice G col ⟨r, β, 1⟩ ↔ ∃ x, Sat G col (fun _ => x) β := by
  rw [scatterSentence_sat_iff]
  obtain ⟨S, hSX, hSmax, hScard⟩ := choice.spec G r {a | Sat G col (fun _ => a) β}
  constructor
  · intro h
    rw [← hScard] at h
    obtain ⟨x, hx⟩ := (Set.ncard_pos (Set.toFinite S)).mp h
    exact ⟨x, hSX hx⟩
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs, -⟩ := exists_withinDist_of_maximal hSmax hx
    rw [← hScard]
    exact (Set.ncard_pos (Set.toFinite S)).mpr ⟨s, hs⟩

/-- The scatter sentence of the sentence case has the distance rank the
theorem demands: one witness is at most `0 + (q + 1)`, and at the rank
witness `i = 1` its formula is local of distance rank `(1, q)` and its
radius sits at the low end of the source's window. -/
private theorem drank_scatterSentence_one {q : ℕ} {β : DistFO L 1}
    (hloc : IsLocal β) (hβ : DRank 1 q β) :
    (⟨4 * rhoMinus 1 q, β, 1⟩ : ScatterSentence L).DRank 0 (q + 1) := by
  rw [scatterSentence_drank_iff]
  refine ⟨?_, 1, le_rfl, by omega, hloc, hβ, le_rfl, Nat.mul_le_mul (by norm_num) le_rfl⟩
  show (1 : ℕ) ≤ 0 + (q + 1)
  omega

/-- **The sentence case.** A boolean combination equivalent to the body
of an unrestricted quantifier over an empty context, at rank `(1, q)`,
yields one equivalent to the quantified sentence, at rank `(0, q + 1)`:
each pattern contributes the scatter sentence demanding a single witness
of its collapsed formula. -/
private theorem exU_zero_step (choice : ScatterChoice) {q : ℕ}
    (bc : BC (DistFO L 1 ⊕ ScatterSentence L))
    (hl : ∀ ψ : DistFO L 1, Sum.inl ψ ∈ bc.atoms → IsLocal ψ ∧ DRank 1 q ψ)
    (hs : ∀ σ : ScatterSentence L, Sum.inr σ ∈ bc.atoms → σ.DRank 1 q) :
    ∃ b : BC (DistFO L 0 ⊕ ScatterSentence L),
      (∀ ψ : DistFO L 0, Sum.inl ψ ∈ b.atoms → IsLocal ψ ∧ DRank 0 (q + 1) ψ) ∧
      (∀ σ : ScatterSentence L, Sum.inr σ ∈ b.atoms → σ.DRank 0 (q + 1)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin 0 → Fin n),
        (∃ x, bc.eval (Sum.elim (Sat G col (fun _ => x))
            (ScatterSentence.Sat choice G col))) ↔
          b.eval (Sum.elim (Sat G col m) (ScatterSentence.Sat choice G col)) := by
  classical
  have hone : (1 : ℕ) ≤ 1 := le_rfl
  have hchi : ∀ τ, IsLocal (patternFml hone τ bc) ∧ DRank 1 q (patternFml hone τ bc) :=
    fun τ => isLocal_drank_patternFml hone τ bc hl
  refine ⟨bigOr ((assignments bc).map fun τ =>
    (map Sum.inr (patternBC τ bc)).and
      (BC.atom (Sum.inr ⟨4 * rhoMinus 1 q, patternFml hone τ bc, 1⟩))), ?_, ?_, ?_⟩
  · intro ψ hψ
    exfalso
    obtain ⟨b, hb, hψb⟩ := mem_atoms_bigOr.mp hψ
    obtain ⟨τ, -, rfl⟩ := List.mem_map.mp hb
    rw [atoms_and, List.mem_append, atoms_map, atoms_atom, List.mem_singleton] at hψb
    rcases hψb with h | h
    · obtain ⟨σ, -, hσ⟩ := List.mem_map.mp h
      exact absurd hσ (by simp)
    · exact absurd h (by simp)
  · intro σ hσ
    obtain ⟨b, hb, hσb⟩ := mem_atoms_bigOr.mp hσ
    obtain ⟨τ, -, rfl⟩ := List.mem_map.mp hb
    rw [atoms_and, List.mem_append, atoms_map, atoms_atom, List.mem_singleton] at hσb
    rcases hσb with h | h
    · obtain ⟨σ', hσ', hσ''⟩ := List.mem_map.mp h
      rw [← Sum.inr_injective hσ'']
      exact ScatterSentence.DRank.antidiagonal (hs σ' (mem_atoms_patternBC.mp hσ'))
    · rw [Sum.inr_injective h]
      exact drank_scatterSentence_one (hchi τ).1 (hchi τ).2
  · intro n G col m
    rw [exists_eval_sum_iff bc (fun (x : Fin n) => Sat G col (fun _ => x))
      (ScatterSentence.Sat choice G col), eval_bigOr]
    simp only [List.mem_map, exists_exists_and_eq_and, eval_and, eval_map_inr, eval_atom,
      Sum.elim_inr]
    refine exists_congr fun τ => and_congr_right fun _ => and_congr_right fun _ => ?_
    rw [scatterSentence_sat_one_iff]
    exact exists_congr fun x => (sat_patternFml hone τ bc fun _ => x).symm

/-! ### The far half of an unrestricted quantifier

A witness further than ρ⁻(k+1, q) from the whole tuple is separated from
it by `Separation.separate`; what is left of the witness is a
one-variable capsule, which `FarQuant.farQuant` discharges.
-/

/-- **The far half.** With at least one free variable, a boolean
combination equivalent to the body of an unrestricted quantifier at rank
`(k + 1, q)` yields one, at rank `(k, q + 1)`, equivalent to "the body
holds at some witness far from the whole tuple". -/
private theorem exU_far_step (choice : ScatterChoice) {k q : ℕ} (hk : 1 ≤ k)
    (bc : BC (DistFO L (k + 1) ⊕ ScatterSentence L))
    (hl : ∀ ψ : DistFO L (k + 1), Sum.inl ψ ∈ bc.atoms → IsLocal ψ ∧ DRank (k + 1) q ψ)
    (hs : ∀ σ : ScatterSentence L, Sum.inr σ ∈ bc.atoms → σ.DRank (k + 1) q) :
    ∃ b : BC (DistFO L k ⊕ ScatterSentence L),
      (∀ ψ : DistFO L k, Sum.inl ψ ∈ b.atoms → IsLocal ψ ∧ DRank k (q + 1) ψ) ∧
      (∀ σ : ScatterSentence L, Sum.inr σ ∈ b.atoms → σ.DRank k (q + 1)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
        (∃ x, (∀ i, ¬ WithinDist G (rhoMinus (k + 1) q) (m i) x) ∧
            bc.eval (Sum.elim (Sat G col (Fin.snoc m x))
              (ScatterSentence.Sat choice G col))) ↔
          b.eval (Sum.elim (Sat G col m) (ScatterSentence.Sat choice G col)) := by
  classical
  have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have hchi : ∀ τ, IsLocal (patternFml hk1 τ bc) ∧ DRank (k + 1) q (patternFml hk1 τ bc) :=
    fun τ => isLocal_drank_patternFml hk1 τ bc hl
  -- the capsule split of the context: the old tuple, and the bound variable alone
  have hinj₁ : Function.Injective (Fin.castSucc : Fin k → Fin (k + 1)) :=
    Fin.castSucc_injective k
  have hinj₂ : Function.Injective (fun _ : Fin 1 => Fin.last k) :=
    fun i j _ => Subsingleton.elim i j
  have hdis : ∀ (i : Fin k) (j : Fin 1),
      (Fin.castSucc i : Fin (k + 1)) ≠ (fun _ : Fin 1 => Fin.last k) j :=
    fun i _ => Fin.castSucc_ne_last i
  have hcov : ∀ v : Fin (k + 1), (∃ i, (Fin.castSucc i : Fin (k + 1)) = v) ∨
      ∃ j : Fin 1, (fun _ : Fin 1 => Fin.last k) j = v := by
    intro v
    induction v using Fin.lastCases with
    | last => exact Or.inr ⟨0, rfl⟩
    | cast j => exact Or.inl ⟨j, rfl⟩
  choose P hPprop hPeq using fun τ =>
    separate (patternFml hk1 τ bc) (hchi τ).1 (hchi τ).2 hk le_rfl
      Fin.castSucc (fun _ : Fin 1 => Fin.last k) hinj₁ hinj₂ hdis hcov
  -- `farQuant`, totalized so that the chosen combination reads only the capsule
  have hfar : ∀ β : DistFO L 1, ∃ bcβ : BC (DistFO L k ⊕ ScatterSentence L),
      IsLocal β → DRank (k + 1) q β →
        (∀ ψ : DistFO L k, Sum.inl ψ ∈ bcβ.atoms → IsLocal ψ ∧ DRank k (q + 1) ψ) ∧
        (∀ σ : ScatterSentence L, Sum.inr σ ∈ bcβ.atoms → σ.DRank k (q + 1)) ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
          ((∃ x, (∀ i, ¬ WithinDist G (rhoMinus (k + 1) q) (m i) x) ∧
              Sat G col (fun _ => x) β) ↔
            bcβ.eval (Sum.elim (Sat G col m) (ScatterSentence.Sat choice G col))) := by
    intro β
    by_cases h : IsLocal β ∧ DRank (k + 1) q β
    · obtain ⟨bcβ, h₁, h₂, h₃⟩ := FarQuant.farQuant choice hk β h.1 h.2
      exact ⟨bcβ, fun _ _ => ⟨h₁, h₂, h₃⟩⟩
    · exact ⟨BC.tru, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h⟩
  choose fq hfq using hfar
  refine ⟨bigOr ((assignments bc).map fun τ =>
    (map Sum.inr (patternBC τ bc)).and
      (bigOr ((P τ).map fun p => (BC.atom (Sum.inl p.1)).and (fq p.2)))), ?_, ?_, ?_⟩
  · intro ψ hψ
    obtain ⟨b, hb, hψb⟩ := mem_atoms_bigOr.mp hψ
    obtain ⟨τ, -, rfl⟩ := List.mem_map.mp hb
    rw [atoms_and, List.mem_append, atoms_map] at hψb
    rcases hψb with h | h
    · obtain ⟨σ, -, hσ⟩ := List.mem_map.mp h
      exact absurd hσ (by simp)
    · obtain ⟨b', hb', hψb'⟩ := mem_atoms_bigOr.mp h
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb'
      obtain ⟨h₁loc, h₁rank, h₂loc, h₂rank⟩ := hPprop τ p hp
      rw [atoms_and, List.mem_append, atoms_atom, List.mem_singleton] at hψb'
      rcases hψb' with h' | h'
      · obtain rfl := Sum.inl_injective h'
        exact ⟨h₁loc, DRank.antidiagonal h₁rank⟩
      · exact (hfq p.2 h₂loc h₂rank).1 ψ h'
  · intro σ hσ
    obtain ⟨b, hb, hσb⟩ := mem_atoms_bigOr.mp hσ
    obtain ⟨τ, -, rfl⟩ := List.mem_map.mp hb
    rw [atoms_and, List.mem_append, atoms_map] at hσb
    rcases hσb with h | h
    · obtain ⟨σ', hσ', hσ''⟩ := List.mem_map.mp h
      rw [← Sum.inr_injective hσ'']
      exact ScatterSentence.DRank.antidiagonal (hs σ' (mem_atoms_patternBC.mp hσ'))
    · obtain ⟨b', hb', hσb'⟩ := mem_atoms_bigOr.mp h
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb'
      obtain ⟨-, -, h₂loc, h₂rank⟩ := hPprop τ p hp
      rw [atoms_and, List.mem_append, atoms_atom, List.mem_singleton] at hσb'
      rcases hσb' with h' | h'
      · exact absurd h' (by simp)
      · exact (hfq p.2 h₂loc h₂rank).2.1 σ h'
  · intro n G col m
    -- the separation, at a far witness
    have hsep : ∀ (τ : ScatterSentence L → Bool) (x : Fin n),
        (∀ i, ¬ WithinDist G (rhoMinus (k + 1) q) (m i) x) →
        (Sat G col (Fin.snoc m x) (patternFml hk1 τ bc) ↔
          ∃ p ∈ P τ, Sat G col m p.1 ∧ Sat G col (fun _ => x) p.2) := by
      intro τ x hx
      have h := hPeq τ n G col (Fin.snoc m x) (by
        intro i j
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact hx i)
      have e₁ : (Fin.snoc m x : Fin (k + 1) → Fin n) ∘ Fin.castSucc = m := by
        funext i; simp
      have e₂ : (Fin.snoc m x : Fin (k + 1) → Fin n) ∘ (fun _ : Fin 1 => Fin.last k) =
          fun _ => x := by
        funext i; simp
      rw [e₁, e₂] at h
      exact h
    have hpack : (∃ x, (∀ i, ¬ WithinDist G (rhoMinus (k + 1) q) (m i) x) ∧
          bc.eval (Sum.elim (Sat G col (Fin.snoc m x))
            (ScatterSentence.Sat choice G col))) ↔
        ∃ v : {x : Fin n // ∀ i, ¬ WithinDist G (rhoMinus (k + 1) q) (m i) x},
          bc.eval (Sum.elim (Sat G col (Fin.snoc m ↑v))
            (ScatterSentence.Sat choice G col)) :=
      ⟨fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, h⟩, fun ⟨⟨x, hx⟩, h⟩ => ⟨x, hx, h⟩⟩
    have hunpack : ∀ τ : ScatterSentence L → Bool,
        (∃ v : {x : Fin n // ∀ i, ¬ WithinDist G (rhoMinus (k + 1) q) (m i) x},
            BC.eval (Sat G col (Fin.snoc m ↑v)) (collapse τ bc)) ↔
          ∃ x, (∀ i, ¬ WithinDist G (rhoMinus (k + 1) q) (m i) x) ∧
            BC.eval (Sat G col (Fin.snoc m x)) (collapse τ bc) :=
      fun τ => ⟨fun ⟨⟨x, hx⟩, h⟩ => ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, h⟩⟩
    rw [hpack, exists_eval_sum_iff bc
      (fun (v : {x : Fin n // ∀ i, ¬ WithinDist G (rhoMinus (k + 1) q) (m i) x}) =>
        Sat G col (Fin.snoc m ↑v)) (ScatterSentence.Sat choice G col), eval_bigOr]
    simp only [List.mem_map, exists_exists_and_eq_and, eval_and, eval_map_inr]
    refine exists_congr fun τ => and_congr_right fun _ => and_congr_right fun _ => ?_
    rw [hunpack τ, eval_bigOr]
    simp only [List.mem_map, exists_exists_and_eq_and, eval_and, eval_atom, Sum.elim_inl]
    constructor
    · rintro ⟨x, hx, hev⟩
      rw [← sat_patternFml hk1 τ bc (Fin.snoc m x), hsep τ x hx] at hev
      obtain ⟨p, hp, h₁, h₂⟩ := hev
      obtain ⟨-, -, h₂loc, h₂rank⟩ := hPprop τ p hp
      exact ⟨p, hp, h₁, ((hfq p.2 h₂loc h₂rank).2.2 n G col m).mp ⟨x, hx, h₂⟩⟩
    · rintro ⟨p, hp, h₁, h₂⟩
      obtain ⟨-, -, h₂loc, h₂rank⟩ := hPprop τ p hp
      obtain ⟨x, hx, h₂'⟩ := ((hfq p.2 h₂loc h₂rank).2.2 n G col m).mpr h₂
      refine ⟨x, hx, ?_⟩
      rw [← sat_patternFml hk1 τ bc (Fin.snoc m x), hsep τ x hx]
      exact ⟨p, hp, h₁, h₂'⟩

/-! ### The unrestricted-quantifier step -/

/-- **The unrestricted-quantifier step at positive arity.** The witness
is split at radius ρ⁻(k+1, q): near the tuple the quantifier is a local
one guarded over the whole context, far from it the far half applies. -/
private theorem exU_pos_step (choice : ScatterChoice) {k q : ℕ} (hk : 1 ≤ k)
    (bc : BC (DistFO L (k + 1) ⊕ ScatterSentence L))
    (hl : ∀ ψ : DistFO L (k + 1), Sum.inl ψ ∈ bc.atoms → IsLocal ψ ∧ DRank (k + 1) q ψ)
    (hs : ∀ σ : ScatterSentence L, Sum.inr σ ∈ bc.atoms → σ.DRank (k + 1) q) :
    ∃ b : BC (DistFO L k ⊕ ScatterSentence L),
      (∀ ψ : DistFO L k, Sum.inl ψ ∈ b.atoms → IsLocal ψ ∧ DRank k (q + 1) ψ) ∧
      (∀ σ : ScatterSentence L, Sum.inr σ ∈ b.atoms → σ.DRank k (q + 1)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
        (∃ x, bc.eval (Sum.elim (Sat G col (Fin.snoc m x))
            (ScatterSentence.Sat choice G col))) ↔
          b.eval (Sum.elim (Sat G col m) (ScatterSentence.Sat choice G col)) := by
  classical
  obtain ⟨bn, hnl, hns, hneq⟩ :=
    exL_step choice (Finset.univ : Finset (Fin k)) (rhoMinus_le_rhoPlus (k + 1) q) bc hl hs
  obtain ⟨bf, hfl, hfs, hfeq⟩ := exU_far_step choice hk bc hl hs
  refine ⟨or bn bf, ?_, ?_, fun n G col m => ?_⟩
  · intro ψ hψ
    rw [atoms_or, List.mem_append] at hψ
    exact hψ.elim (hnl ψ) (hfl ψ)
  · intro σ hσ
    rw [atoms_or, List.mem_append] at hσ
    exact hσ.elim (hns σ) (hfs σ)
  · rw [eval_or, ← hneq n G col m, ← hfeq n G col m]
    constructor
    · rintro ⟨x, hx⟩
      by_cases hnear : ∃ i, WithinDist G (rhoMinus (k + 1) q) (m i) x
      · exact Or.inl ⟨x, (exists_mem_univ_iff _).mpr hnear, hx⟩
      · exact Or.inr ⟨x, not_exists.mp hnear, hx⟩
    · rintro (⟨x, -, hx⟩ | ⟨x, -, hx⟩) <;> exact ⟨x, hx⟩

/-- **The unrestricted-quantifier step.** At arity zero the sentence case
applies, at positive arity the near/far split. -/
private theorem exU_step (choice : ScatterChoice) {k q : ℕ}
    (bc : BC (DistFO L (k + 1) ⊕ ScatterSentence L))
    (hl : ∀ ψ : DistFO L (k + 1), Sum.inl ψ ∈ bc.atoms → IsLocal ψ ∧ DRank (k + 1) q ψ)
    (hs : ∀ σ : ScatterSentence L, Sum.inr σ ∈ bc.atoms → σ.DRank (k + 1) q) :
    ∃ b : BC (DistFO L k ⊕ ScatterSentence L),
      (∀ ψ : DistFO L k, Sum.inl ψ ∈ b.atoms → IsLocal ψ ∧ DRank k (q + 1) ψ) ∧
      (∀ σ : ScatterSentence L, Sum.inr σ ∈ b.atoms → σ.DRank k (q + 1)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
        (∃ x, bc.eval (Sum.elim (Sat G col (Fin.snoc m x))
            (ScatterSentence.Sat choice G col))) ↔
          b.eval (Sum.elim (Sat G col m) (ScatterSentence.Sat choice G col)) := by
  obtain _ | k := k
  · obtain ⟨b, hbl, hbs, hbeq⟩ := exU_zero_step choice bc hl hs
    refine ⟨b, hbl, hbs, fun n G col m => ?_⟩
    rw [← hbeq n G col m]
    refine exists_congr fun x => ?_
    rw [snoc_zero m x]
  · exact exU_pos_step choice (Nat.succ_le_succ (Nat.zero_le k)) bc hl hs

/-! ### The induction -/

/-- **The locality theorem, in the form the induction proves.** The
induction is on the formula, with the rank quantified inside so that the
induction hypothesis is available at the rank of the subformula, and with
the boolean combination chosen before the graph and the environment are
fixed. -/
private theorem exists_bc (choice : ScatterChoice) :
    ∀ {k : ℕ} (φ : DistFO L k) (q : ℕ), DRank k q φ →
      ∃ b : BC (DistFO L k ⊕ ScatterSentence L),
        (∀ ψ : DistFO L k, Sum.inl ψ ∈ b.atoms → IsLocal ψ ∧ DRank k q ψ) ∧
        (∀ σ : ScatterSentence L, Sum.inr σ ∈ b.atoms → σ.DRank k q) ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
          Sat G col m φ ↔
            b.eval (Sum.elim (Sat G col m) (ScatterSentence.Sat choice G col)) := by
  intro k φ
  induction φ with
  | adj i j => exact fun q hφ => exists_bc_atom choice (isLocal_adj i j) hφ
  | eq i j => exact fun q hφ => exists_bc_atom choice (isLocal_eq i j) hφ
  | color c i => exact fun q hφ => exists_bc_atom choice (isLocal_color c i) hφ
  | distLe r i j => exact fun q hφ => exists_bc_atom choice (isLocal_distLe r i j) hφ
  | distColorLt r c i => exact fun q hφ => exists_bc_atom choice (isLocal_distColorLt r c i) hφ
  | not ψ ih =>
    intro q hφ
    obtain ⟨b, hbl, hbs, hbeq⟩ := ih q (drank_of_not hφ)
    refine ⟨b.not, fun χ hχ => hbl χ (by rwa [atoms_not] at hχ),
      fun σ hσ => hbs σ (by rwa [atoms_not] at hσ), fun n G col m => ?_⟩
    rw [sat_not, eval_not, hbeq n G col m]
  | and ψ χ ihψ ihχ =>
    intro q hφ
    obtain ⟨b₁, hb₁l, hb₁s, hb₁eq⟩ := ihψ q (drank_of_and_left hφ)
    obtain ⟨b₂, hb₂l, hb₂s, hb₂eq⟩ := ihχ q (drank_of_and_right hφ)
    refine ⟨b₁.and b₂, ?_, ?_, fun n G col m => ?_⟩
    · intro ζ hζ
      rw [atoms_and, List.mem_append] at hζ
      exact hζ.elim (hb₁l ζ) (hb₂l ζ)
    · intro σ hσ
      rw [atoms_and, List.mem_append] at hσ
      exact hσ.elim (hb₁s σ) (hb₂s σ)
    · rw [sat_and, eval_and, hb₁eq n G col m, hb₂eq n G col m]
  | exU ψ ih =>
    intro q hφ
    obtain ⟨q₀, rfl, hψ⟩ := exists_drank_of_exU hφ
    obtain ⟨bc, hcl, hcs, hceq⟩ := ih q₀ hψ
    obtain ⟨b, hbl, hbs, hbeq⟩ := exU_step choice bc hcl hcs
    refine ⟨b, hbl, hbs, fun n G col m => ?_⟩
    rw [sat_exU, ← hbeq n G col m]
    exact exists_congr fun v => hceq n G col (Fin.snoc m v)
  | exL r g ψ ih =>
    intro q hφ
    obtain ⟨q₀, rfl, hψ, hrq⟩ := exists_drank_of_exL hφ
    obtain ⟨bc, hcl, hcs, hceq⟩ := ih q₀ hψ
    obtain ⟨b, hbl, hbs, hbeq⟩ := exL_step choice g hrq bc hcl hcs
    refine ⟨b, hbl, hbs, fun n G col m => ?_⟩
    rw [sat_exL, ← hbeq n G col m]
    exact exists_congr fun v => and_congr_right fun _ => hceq n G col (Fin.snoc m v)

/-! ### The two theorems -/

/--
---
conclusion: Lax3.Locality.locality
---
**The locality theorem** (Theorem 1 of arXiv:2606.23180): every formula
of distance rank `(k, q)` is equivalent to a boolean combination of local
formulas and scatter sentences, all of distance rank `(k, q)`.

# Proof strategy

Structural induction on the formula, the rank read off by inverting the
`DRank` derivation at each step. Atoms are their own combinations,
boolean connectives compose the combinations of their parts, and both
quantifiers first apply the induction hypothesis to the body and then
pull the scatter sentences — being sentences, they do not see the bound
variable — outside the quantifier, leaving one local formula per truth
pattern of them. A local quantifier is then simply put back in front of
that formula. An unrestricted quantifier is the source's real case: over
an empty context it becomes a scatter sentence with a single witness,
and otherwise the witness is split into a near one, which is a local
quantification guarded over the whole tuple, and a far one, which the
separation lemma and the far-quantification lemma turn into local
formulas and scatter sentences. See the module docstring for the map of
the imported pieces.
-/
theorem locality (choice : ScatterChoice) {k q : ℕ} (φ : DistFO L k)
    (hφ : DRank k q φ) :
    ∃ b : BC (DistFO L k ⊕ ScatterSentence L),
      (∀ ψ : DistFO L k, Sum.inl ψ ∈ b.atoms → IsLocal ψ ∧ DRank k q ψ) ∧
      (∀ σ : ScatterSentence L, Sum.inr σ ∈ b.atoms → σ.DRank k q) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
        Sat G col m φ ↔
          b.eval (Sum.elim (Sat G col m) (ScatterSentence.Sat choice G col)) :=
  exists_bc choice φ q hφ

/--
---
conclusion: Lax3.NormalForm.normalForm
---
**The normal form for distance logic** (Corollary 7 of
arXiv:2606.23180): for `q ≥ 1`, every formula of distance rank `(k, q)`
is equivalent to a boolean combination of local formulas of distance rank
`(k, q)` and the written-out sentences "there are `t` vertices, pairwise
at distance larger than `r`, all satisfying `β`".

# Proof strategy

The claim `Lax3.Locality.locality` at the maximum-size scatter choice,
with the same boolean combination. Its discharge is `locality` above.
With that choice a scatter sentence is definable in
the logic — `Lax3Proofs.ScatterFml.sat_scatterFml` — so replacing each
scatter atom's evaluation by satisfaction of `scatterFml` changes no
truth value, and `Lax3Proofs.BCAlgebra.eval_congr` carries the
replacement through the combination. The five conditions the corollary
states about a scatter atom are the five bridges of
`Lax3Proofs.ScatterFml` applied to the distance rank the locality theorem
already provides; `q ≥ 1` is used by exactly one of them, the one that
climbs the rank witness back to `(k + 1, q − 1)`.
-/
theorem normalForm {k q : ℕ} (hq : 1 ≤ q) (φ : DistFO L k) (hφ : DRank k q φ) :
    ∃ b : BC (DistFO L k ⊕ ScatterSentence L),
      (∀ ψ : DistFO L k, Sum.inl ψ ∈ b.atoms → IsLocal ψ ∧ DRank k q ψ) ∧
      (∀ σ : ScatterSentence L, Sum.inr σ ∈ b.atoms →
        σ.t ≤ k + q ∧ IsLocal σ.β ∧ DRank (k + 1) (q - 1) σ.β ∧
          σ.r ≤ rhoMinus k q ∧ SemanticallyLocal (σ.r / 4) σ.β) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
        Sat G col m φ ↔
          b.eval (Sum.elim (Sat G col m)
            (fun σ => Sat G col Fin.elim0 (scatterFml σ.r σ.t σ.β))) := by
  obtain ⟨b, hbl, hbs, hbeq⟩ := Lax3.Locality.locality maxChoice φ hφ
  refine ⟨b, hbl, fun σ hσ => ⟨t_le_of_drank (hbs σ hσ), isLocal_beta_of_drank (hbs σ hσ),
    drank_succ_pred_of_drank (hbs σ hσ) hq, r_le_rhoMinus_of_drank (hbs σ hσ),
    semanticallyLocal_div_four_of_drank (hbs σ hσ)⟩, fun n G col m => ?_⟩
  rw [hbeq n G col m]
  refine eval_congr b ?_
  rintro (ψ | σ) -
  · exact Iff.rfl
  · show ScatterSentence.Sat maxChoice G col σ ↔
      Sat G col Fin.elim0 (scatterFml σ.r σ.t σ.β)
    rw [sat_scatterFml]

end Lax3Proofs.Assembly
