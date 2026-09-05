import Lax3Proofs.SolveConcreteNames

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
variable {L : ℕ}

/-- Numeric facts used by the concrete passes. The following theorem supplies
all of them from one input-independent word coefficient. -/
structure ConcreteRoom (S : Setup L) (n B : ℕ) : Prop where
  one : 1 < B
  carrier : n < B
  square : n * n < B
  extra : n + 2 < B
  big : n * n + 2 * n + 1 < B
  depth : S.depth < B
  radius : 2 * S.R + 3 < B
  width : S.width < B
  history : n * S.depth * (2 * S.R + 2) < B
  palette : ∀ j ≤ S.depth, n * S.pal j < B
  formulas : ∀ j ≤ S.depth, n * (levelFml S j).length < B
  leaf : ∀ j ≤ S.depth, 2 ^ S.pal j * (concreteQdepth S + 1) < B
  atoms : ∀ j ≤ S.depth, concreteAtomBound (levelAtoms S j) < B
  top : concreteAtomBound (concreteTopAtoms S) < B
  cover : (2 * S.R + 6) * (n + 2) ^ 2 < B

theorem concreteRoom (S : Setup L) {n : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} (henc : EncodesGraph x n G) :
    ConcreteRoom S n (mcB (concreteWordQ S) x) := by
  have hcap := concreteCapacity_lt_mcB S henc
  obtain ⟨hn, hn2, hbig, hs, hmul⟩ := concreteCapacity_bounds S n
  obtain ⟨h4, hw, hd, hr, hh⟩ := concreteScale_static S
  have hstatic {v : ℕ} (hv : v ≤ concreteScale S) : v < mcB (concreteWordQ S) x :=
    lt_of_le_of_lt (hv.trans hs) hcap
  refine ⟨by omega, by omega, by omega, by omega, by omega,
    hstatic hd, hstatic hr, hstatic hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.mul_assoc]
    exact lt_of_le_of_lt (hmul _ hh) hcap
  · intro j hj
    exact lt_of_le_of_lt (hmul _ (concreteScale_level S hj).1) hcap
  · intro j hj
    exact lt_of_le_of_lt (hmul _ (concreteScale_level S hj).2.1) hcap
  · intro j hj
    exact hstatic (concreteScale_level S hj).2.2.2
  · intro j hj
    exact hstatic (concreteScale_level S hj).2.2.1
  · exact hstatic (concreteScale_top S)
  · have hcoef : 2 * S.R + 6 ≤ concreteScale S := by unfold concreteScale; omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hcoef) hcap

end Lax3Proofs.Prog
