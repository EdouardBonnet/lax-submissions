import Lax3Proofs.SolveCodegen
import Lax3Proofs.SolveStageCharge
import Lax3Proofs.SolveCovLoad

/-!
# Uniform final compilation

The actual linear front/back ends surround the recursive budget. One natural
constant then pays the inferred memory layout and the uniform time envelope,
with exactly the endorsed theorem's program/constant/time quantifier order.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Compile
open Lax11.GraphEncoding Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3.ScatterSentences

theorem codeLayout_const (c : Com) : (codeLayout c).const = 10 := rfl

open Classical in
/-- Parsing, materialization, deduplication, root loading, and the top stage
all fit one fixed linear coefficient around the recursive budget. -/
theorem mcK_rootStages_le {L n : ℕ} (G : SimpleGraph (Fin n))
    (as : List (ScatterSentence L)) (e K : ℕ) {x : List ℕ} (hx : EncodesGraph x n G) :
    mcK (fun y => matK y + ((csrLoadK y + (11 * n + 8)) +
      (K + (topScatK n (∑ v : Fin n, G.degree v) as + e)))) x ≤
      K + (104 + 2 * topStageCoeff as + e) * (x.length + 1) := by
  have hW := Headline.graphWeight_le_length hx
  change n + G.edgeSet.ncard ≤ x.length at hW
  have hns : (∑ v : Fin n, G.degree v) = 2 * G.edgeSet.ncard := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, edgeFinset_card_eq_ncard]
  have hnorm : n + (∑ v : Fin n, G.degree v) + 1 ≤ 2 * (x.length + 1) := by
    rw [hns]
    omega
  have htop : topScatK n (∑ v : Fin n, G.degree v) as ≤
      2 * topStageCoeff as * (x.length + 1) := by
    have h := (topScatK_le_stageCoeff n (∑ v : Fin n, G.degree v) as).trans
      (Nat.mul_le_mul_left (topStageCoeff as) hnorm)
    nlinarith only [h]
  have he : e ≤ e * (x.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold mcK matK csrLoadK
  nlinarith only [hW, htop, he]

open Classical in
/-- Choose the final program, common word-room constant, and time function
before all graphs and word lengths. The inferred compiler layout and the
real-valued time coefficient fit into the same natural constant. -/
theorem exists_machine_of_uniformSolve (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ε : ℝ) (ord : CoverSpec.OrderingRoutine)
    (q : ℕ) (ext : List ℕ → String → ℕ) (solveCom : Com)
    (Ks : (n : ℕ) → SimpleGraph (Fin n) → List ℕ → ℕ)
    (hq : 1 ≤ q) (hnw : solveCom.NoWrite)
    (hextOff : ∀ n (G : SimpleGraph (Fin n)) x, EncodesGraph x n G → ext x "off" = vertexCount x + 1)
    (hextTgt : ∀ n (G : SimpleGraph (Fin n)) x, EncodesGraph x n G → ext x "tgt" = 2 * edgeCount x)
    (hsolve : ∀ n (G : SimpleGraph (Fin n)), C n G → ∀ c w,
      SolveSpec C hC φ ord G c w q ext solveCom (Ks n G))
    (cf : ℝ) (T : List ℕ → ℕ)
    (hT : ∀ x, (T x : ℝ) ≤ cf * ((x.length : ℝ) + 1) ^ (1 + ε))
    (hK : ∀ n (G : SimpleGraph (Fin n)), C n G → ∀ x, EncodesGraph x n G →
      (codeLayout (mcCom solveCom)).const * mcK (Ks n G) x ≤ T x) :
    ∃ (p : Lax67.Ram.Program) (c : ℕ) (T : List ℕ → ℕ),
      (∀ x : List ℕ, (T x : ℝ) ≤ c * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
        Lax67.RamComputes.ComputesInTime w p
          {x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ^ 2 ≤ 2 ^ w}
          (fun _ => if Lax3.FirstOrder.Sat G Fin.elim0 φ then [1] else [0]) T := by
  let lay := codeLayout (mcCom solveCom)
  let span := lay.temps + 2 + lay.scalars.length + lay.arrays.length * q
  let c := q + span + ⌈cf⌉₊
  have hqc : q ≤ c := by dsimp [c]; omega
  have hspan : span ≤ c := by dsimp [c]; omega
  have hcf : cf ≤ (c : ℝ) := (Nat.le_ceil cf).trans (Nat.cast_le.mpr (by dsimp [c]; omega))
  refine ⟨compileProgram lay (mcCom solveCom), c, T, ?_, ?_⟩
  · intro x
    exact (hT x).trans (mul_le_mul_of_nonneg_right hcf (by positivity))
  · intro n G w hG x hx
    have hrun := mc_auto_computesInTime_of_solveSpec C hC φ ord G c w q ext solveCom (Ks n G)
      hq hqc hspan
      (fun x hx => hextOff n G x hx.1) (fun x hx => hextTgt n G x hx.1)
      hnw (hsolve n G hG c w)
    obtain ⟨t, ht, hr⟩ := hrun x hx
    exact ⟨t, ht.trans (hK n G hG x hx.1), hr⟩

end Lax3Proofs.Prog
