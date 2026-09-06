import Lax3.ModelChecking
import Lax3Proofs.SolveConcrete
import Lax3Proofs.SolveCoverClean
import Lax3Proofs.SolveAugCharge
import Lax3Proofs.SolveFrameCharge
import Lax3Proofs.SolveUniformMachine

/-!
# The complete word-RAM model checker

The concrete cover, recursion, memory reservations and actual scalar costs
are assembled into the endorsed almost-linear-time theorem. Program, common
word-room constant and time function are fixed before graphs and word lengths.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning Lax62Proofs.Refine
open Lax3Proofs.Driver Lax3Proofs.CoverRoutine Lax3.ColoredGraphs
open Lax11.GraphEncoding Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder
variable {L n : ℕ}

private def machineFixedArrays : List String :=
  AugMachine.arrays ++ [CoverClean.ao, CoverClean.aj, CoverClean.dg,
    CoverClean.mt, CoverClean.od, CoverClean.hp] ++ plArrNames

private theorem concrete_fixed_capacity (S : Setup L) (n j : ℕ) {σ : Env}
    (h : ConcreteScr S n j σ) (a : String) (ha : a ∈ machineFixedArrays) :
    concreteCapacity S n ≤ (σ.arrs a).length := by
  have hnames : ∀ a ∈ machineFixedArrays, a ∉ matArrays ∧
      a ≠ "cp.w" ∧ a ≠ "sa.u" ∧ a.toList.take 4 ≠ "sb.n".toList ∧
      a.toList.take 4 ≠ "sb.f".toList ∧ a.toList.take 4 ≠ "sb.e".toList ∧
      a.toList.take 4 ≠ "sb.x".toList := by decide
  obtain ⟨hm, hw, hu, hn, hf, he, hx⟩ := hnames a ha
  simpa only [concreteSize, if_neg hw, if_neg hu, if_neg hn, if_neg hf,
    if_neg he, if_neg hx] using h.bound S n j a hm

/-- The initialized concrete layout supplies all reservations of the complete
cover, without any hypothesis on scratch contents. -/
theorem ConcreteScr.cover (S : Setup L) (n j : ℕ) {σ : Env}
    (h : ConcreteScr S n j σ) : CoverClean.Scv AugMachine.arrays n j σ := by
  have hcap : n * n + n + 1 ≤ concreteCapacity S n := by
    have := (concreteCapacity_bounds S n).2.2.1
    omega
  constructor
  · intro a ha
    exact hcap.trans (concrete_fixed_capacity S n j h a (by
      simp only [machineFixedArrays, List.mem_append]; tauto))
  · intro a ha
    simp only [CoverClean.arrays, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ha
    · exact hcap.trans (h.ordinary S n j "cc.r" j (by decide))
    · exact hcap.trans (h.ordinary S n j "cc.m" j (by decide))
    all_goals
      apply hcap.trans (concrete_fixed_capacity S n j h _ ?_)
      simp only [machineFixedArrays, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      tauto

theorem machineCoverSyntax (r : ℕ) : ConcreteCoverSyntax (CoverClean.coverCom r) := by
  constructor
  · intro j i _ y hy
    exact CoverClean.cover_vars_free r i j y hy
  · intro j i hji a ha
    exact CoverClean.cover_arrays_free r (by omega) a ha
  · intro j
    exact (CoverClean.cover_tapes r j).2

/-- One scalar multiplier for every fixed recursive stage. -/
noncomputable def machineStageCoeff (S : Setup L) : ℕ :=
  solveStageCoeff S (concreteLp S) (fun j => (arenaNames (j + 1)).tab)
    (fun _ => "rd.s") (concreteQdepth S)

/-- The actual recursive budget, including the unused empty-cover guard. -/
noncomputable def machineKB (S : Setup L) (k j : ℕ) (A : Arena (S.pal j) n) : ℕ :=
  chargeFrameK S (mdOrderingRoutine (3 * S.R)) (concreteLp S)
    (canonicalChannels S (concreteLp S))
    (fun _ A => machineCoverCharge A.N (CoverClean.Kcov A.G S.R))
    (machineStageCoeff S) k j A

theorem machineBudgets (S : Setup L) :
    ConcreteBudgets S (mdOrderingRoutine (3 * S.R)) (machineKB (n := n) S)
      (fun _ A => CoverClean.Kcov A.G S.R) := by
  constructor
  · intro j hj A
    exact chargeFrameK_zero S _ (concreteLp S) _ _ _ _ (concreteQdepth S) j A hj
  · intro k j hj A
    simpa only [machineKB, machineStageCoeff, concreteHb, Nat.add_assoc] using
      chargeFrameK_guard S (mdOrderingRoutine (3 * S.R)) (concreteLp S)
        (canonicalChannels S (concreteLp S))
        (fun _ A => machineCoverCharge A.N (CoverClean.Kcov A.G S.R))
        (fun _ A => CoverClean.Kcov A.G S.R)
        (fun j => (arenaNames (j + 1)).tab) (fun _ => "rd.s")
        (concreteQdepth S) k j A hj (machineCoverCharge_covers A _)

section Headline
variable (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
local notation "Sₕ" => Headline.headlineSetup C hC φ

/-- The complete concrete solve specification has no remaining execution,
layout, ordering, or cost assumption. -/
theorem machineSolveSpec (G : SimpleGraph (Fin n)) (hG : C n G) (c w : ℕ) :
    SolveSpec C hC φ (mdOrderingRoutine (3 * (Sₕ).R)) G c w
      (concreteWordQ Sₕ) (concreteExt Sₕ)
      (concreteSolve Sₕ (CoverClean.coverCom (Sₕ).R))
      (concreteSolveK Sₕ G (machineKB Sₕ)) := by
  apply concreteSolveSpec C hC φ _ G hG c w (CoverClean.coverCom (Sₕ).R)
    (CoverClean.Scv AugMachine.arrays n) (machineKB Sₕ)
    (fun _ A => CoverClean.Kcov A.G (Sₕ).R)
    (machineBudgets Sₕ) (machineCoverSyntax (Sₕ).R)
  · intro j σ h
    exact h.cover Sₕ n j
  · intro x hx
    exact CoverClean.coverAllClean_machine Sₕ (concreteLp Sₕ)
      (canonicalChannels Sₕ (concreteLp Sₕ)) (concreteHb Sₕ) (canonicalAdm Sₕ G)
      (concreteRoom Sₕ hx.1).cover

end Headline
end Lax3Proofs.Prog

namespace Lax3Proofs.ModelChecking
open Lax3Proofs.Prog Lax3Proofs.Driver Lax3Proofs.CoverRoutine
open Lax3.FirstOrder Lax11.GraphEncoding
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax67.Ram Lax67.RamComputes

open Classical in
/--
---
conclusion: Lax3.ModelChecking.exists_almostLinearTime_program_modelChecking
---

The complete concrete word-RAM model checker, with one program and one
almost-linear time bound chosen before all graphs and word lengths.
-/
theorem exists_almostLinearTime_program_modelChecking :
    ∀ (C : GraphClass), NowhereDense C →
    ∀ (φ : FO 0) (ε : ℝ), 0 < ε →
      ∃ (p : Program) (c : ℕ) (T : List ℕ → ℕ),
        (∀ x : List ℕ, (T x : ℝ) ≤ c * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
          ComputesInTime w p
            {x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ^ 2 ≤ 2 ^ w}
            (fun _ => if Sat G Fin.elim0 φ then [1] else [0]) T := by
  intro C hC φ ε hε
  let S := Headline.headlineSetup C hC φ
  let ord := mdOrderingRoutine (3 * S.R)
  have hδ : 0 < headlineδ S ε := by unfold headlineδ; positivity
  obtain ⟨cdeg, f, hcdeg, hf, hcover⟩ :=
    exists_actualCoverCost_le C hC S.R S.one_le_R (headlineδ S ε) hδ
  let a := 104 + 2 * topStageCoeff (concreteTopAtoms S) + topEvalCost S (concreteAV S)
  obtain ⟨cf, T, _, hT, htime⟩ :=
    exists_chargeFrameK_inputTime S ord (concreteLp S) hcdeg hf hε (machineStageCoeff S) 10 a
  apply exists_machine_of_uniformSolve C hC φ ε ord (concreteWordQ S) (concreteExt S)
    (concreteSolve S (CoverClean.coverCom S.R))
    (fun _ G => concreteSolveK S G (machineKB S))
    (by unfold concreteWordQ; omega)
    (concreteSolve_noWrite S _ (fun j => (CoverClean.cover_tapes S.R j).2))
    (fun _ _ x _ => concreteExt_off S x) (fun _ _ x _ => concreteExt_tgt S x)
    (fun _ G hG c w => machineSolveSpec C hC φ G hG c w) cf T hT
  intro n G hG x hx
  have ht := htime n G (Impl.trivialColoring n)
    (canonicalChannels S (concreteLp S))
    (fun _ A => machineCoverCharge A.N (CoverClean.Kcov A.G S.R)) x hx
    (fun j A hsub => machineCoverCharge_le hf (fun hN => by
      rw [CoverClean.Kcov_eq, ← actualCoverCost_eq]
      exact (hcover n G hG A.N A.G hsub).2 hN))
    (fun m H hsub => (hcover n G hG m H hsub).1)
  have hb := mcK_rootStages_le G (concreteTopAtoms S) (topEvalCost S (concreteAV S))
    (machineKB S S.depth 0 (rootArena G (Impl.trivialColoring n))) hx
  rw [codeLayout_const]
  exact (Nat.mul_le_mul_left 10 hb).trans ht

end Lax3Proofs.ModelChecking
