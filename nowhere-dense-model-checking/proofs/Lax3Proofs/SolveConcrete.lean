import Lax3Proofs.SolveConcreteChain

/-! A concrete recursive solve instance. Only the cover callback, its own
allocation/syntax interface, and scalar cost domination remain external. -/
namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
open Lax3.ScatterSentences Lax3Proofs.LocalityFun
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax3.FirstOrder
variable {L n : ℕ}

noncomputable def concreteSolve (S : Setup 0) (covC : ℕ → Com) : Com :=
  .seq matCom (.seq concreteRootLoad
    (.seq (concreteChain S covC) (topCom (concreteTop S) S (concreteAV S))))

noncomputable def concreteSolveK (S : Setup 0) (G : SimpleGraph (Fin n))
    (KB : (k j : ℕ) → Arena (S.pal j) n → ℕ) (x : List ℕ) : ℕ :=
  matK x + (csrLoadK x + (11 * n + 8) +
    (KB S.depth 0 (rootArena G (Impl.trivialColoring n)) +
      (concreteTopK S G + topEvalCost S (concreteAV S))))

private theorem concreteFrame_noWrite (S : Setup L) (covC : ℕ → Com)
    (hcov : ∀ j, (covC j).NoWrite) (j : ℕ) (nx : Com) (hnx : nx.NoWrite) :
    (concreteFrame S covC j nx).NoWrite := by
  simp [concreteFrame, guardBody, canonBotB, coverElse, centreLoopB, centreBody,
    Com.NoWrite, noWrite_botCom, hcov, concretePrep_noWrite, concreteRead_noWrite, hnx]

theorem concreteChain_noWrite (S : Setup L) (covC : ℕ → Com)
    (hcov : ∀ j, (covC j).NoWrite) : (concreteChain S covC).NoWrite := by
  have h : ∀ k j, (chainCom (concreteFrame S covC) (canonBotB S (concreteQdepth S)) k j).NoWrite := by
    intro k
    induction k with
    | zero => intro j; exact noWrite_botCom ..
    | succ k ih => intro j; exact concreteFrame_noWrite S covC hcov j _ (ih (j + 1))
  exact h _ _

theorem concreteSolve_noWrite (S : Setup 0) (covC : ℕ → Com)
    (hcov : ∀ j, (covC j).NoWrite) : (concreteSolve S covC).NoWrite := by
  simp [concreteSolve, topCom, verdictCom, Com.NoWrite, matCom_noWrite,
    concreteRootLoad_noWrite, concreteChain_noWrite S covC hcov, concreteTop_noWrite]

section Headline
variable (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
local notation "Sₕ" => Headline.headlineSetup C hC φ

/-- The full source-level solve specification, with concrete names, ext, root
load, PREP, readback, bottom blocks, recursion, and final scatter. -/
theorem concreteSolveSpec (ord : CoverSpec.OrderingRoutine)
    (G : SimpleGraph (Fin n)) (hG : C n G) (c w : ℕ) (covC : ℕ → Com)
    (Scv : ℕ → Env → Prop)
    (KB : (k j : ℕ) → Arena ((Sₕ).pal j) n → ℕ)
    (Kcov : (j : ℕ) → Arena ((Sₕ).pal j) n → ℕ)
    (hbudget : ConcreteBudgets Sₕ ord KB Kcov) (hsyn : ConcreteCoverSyntax covC)
    (halloc : ∀ j σ, ConcreteScr Sₕ n j σ → Scv j σ)
    (hcov : ∀ x ∈ mcD n G c w,
      CoverAllClean (mcB (concreteWordQ Sₕ) x) Sₕ ord (concreteLp Sₕ)
        (canonicalChannels Sₕ (concreteLp Sₕ)) (concreteHb Sₕ) (canonicalAdm Sₕ G)
        concreteCa concreteCo concreteCm Scv covC Kcov) :
    SolveSpec C hC φ ord G c w (concreteWordQ Sₕ) (concreteExt Sₕ)
      (concreteSolve Sₕ covC) (concreteSolveK Sₕ G KB) := by
  apply solveSpec_of_cleanChain C hC φ ord G c w (concreteWordQ Sₕ) (concreteExt Sₕ)
    (concreteLp Sₕ) (canonicalChannels Sₕ (concreteLp Sₕ)) (concreteHb Sₕ) arenaNames
    (canonicalAdm Sₕ G) KB (ConcreteScr Sₕ n) (concreteFrame Sₕ covC)
    (canonBotB Sₕ (concreteQdepth Sₕ)) concreteRootLoad (concreteTop Sₕ) (concreteAV Sₕ)
    (fun x => csrLoadK x + (11 * n + 8)) (concreteTopK Sₕ G)
  · unfold concreteWordQ; omega
  · intros; exact concreteExt_up ..
  · exact canonicalAdm_root Sₕ G (Impl.trivialColoring n)
  · intro hd
    exact canonicalAdm_mkSetup_eq_bot C hC _ _ _ hG
      (canonicalAdm_root Sₕ G (Impl.trivialColoring n)) hd.symm
  · intro σ σ' h hl; exact h.transport Sₕ n 0 hl
  · intro x hx
    exact concreteChain_spec C hC φ _ ord G hG covC Scv KB Kcov (concreteRoom Sₕ hx.1)
      hbudget hsyn halloc (hcov x hx)
  · exact concreteLoad C hC φ G c w
  · exact concreteRootLoad_rank
  · exact concreteTopScatter C hC φ ord G c w

end Headline
end Lax3Proofs.Prog
