import Lax3Proofs.SolveConcreteOwned
import Lax3Proofs.SolveCovLoad

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning Lax67Proofs.Reasoning.Lib
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
open Lax3.ScatterSentences Lax3Proofs.LocalityFun
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax3.FirstOrder

/-- The actual input-to-root pass. -/
def concreteRootLoad : Com := .seq csrLoadCom rootGlueCom

noncomputable def concreteTop (S : Setup 0) : Com :=
  topAtomsCom (arenaNames 0) "rd.p" "rd.m" "rd.d" "rd.s" (levelFml S 0).length
    (fun a => memIdx (levelFml S 0) a.β) (concreteTopAtoms S) 0

noncomputable def concreteAV (S : Setup 0) (a : ScatterSentence 0) : Expr :=
  .get "rd.s" (.lit (memIdx (concreteTopAtoms S) a))

open Classical in
noncomputable def concreteTopK (S : Setup 0) {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  topScatK n (∑ v : Fin n, G.degree v) (concreteTopAtoms S)

theorem concreteRootLoad_rank : "cp.r" ∉ concreteRootLoad.warrs := by
  simp [concreteRootLoad, csrLoadCom, clInit, clTurn, clTail, Csr.scan,
    rootGlueCom, arenaNames, Com.warrs]

theorem concreteRootLoad_noWrite : concreteRootLoad.NoWrite := by
  simp [concreteRootLoad, csrLoadCom, clInit, clTurn, clTail, Csr.scan,
    rootGlueCom, Com.NoWrite]

section Headline
variable (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
local notation "Sₕ" => Headline.headlineSetup C hC φ

/-- Canonical input materialization and root load, with all layout clauses supplied. -/
theorem concreteLoad {n : ℕ} (G : SimpleGraph (Fin n)) (c w : ℕ) :
    RootLoadSpec C hC φ G c w (concreteWordQ Sₕ) (concreteExt Sₕ)
      (concreteLp Sₕ) (canonicalChannels Sₕ (concreteLp Sₕ)) (concreteHb Sₕ)
      (ConcreteScr Sₕ n) concreteRootLoad (fun x => csrLoadK x + (11 * n + 8)) := by
  have hq : 1 ≤ concreteWordQ Sₕ := by unfold concreteWordQ; omega
  have hext (x : List ℕ) (hx : x ∈ mcD n G c w) (b : String)
      (hb : b ∈ concreteCommonBases) :
      concreteCapacity Sₕ n ≤ concreteExt Sₕ x b := by
    have hh : ∀ b ∈ concreteCommonBases, b.length = 4 ∧ b ≠ "cp.w" ∧ b ≠ "sa.u" ∧
        b ≠ "sb.n" ∧ b ≠ "sb.f" ∧ b ≠ "sb.e" ∧ b ≠ "sb.x" := by decide
    obtain ⟨h4, hw, hu, hn, hf, he, hz⟩ := hh b hb
    simpa only [hx.1.vertexCount_eq, lv_zero] using
      concreteExt_common Sₕ x b 0 h4 hw hu hn hf he hz
  apply rootLoadSpec_of_csrLoad C hC φ G c w (concreteWordQ Sₕ) (concreteExt Sₕ)
    (concreteLp Sₕ) (canonicalChannels Sₕ (concreteLp Sₕ)) (concreteHb Sₕ)
    (ConcreteScr Sₕ n) "cl.d" clScalars csrLoadCom csrLoadK
  · intro x hx; exact (concreteRoom Sₕ hx.1).carrier
  · rfl
  · intro v p; exact canonicalChannels_root Sₕ (concreteLp Sₕ) G (Impl.trivialColoring n) v p
  · intro x hx; simpa [arenaNames] using hx.1.vertexCount_eq
  · intro x hx
    have hh := (concreteCapacity_bounds Sₕ n).2.2.2.2 _ (concreteScale_static Sₕ).2.2.2.2
    apply le_trans (b := concreteCapacity Sₕ n) _ (hext x hx "sa.h" (by decide))
    simpa [concreteLp, concreteHb, Nat.add_assoc, Nat.mul_assoc] using hh
  · intro x hx
    exact ((concreteCapacity_bounds Sₕ n).2.2.2.2 _
      (concreteScale_level Sₕ (Nat.zero_le _)).2.1).trans (hext x hx "sa.b" (by decide))
  · decide
  · decide
  · intro x hx σ σ' hmat hlen
    exact (hmat.concreteScr Sₕ hx.1).transport Sₕ n 0 hlen
  · apply rootCsrLoadAll_csrLoadCom c w (concreteWordQ Sₕ) (concreteExt Sₕ) hq
    · intro x hx
      exact (show n + 1 ≤ concreteCapacity Sₕ n by have := (concreteCapacity_bounds Sₕ n).2.1; omega).trans
        (hext x hx "sa.o" (by decide))
    · intro x _
      rw [← concreteExt_rootTgt]
      exact Nat.le_max_right ..
    · intro x hx
      exact (concreteCapacity_bounds Sₕ n).1.trans (hext x hx "cl.d" (by decide))

/-- Actual final scatter pass and its table read expression. -/
theorem concreteTopScatter (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w : ℕ) :
    TopScatterAll C hC φ ord G c w (concreteWordQ Sₕ) (concreteLp Sₕ)
      (canonicalChannels Sₕ (concreteLp Sₕ)) (concreteHb Sₕ) (ConcreteScr Sₕ n 0)
      (concreteTop Sₕ) (concreteAV Sₕ) (concreteTopK Sₕ G) := by
  unfold concreteTop concreteAV concreteTopK concreteTopAtoms
  apply topScatterAll_of C hC φ ord G c w (concreteWordQ Sₕ) (concreteLp Sₕ)
    (canonicalChannels Sₕ (concreteLp Sₕ)) (concreteHb Sₕ) (ConcreteScr Sₕ n 0)
    "rd.p" "rd.m" "rd.d" "rd.s"
  · unfold concreteWordQ; omega
  · intro σ h
    have hn := (concreteCapacity_bounds Sₕ n).1
    have hc (b : String) (hb : b ∈ concreteCommonBases) := h.ordinary Sₕ n 0 b 0 hb
    refine ⟨hn.trans (hc "rd.p" (by decide)), hn.trans (hc "rd.m" (by decide)),
      hn.trans (hc "rd.d" (by decide)), ?_⟩
    exact (concreteAtomBound_length _).trans ((concreteScale_top Sₕ).trans
      ((concreteCapacity_bounds Sₕ n).2.2.2.1.trans (hc "rd.s" (by decide))))
  · intro x hx
    have hr := concreteRoom Sₕ hx.1
    exact ⟨hr.carrier, hr.square, hr.formulas 0 (Nat.zero_le _),
      (concreteAtomBound_length _).trans_lt hr.top⟩
  · intro x hx a ha
    have hh := concreteAtomBound_mem ha
    have hr := (concreteRoom Sₕ hx.1).top
    exact ⟨hh.1.trans_lt hr, hh.2.trans_lt hr⟩
  · exact concrete_read_arena "rd.p" (by decide) 0
  · exact concrete_read_arena "rd.m" (by decide) 0
  · exact concrete_read_arena "rd.d" (by decide) 0
  · exact concrete_read_arena "rd.s" (by decide) 0
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

end Headline
end Lax3Proofs.Prog
