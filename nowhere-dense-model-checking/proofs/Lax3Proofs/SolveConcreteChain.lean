import Lax3Proofs.SolveConcreteTapes

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
open Lax3.ScatterSentences Lax3Proofs.LocalityFun
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax3.FirstOrder
variable {L n : ℕ}

noncomputable def concreteFrame (S : Setup L) (covC : ℕ → Com) : ℕ → Com → Com :=
  guardBody S (concreteQdepth S)
    (coverElse covC (centreLoopB (centreBody (concretePrep S) (concreteRead S))))

noncomputable def concreteChain (S : Setup L) (covC : ℕ → Com) : Com :=
  chainCom (concreteFrame S covC) (canonBotB S (concreteQdepth S)) S.depth 0

open Classical in
/-- The only numeric residuals in the recursive instance. -/
structure ConcreteBudgets (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (KB : (k j : ℕ) → Arena (S.pal j) n → ℕ)
    (Kcov : (j : ℕ) → Arena (S.pal j) n → ℕ) : Prop where
  leaf : ∀ j ≤ S.depth, ∀ A : Arena (S.pal j) n,
    botComK A.N (S.pal j) (concreteQdepth S) (levelFml S j) ≤ KB 0 j A
  step : ∀ k j, j < S.depth → ∀ A : Arena (S.pal j) n,
    4 + (if A.G = ⊥ then botComK A.N (S.pal j) (concreteQdepth S) (levelFml S j) else
      Kcov j A + ((∑ i ∈ Finset.range A.N,
        (centreKC S ord KB
          (fun _ j A u => prepCleanK S ord (concreteLp S) (concreteHb S) j A u)
          (fun _ j A u => readSegK S ord (arenaNames (j + 1)).tab "rd.s" j A u)
          k j A i + 8)) + 6)) ≤ KB (k + 1) j A

section Headline
variable (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
local notation "Sₕ" => Headline.headlineSetup C hC φ

/-- Every non-cover routine and every mathematical recursive guard is supplied
by the concrete instance. The cover sees and returns `PrepClean`. -/
theorem concreteChain_spec (B : ℕ) (ord : CoverSpec.OrderingRoutine)
    (G : SimpleGraph (Fin n)) (hG : C n G) (covC : ℕ → Com)
    (Scv : ℕ → Env → Prop)
    (KB : (k j : ℕ) → Arena ((Sₕ).pal j) n → ℕ)
    (Kcov : (j : ℕ) → Arena ((Sₕ).pal j) n → ℕ)
    (hroom : ConcreteRoom Sₕ n B) (hbudget : ConcreteBudgets Sₕ ord KB Kcov)
    (hsyn : ConcreteCoverSyntax covC)
    (halloc : ∀ j σ, ConcreteScr Sₕ n j σ → Scv j σ)
    (hcov : CoverAllClean B Sₕ ord (concreteLp Sₕ) (canonicalChannels Sₕ (concreteLp Sₕ))
      (concreteHb Sₕ) (canonicalAdm Sₕ G) concreteCa concreteCo concreteCm Scv covC Kcov) :
    BlockSpecClean B Sₕ ord (concreteLp Sₕ) (canonicalChannels Sₕ (concreteLp Sₕ))
      (concreteHb Sₕ) arenaNames (canonicalAdm Sₕ G) KB (ConcreteScr Sₕ n)
      (Sₕ).depth 0 (concreteChain Sₕ covC) := by
  have hLSb : ∀ j, ∀ y ∈ btScalars, y ∈ concreteLS Sₕ covC j := by
    intro j y hy; simp only [concreteLS, List.mem_append]; tauto
  have hLAb : ∀ j, ∀ a ∈ [botNa j, botFa j, botEa j, botXa j, (arenaNames j).tab],
      a ∈ concreteLA Sₕ covC j := by
    intro j a ha; simp only [concreteLA, List.mem_append]; tauto
  have hbot : ∀ j,
      BlockSpecClean B Sₕ ord (concreteLp Sₕ) (canonicalChannels Sₕ (concreteLp Sₕ))
        (concreteHb Sₕ) arenaNames (canonicalAdm Sₕ G) KB (ConcreteScr Sₕ n) 0 j
        (canonBotB Sₕ (concreteQdepth Sₕ) j) ∧
      OwnedFrom (concreteLS Sₕ covC) (concreteLA Sₕ covC) j (canonBotB Sₕ (concreteQdepth Sₕ) j) := by
    intro j
    refine ⟨?_, botBlock_owned (concreteLS Sₕ covC) (concreteLA Sₕ covC) arenaNames
      j (concreteQdepth Sₕ) Sₕ (hLSb j) (hLAb j)⟩
    intro A hdiag _ hzero
    have hj : j ≤ (Sₕ).depth := by omega
    have hb := botBlock_core B Sₕ ord (concreteLp Sₕ) (canonicalChannels Sₕ (concreteLp Sₕ))
      (concreteHb Sₕ) arenaNames (ConcreteScr Sₕ n) j (concreteQdepth Sₕ)
      (fun β hβ => concreteQdepth_bound Sₕ hj hβ) hroom.carrier (hroom.palette j hj)
      (hroom.leaf j hj) (hroom.formulas j hj) (canon_nd j) (canon_off j) (canon_tgt j)
      (canon_up j) (canon_hist j) (canon_nN j) (canon_nS j) (canon_nd5 j)
      (fun σ h => h.bot Sₕ n j j) 0 A (hzero rfl)
    exact (CleanSpec.of_spec hb (prepClean_canonBot_rank Sₕ (concreteQdepth Sₕ) j)).mono
      (hbudget.leaf j hj A)
  have hstep : FrameStepClean B Sₕ ord (concreteLp Sₕ) (canonicalChannels Sₕ (concreteLp Sₕ))
      (concreteHb Sₕ) arenaNames (canonicalAdm Sₕ G) KB (ConcreteScr Sₕ n)
      (concreteLS Sₕ covC) (concreteLA Sₕ covC) (concreteFrame Sₕ covC) := by
    apply frameStepClean_of_cover_parts_read_branch B Sₕ ord (concreteLp Sₕ)
      (canonicalChannels Sₕ (concreteLp Sₕ)) (concreteHb Sₕ) (canonicalAdm Sₕ G) KB
      (ConcreteScr Sₕ n) (concreteLS Sₕ covC) (concreteLA Sₕ covC)
      concreteCa concreteCo concreteCm Scv covC (concretePrep Sₕ) (concreteRead Sₕ)
      (prepChan Sₕ ord (concreteLp Sₕ) (canonicalChannels Sₕ (concreteLp Sₕ))) Kcov
      (fun _ j A u => prepCleanK Sₕ ord (concreteLp Sₕ) (concreteHb Sₕ) j A u)
      (fun _ j A u => readSegK Sₕ ord (arenaNames (j + 1)).tab "rd.s" j A u)
      (concreteQdepth Sₕ) hroom.carrier hroom.square
    · intro j hj β hβ; exact concreteQdepth_bound Sₕ (by omega) hβ
    · intro j hj; exact hroom.palette j (by omega)
    · intro j hj; exact hroom.leaf j (by omega)
    · intro j hj; exact hroom.formulas j (by omega)
    · intro j _ σ h; exact h.bot Sₕ n j j
    · intro j σ h
      have hc := h.ordinary Sₕ n j "cc.a" j (by decide)
      have ho := h.ordinary Sₕ n j "cc.o" j (by decide)
      have hn := concreteCapacity_bounds Sₕ n
      exact ⟨hn.1.trans hc, (show n + 1 ≤ concreteCapacity Sₕ n by omega).trans ho, halloc j σ h⟩
    · intro j σ σ' h hl; exact h.transport Sₕ n j hl
    · intro j hj σ h; exact h.down Sₕ n j hj
    · intro j hj σ h; exact h.table Sₕ n j (j + 1) hj
    · intro j _ A h u; exact canonicalChannels_child_of_adm Sₕ ord (concreteLp Sₕ) G j A h u rfl
    · exact concrete_freshS Sₕ covC hsyn
    · exact concrete_freshA Sₕ covC hsyn
    · intro j A h hbot u
      exact canonicalAdm_mkSetup_child C hC _ _ _ G h hbot (ord A.N A.G).order u
    · intro j A h hbot hj u
      exact canonicalAdm_mkSetup_leafChild C hC _ _ _ hG h hbot hj (ord A.N A.G).order u
    · intro j; simp [concreteLS]
    · exact hLSb
    · exact hLAb
    · exact concrete_cover_owned Sₕ covC
    · exact concrete_prep_owned Sₕ covC
    · exact concrete_read_owned Sₕ covC
    · exact concreteRead_rank Sₕ
    · exact hbudget.step
    · exact hcov
    · exact concreteParts B Sₕ ord G hroom
        (fun j hj => mkSetup_width_le C hC _ _ _ hj)
    · exact centreRead_of_rows B Sₕ ord (concreteLp Sₕ) (canonicalChannels Sₕ (concreteLp Sₕ))
        (concreteHb Sₕ) (canonicalAdm Sₕ G) (ConcreteScr Sₕ n) concreteCa concreteCo concreteCm
        (concreteRead Sₕ) _ (fun j σ σ' h hl => h.transport Sₕ n j hl)
        (concreteRows B Sₕ ord G hroom (headlineSetup_choice C hC φ))
  exact (chainCom_blockSpecClean B Sₕ ord (concreteLp Sₕ)
    (canonicalChannels Sₕ (concreteLp Sₕ)) (concreteHb Sₕ) arenaNames (canonicalAdm Sₕ G) KB
    (ConcreteScr Sₕ n) (concreteLS Sₕ covC) (concreteLA Sₕ covC)
    (concreteFrame Sₕ covC) (canonBotB Sₕ (concreteQdepth Sₕ)) hbot hstep (Sₕ).depth 0).1

end Headline
end Lax3Proofs.Prog
