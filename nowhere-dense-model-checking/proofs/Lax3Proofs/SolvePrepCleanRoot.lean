import Lax3Proofs.SolvePrepCleanFrame
import Lax3Proofs.SolveMachPrepRun

/-! Root entry and exact SolveSpec closure for the reusable rank scratch.
The parser/materializer already allocate fresh zero scratch, so the root
requires no extra clearing program. -/

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
open Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
variable {L n₀ : ℕ}

/-- Fresh materializer scratch is clean over any root prefix. -/
theorem MatIn.rankClean {ext : String → ℕ} {x : List ℕ} {σ : Env}
    (h : MatIn ext x σ) (N : ℕ) : RankClean N σ := by
  intro p _
  rw [h.arrs "cp.r" (by decide)]
  simp

/-- Every array word at root entry is bounded by the machine word bound. -/
theorem MatIn.arrWords {B n : ℕ} {G : SimpleGraph (Fin n)} {ext : String → ℕ}
    {x : List ℕ} {σ : Env} (h : MatIn ext x σ)
    (henc : EncodesGraph x n G) (hB : x.length < B) : ArrWords B σ := by
  intro a v hv
  by_cases ha : a = "off"
  · subst a
    rw [h.root.off_eq] at hv
    exact lt_of_le_of_lt (mem_csrOffsets_le henc v hv) hB
  by_cases ht : a = "tgt"
  · subst a
    rw [h.root.tgt_eq] at hv
    exact lt_of_le_of_lt (mem_csrTargets_le henc v hv) hB
  by_cases hu : a = "up"
  · subst a
    rw [h.root.up_eq, List.mem_range] at hv
    have hn := henc.vertexCount_eq
    have hl := henc.length_eq
    omega
  rw [h.arrs a (by simpa [matArrays] using ⟨ha, ht, hu⟩)] at hv
  have : v = 0 := (List.mem_replicate.mp hv).2
  omega

theorem solveSpec_of_cleanChain
    (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ext : List ℕ → String → ℕ)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (nmF : ℕ → ArenaNames)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Scr : ℕ → Env → Prop)
    (frameBody : ℕ → Com → Com) (botB : ℕ → Com)
    (rootLoadCom scatCom : Com) (av : ScatterSentence 0 → Expr)
    (Krl : List ℕ → ℕ) (Kc : ℕ)
    (hq : 1 ≤ q)
    (hextUp : ∀ x ∈ mcD n G c w, ext x "up" = vertexCount x)
    (hAdmRoot : Adm 0 (rootArena G (Impl.trivialColoring n)))
    (hdep0 : (Headline.headlineSetup C hC φ).depth = 0 → G = ⊥)
    (hscrLen0 : ∀ σ σ', Scr 0 σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr 0 σ')
    (hchain : ∀ x ∈ mcD n G c w,
      BlockSpecClean (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp htabF hbf
        nmF Adm KB Scr (Headline.headlineSetup C hC φ).depth 0
        (chainCom frameBody botB (Headline.headlineSetup C hC φ).depth 0))
    (hload : ∀ x ∈ mcD n G c w,
      Spec (mcB q x) (MatIn (ext x) x) rootLoadCom
        (fun _ σ' => BlockPre (Headline.headlineSetup C hC φ) 0 (hbf 0)
          (rootArena G (Impl.trivialColoring n))
          (htabF 0 (rootArena G (Impl.trivialColoring n))) (Scr 0) (nmF 0) σ')
        (Krl x))
    (hloadRank : "cp.r" ∉ rootLoadCom.warrs)
    (htop : ∀ x ∈ mcD n G c w,
      TopScatterSpec (mcB q x) (Headline.headlineSetup C hC φ) ord G
        (Impl.trivialColoring n)
        (BlockPost (Headline.headlineSetup C hC φ) ord
          (Headline.headlineSetup C hC φ).depth 0 (hbf 0)
          (rootArena G (Impl.trivialColoring n))
          (htabF 0 (rootArena G (Impl.trivialColoring n))) (nmF 0))
        (Scr 0) scatCom av Kc) :
    SolveSpec C hC φ ord G c w q ext
      (.seq matCom
        (.seq rootLoadCom
          (.seq (chainCom frameBody botB (Headline.headlineSetup C hC φ).depth 0)
            (topCom scatCom (Headline.headlineSetup C hC φ) av))))
      (fun x => matK x + (Krl x +
        (KB (Headline.headlineSetup C hC φ).depth 0
            (rootArena G (Impl.trivialColoring n)) +
          (Kc + topEvalCost (Headline.headlineSetup C hC φ) av)))) := by
  refine solveSpec_of_rest C hC φ ord G c w q ext _ _ hq hextUp ?_
  intro x hx
  obtain ⟨henc, hside⟩ := hx
  have h1B : 1 < mcB q x := one_lt_mcB (three_le_length henc) hq
  -- the chain, at the root arena
  have hchainS := hchain x ⟨henc, hside⟩ (rootArena G (Impl.trivialColoring n))
    (Nat.zero_add _) hAdmRoot (fun h0 => hdep0 h0)
  -- the top scatter residual
  obtain ⟨Q, hscat, hav⟩ := htop x ⟨henc, hside⟩
  -- the root evaluation, at the chain's table state
  have htopS := topCom_spec (mcB q x) (Headline.headlineSetup C hC φ) ord G
    (Impl.trivialColoring n) av rfl h1B hscat hav
  -- chain ; top: the chain preserves every array length, so the
  -- length-only level-0 scratch descriptor crosses it for free and
  -- lands, with the block postcondition, in the top stage's fixed
  -- precondition
  have hct := Spec.seq (specArrsLength hchainS) htopS
    (fun σ σ' hpre hpost => ⟨hpost.1.1, hscrLen0 σ σ' hpre.1.2.2 hpost.2⟩)
    (fun _ _ _ _ _ h => h)
  -- load ; (chain ; top)
  have hloadClean : Spec (mcB q x) (MatIn (ext x) x) rootLoadCom
      (fun _ σ' => BlockPre (Headline.headlineSetup C hC φ) 0 (hbf 0)
        (rootArena G (Impl.trivialColoring n))
        (htabF 0 (rootArena G (Impl.trivialColoring n))) (Scr 0) (nmF 0) σ' ∧
        PrepClean n (mcB q x) σ') (Krl x) := by
    intro σ hσ
    obtain ⟨σ', hr, hBP⟩ := hload x ⟨henc, hside⟩ σ hσ
    exact ⟨σ', hr, hBP,
      (hσ.rankClean n).of_arr_eq (hr.frame_arr _ hloadRank),
      Run.arrWords hr (hσ.arrWords henc (by
        have := length_add_one_lt_mcB (three_le_length henc) hq
        omega))⟩
  have hall := Spec.seq hloadClean hct
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
  exact hall


end Lax3Proofs.Prog
