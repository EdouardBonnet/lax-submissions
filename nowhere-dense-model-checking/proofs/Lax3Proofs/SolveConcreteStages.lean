import Lax3Proofs.SolveConcreteRoom

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
open Lax3.ScatterSentences Lax3Proofs.LocalityFun
variable {L n : ℕ}

theorem ConcreteScr.prep (S : Setup L) (n j : ℕ) {σ : Env}
    (h : ConcreteScr S n j σ) :
    n ≤ (σ.arrs "cp.l").length ∧ n ≤ (σ.arrs "cp.r").length ∧
    n ≤ (σ.arrs "cp.b").length ∧ n ≤ (σ.arrs "cp.d").length ∧
    n ≤ (σ.arrs "cp.p").length ∧ n ≤ (σ.arrs "cp.x").length ∧
    n + 2 ≤ (σ.arrs "cp.v").length ∧ (σ.arrs "cp.w").length = S.width ∧
    n + 1 ≤ (σ.arrs "cp.o").length ∧ n * n ≤ (σ.arrs "cp.t").length ∧
    n * S.pal j ≤ (σ.arrs "cp.c").length ∧
    (∀ i, i < S.width → n ≤ (σ.arrs (lv "cq.d" i)).length) ∧
    (∀ c, c < S.pal j → n * n + 2 * n ≤ (σ.arrs (lv "cq.v" c)).length) ∧
    (∀ c, c < S.pal j + 1 → n + 1 ≤ (σ.arrs (lv "cq.u" c)).length) := by
  obtain ⟨hn, hn2, hbig, hs, hmul⟩ := concreteCapacity_bounds S n
  have hp := hmul _ (concreteScale_level S h.1).1
  have hc (b : String) (hb : b ∈ concreteCommonBases) := h.ordinary S n j b 0 hb
  refine ⟨hn.trans (hc "cp.l" (by decide)), hn.trans (hc "cp.r" (by decide)),
    hn.trans (hc "cp.b" (by decide)), hn.trans (hc "cp.d" (by decide)),
    hn.trans (hc "cp.p" (by decide)), hn.trans (hc "cp.x" (by decide)),
    hn2.trans (hc "cp.v" (by decide)), h.width S n j,
    (show n + 1 ≤ concreteCapacity S n by omega).trans (hc "cp.o" (by decide)),
    (show n * n ≤ concreteCapacity S n by omega).trans (hc "cp.t" (by decide)), hp.trans (hc "cp.c" (by decide)), ?_, ?_, ?_⟩
  · intro i _
    exact hn.trans (h.ordinary S n j "cq.d" i (by decide))
  · intro c _
    have := h.ordinary S n j "cq.v" c (by decide)
    omega
  · intro c _
    have := h.ordinary S n j "cq.u" c (by decide)
    omega

theorem ConcreteScr.child (S : Setup L) (n j : ℕ) (hj : j + 1 ≤ S.depth) {σ : Env}
    (h : ConcreteScr S n j σ) :
    n + 1 ≤ (σ.arrs (arenaNames (j + 1)).off).length ∧
    n * n ≤ (σ.arrs (arenaNames (j + 1)).tgt).length ∧
    n * S.pal (j + 1) ≤ (σ.arrs (arenaNames (j + 1)).col).length ∧
    n ≤ (σ.arrs (arenaNames (j + 1)).up).length ∧
    n * concreteLp S j * (concreteHb S j + 1) ≤
      (σ.arrs (arenaNames (j + 1)).hist).length := by
  obtain ⟨hn, hn2, hbig, hs, hmul⟩ := concreteCapacity_bounds S n
  have hp := hmul _ (concreteScale_level S hj).1
  have hh := hmul _ (concreteScale_static S).2.2.2.2
  have hc (b : String) (hb : b ∈ concreteCommonBases) := h.ordinary S n j b (j + 1) hb
  refine ⟨(show n + 1 ≤ concreteCapacity S n by omega).trans (hc "sa.o" (by decide)),
    (show n * n ≤ concreteCapacity S n by omega).trans (hc "sa.t" (by decide)),
    hp.trans (hc "sa.c" (by decide)), hn.trans (h.childUp S n j j), ?_⟩
  have := hc "sa.h" (by decide)
  simpa only [concreteLp, concreteHb, Nat.add_assoc, Nat.mul_assoc] using hh.trans this

theorem ConcreteScr.table (S : Setup L) (n j i : ℕ) (hi : i ≤ S.depth) {σ : Env}
    (h : ConcreteScr S n j σ) :
    n * (levelFml S i).length ≤ (σ.arrs (arenaNames i).tab).length := by
  exact ((concreteCapacity_bounds S n).2.2.2.2 _ (concreteScale_level S hi).2.1).trans
    (h.ordinary S n j "sa.b" i (by decide))

theorem ConcreteScr.read (S : Setup L) (n j : ℕ) {σ : Env}
    (h : ConcreteScr S n j σ) :
    n ≤ (σ.arrs "rd.p").length ∧ n ≤ (σ.arrs "rd.m").length ∧
    n ≤ (σ.arrs "rd.d").length ∧
      (levelAtoms S j).length ≤ (σ.arrs "rd.s").length := by
  have hn := (concreteCapacity_bounds S n).1
  have hc (b : String) (hb : b ∈ concreteCommonBases) := h.ordinary S n j b 0 hb
  refine ⟨hn.trans (hc "rd.p" (by decide)), hn.trans (hc "rd.m" (by decide)),
    hn.trans (hc "rd.d" (by decide)), ?_⟩
  exact (concreteAtomBound_length _).trans ((concreteScale_level S h.1).2.2.1.trans
    ((concreteCapacity_bounds S n).2.2.2.1.trans (hc "rd.s" (by decide))))

theorem concreteParts (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (G : SimpleGraph (Fin n)) (hroom : ConcreteRoom S n B)
    (hwidth : ∀ j < S.depth, 1 + j * (2 * S.R + 1) ≤ S.width) :
    ChildLoadPartsClean B S ord (concreteLp S) (canonicalChannels S (concreteLp S))
      (concreteHb S) (canonicalAdm S G) (ConcreteScr S n) concreteCa concreteCo concreteCm
      (concretePrep S) (prepChan S ord (concreteLp S) (canonicalChannels S (concreteLp S)))
      (fun _ j A u => prepCleanK S ord (concreteLp S) (concreteHb S) j A u) := by
  apply childLoadPartsClean_of B S ord (concreteLp S) (canonicalChannels S (concreteLp S))
    (concreteHb S) (canonicalAdm S G) (ConcreteScr S n) concreteCa concreteCo concreteCm
  · intros; rfl
  · intros; rfl
  · intro j hj; exact hj
  · intros; exact le_rfl
  · intro j A h; exact h.1
  · intro j A _ v e he z
    exact canonicalChannels_pin S (concreteLp S) j A v e he z
  · intro j A _ v e he
    exact canonicalChannels_empty S (concreteLp S) j A v e he
  · intro j hj; exact hwidth j (by omega)
  · exact hroom.one
  · exact hroom.carrier
  · exact hroom.square
  · exact hroom.extra
  · exact hroom.big
  · exact hroom.depth
  · exact hroom.radius
  · exact hroom.width
  · intros; exact hroom.depth
  · intro j _; have := hroom.radius; dsimp [concreteHb]; omega
  · intros; simpa [concreteLp, concreteHb, Nat.add_assoc] using hroom.history
  · exact hroom.palette
  · intro j σ h; exact h.prep S n j
  · intro j hj σ h; exact h.child S n j hj
  · intro j i
    exact ⟨concrete_cover_arena "cc.a" (by decide) j i,
      concrete_cover_arena "cc.o" (by decide) j i,
      concrete_cover_arena "cc.m" (by decide) j i⟩
  · intro j
    refine ⟨⟨concrete_cover_prep "cc.a" (by decide) j,
      concrete_cover_prep "cc.o" (by decide) j, concrete_cover_prep "cc.m" (by decide) j⟩, ?_⟩
    intro i
    exact ⟨⟨concrete_cover_q "cc.a" (by decide) "cq.d" (by decide) j i,
        concrete_cover_q "cc.a" (by decide) "cq.v" (by decide) j i,
        concrete_cover_q "cc.a" (by decide) "cq.u" (by decide) j i⟩,
      ⟨concrete_cover_q "cc.o" (by decide) "cq.d" (by decide) j i,
        concrete_cover_q "cc.o" (by decide) "cq.v" (by decide) j i,
        concrete_cover_q "cc.o" (by decide) "cq.u" (by decide) j i⟩,
      ⟨concrete_cover_q "cc.m" (by decide) "cq.d" (by decide) j i,
        concrete_cover_q "cc.m" (by decide) "cq.v" (by decide) j i,
        concrete_cover_q "cc.m" (by decide) "cq.u" (by decide) j i⟩⟩

theorem concreteRows (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (G : SimpleGraph (Fin n)) (hroom : ConcreteRoom S n B) (hchoice : S.choice = greedyChoice) :
    ReadRows B S ord (concreteLp S) (canonicalChannels S (concreteLp S))
      (concreteHb S) (canonicalAdm S G) (ConcreteScr S n) concreteCa concreteCo concreteCm
      (concreteRead S)
      (fun _ j A u => readSegK S ord (arenaNames (j + 1)).tab "rd.s" j A u) := by
  apply readRows_of B S ord (concreteLp S) (canonicalChannels S (concreteLp S))
    (concreteHb S) (canonicalAdm S G) (ConcreteScr S n) concreteCa concreteCo concreteCm
    "rd.p" "rd.m" "rd.d" "rd.s" hchoice hroom.one hroom.carrier hroom.square hroom.formulas
  · intro j hj
    exact lt_of_le_of_lt (concreteAtomBound_length _) (hroom.atoms j (by omega))
  · intro j hj a ha
    have hh := concreteAtomBound_mem ha
    have hb := hroom.atoms j (by omega)
    exact ⟨hh.1.trans_lt hb, hh.2.trans_lt hb⟩
  · intro j σ h; exact h.read S n j
  · exact concrete_read_arena "rd.p" (by decide)
  · exact concrete_read_arena "rd.m" (by decide)
  · exact concrete_read_arena "rd.d" (by decide)
  · exact concrete_read_arena "rd.s" (by decide)
  · exact concrete_read_cover "rd.p" (by decide)
  · exact concrete_read_cover "rd.m" (by decide)
  · exact concrete_read_cover "rd.d" (by decide)
  · exact concrete_read_cover "rd.s" (by decide)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact concrete_cover_tab

end Lax3Proofs.Prog
