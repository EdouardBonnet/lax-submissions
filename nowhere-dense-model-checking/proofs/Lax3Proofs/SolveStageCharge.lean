import Lax3Proofs.SolveSegReadRun
import Lax3Proofs.ProgCharge
import Lax3Proofs.SolveMachPrepRun

/-!
# Scalar stage costs at the existing sparse charge

Preparation without repeated carrier resets and readback both cost a fixed
schedule coefficient times restriction plus isolation. Recursion is charged
separately. The single coefficient for all levels is chosen before any graph
or encoding; leaf and top-scatter constants include their real program tails.
-/

namespace Lax3Proofs.Prog
open Lax3.ColoredGraphs Lax3.ScatterSentences Lax3Proofs.Driver
open Lax62Proofs.Refine
variable {L n₀ : ℕ}

/-- A compile-time coefficient for the scalar scatter program. -/
def topStageCoeff {Λc : ℕ} : List (ScatterSentence Λc) → ℕ
  | [] => 1
  | a :: rest => (37 + 130 * (a.t + 1) * (a.r + 1)) + topStageCoeff rest

theorem topScatK_le_stageCoeff {Λc : ℕ} (N ns : ℕ)
    (as : List (ScatterSentence Λc)) :
    topScatK N ns as ≤ topStageCoeff as * (N + ns + 1) := by
  induction as with
  | nil => simp [topScatK, topStageCoeff]
  | cons a as ih =>
    have hs := scatterK_le N ns a.r a.t
    have ha : topAtomK N ns a.r a.t ≤
        (37 + 130 * (a.t + 1) * (a.r + 1)) * (N + ns + 1) := by
      unfold topAtomK
      nlinarith only [hs]
    simp only [topScatK, topStageCoeff, Nat.add_mul]
    simpa only [Nat.add_mul] using Nat.add_le_add ha ih

open Classical in
/-- The sparse work needed for a child before and after recursion. -/
noncomputable def centreWork (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓp : ℕ) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : ℕ :=
  Impl.childCharge A.G (S.pal j) ℓp S.R (cluster S A π u)
    + childN S A π u + ∑ v : Fin (childN S A π u), (preG S A π u).degree v

open Classical in
theorem centreWork_room (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓp : ℕ) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    childN S A π u + (∑ v : Fin (childN S A π u), (preG S A π u).degree v) + 1
      ≤ centreWork S j A ℓp π u := by
  have hp := childN_pos S A π u
  unfold centreWork Impl.childCharge
  change 0 < (cluster S A π u).ncard at hp
  change (cluster S A π u).ncard + _ + 1 ≤ _
  omega

open Classical in
theorem childSlots_le_preSlots (S : Setup L) (j : ℕ)
    (A : Arena (S.pal j) n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    (∑ v : Fin (childN S A π u), (childArena S A π u).G.degree v)
      ≤ ∑ v : Fin (childN S A π u), (preG S A π u).degree v := by
  refine Finset.sum_le_sum fun v _ => ?_
  apply SimpleGraph.degree_le_of_le
  exact Lax3Proofs.WalkDistance.deleteVerts_le _ _

/-- Readback's coefficient depends on the fixed formula schedule only. -/
noncomputable def readStageCoeff (S : Setup L) (ct tsb : String) (j : ℕ) : ℕ :=
  topStageCoeff (levelAtoms S j) + rowStoresK ct tsb S j (F S j) + 34

open Classical in
theorem readSegK_le_centreWork (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ct tsb : String) (j : ℕ) (A : Arena (S.pal j) n₀) (ℓp : ℕ) (u : Fin A.N) :
    readSegK S ord ct tsb j A u ≤
      readStageCoeff S ct tsb j * centreWork S j A ℓp ((ord A.N A.G).order) u := by
  rw [readSegK_coe]
  have ht := topScatK_le_stageCoeff
    (childN S A ((ord A.N A.G).order) u)
    (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
      (childArena S A ((ord A.N A.G).order) u).G.degree v) (levelAtoms S j)
  have hs := childSlots_le_preSlots S j A ((ord A.N A.G).order) u
  have hr := centreWork_room S j A ℓp ((ord A.N A.G).order) u
  have hm := Nat.mul_le_mul_left (topStageCoeff (levelAtoms S j))
    (show childN S A ((ord A.N A.G).order) u +
      (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
        (childArena S A ((ord A.N A.G).order) u).G.degree v) + 1 ≤
      centreWork S j A ℓp ((ord A.N A.G).order) u by omega)
  unfold readStageCoeff
  have hn := Nat.mul_le_mul_left (18 + rowStoresK ct tsb S j (F S j))
    (show childN S A ((ord A.N A.G).order) u ≤
      centreWork S j A ℓp ((ord A.N A.G).order) u by omega)
  have h1 := Nat.mul_le_mul_left 16
    (show 1 ≤ centreWork S j A ℓp ((ord A.N A.G).order) u by omega)
  nlinarith only [ht, hm, hn, h1]

/-- All preparation coefficients are fixed by the schedule. -/
noncomputable def prepStageCoeff (S : Setup L) (ℓp j : ℕ) : ℕ :=
  1000 + (30 + 30 * (2 * S.R + 2)) * ℓp + 12 * S.width
    + 69 * (2 * S.R + 1) + 35 * (2 * S.R + 2)
    + (S.width + (S.pal j + 1)) * 600 * (S.R + 1)
    + 30 * isoPal (relPal (S.pal j)) S.width S.R

open Classical in
theorem prepCleanK_le_centreWork (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ) (j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N) :
    prepCleanK S ord ℓp (fun _ => 2 * S.R + 1) j A u ≤
      prepStageCoeff S (ℓp j) j * centreWork S j A (ℓp j) ((ord A.N A.G).order) u := by
  let π := (ord A.N A.G).order
  let k := childN S A π u
  let ns := ∑ v : Fin k, (preG S A π u).degree v
  let cc := Impl.childCharge A.G (S.pal j) (ℓp j) S.R (cluster S A π u)
  let W := centreWork S j A (ℓp j) π u
  have hr : k + ns + 1 ≤ W := centreWork_room S j A (ℓp j) π u
  have hc : cc ≤ W := by dsimp [W, cc, centreWork]; omega
  have hr0 := restrictK_le_childCharge A.G (S.pal j) (ℓp j) S.R (cluster S A π u)
  have hr1 : restrictK (Impl.degSum A.G (cluster S A π u)) k
      (S.pal j) (ℓp j) (2 * S.R + 1) ≤ 264 * W := by
    change restrictK _ k _ _ _ ≤ 132 * (cc + 1) at hr0
    omega
  have hb := (bfsK_le k ns (2 * S.R)).trans
    (Nat.mul_le_mul_left (69 * (2 * S.R + 1)) hr)
  have hs := (supportsK_le k ns (2 * S.R)).trans
    (Nat.mul_le_mul_left (35 * (2 * S.R + 2)) hr)
  have hpr : profilesK S.width (S.pal j + 1) k ns S.R ≤
      (S.width + (S.pal j + 1)) * 600 * (S.R + 1) * W := by
    have h := profilesK_le S.width (S.pal j + 1) k ns S.R
    have hm := Nat.mul_le_mul_left ((S.width + (S.pal j + 1)) * 600 * (S.R + 1)) hr
    nlinarith only [h, hm]
  have hk := Nat.mul_le_mul_left (116 + 30 * isoPal (relPal (S.pal j)) S.width S.R)
    (show k ≤ W by omega)
  have hns := Nat.mul_le_mul_left 25 (show ns ≤ W by omega)
  have hfixed := Nat.mul_le_mul_left
    (232 + (30 + 30 * (2 * S.R + 2)) * ℓp j + 12 * S.width)
    (show 1 ≤ W by omega)
  rw [prepCleanK_coe]
  change 20 + 1 + (30 * k + 6) + 20 +
    ((30 + 30 * ((2 * S.R + 1) + 1)) * ℓp j + 20) +
    ((30 * k + 6) + (12 * S.width + 20)) + (14 * k + 20) +
    (20 + restrictK (Impl.degSum A.G (cluster S A π u)) k (S.pal j) (ℓp j) (2 * S.R + 1)) +
    (20 + bfsK k ns (2 * S.R)) + (30 + supportsK k ns (2 * S.R)) +
    profilesK S.width (S.pal j + 1) k ns S.R +
    ((30 * isoPal (relPal (S.pal j)) S.width S.R + 9) * k + 6) +
    isolateK k ns + 30 ≤ prepStageCoeff S (ℓp j) j * W
  unfold isolateK prepStageCoeff
  nlinarith only [hr1, hb, hs, hpr, hk, hns, hfixed]

open Classical in
theorem centreWork_eq_components (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓp : ℕ) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    centreWork S j A ℓp π u = chargeTotal (restrictC S j A ℓp π u) +
      chargeTotal (isolateC S j A htab π u) := by
  rw [chargeTotal_restrictC, chargeTotal_isolateC]
  simp only [Impl.isolateCharge, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  change _ = _ + ((∑ v : Fin (childN S A π u), (preG S A π u).degree v) + childN S A π u)
  unfold centreWork
  omega

open Classical in
/-- Restriction and isolation already pay all nonrecursive preparation/readback
work. The recursive charge is kept separately, once. -/
theorem centreWork_add_next_le (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓp : ℕ) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (nx : (B : Arena (S.pal (j + 1)) n₀) → Fin B.N → Lax3.DistFO.DistFO (S.pal (j + 1)) 1 → Prop)
    (nxC : Arena (S.pal (j + 1)) n₀ → ACost String ℕ)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    centreWork S j A ℓp π u + chargeTotal (nxC (childArena S A π u))
      ≤ chargeTotal (centreChargeMS S j A ℓp htab nx nxC π u) := by
  rw [centreWork_eq_components S j A ℓp htab π u, centreChargeMS]
  simp only [chargeTotal_add]
  omega

/-- A fixed coefficient for the leaf evaluator, including its constant tail. -/
noncomputable def botStageCoeff (S : Setup L) (Kq j : ℕ) : ℕ :=
  (3 * 2 ^ S.pal j + 11 * S.pal j + 6 * Kq +
    evalKMax (S.pal j) Kq (levelFml S j) + 60) * (1 + (levelFml S j).length)

theorem botComK_le_stageCoeff (S : Setup L) (Kq j N : ℕ) :
    botComK N (S.pal j) Kq (levelFml S j) ≤ botStageCoeff S Kq j * (N + 1) := by
  simpa only [botStageCoeff, Nat.mul_assoc] using botComK_le N (S.pal j) Kq (levelFml S j)

open Classical in
theorem botComK_le_charge (S : Setup L) (Kq j : ℕ) (A : Arena (S.pal j) n₀) :
    botComK A.N (S.pal j) Kq (levelFml S j) ≤
      botStageCoeff S Kq j * (chargeTotal (botC S j A) + 1) := by
  have hN : A.N ≤ chargeTotal (botC S j A) := by
    rw [chargeTotal_botC]
    unfold weight CoverEdgeSum.graphWeight
    nlinarith
  exact (botComK_le_stageCoeff S Kq j A.N).trans (Nat.mul_le_mul_left _ (by omega))

/-- One finite schedule constant, chosen before the graph and its encoding. -/
noncomputable def solveStageCoeff (S : Setup L) (ℓp : ℕ → ℕ)
    (ct tsb : ℕ → String) (Kq : ℕ) : ℕ :=
  32 + ∑ j ∈ Finset.range (S.depth + 1),
    (prepStageCoeff S (ℓp j) j + readStageCoeff S (ct j) (tsb j) j + botStageCoeff S Kq j)

theorem solveStageCoeff_ge (S : Setup L) (ℓp : ℕ → ℕ)
    (ct tsb : ℕ → String) (Kq : ℕ) : 32 ≤ solveStageCoeff S ℓp ct tsb Kq := by
  unfold solveStageCoeff
  omega

theorem solveStageCoeff_level (S : Setup L) (ℓp : ℕ → ℕ)
    (ct tsb : ℕ → String) (Kq j : ℕ) (hj : j ≤ S.depth) :
    prepStageCoeff S (ℓp j) j + readStageCoeff S (ct j) (tsb j) j + 8
      ≤ solveStageCoeff S ℓp ct tsb Kq ∧
    botStageCoeff S Kq j + 4 ≤ solveStageCoeff S ℓp ct tsb Kq := by
  have h := Finset.single_le_sum (f := fun i => prepStageCoeff S (ℓp i) i +
    readStageCoeff S (ct i) (tsb i) i + botStageCoeff S Kq i)
    (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : j < S.depth + 1))
  dsimp only at h
  unfold solveStageCoeff
  omega

end Lax3Proofs.Prog
