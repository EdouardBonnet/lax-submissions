import Lax3Proofs.SolveStageCharge

/-!
# A uniform scalar budget for the complete recursive program

The guarded recurrence includes all actual stage and loop costs. A fixed
schedule coefficient lifts the existing sparse charge to the machine budget;
the final natural-valued time function is chosen before graphs and encodings.
Its additive one also handles empty graphs and constant program work.
-/

namespace Lax3Proofs.Prog
open scoped SimpleGraph
open Lax62Proofs.Refine Lax3.ColoredGraphs Lax3Proofs.Driver
open Lax12.GraphClasses Lax12.ColoringNumbers Lax3Proofs.CoverEdgeSum
variable {L n₀ : ℕ}

/-- A scalar budget with one fixed multiplier per remaining recursion level. -/
noncomputable def chargeFrameK (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) → Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    (C k j : ℕ) (A : Arena (S.pal j) n₀) : ℕ :=
  C ^ (k + 1) * (chargeTotal (driverChargeMS S ord ℓp htabF covC k j A) + 1)

theorem chargeFrameK_zero (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) → Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    (ct tsb : ℕ → String) (Kq j : ℕ) (A : Arena (S.pal j) n₀) (hj : j ≤ S.depth) :
    botComK A.N (S.pal j) Kq (levelFml S j) ≤
      chargeFrameK S ord ℓp htabF covC (solveStageCoeff S ℓp ct tsb Kq) 0 j A := by
  have h := (solveStageCoeff_level S ℓp ct tsb Kq j hj).2
  simpa only [chargeFrameK, driverChargeMS, zero_add, pow_one] using
    (botComK_le_charge S Kq j A).trans (Nat.mul_le_mul_right _ (by omega :
      botStageCoeff S Kq j ≤ solveStageCoeff S ℓp ct tsb Kq))

open Classical in
theorem chargeFrameK_of_bot (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) → Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    (C k j : ℕ) (A : Arena (S.pal j) n₀) (hbot : A.G = ⊥) :
    chargeFrameK S ord ℓp htabF covC C k j A =
      C ^ (k + 1) * (chargeTotal (botC S j A) + 1) := by
  cases k <;> simp [chargeFrameK, driverChargeMS, frameChargeMS, hbot]

open Classical in
/-- The complete guarded frame fits the scalar budget. Constants and each
recursive call are paid once, including the final failed loop test. -/
theorem chargeFrameK_guard (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) → Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    (Kcov : (j : ℕ) → Arena (S.pal j) n₀ → ℕ)
    (ct tsb : ℕ → String) (Kq k j : ℕ) (A : Arena (S.pal j) n₀) (hj : j < S.depth)
    (hcov : A.G ≠ ⊥ → Kcov j A ≤ chargeTotal (covC j A)) :
    let KB := chargeFrameK S ord ℓp htabF covC (solveStageCoeff S ℓp ct tsb Kq)
    4 + (if A.G = ⊥ then botComK A.N (S.pal j) Kq (levelFml S j)
      else Kcov j A + (∑ i ∈ Finset.range A.N,
        (centreKC S ord KB
          (fun _ j A u => prepCleanK S ord ℓp (fun _ => 2 * S.R + 1) j A u)
          (fun _ j A u => readSegK S ord (ct j) (tsb j) j A u) k j A i + 8)) + 6)
      ≤ KB (k + 1) j A := by
  let C := solveStageCoeff S ℓp ct tsb Kq
  let KB := chargeFrameK S ord ℓp htabF covC C
  let KP : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ :=
    fun _ j A u => prepCleanK S ord ℓp (fun _ => 2 * S.R + 1) j A u
  let KR : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ :=
    fun _ j A u => readSegK S ord (ct j) (tsb j) j A u
  change 4 + (if A.G = ⊥ then botComK A.N (S.pal j) Kq (levelFml S j)
    else Kcov j A + (∑ i ∈ Finset.range A.N, (centreKC S ord KB KP KR k j A i + 8)) + 6)
      ≤ KB (k + 1) j A
  have hC32 : 32 ≤ C := solveStageCoeff_ge S ℓp ct tsb Kq
  have hC0 : 0 < C := by omega
  have hcoeff := solveStageCoeff_level S ℓp ct tsb Kq j (by omega)
  change _ ≤ C ∧ _ ≤ C at hcoeff
  by_cases hbot : A.G = ⊥
  · rw [if_pos hbot]
    change _ ≤ chargeFrameK S ord ℓp htabF covC C (k + 1) j A
    rw [chargeFrameK_of_bot S ord ℓp htabF covC C (k + 1) j A hbot]
    have hb := botComK_le_charge S Kq j A
    have hm := Nat.mul_le_mul_right (chargeTotal (botC S j A) + 1) hcoeff.2
    have hb4 : 4 + botComK A.N (S.pal j) Kq (levelFml S j) ≤
        C * (chargeTotal (botC S j A) + 1) := by nlinarith only [hb, hm]
    have hp : C ≤ C ^ (k + 1 + 1) := by
      rw [pow_succ]
      exact Nat.le_mul_of_pos_left _ (pow_pos hC0 _)
    exact hb4.trans (Nat.mul_le_mul_right _ hp)
  · rw [if_neg hbot]
    let π := (ord A.N A.G).order
    let nx := fun B : Arena (S.pal (j + 1)) n₀ => Unroll.unrollAux S ord k (j + 1) B
    let nxC := fun B : Arena (S.pal (j + 1)) n₀ => driverChargeMS S ord ℓp htabF covC k (j + 1) B
    let E := fun u : Fin A.N => chargeTotal (centreChargeMS S j A (ℓp j) (htabF j A) nx nxC π u)
    let P := C ^ (k + 1)
    have hP0 : 0 < P := pow_pos hC0 _
    have hCP : C ≤ P := by
      dsimp [P]
      rw [pow_succ]
      exact Nat.le_mul_of_pos_left _ (pow_pos hC0 _)
    have hturn : ∀ u : Fin A.N, centreKC S ord KB KP KR k j A u + 8 ≤ P * (E u + 1) := by
      intro u
      let W := centreWork S j A (ℓp j) π u
      have hr := centreWork_room S j A (ℓp j) π u
      have hW1 : 1 ≤ W := by dsimp [W]; omega
      have hp := prepCleanK_le_centreWork S ord ℓp j A u
      have hrb := readSegK_le_centreWork S ord (ct j) (tsb j) j A (ℓp j) u
      have h8 := Nat.mul_le_mul_left 8 hW1
      have hc := Nat.mul_le_mul_right W hcoeff.1
      have hnonrec : KP k j A u + KR k j A u + 8 ≤ C * W := by
        change _ ≤ prepStageCoeff S (ℓp j) j * W at hp
        change _ ≤ readStageCoeff S (ct j) (tsb j) j * W at hrb
        dsimp [KP, KR]
        nlinarith only [hp, hrb, h8, hc]
      have hpay := centreWork_add_next_le S j A (ℓp j) (htabF j A) nx nxC π u
      change W + chargeTotal (nxC (childArena S A π u)) ≤ E u at hpay
      have hpayP := Nat.mul_le_mul_left P hpay
      have hCW := Nat.mul_le_mul_right W hCP
      have hchild : KB k (j + 1) (childArena S A π u) =
          P * (chargeTotal (nxC (childArena S A π u)) + 1) := rfl
      simp only [centreKC, dif_pos u.isLt]
      change KP k j A u + (KB k (j + 1) (childArena S A π u) + KR k j A u) + 8 ≤ _
      rw [hchild]
      nlinarith only [hnonrec, hpayP, hCW]
    have hsum : (∑ i ∈ Finset.range A.N, (centreKC S ord KB KP KR k j A i + 8)) ≤
        P * ((∑ u : Fin A.N, E u) + A.N) := by
      rw [Finset.sum_range]
      calc (∑ u : Fin A.N, (centreKC S ord KB KP KR k j A u + 8))
          ≤ ∑ u : Fin A.N, P * (E u + 1) := Finset.sum_le_sum fun u _ => hturn u
        _ = _ := by simp only [← Finset.mul_sum, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    have htotal : chargeTotal (driverChargeMS S ord ℓp htabF covC (k + 1) j A) =
        chargeTotal (covC j A) + A.N + (∑ u : Fin A.N, E u) + chargeTotal (readC S j A) := by
      rw [driverChargeMS, frameChargeMS, if_neg hbot]
      simp only [chargeTotal_add, chargeTotal_listSum, List.map_map, chargeTotal_allocC]
      rw [← Fin.sum_univ_def]
      simp only [E, nx, nxC, π, Function.comp_def, Nat.add_assoc]
    have hcovP : Kcov j A ≤ P * chargeTotal (covC j A) :=
      (hcov hbot).trans (Nat.le_mul_of_pos_left _ hP0)
    have h10P : 10 ≤ P * 10 := Nat.le_mul_of_pos_left _ hP0
    have hbody : 4 + (Kcov j A +
        (∑ i ∈ Finset.range A.N, (centreKC S ord KB KP KR k j A i + 8)) + 6) ≤
        P * (chargeTotal (driverChargeMS S ord ℓp htabF covC (k + 1) j A) + 10) := by
      rw [htotal]
      nlinarith only [hsum, hcovP, h10P]
    have hslack : chargeTotal (driverChargeMS S ord ℓp htabF covC (k + 1) j A) + 10 ≤
        C * (chargeTotal (driverChargeMS S ord ℓp htabF covC (k + 1) j A) + 1) := by
      nlinarith only [hC32]
    refine hbody.trans ((Nat.mul_le_mul_left P hslack).trans_eq ?_)
    simp only [KB, chargeFrameK, pow_succ, P]
    ring

/-- The root coefficient contains only the fixed schedule and class constants. -/
noncomputable def chargeFrameCoeff (S : Setup L) (ℓp : ℕ → ℕ) (c f : ℝ) (C : ℕ) : ℝ :=
  (C : ℝ) ^ (S.depth + 1) * (KP S ℓp c f ^ (S.depth + 1) + 1)

theorem chargeFrameCoeff_nonneg (S : Setup L) (ℓp : ℕ → ℕ) {c f : ℝ}
    (hc : 0 ≤ c) (hf : 0 ≤ f) (C : ℕ) : 0 ≤ chargeFrameCoeff S ℓp c f C := by
  have hK := one_le_KP S ℓp hc hf
  unfold chargeFrameCoeff
  positivity

open Classical in
/-- The scalar root budget inherits the sparse charge bound, including on the
empty graph. The additive one pays the actual program's constant work. -/
theorem chargeFrameK_root_le (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) → Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ)
    {c f δ : ℝ} (hc : 0 ≤ c) (hf : 0 ≤ f) (hδ : 0 ≤ δ) (C : ℕ)
    (G : SimpleGraph (Fin n₀)) (col : Coloring n₀ L)
    (hcov : ∀ j (A : Arena (S.pal j) n₀), A.G ⊑ G →
      (chargeTotal (covC j A) : ℝ) ≤ f * (A.N : ℝ) ^ (1 + 2 * δ))
    (hdeg : ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G → ∀ v : Fin m,
      (wreach H ((ord m H).order) (2 * S.R) v).ncard ≤ ⌈c * (m : ℝ) ^ δ⌉₊) :
    (chargeFrameK S ord ℓp htabF covC C S.depth 0 (rootArena G col) : ℝ) ≤
      chargeFrameCoeff S ℓp c f C *
        ((graphWeight G : ℝ) + 1) ^ (1 + ((S.depth : ℝ) + 2) * (2 * δ)) := by
  let E : ℝ := 1 + ((S.depth : ℝ) + 2) * (2 * δ)
  let W : ℝ := ((graphWeight G : ℝ) + 1) ^ E
  let K : ℝ := KP S ℓp c f ^ (S.depth + 1)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hK0 : 0 ≤ K := pow_nonneg (zero_le_one.trans (one_le_KP S ℓp hc hf)) _
  have hW1 : 1 ≤ W := by
    calc (1 : ℝ) = 1 ^ E := (Real.one_rpow _).symm
      _ ≤ W := Real.rpow_le_rpow (by norm_num)
        (by have := Nat.cast_nonneg (α := ℝ) (graphWeight G); linarith) hE
  have hdrv : (chargeTotal (driverChargeMS S ord ℓp htabF covC S.depth 0
      (rootArena G col)) : ℝ) ≤ K * W := by
    by_cases hW : 1 ≤ graphWeight G
    · have hd := driverChargeMS_chargeTotal_le S ord ℓp htabF covC hc hf hδ hcov hdeg
        S.depth 0 (by omega) (rootArena G col) ⟨SimpleGraph.Copy.id G⟩ hW
      rw [Headline.weight_rootArena] at hd
      refine hd.trans (mul_le_mul_of_nonneg_left ?_ hK0)
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) hE
    · have hN : (rootArena G col).N = 0 := by
        change n₀ = 0
        have hn : n₀ ≤ graphWeight G := Nat.le_add_right _ _
        omega
      rw [chargeTotal_driverChargeMS_of_N_eq_zero S ord ℓp htabF covC S.depth 0
        (rootArena G col) hN]
      push_cast
      exact mul_nonneg hK0 (by linarith)
  have hplus : (chargeTotal (driverChargeMS S ord ℓp htabF covC S.depth 0
      (rootArena G col)) : ℝ) + 1 ≤ (K + 1) * W := by nlinarith only [hdrv, hW1]
  have hmul := mul_le_mul_of_nonneg_left hplus
    (pow_nonneg (Nat.cast_nonneg C : (0 : ℝ) ≤ C) (S.depth + 1))
  simpa only [chargeFrameK, chargeFrameCoeff, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one, mul_assoc, K, W, E] using hmul

open Classical in
/-- A single natural-valued time bound, fixed before all graphs, encodings and
channel families. The multiplier and linear front/back ends are arbitrary
fixed program constants. -/
theorem exists_chargeFrameK_inputTime (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ) {c f ε : ℝ} (hc : 0 ≤ c) (hf : 0 ≤ f) (hε : 0 < ε)
    (C t a : ℕ) :
    ∃ (cf : ℝ) (T : List ℕ → ℕ), 0 ≤ cf ∧
      (∀ x, (T x : ℝ) ≤ cf * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L)
        (htabF : (j : ℕ) → (A : Arena (S.pal j) n) → Fin A.N → Fin (ℓp j) → List (Fin A.N))
        (covC : (j : ℕ) → Arena (S.pal j) n → ACost String ℕ)
        (x : List ℕ), Lax11.GraphEncoding.EncodesGraph x n G →
        (∀ j (A : Arena (S.pal j) n), A.G ⊑ G →
          (chargeTotal (covC j A) : ℝ) ≤ f * (A.N : ℝ) ^ (1 + 2 * headlineδ S ε)) →
        (∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G → ∀ v : Fin m,
          (wreach H ((ord m H).order) (2 * S.R) v).ncard ≤ ⌈c * (m : ℝ) ^ headlineδ S ε⌉₊) →
        t * (chargeFrameK S ord ℓp htabF covC C S.depth 0 (rootArena G col) + a * (x.length + 1))
          ≤ T x := by
  let κ : ℝ := (t : ℝ) * (chargeFrameCoeff S ℓp c f C + (a : ℝ))
  have hF0 := chargeFrameCoeff_nonneg S ℓp hc hf C
  have hκ0 : 0 ≤ κ := by dsimp [κ]; positivity
  refine ⟨κ + 1, fun x => ⌈κ * ((x.length : ℝ) + 1) ^ (1 + ε)⌉₊,
    by linarith, ?_, ?_⟩
  · intro x
    have hX : (1 : ℝ) ≤ (x.length : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) x.length
      linarith
    have hP : (1 : ℝ) ≤ ((x.length : ℝ) + 1) ^ (1 + ε) := by
      calc (1 : ℝ) = 1 ^ (1 + ε) := (Real.one_rpow _).symm
        _ ≤ _ := Real.rpow_le_rpow (by norm_num) hX (by linarith)
    have hy : 0 ≤ κ * ((x.length : ℝ) + 1) ^ (1 + ε) := mul_nonneg hκ0 (by linarith)
    exact (Nat.ceil_lt_add_one hy).le.trans (by nlinarith only [hP])
  · intro n G col htabF covC x hx hcov hdeg
    have hδ : 0 ≤ headlineδ S ε := by unfold headlineδ; positivity
    have hb := chargeFrameK_root_le S ord ℓp htabF covC hc hf hδ C G col hcov hdeg
    have hexp : 1 + ((S.depth : ℝ) + 2) * (2 * headlineδ S ε) = 1 + ε := by
      rw [headlineδ]
      have h2 : 2 * ((S.depth : ℝ) + 2) ≠ 0 := by positivity
      field_simp
    rw [hexp] at hb
    have hlen : (graphWeight G : ℝ) ≤ (x.length : ℝ) :=
      Nat.cast_le.mpr (Headline.graphWeight_le_length hx)
    have hroot := hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith :
        (graphWeight G : ℝ) + 1 ≤ (x.length : ℝ) + 1) (by linarith : (0 : ℝ) ≤ 1 + ε)) hF0)
    have hlin : (x.length : ℝ) + 1 ≤ ((x.length : ℝ) + 1) ^ (1 + ε) := by
      have h := Real.rpow_le_rpow_of_exponent_le
        (by have := Nat.cast_nonneg (α := ℝ) x.length; linarith :
          (1 : ℝ) ≤ (x.length : ℝ) + 1) (by linarith : (1 : ℝ) ≤ 1 + ε)
      rwa [Real.rpow_one] at h
    have hsum := add_le_add hroot (mul_le_mul_of_nonneg_left hlin (Nat.cast_nonneg a))
    have ht := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg t)
    have hfull : (t * (chargeFrameK S ord ℓp htabF covC C S.depth 0 (rootArena G col) +
        a * (x.length + 1)) : ℝ) ≤ κ * ((x.length : ℝ) + 1) ^ (1 + ε) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, κ, mul_add, add_mul,
        mul_assoc] using ht
    exact_mod_cast hfull.trans (Nat.le_ceil _)

end Lax3Proofs.Prog
