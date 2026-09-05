import Lax3Proofs.ProgCover
import Lax3Proofs.SolveSweepMdPeel
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
Uniform sparsity and time bounds for the deterministic machine ordering.
The constants are chosen before the graph. Sparse witness counts and the
lazy heap's logarithm are retained in the machine charge.
-/

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ShallowMinorDensity
open Lax12.ColoringNumbers
open Lax3Proofs.Augmentation Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.AugmentedDensity Lax3Proofs.CoverDegree Lax3Proofs.CoverRoutine

variable {n : ℕ}

theorem exists_mdChain_inDegLE_pow (C : GraphClass) (hC : NowhereDense C)
    (R : ℕ) (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ i ≤ R, (mdChain G i).InDegLE
          ((3 * ⌈c₀ * (m : ℝ) ^ δ'⌉₊ + 2) ^ 16 ^ R) := by
  obtain ⟨c₀, hc₀⟩ := exists_densityAtMost_of_nowhereDense C hC (chainDepth R 1) δ' hδ'
  refine ⟨max c₀ 0, le_max_right _ _, fun n Gn hGn m G hsub => ?_⟩
  have hXnn : (0 : ℝ) ≤ (m : ℝ) ^ δ' := Real.rpow_nonneg (Nat.cast_nonneg m) δ'
  have hdensR : HasDensityAtMost G (chainDepth R 1) ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ :=
    hasDensityAtMost_mono
      (Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left _ _) hXnn))
      (hc₀ n Gn hGn m G hsub)
  have hdens1 : HasDensityAtMost G 1 ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ :=
    hasDensityAtMost_mono_depth
      (show (1 : ℕ) ≤ chainDepth R 1 from chainDepth_mono_round 1 (Nat.zero_le R)) hdensR
  have hd0 : (mdChain G 0).InDegLE (elimBound G) := inDegLE_baseOr_mdPerm G
  have hd0le : elimBound G ≤ 2 * ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ :=
    inDeg_zero_le hdens1 fun _k' hk' => elimBound_le hk'
  have hjoint := greedy_chain_joint_inDegLE (isAugChain_mdChain G R)
    (fun i _ => greedyFratRound_mdChain G i) hd0 hdensR
  intro i hi v
  refine (hjoint i hi v).trans ?_
  calc (joint (elimBound G) ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ i).1
      ≤ (elimBound G + ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ + 2) ^ 16 ^ i := joint_fst_le _ _ _
    _ ≤ (3 * ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ + 2) ^ 16 ^ i :=
        Nat.pow_le_pow_left (by omega) _
    _ ≤ (3 * ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ + 2) ^ 16 ^ R :=
        Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hi)

/-- The cast of the raw bound: `(3·⌈c₀·X⌉₊ + 2)^P ≤ ((3c₀+5)·X)^P` for
`X ≥ 1` — the ceiling absorbed into the constant, the numeric step every
consumer of the raw form repeats. -/
private theorem md_dmax_cast_le {c₀ X : ℝ} (hc₀ : 0 ≤ c₀) (hX : 1 ≤ X) (P : ℕ) :
    (((3 * ⌈c₀ * X⌉₊ + 2) ^ P : ℕ) : ℝ) ≤ ((3 * c₀ + 5) * X) ^ P := by
  have hXnn : (0 : ℝ) ≤ X := zero_le_one.trans hX
  have hceil : ((⌈c₀ * X⌉₊ : ℕ) : ℝ) ≤ c₀ * X + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hc₀ hXnn)).le
  have hbase : ((3 * ⌈c₀ * X⌉₊ + 2 : ℕ) : ℝ) ≤ (3 * c₀ + 5) * X := by
    push_cast
    nlinarith [hceil, hX, hc₀]
  calc (((3 * ⌈c₀ * X⌉₊ + 2) ^ P : ℕ) : ℝ)
      = (((3 * ⌈c₀ * X⌉₊ + 2 : ℕ) : ℝ)) ^ P := by push_cast; ring
    _ ≤ ((3 * c₀ + 5) * X) ^ P := by gcongr

/-- `(m^(δ/P))^P = m^δ`: the inner exponent, undone. -/
private theorem md_rpow_div_pow (m P : ℕ) (hP : 0 < P) (δ : ℝ) :
    ((m : ℝ) ^ (δ / (P : ℝ))) ^ (P : ℕ) = (m : ℝ) ^ δ := by
  have hP0 : ((P : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  rw [← Real.rpow_natCast ((m : ℝ) ^ (δ / (P : ℝ))) P,
    ← Real.rpow_mul (Nat.cast_nonneg m), div_mul_cancel₀ _ hP0]

/-- **The greedy chain's in-degree bound, on a class** — the
`⌈c·m^δ⌉₊` form: one constant, fixed before the graph, bounding the
in-degree of *every* round `i ≤ R` of the greedy chain on every
subgraph copy of every member.  This is the uniformization of the
landed `greedy_chain_joint_inDegLE` that the pricing consumes. -/
theorem exists_mdChain_inDegLE (C : GraphClass) (hC : NowhereDense C)
    (R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ i ≤ R, (mdChain G i).InDegLE ⌈c * (m : ℝ) ^ δ⌉₊ := by
  have hPpos : 0 < (16 ^ R : ℕ) := by positivity
  have hδ' : 0 < δ / ((16 ^ R : ℕ) : ℝ) := div_pos hδ (by exact_mod_cast hPpos)
  obtain ⟨c₀, hc₀0, hc₀⟩ := exists_mdChain_inDegLE_pow C hC R _ hδ'
  refine ⟨(3 * c₀ + 5) ^ (16 ^ R : ℕ), fun n Gn hGn m G hsub i hi v => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact v.elim0
  have h := hc₀ n Gn hGn m G hsub i hi v
  refine h.trans ?_
  have hX1 : (1 : ℝ) ≤ (m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ)) := one_le_rpow hm hδ'.le
  have hcast := md_dmax_cast_le hc₀0 hX1 (16 ^ R)
  have hXP := md_rpow_div_pow m (16 ^ R) hPpos δ
  have hfin : (((3 * ⌈c₀ * (m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ))⌉₊ + 2) ^ 16 ^ R : ℕ) : ℝ)
      ≤ (3 * c₀ + 5) ^ (16 ^ R : ℕ) * (m : ℝ) ^ δ := by
    calc (((3 * ⌈c₀ * (m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ))⌉₊ + 2) ^ 16 ^ R : ℕ) : ℝ)
        ≤ ((3 * c₀ + 5) * (m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ))) ^ (16 ^ R : ℕ) := hcast
      _ = (3 * c₀ + 5) ^ (16 ^ R : ℕ)
            * ((m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ))) ^ (16 ^ R : ℕ) := mul_pow _ _ _
      _ = (3 * c₀ + 5) ^ (16 ^ R : ℕ) * (m : ℝ) ^ δ := by rw [hXP]
  exact_mod_cast hfin.trans (Nat.le_ceil _)

theorem exists_wreach_degree_mdOrderingRoutine (C : GraphClass) (hC : NowhereDense C)
    (rc R t : ℕ) (ht : 3 * t ≤ R) (hrt : 2 * rc ≤ 2 ^ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ v : Fin m,
          (wreach G ((mdOrderingRoutine R) m G).order (2 * rc) v).ncard
            ≤ ⌈c * (m : ℝ) ^ δ⌉₊ := by
  obtain ⟨c, hc⟩ := wreach_degree_of_data C hC rc R t ht hrt δ hδ
  refine ⟨max c 0, le_max_right _ _, fun n Gn hGn m G hsub v => ?_⟩
  have h := hc n Gn hGn m G hsub _ _ _ _ (mdOrderingRoutine_data R m G) v
  refine h.trans (Nat.ceil_mono ?_)
  exact mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (Nat.cast_nonneg m) δ)


/-- The base phase's vertex/arc count before the heap factor. -/
noncomputable def mdBaseCharge {m : ℕ} (G : SimpleGraph (Fin m)) : ℕ :=
  m + 3 * arcCount (mdChain G 0)

/-- The final phase's vertex/arc count before the heap factor. -/
noncomputable def mdFinalCharge (D : Orientation n) : ℕ :=
  3 * n + 5 * arcCount D

/-- The sparse vertex, arc, and witness count of the deterministic chain.
`mdMachineCharge` separately accounts for lazy-heap operations. -/
noncomputable def mdChainCharge {m : ℕ} (G : SimpleGraph (Fin m)) (R : ℕ) : ℕ :=
  mdBaseCharge G + (∑ i ∈ Finset.range R, levelCharge (mdChain G i))
    + mdFinalCharge (mdChain G R)

/-- On the empty carrier every count is an empty sum: the charge is
`0`.  (The `m = 0` case of every bound below.) -/
theorem mdChainCharge_zero (G : SimpleGraph (Fin 0)) (R : ℕ) : mdChainCharge G R = 0 := by
  simp [mdChainCharge, mdBaseCharge, mdFinalCharge, levelCharge, arcCount, fratPairCount,
    transPairCount]

/-- **Control: the charge is not a disguised placeholder.**  It is at
least the carrier size — the routine reads its input — so the timed
discharge below is not the vacuous `steps := 0` one the interface would
also accept (module docstring). -/
theorem le_mdChainCharge {m : ℕ} (G : SimpleGraph (Fin m)) (R : ℕ) :
    m ≤ mdChainCharge G R := by
  have h1 : m ≤ mdBaseCharge G := Nat.le_add_right m _
  have h2 : mdBaseCharge G ≤ mdChainCharge G R :=
    le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  exact h1.trans h2

/-- **The chain total at a uniform in-degree bound**: `R` levels, the
base and the final elimination, all priced by one `d`, total
`(6R + 8)·m·(d+1)²`.  Pure counting — the class enters only through
`d`. -/
theorem mdChainCharge_le_of_uniform {m : ℕ} {G : SimpleGraph (Fin m)} {R d : ℕ}
    (hd : ∀ i ≤ R, (mdChain G i).InDegLE d) :
    mdChainCharge G R ≤ (6 * R + 8) * (m * ((d + 1) * (d + 1))) := by
  have hbase : mdBaseCharge G ≤ 3 * (m * ((d + 1) * (d + 1))) := by
    have h := arcCount_le (hd 0 (Nat.zero_le R))
    have : mdBaseCharge G = m + 3 * arcCount (mdChain G 0) := rfl
    nlinarith [h]
  have hfin : mdFinalCharge (mdChain G R) ≤ 5 * (m * ((d + 1) * (d + 1))) := by
    have h := arcCount_le (hd R le_rfl)
    have : mdFinalCharge (mdChain G R) = 3 * m + 5 * arcCount (mdChain G R) := rfl
    nlinarith [h]
  have hsum : (∑ i ∈ Finset.range R, levelCharge (mdChain G i))
      ≤ R * (6 * (m * ((d + 1) * (d + 1)))) := by
    calc (∑ i ∈ Finset.range R, levelCharge (mdChain G i))
        ≤ ∑ _i ∈ Finset.range R, 6 * (m * ((d + 1) * (d + 1))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have h := levelCharge_le (hd i (le_of_lt (Finset.mem_range.mp hi)))
          nlinarith [h]
      _ = R * (6 * (m * ((d + 1) * (d + 1)))) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_range]
  calc mdChainCharge G R
      = mdBaseCharge G + (∑ i ∈ Finset.range R, levelCharge (mdChain G i))
        + mdFinalCharge (mdChain G R) := rfl
    _ ≤ 3 * (m * ((d + 1) * (d + 1))) + R * (6 * (m * ((d + 1) * (d + 1))))
        + 5 * (m * ((d + 1) * (d + 1))) := by omega
    _ = (6 * R + 8) * (m * ((d + 1) * (d + 1))) := by ring


theorem exists_mdChainCharge_le (C : GraphClass) (hC : NowhereDense C) (R : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : ℝ, 0 ≤ f ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        (mdChainCharge G R : ℝ) ≤ f * (m : ℝ) ^ (1 + δ) := by
  have hPpos : 0 < (2 * 16 ^ R : ℕ) := by positivity
  have hδ' : 0 < δ / ((2 * 16 ^ R : ℕ) : ℝ) := div_pos hδ (by exact_mod_cast hPpos)
  obtain ⟨c₀, hc₀0, hc₀⟩ := exists_mdChain_inDegLE_pow C hC R _ hδ'
  refine ⟨(4 * (6 * R + 8) : ℝ) * (3 * c₀ + 5) ^ (2 * 16 ^ R : ℕ), by positivity, ?_⟩
  intro n Gn hGn m G hsub
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [mdChainCharge_zero, Nat.cast_zero,
      Real.zero_rpow (by positivity : (1 : ℝ) + δ ≠ 0), mul_zero]
  -- the uniform in-degree bound of every round
  have huni := hc₀ n Gn hGn m G hsub
  set D₁ : ℕ := ⌈c₀ * (m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ))⌉₊ with hD₁def
  -- the ℕ-side total at that bound
  have hN := mdChainCharge_le_of_uniform huni
  set dmax : ℕ := (3 * D₁ + 2) ^ 16 ^ R with hdmaxdef
  have hd1 : 1 ≤ dmax := Nat.one_le_pow _ _ (by omega)
  have hsq : (dmax + 1) * (dmax + 1) ≤ 4 * ((3 * D₁ + 2) ^ (2 * 16 ^ R)) := by
    have h4 : (dmax + 1) * (dmax + 1) ≤ 4 * (dmax * dmax) := by nlinarith [hd1]
    have hdd : dmax * dmax = (3 * D₁ + 2) ^ (2 * 16 ^ R) := by
      rw [hdmaxdef, ← pow_add, two_mul]
    rwa [hdd] at h4
  have hN2 : mdChainCharge G R ≤ 4 * (6 * R + 8) * (m * (3 * D₁ + 2) ^ (2 * 16 ^ R)) := by
    calc mdChainCharge G R ≤ (6 * R + 8) * (m * ((dmax + 1) * (dmax + 1))) := hN
      _ ≤ (6 * R + 8) * (m * (4 * ((3 * D₁ + 2) ^ (2 * 16 ^ R)))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsq)
      _ = 4 * (6 * R + 8) * (m * (3 * D₁ + 2) ^ (2 * 16 ^ R)) := by ring
  -- the ℝ-side massage
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hX1 : (1 : ℝ) ≤ (m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ)) := one_le_rpow hm hδ'.le
  have hcast := md_dmax_cast_le hc₀0 hX1 (2 * 16 ^ R)
  have hXP := md_rpow_div_pow m (2 * 16 ^ R) hPpos δ
  calc (mdChainCharge G R : ℝ)
      ≤ ((4 * (6 * R + 8) * (m * (3 * D₁ + 2) ^ (2 * 16 ^ R)) : ℕ) : ℝ) := by
        exact_mod_cast hN2
    _ = (4 * (6 * R + 8) : ℝ) * ((m : ℝ) * (((3 * D₁ + 2) ^ (2 * 16 ^ R) : ℕ) : ℝ)) := by
        push_cast; ring
    _ ≤ (4 * (6 * R + 8) : ℝ) * ((m : ℝ)
          * ((3 * c₀ + 5) * (m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ))) ^ (2 * 16 ^ R : ℕ)) := by
        rw [hD₁def]
        gcongr
    _ = (4 * (6 * R + 8) : ℝ) * (3 * c₀ + 5) ^ (2 * 16 ^ R : ℕ)
          * ((m : ℝ) * ((m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ))) ^ (2 * 16 ^ R : ℕ)) := by
        rw [mul_pow]; ring
    _ = (4 * (6 * R + 8) : ℝ) * (3 * c₀ + 5) ^ (2 * 16 ^ R : ℕ) * (m : ℝ) ^ (1 + δ) := by
        rw [hXP, Real.rpow_add hm0, Real.rpow_one]


/-- A common logarithmic factor for every heap on a simple `N`-vertex
graph. The quadratic expression bounds addresses, not scanned work. -/
def mdLogFactor (N : ℕ) : ℕ := Nat.log 2 (N * N + N + 1) + 1

theorem one_le_mdLogFactor (N : ℕ) : 1 ≤ mdLogFactor N := by
  unfold mdLogFactor
  omega

theorem mdLogFactor_le_rpow (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (mdLogFactor N : ℝ) ≤
      (2 / (δ * Real.log 2) + 1) * ((N : ℝ) + 1) ^ δ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hp1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ δ :=
    Real.one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) N; linarith) hδ.le
  have hpoly : ((N * N + N + 1 : ℕ) : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (N * N + N + 1 : ℕ)) hpoly
  rw [Real.log_pow] at hl
  norm_num at hl
  have hlog := Real.natLog_le_logb (N * N + N + 1) 2
  norm_num only [Nat.cast_ofNat] at hlog
  rw [Real.logb] at hlog
  push_cast at hlog
  have hsmall := Real.log_le_rpow_div hp.le hδ
  calc
    (mdLogFactor N : ℝ)
        ≤ (2 * Real.log ((N : ℝ) + 1)) / Real.log 2 + 1 := by
          unfold mdLogFactor
          push_cast
          have h := hlog.trans (div_le_div_of_nonneg_right hl hl2.le)
          linarith
    _ ≤ (2 * (((N : ℝ) + 1) ^ δ / δ)) / Real.log 2 + 1 := by
          gcongr
    _ = (2 / (δ * Real.log 2)) * ((N : ℝ) + 1) ^ δ + 1 := by
          field_simp
    _ ≤ (2 / (δ * Real.log 2) + 1) * ((N : ℝ) + 1) ^ δ := by
          nlinarith

/-- The actual lazy-heap budget can be priced by its sparse degree sum
and the common logarithm, including its constant work on an empty graph. -/
theorem KmdPeel_le_mdLogFactor {N ns : ℕ} (hns : ns ≤ N * N) :
    KmdPeel N ns ≤ 200 * (N + ns + 1) * mdLogFactor N := by
  have hlog : Nat.log 2 (N + ns + 1) + 1 ≤ mdLogFactor N := by
    unfold mdLogFactor
    exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
  have h1 := one_le_mdLogFactor N
  have hm := Nat.mul_le_mul_left (100 * (N + ns)) hlog
  unfold KmdPeel
  nlinarith

/-- Sparse work in all rounds, with the real heap factor and one
constant per round. Every term is independent of word size. -/
noncomputable def mdMachineCharge {N : ℕ} (G : SimpleGraph (Fin N)) (R : ℕ) : ℕ :=
  (mdChainCharge G R + R + 1) * mdLogFactor N

/-- The machine envelope is almost linear on nonempty subgraph copies.
Empty carriers take the leaf guard before any cover computation. -/
theorem exists_mdMachineCharge_le (C : GraphClass) (hC : NowhereDense C)
    (R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : ℝ, 0 ≤ f ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn → 0 < m →
        (mdMachineCharge G R : ℝ) ≤ f * (m : ℝ) ^ (1 + δ) := by
  have he : 0 < δ / 2 := by linarith
  obtain ⟨f, hf, hcharge⟩ := exists_mdChainCharge_le C hC R (δ / 2) he
  let l : ℝ := (2 / ((δ / 2) * Real.log 2) + 1) * (2 : ℝ) ^ (δ / 2)
  have hl0 : 0 ≤ l := by
    dsimp [l]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  refine ⟨(f + (R : ℝ) + 1) * l, by positivity, ?_⟩
  intro n Gn hGn m G hsub hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow1 : (1 : ℝ) ≤ (m : ℝ) ^ (1 + δ / 2) :=
    Real.one_le_rpow hm1 (by linarith)
  have hlog : (mdLogFactor m : ℝ) ≤ l * (m : ℝ) ^ (δ / 2) := by
    calc
      _ ≤ (2 / ((δ / 2) * Real.log 2) + 1) * ((m : ℝ) + 1) ^ (δ / 2) :=
        mdLogFactor_le_rpow m he
      _ ≤ (2 / ((δ / 2) * Real.log 2) + 1) * (2 * (m : ℝ)) ^ (δ / 2) := by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        gcongr
        linarith
      _ = l * (m : ℝ) ^ (δ / 2) := by
        rw [Real.mul_rpow (by norm_num) hm0.le]
        simp only [l, mul_assoc]
  have hch : ((mdChainCharge G R + R + 1 : ℕ) : ℝ) ≤
      (f + (R : ℝ) + 1) * (m : ℝ) ^ (1 + δ / 2) := by
    have hb := hcharge n Gn hGn m G hsub
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) R]
  calc
    (mdMachineCharge G R : ℝ)
        ≤ ((f + (R : ℝ) + 1) * (m : ℝ) ^ (1 + δ / 2)) *
          (l * (m : ℝ) ^ (δ / 2)) := by
            unfold mdMachineCharge
            rw [Nat.cast_mul]
            exact mul_le_mul hch hlog (by positivity) (by positivity)
    _ = (f + (R : ℝ) + 1) * l *
          ((m : ℝ) ^ (1 + δ / 2) * (m : ℝ) ^ (δ / 2)) := by ring
    _ = (f + (R : ℝ) + 1) * l * (m : ℝ) ^ (1 + δ) := by
      rw [← Real.rpow_add hm0]
      congr 2
      ring

end Lax3Proofs.Prog
