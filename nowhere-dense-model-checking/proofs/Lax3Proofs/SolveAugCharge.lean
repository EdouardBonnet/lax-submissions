import Lax3Proofs.SolveSweepAugMachine
import Lax3Proofs.SolveMdCharge
import Lax3Proofs.SolveSweepPeel

/-!
The actual cover program's sparse cost, including every lazy-heap logarithm.
Uniform constants are chosen before the graph and before its subgraph copy.
-/

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ColoringNumbers
open Lax3Proofs.Augmentation Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.CoverRoutine Lax3Proofs.CoverDegree

/-- The degree sum counts each directed arc twice in the underlying graph. -/
theorem nsOf_toGraph_eq_two_arcCount {N : ℕ} (D : Orientation N) :
    nsOf D.toGraph = 2 * arcCount D := by
  classical
  let out := fun v : Fin N => Finset.univ.filter (fun u => v ∈ D.inN u)
  have hrow : ∀ v, (D.toGraph.neighborSet v).toFinset = D.inN v ∪ out v := by
    intro v
    ext u
    simp [out, SimpleGraph.mem_neighborSet, toGraph_adj, Adjacent, or_comm]
  have hdisj : ∀ v, Disjoint (D.inN v) (out v) := by
    intro v
    exact Finset.disjoint_left.mpr fun u hu hv => D.asymm u v hu (Finset.mem_filter.mp hv).2
  have hout : (∑ v, (out v).card) = arcCount D := by
    simp only [out, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp [arcCount]
  rw [nsOf_eq_sum_ncard]
  simp_rw [Set.ncard_eq_toFinset_card', hrow, Finset.card_union_of_disjoint (hdisj _)]
  rw [Finset.sum_add_distrib, hout]
  change arcCount D + arcCount D = 2 * arcCount D
  omega

private theorem nsOf_eq_pairsIn {N : ℕ} (G : SimpleGraph (Fin N)) :
    nsOf G = (pairsIn G Finset.univ).card := by
  classical
  rw [nsOf_eq_sum_ncard, card_pairsIn]
  apply Finset.sum_congr rfl
  intro v _
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext u
  simp [mem_nbrsIn, SimpleGraph.mem_neighborSet, G.adj_comm]

/-- Every emitted ordered fraternity edge has one of the enumerated witnesses. -/
theorem nsOf_fratGraph_le {N : ℕ} (D : Orientation N) :
    nsOf (fratGraph D) ≤ fratPairCount D := by
  classical
  rw [nsOf_eq_pairsIn]
  have hsub : pairsIn (fratGraph D) Finset.univ ⊆
      Finset.univ.biUnion (fun w => D.inN w ×ˢ D.inN w) := by
    intro p hp
    obtain ⟨w, hu, hv⟩ := (mem_pairsIn.mp hp).2.2.2
    exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ _, Finset.mem_product.mpr ⟨hu, hv⟩⟩
  calc
    _ ≤ (Finset.univ.biUnion (fun w => D.inN w ×ˢ D.inN w)).card := Finset.card_le_card hsub
    _ ≤ ∑ w : Fin N, (D.inN w ×ˢ D.inN w).card := Finset.card_biUnion_le
    _ = fratPairCount D := by simp only [Finset.card_product, fratPairCount]

/-- The base orientation has precisely one arc per original edge. -/
theorem nsOf_mdChain_zero {N : ℕ} (G : SimpleGraph (Fin N)) :
    nsOf G = 2 * arcCount (mdChain G 0) := by
  have hG : (mdChain G 0).toGraph = G := by
    ext u v
    exact (baseOr_orients G (mdPerm G) u v).symm
  rw [← nsOf_toGraph_eq_two_arcCount, hG]

/-- Arc counts grow monotonically along the exact deterministic chain. -/
theorem arcCount_mdChain_mono {N : ℕ} (G : SimpleGraph (Fin N)) :
    Monotone (fun i => arcCount (mdChain G i)) := by
  apply monotone_nat_of_le_succ
  intro i
  apply Finset.sum_le_sum
  intro v _
  exact Finset.card_le_card (fun u hu =>
    ((isAugChain_mdChain G (i + 1)).2 i (by omega)).mono u v hu)

private theorem charge_parts {N : ℕ} (G : SimpleGraph (Fin N)) (R : ℕ) :
    N ≤ mdChainCharge G R ∧ arcCount (mdChain G 0) ≤ mdChainCharge G R ∧
    arcCount (mdChain G R) ≤ mdChainCharge G R ∧
    ∀ i < R, levelCharge (mdChain G i) ≤ mdChainCharge G R := by
  refine ⟨le_mdChainCharge G R, ?_, ?_, ?_⟩
  · dsimp only [mdChainCharge, mdBaseCharge, mdFinalCharge]
    omega
  · dsimp only [mdChainCharge, mdBaseCharge, mdFinalCharge]
    omega
  · intro i hi
    have hs : levelCharge (mdChain G i) ≤ ∑ j ∈ Finset.range R, levelCharge (mdChain G j) :=
      Finset.single_le_sum (f := fun j => levelCharge (mdChain G j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
    dsimp only [mdChainCharge]
    omega

theorem mdChainCharge_le_mdMachineCharge {N : ℕ} (G : SimpleGraph (Fin N)) (R : ℕ) :
    mdChainCharge G R ≤ mdMachineCharge G R := by
  have hL := one_le_mdLogFactor N
  have h := Nat.le_mul_of_pos_right (mdChainCharge G R + R + 1) hL
  dsimp only [mdMachineCharge]
  omega

theorem one_le_mdMachineCharge {N : ℕ} (G : SimpleGraph (Fin N)) (R : ℕ) :
    1 ≤ mdMachineCharge G R := by
  have hL := one_le_mdLogFactor N
  have h := Nat.le_mul_of_pos_right (mdChainCharge G R + R + 1) hL
  dsimp only [mdMachineCharge]
  omega

private theorem heap_le_mdMachineCharge {N : ℕ} (G F : SimpleGraph (Fin N)) (R : ℕ)
    (hs : nsOf F ≤ 2 * mdChainCharge G R) :
    KmdPeel N (nsOf F) ≤ 800 * mdMachineCharge G R := by
  have hN := le_mdChainCharge G R
  have hB : N + nsOf F + 1 ≤ 4 * (mdChainCharge G R + R + 1) := by omega
  calc
    _ ≤ 200 * (N + nsOf F + 1) * mdLogFactor N := KmdPeel_le_mdLogFactor (nsOf_le F)
    _ ≤ 200 * (4 * (mdChainCharge G R + R + 1)) * mdLogFactor N :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hB)
    _ = 800 * mdMachineCharge G R := by dsimp only [mdMachineCharge]; ring

private theorem base_le_mdMachineCharge {N : ℕ} (G : SimpleGraph (Fin N)) (R : ℕ) :
    AugMachine.baseCost G (nsOf G) ≤ 2000 * mdMachineCharge G R := by
  have hp := charge_parts G R
  have hc := mdChainCharge_le_mdMachineCharge G R
  have h1 := one_le_mdMachineCharge G R
  have hN := hp.1.trans hc
  have hA := hp.2.1.trans hc
  have hh := heap_le_mdMachineCharge G G R (by rw [nsOf_mdChain_zero]; omega)
  rw [AugMachine.baseCost_eq, nsOf_mdChain_zero]
  rw [nsOf_mdChain_zero] at hh
  omega

private theorem round_le_mdMachineCharge {N : ℕ} (G : SimpleGraph (Fin N)) (R i : ℕ) (hi : i < R) :
    AugMachine.roundCost (mdChain G i) ≤ 3000 * mdMachineCharge G R := by
  have hp := charge_parts G R
  have hc := mdChainCharge_le_mdMachineCharge G R
  have h1 := one_le_mdMachineCharge G R
  have hN := hp.1.trans hc
  have hlev := hp.2.2.2 i hi
  have hAN : arcCount (mdChain G (i + 1)) ≤ mdMachineCharge G R :=
    (arcCount_mdChain_mono G (show i + 1 ≤ R by omega)).trans (hp.2.2.1.trans hc)
  have hS := nsOf_fratGraph_le (mdChain G i)
  have hh := heap_le_mdMachineCharge G (fratGraph (mdChain G i)) R (by
    dsimp only [levelCharge] at hlev
    omega)
  rw [AugMachine.roundCost_eq]
  change 289 * arcCount (mdChain G i) + 287 * transPairCount (mdChain G i) +
    439 * fratPairCount (mdChain G i) + 70 * nsOf (fratGraph (mdChain G i)) +
    56 * arcCount (mdChain G (i + 1)) + 185 * N + 162 +
    KmdPeel N (nsOf (fratGraph (mdChain G i))) ≤ _
  dsimp only [levelCharge] at hlev
  omega

private theorem finish_le_mdMachineCharge {N : ℕ} (G : SimpleGraph (Fin N)) (R : ℕ) :
    AugMachine.finishCost (mdChain G R) ≤ 600 * mdMachineCharge G R := by
  have hp := charge_parts G R
  have hc := mdChainCharge_le_mdMachineCharge G R
  have h1 := one_le_mdMachineCharge G R
  have hN := hp.1.trans hc
  have hA := hp.2.2.1.trans hc
  rw [AugMachine.finishCost_eq, nsOf_toGraph_eq_two_arcCount]
  omega

/-- The complete computed ordering phase: augmentation, its final heap peel,
and rebuilding the original graph in that computed order. -/
noncomputable def augOrderCost {N : ℕ} (G : SimpleGraph (Fin N)) (R : ℕ) : ℕ :=
  AugMachine.cost G (nsOf G) R + KmdPeel N (nsOf (mdChain G R).toGraph) + bldCoreK N (nsOf G)

/-- An explicit round-only coefficient pays every actual sparse scan and heap.
The common logarithm remains present in `mdMachineCharge`. -/
theorem augOrderCost_le_mdMachineCharge {N : ℕ} (G : SimpleGraph (Fin N)) (R : ℕ) :
    augOrderCost G R ≤ 4000 * (R + 1) * mdMachineCharge G R := by
  have hp := charge_parts G R
  have hc := mdChainCharge_le_mdMachineCharge G R
  have h1 := one_le_mdMachineCharge G R
  have hN := hp.1.trans hc
  have hA := hp.2.1.trans hc
  have hb := base_le_mdMachineCharge G R
  have hf := finish_le_mdMachineCharge G R
  have hh := heap_le_mdMachineCharge G (mdChain G R).toGraph R (by
    rw [nsOf_toGraph_eq_two_arcCount]
    omega)
  have hbuild : bldCoreK N (nsOf G) ≤ 220 * mdMachineCharge G R := by
    rw [bldCoreK, nsOf_mdChain_zero]
    omega
  have hs : (∑ i ∈ Finset.range R, AugMachine.roundCost (mdChain G i))
      ≤ R * (3000 * mdMachineCharge G R) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range R, 3000 * mdMachineCharge G R :=
        Finset.sum_le_sum fun i hi => round_le_mdMachineCharge G R i (Finset.mem_range.mp hi)
      _ = _ := by simp
  rw [augOrderCost, AugMachine.cost, AugMachine.coreCost, AugMachine.loopCost_eq]
  nlinarith

/-- Uniform almost-linear cost for the actual computed ordering, on nonempty
subgraph copies of every class member. Constants precede the graph. -/
theorem exists_augOrderCost_le (C : GraphClass) (hC : NowhereDense C) (R : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : ℝ, 0 ≤ f ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn → 0 < m →
        (augOrderCost G R : ℝ) ≤ f * (m : ℝ) ^ (1 + δ) := by
  obtain ⟨f, hf, htime⟩ := exists_mdMachineCharge_le C hC R δ hδ
  refine ⟨(4000 * (R + 1) : ℕ) * f, by positivity, ?_⟩
  intro n Gn hGn m G hsub hm
  calc
    _ ≤ ((4000 * (R + 1) : ℕ) : ℝ) * (mdMachineCharge G R : ℝ) := by
      exact_mod_cast augOrderCost_le_mdMachineCharge G R
    _ ≤ ((4000 * (R + 1) : ℕ) : ℝ) * (f * (m : ℝ) ^ (1 + δ)) := by
      gcongr
      exact htime n Gn hGn m G hsub hm
    _ = _ := by ring

/-- The actual full cover cost, with the pinned `3r` augmentation rounds. -/
noncomputable def actualCoverCost {N : ℕ} (G : SimpleGraph (Fin N)) (r : ℕ) : ℕ :=
  augOrderCost G (3 * r) + peelK G ((mdOrderingRoutine (3 * r)) N G).order r

/-- The machine wrapper's four actual budgets, in evaluation order. -/
theorem actualCoverCost_eq {N : ℕ} (G : SimpleGraph (Fin N)) (r : ℕ) :
    actualCoverCost G r = AugMachine.cost G (nsOf G) (3 * r) +
      KmdPeel N (nsOf (mdChain G (3 * r)).toGraph) + bldCoreK N (nsOf G) +
      peelK G ((mdOrderingRoutine (3 * r)) N G).order r := rfl

set_option maxRecDepth 2048 in
/-- The concrete sweep inherits the quadratic weak-reachability charge,
including all of its linear and constant overhead. -/
theorem peelK_le_rpow {N : ℕ} (G : SimpleGraph (Fin N)) (π : Equiv.Perm (Fin N))
    (r : ℕ) (hr : 1 ≤ r) {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hN : 0 < N)
    (hD : ∀ x, (wreach G π (2 * r) x).ncard ≤ ⌈c * (N : ℝ) ^ δ⌉₊) :
    (peelK G π r : ℝ) ≤ (1280 * (c + 1) ^ 2 + 512) * (N : ℝ) ^ (1 + 2 * δ) := by
  classical
  let D := ⌈c * (N : ℝ) ^ δ⌉₊
  have hp := peelK_le_sweepCharge G π r hr hD
  have hs := Impl.sweepCharge_le hr hD
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX1 : (1 : ℝ) ≤ (N : ℝ) ^ δ := one_le_rpow hN hδ.le
  have hceil : (D : ℝ) ≤ (c + 1) * (N : ℝ) ^ δ := by
    have hh : (D : ℝ) ≤ c * (N : ℝ) ^ δ + 1 :=
      (Nat.ceil_lt_add_one (mul_nonneg hc (Real.rpow_nonneg (Nat.cast_nonneg N) δ))).le
    nlinarith
  have hpow : (N : ℝ) ^ (1 + 2 * δ) = (N : ℝ) * ((N : ℝ) ^ δ * (N : ℝ) ^ δ) := by
    rw [show (1 : ℝ) + 2 * δ = 1 + (δ + δ) by ring, Real.rpow_add hN0,
      Real.rpow_one, Real.rpow_add hN0]
  have hsw : (Impl.sweepCharge G π r D : ℝ) ≤
      2 * (c + 1) ^ 2 * (N : ℝ) ^ (1 + 2 * δ) := by
    calc
      _ ≤ ((2 * D * (N * D) : ℕ) : ℝ) := by exact_mod_cast hs
      _ = 2 * (D : ℝ) * ((N : ℝ) * (D : ℝ)) := by push_cast; ring
      _ ≤ 2 * ((c + 1) * (N : ℝ) ^ δ) * ((N : ℝ) * ((c + 1) * (N : ℝ) ^ δ)) := by
        gcongr
      _ = _ := by rw [hpow]; ring
  have hNP : (N : ℝ) ≤ (N : ℝ) ^ (1 + 2 * δ) := by
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hP1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 + 2 * δ) := one_le_rpow hN (by linarith)
  calc
    _ ≤ 640 * (Impl.sweepCharge G π r D : ℝ) + 256 * (N : ℝ) + 256 := by
      exact_mod_cast hp
    _ ≤ 640 * (2 * (c + 1) ^ 2 * (N : ℝ) ^ (1 + 2 * δ)) +
        256 * (N : ℝ) ^ (1 + 2 * δ) + 256 * (N : ℝ) ^ (1 + 2 * δ) := by
      gcongr
      nlinarith [hP1]
    _ = _ := by ring

/-- Uniform degree and time for the complete concrete cover routine. The
constants precede every member and subgraph copy; nonempty carriers are the
ones on which the recursive driver invokes the cover. -/
theorem exists_actualCoverCost_le (C : GraphClass) (hC : NowhereDense C)
    (r : ℕ) (hr : 1 ≤ r) (δ : ℝ) (hδ : 0 < δ) :
    ∃ cdeg f : ℝ, 0 ≤ cdeg ∧ 0 ≤ f ∧
      ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
        ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
          (∀ v : Fin m, (wreach G ((mdOrderingRoutine (3 * r)) m G).order (2 * r) v).ncard
            ≤ ⌈cdeg * (m : ℝ) ^ δ⌉₊) ∧
          (0 < m → (actualCoverCost G r : ℝ) ≤ f * (m : ℝ) ^ (1 + 2 * δ)) := by
  obtain ⟨c, hc, hdeg⟩ := exists_wreach_degree_mdOrderingRoutine C hC r (3 * r) r le_rfl
    (Lax3Proofs.Driver.two_mul_le_two_pow hr) δ hδ
  obtain ⟨f, hf, htime⟩ := exists_augOrderCost_le C hC (3 * r) (2 * δ) (by linarith)
  refine ⟨c, f + (1280 * (c + 1) ^ 2 + 512), hc, by positivity, ?_⟩
  intro n Gn hGn m G hsub
  have hd := hdeg n Gn hGn m G hsub
  refine ⟨hd, fun hm => ?_⟩
  have hs := peelK_le_rpow G ((mdOrderingRoutine (3 * r)) m G).order r hr hc hδ hm hd
  have ho := htime n Gn hGn m G hsub hm
  rw [actualCoverCost, Nat.cast_add]
  calc
    _ ≤ f * (m : ℝ) ^ (1 + 2 * δ) + (1280 * (c + 1) ^ 2 + 512) * (m : ℝ) ^ (1 + 2 * δ) :=
      add_le_add ho hs
    _ = _ := by ring

end Lax3Proofs.Prog
