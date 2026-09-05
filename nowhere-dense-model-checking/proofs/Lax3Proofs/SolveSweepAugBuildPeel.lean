import Lax3Proofs.SolveSweepAugCsr
import Lax3Proofs.SolveSweepBuild

/-!
# Padded CSR to a computed min-degree rank

Identity ranks are initialized in one carrier pass, the existing adjacency
builder reads the padded CSR through its exact window, and the heap peel
computes `mdRank`. No previous rank contents are assumed. The composition
keeps the actual build and heap budgets, including the heap logarithm.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning Lax67Proofs.Reasoning.Lib
open Lax3Proofs.CoverRoutine (mdRank mdPerm mdPerm_val)

/-- The CSR extent is exactly the graph's degree sum. -/
theorem agPaddedCsr_mass_eq {N M : ℕ} {o t : String} {rows : Fin N → List (Fin N)}
    {off : ℕ → ℕ} {σ : Env} {G : SimpleGraph (Fin N)}
    (hc : AgCsrRows o t M rows off σ) (hnd : ∀ v, (rows v).Nodup)
    (hadj : ∀ u v, u ∈ rows v ↔ G.Adj v u) : M = nsOf G := by
  classical
  have hlen : ∀ v, (rows v).length = (G.neighborSet v).ncard := by
    intro v
    have he : (↑(rows v).toFinset : Set (Fin N)) = G.neighborSet v := by
      ext u
      simpa using hadj u v
    rw [← he, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hnd v)]
  have hstep : ∀ v : Fin N, off (v + 1) = off v + (G.neighborSet v).ncard := by
    intro v
    rw [hc.off_step, hlen]
  exact hc.off_last.symm.trans (offF_eq_sum hc.off_zero hstep N le_rfl)

/-- Run the public adjacency builder directly on padded compressed rows. -/
theorem agPaddedBuild_run {B N M : ℕ} {o t ra ao aj dg mt od iv uv wv nN nS : String}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {σ : Env}
    {rows : Fin N → List (Fin N)} {off : ℕ → ℕ}
    (hc : AgCsrRows o t M rows off σ)
    (hnd : ∀ v, (rows v).Nodup) (hadj : ∀ u v, u ∈ rows v ↔ G.Adj v u)
    (hot : o ≠ t) (hrao : ra ≠ o) (hrat : ra ≠ t)
    (hW : [ao, aj, dg, mt, od].Nodup)
    (hWr : ∀ a ∈ [ao, aj, dg, mt, od], a ≠ o ∧ a ≠ t ∧ a ≠ ra)
    (hV : [iv, uv, wv].Nodup)
    (hVr : ∀ y ∈ [iv, uv, wv], y ≠ nN ∧ y ≠ nS)
    (hNB : N + 1 < B) (hMB : M < B)
    (hn : σ.vars nN = N) (hm : σ.vars nS = M) (hrank : RankArr ra π σ)
    (halloc : N + 1 ≤ (σ.arrs ao).length ∧ M ≤ (σ.arrs aj).length ∧
      N ≤ (σ.arrs dg).length ∧ M ≤ (σ.arrs mt).length ∧ N ≤ (σ.arrs od).length) :
    ∃ τ, Run B (bldCoreCom o t ra ao aj dg mt od iv uv wv nN nS) σ τ (bldCoreK N M) ∧
      OrdArr od π τ ∧ DelAdjSt ao aj dg mt G ∅ τ := by
  let ws := agCsrWs o t N M
  have hw : ∀ a, a ≠ o → a ≠ t → ws a = none := by
    intro a hao hat
    simp [ws, agCsrWs, hao, hat]
  have hwout : ∀ a ∈ [ao, aj, dg, mt, od], ws a = none := by
    intro a ha
    exact hw a (hWr a ha).1 (hWr a ha).2.1
  have hrr : RankArr ra π (winA ws σ) := rankArr_of_eq hrank
    (arrs_winA_none (hw ra hrao hrat) σ)
  obtain ⟨hfit, hgraph⟩ := hc.graphCsr_window hot hnd hadj
  have hb := specWindow (bldCore_spec B N M o t ra ao aj dg mt od iv uv wv nN nS
    G π hW hWr hV hVr hNB hMB) ws
  obtain ⟨τ, hr, _, ⟨hord, hdel⟩, _, _⟩ := hb.run
    ⟨hfit, hgraph, hn, hm, hrr,
      by rw [arrs_winA_none (hwout ao (by simp))]; exact halloc.1,
      by rw [arrs_winA_none (hwout aj (by simp))]; exact halloc.2.1,
      by rw [arrs_winA_none (hwout dg (by simp))]; exact halloc.2.2.1,
      by rw [arrs_winA_none (hwout mt (by simp))]; exact halloc.2.2.2.1,
      by rw [arrs_winA_none (hwout od (by simp))]; exact halloc.2.2.2.2⟩
  refine ⟨τ, hr, ordArr_of_eq hord (arrs_winA_none (hwout od (by simp)) τ).symm, ?_⟩
  exact hdel.of_eq (arrs_winA_none (hwout ao (by simp)) τ).symm
    (arrs_winA_none (hwout aj (by simp)) τ).symm
    (arrs_winA_none (hwout dg (by simp)) τ).symm
    (arrs_winA_none (hwout mt (by simp)) τ).symm


/-- The padded build adapter with its finite write frames and stable lengths. -/
theorem agPaddedBuild_spec {B N M : ℕ} {o t ra ao aj dg mt od iv uv wv nN nS : String}
    {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)}
    {rows : Fin N → List (Fin N)} {off : ℕ → ℕ}
    (hnd : ∀ v, (rows v).Nodup) (hadj : ∀ u v, u ∈ rows v ↔ G.Adj v u)
    (hot : o ≠ t) (hrao : ra ≠ o) (hrat : ra ≠ t)
    (hW : [ao, aj, dg, mt, od].Nodup)
    (hWr : ∀ a ∈ [ao, aj, dg, mt, od], a ≠ o ∧ a ≠ t ∧ a ≠ ra)
    (hV : [iv, uv, wv].Nodup)
    (hVr : ∀ y ∈ [iv, uv, wv], y ≠ nN ∧ y ≠ nS)
    (hNB : N + 1 < B) (hMB : M < B) :
    Spec B (fun σ => AgCsrRows o t M rows off σ ∧
        σ.vars nN = N ∧ σ.vars nS = M ∧ RankArr ra π σ ∧
        N + 1 ≤ (σ.arrs ao).length ∧ M ≤ (σ.arrs aj).length ∧
        N ≤ (σ.arrs dg).length ∧ M ≤ (σ.arrs mt).length ∧ N ≤ (σ.arrs od).length)
      (bldCoreCom o t ra ao aj dg mt od iv uv wv nN nS)
      (fun σ τ => OrdArr od π τ ∧ DelAdjSt ao aj dg mt G ∅ τ ∧
        (∀ a, a ∉ [ao, aj, dg, mt, od] → τ.arrs a = σ.arrs a) ∧
        (∀ y, y ∉ [iv, uv, wv] → τ.vars y = σ.vars y) ∧
        (∀ a, (τ.arrs a).length = (σ.arrs a).length)) (bldCoreK N M) := by
  rintro σ ⟨hc, hn, hm, hrank, halloc⟩
  obtain ⟨τ, hr, hord, hdel⟩ := agPaddedBuild_run hc hnd hadj hot hrao hrat
    hW hWr hV hVr hNB hMB hn hm hrank halloc
  refine ⟨τ, hr, hord, hdel, ?_, ?_, run_arrs_length_eq hr⟩
  · intro a ha
    exact hr.frame_arr a (fun hm => ha (warrs_bldCoreCom _ _ _ _ _ _ _ _ _ _ _ _ _ hm))
  · intro y hy
    exact hr.frame_var y (fun hm => hy (wvars_bldCoreCom _ _ _ _ _ _ _ _ _ _ _ _ _ hm))

/-- Initialize the rank array to the identity, once over the carrier. -/
def agIdentityRankCom (nN ra iv : String) : Com :=
  .seq (.assign iv (.lit 0))
    (.while (.lt (.var iv) (.var nN))
      (.seq (.store ra (.var iv) (.var iv))
        (.assign iv (.add (.var iv) (.lit 1)))))

/-- Identity-rank initialization costs `11N+6` and reads no array contents. -/
theorem agIdentityRank_spec {B N : ℕ} {nN ra iv : String}
    (hiv : iv ≠ nN) (hNB : N < B) :
    Spec B (fun σ => σ.vars nN = N ∧ N ≤ (σ.arrs ra).length)
      (agIdentityRankCom nN ra iv)
      (fun σ τ => RankArr ra (Equiv.refl (Fin N)) τ ∧
        (∀ a, a ≠ ra → τ.arrs a = σ.arrs a) ∧
        (∀ y, y ≠ iv → τ.vars y = σ.vars y) ∧
        (∀ a, (τ.arrs a).length = (σ.arrs a).length)) (11 * N + 6) := by
  let I : Env → Prop := fun σ => σ.vars nN = N ∧ σ.vars iv ≤ N ∧
    N ≤ (σ.arrs ra).length ∧ ∀ z, z < σ.vars iv → (σ.arrs ra).getD z 0 = z
  have hbody : Spec B (fun σ => I σ ∧ σ.vars iv < N)
      (.seq (.store ra (.var iv) (.var iv)) (.assign iv (.add (.var iv) (.lit 1))))
      (fun σ τ => I τ ∧ τ.vars iv = σ.vars iv + 1) 7 := by
    rintro σ ⟨⟨hn, hi, hL, hvals⟩, hiN⟩
    run_vcg
    dsimp [I]
    simp only [Ne.symm hiv, if_false, if_true, List.length_set]
    refine ⟨⟨hn, by omega, hL, ?_⟩, by trivial⟩
    intro z hz
    rw [getD_set _ _ _ (by omega)]
    by_cases he : z = σ.vars iv
    · rw [if_pos he, he]
    · rw [if_neg he]
      exact hvals z (by omega)
  have hloop := Spec.forRangeZero iv nN I N 7 hNB
    (fun _ h => h.2.1) (fun _ h => h.1) hbody
  rintro σ ⟨hn, hL⟩
  obtain ⟨τ, hr, hI, hi⟩ := hloop.run (σ := σ) (by simp [I, Ne.symm hiv, hn, hL])
  refine ⟨τ, hr.mono (by omega), ⟨hI.2.2.1, ?_⟩, ?_, ?_, run_arrs_length_eq hr⟩
  · intro v
    exact hI.2.2.2 v (by omega)
  · intro a ha
    exact hr.frame_arr a (by simp [Com.warrs, ha])
  · intro y hy
    exact hr.frame_var y (by simp [Com.wvars, hy])

/-- Build adjacency with identity ranks initialized from the carrier cell. -/
def agBuildInitCom (o t ra ao aj dg mt od bi bu bw nN nS : String) : Com :=
  .seq (agIdentityRankCom nN ra bi) (bldCoreCom o t ra ao aj dg mt od bi bu bw nN nS)

/-- The initializer's linear cost plus the unchanged adjacency-build cost. -/
def agBuildInitK (N M : ℕ) : ℕ := 11 * N + 6 + bldCoreK N M

private theorem agBuildInit_names {o t ra ao aj dg mt od : String}
    (hd : [o, t, ra, ao, aj, dg, mt, od].Nodup) :
    o ≠ t ∧ ra ≠ o ∧ ra ≠ t ∧ [ao, aj, dg, mt, od].Nodup ∧
    (∀ a ∈ [ao, aj, dg, mt, od], a ≠ o ∧ a ≠ t ∧ a ≠ ra) ∧
    ra ∉ [ao, aj, dg, mt, od] := by
  have hW : [ao, aj, dg, mt, od].Nodup := by
    simpa using hd.sublist (List.drop_sublist 3 [o, t, ra, ao, aj, dg, mt, od])
  have hD := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at hD
  refine ⟨?_, ?_, ?_, hW, ?_, ?_⟩
  · tauto
  · exact Ne.symm hD.1.2.1
  · exact Ne.symm hD.2.1.1
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> tauto
  · simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true]
    tauto

/-- Identity initialization and padded adjacency construction. The precondition
contains only the real CSR data, its size cells, and raw allocation lengths. -/
theorem agBuildInit_spec {B N M : ℕ} {o t ra ao aj dg mt od bi bu bw nN nS : String}
    {G : SimpleGraph (Fin N)} {rows : Fin N → List (Fin N)} {off : ℕ → ℕ}
    (hnd : ∀ v, (rows v).Nodup) (hadj : ∀ u v, u ∈ rows v ↔ G.Adj v u)
    (hd : [o, t, ra, ao, aj, dg, mt, od].Nodup)
    (hV : [bi, bu, bw].Nodup)
    (hVr : ∀ y ∈ [bi, bu, bw], y ≠ nN ∧ y ≠ nS)
    (hB : N * N + 4 * N + 4 ≤ B) :
    Spec B (fun σ => AgCsrRows o t M rows off σ ∧ σ.vars nN = N ∧ σ.vars nS = M ∧
        N ≤ (σ.arrs ra).length ∧ N + 1 ≤ (σ.arrs ao).length ∧
        M ≤ (σ.arrs aj).length ∧ N ≤ (σ.arrs dg).length ∧
        M ≤ (σ.arrs mt).length ∧ N ≤ (σ.arrs od).length)
      (agBuildInitCom o t ra ao aj dg mt od bi bu bw nN nS)
      (fun σ τ => RankArr ra (Equiv.refl (Fin N)) τ ∧ OrdArr od (Equiv.refl (Fin N)) τ ∧
        DelAdjSt ao aj dg mt G ∅ τ ∧
        (∀ a, a ∉ [ra, ao, aj, dg, mt, od] → τ.arrs a = σ.arrs a) ∧
        (∀ y, y ∉ [bi, bu, bw] → τ.vars y = σ.vars y) ∧
        (∀ a, (τ.arrs a).length = (σ.arrs a).length)) (agBuildInitK N M) := by
  obtain ⟨hot, hrao, hrat, hW, hWr, hraFree⟩ := agBuildInit_names hd
  rintro σ ⟨hc, hn, hm, hraL, haoL, hajL, hdgL, hmtL, hodL⟩
  have hmass := agPaddedCsr_mass_eq hc hnd hadj
  have hM : M ≤ N * N := by rw [hmass]; exact nsOf_le G
  have hbi := hVr bi (by simp)
  obtain ⟨σ1, hri, hriRank, hia, hiv, hil⟩ :=
    (agIdentityRank_spec hbi.1 (B := B) (by omega)).run ⟨hn, hraL⟩
  obtain ⟨σ2, hrb, hord, hdel, hba, hbv, hbl⟩ :=
    (agPaddedBuild_spec (B := B) (π := Equiv.refl (Fin N)) hnd hadj hot hrao hrat
      hW hWr hV hVr (by omega) (by omega)).run
      ⟨hc.of_eq (hia o (Ne.symm hrao)) (hia t (Ne.symm hrat)),
        (hiv nN (Ne.symm hbi.1)).trans hn, (hiv nS (Ne.symm hbi.2)).trans hm, hriRank,
        by rw [hil]; exact haoL, by rw [hil]; exact hajL, by rw [hil]; exact hdgL,
        by rw [hil]; exact hmtL, by rw [hil]; exact hodL⟩
  refine ⟨σ2, hri.seq hrb, rankArr_of_eq hriRank (hba ra hraFree), hord, hdel, ?_, ?_, ?_⟩
  · intro a ha
    rw [List.mem_cons, not_or] at ha
    exact (hba a ha.2).trans (hia a ha.1)
  · intro y hy
    have hne : y ≠ bi := fun he => hy (by simp [he])
    exact (hbv y hy).trans (hiv y hne)
  · intro a
    exact (hbl a).trans (hil a)

/-- Initialize, build the deletable adjacency, then compute the min-degree ranks. -/
def agBuildPeelCom (o t ra ao aj dg mt od hp bi bu bw nN nS
    hsv tv xv yv kv dv vv zv pi rc pw : String) : Com :=
  .seq (agBuildInitCom o t ra ao aj dg mt od bi bu bw nN nS)
    (mdPeelCom nN ao aj dg ra hp hsv tv xv yv kv dv vv zv pi rc pw)

/-- The real summed budget; the heap logarithm stays inside `KmdPeel`. -/
def agBuildPeelK (N M : ℕ) : ℕ := agBuildInitK N M + KmdPeel N M

/-- Compute exact `mdRank` from padded CSR and uninitialized rank/heap regions.
There is no precomputed-order premise. The source size cell may be the occupied
size of the source key dictionary, and survives all three phases. -/
theorem agBuildPeel_spec {B N M : ℕ}
    {o t ra ao aj dg mt od hp bi bu bw nN nS hsv tv xv yv kv dv vv zv pi rc pw : String}
    {G : SimpleGraph (Fin N)} {rows : Fin N → List (Fin N)} {off : ℕ → ℕ}
    (hnd : ∀ v, (rows v).Nodup) (hadj : ∀ u v, u ∈ rows v ↔ G.Adj v u)
    (hd : [o, t, ra, ao, aj, dg, mt, od, hp].Nodup)
    (hVB : [bi, bu, bw].Nodup)
    (hVr : ∀ y ∈ [bi, bu, bw], y ≠ nN ∧ y ≠ nS)
    (hVM : [nN, nS, hsv, tv, xv, yv, kv, dv, vv, zv, pi, rc, pw].Nodup)
    (hB : N * N + 4 * N + 4 ≤ B) :
    Spec B (fun σ => AgCsrRows o t M rows off σ ∧ σ.vars nN = N ∧ σ.vars nS = M ∧
        N ≤ (σ.arrs ra).length ∧ N + 1 ≤ (σ.arrs ao).length ∧
        M ≤ (σ.arrs aj).length ∧ N ≤ (σ.arrs dg).length ∧
        M ≤ (σ.arrs mt).length ∧ N ≤ (σ.arrs od).length ∧ N * N + N ≤ (σ.arrs hp).length)
      (agBuildPeelCom o t ra ao aj dg mt od hp bi bu bw nN nS hsv tv xv yv kv dv vv zv pi rc pw)
      (fun σ τ => RankArr ra (mdPerm G) τ ∧
        (∀ u : Fin N, (τ.arrs ra).getD u 0 = mdRank G u) ∧
        (∀ a, a ∉ [ra, ao, aj, dg, mt, od, hp] → τ.arrs a = σ.arrs a) ∧
        (∀ y, y ∉ [bi, bu, bw] ++ [hsv, tv, xv, yv, kv, dv, vv, zv, pi, rc, pw] →
          τ.vars y = σ.vars y) ∧
        (∀ a, (τ.arrs a).length = (σ.arrs a).length)) (agBuildPeelK N M) := by
  have hdInit : [o, t, ra, ao, aj, dg, mt, od].Nodup := by
    simpa using hd.sublist (List.take_sublist 8 [o, t, ra, ao, aj, dg, mt, od, hp])
  have hdPeel : [hp, ra, dg, ao, aj].Nodup := by
    have h := hd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      not_false_eq_true, List.nodup_nil, and_true] at h ⊢
    repeat' apply And.intro
    all_goals tauto
  have hvPeel : [nN, hsv, tv, xv, yv, kv, dv, vv, zv, pi, rc, pw].Nodup := by
    obtain ⟨hnfree, htail⟩ := List.nodup_cons.mp hVM
    obtain ⟨_, hrest⟩ := List.nodup_cons.mp htail
    exact List.nodup_cons.mpr ⟨fun h => hnfree (List.mem_cons_of_mem nS h), hrest⟩
  rintro σ ⟨hc, hn, hm, hraL, haoL, hajL, hdgL, hmtL, hodL, hhpL⟩
  have hmass := agPaddedCsr_mass_eq hc hnd hadj
  obtain ⟨σ1, hrb, hrank1, _, hdel1, hba, hbv, hbl⟩ :=
    (agBuildInit_spec hnd hadj hdInit hVB hVr hB).run
      ⟨hc, hn, hm, hraL, haoL, hajL, hdgL, hmtL, hodL⟩
  have hnFree : nN ∉ [bi, bu, bw] := by
    intro h
    exact (hVr nN h).1 rfl
  obtain ⟨σ2, hrm, ⟨hrankLen, hrankVal⟩, hma, hmv, hml⟩ :=
    (mdPeelCore_spec (B := B) (N := N) (F := G) (nNm := nN)
      (ao := ao) (aj := aj) (dg := dg) (ra := ra) (hp := hp)
      (hsv := hsv) (tv := tv) (xv := xv) (yv := yv) (kv := kv) (dv := dv)
      (vv := vv) (zv := zv) (iv := pi) (rc := rc) (wv := pw) mt hvPeel hdPeel hB).run
      ⟨hdel1, (hbv nN hnFree).trans hn, hrank1.1, by rw [hbl]; exact hhpL⟩
  rw [← hmass] at hrm
  refine ⟨σ2, hrb.seq hrm, ⟨hrankLen, fun u => (hrankVal u).trans (mdPerm_val G u).symm⟩,
    hrankVal, ?_, ?_, ?_⟩
  · intro a ha
    have hfB : a ∉ [ra, ao, aj, dg, mt, od] := by
      simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true] at ha ⊢
      tauto
    have hfM : a ∉ [hp, dg, ra] := by
      simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true] at ha ⊢
      tauto
    exact (hma a hfM).trans (hba a hfB)
  · intro y hy
    rw [List.mem_append, not_or] at hy
    exact (hmv y hy.2).trans (hbv y hy.1)
  · intro a
    exact (hml a).trans (hbl a)

/-- The combined adapter's sole word-room premise follows from the fixed
quadratic word bound for every encoded input, with `1 ≤ q`. -/
theorem agBuildPeel_word_room {N n q : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (henc : Lax11.GraphEncoding.EncodesGraph x n G) (hN : N ≤ n) (hq : 1 ≤ q) :
    N * N + 4 * N + 4 ≤ mcB q x := by
  have hnx : n + 3 ≤ x.length := by
    have := henc.length_eq
    have := henc.vertexCount_eq
    omega
  have hle : N + 2 ≤ x.length + 1 := by omega
  have hs : (N + 2) * (N + 2) ≤ (x.length + 1) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hle hle
  have hqB : (x.length + 1) ^ 2 ≤ mcB q x := Nat.le_mul_of_pos_left _ hq
  calc N * N + 4 * N + 4 = (N + 2) * (N + 2) := by ring
    _ ≤ _ := hs.trans hqB

end Lax3Proofs.Prog
