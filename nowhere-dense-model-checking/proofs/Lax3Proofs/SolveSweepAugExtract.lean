import Lax3Proofs.SolveSweepAug

/-!
# Extracting the actual CSR entries as sparse pair keys

The base orientation starts from the arena's real adjacency rows. This pass
reads each row once and records its occupied pair keys without scanning the
reserved pair-key universe.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning

private theorem agxName_ne {xs : List String} (h : xs.Nodup) (i j : ℕ)
    (hi : i < xs.length) (hj : j < xs.length) (hne : i ≠ j) :
    xs[i] ≠ xs[j] := fun he => hne (h.getElem_inj_iff.mp he)

private theorem agxEvalVar {B k : ℕ} {σ : Env} {x : String}
    (hx : σ.vars x = k) (hk : k < B) : (Expr.var x).evalB B σ = some k := by
  rw [← hx]
  exact evalB_var (by omega)

/-- The CSR extent is exactly the sum of its actual row lengths. -/
theorem AgCsrRows.sum_lengths {o t : String} {N ns : ℕ}
    {rows : Fin N → List (Fin N)} {off : ℕ → ℕ} {σ : Env}
    (h : AgCsrRows o t ns rows off σ) : (∑ v, (rows v).length) = ns := by
  let f := fun i => if hi : i < N then (rows ⟨i, hi⟩).length else 0
  have hp : ∀ k, k ≤ N → (∑ i ∈ Finset.range k, f i) = off k := by
    intro k
    induction k with
    | zero => intro _; simp [h.off_zero]
    | succ k ih =>
      intro hk
      have hkN : k < N := by omega
      rw [Finset.sum_range_succ, ih (by omega), h.off_step ⟨k, hkN⟩]
      dsimp only [f]
      rw [dif_pos hkN]
  calc
    (∑ v, (rows v).length) = ∑ i ∈ Finset.range N, f i := by
      rw [Finset.sum_range]
      exact Finset.sum_congr rfl fun v _ => by dsimp only [f]; rw [dif_pos v.isLt]
    _ = off N := hp N le_rfl
    _ = ns := h.off_last

def agxPart {N : ℕ} (rows : Fin N → List (Fin N)) (i : ℕ) : List ℕ :=
  ((List.finRange N).take i).flatMap fun v => (rows v).map fun u => agArcKey (u, v)

private theorem agxPart_succ {N : ℕ} (rows : Fin N → List (Fin N)) {i : ℕ} (hi : i < N) :
    agxPart rows (i + 1) = agxPart rows i ++ (rows ⟨i, hi⟩).map (fun u => agArcKey (u, ⟨i, hi⟩)) := by
  rw [agxPart, List.take_succ_eq_append_getElem (by simpa using hi)]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.getElem_finRange]
  rfl

theorem agxPart_full {N : ℕ} (rows : Fin N → List (Fin N)) :
    agxPart rows N = (agArcCandidates rows).map agArcKey := by
  have ht : (List.finRange N).take N = List.finRange N := by
    simpa only [List.length_finRange] using (List.take_length (l := List.finRange N))
  simp [agxPart, agArcCandidates, List.map_flatMap, List.map_map, Function.comp_def, ht]

def agxBody (o t ix ky sz ov rv fv kv tv hv iv lm nN : String) : Com :=
  .seq (.assign rv (.var ov))
    (.seq (.assign fv (.var ov))
      (.seq (agDictRow o t ix ky sz rv fv kv tv hv iv lm nN false)
        (.assign ov (.add (.var ov) (.lit 1)))))

/-- Reset one occupied dictionary and enumerate the actual CSR rows. -/
def agxExtract (o t ix ky sz ov rv fv kv tv hv iv lm nN : String) : Com :=
  .seq (.assign sz (.lit 0))
    (.seq (.assign ov (.lit 0))
      (.while (.lt (.var ov) (.var nN)) (agxBody o t ix ky sz ov rv fv kv tv hv iv lm nN)))

set_option maxHeartbeats 800000 in
/-- Materialize the actual CSR entries as unique occupied pair keys. The
budget is linear in the CSR extent and vertex count. -/
theorem agxExtract_run {B N ns : ℕ}
    (o t ix ky sz ov rv fv kv tv hv iv lm nN : String)
    (harr : ix ≠ ky) (hread : o ≠ ix ∧ o ≠ ky ∧ t ≠ ix ∧ t ≠ ky)
    (hvs : ([nN, ov, rv, fv, sz, kv, tv, hv, iv, lm] : List String).Nodup)
    (hNB : N + 1 < B) (hnsB : ns < B) (hNNB : N * N < B)
    (rows : Fin N → List (Fin N)) (off : ℕ → ℕ)
    (σ : Env) (hC : AgCsrRows o t ns rows off σ)
    (hix : N * N ≤ (σ.arrs ix).length) (hky : N * N ≤ (σ.arrs ky).length)
    (hwords : ∀ k < N * N, (σ.arrs ix).getD k 0 < B) (hn : σ.vars nN = N) :
    ∃ τ, Run B (agxExtract o t ix ky sz ov rv fv kv tv hv iv lm nN) σ τ
        (58 * ns + 26 * N + 8) ∧
      AgDictSt ix ky sz B (N * N) (agDictUnion [] ((agArcCandidates rows).map agArcKey)) τ ∧
      (∀ y, y ≠ ov → y ≠ rv → y ≠ fv → y ≠ sz → y ≠ kv → y ≠ tv → y ≠ hv →
        y ≠ iv → y ≠ lm → τ.vars y = σ.vars y) ∧
      (∀ a, a ≠ ix → a ≠ ky → τ.arrs a = σ.arrs a) ∧
      (∀ a, (τ.arrs a).length = (σ.arrs a).length) := by
  have n_o : nN ≠ ov := agxName_ne hvs 0 1 (by simp) (by simp) (by decide)
  have n_r : nN ≠ rv := agxName_ne hvs 0 2 (by simp) (by simp) (by decide)
  have n_f : nN ≠ fv := agxName_ne hvs 0 3 (by simp) (by simp) (by decide)
  have n_s : nN ≠ sz := agxName_ne hvs 0 4 (by simp) (by simp) (by decide)
  have n_k : nN ≠ kv := agxName_ne hvs 0 5 (by simp) (by simp) (by decide)
  have n_t : nN ≠ tv := agxName_ne hvs 0 6 (by simp) (by simp) (by decide)
  have n_h : nN ≠ hv := agxName_ne hvs 0 7 (by simp) (by simp) (by decide)
  have n_i : nN ≠ iv := agxName_ne hvs 0 8 (by simp) (by simp) (by decide)
  have n_l : nN ≠ lm := agxName_ne hvs 0 9 (by simp) (by simp) (by decide)
  have o_r : ov ≠ rv := agxName_ne hvs 1 2 (by simp) (by simp) (by decide)
  have o_f : ov ≠ fv := agxName_ne hvs 1 3 (by simp) (by simp) (by decide)
  have o_s : ov ≠ sz := agxName_ne hvs 1 4 (by simp) (by simp) (by decide)
  have o_k : ov ≠ kv := agxName_ne hvs 1 5 (by simp) (by simp) (by decide)
  have o_t : ov ≠ tv := agxName_ne hvs 1 6 (by simp) (by simp) (by decide)
  have o_h : ov ≠ hv := agxName_ne hvs 1 7 (by simp) (by simp) (by decide)
  have o_i : ov ≠ iv := agxName_ne hvs 1 8 (by simp) (by simp) (by decide)
  have o_l : ov ≠ lm := agxName_ne hvs 1 9 (by simp) (by simp) (by decide)
  have r_f : rv ≠ fv := agxName_ne hvs 2 3 (by simp) (by simp) (by decide)
  have r_s : rv ≠ sz := agxName_ne hvs 2 4 (by simp) (by simp) (by decide)
  have f_s : fv ≠ sz := agxName_ne hvs 3 4 (by simp) (by simp) (by decide)
  have hvs9 : ([nN, rv, fv, sz, kv, tv, hv, iv, lm] : List String).Nodup :=
    hvs.sublist (List.Sublist.cons_cons nN (List.Sublist.cons ov (List.Sublist.refl _)))
  let σa := σ.setVar sz 0
  obtain ⟨hreset, hD0⟩ := agDictInit_run ix ky sz σ (by omega) hix hky hwords
  let I : ℕ → Env → Prop := fun i ρ =>
    AgDictSt ix ky sz B (N * N) (agDictUnion [] (agxPart rows i)) ρ ∧
    (∀ y, y ≠ ov → y ≠ rv → y ≠ fv → y ≠ sz → y ≠ kv → y ≠ tv → y ≠ hv →
      y ≠ iv → y ≠ lm → ρ.vars y = σ.vars y) ∧
    (∀ a, a ≠ ix → a ≠ ky → ρ.arrs a = σ.arrs a) ∧
    (∀ a, (ρ.arrs a).length = (σ.arrs a).length)
  let K : ℕ → ℕ := fun i => if hi : i < N then 58 * (rows ⟨i, hi⟩).length + 22 else 0
  have hstep : ∀ i, i < N → ∀ ρ, I i ρ → ρ.vars ov = i →
      ∃ τ, Run B (agxBody o t ix ky sz ov rv fv kv tv hv iv lm nN) ρ τ (K i) ∧
        I (i + 1) τ ∧ τ.vars ov = i + 1 := by
    intro i hi ρ hI hov
    obtain ⟨hDr, hfr, har, hlr⟩ := hI
    have hCr := hC.of_eq (har o hread.1 hread.2.1) (har t hread.2.2.1 hread.2.2.2)
    have hnr : ρ.vars nN = N := (hfr nN n_o n_r n_f n_s n_k n_t n_h n_i n_l).trans hn
    let ρ₁ := ρ.setVar rv i
    have hr1 : Run B (.assign rv (.var ov)) ρ ρ₁ 2 := Run.assign (agxEvalVar hov (by omega))
    have hov1 : ρ₁.vars ov = i := by simp [ρ₁, o_r, hov]
    let ρ₂ := ρ₁.setVar fv i
    have hr2 : Run B (.assign fv (.var ov)) ρ₁ ρ₂ 2 := Run.assign (agxEvalVar hov1 (by omega))
    have hD2 : AgDictSt ix ky sz B (N * N) (agDictUnion [] (agxPart rows i)) ρ₂ :=
      hDr.of_eq rfl rfl (by simp [ρ₂, ρ₁, Ne.symm r_s, Ne.symm f_s])
    have hn2 : ρ₂.vars nN = N := by simp [ρ₂, ρ₁, n_r, n_f, hnr]
    obtain ⟨ρb, hrow, hDb, hfb, hab, hlb⟩ := agDictRow_run
      o t ix ky sz rv fv kv tv hv iv lm nN false harr hread hvs9
      hNB hnsB le_rfl hNNB rows off (agDictUnion [] (agxPart rows i)) ⟨i, hi⟩ ⟨i, hi⟩
      ρ₂ (hCr.of_eq rfl rfl) hD2 (by simp [ρ₂, ρ₁, r_f]) (by simp [ρ₂]) hn2
    have hob : ρb.vars ov = i := by
      rw [hfb ov o_s o_k o_t o_h o_i o_l]
      simp [ρ₂, ρ₁, o_r, o_f, hov]
    let τ := ρb.setVar ov (i + 1)
    have hinc : Run B (.assign ov (.add (.var ov) (.lit 1))) ρb τ 4 :=
      Run.assign (agEvalAdd (agxEvalVar hob (by omega)) (evalB_lit (by omega)) (by omega))
    have hnext : AgDictSt ix ky sz B (N * N) (agDictUnion [] (agxPart rows (i + 1))) τ := by
      rw [agxPart_succ rows hi, agDictUnion_append]
      exact hDb.of_eq rfl rfl (by simp [τ, Ne.symm o_s])
    refine ⟨τ, (hr1.seq (hr2.seq (hrow.seq hinc))).mono ?_, ⟨hnext, ?_, ?_, ?_⟩, by simp [τ]⟩
    · dsimp only [K]
      rw [dif_pos hi]
      omega
    · intro y hy1 hy2 hy3 hy4 hy5 hy6 hy7 hy8 hy9
      rw [show τ.vars y = ρb.vars y by simp [τ, hy1], hfb y hy4 hy5 hy6 hy7 hy8 hy9]
      rw [show ρ₂.vars y = ρ.vars y by simp [ρ₂, ρ₁, hy2, hy3]]
      exact hfr y hy1 hy2 hy3 hy4 hy5 hy6 hy7 hy8 hy9
    · intro a ha1 ha2
      rw [show τ.arrs a = ρb.arrs a from rfl, hab a ha1 ha2]
      exact har a ha1 ha2
    · intro a
      rw [show τ.arrs a = ρb.arrs a from rfl, hlb a]
      exact hlr a
  have hbound : ∀ i, i ≤ N → ∀ ρ, I i ρ → ρ.vars nN = N :=
    fun i _ ρ hI => (hI.2.1 nN n_o n_r n_f n_s n_k n_t n_h n_i n_l).trans hn
  have hstart : I 0 (σa.setVar ov 0) := by
    refine ⟨?_, ?_, fun _ _ _ => rfl, fun _ => rfl⟩
    · have hh := hD0.of_eq (τ := σa.setVar ov 0) rfl rfl (by simp [σa, Ne.symm o_s])
      simpa only [agxPart, List.take_zero, List.flatMap_nil, agDictUnion_nil] using hh
    · intro y hy1 _ _ hy4 _ _ _ _ _
      simp [σa, hy1, hy4]
  obtain ⟨τ, hrun, hI, _⟩ := agForSum_run ov nN (agxBody o t ix ky sz ov rv fv kv tv hv iv lm nN)
    I K (by omega) hbound hstep σa hstart
  have hsum : (∑ i ∈ Finset.range N, K i) = 58 * ns + 22 * N := by
    rw [Finset.sum_range K]
    have hK : (∑ v : Fin N, K v) = ∑ v : Fin N, (58 * (rows v).length + 22) :=
      Finset.sum_congr rfl fun v _ => by dsimp only [K]; rw [dif_pos v.isLt]
    rw [hK]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      smul_eq_mul, Finset.card_univ, Fintype.card_fin]
    rw [hC.sum_lengths]
    omega
  refine ⟨τ, (hreset.seq hrun).mono (by rw [hsum]; omega), ?_, hI.2.1, hI.2.2.1, hI.2.2.2⟩
  simpa only [agxPart_full] using hI.1

/-- Extracted keys have exactly the source-row membership. -/
theorem agxExtract_keys {N : ℕ} (rows : Fin N → List (Fin N)) (u v : Fin N) :
    agArcKey (u, v) ∈ agDictUnion [] ((agArcCandidates rows).map agArcKey) ↔ u ∈ rows v := by
  rw [agDictUnion_arcKey_mem]
  simp [agArcCandidates, List.mem_flatMap, List.mem_map]

end Lax3Proofs.Prog
