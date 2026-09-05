import Lax3Proofs.SolveSweepAugStep
import Lax3Proofs.SolveSweepAugFilter

/-! # Sparse scans implementing deterministic augmentation rounds -/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax3Proofs.Augmentation Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.CoverRoutine

private theorem agssName_ne {xs : List String} (h : xs.Nodup) (i j : ℕ)
    (hi : i < xs.length) (hj : j < xs.length) (hne : i ≠ j) :
    xs[i] ≠ xs[j] := fun he => hne (h.getElem_inj_iff.mp he)

private theorem agssEvalVar {B k : ℕ} {σ : Env} {x : String}
    (hx : σ.vars x = k) (hk : k < B) : (Expr.var x).evalB B σ = some k := by
  rw [← hx]
  exact evalB_var (by omega)

/-! ## Decoding only occupied keys -/

/-- Decode an occupied pair key and compute its reverse. -/
def agsDecode (nN kf kr uv vv : String) : Com :=
  .seq (.assign uv (.div (.var kf) (.var nN)))
    (.seq (.assign vv (.sub (.var kf) (.mul (.var uv) (.var nN))))
      (.assign kr (.add (.mul (.var vv) (.var nN)) (.var uv))))

theorem agsDecode_run {B N : ℕ} (nN kf kr uv vv : String)
    (hnames : ([nN, kf, kr, uv, vv] : List String).Nodup)
    (hNB : N < B) (hNNB : N * N < B) (σ : Env) (u v : Fin N)
    (hn : σ.vars nN = N) (hk : σ.vars kf = agArcKey (u, v)) :
    ∃ τ, Run B (agsDecode nN kf kr uv vv) σ τ 16 ∧
      τ.vars uv = u ∧ τ.vars vv = v ∧ τ.vars kr = agArcKey (v, u) ∧
      (∀ y, y ≠ kr → y ≠ uv → y ≠ vv → τ.vars y = σ.vars y) ∧
      (∀ a, τ.arrs a = σ.arrs a) := by
  have hne := hnames
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hne
  have hdiv : agArcKey (u, v) / N = u := by
    have hd := agDecode (agArcKey_lt (u, v))
    exact (agSplit hd.2.1 v.isLt hd.2.2).1
  have hmul : u.val * N < B := by
    have := agArcKey_lt (u, v)
    dsimp only [agArcKey] at this
    omega
  let σ₁ := σ.setVar uv u
  have h1 : Run B (.assign uv (.div (.var kf) (.var nN))) σ σ₁ 4 := by
    have he := agEvalDiv (agssEvalVar hk (lt_trans (agArcKey_lt _) hNNB))
      (agssEvalVar hn hNB) (by rw [hdiv]; exact lt_trans u.isLt hNB)
    rw [hdiv] at he
    exact Run.assign he
  have hn1 : σ₁.vars nN = N := by simp [σ₁, (show nN ≠ uv by tauto), hn]
  have hk1 : σ₁.vars kf = agArcKey (u, v) := by simp [σ₁, (show kf ≠ uv by tauto), hk]
  have hu1 : σ₁.vars uv = u := by simp [σ₁]
  have hsub : agArcKey (u, v) - u.val * N = v := by simp [agArcKey]
  let σ₂ := σ₁.setVar vv v
  have h2 : Run B (.assign vv (.sub (.var kf) (.mul (.var uv) (.var nN)))) σ₁ σ₂ 6 := by
    have he := agEvalSub (agssEvalVar hk1 (lt_trans (agArcKey_lt _) hNNB))
      (agEvalMul (agssEvalVar hu1 (lt_trans u.isLt hNB)) (agssEvalVar hn1 hNB) hmul)
      (by rw [hsub]; exact lt_trans v.isLt hNB)
    rw [hsub] at he
    exact Run.assign he
  have hn2 : σ₂.vars nN = N := by simp [σ₂, (show nN ≠ vv by tauto), hn1]
  have hu2 : σ₂.vars uv = u := by simp [σ₂, (show uv ≠ vv by tauto), hu1]
  have hv2 : σ₂.vars vv = v := by simp [σ₂]
  have hmul2 : v.val * N < B := by
    have := agArcKey_lt (v, u)
    dsimp only [agArcKey] at this
    omega
  let τ := σ₂.setVar kr (agArcKey (v, u))
  have h3 : Run B (.assign kr (.add (.mul (.var vv) (.var nN)) (.var uv))) σ₂ τ 6 :=
    Run.assign (agEvalAdd
      (agEvalMul (agssEvalVar hv2 (lt_trans v.isLt hNB)) (agssEvalVar hn2 hNB) hmul2)
      (agssEvalVar hu2 (lt_trans u.isLt hNB)) (lt_trans (agArcKey_lt _) hNNB))
  refine ⟨τ, h1.seq (h2.seq h3), ?_, ?_, by simp [τ], ?_, fun _ => rfl⟩
  · simp [τ, (show uv ≠ kr by tauto), hu2]
  · simp [τ, (show vv ≠ kr by tauto), hv2]
  · intro y hyr hyu hyv
    simp [τ, σ₂, σ₁, hyr, hyu, hyv]

/-- Decode an occupied key before performing the five membership tests. -/
def agsKeyTest (oi ok os ti tk ts fi fk fs nN kf kr tmp ofv orv tfv trv ffv ra uv vv ans : String) : Com :=
  .seq (agsDecode nN kf kr uv vv)
    (agsGreedyTest oi ok os ti tk ts fi fk fs kf kr tmp ofv orv tfv trv ffv ra uv vv ans)

set_option maxHeartbeats 600000 in
theorem agsKeyTest_run {B N : ℕ} (D : Orientation N) (rank : Fin N → ℕ)
    (oi ok os ti tk ts fi fk fs nN kf kr tmp ofv orv tfv trv ffv ra uv vv ans : String)
    (hnames : ([os, ts, fs, kf, kr, tmp, ofv, orv, tfv, trv, ffv, uv, vv, ans, nN] : List String).Nodup)
    (hNB : N + 1 < B) (hNNB : N * N < B) (hRank : ∀ w, rank w < N)
    (oks tks fks : List ℕ)
    (hOld : ∀ a b : Fin N, agArcKey (a, b) ∈ oks ↔ a ∈ D.inN b)
    (hTrans : ∀ a b : Fin N, agArcKey (a, b) ∈ tks ↔ TransLink D a b)
    (hFrat : ∀ a b : Fin N, agArcKey (a, b) ∈ fks ↔ FratLink D a b)
    (σ : Env) (u v : Fin N)
    (hO : AgDictSt oi ok os B (N * N) oks σ) (hT : AgDictSt ti tk ts B (N * N) tks σ)
    (hF : AgDictSt fi fk fs B (N * N) fks σ)
    (hkf : σ.vars kf = agArcKey (u, v)) (hn : σ.vars nN = N)
    (hraL : N ≤ (σ.arrs ra).length)
    (hra : ∀ w : Fin N, (σ.arrs ra).getD w 0 = rank w) :
    ∃ τ, Run B (agsKeyTest oi ok os ti tk ts fi fk fs nN kf kr tmp ofv orv tfv trv ffv ra uv vv ans)
        σ τ 163 ∧
      τ.vars ans = agBit (u ∈ (greedyStep rank D).inN v) ∧
      AgFilterVars [kr, tmp, ofv, orv, tfv, trv, ffv, uv, vv, ans] σ τ ∧
      (∀ a, τ.arrs a = σ.arrs a) := by
  have hne := hnames
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hne
  have hdvs : ([nN, kf, kr, uv, vv] : List String).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true, not_false_eq_true]
    tauto
  obtain ⟨ρ, hdecode, hu, hv, hkr, hdfv, hdfa⟩ :=
    agsDecode_run nN kf kr uv vv hdvs (by omega) hNNB σ u v hn hkf
  have htestvs : ([os, ts, fs, kf, kr, tmp, ofv, orv, tfv, trv, ffv, uv, vv, ans] : List String).Nodup :=
    hnames.sublist (List.take_sublist 14 [os, ts, fs, kf, kr, tmp, ofv, orv, tfv, trv, ffv, uv, vv, ans, nN])
  have hOr : AgDictSt oi ok os B (N * N) oks ρ :=
    hO.of_eq (hdfa _) (hdfa _) (hdfv os (by tauto) (by tauto) (by tauto))
  have hTr : AgDictSt ti tk ts B (N * N) tks ρ :=
    hT.of_eq (hdfa _) (hdfa _) (hdfv ts (by tauto) (by tauto) (by tauto))
  have hFr : AgDictSt fi fk fs B (N * N) fks ρ :=
    hF.of_eq (hdfa _) (hdfa _) (hdfv fs (by tauto) (by tauto) (by tauto))
  obtain ⟨τ, htest, hans, htfv, htfa⟩ :=
    agsGreedyTest_run D rank oi ok os ti tk ts fi fk fs kf kr tmp ofv orv tfv trv ffv ra uv vv ans
      htestvs hNB le_rfl hNNB hRank oks tks fks hOld hTrans hFrat ρ u v hOr hTr hFr
      ((hdfv kf (by tauto) (by tauto) (by tauto)).trans hkf) hkr hu hv
      (by rw [hdfa]; exact hraL) (fun w => by rw [hdfa]; exact hra w)
  refine ⟨τ, hdecode.seq htest, hans, ?_, fun a => (htfa a).trans (hdfa a)⟩
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨hkr, htmp, hof, hor, htf, htr, hff, hu, hv, ha⟩ := hy
  rw [htfv y htmp hof hor htf htr hff ha]
  exact hdfv y hkr hu hv

/-- Membership of a raw pair key in an orientation. -/
def AgArcPred {N : ℕ} (D : Orientation N) (k : ℕ) : Prop :=
  ∃ u v : Fin N, agArcKey (u, v) = k ∧ u ∈ D.inN v

@[simp] theorem agArcPred_key {N : ℕ} (D : Orientation N) (u v : Fin N) :
    AgArcPred D (agArcKey (u, v)) ↔ u ∈ D.inN v := by
  constructor
  · rintro ⟨a, b, hk, ha⟩
    have he : (a, b) = (u, v) := agArcKey_injective hk
    cases he
    exact ha
  · intro h
    exact ⟨u, v, rfl, h⟩

/-- Filter one occupied key prefix using the exact augmentation test. -/
def agsGreedyScan (oi ok os ti tk ts fi fk fs nN kf kr tmp ofv orv tfv trv ffv ra uv vv ans
    ix ky sz tv hv iv lm src : String) : Com :=
  agFilterCom ix ky sz kf tv hv iv lm ans (.get src (.var iv))
    (agsKeyTest oi ok os ti tk ts fi fk fs nN kf kr tmp ofv orv tfv trv ffv ra uv vv ans)

set_option maxHeartbeats 1000000 in
/-- One sparse prefix costs at most `229` per candidate. Every decision flag
is computed from the three input dictionaries and the rank array. -/
theorem agsGreedyScan_run {B N : ℕ} (D : Orientation N) (rank : Fin N → ℕ)
    (oi ok os ti tk ts fi fk fs nN kf kr tmp ofv orv tfv trv ffv ra uv vv ans
      ix ky sz tv hv iv lm src : String)
    (hnames : ([os, ts, fs, kf, kr, tmp, ofv, orv, tfv, trv, ffv, uv, vv, ans, nN,
      sz, tv, hv, iv, lm] : List String).Nodup)
    (harr : ix ≠ ky)
    (hread : ∀ a ∈ [oi, ok, ti, tk, fi, fk, ra, src], a ≠ ix ∧ a ≠ ky)
    (hNB : N + 1 < B) (hNNB : N * N < B) (hRank : ∀ w, rank w < N)
    (oks tks fks ks xs : List ℕ)
    (hOld : ∀ a b : Fin N, agArcKey (a, b) ∈ oks ↔ a ∈ D.inN b)
    (hTrans : ∀ a b : Fin N, agArcKey (a, b) ∈ tks ↔ TransLink D a b)
    (hFrat : ∀ a b : Fin N, agArcKey (a, b) ∈ fks ↔ FratLink D a b)
    (σ : Env)
    (hO : AgDictSt oi ok os B (N * N) oks σ) (hT : AgDictSt ti tk ts B (N * N) tks σ)
    (hF : AgDictSt fi fk fs B (N * N) fks σ) (hD : AgDictSt ix ky sz B (N * N) ks σ)
    (hn : σ.vars nN = N) (hraL : N ≤ (σ.arrs ra).length)
    (hra : ∀ w : Fin N, (σ.arrs ra).getD w 0 = rank w)
    (hL : xs.length < B) (hlm : σ.vars lm = xs.length)
    (hxL : xs.length ≤ (σ.arrs src).length)
    (hx : ∀ i, i < xs.length → (σ.arrs src).getD i 0 = xs.getD i 0)
    (hxNN : ∀ k ∈ xs, k < N * N) :
    ∃ τ, Run B (agsGreedyScan oi ok os ti tk ts fi fk fs nN kf kr tmp ofv orv tfv trv ffv ra uv vv ans
        ix ky sz tv hv iv lm src) σ τ (229 * xs.length + 6) ∧
      AgDictSt ix ky sz B (N * N)
        (agFilterPart ks xs (AgArcPred (greedyStep rank D)) xs.length) τ ∧
      AgFilterVars ([sz, kf, tv, hv, iv] ++ [kr, tmp, ofv, orv, tfv, trv, ffv, uv, vv, ans]) σ τ ∧
      (∀ a, a ≠ ix → a ≠ ky → τ.arrs a = σ.arrs a) ∧
      (∀ a, (τ.arrs a).length = (σ.arrs a).length) := by
  let ws := [kr, tmp, ofv, orv, tfv, trv, ffv, uv, vv, ans]
  let W := [sz, kf, tv, hv, iv] ++ ws
  have hvs : ([sz, kf, tv, hv, iv, lm] : List String).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨agssName_ne hnames 15 3 (by simp) (by simp) (by decide), agssName_ne hnames 15 16 (by simp) (by simp) (by decide), agssName_ne hnames 15 17 (by simp) (by simp) (by decide), agssName_ne hnames 15 18 (by simp) (by simp) (by decide), agssName_ne hnames 15 19 (by simp) (by simp) (by decide)⟩, ⟨agssName_ne hnames 3 16 (by simp) (by simp) (by decide), agssName_ne hnames 3 17 (by simp) (by simp) (by decide), agssName_ne hnames 3 18 (by simp) (by simp) (by decide), agssName_ne hnames 3 19 (by simp) (by simp) (by decide)⟩, ⟨agssName_ne hnames 16 17 (by simp) (by simp) (by decide), agssName_ne hnames 16 18 (by simp) (by simp) (by decide), agssName_ne hnames 16 19 (by simp) (by simp) (by decide)⟩, ⟨agssName_ne hnames 17 18 (by simp) (by simp) (by decide), agssName_ne hnames 17 19 (by simp) (by simp) (by decide)⟩, agssName_ne hnames 18 19 (by simp) (by simp) (by decide)⟩
  have hsw : sz ∉ ws := by
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨agssName_ne hnames 15 4 (by simp) (by simp) (by decide), agssName_ne hnames 15 5 (by simp) (by simp) (by decide), agssName_ne hnames 15 6 (by simp) (by simp) (by decide), agssName_ne hnames 15 7 (by simp) (by simp) (by decide), agssName_ne hnames 15 8 (by simp) (by simp) (by decide), agssName_ne hnames 15 9 (by simp) (by simp) (by decide), agssName_ne hnames 15 10 (by simp) (by simp) (by decide), agssName_ne hnames 15 11 (by simp) (by simp) (by decide), agssName_ne hnames 15 12 (by simp) (by simp) (by decide), agssName_ne hnames 15 13 (by simp) (by simp) (by decide)⟩
  have hkw : kf ∉ ws := by
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨agssName_ne hnames 3 4 (by simp) (by simp) (by decide), agssName_ne hnames 3 5 (by simp) (by simp) (by decide), agssName_ne hnames 3 6 (by simp) (by simp) (by decide), agssName_ne hnames 3 7 (by simp) (by simp) (by decide), agssName_ne hnames 3 8 (by simp) (by simp) (by decide), agssName_ne hnames 3 9 (by simp) (by simp) (by decide), agssName_ne hnames 3 10 (by simp) (by simp) (by decide), agssName_ne hnames 3 11 (by simp) (by simp) (by decide), agssName_ne hnames 3 12 (by simp) (by simp) (by decide), agssName_ne hnames 3 13 (by simp) (by simp) (by decide)⟩
  have hiw : iv ∉ ws := by
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨agssName_ne hnames 18 4 (by simp) (by simp) (by decide), agssName_ne hnames 18 5 (by simp) (by simp) (by decide), agssName_ne hnames 18 6 (by simp) (by simp) (by decide), agssName_ne hnames 18 7 (by simp) (by simp) (by decide), agssName_ne hnames 18 8 (by simp) (by simp) (by decide), agssName_ne hnames 18 9 (by simp) (by simp) (by decide), agssName_ne hnames 18 10 (by simp) (by simp) (by decide), agssName_ne hnames 18 11 (by simp) (by simp) (by decide), agssName_ne hnames 18 12 (by simp) (by simp) (by decide), agssName_ne hnames 18 13 (by simp) (by simp) (by decide)⟩
  have hlw : lm ∉ ws := by
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨agssName_ne hnames 19 4 (by simp) (by simp) (by decide), agssName_ne hnames 19 5 (by simp) (by simp) (by decide), agssName_ne hnames 19 6 (by simp) (by simp) (by decide), agssName_ne hnames 19 7 (by simp) (by simp) (by decide), agssName_ne hnames 19 8 (by simp) (by simp) (by decide), agssName_ne hnames 19 9 (by simp) (by simp) (by decide), agssName_ne hnames 19 10 (by simp) (by simp) (by decide), agssName_ne hnames 19 11 (by simp) (by simp) (by decide), agssName_ne hnames 19 12 (by simp) (by simp) (by decide), agssName_ne hnames 19 13 (by simp) (by simp) (by decide)⟩
  have hoW : os ∉ W := by
    simp only [W, ws, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨agssName_ne hnames 0 15 (by simp) (by simp) (by decide), agssName_ne hnames 0 3 (by simp) (by simp) (by decide), agssName_ne hnames 0 16 (by simp) (by simp) (by decide), agssName_ne hnames 0 17 (by simp) (by simp) (by decide), agssName_ne hnames 0 18 (by simp) (by simp) (by decide)⟩, ⟨agssName_ne hnames 0 4 (by simp) (by simp) (by decide), agssName_ne hnames 0 5 (by simp) (by simp) (by decide), agssName_ne hnames 0 6 (by simp) (by simp) (by decide), agssName_ne hnames 0 7 (by simp) (by simp) (by decide), agssName_ne hnames 0 8 (by simp) (by simp) (by decide), agssName_ne hnames 0 9 (by simp) (by simp) (by decide), agssName_ne hnames 0 10 (by simp) (by simp) (by decide), agssName_ne hnames 0 11 (by simp) (by simp) (by decide), agssName_ne hnames 0 12 (by simp) (by simp) (by decide), agssName_ne hnames 0 13 (by simp) (by simp) (by decide)⟩⟩
  have htW : ts ∉ W := by
    simp only [W, ws, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨agssName_ne hnames 1 15 (by simp) (by simp) (by decide), agssName_ne hnames 1 3 (by simp) (by simp) (by decide), agssName_ne hnames 1 16 (by simp) (by simp) (by decide), agssName_ne hnames 1 17 (by simp) (by simp) (by decide), agssName_ne hnames 1 18 (by simp) (by simp) (by decide)⟩, ⟨agssName_ne hnames 1 4 (by simp) (by simp) (by decide), agssName_ne hnames 1 5 (by simp) (by simp) (by decide), agssName_ne hnames 1 6 (by simp) (by simp) (by decide), agssName_ne hnames 1 7 (by simp) (by simp) (by decide), agssName_ne hnames 1 8 (by simp) (by simp) (by decide), agssName_ne hnames 1 9 (by simp) (by simp) (by decide), agssName_ne hnames 1 10 (by simp) (by simp) (by decide), agssName_ne hnames 1 11 (by simp) (by simp) (by decide), agssName_ne hnames 1 12 (by simp) (by simp) (by decide), agssName_ne hnames 1 13 (by simp) (by simp) (by decide)⟩⟩
  have hfW : fs ∉ W := by
    simp only [W, ws, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨agssName_ne hnames 2 15 (by simp) (by simp) (by decide), agssName_ne hnames 2 3 (by simp) (by simp) (by decide), agssName_ne hnames 2 16 (by simp) (by simp) (by decide), agssName_ne hnames 2 17 (by simp) (by simp) (by decide), agssName_ne hnames 2 18 (by simp) (by simp) (by decide)⟩, ⟨agssName_ne hnames 2 4 (by simp) (by simp) (by decide), agssName_ne hnames 2 5 (by simp) (by simp) (by decide), agssName_ne hnames 2 6 (by simp) (by simp) (by decide), agssName_ne hnames 2 7 (by simp) (by simp) (by decide), agssName_ne hnames 2 8 (by simp) (by simp) (by decide), agssName_ne hnames 2 9 (by simp) (by simp) (by decide), agssName_ne hnames 2 10 (by simp) (by simp) (by decide), agssName_ne hnames 2 11 (by simp) (by simp) (by decide), agssName_ne hnames 2 12 (by simp) (by simp) (by decide), agssName_ne hnames 2 13 (by simp) (by simp) (by decide)⟩⟩
  have hnW : nN ∉ W := by
    simp only [W, ws, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨agssName_ne hnames 14 15 (by simp) (by simp) (by decide), agssName_ne hnames 14 3 (by simp) (by simp) (by decide), agssName_ne hnames 14 16 (by simp) (by simp) (by decide), agssName_ne hnames 14 17 (by simp) (by simp) (by decide), agssName_ne hnames 14 18 (by simp) (by simp) (by decide)⟩, ⟨agssName_ne hnames 14 4 (by simp) (by simp) (by decide), agssName_ne hnames 14 5 (by simp) (by simp) (by decide), agssName_ne hnames 14 6 (by simp) (by simp) (by decide), agssName_ne hnames 14 7 (by simp) (by simp) (by decide), agssName_ne hnames 14 8 (by simp) (by simp) (by decide), agssName_ne hnames 14 9 (by simp) (by simp) (by decide), agssName_ne hnames 14 10 (by simp) (by simp) (by decide), agssName_ne hnames 14 11 (by simp) (by simp) (by decide), agssName_ne hnames 14 12 (by simp) (by simp) (by decide), agssName_ne hnames 14 13 (by simp) (by simp) (by decide)⟩⟩
  have htestvs : ([os, ts, fs, kf, kr, tmp, ofv, orv, tfv, trv, ffv, uv, vv, ans, nN] : List String).Nodup :=
    hnames.sublist (List.take_sublist 15 [os, ts, fs, kf, kr, tmp, ofv, orv, tfv, trv, ffv, uv, vv, ans, nN,
      sz, tv, hv, iv, lm])
  have he : ∀ ρ : Env,
      (∀ a, a ≠ ix → a ≠ ky → ρ.arrs a = σ.arrs a) → AgFilterVars W σ ρ →
      ρ.vars iv < xs.length →
      (Expr.get src (.var iv)).evalB B ρ = some (xs.getD (ρ.vars iv) 0) := by
    intro ρ hfa _ hi
    have hsrc := hread src (by simp)
    have hm : xs.getD (ρ.vars iv) 0 ∈ xs := by
      rw [Lax62Proofs.Codegen.getD_eq_getElem hi]
      exact List.getElem_mem hi
    have hreadval : (ρ.arrs src).getD (ρ.vars iv) 0 = xs.getD (ρ.vars iv) 0 := by
      rw [hfa src hsrc.1 hsrc.2, hx _ hi]
    apply evalB_get (evalB_var (lt_trans hi hL))
    · rw [getElem?_of_lt (show ρ.vars iv < (ρ.arrs src).length by
        rw [hfa src hsrc.1 hsrc.2]; exact lt_of_lt_of_le hi hxL), hreadval]
    · exact lt_trans (hxNN _ hm) hNNB
  have htest : ∀ (k : ℕ), k ∈ xs → ∀ ρ : Env,
      (∀ a, a ≠ ix → a ≠ ky → ρ.arrs a = σ.arrs a) → AgFilterVars W σ ρ → ρ.vars kf = k →
      ∃ τ, Run B (agsKeyTest oi ok os ti tk ts fi fk fs nN kf kr tmp ofv orv tfv trv ffv ra uv vv ans)
          ρ τ 163 ∧ τ.vars ans = agBit (AgArcPred (greedyStep rank D) k) ∧
        AgFilterVars ws ρ τ ∧ (∀ a, τ.arrs a = ρ.arrs a) := by
    intro k hkm ρ hfa hfv hk
    have hd := agDecode (hxNN k hkm)
    let u : Fin N := ⟨k / N, hd.1⟩
    let v : Fin N := ⟨k % N, hd.2.1⟩
    have hkey : agArcKey (u, v) = k := hd.2.2
    have ha : ∀ a ∈ [oi, ok, ti, tk, fi, fk, ra, src], ρ.arrs a = σ.arrs a := by
      intro a ham
      exact hfa a (hread a ham).1 (hread a ham).2
    have hOr : AgDictSt oi ok os B (N * N) oks ρ :=
      hO.of_eq (ha oi (by simp)) (ha ok (by simp)) (hfv os hoW)
    have hTr : AgDictSt ti tk ts B (N * N) tks ρ :=
      hT.of_eq (ha ti (by simp)) (ha tk (by simp)) (hfv ts htW)
    have hFr : AgDictSt fi fk fs B (N * N) fks ρ :=
      hF.of_eq (ha fi (by simp)) (ha fk (by simp)) (hfv fs hfW)
    obtain ⟨τ, hr, hans, hv, haa⟩ :=
      agsKeyTest_run D rank oi ok os ti tk ts fi fk fs nN kf kr tmp ofv orv tfv trv ffv ra uv vv ans
        htestvs hNB hNNB hRank oks tks fks hOld hTrans hFrat ρ u v hOr hTr hFr
        (hk.trans hkey.symm) ((hfv nN hnW).trans hn)
        (by rw [ha ra (by simp)]; exact hraL) (by intro w; rw [ha ra (by simp)]; exact hra w)
    refine ⟨τ, hr, ?_, hv, haa⟩
    rw [← hkey, agArcPred_key]
    exact hans
  obtain ⟨τ, hr, hd, hv, ha, hl⟩ := agFilterCom_run ix ky sz kf tv hv iv lm ans
    (.get src (.var iv))
    (agsKeyTest oi ok os ti tk ts fi fk fs nN kf kr tmp ofv orv tfv trv ffv ra uv vv ans)
    ws harr hvs hsw hkw hiw hlw hNNB (by omega) ks xs (AgArcPred (greedyStep rank D)) σ
    hD hL hlm hxNN he htest
  exact ⟨τ, hr, hd, hv, ha, hl⟩

end Lax3Proofs.Prog
