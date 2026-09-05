import Lax3Proofs.SolveSweepAugStepScan

/-!
# Sparse pair filters for the base orientation and fraternity graph

The same occupied-key filter either retains increasing-rank pairs or discards
diagonal pairs. Both tests decode only the current key and take constant time.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax3Proofs.Augmentation Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.CoverRoutine

private theorem agpName_ne {xs : List String} (h : xs.Nodup) (i j : ℕ)
    (hi : i < xs.length) (hj : j < xs.length) (hne : i ≠ j) :
    xs[i] ≠ xs[j] := fun he => hne (h.getElem_inj_iff.mp he)

private theorem agpEvalVar {B k : ℕ} {σ : Env} {x : String}
    (hx : σ.vars x = k) (hk : k < B) : (Expr.var x).evalB B σ = some k := by
  rw [← hx]
  exact evalB_var (by omega)

/-- An increasing-rank test, or the loop-removal test. -/
def agpPairExpr (up : Bool) (ra uv vv : String) : Expr :=
  if up then agLtE (.get ra (.var uv)) (.get ra (.var vv))
  else .sub (.lit 1) (agEqE (.var uv) (.var vv))

theorem agpPairExpr_eval {B N : ℕ} (up : Bool) (ra uv vv : String)
    (rank : Fin N → ℕ) (hRank : ∀ w, rank w < N) (hNB : N + 1 < B)
    (σ : Env) (u v : Fin N) (hu : σ.vars uv = u) (hv : σ.vars vv = v)
    (hra : up = true → N ≤ (σ.arrs ra).length ∧
      ∀ w : Fin N, (σ.arrs ra).getD w 0 = rank w) :
    (agpPairExpr up ra uv vv).evalB B σ =
      some (agBit (if up then rank u < rank v else u ≠ v)) := by
  cases up
  · have he := agEval_eqE (B := B) (agpEvalVar hu (lt_trans u.isLt (by omega)))
      (agpEvalVar hv (lt_trans v.isLt (by omega)))
      (lt_trans u.isLt (by omega)) (lt_trans v.isLt (by omega)) (by omega)
    have hs := agEvalSub (evalB_lit (show 1 < B by omega)) he (by have := agBit_le_one (u.val = v.val); omega)
    rw [agNum_not rfl] at hs
    simpa only [Fin.val_inj] using hs
  · obtain ⟨hl, hr⟩ := hra rfl
    have hget (x : String) (w : Fin N) (hx : σ.vars x = w) :
        (Expr.get ra (.var x)).evalB B σ = some (rank w) :=
      evalB_get (agpEvalVar hx (lt_trans w.isLt (by omega)))
        (by rw [getElem?_of_lt (lt_of_lt_of_le w.isLt hl), hr w]) (lt_trans (hRank w) (by omega))
    exact agEval_ltE (hget uv u hu) (hget vv v hv) (by have := hRank u; omega) (by omega)

/-- Decode one pair and compute the chosen concrete predicate. -/
def agpPairTest (up : Bool) (nN kf kr uv vv ans ra : String) : Com :=
  .seq (agsDecode nN kf kr uv vv) (.assign ans (agpPairExpr up ra uv vv))

theorem agpPairTest_run {B N : ℕ} (up : Bool) (nN kf kr uv vv ans ra : String)
    (hnames : ([nN, kf, kr, uv, vv, ans] : List String).Nodup)
    (rank : Fin N → ℕ) (hRank : ∀ w, rank w < N) (hNB : N + 1 < B) (hNNB : N * N < B)
    (σ : Env) (u v : Fin N) (hn : σ.vars nN = N) (hk : σ.vars kf = agArcKey (u, v))
    (hra : up = true → N ≤ (σ.arrs ra).length ∧
      ∀ w : Fin N, (σ.arrs ra).getD w 0 = rank w) :
    ∃ τ, Run B (agpPairTest up nN kf kr uv vv ans ra) σ τ 30 ∧
      τ.vars ans = agBit (if up then rank u < rank v else u ≠ v) ∧
      AgFilterVars [kr, uv, vv, ans] σ τ ∧ (∀ s, τ.arrs s = σ.arrs s) := by
  obtain ⟨ρ, hd, hu, hv, _, hfv, hfa⟩ := agsDecode_run nN kf kr uv vv
    (hnames.sublist (List.take_sublist 5 [nN, kf, kr, uv, vv, ans])) (by omega) hNNB σ u v hn hk
  have he := agpPairExpr_eval up ra uv vv rank hRank hNB ρ u v hu hv (by
    intro hup
    rw [hfa]
    exact hra hup)
  let τ := ρ.setVar ans (agBit (if up then rank u < rank v else u ≠ v))
  have ht : Run B (.assign ans (agpPairExpr up ra uv vv)) ρ τ 14 :=
    (Run.assign he).mono (by cases up <;> simp [agpPairExpr, agLtE, agEqE, Expr.size])
  refine ⟨τ, hd.seq ht, by simp [τ], ?_, hfa⟩
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
  rw [show τ.vars s = ρ.vars s by simp [τ, hs.2.2.2]]
  exact hfv s hs.1 hs.2.1 hs.2.2.1

/-- The accepted raw-key relation. -/
def AgPairPred {N : ℕ} (up : Bool) (rank : Fin N → ℕ) (k : ℕ) : Prop :=
  ∃ u v : Fin N, agArcKey (u, v) = k ∧ (if up then rank u < rank v else u ≠ v)

@[simp] theorem agPairPred_key {N : ℕ} (up : Bool) (rank : Fin N → ℕ) (u v : Fin N) :
    AgPairPred up rank (agArcKey (u, v)) ↔ (if up then rank u < rank v else u ≠ v) := by
  constructor
  · rintro ⟨a, b, hk, hp⟩
    have he : (a, b) = (u, v) := agArcKey_injective hk
    cases he
    exact hp
  · exact fun hp => ⟨u, v, rfl, hp⟩

/-- A concrete pair filter, including output initialization and reading the
occupied source length. -/
def agpPairFilter (up : Bool) (nN kf kr uv vv ans ra ix ky sz tv hv iv lm src srcsz : String) : Com :=
  .seq (.assign sz (.lit 0))
    (.seq (.assign lm (.var srcsz))
      (agFilterCom ix ky sz kf tv hv iv lm ans (.get src (.var iv))
        (agpPairTest up nN kf kr uv vv ans ra)))

set_option maxHeartbeats 800000 in
/-- Filter a genuine occupied prefix into a sparse dictionary. Rank mode is
the base-orientation test; loop-removal mode reads no rank-array contents. -/
theorem agpPairFilter_run {B N : ℕ} (up : Bool)
    (nN kf kr uv vv ans ra ix ky sz tv hv iv lm src srcsz : String)
    (hnames : ([nN, kf, kr, uv, vv, ans, sz, tv, hv, iv, lm, srcsz] : List String).Nodup)
    (hixky : ix ≠ ky) (hsrc : src ≠ ix ∧ src ≠ ky)
    (hrane : up = true → ra ≠ ix ∧ ra ≠ ky)
    (rank : Fin N → ℕ) (hRank : ∀ w, rank w < N) (hNB : N + 1 < B) (hNNB : N * N < B)
    (xs : List ℕ) (σ : Env) (hn : σ.vars nN = N)
    (hM : xs.length < B) (hsrcsz : σ.vars srcsz = xs.length)
    (hsrcL : xs.length ≤ (σ.arrs src).length)
    (hsrcV : ∀ i, i < xs.length → (σ.arrs src).getD i 0 = xs.getD i 0)
    (hxNN : ∀ k ∈ xs, k < N * N)
    (hra : up = true → N ≤ (σ.arrs ra).length ∧
      ∀ w : Fin N, (σ.arrs ra).getD w 0 = rank w)
    (hix : N * N ≤ (σ.arrs ix).length) (hky : N * N ≤ (σ.arrs ky).length)
    (hwords : ∀ k < N * N, (σ.arrs ix).getD k 0 < B) :
    ∃ τ, Run B (agpPairFilter up nN kf kr uv vv ans ra ix ky sz tv hv iv lm src srcsz) σ τ
        (96 * xs.length + 10) ∧
      AgDictSt ix ky sz B (N * N) (agFilterPart [] xs (AgPairPred up rank) xs.length) τ ∧
      AgFilterVars [sz, kf, tv, hv, iv, lm, kr, uv, vv, ans] σ τ ∧
      (∀ s, s ≠ ix → s ≠ ky → τ.arrs s = σ.arrs s) ∧
      (∀ s, (τ.arrs s).length = (σ.arrs s).length) := by
  obtain ⟨hinit, hD0⟩ := agDictInit_run ix ky sz σ (by omega) hix hky hwords
  let ρ₀ := σ.setVar sz 0
  have hl0 : ρ₀.vars srcsz = xs.length := by simp [ρ₀, show srcsz ≠ sz from agpName_ne hnames 11 6 (by simp) (by simp) (by decide), hsrcsz]
  let ρ := ρ₀.setVar lm xs.length
  have hload : Run B (.assign lm (.var srcsz)) ρ₀ ρ 2 := Run.assign (agpEvalVar hl0 hM)
  have hD : AgDictSt ix ky sz B (N * N) [] ρ :=
    hD0.of_eq rfl rfl (by simp [ρ, ρ₀, show sz ≠ lm from agpName_ne hnames 6 10 (by simp) (by simp) (by decide)])
  have hnρ : ρ.vars nN = N := by
    simp [ρ, ρ₀, show nN ≠ sz from agpName_ne hnames 0 6 (by simp) (by simp) (by decide), show nN ≠ lm from agpName_ne hnames 0 10 (by simp) (by simp) (by decide), hn]
  let ws := [kr, uv, vv, ans]
  let W := [sz, kf, tv, hv, iv] ++ ws
  have hvs : ([sz, kf, tv, hv, iv, lm] : List String).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨agpName_ne hnames 6 1 (by simp) (by simp) (by decide), agpName_ne hnames 6 7 (by simp) (by simp) (by decide), agpName_ne hnames 6 8 (by simp) (by simp) (by decide), agpName_ne hnames 6 9 (by simp) (by simp) (by decide), agpName_ne hnames 6 10 (by simp) (by simp) (by decide)⟩, ⟨agpName_ne hnames 1 7 (by simp) (by simp) (by decide), agpName_ne hnames 1 8 (by simp) (by simp) (by decide), agpName_ne hnames 1 9 (by simp) (by simp) (by decide), agpName_ne hnames 1 10 (by simp) (by simp) (by decide)⟩, ⟨agpName_ne hnames 7 8 (by simp) (by simp) (by decide), agpName_ne hnames 7 9 (by simp) (by simp) (by decide), agpName_ne hnames 7 10 (by simp) (by simp) (by decide)⟩, ⟨agpName_ne hnames 8 9 (by simp) (by simp) (by decide), agpName_ne hnames 8 10 (by simp) (by simp) (by decide)⟩, agpName_ne hnames 9 10 (by simp) (by simp) (by decide)⟩
  have hsw : sz ∉ ws := by
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨agpName_ne hnames 6 2 (by simp) (by simp) (by decide), agpName_ne hnames 6 3 (by simp) (by simp) (by decide), agpName_ne hnames 6 4 (by simp) (by simp) (by decide), agpName_ne hnames 6 5 (by simp) (by simp) (by decide)⟩
  have hkw : kf ∉ ws := by
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨agpName_ne hnames 1 2 (by simp) (by simp) (by decide), agpName_ne hnames 1 3 (by simp) (by simp) (by decide), agpName_ne hnames 1 4 (by simp) (by simp) (by decide), agpName_ne hnames 1 5 (by simp) (by simp) (by decide)⟩
  have hiw : iv ∉ ws := by
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨agpName_ne hnames 9 2 (by simp) (by simp) (by decide), agpName_ne hnames 9 3 (by simp) (by simp) (by decide), agpName_ne hnames 9 4 (by simp) (by simp) (by decide), agpName_ne hnames 9 5 (by simp) (by simp) (by decide)⟩
  have hlw : lm ∉ ws := by
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨agpName_ne hnames 10 2 (by simp) (by simp) (by decide), agpName_ne hnames 10 3 (by simp) (by simp) (by decide), agpName_ne hnames 10 4 (by simp) (by simp) (by decide), agpName_ne hnames 10 5 (by simp) (by simp) (by decide)⟩
  have hnW : nN ∉ W := by
    simp only [W, ws, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨agpName_ne hnames 0 6 (by simp) (by simp) (by decide), agpName_ne hnames 0 1 (by simp) (by simp) (by decide), agpName_ne hnames 0 7 (by simp) (by simp) (by decide), agpName_ne hnames 0 8 (by simp) (by simp) (by decide), agpName_ne hnames 0 9 (by simp) (by simp) (by decide)⟩, ⟨agpName_ne hnames 0 2 (by simp) (by simp) (by decide), agpName_ne hnames 0 3 (by simp) (by simp) (by decide), agpName_ne hnames 0 4 (by simp) (by simp) (by decide), agpName_ne hnames 0 5 (by simp) (by simp) (by decide)⟩⟩
  have he : ∀ η : Env,
      (∀ s, s ≠ ix → s ≠ ky → η.arrs s = ρ.arrs s) → AgFilterVars W ρ η →
      η.vars iv < xs.length →
      (Expr.get src (.var iv)).evalB B η = some (xs.getD (η.vars iv) 0) := by
    intro η ha _ hi
    have hm : xs.getD (η.vars iv) 0 ∈ xs := by
      rw [Lax62Proofs.Codegen.getD_eq_getElem hi]
      exact List.getElem_mem hi
    have hget : (η.arrs src).getD (η.vars iv) 0 = xs.getD (η.vars iv) 0 := by
      rw [ha src hsrc.1 hsrc.2]
      exact hsrcV _ hi
    apply evalB_get (evalB_var (lt_trans hi hM))
    · rw [getElem?_of_lt (show η.vars iv < (η.arrs src).length by
        rw [ha src hsrc.1 hsrc.2]; exact lt_of_lt_of_le hi hsrcL), hget]
    · exact lt_trans (hxNN _ hm) hNNB
  have htest : ∀ k, k ∈ xs → ∀ η : Env,
      (∀ s, s ≠ ix → s ≠ ky → η.arrs s = ρ.arrs s) → AgFilterVars W ρ η → η.vars kf = k →
      ∃ τ, Run B (agpPairTest up nN kf kr uv vv ans ra) η τ 30 ∧
        τ.vars ans = agBit (AgPairPred up rank k) ∧ AgFilterVars ws η τ ∧
        (∀ s, τ.arrs s = η.arrs s) := by
    intro k hkm η ha hframe hk
    have hd := agDecode (hxNN k hkm)
    let u : Fin N := ⟨k / N, hd.1⟩
    let v : Fin N := ⟨k % N, hd.2.1⟩
    have hkey : agArcKey (u, v) = k := hd.2.2
    obtain ⟨τ, hr, hans, hfv, hfa⟩ := agpPairTest_run up nN kf kr uv vv ans ra
      (hnames.sublist (List.take_sublist 6 [nN, kf, kr, uv, vv, ans, sz, tv, hv, iv, lm, srcsz]))
      rank hRank hNB hNNB η u v ((hframe nN hnW).trans hnρ) (hk.trans hkey.symm) (by
        intro hup
        rw [ha ra (hrane hup).1 (hrane hup).2]
        exact hra hup)
    refine ⟨τ, hr, ?_, hfv, hfa⟩
    rw [← hkey, agPairPred_key]
    exact hans
  obtain ⟨τ, hr, hd, hv, ha, hl⟩ := agFilterCom_run ix ky sz kf tv hv iv lm ans
    (.get src (.var iv)) (agpPairTest up nN kf kr uv vv ans ra) ws hixky hvs hsw hkw hiw hlw
    hNNB (by omega) [] xs (AgPairPred up rank) ρ hD hM (by simp [ρ]) hxNN he htest
  refine ⟨τ, (hinit.seq (hload.seq hr)).mono (by change 2 + (2 + ((30 + 2 + 64) * xs.length + 6)) ≤ _; omega),
    hd, ?_, ha, hl⟩
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨hys, hyk, hyt, hyh, hyi, hyl, hyr, hyu, hyv, hya⟩ := hy
  rw [hv y (by simp [ws, hys, hyk, hyt, hyh, hyi, hyr, hyu, hyv, hya])]
  simp [ρ, ρ₀, hys, hyl]

/-- Exact membership in the emitted accepted prefix. -/
theorem agpPairFilter_keys {N : ℕ} (up : Bool) (rank : Fin N → ℕ) (xs : List ℕ) (u v : Fin N) :
    agArcKey (u, v) ∈ agFilterPart [] xs (AgPairPred up rank) xs.length ↔
      agArcKey (u, v) ∈ xs ∧ (if up then rank u < rank v else u ≠ v) := by
  simp only [agFilterPart_mem, List.take_length, List.not_mem_nil, false_or, agPairPred_key]

/-- Loop removal yields the exact simple fraternity graph from the raw
`FratLink` dictionary, whose diagonal entries were honestly counted. -/
theorem agpFratFilter_keys {N : ℕ} (D : Orientation N) (xs : List ℕ)
    (hx : ∀ u v : Fin N, agArcKey (u, v) ∈ xs ↔ FratLink D u v) (u v : Fin N) :
    agArcKey (u, v) ∈ agFilterPart [] xs (AgPairPred false (fun w : Fin N => w.val)) xs.length ↔
      (fratGraph D).Adj u v := by
  rw [agpPairFilter_keys, hx]
  simp only [Bool.false_eq_true, ↓reduceIte, fratGraph_adj, and_comm]

/-- Increasing-rank filtering of the graph's actual arcs is its base orientation. -/
theorem agpBaseFilter_keys {N : ℕ} (G : SimpleGraph (Fin N)) (π : Equiv.Perm (Fin N))
    (xs : List ℕ) (hx : ∀ u v : Fin N, agArcKey (u, v) ∈ xs ↔ G.Adj u v) (u v : Fin N) :
    agArcKey (u, v) ∈ agFilterPart [] xs (AgPairPred true (fun w => (π w).val)) xs.length ↔
      u ∈ (baseOr G π).inN v := by
  rw [agpPairFilter_keys, hx, mem_baseOr]
  rfl

end Lax3Proofs.Prog
