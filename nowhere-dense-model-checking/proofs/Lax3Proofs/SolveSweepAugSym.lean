import Lax3Proofs.SolveSweepAugRound

/-!
# Sparse symmetrization of the final orientation

Two occupied-prefix scans insert each arc and its reversal. This is the exact
underlying graph required by the final adjacency build.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax62Proofs.Codegen (getD_eq_getElem)
open Lax3Proofs.Augmentation Lax3Proofs.Augmentation.Orientation

private theorem agyName_ne {xs : List String} (h : xs.Nodup) (i j : ℕ)
    (hi : i < xs.length) (hj : j < xs.length) (hne : i ≠ j) :
    xs[i] ≠ xs[j] := fun he => hne (h.getElem_inj_iff.mp he)

private theorem agyEvalVar {B k : ℕ} {σ : Env} {x : String}
    (hx : σ.vars x = k) (hk : k < B) : (Expr.var x).evalB B σ = some k := by
  rw [← hx]
  exact evalB_var (by omega)

/-- Reversal of an occupied pair key. -/
def agReverseKey (N k : ℕ) : ℕ := (k % N) * N + k / N

theorem agReverseKey_arc {N : ℕ} (u v : Fin N) :
    agReverseKey N (agArcKey (u, v)) = agArcKey (v, u) := by
  have hd := agDecode (agArcKey_lt (u, v))
  have hs := agSplit hd.2.1 v.isLt hd.2.2
  rw [agReverseKey, hs.1, hs.2]
  rfl

theorem agReverseKey_lt {N k : ℕ} (hk : k < N * N) : agReverseKey N k < N * N := by
  have hd := agDecode hk
  exact agArcKey_lt ((⟨k % N, hd.2.1⟩ : Fin N), (⟨k / N, hd.1⟩ : Fin N))

theorem agReverseKey_invol {N k : ℕ} (hk : k < N * N) :
    agReverseKey N (agReverseKey N k) = k := by
  have hd := agDecode hk
  let u : Fin N := ⟨k / N, hd.1⟩
  let v : Fin N := ⟨k % N, hd.2.1⟩
  have hkey : agArcKey (u, v) = k := hd.2.2
  rw [← hkey, agReverseKey_arc, agReverseKey_arc]

/-- Reversal uses bounded division, multiplication and subtraction on just
the current occupied key. -/
def agReverseExpr (e : Expr) (nN : String) : Expr :=
  .add (.mul (.sub e (.mul (.div e (.var nN)) (.var nN))) (.var nN))
    (.div e (.var nN))

theorem agReverseExpr_eval {B N k : ℕ} {σ : Env} {e : Expr} (nN : String)
    (hN : σ.vars nN = N) (hNB : N < B) (hNNB : N * N < B) (hk : k < N * N)
    (he : e.evalB B σ = some k) :
    (agReverseExpr e nN).evalB B σ = some (agReverseKey N k) := by
  have hd := agDecode hk
  have hvalN := agyEvalVar hN hNB
  have hdiv := agEvalDiv he hvalN (lt_trans hd.1 hNB)
  have hmul := agEvalMul hdiv hvalN (by omega)
  have hsubeq : k - k / N * N = k % N := by omega
  have hsub := agEvalSub he hmul (by rw [hsubeq]; exact lt_trans hd.2.1 hNB)
  rw [hsubeq] at hsub
  have hrB := lt_trans (agReverseKey_lt hk) hNNB
  have hm2B : k % N * N < B := lt_of_le_of_lt (Nat.le_add_right _ (k / N)) hrB
  have hmul2 := agEvalMul hsub hvalN hm2B
  exact agEvalAdd hmul2 hdiv hrB

def agSymKeys (N : ℕ) (xs : List ℕ) : List ℕ :=
  agDictUnion (agDictUnion [] xs) (xs.map (agReverseKey N))

theorem agSymKeys_mem {N : ℕ} (xs : List ℕ) (hx : ∀ k ∈ xs, k < N * N) (u v : Fin N) :
    agArcKey (u, v) ∈ agSymKeys N xs ↔ agArcKey (u, v) ∈ xs ∨ agArcKey (v, u) ∈ xs := by
  have hrev : agArcKey (u, v) ∈ xs.map (agReverseKey N) ↔ agArcKey (v, u) ∈ xs := by
    rw [List.mem_map]
    constructor
    · rintro ⟨k, hk, he⟩
      have hh := congrArg (agReverseKey N) he
      rw [agReverseKey_invol (hx k hk), agReverseKey_arc] at hh
      exact hh ▸ hk
    · exact fun h => ⟨agArcKey (v, u), h, agReverseKey_arc v u⟩
  simp only [agSymKeys, agDictUnion_mem, List.not_mem_nil, false_or, hrev]

theorem agSymKeys_toGraph {N : ℕ} (D : Orientation N) (xs : List ℕ)
    (hx : ∀ k ∈ xs, k < N * N)
    (harc : ∀ u v : Fin N, agArcKey (u, v) ∈ xs ↔ u ∈ D.inN v) (u v : Fin N) :
    agArcKey (u, v) ∈ agSymKeys N xs ↔ D.toGraph.Adj u v := by
  rw [agSymKeys_mem xs hx, harc, harc]
  rfl

def agSymCom (ix ky sz kv tv hv iv lm nN src srcsz : String) : Com :=
  .seq (.assign sz (.lit 0))
    (.seq (.assign lm (.var srcsz))
      (.seq (agDictEnumerate ix ky sz kv tv hv iv lm (.get src (.var iv)))
        (agDictEnumerate ix ky sz kv tv hv iv lm (agReverseExpr (.get src (.var iv)) nN))))

set_option maxHeartbeats 600000 in
/-- Symmetrize a genuine occupied arc-key prefix. The two scans cost at most
`116` per source entry; neither touches unused source capacity. -/
theorem agSymCom_run {B N : ℕ} (ix ky sz kv tv hv iv lm nN src srcsz : String)
    (hnames : ([sz, kv, tv, hv, iv, lm, nN, srcsz] : List String).Nodup)
    (hixky : ix ≠ ky) (hsrc : src ≠ ix ∧ src ≠ ky)
    (hNB : N + 1 < B) (hNNB : N * N < B)
    (xs : List ℕ) (σ : Env) (hn : σ.vars nN = N)
    (hM : xs.length < B) (hsrcsz : σ.vars srcsz = xs.length)
    (hsrcL : xs.length ≤ (σ.arrs src).length)
    (hsrcV : ∀ i, i < xs.length → (σ.arrs src).getD i 0 = xs.getD i 0)
    (hxNN : ∀ k ∈ xs, k < N * N)
    (hix : N * N ≤ (σ.arrs ix).length) (hky : N * N ≤ (σ.arrs ky).length)
    (hwords : ∀ k < N * N, (σ.arrs ix).getD k 0 < B) :
    ∃ τ, Run B (agSymCom ix ky sz kv tv hv iv lm nN src srcsz) σ τ (116 * xs.length + 16) ∧
      AgDictSt ix ky sz B (N * N) (agSymKeys N xs) τ ∧
      (∀ y, y ≠ sz → y ≠ kv → y ≠ tv → y ≠ hv → y ≠ iv → y ≠ lm → τ.vars y = σ.vars y) ∧
      (∀ s, s ≠ ix → s ≠ ky → τ.arrs s = σ.arrs s) ∧
      (∀ s, (τ.arrs s).length = (σ.arrs s).length) := by
  have s_l : sz ≠ lm := agyName_ne hnames 0 5 (by simp) (by simp) (by decide)
  have e_s : srcsz ≠ sz := agyName_ne hnames 7 0 (by simp) (by simp) (by decide)
  have n_s : nN ≠ sz := agyName_ne hnames 6 0 (by simp) (by simp) (by decide)
  have n_k : nN ≠ kv := agyName_ne hnames 6 1 (by simp) (by simp) (by decide)
  have n_t : nN ≠ tv := agyName_ne hnames 6 2 (by simp) (by simp) (by decide)
  have n_h : nN ≠ hv := agyName_ne hnames 6 3 (by simp) (by simp) (by decide)
  have n_i : nN ≠ iv := agyName_ne hnames 6 4 (by simp) (by simp) (by decide)
  have n_l : nN ≠ lm := agyName_ne hnames 6 5 (by simp) (by simp) (by decide)
  have l_s : lm ≠ sz := agyName_ne hnames 5 0 (by simp) (by simp) (by decide)
  have l_k : lm ≠ kv := agyName_ne hnames 5 1 (by simp) (by simp) (by decide)
  have l_t : lm ≠ tv := agyName_ne hnames 5 2 (by simp) (by simp) (by decide)
  have l_h : lm ≠ hv := agyName_ne hnames 5 3 (by simp) (by simp) (by decide)
  have l_i : lm ≠ iv := agyName_ne hnames 5 4 (by simp) (by simp) (by decide)
  have hvs6 : ([sz, kv, tv, hv, iv, lm] : List String).Nodup :=
    hnames.sublist (List.take_sublist 6 [sz, kv, tv, hv, iv, lm, nN, srcsz])
  obtain ⟨hinit, hD0⟩ := agDictInit_run ix ky sz σ (by omega) hix hky hwords
  let ρ₀ := σ.setVar sz 0
  let ρ := ρ₀.setVar lm xs.length
  have hload : Run B (.assign lm (.var srcsz)) ρ₀ ρ 2 :=
    Run.assign (agyEvalVar (by simp [ρ₀, e_s, hsrcsz]) hM)
  have hD : AgDictSt ix ky sz B (N * N) [] ρ :=
    hD0.of_eq rfl rfl (by simp [ρ, ρ₀, s_l])
  have hnρ : ρ.vars nN = N := by simp [ρ, ρ₀, n_s, n_l, hn]
  have hget : ∀ η : Env, η.arrs src = σ.arrs src → η.vars iv < xs.length →
      (Expr.get src (.var iv)).evalB B η = some (xs.getD (η.vars iv) 0) := by
    intro η ha hi
    have hm : xs.getD (η.vars iv) 0 ∈ xs := by
      rw [getD_eq_getElem hi]
      exact List.getElem_mem hi
    apply evalB_get (evalB_var (lt_trans hi hM))
    · rw [getElem?_of_lt (show η.vars iv < (η.arrs src).length by rw [ha]; exact lt_of_lt_of_le hi hsrcL)]
      rw [ha, hsrcV _ hi]
    · exact lt_trans (hxNN _ hm) hNNB
  have he1 : ∀ η : Env,
      (∀ s, s ≠ ix → s ≠ ky → η.arrs s = ρ.arrs s) →
      (∀ y, y ≠ sz → y ≠ kv → y ≠ tv → y ≠ hv → y ≠ iv → η.vars y = ρ.vars y) →
      η.vars iv < xs.length →
      (Expr.get src (.var iv)).evalB B η = some (xs.getD (η.vars iv) 0) :=
    fun η ha _ hi => hget η (ha src hsrc.1 hsrc.2) hi
  obtain ⟨ρ₁, h1, hD1, hv1, ha1, hl1⟩ := agDictEnumerate_run ix ky sz kv tv hv iv lm
    (.get src (.var iv)) hixky hvs6 hNNB (by omega) [] xs ρ hD hM (by simp [ρ]) hxNN he1
  have hn1 : ρ₁.vars nN = N := (hv1 nN n_s n_k n_t n_h n_i).trans hnρ
  have hlm1 : ρ₁.vars lm = (xs.map (agReverseKey N)).length := by
    rw [hv1 lm l_s l_k l_t l_h l_i, List.length_map]
    simp [ρ]
  have hxRev : ∀ k ∈ xs.map (agReverseKey N), k < N * N := by
    intro k hk
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hk
    exact agReverseKey_lt (hxNN z hz)
  have he2 : ∀ η : Env,
      (∀ s, s ≠ ix → s ≠ ky → η.arrs s = ρ₁.arrs s) →
      (∀ y, y ≠ sz → y ≠ kv → y ≠ tv → y ≠ hv → y ≠ iv → η.vars y = ρ₁.vars y) →
      η.vars iv < (xs.map (agReverseKey N)).length →
      (agReverseExpr (.get src (.var iv)) nN).evalB B η =
        some ((xs.map (agReverseKey N)).getD (η.vars iv) 0) := by
    intro η ha hv hi
    have hi' : η.vars iv < xs.length := by simpa only [List.length_map] using hi
    have hmem : xs.getD (η.vars iv) 0 ∈ xs := by
      rw [getD_eq_getElem hi']
      exact List.getElem_mem hi'
    have he := agReverseExpr_eval nN ((hv nN n_s n_k n_t n_h n_i).trans hn1) (by omega) hNNB
      (hxNN _ hmem) (hget η ((ha src hsrc.1 hsrc.2).trans (ha1 src hsrc.1 hsrc.2)) hi')
    rw [getD_eq_getElem hi, List.getElem_map]
    rw [getD_eq_getElem hi'] at he
    exact he
  obtain ⟨τ, h2, hD2, hv2, ha2, hl2⟩ := agDictEnumerate_run ix ky sz kv tv hv iv lm
    (agReverseExpr (.get src (.var iv)) nN) hixky hvs6 hNNB (by omega)
    (agDictUnion [] xs) (xs.map (agReverseKey N)) ρ₁ hD1
    (by simpa only [List.length_map] using hM) hlm1 hxRev he2
  refine ⟨τ, (hinit.seq (hload.seq (h1.seq h2))).mono ?_, hD2, ?_, ?_, ?_⟩
  · simp only [agReverseExpr, Expr.size, List.length_map]
    omega
  · intro y hys hyk hyt hyh hyi hyl
    rw [hv2 y hys hyk hyt hyh hyi, hv1 y hys hyk hyt hyh hyi]
    simp [ρ, ρ₀, hys, hyl]
  · intro s hsi hsk
    exact (ha2 s hsi hsk).trans (ha1 s hsi hsk)
  · intro s
    exact (hl2 s).trans (hl1 s)

/-- The source prefix of an orientation has at most its actual arc count. -/
theorem agArcDict_length_le {B N : ℕ} {ix ky sz : String} {xs : List ℕ} {σ : Env}
    (D : Orientation N) (hD : AgDictSt ix ky sz B (N * N) xs σ)
    (harc : ∀ u v : Fin N, agArcKey (u, v) ∈ xs ↔ u ∈ D.inN v) : xs.length ≤ arcCount D := by
  classical
  let rows := fun v => (D.inN v).toList
  have hrows : AgInRows D rows := ⟨fun _ => Finset.nodup_toList _, fun _ => Finset.toList_toFinset _⟩
  rw [← agArcCandidates_length hrows]
  exact agsDict_length_le_candidates hD (agArcCandidates rows)
    (fun u v hk => (agArcCandidates_mem hrows u v).mpr ((harc u v).mp hk))

end Lax3Proofs.Prog
