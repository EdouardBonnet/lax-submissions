import Lax3Proofs.SolveSweepAug

/-!
# Sparse deterministic augmentation decisions

The candidate dictionary has already eliminated repeated witnesses. A greedy
orientation decision reads old-arc, transitive and fraternal membership at
both endpoints and the computed min-degree ranks. It performs constant work
per candidate and uses the exact `mem_greedyStep` predicate.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax3Proofs.Augmentation Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.CoverRoutine

private theorem agsEvalVar {B k : ℕ} {σ : Env} {x : String}
    (hx : σ.vars x = k) (hk : k < B) : (Expr.var x).evalB B σ = some k := by
  rw [← hx]
  exact evalB_var (by omega)

private def agsNot (e : Expr) : Expr := .sub (.lit 1) e
private def agsAnd (e f : Expr) : Expr := .mul e f
private def agsOr (e f : Expr) : Expr := .sub (.lit 1) (.sub (.lit 1) (.add e f))

private theorem agsEvalNot {B : ℕ} {σ : Env} {e : Expr} {p : Prop}
    (hB : 1 < B) (he : e.evalB B σ = some (agBit p)) :
    (agsNot e).evalB B σ = some (agBit (¬ p)) := by
  have hh := agEvalSub (evalB_lit hB) he (by have := agBit_le_one p; omega)
  rw [agNum_not rfl] at hh
  exact hh

private theorem agsEvalAnd {B : ℕ} {σ : Env} {e f : Expr} {p q : Prop}
    (hB : 1 < B) (he : e.evalB B σ = some (agBit p))
    (hf : f.evalB B σ = some (agBit q)) :
    (agsAnd e f).evalB B σ = some (agBit (p ∧ q)) := by
  have hm : agBit p * agBit q < B := by
    rw [agBit_mul]
    exact lt_of_le_of_lt (agBit_le_one _) hB
  have hh := agEvalMul he hf hm
  rw [agBit_mul] at hh
  exact hh

private theorem agsEvalOr {B : ℕ} {σ : Env} {e f : Expr} {p q : Prop}
    (hB : 2 < B) (he : e.evalB B σ = some (agBit p))
    (hf : f.evalB B σ = some (agBit q)) :
    (agsOr e f).evalB B σ = some (agBit (p ∨ q)) := by
  have hp := agBit_le_one p
  have hq := agBit_le_one q
  have hs := agEvalAdd he hf (by omega)
  have h1 := agEvalSub (evalB_lit (show 1 < B by omega)) hs (by omega)
  have h2 := agEvalSub (evalB_lit (show 1 < B by omega)) h1 (by omega)
  have hh : 1 - (1 - (agBit p + agBit q)) = agBit (p ∨ q) := by
    classical
    by_cases hp' : p <;> by_cases hq' : q <;> simp [agBit, hp', hq']
  rwa [hh] at h2

/-- Branchless exact orientation decision after the five sparse lookups. -/
def agsGreedyExpr (ofv orv tfv trv ffv ra uv vv : String) : Expr :=
  agsOr (.var ofv)
    (agsAnd (agsAnd (agsNot (.var ofv)) (agsNot (.var orv)))
      (agsAnd (agsOr (.var tfv) (.var ffv))
        (agsOr (agLtE (.get ra (.var uv)) (.get ra (.var vv)))
          (agsNot (agsOr (.var trv) (.var ffv))))))

private theorem agsFrat_swap {N : ℕ} (D : Orientation N) (u v : Fin N) :
    FratLink D v u ↔ FratLink D u v := ⟨FratLink.symm, FratLink.symm⟩

/-- The lookup formula is the exact deterministic round, including forced
transitive directions and old arcs in either direction. -/
theorem agsGreedyExpr_eval {B N : ℕ} (D : Orientation N) (rank : Fin N → ℕ)
    (ofv orv tfv trv ffv ra uv vv : String) (σ : Env) (u v : Fin N)
    (hNB : N + 1 < B) (hRank : ∀ w, rank w < N)
    (hraL : N ≤ (σ.arrs ra).length)
    (hra : ∀ w : Fin N, (σ.arrs ra).getD w 0 = rank w)
    (hu : σ.vars uv = u) (hv : σ.vars vv = v)
    (hof : σ.vars ofv = agBit (u ∈ D.inN v))
    (hor : σ.vars orv = agBit (v ∈ D.inN u))
    (htf : σ.vars tfv = agBit (TransLink D u v))
    (htr : σ.vars trv = agBit (TransLink D v u))
    (hff : σ.vars ffv = agBit (FratLink D u v)) :
    (agsGreedyExpr ofv orv tfv trv ffv ra uv vv).evalB B σ =
      some (agBit (u ∈ (greedyStep rank D).inN v)) := by
  have hB : 2 < B := by have := u.isLt; omega
  have h1B : 1 < B := by omega
  have hb (x : String) (p : Prop) (h : σ.vars x = agBit p) :
      (Expr.var x).evalB B σ = some (agBit p) :=
    agsEvalVar h (lt_of_le_of_lt (agBit_le_one _) h1B)
  have hget (x : String) (w : Fin N) (hx : σ.vars x = w) :
      (Expr.get ra (.var x)).evalB B σ = some (rank w) := by
    exact evalB_get (agsEvalVar hx (lt_trans w.isLt (by omega)))
      (by rw [getElem?_of_lt (lt_of_lt_of_le w.isLt hraL), hra w])
      (lt_trans (hRank w) (by omega))
  have hlt := agEval_ltE (hget uv u hu) (hget vv v hv)
    (by have := hRank u; omega) (by omega)
  have hform := agsEvalOr hB (hb ofv _ hof)
    (agsEvalAnd h1B
      (agsEvalAnd h1B (agsEvalNot h1B (hb ofv _ hof)) (agsEvalNot h1B (hb orv _ hor)))
      (agsEvalAnd h1B (agsEvalOr hB (hb tfv _ htf) (hb ffv _ hff))
        (agsEvalOr hB hlt (agsEvalNot h1B (agsEvalOr hB (hb trv _ htr) (hb ffv _ hff))))))
  have hp : ((u ∈ D.inN v) ∨ ((¬ u ∈ D.inN v ∧ ¬ v ∈ D.inN u) ∧
      ((TransLink D u v ∨ FratLink D u v) ∧
        (rank u < rank v ∨ ¬ (TransLink D v u ∨ FratLink D u v))))) ↔
      u ∈ (greedyStep rank D).inN v := by
    rw [mem_greedyStep, agsFrat_swap D u v]
    simp only [Orientation.Adjacent, not_or, and_assoc]
  simpa only [hp] using hform

/-- A lookup request contains names only. Its tag is a static identifier used
by proof-side metadata; it has no role in the executed command. -/
structure AgsLookup where
  tag : ℕ
  ix : String
  ky : String
  sz : String
  key : String
  hit : String

/-- A fixed sequence of sparse dictionary lookups. -/
def agsLookupSeq (tmp : String) : List AgsLookup → Com
  | [] => .skip
  | q :: qs => .seq (agDictFind q.ix q.ky q.sz q.key tmp q.hit) (agsLookupSeq tmp qs)

private theorem agsLookupSeq_run {B U : ℕ} (tmp : String) (qs : List AgsLookup)
    (keys : AgsLookup → List ℕ) (hUB : U < B) (h1B : 1 < B)
    (hnod : (qs.map AgsLookup.hit).Nodup)
    (hvs : ∀ q ∈ qs, ([q.sz, q.key, tmp, q.hit] : List String).Nodup)
    (hinput : ∀ q ∈ qs, ∀ r ∈ qs, q.sz ≠ r.hit ∧ q.key ≠ r.hit)
    (σ : Env) (hD : ∀ q ∈ qs, AgDictSt q.ix q.ky q.sz B U (keys q) σ)
    (hk : ∀ q ∈ qs, σ.vars q.key < U) :
    ∃ τ, Run B (agsLookupSeq tmp qs) σ τ (20 * qs.length + 1) ∧
      (∀ q ∈ qs, τ.vars q.hit = agBit (σ.vars q.key ∈ keys q)) ∧
      (∀ y, y ≠ tmp → (∀ q ∈ qs, y ≠ q.hit) → τ.vars y = σ.vars y) ∧
      (∀ a, τ.arrs a = σ.arrs a) := by
  induction qs generalizing σ with
  | nil => exact ⟨σ, Run.skip, by simp, by simp, fun _ => rfl⟩
  | cons q qs ih =>
      have hqvs := hvs q (List.mem_cons_self ..)
      have hqvs' := hqvs
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        not_or, List.nodup_nil, and_true, not_false_eq_true] at hqvs'
      obtain ⟨⟨hs_k, hs_t, hs_h⟩, ⟨hk_t, hk_h⟩, ht_h⟩ := hqvs'
      have hnhead : q.hit ∉ qs.map AgsLookup.hit := (List.nodup_cons.mp hnod).1
      have hntail : (qs.map AgsLookup.hit).Nodup := (List.nodup_cons.mp hnod).2
      obtain ⟨ρ, h1, hDq, ht, hh, hfv, hfa⟩ := agDictFind_run q.ix q.ky q.sz q.key tmp q.hit
        hqvs hUB h1B σ (hD q (List.mem_cons_self ..)) rfl (hk q (List.mem_cons_self ..))
      have hdt : ∀ r ∈ qs, AgDictSt r.ix r.ky r.sz B U (keys r) ρ := by
        intro r hr
        have hrv := hvs r (List.mem_cons_of_mem _ hr)
        have hrt : r.sz ≠ tmp := by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
            not_or, List.nodup_nil, and_true, not_false_eq_true] at hrv
          exact hrv.1.2.1
        exact (hD r (List.mem_cons_of_mem _ hr)).of_eq (hfa _) (hfa _)
          (hfv r.sz hrt (hinput r (List.mem_cons_of_mem _ hr) q (List.mem_cons_self ..)).1)
      have hkt : ∀ r ∈ qs, ρ.vars r.key < U := by
        intro r hr
        have hrv := hvs r (List.mem_cons_of_mem _ hr)
        have hrt : r.key ≠ tmp := by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
            not_or, List.nodup_nil, and_true, not_false_eq_true] at hrv
          exact hrv.2.1.1
        rw [hfv r.key hrt (hinput r (List.mem_cons_of_mem _ hr) q (List.mem_cons_self ..)).2]
        exact hk r (List.mem_cons_of_mem _ hr)
      obtain ⟨τ, h2, hhit, hframe, harr⟩ := ih hntail
        (fun r hr => hvs r (List.mem_cons_of_mem _ hr))
        (fun r hr s hs => hinput r (List.mem_cons_of_mem _ hr) s (List.mem_cons_of_mem _ hs))
        ρ hdt hkt
      refine ⟨τ, (h1.seq h2).mono (by simp; omega), ?_, ?_, fun a => (harr a).trans (hfa a)⟩
      · intro r hr
        rcases List.mem_cons.mp hr with heqr | hr
        · rw [heqr]
          rw [hframe q.hit (Ne.symm ht_h) ?_]
          · exact hh
          · intro r hr he
            exact hnhead (List.mem_map.mpr ⟨r, hr, he.symm⟩)
        · rw [hhit r hr]
          have hrv := hvs r (List.mem_cons_of_mem _ hr)
          have hrt : r.key ≠ tmp := by
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
              not_or, List.nodup_nil, and_true, not_false_eq_true] at hrv
            exact hrv.2.1.1
          rw [hfv r.key hrt (hinput r (List.mem_cons_of_mem _ hr) q (List.mem_cons_self ..)).2]
      · intro y hyt hy
        rw [hframe y hyt (fun r hr => hy r (List.mem_cons_of_mem _ hr))]
        exact hfv y hyt (hy q (List.mem_cons_self ..))

/-- The five tests needed by `mem_greedyStep`: both old directions, both
transitive directions and the symmetric fraternal link. -/
def agsQueries (oi ok os ti tk ts fi fk fs kf kr ofv orv tfv trv ffv : String) : List AgsLookup :=
  [⟨0, oi, ok, os, kf, ofv⟩, ⟨1, oi, ok, os, kr, orv⟩,
   ⟨2, ti, tk, ts, kf, tfv⟩, ⟨3, ti, tk, ts, kr, trv⟩,
   ⟨4, fi, fk, fs, kf, ffv⟩]

/-- The actual sparse greedy decision, including every membership lookup. -/
def agsGreedyTest (oi ok os ti tk ts fi fk fs kf kr tmp ofv orv tfv trv ffv ra uv vv ans : String) : Com :=
  .seq (agsLookupSeq tmp (agsQueries oi ok os ti tk ts fi fk fs kf kr ofv orv tfv trv ffv))
    (.assign ans (agsGreedyExpr ofv orv tfv trv ffv ra uv vv))

@[simp] theorem agsGreedyExpr_size (ofv orv tfv trv ffv ra uv vv : String) :
    (agsGreedyExpr ofv orv tfv trv ffv ra uv vv).size = 45 := rfl

set_option maxHeartbeats 1200000 in
/-- A constant-cost machine decision for the exact deterministic augmentation
rule. Membership is obtained by five validated sparse lookups, not assumed as
precomputed scratch flags. -/
theorem agsGreedyTest_run {B N U : ℕ} (D : Orientation N) (rank : Fin N → ℕ)
    (oi ok os ti tk ts fi fk fs kf kr tmp ofv orv tfv trv ffv ra uv vv ans : String)
    (hnames : ([os, ts, fs, kf, kr, tmp, ofv, orv, tfv, trv, ffv, uv, vv, ans] : List String).Nodup)
    (hNB : N + 1 < B) (hNU : N * N ≤ U) (hUB : U < B)
    (hRank : ∀ w, rank w < N)
    (oks tks fks : List ℕ)
    (hOld : ∀ a b : Fin N, agArcKey (a, b) ∈ oks ↔ a ∈ D.inN b)
    (hTrans : ∀ a b : Fin N, agArcKey (a, b) ∈ tks ↔ TransLink D a b)
    (hFrat : ∀ a b : Fin N, agArcKey (a, b) ∈ fks ↔ FratLink D a b)
    (σ : Env) (u v : Fin N)
    (hO : AgDictSt oi ok os B U oks σ) (hT : AgDictSt ti tk ts B U tks σ)
    (hF : AgDictSt fi fk fs B U fks σ)
    (hkf : σ.vars kf = agArcKey (u, v)) (hkr : σ.vars kr = agArcKey (v, u))
    (hu : σ.vars uv = u) (hv : σ.vars vv = v)
    (hraL : N ≤ (σ.arrs ra).length)
    (hra : ∀ w : Fin N, (σ.arrs ra).getD w 0 = rank w) :
    ∃ τ, Run B (agsGreedyTest oi ok os ti tk ts fi fk fs kf kr tmp ofv orv tfv trv ffv ra uv vv ans)
        σ τ 147 ∧
      τ.vars ans = agBit (u ∈ (greedyStep rank D).inN v) ∧
      (∀ y, y ≠ tmp → y ≠ ofv → y ≠ orv → y ≠ tfv → y ≠ trv → y ≠ ffv → y ≠ ans →
        τ.vars y = σ.vars y) ∧
      (∀ a, τ.arrs a = σ.arrs a) := by
  let qs := agsQueries oi ok os ti tk ts fi fk fs kf kr ofv orv tfv trv ffv
  let keys : AgsLookup → List ℕ := fun q => if q.tag < 2 then oks else if q.tag < 4 then tks else fks
  have hne := hnames
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hne
  have hnHit : (qs.map AgsLookup.hit).Nodup := by
    simp only [qs, agsQueries, List.map_cons, List.map_nil]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true, not_false_eq_true]
    tauto
  have hvs : ∀ q ∈ qs, ([q.sz, q.key, tmp, q.hit] : List String).Nodup := by
    intro q hq
    simp only [qs, agsQueries, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        not_or, List.nodup_nil, and_true, not_false_eq_true] <;> tauto
  have hinput : ∀ q ∈ qs, ∀ r ∈ qs, q.sz ≠ r.hit ∧ q.key ≠ r.hit := by
    intro q hq r hr
    simp only [qs, agsQueries, List.mem_cons, List.not_mem_nil, or_false] at hq hr
    rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> tauto
  have hD : ∀ q ∈ qs, AgDictSt q.ix q.ky q.sz B U (keys q) σ := by
    intro q hq
    simp only [qs, agsQueries, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp only [keys, Nat.reduceLT, ↓reduceIte]
    · exact hO
    · exact hO
    · exact hT
    · exact hT
    · exact hF
  have hk : ∀ q ∈ qs, σ.vars q.key < U := by
    intro q hq
    simp only [qs, agsQueries, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · rw [hkf]; exact lt_of_lt_of_le (agArcKey_lt _) hNU
    · rw [hkr]; exact lt_of_lt_of_le (agArcKey_lt _) hNU
    · rw [hkf]; exact lt_of_lt_of_le (agArcKey_lt _) hNU
    · rw [hkr]; exact lt_of_lt_of_le (agArcKey_lt _) hNU
    · rw [hkf]; exact lt_of_lt_of_le (agArcKey_lt _) hNU
  obtain ⟨ρ, hlook, hhit, hframe, harr⟩ :=
    agsLookupSeq_run tmp qs keys hUB (by omega) hnHit hvs hinput σ hD hk
  have hof : ρ.vars ofv = agBit (u ∈ D.inN v) := by
    have hh := hhit ⟨0, oi, ok, os, kf, ofv⟩ (by simp [qs, agsQueries])
    simpa only [keys, Nat.reduceLT, ↓reduceIte, hkf, hOld] using hh
  have hor : ρ.vars orv = agBit (v ∈ D.inN u) := by
    have hh := hhit ⟨1, oi, ok, os, kr, orv⟩ (by simp [qs, agsQueries])
    simpa only [keys, Nat.reduceLT, ↓reduceIte, hkr, hOld] using hh
  have htf : ρ.vars tfv = agBit (TransLink D u v) := by
    have hh := hhit ⟨2, ti, tk, ts, kf, tfv⟩ (by simp [qs, agsQueries])
    simpa only [keys, Nat.reduceLT, ↓reduceIte, hkf, hTrans] using hh
  have htr : ρ.vars trv = agBit (TransLink D v u) := by
    have hh := hhit ⟨3, ti, tk, ts, kr, trv⟩ (by simp [qs, agsQueries])
    simpa only [keys, Nat.reduceLT, ↓reduceIte, hkr, hTrans] using hh
  have hff : ρ.vars ffv = agBit (FratLink D u v) := by
    have hh := hhit ⟨4, fi, fk, fs, kf, ffv⟩ (by simp [qs, agsQueries])
    simpa only [keys, Nat.reduceLT, ↓reduceIte, hkf, hFrat] using hh
  have hfree : ∀ y, y ≠ tmp → y ≠ ofv → y ≠ orv → y ≠ tfv → y ≠ trv → y ≠ ffv →
      ρ.vars y = σ.vars y := by
    intro y ht ho hr htf htr hf
    apply hframe y ht
    intro q hq
    simp only [qs, agsQueries, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact ho
    · exact hr
    · exact htf
    · exact htr
    · exact hf
  have hur : ρ.vars uv = u := by
    rw [hfree uv (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) (by tauto)]
    exact hu
  have hvr : ρ.vars vv = v := by
    rw [hfree vv (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) (by tauto)]
    exact hv
  have he := agsGreedyExpr_eval D rank ofv orv tfv trv ffv ra uv vv ρ u v hNB hRank
    (by rw [harr]; exact hraL) (by intro w; rw [harr]; exact hra w)
    hur hvr hof hor htf htr hff
  let τ := ρ.setVar ans (agBit (u ∈ (greedyStep rank D).inN v))
  have hlast : Run B (.assign ans (agsGreedyExpr ofv orv tfv trv ffv ra uv vv)) ρ τ 46 :=
    (Run.assign he).mono (by rw [agsGreedyExpr_size])
  refine ⟨τ, (hlook.seq hlast).mono ?_, by simp [τ], ?_, harr⟩
  · simp only [qs, agsQueries, List.length_cons, List.length_nil]
    omega
  · intro y ht ho hr hf ht' hfr ha
    rw [show τ.vars y = ρ.vars y by simp [τ, ha]]
    exact hfree y ht ho hr hf ht' hfr

end Lax3Proofs.Prog
