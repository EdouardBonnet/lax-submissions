import Lax3Proofs.SolveSweepAug

/-!
# Filtering a sparse stream into a dictionary

The loop reads exactly the supplied candidate stream. The decision command is
charged for each candidate and the insertion validates its inverse-table entry.
The key-space capacity appears only in the word and allocation bounds.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning List
open Lax62Proofs.Codegen (getD_eq_getElem)

/-- Scalar frame used by the sparse stream combinators. -/
def AgFilterVars (written : List String) (σ τ : Env) : Prop :=
  ∀ y, y ∉ written → τ.vars y = σ.vars y

private theorem agfGetD_mem {xs : List ℕ} {i : ℕ} (hi : i < xs.length) :
    xs.getD i 0 ∈ xs := by
  rw [getD_eq_getElem hi]
  exact List.getElem_mem hi

private theorem agfEvalVar {B k : ℕ} {σ : Env} {x : String}
    (hx : σ.vars x = k) (hk : k < B) : (Expr.var x).evalB B σ = some k := by
  rw [← hx]
  exact evalB_var (by omega)

/-- The first `i` accepted stream entries, with duplicate keys removed. -/
noncomputable def agFilterPart (ks xs : List ℕ) (P : ℕ → Prop) (i : ℕ) : List ℕ := by
  classical
  exact agDictUnion ks ((xs.take i).filter (fun k => decide (P k)))

@[simp] theorem agFilterPart_zero (ks xs : List ℕ) (P : ℕ → Prop) :
    agFilterPart ks xs P 0 = ks := by simp [agFilterPart]

@[simp] theorem agFilterPart_mem (ks xs : List ℕ) (P : ℕ → Prop) (i k : ℕ) :
    k ∈ agFilterPart ks xs P i ↔ k ∈ ks ∨ k ∈ xs.take i ∧ P k := by
  classical
  simp [agFilterPart]

private theorem agFilterPart_succ (ks xs : List ℕ) (P : ℕ → Prop) [DecidablePred P] {i : ℕ}
    (hi : i < xs.length) :
    agFilterPart ks xs P (i + 1) =
      if P (xs.getD i 0) then agDictGrow (agFilterPart ks xs P i) (xs.getD i 0)
        else agFilterPart ks xs P i := by
  rw [agFilterPart, List.take_succ_eq_append_getElem hi, List.filter_append,
    agDictUnion_append, getD_eq_getElem hi]
  by_cases hp : P xs[i]
  · simp only [List.filter_cons, hp, decide_true, ↓reduceIte, List.filter_nil]
    rfl
  · simp only [List.filter_cons, hp, decide_false, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
      agDictUnion_nil]
    rfl

/-- Each accepted expression is inserted into an existing sparse dictionary. -/
def agFilterCom (ix ky sz kv tv hv iv lm ans : String) (e : Expr) (test : Com) : Com :=
  .seq (.assign iv (.lit 0))
    (.while (.lt (.var iv) (.var lm))
      (.seq (.assign kv e)
        (.seq test
          (.seq (.ite (.eq (.var ans) (.lit 1)) (agDictInsert ix ky sz kv tv hv) .skip)
            (.assign iv (.add (.var iv) (.lit 1)))))))

set_option maxHeartbeats 800000 in
/-- A stream filter with explicit decision cost. Its command premise is a local
combinator premise, instantiated by concrete read-only tests in the augmentation
round; no semantic flags are required in the initial scratch. -/
theorem agFilterCom_run {B U K : ℕ} (ix ky sz kv tv hv iv lm ans : String)
    (e : Expr) (test : Com) (ws : List String)
    (harr : ix ≠ ky) (hvs : ([sz, kv, tv, hv, iv, lm] : List String).Nodup)
    (hsw : sz ∉ ws) (hkw : kv ∉ ws) (hiw : iv ∉ ws) (hlw : lm ∉ ws)
    (hUB : U < B) (h1B : 1 < B) (ks xs : List ℕ) (P : ℕ → Prop) (σ : Env)
    (hD : AgDictSt ix ky sz B U ks σ) (hL : xs.length < B)
    (hlm : σ.vars lm = xs.length) (hxU : ∀ k ∈ xs, k < U)
    (he : ∀ ρ : Env,
      (∀ a, a ≠ ix → a ≠ ky → ρ.arrs a = σ.arrs a) →
      AgFilterVars ([sz, kv, tv, hv, iv] ++ ws) σ ρ →
      ρ.vars iv < xs.length → e.evalB B ρ = some (xs.getD (ρ.vars iv) 0))
    (htest : ∀ (k : ℕ), k ∈ xs → ∀ ρ : Env,
      (∀ a, a ≠ ix → a ≠ ky → ρ.arrs a = σ.arrs a) →
      AgFilterVars ([sz, kv, tv, hv, iv] ++ ws) σ ρ → ρ.vars kv = k →
      ∃ τ, Run B test ρ τ K ∧ τ.vars ans = agBit (P k) ∧
        AgFilterVars ws ρ τ ∧ (∀ a, τ.arrs a = ρ.arrs a)) :
    ∃ τ, Run B (agFilterCom ix ky sz kv tv hv iv lm ans e test) σ τ
        ((K + e.size + 64) * xs.length + 6) ∧
      AgDictSt ix ky sz B U (agFilterPart ks xs P xs.length) τ ∧
      AgFilterVars ([sz, kv, tv, hv, iv] ++ ws) σ τ ∧
      (∀ a, a ≠ ix → a ≠ ky → τ.arrs a = σ.arrs a) ∧
      (∀ a, (τ.arrs a).length = (σ.arrs a).length) := by
  classical
  have hvs4 : ([sz, kv, tv, hv] : List String).Nodup :=
    hvs.sublist (List.take_sublist 4 [sz, kv, tv, hv, iv, lm])
  have hvs' := hvs
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hvs'
  obtain ⟨⟨hs_k, hs_t, hs_h, hs_i, hs_l⟩,
    ⟨hk_t, hk_h, hk_i, hk_l⟩, ⟨ht_h, ht_i, ht_l⟩,
    ⟨hh_i, hh_l⟩, hi_l⟩ := hvs'
  let W := [sz, kv, tv, hv, iv] ++ ws
  have hw (y : String) (hy : y ∉ W) :
      y ≠ sz ∧ y ≠ kv ∧ y ≠ tv ∧ y ≠ hv ∧ y ≠ iv ∧ y ∉ ws := by
    simpa only [W, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or, and_assoc] using hy
  have hlW : lm ∉ W := by simp [W, Ne.symm hs_l, Ne.symm hk_l,
    Ne.symm ht_l, Ne.symm hh_l, Ne.symm hi_l, hlw]
  let I : Env → Prop := fun ρ => ρ.vars iv ≤ xs.length ∧
    AgDictSt ix ky sz B U (agFilterPart ks xs P (ρ.vars iv)) ρ ∧
    AgFilterVars W σ ρ ∧
    (∀ a, a ≠ ix → a ≠ ky → ρ.arrs a = σ.arrs a) ∧
    (∀ a, (ρ.arrs a).length = (σ.arrs a).length)
  have hbody : Spec B (fun ρ => I ρ ∧ ρ.vars iv < xs.length)
      (.seq (.assign kv e)
        (.seq test
          (.seq (.ite (.eq (.var ans) (.lit 1)) (agDictInsert ix ky sz kv tv hv) .skip)
            (.assign iv (.add (.var iv) (.lit 1))))))
      (fun ρ τ => I τ ∧ τ.vars iv = ρ.vars iv + 1) (K + e.size + 60) := by
    refine Spec.of_exists ?_
    rintro ρ ⟨⟨hle, hDr, hfv, hfa, hlen⟩, hlt⟩
    let k := xs.getD (ρ.vars iv) 0
    have hkm : k ∈ xs := agfGetD_mem hlt
    have hkU : k < U := hxU k hkm
    let ρa := ρ.setVar kv k
    have h1 : Run B (.assign kv e) ρ ρa (1 + e.size) := Run.assign (he ρ hfa hfv hlt)
    have hDa : AgDictSt ix ky sz B U (agFilterPart ks xs P (ρ.vars iv)) ρa :=
      hDr.of_eq rfl rfl (by simp [ρa, hs_k])
    have hfa' : AgFilterVars W σ ρa := by
      intro y hy
      rw [show ρa.vars y = ρ.vars y by simp [ρa, (hw y hy).2.1]]
      exact hfv y hy
    obtain ⟨ρb, h2, hans, hfvb, hfab⟩ := htest k hkm ρa hfa hfa' (by simp [ρa])
    have hDb : AgDictSt ix ky sz B U (agFilterPart ks xs P (ρ.vars iv)) ρb :=
      hDa.of_eq (hfab _) (hfab _) (hfvb sz hsw)
    have hkb : ρb.vars kv = k := by rw [hfvb kv hkw]; simp [ρa]
    have hib : ρb.vars iv = ρ.vars iv := by rw [hfvb iv hiw]; simp [ρa, Ne.symm hk_i]
    have hcond : (Cond.eq (.var ans) (.lit 1)).evalB B ρb = some (agBit (P k) == 1) :=
      evalB_condEq (agfEvalVar hans (lt_of_le_of_lt (agBit_le_one _) h1B)) (evalB_lit h1B)
    have hins : ∃ ρc, Run B (.ite (.eq (.var ans) (.lit 1))
          (agDictInsert ix ky sz kv tv hv) .skip) ρb ρc 44 ∧
        AgDictSt ix ky sz B U (agFilterPart ks xs P (ρ.vars iv + 1)) ρc ∧
        (∀ y, y ≠ sz → y ≠ tv → y ≠ hv → ρc.vars y = ρb.vars y) ∧
        (∀ a, a ≠ ix → a ≠ ky → ρc.arrs a = ρb.arrs a) ∧
        (∀ a, (ρc.arrs a).length = (ρb.arrs a).length) := by
      by_cases hp : P k
      · obtain ⟨ρc, hc, hDc, _, _, _, hcvar, hcarr, hclen⟩ :=
          agDictInsert_run ix ky sz kv tv hv harr hvs4 hUB h1B ρb hDb hkb hkU
        refine ⟨ρc, (Run.ite_true (by rw [hcond, agBit_pos hp]; rfl) hc).mono (by simp [Cond.size, Expr.size]), ?_,
          hcvar, hcarr, hclen⟩
        rw [agFilterPart_succ ks xs P hlt, if_pos hp]
        exact hDc
      · refine ⟨ρb, (Run.ite_false (by rw [hcond, agBit_neg hp]; rfl) Run.skip).mono (by simp [Cond.size, Expr.size]),
          ?_, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩
        rw [agFilterPart_succ ks xs P hlt, if_neg hp]
        exact hDb
    obtain ⟨ρc, h3, hDc, hfvc, hfac, hlenc⟩ := hins
    have hic : ρc.vars iv = ρ.vars iv :=
      (hfvc iv (Ne.symm hs_i) (Ne.symm ht_i) (Ne.symm hh_i)).trans hib
    let τ := ρc.setVar iv (ρ.vars iv + 1)
    have h4 : Run B (.assign iv (.add (.var iv) (.lit 1))) ρc τ 4 :=
      Run.assign (agEvalAdd (agfEvalVar hic (by omega)) (evalB_lit h1B) (by omega))
    have hit : τ.vars iv = ρ.vars iv + 1 := by simp [τ]
    refine ⟨τ, K + e.size + 60, (h1.seq (h2.seq (h3.seq h4))).mono (by omega), le_rfl,
      ⟨by omega, ?_, ?_, ?_, ?_⟩, hit⟩
    · rw [hit]
      exact hDc.of_eq rfl rfl (by simp [τ, hs_i])
    · intro y hy
      obtain ⟨hys, hyk, hyt, hyh, hyi, hyw⟩ := hw y hy
      rw [show τ.vars y = ρc.vars y by simp [τ, hyi], hfvc y hys hyt hyh, hfvb y hyw]
      exact hfa' y hy
    · intro a hai hak
      rw [show τ.arrs a = ρc.arrs a from rfl, hfac a hai hak, hfab a]
      exact hfa a hai hak
    · intro a
      rw [show τ.arrs a = ρc.arrs a from rfl, hlenc a, hfab a]
      exact hlen a
  have hloop := Spec.forRangeZero (B := B) iv lm I xs.length (K + e.size + 60) hL
    (fun ρ h => h.1) (fun ρ h => (h.2.2.1 lm hlW).trans hlm) hbody
  have hstart : I (σ.setVar iv 0) := by
    refine ⟨by simp, ?_, ?_, fun _ _ _ => rfl, fun _ => rfl⟩
    · simpa only [vars_setVar, if_pos rfl, agFilterPart_zero] using
        hD.of_eq (τ := σ.setVar iv 0) rfl rfl (by simp [hs_i])
    · intro y hy
      simp [(hw y hy).2.2.2.2.1]
  obtain ⟨τ, hrun, hI, hiv⟩ := hloop.run hstart
  refine ⟨τ, hrun.mono (by simp only [Nat.add_assoc, Nat.reduceAdd, le_refl]),
    ?_, hI.2.2.1, hI.2.2.2.1, hI.2.2.2.2⟩
  have hlast := hI.2.1
  simpa only [hiv] using hlast

end Lax3Proofs.Prog
