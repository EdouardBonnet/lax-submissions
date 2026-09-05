import Lax3Proofs.SolvePrepCleanStep

/-! The centre loop returns the root-prefix invariant. Its cost remains the
sum of the actual per-centre charges. -/

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
variable {L n₀ : ℕ}

open Classical in
theorem centreLoopClean_of_step (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (ca co cm : ℕ → String)
    (bodyB : ℕ → Com → Com)
    (KC : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ)
    (hn0B : n₀ < B)
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (hLSc : ∀ j, ctrName j ∈ LS j)
    (hstep : CentreStepClean B S ord ℓp htabF hbf Adm KB Scr LS LA ca co cm
      bodyB KC) :
    CentreLoopClean B S ord ℓp htabF hbf Adm KB Scr LS LA ca co cm
      (centreLoopB bodyB)
      (fun k j A => (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 6) := by
  intro k j nxCom hnx hown
  obtain ⟨hbody, hbodyOwn⟩ := hstep k j nxCom hnx hown
  constructor
  · -- the loop's specification
    intro A hdiag hAdm hbot
    have hNle : A.N ≤ n₀ := arenaN_le A
    have hNB : A.N < B := lt_of_le_of_lt hNle hn0B
    -- the invariant, as a state predicate over the counter cell
    set I : Env → Prop := fun σ =>
      CLInv S ord ℓp htabF hbf Scr ca co cm k j A (σ.vars (ctrName j)) σ ∧
      σ.vars (ctrName j) ≤ A.N ∧ PrepClean n₀ B σ with hI_def
    have hn_eq : ∀ σ, I σ → σ.vars (arenaNames j).nN = A.N :=
      fun σ hσ => hσ.1.1.1.n_eq
    -- the guard evaluates on the invariant
    have hdef : ∀ σ, I σ → ∃ v,
        (Cond.lt (.var (ctrName j)) (.var (arenaNames j).nN)).evalB B σ
          = some v := by
      intro σ hσ
      exact evalB_condLt_vars (by have := hσ.2.1; omega)
        (by rw [hn_eq σ hσ]; exact hNB)
    -- one turn: the body at the counter's centre, then the increment
    have hturn : ∀ σ, I σ →
        (Cond.lt (.var (ctrName j)) (.var (arenaNames j).nN)).evalB B σ
          = some true →
        ∃ σ' K, Run B (.seq (bodyB j nxCom)
            (.assign (ctrName j) (.add (.var (ctrName j)) (.lit 1)))) σ σ' K ∧
          I σ' ∧
          1 + (Cond.lt (.var (ctrName j)) (.var (arenaNames j).nN)).size + K +
            (∑ i ∈ Finset.Ico (σ'.vars (ctrName j)) A.N, (KC k j A i + 8))
            ≤ ∑ i ∈ Finset.Ico (σ.vars (ctrName j)) A.N, (KC k j A i + 8) := by
      intro σ hσ htrue
      obtain ⟨hInv, hle, hclean⟩ := hσ
      have hlt : σ.vars (ctrName j) < A.N := by
        have := lt_of_condLt_true htrue
        rwa [hn_eq σ ⟨hInv, hle, hclean⟩] at this
      -- the body, at the counter's centre
      obtain ⟨σ', hrun1, ⟨hpost, hctr'⟩, hclean'⟩ :=
        hbody A hdiag hAdm hbot ⟨σ.vars (ctrName j), hlt⟩ σ ⟨⟨hInv, rfl⟩, hclean⟩
      -- the increment
      have hctrB : σ'.vars (ctrName j) < B := by
        rw [hctr']
        omega
      have hev : (Expr.add (.var (ctrName j)) (.lit 1)).evalB B σ'
          = some (σ'.vars (ctrName j) + 1) := by
        have := evalB_bin (op := .add) (e := Expr.var (ctrName j))
          (f := Expr.lit 1) (evalB_var hctrB)
          (evalB_lit (by omega))
          (by simp only [Bop.apply_add]; rw [hctr']; omega)
        simpa using this
      have hrun2 : Run B (.assign (ctrName j)
            (.add (.var (ctrName j)) (.lit 1))) σ'
          (σ'.setVar (ctrName j) (σ'.vars (ctrName j) + 1)) 4 := by
        have := Run.assign (B := B) (x := ctrName j)
          (e := .add (.var (ctrName j)) (.lit 1)) hev
        exact this.mono (by simp [Expr.size])
      refine ⟨σ'.setVar (ctrName j) (σ'.vars (ctrName j) + 1),
        KC k j A (σ.vars (ctrName j)) + 4, hrun1.seq hrun2, ?_, ?_⟩
      · -- the invariant, at the advanced counter
        constructor
        · have hcv : (σ'.setVar (ctrName j)
              (σ'.vars (ctrName j) + 1)).vars (ctrName j)
              = σ.vars (ctrName j) + 1 := by
            rw [← hctr']
            simp
          rw [hcv]
          exact clInv_setVar_ctr (hscrLen j) hpost _
        · refine ⟨?_, hclean'⟩
          show (σ'.setVar (ctrName j)
              (σ'.vars (ctrName j) + 1)).vars (ctrName j) ≤ A.N
          rw [show (σ'.setVar (ctrName j)
              (σ'.vars (ctrName j) + 1)).vars (ctrName j)
              = σ'.vars (ctrName j) + 1 by simp, hctr']
          omega
      · -- the tail-sum potential pays for the turn
        have hcv : (σ'.setVar (ctrName j)
            (σ'.vars (ctrName j) + 1)).vars (ctrName j)
            = σ.vars (ctrName j) + 1 := by
          rw [← hctr']
          simp
        rw [hcv, Finset.sum_eq_sum_Ico_succ_bot hlt
          (f := fun i => KC k j A i + 8)]
        simp only [Cond.size, Expr.size]
        omega
    -- the loop, priced by the tail-sum potential
    have hloop := Spec.while_potential
      (B := B) (c := .seq (bodyB j nxCom)
        (.assign (ctrName j) (.add (.var (ctrName j)) (.lit 1))))
      (b := .lt (.var (ctrName j)) (.var (arenaNames j).nN))
      (P := fun σ => I σ ∧ σ.vars (ctrName j) = 0)
      I (fun σ => ∑ i ∈ Finset.Ico (σ.vars (ctrName j)) A.N, (KC k j A i + 8))
      hdef hturn (fun σ hσ => hσ.1)
      (K := (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 4)
      (fun σ hσ => by
        show (∑ i ∈ Finset.Ico (σ.vars (ctrName j)) A.N, (KC k j A i + 8))
            + 1 + (Cond.lt (.var (ctrName j)) (.var (arenaNames j).nN)).size
          ≤ (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 4
        rw [hσ.2, Finset.range_eq_Ico]
        simp only [Cond.size, Expr.size]
        omega)
    -- the initialisation in front
    have hinit : Spec B
        (fun σ => (BlockPre S j (hbf j) A (htabF j A) (Scr j)
            (arenaNames j) σ ∧
          CtrArr (ca j) (centre S A ((ord A.N A.G).order)) σ ∧
          ClusterCsr (co j) (cm j) (cluster S A ((ord A.N A.G).order)) σ) ∧
          PrepClean n₀ B σ)
        (.assign (ctrName j) (.lit 0))
        (fun σ σ' => σ' = σ.setVar (ctrName j) 0) 2 := by
      refine (Spec.assign (f := fun _ => 0) ?_).mono (by simp [Expr.size])
      intro σ _
      exact evalB_lit (by omega)
    refine (Spec.seq hinit hloop ?_ ?_).mono
      (show 2 + ((∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 4)
          ≤ (∑ i ∈ Finset.range A.N, (KC k j A i + 8)) + 6 by omega)
    · -- the zeroed counter establishes the invariant: nothing is
      -- written yet, and no centre is below `0`
      rintro σ σ' ⟨⟨hpre, hctr, hcsr⟩, hclean⟩ rfl
      have hinv0 : CLInv S ord ℓp htabF hbf Scr ca co cm k j A 0 σ :=
        ⟨hpre, hctr, hcsr, fun v hv => absurd hv (by omega)⟩
      refine ⟨⟨?_, by simp, hclean⟩, by simp⟩
      have := clInv_setVar_ctr (hscrLen j) hinv0 0
      rwa [show (σ.setVar (ctrName j) 0).vars (ctrName j) = 0 by simp]
    · -- at `counter = N` the partial table is the whole table
      rintro σ σ' σ'' - - ⟨⟨⟨⟨hA, htab, -⟩, -, -, hpart⟩, hle, hclean⟩, hfalse⟩
      have hn_eq'' : σ''.vars (arenaNames j).nN = A.N := hA.n_eq
      have hge : σ''.vars (ctrName j) = A.N := by
        have := le_of_condLt_false hfalse
        rw [hn_eq''] at this
        omega
      refine ⟨⟨hA, htab, ?_⟩, hclean⟩
      intro v i hi
      refine hpart v ?_ i hi
      rw [hge]
      exact (centre S A ((ord A.N A.G).order) v).isLt
  · -- the write discipline: the counter is the level's, the body its
    -- discharger's
    constructor
    · intro y hy
      simp only [centreLoopB, Com.wvars, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hy
      rcases hy with rfl | hy | rfl
      · exact ⟨j, le_rfl, hLSc j⟩
      · exact hbodyOwn.1 y hy
      · exact ⟨j, le_rfl, hLSc j⟩
    · intro a ha
      simp only [centreLoopB, Com.warrs, List.mem_append,
        List.not_mem_nil, or_false, false_or] at ha
      exact hbodyOwn.2 a ha


end Lax3Proofs.Prog
