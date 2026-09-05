import Lax67Proofs.Spec

/-!
Array contents remain words throughout any bounded run. This invariant
also covers unused cells of sparse inverse tables, whose stale values
must be readable before the table validates them against occupied keys.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning

/-- Every allocated array cell is a word below the run's bound. -/
def ArrWords (B : ℕ) (σ : Env) : Prop :=
  ∀ a v, v ∈ σ.arrs a → v < B

theorem ArrWords.setArr {B : ℕ} {σ : Env} (hσ : ArrWords B σ)
    (a : String) (i v : ℕ) (hv : v < B) : ArrWords B (σ.setArr a i v) := by
  intro b z hz
  rw [arrs_setArr] at hz
  split at hz
  · rcases List.mem_or_eq_of_mem_set hz with hz | rfl
    · exact hσ a z hz
    · exact hv
  · exact hσ b z hz

/-- Only stores change arrays, and a bounded store writes a bounded value. -/
theorem BigStepB.arrWords {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStepB B c σ σ' k) (hσ : ArrWords B σ) : ArrWords B σ' := by
  induction h with
  | skip => exact hσ
  | assign _ => exact hσ
  | store _ he _ => exact hσ.setArr _ _ _ (Expr.lt_of_evalB he)
  | seq _ _ ih ih' => exact ih' (ih hσ)
  | ite_true _ _ ih => exact ih hσ
  | ite_false _ _ ih => exact ih hσ
  | while_true _ _ _ ih ih' => exact ih' (ih hσ)
  | while_false _ => exact hσ
  | read _ => exact hσ
  | write _ => exact hσ

theorem Run.arrWords {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ}
    (h : Run B c σ σ' K) (hσ : ArrWords B σ) : ArrWords B σ' := by
  obtain ⟨_, _, hr⟩ := h
  exact BigStepB.arrWords hr hσ

/-- Lift a routine's specification without altering its command or cost. -/
theorem Spec.arrWords {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop}
    {c : Com} {K : ℕ} (h : Spec B P c Q K) :
    Spec B (fun σ => P σ ∧ ArrWords B σ) c
      (fun σ σ' => Q σ σ' ∧ ArrWords B σ') K := by
  intro σ hσ
  obtain ⟨σ', hr, hq⟩ := h σ hσ.1
  exact ⟨σ', hr, hq, Run.arrWords hr hσ.2⟩

theorem arrWords_initEnv {B : ℕ} (hB : 0 < B) (ext : String → ℕ)
    (x : List ℕ) : ArrWords B (initEnv ext x) := by
  intro a v hv
  have : v = 0 := (List.mem_replicate.mp hv).2
  simpa [this] using hB

end Lax3Proofs.Prog
