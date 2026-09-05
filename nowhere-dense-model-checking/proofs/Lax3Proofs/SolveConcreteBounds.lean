import Lax3Proofs.SolveConcreteFrame
import Lax3Proofs.SolveSegReadRun
import Lax3Proofs.SolveChannels

/-! Finite, schedule-only constants for the concrete machine. -/
namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
open Lax3.DistFO Lax3.ScatterSentences Lax3.Locality Lax3Proofs.LocalityFun
variable {L : ℕ}

/-- Maximum over the finitely many static levels. -/
def concreteLevelMax (S : Setup L) (f : ℕ → ℕ) : ℕ :=
  (Finset.range (S.depth + 1)).sup f

theorem concreteLevelMax_le (S : Setup L) (f : ℕ → ℕ) {j : ℕ}
    (hj : j ≤ S.depth) : f j ≤ concreteLevelMax S f :=
  Finset.le_sup (by simpa using Nat.lt_succ_of_le hj)

open Classical in
noncomputable def concreteQdepth (S : Setup L) : ℕ :=
  concreteLevelMax S (fun j => (levelFml S j).toFinset.sup qdepth)

theorem concreteQdepth_bound (S : Setup L) {j : ℕ} (hj : j ≤ S.depth)
    {β : DistFO (S.pal j) 1} (hβ : β ∈ levelFml S j) :
    qdepth β ≤ concreteQdepth S := by
  classical
  exact le_trans (Finset.le_sup (f := qdepth) (s := (levelFml S j).toFinset) (by simpa using hβ)) (concreteLevelMax_le S (fun i => (levelFml S i).toFinset.sup qdepth) hj)

noncomputable def concreteTopAtoms (S : Setup L) : List (ScatterSentence L) :=
  scatterAtoms S.choice S.φ S.hφ

open Classical in
noncomputable def concreteAtomBound {Λ : ℕ} (l : List (ScatterSentence Λ)) : ℕ :=
  l.length + l.toFinset.sup (fun a => a.r + 2 + a.t)

theorem concreteAtomBound_length {Λ : ℕ} (l : List (ScatterSentence Λ)) :
    l.length ≤ concreteAtomBound l := Nat.le_add_right ..

theorem concreteAtomBound_mem {Λ : ℕ} {l : List (ScatterSentence Λ)}
    {a : ScatterSentence Λ} (ha : a ∈ l) :
    a.r + 2 ≤ concreteAtomBound l ∧ a.t ≤ concreteAtomBound l := by
  classical
  have h : a.r + 2 + a.t ≤ l.toFinset.sup (fun a => a.r + 2 + a.t) :=
    Finset.le_sup (f := fun a => a.r + 2 + a.t) (s := l.toFinset) (by simpa using ha)
  unfold concreteAtomBound
  omega

/-- All static dimensions and scalar constants fit this fixed coefficient. -/
noncomputable def concreteScale (S : Setup L) : ℕ :=
  16 + S.width + S.depth + (2 * S.R + 3) + S.depth * (2 * S.R + 2) +
    concreteLevelMax S S.pal +
    concreteLevelMax S (fun j => (levelFml S j).length) +
    concreteLevelMax S (fun j => concreteAtomBound (levelAtoms S j)) +
    concreteAtomBound (concreteTopAtoms S) +
    concreteLevelMax S (fun j => 2 ^ S.pal j * (concreteQdepth S + 1))

theorem concreteScale_pos (S : Setup L) : 0 < concreteScale S := by
  unfold concreteScale
  omega

theorem concreteScale_static (S : Setup L) :
    4 ≤ concreteScale S ∧ S.width ≤ concreteScale S ∧
    S.depth ≤ concreteScale S ∧ 2 * S.R + 3 ≤ concreteScale S ∧
    S.depth * (2 * S.R + 2) ≤ concreteScale S := by
  unfold concreteScale
  omega

theorem concreteScale_level (S : Setup L) {j : ℕ} (hj : j ≤ S.depth) :
    S.pal j ≤ concreteScale S ∧ (levelFml S j).length ≤ concreteScale S ∧
    concreteAtomBound (levelAtoms S j) ≤ concreteScale S ∧
    2 ^ S.pal j * (concreteQdepth S + 1) ≤ concreteScale S := by
  have h1 := concreteLevelMax_le S S.pal hj
  have h2 := concreteLevelMax_le S (fun j => (levelFml S j).length) hj
  have h3 := concreteLevelMax_le S (fun j => concreteAtomBound (levelAtoms S j)) hj
  have h4 := concreteLevelMax_le S (fun j => 2 ^ S.pal j * (concreteQdepth S + 1)) hj
  dsimp only at h2 h3 h4
  unfold concreteScale
  omega

theorem concreteScale_top (S : Setup L) :
    concreteAtomBound (concreteTopAtoms S) ≤ concreteScale S := by
  unfold concreteScale
  omega

/-- The common capacity for non-exact scratch regions. -/
noncomputable def concreteCapacity (S : Setup L) (n : ℕ) : ℕ :=
  concreteScale S * (n + 2) ^ 2

/-- The word coefficient is fixed entirely from the schedule. -/
noncomputable def concreteWordQ (S : Setup L) : ℕ := concreteScale S + 1

theorem concreteCapacity_lt_mcB (S : Setup L) {n : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} (henc : EncodesGraph x n G) :
    concreteCapacity S n < mcB (concreteWordQ S) x := by
  have hn := henc.length_eq
  have hle : n + 2 ≤ x.length + 1 := by omega
  calc concreteCapacity S n
      ≤ concreteScale S * (x.length + 1) ^ 2 := by
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle 2)
    _ < (concreteScale S + 1) * (x.length + 1) ^ 2 :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (by positivity)
    _ = mcB (concreteWordQ S) x := rfl

theorem concreteCapacity_bounds (S : Setup L) (n : ℕ) :
    n ≤ concreteCapacity S n ∧ n + 2 ≤ concreteCapacity S n ∧
    n * n + 2 * n + 1 ≤ concreteCapacity S n ∧
    concreteScale S ≤ concreteCapacity S n ∧
    ∀ c, c ≤ concreteScale S → n * c ≤ concreteCapacity S n := by
  have hp : 1 ≤ concreteScale S := concreteScale_pos S
  have hn1 : 1 ≤ (n + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hn2 : n + 2 ≤ (n + 2) ^ 2 := by nlinarith
  have hn3 : n * n + 2 * n + 1 ≤ (n + 2) ^ 2 := by nlinarith
  have hc : (n + 2) ^ 2 ≤ concreteCapacity S n := Nat.le_mul_of_pos_left _ hp
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · exact Nat.le_mul_of_pos_right _ hn1
  · intro c hc'
    exact le_trans (Nat.mul_le_mul (show n ≤ (n + 2) ^ 2 by omega) hc')
      (by rw [concreteCapacity, Nat.mul_comm])

end Lax3Proofs.Prog
