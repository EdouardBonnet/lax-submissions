import Lax3Proofs.SolveConcreteBoundary

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
open Lax3.ScatterSentences
variable {L : ℕ}

private theorem concrete_noWrite_fold (cs : List Com)
    (h : ∀ c ∈ cs, c.NoWrite) : (cs.foldr Com.seq Com.skip).NoWrite := by
  induction cs with
  | nil => trivial
  | cons c cs ih => exact ⟨h c (by simp), ih (fun d hd => h d (by simp [hd]))⟩

private theorem concrete_noWrite_col (S : Setup L) (j : ℕ) : (prepColCom S j).NoWrite := by
  change True ∧ ((_ : List Com).foldr Com.seq Com.skip).NoWrite ∧ True
  refine ⟨trivial, concrete_noWrite_fold _ ?_, trivial⟩
  change ∀ c ∈ (_ : List Com) ++ _ ++ _ ++ _, c.NoWrite
  intro c hc
  simp only [List.mem_append, List.mem_map, List.mem_singleton, or_assoc] at hc
  rcases hc with ⟨a, _, rfl⟩ | rfl | ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩
  · trivial
  · trivial
  · exact ⟨trivial, trivial⟩
  · exact ⟨trivial, trivial⟩

theorem concretePrep_noWrite (S : Setup L) (j : ℕ) : (concretePrep S j).NoWrite := by
  change (prepRowBoundsCom (concreteCo j) (ctrName j)).NoWrite ∧ True ∧
    (prepRowCom (concreteCm j)).NoWrite ∧ (prepCentreCom (ctrName j)).NoWrite ∧
    (prepBatchCom (arenaNames j).hist (ctrName j) (concreteLp S j) (concreteHb S j)).NoWrite ∧
    (prepWidthCom S.width).NoWrite ∧ (prepClearCom (concreteCm j)).NoWrite ∧
    (prepRestrictCom (arenaNames j) j (S.pal j) (concreteLp S j) (concreteHb S j)).NoWrite ∧
    (prepBfsCom (2 * S.R)).NoWrite ∧
    (prepSupportsCom j (2 * S.R) (concreteLp S j) (concreteHb S j)).NoWrite ∧
    (profilesCom (prepPN j) S.width (S.pal j) S.R).NoWrite ∧
    (prepColCom S j).NoWrite ∧ (prepIsolateCom j).NoWrite
  simp [prepRowBoundsCom, prepRowCom, prepCentreCom, prepBatchCom, prepWidthCom,
    prepClearCom, prepRestrictCom, prepBfsCom, prepSupportsCom, prepIsolateCom,
    Com.NoWrite, noWrite_restrictCom, noWrite_bfsCom, noWrite_supportsCom,
    noWrite_profilesCom, concrete_noWrite_col, noWrite_isolateCom]

private theorem concrete_noWrite_topAtoms (nm : ArenaNames) (pa ma da tsb : String)
    (F : ℕ) (bIdx : ScatterSentence L → ℕ) (l : List (ScatterSentence L)) (i : ℕ) :
    (topAtomsCom nm pa ma da tsb F bIdx l i).NoWrite := by
  induction l generalizing i with
  | nil => trivial
  | cons a l ih =>
    simp [topAtomsCom, topAtomCom, topGlueCom, topColCom, Lax67Proofs.Reasoning.Lib.Fill.put, topBitCom,
      Com.NoWrite, noWrite_scatterCom, ih]

private theorem concrete_noWrite_rows (tb ct tsb : String) (S : Setup L) (j : ℕ)
    (l : List (Fml S j)) (i : ℕ) : (rowStores tb ct tsb S j l i).NoWrite := by
  induction l generalizing i with
  | nil => trivial
  | cons a l ih => exact ⟨trivial, ih _⟩

theorem concreteRead_noWrite (S : Setup L) (j : ℕ) : (concreteRead S j).NoWrite := by
  simp [concreteRead, readSegCom, rowBody, Com.NoWrite, concrete_noWrite_topAtoms,
    concrete_noWrite_rows]

theorem concreteTop_noWrite (S : Setup 0) : (concreteTop S).NoWrite :=
  concrete_noWrite_topAtoms ..

end Lax3Proofs.Prog
