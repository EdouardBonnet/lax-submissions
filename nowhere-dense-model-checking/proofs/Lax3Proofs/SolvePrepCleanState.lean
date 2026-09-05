import Lax3Proofs.SolveMachPrep
import Lax3Proofs.SolveRunWords

/-!
# The rank scratch invariant

The descriptor `Scr` continues to describe allocation lengths. The rank
array's contents are a separate invariant: its root prefix is zero at every
child-call boundary, including the return from the recursive block.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs
open Lax3Proofs.Driver

/-- The shared parent-name rank array is clean on the root carrier. -/
def RankClean (N : ℕ) (σ : Env) : Prop :=
  ∀ i, i < N → (σ.arrs "cp.r").getD i 0 = 0

/-- A content invariant transported by actual array agreement. -/
theorem RankClean.of_arr_eq {N : ℕ} {σ σ' : Env} (h : RankClean N σ)
    (ha : σ'.arrs "cp.r" = σ.arrs "cp.r") : RankClean N σ' := by
  intro i hi
  rw [ha]
  exact h i hi

@[simp] theorem rankClean_setVar {N : ℕ} {σ : Env} {y : String} {v : ℕ} :
    RankClean N (σ.setVar y v) ↔ RankClean N σ := Iff.rfl

/-- The reusable scratch contents: clean ranks and bounded stored words. -/
def PrepClean (N B : ℕ) (σ : Env) : Prop :=
  RankClean N σ ∧ ArrWords B σ

@[simp] theorem prepClean_setVar {N B : ℕ} {σ : Env} {y : String} {v : ℕ} :
    PrepClean N B (σ.setVar y v) ↔ PrepClean N B σ := Iff.rfl

/-- The usual machine contract with rank cleanliness at both boundaries. -/
def CleanSpec (N B : ℕ) (P : Env → Prop) (c : Com)
    (Q : Env → Env → Prop) (K : ℕ) : Prop :=
  Spec B (fun σ => P σ ∧ PrepClean N B σ) c
    (fun σ σ' => Q σ σ' ∧ PrepClean N B σ') K

/-- A program that avoids the rank array preserves its contents. -/
theorem CleanSpec.of_spec {N B K : ℕ} {P : Env → Prop} {c : Com}
    {Q : Env → Env → Prop} (h : Spec B P c Q K) (ha : "cp.r" ∉ c.warrs) :
    CleanSpec N B P c Q K := by
  intro σ hσ
  obtain ⟨σ', hr, hQ⟩ := h σ hσ.1
  exact ⟨σ', hr, hQ, hσ.2.1.of_arr_eq (hr.frame_arr _ ha),
    Run.arrWords hr hσ.2.2⟩

/-- Composition uses the returned content invariant, independently of `Scr`. -/
theorem CleanSpec.seq {N B K₁ K₂ : ℕ} {P R : Env → Prop} {c d : Com}
    {Q T U : Env → Env → Prop}
    (h : CleanSpec N B P c Q K₁) (h' : CleanSpec N B R d T K₂)
    (hpre : ∀ σ σ', P σ → Q σ σ' → R σ')
    (hpost : ∀ σ σ' σ'', P σ → Q σ σ' → T σ' σ'' → U σ σ'') :
    CleanSpec N B P (.seq c d) U (K₁ + K₂) := by
  exact Spec.seq h h'
    (fun σ σ' hp hq => ⟨hpre σ σ' hp.1 hq.1, hq.2⟩)
    (fun σ σ' σ'' hp hq ht => ⟨hpost σ σ' σ'' hp.1 hq.1 ht.1, ht.2⟩)

variable {L n₀ : ℕ}

/-- `ChildLoadParts` with a realizable, separate rank-content invariant. -/
def ChildLoadPartsClean (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (chanF : (j : ℕ) → (A : Arena (S.pal j) n₀) → (u : Fin A.N) →
      Fin (childN S A ((ord A.N A.G).order) u) → Fin (ℓp (j + 1)) →
      List (Fin (childN S A ((ord A.N A.G).order) u)))
    (KP : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ) : Prop :=
  ∀ (k j : ℕ) (A : Arena (S.pal j) n₀), j + (k + 1) = S.depth →
    Adm j A → ¬ A.G = ⊥ → ∀ u : Fin A.N,
    CleanSpec n₀ B
      (fun σ => CLInv S ord ℓp htabF hbf Scr ca co cm k j A (u : ℕ) σ ∧
        σ.vars (ctrName j) = (u : ℕ))
      (prepC j)
      (fun σ σ' =>
        (∃ (Dp : Fin S.width → Fin (childN S A ((ord A.N A.G).order) u) → ℕ)
           (Dc : Fin (relPal (S.pal j)) →
              Fin (childN S A ((ord A.N A.G).order) u + 1) → ℕ),
          Impl.ProfileTablesMS (preG S A ((ord A.N A.G).order) u)
            (batchFn S A ((ord A.N A.G).order) u)
            (childColR S A ((ord A.N A.G).order) u) S.R Dp Dc ∧
          ArenaStW (arenaNames (j + 1)) (hbf (j + 1))
            (machChild S A ((ord A.N A.G).order) u Dp Dc (chanF j A u)) σ') ∧
        (∀ y ∈ ctrName j :: levelScalars j, σ'.vars y = σ.vars y) ∧
        (∀ a ∈ ca j :: co j :: cm j :: levelArrays j, σ'.arrs a = σ.arrs a) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (KP k j A (u : ℕ))


/-- Compatibility of the initialisation pass with the reusable clean pass. -/
def PrepBoundarySpec (reset : Bool) (N B : ℕ) (P : Env → Prop) (c : Com)
    (Q : Env → Env → Prop) (K : ℕ) : Prop :=
  Spec B (fun σ => P σ ∧ (reset = false → RankClean N σ)) c
    (fun σ σ' => Q σ σ' ∧ (RankClean N σ → RankClean N σ')) K

def ChildLoadPartsMode (reset : Bool) (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (chanF : (j : ℕ) → (A : Arena (S.pal j) n₀) → (u : Fin A.N) →
      Fin (childN S A ((ord A.N A.G).order) u) → Fin (ℓp (j + 1)) →
      List (Fin (childN S A ((ord A.N A.G).order) u)))
    (KP : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ) : Prop :=
  ∀ (k j : ℕ) (A : Arena (S.pal j) n₀), j + (k + 1) = S.depth →
    Adm j A → ¬ A.G = ⊥ → ∀ u : Fin A.N,
    PrepBoundarySpec reset n₀ B
      (fun σ => CLInv S ord ℓp htabF hbf Scr ca co cm k j A (u : ℕ) σ ∧
        σ.vars (ctrName j) = (u : ℕ))
      (prepC j)
      (fun σ σ' =>
        (∃ (Dp : Fin S.width → Fin (childN S A ((ord A.N A.G).order) u) → ℕ)
           (Dc : Fin (relPal (S.pal j)) →
              Fin (childN S A ((ord A.N A.G).order) u + 1) → ℕ),
          Impl.ProfileTablesMS (preG S A ((ord A.N A.G).order) u)
            (batchFn S A ((ord A.N A.G).order) u)
            (childColR S A ((ord A.N A.G).order) u) S.R Dp Dc ∧
          ArenaStW (arenaNames (j + 1)) (hbf (j + 1))
            (machChild S A ((ord A.N A.G).order) u Dp Dc (chanF j A u)) σ') ∧
        (∀ y ∈ ctrName j :: levelScalars j, σ'.vars y = σ.vars y) ∧
        (∀ a ∈ ca j :: co j :: cm j :: levelArrays j, σ'.arrs a = σ.arrs a) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (KP k j A (u : ℕ))




def BlockSpecClean (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (nmF : ℕ → ArenaNames)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (k j : ℕ) (com : Com) : Prop :=
  ∀ A : Arena (S.pal j) n₀, j + k = S.depth → Adm j A → (k = 0 → A.G = ⊥) →
    CleanSpec n₀ B (BlockPre S j (hbf j) A (htabF j A) (Scr j) (nmF j)) com
      (fun _ σ' => BlockPost S ord k j (hbf j) A (htabF j A) (nmF j) σ')
      (KB k j A)

def FrameStepClean (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (nmF : ℕ → ArenaNames)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (frameBody : ℕ → Com → Com) : Prop :=
  ∀ (k j : ℕ) (nxCom : Com),
    BlockSpecClean B S ord ℓp htabF hbf nmF Adm KB Scr k (j + 1) nxCom →
    OwnedFrom LS LA (j + 1) nxCom →
    BlockSpecClean B S ord ℓp htabF hbf nmF Adm KB Scr (k + 1) j
        (frameBody j nxCom) ∧
      OwnedFrom LS LA j (frameBody j nxCom)

def CentrePrepClean (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (KP : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ) : Prop :=
  ∀ (k j : ℕ) (A : Arena (S.pal j) n₀), j + (k + 1) = S.depth →
    Adm j A → ¬ A.G = ⊥ → ∀ u : Fin A.N,
    CleanSpec n₀ B
      (fun σ => CLInv S ord ℓp htabF hbf Scr ca co cm k j A (u : ℕ) σ ∧
        σ.vars (ctrName j) = (u : ℕ))
      (prepC j)
      (fun σ σ' => CLInv S ord ℓp htabF hbf Scr ca co cm k j A (u : ℕ) σ' ∧
        σ'.vars (ctrName j) = σ.vars (ctrName j) ∧
        BlockPre S (j + 1) (hbf (j + 1))
          (childArena S A ((ord A.N A.G).order) u)
          (htabF (j + 1) (childArena S A ((ord A.N A.G).order) u))
          (Scr (j + 1)) (arenaNames (j + 1)) σ')
      (KP k j A (u : ℕ))

def CentreStepClean (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (ca co cm : ℕ → String)
    (bodyB : ℕ → Com → Com)
    (KC : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ) : Prop :=
  ∀ (k j : ℕ) (nxCom : Com),
    BlockSpecClean B S ord ℓp htabF hbf arenaNames Adm KB Scr k (j + 1) nxCom →
    OwnedFrom LS LA (j + 1) nxCom →
    (∀ A : Arena (S.pal j) n₀, j + (k + 1) = S.depth → Adm j A →
      ¬ A.G = ⊥ → ∀ u : Fin A.N,
      CleanSpec n₀ B
        (fun σ => CLInv S ord ℓp htabF hbf Scr ca co cm k j A (u : ℕ) σ ∧
          σ.vars (ctrName j) = (u : ℕ))
        (bodyB j nxCom)
        (fun σ σ' =>
          CLInv S ord ℓp htabF hbf Scr ca co cm k j A ((u : ℕ) + 1) σ' ∧
          σ'.vars (ctrName j) = σ.vars (ctrName j))
        (KC k j A (u : ℕ))) ∧
    OwnedFrom LS LA j (bodyB j nxCom)

def CentreLoopClean (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (ca co cm : ℕ → String)
    (loopB : ℕ → Com → Com)
    (KL : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) : Prop :=
  ∀ (k j : ℕ) (nxCom : Com),
    BlockSpecClean B S ord ℓp htabF hbf arenaNames Adm KB Scr k (j + 1) nxCom →
    OwnedFrom LS LA (j + 1) nxCom →
    (∀ A : Arena (S.pal j) n₀, j + (k + 1) = S.depth → Adm j A →
      ¬ A.G = ⊥ →
      CleanSpec n₀ B
        (fun σ =>
          BlockPre S j (hbf j) A (htabF j A) (Scr j) (arenaNames j) σ ∧
          CtrArr (ca j) (centre S A ((ord A.N A.G).order)) σ ∧
          ClusterCsr (co j) (cm j) (cluster S A ((ord A.N A.G).order)) σ)
        (loopB j nxCom)
        (fun _ σ' => BlockPost S ord (k + 1) j (hbf j) A (htabF j A)
          (arenaNames j) σ')
        (KL k j A)) ∧
    OwnedFrom LS LA j (loopB j nxCom)

def FrameElseClean (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (elseB : ℕ → Com → Com)
    (KE : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) : Prop :=
  ∀ (k j : ℕ) (nxCom : Com),
    BlockSpecClean B S ord ℓp htabF hbf arenaNames Adm KB Scr k (j + 1) nxCom →
    OwnedFrom LS LA (j + 1) nxCom →
    (∀ A : Arena (S.pal j) n₀, j + (k + 1) = S.depth → Adm j A →
      ¬ A.G = ⊥ →
      CleanSpec n₀ B (BlockPre S j (hbf j) A (htabF j A) (Scr j) (arenaNames j))
        (elseB j nxCom)
        (fun _ σ' => BlockPost S ord (k + 1) j (hbf j) A (htabF j A)
          (arenaNames j) σ')
        (KE k j A)) ∧
    OwnedFrom LS LA j (elseB j nxCom)


def CoverStageSpecClean (B : ℕ) {L Λ n₀ ℓp : ℕ} (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (hb : ℕ) (nm : ArenaNames)
    (A : Arena Λ n₀) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (ca co cm : String) (Scv : Env → Prop) (coverCom : Com) (Kcov : ℕ) : Prop :=
  CleanSpec n₀ B
    (fun σ => ArenaStW nm hb (Impl.ofArena A htab) σ ∧
      A.N ≤ (σ.arrs ca).length ∧ A.N + 1 ≤ (σ.arrs co).length ∧ Scv σ)
    coverCom
    (fun _ σ' => ArenaStW nm hb (Impl.ofArena A htab) σ' ∧
      CtrArr ca (centre S A ((ord A.N A.G).order)) σ' ∧
      ClusterCsr co cm (cluster S A ((ord A.N A.G).order)) σ')
    Kcov

def CoverAllClean (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (ca co cm : ℕ → String) (Scv : ℕ → Env → Prop) (covC : ℕ → Com)
    (Kcov : (j : ℕ) → Arena (S.pal j) n₀ → ℕ) : Prop :=
  ∀ j, j < S.depth → ∀ A : Arena (S.pal j) n₀, Adm j A → ¬ A.G = ⊥ →
    CoverStageSpecClean B S ord (hbf j) (arenaNames j) A (htabF j A)
      (ca j) (co j) (cm j) (Scv j) (covC j) (Kcov j A)
end Lax3Proofs.Prog
