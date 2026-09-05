import Lax3Proofs.SolvePrepCleanState

/-! The rank contents cross the recursive call and the readback separately from
allocation lengths. The return path uses the child's returned cleanliness. -/

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
variable {L n₀ : ℕ}

theorem centrePrepClean_of_parts (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (chanF : (j : ℕ) → (A : Arena (S.pal j) n₀) → (u : Fin A.N) →
      Fin (childN S A ((ord A.N A.G).order) u) → Fin (ℓp (j + 1)) →
      List (Fin (childN S A ((ord A.N A.G).order) u)))
    (hhtab : ∀ j, j + 1 ≤ S.depth → ∀ A : Arena (S.pal j) n₀,
      Adm j A → ∀ u : Fin A.N,
      htabF (j + 1) (childArena S A ((ord A.N A.G).order) u) = chanF j A u)
    (KP : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ)
    -- the length-only scratch transport (the descriptors always are)
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    -- the descriptor tower: level `j`'s descriptor carries the deeper
    -- level's, wherever the chain still descends
    (hscrDown : ∀ j, j + 1 ≤ S.depth → ∀ σ, Scr j σ → Scr (j + 1) σ)
    -- the level-`(j+1)` table allocation, at the root carrier (the
    -- static layout's; length-only)
    (htabLen : ∀ j, j + 1 ≤ S.depth → ∀ σ, Scr j σ →
      n₀ * (levelFml S (j + 1)).length
        ≤ (σ.arrs (arenaNames (j + 1)).tab).length)
    (hload : ChildLoadPartsClean B S ord ℓp htabF hbf Adm Scr ca co cm prepC chanF KP) :
    CentrePrepClean B S ord ℓp htabF hbf Adm Scr ca co cm prepC KP := by
  intro k j A hdiag hAdm hbot u
  refine (hload k j A hdiag hAdm hbot u).post ?_
  rintro σ σ' ⟨⟨hCL, -⟩, _⟩ ⟨⟨⟨Dp, Dc, hPT, hAW⟩, hvars, harrs, hlen⟩, hclean⟩
  have hchild : ArenaStW (arenaNames (j + 1)) (hbf (j + 1))
      (Impl.ofArena (childArena S A ((ord A.N A.G).order) u)
        (htabF (j + 1) (childArena S A ((ord A.N A.G).order) u))) σ' := by
    rw [hhtab j (by omega) A hAdm u,
      ← machChild_eq_ofArena S A ((ord A.N A.G).order) u (chanF j A u) hPT]
    exact hAW
  have hScrj : Scr j σ := hCL.1.2.2
  refine ⟨⟨clInv_frame (hscrLen j) hCL
      (hvars _ (by simp [levelScalars])) (hvars _ (by simp [levelScalars]))
      harrs hlen,
    hvars _ (by simp), hchild, ?_, ?_⟩, hclean⟩
  · -- the child's table allocation: below the root carrier, off the
    -- level-`j` descriptor, lengths preserved
    calc (childArena S A ((ord A.N A.G).order) u).N
          * (levelFml S (j + 1)).length
        ≤ n₀ * (levelFml S (j + 1)).length :=
          Nat.mul_le_mul_right _ (arenaN_le _)
      _ ≤ (σ.arrs (arenaNames (j + 1)).tab).length :=
          htabLen j (by omega) σ hScrj
      _ = (σ'.arrs (arenaNames (j + 1)).tab).length := (hlen _).symm
  · -- the child's scratch descriptor: the tower's, transported
    exact hscrLen (j + 1) σ σ' (hscrDown j (by omega) σ hScrj) hlen


open Classical in
theorem centreStepClean_of_prep_read (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (ca co cm : ℕ → String)
    (prepC readC : ℕ → Com)
    (KP KR : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ)
    -- the length-only scratch transport
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    -- the level's own names are fresh against the deeper pools
    (hfreshS : ∀ j i, j < i → ∀ y ∈ ctrName j :: levelScalars j, y ∉ LS i)
    (hfreshA : ∀ j i, j < i →
      ∀ a ∈ ca j :: co j :: cm j :: levelArrays j, a ∉ LA i)
    -- the run tree's two facts at the child, through `Adm`
    (hAdmChild : ∀ (j : ℕ) (A : Arena (S.pal j) n₀), Adm j A →
      ¬ A.G = ⊥ → ∀ u : Fin A.N,
      Adm (j + 1) (childArena S A ((ord A.N A.G).order) u))
    (hleafChild : ∀ (j : ℕ) (A : Arena (S.pal j) n₀), Adm j A →
      ¬ A.G = ⊥ → j + 1 = S.depth → ∀ u : Fin A.N,
      (childArena S A ((ord A.N A.G).order) u).G = ⊥)
    -- the two segments obey the write discipline (their dischargers')
    (hprepOwn : ∀ j, OwnedFrom LS LA j (prepC j))
    (hreadOwn : ∀ j, OwnedFrom LS LA j (readC j))
    (hreadRank : ∀ j, "cp.r" ∉ (readC j).warrs)
    -- the two residuals
    (hprep : CentrePrepClean B S ord ℓp htabF hbf Adm Scr ca co cm prepC KP)
    (hread : CentreRead B S ord ℓp htabF hbf Adm Scr ca co cm readC KR) :
    CentreStepClean B S ord ℓp htabF hbf Adm KB Scr LS LA ca co cm
      (centreBody prepC readC) (centreKC S ord KB KP KR) := by
  intro k j nxCom hnx hnxOwn
  constructor
  · intro A hdiag hAdm hbot u σ ⟨⟨hCL, hctr⟩, hclean⟩
    have hvarF : ∀ y ∈ ctrName j :: levelScalars j, y ∉ nxCom.wvars := by
      intro y hy hmem
      obtain ⟨i, hi, hyi⟩ := hnxOwn.1 y hmem
      exact hfreshS j i (by omega) y hy hyi
    have harrF : ∀ a ∈ ca j :: co j :: cm j :: levelArrays j,
        a ∉ nxCom.warrs := by
      intro a ha hmem
      obtain ⟨i, hi, hai⟩ := hnxOwn.2 a hmem
      exact hfreshA j i (by omega) a ha hai
    obtain ⟨σp, hrp, ⟨hCLp, hctrp, hBPp⟩, hcleanp⟩ :=
      hprep k j A hdiag hAdm hbot u σ ⟨⟨hCL, hctr⟩, hclean⟩
    obtain ⟨σn, hrn, hBPn, hcleann⟩ :=
      hnx (childArena S A ((ord A.N A.G).order) u) (by omega)
        (hAdmChild j A hAdm hbot u)
        (fun hk0 => hleafChild j A hAdm hbot (by omega) u) σp ⟨hBPp, hcleanp⟩
    have hCLn := clInv_frame (hscrLen j) hCLp
      (hrn.frame_var _ (hvarF _ (by simp [levelScalars])))
      (hrn.frame_var _ (hvarF _ (by simp [levelScalars])))
      (fun a ha => hrn.frame_arr a (harrF a ha))
      (fun b => run_arrs_length_eq hrn b)
    have hctrn : σn.vars (ctrName j) = σp.vars (ctrName j) :=
      hrn.frame_var _ (hvarF _ (by simp))
    obtain ⟨σr, hrr, ⟨hCLr, hctrr⟩, hcleanr⟩ :=
      CleanSpec.of_spec (hread k j A hdiag hAdm hbot u) (hreadRank j) σn
        ⟨⟨hCLn, by rw [hctrn, hctrp, hctr], hBPn⟩, hcleann⟩
    refine ⟨σr, (hrp.seq (hrn.seq hrr)).mono ?_,
      ⟨hCLr, by rw [hctrr, hctrn, hctrp]⟩, hcleanr⟩
    simp [centreKC, u.isLt]
  · exact OwnedFrom.seq (hprepOwn j)
      (OwnedFrom.seq (OwnedFrom.mono_level (Nat.le_succ j) hnxOwn) (hreadOwn j))

end Lax3Proofs.Prog
