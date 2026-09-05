import Lax3Proofs.SolvePrepCleanLoop

/-! The preserved content reaches the cover call, both branches of the graph
guard, and every recursive block. -/

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
variable {L n₀ : ℕ}

open Classical in
theorem frameElseClean_of_cover_loop (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (ca co cm : ℕ → String)
    (Scv : ℕ → Env → Prop) (covC : ℕ → Com) (loopB : ℕ → Com → Com)
    (Kcov : (j : ℕ) → Arena (S.pal j) n₀ → ℕ)
    (KL : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ)
    -- the level's scratch descriptor carries the cover's needs …
    (hscrCov : ∀ j σ, Scr j σ →
      n₀ ≤ (σ.arrs (ca j)).length ∧ n₀ + 1 ≤ (σ.arrs (co j)).length ∧
      Scv j σ)
    -- … and is length-only, so it survives any run that keeps lengths
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    -- the cover obeys the write discipline (its discharger's, syntactic)
    (hcovOwn : ∀ j, OwnedFrom LS LA j (covC j))
    -- the two residuals
    (hcov : CoverAllClean B S ord ℓp htabF hbf Adm ca co cm Scv covC Kcov)
    (hloop : CentreLoopClean B S ord ℓp htabF hbf Adm KB Scr LS LA ca co cm
      loopB KL) :
    FrameElseClean B S ord ℓp htabF hbf Adm KB Scr LS LA (coverElse covC loopB)
      (fun k j A => Kcov j A + KL k j A) := by
  intro k j nxCom hnx hown
  obtain ⟨hloopSpec, hloopOwn⟩ := hloop k j nxCom hnx hown
  refine ⟨?_, OwnedFrom.seq (hcovOwn j) hloopOwn⟩
  intro A hdiag hAdm hbot
  have hj : j < S.depth := by omega
  have hcv := specArrsLength (hcov j hj A hAdm hbot)
  refine Spec.seq (hcv.pre ?_) (hloopSpec A hdiag hAdm hbot) ?_
    (fun _ _ _ _ _ h => h)
  · -- the block precondition lands in the cover's
    rintro σ ⟨⟨hA, htab, hscrσ⟩, hclean⟩
    obtain ⟨h1, h2, h3⟩ := hscrCov j σ hscrσ
    have hle : A.N ≤ n₀ := arenaN_le A
    exact ⟨⟨hA, le_trans hle h1, le_trans (by omega) h2, h3⟩, hclean⟩
  · -- the cover's postcondition lands in the loop's precondition
    rintro σ σ' ⟨⟨hA, htab, hscrσ⟩, _⟩ ⟨⟨⟨hA', hctr, hcsr⟩, hclean⟩, hlen⟩
    refine ⟨⟨⟨hA', ?_, hscrLen j σ σ' hscrσ hlen⟩, hctr, hcsr⟩, hclean⟩
    rw [hlen ((arenaNames j).tab)]
    exact htab


/-- The canonical bottom block does not access the shared rank array. -/
theorem prepClean_canonBot_rank (S : Setup L) (Kq j : ℕ) :
    "cp.r" ∉ (canonBotB S Kq j).warrs := by
  intro h
  have hm := warrs_botCom (arenaNames j).col (botNa j) (botFa j) (botEa j)
    (botXa j) (arenaNames j).tab (arenaNames j).nN (S.pal j) Kq (levelFml S j) h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h <;>
    exact (lv_ne_of_base_ne (by decide) (by decide) j 0) h.symm

open Classical in
theorem frameStepClean_of_else (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (elseB : ℕ → Com → Com)
    (KE : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Kq : ℕ)
    -- the schedule-rank bound at every non-bottom level
    (hKq : ∀ j, j < S.depth → ∀ β ∈ levelFml S j, qdepth β ≤ Kq)
    -- the word bounds: the carrier once, the level figures per level
    (hn0B : n₀ < B) (hn0B2 : n₀ * n₀ < B)
    (hNLB : ∀ j, j < S.depth → n₀ * S.pal j < B)
    (h2LB : ∀ j, j < S.depth → 2 ^ S.pal j * (Kq + 1) < B)
    (hTB : ∀ j, j < S.depth → n₀ * (levelFml S j).length < B)
    -- the per-level scratch descriptor, at the leaf's four regions
    (hscr : ∀ j, j < S.depth → ∀ σ, Scr j σ →
      (σ.arrs (botNa j)).length = 2 ^ S.pal j ∧
      (σ.arrs (botFa j)).length = 2 ^ S.pal j * (Kq + 1) ∧
      (σ.arrs (botEa j)).length = Kq + 1 ∧
      (σ.arrs (botXa j)).length = Kq + 1)
    -- the budget fit: the guard plus the larger branch
    (hKB : ∀ k j, j < S.depth → ∀ A : Arena (S.pal j) n₀,
      4 + max (botComK A.N (S.pal j) Kq (levelFml S j)) (KE k j A)
        ≤ KB (k + 1) j A)
    -- the name pools carry the leaf's names
    (hLS : ∀ j, ∀ y ∈ btScalars, y ∈ LS j)
    (hLA : ∀ j, ∀ a ∈ ([botNa j, botFa j, botEa j, botXa j,
      (arenaNames j).tab] : List String), a ∈ LA j)
    -- the residual
    (helse : FrameElseClean B S ord ℓp htabF hbf Adm KB Scr LS LA elseB KE) :
    FrameStepClean B S ord ℓp htabF hbf arenaNames Adm KB Scr LS LA
      (guardBody S Kq elseB) := by
  intro k j nxCom hnx hown
  obtain ⟨helseSpec, helseOwn⟩ := helse k j nxCom hnx hown
  have hbotOwn : OwnedFrom LS LA j (canonBotB S Kq j) :=
    botBlock_owned LS LA arenaNames j Kq S (hLS j) (hLA j)
  refine ⟨?_, OwnedFrom.ite hbotOwn helseOwn⟩
  intro A hdiag hAdm _
  have hj : j < S.depth := by omega
  have hle : A.N ≤ n₀ := arenaN_le A
  have hnsB : ∀ σ, BlockPre S j (hbf j) A (htabF j A) (Scr j) (arenaNames j) σ →
      σ.vars (arenaNames j).nS < B := by
    intro σ hσ
    have h1 : σ.vars (arenaNames j).nS ≤ A.N * A.N := hσ.1.ns_le_sq
    have h2 := Nat.mul_le_mul hle hle
    omega
  refine (Spec.ite
    (K := max (botComK A.N (S.pal j) Kq (levelFml S j)) (KE k j A))
    ?_ ?_ ?_).mono ?_
  · intro σ hσ
    obtain ⟨v, hv, -⟩ := evalB_condEq_isSome (evalB_var (hnsB σ hσ.1))
      (evalB_lit (show 0 < B by omega))
    exact ⟨v, hv⟩
  · rintro σ ⟨⟨hP, hclean⟩, htrue⟩
    have hns0 : σ.vars (arenaNames j).nS = 0 := by
      rw [evalB_condEq_iff] at htrue
      obtain ⟨m, n', hm, hn', heq⟩ := htrue
      rw [evalB_var_iff] at hm
      rw [evalB_lit_iff] at hn'
      obtain ⟨rfl, -⟩ := hm
      obtain ⟨rfl, -⟩ := hn'
      simpa using heq.symm
    have hbot : A.G = ⊥ := hP.1.ns_zero_iff_bot.mp hns0
    have hb := botBlock_core B S ord ℓp htabF hbf arenaNames Scr j Kq
      (hKq j hj) hn0B (hNLB j hj) (h2LB j hj) (hTB j hj)
      (canon_nd j) (canon_off j) (canon_tgt j) (canon_up j) (canon_hist j)
      (canon_nN j) (canon_nS j) (canon_nd5 j) (hscr j hj) (k + 1) A hbot
    exact ((CleanSpec.of_spec hb (prepClean_canonBot_rank S Kq j)).mono
      (le_max_left _ _)) σ ⟨hP, hclean⟩
  · rintro σ ⟨⟨hP, hclean⟩, hfalse⟩
    have hns0 : σ.vars (arenaNames j).nS ≠ 0 := by
      rw [evalB_condEq_iff] at hfalse
      obtain ⟨m, n', hm, hn', heq⟩ := hfalse
      rw [evalB_var_iff] at hm
      rw [evalB_lit_iff] at hn'
      obtain ⟨rfl, -⟩ := hm
      obtain ⟨rfl, -⟩ := hn'
      simpa using heq.symm
    have hbot : ¬ A.G = ⊥ := fun h => hns0 (hP.1.ns_zero_iff_bot.mpr h)
    exact ((helseSpec A hdiag hAdm hbot).mono (le_max_right _ _)) σ ⟨hP, hclean⟩
  · have := hKB k j hj A
    simp only [size_condEq, size_var, size_lit]
    omega

theorem chainCom_blockSpecClean (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (nmF : ℕ → ArenaNames)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (frameBody : ℕ → Com → Com) (botB : ℕ → Com)
    (hbot : ∀ j, BlockSpecClean B S ord ℓp htabF hbf nmF Adm KB Scr 0 j (botB j) ∧
      OwnedFrom LS LA j (botB j))
    (hstep : FrameStepClean B S ord ℓp htabF hbf nmF Adm KB Scr LS LA frameBody) :
    ∀ k j, BlockSpecClean B S ord ℓp htabF hbf nmF Adm KB Scr k j
        (chainCom frameBody botB k j) ∧
      OwnedFrom LS LA j (chainCom frameBody botB k j) := by
  intro k
  induction k with
  | zero => exact hbot
  | succ k ih =>
    intro j
    obtain ⟨h1, h2⟩ := ih (j + 1)
    exact hstep k j _ h1 h2


/-- The complete recursive frame from the actual parts, the cover, and readback.
All recursive calls use and return the preserved content bundle. -/
theorem frameStepClean_of_cover_parts_read (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (ca co cm : ℕ → String)
    (Scv : ℕ → Env → Prop) (covC prepC readC : ℕ → Com)
    (chanF : (j : ℕ) → (A : Arena (S.pal j) n₀) → (u : Fin A.N) →
      Fin (childN S A ((ord A.N A.G).order) u) → Fin (ℓp (j + 1)) →
      List (Fin (childN S A ((ord A.N A.G).order) u)))
    (Kcov : (j : ℕ) → Arena (S.pal j) n₀ → ℕ)
    (KP KR : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ) (Kq : ℕ)
    (hn0B : n₀ < B) (hn0B2 : n₀ * n₀ < B)
    (hKq : ∀ j, j < S.depth → ∀ β ∈ levelFml S j, qdepth β ≤ Kq)
    (hNLB : ∀ j, j < S.depth → n₀ * S.pal j < B)
    (h2LB : ∀ j, j < S.depth → 2 ^ S.pal j * (Kq + 1) < B)
    (hTB : ∀ j, j < S.depth → n₀ * (levelFml S j).length < B)
    (hscrBot : ∀ j, j < S.depth → ∀ σ, Scr j σ →
      (σ.arrs (botNa j)).length = 2 ^ S.pal j ∧
      (σ.arrs (botFa j)).length = 2 ^ S.pal j * (Kq + 1) ∧
      (σ.arrs (botEa j)).length = Kq + 1 ∧
      (σ.arrs (botXa j)).length = Kq + 1)
    (hscrCov : ∀ j σ, Scr j σ →
      n₀ ≤ (σ.arrs (ca j)).length ∧ n₀ + 1 ≤ (σ.arrs (co j)).length ∧ Scv j σ)
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (hscrDown : ∀ j, j + 1 ≤ S.depth → ∀ σ, Scr j σ → Scr (j + 1) σ)
    (htabLen : ∀ j, j + 1 ≤ S.depth → ∀ σ, Scr j σ →
      n₀ * (levelFml S (j + 1)).length ≤ (σ.arrs (arenaNames (j + 1)).tab).length)
    (hhtab : ∀ j, j + 1 ≤ S.depth → ∀ A : Arena (S.pal j) n₀,
      Adm j A → ∀ u : Fin A.N,
      htabF (j + 1) (childArena S A ((ord A.N A.G).order) u) = chanF j A u)
    (hfreshS : ∀ j i, j < i → ∀ y ∈ ctrName j :: levelScalars j, y ∉ LS i)
    (hfreshA : ∀ j i, j < i →
      ∀ a ∈ ca j :: co j :: cm j :: levelArrays j, a ∉ LA i)
    (hAdmChild : ∀ j (A : Arena (S.pal j) n₀), Adm j A → ¬ A.G = ⊥ →
      ∀ u : Fin A.N, Adm (j + 1) (childArena S A ((ord A.N A.G).order) u))
    (hleafChild : ∀ j (A : Arena (S.pal j) n₀), Adm j A → ¬ A.G = ⊥ →
      j + 1 = S.depth → ∀ u : Fin A.N,
      (childArena S A ((ord A.N A.G).order) u).G = ⊥)
    (hLSc : ∀ j, ctrName j ∈ LS j)
    (hLSb : ∀ j, ∀ y ∈ btScalars, y ∈ LS j)
    (hLAb : ∀ j, ∀ a ∈ [botNa j, botFa j, botEa j, botXa j, (arenaNames j).tab], a ∈ LA j)
    (hcovOwn : ∀ j, OwnedFrom LS LA j (covC j))
    (hprepOwn : ∀ j, OwnedFrom LS LA j (prepC j))
    (hreadOwn : ∀ j, OwnedFrom LS LA j (readC j))
    (hreadRank : ∀ j, "cp.r" ∉ (readC j).warrs)
    (hKB : ∀ k j, j < S.depth → ∀ A : Arena (S.pal j) n₀,
      4 + max (botComK A.N (S.pal j) Kq (levelFml S j))
        (Kcov j A + ((∑ i ∈ Finset.range A.N,
          (centreKC S ord KB KP KR k j A i + 8)) + 6)) ≤ KB (k + 1) j A)
    (hcov : CoverAllClean B S ord ℓp htabF hbf Adm ca co cm Scv covC Kcov)
    (hparts : ChildLoadPartsClean B S ord ℓp htabF hbf Adm Scr ca co cm prepC chanF KP)
    (hread : CentreRead B S ord ℓp htabF hbf Adm Scr ca co cm readC KR) :
    FrameStepClean B S ord ℓp htabF hbf arenaNames Adm KB Scr LS LA
      (guardBody S Kq (coverElse covC (centreLoopB (centreBody prepC readC)))) := by
  have hp := centrePrepClean_of_parts B S ord ℓp htabF hbf Adm Scr ca co cm prepC
    chanF hhtab KP hscrLen hscrDown htabLen hparts
  have hs := centreStepClean_of_prep_read B S ord ℓp htabF hbf Adm KB Scr LS LA
    ca co cm prepC readC KP KR hscrLen hfreshS hfreshA hAdmChild hleafChild
    hprepOwn hreadOwn hreadRank hp hread
  have hl := centreLoopClean_of_step B S ord ℓp htabF hbf Adm KB Scr LS LA
    ca co cm (centreBody prepC readC) (centreKC S ord KB KP KR) hn0B hscrLen hLSc hs
  have he := frameElseClean_of_cover_loop B S ord ℓp htabF hbf Adm KB Scr LS LA
    ca co cm Scv covC (centreLoopB (centreBody prepC readC)) Kcov _
    hscrCov hscrLen hcovOwn hcov hl
  exact frameStepClean_of_else B S ord ℓp htabF hbf Adm KB Scr LS LA _ _ Kq
    hKq hn0B hn0B2 hNLB h2LB hTB hscrBot hKB hLSb hLAb he

end Lax3Proofs.Prog
