import Lax3Proofs.SolvePrepCleanRoot

/-! Concrete consumer fit: PREP's proved machine pass supplies the exact
child precondition consumed by the clean recursive step. -/
namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
variable {L n₀ : ℕ}

theorem centrePrepClean_of_prep (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String)
    -- the constant-`ℓp` discipline (F7 owns both parameters)
    (hlpEq : ∀ j, j + 1 ≤ S.depth → ℓp (j + 1) = ℓp j)
    (hhbEq : ∀ j, j + 1 ≤ S.depth → hbf (j + 1) = hbf j)
    (hlpRoom : ∀ j, j + 1 ≤ S.depth → j < ℓp j)
    (hhbR : ∀ j, j + 1 ≤ S.depth → 2 * S.R + 1 ≤ hbf j)
    -- the admissible history shape and the channel-pinning seam
    (hAdmLen : ∀ j (A : Arena (S.pal j) n₀), Adm j A → A.hist.length = j)
    (hpin : ∀ j (A : Arena (S.pal j) n₀), Adm j A →
      ∀ (v : Fin A.N) (e : Fin (ℓp j)) (he : (e : ℕ) < A.hist.length)
        (z : Fin A.N),
        z ∈ htabF j A v e ↔ (A.up z) ∈ Lax3Proofs.SplitterWin.pathSet
          (A.hist.reverse[(e : ℕ)]'(by simpa using he)).2 (2 * S.R)
          (A.hist.reverse[(e : ℕ)]'(by simpa using he)).1 (A.up v))
    (hpinE : ∀ j (A : Arena (S.pal j) n₀), Adm j A →
      ∀ (v : Fin A.N) (e : Fin (ℓp j)), A.hist.length ≤ (e : ℕ) →
        htabF j A v e = [])
    -- the batch fits the width
    (hwidth : ∀ j, j + 1 ≤ S.depth → 1 + j * (2 * S.R + 1) ≤ S.width)
    -- word bounds
    (h1B : 1 < B) (hn0B : n₀ < B) (hn0nB : n₀ * n₀ < B)
    (hn02B : n₀ + 2 < B) (hbig1 : n₀ * n₀ + 2 * n₀ + 1 < B)
    (hdepthB : S.depth < B) (hRB : 2 * S.R + 3 < B) (hwB : S.width < B)
    (hlpB : ∀ j ≤ S.depth, ℓp j < B)
    (hhbB : ∀ j ≤ S.depth, hbf j + 1 < B)
    (hhistB : ∀ j ≤ S.depth, n₀ * ℓp j * (hbf j + 1) < B)
    (hpalB : ∀ j ≤ S.depth, n₀ * S.pal j < B)
    -- the scratch descriptor's length clauses
    (hscrA : ∀ j' σ, Scr j' σ →
      n₀ ≤ (σ.arrs "cp.l").length ∧ n₀ ≤ (σ.arrs "cp.r").length ∧
      n₀ ≤ (σ.arrs "cp.b").length ∧ n₀ ≤ (σ.arrs "cp.d").length ∧
      n₀ ≤ (σ.arrs "cp.p").length ∧ n₀ ≤ (σ.arrs "cp.x").length ∧
      n₀ + 2 ≤ (σ.arrs "cp.v").length ∧
      (σ.arrs "cp.w").length = S.width ∧
      n₀ + 1 ≤ (σ.arrs "cp.o").length ∧
      n₀ * n₀ ≤ (σ.arrs "cp.t").length ∧
      n₀ * S.pal j' ≤ (σ.arrs "cp.c").length ∧
      (∀ i, i < S.width → n₀ ≤ (σ.arrs (lv "cq.d" i)).length) ∧
      (∀ c, c < S.pal j' →
        n₀ * n₀ + 2 * n₀ ≤ (σ.arrs (lv "cq.v" c)).length) ∧
      (∀ c, c < S.pal j' + 1 → n₀ + 1 ≤ (σ.arrs (lv "cq.u" c)).length))
    (hscrLvl : ∀ j', j' + 1 ≤ S.depth → ∀ σ, Scr j' σ →
      n₀ + 1 ≤ (σ.arrs (arenaNames (j' + 1)).off).length ∧
      n₀ * n₀ ≤ (σ.arrs (arenaNames (j' + 1)).tgt).length ∧
      n₀ * S.pal (j' + 1) ≤ (σ.arrs (arenaNames (j' + 1)).col).length ∧
      n₀ ≤ (σ.arrs (arenaNames (j' + 1)).up).length ∧
      n₀ * ℓp j' * (hbf j' + 1)
        ≤ (σ.arrs (arenaNames (j' + 1)).hist).length)
    -- cover-name freshness
    (hcovA : ∀ jc j', ca jc ∉ levelArrays j' ∧ co jc ∉ levelArrays j' ∧
      cm jc ∉ levelArrays j')
    (hcovP : ∀ jc, (ca jc ∉ prepArrays ∧ co jc ∉ prepArrays ∧
        cm jc ∉ prepArrays) ∧
      ∀ i, (ca jc ≠ lv "cq.d" i ∧ ca jc ≠ lv "cq.v" i ∧
          ca jc ≠ lv "cq.u" i) ∧
        (co jc ≠ lv "cq.d" i ∧ co jc ≠ lv "cq.v" i ∧
          co jc ≠ lv "cq.u" i) ∧
        (cm jc ≠ lv "cq.d" i ∧ cm jc ≠ lv "cq.v" i ∧
          cm jc ≠ lv "cq.u" i))

    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (hscrDown : ∀ j, j + 1 ≤ S.depth → ∀ σ, Scr j σ → Scr (j + 1) σ)
    (htabLen : ∀ j, j + 1 ≤ S.depth → ∀ σ, Scr j σ →
      n₀ * (levelFml S (j + 1)).length ≤ (σ.arrs (arenaNames (j + 1)).tab).length)
    (hhtab : ∀ j, j + 1 ≤ S.depth → ∀ A : Arena (S.pal j) n₀,
      Adm j A → ∀ u : Fin A.N,
      htabF (j + 1) (childArena S A ((ord A.N A.G).order) u) = prepChan S ord ℓp htabF j A u)
 :
    CentrePrepClean B S ord ℓp htabF hbf Adm Scr ca co cm
      (prepCleanCom S ℓp hbf co cm)
      (fun _ j A u => prepCleanK S ord ℓp hbf j A u) := by
  exact centrePrepClean_of_parts B S ord ℓp htabF hbf Adm Scr ca co cm
    (prepCleanCom S ℓp hbf co cm) (prepChan S ord ℓp htabF) hhtab
    (fun _ j A u => prepCleanK S ord ℓp hbf j A u) hscrLen hscrDown htabLen
    (childLoadPartsClean_of B S ord ℓp htabF hbf Adm Scr ca co cm
    hlpEq hhbEq hlpRoom hhbR hAdmLen hpin hpinE hwidth h1B hn0B hn0nB
    hn02B hbig1 hdepthB hRB hwB hlpB hhbB hhistB hpalB hscrA hscrLvl hcovA hcovP)

end Lax3Proofs.Prog
