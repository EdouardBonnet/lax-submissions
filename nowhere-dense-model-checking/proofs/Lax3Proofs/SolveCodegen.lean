import Lax3Proofs.ProgCodegen

/-! A layout inferred from the complete command supplies every referenced name
and enough expression temporaries. Its finite span is absorbed into the same
squared word-room constant used by the model-checking theorem. -/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Compile
open Lax67Proofs.Reasoning Lax62Proofs.Codegen
open Lax62Proofs.Refine.Codegen (computesInTime_of_spec)
open Lax11.GraphEncoding Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)

def codeExprScalars : Expr → List String
  | .lit _ => []
  | .var x => [x]
  | .get _ i => codeExprScalars i
  | .bin _ e f => codeExprScalars e ++ codeExprScalars f

def codeExprArrays : Expr → List String
  | .lit _ | .var _ => []
  | .get a i => a :: codeExprArrays i
  | .bin _ e f => codeExprArrays e ++ codeExprArrays f

theorem codeExpr_ok {L : Layout} (e : Expr) (d : ℕ)
    (hS : ∀ x ∈ codeExprScalars e, x ∈ L.scalars)
    (hA : ∀ a ∈ codeExprArrays e, a ∈ L.arrays)
    (hT : d + e.size ≤ L.temps) : Expr.Ok L e d := by
  induction e generalizing d with
  | lit => trivial
  | var x => exact hS x (by simp [codeExprScalars])
  | get a i ih =>
    refine ⟨hA a (by simp [codeExprArrays]),
      ih d hS (fun b hb => hA b (List.mem_cons_of_mem a hb)) ?_, ?_⟩ <;>
      simp only [Expr.size] at hT <;> omega
  | bin op e f ihe ihf =>
    simp only [Expr.size] at hT
    refine ⟨ihf d (fun x hx => hS x (List.mem_append_right _ hx))
      (fun a ha => hA a (List.mem_append_right _ ha)) (by omega),
      ihe (d + 1) (fun x hx => hS x (List.mem_append_left _ hx))
      (fun a ha => hA a (List.mem_append_left _ ha)) (by omega), by omega⟩

def codeComScalars : Com → List String
  | .skip => []
  | .assign x e => x :: codeExprScalars e
  | .store _ i e => codeExprScalars i ++ codeExprScalars e
  | .seq c d => codeComScalars c ++ codeComScalars d
  | .ite b c d => codeExprScalars (condExpr b) ++ codeComScalars c ++ codeComScalars d
  | .while b c => codeExprScalars (condExpr b) ++ codeComScalars c
  | .read x => [x]
  | .write e => codeExprScalars e

def codeComArrays : Com → List String
  | .skip | .read _ => []
  | .assign _ e | .write e => codeExprArrays e
  | .store a i e => a :: (codeExprArrays i ++ codeExprArrays e)
  | .seq c d => codeComArrays c ++ codeComArrays d
  | .ite b c d => codeExprArrays (condExpr b) ++ codeComArrays c ++ codeComArrays d
  | .while b c => codeExprArrays (condExpr b) ++ codeComArrays c

def codeComTemps : Com → ℕ
  | .skip | .read _ => 0
  | .assign _ e => e.size
  | .store _ i e => i.size + e.size + 1
  | .seq c d => max (codeComTemps c) (codeComTemps d)
  | .ite b c d => max (condExpr b).size (max (codeComTemps c) (codeComTemps d))
  | .while b c => max (condExpr b).size (codeComTemps c)
  | .write e => e.size + 1

theorem codeCom_ok {L : Layout} (c : Com)
    (hS : ∀ x ∈ codeComScalars c, x ∈ L.scalars)
    (hA : ∀ a ∈ codeComArrays c, a ∈ L.arrays)
    (hT : codeComTemps c ≤ L.temps) : Com.Ok L c := by
  induction c with
  | skip => trivial
  | assign x e =>
    exact ⟨hS x (by simp [codeComScalars]), codeExpr_ok e 0
      (fun y hy => hS y (List.mem_cons_of_mem _ hy)) hA (by simpa [codeComTemps] using hT)⟩
  | store a i e =>
    dsimp only [codeComTemps] at hT
    refine ⟨hA a (by simp [codeComArrays]),
      codeExpr_ok i 0 (fun x hx => hS x (List.mem_append_left _ hx))
        (fun b hb => hA b (List.mem_cons_of_mem _ (List.mem_append_left _ hb))) (by omega),
      codeExpr_ok e 1 (fun x hx => hS x (List.mem_append_right _ hx))
        (fun b hb => hA b (List.mem_cons_of_mem _ (List.mem_append_right _ hb))) (by omega),
      by omega⟩
  | seq c d ihc ihd =>
    have hT' : codeComTemps c ≤ L.temps ∧ codeComTemps d ≤ L.temps := max_le_iff.mp hT
    exact ⟨ihc (fun x hx => hS x (List.mem_append_left _ hx))
      (fun a ha => hA a (List.mem_append_left _ ha)) hT'.1,
      ihd (fun x hx => hS x (List.mem_append_right _ hx))
      (fun a ha => hA a (List.mem_append_right _ ha)) hT'.2⟩
  | ite b c d ihc ihd =>
    have hT' : (condExpr b).size ≤ L.temps ∧
        codeComTemps c ≤ L.temps ∧ codeComTemps d ≤ L.temps := by
      simpa only [codeComTemps, max_le_iff] using hT
    refine ⟨codeExpr_ok (condExpr b) 0
      (fun x hx => hS x (by simp [codeComScalars, hx]))
      (fun a ha => hA a (by simp [codeComArrays, ha])) (by simpa using hT'.1),
      ihc (fun x hx => hS x (by simp [codeComScalars, hx]))
        (fun a ha => hA a (by simp [codeComArrays, ha])) hT'.2.1,
      ihd (fun x hx => hS x (by simp [codeComScalars, hx]))
        (fun a ha => hA a (by simp [codeComArrays, ha])) hT'.2.2⟩
  | «while» b c ih =>
    have hT' : (condExpr b).size ≤ L.temps ∧ codeComTemps c ≤ L.temps := max_le_iff.mp hT
    exact ⟨codeExpr_ok (condExpr b) 0
      (fun x hx => hS x (List.mem_append_left _ hx))
      (fun a ha => hA a (List.mem_append_left _ ha)) (by simpa using hT'.1),
      ih (fun x hx => hS x (List.mem_append_right _ hx))
        (fun a ha => hA a (List.mem_append_right _ ha)) hT'.2⟩
  | read x => exact hS x (by simp [codeComScalars])
  | write e =>
    dsimp only [codeComTemps] at hT
    exact ⟨codeExpr_ok e 0 hS hA (by omega), by omega⟩

/-- A finite layout determined by the actual command, including the temporary
space required by nested boolean expressions. -/
def codeLayout (c : Com) : Layout :=
  ⟨(codeComScalars c).eraseDups, (codeComArrays c).eraseDups, codeComTemps c⟩

theorem codeLayout_ok (c : Com) : Com.Ok (codeLayout c) c :=
  codeCom_ok c (fun _ hx => List.mem_eraseDups.mpr hx)
    (fun _ ha => List.mem_eraseDups.mpr ha) le_rfl

theorem layout_span_le_mcB (lay : Layout) {n c w q : ℕ}
    {G : SimpleGraph (Fin n)}
    (hspan : lay.temps + 2 + lay.scalars.length + lay.arrays.length * q ≤ c) :
    ∀ x ∈ mcD n G c w, lay.span (mcB q x) ≤ 2 ^ w := by
  intro x hx
  have hpos : 0 < (x.length + 1) ^ 2 := Nat.pow_pos (by omega)
  calc
    lay.span (mcB q x) = lay.temps + 2 + lay.scalars.length +
        lay.arrays.length * (q * (x.length + 1) ^ 2) := rfl
    _ ≤ (lay.temps + 2 + lay.scalars.length) * (x.length + 1) ^ 2 +
        lay.arrays.length * (q * (x.length + 1) ^ 2) :=
      Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hpos) _
    _ = (lay.temps + 2 + lay.scalars.length + lay.arrays.length * q) *
        (x.length + 1) ^ 2 := by ring
    _ ≤ c * (x.length + 1) ^ 2 := Nat.mul_le_mul_right _ hspan
    _ ≤ 2 ^ w := c_mul_sq_le_two_pow x hx

theorem layout_fitsWords_mcB (lay : Layout) {n c w q : ℕ}
    {G : SimpleGraph (Fin n)} (hq : 1 ≤ q) (hqc : q ≤ c)
    (hspan : lay.temps + 2 + lay.scalars.length + lay.arrays.length * q ≤ c) :
    ∀ x ∈ mcD n G c w, lay.FitsWords (mcB q x) w := by
  intro x hx
  exact ⟨one_lt_mcB (three_le_length hx.1) hq, mcB_le_two_pow hqc x hx,
    layout_span_le_mcB lay hspan x hx⟩

open Classical in
/-- Compile the full pipeline with all names and temporary cells inferred from
its actual syntax. The solve specification is the only execution premise. -/
theorem mc_auto_computesInTime_of_solveSpec
    (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ext : List ℕ → String → ℕ)
    (solveCom : Com) (Ks : List ℕ → ℕ)
    (hq : 1 ≤ q) (hqc : q ≤ c)
    (hspan : (codeLayout (mcCom solveCom)).temps + 2 +
      (codeLayout (mcCom solveCom)).scalars.length +
      (codeLayout (mcCom solveCom)).arrays.length * q ≤ c)
    (hextOff : ∀ x ∈ mcD n G c w, ext x "off" = vertexCount x + 1)
    (hextTgt : ∀ x ∈ mcD n G c w, ext x "tgt" = 2 * edgeCount x)
    (hnw : solveCom.NoWrite)
    (hsolve : SolveSpec C hC φ ord G c w q ext solveCom Ks) :
    Lax67.RamComputes.ComputesInTime w
      (compileProgram (codeLayout (mcCom solveCom)) (mcCom solveCom))
      (mcD n G c w)
      (fun _ => if Lax3.FirstOrder.Sat G Fin.elim0 φ then [1] else [0])
      (fun x => (codeLayout (mcCom solveCom)).const * mcK Ks x) := by
  refine computesInTime_of_spec (codeLayout_ok (mcCom solveCom)) (mcD_entry_lt_mcB hq) ?_
    (layout_fitsWords_mcB (codeLayout (mcCom solveCom)) hq hqc hspan)
  intro x hx
  obtain ⟨henc, hside⟩ := hx
  refine ⟨ext x, ?_⟩
  -- the semantic chain: the obligation's value is the axiom's value
  have hiff : Unroll.unrolledMC (Headline.headlineSetup C hC φ) ord G
      (Impl.trivialColoring n) ↔ Lax3.FirstOrder.Sat G Fin.elim0 φ := by
    rw [Unroll.unrolledMC_eq_MC]
    exact Headline.headlineSetup_mc_correct C hC φ ord G (Impl.trivialColoring n)
  have hone : 1 < mcB q x := one_lt_mcB (three_le_length henc) hq
  have hv01 : (if Lax3.FirstOrder.Sat G Fin.elim0 φ then (1 : ℕ) else 0)
      < mcB q x := by
    split <;> omega
  -- stage 1: the front end
  have hpar := parseCom_spec (mcB q x) (ext x) henc
    (length_add_one_lt_mcB (three_le_length henc) hq)
    (hextOff x ⟨henc, hside⟩) (hextTgt x ⟨henc, hside⟩)
  -- stage 2: the obligation, its value converted, its output tape framed
  have hsol : Spec (mcB q x) (CsrIn (ext x) x) solveCom
      (fun σ σ' => σ'.vars "verdict" =
          (if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0) ∧
        σ'.out = σ.out) (Ks x) := by
    refine ((hsolve x ⟨henc, hside⟩).frame).post ?_
    rintro σ σ' - ⟨hq', -, -, -, hout⟩
    refine ⟨?_, hout hnw⟩
    rw [hq']
    exact if_congr hiff rfl rfl
  -- stage 3: the epilogue
  have hwr := writeScalar_spec (mcB q x) "verdict"
    (if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0) hv01
  -- the chain
  have htail : Spec (mcB q x) (CsrIn (ext x) x)
      (.seq solveCom (writeScalar "verdict"))
      (fun σ σ'' => σ''.out = σ.out ++
        [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0]) (Ks x + 2) := by
    refine Spec.seq hsol hwr (fun _ _ _ hq' => hq'.1) ?_
    rintro σ σ' σ'' - ⟨-, hout⟩ rfl
    show σ'.out ++ _ = σ.out ++ _
    rw [hout]
  refine (Spec.seq hpar htail (fun _ _ _ hq' => hq') ?_).mono
    (by rw [mcK]; omega)
  rintro σ σ' σ'' - hcsr hout
  rw [hout, hcsr.out]
  simp only [List.nil_append]
  exact apply_ite (fun v : ℕ => ([v] : List ℕ))
    (Lax3.FirstOrder.Sat G Fin.elim0 φ) 1 0

end Lax3Proofs.Prog
