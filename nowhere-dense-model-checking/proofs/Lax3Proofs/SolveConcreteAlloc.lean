import Lax3Proofs.SolveConcreteBounds
import Lax3Proofs.SolveGlueLoad

/-! Realizable lengths. The total `ext` map follows `initEnv`; `codeLayout`
allocates only the finite list of regions used by the program. -/
namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding Lax3.ColoredGraphs Lax3Proofs.Driver
variable {L : ℕ}

def concreteCa (j : ℕ) := lv "cc.a" j
def concreteCo (j : ℕ) := lv "cc.o" j
def concreteCm (j : ℕ) := lv "cc.m" j
def concreteRa (j : ℕ) := lv "cc.r" j

private theorem concrete_lv_take (b : String) (hb : b.length = 4) (j : ℕ) :
    (lv b j).toList.take 4 = b.toList := by
  rw [lv_toList, ← hb, ← String.length_toList, List.take_left]

/-- Exact lengths for the root renaming, padded batch, and leaf evaluator. -/
noncomputable def concreteSize (S : Setup L) (n : ℕ) (a : String) : ℕ :=
  if a = "cp.w" then S.width else
  if a = "sa.u" then n else
  if a.toList.take 4 = "sb.n".toList then 2 ^ S.pal (a.length - 4) else
  if a.toList.take 4 = "sb.f".toList then
    2 ^ S.pal (a.length - 4) * (concreteQdepth S + 1) else
  if a.toList.take 4 = "sb.e".toList then concreteQdepth S + 1 else
  if a.toList.take 4 = "sb.x".toList then concreteQdepth S + 1 else
  concreteCapacity S n

/-- Raw targets may repeat, so the root target extent also covers `2m`. -/
noncomputable def concreteExt (S : Setup L) (x : List ℕ) (a : String) : ℕ :=
  if a = "off" then vertexCount x + 1 else
  if a = "tgt" then 2 * edgeCount x else
  if a = "up" then vertexCount x else
  if a = "sa.t" then max (concreteCapacity S (vertexCount x)) (2 * edgeCount x) else
  concreteSize S (vertexCount x) a

@[simp] theorem concreteExt_off (S : Setup L) (x : List ℕ) :
    concreteExt S x "off" = vertexCount x + 1 := by simp [concreteExt]
@[simp] theorem concreteExt_tgt (S : Setup L) (x : List ℕ) :
    concreteExt S x "tgt" = 2 * edgeCount x := by simp [concreteExt]
@[simp] theorem concreteExt_up (S : Setup L) (x : List ℕ) :
    concreteExt S x "up" = vertexCount x := by simp [concreteExt]
@[simp] theorem concreteExt_rootUp (S : Setup L) (x : List ℕ) :
    concreteExt S x "sa.u" = vertexCount x := by simp [concreteExt, concreteSize]
@[simp] theorem concreteExt_width (S : Setup L) (x : List ℕ) :
    concreteExt S x "cp.w" = S.width := by simp [concreteExt, concreteSize]

theorem concreteExt_rootTgt (S : Setup L) (x : List ℕ) :
    max (concreteCapacity S (vertexCount x)) (2 * edgeCount x) =
      concreteExt S x "sa.t" := by simp [concreteExt]

private theorem concrete_lv_ne_short (b a : String) (hb : b.length = 4)
    (ha : a.length < 4) (j : ℕ) : lv b j ≠ a := by
  intro h
  have := congrArg String.length h
  simp only [lv_length, hb] at this
  omega

theorem concreteSize_common (S : Setup L) (n : ℕ) (b : String) (j : ℕ)
    (hb : b.length = 4) (hw : b ≠ "cp.w") (hu : lv b j ≠ "sa.u")
    (hn : b ≠ "sb.n") (hf : b ≠ "sb.f") (he : b ≠ "sb.e") (hx : b ≠ "sb.x") :
    concreteSize S n (lv b j) = concreteCapacity S n := by
  have hw' : lv b j ≠ "cp.w" := lv_ne_of_base_ne (s := b) (t := "cp.w") hb hw j 0
  have hbn : b.toList ≠ "sb.n".toList := fun h => hn (String.toList_inj.mp h)
  have hbf : b.toList ≠ "sb.f".toList := fun h => hf (String.toList_inj.mp h)
  have hbe : b.toList ≠ "sb.e".toList := fun h => he (String.toList_inj.mp h)
  have hbx : b.toList ≠ "sb.x".toList := fun h => hx (String.toList_inj.mp h)
  simp only [concreteSize, if_neg hw', if_neg hu, concrete_lv_take b hb j,
    if_neg hbn, if_neg hbf, if_neg hbe, if_neg hbx]

/-- Common capacity for every ordinary four-character base. -/
theorem concreteExt_common (S : Setup L) (x : List ℕ) (b : String) (j : ℕ)
    (hb : b.length = 4)
    (hw : b ≠ "cp.w") (hu : lv b j ≠ "sa.u")
    (hn : b ≠ "sb.n") (hf : b ≠ "sb.f")
    (he : b ≠ "sb.e") (hx : b ≠ "sb.x") :
    concreteCapacity S (vertexCount x) ≤ concreteExt S x (lv b j) := by
  have hshort (a : String) (ha : a.length < 4) := concrete_lv_ne_short b a hb ha j
  have hw' : lv b j ≠ "cp.w" := lv_ne_of_base_ne hb hw j 0
  have hprefix := concrete_lv_take b hb j
  unfold concreteExt
  rw [if_neg (hshort "off" (by decide)), if_neg (hshort "tgt" (by decide)),
    if_neg (hshort "up" (by decide))]
  split_ifs with ht
  · exact Nat.le_max_left ..
  · have hbn : b.toList ≠ "sb.n".toList := fun h => hn (String.toList_inj.mp h)
    have hbf : b.toList ≠ "sb.f".toList := fun h => hf (String.toList_inj.mp h)
    have hbe : b.toList ≠ "sb.e".toList := fun h => he (String.toList_inj.mp h)
    have hbx : b.toList ≠ "sb.x".toList := fun h => hx (String.toList_inj.mp h)
    simp only [concreteSize, if_neg hw', if_neg hu, hprefix, if_neg hbn,
      if_neg hbf, if_neg hbe, if_neg hbx, le_refl]

@[simp] theorem concreteExt_bot (S : Setup L) (x : List ℕ) (j : ℕ) :
    concreteExt S x (botNa j) = 2 ^ S.pal j ∧
    concreteExt S x (botFa j) = 2 ^ S.pal j * (concreteQdepth S + 1) ∧
    concreteExt S x (botEa j) = concreteQdepth S + 1 ∧
    concreteExt S x (botXa j) = concreteQdepth S + 1 := by
  have hne (b : String) (hb : b ∈ (["sb.n", "sb.f", "sb.e", "sb.x"] : List String))
      (a : String) (ha : a ∈ (["cp.w", "sa.u", "sa.t"] : List String)) :
      lv b j ≠ a := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ha
    have hb4 : b.length = 4 := by rcases hb with rfl | rfl | rfl | rfl <;> rfl
    have ha4 : a.length = 4 := by rcases ha with rfl | rfl | rfl <;> rfl
    have hba : b ≠ a := by
      rcases hb with rfl | rfl | rfl | rfl <;> rcases ha with rfl | rfl | rfl <;> decide
    exact lv_ne_of_base_ne (s := b) (t := a) (by omega) hba j 0
  have hs (b : String) (hb : b.length = 4) (a : String) (ha : a.length < 4) :=
    concrete_lv_ne_short b a hb ha j
  simp [botNa, botFa, botEa, botXa, concreteExt, concreteSize,
    hs, hne, concrete_lv_take, lv_length,
    show "sb.n".length = 4 from rfl, show "sb.f".length = 4 from rfl,
    show "sb.e".length = 4 from rfl, show "sb.x".length = 4 from rfl,
    show "off".length = 3 from rfl, show "tgt".length = 3 from rfl,
    show "up".length = 2 from rfl]

@[simp] theorem concreteSize_bot (S : Setup L) (n : ℕ) (j : ℕ) :
    concreteSize S n (botNa j) = 2 ^ S.pal j ∧
    concreteSize S n (botFa j) = 2 ^ S.pal j * (concreteQdepth S + 1) ∧
    concreteSize S n (botEa j) = concreteQdepth S + 1 ∧
    concreteSize S n (botXa j) = concreteQdepth S + 1 := by
  have hne (b : String) (hb : b ∈ (["sb.n", "sb.f", "sb.e", "sb.x"] : List String))
      (a : String) (ha : a ∈ (["cp.w", "sa.u", "sa.t"] : List String)) :
      lv b j ≠ a := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ha
    have hb4 : b.length = 4 := by rcases hb with rfl | rfl | rfl | rfl <;> rfl
    have ha4 : a.length = 4 := by rcases ha with rfl | rfl | rfl <;> rfl
    have hba : b ≠ a := by
      rcases hb with rfl | rfl | rfl | rfl <;> rcases ha with rfl | rfl | rfl <;> decide
    exact lv_ne_of_base_ne (s := b) (t := a) (by omega) hba j 0
  have hs (b : String) (hb : b.length = 4) (a : String) (ha : a.length < 4) :=
    concrete_lv_ne_short b a hb ha j
  simp [botNa, botFa, botEa, botXa, concreteSize,
    hs, hne, concrete_lv_take, lv_length,
    show "sb.n".length = 4 from rfl, show "sb.f".length = 4 from rfl,
    show "sb.e".length = 4 from rfl, show "sb.x".length = 4 from rfl,
    show "off".length = 3 from rfl, show "tgt".length = 3 from rfl,
    show "up".length = 2 from rfl]

/-- The level bound and allocated scratch lengths. Only the raw root target
region allows an additional input-dependent extent. -/
noncomputable def ConcreteScr (S : Setup L) (n j : ℕ) (σ : Env) : Prop :=
  j ≤ S.depth ∧ ∀ a, a ∉ matArrays →
    if a = "sa.t" then concreteSize S n a ≤ (σ.arrs a).length
    else (σ.arrs a).length = concreteSize S n a

theorem ConcreteScr.transport (S : Setup L) (n j : ℕ)
    {σ σ' : Env} (h : ConcreteScr S n j σ)
    (hlen : ∀ a, (σ'.arrs a).length = (σ.arrs a).length) : ConcreteScr S n j σ' := by
  refine ⟨h.1, ?_⟩
  intro a ha
  rw [hlen a]
  exact h.2 a ha

theorem ConcreteScr.down (S : Setup L) (n j : ℕ)
    (hj : j + 1 ≤ S.depth) {σ : Env} (h : ConcreteScr S n j σ) :
    ConcreteScr S n (j + 1) σ := ⟨hj, h.2⟩

theorem ConcreteScr.bound (S : Setup L) (n j : ℕ)
    {σ : Env} (h : ConcreteScr S n j σ) (a : String) (ha : a ∉ matArrays) :
    concreteSize S n a ≤ (σ.arrs a).length := by
  have hh := h.2 a ha
  split_ifs at hh with ht
  · exact hh
  · exact hh.ge

theorem concrete_lv_notMat (b : String) (hb : b.length = 4) (j : ℕ) :
    lv b j ∉ matArrays := by
  simp only [matArrays, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨concrete_lv_ne_short b "off" hb (by decide) j,
    concrete_lv_ne_short b "tgt" hb (by decide) j,
    concrete_lv_ne_short b "up" hb (by decide) j⟩

theorem ConcreteScr.common (S : Setup L) (n j : ℕ) {σ : Env}
    (h : ConcreteScr S n j σ) (b : String) (i : ℕ)
    (hb : b.length = 4) (hw : b ≠ "cp.w") (hu : lv b i ≠ "sa.u")
    (hn : b ≠ "sb.n") (hf : b ≠ "sb.f") (he : b ≠ "sb.e") (hx : b ≠ "sb.x") :
    concreteCapacity S n ≤ (σ.arrs (lv b i)).length := by
  rw [← concreteSize_common S n b i hb hw hu hn hf he hx]
  exact h.bound S n j _ (concrete_lv_notMat b hb i)

theorem ConcreteScr.width (S : Setup L) (n j : ℕ) {σ : Env}
    (h : ConcreteScr S n j σ) : (σ.arrs "cp.w").length = S.width := by
  simpa [concreteSize] using h.2 "cp.w" (by decide)

theorem ConcreteScr.bot (S : Setup L) (n j : ℕ) {σ : Env}
    (h : ConcreteScr S n j σ) (i : ℕ) :
    (σ.arrs (botNa i)).length = 2 ^ S.pal i ∧
    (σ.arrs (botFa i)).length = 2 ^ S.pal i * (concreteQdepth S + 1) ∧
    (σ.arrs (botEa i)).length = concreteQdepth S + 1 ∧
    (σ.arrs (botXa i)).length = concreteQdepth S + 1 := by
  have hn := h.2 (botNa i) (concrete_lv_notMat "sb.n" rfl i)
  have hf := h.2 (botFa i) (concrete_lv_notMat "sb.f" rfl i)
  have he := h.2 (botEa i) (concrete_lv_notMat "sb.e" rfl i)
  have hx := h.2 (botXa i) (concrete_lv_notMat "sb.x" rfl i)
  rw [if_neg (show botNa i ≠ "sa.t" from lv_ne_of_base_ne (s := "sb.n") (t := "sa.t") rfl (by decide) i 0)] at hn
  rw [if_neg (show botFa i ≠ "sa.t" from lv_ne_of_base_ne (s := "sb.f") (t := "sa.t") rfl (by decide) i 0)] at hf
  rw [if_neg (show botEa i ≠ "sa.t" from lv_ne_of_base_ne (s := "sb.e") (t := "sa.t") rfl (by decide) i 0)] at he
  rw [if_neg (show botXa i ≠ "sa.t" from lv_ne_of_base_ne (s := "sb.x") (t := "sa.t") rfl (by decide) i 0)] at hx
  simpa only [hn, hf, he, hx] using concreteSize_bot S n i

theorem MatIn.concreteScr (S : Setup L) {n : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} (henc : EncodesGraph x n G) {σ : Env}
    (h : MatIn (concreteExt S x) x σ) : ConcreteScr S n 0 σ := by
  refine ⟨Nat.zero_le _, ?_⟩
  intro a ha
  have ha' := ha
  simp only [matArrays, List.mem_cons, List.not_mem_nil, or_false, not_or] at ha'
  rw [h.arrs a ha, List.length_replicate]
  unfold concreteExt
  rw [if_neg ha'.1, if_neg ha'.2.1, if_neg ha'.2.2, henc.vertexCount_eq]
  split_ifs with ht
  · subst a
    simp [concreteSize]
  · rfl

/-- Ordinary region bases used outside the leaf evaluator. -/
def concreteCommonBases : List String :=
  ["cp.l", "cp.r", "cp.b", "cp.d", "cp.p", "cp.x", "cp.v", "cp.o", "cp.t", "cp.c",
   "cq.d", "cq.v", "cq.u", "sa.o", "sa.t", "sa.c", "sa.h", "sa.b",
   "cc.a", "cc.o", "cc.m", "cc.r", "rd.p", "rd.m", "rd.d", "rd.s", "cl.d"]

theorem ConcreteScr.ordinary (S : Setup L) (n j : ℕ) {σ : Env}
    (h : ConcreteScr S n j σ) (b : String) (i : ℕ) (hb : b ∈ concreteCommonBases) :
    concreteCapacity S n ≤ (σ.arrs (lv b i)).length := by
  have hall : ∀ b ∈ concreteCommonBases, b.length = 4 ∧ b ≠ "cp.w" ∧ b ≠ "sa.u" ∧
      b ≠ "sb.n" ∧ b ≠ "sb.f" ∧ b ≠ "sb.e" ∧ b ≠ "sb.x" := by decide
  obtain ⟨h4, hw, hu, hn, hf, he, hx⟩ := hall b hb
  exact h.common S n j b i h4 hw
    (lv_ne_of_base_ne (s := b) (t := "sa.u") h4 hu i 0) hn hf he hx

theorem ConcreteScr.childUp (S : Setup L) (n j i : ℕ) {σ : Env}
    (h : ConcreteScr S n j σ) :
    concreteCapacity S n ≤ (σ.arrs (arenaNames (i + 1)).up).length := by
  apply h.common S n j "sa.u" (i + 1) rfl (by decide) _ (by decide) (by decide) (by decide) (by decide)
  exact lv_ne_of_level_ne (s := "sa.u") (t := "sa.u") (j := i + 1) (k := 0) rfl (by omega)

end Lax3Proofs.Prog
