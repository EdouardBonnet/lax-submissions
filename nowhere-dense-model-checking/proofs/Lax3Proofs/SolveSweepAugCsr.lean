import Lax3Proofs.SolveSweepAug
import Lax3Proofs.SolveSweepPeel

/-!
# Sparse occupied-key lists to compressed rows

The input is the occupied prefix of a directed-key list: `u*N+v` contributes
`u` to row `v`. Count heads, prefix the counts, copy the cursors, and stably
scatter the tails. Only the occupied prefix is scanned; the reservations for
the dictionary and targets are never initialized by a capacity-sized pass.
-/

namespace Lax3Proofs.Prog

set_option linter.unusedSimpArgs false

open Lax67Proofs.Imp Lax67Proofs.Reasoning Lax67Proofs.Reasoning.Lib
open Lax3Proofs.Augmentation Lax3Proofs.Augmentation.Orientation

/-- The scalar scratch cells, reusable between augmentation stages. -/
def agCsrVars : List String := ["ac.n", "ac.m", "ac.i", "ac.k", "ac.v"]

/-- Zero exactly the `N` meaningful count cells. -/
def agCsrZero (ct : String) : Com :=
  .seq (.assign "ac.i" (.lit 0))
    (.while (.lt (.var "ac.i") (.var "ac.n"))
      (.seq (.store ct (.var "ac.i") (.lit 0))
        (.assign "ac.i" (.add (.var "ac.i") (.lit 1)))))

/-- The head decoded with the machine's division and subtraction operations. -/
def agCsrHead : Expr :=
  .sub (.var "ac.k") (.mul (.div (.var "ac.k") (.var "ac.n")) (.var "ac.n"))

/-- Count heads in the occupied key prefix. -/
def agCsrCount (ky ct : String) : Com :=
  .seq (.assign "ac.i" (.lit 0))
    (.while (.lt (.var "ac.i") (.var "ac.m"))
      (.seq (.assign "ac.k" (.get ky (.var "ac.i")))
        (.seq (.assign "ac.v" agCsrHead)
          (.seq (.store ct (.var "ac.v")
              (.add (.get ct (.var "ac.v")) (.lit 1)))
            (.assign "ac.i" (.add (.var "ac.i") (.lit 1)))))))

/-- Prefix the counts into the requested output offsets. -/
def agCsrPrefix (ct o : String) : Com :=
  .seq (.store o (.lit 0) (.lit 0))
    (.seq (.assign "ac.i" (.lit 0))
      (.while (.lt (.var "ac.i") (.var "ac.n"))
        (.seq (.store o (.add (.var "ac.i") (.lit 1))
            (.add (.get o (.var "ac.i")) (.get ct (.var "ac.i"))))
          (.assign "ac.i" (.add (.var "ac.i") (.lit 1))))))

/-- Copy bucket starts into the `N` fill cursors. -/
def agCsrCopy (o cu : String) : Com :=
  .seq (.assign "ac.i" (.lit 0))
    (.while (.lt (.var "ac.i") (.var "ac.n"))
      (.seq (.store cu (.var "ac.i") (.get o (.var "ac.i")))
        (.assign "ac.i" (.add (.var "ac.i") (.lit 1)))))

/-- Scatter each key's tail into its head's next row slot. -/
def agCsrScatter (ky cu t : String) : Com :=
  .seq (.assign "ac.i" (.lit 0))
    (.while (.lt (.var "ac.i") (.var "ac.m"))
      (.seq (.assign "ac.k" (.get ky (.var "ac.i")))
        (.seq (.assign "ac.v" agCsrHead)
          (.seq (.store t (.get cu (.var "ac.v")) (.div (.var "ac.k") (.var "ac.n")))
            (.seq (.store cu (.var "ac.v") (.add (.get cu (.var "ac.v")) (.lit 1)))
              (.assign "ac.i" (.add (.var "ac.i") (.lit 1))))))))

/-- The complete occupied-prefix CSR constructor. -/
def agCsrCom (nN sz ky o t ct cu : String) : Com :=
  .seq (.seq (.assign "ac.n" (.var nN)) (.assign "ac.m" (.var sz)))
    (.seq (agCsrZero ct)
      (.seq (agCsrCount ky ct)
        (.seq (agCsrPrefix ct o)
          (.seq (agCsrCopy o cu) (agCsrScatter ky cu t)))))

/-- The actual expression-priced bound of the linear passes. -/
def agCsrK (N M : ℕ) : ℕ := 56 * M + 40 * N + 37

/-- A stable payload scatter yields duplicate-free compressed rows whenever
no two source positions carry the same head/tail pair. -/
theorem agCsrRows_of_scatter {N M : ℕ} {o t : String} {f g : ℕ → ℕ} {σ : Env}
    (hf : ∀ p, p < M → f p < N) (hg : ∀ p, p < M → g p < N)
    (hinj : ∀ p q, p < M → q < M → f p = f q → g p = g q → p = q)
    (hoL : N + 1 ≤ (σ.arrs o).length) (htL : M ≤ (σ.arrs t).length)
    (hov : ∀ z, z ≤ N → (σ.arrs o).getD z 0 = peelIOff f M z)
    (htv : ∀ p, p < M → (σ.arrs t).getD (peelDest f M p) 0 = g p) :
    ∃ rows : Fin N → List (Fin N),
      AgCsrRows o t M rows (peelIOff f M) σ ∧
      (∀ v, (rows v).Nodup) ∧
      ∀ u v, u ∈ rows v ↔ ∃ p, p < M ∧ f p = v ∧ g p = u := by
  classical
  let off := peelIOff f M
  let tgt : ℕ → ℕ := fun p => (σ.arrs t).getD p 0
  have htN : ∀ q, q < M → tgt q < N := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := peelDest_surj hf hq
    rw [show tgt (peelDest f M p) = g p from htv p hp]
    exact hg p hp
  have hslot : ∀ (v : Fin N) (i : Fin (peelOcc f v M)), off v + i < M := by
    intro v i
    have h := peelIOff_le hf (show (v : ℕ) + 1 ≤ N by omega)
    rw [peelIOff_succ] at h
    dsimp [off]
    omega
  let entry (v : Fin N) (i : Fin (peelOcc f v M)) : Fin N :=
    ⟨tgt (off v + i), htN _ (hslot v i)⟩
  let rows (v : Fin N) : List (Fin N) := List.ofFn (entry v)
  have hsource : ∀ (v : Fin N) (i : Fin (peelOcc f v M)),
      ∃ p, p < M ∧ f p = v ∧ peelDest f M p = off v + i ∧ g p = entry v i := by
    intro v i
    obtain ⟨p, hp, he⟩ := peelDest_surj hf (hslot v i)
    have hb : off v ≤ off v + i ∧ off v + i < off (v + 1) := by
      dsimp [off]
      rw [peelIOff_succ]
      omega
    have hv : f p = v := peel_bucket_unique (he ▸ peelDest_mem hf hp) hb
    refine ⟨p, hp, hv, he, ?_⟩
    dsimp [entry]
    rw [← he]
    exact (htv p hp).symm
  refine ⟨rows, ⟨peelIOff_zero f M, ?_, peelIOff_last hf, hoL, htL, hov, ?_⟩, ?_, ?_⟩
  · intro v
    simpa [rows] using peelIOff_succ f M v
  · intro v i hi
    have hi' : i < peelOcc f v M := by simpa [rows] using hi
    simp only [rows, List.getElem_ofFn, entry]
    rfl
  · intro v
    apply List.nodup_ofFn.mpr
    intro i j he
    obtain ⟨p, hp, hfp, hep, hgp⟩ := hsource v i
    obtain ⟨q, hq, hfq, heq, hgq⟩ := hsource v j
    have hpq : p = q := hinj p q hp hq (hfp.trans hfq.symm)
      (hgp.trans ((congrArg Fin.val he).trans hgq.symm))
    subst q
    apply Fin.ext
    omega
  · intro u v
    change u ∈ List.ofFn (entry v) ↔ _
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨p, hp, hfp, _, hgp⟩ := hsource v i
      exact ⟨p, hp, hfp, hgp.trans (congrArg Fin.val hi)⟩
    · rintro ⟨p, hp, hfp, hgp⟩
      have hi : peelOcc f v p < peelOcc f v M := by
        simpa [hfp] using peelOcc_strict f hp
      refine ⟨⟨peelOcc f v p, hi⟩, ?_⟩
      apply Fin.ext
      change tgt (off v + peelOcc f v p) = u
      have hd : off v + peelOcc f v p = peelDest f M p := by simp [peelDest, off, hfp]
      rw [hd, show tgt (peelDest f M p) = g p from htv p hp, hgp]

/-- Initialize the count prefix once. -/
theorem agCsrZero_spec {B N : ℕ} {ct : String} (hNB : N < B) :
    Spec B (fun σ => σ.vars "ac.n" = N ∧ N ≤ (σ.arrs ct).length)
      (agCsrZero ct) (fun _ σ' => ∀ z, z < N → (σ'.arrs ct).getD z 0 = 0)
      (11 * N + 6) := by
  let I : Env → Prop := fun σ => σ.vars "ac.n" = N ∧ σ.vars "ac.i" ≤ N ∧
    N ≤ (σ.arrs ct).length ∧ ∀ z, z < σ.vars "ac.i" → (σ.arrs ct).getD z 0 = 0
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "ac.i" < N)
      (.seq (.store ct (.var "ac.i") (.lit 0))
        (.assign "ac.i" (.add (.var "ac.i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "ac.i" = σ.vars "ac.i" + 1) 7 := by
    rintro σ ⟨⟨hn, hi, hL, hv⟩, hiN⟩
    run_vcg
    dsimp [I]
    simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr]
    simp only [show ("ac.n" : String) ≠ "ac.i" by decide, if_false, if_true,
      List.length_set]
    refine ⟨⟨hn, by omega, hL, ?_⟩, by trivial⟩
    intro z hz
    rw [getD_set _ _ _ (by omega)]
    split_ifs with h
    · rfl
    · exact hv z (by omega)
  refine (Spec.forRangeZero "ac.i" "ac.n" I N 7 hNB
    (fun _ h => h.2.1) (fun _ h => h.1) hbody).conseq ?_ ?_ (by omega)
  · rintro σ ⟨hn, hL⟩
    simp [I, hn, hL]
  · rintro σ σ' _ ⟨hI, hi⟩ z hz
    exact hI.2.2.2 z (by omega)

/-- Copy a prefix of bounded words. -/
theorem agCsrCopy_spec {B N : ℕ} {src dst : String} {v : ℕ → ℕ}
    (hNB : N < B) (hne : src ≠ dst) (hvB : ∀ z, z < N → v z < B) :
    Spec B (fun σ => σ.vars "ac.n" = N ∧ N ≤ (σ.arrs src).length ∧
        N ≤ (σ.arrs dst).length ∧ ∀ z, z < N → (σ.arrs src).getD z 0 = v z)
      (.seq (.assign "ac.i" (.lit 0))
        (.while (.lt (.var "ac.i") (.var "ac.n"))
          (.seq (.store dst (.var "ac.i") (.get src (.var "ac.i")))
            (.assign "ac.i" (.add (.var "ac.i") (.lit 1))))))
      (fun _ σ' => ∀ z, z < N → (σ'.arrs dst).getD z 0 = v z) (12 * N + 6) := by
  let I : Env → Prop := fun σ => σ.vars "ac.n" = N ∧ σ.vars "ac.i" ≤ N ∧
    N ≤ (σ.arrs src).length ∧ N ≤ (σ.arrs dst).length ∧
    (∀ z, z < N → (σ.arrs src).getD z 0 = v z) ∧
    (∀ z, z < σ.vars "ac.i" → (σ.arrs dst).getD z 0 = v z)
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "ac.i" < N)
      (.seq (.store dst (.var "ac.i") (.get src (.var "ac.i")))
        (.assign "ac.i" (.add (.var "ac.i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "ac.i" = σ.vars "ac.i" + 1) 8 := by
    rintro σ ⟨⟨hn, hi, hsL, hdL, hsv, hdv⟩, hiN⟩
    have hsi := hsv _ hiN
    have hsiB := hvB _ hiN
    run_vcg
    dsimp [I]
    simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr]
    simp only [show ("ac.n" : String) ≠ "ac.i" by decide, if_false, if_true,
      hne, List.length_set]
    refine ⟨⟨hn, by omega, hsL, hdL, hsv, ?_⟩, by trivial⟩
    intro z hz
    rw [getD_set _ _ _ (by omega)]
    by_cases he : z = σ.vars "ac.i"
    · subst z; rw [if_pos rfl]; exact hsi
    · rw [if_neg he]; exact hdv z (by omega)
  refine (Spec.forRangeZero "ac.i" "ac.n" I N 8 hNB
    (fun _ h => h.2.1) (fun _ h => h.1) hbody).conseq ?_ ?_ (by omega)
  · rintro σ ⟨hn, hsL, hdL, hsv⟩
    simpa [I, hn] using And.intro hsL (And.intro hdL hsv)
  · rintro σ σ' _ ⟨hI, hi⟩ z hz
    exact hI.2.2.2.2.2 z (by omega)

/-- Build offsets from the occurrence counts. -/
theorem agCsrPrefix_spec {B N M : ℕ} {ct o : String} {f : ℕ → ℕ}
    (hco : ct ≠ o) (hNB : N + 1 < B) (hMB : M + 1 < B) (hf : ∀ p, p < M → f p < N) :
    Spec B (fun σ => σ.vars "ac.n" = N ∧ N ≤ (σ.arrs ct).length ∧
        N + 1 ≤ (σ.arrs o).length ∧
        (∀ z, z < N → (σ.arrs ct).getD z 0 = peelOcc f z M))
      (agCsrPrefix ct o)
      (fun _ σ' => ∀ z, z ≤ N → (σ'.arrs o).getD z 0 = peelIOff f M z)
      (17 * N + 9) := by
  let I : Env → Prop := fun σ => σ.vars "ac.n" = N ∧ σ.vars "ac.i" ≤ N ∧
    N ≤ (σ.arrs ct).length ∧ N + 1 ≤ (σ.arrs o).length ∧
    (∀ z, z < N → (σ.arrs ct).getD z 0 = peelOcc f z M) ∧
    (∀ z, z ≤ σ.vars "ac.i" → (σ.arrs o).getD z 0 = peelIOff f M z)
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "ac.i" < N)
      (.seq (.store o (.add (.var "ac.i") (.lit 1))
          (.add (.get o (.var "ac.i")) (.get ct (.var "ac.i"))))
        (.assign "ac.i" (.add (.var "ac.i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "ac.i" = σ.vars "ac.i" + 1) 13 := by
    rintro σ ⟨⟨hn, hi, hzL, hoL, hzv, hov⟩, hiN⟩
    have hzi := hzv _ hiN
    have hoi := hov _ le_rfl
    have hsum : (σ.arrs o).getD (σ.vars "ac.i") 0 +
        (σ.arrs ct).getD (σ.vars "ac.i") 0 ≤ M := by
      rw [hoi, hzi, ← peelIOff_succ]
      exact peelIOff_le hf (by omega)
    run_vcg
    dsimp [I]
    simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr]
    simp only [show ("ac.n" : String) ≠ "ac.i" by decide, if_false, if_true,
      hco, List.length_set]
    refine ⟨⟨hn, by omega, hzL, hoL, hzv, ?_⟩, by trivial⟩
    intro z hz
    rw [getD_set _ _ _ (by omega)]
    by_cases he : z = σ.vars "ac.i" + 1
    · rw [if_pos he, he, peelIOff_succ, hoi, hzi]
    · rw [if_neg he]; exact hov z (by omega)
  have hloop := Spec.forRangeZero "ac.i" "ac.n" I N 13 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) hbody
  rintro σ ⟨hn, hzL, hoL, hzv⟩
  have h0 : Run B (.store o (.lit 0) (.lit 0)) σ (σ.setArr o 0 0) 3 :=
    Run.store (evalB_lit (by omega)) (evalB_lit (by omega)) (by omega)
  obtain ⟨σ', hr, hI, hi⟩ := hloop.run (σ := σ.setArr o 0 0) (by
    dsimp [I]
    simp only [show ("ac.n" : String) ≠ "ac.i" by decide, if_false, if_true,
      hco, List.length_set, Nat.zero_le]
    refine ⟨hn, by trivial, hzL, hoL, hzv, ?_⟩
    intro z hz
    have he : z = 0 := by omega
    subst z
    rw [getD_set _ _ _ (by omega), if_pos rfl, peelIOff_zero])
  refine ⟨σ', (h0.seq hr).mono (by omega), ?_⟩
  intro z hz
  exact hI.2.2.2.2.2 z (by omega)

/-- Count all occupied keys, using no initialized state outside the count prefix. -/
theorem agCsrCount_spec {B N M : ℕ} {ky ct : String} {key : ℕ → ℕ}
    (hkc : ky ≠ ct) (hNB : N + 1 < B) (hMB : M + 1 < B) (hSq : N * N < B)
    (hkB : ∀ p, p < M → key p < N * N) :
    Spec B (fun σ => σ.vars "ac.n" = N ∧ σ.vars "ac.m" = M ∧
        M ≤ (σ.arrs ky).length ∧ N ≤ (σ.arrs ct).length ∧
        (∀ p, p < M → (σ.arrs ky).getD p 0 = key p) ∧
        (∀ z, z < N → (σ.arrs ct).getD z 0 = 0))
      (agCsrCount ky ct)
      (fun _ σ' => ∀ z, z < N → (σ'.arrs ct).getD z 0 =
        peelOcc (fun p => key p % N) z M) (25 * M + 6) := by
  let f : ℕ → ℕ := fun p => key p % N
  let I : Env → Prop := fun σ => σ.vars "ac.n" = N ∧ σ.vars "ac.m" = M ∧
    σ.vars "ac.i" ≤ M ∧ M ≤ (σ.arrs ky).length ∧ N ≤ (σ.arrs ct).length ∧
    (∀ p, p < M → (σ.arrs ky).getD p 0 = key p) ∧
    (∀ z, z < N → (σ.arrs ct).getD z 0 = peelOcc f z (σ.vars "ac.i"))
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "ac.i" < M)
      (.seq (.assign "ac.k" (.get ky (.var "ac.i")))
        (.seq (.assign "ac.v" agCsrHead)
          (.seq (.store ct (.var "ac.v") (.add (.get ct (.var "ac.v")) (.lit 1)))
            (.assign "ac.i" (.add (.var "ac.i") (.lit 1))))))
      (fun σ σ' => I σ' ∧ σ'.vars "ac.i" = σ.vars "ac.i" + 1) 21 := by
    rintro σ ⟨⟨hn, hm, hi, hkL, hcL, hkv, hcv⟩, hiM⟩
    have hki := hkv _ hiM
    have hkiB := hkB _ hiM
    obtain ⟨huN, hvN, hdecode⟩ := agDecode hkiB
    have hmod : key (σ.vars "ac.i") - key (σ.vars "ac.i") / N * N = f (σ.vars "ac.i") := by
      dsimp [f]
      omega
    have hc : (σ.arrs ct).getD (f (σ.vars "ac.i")) 0 =
        peelOcc f (f (σ.vars "ac.i")) (σ.vars "ac.i") := hcv _ hvN
    have hcle := peelOcc_le f (f (σ.vars "ac.i")) (σ.vars "ac.i")
    unfold agCsrHead
    run_vcg
    · dsimp [I]
      simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr]
      simp only [show ("ac.n" : String) ≠ "ac.i" by decide,
        show ("ac.n" : String) ≠ "ac.v" by decide, show ("ac.n" : String) ≠ "ac.k" by decide,
        show ("ac.m" : String) ≠ "ac.i" by decide, show ("ac.m" : String) ≠ "ac.v" by decide,
        show ("ac.m" : String) ≠ "ac.k" by decide, show ("ac.i" : String) ≠ "ac.v" by decide,
        show ("ac.i" : String) ≠ "ac.k" by decide, if_false, if_true, hkc,
        List.length_set, hn, hki, hmod]
      refine ⟨⟨by trivial, hm, by omega, hkL, hcL, hkv, ?_⟩, by trivial⟩
      intro z hz
      rw [getD_set _ _ _ (by omega), peelOcc_succ]
      by_cases he : z = f (σ.vars "ac.i")
      · subst z
        rw [if_pos rfl, if_pos rfl, hcv _ hvN]
      · rw [if_neg he, if_neg (Ne.symm he)]
        exact hcv z hz
    all_goals simp [agCsrHead, hkc, hn, hki] <;>
      simp only [← List.getD_eq_getElem?_getD, hki, hn, hmod, hc] <;> omega
  refine (Spec.forRangeZero "ac.i" "ac.m" I M 21 (by omega)
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) hbody).conseq ?_ ?_ (by omega)
  · rintro σ ⟨hn, hm, hkL, hcL, hkv, hcv⟩
    simpa [I, hn, hm] using And.intro hkL (And.intro hcL (And.intro hkv hcv))
  · rintro σ σ' _ ⟨hI, hi⟩ z hz
    simpa [hi] using hI.2.2.2.2.2.2 z hz

/-- The payload-per-position scatter scans the occupied prefix once. -/
theorem agCsrScatter_spec {B N M : ℕ} {ky cu t : String} {key : ℕ → ℕ}
    (hkcu : ky ≠ cu) (hkt : ky ≠ t) (htcu : t ≠ cu)
    (hNB : N + 1 < B) (hMB : M + 1 < B) (hSq : N * N < B)
    (hkB : ∀ p, p < M → key p < N * N) :
    Spec B (fun σ => σ.vars "ac.n" = N ∧ σ.vars "ac.m" = M ∧
        M ≤ (σ.arrs ky).length ∧ N ≤ (σ.arrs cu).length ∧ M ≤ (σ.arrs t).length ∧
        (∀ p, p < M → (σ.arrs ky).getD p 0 = key p) ∧
        (∀ z, z < N → (σ.arrs cu).getD z 0 = peelIOff (fun p => key p % N) M z))
      (agCsrScatter ky cu t)
      (fun _ σ' => ∀ p, p < M →
        (σ'.arrs t).getD (peelDest (fun p => key p % N) M p) 0 = key p / N)
      (31 * M + 6) := by
  let f : ℕ → ℕ := fun p => key p % N
  have hf : ∀ p, p < M → f p < N := fun p hp => (agDecode (hkB p hp)).2.1
  let I : Env → Prop := fun σ => σ.vars "ac.n" = N ∧ σ.vars "ac.m" = M ∧
    σ.vars "ac.i" ≤ M ∧ M ≤ (σ.arrs ky).length ∧ N ≤ (σ.arrs cu).length ∧
    M ≤ (σ.arrs t).length ∧ (∀ p, p < M → (σ.arrs ky).getD p 0 = key p) ∧
    (∀ z, z < N → (σ.arrs cu).getD z 0 = peelIOff f M z + peelOcc f z (σ.vars "ac.i")) ∧
    (∀ p, p < σ.vars "ac.i" → (σ.arrs t).getD (peelDest f M p) 0 = key p / N)
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "ac.i" < M)
      (.seq (.assign "ac.k" (.get ky (.var "ac.i")))
        (.seq (.assign "ac.v" agCsrHead)
          (.seq (.store t (.get cu (.var "ac.v")) (.div (.var "ac.k") (.var "ac.n")))
            (.seq (.store cu (.var "ac.v") (.add (.get cu (.var "ac.v")) (.lit 1)))
              (.assign "ac.i" (.add (.var "ac.i") (.lit 1)))))))
      (fun σ σ' => I σ' ∧ σ'.vars "ac.i" = σ.vars "ac.i" + 1) 27 := by
    rintro σ ⟨⟨hn, hm, hi, hkL, hcL, htL, hkv, hcv, htv⟩, hiM⟩
    have hki := hkv _ hiM
    have hkiB := hkB _ hiM
    obtain ⟨huN, hvN, hdecode⟩ := agDecode hkiB
    have hmod : key (σ.vars "ac.i") - key (σ.vars "ac.i") / N * N = f (σ.vars "ac.i") := by
      dsimp [f]; omega
    have hc : (σ.arrs cu).getD (f (σ.vars "ac.i")) 0 = peelDest f M (σ.vars "ac.i") :=
      hcv _ hvN
    have hdlt := peelDest_lt hf hiM
    unfold agCsrHead
    run_vcg
    · dsimp [I]
      simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr]
      simp only [show ("ac.n" : String) ≠ "ac.i" by decide,
        show ("ac.n" : String) ≠ "ac.v" by decide, show ("ac.n" : String) ≠ "ac.k" by decide,
        show ("ac.m" : String) ≠ "ac.i" by decide, show ("ac.m" : String) ≠ "ac.v" by decide,
        show ("ac.m" : String) ≠ "ac.k" by decide, show ("ac.i" : String) ≠ "ac.v" by decide,
        show ("ac.i" : String) ≠ "ac.k" by decide, if_false, if_true, hkcu, hkt, htcu,
        Ne.symm htcu, List.length_set, hn, hki, hmod, hc]
      refine ⟨⟨by trivial, hm, by omega, hkL, hcL, htL, hkv, ?_, ?_⟩, by trivial⟩
      · intro z hz
        rw [getD_set _ _ _ (by omega), peelOcc_succ]
        by_cases he : z = f (σ.vars "ac.i")
        · subst z
          rw [if_pos rfl, if_pos rfl]
          simp [peelDest, Nat.add_assoc]
        · rw [if_neg he, if_neg (Ne.symm he), Nat.add_zero]
          exact hcv z hz
      · intro p hp
        rw [getD_set _ _ _ (by omega)]
        by_cases he : p = σ.vars "ac.i"
        · subst p
          rw [if_pos rfl]
        · have hp' : p < σ.vars "ac.i" := by omega
          have hne : peelDest f M p ≠ peelDest f M (σ.vars "ac.i") :=
            fun hd => he (peelDest_inj hf (by omega) hiM hd)
          rw [if_neg hne]
          exact htv p hp'
    all_goals simp [agCsrHead, hkcu, hkt, htcu, Ne.symm htcu, hn, hki] <;>
      simp only [← List.getD_eq_getElem?_getD, hki, hn, hmod, hc] <;> omega
  refine (Spec.forRangeZero "ac.i" "ac.m" I M 27 (by omega)
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) hbody).conseq ?_ ?_ (by omega)
  · rintro σ ⟨hn, hm, hkL, hcL, htL, hkv, hcv⟩
    simpa [I, hn, hm] using And.intro hkL (And.intro hcL (And.intro htL (And.intro hkv hcv)))
  · rintro σ σ' _ ⟨hI, hi⟩ p hp
    exact hI.2.2.2.2.2.2.2.2 p (by omega)

/-- Exactly the four arrays written by the CSR constructor. -/
theorem agCsrCom_warrs_mem (nN sz ky o t ct cu a : String) :
    a ∈ (agCsrCom nN sz ky o t ct cu).warrs ↔ a ∈ [ct, o, cu, t] := by
  simp only [agCsrCom, agCsrZero, agCsrCount, agCsrPrefix, agCsrCopy, agCsrScatter,
    Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil]
  tauto

/-- Exactly the scalar scratch cells written by the constructor. -/
theorem agCsrCom_wvars_mem (nN sz ky o t ct cu y : String) :
    y ∈ (agCsrCom nN sz ky o t ct cu).wvars ↔ y ∈ agCsrVars := by
  simp only [agCsrCom, agCsrZero, agCsrCount, agCsrPrefix, agCsrCopy, agCsrScatter,
    agCsrVars, Com.wvars, List.mem_append, List.mem_cons, List.not_mem_nil]
  tauto

private structure AgCsrSource (ky : String) (N M : ℕ) (key : ℕ → ℕ) (σ : Env) : Prop where
  n : σ.vars "ac.n" = N
  m : σ.vars "ac.m" = M
  len : M ≤ (σ.arrs ky).length
  reads : ∀ p, p < M → (σ.arrs ky).getD p 0 = key p

private theorem agCsrSource_of_run {B K N M : ℕ} {ky : String} {key : ℕ → ℕ}
    {σ τ : Env} {c : Com} (h : AgCsrSource ky N M key σ) (hr : Run B c σ τ K)
    (hn : "ac.n" ∉ c.wvars) (hm : "ac.m" ∉ c.wvars) (hk : ky ∉ c.warrs) :
    AgCsrSource ky N M key τ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr.frame_var _ hn]; exact h.n
  · rw [hr.frame_var _ hm]; exact h.m
  · rw [run_arrs_length_eq hr]; exact h.len
  · intro p hp; rw [hr.frame_arr _ hk]; exact h.reads p hp

/-- The concrete CSR constructor lands its exact stable-scatter equations,
with explicit frames and preservation of every reservation's length. -/
theorem agCsrCom_scatter_spec {B N M : ℕ} {nN sz ky o t ct cu : String} {key : ℕ → ℕ}
    (hd : [ky, o, t, ct, cu].Nodup)
    (hV : ∀ y ∈ agCsrVars, y ≠ nN ∧ y ≠ sz)
    (hNB : N + 1 < B) (hMB : M + 1 < B) (hSq : N * N < B)
    (hkB : ∀ p, p < M → key p < N * N) :
    Spec B (fun σ => σ.vars nN = N ∧ σ.vars sz = M ∧ M ≤ (σ.arrs ky).length ∧
        N + 1 ≤ (σ.arrs o).length ∧ M ≤ (σ.arrs t).length ∧
        N ≤ (σ.arrs ct).length ∧ N ≤ (σ.arrs cu).length ∧
        ∀ p, p < M → (σ.arrs ky).getD p 0 = key p)
      (agCsrCom nN sz ky o t ct cu)
      (fun σ τ =>
        (∀ z, z ≤ N → (τ.arrs o).getD z 0 = peelIOff (fun p => key p % N) M z) ∧
        (∀ p, p < M → (τ.arrs t).getD (peelDest (fun p => key p % N) M p) 0 = key p / N) ∧
        (∀ a, a ∉ [ct, o, cu, t] → τ.arrs a = σ.arrs a) ∧
        (∀ a, (τ.arrs a).length = (σ.arrs a).length) ∧
        (∀ y, y ∉ agCsrVars → τ.vars y = σ.vars y)) (agCsrK N M) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
    not_false_eq_true, and_true, List.nodup_nil] at hd
  obtain ⟨⟨hko, hkt, hkc, hkcu⟩, ⟨hot, hoc, hocu⟩, ⟨htc, htcu⟩, hccu⟩ := hd
  rintro σ ⟨hn, hm, hkL, hoL, htL, hcL, hcuL, hkeys⟩
  have hszn : sz ≠ "ac.n" := Ne.symm (hV _ (by simp [agCsrVars])).2
  have hinit : Run B
      (.seq (.assign "ac.n" (.var nN)) (.assign "ac.m" (.var sz))) σ
      ((σ.setVar "ac.n" N).setVar "ac.m" M) 4 := by
    have h1 : Run B (.assign "ac.n" (.var nN)) σ (σ.setVar "ac.n" N) 2 := by
      simpa only [hn] using Run.assign (x := "ac.n") (evalB_var (B := B) (x := nN)
        (σ := σ) (by omega))
    have h2 : Run B (.assign "ac.m" (.var sz)) (σ.setVar "ac.n" N)
        ((σ.setVar "ac.n" N).setVar "ac.m" M) 2 := by
      have hv : (σ.setVar "ac.n" N).vars sz = M := by simp [hszn, hm]
      simpa only [hv] using Run.assign (x := "ac.m") (evalB_var (B := B) (x := sz)
        (σ := σ.setVar "ac.n" N) (by rw [hv]; omega))
    exact h1.seq h2
  have hS0 : AgCsrSource ky N M key ((σ.setVar "ac.n" N).setVar "ac.m" M) := by
    constructor <;> simp_all
  obtain ⟨σ1, hr1, hz1⟩ := (agCsrZero_spec (B := B) (ct := ct) (by omega)).run
    ⟨hS0.n, hcL⟩
  have hS1 := agCsrSource_of_run hS0 hr1
    (by simp [agCsrZero, Com.wvars]) (by simp [agCsrZero, Com.wvars])
    (by simp [agCsrZero, Com.warrs, hkc])
  obtain ⟨σ2, hr2, hz2⟩ := (agCsrCount_spec hkc hNB hMB hSq hkB).run
    ⟨hS1.n, hS1.m, hS1.len, by rw [run_arrs_length_eq hr1]; exact hcL,
      hS1.reads, hz1⟩
  have hS2 := agCsrSource_of_run hS1 hr2
    (by simp [agCsrCount, Com.wvars]) (by simp [agCsrCount, Com.wvars])
    (by simp [agCsrCount, Com.warrs, hkc])
  have h12 := hr1.seq hr2
  let f : ℕ → ℕ := fun p => key p % N
  have hf : ∀ p, p < M → f p < N := fun p hp => (agDecode (hkB p hp)).2.1
  obtain ⟨σ3, hr3, ho3⟩ := (agCsrPrefix_spec (Ne.symm hoc) hNB hMB hf).run
    ⟨hS2.n, by rw [run_arrs_length_eq h12]; exact hcL,
      by rw [run_arrs_length_eq h12]; exact hoL, hz2⟩
  have hS3 := agCsrSource_of_run hS2 hr3
    (by simp [agCsrPrefix, Com.wvars]) (by simp [agCsrPrefix, Com.wvars])
    (by simp [agCsrPrefix, Com.warrs, hko])
  have h123 := hr1.seq (hr2.seq hr3)
  obtain ⟨σ4, hr4, hcu4⟩ := (agCsrCopy_spec (B := B) (N := N) (src := o) (dst := cu)
    (v := peelIOff f M) (by omega) hocu
    (fun z hz => lt_of_le_of_lt (peelIOff_le hf (by omega)) (by omega))).run
    ⟨hS3.n, by rw [run_arrs_length_eq h123]; change N ≤ (σ.arrs o).length; omega,
      by rw [run_arrs_length_eq h123]; exact hcuL, fun z hz => ho3 z (by omega)⟩
  have hS4 := agCsrSource_of_run hS3 hr4
    (by simp [Com.wvars]) (by simp [Com.wvars]) (by simp [Com.warrs, hkcu])
  have h1234 := hr1.seq (hr2.seq (hr3.seq hr4))
  obtain ⟨σ5, hr5, ht5⟩ := (agCsrScatter_spec hkcu hkt htcu hNB hMB hSq hkB).run
    ⟨hS4.n, hS4.m, hS4.len, by rw [run_arrs_length_eq h1234]; exact hcuL,
      by rw [run_arrs_length_eq h1234]; exact htL, hS4.reads, hcu4⟩
  have hr : Run B (agCsrCom nN sz ky o t ct cu) σ σ5 (agCsrK N M) :=
    (hinit.seq (hr1.seq (hr2.seq (hr3.seq (hr4.seq hr5))))).mono (by simp [agCsrK]; omega)
  refine ⟨σ5, hr, ?_, ht5, ?_, run_arrs_length_eq hr, ?_⟩
  · intro z hz
    rw [(hr4.seq hr5).frame_arr o (by simp [agCsrScatter, Com.warrs, hocu, hot])]
    exact ho3 z hz
  · intro a ha
    exact hr.frame_arr a (by simpa only [agCsrCom_warrs_mem] using ha)
  · intro y hy
    exact hr.frame_var y (by simpa only [agCsrCom_wvars_mem] using hy)

/-- Exact windows for a padded compressed-row pair. -/
def agCsrWs (o t : String) (N M : ℕ) : String → Option ℕ := fun a =>
  if a = o then some (N + 1) else if a = t then some M else none

private theorem agCsr_take_eq_arrOf {l : List ℕ} {m : ℕ} {f : ℕ → ℕ}
    (hm : m ≤ l.length) (hv : ∀ i, i < m → l.getD i 0 = f i) : l.take m = arrOf m f := by
  apply List.ext_getElem (by simp [Nat.min_eq_left hm])
  intro i hi hi'
  have him : i < m := by simpa using hi'
  simp only [List.getElem_take, getElem_arrOf]
  have h := hv i him
  rwa [Lax62Proofs.Codegen.getD_eq_getElem (lt_of_lt_of_le him hm)] at h

/-- Any padded row representation becomes the exact `GraphCsr` input after
windowing, with no copying, no changed offsets, and no additional machine work. -/
theorem AgCsrRows.graphCsr_window {N M : ℕ} {o t : String} {rows : Fin N → List (Fin N)}
    {off : ℕ → ℕ} {σ : Env} {G : SimpleGraph (Fin N)} (h : AgCsrRows o t M rows off σ)
    (hot : o ≠ t) (hnd : ∀ v, (rows v).Nodup)
    (hmem : ∀ u v, u ∈ rows v ↔ G.Adj v u) :
    FitsW (agCsrWs o t N M) σ ∧ GraphCsr o t G M (winA (agCsrWs o t N M) σ) := by
  have hwo : agCsrWs o t N M o = some (N + 1) := by simp [agCsrWs]
  have hwt : agCsrWs o t N M t = some M := by simp [agCsrWs, Ne.symm hot]
  have hcover : ∀ k, k ≤ N → ∀ p, p < off k →
      ∃ v : Fin N, off v ≤ p ∧ p < off (v + 1) := by
    intro k hk
    induction k with
    | zero => intro p hp; rw [h.off_zero] at hp; omega
    | succ k ih =>
      intro p hp
      by_cases hpk : p < off k
      · exact ih (by omega) p hpk
      · exact ⟨⟨k, by omega⟩, Nat.le_of_not_gt hpk, hp⟩
  let tgt : ℕ → ℕ := fun p => (σ.arrs t).getD p 0
  have htN : ∀ p, p < M → tgt p < N := by
    intro p hp
    obtain ⟨v, hlo, hhi⟩ := hcover N le_rfl p (by rwa [h.off_last])
    have hstep := h.off_step v
    have hi : p - off v < (rows v).length := by omega
    have ht := h.targets v (p - off v) hi
    rw [Nat.add_sub_cancel' hlo] at ht
    change (σ.arrs t).getD p 0 < N
    rw [ht]
    exact (rows v)[p - off v].isLt
  have hrow : ∀ v : Fin N, Csr.row off tgt v = (rows v).map Fin.val := by
    intro v
    have hstep := h.off_step v
    have hlen : Csr.rowLen off v = (rows v).length := by dsimp [Csr.rowLen]; omega
    apply List.ext_getElem (by simp [hlen])
    intro i hi hi'
    have hiR : i < (rows v).length := by simpa using hi'
    simp only [Csr.row, getElem_arrOf, List.getElem_map]
    exact h.targets v i hiR
  refine ⟨?_, off, tgt, ⟨?_, ?_, ?_, h.off_last, htN⟩, h.off_zero, ?_, ?_⟩
  · intro a m ha
    by_cases hao : a = o
    · subst a
      rw [hwo] at ha
      cases ha
      exact h.off_len
    · by_cases hat : a = t
      · subst a
        rw [hwt] at ha
        cases ha
        exact h.tgt_len
      · simp [agCsrWs, hao, hat] at ha
  · rw [arrs_winA_some hwo]
    exact agCsr_take_eq_arrOf h.off_len (fun i hi => h.offsets i (by omega))
  · rw [arrs_winA_some hwt]
    exact agCsr_take_eq_arrOf h.tgt_len (fun _ _ => rfl)
  · intro i hi
    exact h.mono (by omega) (by omega)
  · intro v
    rw [hrow]
    exact List.Nodup.map Fin.val_injective (hnd v)
  · intro v w
    rw [hrow, List.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.isLt, (hmem u v).mp hu⟩
    · rintro ⟨hw, hadj⟩
      exact ⟨⟨w, hw⟩, (hmem ⟨w, hw⟩ v).mpr hadj, rfl⟩

/-- The rows represent each occupied directed key exactly once. -/
structure AgCsrKeyRows {N : ℕ} (ks : List ℕ) (rows : Fin N → List (Fin N)) : Prop where
  nodup : ∀ v, (rows v).Nodup
  mem : ∀ u v, u ∈ rows v ↔ agArcKey (u, v) ∈ ks

/-- Exact key membership supplies the in-list contract used by demand scans. -/
theorem AgCsrKeyRows.inRows {N : ℕ} {ks : List ℕ} {rows : Fin N → List (Fin N)}
    {D : Orientation N} (h : AgCsrKeyRows ks rows)
    (hD : ∀ u v, agArcKey (u, v) ∈ ks ↔ u ∈ D.inN v) : AgInRows D rows := by
  refine ⟨h.nodup, ?_⟩
  intro v
  ext u
  rw [List.mem_toFinset]
  exact (h.mem u v).trans (hD u v)

/-- CSR from an arbitrary distinct occupied prefix. The output arrays and
scratch need only the listed reservations; their initial contents are arbitrary. -/
theorem agCsrCom_spec {B N : ℕ} {nN sz ky o t ct cu : String} {ks : List ℕ}
    (hd : [ky, o, t, ct, cu].Nodup)
    (hV : ∀ y ∈ agCsrVars, y ≠ nN ∧ y ≠ sz)
    (hNB : N + 1 < B) (hMB : ks.length + 1 < B) (hSq : N * N < B)
    (hdup : ks.Nodup) (hkeys : ∀ k ∈ ks, k < N * N) :
    Spec B (fun σ => σ.vars nN = N ∧ σ.vars sz = ks.length ∧
        ks.length ≤ (σ.arrs ky).length ∧ N + 1 ≤ (σ.arrs o).length ∧
        ks.length ≤ (σ.arrs t).length ∧ N ≤ (σ.arrs ct).length ∧ N ≤ (σ.arrs cu).length ∧
        ∀ p, p < ks.length → (σ.arrs ky).getD p 0 = ks.getD p 0)
      (agCsrCom nN sz ky o t ct cu)
      (fun σ τ => (∃ (rows : Fin N → List (Fin N)) (off : ℕ → ℕ), AgCsrRows o t ks.length rows off τ ∧ AgCsrKeyRows ks rows) ∧
        (∀ a, a ∉ [ct, o, cu, t] → τ.arrs a = σ.arrs a) ∧
        (∀ a, (τ.arrs a).length = (σ.arrs a).length) ∧
        (∀ y, y ∉ agCsrVars → τ.vars y = σ.vars y)) (agCsrK N ks.length) := by
  let key : ℕ → ℕ := fun p => ks.getD p 0
  have hkB : ∀ p, p < ks.length → key p < N * N := by
    intro p hp
    dsimp [key]
    rw [Lax62Proofs.Codegen.getD_eq_getElem hp]
    exact hkeys _ (List.getElem_mem _)
  have hpair : ∀ p q, p < ks.length → q < ks.length → key p % N = key q % N →
      key p / N = key q / N → p = q := by
    intro p q hp hq hmod hdiv
    have hpdec := (agDecode (hkB p hp)).2.2
    have hqdec := (agDecode (hkB q hq)).2.2
    have hkey : key p = key q := by rw [hmod, hdiv] at hpdec; omega
    dsimp [key] at hkey
    rw [Lax62Proofs.Codegen.getD_eq_getElem hp, Lax62Proofs.Codegen.getD_eq_getElem hq] at hkey
    exact hdup.getElem_inj_iff.mp hkey
  intro σ hσ
  obtain ⟨τ, hr, ho, ht, hfa, hlen, hfv⟩ :=
    (agCsrCom_scatter_spec hd hV hNB hMB hSq hkB).run hσ
  obtain ⟨rows, hcsr, hnd, hmem⟩ := agCsrRows_of_scatter
    (fun p hp => (agDecode (hkB p hp)).2.1) (fun p hp => (agDecode (hkB p hp)).1)
    hpair (by rw [hlen]; exact hσ.2.2.2.1) (by rw [hlen]; exact hσ.2.2.2.2.1) ho ht
  refine ⟨τ, hr, ⟨rows, _, hcsr, ⟨hnd, ?_⟩⟩, hfa, hlen, hfv⟩
  intro u v
  rw [hmem]
  constructor
  · rintro ⟨p, hp, hv, hu⟩
    have hdec := (agDecode (hkB p hp)).2.2
    have hkey : agArcKey (u, v) = key p := by
      rw [hv, hu] at hdec
      exact hdec
    rw [hkey]
    dsimp [key]
    rw [Lax62Proofs.Codegen.getD_eq_getElem hp]
    exact List.getElem_mem _
  · intro hkey
    obtain ⟨p, hp, he⟩ := List.mem_iff_getElem.mp hkey
    have he' : key p = agArcKey (u, v) := by
      dsimp [key]
      rw [Lax62Proofs.Codegen.getD_eq_getElem hp]
      exact he
    obtain ⟨huN, hvN, hdec⟩ := agDecode (hkB p hp)
    have hsplit := agSplit hvN v.isLt (hdec.trans he')
    exact ⟨p, hp, hsplit.2, hsplit.1⟩

/-- Dictionary specialization: the source dictionary itself is preserved.
The inverse table is never consulted by the CSR program. -/
theorem agCsrCom_dict_spec {B N : ℕ} {nN sz ix ky o t ct cu : String} {ks : List ℕ}
    (hd : [ky, o, t, ct, cu].Nodup) (hix : ix ∉ [ct, o, cu, t])
    (hV : ∀ y ∈ agCsrVars, y ≠ nN ∧ y ≠ sz)
    (hNB : N + 1 < B) (hMB : ks.length + 1 < B) (hSq : N * N < B) :
    Spec B (fun σ => AgDictSt ix ky sz B (N * N) ks σ ∧ σ.vars nN = N ∧
        N + 1 ≤ (σ.arrs o).length ∧ ks.length ≤ (σ.arrs t).length ∧
        N ≤ (σ.arrs ct).length ∧ N ≤ (σ.arrs cu).length)
      (agCsrCom nN sz ky o t ct cu)
      (fun σ τ => AgDictSt ix ky sz B (N * N) ks τ ∧
        (∃ (rows : Fin N → List (Fin N)) (off : ℕ → ℕ), AgCsrRows o t ks.length rows off τ ∧ AgCsrKeyRows ks rows) ∧
        (∀ a, a ∉ [ct, o, cu, t] → τ.arrs a = σ.arrs a) ∧
        (∀ a, (τ.arrs a).length = (σ.arrs a).length) ∧
        (∀ y, y ∉ agCsrVars → τ.vars y = σ.vars y)) (agCsrK N ks.length) := by
  rintro σ ⟨hD, hn, ho, ht, hc, hcu⟩
  obtain ⟨τ, hr, hrows, hfa, hlen, hfv⟩ :=
    (agCsrCom_spec hd hV hNB hMB hSq hD.nodup hD.key_lt).run
      ⟨hn, hD.size, hD.length_le.trans hD.ky_len, ho, ht, hc, hcu, hD.keys⟩
  have hky : ky ∉ [ct, o, cu, t] := by
    have h := (List.nodup_cons.mp hd).1
    simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true] at h ⊢
    tauto
  have hsz : sz ∉ agCsrVars := by
    intro hm
    exact (hV sz hm).2 rfl
  exact ⟨τ, hr, hD.of_eq (hfa ix hix) (hfa ky hky) (hfv sz hsz), hrows, hfa, hlen, hfv⟩

/-- The graph corresponding to a symmetric loopless directed-key relation. -/
def agCsrKeyGraph {N : ℕ} (ks : List ℕ)
    (hsym : ∀ u v : Fin N, agArcKey (u, v) ∈ ks → agArcKey (v, u) ∈ ks)
    (hloop : ∀ v : Fin N, agArcKey (v, v) ∉ ks) : SimpleGraph (Fin N) where
  Adj v u := agArcKey (u, v) ∈ ks
  symm v u h := hsym u v h
  loopless := ⟨hloop⟩

/-- The padded key rows feed the exact graph-CSR seam for any represented
simple graph, including the filtered symmetric fraternity relation. -/
theorem AgCsrKeyRows.graphCsr_window {N M : ℕ} {o t : String} {ks : List ℕ}
    {rows : Fin N → List (Fin N)} {off : ℕ → ℕ} {σ : Env} {G : SimpleGraph (Fin N)}
    (hk : AgCsrKeyRows ks rows) (hc : AgCsrRows o t M rows off σ) (hot : o ≠ t)
    (hG : ∀ u v, agArcKey (u, v) ∈ ks ↔ G.Adj v u) :
    FitsW (agCsrWs o t N M) σ ∧ GraphCsr o t G M (winA (agCsrWs o t N M) σ) :=
  hc.graphCsr_window hot hk.nodup (fun u v => (hk.mem u v).trans (hG u v))

/-- The three word-room conditions are supplied by the fixed quadratic bound
for every encoded input; the schedule's constant needs only `1 ≤ q`. -/
theorem agCsr_word_room {N n M q : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (henc : Lax11.GraphEncoding.EncodesGraph x n G) (hN : N ≤ n) (hM : M ≤ N * N)
    (hq : 1 ≤ q) : N + 1 < mcB q x ∧ M + 1 < mcB q x ∧ N * N < mcB q x := by
  have hnx : n + 3 ≤ x.length := by
    have := henc.length_eq
    have := henc.vertexCount_eq
    omega
  have hbase : (x.length + 1) ^ 2 ≤ mcB q x := Nat.le_mul_of_pos_left _ hq
  have hsq : N * N + 1 < (x.length + 1) ^ 2 := by nlinarith
  have hlinear : N + 1 < (x.length + 1) ^ 2 := by nlinarith
  exact ⟨hlinear.trans_le hbase, by omega, by omega⟩

/-- The exact graph-CSR input also supplies explicit finite row lists. This
pure bridge starts occupied-key extraction from the initial arena CSR. -/
theorem graphCsr_agCsrRows {N M : ℕ} {o t : String} {G : SimpleGraph (Fin N)} {σ : Env}
    (hG : GraphCsr o t G M σ) :
    ∃ (rows : Fin N → List (Fin N)) (off : ℕ → ℕ),
      AgCsrRows o t M rows off σ ∧ (∀ v, (rows v).Nodup) ∧
      ∀ u v, u ∈ rows v ↔ G.Adj v u := by
  obtain ⟨off, tgt, hc, h0, hnd, hmem⟩ := hG
  have hslot : ∀ (v : Fin N) (i : Fin (Csr.rowLen off v)), off v + i < M := by
    intro v i
    have hm := hc.off_le_succ v.isLt
    have hM := hc.row_le v.isLt
    have hi := i.isLt
    dsimp [Csr.rowLen] at hi
    omega
  let entry (v : Fin N) (i : Fin (Csr.rowLen off v)) : Fin N :=
    ⟨tgt (off v + i), hc.target (hslot v i)⟩
  let rows (v : Fin N) : List (Fin N) := List.ofFn (entry v)
  have hrow : ∀ v : Fin N, (rows v).map Fin.val = Csr.row off tgt v := by
    intro v
    apply List.ext_getElem (by simp [rows])
    intro i hi hi'
    simp only [rows, List.getElem_map, List.getElem_ofFn, entry, Csr.row, getElem_arrOf]
  refine ⟨rows, off, ⟨h0, ?_, hc.last, by rw [hc.length_off], by rw [hc.length_tgt],
    fun i hi => hc.getD_off hi, ?_⟩, ?_, ?_⟩
  · intro v
    have hm := hc.off_le_succ v.isLt
    simp only [rows, List.length_ofFn, Csr.rowLen]
    omega
  · intro v i hi
    have hi' : i < Csr.rowLen off v := by simpa [rows] using hi
    simpa only [rows, List.getElem_ofFn, entry] using hc.getD_tgt (hslot v ⟨i, hi'⟩)
  · intro v
    apply List.Nodup.of_map Fin.val
    rw [hrow]
    exact hnd v
  · intro u v
    rw [← List.mem_map_of_injective Fin.val_injective, hrow, hmem]
    constructor
    · rintro ⟨hu, hadj⟩
      exact hadj
    · intro hadj
      exact ⟨u.isLt, hadj⟩

end Lax3Proofs.Prog
