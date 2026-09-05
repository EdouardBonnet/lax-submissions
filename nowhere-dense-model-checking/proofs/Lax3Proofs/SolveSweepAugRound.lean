import Lax3Proofs.SolveSweepAugStepScan

/-!
# A complete sparse greedy augmentation round

Three occupied dictionary prefixes suffice: old arcs, transitive demands and
fraternal demands. The command filters each prefix through the exact greedy
decision and inserts accepted keys into a fresh sparse dictionary.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax3Proofs.Augmentation Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.CoverRoutine

/-- Static names for one sparse greedy round. -/
structure AgsRoundNames where
  oi : String
  ok : String
  os : String
  ti : String
  tk : String
  ts : String
  fi : String
  fk : String
  fs : String
  nN : String
  kf : String
  kr : String
  tmp : String
  ofv : String
  orv : String
  tfv : String
  trv : String
  ffv : String
  ra : String
  uv : String
  vv : String
  ans : String
  ix : String
  ky : String
  sz : String
  tv : String
  hv : String
  iv : String
  lm : String

def AgsRoundNames.vars (a : AgsRoundNames) : List String :=
  [a.os, a.ts, a.fs, a.kf, a.kr, a.tmp, a.ofv, a.orv, a.tfv, a.trv, a.ffv, a.uv, a.vv,
    a.ans, a.nN, a.sz, a.tv, a.hv, a.iv, a.lm]

def AgsRoundNames.arrays (a : AgsRoundNames) : List String :=
  [a.oi, a.ok, a.ti, a.tk, a.fi, a.fk, a.ra, a.ix, a.ky]

def AgsRoundNames.readArrays (a : AgsRoundNames) : List String :=
  [a.oi, a.ok, a.ti, a.tk, a.fi, a.fk, a.ra]

def AgsRoundNames.written (a : AgsRoundNames) : List String :=
  [a.sz, a.kf, a.tv, a.hv, a.iv, a.lm, a.kr, a.tmp, a.ofv, a.orv, a.tfv, a.trv, a.ffv,
    a.uv, a.vv, a.ans]

structure AgsRoundNames.WellNamed (a : AgsRoundNames) : Prop where
  vars : a.vars.Nodup
  arrays : a.arrays.Nodup

private theorem agrName_ne {xs : List String} (h : xs.Nodup) (i j : ℕ)
    (hi : i < xs.length) (hj : j < xs.length) (hne : i ≠ j) :
    xs[i] ≠ xs[j] := fun he => hne (h.getElem_inj_iff.mp he)

theorem AgsRoundNames.WellNamed.out_ne {a : AgsRoundNames} (h : a.WellNamed) : a.ix ≠ a.ky :=
  agrName_ne h.arrays 7 8 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide)

theorem AgsRoundNames.WellNamed.read_ne_out {a : AgsRoundNames} (h : a.WellNamed)
    {s : String} (hs : s ∈ a.readArrays) : s ≠ a.ix ∧ s ≠ a.ky := by
  simp only [readArrays, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨agrName_ne h.arrays 0 7 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide),
      agrName_ne h.arrays 0 8 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide)⟩
  · exact ⟨agrName_ne h.arrays 1 7 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide),
      agrName_ne h.arrays 1 8 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide)⟩
  · exact ⟨agrName_ne h.arrays 2 7 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide),
      agrName_ne h.arrays 2 8 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide)⟩
  · exact ⟨agrName_ne h.arrays 3 7 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide),
      agrName_ne h.arrays 3 8 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide)⟩
  · exact ⟨agrName_ne h.arrays 4 7 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide),
      agrName_ne h.arrays 4 8 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide)⟩
  · exact ⟨agrName_ne h.arrays 5 7 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide),
      agrName_ne h.arrays 5 8 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide)⟩
  · exact ⟨agrName_ne h.arrays 6 7 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide),
      agrName_ne h.arrays 6 8 (by simp [AgsRoundNames.arrays]) (by simp [AgsRoundNames.arrays]) (by decide)⟩

/-- The three source dictionaries, with no information hidden in scratch flags. -/
structure AgsRoundSt (a : AgsRoundNames) (B : ℕ) {N : ℕ} (D : Orientation N)
    (rank : Fin N → ℕ) (oks tks fks : List ℕ) (σ : Env) : Prop where
  old : AgDictSt a.oi a.ok a.os B (N * N) oks σ
  trans : AgDictSt a.ti a.tk a.ts B (N * N) tks σ
  frat : AgDictSt a.fi a.fk a.fs B (N * N) fks σ
  nval : σ.vars a.nN = N
  rank_len : N ≤ (σ.arrs a.ra).length
  rank_val : ∀ v : Fin N, (σ.arrs a.ra).getD v 0 = rank v

def AgsRoundNames.sourceI (a : AgsRoundNames) (t : Fin 3) : String :=
  if t = 0 then a.oi else if t = 1 then a.ti else a.fi

def AgsRoundNames.sourceK (a : AgsRoundNames) (t : Fin 3) : String :=
  if t = 0 then a.ok else if t = 1 then a.tk else a.fk

def AgsRoundNames.sourceS (a : AgsRoundNames) (t : Fin 3) : String :=
  if t = 0 then a.os else if t = 1 then a.ts else a.fs

def agsSourceKeys (oks tks fks : List ℕ) (t : Fin 3) : List ℕ :=
  if t = 0 then oks else if t = 1 then tks else fks

theorem AgsRoundNames.sourceK_mem (a : AgsRoundNames) (t : Fin 3) :
    a.sourceK t ∈ a.readArrays := by
  fin_cases t <;> simp [sourceK, readArrays]

theorem AgsRoundSt.source {a : AgsRoundNames} {B N : ℕ} {D : Orientation N}
    {rank : Fin N → ℕ} {oks tks fks : List ℕ} {σ : Env}
    (h : AgsRoundSt a B D rank oks tks fks σ) (t : Fin 3) :
    AgDictSt (a.sourceI t) (a.sourceK t) (a.sourceS t) B (N * N) (agsSourceKeys oks tks fks t) σ := by
  fin_cases t <;> simp only [AgsRoundNames.sourceI, AgsRoundNames.sourceK, AgsRoundNames.sourceS,
    agsSourceKeys, Fin.isValue, ↓reduceIte, Fin.zero_eta]
  · exact h.old
  · exact h.trans
  · exact h.frat

theorem AgsRoundNames.WellNamed.read_not_written {a : AgsRoundNames} (h : a.WellNamed)
    {s : String} (hs : s ∈ [a.os, a.ts, a.fs, a.nN]) : s ∉ a.written := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · simp only [written, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨agrName_ne h.vars 0 15 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 3 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 16 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 17 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 18 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 19 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 4 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 5 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 6 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 7 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 8 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 9 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 10 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 11 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 12 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 0 13 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide)⟩
  · simp only [written, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨agrName_ne h.vars 1 15 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 3 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 16 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 17 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 18 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 19 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 4 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 5 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 6 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 7 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 8 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 9 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 10 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 11 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 12 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 1 13 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide)⟩
  · simp only [written, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨agrName_ne h.vars 2 15 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 3 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 16 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 17 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 18 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 19 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 4 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 5 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 6 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 7 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 8 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 9 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 10 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 11 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 12 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 2 13 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide)⟩
  · simp only [written, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨agrName_ne h.vars 14 15 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 3 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 16 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 17 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 18 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 19 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 4 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 5 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 6 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 7 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 8 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 9 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 10 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 11 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 12 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide),
      agrName_ne h.vars 14 13 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide)⟩

theorem AgsRoundSt.of_frame {a : AgsRoundNames} {B N : ℕ} {D : Orientation N}
    {rank : Fin N → ℕ} {oks tks fks : List ℕ} {σ τ : Env}
    (h : AgsRoundSt a B D rank oks tks fks σ) (hn : a.WellNamed)
    (hv : AgFilterVars a.written σ τ)
    (ha : ∀ s, s ≠ a.ix → s ≠ a.ky → τ.arrs s = σ.arrs s) :
    AgsRoundSt a B D rank oks tks fks τ := by
  have har : ∀ s ∈ a.readArrays, τ.arrs s = σ.arrs s :=
    fun s hs => ha s (hn.read_ne_out hs).1 (hn.read_ne_out hs).2
  have hvr : ∀ s ∈ [a.os, a.ts, a.fs, a.nN], τ.vars s = σ.vars s :=
    fun s hs => hv s (hn.read_not_written hs)
  refine ⟨h.old.of_eq (har a.oi (by simp [AgsRoundNames.readArrays]))
      (har a.ok (by simp [AgsRoundNames.readArrays])) (hvr a.os (by simp)),
    h.trans.of_eq (har a.ti (by simp [AgsRoundNames.readArrays]))
      (har a.tk (by simp [AgsRoundNames.readArrays])) (hvr a.ts (by simp)),
    h.frat.of_eq (har a.fi (by simp [AgsRoundNames.readArrays]))
      (har a.fk (by simp [AgsRoundNames.readArrays])) (hvr a.fs (by simp)),
    (hvr a.nN (by simp)).trans h.nval, ?_, ?_⟩
  · rw [har a.ra (by simp [AgsRoundNames.readArrays])]
    exact h.rank_len
  · intro v
    rw [har a.ra (by simp [AgsRoundNames.readArrays])]
    exact h.rank_val v

/-- Load one occupied prefix length, then filter exactly that many keys. -/
def agsRoundFrom (a : AgsRoundNames) (t : Fin 3) : Com :=
  .seq (.assign a.lm (.var (a.sourceS t)))
    (agsGreedyScan a.oi a.ok a.os a.ti a.tk a.ts a.fi a.fk a.fs a.nN a.kf a.kr a.tmp
      a.ofv a.orv a.tfv a.trv a.ffv a.ra a.uv a.vv a.ans a.ix a.ky a.sz a.tv a.hv a.iv a.lm
      (a.sourceK t))

set_option maxHeartbeats 600000 in
theorem agsRoundFrom_run {B N : ℕ} (a : AgsRoundNames) (hnames : a.WellNamed)
    (D : Orientation N) (rank : Fin N → ℕ) (hRank : ∀ v, rank v < N)
    (hNB : N + 1 < B) (hNNB : N * N < B) (oks tks fks ks : List ℕ)
    (hOld : ∀ u v : Fin N, agArcKey (u, v) ∈ oks ↔ u ∈ D.inN v)
    (hTrans : ∀ u v : Fin N, agArcKey (u, v) ∈ tks ↔ TransLink D u v)
    (hFrat : ∀ u v : Fin N, agArcKey (u, v) ∈ fks ↔ FratLink D u v)
    (σ : Env) (hIn : AgsRoundSt a B D rank oks tks fks σ)
    (hOut : AgDictSt a.ix a.ky a.sz B (N * N) ks σ) (t : Fin 3) :
    ∃ τ, Run B (agsRoundFrom a t) σ τ (229 * (agsSourceKeys oks tks fks t).length + 8) ∧
      AgsRoundSt a B D rank oks tks fks τ ∧
      AgDictSt a.ix a.ky a.sz B (N * N)
        (agFilterPart ks (agsSourceKeys oks tks fks t) (AgArcPred (greedyStep rank D))
          (agsSourceKeys oks tks fks t).length) τ ∧
      AgFilterVars a.written σ τ ∧
      (∀ s, s ≠ a.ix → s ≠ a.ky → τ.arrs s = σ.arrs s) ∧
      (∀ s, (τ.arrs s).length = (σ.arrs s).length) := by
  let xs := agsSourceKeys oks tks fks t
  have hSrc := hIn.source t
  have hxsB : xs.length < B := lt_of_le_of_lt hSrc.length_le hNNB
  let ρ := σ.setVar a.lm xs.length
  have hload : Run B (.assign a.lm (.var (a.sourceS t))) σ ρ 2 := by
    apply Run.assign
    rw [← hSrc.size]
    exact evalB_var (by rw [hSrc.size]; exact hxsB)
  have hvl : AgFilterVars a.written σ ρ := by
    intro y hy
    have hym : y ≠ a.lm := fun he => hy (he ▸ (by simp [AgsRoundNames.written]))
    simp [ρ, hym]
  have hInρ := hIn.of_frame hnames hvl (fun _ _ _ => rfl)
  have hs_l : a.sz ≠ a.lm :=
    agrName_ne hnames.vars 15 19 (by simp [AgsRoundNames.vars]) (by simp [AgsRoundNames.vars]) (by decide)
  have hOutρ := hOut.of_eq (τ := ρ) rfl rfl (by simp [ρ, hs_l])
  have hSrcρ := hInρ.source t
  have hread : ∀ s ∈ [a.oi, a.ok, a.ti, a.tk, a.fi, a.fk, a.ra, a.sourceK t], s ≠ a.ix ∧ s ≠ a.ky := by
    intro s hs
    apply hnames.read_ne_out
    change s ∈ a.readArrays ++ [a.sourceK t] at hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hs
    · rw [List.mem_singleton] at hs
      rw [hs]
      exact a.sourceK_mem t
  obtain ⟨τ, hscan, hD, hv, ha, hl⟩ :=
    agsGreedyScan_run D rank a.oi a.ok a.os a.ti a.tk a.ts a.fi a.fk a.fs a.nN a.kf a.kr a.tmp
      a.ofv a.orv a.tfv a.trv a.ffv a.ra a.uv a.vv a.ans a.ix a.ky a.sz a.tv a.hv a.iv a.lm
      (a.sourceK t) hnames.vars hnames.out_ne hread hNB hNNB hRank oks tks fks ks xs
      hOld hTrans hFrat ρ hInρ.old hInρ.trans hInρ.frat hOutρ hInρ.nval hInρ.rank_len hInρ.rank_val
      hxsB (by simp [ρ]) (le_trans hSrcρ.length_le hSrcρ.ky_len) hSrcρ.keys hSrcρ.key_lt
  have hv' : AgFilterVars a.written ρ τ := by
    intro y hy
    apply hv y
    simp only [AgsRoundNames.written, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    tauto
  refine ⟨τ, (hload.seq hscan).mono (by dsimp only [xs]; omega), hInρ.of_frame hnames hv' ha, hD,
    fun y hy => (hv' y hy).trans (hvl y hy), ha, hl⟩

/-- The concrete list left by the three sparse filters. -/
noncomputable def agsRoundKeys {N : ℕ} (D : Orientation N) (rank : Fin N → ℕ)
    (oks tks fks : List ℕ) : List ℕ :=
  let P := AgArcPred (greedyStep rank D)
  agFilterPart (agFilterPart (agFilterPart [] oks P oks.length) tks P tks.length) fks P fks.length

/-- Old arcs and both kinds of actual demand cover every output arc. -/
theorem agsRoundKeys_mem {N : ℕ} (D : Orientation N) (rank : Fin N → ℕ)
    (oks tks fks : List ℕ)
    (hOld : ∀ u v : Fin N, agArcKey (u, v) ∈ oks ↔ u ∈ D.inN v)
    (hTrans : ∀ u v : Fin N, agArcKey (u, v) ∈ tks ↔ TransLink D u v)
    (hFrat : ∀ u v : Fin N, agArcKey (u, v) ∈ fks ↔ FratLink D u v)
    (u v : Fin N) :
    agArcKey (u, v) ∈ agsRoundKeys D rank oks tks fks ↔ u ∈ (greedyStep rank D).inN v := by
  have hcover : u ∈ (greedyStep rank D).inN v →
      agArcKey (u, v) ∈ oks ∨ agArcKey (u, v) ∈ tks ∨ agArcKey (u, v) ∈ fks := by
    intro hu
    rcases mem_greedyStep.mp hu with hold | hadd
    · exact Or.inl ((hOld u v).mpr hold)
    · rcases hadd.2.1 with ht | hf
      · exact Or.inr (Or.inl ((hTrans u v).mpr ht))
      · exact Or.inr (Or.inr ((hFrat u v).mpr hf))
  simp only [agsRoundKeys, agFilterPart_mem, List.take_length, List.not_mem_nil,
    false_or, agArcPred_key]
  tauto

/-- Empty the output sparse set, then scan the three occupied input prefixes. -/
def agsGreedyRound (a : AgsRoundNames) : Com :=
  .seq (.assign a.sz (.lit 0))
    (.seq (agsRoundFrom a 0) (.seq (agsRoundFrom a 1) (agsRoundFrom a 2)))

set_option maxHeartbeats 600000 in
/-- The complete greedy orientation phase. It uses no precomputed decision
flags, preserves all input dictionaries and ranks, and costs only the three
occupied input lengths. The stale inverse-table word condition is explicit. -/
theorem agsGreedyRound_run {B N : ℕ} (a : AgsRoundNames) (hnames : a.WellNamed)
    (D : Orientation N) (rank : Fin N → ℕ) (hRank : ∀ v, rank v < N)
    (hNB : N + 1 < B) (hNNB : N * N < B) (oks tks fks : List ℕ)
    (hOld : ∀ u v : Fin N, agArcKey (u, v) ∈ oks ↔ u ∈ D.inN v)
    (hTrans : ∀ u v : Fin N, agArcKey (u, v) ∈ tks ↔ TransLink D u v)
    (hFrat : ∀ u v : Fin N, agArcKey (u, v) ∈ fks ↔ FratLink D u v)
    (σ : Env) (hIn : AgsRoundSt a B D rank oks tks fks σ)
    (hix : N * N ≤ (σ.arrs a.ix).length) (hky : N * N ≤ (σ.arrs a.ky).length)
    (hwords : ∀ k < N * N, (σ.arrs a.ix).getD k 0 < B) :
    ∃ τ, Run B (agsGreedyRound a) σ τ (229 * (oks.length + tks.length + fks.length) + 26) ∧
      AgsRoundSt a B D rank oks tks fks τ ∧
      AgDictSt a.ix a.ky a.sz B (N * N) (agsRoundKeys D rank oks tks fks) τ ∧
      (∀ u v : Fin N, agArcKey (u, v) ∈ agsRoundKeys D rank oks tks fks ↔
        u ∈ (greedyStep rank D).inN v) ∧
      AgFilterVars a.written σ τ ∧
      (∀ s, s ≠ a.ix → s ≠ a.ky → τ.arrs s = σ.arrs s) ∧
      (∀ s, (τ.arrs s).length = (σ.arrs s).length) := by
  obtain ⟨hinit, hD0⟩ := agDictInit_run a.ix a.ky a.sz σ (by omega) hix hky hwords
  let ρ₀ := σ.setVar a.sz 0
  have hf0 : AgFilterVars a.written σ ρ₀ := by
    intro y hy
    have hys : y ≠ a.sz := fun he => hy (he ▸ (by simp [AgsRoundNames.written]))
    simp [ρ₀, hys]
  have hI0 := hIn.of_frame hnames hf0 (fun _ _ _ => rfl)
  obtain ⟨ρ₁, h1, hI1, hD1, hf1, ha1, hl1⟩ :=
    agsRoundFrom_run a hnames D rank hRank hNB hNNB oks tks fks [] hOld hTrans hFrat ρ₀ hI0 hD0 0
  obtain ⟨ρ₂, h2, hI2, hD2, hf2, ha2, hl2⟩ :=
    agsRoundFrom_run a hnames D rank hRank hNB hNNB oks tks fks _ hOld hTrans hFrat ρ₁ hI1 hD1 1
  obtain ⟨τ, h3, hI3, hD3, hf3, ha3, hl3⟩ :=
    agsRoundFrom_run a hnames D rank hRank hNB hNNB oks tks fks _ hOld hTrans hFrat ρ₂ hI2 hD2 2
  refine ⟨τ, (hinit.seq (h1.seq (h2.seq h3))).mono ?_, hI3, ?_,
    agsRoundKeys_mem D rank oks tks fks hOld hTrans hFrat, ?_, ?_, ?_⟩
  · simp only [agsSourceKeys, show (1 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
    omega
  · simpa only [agsSourceKeys, Fin.isValue, ↓reduceIte, Fin.zero_eta] using hD3
  · intro y hy
    exact (hf3 y hy).trans ((hf2 y hy).trans ((hf1 y hy).trans (hf0 y hy)))
  · intro s hsi hsk
    exact (ha3 s hsi hsk).trans ((ha2 s hsi hsk).trans (ha1 s hsi hsk))
  · intro s
    exact (hl3 s).trans ((hl2 s).trans (hl1 s))

/-- A unique occupied prefix is no longer than any complete witness stream.
Only the occupied keys are counted; reserved capacity plays no part. -/
theorem agsDict_length_le_candidates {B N : ℕ} {ix ky sz : String} {ks : List ℕ} {σ : Env}
    (hD : AgDictSt ix ky sz B (N * N) ks σ) (ps : List (Fin N × Fin N))
    (hcover : ∀ u v : Fin N, agArcKey (u, v) ∈ ks → (u, v) ∈ ps) :
    ks.length ≤ ps.length := by
  classical
  have hsub : ks.toFinset ⊆ (ps.map agArcKey).toFinset := by
    intro k hk
    have hkm := List.mem_toFinset.mp hk
    have hd := agDecode (hD.key_lt k hkm)
    let u : Fin N := ⟨k / N, hd.1⟩
    let v : Fin N := ⟨k % N, hd.2.1⟩
    have hkey : agArcKey (u, v) = k := hd.2.2
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨(u, v), hcover u v (hkey ▸ hkm), hkey⟩)
  calc
    ks.length = ks.toFinset.card := (List.toFinset_card_of_nodup hD.nodup).symm
    _ ≤ (ps.map agArcKey).toFinset.card := Finset.card_le_card hsub
    _ ≤ (ps.map agArcKey).length := List.toFinset_card_le _
    _ = ps.length := List.length_map _

/-- The three dictionary lengths are bounded by the actual sparse charges,
independently of the particular row order or deduplication history. -/
theorem AgsRoundSt.sparse_lengths {a : AgsRoundNames} {B N : ℕ} {D : Orientation N}
    {rank : Fin N → ℕ} {oks tks fks : List ℕ} {σ : Env}
    (h : AgsRoundSt a B D rank oks tks fks σ)
    (hOld : ∀ u v : Fin N, agArcKey (u, v) ∈ oks ↔ u ∈ D.inN v)
    (hTrans : ∀ u v : Fin N, agArcKey (u, v) ∈ tks ↔ TransLink D u v)
    (hFrat : ∀ u v : Fin N, agArcKey (u, v) ∈ fks ↔ FratLink D u v) :
    oks.length ≤ arcCount D ∧ tks.length ≤ transPairCount D ∧ fks.length ≤ fratPairCount D := by
  classical
  let rows := fun v => (D.inN v).toList
  have hrows : AgInRows D rows := ⟨fun _ => Finset.nodup_toList _, fun _ => Finset.toList_toFinset _⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← agArcCandidates_length hrows]
    exact agsDict_length_le_candidates h.old (agArcCandidates rows)
      (fun u v hk => (agArcCandidates_mem hrows u v).mpr ((hOld u v).mp hk))
  · rw [← agTransCandidates_length hrows]
    exact agsDict_length_le_candidates h.trans (agTransCandidates rows)
      (fun u v hk => (agTransCandidates_mem hrows u v).mpr ((hTrans u v).mp hk))
  · rw [← agFratCandidates_length hrows]
    exact agsDict_length_le_candidates h.frat (agFratCandidates rows)
      (fun u v hk => (agFratCandidates_mem hrows u v).mpr ((hFrat u v).mp hk))

/-- The source-faithful sparse budget for the orientation phase. The min-degree
peel used to compute `rank` is separate and must retain its own logarithm. -/
def agsGreedyCost {N : ℕ} (D : Orientation N) : ℕ :=
  229 * (arcCount D + transPairCount D + fratPairCount D) + 26

theorem agsGreedyRound_sparse_run {B N : ℕ} (a : AgsRoundNames) (hnames : a.WellNamed)
    (D : Orientation N) (rank : Fin N → ℕ) (hRank : ∀ v, rank v < N)
    (hNB : N + 1 < B) (hNNB : N * N < B) (oks tks fks : List ℕ)
    (hOld : ∀ u v : Fin N, agArcKey (u, v) ∈ oks ↔ u ∈ D.inN v)
    (hTrans : ∀ u v : Fin N, agArcKey (u, v) ∈ tks ↔ TransLink D u v)
    (hFrat : ∀ u v : Fin N, agArcKey (u, v) ∈ fks ↔ FratLink D u v)
    (σ : Env) (hIn : AgsRoundSt a B D rank oks tks fks σ)
    (hix : N * N ≤ (σ.arrs a.ix).length) (hky : N * N ≤ (σ.arrs a.ky).length)
    (hwords : ∀ k < N * N, (σ.arrs a.ix).getD k 0 < B) :
    ∃ τ, Run B (agsGreedyRound a) σ τ (agsGreedyCost D) ∧
      AgsRoundSt a B D rank oks tks fks τ ∧
      AgDictSt a.ix a.ky a.sz B (N * N) (agsRoundKeys D rank oks tks fks) τ ∧
      (∀ u v : Fin N, agArcKey (u, v) ∈ agsRoundKeys D rank oks tks fks ↔
        u ∈ (greedyStep rank D).inN v) ∧
      AgFilterVars a.written σ τ ∧
      (∀ s, s ≠ a.ix → s ≠ a.ky → τ.arrs s = σ.arrs s) ∧
      (∀ s, (τ.arrs s).length = (σ.arrs s).length) := by
  obtain ⟨τ, hr, hrest⟩ := agsGreedyRound_run a hnames D rank hRank hNB hNNB
    oks tks fks hOld hTrans hFrat σ hIn hix hky hwords
  obtain ⟨ho, ht, hf⟩ := hIn.sparse_lengths hOld hTrans hFrat
  exact ⟨τ, hr.mono (by dsimp only [agsGreedyCost]; omega), hrest⟩

end Lax3Proofs.Prog
