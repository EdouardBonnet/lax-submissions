import Lax3Proofs.SolveSweepAugCsr
import Lax3Proofs.SolveSweepAugBuildPeel
import Lax3Proofs.SolveSweepAugExtract
import Lax3Proofs.SolveSweepAugPairFilter
import Lax3Proofs.SolveSweepAugSym
import Lax3Proofs.SolveRunWords

/-!
# The sparse augmentation machine

The two arc dictionaries alternate between consecutive rounds. A shared CSR
region holds the current in-lists, then the fraternity graph, then the next
in-lists. All unused inverse entries remain bounded words, transported by
the actual bounded execution; reservations are expressed only as lengths.
-/

namespace Lax3Proofs.Prog.AugMachine

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax62Proofs.Codegen (getD_eq_getElem)
open Lax3Proofs.Augmentation Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.CoverRoutine

def oldI (b : Bool) : String := if b then "@aug.a1.i" else "@aug.a0.i"
def oldK (b : Bool) : String := if b then "@aug.a1.k" else "@aug.a0.k"
def oldS (b : Bool) : String := if b then "@aug.a1.s" else "@aug.a0.s"
def nN : String := "@aug.n"
def ti : String := "@aug.t.i"
def tk : String := "@aug.t.k"
def ts : String := "@aug.t.s"
def fi : String := "@aug.f.i"
def fk : String := "@aug.f.k"
def fs : String := "@aug.f.s"
def co : String := "@aug.csr.o"
def ct : String := "@aug.csr.t"
def cnt : String := "@aug.csr.count"
def cur : String := "@aug.csr.cursor"
def ra : String := "@aug.rank"
def ao : String := "@aug.adj.o"
def aj : String := "@aug.adj.t"
def dg : String := "@aug.adj.degree"
def mt : String := "@aug.adj.mate"
def od : String := "@aug.order"
def hp : String := "@aug.heap"

/-- These are reserved arrays; the program only visits occupied prefixes. -/
def arrays : List String :=
  [oldI false, oldK false, oldI true, oldK true, ti, tk, fi, fk, co, ct, cnt, cur, ra, ao, aj, dg, mt, od, hp]

def capacity (N : ℕ) : ℕ := N * N + N + 1

def Alloc (N : ℕ) (σ : Env) : Prop :=
  ∀ a ∈ arrays, capacity N ≤ (σ.arrs a).length

def Memory (B N : ℕ) (σ : Env) : Prop := ArrWords B σ ∧ Alloc N σ

theorem Memory.run {B N K : ℕ} {c : Com} {σ τ : Env} (h : Memory B N σ) (hr : Run B c σ τ K) :
    Memory B N τ := by
  refine ⟨Lax3Proofs.Prog.Run.arrWords hr h.1, ?_⟩
  intro a ha
  rw [run_arrs_length_eq hr]
  exact h.2 a ha

theorem Memory.reserve {B N : ℕ} {σ : Env} (h : Memory B N σ) (a : String) (ha : a ∈ arrays) :
    N * N ≤ (σ.arrs a).length ∧ N + 1 ≤ (σ.arrs a).length ∧ N * N + N ≤ (σ.arrs a).length := by
  have hh := h.2 a ha
  dsimp only [capacity] at hh
  omega

theorem Memory.words {B N : ℕ} {σ : Env} (h : Memory B N σ) (a : String) (ha : a ∈ arrays) :
    ∀ k < N * N, (σ.arrs a).getD k 0 < B := by
  intro k hk
  have hkl := lt_of_lt_of_le hk (h.reserve a ha).1
  apply h.1 a
  rw [getD_eq_getElem hkl]
  exact List.getElem_mem hkl

private theorem keepDict {B U K : ℕ} {ix ky sz : String} {ks : List ℕ}
    {σ τ : Env} {c : Com} (hr : Run B c σ τ K) (hD : AgDictSt ix ky sz B U ks σ)
    (hix : ix ∉ c.warrs) (hky : ky ∉ c.warrs) (hsz : sz ∉ c.wvars) :
    AgDictSt ix ky sz B U ks τ :=
  hD.of_eq (hr.frame_arr ix hix) (hr.frame_arr ky hky) (hr.frame_var sz hsz)

def names (b : Bool) : AgsRoundNames where
  oi := oldI b
  ok := oldK b
  os := oldS b
  ti := ti
  tk := tk
  ts := ts
  fi := fi
  fk := fk
  fs := fs
  nN := nN
  kf := "@aug.g.k"
  kr := "@aug.g.rev"
  tmp := "@aug.g.tmp"
  ofv := "@aug.g.old"
  orv := "@aug.g.oldrev"
  tfv := "@aug.g.trans"
  trv := "@aug.g.transrev"
  ffv := "@aug.g.frat"
  ra := ra
  uv := "@aug.g.u"
  vv := "@aug.g.v"
  ans := "@aug.g.yes"
  ix := oldI (!b)
  ky := oldK (!b)
  sz := oldS (!b)
  tv := "@aug.g.pos"
  hv := "@aug.g.hit"
  iv := "@aug.g.i"
  lm := "@aug.g.end"

theorem names_good (b : Bool) : (names b).WellNamed := by
  cases b <;> constructor <;> decide

def demands (b : Bool) : Com :=
  agDictDemands co ct (if b then fi else ti) (if b then fk else tk) (if b then fs else ts)
    "@aug.d.outer" "@aug.d.row" "@aug.d.fixed" "@aug.d.key" "@aug.d.pos" "@aug.d.hit"
    "@aug.d.i" "@aug.d.end" "@aug.d.middle" "@aug.d.middleEnd" nN b

def demandPass : Com := .seq (demands false) (demands true)

def csr (b : Bool) : Com := agCsrCom nN (oldS b) (oldK b) co ct cnt cur

def pairFilter (up b : Bool) (src srcsz : String) : Com :=
  agpPairFilter up nN "@aug.p.key" "@aug.p.rev" "@aug.p.u" "@aug.p.v" "@aug.p.yes" ra
    (oldI b) (oldK b) (oldS b) "@aug.p.pos" "@aug.p.hit" "@aug.p.i" "@aug.p.end" src srcsz

def fratFilter (b : Bool) : Com := pairFilter false (!b) fk fs

def extract (o t : String) : Com :=
  agxExtract o t (oldI true) (oldK true) (oldS true) "@aug.x.outer" "@aug.x.row" "@aug.x.fixed"
    "@aug.x.key" "@aug.x.pos" "@aug.x.hit" "@aug.x.i" "@aug.x.end" nN

def symmetrize (b : Bool) : Com :=
  agSymCom (oldI (!b)) (oldK (!b)) (oldS (!b)) "@aug.s.key" "@aug.s.pos" "@aug.s.hit"
    "@aug.s.i" "@aug.s.end" nN (oldK b) (oldS b)

/-- The loop invariant holds a unique arc dictionary and its actual in-list CSR. -/
def ChainSt (B : ℕ) {N : ℕ} (D : Orientation N) (b : Bool) (σ : Env) : Prop :=
  Memory B N σ ∧ σ.vars nN = N ∧
    ∃ (ks : List ℕ) (rows : Fin N → List (Fin N)) (off : ℕ → ℕ),
      AgDictSt (oldI b) (oldK b) (oldS b) B (N * N) ks σ ∧
      (∀ u v : Fin N, agArcKey (u, v) ∈ ks ↔ u ∈ D.inN v) ∧
      AgCsrRows co ct ks.length rows off σ ∧ AgInRows D rows

/-- Exact sparse charge of the two witnessed-demand passes. -/
def demandCost {N : ℕ} (D : Orientation N) : ℕ :=
  58 * (transPairCount D + fratPairCount D) + 60 * arcCount D + 44 * N + 16

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem demandPass_run {B N : ℕ} (D : Orientation N) (b : Bool)
    (hB : N * N + 4 * N + 4 ≤ B) (σ : Env) (hSt : ChainSt B D b σ) :
    ∃ τ, Run B demandPass σ τ (demandCost D) ∧ ChainSt B D b τ ∧
      ∃ tks fks : List ℕ,
        AgDictSt ti tk ts B (N * N) tks τ ∧
        (∀ u v : Fin N, agArcKey (u, v) ∈ tks ↔ TransLink D u v) ∧
        AgDictSt fi fk fs B (N * N) fks τ ∧
        (∀ u v : Fin N, agArcKey (u, v) ∈ fks ↔ FratLink D u v) := by
  obtain ⟨hm, hn, ks, rows, off, hOld, hArc, hC, hR⟩ := hSt
  have hNB : N + 1 < B := by omega
  have hNNB : N * N < B := by omega
  have hnsB : ks.length < B := lt_of_le_of_lt hOld.length_le hNNB
  obtain ⟨ρ, ht, hT, htv, hta, htl⟩ := agDictDemands_run
    co ct ti tk ts "@aug.d.outer" "@aug.d.row" "@aug.d.fixed" "@aug.d.key" "@aug.d.pos" "@aug.d.hit"
    "@aug.d.i" "@aug.d.end" "@aug.d.middle" "@aug.d.middleEnd" nN false
    (by decide) (by decide) (by decide) hNB hnsB le_rfl hNNB D rows off σ hC hR
    (hm.reserve ti (by decide)).1 (hm.reserve tk (by decide)).1 (hm.words ti (by decide)) hn
  have hMemρ : Memory B N ρ := hm.run ht
  have hnρ : ρ.vars nN = N :=
    (ht.frame_var nN (by decide)).trans hn
  have hCρ : AgCsrRows co ct ks.length rows off ρ :=
    hC.of_eq (ht.frame_arr co (by decide)) (ht.frame_arr ct (by decide))
  obtain ⟨τ, hf, hF, hfv, hfa, hfl⟩ := agDictDemands_run
    co ct fi fk fs "@aug.d.outer" "@aug.d.row" "@aug.d.fixed" "@aug.d.key" "@aug.d.pos" "@aug.d.hit"
    "@aug.d.i" "@aug.d.end" "@aug.d.middle" "@aug.d.middleEnd" nN true
    (by decide) (by decide) (by decide) hNB hnsB le_rfl hNNB D rows off ρ hCρ hR
    (hMemρ.reserve fi (by decide)).1 (hMemρ.reserve fk (by decide)).1 (hMemρ.words fi (by decide)) hnρ
  have hr : Run B demandPass σ τ (demandCost D) :=
    (ht.seq hf).mono (by dsimp only [demandCost]; simp only [Bool.false_eq_true, ↓reduceIte]; omega)
  have hOτ := keepDict hr hOld (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide)
  have hCτ : AgCsrRows co ct ks.length rows off τ :=
    hC.of_eq (hr.frame_arr co (by decide)) (hr.frame_arr ct (by decide))
  have hTτ := keepDict hf hT (by decide) (by decide) (by decide)
  refine ⟨τ, hr, ⟨hm.run hr, (hr.frame_var nN (by decide)).trans hn,
    ks, rows, off, hOτ, hArc, hCτ, hR⟩, _, _, hTτ, ?_, hF, ?_⟩
  · exact agTransDemand_keys hR
  · exact agFratDemand_keys hR

/-- The semantic dictionaries used by an exact greedy decision. -/
structure Dictionaries (B : ℕ) {N : ℕ} (D : Orientation N) (b : Bool)
    (oks tks fks : List ℕ) (σ : Env) : Prop where
  old : AgDictSt (oldI b) (oldK b) (oldS b) B (N * N) oks σ
  old_mem : ∀ u v : Fin N, agArcKey (u, v) ∈ oks ↔ u ∈ D.inN v
  trans : AgDictSt ti tk ts B (N * N) tks σ
  trans_mem : ∀ u v : Fin N, agArcKey (u, v) ∈ tks ↔ TransLink D u v
  frat : AgDictSt fi fk fs B (N * N) fks σ
  frat_mem : ∀ u v : Fin N, agArcKey (u, v) ∈ fks ↔ FratLink D u v

theorem Dictionaries.run {B N K : ℕ} {D : Orientation N} {b : Bool}
    {oks tks fks : List ℕ} {σ τ : Env} {c : Com}
    (h : Dictionaries B D b oks tks fks σ) (hr : Run B c σ τ K)
    (ha : ∀ s ∈ [oldI b, oldK b, ti, tk, fi, fk], s ∉ c.warrs)
    (hv : ∀ s ∈ [oldS b, ts, fs], s ∉ c.wvars) :
    Dictionaries B D b oks tks fks τ :=
  ⟨keepDict hr h.old (ha _ (by simp)) (ha _ (by simp)) (hv _ (by simp)), h.old_mem,
    keepDict hr h.trans (ha _ (by simp)) (ha _ (by simp)) (hv _ (by simp)), h.trans_mem,
    keepDict hr h.frat (ha _ (by simp)) (ha _ (by simp)) (hv _ (by simp)), h.frat_mem⟩

theorem Dictionaries.lengths {B N : ℕ} {D : Orientation N} {b : Bool}
    {oks tks fks : List ℕ} {σ : Env} (h : Dictionaries B D b oks tks fks σ) :
    oks.length ≤ arcCount D ∧ tks.length ≤ transPairCount D ∧ fks.length ≤ fratPairCount D := by
  classical
  let rows := fun v => (D.inN v).toList
  have hrows : AgInRows D rows := ⟨fun _ => Finset.nodup_toList _, fun _ => Finset.toList_toFinset _⟩
  refine ⟨agArcDict_length_le D h.old h.old_mem, ?_, ?_⟩
  · rw [← agTransCandidates_length hrows]
    exact agsDict_length_le_candidates h.trans (agTransCandidates rows)
      (fun u v hk => (agTransCandidates_mem hrows u v).mpr ((h.trans_mem u v).mp hk))
  · rw [← agFratCandidates_length hrows]
    exact agsDict_length_le_candidates h.frat (agFratCandidates rows)
      (fun u v hk => (agFratCandidates_mem hrows u v).mpr ((h.frat_mem u v).mp hk))

private theorem length_le_of_mem {xs ys : List ℕ} (hn : xs.Nodup)
    (hs : ∀ k ∈ xs, k ∈ ys) : xs.length ≤ ys.length := by
  calc
    xs.length = xs.toFinset.card := (List.toFinset_card_of_nodup hn).symm
    _ ≤ ys.toFinset.card := Finset.card_le_card (fun k hk => List.mem_toFinset.mpr (hs k (List.mem_toFinset.mp hk)))
    _ ≤ ys.length := List.toFinset_card_le _

def fratCsr (b : Bool) : Com := .seq (fratFilter b) (csr (!b))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem fratCsr_run {B N : ℕ} (D : Orientation N) (b : Bool) (oks tks fks : List ℕ)
    (hB : N * N + 4 * N + 4 ≤ B) (σ : Env) (hm : Memory B N σ) (hn : σ.vars nN = N)
    (hd : Dictionaries B D b oks tks fks σ) :
    ∃ τ, Run B (fratCsr b) σ τ (152 * fratPairCount D + 40 * N + 47) ∧
      Memory B N τ ∧ τ.vars nN = N ∧ Dictionaries B D b oks tks fks τ ∧
      ∃ (gks : List ℕ) (rows : Fin N → List (Fin N)) (off : ℕ → ℕ),
        AgDictSt (oldI (!b)) (oldK (!b)) (oldS (!b)) B (N * N) gks τ ∧
        AgCsrRows co ct gks.length rows off τ ∧
        (∀ v, (rows v).Nodup) ∧ (∀ u v, u ∈ rows v ↔ (fratGraph D).Adj v u) := by
  have hNB : N + 1 < B := by omega
  have hNNB : N * N < B := by omega
  have hFL := hd.frat.length_le
  obtain ⟨ρ, hfilter, hG, hgv, hga, hgl⟩ := agpPairFilter_run false
    nN "@aug.p.key" "@aug.p.rev" "@aug.p.u" "@aug.p.v" "@aug.p.yes" ra
    (oldI (!b)) (oldK (!b)) (oldS (!b)) "@aug.p.pos" "@aug.p.hit" "@aug.p.i" "@aug.p.end" fk fs
    (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide)
    (by simp) (fun w : Fin N => w.val) (fun w => w.isLt) hNB hNNB fks σ hn
    (by omega) hd.frat.size (hd.frat.length_le.trans hd.frat.ky_len) hd.frat.keys hd.frat.key_lt
    (by simp) (hm.reserve (oldI (!b)) (by cases b <;> decide)).1
    (hm.reserve (oldK (!b)) (by cases b <;> decide)).1
    (hm.words (oldI (!b)) (by cases b <;> decide))
  have hMemρ : Memory B N ρ := hm.run hfilter
  have hnρ : ρ.vars nN = N := (hfilter.frame_var nN (by cases b <;> decide)).trans hn
  let gks := agFilterPart [] fks (AgPairPred false (fun w : Fin N => w.val)) fks.length
  have hGL : gks.length ≤ fks.length := length_le_of_mem hG.nodup (by
    intro k hk
    rw [agFilterPart_mem, List.take_length] at hk
    exact hk.resolve_left (List.not_mem_nil) |>.1)
  have hgB : gks.length + 1 < B := by have := hG.length_le; omega
  obtain ⟨τ, hcsr, hGt, ⟨rows, off, hC, hK⟩, hca, hcl, hcv⟩ :=
    (agCsrCom_dict_spec (B := B) (N := N) (nN := nN) (sz := oldS (!b)) (ix := oldI (!b))
      (ky := oldK (!b)) (o := co) (t := ct) (ct := cnt) (cu := cur)
      (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide) hNB hgB hNNB).run
      ⟨hG, hnρ, (hMemρ.reserve co (by decide)).2.1,
        le_trans hG.length_le (hMemρ.reserve ct (by decide)).1,
        by have := (hMemρ.reserve cnt (by decide)).2.1; omega,
        by have := (hMemρ.reserve cur (by decide)).2.1; omega⟩
  have hFQ := hd.lengths.2.2
  have hr : Run B (fratCsr b) σ τ (152 * fratPairCount D + 40 * N + 47) :=
    (hfilter.seq hcsr).mono (by dsimp only [agCsrK]; omega)
  have hdτ := hd.run hr (by cases b <;> decide) (by cases b <;> decide)
  refine ⟨τ, hr, hm.run hr, (hr.frame_var nN (by cases b <;> decide)).trans hn, hdτ,
    gks, rows, off, hGt, hC, hK.nodup, ?_⟩
  intro u v
  rw [hK.mem]
  exact (agpFratFilter_keys D fks hd.frat_mem u v).trans ⟨fun h => h.symm, fun h => h.symm⟩

def buildVars : List String := ["@aug.bp.i", "@aug.bp.u", "@aug.bp.w"]
def peelVars : List String :=
  ["@aug.bp.hsize", "@aug.bp.time", "@aug.bp.x", "@aug.bp.y", "@aug.bp.key", "@aug.bp.d",
    "@aug.bp.v", "@aug.bp.z", "@aug.bp.pos", "@aug.bp.rank", "@aug.bp.word"]
def buildArrays : List String := [ra, ao, aj, dg, mt, od, hp]

def buildPeel (o t nS : String) : Com :=
  agBuildPeelCom o t ra ao aj dg mt od hp "@aug.bp.i" "@aug.bp.u" "@aug.bp.w" nN nS
    "@aug.bp.hsize" "@aug.bp.time" "@aug.bp.x" "@aug.bp.y" "@aug.bp.key" "@aug.bp.d"
    "@aug.bp.v" "@aug.bp.z" "@aug.bp.pos" "@aug.bp.rank" "@aug.bp.word"

/-- The common graph-to-rank phase, with only actual CSR data and allocations. -/
theorem buildPeel_run {B N M : ℕ} {G : SimpleGraph (Fin N)}
    {rows : Fin N → List (Fin N)} {off : ℕ → ℕ} (o t nS : String)
    (hA : [o, t, ra, ao, aj, dg, mt, od, hp].Nodup)
    (hS : [nN, nS] ++ peelVars |>.Nodup)
    (hSV : nS ∉ buildVars) (hB : N * N + 4 * N + 4 ≤ B)
    (σ : Env) (hm : Memory B N σ) (hn : σ.vars nN = N) (hs : σ.vars nS = M)
    (hc : AgCsrRows o t M rows off σ)
    (hnd : ∀ v, (rows v).Nodup) (hadj : ∀ u v, u ∈ rows v ↔ G.Adj v u) :
    ∃ τ, Run B (buildPeel o t nS) σ τ (agBuildPeelK N M) ∧ Memory B N τ ∧
      RankArr ra (mdPerm G) τ ∧ (∀ u : Fin N, (τ.arrs ra).getD u 0 = mdRank G u) ∧
      (∀ a, a ∉ buildArrays → τ.arrs a = σ.arrs a) ∧
      (∀ y, y ∉ buildVars ++ peelVars → τ.vars y = σ.vars y) := by
  have hM : M ≤ N * N := by rw [agPaddedCsr_mass_eq hc hnd hadj]; exact nsOf_le G
  obtain ⟨τ, hr, hRank, hVal, hfa, hfv, hl⟩ :=
    (agBuildPeel_spec (B := B) (N := N) (G := G) (rows := rows) (off := off)
      (o := o) (t := t) (ra := ra) (ao := ao) (aj := aj) (dg := dg) (mt := mt) (od := od) (hp := hp)
      (bi := "@aug.bp.i") (bu := "@aug.bp.u") (bw := "@aug.bp.w") (nN := nN) (nS := nS)
      (hsv := "@aug.bp.hsize") (tv := "@aug.bp.time") (xv := "@aug.bp.x") (yv := "@aug.bp.y")
      (kv := "@aug.bp.key") (dv := "@aug.bp.d") (vv := "@aug.bp.v") (zv := "@aug.bp.z")
      (pi := "@aug.bp.pos") (rc := "@aug.bp.rank") (pw := "@aug.bp.word")
      hnd hadj hA (by decide) (by
        intro y hy
        refine ⟨?_, fun he => hSV (he ▸ hy)⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl <;> decide)
      hS hB).run
      ⟨hc, hn, hs, by have := (hm.reserve ra (by decide)).2.1; omega,
        (hm.reserve ao (by decide)).2.1, hM.trans (hm.reserve aj (by decide)).1,
        by have := (hm.reserve dg (by decide)).2.1; omega,
        hM.trans (hm.reserve mt (by decide)).1,
        by have := (hm.reserve od (by decide)).2.1; omega,
        (hm.reserve hp (by decide)).2.2⟩
  exact ⟨τ, hr, hm.run hr, hRank, hVal, hfa, hfv⟩

/-- Sparse filtering with the computed rank, followed by a fresh in-list CSR. -/
def greedyCsr (b : Bool) : Com := .seq (agsGreedyRound (names b)) (csr (!b))

noncomputable def next {N : ℕ} (D : Orientation N) : Orientation N := greedyStep (mdRank (fratGraph D)) D

noncomputable def greedyCsrCost {N : ℕ} (D : Orientation N) : ℕ :=
  agsGreedyCost D + agCsrK N (arcCount (next D))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem greedyCsr_run {B N : ℕ} (D : Orientation N) (b : Bool) (oks tks fks : List ℕ)
    (hB : N * N + 4 * N + 4 ≤ B) (σ : Env) (hm : Memory B N σ) (hn : σ.vars nN = N)
    (hd : Dictionaries B D b oks tks fks σ) (hra : RankArr ra (mdPerm (fratGraph D)) σ) :
    ∃ τ, Run B (greedyCsr b) σ τ (greedyCsrCost D) ∧ ChainSt B (next D) (!b) τ := by
  have hNB : N + 1 < B := by omega
  have hNNB : N * N < B := by omega
  have hIn : AgsRoundSt (names b) B D (mdRank (fratGraph D)) oks tks fks σ :=
    ⟨hd.old, hd.trans, hd.frat, hn, hra.1, fun v => (hra.2 v).trans (mdPerm_val _ v)⟩
  obtain ⟨ρ, hg, hIp, hNew, hArc, hgv, hga, hgl⟩ :=
    agsGreedyRound_sparse_run (names b) (names_good b) D (mdRank (fratGraph D))
      (mdRank_lt _) hNB hNNB oks tks fks hd.old_mem hd.trans_mem hd.frat_mem σ hIn
      (hm.reserve (oldI (!b)) (by cases b <;> decide)).1
      (hm.reserve (oldK (!b)) (by cases b <;> decide)).1
      (hm.words (oldI (!b)) (by cases b <;> decide))
  have hmρ : Memory B N ρ := hm.run hg
  have hnρ : ρ.vars nN = N := hIp.nval
  let ks := agsRoundKeys D (mdRank (fratGraph D)) oks tks fks
  have hkL : ks.length ≤ N * N := hNew.length_le
  have hkB : ks.length + 1 < B := by omega
  obtain ⟨τ, hc, hD, ⟨rows, off, hC, hK⟩, hca, hcl, hcv⟩ :=
    (agCsrCom_dict_spec (B := B) (N := N) (nN := nN) (sz := oldS (!b)) (ix := oldI (!b))
      (ky := oldK (!b)) (o := co) (t := ct) (ct := cnt) (cu := cur)
      (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide) hNB hkB hNNB).run
      ⟨hNew, hnρ, (hmρ.reserve co (by decide)).2.1,
        le_trans hNew.length_le (hmρ.reserve ct (by decide)).1,
        by have := (hmρ.reserve cnt (by decide)).2.1; omega,
        by have := (hmρ.reserve cur (by decide)).2.1; omega⟩
  have hKL : ks.length ≤ arcCount (next D) := agArcDict_length_le (next D) hNew hArc
  have hr : Run B (greedyCsr b) σ τ (greedyCsrCost D) :=
    (hg.seq hc).mono (by dsimp only [greedyCsrCost, agCsrK]; omega)
  exact ⟨τ, hr, hm.run hr, (hc.frame_var nN (by cases b <;> decide)).trans hnρ,
    ks, rows, off, hD, hArc, hC, hK.inRows hArc⟩

/-- One complete augmentation round: both demand streams, the computed
fraternity rank, exact greedy decisions, and the next incoming lists. -/
def round (b : Bool) : Com :=
  .seq demandPass (.seq (fratCsr b) (.seq (buildPeel co ct (oldS (!b))) (greedyCsr b)))

noncomputable def roundCost {N : ℕ} (D : Orientation N) : ℕ :=
  demandCost D + (152 * fratPairCount D + 40 * N + 47) +
    agBuildPeelK N (nsOf (fratGraph D)) + greedyCsrCost D

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem round_run {B N : ℕ} (D : Orientation N) (b : Bool)
    (hB : N * N + 4 * N + 4 ≤ B) (σ : Env) (hSt : ChainSt B D b σ) :
    ∃ τ, Run B (round b) σ τ (roundCost D) ∧ ChainSt B (next D) (!b) τ := by
  obtain ⟨ρ₁, h₁, hSt₁, tks, fks, hT, hTrans, hF, hFrat⟩ := demandPass_run D b hB σ hSt
  obtain ⟨hm₁, hn₁, oks, _, _, hOld, hArc, _, _⟩ := hSt₁
  have hd₁ : Dictionaries B D b oks tks fks ρ₁ := ⟨hOld, hArc, hT, hTrans, hF, hFrat⟩
  obtain ⟨ρ₂, h₂, hm₂, hn₂, hd₂, gks, rows, off, hG, hC, hnd, hadj⟩ :=
    fratCsr_run D b oks tks fks hB ρ₁ hm₁ hn₁ hd₁
  obtain ⟨ρ₃, h₃, hm₃, hRank, hVals, hfa, hfv⟩ :=
    buildPeel_run co ct (oldS (!b)) (by decide) (by cases b <;> decide)
      (by cases b <;> decide) hB ρ₂ hm₂ hn₂ hG.size hC hnd hadj
  have hd₃ : Dictionaries B D b oks tks fks ρ₃ :=
    ⟨hd₂.old.of_eq (hfa _ (by cases b <;> decide)) (hfa _ (by cases b <;> decide))
        (hfv _ (by cases b <;> decide)), hd₂.old_mem,
      hd₂.trans.of_eq (hfa _ (by decide)) (hfa _ (by decide)) (hfv _ (by decide)), hd₂.trans_mem,
      hd₂.frat.of_eq (hfa _ (by decide)) (hfa _ (by decide)) (hfv _ (by decide)), hd₂.frat_mem⟩
  have hn₃ : ρ₃.vars nN = N := (hfv nN (by decide)).trans hn₂
  obtain ⟨τ, h₄, hOut⟩ := greedyCsr_run D b oks tks fks hB ρ₃ hm₃ hn₃ hd₃ hRank
  have hMass := agPaddedCsr_mass_eq hC hnd hadj
  rw [hMass] at h₃
  exact ⟨τ, (h₁.seq (h₂.seq (h₃.seq h₄))).mono (by dsimp only [roundCost]; omega), hOut⟩

def inputSize : String := "@aug.input.size"

private theorem source_names {o t : String} (ho : o ∉ arrays) (ht : t ∉ arrays) (hot : o ≠ t) :
    [o, t, ra, ao, aj, dg, mt, od, hp].Nodup := by
  have hs : [ra, ao, aj, dg, mt, od, hp] ⊆ arrays := by decide
  exact List.nodup_cons.mpr ⟨by
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact hot h
    · exact ho (hs h), List.nodup_cons.mpr ⟨fun h => ht (hs h), by decide⟩⟩

private theorem source_ne {o : String} (ho : o ∉ arrays) (a : String) (ha : a ∈ arrays) : o ≠ a :=
  fun he => ho (he ▸ ha)

private theorem candidates_mass {N M : ℕ} {o t : String} {rows : Fin N → List (Fin N)}
    {off : ℕ → ℕ} {σ : Env} (hc : AgCsrRows o t M rows off σ) :
    (agArcCandidates rows).length = M := by
  simpa [agArcCandidates, List.length_flatMap, List.finRange, List.map_ofFn,
    List.sum_ofFn, Function.comp_def] using hc.sum_lengths

/-- Compute the pinned base orientation from genuine input CSR. -/
def base (o t : String) : Com :=
  .seq (extract o t) (.seq (buildPeel o t inputSize)
    (.seq (pairFilter true false (oldK true) (oldS true)) (csr false)))

noncomputable def baseCost {N : ℕ} (G : SimpleGraph (Fin N)) (M : ℕ) : ℕ :=
  154 * M + 26 * N + 18 + agBuildPeelK N M + agCsrK N (arcCount (mdChain G 0))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem base_run {B N M : ℕ} (G : SimpleGraph (Fin N)) (o t : String)
    (ho : o ∉ arrays) (ht : t ∉ arrays) (hot : o ≠ t)
    (hB : N * N + 4 * N + 4 ≤ B) (rows : Fin N → List (Fin N)) (off : ℕ → ℕ)
    (σ : Env) (hm : Memory B N σ) (hn : σ.vars nN = N) (hs : σ.vars inputSize = M)
    (hc : AgCsrRows o t M rows off σ)
    (hnd : ∀ v, (rows v).Nodup) (hadj : ∀ u v, u ∈ rows v ↔ G.Adj v u) :
    ∃ τ, Run B (base o t) σ τ (baseCost G M) ∧ ChainSt B (mdChain G 0) false τ := by
  have hM : M ≤ N * N := by rw [agPaddedCsr_mass_eq hc hnd hadj]; exact nsOf_le G
  have hNB : N + 1 < B := by omega
  have hNNB : N * N < B := by omega
  have hoi := source_ne ho (oldI true) (by decide)
  have hok := source_ne ho (oldK true) (by decide)
  have hti := source_ne ht (oldI true) (by decide)
  have htk := source_ne ht (oldK true) (by decide)
  obtain ⟨ρ₁, h₁, hRaw, h₁v, h₁a, h₁l⟩ := agxExtract_run
    o t (oldI true) (oldK true) (oldS true) "@aug.x.outer" "@aug.x.row" "@aug.x.fixed"
    "@aug.x.key" "@aug.x.pos" "@aug.x.hit" "@aug.x.i" "@aug.x.end" nN
    (by decide) ⟨hoi, hok, hti, htk⟩ (by decide) hNB (by omega) hNNB rows off σ hc
    (hm.reserve (oldI true) (by decide)).1 (hm.reserve (oldK true) (by decide)).1
    (hm.words (oldI true) (by decide)) hn
  have hm₁ : Memory B N ρ₁ := hm.run h₁
  have hn₁ : ρ₁.vars nN = N := (h₁v nN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn
  have hs₁ : ρ₁.vars inputSize = M := (h₁v inputSize (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs
  have hc₁ := hc.of_eq (h₁a o hoi hok) (h₁a t hti htk)
  obtain ⟨ρ₂, h₂, hm₂, hRank, hVals, h₂a, h₂v⟩ :=
    buildPeel_run o t inputSize (source_names ho ht hot) (by decide) (by decide)
      hB ρ₁ hm₁ hn₁ hs₁ hc₁ hnd hadj
  have hRaw₂ := hRaw.of_eq (h₂a _ (by decide)) (h₂a _ (by decide)) (h₂v _ (by decide))
  have hn₂ : ρ₂.vars nN = N := (h₂v _ (by decide)).trans hn₁
  let rks := agDictUnion [] ((agArcCandidates rows).map agArcKey)
  have hRL : rks.length ≤ M := by
    have hle : rks.length ≤ ((agArcCandidates rows).map agArcKey).length :=
      length_le_of_mem hRaw.nodup (by
        intro k hk
        rw [agDictUnion_mem] at hk
        exact hk.resolve_left List.not_mem_nil)
    simpa only [List.length_map, candidates_mass hc] using hle
  have hrB : rks.length < B := by omega
  obtain ⟨ρ₃, h₃, hBase, h₃v, h₃a, h₃l⟩ := agpPairFilter_run true
    nN "@aug.p.key" "@aug.p.rev" "@aug.p.u" "@aug.p.v" "@aug.p.yes" ra
    (oldI false) (oldK false) (oldS false) "@aug.p.pos" "@aug.p.hit" "@aug.p.i" "@aug.p.end"
    (oldK true) (oldS true) (by decide) (by decide) (by decide) (by decide)
    (fun w => (mdPerm G w).val) (fun w => (mdPerm G w).isLt) hNB hNNB rks ρ₂ hn₂ hrB
    hRaw₂.size (hRaw₂.length_le.trans hRaw₂.ky_len) hRaw₂.keys hRaw₂.key_lt
    (fun _ => hRank) (hm₂.reserve (oldI false) (by decide)).1
    (hm₂.reserve (oldK false) (by decide)).1 (hm₂.words (oldI false) (by decide))
  have hm₃ : Memory B N ρ₃ := hm₂.run h₃
  have hn₃ : ρ₃.vars nN = N := (h₃.frame_var nN (by decide)).trans hn₂
  let ks := agFilterPart [] rks (AgPairPred true (fun w => (mdPerm G w).val)) rks.length
  have hArc : ∀ u v : Fin N, agArcKey (u, v) ∈ ks ↔ u ∈ (mdChain G 0).inN v :=
    agpBaseFilter_keys G (mdPerm G) rks (fun u v => (agxExtract_keys rows u v).trans
      ((hadj u v).trans ⟨fun h => h.symm, fun h => h.symm⟩))
  have hkL : ks.length ≤ N * N := hBase.length_le
  have hkB : ks.length + 1 < B := by omega
  obtain ⟨τ, h₄, hD, ⟨rrows, roff, hC, hK⟩, h₄a, h₄l, h₄v⟩ :=
    (agCsrCom_dict_spec (B := B) (N := N) (nN := nN) (sz := oldS false) (ix := oldI false)
      (ky := oldK false) (o := co) (t := ct) (ct := cnt) (cu := cur)
      (by decide) (by decide) (by decide) hNB hkB hNNB).run
      ⟨hBase, hn₃, (hm₃.reserve co (by decide)).2.1,
        le_trans hBase.length_le (hm₃.reserve ct (by decide)).1,
        by have := (hm₃.reserve cnt (by decide)).2.1; omega,
        by have := (hm₃.reserve cur (by decide)).2.1; omega⟩
  have hKL : ks.length ≤ arcCount (mdChain G 0) := agArcDict_length_le _ hBase hArc
  have hr : Run B (base o t) σ τ (baseCost G M) :=
    (h₁.seq (h₂.seq (h₃.seq h₄))).mono (by dsimp only [baseCost, agCsrK]; omega)
  exact ⟨τ, hr, hm.run hr, (h₄.frame_var nN (by decide)).trans hn₃,
    ks, rrows, roff, hD, hArc, hC, hK.inRows hArc⟩

def side : ℕ → Bool → Bool
  | 0, b => b
  | r + 1, b => !(side r b)

/-- Formula-dependent unrolling; every round still scans only occupied data. -/
def loop : ℕ → Bool → Com
  | 0, _ => .skip
  | r + 1, b => .seq (loop r b) (round (side r b))

noncomputable def loopCost {N : ℕ} (G : SimpleGraph (Fin N)) : ℕ → ℕ
  | 0 => 1
  | r + 1 => loopCost G r + roundCost (mdChain G r)

theorem loopCost_eq {N : ℕ} (G : SimpleGraph (Fin N)) (R : ℕ) :
    loopCost G R = 1 + ∑ r ∈ Finset.range R, roundCost (mdChain G r) := by
  induction R with
  | zero => simp [loopCost]
  | succ r ih => simp only [loopCost, ih, Finset.sum_range_succ]; omega

theorem loop_run {B N : ℕ} (G : SimpleGraph (Fin N)) (R : ℕ) (b : Bool)
    (hB : N * N + 4 * N + 4 ≤ B) (σ : Env) (hSt : ChainSt B (mdChain G 0) b σ) :
    ∃ τ, Run B (loop R b) σ τ (loopCost G R) ∧ ChainSt B (mdChain G R) (side R b) τ := by
  induction R with
  | zero => exact ⟨σ, Run.skip, hSt⟩
  | succ r ih =>
    obtain ⟨ρ, h₁, hSt₁⟩ := ih
    obtain ⟨τ, h₂, hSt₂⟩ := round_run (mdChain G r) (side r b) hB ρ hSt₁
    exact ⟨τ, h₁.seq h₂, hSt₂⟩

def buildInit (nS : String) : Com :=
  agBuildInitCom co ct ra ao aj dg mt od "@aug.bp.i" "@aug.bp.u" "@aug.bp.w" nN nS

/-- Materialize the final underlying graph by two sparse arc passes. -/
def finish (b : Bool) : Com :=
  .seq (symmetrize b) (.seq (csr (!b)) (buildInit (oldS (!b))))

noncomputable def finishCost {N : ℕ} (D : Orientation N) : ℕ :=
  116 * arcCount D + 16 + agCsrK N (nsOf D.toGraph) + agBuildInitK N (nsOf D.toGraph)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem finish_run {B N : ℕ} (D : Orientation N) (b : Bool)
    (hB : N * N + 4 * N + 4 ≤ B) (σ : Env) (hSt : ChainSt B D b σ) :
    ∃ τ, Run B (finish b) σ τ (finishCost D) ∧ Memory B N τ ∧ τ.vars nN = N ∧
      DelAdjSt ao aj dg mt D.toGraph ∅ τ := by
  obtain ⟨hm, hn, ks, _, _, hD, hArc, _, _⟩ := hSt
  have hNB : N + 1 < B := by omega
  have hNNB : N * N < B := by omega
  have hkL := hD.length_le
  obtain ⟨ρ₁, h₁, hSym, h₁v, h₁a, h₁l⟩ := agSymCom_run
    (oldI (!b)) (oldK (!b)) (oldS (!b)) "@aug.s.key" "@aug.s.pos" "@aug.s.hit"
    "@aug.s.i" "@aug.s.end" nN (oldK b) (oldS b)
    (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide)
    hNB hNNB ks σ hn (by omega) hD.size (hD.length_le.trans hD.ky_len) hD.keys hD.key_lt
    (hm.reserve (oldI (!b)) (by cases b <;> decide)).1
    (hm.reserve (oldK (!b)) (by cases b <;> decide)).1
    (hm.words (oldI (!b)) (by cases b <;> decide))
  have hm₁ : Memory B N ρ₁ := hm.run h₁
  have hn₁ : ρ₁.vars nN = N := (h₁.frame_var nN (by cases b <;> decide)).trans hn
  have hsL := hSym.length_le
  have hsB : (agSymKeys N ks).length + 1 < B := by omega
  obtain ⟨ρ₂, h₂, hDict, ⟨rows, off, hC, hK⟩, h₂a, h₂l, h₂v⟩ :=
    (agCsrCom_dict_spec (B := B) (N := N) (nN := nN) (sz := oldS (!b)) (ix := oldI (!b))
      (ky := oldK (!b)) (o := co) (t := ct) (ct := cnt) (cu := cur)
      (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide) hNB hsB hNNB).run
      ⟨hSym, hn₁, (hm₁.reserve co (by decide)).2.1,
        le_trans hSym.length_le (hm₁.reserve ct (by decide)).1,
        by have := (hm₁.reserve cnt (by decide)).2.1; omega,
        by have := (hm₁.reserve cur (by decide)).2.1; omega⟩
  have hm₂ : Memory B N ρ₂ := hm₁.run h₂
  have hn₂ : ρ₂.vars nN = N := (h₂.frame_var nN (by cases b <;> decide)).trans hn₁
  have hadj : ∀ u v, u ∈ rows v ↔ D.toGraph.Adj v u := by
    intro u v
    rw [hK.mem]
    exact (agSymKeys_toGraph D ks hD.key_lt hArc u v).trans ⟨fun h => h.symm, fun h => h.symm⟩
  have hMass := agPaddedCsr_mass_eq hC hK.nodup hadj
  obtain ⟨τ, h₃, hRank, hOrd, hDel, h₃a, h₃v, h₃l⟩ :=
    (agBuildInit_spec (B := B) (N := N) (G := D.toGraph) (rows := rows) (off := off)
      (o := co) (t := ct) (ra := ra) (ao := ao) (aj := aj) (dg := dg) (mt := mt) (od := od)
      (bi := "@aug.bp.i") (bu := "@aug.bp.u") (bw := "@aug.bp.w") (nN := nN) (nS := oldS (!b))
      hK.nodup hadj (by decide) (by decide) (by cases b <;> decide) hB).run
      ⟨hC, hn₂, hDict.size, by have := (hm₂.reserve ra (by decide)).2.1; omega,
        (hm₂.reserve ao (by decide)).2.1, hDict.length_le.trans (hm₂.reserve aj (by decide)).1,
        by have := (hm₂.reserve dg (by decide)).2.1; omega,
        hDict.length_le.trans (hm₂.reserve mt (by decide)).1,
        by have := (hm₂.reserve od (by decide)).2.1; omega⟩
  have hKA := agArcDict_length_le D hD hArc
  rw [hMass] at h₂ h₃
  have hr : Run B (finish b) σ τ (finishCost D) :=
    (h₁.seq (h₂.seq h₃)).mono (by dsimp only [finishCost]; omega)
  exact ⟨τ, hr, hm.run hr, (h₃v nN (by decide)).trans hn₂, hDel⟩

/-- Complete augmentation after the two input size cells have been copied. -/
def core (o t : String) (R : ℕ) : Com :=
  .seq (base o t) (.seq (loop R false) (finish (side R false)))

noncomputable def coreCost {N : ℕ} (G : SimpleGraph (Fin N)) (M R : ℕ) : ℕ :=
  baseCost G M + loopCost G R + finishCost (mdChain G R)

theorem core_run {B N M : ℕ} (G : SimpleGraph (Fin N)) (o t : String) (R : ℕ)
    (ho : o ∉ arrays) (ht : t ∉ arrays) (hot : o ≠ t)
    (hB : N * N + 4 * N + 4 ≤ B) (rows : Fin N → List (Fin N)) (off : ℕ → ℕ)
    (σ : Env) (hm : Memory B N σ) (hn : σ.vars nN = N) (hs : σ.vars inputSize = M)
    (hc : AgCsrRows o t M rows off σ)
    (hnd : ∀ v, (rows v).Nodup) (hadj : ∀ u v, u ∈ rows v ↔ G.Adj v u) :
    ∃ τ, Run B (core o t R) σ τ (coreCost G M R) ∧ Memory B N τ ∧ τ.vars nN = N ∧
      DelAdjSt ao aj dg mt (mdChain G R).toGraph ∅ τ := by
  obtain ⟨ρ₁, h₁, hSt₁⟩ := base_run G o t ho ht hot hB rows off σ hm hn hs hc hnd hadj
  obtain ⟨ρ₂, h₂, hSt₂⟩ := loop_run G R false hB ρ₁ hSt₁
  obtain ⟨τ, h₃, hmτ, hnτ, hDel⟩ := finish_run (mdChain G R) (side R false) hB ρ₂ hSt₂
  exact ⟨τ, (h₁.seq (h₂.seq h₃)).mono (by dsimp only [coreCost]; omega), hmτ, hnτ, hDel⟩

def initSizes (nSrc mSrc : String) : Com :=
  .seq (.assign nN (.var nSrc)) (.assign inputSize (.var mSrc))

/-- The actual program takes ordinary source CSR and its source size cells. -/
def com (o t nSrc mSrc : String) (R : ℕ) : Com :=
  .seq (initSizes nSrc mSrc) (core o t R)

noncomputable def cost {N : ℕ} (G : SimpleGraph (Fin N)) (M R : ℕ) : ℕ :=
  4 + coreCost G M R

theorem com_run {B N M : ℕ} (G : SimpleGraph (Fin N)) (o t nSrc mSrc : String) (R : ℕ)
    (ho : o ∉ arrays) (ht : t ∉ arrays) (hot : o ≠ t) (hms : mSrc ≠ nN)
    (hB : N * N + 4 * N + 4 ≤ B) (rows : Fin N → List (Fin N)) (off : ℕ → ℕ)
    (σ : Env) (hm : Memory B N σ) (hn : σ.vars nSrc = N) (hs : σ.vars mSrc = M)
    (hc : AgCsrRows o t M rows off σ)
    (hnd : ∀ v, (rows v).Nodup) (hadj : ∀ u v, u ∈ rows v ↔ G.Adj v u) :
    ∃ τ, Run B (com o t nSrc mSrc R) σ τ (cost G M R) ∧ Memory B N τ ∧ τ.vars nN = N ∧
      DelAdjSt ao aj dg mt (mdChain G R).toGraph ∅ τ := by
  have hMB : M < B := by
    have hM : M ≤ N * N := by rw [agPaddedCsr_mass_eq hc hnd hadj]; exact nsOf_le G
    omega
  have hnE : (Expr.var nSrc).evalB B σ = some N := by
    exact (evalB_var (B := B) (by rw [hn]; omega)).trans (congrArg some hn)
  let ρ₁ := σ.setVar nN N
  have hmE : (Expr.var mSrc).evalB B ρ₁ = some M := by
    have hs₁ : ρ₁.vars mSrc = M := by simp [ρ₁, hms, hs]
    exact (evalB_var (B := B) (by rw [hs₁]; exact hMB)).trans (congrArg some hs₁)
  let ρ := ρ₁.setVar inputSize M
  have hinit : Run B (initSizes nSrc mSrc) σ ρ 4 := (Run.assign hnE).seq (Run.assign hmE)
  have hnρ : ρ.vars nN = N := by simp [ρ, ρ₁, show nN ≠ inputSize by decide]
  have hsρ : ρ.vars inputSize = M := by simp [ρ]
  obtain ⟨τ, hr, hmτ, hnτ, hDel⟩ := core_run G o t R ho ht hot hB rows off ρ
    (hm.run hinit) hnρ hsρ (hc.of_eq rfl rfl) hnd hadj
  exact ⟨τ, hinit.seq hr, hmτ, hnτ, hDel⟩

/-- A fixed finite scalar pool, obtained directly from the five concrete
phase programs. Its size is independent of the graph and of the round count. -/
def vars : List String := [nN, inputSize] ++ (base "" "").wvars ++
  (round false).wvars ++ (round true).wvars ++ (finish false).wvars ++ (finish true).wvars

set_option maxRecDepth 8192 in
private theorem base_warrs (o t : String) : (base o t).warrs ⊆ arrays := by
  change (base "" "").warrs ⊆ arrays
  decide

set_option maxRecDepth 8192 in
private theorem round_warrs (b : Bool) : (round b).warrs ⊆ arrays := by
  cases b <;> decide

set_option maxRecDepth 8192 in
private theorem finish_warrs (b : Bool) : (finish b).warrs ⊆ arrays := by
  cases b <;> decide

private theorem loop_warrs (R : ℕ) (b : Bool) : (loop R b).warrs ⊆ arrays := by
  induction R with
  | zero => simp [loop]
  | succ r ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ih ha
    · exact round_warrs (side r b) ha

theorem com_warrs (o t nSrc mSrc : String) (R : ℕ) : (com o t nSrc mSrc R).warrs ⊆ arrays := by
  intro a ha
  simp only [com, initSizes, core, Com.warrs, List.nil_append, List.mem_append] at ha
  rcases ha with ha | ha | ha
  · exact base_warrs o t ha
  · exact loop_warrs R false ha
  · exact finish_warrs (side R false) ha

private theorem base_wvars (o t : String) : (base o t).wvars ⊆ vars := by
  change (base "" "").wvars ⊆ vars
  intro y hy
  simp only [vars, List.mem_append]
  tauto

private theorem round_wvars (b : Bool) : (round b).wvars ⊆ vars := by
  cases b <;> intro y hy <;> simp only [vars, List.mem_append] <;> tauto

private theorem finish_wvars (b : Bool) : (finish b).wvars ⊆ vars := by
  cases b <;> intro y hy <;> simp only [vars, List.mem_append] <;> tauto

private theorem loop_wvars (R : ℕ) (b : Bool) : (loop R b).wvars ⊆ vars := by
  induction R with
  | zero => simp [loop]
  | succ r ih =>
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact ih hy
    · exact round_wvars (side r b) hy

theorem com_wvars (o t nSrc mSrc : String) (R : ℕ) : (com o t nSrc mSrc R).wvars ⊆ vars := by
  intro y hy
  simp only [com, initSizes, core, Com.wvars, List.mem_append] at hy
  rcases hy with (hy | hy) | hy | hy | hy
  · simp only [vars, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at *
    tauto
  · simp only [vars, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at *
    tauto
  · exact base_wvars o t hy
  · exact loop_wvars R false hy
  · exact finish_wvars (side R false) hy

/-- Full concrete augmentation specification. The only scratch information
required at entry is word boundedness and finite raw allocation lengths. -/
theorem com_spec {B N M : ℕ} (G : SimpleGraph (Fin N)) (o t nSrc mSrc : String) (R : ℕ)
    (ho : o ∉ arrays) (ht : t ∉ arrays) (hot : o ≠ t) (hms : mSrc ≠ nN)
    (hB : N * N + 4 * N + 4 ≤ B) (rows : Fin N → List (Fin N)) (off : ℕ → ℕ)
    (hnd : ∀ v, (rows v).Nodup) (hadj : ∀ u v, u ∈ rows v ↔ G.Adj v u) :
    Spec B (fun σ => Memory B N σ ∧ σ.vars nSrc = N ∧ σ.vars mSrc = M ∧
        AgCsrRows o t M rows off σ)
      (com o t nSrc mSrc R)
      (fun σ τ => Memory B N τ ∧ τ.vars nN = N ∧
        DelAdjSt ao aj dg mt (mdChain G R).toGraph ∅ τ ∧
        (∀ a, a ∉ arrays → τ.arrs a = σ.arrs a) ∧
        (∀ y, y ∉ vars → τ.vars y = σ.vars y) ∧
        (∀ a, (τ.arrs a).length = (σ.arrs a).length)) (cost G M R) := by
  rintro σ ⟨hm, hn, hs, hc⟩
  obtain ⟨τ, hr, hmτ, hnτ, hDel⟩ := com_run G o t nSrc mSrc R ho ht hot hms hB rows off σ
    hm hn hs hc hnd hadj
  exact ⟨τ, hr, hmτ, hnτ, hDel,
    fun a ha => hr.frame_arr a (fun hh => ha (com_warrs o t nSrc mSrc R hh)),
    fun y hy => hr.frame_var y (fun hh => hy (com_wvars o t nSrc mSrc R hh)),
    fun a => run_arrs_length_eq hr a⟩

set_option maxRecDepth 8192 in
private theorem base_tapes (o t : String) : ¬ (base o t).reads ∧ (base o t).NoWrite := by
  change ¬ (base "" "").reads ∧ (base "" "").NoWrite
  decide

set_option maxRecDepth 8192 in
private theorem round_tapes (b : Bool) : ¬ (round b).reads ∧ (round b).NoWrite := by
  cases b <;> decide

set_option maxRecDepth 8192 in
private theorem finish_tapes (b : Bool) : ¬ (finish b).reads ∧ (finish b).NoWrite := by
  cases b <;> decide

private theorem loop_tapes (R : ℕ) (b : Bool) : ¬ (loop R b).reads ∧ (loop R b).NoWrite := by
  induction R with
  | zero => change ¬ Com.skip.reads ∧ Com.skip.NoWrite; decide
  | succ r ih =>
    have hh := round_tapes (side r b)
    exact ⟨fun h => h.elim ih.1 hh.1, ih.2, hh.2⟩

/-- The complete program leaves both input and output tapes unchanged. -/
theorem com_tapes (o t nSrc mSrc : String) (R : ℕ) :
    ¬ (com o t nSrc mSrc R).reads ∧ (com o t nSrc mSrc R).NoWrite := by
  have hb := base_tapes o t
  have hl := loop_tapes R false
  have hf := finish_tapes (side R false)
  refine ⟨?_, ⟨trivial, trivial⟩, hb.2, hl.2, hf.2⟩
  simp only [com, initSizes, core, Com.reads, false_or]
  exact fun h => h.elim hb.1 (fun h => h.elim hl.1 hf.1)

/-- Every finite reservation fits the one supplied word bound. -/
theorem capacity_le_wordRoom {B N : ℕ} (hB : N * N + 4 * N + 4 ≤ B) : capacity N ≤ B := by
  dsimp only [capacity]
  omega

/-- Exact coefficients expose all scans and the retained lazy-heap logarithm. -/
theorem baseCost_eq {N : ℕ} (G : SimpleGraph (Fin N)) (M : ℕ) :
    baseCost G M = 224 * M + 56 * arcCount (mdChain G 0) + 127 * N + 91 + KmdPeel N M := by
  simp only [baseCost, agBuildPeelK, agBuildInitK, bldCoreK, agCsrK]
  omega

theorem roundCost_eq {N : ℕ} (D : Orientation N) :
    roundCost D = 289 * arcCount D + 287 * transPairCount D + 439 * fratPairCount D +
      70 * nsOf (fratGraph D) + 56 * arcCount (next D) + 185 * N + 162 +
      KmdPeel N (nsOf (fratGraph D)) := by
  simp only [roundCost, demandCost, agBuildPeelK, agBuildInitK, bldCoreK, greedyCsrCost,
    agsGreedyCost, agCsrK]
  omega

theorem finishCost_eq {N : ℕ} (D : Orientation N) :
    finishCost D = 116 * arcCount D + 126 * nsOf D.toGraph + 101 * N + 89 := by
  simp only [finishCost, agCsrK, agBuildInitK, bldCoreK]
  omega

end Lax3Proofs.Prog.AugMachine
