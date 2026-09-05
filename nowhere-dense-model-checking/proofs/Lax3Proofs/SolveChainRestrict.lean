import Lax3Proofs.SolveChainWin
import Lax3Proofs.SolveBlocksRestrict

/-!
# F6c6 (part 4) — `restrict`, lifted to the windowed contract

The stage the wave-13 seam was actually flagged on: `restrictCom`
builds the **child's** five regions at the child's exact,
data-dependent dimensions (`|S|+1` offsets, `Σ_child deg` targets, …),
and the static layout can only hand it max-size allocations — two
window families at once (the parent's, at the parent's dimensions, and
the child's, at the child's), plus the windowed clean scratch. This
file is `specWindow` on that hard case: `restrictCom_specW` consumes
`ArenaStW` at the parent and *allocation lower bounds* for the child,
and delivers `ArenaStW` at **both** arenas — the child region's valid
prefixes are exactly `MArena.restrict A S`'s data, the parent's are
untouched, the rank scratch's window is clean again. Same command,
same budget `restrictK`.

The window assignment is the union of the three families (child
regions shadow nothing — every name-disjointness is a hypothesis, all
`lv`-dischargeable): `ra ↦ A.N`, the child five at the child's
dimensions, the parent five at the parent's. The cluster region `la`
carries **no** window — `ClusterList` is already prefix-shaped.

With this and the leaf (`SolveChainBot`), both region disciplines the
six stages use — self-owned regions read/written in place, and fresh
regions built at data-dependent sizes — have a worked windowed lift;
the remaining four stages (`isolateCom`, `bfsCom`, `supportsCom`,
`profilesCom`) are instances of the same two patterns (windows at the
level's own dimensions, scratch windows at exact lengths or none).
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning Lax67Proofs.Reasoning.Lib

/-- `ClusterList` reads one array; it transports along agreement. -/
theorem clusterList_of_eq {la : String} {n : ℕ} {S : Set (Fin n)}
    {σ σ' : Env} (h : ClusterList la S σ) (ha : σ'.arrs la = σ.arrs la) :
    ClusterList la S σ' := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by rw [ha]; exact h1, fun t ht => by rw [ha]; exact h2 t ht⟩

set_option maxHeartbeats 800000 in
open Classical in
/-- **`restrict`, at the windowed contract** (the wave-13 seam,
resolved): from the parent's windowed regions, the cluster region, the
schedule cells, child allocations of *at least* the child's dimensions,
and the rank scratch clean on its window, `restrictCom` leaves the
windowed contract at **both** arenas — the child's valid prefixes are
`MArena.restrict A S`, the parent intact, the scratch window clean
again — at the landed budget `restrictK`. The slot-count bound rides
`ns ≤ A.N²` (`ArenaStW.ns_le_sq`), so only carrier-level `< B` bounds
are consumed. -/
theorem restrictCom_specW_suffix {B n₀ Λc ℓp : ℕ} {hb : ℕ} {A : Impl.MArena Λc n₀ ℓp}
    {S : Set (Fin A.N)} {nmP nmC : ArenaNames} {la ra : String}
    (hNB : A.N < B) (hNNB : A.N * A.N < B) (hn0B : n₀ < B)
    (hLB : A.N * Λc < B) (hHB : A.N * ℓp * (hb + 1) < B)
    (hdisj : ∀ x ∈ [nmC.off, nmC.tgt, nmC.col, nmC.up, nmC.hist, ra],
      ∀ y ∈ [nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist, la], x ≠ y)
    (hpair : ([nmC.off, nmC.tgt, nmC.col, nmC.up, nmC.hist, ra]).Pairwise (· ≠ ·))
    (hCn : nmC.nN ∉ rsScalars) (hCs : nmC.nS ∉ rsScalars)
    (hCns : nmC.nN ≠ nmC.nS)
    (hPn : nmP.nN ∉ rsScalars) (hPs : nmP.nS ∉ rsScalars)
    (hPn1 : nmP.nN ≠ nmC.nN) (hPn2 : nmP.nN ≠ nmC.nS)
    (hPs1 : nmP.nS ≠ nmC.nN) (hPs2 : nmP.nS ≠ nmC.nS)
    -- the windowing's own side conditions (all `lv`-dischargeable)
    (hnd5P : ([nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist] :
      List String).Nodup)
    (hla5 : la ∉ ([nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist] :
      List String)) :
    Spec B
      (fun σ => ArenaStW nmP hb A σ ∧
        ClusterList la S σ ∧ σ.vars "rs.k" = S.ncard ∧
        σ.vars "rs.l" = Λc ∧ σ.vars "rs.p" = ℓp ∧ σ.vars "rs.h" = hb ∧
        A.N ≤ (σ.arrs ra).length ∧
        (σ.arrs ra).take A.N = arrOf A.N (fun _ => 0) ∧
        S.ncard + 1 ≤ (σ.arrs nmC.off).length ∧
        (∑ v : Fin (A.restrict S).N, (A.restrict S).G.degree v)
          ≤ (σ.arrs nmC.tgt).length ∧
        S.ncard * Λc ≤ (σ.arrs nmC.col).length ∧
        S.ncard ≤ (σ.arrs nmC.up).length ∧
        S.ncard * ℓp * (hb + 1) ≤ (σ.arrs nmC.hist).length)
      (restrictCom nmP nmC la ra)
      (fun σ σ' => ArenaStW nmC hb (A.restrict S) σ' ∧
        σ'.vars nmC.nS
          = ∑ v : Fin (A.restrict S).N, (A.restrict S).G.degree v ∧
        ArenaStW nmP hb A σ' ∧ σ'.vars nmP.nS = σ.vars nmP.nS ∧
        ClusterList la S σ' ∧ σ'.vars "rs.k" = S.ncard ∧
        A.N ≤ (σ'.arrs ra).length ∧
        (σ'.arrs ra).take A.N = arrOf A.N (fun _ => 0) ∧
        (σ'.arrs ra).drop A.N = (σ.arrs ra).drop A.N)
      (restrictK (Impl.degSum A.G S) S.ncard Λc ℓp hb) := by
  -- the disequalities, spelled out (copies; the originals feed the
  -- landed spec whole)
  have hpo_pt : nmC.off ≠ nmC.tgt := List.rel_of_pairwise_cons hpair (by simp)
  have hpo_pc : nmC.off ≠ nmC.col := List.rel_of_pairwise_cons hpair (by simp)
  have hpo_pu : nmC.off ≠ nmC.up := List.rel_of_pairwise_cons hpair (by simp)
  have hpo_ph : nmC.off ≠ nmC.hist := List.rel_of_pairwise_cons hpair (by simp)
  have hpo_ra : nmC.off ≠ ra := List.rel_of_pairwise_cons hpair (by simp)
  have hpair₁ := List.Pairwise.of_cons hpair
  have hpt_pc : nmC.tgt ≠ nmC.col := List.rel_of_pairwise_cons hpair₁ (by simp)
  have hpt_pu : nmC.tgt ≠ nmC.up := List.rel_of_pairwise_cons hpair₁ (by simp)
  have hpt_ph : nmC.tgt ≠ nmC.hist := List.rel_of_pairwise_cons hpair₁ (by simp)
  have hpt_ra : nmC.tgt ≠ ra := List.rel_of_pairwise_cons hpair₁ (by simp)
  have hpair₂ := List.Pairwise.of_cons hpair₁
  have hpc_pu : nmC.col ≠ nmC.up := List.rel_of_pairwise_cons hpair₂ (by simp)
  have hpc_ph : nmC.col ≠ nmC.hist := List.rel_of_pairwise_cons hpair₂ (by simp)
  have hpc_ra : nmC.col ≠ ra := List.rel_of_pairwise_cons hpair₂ (by simp)
  have hpair₃ := List.Pairwise.of_cons hpair₂
  have hpu_ph : nmC.up ≠ nmC.hist := List.rel_of_pairwise_cons hpair₃ (by simp)
  have hpu_ra : nmC.up ≠ ra := List.rel_of_pairwise_cons hpair₃ (by simp)
  have hpair₄ := List.Pairwise.of_cons hpair₃
  have hph_ra : nmC.hist ≠ ra := List.rel_of_pairwise_cons hpair₄ (by simp)
  -- child/scratch versus parent/list
  have hCP : ∀ x ∈ ([nmC.off, nmC.tgt, nmC.col, nmC.up, nmC.hist, ra] :
      List String), x ≠ nmP.off ∧ x ≠ nmP.tgt ∧ x ≠ nmP.col ∧ x ≠ nmP.up ∧
      x ≠ nmP.hist ∧ x ≠ la := by
    intro x hx
    exact ⟨hdisj x hx nmP.off (by simp), hdisj x hx nmP.tgt (by simp),
      hdisj x hx nmP.col (by simp), hdisj x hx nmP.up (by simp),
      hdisj x hx nmP.hist (by simp), hdisj x hx la (by simp)⟩
  -- the parent five, pairwise
  have hnd5PC := hnd5P
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or] at hnd5PC
  obtain ⟨⟨hot, hoc, hou, hoh⟩, ⟨htc, htu, hth⟩, ⟨hcu, hch⟩, huh, -⟩ := hnd5PC
  have hla5C := hla5
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hla5C
  obtain ⟨hla_o, hla_t, hla_c, hla_u, hla_h⟩ := hla5C
  intro σ hσ
  obtain ⟨hAW, hcl, hk, hl, hp, hhb, hraL, hraC, hCoff, hCtgt, hCcol, hCup,
    hChist⟩ := hσ
  -- the slot count, off the cell, and its bound
  set ns := σ.vars nmP.nS with hns_def
  have hnsB : ns < B := by
    have h1 : σ.vars nmP.nS ≤ A.N * A.N := hAW.ns_le_sq
    omega
  set cns := ∑ v : Fin (A.restrict S).N, (A.restrict S).G.degree v with hcns_def
  -- the window assignment: scratch, then the child five, then the
  -- parent five
  set ws : String → Option ℕ := fun b =>
    if b = ra then some A.N
    else match arenaWs nmC Λc ℓp hb S.ncard cns b with
      | some m => some m
      | none => arenaWs nmP Λc ℓp hb A.N ns b
    with hws_def
  -- evaluating the assignment at the names in play
  have hws_ra : ws ra = some A.N := if_pos rfl
  have hwsC : ∀ b, b ≠ ra →
      ∀ {m : ℕ}, arenaWs nmC Λc ℓp hb S.ncard cns b = some m → ws b = some m := by
    intro b hbra m hbm
    show (if b = ra then some A.N else _) = some m
    rw [if_neg hbra, hbm]
  have hwsP : ∀ b, b ≠ ra → b ≠ nmC.off → b ≠ nmC.tgt → b ≠ nmC.col →
      b ≠ nmC.up → b ≠ nmC.hist →
      ws b = arenaWs nmP Λc ℓp hb A.N ns b := by
    intro b h0 h1 h2 h3 h4 h5
    show (if b = ra then some A.N else _) = _
    rw [if_neg h0, arenaWs_none h1 h2 h3 h4 h5]
  -- the five child window values
  have hwsCoff : ws nmC.off = some (S.ncard + 1) :=
    hwsC _ hpo_ra arenaWs_off
  have hwsCtgt : ws nmC.tgt = some cns :=
    hwsC _ hpt_ra (arenaWs_tgt (Ne.symm hpo_pt))
  have hwsCcol : ws nmC.col = some (S.ncard * Λc) :=
    hwsC _ hpc_ra (arenaWs_col (Ne.symm hpo_pc) (Ne.symm hpt_pc))
  have hwsCup : ws nmC.up = some S.ncard :=
    hwsC _ hpu_ra
      (arenaWs_up (Ne.symm hpo_pu) (Ne.symm hpt_pu) (Ne.symm hpc_pu))
  have hwsChist : ws nmC.hist = some (S.ncard * ℓp * (hb + 1)) :=
    hwsC _ hph_ra (arenaWs_hist (Ne.symm hpo_ph) (Ne.symm hpt_ph)
      (Ne.symm hpc_ph) (Ne.symm hpu_ph))
  -- the five parent window values
  have hwsPat : ∀ b, b = nmP.off ∨ b = nmP.tgt ∨ b = nmP.col ∨ b = nmP.up ∨
      b = nmP.hist → ws b = arenaWs nmP Λc ℓp hb A.N ns b := by
    intro b hb
    have hmem : ∀ x ∈ ([nmC.off, nmC.tgt, nmC.col, nmC.up, nmC.hist, ra] :
        List String), x ≠ b := by
      intro x hx
      obtain ⟨e1, e2, e3, e4, e5, -⟩ := hCP x hx
      rcases hb with rfl | rfl | rfl | rfl | rfl
      · exact e1
      · exact e2
      · exact e3
      · exact e4
      · exact e5
    exact hwsP b (Ne.symm (hmem ra (by simp))) (Ne.symm (hmem nmC.off (by simp)))
      (Ne.symm (hmem nmC.tgt (by simp))) (Ne.symm (hmem nmC.col (by simp)))
      (Ne.symm (hmem nmC.up (by simp))) (Ne.symm (hmem nmC.hist (by simp)))
  have hwsPoff : ws nmP.off = some (A.N + 1) := by
    rw [hwsPat nmP.off (Or.inl rfl)]; exact arenaWs_off
  have hwsPtgt : ws nmP.tgt = some ns := by
    rw [hwsPat nmP.tgt (Or.inr (Or.inl rfl))]; exact arenaWs_tgt (Ne.symm hot)
  have hwsPcol : ws nmP.col = some (A.N * Λc) := by
    rw [hwsPat nmP.col (Or.inr (Or.inr (Or.inl rfl)))]
    exact arenaWs_col (Ne.symm hoc) (Ne.symm htc)
  have hwsPup : ws nmP.up = some A.N := by
    rw [hwsPat nmP.up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
    exact arenaWs_up (Ne.symm hou) (Ne.symm htu) (Ne.symm hcu)
  have hwsPhist : ws nmP.hist = some (A.N * ℓp * (hb + 1)) := by
    rw [hwsPat nmP.hist (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
    exact arenaWs_hist (Ne.symm hoh) (Ne.symm hth) (Ne.symm hch) (Ne.symm huh)
  -- the cluster region carries no window
  have hws_la : ws la = none := by
    have hmem : ∀ x ∈ ([nmC.off, nmC.tgt, nmC.col, nmC.up, nmC.hist, ra] :
        List String), x ≠ la := fun x hx => (hCP x hx).2.2.2.2.2
    rw [hwsP la (Ne.symm (hmem ra (by simp))) (Ne.symm (hmem nmC.off (by simp)))
      (Ne.symm (hmem nmC.tgt (by simp))) (Ne.symm (hmem nmC.col (by simp)))
      (Ne.symm (hmem nmC.up (by simp))) (Ne.symm (hmem nmC.hist (by simp)))]
    exact arenaWs_none hla_o hla_t hla_c hla_u hla_h
  -- the allocation fits
  have hFits : FitsW ws σ := by
    intro b m hbm
    by_cases h0 : b = ra
    · subst h0
      rw [hws_ra] at hbm
      cases hbm
      exact hraL
    by_cases h1 : b = nmC.off
    · subst h1; rw [hwsCoff] at hbm; cases hbm; exact hCoff
    by_cases h2 : b = nmC.tgt
    · subst h2; rw [hwsCtgt] at hbm; cases hbm; exact hCtgt
    by_cases h3 : b = nmC.col
    · subst h3; rw [hwsCcol] at hbm; cases hbm; exact hCcol
    by_cases h4 : b = nmC.up
    · subst h4; rw [hwsCup] at hbm; cases hbm; exact hCup
    by_cases h5 : b = nmC.hist
    · subst h5; rw [hwsChist] at hbm; cases hbm; exact hChist
    · rw [hwsP b h0 h1 h2 h3 h4 h5] at hbm
      exact hAW.fits b m hbm
  -- the truncation satisfies the landed precondition
  have hstP : ArenaSt nmP hb A (winA ws σ) := by
    refine arenaSt_of_eq hAW.st rfl rfl ?_ ?_ ?_ ?_ ?_
    · exact arrs_winA_congr (hwsPat nmP.off (by simp)) σ
    · exact arrs_winA_congr (hwsPat nmP.tgt (by simp)) σ
    · exact arrs_winA_congr (hwsPat nmP.col (by simp)) σ
    · exact arrs_winA_congr (hwsPat nmP.up (by simp)) σ
    · exact arrs_winA_congr (hwsPat nmP.hist (by simp)) σ
  -- run the landed spec on the truncation, pad the derivation back
  obtain ⟨σ', hrun, hfit', hQ, hlenEq, htail⟩ :=
    (specWindow (restrictCom_spec (B := B) (A := A) (S := S) (nmP := nmP)
      (nmC := nmC) (la := la) (ra := ra) (ns := ns) hNB hnsB hn0B hLB hHB
      hdisj hpair hCn hCs hCns hPn hPs hPn1 hPn2 hPs1 hPs2) ws) σ
      ⟨hFits, hstP, rfl,
        clusterList_of_eq hcl (arrs_winA_none hws_la σ),
        hk, hl, hp, hhb,
        by rw [arrs_winA_some hws_ra]; exact hraC,
        length_arrs_winA hwsCoff hCoff,
        length_arrs_winA hwsCtgt hCtgt,
        length_arrs_winA hwsCcol hCcol,
        length_arrs_winA hwsCup hCup,
        length_arrs_winA hwsChist hChist⟩
  obtain ⟨hstC', hcns', hstP', hns', hcl', hk', hra'⟩ := hQ
  refine ⟨σ', hrun, ?_, hcns', ?_, hns', ?_, hk', ?_, ?_, ?_⟩
  · -- the child's windowed contract, at the child's dimensions
    have hcell : σ'.vars nmC.nS = cns := hcns'
    constructor
    · show FitsW (arenaWs nmC Λc ℓp hb (A.restrict S).N (σ'.vars nmC.nS)) σ'
      rw [hcell]
      show FitsW (arenaWs nmC Λc ℓp hb S.ncard cns) σ'
      intro b m hbm
      have hb5 := arenaWs_some_elim hbm
      rcases hb5 with rfl | rfl | rfl | rfl | rfl
      · rw [arenaWs_off] at hbm; cases hbm; exact hfit' _ _ hwsCoff
      · rw [arenaWs_tgt (Ne.symm hpo_pt)] at hbm; cases hbm
        exact hfit' _ _ hwsCtgt
      · rw [arenaWs_col (Ne.symm hpo_pc) (Ne.symm hpt_pc)] at hbm; cases hbm
        exact hfit' _ _ hwsCcol
      · rw [arenaWs_up (Ne.symm hpo_pu) (Ne.symm hpt_pu) (Ne.symm hpc_pu)]
          at hbm
        cases hbm
        exact hfit' _ _ hwsCup
      · rw [arenaWs_hist (Ne.symm hpo_ph) (Ne.symm hpt_ph) (Ne.symm hpc_ph)
          (Ne.symm hpu_ph)] at hbm
        cases hbm
        exact hfit' _ _ hwsChist
    · show ArenaSt nmC hb (A.restrict S)
        (winA (arenaWs nmC Λc ℓp hb (A.restrict S).N (σ'.vars nmC.nS)) σ')
      rw [hcell]
      show ArenaSt nmC hb (A.restrict S)
        (winA (arenaWs nmC Λc ℓp hb S.ncard cns) σ')
      refine arenaSt_of_eq hstC' rfl rfl ?_ ?_ ?_ ?_ ?_
      · exact arrs_winA_congr (arenaWs_off.trans hwsCoff.symm) σ'
      · exact arrs_winA_congr
          ((arenaWs_tgt (Ne.symm hpo_pt)).trans hwsCtgt.symm) σ'
      · exact arrs_winA_congr
          ((arenaWs_col (Ne.symm hpo_pc) (Ne.symm hpt_pc)).trans
            hwsCcol.symm) σ'
      · exact arrs_winA_congr
          ((arenaWs_up (Ne.symm hpo_pu) (Ne.symm hpt_pu)
            (Ne.symm hpc_pu)).trans hwsCup.symm) σ'
      · exact arrs_winA_congr
          ((arenaWs_hist (Ne.symm hpo_ph) (Ne.symm hpt_ph) (Ne.symm hpc_ph)
            (Ne.symm hpu_ph)).trans hwsChist.symm) σ'
  · -- the parent's windowed contract, preserved
    have hcell : σ'.vars nmP.nS = ns := hns'
    constructor
    · show FitsW (arenaWs nmP Λc ℓp hb A.N (σ'.vars nmP.nS)) σ'
      rw [hcell]
      intro b m hbm
      have hb5 := arenaWs_some_elim hbm
      rcases hb5 with rfl | rfl | rfl | rfl | rfl <;>
        exact hfit' _ m ((hwsPat _ (by simp)).trans hbm)
    · show ArenaSt nmP hb A
        (winA (arenaWs nmP Λc ℓp hb A.N (σ'.vars nmP.nS)) σ')
      rw [hcell]
      refine arenaSt_of_eq hstP' rfl rfl ?_ ?_ ?_ ?_ ?_ <;>
        exact (arrs_winA_congr (hwsPat _ (by simp)) σ').symm
  · -- the cluster region, untouched
    exact clusterList_of_eq hcl' (arrs_winA_none hws_la σ').symm
  · -- the scratch allocation's length is preserved
    rw [hlenEq ra]
    exact hraL
  · -- the scratch window is clean again
    have := hra'
    rwa [arrs_winA_some hws_ra] at this

  · exact htail ra A.N hws_ra

open Classical in
/-- The original windowed contract, forgetting only the preserved rank suffix. -/
theorem restrictCom_specW {B n₀ Λc ℓp : ℕ} {hb : ℕ} {A : Impl.MArena Λc n₀ ℓp}
    {S : Set (Fin A.N)} {nmP nmC : ArenaNames} {la ra : String}
    (hNB : A.N < B) (hNNB : A.N * A.N < B) (hn0B : n₀ < B)
    (hLB : A.N * Λc < B) (hHB : A.N * ℓp * (hb + 1) < B)
    (hdisj : ∀ x ∈ [nmC.off, nmC.tgt, nmC.col, nmC.up, nmC.hist, ra],
      ∀ y ∈ [nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist, la], x ≠ y)
    (hpair : ([nmC.off, nmC.tgt, nmC.col, nmC.up, nmC.hist, ra]).Pairwise (· ≠ ·))
    (hCn : nmC.nN ∉ rsScalars) (hCs : nmC.nS ∉ rsScalars)
    (hCns : nmC.nN ≠ nmC.nS)
    (hPn : nmP.nN ∉ rsScalars) (hPs : nmP.nS ∉ rsScalars)
    (hPn1 : nmP.nN ≠ nmC.nN) (hPn2 : nmP.nN ≠ nmC.nS)
    (hPs1 : nmP.nS ≠ nmC.nN) (hPs2 : nmP.nS ≠ nmC.nS)
    -- the windowing's own side conditions (all `lv`-dischargeable)
    (hnd5P : ([nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist] :
      List String).Nodup)
    (hla5 : la ∉ ([nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist] :
      List String)) :
    Spec B
      (fun σ => ArenaStW nmP hb A σ ∧
        ClusterList la S σ ∧ σ.vars "rs.k" = S.ncard ∧
        σ.vars "rs.l" = Λc ∧ σ.vars "rs.p" = ℓp ∧ σ.vars "rs.h" = hb ∧
        A.N ≤ (σ.arrs ra).length ∧
        (σ.arrs ra).take A.N = arrOf A.N (fun _ => 0) ∧
        S.ncard + 1 ≤ (σ.arrs nmC.off).length ∧
        (∑ v : Fin (A.restrict S).N, (A.restrict S).G.degree v)
          ≤ (σ.arrs nmC.tgt).length ∧
        S.ncard * Λc ≤ (σ.arrs nmC.col).length ∧
        S.ncard ≤ (σ.arrs nmC.up).length ∧
        S.ncard * ℓp * (hb + 1) ≤ (σ.arrs nmC.hist).length)
      (restrictCom nmP nmC la ra)
      (fun σ σ' => ArenaStW nmC hb (A.restrict S) σ' ∧
        σ'.vars nmC.nS
          = ∑ v : Fin (A.restrict S).N, (A.restrict S).G.degree v ∧
        ArenaStW nmP hb A σ' ∧ σ'.vars nmP.nS = σ.vars nmP.nS ∧
        ClusterList la S σ' ∧ σ'.vars "rs.k" = S.ncard ∧
        A.N ≤ (σ'.arrs ra).length ∧
        (σ'.arrs ra).take A.N = arrOf A.N (fun _ => 0))
      (restrictK (Impl.degSum A.G S) S.ncard Λc ℓp hb) := by
  refine (restrictCom_specW_suffix (B := B) (A := A) (S := S)
    (nmP := nmP) (nmC := nmC) (la := la) (ra := ra)
    hNB hNNB hn0B hLB hHB hdisj hpair hCn hCs hCns hPn hPs
    hPn1 hPn2 hPs1 hPs2 hnd5P hla5).post ?_
  rintro σ σ' _ ⟨hC, hnsC, hP, hnsP, hcl, hk, hlen, hclean, _⟩
  exact ⟨hC, hnsC, hP, hnsP, hcl, hk, hlen, hclean⟩

end Lax3Proofs.Prog
