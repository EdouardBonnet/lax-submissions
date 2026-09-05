# ND-MC execution ledger

The *mutable* half of the campaign state. `execution-plan.md` says what each
leaf is; this says where each one stands. `/ndmc` reads both.

**Keep this accurate after every boundary.** A compacted context or a fresh
session recovers the campaign from this file plus `git log` and nothing else.

Status values: `ready` (dependencies met, may be dispatched) · `waiting`
(dependency not yet `done`) · `wip` (dispatched, worker running) · `review`
(worker returned, supervisor reviewing) · `done` (landed on `main`) ·
`blocked` (cannot proceed; the note says what would unblock it).

| leaf | what it closes | status | wave | commit | note |
|---|---|---|---|---|---|
| E0 | cover time bound stated as an assumption; §8/§9 rewrite | done | w1 | 8709c19 | `CoverSpec.CoverOrderingTime`; only the `time` field is assumed, cover/degree derived; §8 0b + §9 O7 rewritten, pins spot-checked |
| E1 | cover clusters are path-closed (§5) | done | w1 | 8709c19 | `ClusterPaths`; delivered through to the induced graph, ~110 lines against the ~10-line estimate |
| E2 | `ctr` and the π-min identity (§4) | done | w1 | 8709c19 | `CoverCentres`; `ctr` is noncomputable (`Finset.min'` via `π`) — E12 must implement it; ~217 lines against the ~6-line estimate |
| E3 | the edge half of (★) (§7) | done | w1 | 8709c19 | `CoverEdgeSum.sum_clusterWeight_le_rpow`; hypotheses exactly `0 ≤ c_D`, `0 ≤ δ`, `1 ≤ ‖A‖`; ceiling carried into `c_D+1` |
| E4 | the cost recurrence, amended and slackened (§7) | done | w2 | b0444fa | `cost_root_le_chosenK`: `K^{ℓ+1}·n^{1+ε}` at `δ=ε/(ℓ+2)`, **no condition on `c`**; `star_of_cover_degree` bridges (★) to E3 |
| E5 | `ReachedR` generalized to `S`-moves (§8.2) | done | w2 | b0444fa | `ReachedS`; descend batch is an equality; `splitterWins_of_reachedS` via mixed histories — no `splitterWins_anti` needed |
| E6 | carrier transport for `ReachedR` (§9) | done | w3 | 55ba312 | `ArenaTransport`: one pushforward covers bijection + isolated cases; §5 line 8 was a **type error** — record kept at the root carrier, §5/§9 rewritten |
| E7 | the compaction lemma (§5 step 3′, §8.4a) | done | w2 | b0444fa | `sat_compact_iff_satWithin_deleteVerts_compl`; plain `Sat↔Sat` is false (`exU` sees isolated verts) — `SatWithin` is the true form; no order hypothesis |
| E8 | locality decomposition as a function (§8.3, O2) | done | w2 | b0444fa | `localityBC` via the Assembly discharge (axiom-free); `rfl`-irrelevant in the rank witness; atom lists for E9 |
| E9 | the abstract algorithm — **hard gate** (§8.4) | done | w4 | bf7baef | did **not** split: `Driver*` (5 files, 2125 lines); `tables_correct` unconditional, `mc_correct` for every ordering, `mkSetup_dcost_root_le` from `CoverOrderingTime` |
| E10 | unrolling the depth-`ℓ` recursion (§8.4b) | done | w5 | a1d9294 | `Unroll`; iterative form = `tables` by fuel induction; frames **static**, peak `(ℓ+1)(2+c_S)·n²` absorbed by the squared guarantee; `mkSetup_memLeaf_eq_bot` closes E9's deferred composition |
| E11 | the `Refine` tower probe (§8.5) | done | w2 | b0444fa | charge is alive-summed + carrier-sized init per call: restrict-then-BFS **forced**, mask ≠ restrict; `SpaceBudgetProbe` is §11's natural home |
| E12 | `Arena` implementation (§8.6) — **split** | done (part) | w5 | a1d9294 | `Impl{Scatter,Bot,Bfs}` landed: guarded scatter (`t=0` guard is the cost statement), `botEval = Sat ⊥`, BFS at `B₀` with `chargeB0_total = 2‖B₀‖+d+2`; remainder is E12b/c/d |
| E12b | `restrict` + `isolate` (§6.1) | done | w6 | 84ae503 | scratch array **one per node**, amortization visible in the cost model; charge is `Σ_{s∈S} deg_A(s)`-shaped — `O(‖A[S]‖+|S|)` is FALSE (`K_{3,n−3}`) |
| E12c | the `cover` sweep + computed `ctr` (§6.2 ⟨B⟩) | done | w6 | 84ae503 | GKS's peeling sweep, `N_</N_>` split repr; identities to `Driver.cluster` and `CoverCentres.ctr`; (★) as GKS's accounting; expect 2 runs, schedule first |
| E12d | `recordProfiles` (§6.3) | done | w6 | 84ae503 | iterate single-source `chargeB0` `(m+L)` times; rows cumulative, measured in `preG` **before** isolation; identity target `Driver.childCol`'s slot families |
| E13 | compose to the headline (§8.7) | done | w7 | b2df405 | `headline_abstract`/`headline_encoded`: full iff at `FirstOrder.Sat`, cost at `(x.length+1)^{1+ε}` under `CoverOrderingTime` alone; remainder mapped in-file |
| F1 | ordering routine + `data` discharge | done | w8 | 2206f72 | **no hypothesis at all**; minimality via `sInf`; new `greedyStep` (landed `tightStep` fails `PiIncreasing` on greedy rounds); F5 owes exactly `time` |
| F2 | the CSR front end | done | w8 | 2206f72 | round trip is a graph **equality**; `chargeParse` total = `x.length` exactly |
| F3 | the frame program (NREST) | done | w8 | 2206f72 | `frameProg_le_spec`: the table IS `frameEval` given the two slots; charge ledger named; comparison deferred to F3c |
| F3b | multi-source profiles via a virtual source | done | w9 | 7ed61d3 | bridge survives source-revisits (strong recursion); `recordProfilesMS_eq_childCol` against the frozen target; marker free; §6.3's `(m+L)` shape restored |
| F3c | the program's charge, closed to the `T`-clause | done | w10 | 9b4cdfa | `exists_mcChargeMS_T` with **no `CoverOrderingTime` assumption**; route (b) forced (landed budget fails the headline — MS column swap + transfer lemmas); direct-κ vs `dcost` impossible; empty centres make node-aggregate essential |
| F4 | the driver program (ℓ+1 levels) | done | w9 | 7ed61d3 | `driverProg_le_spec` by level induction; `mcProg_headline` at the axiom's semantic object; fuel-0 edged branch dead on the class |
| F5 | the cover pipeline's cost, proved | done | w9 | 7ed61d3 | **`coverOrderingTime_of_nowhereDense`** with the honest witness `timedGreedyRoutine`; true exponent `1+δ`; no sort (the peel ranks); vacuity guarded (`le_chainCharge`) |
| F6 | codegen to the machine — **split** | done (part) | w10 | 9b4cdfa | `mc_computesInTime_of_solveSpec`: ONE named obligation (`SolveSpec`) from the axiom; parse `Spec` discharged; `mcD` verbatim; word-size condition spent (`mcB = q(|x|+1)²`) |
| F6b | arena materialization + profiles reroute + root eval | done | w11 | c4cde5b | `frameProgMS` at the MS budget; the CSR cells ARE the root arena; `solveSpec_of_rest` leaves one obligation; the sweep's BFS cut to F6d |
| F6c | the `ℓ+1` driver blocks — run 1 | done (part) | w11 | 7bad766 | frame contract + greedyScatter fully IMP+ (with an inlined marking BFS) + botEval's schedule fix; direct `Spec`-kit route validated; continuation split into F6c2/F6c3 + the post-F6d stages (supports, profilesMS, cover sweep, readback, frame/driver composition) |
| F6c2 | restrict + isolate as IMP+ | done | w13 | 7736b66 | both landed; fill amortized at the **parent** degree; forced the `setEquiv` repin (sorted `orderIsoOfFin` — the docstring lied about its own theorem, lesson #6); exact-length-region seam flagged for the composer |
| F6c3 | block 0's IMP+ table fill | done | w13 | 7736b66 | `botCom_spec` at the frame contract, table at `Sat A.G` under `hbot`; edgelessness a hypothesis, no machine edge scan; budget in `botC`'s shape |
| F6d | shared IMP+ BFS: generalize `markCom` | done | w12 | ab14f30 | `bfsCom_spec` literally at `ImplBfs.BallTable` (+ sentinel bound clause), `bfsK ≤ 69·(d+1)·(N+ns+1)`; markCom's invariant minus the mark coupling; gate green |
| F6c4 | supports stage as IMP+ | done | w13 | 7736b66 | least parent by min-in-cell; stored lists = `Impl.descend` verbatim; `d+1 ≤ hb` is the slot-capacity hypothesis the composer supplies |
| F6c5 | profilesMS stage as IMP+ | done | w13 | 7736b66 | lands under the frozen identity with `preG` by `rfl`; marker at zero BFS; per-class exact-length `vt` regions — the composer's windowed-contract seam |
| F6c6 | the frame + `ℓ+1` chain: close `SolveSpec` | done (part) | w14 | b3a5502 | windowed contract landed (`bigStepB_padA`, `specWindow`, `ArenaStW`/`TableBitsW`); botCom/restrictCom lifted; level chain proved (`chainCom_blockSpec`); leaf guard machine-tested (`ns_zero_iff_bot` ⟺ edgeless); **`solveSpec_of_chain`**: `SolveSpec` for `matCom ; rootLoadCom ; chainCom ; topCom scatCom` conditional on FOUR residuals — root `BlockSpec` (= FrameStep), root load, `TopScatterSpec`, `Adm` — budget `Ks`, `KsChargeBridge` named; supervisor decision: supports runs at radius **2R** (§5 l.17), `ProgFrame.supportsC`'s `S.R` slot is the stale figure |
| F6c7 | discharge the four chain residuals | done (part) | w15 | c148266 | all five stage lifts landed (`bfsCom/supportsCom/scatterCom/isolateCom/profilesCom_specW` — radius free, 2R instantiable; profiles at `preG`, batch exactly `mb`); `canonBotB` with every name condition off `lv`; **`solveSpec_closed`** from THREE residuals (`FrameStepAll`, `RootLoadSpec`, `TopScatterAll`) + Adm-side root facts; axioms = landed baseline; finding: `ProfNames.Ok` lacks up/hist freshness — taken as `lv`-dischargeable hypotheses; `KB` unpinned until FrameStep. Remainder → F6c8 |
| F6c8 | FrameStep glue + the last three residuals | done (part) | w16 | 1fb64b9 | guard/leaf branch, cover→loop seam, and the centre loop PROVED (`CLInv` invariant, budget = per-centre **sum** via tail-sum potential); `frameStepAll_of_cover_step` concludes verbatim `FrameStepAll` from `CoverAllIn` + `CentreStepAll`; `rootLoadSpec_of_csrLoad` concludes verbatim `RootLoadSpec` from `RootCsrLoadAll`. **Finding 1 (scope)**: `EncodesGraph` permits duplicate neighbours, `GraphCsr` forbids — root load must dedup (mark-array, O(n+m)). **Finding 2 (statement gap)**: `TopScatterSpec` pre is `BlockPost` alone, no scratch lengths — IMP+ can't allocate, no honest `scatCom` speccable; fix = length-only top-scratch descriptor threaded via `hscrLen` pattern. Remainder → F6c9a/b |
| F6c9a | `CentreStepAll` — the per-centre body | done (part) | w17 | b0c947c | the recursion window DISCHARGED: `centreStepAll_of_prep_read` concludes verbatim `CentreStepAll` at `centreBody prepC readC` from two straight-line residuals — **`CentrePrepAll`** (child construction: cluster-row read → restrict → BFS 2R → supports → profilesMS at `preG` → isolate → load, delivering verbatim `BlockPre` at `childArena`) and **`CentreReadAll`** (scatters on isolated child + `bcExpr` readback, `CLInv u → CLInv (u+1)`); parent invariant crosses the inner block by `Spec.frame` + level-name freshness; budget `KP + KB(child) + KR`; `frameStepAll_of_cover_prep_read` end-to-end. Verified non-gaps: `restrictEmb`/`childEquiv` `rfl`; `inv_child` any-centre ⇒ **F7's `Adm` must be `Inv`-based**. Remainder → F6c10 |
| F6c9b | TopScatter fix + `CoverAllIn` + `RootCsrLoadAll` | done (part) | w18 | f7f9f43 | the statement fix landed: `TopScatterSpec` pre gains a length-only `Scr` (threaded from `Scr 0` via `specArrsLength` + one `hscrLen0` hypothesis; conclusions/budgets unchanged); **`topScatterAll_of` discharges verbatim `TopScatterAll`** with a real per-atom program (glue + column extraction to `FinBitsW` + landed `scatterCom` verbatim + bit store; `av` reads exactly the written bits; `unrollAux ≡ unrolledTables` by `rfl`); duplicated atoms harmless. `CoverAllIn`/`RootCsrLoadAll` not started — **flag: the GKS sweep needs a peel-masked BFS** (`bfsCom_specW` computes distances in the full arena graph). Remainder → F6c10a/b |
| F6c10a | `CentrePrepAll` + `CentreReadAll` | done (part) | w19 | 945aeef | the seams PROVED: `unrollAux_succ_of_ne_bot` (recursive table = `RowEval` after the leaf guard), `tablePartial_succ`, `bcExprA` full evaluation (compiled row = `RowEval`'s bit under `1 < B`), atom membership in `levelFml (j+1)`; `centreStepAll_of_childLoad_rows` concludes verbatim `CentreStepAll` from TWO machine residuals — **`ChildLoadAll`** (restrict→bfs 2R→supports→profilesMS→isolate chain + glue, delivering the windowed contract at `Impl.ofArena childArena` with `htabF (j+1)`, level-`j` names untouched) and **`ReadRowsAll`** (write exactly the centre-`u` rows at `RowEval`'s bits). F7 notes: channel content per child arena; descriptor tower guarded to `j+1 ≤ depth`. Remainder → F6c11 |
| F6c10b | `CoverAllIn` + `RootCsrLoadAll` | done (part) | w20 | d7f22ca | **`RootCsrLoadAll` DISCHARGED outright** (`rootCsrLoadAll_csrLoadCom`: row-stamped mark-array dedup, O(n+m) at `70|x|+20`; scope findings — `adj_iff` is an iff ⇒ no self-loops, both directions present, dedup only). `CoverAllIn` split at its own seam: `coverAllIn_of_order_sweep` verbatim from **`CovOrderIn`** (rank array of `ord`'s order) + **`CovSweepIn`** (rank array → `CoverStageSpec` post). Findings: ordering must be computed inside `covC`; **`timedGreedyRoutine` NOT machine-matchable** (choice-picked `elimRank`) — headline binds `∃ ord`, F7 instantiates a machine-defined min-degree peel (attains `elimBound`, sInf clauses stay provable; residuals parametric in `ord`); peeled BFS must be a frontier-queue over a **deletable adjacency structure** (full-pass rounds bust `sweepCharge`). Remainder → F6c11 |
| F6c11 | the four machine passes | done (part) | w21+w22 | a2e8b61 | w21: `machChild_eq_ofArena` + `ChildLoadParts` + `htabF` canonicity kit + readback bit bridges (see w21 note in log). w22: `DelAdjSt` (deletable adjacency, full bridge algebra; deletion priced at CURRENT degree inside `sweepCharge`), `covSweepIn_of_build_peel` verbatim from **`CovAdjBuildIn`**+**`CovPeelIn`**; **`mdOrderingRoutine R`** — the machine ordering (min-degree peel, `mdRank` replacing the choice-picked `elimRank`) with the FULL six-clause `AugChainData` proved (`mdRank_backDegLE` resolves clauses 5–6: optimal elimination of the AUGMENTED graph); `covOrderIn_of_aug_mdPeel` verbatim from **`CovAugAdjIn`**+**`CovMdPeelIn`**. Remaining SIX program residuals → F6c12 |
| F6c12 | the six machine programs | wip | w60 | — | per-centre: (1) `ChildLoadPartsAll` — **DONE** (`2fe7db5`, `SolveMachPrepRun`): complete supports/profile/colour/isolate tail and oldest-first channels, guarded admissible `ChildLoadAll` seam; honest `prepK` still includes the per-child rank reset, to be removed before the global cost bound, (2) `ReadRowsAll` — **DONE** (w60 worker, landed with this row's edit): `SolveSegReadRun.lean` (~1540 lines), headline `readRowsAll_of` verbatim + a compile-time consumer-fit `example` through `centreReadAll_of_rows`; axioms = the landed `topScatterAll_of` baseline; extra hypotheses all F7-suppliable kinds with precedents (hq, depth-guarded word bounds, Scr length clauses, name freshness incl. `hccm_tab`); budget `readSegK` closed-form (atoms × (column copy + scatterK) + cluster-row states × row-eval); cover: (3) `CovAdjBuildIn` — **DONE** (w60 worker, landed with this row's edit): `SolveSweepBuild.lean` (2213 lines), headline `covAdjBuildIn_bldCom` verbatim, `Sbd := bldSbd` length-only, `Spl` universal via the `hSplT` transport; owner-advancing CSR scan places both directed copies and crosses the mates in one step (no row-sortedness assumed — `GraphCsr` promises none); budget `70·ns + 50·N + 30`; axioms = the landed consumer's set, (4) `CovPeelIn` — **DONE** (`3ad2ed7`, `SolveSweepPeel`): exact centres and ascending cluster CSR via global stable counting passes; `peelK` bounded by `640*sweepCharge + 256*N + 256`, (5) `CovAugAdjIn` (augmentation rounds leaving `DelAdjSt` of the augmented graph; each `mdChain` round embeds a full `mdRank (fratGraph ·)` peel, so this **consumes (3)+(6)'s kits — w62**), (6) `CovMdPeelIn` — **DONE** (w60 worker, landed with this row's edit): `SolveSweepMdPeel.lean` (~4130 lines), headline `covMdPeelIn_mdPeelCom` verbatim at the lazy-heap route (first valid pop = `minDegVert` via exactly-one-witness-entry + encoded-key minimality; ranks down from N−1, `mdPerm_val` definitional); **parametric core `mdPeelCore_spec`** exported for the aug leaf (any F, any names, `N²+4N+4 ≤ B`); budget `KmdPeel N ns = 100(N+ns)(log₂(N+ns+1)+1)+100N+100` with `nsOf_eq_sum_ncard` = the pinned nsAug currency; hypotheses hq + one Nodup bundle + hSswT; axioms = the landed consumer's set. Supervisor corrections at landing (the w13 pattern): `rowBody`→`mpRowBody` (collided with SolveSegReadRun's), `getD_set_self/ne` privatized (BUILD's are private), and the two Run-length lemmas relocated from `_root_.Lax13Proofs.*` into the package namespace (`bigStep_length_arrs`/`spec_arrLengths` — the audit rejects foreign-namespace decls); then KB pin + `KsChargeBridge`, then F7. NOTE: `SolveSweepAdj` §3's free-standing `AdjBuildIn`/`AdjDeleteIn` contracts are **defective as stated** (quantify over every `N` with no relation to `B`; IMP+ has no length primitive) — the six residuals do not consume them; workers bypass, sizes come from the arena's named cells |
| F6c12p | canonicalize the batch (the ⟨D⟩ repair) | done | w61 | 9c66491 | **Finding (statement gap, the 7th read-the-theorem instance)**: `DriverArena.batchRoot = SplitterWin.genSet`, whose `pathSet` is `(withinDist_iff.mp h).choose.support` — a choice-picked walk no program can be proved to output; `childArena.G = deleteVerts preG (range batchFn)` and `childCol` both depend on it, so residual (1) is undischargeable as reachable-from-machine. §5 l.19 always meant *recorded* supports. Governing obligation: `DriverCorrect:487`'s `hwalk` — per round `er ∈ hist` with `WithinDist er.arena (2R) er.vtx (A.up u)`, a walk **in `er.arena` (the round graph)** whose `Ximg`-trace lies in the batch; current-graph or `preG`-graph walks do NOT discharge it as stated (round graphs are supersets — walks don't transport down). Two candidate repairs, worker investigates then implements: **(α)** repin `SplitterWin.pathSet` itself to the canonical min-index-parent gradient walk (needs `[LinearOrder V]`; `pathSet_spec`/`ncard_le`/`genSet` statements unchanged, consumers re-elaborate verbatim; machine later reads per-level persisted 2R ball/parent tables of each round graph — mirrors the landed `ballDist`/`descendTab` w21 kit, `up` maps are StrictMono by the sorted `setEquiv` chain so min-index parents commute with the root renaming); **(α′)** same but first check whether `reachedS_descend`'s proof can take walks in a graph between current and round (hypothesis-weakening = theorem-strengthening, legitimate) — if yes the channel's own `preG` walks serve and the machine side is free; **(A)** record the supports in the object (a `chan` field on `Arena`, `Inv` clause for round-graph validity — heavier cascade through E9/E10 arena constructions; the machine `MArena` already has `chan`). **LANDED as (α)+: canonical min-parent gradient `pathSet` (new kit `DriverBatchCanon`, mirror of `Prog.ballDist`/`Impl.parents`/`Impl.descend`, with `IsBallTable` uniqueness and the StrictMono transport `pathList_map`) AND the channel records the graph the walks live in** — `childArena.hist` pushes `(A.up u, histGraph)`, `histGraph = deleteVerts (map A.up A.G) (A.up '' cluster)ᶜ = map childUp preG` (§5 l.17's `B₀`; `histGraph_eq_map`); `Inv`'s trace clause pairs rounds with `(e.vtx, deleteVerts e.arena e.resᶜ)` + the path-closure fact (every current carrier vertex within 2R of the connector THERE — E1's `exists_walk_support_subset_fiber` at birth), `hwalk` discharged via `pathSet_spec` + `Walk.transfer`. (α′) refuted in the object (recorded connectors are edge-isolated in later arenas — `selfS`/`isolatedS`); full-round-graph (α) refuted on cost (per-child carrier-wide BFS = D6's rejected shape). Five consumed statements byte-identical; games untouched; `Unroll` verbatim; full build green, zero sorry, key theorems at bare `[propext, Classical.choice, Quot.sound]`. Machine story for ChildLoadPartsAll: batch = channel row u (+u), new column = one BFS+gradient in `B₀`, old columns filter-down through restrict; owes the mechanical mirrors `Prog.ballDist = cdist`, `Impl.descend = cdescend`. Doc drift deferred to that leaf: SolveMachPrep §2's per-round-recompute narrative, SolveMatFrame:72's `S.R` cap prose |
| F7 | discharge the endorsed axiom | waiting | — | — | needs F6c10a+b, then KB pin + `KsChargeBridge`; `Adm` must be `Inv`-based (w17 finding); then: `Adm` at the run tree (`mkSetup_memLeaf_eq_bot`), instantiate `SolveSpec` via `solveSpec_closed`, `q`/`c` per `hspan`, `temps ≥` boolean depth, `T x := L.const·mcK`, reconcile `Ks` with `exists_mcChargeMS_T`, ∃-close with the `conclusion:` header |

## Campaign log

### 2026-09-06 — uniform compilation and linear boundary costs landed

`1a521eb` adds `SolveUniformMachine`. The complete parsing, materialization,
CSR/root loading and top stage have one fixed linear bound around the recursive
budget. `exists_machine_of_uniformSolve` chooses one program, natural constant,
and time function before all graphs and word lengths, absorbing the inferred
memory layout and real time coefficient into that same constant. Full archive
build and axiom checks pass at the existing UQW baseline. Concrete clean solve,
cover integration, and the actual cover cost comparison remain in progress.

### 2026-09-06 — complete sparse augmentation machine landed

Reviewed `9dbb178`, landed through `4ed0954`. `AugMachine.com_spec` computes
the exact deterministic `mdChain` from genuine padded CSR and uninitialized
reserved arrays with bounded words. Every base/round/final machine phase is
composed; no assumed machine callback or incoming rank remains. Allocation
is finite, scans follow occupied prefixes, and every heap logarithm remains
in the transparent cost. Full archive build, concrete consumers (including
the `cp.r` array frame), and standard-axiom checks pass. Clean cover integration
can now instantiate this concrete core; its uniform cost comparison is next.

### 2026-09-05 — guarded scalar recurrence and uniform time landed

`bb0c3dc` adds `SolveFrameCharge`. `chargeFrameK_guard` pays the actual
branch-sensitive frame: four guard steps, complete clean PREP/readback,
one child call, eight loop steps per centre, and the six-step loop boundary.
`chargeFrameK_root_le` closes it against the sparse driver charge, including
empty graphs. `exists_chargeFrameK_inputTime` chooses one natural-valued
almost-linear time function before every graph, input, channel family, and
word length; fixed compiler and linear boundary costs are parameters.
Full archive build and all new axiom checks pass. Remaining assembly is
concrete clean layout/cover, actual AUG cost comparison, and the endorsed
headline. Augmentation rounds must be `3*S.R`; sweep radius remains `S.R`.

### 2026-09-05 — scalar stage-charge comparison landed

`c6c3b62` adds `SolveStageCharge`: actual clean PREP and readback are bounded
by schedule-only coefficients times `centreWork`, exactly the existing
restriction-plus-isolation charge. The recursive child charge is counted
separately once. Top scatter and bottom evaluation include constant tails;
`solveStageCoeff` is one finite constant fixed before graphs or inputs.
Full archive build and all new theorem axiom checks pass. Next is the guarded
recursive scalar budget and its uniform input-time consequence.

### 2026-09-05 — sparse symmetrization landed

Reviewed `74d27f7`, landed through `be8280d`. The real final conversion scans
occupied arcs and their reversals for `116*M+16`, yielding exactly `D.toGraph`;
all source/frame/length facts and the occupied-length bound are retained.
Full archive build and axiom checks pass. Full AUG composition continues in
the existing isolated worker tree.

### 2026-09-05 — sparse build and computed-rank adapter landed

Reviewed `fbf06d3`, landed through `e898e98`. `agBuildPeel_spec` composes
padded CSR, identity-rank initialization, the real adjacency builder, and
heap peeling to exact `mdRank`. Its budget retains the full
`11*N+6+bldCoreK N M+KmdPeel N M`; raw allocations suffice and the source
CSR/size cells survive. Full archive build, concrete fixed-name consumers,
and standard-axiom checks pass. Next dependent leaf is the clean cover
composition around the full AUG core.

### 2026-09-05 — clean PREP recursion landed

Reviewed worker `f497f73` and landed through `0441d30`. `prepCleanCom`
returns root-prefix rank cleanliness and bounded array words across every
recursive block; restriction preserves the unused suffix. The existing zero
materialization establishes the root invariant. The actual per-child budget
removes exactly `11*A.N+5`, accounting for the replacement skip. Public
path-list and compatibility APIs remain intact. Full archive build and axiom
checks pass; the root solve theorem retains only the existing UQW dependency.
Next: concrete names/allocation/clean-chain instantiation, sparse full AUG,
and a uniform scalar-cost comparison. Reuse the clean, seeded worktrees for
these immediate followups; unrelated stream-colour WIP remains untouched.

### 2026-09-05 — sparse pair preparation landed

`bedc1cc` lands checkpoint `69a1a00`: actual CSR rows yield the unique
occupied-key dictionary in `58M + 26N + 8`; the rank and diagonal filters
cost `96M + 10` and produce exactly `baseOr` and the simple fraternity graph.
The diagonal filter reads no rank array. Source storage and all lengths are
preserved. Supervisor build, archive inspection, and axiom audit pass using
only the three logical axioms.

### 2026-09-05 — sparse key-to-CSR constructor landed

`623d4b2` lands checkpoint `4ec95e6` and imports `SolveSweepAugCsr`.
The occupied directed-key prefix becomes exact duplicate-free incoming rows
in `56M + 40N + 37`, preserving the source dictionary and unrelated storage.
Padded rows feed `GraphCsr` by windows without machine copying. Supervisor
archive inspection and the actual `bldCore_spec` consumer pass; axioms are
within the three logical axioms. The worker next packages build/peel adapters
needed by AUG's round composition.

### 2026-09-05 — complete compiler layout landed

`171342f` adds `SolveCodegen`. A structural traversal of the actual command
collects all scalar/array names and enough temporary cells, proving `Com.Ok`
for every command. `mc_auto_computesInTime_of_solveSpec` removes the old
two-temporary layout restriction and the manual compilation premise; its
span is absorbed into the same squared word-room constant. Full archive
inspection and axiom audit pass at the existing setup baseline.

### 2026-09-05 — exact sparse greedy augmentation round landed

`3414a87` lands checkpoint `fd377ab` and imports all four new satellites.
Five validated dictionary lookups implement `mem_greedyStep`; three occupied
prefix scans produce the exact next-arc dictionary at
`229*(arcCount + transPairCount + fratPairCount) + 26`. Input dictionaries,
rank, unrelated state, and all array lengths are preserved. Supervisor
compilation, concrete-name feasibility, axiom audit, and full archive inspection
pass with only the three logical axioms. Remaining AUG work composes this
with sparse CSR conversion and the separately charged min-degree peel.

### 2026-09-05 — canonical channels and admissible recursion landed

`ad72c09` adds `SolveChannels`. The oldest-first history columns equal
PREP's computed child columns exactly, including filtering inherited paths
through local embeddings. Their length is uniformly at most `2R + 1`.
`canonicalAdm` carries history length, increasing root names, and the
depth-guarded game invariant; root, arbitrary child, and edgeless final-child
obligations are proved. Full archive inspection passes. Channel proofs use
the three logical axioms; setup facts retain only the existing UQW dependency.

### 2026-09-05 — array word invariant landed

`8b73308` adds `SolveRunWords`: every bounded run preserves `ArrWords`,
with a specification lift at the same command and cost. This supplies the
stale inverse-cell bound required at sparse AUG entry. PREP's recursive
content contract now threads this alongside the clean rank prefix.
Narrow build and full archive inspection pass; the preservation theorem
uses only `propext` and `Quot.sound`. No array clearing was added.

### 2026-09-05 — full cover sweep landed

`3ad2ed7` lands PEEL checkpoint `3034240` and its root import.
`covPeelIn_peelCom` concludes the exact existing residual, with feasible
name/length conditions and the uniform schedule bound `2R + 3 ≤ q`.
Global regrouping gives ascending `restrictEmb` rows in `58M + 120N + 54`;
the full program retains the original `peelK`, now bounded by
`640*sweepCharge + 256*N + 256`. The combined root build, concrete-name
consumer, archive inspection, and axiom audit pass at the existing baseline.
PEEL's worker next builds AUG's sparse key-to-CSR satellite using these
counting lemmas. The active worktrees remain warm for the immediate followups.

### 2026-09-05 — sparse augmentation API and deterministic costing

`9cf5300` lands AUG's validated sparse dictionary and CSR witness scans
(checkpoints `844b372`, `78bbd06`) and `SolveMdCharge`. Each transitive or
fraternal demand pass costs `58 * candidates + 30 * arcs + 22 * N + 8`.
The deterministic `mdChain` now has uniform in-degree and wreach bounds,
and its sparse-count envelope times the actual lazy-heap logarithm is
proved almost linear on nonempty subgraph copies. Constants precede the
graph. This remains a prerequisite to `CovAugAdjIn`, not its discharge.
Full Lake build, archive inspection, and axiom checks pass; these new
results use only `propext`, `Classical.choice`, and `Quot.sound`.

### 2026-09-05 — PREP machine boundary landed

`2fe7db5` lands `SolveMachPrepRun` and its root import. The conditional
machine tail is discharged; `childLoadPartsAll_of` concludes the existing
contract, with the actual profile tables computed in `preG`. History
columns are oldest-first; `childLoadAll_of_parts_adm` needs channel equality
only on admissible run levels. Full Lake build and archive statement
inspection pass; axiom sets match the existing consumer baseline.

Next PREP leaf removes the explicit `11 * A.N + 6` reset per child by
preserving clean scratch through recursive calls. PEEL and sparse AUG
continue independently; the final cost and endorsed axiom remain open.

### 2026-09-05 — resumed on current main

Recovered the parked PREP (`w62`), PEEL (`w61`), and AUG (`w63`) files
into separate seeded `ndmc-*-finish` worktrees based on `e20e09a`.
PREP is closing the tail and correcting oldest-first channel indexing;
PEEL is closing initialization, iteration, and regrouping; AUG is replacing
the dense scans with sparse demand enumeration. The per-child rank reset
still needs a persistent cleanliness invariant before the final cost close.

`ff6dceb` exposes `SolveSweepBuild.bldCore_spec` for AUG, with its statement
and proof unchanged. Narrow and full Lake builds, the archive build and
statement inspection pass; the core uses only `propext`, `Classical.choice`,
and `Quot.sound`. Updated the local lax CLI from 0.1.31 to 0.1.41 because
the former rejected main's existing `manifest.yaml` `issue` field.

### 2026-08-27 ~11:30Z — RESUME POINT 2: wrap-up at the second quota wall

Jan ordered all workers to wrap up NOW; all three parked at green,
sorry-free, checkpoint-pushed states with STATE-OF-THE-LEAF headers in
their files. Landed today in total: **F6c12p + four of six program
residuals** (ReadRowsAll `60ac2ab`, CovAdjBuildIn `c929499`,
CovMdPeelIn `c8fba66`; F6c12p `9c66491`+`a0c505e`). The three parks:

- **CovPeelIn** (`worktree-w61`, `SolveSweepPeel.lean`, 4833 lines,
  0 sorries): the per-rank sweep step is fully PROVED
  (`peelStepB_spec`: SwInv i → SwInv (i+1) at `64·peelDeg + 187·|fibre|
  + 57`, amortized BFS pop loop, O(touched) reset, first-hit = centre
  via `1 ≤ R` [hypothesis `hr`]). Remains: `peelInitB` prologue, the
  rank loop (tail-sum potential, mirror `centreLoop_of_step`), regroup
  P1–P7 to `CtrArr`/`ClusterCsr` (`cntBelow`/`restrictEmb` counting
  lemmas already proved), `peelK ≤ c₁·sweepCharge + …` bridge, headline.
  ~One worker-session.
- **ChildLoadPartsAll** (`worktree-w62`, `SolveMachPrepRun.lean`,
  ~4860 lines, 0 sorries): **the htabF-pinning crux is RESOLVED**
  (`hpin`/`hpinE`/`hAdmLen`, F7-suppliable; mirror-seam lemmas
  `cdist_eq_ballDist`/`cdescend_eq_descend` proved in-file);
  `childLoadParts_of` concludes verbatim `ChildLoadParts` conditional on
  ONE flagged non-F7 hypothesis **`htail`** — the
  supports→profiles→colWrite→isolate tail as a Spec from the proved
  mid-state `PrepMid`; every ingredient is in-file, composition work
  only. Then the `ChildLoadPartsAll` headline (mirror `readRowsAll_of`)
  + consumer example. ⚠ Ruling needed (Jan/supervisor): `prepK` carries
  an honest `11N+6` per-centre rank-zeroing term (Σ = N² per level)
  because restrict's clean-scratch pre can't come from length-only Scr;
  removing it needs a cleanliness clause through `CLInv` (landed-file
  change). Decide absorb-vs-amend at the KB bridge.
- **CovAugAdjIn** (`worktree-w63`, `SolveSweepAug.lean`, 1226 lines,
  0 sorries, Opus): foundation only — bit/scan calculus, the
  edge-placement bridge `agDelAdjSt_of_part`, nine program defs, name
  kit. ⚠ Design flag (supervisor): it pinned a DENSE N×N matrix
  representation — Θ(N²) per round, the same budget shape that broke
  the opus lineage; RE-SCOPE to in-list demand enumeration
  (`Σ_w indeg(w)²`) before resuming; §1–§3 and the builder bridge
  survive that change. Discoveries recorded in its header (arc
  direction, FratLink symmetry, three accumulators, branchless
  comparisons, `Sag` must supply the four output allocations).

Resume order when quota returns: (1) finish PREP (htail + headline —
nearest), (2) finish PEEL, (3) re-scope + finish AUG, (4) KB pin +
uniform bridge + `exists_mcChargeMS_T` at `mdOrderingRoutine` (fold in
the prepK-N² ruling), (5) F7 (Fable). Workers per Jan: Opus for the
scaffolded finishes, same-session agent ids in RESUME POINT 1 below
(PEEL/PREP) — AUG's Opus agent parked at a natural interface, a fresh
Opus worker from the file header is equally fine.

### 2026-08-27 ~07:10Z — RESUME POINT: quota at 95%, freeze imminent

Jan's standing directives at the wall: **no new workers** (only existing
ones finish; correction rounds to the same agents are fine), worker
dispatches default to **Opus** when new ones are next authorized (Fable
only for supervision, a leaf Opus fails twice, and the F7 assembly).

**Landed and pushed** (origin/main = the session branch
`claude/ndmc-continuation-6eulbi`, tip `c929499`): F6c12p (`9c66491` +
root-registration `a0c505e`), ReadRowsAll (`60ac2ab`), CovAdjBuildIn
(`c929499`). Three of six F6c12 program residuals remain, all in flight
at the freeze, every file checkpoint-pushed on its worktree branch:

- **CovPeelIn** — `worktree-w61`,
  `…/w61/…/Lax3Proofs/SolveSweepPeel.lean`, 3768 lines, 1 sorry,
  last active 06:57Z. Late phase (seed/init specs after the sweep
  invariant machinery); headline not yet stated.
- **CovMdPeelIn** — `worktree-w61`, `…/SolveSweepMdPeel.lean`,
  4124 lines, **0 sorries**, active 07:07Z. Likely nearest its gates
  (heap kit + invariant + potential all present).
- **ChildLoadPartsAll** — `worktree-w62`, `…/SolveMachPrepRun.lean`,
  3472 lines, 1 sorry, active 07:07Z. Stage composition + write-set
  lemmas present; the htabF-pinning seam appeared to resolve without a
  design round (unconfirmed until its report).

**To resume, same session** (freeze-then-thaw, like last night): the
three workers resume via SendMessage to their agent ids — PEEL
`a9fef27b57d0825b7`, MDPEEL `ab66a9d6acecb7e7e`, PREP
`a3a22ad1d408b4ea6` — message: "resume your leaf from your file's
current on-disk state; finish to your packet's gates; report." A
supervisor wake (trig_0195uDseGWiQ3moMJsVvKeQ8, 07:57Z) queues and
delivers on thaw; its instructions carry the no-new-workers directive.

**To resume, fresh session**: cold-start per `/ndmc` (this ledger +
`git log`), fetch the three worktree branches, and for each unfinished
leaf either finish it in-session or dispatch ONE worker (Opus) per leaf
with: the file's current state as the starting point, the residual's
def location (F6c12 row above), the w60-packet hazards (this log,
2026-08-26 entry), and the gates (module `lake build`, zero sorry,
`lean_verify` at the landed baseline, verbatim conclusion + only
F7-suppliable extra hypotheses). Landing recipe per boundary: copy file
to main, register the module in `Lax3Proofs.lean` (the audit demands
the exact mirror), `lake build` in the proofs dir, `lax build --only
proofs nowhere-dense-model-checking` FROM THE REPO ROOT, ledger row,
commit, push `claude/ndmc-continuation-6eulbi` and `main`.

**After the three land, in order** (each awaiting Jan's go-ahead per
the no-new-workers directive): (a) CovAugAdjIn — w63, Opus; consumes
CovAdjBuildIn's build kit + CovMdPeelIn's parametric peel core; spec in
the F6c12 row; the augmentation rounds mirror `mdChain`
(SolveSweepOrder:333, `greedyStep` CoverRoutine:212, `fratGraph`
Augmentation:178). (b) KB pin + uniform `KsChargeBridge` +
`exists_mcChargeMS_T` re-instantiated at `mdOrderingRoutine R` — the
verified five-point checklist is in this log's 2026-08-26 entry.
(c) F7 — guarded-Inv Adm, canonical htabF + hhtab, `solveSpec_closed`'s
bookkeeping quartet, `mcLayout.temps` bump if the row towers need it,
the ∃-close at the `conclusion:` header.

### 2026-08-27 — the spend-limit freeze, F6c12p lands, ReadRowsAll lands

The account hit its monthly spend limit at ~20:32Z on the 26th: all four
program workers died mid-flight and the session froze until ~05:07Z.
Nothing was lost — every in-flight file was checkpoint-pushed on its
worktree branch before and after the cutoff, and the container survived.
Two boundaries landed around the freeze:

- **F6c12p** (`9c66491` + row flip `22cbd15`): the batch canonicalized.
  The worker's investigation beat the packet's map — (α′) refuted on a
  real obstruction (recorded connectors are edge-isolated in later
  arenas), full-round-graph (α) rejected as cost-dead (per-child
  carrier-wide BFS, D6's rejected shape) — landing on §5 l.17's own
  answer: canonical min-parent gradient walks in the
  **cluster-restricted round graph**, recorded in the channel
  (`histGraph = map childUp preG`, `histGraph_eq_map`), the game bridge
  closed by E1's path-closure through a STRENGTHENED `Inv` (each round
  paired with its restricted graph + a carrier-wide 2R clause). Five
  game-API statements byte-identical; StrictMono `up`-chain +
  `pathList_map` = the machine transport; `DriverBatchCanon` (526 lines)
  mirrors the machine's own `ballDist`/`parents`/`descend` kit. Key
  theorems at bare `[propext, Classical.choice, Quot.sound]`.
  Post-landing fix `a0c505e`: the root module must import exactly the
  package's modules — the supervisor's registration step, missed once
  ("imported transitively" does not satisfy the audit). Doc drift owed:
  `SolveMachPrep` §2's per-round-recompute narrative and
  `SolveMatFrame:72`'s `S.R` cap prose describe the pre-repair channel
  discipline (residuals parametric, nothing broken; the machine-pass
  leaf aims at write-once-filter-down at 2R).
- **ReadRowsAll** (residual (2), landed with this entry): see the F6c12
  row. Review basis: verbatim conclusion + machine-checked consumer fit
  + axiom baseline + build/audit replay on main.

Process notes: three of five w60 workers resolved their packet paths
from the dispatching shell's cwd and wrote into the w61 worktree —
harmless (disjoint files; the supervisor lands per-file), fixed forward
by absolute-paths + verify-pwd packet lines. Gate-script readings: pipe
the gate through nothing — `leaf-gate.sh | tail` reports the pipe's exit
code, not the gate's. The remaining three workers (BUILD at a parse
cascade, PEEL mid-invariant, MDPEEL entering §2a) resumed from their
transcripts at ~05:10Z; w62 `ChildLoadPartsAll` dispatches on the
F6c12p base.

### 2026-08-26 — the fable lineage resumes at `783eb34`; waves jump to w60

Fresh session, Jan's instruction: continue from the last fable commit
(`783eb34`, this lineage's tip and `origin/main`). A parallel lineage
(`origin/claude/ndmc-1om1vl` + `worktree-w26…w41`/`wip-w2x` branches,
2026-08-24/26, waves w23–w51) worked the same six residuals; Jan rated it
unreliable and it is **not merged** — none of its commits are ancestors of
this line. To keep wave ids globally unique this lineage resumes at **w60**.
A read-only survey of that branch was distilled into warnings (its residual
*definitions* match `783eb34` byte-for-byte; its `concepts/` and pins are
untouched; several of its findings about landed material were re-verified
here independently):

- **Verified here, real**: the ⟨D⟩ batch gap (F6c12p row — checked against
  `SplitterWin.pathSet`/`DriverArena.batchRoot` in this tree); the §3
  `AdjBuildIn`/`AdjDeleteIn` contract defect (checked — no `N`↔`B`
  relation, and IMP+ has no length primitive, `Imp.lean`); `ClusterCsr`
  rows are ascending-sorted (its peel must sort — checked, the def says
  `restrictEmb`'s enumeration).
- **Rejected**: its claim that `CovMdPeelIn` is undischargeable
  subquadratically (it shipped `86N²+43N+14` and blamed the statement; the
  lazy-heap route in the F6c12 row meets the pinned tie-break at
  quasi-linear cost — the budget parameter was always free).
- **KB/F7-boundary claims, VERIFIED against this tree** (same session,
  before w60 returned): (i) `KsChargeBridge` (SolveChain:705) does put
  `∃ cB` inside fixed `(n,G,c,w)` — but nothing landed consumes the def;
  F7 proves a uniform variant (∃cB outermost) from the same per-stage
  comparison lemmas. `exists_mcChargeMS_T` (ProgCharge:1314) is already
  uniform (`∃ cf c' T` before `∀ n G`) but pinned at
  `timedGreedyRoutine (3R)` — the KB wave must re-instantiate it at
  `mdOrderingRoutine R` (its `steps := 0` makes the `IsCoverOrdering.time`
  clause free; the machine ordering's real cost rides the `covC` column,
  which must be shown ≤ `coverCF`'s shape). (ii) `blockSpec_leaf_guard`'s
  `hKB` (SolveChain:418) demands `4 + max(botComK, KElse A) ≤ KB` at EVERY
  `A`; `frameK` returns bare `botComK` on `⊥` — so F7 pins `KB` at the
  guard-corrected majorant, never `frameK` verbatim (the frameK docstring's
  suggestion is stale). (iii) `mcLayout` hard-codes `temps := 2`
  (ProgCodegenLayout:69) and its own docstring plans the extension; if the
  readback's row towers exceed depth 2, F7 parametrizes/bumps `temps` and
  replays the codegen cone — contained. (iv) `inv_child`
  (DriverCorrect:444) needs `hwidth : 1 + j·(2R+1) ≤ S.width`, so F7's
  `Adm` is the **guarded** Inv form (`j ≤ depth → Inv`), making
  `hAdmChild` vacuous past depth and real below it. (v) The alleged
  `Scr`-content inconsistency does not arise in this lineage: rank/cover
  content rides named regions (`ra`/`ca`/`co`/`cm` clauses), `Scr` stays
  pure-length; `solveSpec_closed`'s `hscr` exact-length demands are
  length-facts and transport. None blocks the six programs.
- **Adopted as packet hazards**: `(by decide)` not `(by rfl)` for
  string-literal defeq (~100s/decl vs ~3s, measured there); the
  exact-length trap ("is the demanded figure stable over the loop?");
  two-state maintenance lemmas for loop descriptors, never single-state
  inhabitation.

Environment note: fresh container; capture blobs for word-ram and lax-3
exceed the proxy's single-read tolerance — fetched with resumable curl,
digest-verified, installed; drift replay from the 2026-08-07 captures.
That branch's sessions may still be live (a `worktree-w40` checkpoint is
dated 2026-08-26); they push only to their own branches.

**Wave w60 dispatched**: CovAdjBuildIn (`SolveSweepBuild.lean`), CovPeelIn
(`SolveSweepPeel.lean`), CovMdPeelIn (`SolveSweepMdPeel.lean`), ReadRowsAll
(`SolveSegReadRun.lean`) — four workers, one worktree, disjoint new files.
**Wave w61**: F6c12p solo in its own worktree (it edits landed files;
full-build gate; lands after w60). w62 next: CovAugAdjIn on (3)+(6)'s kits,
ChildLoadPartsAll on F6c12p.

### 2026-08-18 — wave 12 dispatched: F6d + the two BFS-free F6c runs

Fresh session, cold start from the ledger. Wave 12 is three workers on
disjoint new files in `worktree-w12`: **F6d** (`SolveBfs.lean` — the shared
BFS-by-rounds command, generalizing run 1's `markCom` to deliver exact
truncated distances at `ImplBfs.BallTable`, the seam `descend`/`bfsSupports`
and the `vsrc` route already consume), **F6c2** (`SolveBlocksRestrict.lean` —
`restrictCom`/`isolateCom` against `MArena.restrict`/`isolate`, rank-scratch
renumbering self-cleaned at touched entries), **F6c3**
(`SolveBlocksBotCom.lean` — the `firsts` table build + the compile-time
generated evaluator, target `botEvalT` verbatim). Chosen because they are
the only F6 stages that do not consume F6d's BFS; supports/profilesMS/cover
sweep/composition follow once F6d lands. Workers do not touch the root
module; the supervisor adds the three imports at landing.

### 2026-08-19 — w13 lands: the machine has every routine (`7736b66`)

All four remaining routine stages are IMP+ programs with `Spec`s landing on
the frozen abstract identities — 13.4k lines, the heaviest wave. What is now
true: **every §4 operation exists at every layer** — abstract, NREST, and
compiled-machine `Spec`. The remaining distance to the axiom is composition
(F6c6: the frame chain and `ℓ+1` levels closing `SolveSpec`, with the
windowed-region contract the exact-length seam demands) and then F7's
∃-close. Two findings entered the permanent record: `Driver.setEquiv` was
Classical-chosen while its consumer's docstring said "sorted" — repinned to
the sorted enumeration under D3/E7's any-bijection license (the read-the-
theorem lesson, sixth occurrence); and exact-length CSR regions cannot serve
a per-centre loop over different-sized children — the composer owes the
prefix-CSR variant. Process: one worker ran git against its packet (benign,
disclosed); two cross-file name collisions fixed at review; one worker
resumed cleanly after a connection drop.

### 2026-08-18 — w11 lands in full; the session closes here

F6c's run-1 report arrived during wrap-up and was reviewed and landed
(`9996e30`), after F6b (`c4cde5b`). The wave is complete. Two supervisor
cwd slips during the wrap-up landings (a doubled worktree path, and an edit
applied to the worktree's root module instead of main's) were both caught by
the gate and fixed — the gate earned its keep twice in twenty minutes.

**Correction, written minutes later:** a second supervisor session picked
the loop up from this ledger while this one was wrapping — it landed F6c
first (`7bad766`; this session's `9996e30` was a benign near-empty duplicate),
landed **F6d as `SolveBfs`** (`ab14f30`, the shared bounded BFS at
`BallTable`), and dispatched wave 12 (F6c2–F6c5). The remaining stretch is
theirs: the F6c2–F6c5 rows above, then **F7**'s ∃-close. Everything else —
the mathematics, the abstract algorithm, the cost chain to the axiom's own
`T`-clause, the codegen skeleton, the frame contract, and the first routines
down to IMP+ — is landed, gated, and pushed. This session ends here; the
ledger did its job twice over.

### (superseded by the entry above) session wrap-up (Jan's call): the state, and the road left

Jan closed the session mid-wave-11. Landed this session: **all seventeen E
rows and F1–F5, F3b/F3c, F6, F6b** — the abstract theorem, the machine layer,
the discharged cover-time bound, and the codegen skeleton one `SolveSpec`
hole from the endorsed axiom, with the `T`-clause number already proved
(`exists_mcChargeMS_T`).

**What remains, precisely** (the next session's cold start is this entry +
`git log`):

1. **F6c** — in flight at wrap-up; its checkpoint (if any files were written)
   is on `origin/worktree-w11`. Review against its packet, land or
   re-dispatch. Its scope: the per-frame state contract, the routine `Spec`s
   (botEval, greedyScatter, isolate, restrict, supports, profilesMS,
   cover-sweep), one conditional frame block.
2. **F6d** (minted at wrap-up) — the shared IMP+ marking-BFS command; three
   consumers wait on it (F6b's scatter sweep slot `hscat`, the supports
   stage, the profilesMS stage). Build it first.
3. **F7** — the ∃-close: instantiate `SolveSpec` from F6b's
   `solveSpec_of_rest` + F6c's blocks, pick `q`/`c` per
   `mcLayout_fitsWords`'s `hspan`, `temps ≥` the boolean depth (F6b's seam
   note), `T x := L.const·mcK`, reconcile `Ks` against
   `exists_mcChargeMS_T`, and write the theorem with the
   `conclusion: Lax3.ModelChecking.exists_almostLinearTime_program_modelChecking`
   header.

Known seams for the next workers: `Nat.decLe` vs `Classical.propDecidable`
at scatter guards (`if_congr` crosses it); zombie LSP servers of dead
worktrees eat container memory (kill by open-file path); pushes that report
"Everything up-to-date" wrongly — verify `ls-remote`, push by explicit
refspec.

### 2026-08-18 — w10 lands: one `Spec` obligation from the axiom (`9b4cdfa`)

What is now true: the endorsed axiom is reachable through exactly one named
hole. `mc_computesInTime_of_solveSpec` delivers `ComputesInTime` on the
axiom's input set verbatim, at `T = L.const · mcK`, conditional on
`SolveSpec` alone — the compiled solve stage's `Spec`. And the number that
fills `T` exists: `exists_mcChargeMS_T` bounds the whole program budget by
`c'·(|x|+1)^{1+ε}` with **no cover-time assumption** — F5's theorem consumed,
the honest routine pinned, the vacuity question answered in the object.

Hard-won shape facts, recorded so they are not relearned: the landed
`frameCharge` does NOT satisfy the headline (the profiles column gap is real
— F3b's MS budget is not an optimization but a correctness requirement of
the accounting); direct-κ against `dcost` is impossible (unbounded ratio);
empty centres are free in `dcost` but not in the program's ledger, so only
node-aggregate comparisons close. The session hit its usage limit mid-wave —
both workers resumed from transcripts with nothing lost — and zombie LSP
servers of deleted worktrees exhausted container memory (killed by open-file
path; future waves should expect this).

**The remaining work is F6b + F6c (the Sepref descent), then F7's ∃-close.**

### 2026-08-18 — w9 lands, and the design's one unproved claim is unproved no more (`7ed61d3`)

**`coverOrderingTime_of_nowhereDense` is a theorem.** O7 — "the one that
decides the project" — is decided: the cover's time bound, assumed since E0,
is discharged by the honest witness (`timedGreedyRoutine`, `steps :=
chainCharge`), at the true exponent `1+δ` (the interface's `1+2δ` a
weakening), with the greedy chain's in-degree bound found already landed by a
route the plan had mislabeled (`greedy_chain_joint_inDegLE`, not the wcol
chain's `:1076`). Vacuity honestly flagged: the Prop was always cheaply true
at `steps := 0`; the deliverable is the witness, and `le_chainCharge` pins it
as real. F3's profiles blocker dissolved consumer-side (F3b's virtual source;
the bridge's source-revisit subtlety handled by strong recursion). F4
composed the levels and landed `mcProg_headline`. Wave 10 is F3c + F6; then
F7 discharges the endorsed axiom.

### 2026-08-18 — the discharge campaign opens (Jan's authorization)

Jan, in his own words: *"Please discharge all the remaining ones."* The
remainder map of `Headline.lean` becomes the F DAG (execution-plan.md, F
section). Recon before minting: the greedy-chain assembly pieces are all
landed; `exists_augChain_inDeg_subpolynomial` already carries the md ≤ c·m^δ
per-round mathematics; and the Refine tower has a landed end-to-end
`ComputesInTime` precedent (`Codegen/Examples/EndToEnd.lean`), so the codegen
path is exercised, not hypothetical. **Wave 8 (`w8`) is F1, F2, F3.**

### 2026-08-18 — w7 lands E13, and the ledger is complete (`b2df405`)

**All thirteen leaves (plus the three E12 sub-leaves) are done.** What the
campaign now holds, end to end: the cover layer's four owed guarantees with
the time bound as one named hypothesis (`CoverOrderingTime`); the slackened
cost induction with no constant side conditions; the cluster-restricted game
record with its transports; the compaction; the schedule; the abstract driver,
correct for every ordering and affordable under the one hypothesis; the
`ℓ+1`-level unroll computing exactly the same tables at exactly the same cost,
with the run-tree invariant threaded end to end; the complete machine-routine
layer with charges and identities; and the composition `headline_encoded` —
the endorsed axiom's statement, reachable conditionally, at its own input
measure, with the full iff on every graph.

**What this campaign deliberately does not contain**, mapped precisely in
`Headline.lean`'s remainder section, is the successor work: (a) the composed
NREST driver program over the `Impl*` routines (the largest block), (b)
Sepref/Codegen to a `Lax13.Ram.Program` plus a CSR front end (which exists
nowhere yet), (c) the `CoverOrderingTime` discharge — the NOdM formalization,
a campaign of its own — (d) the word-size condition spent against the static
layout, (e) the machine-side `T` arithmetic. The endorsed axiom stands until
those exist; nothing found in seven waves contradicts its shape.

The loop's own termination condition is met: no leaf is ready, none is
blocked. **The campaign is complete.**

### 2026-08-18 — w6 lands: the machine layer is complete (`84ae503`)

What is now true: every routine of §4's table exists with its charge and its
identity to the abstract driver — twelve of thirteen leaves done, and only the
composition (E13) remains. Three findings from the wave:

- **E12c's fibre lemma holds with no side condition** — the peeled-ball IS
  the wreach fibre, at any radius; the strict peel and the non-strict
  endpoint clause are the same condition read through `not_lt`. But **(★)'s
  closing needs `1 ≤ r`**, which GKS assume silently and which is false at
  `r = 0` (a star refutes both `d_< ≤ |wreach|` and `N_> ⊆ X_v`). Explicit
  hypothesis, spent in two lemmas; the design's `R ≥ 1` supplies it.
- E12b's identities are `rfl` because it reuses the driver's own cluster
  enumeration — pick implementation names to match the abstraction's and the
  seam disappears.
- E12d's marker class is `univ`, so its naive per-member iteration prices
  `classSum ≥ n`; semantically the marker row is free (`y := z`). A
  consumer-side special-case lemma is available to E13 if the constant
  matters; it does not affect the exponent.

A container restart hit mid-gate; the filesystem survived, the gate was
re-run green, and nothing was lost — the checkpoint discipline was not
needed this time but would have bounded the loss to one wake interval.

### 2026-08-18 — w5 lands: the unroll, and the machine layer opens (`a1d9294`)

What is now true: §8 step 4b is closed — the driver runs as `ℓ+1` static
levels computing *exactly* `tables`, priced identically, with the run tree
reified and the invariant threaded end to end (`mkSetup_memLeaf_eq_bot`). And
the machine layer has its first three routines with their identities to the
abstract driver: the scatter atoms, the leaf evaluator, and BFS-at-`B₀`.
E12 split as predicted: E12b (restrict/isolate), E12c (the cover sweep — the
sole superlinear routine, scheduled first per §6.2 ⟨A⟩), E12d (recordProfiles).
E13 now waits on exactly those three.

Findings worth keeping:

- **`descend_spec` gives exact distances** — the tower's `Post` is strong
  enough to reconstruct the BFS tree consumer-side; no new tower program was
  needed for `bfsSupports`. The tower lacks multi-source BFS; E12d's honest
  route is `(m+L)` single-source calls, matching §6.3's charge.
- **`bfsSupports` delivers "IS a witness-walk support", not "= `genSet`'s
  chosen walks"** — the latter is neither provable (Classical choice) nor
  needed (the driver needs *some* walk support). Consistent with E9's D6
  scoping.
- Toolchain drift notes for future workers: `Fin.find` is proof-carrying now;
  `List.pairwise_lt_finRange` → `sortedLT_finRange`; `Finset.toList` is
  noncomputable — evaluators use `decide`.
- E12's worker flagged §7's "edge half is owed" as load-bearing context —
  it was stale (E3 landed it); fixed in this landing. Doc drift after a leaf
  lands is real: when a landing supersedes a design sentence, fix the
  sentence in the same boundary.

### 2026-08-18 — w4 lands: the hard gate is passed (`bf7baef`)

What is now true: **the abstract algorithm exists and is correct and
affordable.** `mc_correct` — the driver decides `φ` on every input, for every
ordering routine and every scatter choice; `mkSetup_dcost_root_le` — its cost
closes at `KD^{ℓ+1}·‖A₀‖^{1+ε}` from exactly one hypothesis, E0's
`CoverOrderingTime`; `eq_bot_of_inv_depth` — the leaf test is exhaustive in
budget, via the `ReachedS` invariant kept at the root carrier as E6 prescribed.
E9 did not split. E10 and E12 are both ready and disjoint — they are the next
wave, and E13 is the only leaf behind them.

Findings worth keeping:

- **The leaf IS `Sat`, and that is landed intent, not a shortcut**:
  `BotEval`'s docstring defines the base case as "returns `Sat` itself; an
  implementation has to evaluate that value" — its lemma set is the machine's
  evaluation bridge, consumed at E12, with the off-budget fuel-0 corner
  covered by `eq_bot_of_inv_depth`.
- **§5 step 3′ dissolves under reordering**: fusing the compaction with line
  16's restrict makes every later rewrite a landed lemma on the child carrier.
  The doc's stated order would have needed a genuinely new transport. Doc
  simplification available; not urgent.
- **D6 sharpened and scoped**: the abstract layer needs only `(vtx, arena)`
  pairs — `Classical.choose`-deterministic `pathSet` reconstructs identical
  supports at descent. The per-vertex lists are purely P1a avoidance on the
  machine; entirely E12's.
- **`IsCostRecurrence`'s `node` clause is not consumable at an arena-typed
  cost** (size-indexed sup does not exist once `hist` makes the type infinite
  per weight); E9 ran the induction directly, consuming `chosenK_step` + the
  E3 mass bounds. Optional refactor: an arena-shaped `node` clause. Not
  blocking anything.
- The augmentation-round instantiation is `R' := 3R, t := R` — slack absorbed
  as constants; the `≈3log₂(4rc)` depth naming stays an E12-side constant
  improvement.

### 2026-08-18 — w3 lands: E6, and §5's precondition is finally well-typed (`55ba312`)

What is now true: every dependency of E9 is `done`. The carrier seam D1 opened
is closed the cheap way — the play record lives at the root carrier and is
never re-typed; `ArenaTransport` supplies the wholesale transports anyway
(`reachedS_map`/`reachedS_restrict` along any embedding, `nextArenaS_mapRound`,
`ball_map`), and §5 line 8 now states the invariant that actually typechecks.
E6's one deviation from the plan is recorded in §9: general embeddings, not
`castLE` — the child-to-root composite of `up` maps lands on a cluster, not an
initial segment. One identity is explicitly booked for E12: `map emb B =
deleteVerts (deleteVerts A Xᶜ) W` at the implementation's restrict∘isolate
(line 16/21), which is what re-expresses a child's reached arena at the root.

**Wave 4 is E9 alone — the hard gate.** No ND-MC driver until it is complete
and reviewed.

### 2026-08-18 — w2 lands: every interface E9 composes against exists (`b0444fa`)

What is now true: the abstract driver's whole dependency surface is landed.
The cost induction is solved and slackened (`c ≥ 6` did disappear — the `L = 0`
step of the chosen `K` is an *equality* for all constants, so nothing could
hide in it); the cluster-restricted game record exists with the descend batch
an equality and Splitter's win transferred; the compaction transports `Sat`
along any bijection into `SatWithin`; the locality decomposition is one fixed
function with iterable atom lists; and the Refine probe returned with the
charge in hand. E9 now waits on E6 alone — wave 3 is E6, then E9 by itself.

Findings worth keeping:

- **E5 beat its audit estimate qualitatively**: `splitterWins_of_reachedS`
  needed neither `splitterWins_anti` nor the `W ↦ W ∩ S` batch map — Splitter's
  own rounds simply record `res := ball` (legal by `subset_rfl`) and the R
  proof replays on histories that mix cluster and ball rounds. One fewer
  dependency than the audit priced, and the changed-distances objection never
  arises.
- **E7 confirmed D3 in the object**: no order hypothesis, no dead-vertex
  correction. But note the *true* statement is `Sat B ↔ SatWithin X A` — the
  unrelativized `Sat ↔ Sat` is false because `exU` ranges over the kept
  carrier's isolated vertices. §5's chain must consume the `SatWithin` form.
- **E11's probe verdict**: the tower's BFS budget is alive-summed
  (`Σ_{alive}(deg_G+1)`) with a carrier-sized `bfs.init` per call — the
  §6.1 `O(‖ball‖)` shape appears only *after* `restrict`. The quadratic trap
  sits in the init term. E12 must call BFS on `B₀`, never mask-on-arena; a
  ball-shaped restatement of the tower spec would need a frontier-in-ball
  invariant (owed only if E12 wants §4's charge verbatim).
- E8's `localityBC` chooses from the **Assembly discharge**, not the endorsed
  axiom — footprint stays at the standard three. Same trick available any
  time a concept axiom has a proofs-side discharge.
- `Lax13Proofs` had never been elaborated in this checkout: E11 paid ~10 min
  compiling the ~11-file NREST closure of `Examples.Bfs` from source. The
  captures (`capture-seed.sh word-ram`) could have supplied it prebuilt;
  worth doing before E12, which imports much more of the tower.

One entry per landed boundary. What is now true that was not before — not what
was done.

### 2026-08-17 — the ledger opens

Nothing landed yet. **Wave 1 (`w1`) is E0, E1, E2, E3** — three small, disjoint
cover-layer satellites plus the one document leaf. Chosen because they are the
cheapest way to test whether the design's line-count estimates mean anything,
and because they land both of E4's dependencies, so wave 2 opens fully.

Four adversarial audits (29 + 9 agents) preceded this file. Their standing
result: the abstract core — §5's recursion, §7's shape, D2–D4, and both of Rev
3's inventions — has survived every attack. What repeatedly broke was the seams
between patches, the constants, and citations asserted rather than opened.

Two things changed on the day the ledger opened, and both shrink the plan:

- **§8 step 0b is not blocked.** GKS's bracket resolves to arXiv math/0508324v2,
  now at `references/nodm05/`. It supplies the round count and per-round cost
  Rev 4 recorded as absent everywhere. Its own Lemma 4.1 defers once more, to
  Lemma 6.1 of part I — arXiv math/0508323v1, now at `references/nodm05i/`,
  where it is proved in full. So the deferral chain is four links long, one
  longer than Rev 4 thought, and it **terminates in a proof**. What none of the
  four papers supplies is the nowhere-dense instantiation — part II's Theorem
  4.3 is a **bounded expansion** statement in time **O(n)** — and that
  adaptation, not the import, is E0's content.
- **§7 stops being tightened.** Jan's call: take the slack. `δ = ε/(ℓ+2)` and a
  freely chosen base constant `K`, in place of Rev 4's `ε/(ℓ+1)` and the forced
  `(2c)^{L+1}` shape that manufactured the `c ≥ 6` side condition. The headline
  is unchanged; three consecutive revisions got that paragraph's arithmetic
  wrong, and the tight inequality was the reason.

### 2026-08-17 — wave 1 dispatched, and the gate was red before it

`w1` is E0, E1, E2, E3, one worker each, on `worktree-w1` off `main`. Seed took
0.9 s; the packages were already warm.

**The baseline gate failed, and not because of a leaf.**
`.claude/leaf-gate.sh nowhere-dense-model-checking` was red on `main` at
`b9a049a`: both `lake build`s passed, and the statement audit rejected the
package with `Lax3Proofs must have no module docstring`. The `/-! -/` block
after the root module's import list is what the 2026-08-17 prune left behind;
no other section of that file uses one. Converted to `--` comments at `38c5243`
and the audit passes. What this cost is worth recording: **no leaf in this
campaign could have landed until it was fixed**, and it was invisible from the
ledger, which had never seen a gate run. Run the gate once at the start of a
campaign, not first at the first landing.

Also measured: a cold-ish full `leaf-gate.sh` is ~10 min (concepts 25 s, proofs
1 m31 s, inspector 36 s, plus the two prior `lake build`s); a re-run of the
`lax build` audit alone against a warm tree is ~16 s. Budget the gate per
landing, not per leaf.

### 2026-08-18 — the flow is cloud-adjusted: nothing may live only in the container

This session runs in an ephemeral claude.ai/code container — reclaimed on
inactivity, repo recloned fresh next time. Standing adjustments, Jan's call:

- **Push at every boundary** — `main` and the mirror `claude/ndmc-71wd6g`
  both (origin/main is live again as of `801d5df`; the stop hook watches it).
- **Checkpoint-push in-flight waves**: at every supervisor wake, commit the
  wave worktree's current files on its `worktree-w<N>` branch and push. Not a
  landing — never merge a checkpoint; review still happens on final state
  only. If the container dies mid-wave, recovery = fetch `worktree-w<N>`,
  diff against `main`, salvage or re-dispatch per leaf.
- **Delete the remote `worktree-w<N>` branch when the wave lands** (the
  landing supersedes it).
- A dead container also kills the wave's workers and any fallback timer;
  the ledger + `git log` on origin remain the whole recovery state, as
  designed.

### 2026-08-18 — w1 lands: the cover layer owes nothing but time (`8709c19`)

What is now true: the four guarantees §4/§5 demand of `cover` beyond the
endorsed `IsNeighborhoodCover` all exist proofs-side — path-closure into the
induced graph (E1), a named `ctr` with the π-min identity at the two distinct
radii (E2), the edge half of (★) with the ceiling absorbed into `c_D+1` (E3) —
and the one thing nobody can prove from material in-repo, the ordering phase's
step count, is a hypothesis with a name (`CoverOrderingTime`, E0) rather than a
gap with a citation. E4's dependencies are both landed; wave 2 is E4, E5, E7,
E8, E11.

Findings worth keeping:

- **The line-count estimates were off by an order of magnitude** — "~6 lines"
  (E2) landed at ~217, "~10 lines" (E1) at ~110. The *arguments* were exactly
  as priced (the math was right); the factor is statements, docstrings, and
  the private `withinDist_of_mem_support` E2 had to re-prove because
  `CoverConstruction` hides it. Price future leaves accordingly.
- `ctr` is noncomputable as defined. Fine for the abstract layer; E12 owes the
  computed version read off the cover sweep.
- E0 went past its packet in the right direction: `CoverDegree.AugChainData`
  lets the whole cover *structure* be derived rather than assumed, so the
  assumption surface is exactly one field (`IsCoverOrdering.time`), plus two
  controls (binder-order rationale, satisfiability on the empty class).
- Worker-report channel: all four completion notifications were lost;
  supervision recovered entirely from the files, which is what the review
  order prescribes anyway. E3's worker left five mechanical build errors
  (a misspelled lemma name, two `noncomputable`s, two casts through a `set`
  binder) — fixed at review, smaller than a correction round-trip.
