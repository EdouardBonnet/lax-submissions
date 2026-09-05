-- The locality theorem of arXiv:2606.23180 and its normal form.
import Lax3Proofs.WalkDistance
import Lax3Proofs.ScatterChoices
import Lax3Proofs.Horizon
import Lax3Proofs.SyntaxLemmas
import Lax3Proofs.SemLocal
import Lax3Proofs.Clusters
import Lax3Proofs.ScatterCore
import Lax3Proofs.Separation
import Lax3Proofs.FarQuant
import Lax3Proofs.BCAlgebra
import Lax3Proofs.ScatterFml
import Lax3Proofs.Assembly

-- Plain first-order logic as an input to the distance-logic engine.
import Lax3Proofs.Reduction

-- The isolation splitter game and Splitter's win on nowhere dense classes.
import Lax3Proofs.SplitterBasics
import Lax3Proofs.SplitterMono
import Lax3Proofs.SplitterWin
import Lax3Proofs.SplitterWinRec
import Lax3Proofs.UqwInstantiation
import Lax3Proofs.ReachedS
import Lax3Proofs.ArenaTransport

-- Sparse neighborhood covers and the augmentation chain behind their degree.
import Lax3Proofs.CoverConstruction
import Lax3Proofs.Augmentation
import Lax3Proofs.AugmentedDensity
import Lax3Proofs.OrderedCovers
import Lax3Proofs.CoverDegree
import Lax3Proofs.ClusterPaths
import Lax3Proofs.CoverCentres
import Lax3Proofs.CoverEdgeSum
import Lax3Proofs.CoverSpec

-- The two rewrites a step of the recursion performs, and the leaf case.
import Lax3Proofs.Relativize
import Lax3Proofs.Isolate
import Lax3Proofs.BotEval
import Lax3Proofs.Compaction
import Lax3Proofs.LocalityFun

-- Machine-independent arithmetic the redesign's cost argument amends rather
-- than re-derives: the sigma recursion over the game tree with its n^(1+eps)
-- close, and the adjacency-slot bound a cover implementation must size to.
import Lax3Proofs.CostRecurrence
import Lax3Proofs.TgtCoupling
import Lax3Proofs.RefineBfsProbe

-- The abstract algorithm (E9): section 5's driver over the abstract
-- arena -- schedule, arena and recursion, correctness, cost.
import Lax3Proofs.DriverSchedule
import Lax3Proofs.DriverBatchCanon
import Lax3Proofs.DriverArena
import Lax3Proofs.DriverCorrect
import Lax3Proofs.DriverCost
import Lax3Proofs.Driver
import Lax3Proofs.Unroll

-- The machine-level routines (E12): the guarded greedy scatter, the
-- edgeless-leaf evaluator, and BFS with supports at the restricted arena.
import Lax3Proofs.ImplScatter
import Lax3Proofs.ImplBot
import Lax3Proofs.ImplBfs
import Lax3Proofs.ImplRestrict
import Lax3Proofs.ImplCover
import Lax3Proofs.ImplProfiles
import Lax3Proofs.Impl

-- The composition to the headline (E13): the conditional abstract
-- headline under CoverOrderingTime, at the endorsed axiom's vocabulary.
import Lax3Proofs.Headline

-- The discharge campaign (F): the greedy ordering routine, the CSR
-- front end, and the driver's frame as one NREST program.
import Lax3Proofs.CoverRoutine
import Lax3Proofs.ImplFrontEnd
import Lax3Proofs.ImplMultiSource
import Lax3Proofs.ProgFrame
import Lax3Proofs.ProgDriver
import Lax3Proofs.ProgCoverCharge
import Lax3Proofs.ProgCover
import Lax3Proofs.ProgCharge
import Lax3Proofs.ProgCodegenParse
import Lax3Proofs.ProgCodegenLayout
import Lax3Proofs.ProgCodegen
import Lax3Proofs.SolveMatFrame
import Lax3Proofs.SolveMatArena
import Lax3Proofs.SolveMatTop
import Lax3Proofs.SolveMat
import Lax3Proofs.SolveBlocks
import Lax3Proofs.SolveBlocksScatter
import Lax3Proofs.SolveBlocksBot
import Lax3Proofs.SolveBfs
import Lax3Proofs.SolveBlocksRestrict
import Lax3Proofs.SolveBlocksBotCom
import Lax3Proofs.SolveBlocksSupports
import Lax3Proofs.SolveBlocksProfiles
import Lax3Proofs.SolveChainWin
import Lax3Proofs.SolveChainBot
import Lax3Proofs.SolveChainCover
import Lax3Proofs.SolveChainRestrict
import Lax3Proofs.SolveChain
import Lax3Proofs.SolveFrameStages
import Lax3Proofs.SolveFrameBridge
import Lax3Proofs.SolveGlueStep
import Lax3Proofs.SolveGlueLoad
import Lax3Proofs.SolveGlueLoop
import Lax3Proofs.SolveStep
import Lax3Proofs.SolveSeamTop
import Lax3Proofs.SolveSegPrep
import Lax3Proofs.SolveSegRead
import Lax3Proofs.SolveCovLoad
import Lax3Proofs.SolveCovStep
import Lax3Proofs.SolveMachPrep
import Lax3Proofs.SolveMachPrepRun
import Lax3Proofs.SolvePrepCleanFit
import Lax3Proofs.SolvePrepCleanState
import Lax3Proofs.SolvePrepCleanStep
import Lax3Proofs.SolvePrepCleanLoop
import Lax3Proofs.SolvePrepCleanFrame
import Lax3Proofs.SolvePrepCleanRoot
import Lax3Proofs.SolveMachRead
import Lax3Proofs.SolveSegReadRun
import Lax3Proofs.SolveSweepAdj
import Lax3Proofs.SolveSweepStep
import Lax3Proofs.SolveSweepOrder
import Lax3Proofs.SolveSweepBuild
import Lax3Proofs.SolveSweepMdPeel
import Lax3Proofs.SolveMdCharge
import Lax3Proofs.SolveSweepAug
import Lax3Proofs.SolveSweepAugFilter
import Lax3Proofs.SolveSweepAugStep
import Lax3Proofs.SolveSweepAugStepScan
import Lax3Proofs.SolveSweepAugRound
import Lax3Proofs.SolveSweepAugCsr
import Lax3Proofs.SolveSweepAugPairFilter
import Lax3Proofs.SolveSweepAugExtract
import Lax3Proofs.SolveSweepPeel
import Lax3Proofs.SolveRunWords
import Lax3Proofs.SolveChannels
import Lax3Proofs.SolveCodegen

-- The proofs package of submission Lax3.
--
-- What is here is the mathematical layer of the nowhere dense model
-- checking theorem: the locality engine of arXiv:2606.23180, the isolation
-- splitter game and Splitter's win on nowhere dense classes, the sparse
-- neighborhood covers of Grohe-Kreutzer-Siebertz section 6 with the
-- augmentation machinery behind their degree bound, and the two syntactic
-- rewrites (relativization to a cluster, isolation of a batch) that a
-- recursion descending the game tree performs on formulas.
--
-- What is not here, deliberately: the algorithm and its realization on
-- the word RAM. That layer was pruned on 2026-08-17 and is being redesigned
-- from first principles. See `plans/nowhere-dense-model-checking/`:
-- `pruned-algorithmic-layer.md` records what was removed and what it
-- taught, `algorithm-v2.md` is the design that replaces it. Nothing in
-- this package refers to the pruned layer, and the concept surface in
-- `../concepts` is unchanged by the prune.
--
-- Discharged here: `Lax3.Locality.locality` and `Lax3.NormalForm.normalForm`
-- (in `Assembly`). Still axioms on the concept surface:
-- `Lax3.ModelChecking.exists_almostLinearTime_program_modelChecking` (the
-- headline, which is what the redesign is for),
-- `Lax3.NowhereDenseSplitter.splitterWins_of_nowhereDense`, and
-- `Lax3.NeighborhoodCoverBound.exists_neighborhoodCover_degree_wcol`.
