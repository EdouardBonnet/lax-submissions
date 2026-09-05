import Lax3Proofs.SolveSweepStep
import Lax3Proofs.SolveBfs
import Lax67Proofs.Tactic

/-!
STATE OF THE LEAF (2026-08-27, wave w61, quota stop — file compiles, 0 sorries):
PROVED: full program text (§2); mate-swap deletion `peel_delete_turn` /
`peelDelTurnB_spec` / `peelDelB_spec`; seed `peelSeedB_spec`; expansion
`peelExpandB_spec` / `peelExpand_loop`; the potential-priced BFS pop loop
`peelBfs_loop` (64·peelDeg + 128·|fibre| + 4); reset `peelResetB_spec`;
and the full rank step `peelStepB_spec` (SwInv i → SwInv (i+1), cost
64·peelDeg i + 187·|pfibR i| + 57) including the bfs_exact/ctr-based
first-hit-mark correctness.  REMAINS: `peelInitB` prologue spec; sweep
loop over ranks (Spec.while_potential, tail-sum Σ stepK — mirror
centreLoop_of_step in SolveGlueLoop); regroup passes P1–P7 (counts →
prefix → scatter via cntBelow/restrictEmb of §6) closing `CtrArr` +
`ClusterCsr`; budget bridge peelK ≤ c₁·Impl.sweepCharge + c₂·N + c₃
(peelDeg ≤ 2·Σ dlt double count + curdeg_le_pfib, needs 1 ≤ R); core
theorem over (B,N,G,π,R); headline `covPeelIn_peelCom` at Spl := peelScr,
plC := peelCom-family, Kpl := peelK — one F7-suppliable word-room
hypothesis (mcB q x lower bound) expected at the headline.

# F6c12 — `CovPeelIn`: the GKS peeling sweep, discharged

`SolveSweepStep` names `CovPeelIn`: from the built deletable adjacency
region (`DelAdjSt` at `∅`), the order region (`OrdArr`), the rank
region (`RankArr`) and the two output allocations, run GKS's peel —
per rank one frontier-queue BFS at radius `2R` over the **live
prefixes** of the deletable structure, emit the ball, write first-hit
centre marks, delete the centre at `O(1)` per removed edge copy — and
land `CoverStageSpec`'s exact postcondition (`CtrArr` at
`Driver.centre`, `ClusterCsr` at `Driver.cluster`).  This file is that
discharge: `covPeelIn_peelCom` concludes the verbatim residual at the
concrete program `peelCom` and the closed budget `peelK`.

## The machine

One program (`peelCom`), five phases:

* **Prologue** — one `O(N)` pass: distance region to the sentinel
  `2R+1`, assignment region to the sentinel `N` (`ca[v] = N` means
  "unassigned"), stream cursor and segment anchor to `0`.
* **The sweep** — for rank `i` ascending, `u := od[i]`:
  a *frontier-queue* BFS from `u` in the current structure — the queue
  is the emitted segment of the member stream `pc.r` itself, walked by
  head/tail cursors; a popped vertex is expanded only when its stored
  level is `< 2R`, and expansion reads exactly the **live prefix**
  `aj[ao[z] .. ao[z]+dg[z])` (the w20 finding: never a full pass).
  Discovery writes the level, appends to the segment, and lays the
  first-hit `ctr` mark (`ca[w] := u` when the level is `≤ R` and
  `ca[w]` still holds the sentinel).  After the BFS the touched
  distance cells are re-sentineled by walking the emitted segment
  (`O(|X_u|)`, the E11 discipline — never `O(N)` per centre), the
  segment end is recorded (`pc.e[i+1] := tail`), and `u` is deleted:
  per live copy, swap-remove through the mate pointer at `O(1)`, then
  `dg[u] := 0`.
* **Correctness anchors** (`SolveSweepAdj` §4): the emitted segment is
  `cluster S A π u` (`cluster_eq_ball_peelSet` through the exactness
  of the truncated level table, re-derived from soundness + the
  relaxation closure by `d_complete`); the first-hit marks are
  `Driver.centre` (`centre_eq_of_hit_first`'s content, in the
  invariant form `π (ctr v) < i → ca[v] = ctr v`); the deleted set
  walks the rank prefixes (`peelSet_zero/succ`).
* **The regroup** — `ClusterCsr` wants each row **ascending**
  (`restrictEmb`'s enumeration).  Discovery order is not sorted, so
  the sweep's segments are regrouped globally at `O(N + M)`,
  `M = Σ|X_u|`: count per-member occurrences (`pc.z`), prefix-sum to
  inverse offsets (`pc.o`), scatter the (centre, member) pairs into
  member-major buckets (`pc.v`), prefix-sum the row lengths into the
  offsets `co` (via the rank array: row `u`'s segment is `ra[u]`),
  then one member-ascending placement pass: each bucket `z` appends
  `z` to the next slot (`pc.f`) of each containing row — rows fill in
  ascending member order, which *is* `restrictEmb`'s order.
* **Budget** — the BFS is priced by a queue potential whose weight at
  `z` is its live degree when `z` can be expanded (`dist < 2R`) plus a
  constant; the deletion at `u`'s current degree rides inside the
  cluster mass (`curDeg_at_deletion_le_cluster`).  The closed budget
  `peelK` is `Σ_i (peelDeg + peelNc) + O(N)` in shape;
  `peelK_le_sweepCharge` closes it against a constant multiple of the
  landed `Impl.sweepCharge` account under the wreach-degree bound —
  the scanned edges live inside the ball, and each is charged to the
  back-degree `dlt` of its later endpoint (GKS tex:1488-1491).

## The intermediate structure

Deletion is proved against `PAdj` — `DelAdjSt`'s clauses with the
current graph `H` an explicit parameter and an exemption set for the
row being dismantled (`delStar H u T` is `H` minus the `u`–`T` star).
`DelAdjSt G S = PAdj G (deleteVerts G S) S ∅` definitionally-tightly
(`delAdjSt_iff_pAdj`), and one swap-remove moves
`PAdj … (delStar H u T) … {u}` to `T ∪ {w}` (`the delete turn`).
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax12.ColoringNumbers
open Lax3Proofs.WalkDistance
open Lax3Proofs.SplitterBasics (deleteVerts_adj)

/-! ## §1 Names and the scratch descriptor -/

/-- Distance region (levels; sentinel `2R+1`). -/
def plDd : String := "pc.d"
/-- The member stream: the emitted segments, in rank order — also the
BFS queue of the segment being emitted. -/
def plRw : String := "pc.r"
/-- Segment ends: `pc.e[i]` is the stream offset where rank `i`'s
segment begins (`pc.e[N]` the total mass). -/
def plRe : String := "pc.e"
/-- Inverse counts: per member, the number of containing clusters. -/
def plDz : String := "pc.z"
/-- Inverse offsets: prefix sums of `pc.z`. -/
def plIo : String := "pc.o"
/-- Inverse cursors (scatter fill). -/
def plCu : String := "pc.c"
/-- The inverse stream: member-major buckets of containing centres. -/
def plIv : String := "pc.v"
/-- Row fill cursors of the placement pass. -/
def plFl : String := "pc.f"

/-- The eight scratch arrays of the peel pass. -/
def plArrNames : List String := [plDd, plRw, plRe, plDz, plIo, plCu, plIv, plFl]

/-- **The peel's scratch descriptor `Spl`** — length-only, as the frame
seam demands: the eight scratch allocations at the carrier bound `n`,
and the membership allocation `cm` at the mass bound `n²` (the one
allocation `CovPeelIn`'s precondition does not carry). -/
def peelScr (n : ℕ) (cm : ℕ → String) (j : ℕ) (σ : Env) : Prop :=
  n ≤ (σ.arrs plDd).length ∧ n * n ≤ (σ.arrs plRw).length ∧
  n + 1 ≤ (σ.arrs plRe).length ∧ n ≤ (σ.arrs plDz).length ∧
  n + 1 ≤ (σ.arrs plIo).length ∧ n ≤ (σ.arrs plCu).length ∧
  n * n ≤ (σ.arrs plIv).length ∧ n ≤ (σ.arrs plFl).length ∧
  n * n ≤ (σ.arrs (cm j)).length

/-! ## §2 The program -/

/-- One turn of the expansion scan over `z`'s live prefix: read the
slot; on an undiscovered target, set its level, lay the first-hit mark
when within radius `R`, and append it to the queue. -/
def peelExpandB (R : ℕ) (ca aj : String) : Com :=
  .seq (.assign "pl.w" (.get aj (.add (.var "pl.a") (.var "pl.j"))))
    (.seq
      (.ite (.eq (.get plDd (.var "pl.w")) (.lit (2 * R + 1)))
        (.seq (.store plDd (.var "pl.w") (.add (.var "pl.d") (.lit 1)))
          (.seq
            (.ite (.lt (.lit R) (.add (.var "pl.d") (.lit 1)))
              .skip
              (.ite (.eq (.get ca (.var "pl.w")) (.var "pl.n"))
                (.store ca (.var "pl.w") (.var "pl.u"))
                .skip))
            (.seq (.store plRw (.var "pl.t") (.var "pl.w"))
              (.assign "pl.t" (.add (.var "pl.t") (.lit 1))))))
        .skip)
      (.assign "pl.j" (.add (.var "pl.j") (.lit 1))))

/-- One BFS pop: read the head vertex and its level; when the level is
below `2R`, scan its live prefix; advance the head. -/
def peelPopB (R : ℕ) (ca ao aj dg : String) : Com :=
  .seq (.assign "pl.z" (.get plRw (.var "pl.h")))
    (.seq (.assign "pl.d" (.get plDd (.var "pl.z")))
      (.seq
        (.ite (.lt (.var "pl.d") (.lit (2 * R)))
          (.seq (.assign "pl.a" (.get ao (.var "pl.z")))
            (.seq (.assign "pl.g" (.get dg (.var "pl.z")))
              (.seq (.assign "pl.j" (.lit 0))
                (.while (.lt (.var "pl.j") (.var "pl.g"))
                  (peelExpandB R ca aj)))))
          .skip)
        (.assign "pl.h" (.add (.var "pl.h") (.lit 1)))))

/-- The seed: the centre off the order region, level `0`, the segment
anchor, the self mark, the two cursors. -/
def peelSeedB (ca od : String) : Com :=
  .seq (.assign "pl.u" (.get od (.var "pl.i")))
    (.seq (.assign "pl.b" (.var "pl.m"))
      (.seq (.store plDd (.var "pl.u") (.lit 0))
        (.seq (.store plRw (.var "pl.m") (.var "pl.u"))
          (.seq
            (.ite (.eq (.get ca (.var "pl.u")) (.var "pl.n"))
              (.store ca (.var "pl.u") (.var "pl.u"))
              .skip)
            (.seq (.assign "pl.h" (.var "pl.m"))
              (.assign "pl.t" (.add (.var "pl.m") (.lit 1))))))))

/-- The touched-cell reset: walk the emitted segment, re-sentinel the
level of each member — `O(|X_u|)`, never `O(N)`. -/
def peelResetB (R : ℕ) : Com :=
  .seq (.assign "pl.k" (.var "pl.b"))
    (.while (.lt (.var "pl.k") (.var "pl.t"))
      (.seq (.store plDd (.get plRw (.var "pl.k")) (.lit (2 * R + 1)))
        (.assign "pl.k" (.add (.var "pl.k") (.lit 1)))))

/-- One swap-remove: `u`'s copy at slot `pl.a + pl.j` names the mate
slot `m` inside `w`'s row; move `w`'s last live slot into `m`, repair
the moved copy's mate, shrink `w`'s live prefix. -/
def peelDelTurnB (ao aj dg mt : String) : Com :=
  .seq (.assign "pl.w" (.get aj (.add (.var "pl.a") (.var "pl.j"))))
    (.seq (.assign "pl.p" (.get mt (.add (.var "pl.a") (.var "pl.j"))))
      (.seq (.assign "pl.k"
          (.sub (.add (.get ao (.var "pl.w")) (.get dg (.var "pl.w"))) (.lit 1)))
        (.seq (.assign "pl.y" (.get aj (.var "pl.k")))
          (.seq (.assign "pl.s" (.get mt (.var "pl.k")))
            (.seq (.store aj (.var "pl.p") (.var "pl.y"))
              (.seq (.store mt (.var "pl.p") (.var "pl.s"))
                (.seq (.store mt (.var "pl.s") (.var "pl.p"))
                  (.seq (.store dg (.var "pl.w")
                      (.sub (.get dg (.var "pl.w")) (.lit 1)))
                    (.assign "pl.j" (.add (.var "pl.j") (.lit 1)))))))))))

/-- Delete the centre: one swap-remove per live copy, then kill the
row. -/
def peelDelB (ao aj dg mt : String) : Com :=
  .seq (.assign "pl.a" (.get ao (.var "pl.u")))
    (.seq (.assign "pl.g" (.get dg (.var "pl.u")))
      (.seq (.assign "pl.j" (.lit 0))
        (.seq
          (.while (.lt (.var "pl.j") (.var "pl.g")) (peelDelTurnB ao aj dg mt))
          (.store dg (.var "pl.u") (.lit 0)))))

/-- One rank of the sweep: seed, BFS, reset, segment end, delete. -/
def peelStepB (R : ℕ) (ca ao aj dg mt od : String) : Com :=
  .seq (peelSeedB ca od)
    (.seq (.while (.lt (.var "pl.h") (.var "pl.t")) (peelPopB R ca ao aj dg))
      (.seq (peelResetB R)
        (.seq (.store plRe (.add (.var "pl.i") (.lit 1)) (.var "pl.t"))
          (.seq (.assign "pl.m" (.var "pl.t"))
            (peelDelB ao aj dg mt)))))

/-- The prologue: `N` off the carrier cell, one fused sentinel pass,
the stream anchors. -/
def peelInitB (R : ℕ) (nNs ca : String) : Com :=
  .seq (.assign "pl.n" (.var nNs))
    (.seq (.assign "pl.i" (.lit 0))
      (.seq
        (.while (.lt (.var "pl.i") (.var "pl.n"))
          (.seq (.store plDd (.var "pl.i") (.lit (2 * R + 1)))
            (.seq (.store ca (.var "pl.i") (.var "pl.n"))
              (.assign "pl.i" (.add (.var "pl.i") (.lit 1))))))
        (.seq (.assign "pl.m" (.lit 0))
          (.store plRe (.lit 0) (.lit 0)))))

/-- The sweep loop over the ranks. -/
def peelSweepB (R : ℕ) (ca ao aj dg mt od : String) : Com :=
  .seq (.assign "pl.i" (.lit 0))
    (.while (.lt (.var "pl.i") (.var "pl.n"))
      (.seq (peelStepB R ca ao aj dg mt od)
        (.assign "pl.i" (.add (.var "pl.i") (.lit 1)))))

/-- Regroup pass 1: zero the inverse counts. -/
def peelP1B : Com :=
  .seq (.assign "pl.i" (.lit 0))
    (.while (.lt (.var "pl.i") (.var "pl.n"))
      (.seq (.store plDz (.var "pl.i") (.lit 0))
        (.assign "pl.i" (.add (.var "pl.i") (.lit 1)))))

/-- Regroup pass 2: count occurrences over the whole stream. -/
def peelP2B : Com :=
  .seq (.assign "pl.k" (.lit 0))
    (.while (.lt (.var "pl.k") (.var "pl.m"))
      (.seq (.store plDz (.get plRw (.var "pl.k"))
          (.add (.get plDz (.get plRw (.var "pl.k"))) (.lit 1)))
        (.assign "pl.k" (.add (.var "pl.k") (.lit 1)))))

/-- Regroup pass 3: prefix-sum the counts into the inverse offsets. -/
def peelP3B : Com :=
  .seq (.store plIo (.lit 0) (.lit 0))
    (.seq (.assign "pl.i" (.lit 0))
      (.while (.lt (.var "pl.i") (.var "pl.n"))
        (.seq (.store plIo (.add (.var "pl.i") (.lit 1))
            (.add (.get plIo (.var "pl.i")) (.get plDz (.var "pl.i"))))
          (.assign "pl.i" (.add (.var "pl.i") (.lit 1))))))

/-- Regroup pass 3b: cursors to the bucket starts. -/
def peelP3bB : Com :=
  .seq (.assign "pl.i" (.lit 0))
    (.while (.lt (.var "pl.i") (.var "pl.n"))
      (.seq (.store plCu (.var "pl.i") (.get plIo (.var "pl.i")))
        (.assign "pl.i" (.add (.var "pl.i") (.lit 1)))))

/-- Regroup pass 4: scatter each segment's pairs into the member-major
buckets — outer loop over ranks, inner over the segment. -/
def peelP4B (od : String) : Com :=
  .seq (.assign "pl.i" (.lit 0))
    (.while (.lt (.var "pl.i") (.var "pl.n"))
      (.seq (.assign "pl.u" (.get od (.var "pl.i")))
        (.seq (.assign "pl.k" (.get plRe (.var "pl.i")))
          (.seq (.assign "pl.g" (.get plRe (.add (.var "pl.i") (.lit 1))))
            (.seq
              (.while (.lt (.var "pl.k") (.var "pl.g"))
                (.seq (.assign "pl.z" (.get plRw (.var "pl.k")))
                  (.seq (.store plIv (.get plCu (.var "pl.z")) (.var "pl.u"))
                    (.seq (.store plCu (.var "pl.z")
                        (.add (.get plCu (.var "pl.z")) (.lit 1)))
                      (.assign "pl.k" (.add (.var "pl.k") (.lit 1)))))))
              (.assign "pl.i" (.add (.var "pl.i") (.lit 1))))))))

/-- Regroup pass 5: the output offsets — row `u`'s length is its
segment's, found through the rank region. -/
def peelP5B (co ra : String) : Com :=
  .seq (.store co (.lit 0) (.lit 0))
    (.seq (.assign "pl.i" (.lit 0))
      (.while (.lt (.var "pl.i") (.var "pl.n"))
        (.seq (.assign "pl.k" (.get ra (.var "pl.i")))
          (.seq (.store co (.add (.var "pl.i") (.lit 1))
              (.add (.get co (.var "pl.i"))
                (.sub (.get plRe (.add (.var "pl.k") (.lit 1)))
                  (.get plRe (.var "pl.k")))))
            (.assign "pl.i" (.add (.var "pl.i") (.lit 1)))))))

/-- Regroup pass 6: row fill cursors to the row starts. -/
def peelP6B (co : String) : Com :=
  .seq (.assign "pl.i" (.lit 0))
    (.while (.lt (.var "pl.i") (.var "pl.n"))
      (.seq (.store plFl (.var "pl.i") (.get co (.var "pl.i")))
        (.assign "pl.i" (.add (.var "pl.i") (.lit 1)))))

/-- Regroup pass 7: the member-ascending placement — bucket `z` puts
`z` into the next slot of every containing row; rows fill sorted. -/
def peelP7B (cm : String) : Com :=
  .seq (.assign "pl.z" (.lit 0))
    (.while (.lt (.var "pl.z") (.var "pl.n"))
      (.seq (.assign "pl.k" (.get plIo (.var "pl.z")))
        (.seq (.assign "pl.g" (.get plIo (.add (.var "pl.z") (.lit 1))))
          (.seq
            (.while (.lt (.var "pl.k") (.var "pl.g"))
              (.seq (.assign "pl.u" (.get plIv (.var "pl.k")))
                (.seq (.store cm (.get plFl (.var "pl.u")) (.var "pl.z"))
                  (.seq (.store plFl (.var "pl.u")
                      (.add (.get plFl (.var "pl.u")) (.lit 1)))
                    (.assign "pl.k" (.add (.var "pl.k") (.lit 1)))))))
            (.assign "pl.z" (.add (.var "pl.z") (.lit 1)))))))

/-- **The peel program**: prologue, sweep, regroup. -/
def peelCom (R : ℕ) (nNs ca co cm ra ao aj dg mt od : String) : Com :=
  .seq (peelInitB R nNs ca)
    (.seq (peelSweepB R ca ao aj dg mt od)
      (.seq peelP1B
        (.seq peelP2B
          (.seq peelP3B
            (.seq peelP3bB
              (.seq (peelP4B od)
                (.seq (peelP5B co ra)
                  (.seq (peelP6B co) (peelP7B cm)))))))))

/-! ## §3 Cell algebra -/

/-- Reading through a store, `getD`-pointwise. -/
theorem getD_set (l : List ℕ) {i : ℕ} (v j : ℕ) (hi : i < l.length) :
    (l.set i v).getD j 0 = if j = i then v else l.getD j 0 := by
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_set_self hi]
    rfl
  · rw [if_neg hj, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_set_ne (fun h => hj h.symm)]

private theorem evalB_incr {B : ℕ} {x : String} {σ : Env}
    (hx : σ.vars x + 1 < B) :
    (Expr.add (.var x) (.lit 1)).evalB B σ = some (σ.vars x + 1) := by
  have h := evalB_bin (B := B) (op := .add) (e := .var x) (f := .lit 1) (σ := σ)
    (evalB_var (by omega)) (evalB_lit (by omega)) (by simpa using hx)
  simpa using h

/-! ## §4 The star deletion, and the parametric region -/

/-- `H` minus the `u`–`T` star: the graph after the copies of `u`'s
edges into `T` are unlinked.  The deletion loop walks `T` up `u`'s
frozen live prefix. -/
def delStar {N : ℕ} (H : SimpleGraph (Fin N)) (u : Fin N) (T : Set (Fin N)) :
    SimpleGraph (Fin N) where
  Adj v w := H.Adj v w ∧ ¬(v = u ∧ w ∈ T) ∧ ¬(w = u ∧ v ∈ T)
  symm := by
    intro v w h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    exact ⟨fun v h => H.irrefl h.1⟩

theorem delStar_adj {N : ℕ} {H : SimpleGraph (Fin N)} {u : Fin N}
    {T : Set (Fin N)} {v w : Fin N} :
    (delStar H u T).Adj v w ↔
      H.Adj v w ∧ ¬(v = u ∧ w ∈ T) ∧ ¬(w = u ∧ v ∈ T) := Iff.rfl

theorem delStar_le {N : ℕ} (H : SimpleGraph (Fin N)) (u : Fin N)
    (T : Set (Fin N)) : delStar H u T ≤ H := by
  intro v w h
  exact h.1

@[simp] theorem delStar_empty {N : ℕ} (H : SimpleGraph (Fin N)) (u : Fin N) :
    delStar H u (∅ : Set (Fin N)) = H := by
  ext v w
  simp [delStar_adj]

open Classical in
/-- Away from `u`, the star deletion only removes the `u`-edge (when
the row is in `T`). -/
theorem delStar_neighborSet_ne {N : ℕ} (H : SimpleGraph (Fin N)) (u : Fin N)
    (T : Set (Fin N)) {v : Fin N} (hv : v ≠ u) :
    (delStar H u T).neighborSet v =
      if v ∈ T then H.neighborSet v \ {u} else H.neighborSet v := by
  by_cases hvT : v ∈ T
  · rw [if_pos hvT]
    ext w
    simp only [SimpleGraph.mem_neighborSet, delStar_adj, Set.mem_diff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, -, h3⟩
      refine ⟨h1, fun hw => h3 ⟨hw, hvT⟩⟩
    · rintro ⟨h1, hw⟩
      exact ⟨h1, fun hc => hv hc.1, fun hc => hw hc.1⟩
  · rw [if_neg hvT]
    ext w
    simp only [SimpleGraph.mem_neighborSet, delStar_adj]
    constructor
    · rintro ⟨h1, -, -⟩; exact h1
    · intro h1
      exact ⟨h1, fun hc => hv hc.1, fun hc => hvT hc.2⟩

/-- At `u`, the star deletion removes exactly `T`. -/
theorem delStar_neighborSet_self {N : ℕ} (H : SimpleGraph (Fin N)) (u : Fin N)
    (T : Set (Fin N)) :
    (delStar H u T).neighborSet u = H.neighborSet u \ T := by
  ext w
  simp only [SimpleGraph.mem_neighborSet, delStar_adj, Set.mem_diff]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, fun hw => h2 ⟨trivial, hw⟩⟩
  · rintro ⟨h1, hw⟩
    refine ⟨h1, fun hc => hw hc.2, fun hc => ?_⟩
    exact H.irrefl (hc.1 ▸ h1)

/-- Killing the whole current star is deleting the vertex. -/
theorem delStar_neighborSet_eq_deleteVerts {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Set (Fin N)) (u : Fin N) {T : Set (Fin N)}
    (hT : ∀ w, (deleteVerts G S).Adj u w → w ∈ T) :
    delStar (deleteVerts G S) u T = deleteVerts G (S ∪ {u}) := by
  ext v w
  rw [delStar_adj, deleteVerts_adj, deleteVerts_adj]
  constructor
  · rintro ⟨⟨hadj, hv, hw⟩, h2, h3⟩
    refine ⟨hadj, ?_, ?_⟩
    · intro hc
      rcases (Set.mem_union _ _ _).mp hc with h | h
      · exact hv h
      · obtain rfl := Set.mem_singleton_iff.mp h
        exact h2 ⟨rfl, hT w ⟨hadj, hv, hw⟩⟩
    · intro hc
      rcases (Set.mem_union _ _ _).mp hc with h | h
      · exact hw h
      · obtain rfl := Set.mem_singleton_iff.mp h
        exact h3 ⟨rfl, hT v ⟨hadj.symm, hw, hv⟩⟩
  · rintro ⟨hadj, hv, hw⟩
    refine ⟨⟨hadj, fun h => hv (Set.mem_union_left _ h),
      fun h => hw (Set.mem_union_left _ h)⟩, ?_, ?_⟩
    · rintro ⟨rfl, -⟩
      exact hv (Set.mem_union_right _ rfl)
    · rintro ⟨rfl, -⟩
      exact hw (Set.mem_union_right _ rfl)

/-- **The parametric region, function level**: `DelAdjSt`'s live-data
clauses over the `getD`-read functions, with the current graph `H`
explicit and the rows of `ex` suspended (their cells hold whatever the
suspension's owner maintains by hand).  `dead` rows are empty; live,
unsuspended rows are exact live prefixes of `H` with consistent
mates. -/
def PAdjF {N : ℕ} (H : SimpleGraph (Fin N)) (dead ex : Set (Fin N))
    (offF AJ MT DG : ℕ → ℕ) : Prop :=
  (∀ v : Fin N, v ∈ dead → DG (v : ℕ) = 0) ∧
  (∀ v : Fin N, v ∉ dead → v ∉ ex → DG (v : ℕ) = (H.neighborSet v).ncard) ∧
  (∀ v : Fin N, v ∉ dead → v ∉ ex → ∀ t : ℕ, t < DG (v : ℕ) →
    ∃ w : Fin N, H.Adj v w ∧ AJ (offF (v : ℕ) + t) = (w : ℕ) ∧
      ∃ s : ℕ, s < DG (w : ℕ) ∧ MT (offF (v : ℕ) + t) = offF (w : ℕ) + s ∧
        AJ (offF (w : ℕ) + s) = (v : ℕ) ∧
        MT (offF (w : ℕ) + s) = offF (v : ℕ) + t) ∧
  (∀ v : Fin N, v ∉ dead → v ∉ ex → ∀ w : Fin N, H.Adj v w →
    ∃ t : ℕ, t < DG (v : ℕ) ∧ AJ (offF (v : ℕ) + t) = (w : ℕ))

/-- **The parametric region, at a pinned offset function**: the offset
head (anchor, degree-sum steps, the `ao` region, the allocations) plus
the function-level clauses at the `getD` reads. -/
def PAdjOff (ao aj dg mt : String) {N : ℕ} (G H : SimpleGraph (Fin N))
    (dead ex : Set (Fin N)) (offF : ℕ → ℕ) (σ : Env) : Prop :=
  offF 0 = 0 ∧
  (∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) ∧
  N + 1 ≤ (σ.arrs ao).length ∧
  (∀ i, i ≤ N → (σ.arrs ao).getD i 0 = offF i) ∧
  offF N ≤ (σ.arrs aj).length ∧
  offF N ≤ (σ.arrs mt).length ∧
  N ≤ (σ.arrs dg).length ∧
  PAdjF H dead ex offF (fun c => (σ.arrs aj).getD c 0)
    (fun c => (σ.arrs mt).getD c 0) (fun c => (σ.arrs dg).getD c 0)

/-- The landed region is the parametric one at `deleteVerts` and no
suspension. -/
theorem delAdjSt_iff_pAdj {ao aj dg mt : String} {N : ℕ}
    {G : SimpleGraph (Fin N)} {S : Set (Fin N)} {σ : Env} :
    DelAdjSt ao aj dg mt G S σ ↔
      ∃ offF, PAdjOff ao aj dg mt G (deleteVerts G S) S ∅ offF σ := by
  constructor
  · rintro ⟨offF, h0, hstep, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨offF, h0, hstep, h1, h2, h3, h4, h5, h6,
      fun v hv _ => h7 v hv, fun v hv _ => h8 v hv, fun v hv _ => h9 v hv⟩
  · rintro ⟨offF, h0, hstep, h1, h2, h3, h4, h5, ⟨h6, h7, h8, h9⟩⟩
    exact ⟨offF, h0, hstep, h1, h2, h3, h4, h5, h6,
      fun v hv => h7 v hv (Set.notMem_empty v),
      fun v hv => h8 v hv (Set.notMem_empty v),
      fun v hv => h9 v hv (Set.notMem_empty v)⟩

section PAdjFacts

variable {N : ℕ} {G H : SimpleGraph (Fin N)}
  {dead ex : Set (Fin N)} {offF AJ MT DG : ℕ → ℕ}

/-- A live, unsuspended row enumerates without duplicates —
`DelAdjSt.slot_injOn`'s pigeonhole, at the parametric region. -/
theorem PAdjF.rowInj (h : PAdjF H dead ex offF AJ MT DG)
    {v : Fin N} (hv : v ∉ dead) (hv' : v ∉ ex) {s s' : ℕ}
    (hs : s < DG (v : ℕ)) (hs' : s' < DG (v : ℕ))
    (heq : AJ (offF (v : ℕ) + s) = AJ (offF (v : ℕ) + s')) : s = s' := by
  obtain ⟨-, hdeg, -, hcomp⟩ := h
  have hdv := hdeg v hv hv'
  have h1 : (Fin.val '' (H.neighborSet v)) ⊆
      ↑((Finset.range (DG (v : ℕ))).image
        (fun t => AJ (offF (v : ℕ) + t))) := by
    rintro x ⟨w, hw, rfl⟩
    obtain ⟨t, ht, hval⟩ := hcomp v hv hv' w hw
    exact Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, hval⟩)
  have h2 : DG (v : ℕ) ≤
      ((Finset.range (DG (v : ℕ))).image
        (fun t => AJ (offF (v : ℕ) + t))).card :=
    calc DG (v : ℕ)
        = (H.neighborSet v).ncard := hdv
      _ = (Fin.val '' (H.neighborSet v)).ncard :=
          (Set.ncard_image_of_injective _ Fin.val_injective).symm
      _ ≤ _ := by
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard h1 (Set.toFinite _)
  have h3 : ((Finset.range (DG (v : ℕ))).image
      (fun t => AJ (offF (v : ℕ) + t))).card =
        (Finset.range (DG (v : ℕ))).card :=
    le_antisymm Finset.card_image_le (by rw [Finset.card_range]; exact h2)
  have hinj := Finset.injOn_of_card_image_eq h3
  exact hinj (Finset.mem_coe.mpr (Finset.mem_range.mpr hs))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr hs')) heq

/-- Slot-space room: a slot below a row bound that is itself below the
base degree lands inside the slot space. -/
theorem slot_lt_of_le {v : Fin N} {t : ℕ}
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard)
    (hle : t < (G.neighborSet v).ncard) :
    offF (v : ℕ) + t < offF N := by
  have hlt : offF (v : ℕ) + t < offF ((v : ℕ) + 1) := by
    rw [hstep v]
    omega
  exact lt_of_lt_of_le hlt (offF_mono hstep N le_rfl ((v : ℕ) + 1) v.isLt)

end PAdjFacts

/-! ## §5 The deletion loop's state -/

/-- The processed star: the first `t` values of the frozen prefix. -/
def Tset {N : ℕ} (wfun : ℕ → ℕ) (t : ℕ) : Set (Fin N) :=
  {x | ∃ s, s < t ∧ (x : ℕ) = wfun s}

@[simp] theorem Tset_zero {N : ℕ} (wfun : ℕ → ℕ) :
    Tset (N := N) wfun 0 = ∅ := by
  ext x
  simp [Tset]

theorem mem_Tset_succ {N : ℕ} {wfun : ℕ → ℕ} {t : ℕ} {x : Fin N} :
    x ∈ Tset wfun (t + 1) ↔ x ∈ Tset wfun t ∨ (x : ℕ) = wfun t := by
  constructor
  · rintro ⟨s, hs, hx⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | rfl
    · exact Or.inl ⟨s, h, hx⟩
    · exact Or.inr hx
  · rintro (⟨s, hs, hx⟩ | hx)
    · exact ⟨s, by omega, hx⟩
    · exact ⟨t, by omega, hx⟩

/-- One more processed value refines the star-deleted adjacency by the
single edge `u`–`wfun t`. -/
theorem delStar_Tset_succ_adj {N : ℕ} {H₀ : SimpleGraph (Fin N)} {u : Fin N}
    {wfun : ℕ → ℕ} {t : ℕ} {v x : Fin N} :
    (delStar H₀ u (Tset wfun (t + 1))).Adj v x ↔
      (delStar H₀ u (Tset wfun t)).Adj v x ∧
        ¬(v = u ∧ (x : ℕ) = wfun t) ∧ ¬(x = u ∧ (v : ℕ) = wfun t) := by
  rw [delStar_adj, delStar_adj]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, fun hc => h2 ⟨hc.1, mem_Tset_succ.mpr (Or.inl hc.2)⟩,
      fun hc => h3 ⟨hc.1, mem_Tset_succ.mpr (Or.inl hc.2)⟩⟩,
      fun hc => h2 ⟨hc.1, mem_Tset_succ.mpr (Or.inr hc.2)⟩,
      fun hc => h3 ⟨hc.1, mem_Tset_succ.mpr (Or.inr hc.2)⟩⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    refine ⟨h1, ?_, ?_⟩
    · rintro ⟨rfl, hmem⟩
      rcases mem_Tset_succ.mp hmem with h | h
      · exact h2 ⟨rfl, h⟩
      · exact h4 ⟨rfl, h⟩
    · rintro ⟨rfl, hmem⟩
      rcases mem_Tset_succ.mp hmem with h | h
      · exact h3 ⟨rfl, h⟩
      · exact h5 ⟨rfl, h⟩

/-- **The `u`-row clauses of the deletion loop**: the still-unprocessed
slots of the frozen prefix read their original values, and each still
carries a consistent mate into its target's live prefix. -/
def URowF {N : ℕ} (u : Fin N) (offF wfun AJ MT DG : ℕ → ℕ)
    (dgu t : ℕ) : Prop :=
  ∀ s : ℕ, t ≤ s → s < dgu →
    AJ (offF (u : ℕ) + s) = wfun s ∧
    ∃ s' : ℕ, s' < DG (wfun s) ∧
      MT (offF (u : ℕ) + s) = offF (wfun s) + s' ∧
      AJ (offF (wfun s) + s') = (u : ℕ) ∧
      MT (offF (wfun s) + s') = offF (u : ℕ) + s

section DeleteTurn

variable {N : ℕ} {G : SimpleGraph (Fin N)} {dead : Set (Fin N)} {u : Fin N}
  {offF wfun AJ MT DG : ℕ → ℕ} {dgu t : ℕ}

/-- A neighbourhood inside `Fin N` has at most `N` members. -/
theorem ncard_neighborSet_le_card {H : SimpleGraph (Fin N)} (v : Fin N) :
    (H.neighborSet v).ncard ≤ N := by
  calc (H.neighborSet v).ncard ≤ (Set.univ : Set (Fin N)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    _ = N := by simp [Set.ncard_univ]

/-- The whole slot space is at most `N²`. -/
theorem offF_le_sq (h0 : offF 0 = 0)
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) :
    offF N ≤ N * N := by
  suffices h : ∀ i, i ≤ N → offF i ≤ i * N from h N le_rfl
  intro i
  induction i with
  | zero => intro _; simp [h0]
  | succ k ih =>
      intro hk
      have hkN : k < N := hk
      rw [hstep ⟨k, hkN⟩]
      have hval : ((⟨k, hkN⟩ : Fin N) : ℕ) = k := rfl
      rw [hval]
      have h1 := ih (by omega)
      have h2 := ncard_neighborSet_le_card (H := G) ⟨k, hkN⟩
      have : (k + 1) * N = k * N + N := by ring
      omega

/-- Distinct rows occupy disjoint slot ranges. -/
theorem offF_row_ne
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard)
    {v v' : Fin N} (hne : v ≠ v') {a a' : ℕ}
    (ha : a < (G.neighborSet v).ncard) (ha' : a' < (G.neighborSet v').ncard) :
    offF (v : ℕ) + a ≠ offF (v' : ℕ) + a' := by
  have key : ∀ x x' : Fin N, (x : ℕ) < (x' : ℕ) → ∀ {b b' : ℕ},
      b < (G.neighborSet x).ncard → b' < (G.neighborSet x').ncard →
      offF (x : ℕ) + b ≠ offF (x' : ℕ) + b' := by
    intro x x' hlt b b' hb hb'
    have h1 : offF (x : ℕ) + b < offF ((x : ℕ) + 1) := by
      rw [hstep x]; omega
    have h2 : offF ((x : ℕ) + 1) ≤ offF (x' : ℕ) :=
      offF_mono hstep (x' : ℕ) (le_of_lt x'.isLt) ((x : ℕ) + 1) (by omega)
    omega
  rcases Nat.lt_trichotomy (v : ℕ) (v' : ℕ) with h | h | h
  · exact key v v' h ha ha'
  · exact absurd (Fin.ext h) hne
  · exact fun hc => key v' v h ha' ha hc.symm

/-- **The delete turn**: with the region suspended at `u` and the
`u`-row clauses at position `t < dgu`, one swap-remove — read the mate
`p` of `u`'s copy `t`, move the target row's last live slot into `p`,
repair the moved copy's mate, shrink the row — advances the processed
star by `wfun t`.  The machine's five reads are named and bounded, and
the three stores' pointwise effect is exactly the update functions the
conclusion carries. -/
theorem peel_delete_turn
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard)
    (hwN : ∀ s, s < dgu → wfun s < N)
    (hwadj : ∀ s, (hs : s < dgu) → (deleteVerts G dead).Adj u ⟨wfun s, hwN s hs⟩)
    (hwinj : ∀ s, s < dgu → ∀ s', s' < dgu → wfun s = wfun s' → s = s')
    (hdguG : dgu ≤ (G.neighborSet u).ncard)
    (hP : PAdjF (delStar (deleteVerts G dead) u (Tset wfun t)) dead {u} offF AJ MT DG)
    (hU : URowF u offF wfun AJ MT DG dgu t)
    (hdgu : DG (u : ℕ) = dgu)
    (ht : t < dgu) :
    ∃ pv gv yv ysv : ℕ,
      MT (offF (u : ℕ) + t) = pv ∧
      AJ (offF (u : ℕ) + t) = wfun t ∧
      DG (wfun t) = gv ∧ 1 ≤ gv ∧ gv ≤ N ∧
      AJ (offF (wfun t) + (gv - 1)) = yv ∧
      MT (offF (wfun t) + (gv - 1)) = ysv ∧
      pv < offF N ∧ ysv < offF N ∧ offF (wfun t) + (gv - 1) < offF N ∧
      yv < N ∧ (u : ℕ) ≠ wfun t ∧ wfun t < N ∧ pv ≠ ysv ∧
      offF (wfun t) ≤ pv ∧
      PAdjF (delStar (deleteVerts G dead) u (Tset wfun (t + 1))) dead {u} offF
        (fun c => if c = pv then yv else AJ c)
        (fun c => if c = ysv then pv else if c = pv then ysv else MT c)
        (fun c => if c = wfun t then gv - 1 else DG c) ∧
      URowF u offF wfun
        (fun c => if c = pv then yv else AJ c)
        (fun c => if c = ysv then pv else if c = pv then ysv else MT c)
        (fun c => if c = wfun t then gv - 1 else DG c) dgu (t + 1) := by
  classical
  have hP' := hP
  obtain ⟨hdead, hdeg, hsound, hcomp⟩ := hP'
  set H₀ := deleteVerts G dead with hH₀
  set Ht := delStar H₀ u (Tset wfun t) with hHt
  set W : Fin N := ⟨wfun t, hwN t ht⟩ with hW
  have hWval : (W : ℕ) = wfun t := rfl
  have huW : u ≠ W := (hwadj t ht).ne
  have hWu : W ≠ u := huW.symm
  have hne_ut : (u : ℕ) ≠ wfun t := fun h => huW (Fin.ext h)
  have hvalW : ∀ {v : Fin N}, (v : ℕ) = wfun t → v = W :=
    fun {v} h => Fin.ext (h.trans hWval.symm)
  have hWdead : W ∉ dead := ((deleteVerts_adj).mp (hwadj t ht)).2.2
  have hudead : u ∉ dead := ((deleteVerts_adj).mp (hwadj t ht)).2.1
  have hWex : W ∉ ({u} : Set (Fin N)) := by
    simp only [Set.mem_singleton_iff]
    exact hWu
  have hWT : W ∉ Tset wfun t := by
    rintro ⟨s, hs, hval⟩
    have := hwinj t ht s (by omega) (by exact hval)
    omega
  -- degrees below the base graph
  have hHtG : ∀ {a b : Fin N}, Ht.Adj a b → G.Adj a b := by
    intro a b h
    exact (deleteVerts_le G dead) ((delStar_le H₀ u _) h)
  have hHtdead : ∀ {a b : Fin N}, Ht.Adj a b → b ∉ dead := by
    intro a b h
    exact ((deleteVerts_adj).mp ((delStar_le H₀ u _) h)).2.2
  have hDGle : ∀ v : Fin N, v ∉ dead → v ≠ u →
      DG (v : ℕ) ≤ (G.neighborSet v).ncard := by
    intro v hv hv'
    rw [hdeg v hv (by simpa using hv')]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro w hw
    exact hHtG hw
  have hrne : ∀ (a b : Fin N), a ≠ b → ∀ {c c' : ℕ},
      c < (G.neighborSet a).ncard → c' < (G.neighborSet b).ncard →
      offF (a : ℕ) + c ≠ offF (b : ℕ) + c' :=
    fun a b hab {c c'} hc hc' => offF_row_ne hstep hab hc hc'
  -- the mate of u's copy t
  obtain ⟨hAJut, s', hs'g, hMTut, hAJp, hMTp⟩ := hU t le_rfl ht
  set gv := DG (wfun t) with hgv
  have hg1 : 1 ≤ gv := by omega
  have hgleG : gv ≤ (G.neighborSet W).ncard := hDGle W hWdead hWu
  have hgN : gv ≤ N := le_trans hgleG (ncard_neighborSet_le_card W)
  have hs'G : s' < (G.neighborSet W).ncard := lt_of_lt_of_le hs'g hgleG
  set pv := offF (wfun t) + s' with hpv
  -- the last live slot of W's row and its data
  have hlastg : gv - 1 < gv := by omega
  have hlastG : gv - 1 < (G.neighborSet W).ncard := lt_of_lt_of_le hlastg hgleG
  have hWTsucc : W ∈ Tset wfun (t + 1) := mem_Tset_succ.mpr (Or.inr rfl)
  obtain ⟨y, hHtWy, hAJlast, s'', hs''lt, hMTlast, hAJys, hMTys⟩ :=
    hsound W hWdead hWex (gv - 1) (by omega)
  rw [show offF ((W : ℕ)) = offF (wfun t) from rfl] at hAJlast hMTlast hMTys
  set lastv := offF (wfun t) + (gv - 1) with hlastv
  set ysv := offF (y : ℕ) + s'' with hysv
  have hydead : y ∉ dead := hHtdead hHtWy
  have hyW : y ≠ W := (SimpleGraph.Adj.ne hHtWy).symm
  have hyWv : (y : ℕ) ≠ wfun t := fun h => hyW (hvalW h)
  -- range facts
  have hpvlt : pv < offF N := by
    rw [hpv, ← hWval]
    exact slot_lt_of_le hstep hs'G
  have hlastlt' : lastv < offF N := by
    rw [hlastv, ← hWval]
    exact slot_lt_of_le hstep hlastG
  have hs''G : s'' < (G.neighborSet y).ncard := by
    by_cases hyu : y = u
    · subst hyu
      rw [hdgu] at hs''lt
      exact lt_of_lt_of_le hs''lt hdguG
    · exact lt_of_lt_of_le hs''lt (hDGle y hydead hyu)
  have hysvlt : ysv < offF N := by
    rw [hysv]
    exact slot_lt_of_le hstep hs''G
  have hyvN : AJ lastv < N := by
    rw [hAJlast]
    exact y.isLt
  have hpvne_ysv : pv ≠ ysv := by
    rw [hpv, hysv, ← hWval]
    exact hrne W y hyW.symm hs'G hs''G
  -- the mate of u's copy t sits in W's live row
  have hpv_lo : offF (wfun t) ≤ pv := by
    rw [hpv]
    omega
  -- abbreviations for the update functions
  set AJ' : ℕ → ℕ := fun c => if c = pv then AJ lastv else AJ c with hAJ'
  set MT' : ℕ → ℕ := fun c => if c = ysv then pv else if c = pv then ysv else MT c
    with hMT'
  set DG' : ℕ → ℕ := fun c => if c = wfun t then gv - 1 else DG c with hDG'
  -- membership of the refined star, and the refined neighbourhoods
  have hTT : ∀ {v : Fin N}, v ≠ W →
      (v ∈ Tset wfun (t + 1) ↔ v ∈ Tset wfun t) := by
    intro v hv
    constructor
    · intro h
      exact (mem_Tset_succ.mp h).resolve_right fun hc => hv (hvalW hc)
    · intro h
      exact mem_Tset_succ.mpr (Or.inl h)
  have hnb_ne : ∀ {v : Fin N}, v ≠ u → v ≠ W →
      (delStar H₀ u (Tset wfun (t + 1))).neighborSet v = Ht.neighborSet v := by
    intro v hvu hvW
    rw [hHt, delStar_neighborSet_ne H₀ u _ hvu, delStar_neighborSet_ne H₀ u _ hvu,
      if_congr (hTT hvW) rfl rfl]
  have hnbW : (delStar H₀ u (Tset wfun (t + 1))).neighborSet W =
      H₀.neighborSet W \ {u} := by
    rw [delStar_neighborSet_ne H₀ u _ hWu, if_pos hWTsucc]
  have hnbWt : Ht.neighborSet W = H₀.neighborSet W := by
    rw [hHt, delStar_neighborSet_ne H₀ u _ hWu, if_neg hWT]
  have huWmem : u ∈ H₀.neighborSet W := (hwadj t ht).symm
  have hdegW : gv = (H₀.neighborSet W).ncard := by
    rw [hgv, ← hWval, hdeg W hWdead hWex, hnbWt]
  have hdegW' : ((delStar H₀ u (Tset wfun (t + 1))).neighborSet W).ncard =
      gv - 1 := by
    rw [hnbW, Set.ncard_diff_singleton_of_mem huWmem, ← hdegW]
  -- the refined adjacency, forward and backward
  have hadj_succ : ∀ {v x : Fin N},
      (delStar H₀ u (Tset wfun (t + 1))).Adj v x ↔
        Ht.Adj v x ∧ ¬(v = u ∧ (x : ℕ) = wfun t) ∧ ¬(x = u ∧ (v : ℕ) = wfun t) :=
    fun {v x} => delStar_Tset_succ_adj
  -- ===== the shared toolkit =====
  have hexOf : ∀ {v : Fin N}, v ≠ u → v ∉ ({u} : Set (Fin N)) :=
    fun {v} h hc => h (Set.mem_singleton_iff.mp hc)
  have hneOf : ∀ {v : Fin N}, v ∉ ({u} : Set (Fin N)) → v ≠ u :=
    fun {v} hv hc => hv (Set.mem_singleton_iff.mpr hc)
  have hwdead : ∀ s (hs : s < dgu), (⟨wfun s, hwN s hs⟩ : Fin N) ∉ dead :=
    fun s hs => ((deleteVerts_adj).mp (hwadj s hs)).2.2
  have hltW : ∀ {c : ℕ}, c < gv → c < (G.neighborSet W).ncard :=
    fun {c} h => lt_of_lt_of_le h hgleG
  have hDGleU : ∀ (x : Fin N), x ∉ dead → ∀ {c : ℕ}, c < DG ((x : ℕ)) →
      c < (G.neighborSet x).ncard := by
    intro x hx c hc
    by_cases hxu : x = u
    · subst hxu
      rw [hdgu] at hc
      exact lt_of_lt_of_le hc hdguG
    · exact lt_of_lt_of_le hc (hDGle x hx hxu)
  have htG : t < (G.neighborSet u).ncard := lt_of_lt_of_le ht hdguG
  -- the pointwise evaluators of the update functions
  have hAJe : ∀ c, AJ' c = if c = pv then AJ lastv else AJ c := fun _ => rfl
  have hMTe : ∀ c, MT' c = if c = ysv then pv else if c = pv then ysv else MT c :=
    fun _ => rfl
  have hDGe : ∀ c, DG' c = if c = wfun t then gv - 1 else DG c := fun _ => rfl
  -- the two clause families that do not depend on the mate-slot split
  have hDEAD : ∀ v : Fin N, v ∈ dead → DG' ((v : ℕ)) = 0 := by
    intro v hv
    rw [hDGe, if_neg fun hc => hWdead (hvalW hc ▸ hv)]
    exact hdead v hv
  have hDEG : ∀ v : Fin N, v ∉ dead → v ∉ ({u} : Set (Fin N)) →
      DG' ((v : ℕ)) =
        ((delStar H₀ u (Tset wfun (t + 1))).neighborSet v).ncard := by
    intro v hv hvex
    rw [hDGe]
    by_cases hvW : v = W
    · rw [if_pos (by rw [hvW]), hvW, hdegW']
    · rw [if_neg fun hc => hvW (hvalW hc), hnb_ne (hneOf hvex) hvW]
      exact hdeg v hv hvex
  -- ===== the two main deliverables, split on whether the mate slot is
  -- the last live slot of the target row =====
  have hmain :
      PAdjF (delStar H₀ u (Tset wfun (t + 1))) dead {u} offF AJ' MT' DG' ∧
      URowF u offF wfun AJ' MT' DG' dgu (t + 1) := by
    by_cases hsp : s' = gv - 1
    -- ========== CASE A: the mate slot is the last slot ==========
    · have hpl : pv = lastv := by rw [hpv, hlastv, hsp]
      have hyuv : (y : ℕ) = (u : ℕ) := by rw [← hAJlast, ← hpl, hAJp]
      have hysv_ut : ysv = offF ((u : ℕ)) + s'' := by rw [hysv, hyuv]
      have hs''t : s'' = t := by
        have h2 : MT pv = ysv := by rw [hpl]; exact hMTlast
        rw [hysv_ut] at h2
        rw [hMTp] at h2
        omega
      have hysv_t : ysv = offF ((u : ℕ)) + t := by rw [hysv_ut, hs''t]
      -- the AJ update is the identity, the pv-branch of MT is idle
      have hAJid : ∀ c, AJ' c = AJ c := by
        intro c
        rw [hAJe c]
        by_cases hc : c = pv
        · rw [if_pos hc, hc, hpl]
        · rw [if_neg hc]
      have hMTid : ∀ c, MT' c = if c = ysv then pv else MT c := by
        intro c
        rw [hMTe c]
        by_cases hc : c = ysv
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc]
          by_cases hcp : c = pv
          · rw [if_pos hcp, hcp, hpl, hMTlast]
          · rw [if_neg hcp]
      refine ⟨⟨hDEAD, hDEG, ?_, ?_⟩, ?_⟩
      · -- soundness
        intro v hv hvex s hs
        rw [hDGe] at hs
        by_cases hvW : v = W
        · subst hvW
          rw [if_pos hWval] at hs
          rw [hWval]
          obtain ⟨x, hadjx, hAJx, s₂, hs₂, hMTx, hAJb, hMTb⟩ :=
            hsound W hWdead hWex s (by rw [hWval, ← hgv]; omega)
          rw [hWval] at hAJx hMTx hAJb hMTb
          have hxdead : x ∉ dead := hHtdead hadjx
          have hxW : x ≠ W := (SimpleGraph.Adj.ne hadjx).symm
          have hxu : x ≠ u := by
            intro hc
            have heq : AJ (offF (wfun t) + s) = AJ (offF (wfun t) + s') := by
              rw [hAJx, ← hpv, hAJp, hc]
            have := hP.rowInj hWdead hWex
              (show s < DG ((W : ℕ)) by rw [hWval, ← hgv]; omega)
              (show s' < DG ((W : ℕ)) by rw [hWval, ← hgv]; omega)
              (by rw [hWval]; exact heq)
            omega
          refine ⟨x, ?_, ?_, s₂, ?_, ?_, ?_, ?_⟩
          · exact delStar_Tset_succ_adj.mpr ⟨hadjx,
              fun hc => hWu hc.1, fun hc => hxu hc.1⟩
          · rw [hAJid]
            exact hAJx
          · rw [hDGe, if_neg fun hc => hxW (hvalW hc)]
            exact hs₂
          · rw [hMTid, if_neg (show offF (wfun t) + s ≠ ysv from by
              rw [hysv_t]
              exact hrne W u hWu (hltW (by omega)) htG)]
            exact hMTx
          · rw [hAJid]
            exact hAJb
          · rw [hMTid, if_neg (show offF ((x : ℕ)) + s₂ ≠ ysv from by
              rw [hysv_t]
              exact hrne x u hxu (hDGleU x hxdead hs₂) htG)]
            exact hMTb
        · rw [if_neg fun hc => hvW (hvalW hc)] at hs
          obtain ⟨x, hadjx, hAJx, s₂, hs₂, hMTx, hAJb, hMTb⟩ :=
            hsound v hv hvex s hs
          have hxdead : x ∉ dead := hHtdead hadjx
          have hvu : v ≠ u := hneOf hvex
          have hvG : s < (G.neighborSet v).ncard :=
            lt_of_lt_of_le hs (hDGle v hv hvu)
          refine ⟨x, ?_, ?_, s₂, ?_, ?_, ?_, ?_⟩
          · exact delStar_Tset_succ_adj.mpr ⟨hadjx,
              fun hc => hvu hc.1, fun hc => hvW (hvalW hc.2)⟩
          · rw [hAJid]
            exact hAJx
          · rw [hDGe]
            by_cases hxWv : (x : ℕ) = wfun t
            · rw [if_pos hxWv]
              have hs₂g : s₂ < gv := by rw [hgv, ← hxWv]; exact hs₂
              have hne : s₂ ≠ gv - 1 := by
                intro hc
                have hcell : offF ((x : ℕ)) + s₂ = lastv := by
                  rw [hxWv, hlastv, hc]
                rw [hcell, hAJlast] at hAJb
                exact hvu (Fin.ext ((hAJb.symm.trans hyuv)))
              omega
            · rw [if_neg hxWv]
              exact hs₂
          · rw [hMTid, if_neg (show offF ((v : ℕ)) + s ≠ ysv from by
              rw [hysv_t]
              exact hrne v u hvu hvG htG)]
            exact hMTx
          · rw [hAJid]
            exact hAJb
          · rw [hMTid, if_neg (show offF ((x : ℕ)) + s₂ ≠ ysv from by
              rw [hysv_t]
              by_cases hxu : x = u
              · subst hxu
                intro hc
                have hst : s₂ = t := by omega
                rw [hst, hAJut] at hAJb
                exact hvW (hvalW hAJb.symm)
              · exact hrne x u hxu (hDGleU x hxdead hs₂) htG)]
            exact hMTb
      · -- completeness
        intro v hv hvex x hadj'
        have hadjt : Ht.Adj v x := (delStar_Tset_succ_adj.mp hadj').1
        obtain ⟨s, hslt, hAJx⟩ := hcomp v hv hvex x hadjt
        rw [hDGe]
        by_cases hvW : v = W
        · subst hvW
          rw [if_pos hWval]
          rw [hWval] at hAJx ⊢
          have hxu : x ≠ u := by
            intro hc
            exact (delStar_Tset_succ_adj.mp hadj').2.2 ⟨hc, hWval⟩
          have hslt' : s < gv := by rw [hgv, ← hWval]; exact hslt
          have hne : s ≠ gv - 1 := by
            intro hc
            have hcell : offF (wfun t) + s = pv := by
              rw [hc, hpv, hsp]
            rw [hcell, hAJp] at hAJx
            exact hxu (Fin.ext hAJx.symm)
          refine ⟨s, by omega, ?_⟩
          rw [hAJid]
          exact hAJx
        · rw [if_neg fun hc => hvW (hvalW hc)]
          refine ⟨s, hslt, ?_⟩
          rw [hAJid]
          exact hAJx
      · -- the u-row clauses, advanced
        intro s hts hsd
        obtain ⟨hAJus, s₄, hs₄, hMTus, hAJm, hMTm⟩ := hU s (by omega) hsd
        have hsW : wfun s ≠ wfun t := fun h => by
          have := hwinj s hsd t ht h
          omega
        have hsu : u ≠ (⟨wfun s, hwN s hsd⟩ : Fin N) := (hwadj s hsd).ne
        have hs₄G : s₄ < (G.neighborSet (⟨wfun s, hwN s hsd⟩ : Fin N)).ncard :=
          lt_of_lt_of_le hs₄ (hDGle _ (hwdead s hsd) hsu.symm)
        refine ⟨?_, s₄, ?_, ?_, ?_, ?_⟩
        · rw [hAJid]
          exact hAJus
        · rw [hDGe, if_neg hsW]
          exact hs₄
        · rw [hMTid, if_neg (show offF ((u : ℕ)) + s ≠ ysv from by
            rw [hysv_t]
            omega)]
          exact hMTus
        · rw [hAJid]
          exact hAJm
        · rw [hMTid, if_neg (show offF (wfun s) + s₄ ≠ ysv from by
            rw [hysv_t]
            exact hrne ⟨wfun s, hwN s hsd⟩ u hsu.symm hs₄G htG)]
          exact hMTm
    -- ========== CASE B: a genuine swap ==========
    · have hpl : pv ≠ lastv := by
        rw [hpv, hlastv]
        omega
      have hyu : y ≠ u := by
        intro hc
        have heq : AJ lastv = AJ pv := by rw [hAJlast, hAJp, hc]
        have := hP.rowInj hWdead hWex
          (show gv - 1 < DG ((W : ℕ)) by rw [hWval, ← hgv]; omega)
          (show s' < DG ((W : ℕ)) by rw [hWval, ← hgv]; omega)
          (by exact heq)
        exact hsp this.symm
      have hyuv : (y : ℕ) ≠ (u : ℕ) := fun h => hyu (Fin.ext h)
      refine ⟨⟨hDEAD, hDEG, ?_, ?_⟩, ?_⟩
      · -- soundness
        intro v hv hvex s hs
        rw [hDGe] at hs
        by_cases hvW : v = W
        · subst hvW
          rw [if_pos hWval] at hs
          rw [hWval]
          by_cases hss : s = s'
          · -- the vacated slot now holds the moved copy
            subst hss
            refine ⟨y, ?_, ?_, s'', ?_, ?_, ?_, ?_⟩
            · exact delStar_Tset_succ_adj.mpr ⟨hHtWy,
                fun hc => hWu hc.1, fun hc => hyu hc.1⟩
            · rw [hAJe, if_pos (show offF (wfun t) + s = pv from by
                rw [hpv])]
              exact hAJlast
            · rw [hDGe, if_neg fun hc => hyW (hvalW hc)]
              exact hs''lt
            · rw [hMTe,
                if_neg (show offF (wfun t) + s ≠ ysv from
                  fun hc => hpvne_ysv (hpv.trans hc)),
                if_pos (show offF (wfun t) + s = pv from by rw [hpv])]
            · rw [hAJe, if_neg (show offF ((y : ℕ)) + s'' ≠ pv from
                fun hc => hpvne_ysv (hysv.trans hc).symm)]
              exact hAJys
            · rw [hMTe, if_pos (show offF ((y : ℕ)) + s'' = ysv from hysv.symm)]
          · -- an untouched slot of the target row
            obtain ⟨x, hadjx, hAJx, s₂, hs₂, hMTx, hAJb, hMTb⟩ :=
              hsound W hWdead hWex s (by rw [hWval, ← hgv]; omega)
            rw [hWval] at hAJx hMTx hAJb hMTb
            have hxdead : x ∉ dead := hHtdead hadjx
            have hxW : x ≠ W := (SimpleGraph.Adj.ne hadjx).symm
            have hxu : x ≠ u := by
              intro hc
              apply hss
              refine hP.rowInj hWdead hWex
                (show s < DG ((W : ℕ)) by rw [hWval, ← hgv]; omega)
                (show s' < DG ((W : ℕ)) by rw [hWval, ← hgv]; omega) ?_
              rw [hWval, hAJx, ← hpv, hAJp, hc]
            have hxy : x ≠ y := by
              intro hc
              have heq : AJ (offF (wfun t) + s) = AJ (offF (wfun t) + (gv - 1)) := by
                rw [hAJx, hc, ← hlastv, hAJlast]
              have := hP.rowInj hWdead hWex
                (show s < DG ((W : ℕ)) by rw [hWval, ← hgv]; omega)
                (show gv - 1 < DG ((W : ℕ)) by rw [hWval, ← hgv]; omega)
                (by rw [hWval]; exact heq)
              omega
            refine ⟨x, ?_, ?_, s₂, ?_, ?_, ?_, ?_⟩
            · exact delStar_Tset_succ_adj.mpr ⟨hadjx,
                fun hc => hWu hc.1, fun hc => hxu hc.1⟩
            · rw [hAJe, if_neg (show offF (wfun t) + s ≠ pv from by
                rw [hpv]; omega)]
              exact hAJx
            · rw [hDGe, if_neg fun hc => hxW (hvalW hc)]
              exact hs₂
            · rw [hMTe,
                if_neg (show offF (wfun t) + s ≠ ysv from by
                  rw [hysv]
                  exact hrne W y hyW.symm (hltW (by omega)) hs''G),
                if_neg (show offF (wfun t) + s ≠ pv from by rw [hpv]; omega)]
              exact hMTx
            · rw [hAJe, if_neg (show offF ((x : ℕ)) + s₂ ≠ pv from by
                rw [hpv, ← hWval]
                exact hrne x W hxW (hDGleU x hxdead hs₂) hs'G)]
              exact hAJb
            · rw [hMTe,
                if_neg (show offF ((x : ℕ)) + s₂ ≠ ysv from by
                  rw [hysv]
                  exact hrne x y hxy (hDGleU x hxdead hs₂) hs''G),
                if_neg (show offF ((x : ℕ)) + s₂ ≠ pv from by
                  rw [hpv, ← hWval]
                  exact hrne x W hxW (hDGleU x hxdead hs₂) hs'G)]
              exact hMTb
        · -- a row away from the target
          rw [if_neg fun hc => hvW (hvalW hc)] at hs
          obtain ⟨x, hadjx, hAJx, s₂, hs₂, hMTx, hAJb, hMTb⟩ :=
            hsound v hv hvex s hs
          have hxdead : x ∉ dead := hHtdead hadjx
          have hvu : v ≠ u := hneOf hvex
          have hvG : s < (G.neighborSet v).ncard :=
            lt_of_lt_of_le hs (hDGle v hv hvu)
          by_cases hmoved : (v : ℕ) = (y : ℕ) ∧ s = s''
          · -- the partner of the moved copy: its mate follows the move
            obtain ⟨hvy, hss''⟩ := hmoved
            have hcell : offF ((v : ℕ)) + s = ysv := by
              rw [hysv, hvy, hss'']
            have hxWv : (x : ℕ) = wfun t := by
              have h1 : AJ ysv = (x : ℕ) := by rw [← hcell]; exact hAJx
              rw [hAJys] at h1
              rw [← h1, hWval]
            refine ⟨x, ?_, ?_, s', ?_, ?_, ?_, ?_⟩
            · exact delStar_Tset_succ_adj.mpr ⟨hadjx,
                fun hc => hvu hc.1, fun hc => hvW (hvalW hc.2)⟩
            · rw [hAJe, if_neg (show offF ((v : ℕ)) + s ≠ pv from by
                rw [hcell]
                exact fun hc => hpvne_ysv hc.symm)]
              exact hAJx
            · rw [hDGe, hxWv, if_pos rfl]
              have : s' < gv := hs'g
              omega
            · rw [hMTe, if_pos hcell]
              rw [hxWv, hpv]
            · rw [hxWv, hAJe, if_pos (show offF (wfun t) + s' = pv from hpv.symm)]
              rw [hAJlast, hvy]
            · rw [hxWv, hMTe,
                if_neg (show offF (wfun t) + s' ≠ ysv from
                  fun hc => hpvne_ysv (hpv.trans hc)),
                if_pos (show offF (wfun t) + s' = pv from hpv.symm)]
              rw [hcell]
          · -- everything about this slot is untouched
            refine ⟨x, ?_, ?_, s₂, ?_, ?_, ?_, ?_⟩
            · exact delStar_Tset_succ_adj.mpr ⟨hadjx,
                fun hc => hvu hc.1, fun hc => hvW (hvalW hc.2)⟩
            · rw [hAJe, if_neg (show offF ((v : ℕ)) + s ≠ pv from by
                rw [hpv, ← hWval]
                exact hrne v W hvW hvG hs'G)]
              exact hAJx
            · rw [hDGe]
              by_cases hxWv : (x : ℕ) = wfun t
              · rw [if_pos hxWv]
                have hs₂g : s₂ < gv := by rw [hgv, ← hxWv]; exact hs₂
                have hne : s₂ ≠ gv - 1 := by
                  intro hc
                  have hcell : offF ((x : ℕ)) + s₂ = lastv := by
                    rw [hxWv, hlastv, hc]
                  rw [hcell, hAJlast] at hAJb
                  rw [hcell, hMTlast] at hMTb
                  refine hmoved ⟨hAJb.symm, ?_⟩
                  rw [hysv] at hMTb
                  rw [← hAJb] at hMTb
                  omega
                omega
              · rw [if_neg hxWv]
                exact hs₂
            · rw [hMTe,
                if_neg (show offF ((v : ℕ)) + s ≠ ysv from by
                  by_cases hvy : (v : ℕ) = (y : ℕ)
                  · rw [hysv, hvy]
                    intro hc
                    exact hmoved ⟨hvy, by omega⟩
                  · rw [hysv]
                    exact hrne v y (fun h => hvy (congrArg Fin.val h)) hvG hs''G),
                if_neg (show offF ((v : ℕ)) + s ≠ pv from by
                  rw [hpv, ← hWval]
                  exact hrne v W hvW hvG hs'G)]
              exact hMTx
            · rw [hAJe, if_neg (show offF ((x : ℕ)) + s₂ ≠ pv from by
                by_cases hxWv : (x : ℕ) = wfun t
                · rw [hxWv, hpv]
                  intro hc
                  have hs₂s : s₂ = s' := by omega
                  have hcell : offF ((x : ℕ)) + s₂ = pv := by
                    rw [hxWv, hpv, hs₂s]
                  rw [hcell, hAJp] at hAJb
                  exact hvu (Fin.ext hAJb.symm)
                · rw [hpv, ← hWval]
                  exact hrne x W (fun h => hxWv (by rw [h]))
                    (hDGleU x hxdead hs₂) hs'G)]
              exact hAJb
            · rw [hMTe,
                if_neg (show offF ((x : ℕ)) + s₂ ≠ ysv from by
                  by_cases hxyv : (x : ℕ) = (y : ℕ)
                  · rw [hysv, hxyv]
                    intro hc
                    have hs₂s : s₂ = s'' := by omega
                    have hcell : offF ((x : ℕ)) + s₂ = ysv := by
                      rw [hysv, hxyv, hs₂s]
                    rw [hcell, hAJys] at hAJb
                    exact hvW (hvalW (by rw [← hAJb]))
                  · rw [hysv]
                    exact hrne x y (fun h => hxyv (congrArg Fin.val h))
                      (hDGleU x hxdead hs₂) hs''G),
                if_neg (show offF ((x : ℕ)) + s₂ ≠ pv from by
                  by_cases hxWv : (x : ℕ) = wfun t
                  · rw [hxWv, hpv]
                    intro hc
                    have hs₂s : s₂ = s' := by omega
                    have hcell : offF ((x : ℕ)) + s₂ = pv := by
                      rw [hxWv, hpv, hs₂s]
                    rw [hcell, hAJp] at hAJb
                    exact hvu (Fin.ext hAJb.symm)
                  · rw [hpv, ← hWval]
                    exact hrne x W (fun h => hxWv (by rw [h]))
                      (hDGleU x hxdead hs₂) hs'G)]
              exact hMTb
      · -- completeness
        intro v hv hvex x hadj'
        have hadjt : Ht.Adj v x := (delStar_Tset_succ_adj.mp hadj').1
        obtain ⟨s, hslt, hAJx⟩ := hcomp v hv hvex x hadjt
        rw [hDGe]
        by_cases hvW : v = W
        · subst hvW
          rw [if_pos hWval]
          rw [hWval] at hAJx ⊢
          have hxu : x ≠ u := by
            intro hc
            exact (delStar_Tset_succ_adj.mp hadj').2.2 ⟨hc, hWval⟩
          have hslt' : s < gv := by rw [hgv, ← hWval]; exact hslt
          have hss' : s ≠ s' := by
            intro hc
            have hcell : offF (wfun t) + s = pv := by rw [hc, hpv]
            rw [hcell, hAJp] at hAJx
            exact hxu (Fin.ext hAJx.symm)
          by_cases hslast : s = gv - 1
          · -- the copy moved into the vacated slot
            refine ⟨s', by omega, ?_⟩
            rw [hAJe, if_pos (show offF (wfun t) + s' = pv from hpv.symm)]
            rw [hslast] at hAJx
            exact hAJx
          · refine ⟨s, by omega, ?_⟩
            rw [hAJe, if_neg (show offF (wfun t) + s ≠ pv from by
              rw [hpv]; omega)]
            exact hAJx
        · rw [if_neg fun hc => hvW (hvalW hc)]
          have hvu : v ≠ u := hneOf hvex
          have hvG : s < (G.neighborSet v).ncard :=
            lt_of_lt_of_le hslt (hDGle v hv hvu)
          refine ⟨s, hslt, ?_⟩
          rw [hAJe, if_neg (show offF ((v : ℕ)) + s ≠ pv from by
            rw [hpv, ← hWval]
            exact hrne v W hvW hvG hs'G)]
          exact hAJx
      · -- the u-row clauses, advanced
        intro s hts hsd
        obtain ⟨hAJus, s₄, hs₄, hMTus, hAJm, hMTm⟩ := hU s (by omega) hsd
        have hsW : wfun s ≠ wfun t := fun h => by
          have := hwinj s hsd t ht h
          omega
        have hsu : u ≠ (⟨wfun s, hwN s hsd⟩ : Fin N) := (hwadj s hsd).ne
        have hs₄G : s₄ < (G.neighborSet (⟨wfun s, hwN s hsd⟩ : Fin N)).ncard :=
          lt_of_lt_of_le hs₄ (hDGle _ (hwdead s hsd) hsu.symm)
        have hsdgu : s < (G.neighborSet u).ncard := lt_of_lt_of_le hsd hdguG
        refine ⟨?_, s₄, ?_, ?_, ?_, ?_⟩
        · rw [hAJe, if_neg (show offF ((u : ℕ)) + s ≠ pv from by
            rw [hpv, ← hWval]
            exact hrne u W huW hsdgu hs'G)]
          exact hAJus
        · rw [hDGe, if_neg hsW]
          exact hs₄
        · rw [hMTe,
            if_neg (show offF ((u : ℕ)) + s ≠ ysv from by
              rw [hysv]
              exact hrne u y hyu.symm hsdgu hs''G),
            if_neg (show offF ((u : ℕ)) + s ≠ pv from by
              rw [hpv, ← hWval]
              exact hrne u W huW hsdgu hs'G)]
          exact hMTus
        · rw [hAJe, if_neg (show offF (wfun s) + s₄ ≠ pv from by
            rw [hpv, ← hWval]
            exact hrne ⟨wfun s, hwN s hsd⟩ W
              (fun h => hsW (congrArg Fin.val h))
              hs₄G hs'G)]
          exact hAJm
        · rw [hMTe,
            if_neg (show offF (wfun s) + s₄ ≠ ysv from by
              by_cases hsy : wfun s = (y : ℕ)
              · rw [hysv, hsy]
                intro hc
                have hs₄s : s₄ = s'' := by omega
                have hcell : offF (wfun s) + s₄ = ysv := by
                  rw [hysv, hsy, hs₄s]
                rw [hcell, hAJys] at hAJm
                exact hne_ut (by rw [← hAJm])
              · rw [hysv]
                exact hrne ⟨wfun s, hwN s hsd⟩ y
                  (fun h => hsy (congrArg Fin.val h)) hs₄G hs''G),
            if_neg (show offF (wfun s) + s₄ ≠ pv from by
              rw [hpv, ← hWval]
              exact hrne ⟨wfun s, hwN s hsd⟩ W
                (fun h => hsW (congrArg Fin.val h))
                hs₄G hs'G)]
          exact hMTm
  exact ⟨pv, gv, AJ lastv, ysv, hMTut, hAJut, rfl, hg1, hgN, rfl, hMTlast,
    hpvlt, hysvlt, hlastlt', hyvN, hne_ut, hwN t ht, hpvne_ysv, hpv_lo,
    hmain.1, hmain.2⟩

end DeleteTurn

/-! ## §6 The sorted enumeration's counting identities

`ClusterCsr` rows are `restrictEmb`'s ascending enumeration.  The
placement pass fills row `u` in ascending member order, so its
invariant speaks of *how many members lie below the current value* —
`cntBelow` — and needs: position `a` of the enumeration is below `z`
iff `a < cntBelow z`, and a member `z`'s own position is exactly
`cntBelow z`. -/

section RestrictOrder

variable {n : ℕ}

/-- The number of members of `S` with value below `z`. -/
noncomputable def cntBelow (S : Set (Fin n)) (z : ℕ) : ℕ :=
  (S ∩ {w : Fin n | (w : ℕ) < z}).ncard

theorem cntBelow_le (S : Set (Fin n)) (z : ℕ) : cntBelow S z ≤ S.ncard :=
  Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)

theorem cntBelow_of_ge (S : Set (Fin n)) {z : ℕ} (hz : n ≤ z) :
    cntBelow S z = S.ncard := by
  rw [cntBelow]
  congr 1
  ext w
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_iff_left_iff_imp]
  intro _
  exact lt_of_lt_of_le w.isLt hz

open Classical in
/-- One more value: the count grows by the new member, if it is one. -/
theorem cntBelow_succ (S : Set (Fin n)) (z : ℕ) (hz : z < n) :
    cntBelow S (z + 1) =
      cntBelow S z + (if (⟨z, hz⟩ : Fin n) ∈ S then 1 else 0) := by
  classical
  by_cases hmem : (⟨z, hz⟩ : Fin n) ∈ S
  · rw [if_pos hmem]
    have hset : S ∩ {w : Fin n | (w : ℕ) < z + 1} =
        insert (⟨z, hz⟩ : Fin n) (S ∩ {w : Fin n | (w : ℕ) < z}) := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_insert_iff]
      constructor
      · rintro ⟨hwS, hwz⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hwz with h | h
        · exact Or.inr ⟨hwS, h⟩
        · exact Or.inl (Fin.ext h)
      · rintro (rfl | ⟨hwS, hwz⟩)
        · exact ⟨hmem, Nat.lt_succ_self z⟩
        · exact ⟨hwS, by omega⟩
    have hnot : (⟨z, hz⟩ : Fin n) ∉ S ∩ {w : Fin n | (w : ℕ) < z} := by
      rintro ⟨-, hc⟩
      have hc' : z < z := hc
      omega
    rw [cntBelow, hset, Set.ncard_insert_of_notMem hnot (Set.toFinite _), cntBelow]
  · rw [if_neg hmem]
    have hset : S ∩ {w : Fin n | (w : ℕ) < z + 1} =
        S ∩ {w : Fin n | (w : ℕ) < z} := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hwS, hwz⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hwz with h | h
        · exact ⟨hwS, h⟩
        · exact absurd hwS (by rw [show w = ⟨z, hz⟩ from Fin.ext h]; exact hmem)
      · rintro ⟨hwS, hwz⟩
        exact ⟨hwS, by omega⟩
    rw [cntBelow, hset, cntBelow]
    omega

/-- **Position below a value**: the `a`-th enumerated member has value
below `z` exactly when `a` is below the count of members below `z`. -/
theorem restrictEmb_val_lt_iff (S : Set (Fin n)) (z : ℕ) (a : Fin S.ncard) :
    ((Impl.restrictEmb S a : Fin n) : ℕ) < z ↔ (a : ℕ) < cntBelow S z := by
  classical
  set A : Finset (Fin S.ncard) :=
    Finset.univ.filter (fun a' => ((Impl.restrictEmb S a' : Fin n) : ℕ) < z)
    with hA
  have hmono : StrictMono (fun a' => (Impl.restrictEmb S a' : Fin n)) :=
    fun x y hxy => Driver.setEquiv_coe_strictMono S hxy
  have hmonoV : ∀ {x y : Fin S.ncard}, x < y →
      ((Impl.restrictEmb S x : Fin n) : ℕ) < ((Impl.restrictEmb S y : Fin n) : ℕ) := by
    intro x y hxy
    have h := Driver.setEquiv_coe_strictMono S hxy
    rw [Fin.lt_def] at h
    exact h
  have hinj : Function.Injective (fun a' => (Impl.restrictEmb S a' : Fin n)) :=
    hmono.injective
  have himg : A.image (fun a' => (Impl.restrictEmb S a' : Fin n)) =
      (Set.toFinite (S ∩ {w : Fin n | (w : ℕ) < z})).toFinset := by
    ext x
    simp only [Finset.mem_image, hA, Finset.mem_filter, Finset.mem_univ,
      true_and, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a', ha', rfl⟩
      exact ⟨Impl.restrictEmb_mem S a', ha'⟩
    · rintro ⟨hxS, hxz⟩
      refine ⟨(Driver.setEquiv S).symm ⟨x, hxS⟩, ?_, ?_⟩
      · rw [show (Impl.restrictEmb S ((Driver.setEquiv S).symm ⟨x, hxS⟩) : Fin n)
            = x from by rw [Impl.restrictEmb_apply, Equiv.apply_symm_apply]]
        exact hxz
      · rw [Impl.restrictEmb_apply, Equiv.apply_symm_apply]
  have hcard : A.card = cntBelow S z := by
    rw [← Finset.card_image_of_injective A hinj, himg, cntBelow,
      ← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  have hdc : ∀ a' ∈ A, ∀ b, b ≤ a' → b ∈ A := by
    intro a' ha' b hb
    rw [hA, Finset.mem_filter] at ha' ⊢
    refine ⟨Finset.mem_univ b, ?_⟩
    rcases eq_or_lt_of_le hb with rfl | hlt
    · exact ha'.2
    · have := hmonoV hlt
      omega
  rw [← hcard]
  constructor
  · intro h
    have hsub : Finset.Iic a ⊆ A := fun b hb =>
      hdc a (by rw [hA, Finset.mem_filter]; exact ⟨Finset.mem_univ a, h⟩) b
        (Finset.mem_Iic.mp hb)
    have hle := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hle
    omega
  · intro h
    by_contra hc
    have hsub : A ⊆ Finset.Iio a := by
      intro b hb
      rw [Finset.mem_Iio]
      by_contra hba
      push_neg at hba
      refine hc ?_
      have hmem := hdc b hb a hba
      rw [hA, Finset.mem_filter] at hmem
      exact hmem.2
    have hle := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hle
    omega

/-- **A member's own position** is the count of members below it. -/
theorem restrictEmb_cntBelow_self (S : Set (Fin n)) {z : Fin n} (hz : z ∈ S) :
    ∃ h : cntBelow S (z : ℕ) < S.ncard,
      (Impl.restrictEmb S ⟨cntBelow S (z : ℕ), h⟩ : Fin n) = z := by
  classical
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, (Impl.restrictEmb S a₀ : Fin n) = z :=
    ⟨(Driver.setEquiv S).symm ⟨z, hz⟩, by
      rw [Impl.restrictEmb_apply, Equiv.apply_symm_apply]⟩
  have hmonoV : ∀ {x y : Fin S.ncard}, x < y →
      ((Impl.restrictEmb S x : Fin n) : ℕ) < ((Impl.restrictEmb S y : Fin n) : ℕ) := by
    intro x y hxy
    have h := Driver.setEquiv_coe_strictMono S hxy
    rw [Fin.lt_def] at h
    exact h
  have hval : (a₀ : ℕ) = cntBelow S (z : ℕ) := by
    have h1 : ¬ ((Impl.restrictEmb S a₀ : Fin n) : ℕ) < (z : ℕ) := by
      rw [ha₀]
      omega
    rw [restrictEmb_val_lt_iff] at h1
    push_neg at h1
    rcases eq_or_lt_of_le h1 with h | h
    · exact h.symm
    · exfalso
      have hltFin : (⟨cntBelow S (z : ℕ), lt_trans h a₀.isLt⟩ : Fin S.ncard)
          < a₀ := by
        rw [Fin.lt_def]
        exact h
      have h2 := hmonoV hltFin
      rw [ha₀] at h2
      have h3 := (restrictEmb_val_lt_iff S (z : ℕ)
        ⟨cntBelow S (z : ℕ), lt_trans h a₀.isLt⟩).mp h2
      simp only at h3
      omega
  refine ⟨hval ▸ a₀.isLt, ?_⟩
  have harg : (⟨cntBelow S (z : ℕ), hval ▸ a₀.isLt⟩ : Fin S.ncard) = a₀ :=
    Fin.ext hval.symm
  rw [harg, ha₀]

/-- Counting a vertex set through a `ℕ`-predicate — the bridge between
the machine's counters and `ncard`. -/
theorem ncard_eq_filter_card {N : ℕ} (X : Set (Fin N)) (P : ℕ → Prop)
    [DecidablePred P] (h : ∀ z (hz : z < N), (⟨z, hz⟩ : Fin N) ∈ X ↔ P z) :
    X.ncard = ((Finset.range N).filter P).card := by
  classical
  have himg : Fin.val '' X = ↑((Finset.range N).filter P) := by
    ext x
    simp only [Set.mem_image, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_range]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.isLt, (h (w : ℕ) w.isLt).mp ?_⟩
      rwa [Fin.eta]
    · rintro ⟨hx, hP⟩
      exact ⟨⟨x, hx⟩, (h x hx).mpr hP, rfl⟩
  rw [← Set.ncard_image_of_injective X Fin.val_injective, himg,
    Set.ncard_coe_finset]

end RestrictOrder

/-! ## §7 The deletion pass, at the machine -/

/-- A `getD` fact is a `getElem?` fact inside the allocation. -/
private theorem getElem?_of_getD {l : List ℕ} {k v : ℕ} (hk : k < l.length)
    (hv : l.getD k 0 = v) : l[k]? = some v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
    Option.getD_some] at hv
  rw [List.getElem?_eq_getElem hk]
  exact congrArg some hv

section DelLoop

variable {B N : ℕ} {G : SimpleGraph (Fin N)} {dead : Set (Fin N)} {u : Fin N}
  {ao aj dg mt : String} {offF wfun : ℕ → ℕ} {dgu : ℕ}

/-- The deletion loop's state at the counter's value: the cached
scalars, the offset head, the suspended region at the processed star,
and the `u`-row clauses. -/
def DelInv (ao aj dg mt : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (dead : Set (Fin N)) (u : Fin N) (offF wfun : ℕ → ℕ) (dgu : ℕ)
    (σ : Env) : Prop :=
  σ.vars "pl.a" = offF (u : ℕ) ∧
  σ.vars "pl.g" = dgu ∧
  σ.vars "pl.u" = (u : ℕ) ∧
  σ.vars "pl.j" ≤ dgu ∧
  offF 0 = 0 ∧
  (∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) ∧
  N + 1 ≤ (σ.arrs ao).length ∧
  (∀ i, i ≤ N → (σ.arrs ao).getD i 0 = offF i) ∧
  offF N ≤ (σ.arrs aj).length ∧
  offF N ≤ (σ.arrs mt).length ∧
  N ≤ (σ.arrs dg).length ∧
  (σ.arrs dg).getD (u : ℕ) 0 = dgu ∧
  PAdjF (delStar (deleteVerts G dead) u (Tset wfun (σ.vars "pl.j"))) dead {u}
    offF (fun c => (σ.arrs aj).getD c 0) (fun c => (σ.arrs mt).getD c 0)
    (fun c => (σ.arrs dg).getD c 0) ∧
  URowF u offF wfun (fun c => (σ.arrs aj).getD c 0)
    (fun c => (σ.arrs mt).getD c 0) (fun c => (σ.arrs dg).getD c 0) dgu
    (σ.vars "pl.j")

/-- **One deletion turn, on the machine**: the four reads, the three
repairing stores, the shrink, the counter.  Cost `43`. -/
theorem peelDelTurnB_spec
    (hNB : N < B) (hsq : N * N + N + 4 < B)
    (haj_ao : aj ≠ ao) (hdg_ao : dg ≠ ao) (hmt_ao : mt ≠ ao)
    (haj_dg : aj ≠ dg) (haj_mt : aj ≠ mt) (hdg_mt : dg ≠ mt)
    (hwN : ∀ s, s < dgu → wfun s < N)
    (hwadj : ∀ s, (hs : s < dgu) → (deleteVerts G dead).Adj u ⟨wfun s, hwN s hs⟩)
    (hwinj : ∀ s, s < dgu → ∀ s', s' < dgu → wfun s = wfun s' → s = s')
    (hdguG : dgu ≤ (G.neighborSet u).ncard) :
    Spec B
      (fun σ => DelInv ao aj dg mt G dead u offF wfun dgu σ ∧
        σ.vars "pl.j" < dgu)
      (peelDelTurnB ao aj dg mt)
      (fun σ σ' => DelInv ao aj dg mt G dead u offF wfun dgu σ' ∧
        σ'.vars "pl.j" = σ.vars "pl.j" + 1) 43 := by
  intro σ hσ
  obtain ⟨⟨hva, hvg, hvu, hjle, h0, hstep, haoL, haoV, hajL, hmtL, hdgL, hdguC,
    hPf, hUf⟩, hjlt⟩ := hσ
  set t := σ.vars "pl.j" with htdef
  -- the state-level turn
  obtain ⟨pv, gv, yv, ysv, hMTut, hAJut, hDGw, hg1, hgN, hAJlast, hMTlast,
    hpvlt, hysvlt, hlastlt, hyvN, hne_ut, hwtN, hpvys, hpvlo, hPf', hUf'⟩ :=
    peel_delete_turn hstep hwN hwadj hwinj hdguG hPf hUf hdguC hjlt
  -- numeric room
  have hoffN : offF N ≤ N * N := offF_le_sq h0 hstep
  have hoffu : offF (u : ℕ) ≤ N * N :=
    le_trans (offF_mono hstep N le_rfl (u : ℕ) (le_of_lt u.isLt)) hoffN
  have hoffw : offF (wfun t) ≤ N * N :=
    le_trans (offF_mono hstep N le_rfl (wfun t) (le_of_lt hwtN)) hoffN
  have hcellu : offF (u : ℕ) + t < offF N := by
    have : t < (G.neighborSet u).ncard := lt_of_lt_of_le hjlt hdguG
    exact slot_lt_of_le hstep this
  have htB : t < B := by
    have : t < dgu := hjlt
    omega
  -- ===== the run, step by step =====
  -- 1. the target read
  have hev1 : (Expr.add (.var "pl.a") (.var "pl.j")).evalB B σ
      = some (offF (u : ℕ) + t) := by
    have := evalB_bin (B := B) (op := .add) (e := .var "pl.a") (f := .var "pl.j")
      (σ := σ) (evalB_var (by rw [hva]; omega)) (evalB_var (by rw [← htdef]; omega))
      (by simp only [Bop.apply_add]; rw [hva, ← htdef]; omega)
    rw [hva, ← htdef] at this
    simpa using this
  have hr1 : Run B (.assign "pl.w" (.get aj (.add (.var "pl.a") (.var "pl.j"))))
      σ (σ.setVar "pl.w" (wfun t)) 5 := by
    refine (Run.assign (evalB_get hev1
      (getElem?_of_getD (lt_of_lt_of_le hcellu hajL) hAJut) (by omega))).mono ?_
    simp
  set σ₁ := σ.setVar "pl.w" (wfun t) with hσ₁
  -- 2. the mate read
  have hev2 : (Expr.add (.var "pl.a") (.var "pl.j")).evalB B σ₁
      = some (offF (u : ℕ) + t) := by
    have h1a : σ₁.vars "pl.a" = offF (u : ℕ) := by rw [hσ₁]; simpa using hva
    have h1j : σ₁.vars "pl.j" = t := by rw [hσ₁]; simp [← htdef]
    have := evalB_bin (B := B) (op := .add) (e := .var "pl.a") (f := .var "pl.j")
      (σ := σ₁) (evalB_var (by rw [h1a]; omega)) (evalB_var (by rw [h1j]; omega))
      (by simp only [Bop.apply_add]; rw [h1a, h1j]; omega)
    rw [h1a, h1j] at this
    simpa using this
  have hr2 : Run B (.assign "pl.p" (.get mt (.add (.var "pl.a") (.var "pl.j"))))
      σ₁ (σ₁.setVar "pl.p" pv) 5 := by
    refine (Run.assign (evalB_get hev2
      (getElem?_of_getD (lt_of_lt_of_le hcellu (by rw [hσ₁]; simpa using hmtL))
        (by rw [hσ₁]; simpa using hMTut)) (by omega))).mono ?_
    simp
  set σ₂ := σ₁.setVar "pl.p" pv with hσ₂
  have h2w : σ₂.vars "pl.w" = wfun t := by rw [hσ₂, hσ₁]; simp
  have h2arrs : ∀ b, σ₂.arrs b = σ.arrs b := by intro b; rw [hσ₂, hσ₁]; simp
  -- 3. the last live slot
  have hev3 : (Expr.sub (.add (.get ao (.var "pl.w")) (.get dg (.var "pl.w")))
      (.lit 1)).evalB B σ₂ = some (offF (wfun t) + (gv - 1)) := by
    have hao : (Expr.get ao (.var "pl.w")).evalB B σ₂ = some (offF (wfun t)) := by
      refine evalB_get (evalB_var (by rw [h2w]; omega)) ?_ (by omega)
      rw [h2arrs]
      exact getElem?_of_getD (by omega) (haoV (wfun t) (le_of_lt hwtN))
    have hdg : (Expr.get dg (.var "pl.w")).evalB B σ₂ = some gv := by
      refine evalB_get (evalB_var (by rw [h2w]; omega)) ?_ (by omega)
      rw [h2arrs]
      exact getElem?_of_getD (lt_of_lt_of_le hwtN hdgL) hDGw
    have := evalB_bin (B := B) (op := .sub)
      (e := .add (.get ao (.var "pl.w")) (.get dg (.var "pl.w"))) (f := .lit 1)
      (σ := σ₂)
      (by
        have := evalB_bin (B := B) (op := .add) (e := .get ao (.var "pl.w"))
          (f := .get dg (.var "pl.w")) (σ := σ₂) hao hdg (by simp; omega)
        simpa using this)
      (evalB_lit (by omega)) (by simp; omega)
    simp only [Bop.apply_sub] at this
    rw [show offF (wfun t) + gv - 1 = offF (wfun t) + (gv - 1) by omega] at this
    exact this
  have hr3 : Run B (.assign "pl.k"
      (.sub (.add (.get ao (.var "pl.w")) (.get dg (.var "pl.w"))) (.lit 1)))
      σ₂ (σ₂.setVar "pl.k" (offF (wfun t) + (gv - 1))) 8 := by
    refine (Run.assign hev3).mono ?_
    simp
  set σ₃ := σ₂.setVar "pl.k" (offF (wfun t) + (gv - 1)) with hσ₃
  have h3k : σ₃.vars "pl.k" = offF (wfun t) + (gv - 1) := by rw [hσ₃]; simp
  have h3arrs : ∀ b, σ₃.arrs b = σ.arrs b := by
    intro b; rw [hσ₃]; simpa using h2arrs b
  -- 4./5. the moved copy's value and its mate
  have hr4 : Run B (.assign "pl.y" (.get aj (.var "pl.k"))) σ₃
      (σ₃.setVar "pl.y" yv) 3 := by
    refine (Run.assign (evalB_get (evalB_var (by rw [h3k]; omega)) ?_
      (by omega))).mono (by simp)
    rw [h3arrs]
    exact getElem?_of_getD (lt_of_lt_of_le hlastlt hajL) hAJlast
  set σ₄ := σ₃.setVar "pl.y" yv with hσ₄
  have h4k : σ₄.vars "pl.k" = offF (wfun t) + (gv - 1) := by
    rw [hσ₄]; simpa using h3k
  have h4arrs : ∀ b, σ₄.arrs b = σ.arrs b := by
    intro b; rw [hσ₄]; simpa using h3arrs b
  have hr5 : Run B (.assign "pl.s" (.get mt (.var "pl.k"))) σ₄
      (σ₄.setVar "pl.s" ysv) 3 := by
    refine (Run.assign (evalB_get (evalB_var (by rw [h4k]; omega)) ?_
      (by omega))).mono (by simp)
    rw [h4arrs]
    exact getElem?_of_getD (lt_of_lt_of_le hlastlt hmtL) hMTlast
  set σ₅ := σ₄.setVar "pl.s" ysv with hσ₅
  have h5p : σ₅.vars "pl.p" = pv := by rw [hσ₅, hσ₄, hσ₃, hσ₂]; simp
  have h5y : σ₅.vars "pl.y" = yv := by rw [hσ₅, hσ₄]; simp
  have h5s : σ₅.vars "pl.s" = ysv := by rw [hσ₅]; simp
  have h5w : σ₅.vars "pl.w" = wfun t := by rw [hσ₅, hσ₄, hσ₃]; simpa using h2w
  have h5arrs : ∀ b, σ₅.arrs b = σ.arrs b := by
    intro b; rw [hσ₅]; simpa using h4arrs b
  -- 6. move the last copy into the vacated slot
  have hr6 : Run B (.store aj (.var "pl.p") (.var "pl.y")) σ₅
      (σ₅.setArr aj pv yv) 3 := by
    refine (Run.store (by rw [← h5p]; exact evalB_var (by rw [h5p]; omega))
      (by rw [← h5y]; exact evalB_var (by rw [h5y]; omega)) ?_).mono (by simp)
    rw [h5arrs]
    exact lt_of_lt_of_le hpvlt hajL
  set σ₆ := σ₅.setArr aj pv yv with hσ₆
  have h6p : σ₆.vars "pl.p" = pv := by rw [hσ₆]; simpa using h5p
  have h6s : σ₆.vars "pl.s" = ysv := by rw [hσ₆]; simpa using h5s
  have h6mt : σ₆.arrs mt = σ.arrs mt := by
    rw [hσ₆]
    simp only [arrs_setArr, if_neg (Ne.symm haj_mt)]
    exact h5arrs mt
  -- 7. the vacated slot's new mate
  have hr7 : Run B (.store mt (.var "pl.p") (.var "pl.s")) σ₆
      (σ₆.setArr mt pv ysv) 3 := by
    refine (Run.store (by rw [← h6p]; exact evalB_var (by rw [h6p]; omega))
      (by rw [← h6s]; exact evalB_var (by rw [h6s]; omega)) ?_).mono (by simp)
    rw [h6mt]
    exact lt_of_lt_of_le hpvlt hmtL
  set σ₇ := σ₆.setArr mt pv ysv with hσ₇
  have h7p : σ₇.vars "pl.p" = pv := by rw [hσ₇]; simpa using h6p
  have h7s : σ₇.vars "pl.s" = ysv := by rw [hσ₇]; simpa using h6s
  have h7mtL : (σ₇.arrs mt).length = (σ.arrs mt).length := by
    rw [hσ₇]
    simp only [arrs_setArr, if_pos rfl, if_true, List.length_set]
    rw [h6mt]
  -- 8. the moved copy's mate repaired
  have hr8 : Run B (.store mt (.var "pl.s") (.var "pl.p")) σ₇
      (σ₇.setArr mt ysv pv) 3 := by
    refine (Run.store (by rw [← h7s]; exact evalB_var (by rw [h7s]; omega))
      (by rw [← h7p]; exact evalB_var (by rw [h7p]; omega)) ?_).mono (by simp)
    rw [h7mtL]
    exact lt_of_lt_of_le hysvlt hmtL
  set σ₈ := σ₇.setArr mt ysv pv with hσ₈
  have h8w : σ₈.vars "pl.w" = wfun t := by
    rw [hσ₈, hσ₇, hσ₆]
    simpa using h5w
  have h8dg : σ₈.arrs dg = σ.arrs dg := by
    rw [hσ₈, hσ₇, hσ₆]
    simp only [arrs_setArr, if_neg hdg_mt, if_neg (Ne.symm haj_dg)]
    exact h5arrs dg
  -- 9. shrink the target row
  have hev9 : (Expr.sub (.get dg (.var "pl.w")) (.lit 1)).evalB B σ₈
      = some (gv - 1) := by
    have hdg : (Expr.get dg (.var "pl.w")).evalB B σ₈ = some gv := by
      refine evalB_get (evalB_var (by rw [h8w]; omega)) ?_ (by omega)
      rw [h8dg]
      exact getElem?_of_getD (lt_of_lt_of_le hwtN hdgL) hDGw
    have := evalB_bin (B := B) (op := .sub) (e := .get dg (.var "pl.w"))
      (f := .lit 1) (σ := σ₈) hdg (evalB_lit (by omega)) (by simp; omega)
    simpa using this
  have hr9 : Run B (.store dg (.var "pl.w")
      (.sub (.get dg (.var "pl.w")) (.lit 1))) σ₈
      (σ₈.setArr dg (wfun t) (gv - 1)) 6 := by
    refine (Run.store (by rw [← h8w]; exact evalB_var (by rw [h8w]; omega))
      hev9 ?_).mono (by simp)
    rw [h8dg]
    exact lt_of_lt_of_le hwtN hdgL
  set σ₉ := σ₈.setArr dg (wfun t) (gv - 1) with hσ₉
  have h9j : σ₉.vars "pl.j" = t := by
    rw [hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁]
    simp [← htdef]
  -- 10. the counter
  have hr10 : Run B (.assign "pl.j" (.add (.var "pl.j") (.lit 1))) σ₉
      (σ₉.setVar "pl.j" (t + 1)) 4 := by
    have := evalB_incr (B := B) (x := "pl.j") (σ := σ₉) (by rw [h9j]; omega)
    rw [h9j] at this
    exact (Run.assign this).mono (by simp)
  set σf := σ₉.setVar "pl.j" (t + 1) with hσf
  -- ===== the final state's regions =====
  have hfj : σf.vars "pl.j" = t + 1 := by rw [hσf]; simp
  have hfvars : ∀ y', y' ≠ "pl.j" → y' ≠ "pl.w" → y' ≠ "pl.p" → y' ≠ "pl.k" →
      y' ≠ "pl.y" → y' ≠ "pl.s" → σf.vars y' = σ.vars y' := by
    intro y' h1 h2 h3 h4 h5 h6
    rw [hσf, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁]
    simp [h1, h2, h3, h4, h5, h6]
  have hfao : σf.arrs ao = σ.arrs ao := by
    rw [hσf, hσ₉, hσ₈, hσ₇, hσ₆]
    simp only [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdg_ao),
      if_neg (Ne.symm hmt_ao), if_neg (Ne.symm haj_ao)]
    exact h5arrs ao
  have hfaj : σf.arrs aj = (σ.arrs aj).set pv yv := by
    rw [hσf, hσ₉, hσ₈, hσ₇, hσ₆]
    simp only [arrs_setVar, arrs_setArr, if_neg haj_dg, if_neg haj_mt,
      if_pos rfl, if_true]
    rw [h5arrs aj]
  have hfmt : σf.arrs mt = ((σ.arrs mt).set pv ysv).set ysv pv := by
    rw [hσf, hσ₉, hσ₈, hσ₇]
    simp only [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdg_mt), if_pos rfl,
      if_true]
    rw [h6mt]
  have hfdg : σf.arrs dg = (σ.arrs dg).set (wfun t) (gv - 1) := by
    rw [hσf, hσ₉]
    simp only [arrs_setVar, arrs_setArr, if_pos rfl, if_true]
    rw [h8dg]
  -- the pointwise reads of the final arrays
  have hfajD : ∀ c, (σf.arrs aj).getD c 0 =
      if c = pv then yv else (σ.arrs aj).getD c 0 := by
    intro c
    rw [hfaj, getD_set _ _ _ (lt_of_lt_of_le hpvlt hajL)]
  have hfmtD : ∀ c, (σf.arrs mt).getD c 0 =
      if c = ysv then pv else if c = pv then ysv else (σ.arrs mt).getD c 0 := by
    intro c
    rw [hfmt, getD_set _ _ _ (by
        rw [List.length_set]
        exact lt_of_lt_of_le hysvlt hmtL),
      getD_set _ _ _ (lt_of_lt_of_le hpvlt hmtL)]
  have hfdgD : ∀ c, (σf.arrs dg).getD c 0 =
      if c = wfun t then gv - 1 else (σ.arrs dg).getD c 0 := by
    intro c
    rw [hfdg, getD_set _ _ _ (lt_of_lt_of_le hwtN hdgL)]
  -- assemble
  refine ⟨σf, ?_, ⟨?_, ?_, ?_, ?_, h0, hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [hfj]⟩
  · -- the run at cost 43 = 6+6+10+4+4+3+3+3+7+4... wait: 50
    have h := hr1.seq (hr2.seq (hr3.seq (hr4.seq (hr5.seq (hr6.seq
      (hr7.seq (hr8.seq (hr9.seq hr10))))))))
    exact h.mono (by omega)
  · rw [hfvars "pl.a" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hva
  · rw [hfvars "pl.g" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hvg
  · rw [hfvars "pl.u" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hvu
  · rw [hfj]
    omega
  · rw [hfao]
    exact haoL
  · intro i hi
    rw [hfao]
    exact haoV i hi
  · rw [hfaj, List.length_set]
    exact hajL
  · rw [hfmt, List.length_set, List.length_set]
    exact hmtL
  · rw [hfdg, List.length_set]
    exact hdgL
  · rw [hfdgD, if_neg hne_ut]
    exact hdguC
  · rw [hfj]
    have := hPf'
    rw [funext hfajD, funext hfmtD, funext hfdgD]
    exact this
  · rw [hfj]
    rw [funext hfajD, funext hfmtD, funext hfdgD]
    exact hUf'

/-- Suspending more rows only weakens the region. -/
theorem PAdjF_mono_ex {H : SimpleGraph (Fin N)} {dead ex ex' : Set (Fin N)}
    {offF AJ MT DG : ℕ → ℕ} (hsub : ex ⊆ ex')
    (h : PAdjF H dead ex offF AJ MT DG) : PAdjF H dead ex' offF AJ MT DG := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, fun v hv hv' => h2 v hv (fun hc => hv' (hsub hc)),
    fun v hv hv' => h3 v hv (fun hc => hv' (hsub hc)),
    fun v hv hv' => h4 v hv (fun hc => hv' (hsub hc))⟩

/-- **The deletion pass**: read the row base and length, swap-remove
every live copy through its mate, kill the row.  From the region at
`dead` with the live centre named in `pl.u`, the region moves to
`dead ∪ {u}` — at a cost affine in the centre's **current** degree,
the swap-delete account. -/
theorem peelDelB_spec
    (hNB : N < B) (hsq : N * N + N + 4 < B)
    (haj_ao : aj ≠ ao) (hdg_ao : dg ≠ ao) (hmt_ao : mt ≠ ao)
    (haj_dg : aj ≠ dg) (haj_mt : aj ≠ mt) (hdg_mt : dg ≠ mt)
    (hu : u ∉ dead) :
    Spec B
      (fun σ => DelAdjSt ao aj dg mt G dead σ ∧ σ.vars "pl.u" = (u : ℕ))
      (peelDelB ao aj dg mt)
      (fun _ σ' => DelAdjSt ao aj dg mt G (dead ∪ {u}) σ')
      (47 * ((deleteVerts G dead).neighborSet u).ncard + 15) := by
  rintro σ ⟨hDel, hvu⟩
  obtain ⟨offF, h0, hstep, haoL, haoV, hajL, hmtL, hdgL, hPf0⟩ :=
    delAdjSt_iff_pAdj.mp hDel
  have hPf0' := hPf0
  obtain ⟨hdead0, hdeg0, hsound0, hcomp0⟩ := hPf0'
  have hexe : u ∉ (∅ : Set (Fin N)) := Set.notMem_empty u
  -- the frozen prefix and its facts
  set dgu := (σ.arrs dg).getD (u : ℕ) 0 with hdgu_def
  set wfun : ℕ → ℕ := fun s => (σ.arrs aj).getD (offF (u : ℕ) + s) 0 with hwf
  have hdgu0 : dgu = ((deleteVerts G dead).neighborSet u).ncard :=
    hdeg0 u hu hexe
  have hdguG : dgu ≤ (G.neighborSet u).ncard := by
    rw [hdgu0]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro w hw
    exact (deleteVerts_le G dead) hw
  have hwit : ∀ s, s < dgu → ∃ w : Fin N,
      (deleteVerts G dead).Adj u w ∧ wfun s = (w : ℕ) := by
    intro s hs
    obtain ⟨w, hadj, hAJc, -⟩ := hsound0 u hu hexe s hs
    exact ⟨w, hadj, hAJc⟩
  have hwN : ∀ s, s < dgu → wfun s < N := by
    intro s hs
    obtain ⟨w, -, hw⟩ := hwit s hs
    rw [hw]
    exact w.isLt
  have hwadj : ∀ s, (hs : s < dgu) →
      (deleteVerts G dead).Adj u ⟨wfun s, hwN s hs⟩ := by
    intro s hs
    obtain ⟨w, hadj, hw⟩ := hwit s hs
    have : (⟨wfun s, hwN s hs⟩ : Fin N) = w := Fin.ext hw
    rw [this]
    exact hadj
  have hwinj : ∀ s, s < dgu → ∀ s', s' < dgu → wfun s = wfun s' → s = s' := by
    intro s hs s' hs' heq
    exact hPf0.rowInj hu hexe hs hs' heq
  have hwcompl : ∀ x : Fin N, (deleteVerts G dead).Adj u x →
      (x : Fin N) ∈ Tset wfun dgu := by
    intro x hadj
    obtain ⟨s, hs, hAJc⟩ := hcomp0 u hu hexe x hadj
    exact ⟨s, hs, hAJc.symm⟩
  have huval : (u : ℕ) < B := by
    have := u.isLt
    omega
  have hoffN : offF N ≤ N * N := offF_le_sq h0 hstep
  have hoffu : offF (u : ℕ) ≤ N * N :=
    le_trans (offF_mono hstep N le_rfl (u : ℕ) (le_of_lt u.isLt)) hoffN
  have hdguN : dgu ≤ N := le_trans hdguG (ncard_neighborSet_le_card u)
  -- ===== prologue: cache the row base and length, zero the counter =====
  have hra : Run B (.assign "pl.a" (.get ao (.var "pl.u"))) σ
      (σ.setVar "pl.a" (offF (u : ℕ))) 3 := by
    refine (Run.assign (evalB_get (by rw [← hvu]; exact evalB_var (by rw [hvu]; omega))
      (getElem?_of_getD (by omega) (haoV (u : ℕ) (le_of_lt u.isLt)))
      (by omega))).mono (by simp)
  set σa := σ.setVar "pl.a" (offF (u : ℕ)) with hσa
  have hau : σa.vars "pl.u" = (u : ℕ) := by rw [hσa]; simpa using hvu
  have haarrs : ∀ b, σa.arrs b = σ.arrs b := fun b => by rw [hσa]; simp
  have hrb : Run B (.assign "pl.g" (.get dg (.var "pl.u"))) σa
      (σa.setVar "pl.g" dgu) 3 := by
    refine (Run.assign (evalB_get (k := (u : ℕ))
      (by rw [← hau]; exact evalB_var (by rw [hau]; omega))
      ?_ (by omega))).mono (by simp)
    rw [haarrs]
    exact getElem?_of_getD (lt_of_lt_of_le u.isLt hdgL) rfl
  set σb := σa.setVar "pl.g" dgu with hσb
  have hrc : Run B (.assign "pl.j" (.lit 0)) σb (σb.setVar "pl.j" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  set σc := σb.setVar "pl.j" 0 with hσc
  have hcarrs : ∀ b, σc.arrs b = σ.arrs b := fun b => by
    rw [hσc, hσb]
    simpa using haarrs b
  -- the invariant holds on entry
  have hIc : DelInv ao aj dg mt G dead u offF wfun dgu σc ∧
      σc.vars "pl.j" = 0 := by
    have hcj : σc.vars "pl.j" = 0 := by rw [hσc]; simp
    refine ⟨⟨?_, ?_, ?_, ?_, h0, hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hcj⟩
    · rw [hσc, hσb, hσa]; simp
    · rw [hσc, hσb]; simp
    · rw [hσc, hσb]; simpa using hau
    · rw [hcj]; omega
    · rw [hcarrs]; exact haoL
    · intro i hi; rw [hcarrs]; exact haoV i hi
    · rw [hcarrs]; exact hajL
    · rw [hcarrs]; exact hmtL
    · rw [hcarrs]; exact hdgL
    · rw [hcarrs]
    · rw [hcj, Tset_zero, delStar_empty]
      have := PAdjF_mono_ex (Set.empty_subset {u}) hPf0
      simp only [hcarrs]
      exact this
    · rw [hcj]
      intro s hs0 hs
      refine ⟨rfl, ?_⟩
      obtain ⟨w, hadj, hAJc, s', hs', hMTc, hAJb, hMTb⟩ := hsound0 u hu hexe s hs
      refine ⟨s', ?_, ?_, ?_, ?_⟩ <;> simp only [hcarrs] <;>
        rw [show wfun s = (w : ℕ) from hAJc]
      · exact hs'
      · exact hMTc
      · exact hAJb
      · exact hMTb
  -- ===== the loop =====
  have hloop := Spec.forRange (B := B)
    (P := fun σ' => DelInv ao aj dg mt G dead u offF wfun dgu σ' ∧
      σ'.vars "pl.j" = 0)
    "pl.j" "pl.g"
    (fun σ' => DelInv ao aj dg mt G dead u offF wfun dgu σ') dgu 43
    (47 * dgu + 4)
    (fun σ' hσ' => by
      have := hσ'.2.2.2.1
      omega)
    (fun σ' hσ' => by
      have := hσ'.2.1
      omega)
    (fun σ' hσ' => hσ'.2.1)
    (fun σ' hσ' => hσ'.2.2.2.1)
    (peelDelTurnB_spec hNB hsq haj_ao hdg_ao hmt_ao haj_dg haj_mt hdg_mt
      hwN hwadj hwinj hdguG)
    (fun σ' hσ' => hσ'.1)
    (fun σ' hσ' => by
      rw [hσ'.2]
      omega)
  obtain ⟨σd, hrd, hId, hjd⟩ := hloop.run ⟨hIc.1, hIc.2⟩
  obtain ⟨hda, hdg', hdu, hdj, -, -, haoLd, haoVd, hajLd, hmtLd, hdgLd, hdguCd,
    hPfd, -⟩ := hId
  -- ===== kill the row =====
  have hre : Run B (.store dg (.var "pl.u") (.lit 0)) σd
      (σd.setArr dg (u : ℕ) 0) 3 := by
    refine (Run.store (by rw [← hdu]; exact evalB_var (by rw [hdu]; omega))
      (evalB_lit (by omega)) ?_).mono (by simp)
    exact lt_of_lt_of_le u.isLt hdgLd
  set σe := σd.setArr dg (u : ℕ) 0 with hσe
  have hedg : σe.arrs dg = (σd.arrs dg).set (u : ℕ) 0 := by
    rw [hσe]
    simp
  have heaj : σe.arrs aj = σd.arrs aj := by
    rw [hσe]
    simp only [arrs_setArr, if_neg haj_dg]
  have hemt : σe.arrs mt = σd.arrs mt := by
    rw [hσe]
    simp only [arrs_setArr, if_neg (Ne.symm hdg_mt)]
  have heao : σe.arrs ao = σd.arrs ao := by
    rw [hσe]
    simp only [arrs_setArr, if_neg (Ne.symm hdg_ao)]
  have hedgD : ∀ c, (σe.arrs dg).getD c 0 =
      if c = (u : ℕ) then 0 else (σd.arrs dg).getD c 0 := by
    intro c
    rw [hedg, getD_set _ _ _ (lt_of_lt_of_le u.isLt hdgLd)]
  -- the fully-starred graph is the vertex deletion
  have hgraph : delStar (deleteVerts G dead) u (Tset wfun dgu)
      = deleteVerts G (dead ∪ {u}) :=
    delStar_neighborSet_eq_deleteVerts G dead u hwcompl
  rw [hjd, hgraph] at hPfd
  obtain ⟨hdeadd, hdegd, hsoundd, hcompd⟩ := hPfd
  -- assemble the final region
  refine ⟨σe, ?_, ?_⟩
  · have h := hra.seq (hrb.seq (hrc.seq (hrd.seq hre)))
    refine h.mono ?_
    rw [hdgu0] at *
    omega
  · show DelAdjSt ao aj dg mt G (dead ∪ {u}) σe
    rw [delAdjSt_iff_pAdj]
    refine ⟨offF, h0, hstep, by rw [heao]; exact haoLd,
      (fun i hi => by rw [heao]; exact haoVd i hi),
      by rw [heaj]; exact hajLd, by rw [hemt]; exact hmtLd,
      by rw [hedg, List.length_set]; exact hdgLd, ?_, ?_, ?_, ?_⟩
    · -- dead rows of the union
      intro v hv
      try simp only []
      rw [hedgD]
      rcases (Set.mem_union _ _ _).mp hv with hvd | hvu'
      · rw [if_neg (fun hc => hu ((Fin.ext hc : v = u) ▸ hvd))]
        exact hdeadd v hvd
      · rw [if_pos (congrArg Fin.val (Set.mem_singleton_iff.mp hvu'))]
    · -- degrees
      intro v hv hvex
      try simp only []
      have hvu' : v ≠ u := fun hc => hv (Set.mem_union_right _ (hc ▸ rfl))
      have hvd : v ∉ dead := fun hc => hv (Set.mem_union_left _ hc)
      rw [hedgD, if_neg (fun hc => hvu' (Fin.ext hc))]
      exact hdegd v hvd (by simpa using hvu')
    · -- soundness
      intro v hv hvex s hs
      try simp only [] at hs ⊢
      have hvu' : v ≠ u := fun hc => hv (Set.mem_union_right _ (hc ▸ rfl))
      have hvd : v ∉ dead := fun hc => hv (Set.mem_union_left _ hc)
      rw [hedgD, if_neg (fun hc => hvu' (Fin.ext hc))] at hs
      obtain ⟨w, hadj, hAJc, s', hs', hMTc, hAJb, hMTb⟩ :=
        hsoundd v hvd (by simpa using hvu') s hs
      have hwu : w ≠ u := by
        intro hc
        subst hc
        exact absurd ((deleteVerts_adj).mp hadj).2.2
          (fun hcc => hcc (Set.mem_union_right _ rfl))
      refine ⟨w, hadj, by rw [heaj]; exact hAJc, s', ?_, ?_, ?_, ?_⟩
      · rw [hedgD, if_neg (fun hc => hwu (Fin.ext hc))]
        exact hs'
      · rw [hemt]; exact hMTc
      · rw [heaj]; exact hAJb
      · rw [hemt]; exact hMTb
    · -- completeness
      intro v hv hvex w hadj
      try simp only []
      have hvu' : v ≠ u := fun hc => hv (Set.mem_union_right _ (hc ▸ rfl))
      have hvd : v ∉ dead := fun hc => hv (Set.mem_union_left _ hc)
      obtain ⟨s, hs, hAJc⟩ := hcompd v hvd (by simpa using hvu') w hadj
      refine ⟨s, ?_, by rw [heaj]; exact hAJc⟩
      rw [hedgD, if_neg (fun hc => hvu' (Fin.ext hc))]
      exact hs

end DelLoop

/-! ## §8 The sweep's abstract quantities

The machine's semantic targets, in `(G, π, R)`-form: the cluster is the
wreach fibre at `2R` (`pfib`), rank-indexed totally (`pfibR`); the
stream mass is its running sum (`mval`); the ball the BFS emits is the
fibre (`pfib_eq_ball`); the level table is exact at every radius once
anchored, achieved and relaxed (`bfs_exact` — soundness plus
`d_complete`); and the deletion's current degree rides inside the
fibre (`curdeg_le_pfib`).  The budget's per-rank quantities `peelDeg`
(the live degrees over the ball at `2R-1` — every edge the BFS scans)
and the fibre size close against `Impl.sweepCharge` in §12. -/

section SweepAbstract

variable {N : ℕ} (G : SimpleGraph (Fin N)) (π : Equiv.Perm (Fin N)) (R : ℕ)

/-- The cluster of `u`, `(G, π, R)`-form — definitionally
`Driver.cluster` at the arena instantiation. -/
def pfib (u : Fin N) : Set (Fin N) := {w | u ∈ wreach G π (2 * R) w}

/-- Rank-indexed clusters, total. -/
noncomputable def pfibR (i : ℕ) : Set (Fin N) :=
  if h : i < N then pfib G π R (π.symm ⟨i, h⟩) else ∅

/-- The stream mass after `i` ranks. -/
noncomputable def mval (i : ℕ) : ℕ :=
  ∑ t ∈ Finset.range i, (pfibR G π R t).ncard

theorem mval_succ (i : ℕ) :
    mval G π R (i + 1) = mval G π R i + (pfibR G π R i).ncard :=
  Finset.sum_range_succ _ i

theorem mval_zero : mval G π R 0 = 0 := rfl

theorem self_mem_pfib (u : Fin N) : u ∈ pfib G π R u :=
  Lax3Proofs.ClusterPaths.self_mem_fiber G π (2 * R) u

theorem pfibR_eq {i : ℕ} (hi : i < N) :
    pfibR G π R i = pfib G π R (π.symm ⟨i, hi⟩) := dif_pos hi

theorem pfibR_ncard_le (i : ℕ) : (pfibR G π R i).ncard ≤ N := by
  calc (pfibR G π R i).ncard ≤ (Set.univ : Set (Fin N)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    _ = N := by simp [Set.ncard_univ]

theorem mval_le {i : ℕ} : mval G π R i ≤ i * N := by
  rw [mval]
  calc ∑ t ∈ Finset.range i, (pfibR G π R t).ncard
      ≤ ∑ _t ∈ Finset.range i, N :=
        Finset.sum_le_sum fun t _ => pfibR_ncard_le G π R t
    _ = i * N := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem mval_mono {i j : ℕ} (hij : i ≤ j) : mval G π R i ≤ mval G π R j := by
  rw [mval, mval]
  refine Finset.sum_le_sum_of_subset ?_
  intro x hx
  rw [Finset.mem_range] at hx ⊢
  omega

/-- **The cluster is the current ball** — `fiber_eq_peeledBall` at the
peel prefix. -/
theorem pfib_eq_ball (u : Fin N) :
    pfib G π R u =
      ball (deleteVerts G (peelSet π ((π u : ℕ)))) (2 * R) u := by
  rw [pfib, Impl.fiber_eq_peeledBall, peelSet_rank]

/-- **The exact truncated level table**: anchored at the source,
achieved on discovered entries, relaxed below the cap — then a level
test at any radius `k ≤ r` is exactly ball membership. -/
theorem bfs_exact {H : SimpleGraph (Fin N)} {u : Fin N} {D : ℕ → ℕ} {r : ℕ}
    (h0 : D ((u : ℕ)) = 0)
    (hach : ∀ z, (hz : z < N) → D z ≤ r → WithinDist H (D z) u ⟨z, hz⟩)
    (hrel : ∀ s w : Fin N, D ((s : ℕ)) < r → H.Adj s w →
      D ((w : ℕ)) ≤ D ((s : ℕ)) + 1) :
    ∀ k, k ≤ r → ∀ v : Fin N, (D ((v : ℕ)) ≤ k ↔ v ∈ ball H k u) := by
  intro k hk v
  constructor
  · intro h
    have hach' := hach (v : ℕ) v.isLt (le_trans h hk)
    rw [Fin.eta] at hach'
    exact mem_ball.mpr (withinDist_mono_radius h hach')
  · intro h
    exact d_complete h0 hrel k hk v (mem_ball.mp h)

/-- A walk inside the peeled graph stays off the peeled set. -/
theorem not_mem_of_withinDist_deleteVerts {V : Type*} {G : SimpleGraph V}
    {S : Set V} {d : ℕ} {a b : V}
    (h : WithinDist (deleteVerts G S) d a b) (ha : a ∉ S) : b ∉ S := by
  obtain ⟨q, -⟩ := h
  exact Impl.not_mem_of_mem_support_deleteVerts q ha b q.end_mem_support

/-- The rank-`i` centre is live at its own step. -/
theorem symm_not_peeled {N : ℕ} (π : Equiv.Perm (Fin N)) {i : ℕ}
    (hi : i < N) : π.symm ⟨i, hi⟩ ∉ peelSet π i := by
  simp [peelSet]

open Classical in
/-- **The deletion account closes into the fibre**: the current degree
of the centre at its own deletion is at most its cluster size —
`curDeg_at_deletion_le_cluster` in `(G, π, R)`-form. -/
theorem curdeg_le_pfib (hr : 1 ≤ R) (u : Fin N) :
    ((deleteVerts G (peelSet π ((π u : ℕ)))).neighborSet u).ncard ≤
      (pfib G π R u).ncard := by
  classical
  rw [neighborSet_deleteVerts_peelSet_self, Set.ncard_coe_finset]
  have h := Impl.card_Ngt_le_cluster (G := G) (π := π) (r := R) hr u
  rwa [Impl.sweepCluster_eq_fiber] at h

open Classical in
/-- The per-rank scanned-edge budget: the live degrees over the ball at
radius `2R - 1` — exactly the rows the BFS expands. -/
noncomputable def peelDeg (i : ℕ) : ℕ :=
  if h : i < N then
    ∑ z ∈ (Set.toFinite (ball (deleteVerts G (peelSet π i)) (2 * R - 1)
        (π.symm ⟨i, h⟩))).toFinset,
      ((deleteVerts G (peelSet π i)).neighborSet z).ncard
  else 0

/-- The per-rank budget of the peel: the scanned edges, the fibre, a
constant. -/
noncomputable def stepK (i : ℕ) : ℕ :=
  64 * peelDeg G π R i + 256 * (pfibR G π R i).ncard + 256

/-- **The peel's closed budget.** -/
noncomputable def peelK : ℕ :=
  (∑ i ∈ Finset.range N, stepK G π R i) + 256 * N + 256

end SweepAbstract

/-! ## §9 Segments of the member stream -/

/-- A window of the stream enumerates a vertex set without
duplicates. -/
def SegAt {N : ℕ} (f : ℕ → ℕ) (b e : ℕ) (X : Set (Fin N)) : Prop :=
  (∀ p, b ≤ p → p < e → ∃ hz : f p < N, (⟨f p, hz⟩ : Fin N) ∈ X) ∧
  (∀ z : Fin N, z ∈ X → ∃ p, b ≤ p ∧ p < e ∧ f p = (z : ℕ)) ∧
  (∀ p q, b ≤ p → p < e → b ≤ q → q < e → f p = f q → p = q)

/-- A segment's width is its set's size. -/
theorem SegAt.card {N : ℕ} {f : ℕ → ℕ} {b e : ℕ} {X : Set (Fin N)}
    (h : SegAt f b e X) : e - b = X.ncard := by
  classical
  obtain ⟨hsound, hcompl, hinj⟩ := h
  have himg : (Finset.Ico b e).image f =
      (Set.toFinite X).toFinset.image Fin.val := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Ico, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨p, ⟨hbp, hpe⟩, rfl⟩
      obtain ⟨hz, hmem⟩ := hsound p hbp hpe
      exact ⟨⟨f p, hz⟩, hmem, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨p, hbp, hpe, hfp⟩ := hcompl z hz
      exact ⟨p, ⟨hbp, hpe⟩, hfp⟩
  have hcard1 : ((Finset.Ico b e).image f).card = (Finset.Ico b e).card := by
    refine Finset.card_image_of_injOn ?_
    intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_Ico] at hp hq
    exact hinj p q hp.1 hp.2 hq.1 hq.2 hpq
  have hcard2 : ((Set.toFinite X).toFinset.image Fin.val).card =
      (Set.toFinite X).toFinset.card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have hX : (Set.toFinite X).toFinset.card = X.ncard :=
    (Set.ncard_eq_toFinset_card X (Set.toFinite X)).symm
  rw [← Nat.card_Ico b e, ← hcard1, himg, hcard2, hX]

/-- A segment transports along agreement on its window. -/
theorem SegAt.congr {N : ℕ} {f f' : ℕ → ℕ} {b e : ℕ} {X : Set (Fin N)}
    (h : SegAt f b e X) (hagree : ∀ p, b ≤ p → p < e → f' p = f p) :
    SegAt f' b e X := by
  obtain ⟨hsound, hcompl, hinj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro p hbp hpe
    rw [hagree p hbp hpe]
    exact hsound p hbp hpe
  · intro z hz
    obtain ⟨p, hbp, hpe, hfp⟩ := hcompl z hz
    exact ⟨p, hbp, hpe, by rw [hagree p hbp hpe]; exact hfp⟩
  · intro p q hbp hpe hbq hqe hpq
    rw [hagree p hbp hpe, hagree q hbq hqe] at hpq
    exact hinj p q hbp hpe hbq hqe hpq

/-! ## §10 The sweep, at the machine -/

/-- The centre assignment, `(G, π, R)`-form — definitionally
`Driver.centre` at the arena instantiation. -/
noncomputable def pctr {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) (R : ℕ) (v : Fin N) : Fin N :=
  Lax3Proofs.CoverCentres.ctr G π R v

section SweepMachine

variable {B N : ℕ} {G : SimpleGraph (Fin N)} {π : Equiv.Perm (Fin N)} {R : ℕ}
  {ca co cm ra ao aj dg mt od : String}

/-- **The sweep loop's invariant at rank `i`**: the two cached cells,
the order, rank and deletable regions (the deleted set the rank
prefix), the assignment region partially written (first-hit marks below
`i`, sentinel `N` above), the level region all-sentinel, the stream's
segments and their recorded ends. -/
def SwInv (ca ra ao aj dg mt od : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) (R : ℕ) (i : ℕ) (σ : Env) : Prop :=
  σ.vars "pl.n" = N ∧
  σ.vars "pl.m" = mval G π R i ∧
  i ≤ N ∧
  OrdArr od π σ ∧
  RankArr ra π σ ∧
  DelAdjSt ao aj dg mt G (peelSet π i) σ ∧
  N ≤ (σ.arrs ca).length ∧
  (∀ v : Fin N, (σ.arrs ca).getD ((v : ℕ)) 0 =
    if ((π (pctr G π R v) : ℕ)) < i then ((pctr G π R v : Fin N) : ℕ) else N) ∧
  N ≤ (σ.arrs plDd).length ∧
  (∀ z, z < N → (σ.arrs plDd).getD z 0 = 2 * R + 1) ∧
  N * N ≤ (σ.arrs plRw).length ∧
  N + 1 ≤ (σ.arrs plRe).length ∧
  (∀ i', i' ≤ i → (σ.arrs plRe).getD i' 0 = mval G π R i') ∧
  (∀ i', i' < i → SegAt (fun p => (σ.arrs plRw).getD p 0) (mval G π R i')
    (mval G π R (i' + 1)) (pfibR G π R i'))

/-- **The BFS state at centre `u` of rank `i`**: the queue is the
segment being emitted (`pl.b .. pl.t`), read by the head cursor; the
level table is anchored, bounded, achieved and — over the popped
prefix — relaxed; the queue enumerates the discovered set without
duplicates, its levels are monotone along the stream with the window
within one level; and the first-hit marks are laid exactly on the
discovered vertices within radius `R`. -/
def PBfs (ca ra ao aj dg mt od : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) (R : ℕ) (i : ℕ) (u : Fin N) (σ : Env) : Prop :=
  σ.vars "pl.n" = N ∧
  σ.vars "pl.i" = i ∧
  σ.vars "pl.u" = (u : ℕ) ∧
  σ.vars "pl.b" = mval G π R i ∧
  σ.vars "pl.m" = mval G π R i ∧
  mval G π R i ≤ σ.vars "pl.h" ∧
  σ.vars "pl.h" ≤ σ.vars "pl.t" ∧
  σ.vars "pl.t" = mval G π R i +
    {z : Fin N | (σ.arrs plDd).getD ((z : ℕ)) 0 ≤ 2 * R}.ncard ∧
  OrdArr od π σ ∧
  RankArr ra π σ ∧
  DelAdjSt ao aj dg mt G (peelSet π i) σ ∧
  N ≤ (σ.arrs ca).length ∧
  N ≤ (σ.arrs plDd).length ∧
  N * N ≤ (σ.arrs plRw).length ∧
  N + 1 ≤ (σ.arrs plRe).length ∧
  (∀ i', i' ≤ i → (σ.arrs plRe).getD i' 0 = mval G π R i') ∧
  (∀ i', i' < i → SegAt (fun p => (σ.arrs plRw).getD p 0) (mval G π R i')
    (mval G π R (i' + 1)) (pfibR G π R i')) ∧
  (σ.arrs plDd).getD ((u : ℕ)) 0 = 0 ∧
  (∀ z, z < N → (σ.arrs plDd).getD z 0 ≤ 2 * R + 1) ∧
  (∀ z, (hz : z < N) → (σ.arrs plDd).getD z 0 ≤ 2 * R →
    WithinDist (deleteVerts G (peelSet π i)) ((σ.arrs plDd).getD z 0) u
      ⟨z, hz⟩) ∧
  SegAt (fun p => (σ.arrs plRw).getD p 0) (mval G π R i) (σ.vars "pl.t")
    {z : Fin N | (σ.arrs plDd).getD ((z : ℕ)) 0 ≤ 2 * R} ∧
  (∀ p q, mval G π R i ≤ p → p ≤ q → q < σ.vars "pl.t" →
    (σ.arrs plDd).getD ((σ.arrs plRw).getD p 0) 0 ≤
      (σ.arrs plDd).getD ((σ.arrs plRw).getD q 0) 0) ∧
  (σ.vars "pl.h" < σ.vars "pl.t" →
    ∀ p, mval G π R i ≤ p → p < σ.vars "pl.t" →
    (σ.arrs plDd).getD ((σ.arrs plRw).getD p 0) 0 ≤
      (σ.arrs plDd).getD ((σ.arrs plRw).getD (σ.vars "pl.h") 0) 0 + 1) ∧
  (∀ p, mval G π R i ≤ p → p < σ.vars "pl.h" →
    ∀ hp : (σ.arrs plRw).getD p 0 < N,
    (σ.arrs plDd).getD ((σ.arrs plRw).getD p 0) 0 < 2 * R →
    ∀ w : Fin N,
      (deleteVerts G (peelSet π i)).Adj ⟨(σ.arrs plRw).getD p 0, hp⟩ w →
      (σ.arrs plDd).getD ((w : ℕ)) 0 ≤
        (σ.arrs plDd).getD ((σ.arrs plRw).getD p 0) 0 + 1) ∧
  (∀ v : Fin N, ((π (pctr G π R v) : ℕ)) < i →
    (σ.arrs ca).getD ((v : ℕ)) 0 = ((pctr G π R v : Fin N) : ℕ)) ∧
  (∀ v : Fin N, ¬ ((π (pctr G π R v) : ℕ)) < i →
    (((σ.arrs plDd).getD ((v : ℕ)) 0 ≤ R ∧
        (σ.arrs ca).getD ((v : ℕ)) 0 = (u : ℕ)) ∨
      (¬ (σ.arrs plDd).getD ((v : ℕ)) 0 ≤ R ∧
        (σ.arrs ca).getD ((v : ℕ)) 0 = N)))

/-- **The expansion state**: the BFS state with the popped vertex's
cells cached and its row relaxed up to the inner counter. -/
def EInv (ca ra ao aj dg mt od : String) {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) (R : ℕ) (i : ℕ) (u : Fin N) (z : Fin N)
    (offF : ℕ → ℕ) (σ : Env) : Prop :=
  PBfs ca ra ao aj dg mt od G π R i u σ ∧
  σ.vars "pl.z" = (z : ℕ) ∧
  σ.vars "pl.d" = (σ.arrs plDd).getD ((z : ℕ)) 0 ∧
  σ.vars "pl.a" = offF ((z : ℕ)) ∧
  σ.vars "pl.g" = (σ.arrs dg).getD ((z : ℕ)) 0 ∧
  σ.vars "pl.j" ≤ σ.vars "pl.g" ∧
  (σ.arrs plDd).getD ((z : ℕ)) 0 < 2 * R ∧
  σ.vars "pl.h" < σ.vars "pl.t" ∧
  (σ.arrs plRw).getD (σ.vars "pl.h") 0 = (z : ℕ) ∧
  (∀ s, s < σ.vars "pl.j" →
    ∀ w : Fin N, (σ.arrs aj).getD (offF ((z : ℕ)) + s) 0 = (w : ℕ) →
      (σ.arrs plDd).getD ((w : ℕ)) 0 ≤ (σ.arrs plDd).getD ((z : ℕ)) 0 + 1)

/-- `OrdArr` transports along agreement on its array. -/
theorem ordArr_of_eq {od : String} {N : ℕ} {π : Equiv.Perm (Fin N)}
    {σ σ' : Env} (h : OrdArr od π σ) (he : σ'.arrs od = σ.arrs od) :
    OrdArr od π σ' := by
  rw [OrdArr, he]
  exact h

/-- `RankArr` transports along agreement on its array. -/
theorem rankArr_of_eq {ra : String} {N : ℕ} {π : Equiv.Perm (Fin N)}
    {σ σ' : Env} (h : RankArr ra π σ) (he : σ'.arrs ra = σ.arrs ra) :
    RankArr ra π σ' := by
  rw [RankArr, he]
  exact h

/-- **The seed**: read the rank's centre off the order region, anchor
its level and the segment, lay the self mark, set the cursors. -/
theorem peelSeedB_spec
    (hNB : N < B) (hsq : N * N + N + 4 < B) (hRB : 2 * R + 2 < B)
    (hca_dd : ca ≠ plDd) (hca_rw : ca ≠ plRw) (hca_re : ca ≠ plRe)
    (hod_ca : od ≠ ca) (hod_dd : od ≠ plDd) (hod_rw : od ≠ plRw)
    (hra_ca : ra ≠ ca) (hra_dd : ra ≠ plDd) (hra_rw : ra ≠ plRw)
    (hao_ca : ao ≠ ca) (hao_dd : ao ≠ plDd) (hao_rw : ao ≠ plRw)
    (haj_ca : aj ≠ ca) (haj_dd : aj ≠ plDd) (haj_rw : aj ≠ plRw)
    (hdg_ca : dg ≠ ca) (hdg_dd : dg ≠ plDd) (hdg_rw : dg ≠ plRw)
    (hmt_ca : mt ≠ ca) (hmt_dd : mt ≠ plDd) (hmt_rw : mt ≠ plRw)
    {i : ℕ} (hi : i < N) :
    Spec B
      (fun σ => SwInv ca ra ao aj dg mt od G π R i σ ∧ σ.vars "pl.i" = i)
      (peelSeedB ca od)
      (fun _ σ' => PBfs ca ra ao aj dg mt od G π R i (π.symm ⟨i, hi⟩) σ')
      25 := by
  rintro σ ⟨⟨hvn, hvm, hiN, hord, hrank, hadj, hcaL, hcaV, hddL, hddSen,
    hrwL, hreL, hreV, hsegs⟩, hvi⟩
  set u : Fin N := π.symm ⟨i, hi⟩ with hu
  have huval : (u : ℕ) < N := u.isLt
  have hmvle : mval G π R i ≤ i * N := mval_le G π R
  have hmvsq : mval G π R i < N * N := by
    have h3 : (i + 1) * N ≤ N * N := Nat.mul_le_mul_right N hi
    have h4 : i * N + N = (i + 1) * N := by ring
    omega
  -- 1. the centre off the order region
  have hr1 : Run B (.assign "pl.u" (.get od (.var "pl.i"))) σ
      (σ.setVar "pl.u" ((u : ℕ))) 3 := by
    refine (Run.assign (evalB_get (k := i)
      (by rw [← hvi]; exact evalB_var (by rw [hvi]; omega)) ?_
      (by omega))).mono (by simp)
    exact getElem?_of_getD (lt_of_lt_of_le hi hord.1) (hord.2 ⟨i, hi⟩)
  set σ1 := σ.setVar "pl.u" ((u : ℕ)) with hσ1
  have h1m : σ1.vars "pl.m" = mval G π R i := by rw [hσ1]; simpa using hvm
  -- 2. the segment anchor
  have hr2 : Run B (.assign "pl.b" (.var "pl.m")) σ1
      (σ1.setVar "pl.b" (mval G π R i)) 2 := by
    refine (Run.assign ?_).mono (by simp)
    rw [← h1m]
    exact evalB_var (by rw [h1m]; omega)
  set σ2 := σ1.setVar "pl.b" (mval G π R i) with hσ2
  have h2u : σ2.vars "pl.u" = (u : ℕ) := by rw [hσ2, hσ1]; simp
  have h2arrs : ∀ b, σ2.arrs b = σ.arrs b := fun b => by rw [hσ2, hσ1]; simp
  -- 3. the level anchor
  have hr3 : Run B (.store plDd (.var "pl.u") (.lit 0)) σ2
      (σ2.setArr plDd ((u : ℕ)) 0) 3 := by
    refine (Run.store (by rw [← h2u]; exact evalB_var (by rw [h2u]; omega))
      (evalB_lit (by omega)) ?_).mono (by simp)
    rw [h2arrs]
    exact lt_of_lt_of_le huval hddL
  set σ3 := σ2.setArr plDd ((u : ℕ)) 0 with hσ3
  have h3u : σ3.vars "pl.u" = (u : ℕ) := by rw [hσ3]; simpa using h2u
  have h3m : σ3.vars "pl.m" = mval G π R i := by
    rw [hσ3, hσ2, hσ1]
    simpa using hvm
  have h3rw : σ3.arrs plRw = σ.arrs plRw := by
    rw [hσ3]
    simp only [arrs_setArr, if_neg (show plRw ≠ plDd by decide)]
    exact h2arrs plRw
  -- 4. the segment's first member
  have hr4 : Run B (.store plRw (.var "pl.m") (.var "pl.u")) σ3
      (σ3.setArr plRw (mval G π R i) ((u : ℕ))) 3 := by
    refine (Run.store (by rw [← h3m]; exact evalB_var (by rw [h3m]; omega))
      (by rw [← h3u]; exact evalB_var (by rw [h3u]; omega)) ?_).mono (by simp)
    rw [h3rw]
    exact lt_of_lt_of_le hmvsq hrwL
  set σ4 := σ3.setArr plRw (mval G π R i) ((u : ℕ)) with hσ4
  have h4u : σ4.vars "pl.u" = (u : ℕ) := by rw [hσ4]; simpa using h3u
  have h4n : σ4.vars "pl.n" = N := by
    rw [hσ4, hσ3, hσ2, hσ1]
    simpa using hvn
  have h4ca : σ4.arrs ca = σ.arrs ca := by
    rw [hσ4, hσ3]
    simp only [arrs_setArr, if_neg hca_rw, if_neg hca_dd]
    exact h2arrs ca
  -- 5. the self mark
  have hcau : (σ4.arrs ca).getD ((u : ℕ)) 0 =
      if ((π (pctr G π R u) : ℕ)) < i then ((pctr G π R u : Fin N) : ℕ)
      else N := by
    rw [h4ca]
    exact hcaV u
  have hcondEv : (Cond.eq (.get ca (.var "pl.u")) (.var "pl.n")).evalB B σ4
      = some (((σ4.arrs ca).getD ((u : ℕ)) 0) == N) := by
    refine evalB_condEq (evalB_get (k := (u : ℕ))
      (by rw [← h4u]; exact evalB_var (by rw [h4u]; omega)) ?_ ?_) ?_
    · exact getElem?_of_getD (by rw [h4ca]; exact lt_of_lt_of_le huval hcaL) rfl
    · rw [hcau]
      split
      · exact lt_trans (pctr G π R u).isLt (by omega)
      · omega
    · rw [← h4n]
      exact evalB_var (by rw [h4n]; omega)
  -- the two mark branches agree on everything the finish reads
  suffices hfin : ∀ σ5 : Env,
      Run B (.ite (.eq (.get ca (.var "pl.u")) (.var "pl.n"))
        (.store ca (.var "pl.u") (.var "pl.u")) .skip) σ4 σ5 8 →
      (∀ b', b' ≠ ca → σ5.arrs b' = σ4.arrs b') →
      σ5.vars = σ4.vars →
      (∀ v : Fin N, v ≠ u →
        (σ5.arrs ca).getD ((v : ℕ)) 0 = (σ4.arrs ca).getD ((v : ℕ)) 0) →
      (σ5.arrs ca).length = (σ4.arrs ca).length →
      (¬ ((π (pctr G π R u) : ℕ)) < i →
        (σ5.arrs ca).getD ((u : ℕ)) 0 = (u : ℕ)) →
      (((π (pctr G π R u) : ℕ)) < i →
        (σ5.arrs ca).getD ((u : ℕ)) 0 = (σ4.arrs ca).getD ((u : ℕ)) 0) →
      ∃ σ', Run B (peelSeedB ca od) σ σ' 25 ∧
        PBfs ca ra ao aj dg mt od G π R i u σ' by
    by_cases hmark : ((π (pctr G π R u) : ℕ)) < i
    · have hne : (σ4.arrs ca).getD ((u : ℕ)) 0 ≠ N := by
        rw [hcau, if_pos hmark]
        exact Nat.ne_of_lt (pctr G π R u).isLt
      have hcondF : (Cond.eq (.get ca (.var "pl.u")) (.var "pl.n")).evalB B σ4
          = some false := by
        rw [hcondEv]
        congr 1
        simpa using hne
      exact hfin σ4 ((Run.ite_false hcondF Run.skip).mono (by simp))
        (fun _ _ => rfl) rfl (fun _ _ => rfl) rfl
        (fun hc => absurd hmark hc) (fun _ => rfl)
    · have heq : (σ4.arrs ca).getD ((u : ℕ)) 0 = N := by
        rw [hcau, if_neg hmark]
      have hcondT : (Cond.eq (.get ca (.var "pl.u")) (.var "pl.n")).evalB B σ4
          = some true := by
        rw [hcondEv]
        congr 1
        simpa using heq
      have hst : Run B (.store ca (.var "pl.u") (.var "pl.u")) σ4
          (σ4.setArr ca ((u : ℕ)) ((u : ℕ))) 3 := by
        refine (Run.store (by rw [← h4u]; exact evalB_var (by rw [h4u]; omega))
          (by rw [← h4u]; exact evalB_var (by rw [h4u]; omega)) ?_).mono
          (by simp)
        rw [h4ca]
        exact lt_of_lt_of_le huval hcaL
      refine hfin (σ4.setArr ca ((u : ℕ)) ((u : ℕ)))
        ((Run.ite_true hcondT hst).mono (by simp))
        (fun b' hb' => by simp only [arrs_setArr, if_neg hb']) rfl
        (fun v hv => by
          simp only [arrs_setArr, if_pos rfl, if_true]
          rw [getD_set _ _ _ (lt_of_lt_of_le huval (by rw [h4ca]; exact hcaL)),
            if_neg (fun hc => hv (Fin.ext hc))])
        (by simp only [arrs_setArr, if_pos rfl, if_true, List.length_set])
        (fun _ => by
          simp only [arrs_setArr, if_pos rfl, if_true]
          rw [getD_set _ _ _ (lt_of_lt_of_le huval (by rw [h4ca]; exact hcaL)),
            if_pos rfl])
        (fun hc => absurd hc hmark)
  intro σ5 hr5 h5other h5vars h5ne h5len h5neg h5pos
  -- 6./7. the cursors
  have h5m : σ5.vars "pl.m" = mval G π R i := by
    rw [h5vars, hσ4, hσ3, hσ2, hσ1]
    simpa using hvm
  have hr6 : Run B (.assign "pl.h" (.var "pl.m")) σ5
      (σ5.setVar "pl.h" (mval G π R i)) 2 := by
    refine (Run.assign ?_).mono (by simp)
    rw [← h5m]
    exact evalB_var (by rw [h5m]; omega)
  set σ6 := σ5.setVar "pl.h" (mval G π R i) with hσ6
  have h6m : σ6.vars "pl.m" = mval G π R i := by rw [hσ6]; simpa using h5m
  have hr7 : Run B (.assign "pl.t" (.add (.var "pl.m") (.lit 1))) σ6
      (σ6.setVar "pl.t" (mval G π R i + 1)) 4 := by
    have hev := evalB_bin (B := B) (op := .add) (e := .var "pl.m")
      (f := .lit 1) (σ := σ6) (evalB_var (by rw [h6m]; omega))
      (evalB_lit (by omega)) (by simp only [Bop.apply_add]; rw [h6m]; omega)
    rw [h6m] at hev
    refine (Run.assign (by simpa using hev)).mono (by simp)
  set σ7 := σ6.setVar "pl.t" (mval G π R i + 1) with hσ7
  -- the final environment's projections
  have hfvars : ∀ y, y ≠ "pl.u" → y ≠ "pl.b" → y ≠ "pl.h" → y ≠ "pl.t" →
      σ7.vars y = σ.vars y := by
    intro y h1 h2 h3 h4
    rw [hσ7, hσ6]
    simp only [vars_setVar, if_neg h4, if_neg h3]
    rw [h5vars, hσ4, hσ3, hσ2, hσ1]
    simp [h1, h2]
  have hfarrs : ∀ b', b' ≠ ca → b' ≠ plDd → b' ≠ plRw →
      σ7.arrs b' = σ.arrs b' := by
    intro b' h1 h2 h3
    rw [hσ7, hσ6]
    simp only [arrs_setVar]
    rw [h5other b' h1, hσ4, hσ3]
    simp only [arrs_setArr, if_neg h3, if_neg h2]
    exact h2arrs b'
  have hfdd : σ7.arrs plDd = (σ.arrs plDd).set ((u : ℕ)) 0 := by
    rw [hσ7, hσ6]
    simp only [arrs_setVar]
    rw [h5other plDd (Ne.symm hca_dd), hσ4, hσ3]
    simp only [arrs_setArr, if_neg (show plDd ≠ plRw by decide), if_pos rfl,
      if_true]
    rw [h2arrs plDd]
  have hfddD : ∀ c, (σ7.arrs plDd).getD c 0 =
      if c = (u : ℕ) then 0 else (σ.arrs plDd).getD c 0 := by
    intro c
    rw [hfdd, getD_set _ _ _ (lt_of_lt_of_le huval hddL)]
  have hfrw : σ7.arrs plRw = (σ.arrs plRw).set (mval G π R i) ((u : ℕ)) := by
    rw [hσ7, hσ6]
    simp only [arrs_setVar]
    rw [h5other plRw (Ne.symm hca_rw), hσ4, hσ3]
    simp only [arrs_setArr, if_pos rfl, if_true, if_neg
      (show plRw ≠ plDd by decide)]
    rw [h2arrs plRw]
  have hfrwD : ∀ c, (σ7.arrs plRw).getD c 0 =
      if c = mval G π R i then ((u : ℕ)) else (σ.arrs plRw).getD c 0 := by
    intro c
    rw [hfrw, getD_set _ _ _ (lt_of_lt_of_le hmvsq hrwL)]
  have hfca : ∀ v : Fin N, v ≠ u →
      (σ7.arrs ca).getD ((v : ℕ)) 0 = (σ.arrs ca).getD ((v : ℕ)) 0 := by
    intro v hv
    rw [hσ7, hσ6]
    simp only [arrs_setVar]
    rw [h5ne v hv, h4ca]
  have hfcau_pos : ((π (pctr G π R u) : ℕ)) < i →
      (σ7.arrs ca).getD ((u : ℕ)) 0 = (σ.arrs ca).getD ((u : ℕ)) 0 := by
    intro h
    rw [hσ7, hσ6]
    simp only [arrs_setVar]
    rw [h5pos h, h4ca]
  have hfcau_neg : ¬ ((π (pctr G π R u) : ℕ)) < i →
      (σ7.arrs ca).getD ((u : ℕ)) 0 = (u : ℕ) := by
    intro h
    rw [hσ7, hσ6]
    simp only [arrs_setVar]
    exact h5neg h
  -- the discovered set is the singleton
  have hset : {z : Fin N | (σ7.arrs plDd).getD ((z : ℕ)) 0 ≤ 2 * R}
      = {u} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [hfddD]
    by_cases hz : (z : ℕ) = (u : ℕ)
    · rw [if_pos hz]
      simp only [Nat.zero_le, true_iff]
      exact Fin.ext hz
    · rw [if_neg hz, hddSen (z : ℕ) z.isLt]
      constructor
      · omega
      · intro hc
        exact absurd (congrArg Fin.val hc) hz
  refine ⟨σ7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the assembled run
    have h := hr1.seq (hr2.seq (hr3.seq (hr4.seq (hr5.seq (hr6.seq hr7)))))
    exact h.mono (by omega)
  · rw [hfvars "pl.n" (by decide) (by decide) (by decide) (by decide)]
    exact hvn
  · rw [hfvars "pl.i" (by decide) (by decide) (by decide) (by decide)]
    exact hvi
  · rw [hσ7, hσ6]
    simp only [vars_setVar, if_neg (show ¬("pl.u" = "pl.t") by decide),
      if_neg (show ¬("pl.u" = "pl.h") by decide)]
    rw [h5vars, hσ4, hσ3, hσ2, hσ1]
    simp
  · rw [hσ7, hσ6]
    simp only [vars_setVar, if_neg (show ¬("pl.b" = "pl.t") by decide),
      if_neg (show ¬("pl.b" = "pl.h") by decide)]
    rw [h5vars, hσ4, hσ3, hσ2]
    simp
  · rw [hfvars "pl.m" (by decide) (by decide) (by decide) (by decide)]
    exact hvm
  · rw [hσ7, hσ6]
    simp
  · have hvh7 : σ7.vars "pl.h" = mval G π R i := by rw [hσ7, hσ6]; simp
    have hvt7 : σ7.vars "pl.t" = mval G π R i + 1 := by rw [hσ7]; simp
    rw [hvh7, hvt7]
    omega
  · -- the count
    have hvt7 : σ7.vars "pl.t" = mval G π R i + 1 := by rw [hσ7]; simp
    rw [hvt7, hset, Set.ncard_singleton]
  · exact ordArr_of_eq hord (hfarrs od hod_ca hod_dd hod_rw)
  · exact rankArr_of_eq hrank (hfarrs ra hra_ca hra_dd hra_rw)
  · exact hadj.of_eq (hfarrs ao hao_ca hao_dd hao_rw)
      (hfarrs aj haj_ca haj_dd haj_rw) (hfarrs dg hdg_ca hdg_dd hdg_rw)
      (hfarrs mt hmt_ca hmt_dd hmt_rw)
  · rw [hσ7, hσ6]
    simp only [arrs_setVar]
    rw [h5len, h4ca]
    exact hcaL
  · rw [hfdd, List.length_set]
    exact hddL
  · rw [hfrw, List.length_set]
    exact hrwL
  · rw [hfarrs plRe (Ne.symm hca_re) (by decide) (by decide)]
    exact hreL
  · intro i' hi'
    rw [hfarrs plRe (Ne.symm hca_re) (by decide) (by decide)]
    exact hreV i' hi'
  · -- earlier segments survive: their cells sit below the write
    intro i' hi'
    refine SegAt.congr (hsegs i' hi') ?_
    intro p hbp hpe
    rw [hfrwD, if_neg ?_]
    have hlt : p < mval G π R i := lt_of_lt_of_le hpe (mval_mono G π R hi')
    omega
  · rw [hfddD, if_pos rfl]
  · intro z hz
    rw [hfddD]
    by_cases hzu : z = (u : ℕ)
    · rw [if_pos hzu]
      omega
    · rw [if_neg hzu, hddSen z hz]
  · -- achieved: only the source is discovered, at level zero
    intro z hz hle
    rw [hfddD] at hle ⊢
    by_cases hzu : z = (u : ℕ)
    · rw [if_pos hzu]
      have : (⟨z, hz⟩ : Fin N) = u := Fin.ext hzu
      rw [this]
      exact withinDist_of_eq _ 0 rfl
    · rw [if_neg hzu, hddSen z hz] at hle
      omega
  · -- the queue segment is the singleton
    have hvt7 : σ7.vars "pl.t" = mval G π R i + 1 := by rw [hσ7]; simp
    rw [hvt7, hset]
    refine ⟨?_, ?_, ?_⟩
    · intro p hbp hpe
      try simp only []
      have hp : p = mval G π R i := by omega
      subst hp
      have hval : (σ7.arrs plRw).getD (mval G π R i) 0 = (u : ℕ) := by
        rw [hfrwD, if_pos rfl]
      simp only [hval]
      exact ⟨huval, by simp⟩
    · intro z hzmem
      rw [Set.mem_singleton_iff] at hzmem
      subst hzmem
      refine ⟨mval G π R i, le_rfl, by omega, ?_⟩
      try simp only []
      rw [hfrwD, if_pos rfl]
    · intro p q hbp hpe hbq hqe _
      omega
  · -- levels monotone on the singleton window
    intro p q hbp hpq hqt
    have hvt7 : σ7.vars "pl.t" = mval G π R i + 1 := by rw [hσ7]; simp
    rw [hvt7] at hqt
    have hp : p = mval G π R i := by omega
    have hq : q = mval G π R i := by omega
    subst hp
    rw [hq]
  · -- the window is within one level of its head
    intro hht p hbp hpt
    have hvt7 : σ7.vars "pl.t" = mval G π R i + 1 := by rw [hσ7]; simp
    have hvh7 : σ7.vars "pl.h" = mval G π R i := by rw [hσ7, hσ6]; simp
    rw [hvt7] at hpt
    rw [hvh7]
    have hp : p = mval G π R i := by omega
    subst hp
    omega
  · -- nothing is popped yet
    intro p hbp hph
    have hvh7 : σ7.vars "pl.h" = mval G π R i := by rw [hσ7, hσ6]; simp
    rw [hvh7] at hph
    omega
  · -- earlier marks are untouched
    intro v hv
    by_cases hvu : v = u
    · subst hvu
      rw [hfcau_pos hv, hcaV u, if_pos hv]
    · rw [hfca v hvu, hcaV v, if_pos hv]
  · -- fresh marks: the source got its self mark; the rest are sentinel
    intro v hv
    by_cases hvu : v = u
    · subst hvu
      left
      rw [hfddD, if_pos rfl, hfcau_neg hv]
      exact ⟨Nat.zero_le R, rfl⟩
    · right
      rw [hfddD, if_neg (fun hc => hvu (Fin.ext hc)), hddSen (v : ℕ) v.isLt,
        hfca v hvu, hcaV v, if_neg hv]
      exact ⟨by omega, rfl⟩

/-- **One expansion turn**: read the slot off the live prefix; on an
undiscovered target, set its level, lay the first-hit mark when within
radius `R`, append it to the queue; advance the slot counter. -/
theorem peelExpandB_spec
    (hNB : N < B) (hsq : N * N + N + 4 < B) (hRB : 2 * R + 2 < B)
    (hca_dd : ca ≠ plDd) (hca_rw : ca ≠ plRw) (hca_re : ca ≠ plRe)
    (hod_ca : od ≠ ca) (hod_dd : od ≠ plDd) (hod_rw : od ≠ plRw)
    (hra_ca : ra ≠ ca) (hra_dd : ra ≠ plDd) (hra_rw : ra ≠ plRw)
    (hao_ca : ao ≠ ca) (hao_dd : ao ≠ plDd) (hao_rw : ao ≠ plRw)
    (haj_ca : aj ≠ ca) (haj_dd : aj ≠ plDd) (haj_rw : aj ≠ plRw)
    (hdg_ca : dg ≠ ca) (hdg_dd : dg ≠ plDd) (hdg_rw : dg ≠ plRw)
    (hmt_ca : mt ≠ ca) (hmt_dd : mt ≠ plDd) (hmt_rw : mt ≠ plRw)
    {offF : ℕ → ℕ} (h0 : offF 0 = 0)
    (hstepF : ∀ v : Fin N, offF ((v : ℕ) + 1) =
      offF ((v : ℕ)) + (G.neighborSet v).ncard)
    {i : ℕ} (hi : i < N) {z : Fin N} :
    Spec B
      (fun σ => EInv ca ra ao aj dg mt od G π R i (π.symm ⟨i, hi⟩) z offF σ ∧
        σ.vars "pl.j" < σ.vars "pl.g")
      (peelExpandB R ca aj)
      (fun σ σ' =>
        EInv ca ra ao aj dg mt od G π R i (π.symm ⟨i, hi⟩) z offF σ' ∧
        σ'.vars "pl.j" = σ.vars "pl.j" + 1 ∧
        (∀ p, p < σ.vars "pl.t" →
          (σ'.arrs plRw).getD p 0 = (σ.arrs plRw).getD p 0) ∧
        σ.vars "pl.t" ≤ σ'.vars "pl.t" ∧
        σ'.vars "pl.g" = σ.vars "pl.g" ∧
        σ'.vars "pl.h" = σ.vars "pl.h" ∧
        (∀ c, (σ'.arrs plDd).getD c 0 = 2 * R + 1 →
          (σ.arrs plDd).getD c 0 = 2 * R + 1))
      40 := by
  rintro σ ⟨⟨hPB, hvz, hvd, hva, hvg, hjle, hdlt, hht0, hfh, hrelax⟩, hjg⟩
  obtain ⟨hvn, hvi, hvu, hvb, hvm, hhl, hht, hcnt, hord, hrank, hadj, hcaL,
    hddL, hrwL, hreL, hreV, hsegs, hanch, hdbd, hach, hqseg, hmono, hreach,
    hpopped, hcaOld, hcaNew⟩ := id hPB
  set u : Fin N := π.symm ⟨i, hi⟩ with hu
  set jj := σ.vars "pl.j" with hjj
  set dz := (σ.arrs plDd).getD ((z : ℕ)) 0 with hdz
  have hzlist : dz ≤ 2 * R := le_of_lt hdlt
  have hach_z : WithinDist (deleteVerts G (peelSet π i)) dz u z := by
    have h := hach ((z : ℕ)) z.isLt (by rw [← hdz]; exact hzlist)
    rw [Fin.eta] at h
    exact h
  have hznp : z ∉ peelSet π i :=
    not_mem_of_withinDist_deleteVerts hach_z (symm_not_peeled π hi)
  -- the slot's target: a live neighbour of z
  obtain ⟨offF', h0', hstepF', haoL', haoV', hajL', hmtL', hdgL',
    hdead', hdeg', hsound', hcomp'⟩ := id hadj
  have hoffeq : ∀ k, k ≤ N → offF' k = offF k :=
    offF_unique h0' h0 hstepF' hstepF
  have hjdg : jj < (σ.arrs dg).getD ((z : ℕ)) 0 := by
    rw [← hvg]
    exact hjg
  have hdgzG : (σ.arrs dg).getD ((z : ℕ)) 0 ≤ (G.neighborSet z).ncard := by
    rw [hdeg' z hznp]
    exact Set.ncard_le_ncard (fun w' hw' => (deleteVerts_le G _) hw')
      (Set.toFinite _)
  obtain ⟨w, hadjw, hAJc, -⟩ := hsound' z hznp jj hjdg
  rw [hoffeq ((z : ℕ)) (le_of_lt z.isLt)] at hAJc
  have hslot : offF ((z : ℕ)) + jj < offF N :=
    slot_lt_of_le hstepF (lt_of_lt_of_le hjdg hdgzG)
  have hajLen : offF N ≤ (σ.arrs aj).length := by
    rw [← hoffeq N le_rfl]
    exact hajL'
  have hwN : (w : ℕ) < N := w.isLt
  have hjN : jj < N :=
    lt_of_lt_of_le (lt_of_lt_of_le hjdg hdgzG) (ncard_neighborSet_le_card z)
  have hddw : (σ.arrs plDd).getD ((w : ℕ)) 0 ≤ 2 * R + 1 :=
    hdbd ((w : ℕ)) hwN
  -- 1. the slot read
  have hr1 : Run B (.assign "pl.w" (.get aj (.add (.var "pl.a") (.var "pl.j"))))
      σ (σ.setVar "pl.w" ((w : ℕ))) 5 := by
    have hoffB : offF ((z : ℕ)) ≤ N * N :=
      le_trans (offF_mono hstepF N le_rfl ((z : ℕ)) (le_of_lt z.isLt))
        (offF_le_sq h0 hstepF)
    have hev : (Expr.add (.var "pl.a") (.var "pl.j")).evalB B σ
        = some (offF ((z : ℕ)) + jj) := by
      have := evalB_bin (B := B) (op := .add) (e := .var "pl.a")
        (f := .var "pl.j") (σ := σ) (evalB_var (by rw [hva]; omega))
        (evalB_var (by rw [← hjj]; omega))
        (by simp only [Bop.apply_add]; rw [hva, ← hjj]; omega)
      rw [hva, ← hjj] at this
      simpa using this
    refine (Run.assign (evalB_get hev
      (getElem?_of_getD (lt_of_lt_of_le hslot hajLen) hAJc) (by omega))).mono
      (by simp)
  set σa := σ.setVar "pl.w" ((w : ℕ)) with hσa
  have haw : σa.vars "pl.w" = (w : ℕ) := by rw [hσa]; simp
  have haarrs : ∀ b', σa.arrs b' = σ.arrs b' := fun b' => by rw [hσa]; simp
  have hacond : (Cond.eq (.get plDd (.var "pl.w")) (.lit (2 * R + 1))).evalB B
      σa = some (((σ.arrs plDd).getD ((w : ℕ)) 0) == (2 * R + 1)) := by
    refine evalB_condEq (evalB_get (k := (w : ℕ))
      (by rw [← haw]; exact evalB_var (by rw [haw]; omega)) ?_ (by omega))
      (evalB_lit (by omega))
    rw [haarrs]
    exact getElem?_of_getD (lt_of_lt_of_le hwN hddL) rfl
  by_cases hdisc : (σ.arrs plDd).getD ((w : ℕ)) 0 = 2 * R + 1
  case neg =>
    -- ===== already discovered: skip, advance the counter =====
    have hcondF : (Cond.eq (.get plDd (.var "pl.w")) (.lit (2 * R + 1))).evalB
        B σa = some false := by
      rw [hacond]
      congr 1
      simpa using hdisc
    have hr2 : Run B (.ite (.eq (.get plDd (.var "pl.w")) (.lit (2 * R + 1)))
        (.seq (.store plDd (.var "pl.w") (.add (.var "pl.d") (.lit 1)))
          (.seq
            (.ite (.lt (.lit R) (.add (.var "pl.d") (.lit 1)))
              .skip
              (.ite (.eq (.get ca (.var "pl.w")) (.var "pl.n"))
                (.store ca (.var "pl.w") (.var "pl.u"))
                .skip))
            (.seq (.store plRw (.var "pl.t") (.var "pl.w"))
              (.assign "pl.t" (.add (.var "pl.t") (.lit 1))))))
        .skip) σa σa 31 :=
      (Run.ite_false hcondF Run.skip).mono (by simp)
    have hr3 : Run B (.assign "pl.j" (.add (.var "pl.j") (.lit 1))) σa
        (σa.setVar "pl.j" (jj + 1)) 4 := by
      have hjB : σa.vars "pl.j" = jj := by rw [hσa]; simp [← hjj]
      have hev := evalB_incr (B := B) (x := "pl.j") (σ := σa) (by
        rw [hjB]
        omega)
      rw [hjB] at hev
      exact (Run.assign hev).mono (by simp)
    set σf := σa.setVar "pl.j" (jj + 1) with hσf
    have hfvars : ∀ y, y ≠ "pl.w" → y ≠ "pl.j" → σf.vars y = σ.vars y := by
      intro y h1 h2
      rw [hσf, hσa]
      simp [h1, h2]
    have hfarrs : ∀ b', σf.arrs b' = σ.arrs b' := fun b' => by
      rw [hσf, hσa]
      simp
    have hwlist : (σ.arrs plDd).getD ((w : ℕ)) 0 ≤ 2 * R := by omega
    refine ⟨σf, (hr1.seq (hr2.seq hr3)).mono (by omega), ⟨?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩, by rw [hσf]; simp [← hjj],
      fun p _ => by rw [hfarrs plRw], le_of_eq (hfvars "pl.t" (by decide)
        (by decide)).symm, hfvars "pl.g" (by decide) (by decide),
      hfvars "pl.h" (by decide) (by decide),
      fun c hc => by rw [hfarrs plDd] at hc; exact hc⟩
    · -- PBfs untouched
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (try simp only [hfarrs]) <;>
        first
          | (rw [hfvars "pl.n" (by decide) (by decide)]; exact hvn)
          | (rw [hfvars "pl.i" (by decide) (by decide)]; exact hvi)
          | (rw [hfvars "pl.u" (by decide) (by decide)]; exact hvu)
          | (rw [hfvars "pl.b" (by decide) (by decide)]; exact hvb)
          | (rw [hfvars "pl.m" (by decide) (by decide)]; exact hvm)
          | (rw [hfvars "pl.h" (by decide) (by decide)]; exact hhl)
          | (rw [hfvars "pl.h" (by decide) (by decide),
              hfvars "pl.t" (by decide) (by decide)]; exact hht)
          | (rw [hfvars "pl.t" (by decide) (by decide)]; exact hcnt)
          | exact ordArr_of_eq hord (hfarrs od)
          | exact rankArr_of_eq hrank (hfarrs ra)
          | exact hadj.of_eq (hfarrs ao) (hfarrs aj) (hfarrs dg) (hfarrs mt)
          | exact hcaL
          | exact hddL
          | exact hrwL
          | exact hreL
          | exact hreV
          | exact hsegs
          | exact hanch
          | exact hdbd
          | exact hach
          | (rw [hfvars "pl.t" (by decide) (by decide)]; exact hqseg)
          | (rw [hfvars "pl.t" (by decide) (by decide)]; exact hmono)
          | (rw [hfvars "pl.h" (by decide) (by decide),
              hfvars "pl.t" (by decide) (by decide)]; exact hreach)
          | (rw [hfvars "pl.h" (by decide) (by decide)]; exact hpopped)
          | exact hcaOld
          | exact hcaNew
    · rw [hfvars "pl.z" (by decide) (by decide)]
      exact hvz
    · rw [hfvars "pl.d" (by decide) (by decide)]
      simp only [hfarrs]
      exact hvd
    · rw [hfvars "pl.a" (by decide) (by decide)]
      exact hva
    · rw [hfvars "pl.g" (by decide) (by decide)]
      simp only [hfarrs]
      exact hvg
    · rw [show σf.vars "pl.j" = jj + 1 from by rw [hσf]; simp,
        hfvars "pl.g" (by decide) (by decide), hvg]
      omega
    · simp only [hfarrs]
      exact hdlt
    · rw [hfvars "pl.h" (by decide) (by decide),
        hfvars "pl.t" (by decide) (by decide)]
      exact hht0
    · rw [hfvars "pl.h" (by decide) (by decide)]
      simp only [hfarrs]
      exact hfh
    · -- the processed prefix grew: the new slot's target is listed
      intro s hs w' hAJ'
      simp only [hfarrs] at hAJ' ⊢
      rw [show σf.vars "pl.j" = jj + 1 from by rw [hσf]; simp] at hs
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | rfl
      · exact hrelax s h w' hAJ'
      · -- slot jj: the target is w, already listed and within reach
        have hval : (w' : ℕ) = (w : ℕ) := by
          rw [← hAJ']
          exact hAJc
        rw [hval]
        obtain ⟨p, hbp, hpt, hfp⟩ := hqseg.2.1 w (by
          simp only [Set.mem_setOf_eq]
          exact hwlist)
        try simp only [] at hfp
        have hrp := hreach hht0 p hbp hpt
        rw [hfp, hfh] at hrp
        exact hrp
  case pos =>
    -- ===== discovery: level, mark, append =====
    set t0 := σ.vars "pl.t" with ht0
    have hwnl : w ∉ {z' : Fin N | (σ.arrs plDd).getD ((z' : ℕ)) 0 ≤ 2 * R} := by
      simp only [Set.mem_setOf_eq, hdisc]
      omega
    have hcntlt :
        {z' : Fin N | (σ.arrs plDd).getD ((z' : ℕ)) 0 ≤ 2 * R}.ncard < N := by
      have hss : {z' : Fin N | (σ.arrs plDd).getD ((z' : ℕ)) 0 ≤ 2 * R}
          ⊂ Set.univ :=
        ⟨Set.subset_univ _, fun hsub => hwnl (hsub (Set.mem_univ w))⟩
      have := Set.ncard_lt_ncard hss (Set.toFinite _)
      simpa [Set.ncard_univ] using this
    have ht0lt : t0 < N * N := by
      have h1 : mval G π R i ≤ i * N := mval_le G π R
      have h3 : (i + 1) * N ≤ N * N := Nat.mul_le_mul_right N hi
      have h4 : i * N + N = (i + 1) * N := by ring
      omega
    have ht0B : t0 < B := by omega
    have hcondT : (Cond.eq (.get plDd (.var "pl.w")) (.lit (2 * R + 1))).evalB
        B σa = some true := by
      rw [hacond]
      congr 1
      simpa using hdisc
    -- a. the level write
    have hadz : σa.vars "pl.d" = dz := by rw [hσa]; simpa using hvd
    have hrb1 : Run B (.store plDd (.var "pl.w") (.add (.var "pl.d") (.lit 1)))
        σa (σa.setArr plDd ((w : ℕ)) (dz + 1)) 5 := by
      have hev : (Expr.add (.var "pl.d") (.lit 1)).evalB B σa
          = some (dz + 1) := by
        have := evalB_bin (B := B) (op := .add) (e := .var "pl.d")
          (f := .lit 1) (σ := σa) (evalB_var (by rw [hadz]; omega))
          (evalB_lit (by omega))
          (by simp only [Bop.apply_add]; rw [hadz]; omega)
        rw [hadz] at this
        simpa using this
      refine (Run.store (by rw [← haw]; exact evalB_var (by rw [haw]; omega))
        hev ?_).mono (by simp)
      rw [haarrs]
      exact lt_of_lt_of_le hwN hddL
    set σb := σa.setArr plDd ((w : ℕ)) (dz + 1) with hσb
    have hbw : σb.vars "pl.w" = (w : ℕ) := by rw [hσb]; simpa using haw
    have hbn : σb.vars "pl.n" = N := by
      rw [hσb, hσa]
      simpa using hvn
    have hbu : σb.vars "pl.u" = (u : ℕ) := by
      rw [hσb, hσa]
      simpa using hvu
    have hbca : σb.arrs ca = σ.arrs ca := by
      rw [hσb]
      simp only [arrs_setArr, if_neg hca_dd]
      exact haarrs ca
    -- b. the mark, joined over its two idle branches
    have hmark_join : ∀ σc : Env,
        Run B (.ite (.lt (.lit R) (.add (.var "pl.d") (.lit 1)))
          .skip
          (.ite (.eq (.get ca (.var "pl.w")) (.var "pl.n"))
            (.store ca (.var "pl.w") (.var "pl.u"))
            .skip)) σb σc 14 →
        (∀ b', b' ≠ ca → σc.arrs b' = σb.arrs b') →
        σc.vars = σb.vars →
        (∀ v : Fin N, v ≠ w →
          (σc.arrs ca).getD ((v : ℕ)) 0 = (σ.arrs ca).getD ((v : ℕ)) 0) →
        (σc.arrs ca).length = (σ.arrs ca).length →
        (dz + 1 ≤ R → ¬ ((π (pctr G π R w) : ℕ)) < i →
          (σc.arrs ca).getD ((w : ℕ)) 0 = (u : ℕ)) →
        ((R < dz + 1 ∨ ((π (pctr G π R w) : ℕ)) < i) →
          (σc.arrs ca).getD ((w : ℕ)) 0 = (σ.arrs ca).getD ((w : ℕ)) 0) →
        ∃ σ', Run B (peelExpandB R ca aj) σ σ' 40 ∧
          (EInv ca ra ao aj dg mt od G π R i u z offF σ' ∧
            σ'.vars "pl.j" = σ.vars "pl.j" + 1 ∧
            (∀ p, p < σ.vars "pl.t" →
              (σ'.arrs plRw).getD p 0 = (σ.arrs plRw).getD p 0) ∧
            σ.vars "pl.t" ≤ σ'.vars "pl.t" ∧
            σ'.vars "pl.g" = σ.vars "pl.g" ∧
            σ'.vars "pl.h" = σ.vars "pl.h" ∧
            (∀ c, (σ'.arrs plDd).getD c 0 = 2 * R + 1 →
              (σ.arrs plDd).getD c 0 = 2 * R + 1)) := by
      intro σc hrc hcother hcvars hcne hclen hcmark hckeep
      -- c. the append
      have hct : σc.vars "pl.t" = t0 := by
        rw [hcvars, hσb, hσa]
        simp [← ht0]
      have hcw : σc.vars "pl.w" = (w : ℕ) := by rw [hcvars]; exact hbw
      have hcrw : σc.arrs plRw = σ.arrs plRw := by
        rw [hcother plRw (Ne.symm hca_rw), hσb]
        simp only [arrs_setArr, if_neg (show plRw ≠ plDd by decide)]
        exact haarrs plRw
      have hrc1 : Run B (.store plRw (.var "pl.t") (.var "pl.w")) σc
          (σc.setArr plRw t0 ((w : ℕ))) 3 := by
        refine (Run.store (by rw [← hct]; exact evalB_var (by rw [hct]; omega))
          (by rw [← hcw]; exact evalB_var (by rw [hcw]; omega)) ?_).mono
          (by simp)
        rw [hcrw]
        exact lt_of_lt_of_le ht0lt hrwL
      set σd := σc.setArr plRw t0 ((w : ℕ)) with hσd
      have hdt : σd.vars "pl.t" = t0 := by rw [hσd]; simpa using hct
      have hrc2 : Run B (.assign "pl.t" (.add (.var "pl.t") (.lit 1))) σd
          (σd.setVar "pl.t" (t0 + 1)) 4 := by
        have hev := evalB_incr (B := B) (x := "pl.t") (σ := σd)
          (by rw [hdt]; omega)
        rw [hdt] at hev
        exact (Run.assign hev).mono (by simp)
      set σe := σd.setVar "pl.t" (t0 + 1) with hσe
      -- d. the counter
      have hej : σe.vars "pl.j" = jj := by
        rw [hσe, hσd]
        simp only [vars_setVar, vars_setArr,
          if_neg (show ¬("pl.j" = "pl.t") by decide)]
        rw [hcvars, hσb, hσa]
        simp [← hjj]
      have hrc3 : Run B (.assign "pl.j" (.add (.var "pl.j") (.lit 1))) σe
          (σe.setVar "pl.j" (jj + 1)) 4 := by
        have hev := evalB_incr (B := B) (x := "pl.j") (σ := σe) (by
          rw [hej]
          omega)
        rw [hej] at hev
        exact (Run.assign hev).mono (by simp)
      set σf := σe.setVar "pl.j" (jj + 1) with hσf
      -- the final environment's projections
      have hfvars : ∀ y, y ≠ "pl.w" → y ≠ "pl.t" → y ≠ "pl.j" →
          σf.vars y = σ.vars y := by
        intro y h1 h2 h3
        rw [hσf, hσe]
        simp only [vars_setVar, if_neg h3, if_neg h2]
        rw [hσd]
        simp only [vars_setArr]
        rw [hcvars, hσb]
        simp only [vars_setArr]
        rw [hσa]
        simp [h1]
      have hft : σf.vars "pl.t" = t0 + 1 := by
        rw [hσf, hσe]
        simp
      have hfj : σf.vars "pl.j" = jj + 1 := by rw [hσf]; simp
      have hfarrs : ∀ b', b' ≠ ca → b' ≠ plDd → b' ≠ plRw →
          σf.arrs b' = σ.arrs b' := by
        intro b' h1 h2 h3
        rw [hσf, hσe]
        simp only [arrs_setVar]
        rw [hσd]
        simp only [arrs_setArr, if_neg h3]
        rw [hcother b' h1, hσb]
        simp only [arrs_setArr, if_neg h2]
        exact haarrs b'
      have hfdd : σf.arrs plDd = (σ.arrs plDd).set ((w : ℕ)) (dz + 1) := by
        rw [hσf, hσe]
        simp only [arrs_setVar]
        rw [hσd]
        simp only [arrs_setArr, if_neg (show plDd ≠ plRw by decide)]
        rw [hcother plDd (Ne.symm hca_dd), hσb]
        simp only [arrs_setArr, if_pos rfl, if_true]
        rw [haarrs plDd]
      have hfddD : ∀ c, (σf.arrs plDd).getD c 0 =
          if c = (w : ℕ) then dz + 1 else (σ.arrs plDd).getD c 0 := by
        intro c
        rw [hfdd, getD_set _ _ _ (lt_of_lt_of_le hwN hddL)]
      have hfrw : σf.arrs plRw = (σ.arrs plRw).set t0 ((w : ℕ)) := by
        rw [hσf, hσe]
        simp only [arrs_setVar]
        rw [hσd]
        simp only [arrs_setArr, if_pos rfl, if_true]
        rw [hcrw]
      have hfrwD : ∀ c, (σf.arrs plRw).getD c 0 =
          if c = t0 then ((w : ℕ)) else (σ.arrs plRw).getD c 0 := by
        intro c
        rw [hfrw, getD_set _ _ _ (lt_of_lt_of_le ht0lt hrwL)]
      have hfca : σf.arrs ca = σc.arrs ca := by
        rw [hσf, hσe]
        simp only [arrs_setVar]
        rw [hσd]
        simp only [arrs_setArr, if_neg hca_rw]
      -- the discovered set grew by exactly `w`
      have hsetins : {z' : Fin N | (σf.arrs plDd).getD ((z' : ℕ)) 0 ≤ 2 * R}
          = insert w {z' : Fin N | (σ.arrs plDd).getD ((z' : ℕ)) 0 ≤ 2 * R}
          := by
        ext z'
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
        rw [hfddD]
        by_cases hz' : (z' : ℕ) = (w : ℕ)
        · rw [if_pos hz']
          constructor
          · intro _
            exact Or.inl (Fin.ext hz')
          · intro _
            omega
        · rw [if_neg hz']
          constructor
          · intro h
            exact Or.inr h
          · intro h
            rcases h with h | h
            · exact absurd (congrArg Fin.val h) hz'
            · exact h
      have hwdd_ne : ∀ z' : Fin N,
          (σ.arrs plDd).getD ((z' : ℕ)) 0 ≤ 2 * R → (z' : ℕ) ≠ (w : ℕ) := by
        intro z' hz' hc
        rw [hc, hdisc] at hz'
        omega
      have hachw : WithinDist (deleteVerts G (peelSet π i)) (dz + 1) u w := by
        have h1 := withinDist_trans hach_z (withinDist_of_adj hadjw)
        simpa using h1
      -- assemble
      refine ⟨σf, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by
        rw [hfj, ← hjj], fun p hp => by rw [hfrwD, if_neg (by rw [← ht0] at hp; omega)],
        by rw [hft, ← ht0]; omega, hfvars "pl.g" (by decide) (by decide) (by decide),
        hfvars "pl.h" (by decide) (by decide) (by decide),
        fun c hc => by
          rw [hfddD] at hc
          by_cases hcw : c = (w : ℕ)
          · rw [if_pos hcw] at hc
            omega
          · rw [if_neg hcw] at hc
            exact hc⟩
      · -- the run
        have hite : Run B (.ite (.eq (.get plDd (.var "pl.w"))
            (.lit (2 * R + 1)))
            (.seq (.store plDd (.var "pl.w") (.add (.var "pl.d") (.lit 1)))
              (.seq
                (.ite (.lt (.lit R) (.add (.var "pl.d") (.lit 1)))
                  .skip
                  (.ite (.eq (.get ca (.var "pl.w")) (.var "pl.n"))
                    (.store ca (.var "pl.w") (.var "pl.u"))
                    .skip))
                (.seq (.store plRw (.var "pl.t") (.var "pl.w"))
                  (.assign "pl.t" (.add (.var "pl.t") (.lit 1))))))
            .skip) σa σe 31 := by
          refine (Run.ite_true hcondT (hrb1.seq (hrc.seq (hrc1.seq
            hrc2)))).mono ?_
          simp
        exact ((hr1.seq (hite.seq hrc3))).mono (by simp)
      · -- PBfs
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hfvars "pl.n" (by decide) (by decide) (by decide)]
          exact hvn
        · rw [hfvars "pl.i" (by decide) (by decide) (by decide)]
          exact hvi
        · rw [hfvars "pl.u" (by decide) (by decide) (by decide)]
          exact hvu
        · rw [hfvars "pl.b" (by decide) (by decide) (by decide)]
          exact hvb
        · rw [hfvars "pl.m" (by decide) (by decide) (by decide)]
          exact hvm
        · rw [hfvars "pl.h" (by decide) (by decide) (by decide)]
          exact hhl
        · rw [hfvars "pl.h" (by decide) (by decide) (by decide), hft]
          omega
        · rw [hft, hsetins,
            Set.ncard_insert_of_notMem hwnl (Set.toFinite _), hcnt]
          ring
        · exact ordArr_of_eq hord (hfarrs od hod_ca hod_dd hod_rw)
        · exact rankArr_of_eq hrank (hfarrs ra hra_ca hra_dd hra_rw)
        · exact hadj.of_eq (hfarrs ao hao_ca hao_dd hao_rw)
            (hfarrs aj haj_ca haj_dd haj_rw) (hfarrs dg hdg_ca hdg_dd hdg_rw)
            (hfarrs mt hmt_ca hmt_dd hmt_rw)
        · rw [hfca, hclen]
          exact hcaL
        · rw [hfdd, List.length_set]
          exact hddL
        · rw [hfrw, List.length_set]
          exact hrwL
        · rw [hfarrs plRe (Ne.symm hca_re) (by decide) (by decide)]
          exact hreL
        · intro i' hi'
          rw [hfarrs plRe (Ne.symm hca_re) (by decide) (by decide)]
          exact hreV i' hi'
        · -- prior segments: below the write
          intro i' hi'
          refine SegAt.congr (hsegs i' hi') ?_
          intro p hbp hpe
          try simp only []
          rw [hfrwD, if_neg ?_]
          have hlt : p < mval G π R i :=
            lt_of_lt_of_le hpe (mval_mono G π R hi')
          omega
        · -- anchor: the source is not the discovered vertex
          rw [hfddD, if_neg (fun hc => by
            rw [← hc] at hdisc
            rw [hanch] at hdisc
            omega)]
          exact hanch
        · intro z' hz'
          rw [hfddD]
          by_cases hzw : z' = (w : ℕ)
          · rw [if_pos hzw]
            omega
          · rw [if_neg hzw]
            exact hdbd z' hz'
        · -- achieved
          intro z' hz' hle
          rw [hfddD] at hle ⊢
          by_cases hzw : z' = (w : ℕ)
          · rw [if_pos hzw] at hle ⊢
            have : (⟨z', hz'⟩ : Fin N) = w := Fin.ext hzw
            rw [this]
            exact hachw
          · rw [if_neg hzw] at hle ⊢
            exact hach z' hz' hle
        · -- the queue segment gains `w` at its end
          rw [hft, hsetins]
          obtain ⟨hqs, hqc, hqi⟩ := id hqseg
          have hvalt : (σf.arrs plRw).getD t0 0 = (w : ℕ) := by
            rw [hfrwD, if_pos rfl]
          have hvalo : ∀ p', p' ≠ t0 →
              (σf.arrs plRw).getD p' 0 = (σ.arrs plRw).getD p' 0 := by
            intro p' hp'
            rw [hfrwD, if_neg hp']
          refine ⟨?_, ?_, ?_⟩
          · intro p hbp hpe
            by_cases hpt : p = t0
            · subst hpt
              simp only [hvalt]
              exact ⟨hwN, Set.mem_insert w _⟩
            · simp only [hvalo p hpt]
              obtain ⟨hz, hmem⟩ := hqs p hbp (by omega)
              exact ⟨hz, Set.mem_insert_of_mem w hmem⟩
          · intro z' hz'
            rcases Set.mem_insert_iff.mp hz' with rfl | hz'
            · exact ⟨t0, le_trans hhl hht, by omega, by simp only [hvalt]⟩
            · obtain ⟨p, hbp, hpt, hfp⟩ := hqc z' hz'
              refine ⟨p, hbp, by omega, ?_⟩
              simp only [hvalo p (by omega)]
              exact hfp
          · intro p q hbp hpe hbq hqe hpq
            simp only [] at hpq
            by_cases hpt : p = t0 <;> by_cases hqt : q = t0
            · rw [hpt, hqt]
            · subst hpt
              rw [hvalt, hvalo q hqt] at hpq
              obtain ⟨hz, hmem⟩ := hqs q hbq (by omega)
              exact absurd hpq.symm (hwdd_ne ⟨_, hz⟩ hmem)
            · subst hqt
              rw [hvalt, hvalo p hpt] at hpq
              obtain ⟨hz, hmem⟩ := hqs p hbp (by omega)
              exact absurd hpq (hwdd_ne ⟨_, hz⟩ hmem)
            · rw [hvalo p hpt, hvalo q hqt] at hpq
              exact hqi p q hbp (by omega) hbq (by omega) hpq
        · -- levels stay monotone along the stream
          intro p q hbp hpq hqt
          rw [hft] at hqt
          have hvalt : (σf.arrs plRw).getD t0 0 = (w : ℕ) := by
            rw [hfrwD, if_pos rfl]
          have hvalo : ∀ p', p' ≠ t0 →
              (σf.arrs plRw).getD p' 0 = (σ.arrs plRw).getD p' 0 := by
            intro p' hp'
            rw [hfrwD, if_neg hp']
          have hddo : ∀ (c : ℕ), c < N → (σ.arrs plDd).getD c 0 ≤ 2 * R →
              (σf.arrs plDd).getD c 0 = (σ.arrs plDd).getD c 0 := by
            intro c hc hcl
            rw [hfddD, if_neg (hwdd_ne ⟨c, hc⟩ hcl)]
          have hwv : (σf.arrs plDd).getD ((w : ℕ)) 0 = dz + 1 := by
            rw [hfddD, if_pos rfl]
          by_cases hqt0 : q = t0
          · subst hqt0
            rw [hvalt, hwv]
            by_cases hpt0 : p = t0
            · subst hpt0
              rw [hvalt, hwv]
            · have hplt : p < t0 := by omega
              obtain ⟨hz, hmem⟩ := hqseg.1 p hbp hplt
              rw [hvalo p hpt0, hddo _ hz hmem]
              have hr := hreach hht0 p hbp hplt
              rw [hfh] at hr
              omega
          · have hqlt : q < t0 := by omega
            have hplt : p < t0 := by omega
            obtain ⟨hzp, hmemp⟩ := hqseg.1 p hbp hplt
            obtain ⟨hzq, hmemq⟩ := hqseg.1 q (le_trans hbp hpq) hqlt
            rw [hvalo p (by omega), hvalo q (by omega),
              hddo _ hzp hmemp, hddo _ hzq hmemq]
            exact hmono p q hbp hpq hqlt
        · -- the window stays within one level of its head
          intro hht' p hbp hpt
          rw [hft] at hpt
          rw [hfvars "pl.h" (by decide) (by decide) (by decide)] at hht' ⊢
          have hvalt : (σf.arrs plRw).getD t0 0 = (w : ℕ) := by
            rw [hfrwD, if_pos rfl]
          have hvalo : ∀ p', p' ≠ t0 →
              (σf.arrs plRw).getD p' 0 = (σ.arrs plRw).getD p' 0 := by
            intro p' hp'
            rw [hfrwD, if_neg hp']
          have hddo : ∀ (c : ℕ), c < N → (σ.arrs plDd).getD c 0 ≤ 2 * R →
              (σf.arrs plDd).getD c 0 = (σ.arrs plDd).getD c 0 := by
            intro c hc hcl
            rw [hfddD, if_neg (hwdd_ne ⟨c, hc⟩ hcl)]
          have hwv : (σf.arrs plDd).getD ((w : ℕ)) 0 = dz + 1 := by
            rw [hfddD, if_pos rfl]
          have hvalh : (σf.arrs plRw).getD (σ.vars "pl.h") 0 = (z : ℕ) := by
            rw [hvalo _ (by omega)]
            exact hfh
          rw [hvalh, hddo _ z.isLt (by rw [← hdz]; exact hzlist), ← hdz]
          by_cases hpt0 : p = t0
          · subst hpt0
            rw [hvalt, hwv]
          · have hplt : p < t0 := by omega
            obtain ⟨hzp, hmemp⟩ := hqseg.1 p hbp hplt
            rw [hvalo p hpt0, hddo _ hzp hmemp]
            have hr := hreach hht0 p hbp hplt
            rw [hfh] at hr
            exact hr
        · -- the popped prefix stays relaxed
          intro p hbp hph hp hlt w' hadj'
          rw [hfvars "pl.h" (by decide) (by decide) (by decide)] at hph
          have hplt : p < t0 := lt_of_lt_of_le hph hht
          have hvalo : (σf.arrs plRw).getD p 0 = (σ.arrs plRw).getD p 0 := by
            rw [hfrwD, if_neg (by omega)]
          have hp' : (σ.arrs plRw).getD p 0 < N := by
            rw [← hvalo]
            exact hp
          have hFin : (⟨(σf.arrs plRw).getD p 0, hp⟩ : Fin N)
              = ⟨(σ.arrs plRw).getD p 0, hp'⟩ := Fin.ext hvalo
          rw [hFin] at hadj'
          obtain ⟨hzp, hmemp⟩ := hqseg.1 p hbp hplt
          have hddp : (σf.arrs plDd).getD ((σ.arrs plRw).getD p 0) 0
              = (σ.arrs plDd).getD ((σ.arrs plRw).getD p 0) 0 := by
            rw [hfddD, if_neg (hwdd_ne ⟨_, hzp⟩ hmemp)]
          rw [hvalo, hddp] at hlt ⊢
          have hold := hpopped p hbp hph hp' hlt w' hadj'
          rw [hfddD]
          by_cases hw' : (w' : ℕ) = (w : ℕ)
          · rw [if_pos hw']
            rw [hw', hdisc] at hold
            omega
          · rw [if_neg hw']
            exact hold
        · -- earlier marks untouched
          intro v hv
          rw [hfca]
          by_cases hvw : v = w
          · subst hvw
            rw [hckeep (Or.inr hv)]
            exact hcaOld v hv
          · rw [hcne v hvw]
            exact hcaOld v hv
        · -- fresh marks
          intro v hv
          rw [hfca, hfddD]
          by_cases hvw : v = w
          · subst hvw
            rw [if_pos rfl]
            by_cases hmk : dz + 1 ≤ R
            · left
              exact ⟨hmk, hcmark hmk hv⟩
            · right
              refine ⟨by omega, ?_⟩
              rw [hckeep (Or.inl (by omega))]
              rcases hcaNew v hv with ⟨hd, -⟩ | ⟨-, hc⟩
              · exact absurd hd (by rw [hdisc]; omega)
              · exact hc
          · rw [if_neg (fun hc => hvw (Fin.ext hc)), hcne v hvw]
            exact hcaNew v hv
      · rw [hfvars "pl.z" (by decide) (by decide) (by decide)]
        exact hvz
      · rw [hfvars "pl.d" (by decide) (by decide) (by decide), hfddD,
          if_neg (hwdd_ne z (by rw [← hdz]; exact hzlist))]
        exact hvd
      · rw [hfvars "pl.a" (by decide) (by decide) (by decide)]
        exact hva
      · rw [hfvars "pl.g" (by decide) (by decide) (by decide),
          hfarrs dg hdg_ca hdg_dd hdg_rw]
        exact hvg
      · rw [hfj, hfvars "pl.g" (by decide) (by decide) (by decide), hvg]
        omega
      · rw [hfddD, if_neg (hwdd_ne z (by rw [← hdz]; exact hzlist))]
        exact hdlt
      · rw [hfvars "pl.h" (by decide) (by decide) (by decide), hft]
        omega
      · rw [hfvars "pl.h" (by decide) (by decide) (by decide)]
        rw [hfrwD, if_neg (by omega : ¬ (σ.vars "pl.h" = t0))]
        exact hfh
      · -- the processed prefix grew
        intro s hs w' hAJ'
        rw [hfj] at hs
        rw [hfarrs aj haj_ca haj_dd haj_rw] at hAJ'
        have hddz : (σf.arrs plDd).getD ((z : ℕ)) 0 = dz := by
          rw [hfddD, if_neg (hwdd_ne z (by rw [← hdz]; exact hzlist)), ← hdz]
        rw [hddz]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | rfl
        · have hold := hrelax s h w' hAJ'
          rw [hfddD]
          by_cases hw' : (w' : ℕ) = (w : ℕ)
          · rw [if_pos hw']
          · rw [if_neg hw']
            exact hold
        · have hval : (w' : ℕ) = (w : ℕ) := by
            rw [← hAJ']
            exact hAJc
          rw [hfddD, if_pos hval]
    -- discharge the join: the two mark branches
    have hbd : σb.vars "pl.d" = dz := by rw [hσb]; simpa using hadz
    have hmkEv : (Cond.lt (.lit R) (.add (.var "pl.d") (.lit 1))).evalB B σb
        = some (decide (R < dz + 1)) := by
      have hev : (Expr.add (.var "pl.d") (.lit 1)).evalB B σb
          = some (dz + 1) := by
        have := evalB_bin (B := B) (op := .add) (e := .var "pl.d")
          (f := .lit 1) (σ := σb) (evalB_var (by rw [hbd]; omega))
          (evalB_lit (by omega))
          (by simp only [Bop.apply_add]; rw [hbd]; omega)
        rw [hbd] at this
        simpa using this
      exact evalB_condLt (evalB_lit (by omega)) hev
    by_cases hmk : R < dz + 1
    · -- beyond the mark radius: skip
      have hmkT : (Cond.lt (.lit R) (.add (.var "pl.d") (.lit 1))).evalB B σb
          = some true := by
        rw [hmkEv]
        congr 1
        simpa using hmk
      have hrmark : Run B (.ite (.lt (.lit R) (.add (.var "pl.d") (.lit 1)))
          .skip
          (.ite (.eq (.get ca (.var "pl.w")) (.var "pl.n"))
            (.store ca (.var "pl.w") (.var "pl.u"))
            .skip)) σb σb 14 :=
        (Run.ite_true hmkT Run.skip).mono (by simp)
      exact hmark_join σb hrmark
        (fun _ _ => rfl) rfl
        (fun v hv => by rw [hbca]) (by rw [hbca])
        (fun hc _ => absurd hmk (by omega)) (fun _ => by rw [hbca])
    · -- within radius: the first-hit test
      have hmkF : (Cond.lt (.lit R) (.add (.var "pl.d") (.lit 1))).evalB B σb
          = some false := by
        rw [hmkEv]
        congr 1
        simpa using hmk
      have hcaw : (σb.arrs ca).getD ((w : ℕ)) 0 = (σ.arrs ca).getD ((w : ℕ)) 0
          := by rw [hbca]
      have hcondEv2 : (Cond.eq (.get ca (.var "pl.w")) (.var "pl.n")).evalB B
          σb = some (((σ.arrs ca).getD ((w : ℕ)) 0) == N) := by
        refine evalB_condEq (evalB_get (k := (w : ℕ))
          (by rw [← hbw]; exact evalB_var (by rw [hbw]; omega)) ?_ ?_)
          (by rw [← hbn]; exact evalB_var (by rw [hbn]; omega))
        · rw [hbca]
          exact getElem?_of_getD (lt_of_lt_of_le hwN hcaL) rfl
        · by_cases hwm : ((π (pctr G π R w) : ℕ)) < i
          · rw [hcaOld w hwm]
            exact lt_trans (pctr G π R w).isLt (by omega)
          · rcases hcaNew w hwm with ⟨hd, -⟩ | ⟨-, hc⟩
            · exact absurd hd (by rw [hdisc]; omega)
            · rw [hc]
              omega
      by_cases hwm : ((π (pctr G π R w) : ℕ)) < i
      · -- already assigned: the cell holds its centre, not the sentinel
        have hne : (σ.arrs ca).getD ((w : ℕ)) 0 ≠ N := by
          rw [hcaOld w hwm]
          exact Nat.ne_of_lt (pctr G π R w).isLt
        have hcF : (Cond.eq (.get ca (.var "pl.w")) (.var "pl.n")).evalB B σb
            = some false := by
          rw [hcondEv2]
          congr 1
          simpa using hne
        have hrmark : Run B (.ite (.lt (.lit R) (.add (.var "pl.d") (.lit 1)))
            .skip
            (.ite (.eq (.get ca (.var "pl.w")) (.var "pl.n"))
              (.store ca (.var "pl.w") (.var "pl.u"))
              .skip)) σb σb 14 :=
          (Run.ite_false hmkF (Run.ite_false hcF Run.skip)).mono (by simp)
        exact hmark_join σb hrmark
          (fun _ _ => rfl) rfl (fun v hv => by rw [hbca]) (by rw [hbca])
          (fun _ hc => absurd hwm hc) (fun _ => by rw [hbca])
      · -- unassigned: lay the mark
        have heqN : (σ.arrs ca).getD ((w : ℕ)) 0 = N := by
          rcases hcaNew w hwm with ⟨hd, -⟩ | ⟨-, hc⟩
          · exact absurd hd (by rw [hdisc]; omega)
          · exact hc
        have hcT : (Cond.eq (.get ca (.var "pl.w")) (.var "pl.n")).evalB B σb
            = some true := by
          rw [hcondEv2]
          congr 1
          simpa using heqN
        have hstca : Run B (.store ca (.var "pl.w") (.var "pl.u")) σb
            (σb.setArr ca ((w : ℕ)) ((u : ℕ))) 3 := by
          refine (Run.store
            (by rw [← hbw]; exact evalB_var (by rw [hbw]; omega))
            (by rw [← hbu]; exact evalB_var (by rw [hbu]; omega)) ?_).mono
            (by simp)
          rw [hbca]
          exact lt_of_lt_of_le hwN hcaL
        have hrmark : Run B (.ite (.lt (.lit R) (.add (.var "pl.d") (.lit 1)))
            .skip
            (.ite (.eq (.get ca (.var "pl.w")) (.var "pl.n"))
              (.store ca (.var "pl.w") (.var "pl.u"))
              .skip)) σb (σb.setArr ca ((w : ℕ)) ((u : ℕ))) 14 :=
          (Run.ite_false hmkF (Run.ite_true hcT hstca)).mono (by simp)
        refine hmark_join (σb.setArr ca ((w : ℕ)) ((u : ℕ))) hrmark
          (fun b' hb' => by simp only [arrs_setArr, if_neg hb']) rfl
          (fun v hv => by
            simp only [arrs_setArr, if_pos rfl, if_true]
            rw [getD_set _ _ _ (lt_of_lt_of_le hwN (by rw [hbca]; exact hcaL)),
              if_neg (fun hc => hv (Fin.ext hc)), hbca])
          (by simp only [arrs_setArr, if_pos rfl, if_true, List.length_set]
              rw [hbca])
          (fun _ _ => by
            simp only [arrs_setArr, if_pos rfl, if_true]
            rw [getD_set _ _ _ (lt_of_lt_of_le hwN (by rw [hbca]; exact hcaL)),
              if_pos rfl])
          (fun hor => by
            rcases hor with h | h
            · exact absurd h (by omega)
            · exact absurd h hwm)

/-- The cached row length is bounded by the carrier. -/
theorem EInv_g_le {i : ℕ} {u z : Fin N} {offF : ℕ → ℕ} {σ : Env}
    (hI : EInv ca ra ao aj dg mt od G π R i u z offF σ)
    (hu : u ∉ peelSet π i) :
    σ.vars "pl.g" ≤ N := by
  obtain ⟨hPB, hvz, hvd, hva, hvg, hjle, hdlt, hht0, hfh, hrelax⟩ := hI
  obtain ⟨hvn, hvi, hvu, hvb, hvm, hhl, hht, hcnt, hord, hrank, hadj, hcaL,
    hddL, hrwL, hreL, hreV, hsegs, hanch, hdbd, hach, hqseg, hmono, hreach,
    hpopped, hcaOld, hcaNew⟩ := hPB
  have hach_z : WithinDist (deleteVerts G (peelSet π i))
      ((σ.arrs plDd).getD ((z : ℕ)) 0) u z := by
    have h := hach ((z : ℕ)) z.isLt (le_of_lt hdlt)
    rw [Fin.eta] at h
    exact h
  have hznp : z ∉ peelSet π i :=
    not_mem_of_withinDist_deleteVerts hach_z hu
  obtain ⟨offF', -, -, -, -, -, -, -, -, hdeg', -, -⟩ := hadj
  rw [hvg, hdeg' z hznp]
  refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
    (ncard_neighborSet_le_card (H := G) z)
  intro w' hw'
  exact (deleteVerts_le G _) hw'

/-- **The expansion loop**: run the live prefix to its end.  Fuel
induction, carrying the stream stability the queue potential's
bookkeeping reads. -/
theorem peelExpand_loop
    (hNB : N < B) (hsq : N * N + N + 4 < B) (hRB : 2 * R + 2 < B)
    (hca_dd : ca ≠ plDd) (hca_rw : ca ≠ plRw) (hca_re : ca ≠ plRe)
    (hod_ca : od ≠ ca) (hod_dd : od ≠ plDd) (hod_rw : od ≠ plRw)
    (hra_ca : ra ≠ ca) (hra_dd : ra ≠ plDd) (hra_rw : ra ≠ plRw)
    (hao_ca : ao ≠ ca) (hao_dd : ao ≠ plDd) (hao_rw : ao ≠ plRw)
    (haj_ca : aj ≠ ca) (haj_dd : aj ≠ plDd) (haj_rw : aj ≠ plRw)
    (hdg_ca : dg ≠ ca) (hdg_dd : dg ≠ plDd) (hdg_rw : dg ≠ plRw)
    (hmt_ca : mt ≠ ca) (hmt_dd : mt ≠ plDd) (hmt_rw : mt ≠ plRw)
    {offF : ℕ → ℕ} (h0 : offF 0 = 0)
    (hstepF : ∀ v : Fin N, offF ((v : ℕ) + 1) =
      offF ((v : ℕ)) + (G.neighborSet v).ncard)
    {i : ℕ} (hi : i < N) {z : Fin N} :
    ∀ (fuel : ℕ) (σ : Env),
      EInv ca ra ao aj dg mt od G π R i (π.symm ⟨i, hi⟩) z offF σ →
      σ.vars "pl.g" - σ.vars "pl.j" = fuel →
      ∃ σ', Run B (.while (.lt (.var "pl.j") (.var "pl.g"))
          (peelExpandB R ca aj)) σ σ' (44 * fuel + 4) ∧
        EInv ca ra ao aj dg mt od G π R i (π.symm ⟨i, hi⟩) z offF σ' ∧
        σ'.vars "pl.j" = σ'.vars "pl.g" ∧
        (∀ p, p < σ.vars "pl.t" →
          (σ'.arrs plRw).getD p 0 = (σ.arrs plRw).getD p 0) ∧
        σ.vars "pl.t" ≤ σ'.vars "pl.t" ∧
        σ'.vars "pl.g" = σ.vars "pl.g" ∧
        σ'.vars "pl.h" = σ.vars "pl.h" ∧
        (∀ c, (σ'.arrs plDd).getD c 0 = 2 * R + 1 →
          (σ.arrs plDd).getD c 0 = 2 * R + 1) := by
  intro fuel
  induction fuel with
  | zero =>
      intro σ hI hf
      have hgN : σ.vars "pl.g" ≤ N := EInv_g_le hI (symm_not_peeled π hi)
      have hjle : σ.vars "pl.j" ≤ σ.vars "pl.g" := hI.2.2.2.2.2.1
      have hjg : σ.vars "pl.j" = σ.vars "pl.g" := by omega
      have hcondF : (Cond.lt (.var "pl.j") (.var "pl.g")).evalB B σ
          = some false := by
        rw [evalB_condLt (evalB_var (by omega)) (evalB_var (by omega))]
        congr 1
        simp [hjg]
      exact ⟨σ, (Run.while_false hcondF).mono (by simp), hI, hjg,
        fun _ _ => rfl, le_rfl, rfl, rfl, fun _ hc => hc⟩
  | succ n ih =>
      intro σ hI hf
      have hgN : σ.vars "pl.g" ≤ N := EInv_g_le hI (symm_not_peeled π hi)
      have hjlt : σ.vars "pl.j" < σ.vars "pl.g" := by omega
      have hcondT : (Cond.lt (.var "pl.j") (.var "pl.g")).evalB B σ
          = some true := by
        rw [evalB_condLt (evalB_var (by omega)) (evalB_var (by omega))]
        congr 1
        simp [hjlt]
      obtain ⟨σ₁, hr1, hI₁, hj₁, hstab₁, hmono₁, hg₁, hh₁, hsen₁⟩ :=
        (peelExpandB_spec hNB hsq hRB hca_dd hca_rw hca_re hod_ca hod_dd
          hod_rw hra_ca hra_dd hra_rw hao_ca hao_dd hao_rw haj_ca haj_dd
          haj_rw hdg_ca hdg_dd hdg_rw hmt_ca hmt_dd hmt_rw h0 hstepF hi).run
          ⟨hI, hjlt⟩
      obtain ⟨σ', hr', hI', hjg', hstab', hmono', hg', hh', hsen'⟩ :=
        ih σ₁ hI₁ (by rw [hg₁, hj₁]; omega)
      refine ⟨σ', ?_, hI', hjg', ?_, le_trans hmono₁ hmono',
        by rw [hg', hg₁], by rw [hh', hh₁], fun c hc => hsen₁ c (hsen' c hc)⟩
      · obtain ⟨k1, hk1, hb1⟩ := hr1
        obtain ⟨k', hk', hb'⟩ := hr'
        refine ⟨1 + 3 + k1 + k', by omega, ?_⟩
        have hsize : (Cond.lt (Expr.var "pl.j") (Expr.var "pl.g")).size = 3 :=
          by simp
        rw [show (1 + 3 + k1 + k' : ℕ)
          = 1 + (Cond.lt (Expr.var "pl.j") (Expr.var "pl.g")).size + k1 + k'
          from by rw [hsize]]
        exact .while_true hcondT hb1 hb'
      · intro p hp
        rw [hstab' p (lt_of_lt_of_le hp hmono₁), hstab₁ p hp]

/-- `PBfs` transports along agreement on its cells and arrays. -/
theorem pbfs_of_eq {i : ℕ} {u : Fin N} {σ σ' : Env}
    (h : PBfs ca ra ao aj dg mt od G π R i u σ)
    (hv : ∀ y, y ∈ (["pl.n", "pl.i", "pl.u", "pl.b", "pl.m", "pl.h",
      "pl.t"] : List String) → σ'.vars y = σ.vars y)
    (ha : ∀ b', σ'.arrs b' = σ.arrs b') :
    PBfs ca ra ao aj dg mt od G π R i u σ' := by
  have harrs : σ'.arrs = σ.arrs := funext ha
  obtain ⟨hvn, hvi, hvu, hvb, hvm, hhl, hht, hcnt, hord, hrank, hadj, hcaL,
    hddL, hrwL, hreL, hreV, hsegs, hanch, hdbd, hach, hqseg, hmono, hreach,
    hpopped, hcaOld, hcaNew⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv "pl.n" (by simp)]; exact hvn
  · rw [hv "pl.i" (by simp)]; exact hvi
  · rw [hv "pl.u" (by simp)]; exact hvu
  · rw [hv "pl.b" (by simp)]; exact hvb
  · rw [hv "pl.m" (by simp)]; exact hvm
  · rw [hv "pl.h" (by simp)]; exact hhl
  · rw [hv "pl.h" (by simp), hv "pl.t" (by simp)]; exact hht
  · rw [hv "pl.t" (by simp), harrs]; exact hcnt
  · exact ordArr_of_eq hord (ha od)
  · exact rankArr_of_eq hrank (ha ra)
  · exact hadj.of_eq (ha ao) (ha aj) (ha dg) (ha mt)
  · rw [harrs]; exact hcaL
  · rw [harrs]; exact hddL
  · rw [harrs]; exact hrwL
  · rw [harrs]; exact hreL
  · rw [harrs]; exact hreV
  · rw [harrs]; exact hsegs
  · rw [harrs]; exact hanch
  · rw [harrs]; exact hdbd
  · rw [harrs]; exact hach
  · rw [harrs, hv "pl.t" (by simp)]; exact hqseg
  · rw [harrs, hv "pl.t" (by simp)]; exact hmono
  · rw [harrs, hv "pl.h" (by simp), hv "pl.t" (by simp)]; exact hreach
  · rw [harrs, hv "pl.h" (by simp)]; exact hpopped
  · rw [harrs]; exact hcaOld
  · rw [harrs]; exact hcaNew

/-- **The head bump**: `PBfs` survives `pl.h := pl.h + 1` when the
window is nonempty and the outgoing head's row — where expandable — is
fully relaxed. -/
theorem pbfs_bump {i : ℕ} {u : Fin N} {σ σ' : Env}
    (h : PBfs ca ra ao aj dg mt od G π R i u σ)
    (hv : ∀ y, y ∈ (["pl.n", "pl.i", "pl.u", "pl.b", "pl.m",
      "pl.t"] : List String) → σ'.vars y = σ.vars y)
    (ha : ∀ b', σ'.arrs b' = σ.arrs b')
    (hh' : σ'.vars "pl.h" = σ.vars "pl.h" + 1)
    (hlt : σ.vars "pl.h" < σ.vars "pl.t")
    (hpop : ∀ hp : (σ.arrs plRw).getD (σ.vars "pl.h") 0 < N,
      (σ.arrs plDd).getD ((σ.arrs plRw).getD (σ.vars "pl.h") 0) 0 < 2 * R →
      ∀ w : Fin N, (deleteVerts G (peelSet π i)).Adj
        ⟨(σ.arrs plRw).getD (σ.vars "pl.h") 0, hp⟩ w →
      (σ.arrs plDd).getD ((w : ℕ)) 0 ≤
        (σ.arrs plDd).getD ((σ.arrs plRw).getD (σ.vars "pl.h") 0) 0 + 1) :
    PBfs ca ra ao aj dg mt od G π R i u σ' := by
  have harrs : σ'.arrs = σ.arrs := funext ha
  obtain ⟨hvn, hvi, hvu, hvb, hvm, hhl, hht, hcnt, hord, hrank, hadj, hcaL,
    hddL, hrwL, hreL, hreV, hsegs, hanch, hdbd, hach, hqseg, hmono, hreach,
    hpopped, hcaOld, hcaNew⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv "pl.n" (by simp)]; exact hvn
  · rw [hv "pl.i" (by simp)]; exact hvi
  · rw [hv "pl.u" (by simp)]; exact hvu
  · rw [hv "pl.b" (by simp)]; exact hvb
  · rw [hv "pl.m" (by simp)]; exact hvm
  · rw [hh']; omega
  · rw [hh', hv "pl.t" (by simp)]; omega
  · rw [hv "pl.t" (by simp), harrs]; exact hcnt
  · exact ordArr_of_eq hord (ha od)
  · exact rankArr_of_eq hrank (ha ra)
  · exact hadj.of_eq (ha ao) (ha aj) (ha dg) (ha mt)
  · rw [harrs]; exact hcaL
  · rw [harrs]; exact hddL
  · rw [harrs]; exact hrwL
  · rw [harrs]; exact hreL
  · rw [harrs]; exact hreV
  · rw [harrs]; exact hsegs
  · rw [harrs]; exact hanch
  · rw [harrs]; exact hdbd
  · rw [harrs]; exact hach
  · rw [harrs, hv "pl.t" (by simp)]; exact hqseg
  · rw [harrs, hv "pl.t" (by simp)]; exact hmono
  · rw [harrs, hh', hv "pl.t" (by simp)]
    intro hlt' p hp1 hp2
    have h1 := hreach hlt p hp1 hp2
    have h2 := hmono (σ.vars "pl.h") (σ.vars "pl.h" + 1) hhl (Nat.le_succ _)
      hlt'
    omega
  · rw [harrs, hh']
    intro p hp1 hp2 hp hplt w hadjw
    rcases Nat.lt_or_ge p (σ.vars "pl.h") with hcase | hcase
    · exact hpopped p hp1 hcase hp hplt w hadjw
    · have hpe : p = σ.vars "pl.h" := by omega
      subst hpe
      exact hpop hp hplt w hadjw
  · rw [harrs]; exact hcaOld
  · rw [harrs]; exact hcaNew

open Classical in
/-- **The BFS loop**: pop until the queue empties.  Priced by the queue
potential — the weight of a vertex is its live degree when it can still
be expanded, plus a constant — so the loop's total is the scanned-edge
budget plus the fibre's size, never a full pass. -/
theorem peelBfs_loop
    (hNB : N < B) (hsq : N * N + N + 4 < B) (hRB : 2 * R + 2 < B)
    (hca_dd : ca ≠ plDd) (hca_rw : ca ≠ plRw) (hca_re : ca ≠ plRe)
    (hod_ca : od ≠ ca) (hod_dd : od ≠ plDd) (hod_rw : od ≠ plRw)
    (hra_ca : ra ≠ ca) (hra_dd : ra ≠ plDd) (hra_rw : ra ≠ plRw)
    (hao_ca : ao ≠ ca) (hao_dd : ao ≠ plDd) (hao_rw : ao ≠ plRw)
    (haj_ca : aj ≠ ca) (haj_dd : aj ≠ plDd) (haj_rw : aj ≠ plRw)
    (hdg_ca : dg ≠ ca) (hdg_dd : dg ≠ plDd) (hdg_rw : dg ≠ plRw)
    (hmt_ca : mt ≠ ca) (hmt_dd : mt ≠ plDd) (hmt_rw : mt ≠ plRw)
    {i : ℕ} (hi : i < N) :
    Spec B (fun σ => PBfs ca ra ao aj dg mt od G π R i (π.symm ⟨i, hi⟩) σ)
      (.while (.lt (.var "pl.h") (.var "pl.t")) (peelPopB R ca ao aj dg))
      (fun _ σ' => PBfs ca ra ao aj dg mt od G π R i (π.symm ⟨i, hi⟩) σ' ∧
        σ'.vars "pl.h" = σ'.vars "pl.t")
      (64 * peelDeg G π R i + 128 * (pfibR G π R i).ncard + 4) := by
  classical
  set u : Fin N := π.symm ⟨i, hi⟩ with hu
  have hπu : ((π u : Fin N) : ℕ) = i := by rw [hu, Equiv.apply_symm_apply]
  set H := deleteVerts G (peelSet π i) with hH
  have hpfib : pfibR G π R i = ball H (2 * R) u := by
    rw [pfibR_eq G π R hi, ← hu, pfib_eq_ball, hπu, hH]
  set Xf : Finset (Fin N) := (Set.toFinite (pfibR G π R i)).toFinset with hXf
  have hXfcard : Xf.card = (pfibR G π R i).ncard := by
    rw [hXf, ← Set.ncard_eq_toFinset_card]
  set wtv : ℕ → ℕ := fun c =>
    if hc : c < N then
      (if (⟨c, hc⟩ : Fin N) ∈ ball H (2 * R - 1) u
        then 64 * (H.neighborSet ⟨c, hc⟩).ncard else 0) + 128
    else 128 with hwtv
  have hwtv128 : ∀ c, 128 ≤ wtv c := by
    intro c
    simp only [hwtv]
    split
    · exact Nat.le_add_left _ _
    · exact le_rfl
  have hwtvF : ∀ z' : Fin N, wtv ((z' : ℕ)) =
      (if z' ∈ ball H (2 * R - 1) u
        then 64 * (H.neighborSet z').ncard else 0) + 128 := by
    intro z'
    simp only [hwtv, z'.isLt, dif_pos, Fin.eta]
  -- mid-run facts: the listed set sits inside the fibre
  have hlistXf : ∀ (σ : Env),
      (∀ z, (hz : z < N) → (σ.arrs plDd).getD z 0 ≤ 2 * R →
        WithinDist H ((σ.arrs plDd).getD z 0) u ⟨z, hz⟩) →
      ∀ z' : Fin N, (σ.arrs plDd).getD ((z' : ℕ)) 0 ≤ 2 * R → z' ∈ Xf := by
    intro σ hach z' hz'
    rw [hXf, Set.Finite.mem_toFinset, hpfib]
    have h := hach ((z' : ℕ)) z'.isLt hz'
    rw [Fin.eta] at h
    exact mem_ball.mpr (withinDist_mono_radius hz' h)
  -- the window's weight rides inside the listed set's weight
  have himage : ∀ (σ : Env),
      PBfs ca ra ao aj dg mt od G π R i u σ →
      ∀ lo, mval G π R i ≤ lo →
      (∑ p ∈ Finset.Ico lo (σ.vars "pl.t"),
        wtv ((σ.arrs plRw).getD p 0)) ≤
        ∑ z' ∈ Xf.filter
          (fun z' => (σ.arrs plDd).getD z'.val 0 ≤ 2 * R),
          wtv z'.val := by
    intro σ hPB lo hlo
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hach,
      hqseg, -, -, -, -, -⟩ := hPB
    obtain ⟨hqs, hqc, hqi⟩ := hqseg
    have hinj : Set.InjOn (fun p => (σ.arrs plRw).getD p 0)
        ↑(Finset.Ico lo (σ.vars "pl.t")) := by
      intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_Ico] at hp hq
      exact hqi p q (le_trans hlo hp.1) hp.2 (le_trans hlo hq.1) hq.2 hpq
    have hvinj : Set.InjOn (fun z' : Fin N => z'.val)
        ↑(Xf.filter (fun z' => (σ.arrs plDd).getD z'.val 0 ≤ 2 * R)) :=
      fun a _ b _ hab => Fin.ext hab
    have hsub : (Finset.Ico lo (σ.vars "pl.t")).image
          (fun p => (σ.arrs plRw).getD p 0) ⊆
        (Xf.filter (fun z' => (σ.arrs plDd).getD z'.val 0 ≤ 2 * R)).image
          (fun z' : Fin N => z'.val) := by
      intro c hc
      rw [Finset.mem_image] at hc
      obtain ⟨p, hp, rfl⟩ := hc
      rw [Finset.mem_Ico] at hp
      obtain ⟨hz, hmem⟩ := hqs p (le_trans hlo hp.1) hp.2
      have hlst : (σ.arrs plDd).getD ((σ.arrs plRw).getD p 0) 0 ≤ 2 * R := hmem
      rw [Finset.mem_image]
      refine ⟨⟨(σ.arrs plRw).getD p 0, hz⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨hlistXf σ hach _ hlst, hlst⟩
    calc ∑ p ∈ Finset.Ico lo (σ.vars "pl.t"), wtv ((σ.arrs plRw).getD p 0)
        = ∑ c ∈ (Finset.Ico lo (σ.vars "pl.t")).image
            (fun p => (σ.arrs plRw).getD p 0), wtv c :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ c ∈ (Xf.filter
            (fun z' => (σ.arrs plDd).getD z'.val 0 ≤ 2 * R)).image
            (fun z' : Fin N => z'.val), wtv c :=
          Finset.sum_le_sum_of_subset hsub
      _ = ∑ z' ∈ Xf.filter
            (fun z' => (σ.arrs plDd).getD z'.val 0 ≤ 2 * R), wtv z'.val :=
          Finset.sum_image hvinj
  -- any vertex set holds at most `N` vertices
  have hncN : ∀ X : Set (Fin N), X.ncard ≤ N := by
    intro X
    calc X.ncard ≤ (Set.univ : Set (Fin N)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      _ = N := by simp [Set.ncard_univ]
  -- the two cursors stay inside the slot space
  have hvarB : ∀ σ : Env, PBfs ca ra ao aj dg mt od G π R i u σ →
      σ.vars "pl.h" ≤ σ.vars "pl.t" ∧ σ.vars "pl.t" ≤ N * N := by
    intro σ hPB
    obtain ⟨-, -, -, -, -, -, hht, hcnt, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -⟩ := hPB
    refine ⟨hht, ?_⟩
    rw [hcnt]
    have h1 := hncN {z : Fin N | (σ.arrs plDd).getD ((z : ℕ)) 0 ≤ 2 * R}
    have h2 : mval G π R i ≤ i * N := mval_le G π R
    have h3 : (i + 1) * N ≤ N * N :=
      Nat.mul_le_mul (Nat.succ_le_of_lt hi) le_rfl
    have h4 : (i + 1) * N = i * N + N := by ring
    omega
  have hbsize : (Cond.lt (Expr.var "pl.h") (Expr.var "pl.t")).size = 3 := by
    simp
  have hbsize2 : (Cond.lt (Expr.var "pl.d") (Expr.lit (2 * R))).size = 3 := by
    simp
  -- the queue potential: undiscovered weight plus window weight
  set Φ : Env → ℕ := fun σ =>
    (∑ z' ∈ Xf.filter
        (fun z' => (σ.arrs plDd).getD z'.val 0 = 2 * R + 1), wtv z'.val) +
    ∑ p ∈ Finset.Ico (σ.vars "pl.h") (σ.vars "pl.t"),
      wtv ((σ.arrs plRw).getD p 0) with hΦ
  refine (Spec.while_potential
    (fun σ => PBfs ca ra ao aj dg mt od G π R i u σ) Φ ?_ ?_
    (fun _ hσ => hσ) ?_).post ?_
  · -- the condition always evaluates
    intro σ hPB
    obtain ⟨hle, hub⟩ := hvarB σ hPB
    exact evalB_condLt_vars (by omega) (by omega)
  · -- one pop pays for itself out of the potential
    intro σ hPB htrue
    obtain ⟨hle0, hub0⟩ := hvarB σ hPB
    have hlt : σ.vars "pl.h" < σ.vars "pl.t" := by
      have heval := evalB_condLt (B := B) (σ := σ)
        (evalB_var (x := "pl.h") (by omega))
        (evalB_var (x := "pl.t") (by omega))
      rw [heval] at htrue
      simpa using htrue
    obtain ⟨hvn, hvi, hvu, hvb, hvm, hhl, hht, hcnt, hord, hrank, hadj, hcaL,
      hddL, hrwL, hreL, hreV, hsegs, hanch, hdbd, hach, hqseg, hmono, hreach,
      hpopped, hcaOld, hcaNew⟩ := id hPB
    -- the popped vertex
    set zval : ℕ := (σ.arrs plRw).getD (σ.vars "pl.h") 0 with hzval
    obtain ⟨hzN0, hzmem0⟩ := hqseg.1 (σ.vars "pl.h") hhl hlt
    have hzN : zval < N := by rw [hzval]; exact hzN0
    have hdz2R : (σ.arrs plDd).getD zval 0 ≤ 2 * R := by
      rw [hzval]; exact hzmem0
    have hachz := hach zval hzN hdz2R
    have hznp : (⟨zval, hzN⟩ : Fin N) ∉ peelSet π i :=
      not_mem_of_withinDist_deleteVerts hachz (symm_not_peeled π hi)
    -- the two anchor reads
    have hidx1 : σ.vars "pl.h" < (σ.arrs plRw).length := by omega
    have hr1 : Run B (.assign "pl.z" (.get plRw (.var "pl.h"))) σ
        (σ.setVar "pl.z" zval) 3 := by
      have h := Run.assign (B := B) (x := "pl.z")
        (h := evalB_get (a := plRw) (i := Expr.var "pl.h")
          (evalB_var (by omega))
          (getElem?_of_getD hidx1 hzval.symm) (by omega))
      exact h.mono (by simp)
    have h1z : (σ.setVar "pl.z" zval).vars "pl.z" = zval := by
      simp
    have hr2 : Run B (.assign "pl.d" (.get plDd (.var "pl.z")))
        (σ.setVar "pl.z" zval)
        ((σ.setVar "pl.z" zval).setVar "pl.d"
          ((σ.arrs plDd).getD zval 0)) 3 := by
      have hez : (Expr.var "pl.z").evalB B (σ.setVar "pl.z" zval)
          = some zval := by
        have h := evalB_var (B := B) (x := "pl.z")
          (σ := σ.setVar "pl.z" zval) (by rw [h1z]; omega)
        rwa [h1z] at h
      have h := Run.assign (B := B) (x := "pl.d")
        (h := evalB_get (a := plDd) (i := Expr.var "pl.z") hez
          (getElem?_of_getD (l := σ.arrs plDd) (by omega) rfl) (by omega))
      exact h.mono (by simp)
    set σ₂ : Env := (σ.setVar "pl.z" zval).setVar "pl.d"
      ((σ.arrs plDd).getD zval 0) with hσ₂
    have h2d : σ₂.vars "pl.d" = (σ.arrs plDd).getD zval 0 := by
      rw [hσ₂]; simp
    have h2z : σ₂.vars "pl.z" = zval := by
      rw [hσ₂]; simp
    have h2h : σ₂.vars "pl.h" = σ.vars "pl.h" := by
      rw [hσ₂]; simp
    -- the window's bottom element
    have hbot : (∑ p ∈ Finset.Ico (σ.vars "pl.h") (σ.vars "pl.t"),
          wtv ((σ.arrs plRw).getD p 0))
        = wtv zval + ∑ p ∈ Finset.Ico (σ.vars "pl.h" + 1) (σ.vars "pl.t"),
            wtv ((σ.arrs plRw).getD p 0) := by
      rw [Finset.sum_eq_sum_Ico_succ_bot hlt, hzval]
    have hΦσ : Φ σ = (∑ z' ∈ Xf.filter
          (fun z' => (σ.arrs plDd).getD z'.val 0 = 2 * R + 1), wtv z'.val) +
        ∑ p ∈ Finset.Ico (σ.vars "pl.h") (σ.vars "pl.t"),
          wtv ((σ.arrs plRw).getD p 0) := by
      simp only [hΦ]
    by_cases hexp : (σ.arrs plDd).getD zval 0 < 2 * R
    · -- expansion: the head's row is scanned
      obtain ⟨offF₀, hoff0, hoffstep, haoL, haoV, hajL, hmtL, hdgL, hdead,
        hdeg, hsound, hcomp⟩ := hadj
      have hoffz : offF₀ zval ≤ offF₀ N :=
        offF_mono hoffstep N le_rfl zval (le_of_lt hzN)
      have hoffsq : offF₀ N ≤ N * N := offF_le_sq hoff0 hoffstep
      have hgdeg : (σ.arrs dg).getD zval 0
          = ((deleteVerts G (peelSet π i)).neighborSet ⟨zval, hzN⟩).ncard :=
        hdeg ⟨zval, hzN⟩ hznp
      have hgN : (σ.arrs dg).getD zval 0 ≤ N := by
        rw [hgdeg]; exact ncard_neighborSet_le_card _
      -- the three row reads
      have hez2 : (Expr.var "pl.z").evalB B σ₂ = some zval := by
        have h := evalB_var (B := B) (x := "pl.z") (σ := σ₂)
          (by rw [h2z]; omega)
        rwa [h2z] at h
      have hr3 : Run B (.assign "pl.a" (.get ao (.var "pl.z"))) σ₂
          (σ₂.setVar "pl.a" (offF₀ zval)) 3 := by
        have h := Run.assign (B := B) (x := "pl.a")
          (h := evalB_get (a := ao) (i := Expr.var "pl.z") hez2
            (getElem?_of_getD (l := σ.arrs ao) (by omega)
              (haoV zval (le_of_lt hzN)))
            (by omega))
        exact h.mono (by simp)
      have h3z : (σ₂.setVar "pl.a" (offF₀ zval)).vars "pl.z" = zval := by
        simp [h2z]
      have hez3 : (Expr.var "pl.z").evalB B (σ₂.setVar "pl.a" (offF₀ zval))
          = some zval := by
        have h := evalB_var (B := B) (x := "pl.z")
          (σ := σ₂.setVar "pl.a" (offF₀ zval)) (by rw [h3z]; omega)
        rwa [h3z] at h
      have hr4 : Run B (.assign "pl.g" (.get dg (.var "pl.z")))
          (σ₂.setVar "pl.a" (offF₀ zval))
          ((σ₂.setVar "pl.a" (offF₀ zval)).setVar "pl.g"
            ((σ.arrs dg).getD zval 0)) 3 := by
        have h := Run.assign (B := B) (x := "pl.g")
          (h := evalB_get (a := dg) (i := Expr.var "pl.z") hez3
            (getElem?_of_getD (l := σ.arrs dg) (by omega) rfl) (by omega))
        exact h.mono (by simp)
      have hr5 : Run B (.assign "pl.j" (.lit 0))
          ((σ₂.setVar "pl.a" (offF₀ zval)).setVar "pl.g"
            ((σ.arrs dg).getD zval 0))
          (((σ₂.setVar "pl.a" (offF₀ zval)).setVar "pl.g"
            ((σ.arrs dg).getD zval 0)).setVar "pl.j" 0) 2 :=
        (Run.assign (evalB_lit (by omega))).mono (by simp)
      set σ₅ : Env := ((σ₂.setVar "pl.a" (offF₀ zval)).setVar "pl.g"
        ((σ.arrs dg).getD zval 0)).setVar "pl.j" 0 with hσ₅
      have h5z : σ₅.vars "pl.z" = zval := by
        rw [hσ₅]; simp [h2z]
      have h5d : σ₅.vars "pl.d" = (σ.arrs plDd).getD zval 0 := by
        rw [hσ₅]; simp [h2d]
      have h5a : σ₅.vars "pl.a" = offF₀ zval := by
        rw [hσ₅]; simp
      have h5g : σ₅.vars "pl.g" = (σ.arrs dg).getD zval 0 := by
        rw [hσ₅]; simp
      have h5j : σ₅.vars "pl.j" = 0 := by
        rw [hσ₅]; simp
      have h5h : σ₅.vars "pl.h" = σ.vars "pl.h" := by
        rw [hσ₅]; simp [h2h]
      have h5t : σ₅.vars "pl.t" = σ.vars "pl.t" := by
        rw [hσ₅, hσ₂]; simp
      have h5arr : ∀ b', σ₅.arrs b' = σ.arrs b' := fun _ => rfl
      -- the expansion state at the entry of the row scan
      have hI5 : EInv ca ra ao aj dg mt od G π R i u ⟨zval, hzN⟩ offF₀ σ₅ := by
        refine ⟨pbfs_of_eq hPB ?_ h5arr, ?_, ?_, ?_, ?_, ?_, hexp, ?_, ?_, ?_⟩
        · intro y hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            (rw [hσ₅, hσ₂]; simp)
        · rw [h5z]
        · show σ₅.vars "pl.d" = (σ₅.arrs plDd).getD zval 0
          rw [h5d, h5arr plDd]
        · rw [h5a]
        · show σ₅.vars "pl.g" = (σ₅.arrs dg).getD zval 0
          rw [h5g, h5arr dg]
        · rw [h5j]
          exact Nat.zero_le _
        · rw [h5h, h5t]
          exact hlt
        · rw [h5h]
          exact hzval.symm
        · rw [h5j]
          intro s hs
          exact absurd hs (Nat.not_lt_zero s)
      obtain ⟨σw, hrun_w, hIw, hwjg, hstab, hmonot, hwg, hwh, hsen⟩ :=
        peelExpand_loop hNB hsq hRB hca_dd hca_rw hca_re hod_ca hod_dd hod_rw
          hra_ca hra_dd hra_rw hao_ca hao_dd hao_rw haj_ca haj_dd haj_rw
          hdg_ca hdg_dd hdg_rw hmt_ca hmt_dd hmt_rw hoff0 hoffstep hi
          ((σ.arrs dg).getD zval 0) σ₅ hI5 (by simp [h5g, h5j])
      rw [h5t] at hstab hmonot
      rw [h5h] at hwh
      rw [h5g] at hwg
      simp only [h5arr] at hstab hsen
      obtain ⟨hPBw, hwz, hwd, hwa, hwgv, hwjle, hwdlt, hwhtl, hwfh,
        hwrelax⟩ := hIw
      have hltw : σw.vars "pl.h" < σw.vars "pl.t" := by
        rw [hwh]
        exact lt_of_lt_of_le hlt hmonot
      -- the full relaxation of the popped head's row
      have hpop : ∀ hp : (σw.arrs plRw).getD (σw.vars "pl.h") 0 < N,
          (σw.arrs plDd).getD
            ((σw.arrs plRw).getD (σw.vars "pl.h") 0) 0 < 2 * R →
          ∀ w' : Fin N, (deleteVerts G (peelSet π i)).Adj
            ⟨(σw.arrs plRw).getD (σw.vars "pl.h") 0, hp⟩ w' →
          (σw.arrs plDd).getD ((w' : ℕ)) 0 ≤
            (σw.arrs plDd).getD
              ((σw.arrs plRw).getD (σw.vars "pl.h") 0) 0 + 1 := by
        intro hp hplt w' hadjw
        have hFin : (⟨(σw.arrs plRw).getD (σw.vars "pl.h") 0, hp⟩ : Fin N)
            = ⟨zval, hzN⟩ := Fin.ext hwfh
        rw [hFin] at hadjw
        obtain ⟨-, -, -, -, -, -, -, -, -, -, hadjW, -, -, -, -, -, -, -, -,
          -, -, -, -, -, -, -⟩ := id hPBw
        obtain ⟨offF₁, hoff0₁, hstep₁, -, -, -, -, -, -, -, -, hcomp₁⟩ :=
          hadjW
        obtain ⟨t₁, ht₁, hajt₁⟩ := hcomp₁ ⟨zval, hzN⟩ hznp w' hadjw
        have hoffeq : offF₁ zval = offF₀ zval :=
          offF_unique hoff0₁ hoff0 hstep₁ hoffstep zval (le_of_lt hzN)
        have ht₁' : t₁ < σw.vars "pl.j" := by
          rw [hwjg, hwgv]
          exact ht₁
        have hval : (σw.arrs aj).getD (offF₀ zval + t₁) 0 = ((w' : Fin N) : ℕ) := by
          rw [← hoffeq]
          exact hajt₁
        have h := hwrelax t₁ ht₁' w' hval
        rw [hwfh]
        exact h
      have hPBf : PBfs ca ra ao aj dg mt od G π R i u
          (σw.setVar "pl.h" (σw.vars "pl.h" + 1)) := by
        refine pbfs_bump hPBw ?_ (fun _ => rfl) (by simp) hltw hpop
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      have hcondT : (Cond.lt (.var "pl.d") (.lit (2 * R))).evalB B σ₂
          = some true := by
        have h := evalB_condLt (B := B) (σ := σ₂)
          (evalB_var (x := "pl.d") (by rw [h2d]; omega))
          (evalB_lit (n := 2 * R) (by omega))
        rw [h2d] at h
        rw [h]
        simp only [Option.some.injEq, decide_eq_true_eq]
        exact hexp
      have hr6 : Run B (.assign "pl.h" (.add (.var "pl.h") (.lit 1))) σw
          (σw.setVar "pl.h" (σw.vars "pl.h" + 1)) 4 := by
        have h := Run.assign (B := B) (x := "pl.h")
          (h := evalB_incr (x := "pl.h") (σ := σw) (by rw [hwh]; omega))
        exact h.mono (by simp)
      have hbody : Run B (.seq (.assign "pl.a" (.get ao (.var "pl.z")))
          (.seq (.assign "pl.g" (.get dg (.var "pl.z")))
            (.seq (.assign "pl.j" (.lit 0))
              (.while (.lt (.var "pl.j") (.var "pl.g"))
                (peelExpandB R ca aj)))) ) σ₂ σw
          (3 + (3 + (2 + (44 * ((σ.arrs dg).getD zval 0) + 4)))) :=
        hr3.seq (hr4.seq (hr5.seq hrun_w))
      refine ⟨σw.setVar "pl.h" (σw.vars "pl.h" + 1),
        44 * ((σ.arrs dg).getD zval 0) + 26, ?_, hPBf, ?_⟩
      · exact (hr1.seq (hr2.seq ((Run.ite_true hcondT hbody).seq hr6))).mono
          (by simp only [hbsize2]; omega)
      · -- the payment: the popped weight covers the scan
        rw [hbsize]
        have hΦf : Φ (σw.setVar "pl.h" (σw.vars "pl.h" + 1))
            = (∑ z' ∈ Xf.filter
                (fun z' => (σw.arrs plDd).getD z'.val 0 = 2 * R + 1),
                wtv z'.val) +
              ∑ p ∈ Finset.Ico (σ.vars "pl.h" + 1) (σw.vars "pl.t"),
                wtv ((σw.arrs plRw).getD p 0) := by
          simp only [hΦ]
          rw [show (σw.setVar "pl.h" (σw.vars "pl.h" + 1)).vars "pl.h"
              = σ.vars "pl.h" + 1 from by simp [hwh],
            show (σw.setVar "pl.h" (σw.vars "pl.h" + 1)).vars "pl.t"
              = σw.vars "pl.t" from by simp]
          try rfl
        have hsplitW : (∑ p ∈ Finset.Ico (σ.vars "pl.h" + 1)
              (σw.vars "pl.t"), wtv ((σw.arrs plRw).getD p 0))
            = (∑ p ∈ Finset.Ico (σ.vars "pl.h" + 1) (σ.vars "pl.t"),
                wtv ((σw.arrs plRw).getD p 0)) +
              ∑ p ∈ Finset.Ico (σ.vars "pl.t") (σw.vars "pl.t"),
                wtv ((σw.arrs plRw).getD p 0) :=
          (Finset.sum_Ico_consecutive _ (by omega) hmonot).symm
        have hstabW : (∑ p ∈ Finset.Ico (σ.vars "pl.h" + 1) (σ.vars "pl.t"),
              wtv ((σw.arrs plRw).getD p 0))
            = ∑ p ∈ Finset.Ico (σ.vars "pl.h" + 1) (σ.vars "pl.t"),
              wtv ((σ.arrs plRw).getD p 0) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [Finset.mem_Ico] at hp
          rw [hstab p hp.2]
        have hA'A : Xf.filter
              (fun z' => (σw.arrs plDd).getD z'.val 0 = 2 * R + 1)
            ⊆ Xf.filter
              (fun z' => (σ.arrs plDd).getD z'.val 0 = 2 * R + 1) := by
          intro a ha
          rw [Finset.mem_filter] at ha ⊢
          exact ⟨ha.1, hsen _ ha.2⟩
        have hAsplit : (∑ z' ∈ (Xf.filter
              (fun z' => (σ.arrs plDd).getD z'.val 0 = 2 * R + 1) \
              Xf.filter
              (fun z' => (σw.arrs plDd).getD z'.val 0 = 2 * R + 1)),
              wtv z'.val) +
            (∑ z' ∈ Xf.filter
              (fun z' => (σw.arrs plDd).getD z'.val 0 = 2 * R + 1),
              wtv z'.val)
            = ∑ z' ∈ Xf.filter
              (fun z' => (σ.arrs plDd).getD z'.val 0 = 2 * R + 1),
              wtv z'.val :=
          Finset.sum_sdiff hA'A
        -- the appended segment rides inside the newly discovered weight
        have hnew : (∑ p ∈ Finset.Ico (σ.vars "pl.t") (σw.vars "pl.t"),
              wtv ((σw.arrs plRw).getD p 0))
            ≤ ∑ z' ∈ (Xf.filter
                (fun z' => (σ.arrs plDd).getD z'.val 0 = 2 * R + 1) \
                Xf.filter
                (fun z' => (σw.arrs plDd).getD z'.val 0 = 2 * R + 1)),
              wtv z'.val := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
            hachW, hqsegW, -, -, -, -, -⟩ := id hPBw
          obtain ⟨hqsW, hqcW, hqiW⟩ := hqsegW
          obtain ⟨hqs0, hqc0, hqi0⟩ := id hqseg
          have hmem : ∀ p, σ.vars "pl.t" ≤ p → p < σw.vars "pl.t" →
              ∃ hzp : (σw.arrs plRw).getD p 0 < N,
                (⟨(σw.arrs plRw).getD p 0, hzp⟩ : Fin N) ∈
                  (Xf.filter
                    (fun z' => (σ.arrs plDd).getD z'.val 0 = 2 * R + 1) \
                  Xf.filter
                    (fun z' => (σw.arrs plDd).getD z'.val 0 = 2 * R + 1)) := by
            intro p hp1 hp2
            have hmv : mval G π R i ≤ p :=
              le_trans (le_trans hhl (le_of_lt hlt)) hp1
            obtain ⟨hzp, hlstp⟩ := hqsW p hmv hp2
            refine ⟨hzp, ?_⟩
            have hlstp' : (σw.arrs plDd).getD
                ((σw.arrs plRw).getD p 0) 0 ≤ 2 * R := hlstp
            have hold : (σ.arrs plDd).getD
                ((σw.arrs plRw).getD p 0) 0 = 2 * R + 1 := by
              by_contra hne
              have hle : (σ.arrs plDd).getD
                  ((σw.arrs plRw).getD p 0) 0 ≤ 2 * R := by
                have := hdbd ((σw.arrs plRw).getD p 0) hzp
                omega
              obtain ⟨q, hq1, hq2, hq3⟩ :=
                hqc0 ⟨(σw.arrs plRw).getD p 0, hzp⟩ hle
              have hq3' : (σ.arrs plRw).getD q 0
                  = ((⟨(σw.arrs plRw).getD p 0, hzp⟩ : Fin N) : ℕ) := hq3
              have hqw : (σw.arrs plRw).getD q 0
                  = (σw.arrs plRw).getD p 0 := by
                rw [hstab q hq2, hq3']
              have := hqiW q p hq1 (lt_of_lt_of_le hq2 hmonot) hmv hp2 hqw
              omega
            rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
            refine ⟨⟨?_, hold⟩, ?_⟩
            · exact hlistXf σw hachW ⟨(σw.arrs plRw).getD p 0, hzp⟩ hlstp'
            · rintro ⟨-, hbad⟩
              have hbad' : (σw.arrs plDd).getD
                  ((σw.arrs plRw).getD p 0) 0 = 2 * R + 1 := hbad
              omega
          have hinj2 : Set.InjOn (fun p => (σw.arrs plRw).getD p 0)
              ↑(Finset.Ico (σ.vars "pl.t") (σw.vars "pl.t")) := by
            intro p hp q hq hpq
            rw [Finset.mem_coe, Finset.mem_Ico] at hp hq
            exact hqiW p q
              (le_trans (le_trans hhl (le_of_lt hlt)) hp.1) hp.2
              (le_trans (le_trans hhl (le_of_lt hlt)) hq.1) hq.2 hpq
          have hvinj2 : Set.InjOn (fun z' : Fin N => z'.val)
              ↑(Xf.filter
                  (fun z' => (σ.arrs plDd).getD z'.val 0 = 2 * R + 1) \
                Xf.filter
                  (fun z' => (σw.arrs plDd).getD z'.val 0 = 2 * R + 1)) :=
            fun a _ b _ hab => Fin.ext hab
          have hsub2 : (Finset.Ico (σ.vars "pl.t") (σw.vars "pl.t")).image
                (fun p => (σw.arrs plRw).getD p 0)
              ⊆ (Xf.filter
                  (fun z' => (σ.arrs plDd).getD z'.val 0 = 2 * R + 1) \
                Xf.filter
                  (fun z' => (σw.arrs plDd).getD z'.val 0 = 2 * R + 1)).image
                (fun z' : Fin N => z'.val) := by
            intro c hc
            rw [Finset.mem_image] at hc
            obtain ⟨p, hp, rfl⟩ := hc
            rw [Finset.mem_Ico] at hp
            obtain ⟨hzp, hmemp⟩ := hmem p hp.1 hp.2
            rw [Finset.mem_image]
            exact ⟨⟨(σw.arrs plRw).getD p 0, hzp⟩, hmemp, rfl⟩
          calc (∑ p ∈ Finset.Ico (σ.vars "pl.t") (σw.vars "pl.t"),
                wtv ((σw.arrs plRw).getD p 0))
              = ∑ c ∈ (Finset.Ico (σ.vars "pl.t") (σw.vars "pl.t")).image
                  (fun p => (σw.arrs plRw).getD p 0), wtv c :=
                (Finset.sum_image hinj2).symm
            _ ≤ ∑ c ∈ (Xf.filter
                  (fun z' => (σ.arrs plDd).getD z'.val 0 = 2 * R + 1) \
                Xf.filter
                  (fun z' => (σw.arrs plDd).getD z'.val 0 = 2 * R + 1)).image
                  (fun z' : Fin N => z'.val), wtv c :=
                Finset.sum_le_sum_of_subset hsub2
            _ = _ := Finset.sum_image hvinj2
        -- the popped head's weight
        have hwval : wtv zval = 64 * ((σ.arrs dg).getD zval 0) + 128 := by
          have hzball : (⟨zval, hzN⟩ : Fin N) ∈ ball H (2 * R - 1) u :=
            mem_ball.mpr (withinDist_mono_radius (by omega) hachz)
          have h := hwtvF ⟨zval, hzN⟩
          rw [if_pos hzball] at h
          rw [show ((⟨zval, hzN⟩ : Fin N) : ℕ) = zval from rfl] at h
          rw [h, hgdeg]
          try rfl
        rw [hΦσ, hΦf, hbot, hsplitW, hstabW]
        omega
    · -- no expansion: the head's level is already `2R`
      have hcondF : (Cond.lt (.var "pl.d") (.lit (2 * R))).evalB B σ₂
          = some false := by
        have h := evalB_condLt (B := B) (σ := σ₂)
          (evalB_var (x := "pl.d") (by rw [h2d]; omega))
          (evalB_lit (n := 2 * R) (by omega))
        rw [h2d] at h
        rw [h]
        simp only [Option.some.injEq, decide_eq_false_iff_not]
        exact hexp
      have hr6' : Run B (.assign "pl.h" (.add (.var "pl.h") (.lit 1))) σ₂
          (σ₂.setVar "pl.h" (σ.vars "pl.h" + 1)) 4 := by
        have h := Run.assign (B := B) (x := "pl.h")
          (h := evalB_incr (x := "pl.h") (σ := σ₂) (by rw [h2h]; omega))
        rw [h2h] at h
        exact h.mono (by simp)
      have hPBf : PBfs ca ra ao aj dg mt od G π R i u
          (σ₂.setVar "pl.h" (σ.vars "pl.h" + 1)) := by
        refine pbfs_bump hPB ?_ (fun _ => rfl) (by simp) hlt ?_
        · intro y hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
            (rw [hσ₂]; simp)
        · intro hp hplt w' hadjw
          rw [← hzval] at hplt
          exact absurd hplt hexp
      have hΦ3 : Φ (σ₂.setVar "pl.h" (σ.vars "pl.h" + 1))
          = (∑ z' ∈ Xf.filter
              (fun z' => (σ.arrs plDd).getD z'.val 0 = 2 * R + 1),
              wtv z'.val) +
            ∑ p ∈ Finset.Ico (σ.vars "pl.h" + 1) (σ.vars "pl.t"),
              wtv ((σ.arrs plRw).getD p 0) := by
        simp only [hΦ]
        rw [show (σ₂.setVar "pl.h" (σ.vars "pl.h" + 1)).vars "pl.h"
            = σ.vars "pl.h" + 1 from by simp,
          show (σ₂.setVar "pl.h" (σ.vars "pl.h" + 1)).vars "pl.t"
            = σ.vars "pl.t" from by rw [hσ₂]; simp]
        try rfl
      refine ⟨σ₂.setVar "pl.h" (σ.vars "pl.h" + 1), 15, ?_, hPBf, ?_⟩
      · exact (hr1.seq (hr2.seq
          ((Run.ite_false hcondF Run.skip).seq hr6'))).mono
          (by simp only [hbsize2]; omega)
      · rw [hbsize, hΦσ, hΦ3, hbot]
        have h128 := hwtv128 zval
        omega
  · -- the potential at entry is the budget
    intro σ hPB
    rw [hbsize]
    obtain ⟨-, -, -, -, -, hhl, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -⟩ := id hPB
    have hwin := himage σ hPB (σ.vars "pl.h") hhl
    have hsplit : (∑ z' ∈ Xf.filter
          (fun z' => (σ.arrs plDd).getD z'.val 0 ≤ 2 * R), wtv z'.val) +
        (∑ z' ∈ Xf.filter
          (fun z' => ¬ (σ.arrs plDd).getD z'.val 0 ≤ 2 * R), wtv z'.val)
        = ∑ z' ∈ Xf, wtv z'.val :=
      Finset.sum_filter_add_sum_filter_not Xf
        (fun z' => (σ.arrs plDd).getD z'.val 0 ≤ 2 * R)
        (fun z' => wtv z'.val)
    have hunv : (∑ z' ∈ Xf.filter
          (fun z' => (σ.arrs plDd).getD z'.val 0 = 2 * R + 1), wtv z'.val)
        ≤ ∑ z' ∈ Xf.filter
          (fun z' => ¬ (σ.arrs plDd).getD z'.val 0 ≤ 2 * R), wtv z'.val := by
      refine Finset.sum_le_sum_of_subset ?_
      intro a ha
      rw [Finset.mem_filter] at ha ⊢
      refine ⟨ha.1, ?_⟩
      omega
    have hpeel : peelDeg G π R i = ∑ z ∈ (Set.toFinite (ball H (2 * R - 1)
        u)).toFinset, (H.neighborSet z).ncard := by
      simp only [peelDeg]
      rw [dif_pos hi]
      try rfl
    have hfilter : Xf.filter (fun z' => z' ∈ ball H (2 * R - 1) u)
        = (Set.toFinite (ball H (2 * R - 1) u)).toFinset := by
      ext a
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨-, hb⟩
        exact hb
      · intro hb
        refine ⟨?_, hb⟩
        rw [hXf, Set.Finite.mem_toFinset, hpfib]
        exact ball_mono_radius H u (by omega) hb
    have hXsum : (∑ z' ∈ Xf, wtv z'.val)
        = 64 * peelDeg G π R i + 128 * (pfibR G π R i).ncard := by
      calc (∑ z' ∈ Xf, wtv z'.val)
          = ∑ z' ∈ Xf, ((if z' ∈ ball H (2 * R - 1) u
              then 64 * (H.neighborSet z').ncard else 0) + 128) :=
            Finset.sum_congr rfl (fun z' _ => hwtvF z')
        _ = (∑ z' ∈ Xf, if z' ∈ ball H (2 * R - 1) u
              then 64 * (H.neighborSet z').ncard else 0) +
            ∑ _z' ∈ Xf, 128 := Finset.sum_add_distrib
        _ = (∑ z' ∈ Xf.filter (fun z' => z' ∈ ball H (2 * R - 1) u),
              64 * (H.neighborSet z').ncard) + Xf.card * 128 := by
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
        _ = 64 * peelDeg G π R i + 128 * (pfibR G π R i).ncard := by
            rw [hfilter, ← Finset.mul_sum, ← hpeel, hXfcard]
            ring
    have hΦσ : Φ σ = (∑ z' ∈ Xf.filter
          (fun z' => (σ.arrs plDd).getD z'.val 0 = 2 * R + 1), wtv z'.val) +
        ∑ p ∈ Finset.Ico (σ.vars "pl.h") (σ.vars "pl.t"),
          wtv ((σ.arrs plRw).getD p 0) := by
      simp only [hΦ]
    rw [hΦσ]
    omega
  · -- the exit: the two cursors have met
    rintro σ σ' - ⟨hPB', hfalse⟩
    refine ⟨hPB', ?_⟩
    obtain ⟨hle, hub⟩ := hvarB σ' hPB'
    have heval := evalB_condLt (B := B) (σ := σ')
      (evalB_var (x := "pl.h") (by omega))
      (evalB_var (x := "pl.t") (by omega))
    rw [heval] at hfalse
    have hnlt : ¬ σ'.vars "pl.h" < σ'.vars "pl.t" := by
      simpa using hfalse
    omega

/-- **The touched-cell reset**: walk the emitted segment and re-sentinel
each member's level — `O(|X_u|)`, never `O(N)`.  Every listed cell lies
in the window, so after the walk the level region is all-sentinel
again. -/
theorem peelResetB_spec (hsq : N * N + N + 4 < B) (hRB : 2 * R + 2 < B)
    {b₀ t₀ : ℕ} (hbt : b₀ ≤ t₀) (ht : t₀ ≤ N * N) :
    Spec B
      (fun σ => σ.vars "pl.b" = b₀ ∧ σ.vars "pl.t" = t₀ ∧
        N ≤ (σ.arrs plDd).length ∧ N * N ≤ (σ.arrs plRw).length ∧
        (∀ p, b₀ ≤ p → p < t₀ → (σ.arrs plRw).getD p 0 < N) ∧
        (∀ z, z < N → (σ.arrs plDd).getD z 0 ≤ 2 * R + 1) ∧
        (∀ z, z < N → (σ.arrs plDd).getD z 0 ≤ 2 * R →
          ∃ p, b₀ ≤ p ∧ p < t₀ ∧ (σ.arrs plRw).getD p 0 = z))
      (peelResetB R)
      (fun _ σ' => (∀ z, z < N → (σ'.arrs plDd).getD z 0 = 2 * R + 1) ∧
        N ≤ (σ'.arrs plDd).length)
      (12 * (t₀ - b₀) + 6) := by
  classical
  -- the walk's invariant: listed cells lie ahead of the cursor
  set I : Env → Prop := fun ρ =>
    ρ.vars "pl.b" = b₀ ∧ ρ.vars "pl.t" = t₀ ∧
    b₀ ≤ ρ.vars "pl.k" ∧ ρ.vars "pl.k" ≤ t₀ ∧
    N ≤ (ρ.arrs plDd).length ∧ N * N ≤ (ρ.arrs plRw).length ∧
    (∀ p, b₀ ≤ p → p < t₀ → (ρ.arrs plRw).getD p 0 < N) ∧
    (∀ z, z < N → (ρ.arrs plDd).getD z 0 ≤ 2 * R + 1) ∧
    (∀ z, z < N → (ρ.arrs plDd).getD z 0 ≤ 2 * R →
      ∃ p, ρ.vars "pl.k" ≤ p ∧ p < t₀ ∧ (ρ.arrs plRw).getD p 0 = z)
    with hI
  have hbody : Spec B (fun ρ => I ρ ∧ ρ.vars "pl.k" < t₀)
      (.seq (.store plDd (.get plRw (.var "pl.k")) (.lit (2 * R + 1)))
        (.assign "pl.k" (.add (.var "pl.k") (.lit 1))))
      (fun ρ ρ' => I ρ' ∧ ρ'.vars "pl.k" = ρ.vars "pl.k" + 1) 8 := by
    rintro ρ ⟨hIρ, hklt⟩
    rw [hI] at hIρ
    obtain ⟨hb', ht', hbk, hkt, hddL', hrwL', hsound', hbound', hcompl'⟩ :=
      hIρ
    have hrwk : (ρ.arrs plRw).getD (ρ.vars "pl.k") 0 < N :=
      hsound' _ hbk hklt
    have hidx : ρ.vars "pl.k" < (ρ.arrs plRw).length := by omega
    have hs1 : Run B (.store plDd (.get plRw (.var "pl.k"))
        (.lit (2 * R + 1))) ρ
        (ρ.setArr plDd ((ρ.arrs plRw).getD (ρ.vars "pl.k") 0)
          (2 * R + 1)) 4 := by
      have h := Run.store (B := B) (a := plDd)
        (hi := evalB_get (a := plRw) (i := Expr.var "pl.k")
          (evalB_var (by omega)) (getElem?_of_getD hidx rfl) (by omega))
        (he := evalB_lit (n := 2 * R + 1) (by omega))
        (hidx := by omega)
      exact h.mono (by simp)
    have hva : (ρ.setArr plDd ((ρ.arrs plRw).getD (ρ.vars "pl.k") 0)
        (2 * R + 1)).vars "pl.k" = ρ.vars "pl.k" := by simp
    have hs2 : Run B (.assign "pl.k" (.add (.var "pl.k") (.lit 1)))
        (ρ.setArr plDd ((ρ.arrs plRw).getD (ρ.vars "pl.k") 0) (2 * R + 1))
        ((ρ.setArr plDd ((ρ.arrs plRw).getD (ρ.vars "pl.k") 0)
          (2 * R + 1)).setVar "pl.k" (ρ.vars "pl.k" + 1)) 4 := by
      have h := Run.assign (B := B) (x := "pl.k")
        (h := evalB_incr (x := "pl.k")
          (σ := ρ.setArr plDd ((ρ.arrs plRw).getD (ρ.vars "pl.k") 0)
            (2 * R + 1))
          (by rw [hva]; omega))
      rw [hva] at h
      exact h.mono (by simp)
    refine ⟨_, (hs1.seq hs2).mono (by omega), ?_, by simp⟩
    rw [hI]
    have harr : ∀ b', b' ≠ plDd →
        ((ρ.setArr plDd ((ρ.arrs plRw).getD (ρ.vars "pl.k") 0)
          (2 * R + 1)).setVar "pl.k" (ρ.vars "pl.k" + 1)).arrs b'
        = ρ.arrs b' := by
      intro b' hb'
      simp [hb']
    have hdd : ∀ z, (((ρ.setArr plDd ((ρ.arrs plRw).getD (ρ.vars "pl.k") 0)
          (2 * R + 1)).setVar "pl.k" (ρ.vars "pl.k" + 1)).arrs plDd).getD z 0
        = if z = (ρ.arrs plRw).getD (ρ.vars "pl.k") 0 then 2 * R + 1
          else (ρ.arrs plDd).getD z 0 := by
      intro z
      simp only [arrs_setVar, arrs_setArr, eq_self_iff_true, if_true]
      exact getD_set (ρ.arrs plDd) (2 * R + 1) z (by omega)
    refine ⟨by simp [hb'], by simp [ht'], by simp; omega, by simp; omega,
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [arrs_setVar, arrs_setArr, eq_self_iff_true, if_true]
      rw [List.length_set]
      exact hddL'
    · rw [harr plRw (by decide)]
      exact hrwL'
    · intro p hp1 hp2
      rw [harr plRw (by decide)]
      exact hsound' p hp1 hp2
    · intro z hz
      rw [hdd z]
      by_cases hzk : z = (ρ.arrs plRw).getD (ρ.vars "pl.k") 0
      · rw [if_pos hzk]
      · rw [if_neg hzk]
        exact hbound' z hz
    · intro z hz hle
      rw [hdd z] at hle
      by_cases hzk : z = (ρ.arrs plRw).getD (ρ.vars "pl.k") 0
      · rw [if_pos hzk] at hle
        omega
      · rw [if_neg hzk] at hle
        obtain ⟨p, hp1, hp2, hp3⟩ := hcompl' z hz hle
        refine ⟨p, ?_, hp2, by rw [harr plRw (by decide)]; exact hp3⟩
        have hsv : ((ρ.setArr plDd ((ρ.arrs plRw).getD (ρ.vars "pl.k") 0)
            (2 * R + 1)).setVar "pl.k" (ρ.vars "pl.k" + 1)).vars "pl.k"
            = ρ.vars "pl.k" + 1 := by simp
        rw [hsv]
        rcases Nat.eq_or_lt_of_le hp1 with heq | hlt'
        · exfalso
          apply hzk
          rw [← hp3, ← heq]
        · omega
  intro σ hσ
  obtain ⟨hb, htv, hddL, hrwL, hsound, hbound, hcompl⟩ := hσ
  have hr0 : Run B (.assign "pl.k" (.var "pl.b")) σ
      (σ.setVar "pl.k" b₀) 2 := by
    have h := Run.assign (B := B) (x := "pl.k")
      (h := evalB_var (x := "pl.b") (σ := σ) (by omega))
    rw [hb] at h
    exact h.mono (by simp)
  have hI0 : I (σ.setVar "pl.k" b₀) ∧ (σ.setVar "pl.k" b₀).vars "pl.k"
      = b₀ := by
    refine ⟨?_, by simp⟩
    rw [hI]
    refine ⟨by simp [hb], by simp [htv], by simp, by simp [hbt], hddL, hrwL,
      hsound, hbound, ?_⟩
    intro z hz hle
    obtain ⟨p, hp1, hp2, hp3⟩ := hcompl z hz hle
    exact ⟨p, by simp; omega, hp2, hp3⟩
  obtain ⟨σ', hr1, hI', hk'⟩ := (Spec.forRange
    (P := fun ρ => I ρ ∧ ρ.vars "pl.k" = b₀) "pl.k" "pl.t" I t₀ 8
    (12 * (t₀ - b₀) + 4)
    (fun ρ hρ => by rw [hI] at hρ; omega)
    (fun ρ hρ => by rw [hI] at hρ; omega)
    (fun ρ hρ => by rw [hI] at hρ; exact hρ.2.1)
    (fun ρ hρ => by rw [hI] at hρ; omega)
    hbody (fun ρ hρ => hρ.1)
    (fun ρ hρ => by rw [hρ.2]; try omega)).run hI0
  rw [hI] at hI'
  obtain ⟨-, -, -, -, hddL', -, -, hbound', hcompl'⟩ := hI'
  refine ⟨σ', (hr0.seq hr1).mono (by omega), ?_, hddL'⟩
  intro z hz
  have hb' := hbound' z hz
  by_cases hle : (σ'.arrs plDd).getD z 0 ≤ 2 * R
  · obtain ⟨p, hp1, hp2, -⟩ := hcompl' z hz hle
    rw [hk'] at hp1
    omega
  · omega

open Classical in
/-- **One rank of the sweep**: seed, BFS to exhaustion, reset the
touched levels, record the segment end, advance the mass, delete the
centre.  The sweep invariant advances one rank; the cost is the
scanned-edge account plus the fibre. -/
theorem peelStepB_spec
    (hNB : N < B) (hsq : N * N + N + 4 < B) (hRB : 2 * R + 2 < B)
    (hr : 1 ≤ R)
    (hca_dd : ca ≠ plDd) (hca_rw : ca ≠ plRw) (hca_re : ca ≠ plRe)
    (hod_ca : od ≠ ca) (hod_dd : od ≠ plDd) (hod_rw : od ≠ plRw)
    (hod_re : od ≠ plRe)
    (hra_ca : ra ≠ ca) (hra_dd : ra ≠ plDd) (hra_rw : ra ≠ plRw)
    (hra_re : ra ≠ plRe)
    (hao_ca : ao ≠ ca) (hao_dd : ao ≠ plDd) (hao_rw : ao ≠ plRw)
    (hao_re : ao ≠ plRe)
    (haj_ca : aj ≠ ca) (haj_dd : aj ≠ plDd) (haj_rw : aj ≠ plRw)
    (haj_re : aj ≠ plRe)
    (hdg_ca : dg ≠ ca) (hdg_dd : dg ≠ plDd) (hdg_rw : dg ≠ plRw)
    (hdg_re : dg ≠ plRe)
    (hmt_ca : mt ≠ ca) (hmt_dd : mt ≠ plDd) (hmt_rw : mt ≠ plRw)
    (hmt_re : mt ≠ plRe)
    (haj_ao : aj ≠ ao) (hdg_ao : dg ≠ ao) (hmt_ao : mt ≠ ao)
    (haj_dg : aj ≠ dg) (haj_mt : aj ≠ mt) (hdg_mt : dg ≠ mt)
    (hod_aj : od ≠ aj) (hod_dg : od ≠ dg) (hod_mt : od ≠ mt)
    (hra_aj : ra ≠ aj) (hra_dg : ra ≠ dg) (hra_mt : ra ≠ mt)
    {i : ℕ} (hi : i < N) :
    Spec B
      (fun σ => SwInv ca ra ao aj dg mt od G π R i σ ∧ σ.vars "pl.i" = i)
      (peelStepB R ca ao aj dg mt od)
      (fun _ σ' => SwInv ca ra ao aj dg mt od G π R (i + 1) σ' ∧
        σ'.vars "pl.i" = i)
      (64 * peelDeg G π R i + 187 * (pfibR G π R i).ncard + 57) := by
  classical
  rintro σ0 ⟨hSw, hvi0⟩
  set u : Fin N := π.symm ⟨i, hi⟩ with huEq
  have hπu : ((π u : Fin N) : ℕ) = i := by rw [huEq, Equiv.apply_symm_apply]
  -- seed
  obtain ⟨σ1, hrs, hPB1⟩ :=
    (peelSeedB_spec hNB hsq hRB hca_dd hca_rw hca_re hod_ca hod_dd hod_rw
      hra_ca hra_dd hra_rw hao_ca hao_dd hao_rw haj_ca haj_dd haj_rw
      hdg_ca hdg_dd hdg_rw hmt_ca hmt_dd hmt_rw hi).run ⟨hSw, hvi0⟩
  -- the BFS
  obtain ⟨σ2, hrb, hPB2, hhteq⟩ :=
    (peelBfs_loop hNB hsq hRB hca_dd hca_rw hca_re hod_ca hod_dd hod_rw
      hra_ca hra_dd hra_rw hao_ca hao_dd hao_rw haj_ca haj_dd haj_rw
      hdg_ca hdg_dd hdg_rw hmt_ca hmt_dd hmt_rw hi).run hPB1
  obtain ⟨hvn2, hvi2, hvu2, hvb2, hvm2, hhl2, hhle2, hcnt2, hord2, hrank2,
    hadj2, hcaL2, hddL2, hrwL2, hreL2, hreV2, hsegs2, hanch2, hdbd2, hach2,
    hqseg2, hmono2, hreach2, hpopped2, hcaOld2, hcaNew2⟩ := id hPB2
  -- the exact truncated level table at exhaustion
  have hrel : ∀ s w : Fin N, (σ2.arrs plDd).getD ((s : ℕ)) 0 < 2 * R →
      (deleteVerts G (peelSet π i)).Adj s w →
      (σ2.arrs plDd).getD ((w : ℕ)) 0 ≤
        (σ2.arrs plDd).getD ((s : ℕ)) 0 + 1 := by
    intro s w hs hadjsw
    obtain ⟨p, hp1, hp2, hp3⟩ := hqseg2.2.1 s (le_of_lt hs)
    have hp3' : (σ2.arrs plRw).getD p 0 = (s : ℕ) := hp3
    have hpN : (σ2.arrs plRw).getD p 0 < N := by rw [hp3']; exact s.isLt
    have hph : p < σ2.vars "pl.h" := by rw [hhteq]; exact hp2
    have h := hpopped2 p hp1 hph hpN (by rw [hp3']; exact hs) w (by
      have hFin : (⟨(σ2.arrs plRw).getD p 0, hpN⟩ : Fin N) = s :=
        Fin.ext hp3'
      rw [hFin]
      exact hadjsw)
    rw [hp3'] at h
    exact h
  have hexact := bfs_exact (H := deleteVerts G (peelSet π i)) (u := u)
    (D := fun z => (σ2.arrs plDd).getD z 0) (r := 2 * R) hanch2 hach2 hrel
  have hpfib : pfibR G π R i =
      ball (deleteVerts G (peelSet π i)) (2 * R) u := by
    rw [pfibR_eq G π R hi, ← huEq, pfib_eq_ball, hπu]
  have hlist_eq : {z : Fin N | (σ2.arrs plDd).getD ((z : ℕ)) 0 ≤ 2 * R}
      = pfibR G π R i := by
    ext v
    rw [Set.mem_setOf_eq, hpfib]
    exact hexact (2 * R) le_rfl v
  have hcard := SegAt.card hqseg2
  rw [hlist_eq] at hcard
  have ht2 : σ2.vars "pl.t" = mval G π R (i + 1) := by
    rw [mval_succ]
    omega
  have hub : mval G π R (i + 1) ≤ N * N := by
    have h1 : mval G π R (i + 1) ≤ (i + 1) * N := mval_le G π R
    have h2 : (i + 1) * N ≤ N * N :=
      Nat.mul_le_mul (Nat.succ_le_of_lt hi) le_rfl
    omega
  have hmv_le : mval G π R i ≤ mval G π R (i + 1) :=
    mval_mono G π R (Nat.le_succ i)
  -- the reset, with its frame
  have hpre3 : σ2.vars "pl.b" = mval G π R i ∧
      σ2.vars "pl.t" = mval G π R (i + 1) ∧
      N ≤ (σ2.arrs plDd).length ∧ N * N ≤ (σ2.arrs plRw).length ∧
      (∀ p, mval G π R i ≤ p → p < mval G π R (i + 1) →
        (σ2.arrs plRw).getD p 0 < N) ∧
      (∀ z, z < N → (σ2.arrs plDd).getD z 0 ≤ 2 * R + 1) ∧
      (∀ z, z < N → (σ2.arrs plDd).getD z 0 ≤ 2 * R →
        ∃ p, mval G π R i ≤ p ∧ p < mval G π R (i + 1) ∧
          (σ2.arrs plRw).getD p 0 = z) := by
    refine ⟨hvb2, ht2, hddL2, hrwL2, ?_, hdbd2, ?_⟩
    · intro p hp1 hp2
      obtain ⟨hz, -⟩ := hqseg2.1 p hp1 (by rw [ht2]; exact hp2)
      exact hz
    · intro z hz hle
      obtain ⟨p, hp1, hp2, hp3⟩ := hqseg2.2.1 ⟨z, hz⟩ hle
      exact ⟨p, hp1, by rw [← ht2]; exact hp2, hp3⟩
  obtain ⟨σ3, hrr, ⟨hsen3, hddL3⟩, hfv3, hfa3, -, -⟩ :=
    ((peelResetB_spec (B := B) (b₀ := mval G π R i)
      (t₀ := mval G π R (i + 1)) hsq hRB hmv_le hub).frame).run hpre3
  have hfv3' : ∀ y, y ≠ "pl.k" → σ3.vars y = σ2.vars y := by
    intro y hy
    refine hfv3 y ?_
    simp [peelResetB, Com.wvars, hy]
  have hfa3' : ∀ a', a' ≠ plDd → σ3.arrs a' = σ2.arrs a' := by
    intro a' ha'
    refine hfa3 a' ?_
    simp [peelResetB, Com.warrs, ha']
  have h3i : σ3.vars "pl.i" = i := by
    rw [hfv3' "pl.i" (by decide)]; exact hvi2
  have h3t : σ3.vars "pl.t" = mval G π R (i + 1) := by
    rw [hfv3' "pl.t" (by decide)]; exact ht2
  have h3reL : N + 1 ≤ (σ3.arrs plRe).length := by
    rw [hfa3' plRe (by decide)]
    exact hreL2
  -- the segment end
  set σ4 : Env := σ3.setArr plRe (i + 1) (mval G π R (i + 1)) with hσ4
  have hr4 : Run B (.store plRe (.add (.var "pl.i") (.lit 1))
      (.var "pl.t")) σ3 σ4 5 := by
    have hidx : (Expr.add (.var "pl.i") (.lit 1)).evalB B σ3
        = some (i + 1) := by
      have h := evalB_incr (B := B) (x := "pl.i") (σ := σ3)
        (by rw [h3i]; omega)
      rwa [h3i] at h
    have hval : (Expr.var "pl.t").evalB B σ3
        = some (mval G π R (i + 1)) := by
      have h := evalB_var (B := B) (x := "pl.t") (σ := σ3)
        (by rw [h3t]; omega)
      rwa [h3t] at h
    have h := Run.store (B := B) (a := plRe) (idx := i + 1)
      (v := mval G π R (i + 1)) (hi := hidx) (he := hval)
      (hidx := by omega)
    exact h.mono (by simp)
  -- the mass advance
  set σ5 : Env := σ4.setVar "pl.m" (mval G π R (i + 1)) with hσ5
  have h4t : σ4.vars "pl.t" = mval G π R (i + 1) := by
    rw [hσ4]
    simp only [vars_setArr]
    exact h3t
  have hr5 : Run B (.assign "pl.m" (.var "pl.t")) σ4 σ5 2 := by
    have h := Run.assign (B := B) (x := "pl.m")
      (h := evalB_var (x := "pl.t") (σ := σ4) (by rw [h4t]; omega))
    rw [h4t] at h
    exact h.mono (by simp)
  -- state facts carried to the deletion
  have hv54 : ∀ y, y ≠ "pl.m" → σ5.vars y = σ3.vars y := by
    intro y hy
    rw [hσ5]
    simp only [vars_setVar]
    rw [if_neg hy, hσ4]
    simp only [vars_setArr]
  have ha54 : ∀ a', a' ≠ plRe → σ5.arrs a' = σ3.arrs a' := by
    intro a' ha'
    rw [hσ5, hσ4]
    simp only [arrs_setVar, arrs_setArr]
    rw [if_neg ha']
  have h5u : σ5.vars "pl.u" = (u : ℕ) := by
    rw [hv54 "pl.u" (by decide), hfv3' "pl.u" (by decide)]
    exact hvu2
  have hDel5 : DelAdjSt ao aj dg mt G (peelSet π i) σ5 :=
    hadj2.of_eq ((ha54 ao hao_re).trans (hfa3' ao hao_dd))
      ((ha54 aj haj_re).trans (hfa3' aj haj_dd))
      ((ha54 dg hdg_re).trans (hfa3' dg hdg_dd))
      ((ha54 mt hmt_re).trans (hfa3' mt hmt_dd))
  -- the deletion, with its frame
  obtain ⟨σ6, hrd, hDel6, hfv6, hfa6, -, -⟩ :=
    ((peelDelB_spec (u := u) hNB hsq haj_ao hdg_ao hmt_ao haj_dg haj_mt
      hdg_mt (symm_not_peeled π hi)).frame).run ⟨hDel5, h5u⟩
  have hfa6' : ∀ a', a' ≠ aj → a' ≠ mt → a' ≠ dg →
      σ6.arrs a' = σ5.arrs a' := by
    intro a' h1 h2 h3
    refine hfa6 a' ?_
    simp [peelDelB, peelDelTurnB, Com.warrs, h1, h2, h3]
  have hArr : ∀ a', a' ≠ plDd → a' ≠ plRe → a' ≠ aj → a' ≠ mt → a' ≠ dg →
      σ6.arrs a' = σ2.arrs a' := by
    intro a' h1 h2 h3 h4 h5
    rw [hfa6' a' h3 h4 h5, ha54 a' h2]
    exact hfa3' a' h1
  have h6i : σ6.vars "pl.i" = i := by
    rw [hfv6 "pl.i" (by simp [peelDelB, peelDelTurnB, Com.wvars]),
      hv54 "pl.i" (by decide), hfv3' "pl.i" (by decide)]
    exact hvi2
  have h6n : σ6.vars "pl.n" = N := by
    rw [hfv6 "pl.n" (by simp [peelDelB, peelDelTurnB, Com.wvars]),
      hv54 "pl.n" (by decide), hfv3' "pl.n" (by decide)]
    exact hvn2
  have h6m : σ6.vars "pl.m" = mval G π R (i + 1) := by
    rw [hfv6 "pl.m" (by simp [peelDelB, peelDelTurnB, Com.wvars]), hσ5]
    simp
  -- the level region and the segment record after the walk
  have hDd6arr : σ6.arrs plDd = σ3.arrs plDd :=
    (hfa6' plDd (Ne.symm haj_dd) (Ne.symm hmt_dd) (Ne.symm hdg_dd)).trans
      (ha54 plDd (by decide))
  have hRe6arr : σ6.arrs plRe
      = (σ3.arrs plRe).set (i + 1) (mval G π R (i + 1)) := by
    rw [hfa6' plRe (Ne.symm haj_re) (Ne.symm hmt_re) (Ne.symm hdg_re),
      hσ5, hσ4]
    simp only [arrs_setVar, arrs_setArr, eq_self_iff_true, if_true]
  have hRw6arr : σ6.arrs plRw = σ2.arrs plRw :=
    hArr plRw (by decide) (by decide) (Ne.symm haj_rw) (Ne.symm hmt_rw)
      (Ne.symm hdg_rw)
  -- the new segment
  have hseg_i : SegAt (fun p => (σ2.arrs plRw).getD p 0) (mval G π R i)
      (mval G π R (i + 1)) (pfibR G π R i) := by
    have h := hqseg2
    rw [ht2, hlist_eq] at h
    exact h
  -- the assignment region advances
  have hCa6arr : σ6.arrs ca = σ2.arrs ca :=
    hArr ca hca_dd hca_re (Ne.symm haj_ca) (Ne.symm hmt_ca) (Ne.symm hdg_ca)
  have hCa6 : ∀ v : Fin N, (σ6.arrs ca).getD ((v : ℕ)) 0 =
      if ((π (pctr G π R v) : ℕ)) < i + 1
        then ((pctr G π R v : Fin N) : ℕ) else N := by
    intro v
    rw [hCa6arr]
    by_cases hlt : ((π (pctr G π R v) : ℕ)) < i
    · rw [if_pos (by omega)]
      exact hcaOld2 v hlt
    · rcases hcaNew2 v hlt with ⟨hddv, hcav⟩ | ⟨hddv, hcav⟩
      · -- freshly discovered within radius `R`: the centre is `u`
        have hball : v ∈ ball (deleteVerts G (peelSet π i)) R u :=
          (hexact R (by omega) v).mp hddv
        have hwr : u ∈ wreach G π R v := by
          rw [Impl.mem_wreach_iff_mem_peeledBall, ← peelSet_rank π u, hπu]
          exact hball
        have hle' : ((π (pctr G π R v) : Fin N) : ℕ) ≤ i := by
          have h : ((π (pctr G π R v) : Fin N) : ℕ) ≤ ((π u : Fin N) : ℕ) :=
            CoverCentres.ctr_le_of_mem_wreach hwr
          rw [hπu] at h
          exact h
        have hctr : pctr G π R v = u :=
          π.injective (Fin.ext (by rw [hπu]; omega))
        rw [if_pos (by omega), hctr]
        exact hcav
      · -- beyond radius `R`: not this rank's centre, still unassigned
        have hnot : ¬ ((π (pctr G π R v) : ℕ)) < i + 1 := by
          intro hlt'
          have hctr : pctr G π R v = u :=
            π.injective (Fin.ext (by rw [hπu]; omega))
          have hwr : u ∈ wreach G π R v := by
            rw [← hctr]
            exact CoverCentres.ctr_mem_wreach G π R v
          rw [Impl.mem_wreach_iff_mem_peeledBall, ← peelSet_rank π u, hπu]
            at hwr
          exact hddv ((hexact R (by omega) v).mpr hwr)
        rw [if_neg hnot]
        exact hcav
  -- the deletion account closes into the fibre
  have hcur : ((deleteVerts G (peelSet π i)).neighborSet u).ncard
      ≤ (pfibR G π R i).ncard := by
    have h := curdeg_le_pfib G π R hr u
    rw [hπu] at h
    rw [pfibR_eq G π R hi, ← huEq]
    exact h
  -- assemble
  refine ⟨σ6, ?_, ⟨h6n, h6m, by omega, ?_, ?_, ?_, ?_, hCa6, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, h6i⟩
  · -- the run, at the step budget
    have hms := mval_succ G π R i
    exact (hrs.seq (hrb.seq (hrr.seq (hr4.seq (hr5.seq hrd))))).mono
      (by omega)
  · exact ordArr_of_eq hord2
      (hArr od hod_dd hod_re hod_aj hod_mt hod_dg)
  · exact rankArr_of_eq hrank2
      (hArr ra hra_dd hra_re hra_aj hra_mt hra_dg)
  · rw [peelSet_succ π hi]
    exact hDel6
  · rw [hCa6arr]
    exact hcaL2
  · rw [hDd6arr]
    exact hddL3
  · intro z hz
    rw [hDd6arr]
    exact hsen3 z hz
  · rw [hRw6arr]
    exact hrwL2
  · rw [hRe6arr, List.length_set]
    exact h3reL
  · intro i' hi'
    rw [hRe6arr, getD_set (σ3.arrs plRe) (mval G π R (i + 1)) i' (by omega)]
    by_cases hii : i' = i + 1
    · rw [if_pos hii, hii]
    · rw [if_neg hii, hfa3' plRe (by decide)]
      exact hreV2 i' (by omega)
  · intro i' hi'
    rw [hRw6arr]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | h
    · exact hsegs2 i' h
    · rw [h]
      exact hseg_i

end SweepMachine

end Lax3Proofs.Prog

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax12.ColoringNumbers
open Lax3Proofs.WalkDistance
open Lax3Proofs.SplitterBasics (deleteVerts_adj)

theorem peel_forRangeSum {B N : ℕ} {c : Com} (x m : String)
    (I : Env → Prop) (k : ℕ → ℕ) (hNB : N < B)
    (hb : ∀ σ, I σ → σ.vars m = N ∧ σ.vars x ≤ N)
    (hstep : ∀ i, i < N → Spec B (fun σ => I σ ∧ σ.vars x = i) c
      (fun _ σ' => I σ' ∧ σ'.vars x = i + 1) (k i)) :
    Spec B (fun σ => I σ ∧ σ.vars x = 0)
      (.while (.lt (.var x) (.var m)) c)
      (fun _ σ' => I σ' ∧ σ'.vars x = N)
      ((∑ i ∈ Finset.range N, (k i + 4)) + 4) := by
  refine (Spec.while_potential I
    (fun σ => ∑ i ∈ Finset.Ico (σ.vars x) N, (k i + 4))
    (fun σ hI => by have := hb σ hI; exact evalB_condLt_vars (by omega) (by omega))
    ?_ (fun _ h => h.1) ?_).post ?_
  · intro σ hI htrue
    have hi : σ.vars x < N := by
      have := lt_of_condLt_true htrue
      have := hb σ hI
      omega
    obtain ⟨σ', hrun, hI', hx'⟩ := (hstep _ hi).run ⟨hI, rfl⟩
    refine ⟨σ', k (σ.vars x), hrun, hI', ?_⟩
    dsimp only
    rw [hx', Finset.sum_eq_sum_Ico_succ_bot hi]
    simp only [Cond.size, Expr.size]
    omega
  · rintro σ ⟨hI, hx⟩
    dsimp only
    rw [hx, Finset.range_eq_Ico]
    simp only [Cond.size, Expr.size]
    omega
  · rintro σ σ' _ ⟨hI, hf⟩
    have := le_of_condLt_false hf
    have := hb σ' hI
    exact ⟨hI, by omega⟩

/-- The prologue fills the two sentinels once, then anchors the member stream. -/
theorem peelInitB_arrays_spec {B N R : ℕ} {nNs ca : String}
    (hNB : N + 1 < B) (hRB : 2 * R + 2 < B)
    (hca_dd : ca ≠ plDd) (hca_re : ca ≠ plRe) :
    Spec B (fun σ => σ.vars nNs = N ∧ N ≤ (σ.arrs ca).length ∧
        N ≤ (σ.arrs plDd).length ∧ N + 1 ≤ (σ.arrs plRe).length)
      (peelInitB R nNs ca)
      (fun _ σ' => σ'.vars "pl.n" = N ∧ σ'.vars "pl.m" = 0 ∧
        (∀ z, z < N → (σ'.arrs ca).getD z 0 = N) ∧
        (∀ z, z < N → (σ'.arrs plDd).getD z 0 = 2 * R + 1) ∧
        (σ'.arrs plRe).getD 0 0 = 0)
      (14 * N + 13) := by
  let I : Env → Prop := fun σ => σ.vars "pl.n" = N ∧ σ.vars "pl.i" ≤ N ∧
    N ≤ (σ.arrs ca).length ∧ N ≤ (σ.arrs plDd).length ∧
    (∀ z, z < σ.vars "pl.i" → (σ.arrs ca).getD z 0 = N) ∧
    (∀ z, z < σ.vars "pl.i" → (σ.arrs plDd).getD z 0 = 2 * R + 1)
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "pl.i" < N)
      (.seq (.store plDd (.var "pl.i") (.lit (2 * R + 1)))
        (.seq (.store ca (.var "pl.i") (.var "pl.n"))
          (.assign "pl.i" (.add (.var "pl.i") (.lit 1)))))
      (fun σ σ' => I σ' ∧ σ'.vars "pl.i" = σ.vars "pl.i" + 1) 10 := by
    rintro σ ⟨⟨hn, hi, hca, hdd, hcav, hddv⟩, hiN⟩
    run_vcg
    dsimp [I]
    simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr]
    simp only [show ("pl.n" : String) ≠ "pl.i" by decide, if_false, if_true,
      hca_dd, Ne.symm hca_dd, List.length_set]
    refine ⟨⟨hn, by omega, hca, hdd, ?_, ?_⟩, by trivial⟩
    · intro z hz
      rw [getD_set _ _ _ (by omega)]
      split_ifs with he
      · exact hn
      · exact hcav z (by omega)
    · intro z hz
      rw [getD_set _ _ _ (by omega)]
      split_ifs with he
      · rfl
      · exact hddv z (by omega)
    all_goals simp [hca_dd]; omega
  have hscan := Spec.forRange "pl.i" "pl.n" I N 10 (14 * N + 4)
    (fun σ h => by have := h.2.1; omega)
    (fun σ h => by rw [h.1]; omega)
    (fun σ h => h.1) (fun σ h => h.2.1) hbody
    (P := fun σ => I σ ∧ σ.vars "pl.i" = 0)
    (fun _ h => h.1) (fun σ h => by rw [h.2]; simp)
  rintro σ ⟨hn, hca, hdd, hre⟩
  have hr0 : Run B (.assign "pl.n" (.var nNs)) σ (σ.setVar "pl.n" N) 2 := by
    have h := Run.assign (x := "pl.n") (evalB_var (B := B) (x := nNs)
      (σ := σ) (by omega))
    simpa [hn] using h
  have hri : Run B (.assign "pl.i" (.lit 0)) (σ.setVar "pl.n" N)
      ((σ.setVar "pl.n" N).setVar "pl.i" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  obtain ⟨σ1, hr1, hI1, hi1⟩ := hscan.run
    (σ := (σ.setVar "pl.n" N).setVar "pl.i" 0) (by simp [I, hca, hdd])
  have hfr := hr1.frame_arr plRe (by
    simp only [Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil]
    simp [Ne.symm hca_re, show plRe ≠ plDd by decide])
  have hre1 : N + 1 ≤ (σ1.arrs plRe).length := by rw [hfr]; exact hre
  have hr2 : Run B
      (.seq (.assign "pl.m" (.lit 0)) (.store plRe (.lit 0) (.lit 0))) σ1
      ((σ1.setVar "pl.m" 0).setArr plRe 0 0) 5 := by
    exact (Run.assign (B := B) (x := "pl.m") (σ := σ1)
      (evalB_lit (n := 0) (by omega))).seq
      (Run.store (B := B) (a := plRe) (σ := σ1.setVar "pl.m" 0)
        (evalB_lit (n := 0) (by omega)) (evalB_lit (n := 0) (by omega))
        (by simpa using Nat.lt_of_lt_of_le (by omega : 0 < N + 1) hre1))
  refine ⟨_, (hr0.seq (hri.seq (hr1.seq hr2))).mono (by omega), ?_⟩
  rcases hI1 with ⟨hn1, _, _, _, hca1, hdd1⟩
  simp only [vars_setArr, vars_setVar, arrs_setArr, arrs_setVar]
  simp only [show ("pl.n" : String) ≠ "pl.m" by decide, if_false, if_true,
    hca_re, show plDd ≠ plRe by decide]
  refine ⟨hn1, by trivial, ?_, ?_, ?_⟩
  · intro z hz; exact hca1 z (by omega)
  · intro z hz; exact hdd1 z (by omega)
  · rw [getD_set _ _ _ (by omega), if_pos rfl]

end Lax3Proofs.Prog

namespace Lax3Proofs.Prog
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding
open Lax12.ColoringNumbers
open Lax12.UniformQuasiWideness (deleteVerts)

private theorem peel_swInv_set_i {N : ℕ} {G : SimpleGraph (Fin N)}
    {π : Equiv.Perm (Fin N)} {R i v : ℕ} {ca ra ao aj dg mt od : String} {σ : Env}
    (h : SwInv ca ra ao aj dg mt od G π R i σ) :
    SwInv ca ra ao aj dg mt od G π R i (σ.setVar "pl.i" v) := by
  simpa [SwInv, OrdArr, RankArr, DelAdjSt] using h

/-- The complete ascending rank sweep, priced by the sum of live scans. -/
theorem peelSweepB_spec {B N R : ℕ} {G : SimpleGraph (Fin N)}
    {π : Equiv.Perm (Fin N)} {ca ra ao aj dg mt od : String}
    (hsq : N * N + N + 4 < B) (hRB : 2 * R + 2 < B) (hr : 1 ≤ R)
    (hd : [ca, ra, ao, aj, dg, mt, od, plDd, plRw, plRe].Nodup) :
    Spec B (SwInv ca ra ao aj dg mt od G π R 0)
      (peelSweepB R ca ao aj dg mt od)
      (fun _ σ' => SwInv ca ra ao aj dg mt od G π R N σ')
      ((∑ i ∈ Finset.range N,
        (64 * peelDeg G π R i + 187 * (pfibR G π R i).ncard + 65)) + 6) := by
  let I : Env → Prop := fun σ => SwInv ca ra ao aj dg mt od G π R (σ.vars "pl.i") σ
  let K : ℕ → ℕ := fun i => 64 * peelDeg G π R i + 187 * (pfibR G π R i).ncard + 61
  have hstep : ∀ i, i < N → Spec B (fun σ => I σ ∧ σ.vars "pl.i" = i)
      (.seq (peelStepB R ca ao aj dg mt od)
        (.assign "pl.i" (.add (.var "pl.i") (.lit 1))))
      (fun _ σ' => I σ' ∧ σ'.vars "pl.i" = i + 1) (K i) := by
    intro i hi
    have hs : Spec B
        (fun σ => SwInv ca ra ao aj dg mt od G π R i σ ∧ σ.vars "pl.i" = i)
        (peelStepB R ca ao aj dg mt od)
        (fun _ σ' => SwInv ca ra ao aj dg mt od G π R (i + 1) σ' ∧ σ'.vars "pl.i" = i)
        (64 * peelDeg G π R i + 187 * (pfibR G π R i).ncard + 57) := by
      apply peelStepB_spec (by omega) hsq hRB hr <;>
        first | exact hi | simp_all only [List.nodup_cons, List.mem_cons,
          List.not_mem_nil, not_or, not_false_eq_true, and_true, List.nodup_nil]; aesop
    rintro σ ⟨hI, hvi⟩
    obtain ⟨σ', hrun, hpost, hvi'⟩ := hs.run ⟨by simpa [I, hvi] using hI, hvi⟩
    have hinc : Run B (.assign "pl.i" (.add (.var "pl.i") (.lit 1))) σ'
        (σ'.setVar "pl.i" (i + 1)) 4 := by
      have hev : (Expr.add (.var "pl.i") (.lit 1)).evalB B σ' = some (i + 1) := by
        have h := evalB_bin (op := .add) (e := Expr.var "pl.i") (f := Expr.lit 1)
          (B := B) (σ := σ') (evalB_var (by omega)) (evalB_lit (by omega)) (by
            simp only [Bop.apply_add]; omega)
        simpa [hvi'] using h
      exact Run.assign hev
    refine ⟨_, (hrun.seq hinc).mono (by dsimp [K]; omega), ?_, by simp⟩
    dsimp [I]
    simpa using (peel_swInv_set_i (v := i + 1) hpost)
  have hloop := peel_forRangeSum "pl.i" "pl.n" I K (by omega)
    (fun σ h => ⟨h.1, h.2.2.1⟩) hstep
  intro σ hσ
  have hinit : Run B (.assign "pl.i" (.lit 0)) σ (σ.setVar "pl.i" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  obtain ⟨σ', hrun, hI', hN'⟩ := hloop.run
    ⟨by dsimp [I]; simpa using (peel_swInv_set_i (v := 0) hσ), by simp⟩
  refine ⟨σ', (hinit.seq hrun).mono ?_, ?_⟩
  · dsimp [K]
    norm_num only [Nat.add_assoc]
    omega
  · simpa [I, hN'] using hI'

/-- The initialized sweep invariant uses only allocation and built-region facts. -/
theorem peelInitB_spec {B N R : ℕ} {G : SimpleGraph (Fin N)}
    {π : Equiv.Perm (Fin N)} {nNs ca ra ao aj dg mt od : String}
    (hsq : N * N + N + 4 < B) (hRB : 2 * R + 2 < B)
    (hd : [ca, ra, ao, aj, dg, mt, od, plDd, plRw, plRe].Nodup) :
    Spec B (fun σ => σ.vars nNs = N ∧ OrdArr od π σ ∧ RankArr ra π σ ∧
        DelAdjSt ao aj dg mt G ∅ σ ∧ N ≤ (σ.arrs ca).length ∧
        N ≤ (σ.arrs plDd).length ∧ N * N ≤ (σ.arrs plRw).length ∧
        N + 1 ≤ (σ.arrs plRe).length)
      (peelInitB R nNs ca)
      (fun _ σ' => SwInv ca ra ao aj dg mt od G π R 0 σ') (14 * N + 13) := by
  have hcd : ca ≠ plDd := by
    simp_all only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      not_false_eq_true, and_true, List.nodup_nil]; aesop
  have hcr : ca ≠ plRe := by
    simp_all only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      not_false_eq_true, and_true, List.nodup_nil]; aesop
  rintro σ ⟨hn, hord, hra, hadj, hca, hdd, hrw, hre⟩
  obtain ⟨σ', hrun, hn', hm', hca', hdd', hre'⟩ :=
    (peelInitB_arrays_spec (by omega) hRB hcd hcr).run ⟨hn, hca, hdd, hre⟩
  have hframe : ∀ a, a ≠ ca → a ≠ plDd → a ≠ plRe → σ'.arrs a = σ.arrs a := by
    intro a h1 h2 h3
    exact hrun.frame_arr a (by simp [peelInitB, Com.warrs, h1, h2, h3])
  have hlen := run_arrs_length_eq hrun
  have hfr : ∀ a ∈ [ra, ao, aj, dg, mt, od], σ'.arrs a = σ.arrs a := by
    intro a ha
    apply hframe <;> simp_all only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, and_true, List.nodup_nil] <;> aesop
  refine ⟨σ', hrun, hn', ?_, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, hdd', ?_, ?_, ?_, ?_⟩
  · simpa [mval_zero] using hm'
  · exact ordArr_of_eq hord (hfr od (by simp))
  · exact rankArr_of_eq hra (hfr ra (by simp))
  · rw [peelSet_zero]
    exact hadj.of_eq (hfr ao (by simp)) (hfr aj (by simp))
      (hfr dg (by simp)) (hfr mt (by simp))
  · rw [hlen]; exact hca
  · intro v; simpa using hca' v v.isLt
  · rw [hlen]; exact hdd
  · rw [hlen]; exact hrw
  · rw [hlen]; exact hre
  · intro i hi
    have : i = 0 := by omega
    subst i
    simpa [mval_zero] using hre'
  · intro i hi; omega

end Lax3Proofs.Prog

namespace Lax3Proofs.Prog
set_option linter.unusedSimpArgs false
open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax12.ColoringNumbers

/-- Occurrences of one member in a prefix of the emitted stream. -/
def peelOcc (f : ℕ → ℕ) (z k : ℕ) : ℕ :=
  ∑ p ∈ Finset.range k, if f p = z then 1 else 0

@[simp] theorem peelOcc_zero (f : ℕ → ℕ) (z : ℕ) : peelOcc f z 0 = 0 := rfl

theorem peelOcc_succ (f : ℕ → ℕ) (z k : ℕ) :
    peelOcc f z (k + 1) = peelOcc f z k + if f k = z then 1 else 0 :=
  Finset.sum_range_succ _ k

theorem peelOcc_mono (f : ℕ → ℕ) (z : ℕ) {i j : ℕ} (h : i ≤ j) :
    peelOcc f z i ≤ peelOcc f z j := by
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem peelOcc_le (f : ℕ → ℕ) (z k : ℕ) : peelOcc f z k ≤ k := by
  calc peelOcc f z k ≤ ∑ _p ∈ Finset.range k, 1 :=
      Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
    _ = k := by simp

theorem peelOcc_strict (f : ℕ → ℕ) {p q : ℕ} (hpq : p < q) :
    peelOcc f (f p) p < peelOcc f (f p) q := by
  have h := peelOcc_mono f (f p) (Nat.succ_le_of_lt hpq)
  rw [peelOcc_succ, if_pos rfl] at h
  omega

/-- Counting all member buckets counts each stream entry exactly once. -/
theorem peelOcc_sum {N k : ℕ} {f : ℕ → ℕ} (hf : ∀ p, p < k → f p < N) :
    ∑ z ∈ Finset.range N, peelOcc f z k = k := by
  unfold peelOcc
  rw [Finset.sum_comm]
  have hh : ∀ p ∈ Finset.range k,
      (∑ z ∈ Finset.range N, if f p = z then 1 else 0) = 1 := by
    intro p hp
    simp [Finset.sum_ite_eq, hf p (Finset.mem_range.mp hp)]
  rw [Finset.sum_congr rfl hh]
  simp

/-- Prefix offsets of the member-major buckets. -/
def peelIOff (f : ℕ → ℕ) (M z : ℕ) : ℕ :=
  ∑ w ∈ Finset.range z, peelOcc f w M

@[simp] theorem peelIOff_zero (f : ℕ → ℕ) (M : ℕ) : peelIOff f M 0 = 0 := rfl

theorem peelIOff_succ (f : ℕ → ℕ) (M z : ℕ) :
    peelIOff f M (z + 1) = peelIOff f M z + peelOcc f z M :=
  Finset.sum_range_succ _ z

theorem peelIOff_mono (f : ℕ → ℕ) (M : ℕ) {i j : ℕ} (h : i ≤ j) :
    peelIOff f M i ≤ peelIOff f M j :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem peelIOff_last {N M : ℕ} {f : ℕ → ℕ} (hf : ∀ p, p < M → f p < N) :
    peelIOff f M N = M := peelOcc_sum hf

theorem peelIOff_le {N M : ℕ} {f : ℕ → ℕ} (hf : ∀ p, p < M → f p < N)
    {z : ℕ} (hz : z ≤ N) : peelIOff f M z ≤ M := by
  exact (peelIOff_mono f M hz).trans_eq (peelIOff_last hf)

/-- Regroup pass 1 initializes only the inverse count prefix. -/
theorem peelP1B_spec {B N : ℕ} (hNB : N < B) :
    Spec B (fun σ => σ.vars "pl.n" = N ∧ N ≤ (σ.arrs plDz).length)
      peelP1B (fun _ σ' => ∀ z, z < N → (σ'.arrs plDz).getD z 0 = 0)
      (11 * N + 6) := by
  let I : Env → Prop := fun σ => σ.vars "pl.n" = N ∧ σ.vars "pl.i" ≤ N ∧
    N ≤ (σ.arrs plDz).length ∧ ∀ z, z < σ.vars "pl.i" → (σ.arrs plDz).getD z 0 = 0
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "pl.i" < N)
      (.seq (.store plDz (.var "pl.i") (.lit 0))
        (.assign "pl.i" (.add (.var "pl.i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "pl.i" = σ.vars "pl.i" + 1) 7 := by
    rintro σ ⟨⟨hn, hi, hL, hv⟩, hiN⟩
    run_vcg
    dsimp [I]
    simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr]
    simp only [show ("pl.n" : String) ≠ "pl.i" by decide, if_false, if_true,
      List.length_set]
    refine ⟨⟨hn, by omega, hL, ?_⟩, by trivial⟩
    intro z hz
    rw [getD_set _ _ _ (by omega)]
    split_ifs with h
    · rfl
    · exact hv z (by omega)
  refine (Spec.forRangeZero "pl.i" "pl.n" I N 7 hNB
    (fun _ h => h.2.1) (fun _ h => h.1) hbody).conseq ?_ ?_ (by omega)
  · rintro σ ⟨hn, hL⟩
    simp [I, hn, hL]
  · rintro σ σ' _ ⟨hI, hi⟩ z hz
    exact hI.2.2.2 z (by omega)

/-- Regroup pass 2 counts the complete emitted stream once. -/
theorem peelP2B_spec {B N M : ℕ} {f : ℕ → ℕ}
    (hNB : N < B) (hMB : M + 1 < B) (hf : ∀ p, p < M → f p < N) :
    Spec B (fun σ => σ.vars "pl.m" = M ∧ N ≤ (σ.arrs plDz).length ∧
        M ≤ (σ.arrs plRw).length ∧
        (∀ p, p < M → (σ.arrs plRw).getD p 0 = f p) ∧
        (∀ z, z < N → (σ.arrs plDz).getD z 0 = 0))
      peelP2B (fun _ σ' => ∀ z, z < N → (σ'.arrs plDz).getD z 0 = peelOcc f z M)
      (16 * M + 6) := by
  let I : Env → Prop := fun σ => σ.vars "pl.m" = M ∧ σ.vars "pl.k" ≤ M ∧
    N ≤ (σ.arrs plDz).length ∧ M ≤ (σ.arrs plRw).length ∧
    (∀ p, p < M → (σ.arrs plRw).getD p 0 = f p) ∧
    (∀ z, z < N → (σ.arrs plDz).getD z 0 = peelOcc f z (σ.vars "pl.k"))
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "pl.k" < M)
      (.seq (.store plDz (.get plRw (.var "pl.k"))
          (.add (.get plDz (.get plRw (.var "pl.k"))) (.lit 1)))
        (.assign "pl.k" (.add (.var "pl.k") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "pl.k" = σ.vars "pl.k" + 1) 12 := by
    rintro σ ⟨⟨hm, hk, hzL, hrL, hrv, hzv⟩, hkM⟩
    have hfk := hf _ hkM
    have hrk := hrv _ hkM
    have hzk : (σ.arrs plDz).getD ((σ.arrs plRw).getD (σ.vars "pl.k") 0) 0
        = peelOcc f (f (σ.vars "pl.k")) (σ.vars "pl.k") := by
      rw [hrk, hzv _ hfk]
    have hzkB := peelOcc_le f (f (σ.vars "pl.k")) (σ.vars "pl.k")
    run_vcg
    dsimp [I]
    simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr]
    simp only [show ("pl.m" : String) ≠ "pl.k" by decide, if_false, if_true,
      show plRw ≠ plDz by decide, List.length_set]
    refine ⟨⟨hm, by omega, hzL, hrL, hrv, ?_⟩, by trivial⟩
    intro z hz
    rw [getD_set _ _ _ (by omega), peelOcc_succ]
    rw [hrk, hzv _ hfk]
    by_cases he : z = f (σ.vars "pl.k")
    · subst z
      simp
    · rw [if_neg he, if_neg (Ne.symm he)]
      exact hzv z hz
  refine (Spec.forRangeZero "pl.k" "pl.m" I M 12 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) hbody).conseq ?_ ?_ (by omega)
  · rintro σ ⟨hm, hzL, hrL, hrv, hzv⟩
    simpa [I, hm] using And.intro hzL (And.intro hrL (And.intro hrv hzv))
  · rintro σ σ' _ ⟨hI, hk⟩ z hz
    simpa [hk] using hI.2.2.2.2.2 z hz

/-- Copy a carrier-sized prefix, used for the two cursor initializations. -/
theorem peel_copy_spec {B N : ℕ} {src dst : String} {v : ℕ → ℕ}
    (hNB : N < B) (hne : src ≠ dst) (hvB : ∀ z, z < N → v z < B) :
    Spec B (fun σ => σ.vars "pl.n" = N ∧ N ≤ (σ.arrs src).length ∧
        N ≤ (σ.arrs dst).length ∧ ∀ z, z < N → (σ.arrs src).getD z 0 = v z)
      (.seq (.assign "pl.i" (.lit 0))
        (.while (.lt (.var "pl.i") (.var "pl.n"))
          (.seq (.store dst (.var "pl.i") (.get src (.var "pl.i")))
            (.assign "pl.i" (.add (.var "pl.i") (.lit 1))))))
      (fun _ σ' => ∀ z, z < N → (σ'.arrs dst).getD z 0 = v z) (12 * N + 6) := by
  let I : Env → Prop := fun σ => σ.vars "pl.n" = N ∧ σ.vars "pl.i" ≤ N ∧
    N ≤ (σ.arrs src).length ∧ N ≤ (σ.arrs dst).length ∧
    (∀ z, z < N → (σ.arrs src).getD z 0 = v z) ∧
    (∀ z, z < σ.vars "pl.i" → (σ.arrs dst).getD z 0 = v z)
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "pl.i" < N)
      (.seq (.store dst (.var "pl.i") (.get src (.var "pl.i")))
        (.assign "pl.i" (.add (.var "pl.i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "pl.i" = σ.vars "pl.i" + 1) 8 := by
    rintro σ ⟨⟨hn, hi, hsL, hdL, hsv, hdv⟩, hiN⟩
    have hsi := hsv _ hiN
    have hsiB := hvB _ hiN
    run_vcg
    dsimp [I]
    simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr]
    simp only [show ("pl.n" : String) ≠ "pl.i" by decide, if_false, if_true,
      hne, List.length_set]
    refine ⟨⟨hn, by omega, hsL, hdL, hsv, ?_⟩, by trivial⟩
    intro z hz
    rw [getD_set _ _ _ (by omega)]
    by_cases he : z = σ.vars "pl.i"
    · subst z; rw [if_pos rfl]; exact hsi
    · rw [if_neg he]; exact hdv z (by omega)
  refine (Spec.forRangeZero "pl.i" "pl.n" I N 8 hNB
    (fun _ h => h.2.1) (fun _ h => h.1) hbody).conseq ?_ ?_ (by omega)
  · rintro σ ⟨hn, hsL, hdL, hsv⟩
    simpa [I, hn] using And.intro hsL (And.intro hdL hsv)
  · rintro σ σ' _ ⟨hI, hi⟩ z hz
    exact hI.2.2.2.2.2 z (by omega)

/-- Regroup pass 3 computes the inverse bucket offsets. -/
theorem peelP3B_spec {B N M : ℕ} {f : ℕ → ℕ}
    (hNB : N + 1 < B) (hMB : M + 1 < B) (hf : ∀ p, p < M → f p < N) :
    Spec B (fun σ => σ.vars "pl.n" = N ∧ N ≤ (σ.arrs plDz).length ∧
        N + 1 ≤ (σ.arrs plIo).length ∧
        (∀ z, z < N → (σ.arrs plDz).getD z 0 = peelOcc f z M))
      peelP3B
      (fun _ σ' => ∀ z, z ≤ N → (σ'.arrs plIo).getD z 0 = peelIOff f M z)
      (17 * N + 9) := by
  let I : Env → Prop := fun σ => σ.vars "pl.n" = N ∧ σ.vars "pl.i" ≤ N ∧
    N ≤ (σ.arrs plDz).length ∧ N + 1 ≤ (σ.arrs plIo).length ∧
    (∀ z, z < N → (σ.arrs plDz).getD z 0 = peelOcc f z M) ∧
    (∀ z, z ≤ σ.vars "pl.i" → (σ.arrs plIo).getD z 0 = peelIOff f M z)
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "pl.i" < N)
      (.seq (.store plIo (.add (.var "pl.i") (.lit 1))
          (.add (.get plIo (.var "pl.i")) (.get plDz (.var "pl.i"))))
        (.assign "pl.i" (.add (.var "pl.i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "pl.i" = σ.vars "pl.i" + 1) 13 := by
    rintro σ ⟨⟨hn, hi, hzL, hoL, hzv, hov⟩, hiN⟩
    have hzi := hzv _ hiN
    have hoi := hov _ le_rfl
    have hsum : (σ.arrs plIo).getD (σ.vars "pl.i") 0 +
        (σ.arrs plDz).getD (σ.vars "pl.i") 0 ≤ M := by
      rw [hoi, hzi, ← peelIOff_succ]
      exact peelIOff_le hf (by omega)
    run_vcg
    dsimp [I]
    simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr]
    simp only [show ("pl.n" : String) ≠ "pl.i" by decide, if_false, if_true,
      show plDz ≠ plIo by decide, List.length_set]
    refine ⟨⟨hn, by omega, hzL, hoL, hzv, ?_⟩, by trivial⟩
    intro z hz
    rw [getD_set _ _ _ (by omega)]
    by_cases he : z = σ.vars "pl.i" + 1
    · rw [if_pos he, he, peelIOff_succ, hoi, hzi]
    · rw [if_neg he]; exact hov z (by omega)
  have hloop := Spec.forRangeZero "pl.i" "pl.n" I N 13 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) hbody
  rintro σ ⟨hn, hzL, hoL, hzv⟩
  have h0 : Run B (.store plIo (.lit 0) (.lit 0)) σ (σ.setArr plIo 0 0) 3 :=
    Run.store (evalB_lit (by omega)) (evalB_lit (by omega)) (by omega)
  obtain ⟨σ', hr, hI, hi⟩ := hloop.run (σ := σ.setArr plIo 0 0) (by
    dsimp [I]
    simp only [show ("pl.n" : String) ≠ "pl.i" by decide, if_false, if_true,
      show plDz ≠ plIo by decide, List.length_set, Nat.zero_le]
    refine ⟨hn, by trivial, hzL, hoL, hzv, ?_⟩
    intro z hz
    have he : z = 0 := by omega
    subst z
    rw [getD_set _ _ _ (by omega), if_pos rfl, peelIOff_zero])
  refine ⟨σ', (h0.seq hr).mono (by omega), ?_⟩
  intro z hz
  exact hI.2.2.2.2.2 z (by omega)

/-- The destination of one stream pair in the member-major regroup. -/
def peelDest (f : ℕ → ℕ) (M p : ℕ) : ℕ := peelIOff f M (f p) + peelOcc f (f p) p

theorem peelDest_mem {N M : ℕ} {f : ℕ → ℕ}
    (hf : ∀ p, p < M → f p < N) {p : ℕ} (hp : p < M) :
    peelIOff f M (f p) ≤ peelDest f M p ∧
      peelDest f M p < peelIOff f M (f p + 1) := by
  have hs := peelOcc_strict f hp
  rw [peelIOff_succ]
  dsimp [peelDest]
  omega

theorem peelDest_lt {N M : ℕ} {f : ℕ → ℕ}
    (hf : ∀ p, p < M → f p < N) {p : ℕ} (hp : p < M) : peelDest f M p < M :=
  lt_of_lt_of_le (peelDest_mem hf hp).2 (peelIOff_le hf (by have := hf p hp; omega))

theorem peel_bucket_unique {f : ℕ → ℕ} {M z w q : ℕ}
    (hz : peelIOff f M z ≤ q ∧ q < peelIOff f M (z + 1))
    (hw : peelIOff f M w ≤ q ∧ q < peelIOff f M (w + 1)) : z = w := by
  rcases lt_trichotomy z w with h | h | h
  · have hh := peelIOff_mono f M (Nat.succ_le_of_lt h)
    simp only [Nat.succ_eq_add_one] at hh
    omega
  · exact h
  · have hh := peelIOff_mono f M (Nat.succ_le_of_lt h)
    simp only [Nat.succ_eq_add_one] at hh
    omega

theorem peelDest_inj {N M : ℕ} {f : ℕ → ℕ}
    (hf : ∀ p, p < M → f p < N) {p q : ℕ} (hp : p < M) (hq : q < M)
    (h : peelDest f M p = peelDest f M q) : p = q := by
  have he : f p = f q := peel_bucket_unique (peelDest_mem hf hp) (h ▸ peelDest_mem hf hq)
  have hc : peelOcc f (f p) p = peelOcc f (f q) q := by
    simp only [peelDest, he] at h
    rw [he]
    exact Nat.add_left_cancel h
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · have := peelOcc_strict f hpq; rw [← he] at hc; omega
  · exact hpq
  · have := peelOcc_strict f hpq; rw [he] at hc; omega

theorem peelDest_surj {N M : ℕ} {f : ℕ → ℕ}
    (hf : ∀ p, p < M → f p < N) {q : ℕ} (hq : q < M) :
    ∃ p, p < M ∧ peelDest f M p = q := by
  let e : Fin M → Fin M := fun p => ⟨peelDest f M p, peelDest_lt hf p.isLt⟩
  have hi : Function.Injective e := by
    intro p p' he
    exact Fin.ext (peelDest_inj hf p.isLt p'.isLt (congrArg Fin.val he))
  obtain ⟨p, hp⟩ := (Finite.surjective_of_injective hi) ⟨q, hq⟩
  exact ⟨p, p.isLt, congrArg Fin.val hp⟩

/-- The inverse scatter preserves the source relation, with one copy per pair. -/
theorem peel_transpose_segments {N M : ℕ} {f own iv : ℕ → ℕ}
    {X : Fin N → Set (Fin N)} (hf : ∀ p, p < M → f p < N)
    (ho : ∀ p, p < M → own p < N)
    (hs : ∀ p, (hp : p < M) → (⟨f p, hf p hp⟩ : Fin N) ∈ X ⟨own p, ho p hp⟩)
    (hc : ∀ u z : Fin N, z ∈ X u → ∃ p, p < M ∧ own p = u ∧ f p = z)
    (hi : ∀ p q, p < M → q < M → own p = own q → f p = f q → p = q)
    (hv : ∀ p, p < M → iv (peelDest f M p) = own p) (z : Fin N) :
    SegAt iv (peelIOff f M z) (peelIOff f M (z + 1)) {u | z ∈ X u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq0 hq1
    have hqM : q < M := lt_of_lt_of_le hq1 (peelIOff_le hf (by omega))
    obtain ⟨p, hp, hpq⟩ := peelDest_surj hf hqM
    have hfp : f p = z := peel_bucket_unique (peelDest_mem hf hp) (by simpa [hpq] using And.intro hq0 hq1)
    have hiv : iv q = own p := by rw [← hpq]; exact hv p hp
    refine ⟨by rw [hiv]; exact ho p hp, ?_⟩
    have hzFin : (⟨f p, hf p hp⟩ : Fin N) = z := Fin.ext hfp
    have hoFin : (⟨iv q, by rw [hiv]; exact ho p hp⟩ : Fin N) = ⟨own p, ho p hp⟩ := Fin.ext hiv
    change z ∈ X _
    rw [hoFin, ← hzFin]
    exact hs p hp
  · intro u hu
    obtain ⟨p, hp, hop, hfp⟩ := hc u z hu
    have hmem := peelDest_mem hf hp
    rw [hfp] at hmem
    exact ⟨peelDest f M p, hmem.1, hmem.2, (hv p hp).trans hop⟩
  · intro q q' hq0 hq1 hq0' hq1' heq
    have hqM : q < M := lt_of_lt_of_le hq1 (peelIOff_le hf (by omega))
    have hqM' : q' < M := lt_of_lt_of_le hq1' (peelIOff_le hf (by omega))
    obtain ⟨p, hp, hpq⟩ := peelDest_surj hf hqM
    obtain ⟨p', hp', hpq'⟩ := peelDest_surj hf hqM'
    have hfp : f p = z := peel_bucket_unique (peelDest_mem hf hp) (by simpa [hpq] using And.intro hq0 hq1)
    have hfp' : f p' = z := peel_bucket_unique (peelDest_mem hf hp') (by simpa [hpq'] using And.intro hq0' hq1')
    have hop : own p = own p' := by rw [← hv p hp, ← hv p' hp', hpq, hpq']; exact heq
    have hpp := hi p p' hp hp' hop (hfp.trans hfp'.symm)
    rw [← hpq, ← hpq', hpp]

/-- The immutable input of the inverse scatter, plus its allocations. -/
def PeelScBase (od : String) (N M : ℕ) (e row f : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "pl.n" = N ∧ N ≤ (σ.arrs od).length ∧
  N + 1 ≤ (σ.arrs plRe).length ∧ M ≤ (σ.arrs plRw).length ∧
  N ≤ (σ.arrs plCu).length ∧ M ≤ (σ.arrs plIv).length ∧
  (∀ i, i < N → (σ.arrs od).getD i 0 = row i) ∧
  (∀ i, i ≤ N → (σ.arrs plRe).getD i 0 = e i) ∧
  (∀ p, p < M → (σ.arrs plRw).getD p 0 = f p)

theorem peelScBase_setVar {od x : String} {N M v : ℕ} {e row f : ℕ → ℕ} {σ : Env}
    (h : PeelScBase od N M e row f σ) (hx : ("pl.n" : String) ≠ x) :
    PeelScBase od N M e row f (σ.setVar x v) := by
  simpa [PeelScBase, hx] using h

theorem peelScBase_setArr {od a : String} {N M p v : ℕ} {e row f : ℕ → ℕ} {σ : Env}
    (h : PeelScBase od N M e row f σ) (h1 : od ≠ a) (h2 : plRe ≠ a) (h3 : plRw ≠ a) :
    PeelScBase od N M e row f (σ.setArr a p v) := by
  simp only [PeelScBase, length_arrs_setArr] at h ⊢
  simpa only [vars_setArr, arrs_setArr, if_neg h1, if_neg h2, if_neg h3] using h

/-- The already scattered prefix and the next empty slot of each bucket. -/
def PeelScPart (N M : ℕ) (f own : ℕ → ℕ) (k : ℕ) (σ : Env) : Prop :=
  (∀ z, z < N → (σ.arrs plCu).getD z 0 = peelIOff f M z + peelOcc f z k) ∧
  (∀ p, p < k → (σ.arrs plIv).getD (peelDest f M p) 0 = own p)

/-- Scatter one source segment, retaining the global prefix account. -/
theorem peelP4_inner_spec {B N M i : ℕ} {od : String} {e row f own : ℕ → ℕ}
    (hNB : N + 1 < B) (hMB : M + 1 < B)
    (hdi : od ≠ plIv) (hdc : od ≠ plCu) (hi : i < N)
    (he : e i ≤ e (i + 1)) (heM : e (i + 1) ≤ M)
    (hrow : row i < N) (hf : ∀ p, p < M → f p < N)
    (hown : ∀ p, e i ≤ p → p < e (i + 1) → own p = row i) :
    Spec B (fun σ => PeelScBase od N M e row f σ ∧
        σ.vars "pl.u" = row i ∧ σ.vars "pl.g" = e (i + 1) ∧
        σ.vars "pl.k" = e i ∧ PeelScPart N M f own (e i) σ)
      (.while (.lt (.var "pl.k") (.var "pl.g"))
        (.seq (.assign "pl.z" (.get plRw (.var "pl.k")))
          (.seq (.store plIv (.get plCu (.var "pl.z")) (.var "pl.u"))
            (.seq (.store plCu (.var "pl.z")
                (.add (.get plCu (.var "pl.z")) (.lit 1)))
              (.assign "pl.k" (.add (.var "pl.k") (.lit 1)))))))
      (fun _ σ' => PeelScBase od N M e row f σ' ∧ PeelScPart N M f own (e (i + 1)) σ')
      (21 * (e (i + 1) - e i) + 4) := by
  let I : Env → Prop := fun σ => PeelScBase od N M e row f σ ∧
    σ.vars "pl.u" = row i ∧ σ.vars "pl.g" = e (i + 1) ∧
    e i ≤ σ.vars "pl.k" ∧ σ.vars "pl.k" ≤ e (i + 1) ∧
    PeelScPart N M f own (σ.vars "pl.k") σ
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "pl.k" < e (i + 1))
      (.seq (.assign "pl.z" (.get plRw (.var "pl.k")))
        (.seq (.store plIv (.get plCu (.var "pl.z")) (.var "pl.u"))
          (.seq (.store plCu (.var "pl.z")
              (.add (.get plCu (.var "pl.z")) (.lit 1)))
            (.assign "pl.k" (.add (.var "pl.k") (.lit 1))))))
      (fun σ σ' => I σ' ∧ σ'.vars "pl.k" = σ.vars "pl.k" + 1) 17 := by
    rintro σ ⟨⟨hbase, hu, hg, hek, hke, hpart⟩, hklt⟩
    rcases hbase with ⟨hn, hodL, hreL, hrwL, hcuL, hivL, hodv, hrev, hrwv⟩
    rcases hpart with ⟨hcuv, hivv⟩
    have hkM : σ.vars "pl.k" < M := by omega
    have hfk := hf _ hkM
    have hrk := hrwv _ hkM
    have hcur : (σ.arrs plCu).getD ((σ.arrs plRw).getD (σ.vars "pl.k") 0) 0
        = peelDest f M (σ.vars "pl.k") := by
      rw [hrk, hcuv _ hfk]; rfl
    have hdest := peelDest_lt hf hkM
    have hownk := hown _ hek hklt
    run_vcg
    dsimp only [I]
    simp only [vars_setVar, vars_setArr, arrs_setVar]
    simp only [show ("pl.u" : String) ≠ "pl.k" by decide,
      show ("pl.u" : String) ≠ "pl.z" by decide,
      show ("pl.g" : String) ≠ "pl.k" by decide,
      show ("pl.g" : String) ≠ "pl.z" by decide,
      show ("pl.k" : String) ≠ "pl.z" by decide, if_false, if_true]
    refine ⟨⟨?_, hu, hg, by omega, by omega, ?_, ?_⟩, by trivial⟩
    · apply peelScBase_setVar _ (by decide)
      apply peelScBase_setArr _ hdc (by decide) (by decide)
      apply peelScBase_setArr _ hdi (by decide) (by decide)
      exact peelScBase_setVar ⟨hn, hodL, hreL, hrwL, hcuL, hivL, hodv, hrev, hrwv⟩ (by decide)
    · intro z hz
      simp only [arrs_setArr, vars_setArr, arrs_setVar, vars_setVar]
      simp only [show plCu ≠ plIv by decide, if_false, if_true,
        show ("pl.k" : String) ≠ "pl.z" by decide]
      rw [getD_set _ _ _ (by omega), peelOcc_succ]
      rw [hrk, hcuv _ hfk]
      by_cases hez : z = f (σ.vars "pl.k")
      · subst z; simp only [if_pos rfl, if_true]; omega
      · rw [if_neg hez, if_neg (Ne.symm hez), hcuv z hz]
        omega
    · intro p hp
      simp only [arrs_setArr, vars_setArr, arrs_setVar, vars_setVar]
      simp only [show plIv ≠ plCu by decide, if_false, if_true,
        show ("pl.k" : String) ≠ "pl.z" by decide]
      rw [getD_set _ _ _ (by omega), hcur]
      by_cases hpk : p = σ.vars "pl.k"
      · subst p; rw [if_pos rfl]; exact hu.trans hownk.symm
      · have hplt : p < σ.vars "pl.k" := by omega
        have hpM : p < M := by omega
        rw [if_neg (fun h => hpk (peelDest_inj hf hpM hkM h))]
        exact hivv p hplt
    all_goals simp [show plCu ≠ plIv by decide] <;>
      simp only [← List.getD_eq_getElem?_getD] <;> omega
  refine (Spec.forRange "pl.k" "pl.g" I (e (i + 1)) 17
    (21 * (e (i + 1) - e i) + 4)
    (fun _ h => by have := h.2.2.2.2.1; omega)
    (fun _ h => by rw [h.2.2.1]; omega)
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.2.1) hbody ?_ ?_).post ?_
  · rintro σ ⟨hb, hu, hg, hk, hp⟩
    exact ⟨hb, hu, hg, by omega, by omega, by simpa [hk] using hp⟩
  · rintro σ ⟨_, _, _, hk, _⟩
    rw [hk]
  · rintro σ σ' _ ⟨hI, hk⟩
    exact ⟨hI.1, by simpa [hk] using hI.2.2.2.2.2⟩

private theorem peel_sum_widths {N : ℕ} {e : ℕ → ℕ} (h0 : e 0 = 0)
    (he : ∀ i, i < N → e i ≤ e (i + 1)) :
    ∑ i ∈ Finset.range N, (e (i + 1) - e i) = e N := by
  induction N with
  | zero => simpa using h0.symm
  | succ N ih =>
    rw [Finset.sum_range_succ, ih (fun i hi => he i (by omega))]
    exact Nat.add_sub_of_le (he N (by omega))

/-- Regroup pass 4 scatters every source pair exactly once. -/
theorem peelP4B_spec {B N M : ℕ} {od : String} {e row f own : ℕ → ℕ}
    (hNB : N + 1 < B) (hMB : M + 1 < B)
    (hdi : od ≠ plIv) (hdc : od ≠ plCu)
    (he0 : e 0 = 0) (heN : e N = M)
    (hemono : ∀ i j, i ≤ j → j ≤ N → e i ≤ e j)
    (hrow : ∀ i, i < N → row i < N) (hf : ∀ p, p < M → f p < N)
    (hown : ∀ i, i < N → ∀ p, e i ≤ p → p < e (i + 1) → own p = row i) :
    Spec B (fun σ => PeelScBase od N M e row f σ ∧ PeelScPart N M f own 0 σ)
      (peelP4B od)
      (fun _ σ' => PeelScPart N M f own M σ') (21 * M + 23 * N + 6) := by
  let I : Env → Prop := fun σ => PeelScBase od N M e row f σ ∧
    σ.vars "pl.i" ≤ N ∧ PeelScPart N M f own (e (σ.vars "pl.i")) σ
  let K : ℕ → ℕ := fun i => 21 * (e (i + 1) - e i) + 19
  have hstep : ∀ i, i < N → Spec B (fun σ => I σ ∧ σ.vars "pl.i" = i)
      (.seq (.assign "pl.u" (.get od (.var "pl.i")))
        (.seq (.assign "pl.k" (.get plRe (.var "pl.i")))
          (.seq (.assign "pl.g" (.get plRe (.add (.var "pl.i") (.lit 1))))
            (.seq
              (.while (.lt (.var "pl.k") (.var "pl.g"))
                (.seq (.assign "pl.z" (.get plRw (.var "pl.k")))
                  (.seq (.store plIv (.get plCu (.var "pl.z")) (.var "pl.u"))
                    (.seq (.store plCu (.var "pl.z")
                        (.add (.get plCu (.var "pl.z")) (.lit 1)))
                      (.assign "pl.k" (.add (.var "pl.k") (.lit 1)))))))
              (.assign "pl.i" (.add (.var "pl.i") (.lit 1)))))))
      (fun _ σ' => I σ' ∧ σ'.vars "pl.i" = i + 1) (K i) := by
    intro i hi
    rintro σ ⟨⟨hbase, _, hp⟩, hvi⟩
    have hemi : e i ≤ e (i + 1) := hemono _ _ (by omega) (by omega)
    have heiM : e (i + 1) ≤ M := by rw [← heN]; exact hemono _ _ (by omega) le_rfl
    obtain ⟨hn, hodL, hreL, hrwL, hcuL, hivL, hodv, hrev, hrwv⟩ := id hbase
    let σ1 := σ.setVar "pl.u" (row i)
    let σ2 := σ1.setVar "pl.k" (e i)
    let σ3 := σ2.setVar "pl.g" (e (i + 1))
    have huRun : Run B (.assign "pl.u" (.get od (.var "pl.i"))) σ σ1 3 := by
      have hev := RunStep.eval_get B σ od (.var "pl.i") i
        (by simpa [hvi] using (evalB_var (B := B) (x := "pl.i") (σ := σ) (by omega)))
        (by omega) (by rw [hodv i hi]; exact lt_trans (hrow i hi) (by omega))
      simpa only [σ1, hodv i hi, Expr.size] using Run.assign (x := "pl.u") hev
    have hkRun : Run B (.assign "pl.k" (.get plRe (.var "pl.i"))) σ1 σ2 3 := by
      have hev := RunStep.eval_get B σ1 plRe (.var "pl.i") i
        (by simpa [σ1, hvi] using (evalB_var (B := B) (x := "pl.i") (σ := σ1)
          (by simp [σ1, hvi]; omega)))
        (by simp [σ1]; omega) (by change (σ.arrs plRe).getD i 0 < B; rw [hrev i (by omega)]; omega)
      simpa only [σ1, σ2, arrs_setVar, hrev i (by omega), Expr.size] using Run.assign (x := "pl.k") hev
    have hgRun : Run B (.assign "pl.g" (.get plRe (.add (.var "pl.i") (.lit 1)))) σ2 σ3 5 := by
      have hevi : (Expr.add (.var "pl.i") (.lit 1)).evalB B σ2 = some (i + 1) := by
        have h := evalB_bin (B := B) (σ := σ2) (op := .add)
          (e := Expr.var "pl.i") (f := Expr.lit 1)
          (evalB_var (by simp [σ2, σ1, hvi]; omega)) (evalB_lit (by omega))
          (by simp [σ2, σ1, hvi]; omega)
        simpa [σ2, σ1, hvi] using h
      have hev := RunStep.eval_get B σ2 plRe (.add (.var "pl.i") (.lit 1)) (i + 1)
        hevi (by simp [σ2, σ1]; omega)
        (by change (σ.arrs plRe).getD (i + 1) 0 < B; rw [hrev (i + 1) (by omega)]; omega)
      simpa only [σ3, σ2, σ1, arrs_setVar, hrev (i + 1) (by omega), Expr.size] using Run.assign (x := "pl.g") hev
    obtain ⟨σ4, hir, hb4, hp4⟩ := (peelP4_inner_spec hNB hMB hdi hdc hi hemi heiM
      (hrow i hi) hf (hown i hi)).run (σ := σ3) (by
        refine ⟨?_, by simp [σ3, σ2, σ1], by simp [σ3], by simp [σ3, σ2], ?_⟩
        · exact peelScBase_setVar (peelScBase_setVar (peelScBase_setVar hbase (by decide)) (by decide)) (by decide)
        · simpa [PeelScPart, σ3, σ2, σ1, hvi] using hp)
    have hi4 : σ4.vars "pl.i" = i := by
      rw [hir.frame_var "pl.i" (by simp [Com.wvars])]
      simp [σ3, σ2, σ1, hvi]
    have hinc : Run B (.assign "pl.i" (.add (.var "pl.i") (.lit 1))) σ4
        (σ4.setVar "pl.i" (i + 1)) 4 := by
      have h := evalB_bin (B := B) (σ := σ4) (op := .add)
        (e := Expr.var "pl.i") (f := Expr.lit 1)
        (evalB_var (by omega)) (evalB_lit (by omega))
        (by simp only [Bop.apply_add]; omega)
      have hev : (Expr.add (.var "pl.i") (.lit 1)).evalB B σ4 = some (i + 1) := by simpa [hi4] using h
      exact Run.assign hev
    refine ⟨_, (huRun.seq (hkRun.seq (hgRun.seq (hir.seq hinc)))).mono (by dsimp [K]; omega), ?_, by simp⟩
    refine ⟨peelScBase_setVar hb4 (by decide), by simp; omega, ?_⟩
    simpa [PeelScPart] using hp4
  have hloop := peel_forRangeSum "pl.i" "pl.n" I K (by omega)
    (fun _ h => ⟨h.1.1, h.2.1⟩) hstep
  rintro σ ⟨hb, hp⟩
  have hinit : Run B (.assign "pl.i" (.lit 0)) σ (σ.setVar "pl.i" 0) 2 := Run.assign (evalB_lit (by omega))
  obtain ⟨σ', hr, hI, hi⟩ := hloop.run (σ := σ.setVar "pl.i" 0) (by
    refine ⟨⟨peelScBase_setVar hb (by decide), by simp, ?_⟩, by simp⟩
    simpa [PeelScPart, he0] using hp)
  have hsum : (∑ i ∈ Finset.range N, (K i + 4)) = 21 * M + 23 * N := by
    have hwidth := peel_sum_widths (N := N) he0 (fun i hi => hemono i (i + 1) (by omega) (by omega))
    rw [heN] at hwidth
    have ht : ∀ i, K i + 4 = 21 * (e (i + 1) - e i) + 23 := by intro i; dsimp [K]
    simp_rw [ht]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hwidth]
    simp [Nat.mul_comm]
  refine ⟨σ', (hinit.seq hr).mono (by rw [hsum]; omega), ?_⟩
  simpa [hi, heN] using hI.2.2

/-- Regroup pass 5 reindexes the source row lengths into carrier order. -/
theorem peelP5B_spec {B N M : ℕ} {co ra : String} {e rk o : ℕ → ℕ}
    (hNB : N + 1 < B) (hMB : M + 1 < B) (hcr : ra ≠ co) (hce : plRe ≠ co)
    (hrk : ∀ i, i < N → rk i < N) (he : ∀ i, i ≤ N → e i ≤ M)
    (ho : ∀ i, i ≤ N → o i ≤ M) (ho0 : o 0 = 0)
    (hostep : ∀ i, i < N → o (i + 1) = o i + (e (rk i + 1) - e (rk i))) :
    Spec B (fun σ => σ.vars "pl.n" = N ∧ N ≤ (σ.arrs ra).length ∧
        N + 1 ≤ (σ.arrs plRe).length ∧ N + 1 ≤ (σ.arrs co).length ∧
        (∀ i, i < N → (σ.arrs ra).getD i 0 = rk i) ∧
        (∀ i, i ≤ N → (σ.arrs plRe).getD i 0 = e i))
      (peelP5B co ra) (fun _ σ' => ∀ i, i ≤ N → (σ'.arrs co).getD i 0 = o i)
      (25 * N + 9) := by
  let I : Env → Prop := fun σ => σ.vars "pl.n" = N ∧ σ.vars "pl.i" ≤ N ∧
    N ≤ (σ.arrs ra).length ∧ N + 1 ≤ (σ.arrs plRe).length ∧
    N + 1 ≤ (σ.arrs co).length ∧
    (∀ i, i < N → (σ.arrs ra).getD i 0 = rk i) ∧
    (∀ i, i ≤ N → (σ.arrs plRe).getD i 0 = e i) ∧
    (∀ i, i ≤ σ.vars "pl.i" → (σ.arrs co).getD i 0 = o i)
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "pl.i" < N)
      (.seq (.assign "pl.k" (.get ra (.var "pl.i")))
        (.seq (.store co (.add (.var "pl.i") (.lit 1))
            (.add (.get co (.var "pl.i"))
              (.sub (.get plRe (.add (.var "pl.k") (.lit 1))) (.get plRe (.var "pl.k")))))
          (.assign "pl.i" (.add (.var "pl.i") (.lit 1)))))
      (fun σ σ' => I σ' ∧ σ'.vars "pl.i" = σ.vars "pl.i" + 1) 21 := by
    rintro σ ⟨⟨hn, hi, hrL, heL, hoL, hrv, hev, hov⟩, hiN⟩
    have hrki := hrv _ hiN
    have hrkiN := hrk _ hiN
    have heki := hev (rk (σ.vars "pl.i")) (by omega)
    have heki1 := hev (rk (σ.vars "pl.i") + 1) (by omega)
    have hekiB := he (rk (σ.vars "pl.i")) (by omega)
    have heki1B := he (rk (σ.vars "pl.i") + 1) (by omega)
    have hoi := hov _ le_rfl
    have hoiB := ho (σ.vars "pl.i") (by omega)
    have hoi1B := ho (σ.vars "pl.i" + 1) (by omega)
    have hstep := hostep _ hiN
    run_vcg
    dsimp only [I]
    simp only [vars_setVar, vars_setArr, arrs_setVar, arrs_setArr]
    simp only [show ("pl.n" : String) ≠ "pl.i" by decide,
      show ("pl.n" : String) ≠ "pl.k" by decide,
      show ("pl.i" : String) ≠ "pl.k" by decide, if_false, if_true,
      hcr, hce, List.length_set]
    refine ⟨⟨hn, by omega, hrL, heL, hoL, hrv, hev, ?_⟩, by trivial⟩
    intro z hz
    rw [getD_set _ _ _ (by omega)]
    by_cases hez : z = σ.vars "pl.i" + 1
    · rw [if_pos hez, hez, hrki, heki, heki1, hoi]
      exact hstep.symm
    · rw [if_neg hez]; exact hov z (by omega)
    all_goals simp <;> simp only [← List.getD_eq_getElem?_getD] <;>
      simp only [hrki, heki, heki1, hoi] <;> omega
  have hloop := Spec.forRangeZero "pl.i" "pl.n" I N 21 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) hbody
  rintro σ ⟨hn, hrL, heL, hoL, hrv, hev⟩
  have h0 : Run B (.store co (.lit 0) (.lit 0)) σ (σ.setArr co 0 0) 3 :=
    Run.store (evalB_lit (by omega)) (evalB_lit (by omega)) (by omega)
  obtain ⟨σ', hr, hI, hi⟩ := hloop.run (σ := σ.setArr co 0 0) (by
    dsimp [I]
    simp only [hcr, hce, if_false, if_true, List.length_set, Nat.zero_le]
    refine ⟨hn, by trivial, hrL, heL, hoL, hrv, hev, ?_⟩
    intro z hz
    have hez : z = 0 := by omega
    subst z
    rw [getD_set _ _ _ (by omega), if_pos rfl, ho0])
  refine ⟨σ', (h0.seq hr).mono (by omega), ?_⟩
  intro z hz
  exact hI.2.2.2.2.2.2.2 z (by omega)

/-- The rank interval containing a position of the emitted member stream. -/
noncomputable def peelOwner (e row : ℕ → ℕ) (N p : ℕ) : ℕ :=
  if h : p < e N then row (Nat.find (show ∃ j, p < e j from ⟨N, h⟩) - 1) else 0

private theorem peel_interval_exists {e : ℕ → ℕ} {N p : ℕ} (h0 : e 0 = 0)
    (hp : p < e N) : ∃ i, i < N ∧ e i ≤ p ∧ p < e (i + 1) := by
  classical
  have hex : ∃ j, p < e j := ⟨N, hp⟩
  have hj := Nat.find_spec hex
  have hjN := Nat.find_min' hex hp
  have hj0 : 0 < Nat.find hex := by
    by_contra hn
    have heq : Nat.find hex = 0 := by omega
    rw [heq, h0] at hj
    omega
  have hjp := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  refine ⟨Nat.find hex - 1, by omega, by omega, ?_⟩
  have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  rw [heq]
  exact hj

private theorem peelOwner_at {e row : ℕ → ℕ} {N i p : ℕ}
    (hi : i < N) (hmono : ∀ i j, i ≤ j → j ≤ N → e i ≤ e j)
    (hlo : e i ≤ p) (hhi : p < e (i + 1)) : peelOwner e row N p = row i := by
  classical
  have hp : p < e N := lt_of_lt_of_le hhi (hmono _ _ (by omega) le_rfl)
  rw [peelOwner, dif_pos hp]
  have hx : ∃ j, p < e j := ⟨N, hp⟩
  have hj := Nat.find_spec hx
  have hjle : Nat.find hx ≤ i + 1 := Nat.find_min' hx hhi
  have hjgt : i < Nat.find hx := by
    by_contra hh
    have hm := hmono (Nat.find hx) i (by omega) (by omega)
    omega
  have heq : Nat.find hx - 1 = i := by omega
  simpa only [heq]

/-- Natural-indexed access to an order permutation. -/
noncomputable def peelRow {N : ℕ} (ρ : Equiv.Perm (Fin N)) (i : ℕ) : ℕ :=
  if h : i < N then (ρ ⟨i, h⟩ : ℕ) else 0

theorem peelRow_eq {N : ℕ} (ρ : Equiv.Perm (Fin N)) {i : ℕ} (hi : i < N) :
    peelRow ρ i = (ρ ⟨i, hi⟩ : ℕ) := dif_pos hi

/-- The mathematical source relation supplied by completed sweep segments. -/
theorem peel_source_of_segments {N M : ℕ} {ρ : Equiv.Perm (Fin N)}
    {e f : ℕ → ℕ} {X : Fin N → Set (Fin N)}
    (he0 : e 0 = 0) (heN : e N = M)
    (hemono : ∀ i j, i ≤ j → j ≤ N → e i ≤ e j)
    (hseg : ∀ i, (hi : i < N) → SegAt f (e i) (e (i + 1)) (X (ρ ⟨i, hi⟩))) :
    (∀ p, p < M → f p < N) ∧
    (∀ p, p < M → peelOwner e (peelRow ρ) N p < N) ∧
    (∀ p, (hp : p < M) → ∃ hv : f p < N, ∃ hu : peelOwner e (peelRow ρ) N p < N,
      (⟨f p, hv⟩ : Fin N) ∈ X ⟨peelOwner e (peelRow ρ) N p, hu⟩) ∧
    (∀ u z : Fin N, z ∈ X u → ∃ p, p < M ∧ peelOwner e (peelRow ρ) N p = u ∧ f p = z) ∧
    (∀ p q, p < M → q < M → peelOwner e (peelRow ρ) N p = peelOwner e (peelRow ρ) N q →
      f p = f q → p = q) := by
  have hloc : ∀ p, p < M → ∃ i, i < N ∧ e i ≤ p ∧ p < e (i + 1) := by
    intro p hp
    exact peel_interval_exists he0 (by rwa [heN])
  have hown : ∀ i, (hi : i < N) → ∀ p, e i ≤ p → p < e (i + 1) →
      peelOwner e (peelRow ρ) N p = (ρ ⟨i, hi⟩ : ℕ) := by
    intro i hi p hp1 hp2
    rw [peelOwner_at hi hemono hp1 hp2, peelRow_eq ρ hi]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hi, hp1, hp2⟩ := hloc p hp
    exact ((hseg i hi).1 p hp1 hp2).1
  · intro p hp
    obtain ⟨i, hi, hp1, hp2⟩ := hloc p hp
    rw [hown i hi p hp1 hp2]
    exact (ρ ⟨i, hi⟩).isLt
  · intro p hp
    obtain ⟨i, hi, hp1, hp2⟩ := hloc p hp
    obtain ⟨hv, hm⟩ := (hseg i hi).1 p hp1 hp2
    have ho := hown i hi p hp1 hp2
    refine ⟨hv, by rw [ho]; exact (ρ ⟨i, hi⟩).isLt, ?_⟩
    have huFin : (⟨peelOwner e (peelRow ρ) N p, by rw [ho]; exact (ρ ⟨i, hi⟩).isLt⟩ : Fin N) = ρ ⟨i, hi⟩ := Fin.ext ho
    rw [huFin]
    exact hm
  · intro u z hz
    let i : Fin N := ρ.symm u
    have hu : ρ i = u := ρ.apply_symm_apply u
    obtain ⟨p, hp1, hp2, hp3⟩ := (hseg i i.isLt).2.1 z (by simpa [hu] using hz)
    exact ⟨p, lt_of_lt_of_le hp2 ((hemono _ _ (by omega) le_rfl).trans_eq heN),
      by rw [hown i i.isLt p hp1 hp2]; exact congrArg Fin.val hu, hp3⟩
  · intro p q hp hq ho hf
    obtain ⟨i, hi, hp1, hp2⟩ := hloc p hp
    obtain ⟨j, hj, hq1, hq2⟩ := hloc q hq
    rw [hown i hi p hp1 hp2, hown j hj q hq1 hq2] at ho
    have hij : i = j := congrArg Fin.val (ρ.injective (Fin.ext ho))
    subst j
    exact (hseg i hi).2.2 p q hp1 hp2 hq1 hq2 hf

/-- The canonical output offsets, in ascending carrier order. -/
noncomputable def peelCOff {N : ℕ} (X : Fin N → Set (Fin N)) (z : ℕ) : ℕ :=
  ∑ i ∈ Finset.range z, if h : i < N then (X ⟨i, h⟩).ncard else 0

@[simp] theorem peelCOff_zero {N : ℕ} (X : Fin N → Set (Fin N)) : peelCOff X 0 = 0 := rfl

theorem peelCOff_succ {N : ℕ} (X : Fin N → Set (Fin N)) (u : Fin N) :
    peelCOff X (u + 1) = peelCOff X u + (X u).ncard := by
  rw [peelCOff, Finset.sum_range_succ, dif_pos u.isLt]
  rfl

theorem peelCOff_mono {N : ℕ} (X : Fin N → Set (Fin N)) {i j : ℕ} (h : i ≤ j) :
    peelCOff X i ≤ peelCOff X j := Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem peelCOff_last {N : ℕ} {X : Fin N → Set (Fin N)} :
    peelCOff X N = ∑ u : Fin N, (X u).ncard := by
  rw [peelCOff, ← Fin.sum_univ_eq_sum_range]
  simp

/-- Source segment mass equals the canonical output mass, independently of the permutation. -/
theorem peelCOff_eq_mass {N : ℕ} {ρ : Equiv.Perm (Fin N)} {X : Fin N → Set (Fin N)}
    {e : ℕ → ℕ} (he0 : e 0 = 0)
    (hstep : ∀ i, (hi : i < N) → e (i + 1) = e i + (X (ρ ⟨i, hi⟩)).ncard) :
    peelCOff X N = e N := by
  rw [peelCOff_last]
  have hemono : ∀ i, i < N → e i ≤ e (i + 1) := by intro i hi; rw [hstep i hi]; omega
  have hwidth := peel_sum_widths (N := N) he0 hemono
  have hsum : (∑ i ∈ Finset.range N, (e (i + 1) - e i)) =
      ∑ i : Fin N, (X (ρ i)).ncard := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [hstep i i.isLt]
    simp
  rw [hsum] at hwidth
  rw [← Equiv.sum_comp ρ (fun u => (X u).ncard)]
  exact hwidth

end Lax3Proofs.Prog
