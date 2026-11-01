import D5.S3.Geometry.Polygons.PolygonConditionalCounts
import Lean
open Finset
open D5.S3.Geometry.Polygons
open PolygonEarSlide PolygonEarSlide.Carrier PolygonEarSlide.Actual PolygonEarContraction PolygonConditionalCounts
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

example {n : ℕ} [NeZero n] (hn : 14 ≤ n) (P Q : Finset (ZMod n))
    (hd : Disjoint P Q) (hk : Compatible (P ∪ Q))
    (hp : P.card = 2) (hq : Q.card = 2) :
    (Nat.card (ConditionFiber P Q ∅ ∅) : ℤ) =
      ∑ j ∈ range (2+1), (-1 : ℤ)^j * (Nat.choose 2 j : ℤ) * catalan (n-2-j-2) := by
  simpa only [hp, hq, Npq] using conditional_card hn P Q hd hk

example {n : ℕ} [NeZero n] (hn : 14 ≤ n) (P Q : Finset (ZMod n))
    (hd : Disjoint P Q) (hk : Compatible (P ∪ Q))
    (hp : P.card = 3) (hq : Q.card = 3) :
    (Nat.card (ConditionFiber P Q ∅ ∅) : ℤ) =
      ∑ j ∈ range (3+1), (-1 : ℤ)^j * (Nat.choose 3 j : ℤ) * catalan (n-3-j-2) := by
  simpa only [hp, hq, Npq] using conditional_card hn P Q hd hk

example {n : ℕ} [NeZero n] (hn : 14 ≤ n) (P Q : Finset (ZMod n))
    (hd : Disjoint P Q) (hk : Compatible (P ∪ Q))
    (hp : P.card = 2) (hq : Q.card = 4) :
    (Nat.card (ConditionFiber P Q ∅ ∅) : ℤ) =
      ∑ j ∈ range (4+1), (-1 : ℤ)^j * (Nat.choose 4 j : ℤ) * catalan (n-2-j-2) := by
  simpa only [hp, hq, Npq] using conditional_card hn P Q hd hk

example {n : ℕ} [NeZero n] (hn : 14 ≤ n) (P Q : Finset (ZMod n))
    (hd : Disjoint P Q) (hk : Compatible (P ∪ Q))
    (hp : P.card = 4) (hq : Q.card = 2) :
    (Nat.card (ConditionFiber P Q ∅ ∅) : ℤ) =
      ∑ j ∈ range (2+1), (-1 : ℤ)^j * (Nat.choose 2 j : ℤ) * catalan (n-4-j-2) := by
  simpa only [hp, hq, Npq] using conditional_card hn P Q hd hk

-- Both sides use their own parameter order.
example {n : ℕ} [NeZero n] (hn : 14 ≤ n) (P Q : Finset (ZMod n))
    (hd : Disjoint P Q) (hk : Compatible (P ∪ Q)) :
    (Nat.card (ConditionFiber Q P ∅ ∅) : ℤ) = Npq n Q.card P.card := by
  exact conditional_card hn Q P hd.symm (by simpa only [union_comm] using hk)

-- The same count supplies (37.6), without a retained specialization.
example {n : ℕ} [NeZero n] (hn : 14 ≤ n) (P Q I : Finset (ZMod n))
    (hd : Disjoint P Q) (hk : Compatible (P ∪ Q))
    (hi : I ⊆ E_K (P ∪ Q)) (hc : Compatible I) :
    (Nat.card (ConditionFiber (P ∪ I) Q ∅ ∅) : ℤ) =
      Npq n (P.card + I.card) Q.card := by
  have hsep : Disjoint I (P ∪ Q) := by
    apply disjoint_left.mpr
    intro x hx hxk
    exact (mem_filter.mp (hi hx)).2.1 hxk
  have hd' : Disjoint (P ∪ I) Q := disjoint_union_left.mpr
    ⟨hd, hsep.mono_right subset_union_right⟩
  have hk' : Compatible ((P ∪ I) ∪ Q) := by
    intro x hx y hy hxy
    have split (z : ZMod n) (hz : z ∈ (P ∪ I) ∪ Q) : z ∈ I ∨ z ∈ P ∪ Q := by
      rcases mem_union.mp hz with hz | hz
      · rcases mem_union.mp hz with hz | hz
        · exact Or.inr (mem_union_left _ hz)
        · exact Or.inl hz
      · exact Or.inr (mem_union_right _ hz)
    rcases split x hx with hx | hx <;> rcases split y hy with hy | hy
    · exact hc hx hy hxy
    · exact (mem_filter.mp (hi hx)).2.2 y hy
    · exact fun h => (mem_filter.mp (hi hy)).2.2 x hx (cross_symm h)
    · exact hk hx hy hxy
  have hpi : Disjoint P I := (hsep.mono_right subset_union_left).symm
  simpa only [card_union_of_disjoint hpi] using conditional_card hn (P ∪ I) Q hd' hk'

-- An inhabited geometric hypothesis domain, on the original fourteen vertices.
example : Compatible ({0,2,4,6,8,10} : Finset (ZMod 14)) := by
  intro i hi j hj hij
  simp only [mem_insert, mem_singleton] at hi hj
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact (hij rfl).elim | (simp only [ear]; change ¬ClusterAlgebras.Cross _ _; rw [ClusterAlgebras.TypeA.cross_mk_iff]; decide)

open Lean Elab Command
private def selected (n : Name) : Bool :=
  n.toString.startsWith "ClusterAlgebras." ||
  n.toString.startsWith "D5.S3.Geometry.Polygons.PolygonEarContraction." ||
  n.toString.startsWith "D5.S3.Geometry.Polygons.PolygonConditionalCounts." ||
  n.toString.startsWith "_private.D5.S3.Geometry.Polygons.PolygonEarContraction." ||
  n.toString.startsWith "_private.D5.S3.Geometry.Polygons.PolygonConditionalCounts."
run_cmd do
  let env ← getEnv
  let roots : List Name := [``PolygonConditionalCounts.conditional_card,
    ``PolygonEarContraction.forcedEquiv, ``PolygonEarContraction.earEquiv]
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing declaration {n}"
    let deps := (ci.type.getUsedConstants.toList ++
      ((ci.value? (allowOpaque := true)).map (fun e => e.getUsedConstants.toList)).getD []).eraseDups
    let children := deps.filter selected
    rows := rows.push <| Json.mkObj [("name", toJson n.toString),
      ("dependencies", toJson (deps.map Name.toString))]
    todo := children ++ todo
  let targets : List Name := [`ClusterAlgebras.IsDiagonal.isSegment, `ClusterAlgebras.catalanNumber_zero, `ClusterAlgebras.catalanNumber_succ, `ClusterAlgebras.TypeA.Interleave.symm, `ClusterAlgebras.TypeA.mem_intervalTriangulations, `ClusterAlgebras.TypeA.mk_mem_intervalDiagonals_iff, `ClusterAlgebras.TypeA.mk_mem_intervalSides_iff, `ClusterAlgebras.TypeA.not_interleave_of_mem_intervalSides, `ClusterAlgebras.TypeA.IsIntervalTriangulation.bounds_of_mem_intervalSegments, `ClusterAlgebras.TypeA.IsIntervalTriangulation.not_interleave, `ClusterAlgebras.TypeA.IsIntervalTriangulation.exists_interleave, `ClusterAlgebras.TypeA.IsIntervalTriangulation.existsUnique_apex, `ClusterAlgebras.TypeA.IsIntervalTriangulation.le_or_le_of_apex, `ClusterAlgebras.TypeA.IsIntervalTriangulation.eq_union_of_apex, `ClusterAlgebras.TypeA.IsIntervalTriangulation.inter_left_of_apex, `ClusterAlgebras.TypeA.IsIntervalTriangulation.inter_right_of_apex, `ClusterAlgebras.TypeA.mk_mem_union_intervalDiagonals_iff, `ClusterAlgebras.TypeA.IsIntervalTriangulation.union, `ClusterAlgebras.TypeA.union_inter_intervalDiagonals_left, `ClusterAlgebras.TypeA.union_inter_intervalDiagonals_right, `ClusterAlgebras.TypeA.union_apex_mem_intervalSegments, `ClusterAlgebras.TypeA.exists_equiv_intervalTriangulation, `ClusterAlgebras.TypeA.card_subtype_isIntervalTriangulation, `ClusterAlgebras.TypeA.intervalTriangulationCount_eq_sum, `ClusterAlgebras.TypeA.intervalTriangulationCount_self_add_one, `ClusterAlgebras.TypeA.intervalTriangulationCount_eq_catalanNumber, `ClusterAlgebras.TypeA.basePosSeg_mk, `ClusterAlgebras.TypeA.basePos_nonneg, `ClusterAlgebras.TypeA.basePos_lt, `ClusterAlgebras.TypeA.basePos_eq_ite, `ClusterAlgebras.TypeA.basePos_injective, `ClusterAlgebras.TypeA.exists_basePos_eq, `ClusterAlgebras.TypeA.sbtw_iff_val, `ClusterAlgebras.TypeA.sbtw_iff_sbtw_basePos, `ClusterAlgebras.TypeA.basePos_add_one, `ClusterAlgebras.TypeA.basePosSeg_injective, `ClusterAlgebras.TypeA.IsSegment.exists_basePos_lt, `ClusterAlgebras.TypeA.basePosSeg_mk_of_lt, `ClusterAlgebras.TypeA.isSide_mk_iff, `ClusterAlgebras.TypeA.cross_mk_iff, `ClusterAlgebras.TypeA.cross_mk_iff_basePos, `ClusterAlgebras.TypeA.isSide_mk_iff_basePos, `ClusterAlgebras.TypeA.bijOn_basePosSeg_isDiagonal, `ClusterAlgebras.TypeA.cross_iff_interleave, `ClusterAlgebras.TypeA.bijOn_basePosTri, `ClusterAlgebras.TypeA.encard_setOf_isTriangulation, `D5.S3.Geometry.Polygons.PolygonEarContraction.Compatible, `D5.S3.Geometry.Polygons.PolygonEarContraction.vertexLift, `D5.S3.Geometry.Polygons.PolygonEarContraction.vertexDrop, `D5.S3.Geometry.Polygons.PolygonEarContraction.chordLift, `D5.S3.Geometry.Polygons.PolygonEarContraction.chordDrop, `D5.S3.Geometry.Polygons.PolygonEarContraction.boundary_lift_iff, `D5.S3.Geometry.Polygons.PolygonEarContraction.reduce, `D5.S3.Geometry.Polygons.PolygonEarContraction.expand, `D5.S3.Geometry.Polygons.PolygonEarContraction.reduce_isTriangulation, `D5.S3.Geometry.Polygons.PolygonEarContraction.expand_isTriangulation, `D5.S3.Geometry.Polygons.PolygonEarContraction.expand_reduce, `D5.S3.Geometry.Polygons.PolygonEarContraction.reduce_expand, `D5.S3.Geometry.Polygons.PolygonEarContraction.earOneEquiv, `D5.S3.Geometry.Polygons.PolygonEarContraction.earEquiv, `D5.S3.Geometry.Polygons.PolygonEarContraction.reducedCenters, `D5.S3.Geometry.Polygons.PolygonEarContraction.forcedOneEquiv, `D5.S3.Geometry.Polygons.PolygonEarContraction.forcedEquiv, `D5.S3.Geometry.Polygons.PolygonEarContraction.compatible_card_bound, `D5.S3.Geometry.Polygons.PolygonConditionalCounts.forced_card, `D5.S3.Geometry.Polygons.PolygonConditionalCounts.Npq, `D5.S3.Geometry.Polygons.PolygonConditionalCounts.conditional_card]
  let mut statements : Array Json := #[]
  for n in targets do
    let some ci := env.find? n | throwError "Missing audit target {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"
    let ty ← liftTermElabM do
      withOptions (fun o => (o.setNat `pp.width 130).setBool `pp.fullNames true) do
        return (← Lean.Meta.ppExpr ci.type).pretty
    statements := statements.push <| Json.mkObj [("name",toJson n.toString),
      ("type",toJson ty), ("axioms",toJson (axs.map Name.toString)),
      ("consumed",toJson (seen.contains n))]
  liftIO <| IO.FS.writeFile "/tmp/fib-count-current-evidence.json" <|
    (Json.mkObj [("nodes",Json.arr rows),("statements",Json.arr statements)]).pretty
  logInfo m!"Accepted standard-three axiom guards for {statements.size} exact targets; {rows.size} selected dependency nodes."
