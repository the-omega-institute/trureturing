/- GID: D5/S3/Geometry/OriginalLabelTwoSum/RowIteration
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/RowIteration
   mirror-E: none(waiver:original-label-two-sum-row-iteration)
   anchors: [mathlib/module/Mathlib.Data.Finset.Image]
   utility: none
   digest: Coupled original path-row substitutions recursively construct native certificates and critical statistics on arbitrary retained labels. -/
import D5.S3.Geometry.OriginalLabelTwoSum.WheelSupplier
import D5.S3.Geometry.OriginalLabelTwoSum.Graph

/-! UNCOMPILED. RowHistory is a literal ROW construction, not a graph-sum
construction. Its right and seed rows come from the proved fixed graph inputs.
The missing general graph-path substitution theorem is required to identify an
arbitrary RowHistory with the actual graphs in the requested supplier. Nothing
here assumes that graph binding or calls it proved. -/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
open FiniteConeCollapse FiniteSimplicialJoin
open scoped unitInterval ContinuousMap
variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- Indexed path rows transported injectively; chord indices are not discarded. -/
def renameRows (f : U ↪ V) (r : Rows U) : Rows V where
  ground := r.ground.image f
  chords := r.chords
  row c := (r.row c).image f
  row_supported c := Finset.image_subset_image (r.row_supported c)

/-- Raw root transport preserves VOID, UNIT and every original indexed row. -/
theorem renameRows_root (f : U ↪ V) (r : Rows U) :
    (renameRows f r).root = renameFamily f r.root := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨c,hc⟩
    change s ⊆ r.ground.image f \ (r.row c).image f at hc
    rw [← Finset.image_sdiff _ _ f.injective] at hc
    obtain ⟨t,ht,rfl⟩ := Finset.subset_image_iff.mp hc
    exact ⟨t,⟨c,ht⟩,rfl⟩
  · rintro ⟨t,⟨c,ht⟩,rfl⟩
    refine ⟨c,?_⟩
    change t.image f ⊆ r.ground.image f \ (r.row c).image f
    rw [← Finset.image_sdiff _ _ f.injective]
    exact Finset.image_subset_image ht

private theorem fresh_interface {e : V} (f : Wheel.Label ↪ V) (hf0 : f 0 = e) :
    e ∉ Wheel.Y.image f := by
  intro h
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
  have hz : i = 0 := f.injective (he.trans hf0.symm)
  subst i
  exact (by decide : (0 : Wheel.Label) ∉ Wheel.Y) hi

/-- The exact coupled row update. Old rows containing e are substituted; old
rows avoiding e and every non-interface right chord index are retained. -/
def appendWheelRows (r : Rows V) (e : V) (he : e ∈ r.ground)
    (f : Wheel.Label ↪ V) (hf0 : f 0 = e) : Rows V :=
  transportedRows (r.ground.erase e) (Wheel.Y.image f) e (Wheel.R.image f)
    r (renameRows f Wheel.wheelGraphData.rows) (0 : Fin 4)
    (Finset.insert_erase he).symm rfl (by simp) (fresh_interface f hf0)
    (Finset.image_subset_image (by decide : Wheel.R ⊆ Wheel.Y))

private theorem appended_root (r : Rows V) (e : V) (he : e ∈ r.ground)
    (f : Wheel.Label ↪ V) (hf0 : f 0 = e)
    (hnew : Disjoint r.ground (Wheel.Y.image f)) :
    (appendWheelRows r e he f hf0).root =
      parentOf (r.ground.erase e) (Wheel.Y.image f) (Wheel.Z.image f) e
        (renameFamily f Wheel.E) r.root := by
  have hd : Disjoint (r.ground.erase e) (Wheel.Y.image f) :=
    hnew.mono_left (Finset.erase_subset _ _)
  have hc : (renameRows f Wheel.wheelGraphData.rows).row (0 : Fin 4) =
      Wheel.R.image f := by
    change (Wheel.wheelGraphData.rows.row (0 : Fin 4)).image f = Wheel.R.image f
    rw [Wheel.fundamental_rows]
    rfl
  have hroot : ((renameRows f Wheel.wheelGraphData.rows).without (0 : Fin 4)).root =
      renameFamily f Wheel.E := by
    change (renameRows f (Wheel.wheelGraphData.rows.without (0 : Fin 4))).root = _
    rw [renameRows_root,Wheel.wheelOriginalRoot.2]
  have hz : Wheel.Z.image f = Wheel.Y.image f \ Wheel.R.image f := by
    rw [Wheel.interface_equations.1,Finset.image_sdiff _ _ f.injective]
  rw [appendWheelRows,row_transport _ _ _ _ _ _ _
    (Finset.insert_erase he).symm rfl (by simp) (fresh_interface f hf0) hd
    (Finset.image_subset_image (by decide : Wheel.R ⊆ Wheel.Y)) hc,hroot,← hz]
  rfl

private def changeGround {W W' : Finset V} {K : Family V}
    (c : Certificate W K) (h : W = W') : Certificate W' K where
  supported := by intro s hs; rw [← h]; exact c.supported s hs
  core := c.core
  critical := c.critical
  vertex := c.vertex
  vertex_mem := c.vertex_mem
  core_supported := by intro s hs; rw [← h]; exact c.core_supported s hs
  critical_supported := by intro s hs; rw [← h]; exact c.critical_supported s hs
  cells := c.cells
  main := c.main
  separate := c.separate

private def changeSource {W : Finset V} {K K' : Family V}
    (c : Certificate W K) (h : K = K') : Certificate W K' where
  supported := by intro s hs; rw [← h] at hs; exact c.supported s hs
  core := c.core
  critical := c.critical
  vertex := c.vertex
  vertex_mem := c.vertex_mem
  core_supported := c.core_supported
  critical_supported := c.critical_supported
  cells := c.cells
  main := c.main.cast (congrArg project h) rfl
  separate := c.separate

/-- Finite coupled row construction with arbitrary retained-edge choices. No
parent endpoint, critical formula, collapse or graph substitution is a field. -/
inductive RowHistory : Nat → Rows V → Type _
  | seed (f : K4.SeedLabel ↪ V) :
      RowHistory 0 (renameRows f K4.seedGraphData.rows)
  | attach {n : Nat} {r : Rows V} (old : RowHistory n r)
      (e : V) (he : e ∈ r.ground) (f : Wheel.Label ↪ V) (hf0 : f 0 = e)
      (hnew : Disjoint r.ground (Wheel.Y.image f)) :
      RowHistory (n+1) (appendWheelRows r e he f hf0)

/-- Recursive native main/core lists for the coupled row class. Both lists are
those of the real compiler; there is no separate assumed schedule or critical
endpoint in this construction. -/
def rowHistoryCertificate {n : Nat} {r : Rows V} (h : RowHistory n r) :
    Certificate r.ground r.root := by
  induction h with
  | seed f =>
    exact changeSource (renameCertificate f K4.seedGraphCertificate)
      (renameRows_root f K4.seedGraphData.rows).symm
  | @attach n r old e he f hf0 hnew ih =>
    let c := changeGround ih (Finset.insert_erase he).symm
    let d := WheelSupplier.oneStep c f hf0 (by simp)
      (hnew.mono_left (Finset.erase_subset _ _))
    exact changeSource d (appended_root r e he f hf0 hnew).symm

/-- At EVERY finite row stage there are exactly two distinct critical faces,
each of size 2n+1. This is consumed row-level source content, and requires the
still missing graph binding before it can be advertised as the graph theorem. -/
theorem rowHistory_statistics {n : Nat} {r : Rows V} (h : RowHistory n r) :
    (rowHistoryCertificate h).critical.card = 2 ∧
      ∀ s ∈ (rowHistoryCertificate h).critical, s.card = 2*n+1 := by
  induction h with
  | seed f =>
    change (K4.seed.critical.image (fun t => t.image f)).card = 2 ∧
      ∀ s ∈ K4.seed.critical.image (fun t => t.image f), s.card = 2*0+1
    constructor
    · rw [Finset.card_image_of_injective _ (Finset.image_injective f.injective)]
      decide
    · intro s hs
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
      have htcard : t.card = 1 := by
        have hh : t = {1} ∨ t = {2} := by simpa [K4.seed] using ht
        rcases hh with rfl | rfl <;> simp
      rw [Finset.card_image_of_injective _ f.injective,htcard]
      rfl
  | @attach n r old e he f hf0 hnew ih =>
    let c := changeGround (rowHistoryCertificate old) (Finset.insert_erase he).symm
    let hd := hnew.mono_left (Finset.erase_subset e r.ground)
    have stats := WheelSupplier.oneStep_statistics c f hf0 (by simp) hd
    change (WheelSupplier.oneStep c f hf0 (by simp) hd).critical.card = 2 ∧
      ∀ s ∈ (WheelSupplier.oneStep c f hf0 (by simp) hd).critical, s.card = 2*(n+1)+1
    constructor
    · exact stats.1.trans ih.1
    · intro s hs
      rw [WheelSupplier.oneStep_critical] at hs
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
      have hsize := stats.2 t ht
      have hold := ih.2 t ht
      omega


/-- Critical labels are recursively specified from the actual K4 seed and
literal wheel label substitution, independently of rowHistoryCertificate. -/
def rowHistoryCriticalSchedule {n : Nat} {r : Rows V}
    (h : RowHistory n r) : Finset (Finset V) := by
  induction h with
  | seed f => exact K4.seed.critical.image (fun t => t.image f)
  | @attach n r old e he f hf0 hnew ih =>
      exact ih.image (wheelCell e (f 1) (f 3) (f 4))

/-- The original terminal vertex recursion, starting at the renamed seed 0. -/
def rowHistoryVertexSchedule {n : Nat} {r : Rows V}
    (h : RowHistory n r) : V := by
  induction h with
  | seed f => exact f 0
  | @attach n r old e he f hf0 hnew ih =>
      exact finishVertex (r.ground.erase e) (Wheel.R.image f) e ih
        (Finset.image_nonempty.mpr (by decide : Wheel.R.Nonempty))

/-- The certificate's critical labels and vertex satisfy the independent seed
recursions; these equations transport the input data in both list inductions. -/
theorem rowHistoryCertificate_schedule_data {n : Nat} {r : Rows V}
    (h : RowHistory n r) :
    (rowHistoryCertificate h).critical = rowHistoryCriticalSchedule h ∧
    (rowHistoryCertificate h).vertex = rowHistoryVertexSchedule h := by
  induction h with
  | seed f => exact ⟨rfl, rfl⟩
  | @attach n r old e he f hf0 hnew ih =>
      let c := changeGround (rowHistoryCertificate old) (Finset.insert_erase he).symm
      let hd := hnew.mono_left (Finset.erase_subset e r.ground)
      change (WheelSupplier.oneStep c f hf0 (by simp) hd).critical =
        (rowHistoryCriticalSchedule old).image (wheelCell e (f 1) (f 3) (f 4)) ∧
        (WheelSupplier.oneStep c f hf0 (by simp) hd).vertex =
          finishVertex (r.ground.erase e) (Wheel.R.image f) e
            (rowHistoryVertexSchedule old) _
      constructor
      · rw [WheelSupplier.oneStep_critical]
        exact congrArg (fun cc => cc.image (wheelCell e (f 1) (f 3) (f 4))) ih.1
      · rw [WheelSupplier.oneStep_vertex]
        exact congrArg (fun p => finishVertex (r.ground.erase e)
          (Wheel.R.image f) e p _) ih.2

/-- Seed-based all-n main enumeration. The K4 main is an actual reflexive
operation, so its pair list is empty even after the original label map. Each
attach flatMaps the previous independently enumerated list. -/
def rowHistoryMainSchedule {n : Nat} {r : Rows V}
    (h : RowHistory n r) : List (Finset V × Finset V) := by
  induction h with
  | seed f => exact []
  | @attach n r old e he f hf0 hnew ih =>
      exact WheelSupplier.oneStepMainFrom e f
        (rowHistoryCriticalSchedule old) ih

/-- Seed-based all-n core enumeration, including recursively computed critical
labels and vertex. Neither attach reads a previous certificate's native pairs. -/
def rowHistorySeparateSchedule {n : Nat} {r : Rows V}
    (h : RowHistory n r) : List (Finset V × Finset V) := by
  induction h with
  | seed f => exact []
  | @attach n r old e he f hf0 hnew ih =>
      exact WheelSupplier.oneStepSeparateFrom (r.ground.erase e) e f
        (rowHistoryCriticalSchedule old) (rowHistoryVertexSchedule old) ih

/-- The main induction consumes the previous list equality through the raw
wheel substitution, together with the independent critical-label recursion. -/
theorem rowHistoryCertificate_main_orderedPairs {n : Nat} {r : Rows V}
    (h : RowHistory n r) :
    orderedPairs (rowHistoryCertificate h).main = rowHistoryMainSchedule h := by
  induction h with
  | seed f =>
      change orderedPairs (changeSource (renameCertificate f K4.seedGraphCertificate)
        (renameRows_root f K4.seedGraphData.rows).symm).main = []
      simpa only [changeSource, renameCertificate, orderedPairs_cast,
        orderedPairs, orderedPair, K4.seedGraphCertificate, K4.seed,
        Sequence.pairs_cast, Sequence.pairs, List.map_nil] using
        renameSequence_pairs f K4.seedGraphCertificate.main
  | @attach n r old e he f hf0 hnew ih =>
      let c := changeGround (rowHistoryCertificate old) (Finset.insert_erase he).symm
      change orderedPairs
        ((WheelSupplier.oneStep c f hf0 (by simp)
          (hnew.mono_left (Finset.erase_subset _ _))).main.cast
            (congrArg project (appended_root r e he f hf0 hnew).symm) rfl) = _
      rw [orderedPairs_cast, WheelSupplier.oneStep_main_orderedPairs]
      change WheelSupplier.oneStepMainFrom e f
        (rowHistoryCertificate old).critical (orderedPairs (rowHistoryCertificate old).main) = _
      rw [ih, (rowHistoryCertificate_schedule_data old).1] <;> rfl

/-- The separate induction consumes its own previous-list hypothesis, and both
critical/vertex transports. It preserves collars/replay/terminal append order. -/
theorem rowHistoryCertificate_separate_orderedPairs {n : Nat} {r : Rows V}
    (h : RowHistory n r) :
    orderedPairs (rowHistoryCertificate h).separate = rowHistorySeparateSchedule h := by
  induction h with
  | seed f =>
      change orderedPairs (changeSource (renameCertificate f K4.seedGraphCertificate)
        (renameRows_root f K4.seedGraphData.rows).symm).separate = []
      simpa only [changeSource, renameCertificate, orderedPairs_cast,
        orderedPairs, orderedPair, K4.seedGraphCertificate, K4.seed,
        Sequence.pairs_cast, Sequence.pairs, List.map_nil] using
        renameSequence_pairs f K4.seedGraphCertificate.separate
  | @attach n r old e he f hf0 hnew ih =>
      let c := changeGround (rowHistoryCertificate old) (Finset.insert_erase he).symm
      change orderedPairs
        (WheelSupplier.oneStep c f hf0 (by simp)
          (hnew.mono_left (Finset.erase_subset _ _))).separate = _
      rw [WheelSupplier.oneStep_separate_orderedPairs]
      change WheelSupplier.oneStepSeparateFrom (r.ground.erase e) e f
        (rowHistoryCertificate old).critical (rowHistoryCertificate old).vertex
        (orderedPairs (rowHistoryCertificate old).separate) = _
      rw [ih, (rowHistoryCertificate_schedule_data old).1,
        (rowHistoryCertificate_schedule_data old).2] <;> rfl

/-- A certificate consumer keeps BOTH all-n list expansions and the actual
whole-endpoint coordinate-fixed homotopy. No graph identification is assumed. -/
theorem rowHistoryCertificate_expansion {n : Nat} {r : Rows V}
    (h : RowHistory n r) :
    orderedPairs (rowHistoryCertificate h).main = rowHistoryMainSchedule h ∧
    orderedPairs (rowHistoryCertificate h).separate = rowHistorySeparateSchedule h ∧
    ∀ (t : unitInterval) (x : Space (project r.root)),
      x.val ∈ realization (project (endpoint
        (rowHistoryCertificate h).core (rowHistoryCertificate h).critical)) →
      ∀ v : V, ((rowHistoryCertificate h).main.collapseHomotopy (t,x)).val v = x.val v := by
  exact ⟨rowHistoryCertificate_main_orderedPairs h,
    rowHistoryCertificate_separate_orderedPairs h,
    fun t x hx v => compiler_main_fixed (rowHistoryCertificate h) t x hx v⟩

/-- The fixed K4 seed/fresh-wheel construction consumes both genuine recursive
expansions. Actual graph G2/history/closed-chain binding is still separate. -/
theorem rowHistory_fixed_seed_fresh_wheel
    (f : K4.SeedLabel ↪ V) (e : V)
    (he : e ∈ (renameRows f K4.seedGraphData.rows).ground)
    (wheel : Wheel.Label ↪ V) (h0 : wheel 0 = e)
    (hnew : Disjoint (renameRows f K4.seedGraphData.rows).ground
      (Wheel.Y.image wheel)) :
    orderedPairs (rowHistoryCertificate
      (RowHistory.attach (RowHistory.seed f) e he wheel h0 hnew)).main =
      rowHistoryMainSchedule
        (RowHistory.attach (RowHistory.seed f) e he wheel h0 hnew) ∧
    orderedPairs (rowHistoryCertificate
      (RowHistory.attach (RowHistory.seed f) e he wheel h0 hnew)).separate =
      rowHistorySeparateSchedule
        (RowHistory.attach (RowHistory.seed f) e he wheel h0 hnew) := by
  have h := rowHistoryCertificate_expansion
    (RowHistory.attach (RowHistory.seed f) e he wheel h0 hnew)
  exact ⟨h.1, h.2.1⟩

end D5.S3.Geometry.OriginalLabelTwoSum
