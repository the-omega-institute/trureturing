/- GID: D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate
   mirror-E: none(waiver:original-label-physical-certificate)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Actual retained-edge W4 gluing consumes the native compiler on its derived raw graph root. -/
import D5.S3.Geometry.OriginalLabelTwoSum.PhysicalWheel
import D5.S3.Geometry.OriginalLabelTwoSum.WheelSupplier

/-! SOURCE_ONLY_UNCOMPILED. The only certificate input is on the actual left
path-row root. G1 constructs the graph/tree/paths; the native compiler constructs
both output sequences before the DERIVED raw-root equality transports main.
The endpoint representation a,b merely orients the selected physical tree edge.
No finiteness of VL, parent path/root premise, row history, second Family or
Sequence, global chord injectivity or desired pair-list premise is used.
This is G2 for fixed W4. G3 graph recursion and C1 remain separate work. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Finset SimpleGraph
open scoped unitInterval ContinuousMap
namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse FiniteSimplicialJoin FiniteConeCollapse
variable {VL V : Type*} [Fintype V] [DecidableEq V]

section Step
variable (left : GraphData VL V) (e : V) (he : e ∈ left.ground)
  (a b : VL) (hedge : left.edge e = s(a,b))
  (f : Wheel.Label ↪ V) (hf0 : f 0 = e)
  (hFresh : Disjoint left.ground (Wheel.Y.image f))

local notation "X" => left.ground.erase e
local notation "Yf" => Wheel.Y.image f
local notation "Zf" => Wheel.Z.image f
local notation "Rf" => Wheel.R.image f
local notation "Ef" => renameFamily f Wheel.E

/-- The existing physical construction at ANY retained edge. The four active
right labels are fresh relative to the current ground, not the whole ambient
carrier; all deleted and never-active labels remain total ambient coordinates. -/
def attachment : PhysicalGlue VL Wheel.Label V :=
  Wheel.ambientGlue left X e a b (Finset.insert_erase he).symm hedge f hf0
    (Finset.notMem_erase _ _) (hFresh.mono_left (Finset.erase_subset _ _))

local notation "g" => attachment left e he a b hedge f hf0 hFresh

/-- Actual graph/tree ground, not a ground attached to an assumed row model. -/
theorem attachment_ground : (g).data.ground = X ∪ Yf := rfl

/-- Actual unique-path-derived raw root, identified BEFORE projecting away the
empty face. PhysicalWheel consumes unrestricted physical-fiber G1 and W4 E;
its literal-index consumer is justified separately by the actual local U*. -/
theorem attachment_root : (g).data.rows.root =
    parentOf X Yf Zf e Ef left.rows.root := by
  exact Wheel.ambient_actual_root left X e a b (Finset.insert_erase he).symm
    hedge f hf0 (Finset.notMem_erase _ _)
    (hFresh.mono_left (Finset.erase_subset _ _))

/-- Every original left index and every physical surviving right index is
retained. Literal d != selected is available only via W4's proved U*. -/
theorem attachment_rows :
    (∀ c : left.chords, (g).data.rows.row (.inl c) =
      substitute e (Wheel.R.image f) (left.rows.row c)) ∧
    (∀ d : (Wheel.ambientGraph f).PhysicalSurvivor (0 : Fin 4),
      (g).data.rows.row (.inr d) = (Wheel.ambientGraph f).rows.row d.1) := by
  constructor
  · intro c
    have hr : (Wheel.ambientGraph f).rows.row (0 : Fin 4) = Wheel.R.image f :=
      (Wheel.ambient_row f 0).trans
        (congrArg (fun t : Finset Wheel.Label => t.image f) (Wheel.fundamental_rows 0))
    exact ((g).left_row c).trans (congrArg
      (fun t => substitute e t (left.rows.row c)) hr)
  · intro d
    exact (g).right_row d

/-- W4 supplies local U* without a uniqueness premise on the arbitrary left
chords or on all chord indices of a general right graph. -/
def attachment_chords : (g).data.chords ≃
    left.chords ⊕ {d : Fin 4 // d ≠ 0} :=
  (g).uniqueChordEquiv (Wheel.ambient_uniqueInterface f)

private def child (c : Certificate left.ground left.rows.root) :
    Certificate (insert e X) left.rows.root where
  supported := by
    intro s hs
    change s ⊆ insert e (left.ground.erase e)
    rw [Finset.insert_erase he]
    exact c.supported s hs
  core := c.core
  critical := c.critical
  vertex := c.vertex
  vertex_mem := c.vertex_mem
  core_supported := by
    intro s hs
    change s ⊆ insert e (left.ground.erase e)
    rw [Finset.insert_erase he]
    exact c.core_supported s hs
  critical_supported := by
    intro s hs
    change s ⊆ insert e (left.ground.erase e)
    rw [Finset.insert_erase he]
    exact c.critical_supported s hs
  cells := c.cells
  main := c.main
  separate := c.separate

private def native (c : Certificate left.ground left.rows.root) :
    Certificate (X ∪ Yf) (parentOf X Yf Zf e Ef left.rows.root) :=
  WheelSupplier.oneStep (child left e he c) f hf0 (Finset.notMem_erase _ _)
    (hFresh.mono_left (Finset.erase_subset _ _))

/-- A CONSTRUCTED native certificate on the ACTUAL glued GraphData root.
Only main needs raw-root transport; Cout, its separate list, new vertex and
critical attachments are the computed native result, unchanged by that cast. -/
def certificate (c : Certificate left.ground left.rows.root) :
    Certificate (g).data.ground (g).data.rows.root where
  supported := by
    rw [attachment_root left e he a b hedge f hf0 hFresh]
    exact (native left e he f hf0 hFresh c).supported
  core := (native left e he f hf0 hFresh c).core
  critical := (native left e he f hf0 hFresh c).critical
  vertex := (native left e he f hf0 hFresh c).vertex
  vertex_mem := (native left e he f hf0 hFresh c).vertex_mem
  core_supported := (native left e he f hf0 hFresh c).core_supported
  critical_supported := (native left e he f hf0 hFresh c).critical_supported
  cells := (native left e he f hf0 hFresh c).cells
  main := (native left e he f hf0 hFresh c).main.cast
    (congrArg project (attachment_root left e he a b hedge f hf0 hFresh)).symm rfl
  separate := (native left e he f hf0 hFresh c).separate

variable (c : Certificate left.ground left.rows.root)
local notation "out" => certificate left e he a b hedge f hf0 hFresh c

/-- Exact native critical labels, now bound to the actual graph certificate. -/
theorem certificate_critical : (out).critical =
    c.critical.image (wheelCell e (f 1) (f 3) (f 4)) :=
  WheelSupplier.oneStep_critical (child left e he c) f hf0
    (Finset.notMem_erase _ _) (hFresh.mono_left (Finset.erase_subset _ _))

/-- No image collision and exactly +2 in either branch, including sigma={e}. -/
theorem certificate_statistics : (out).critical.card = c.critical.card ∧
    ∀ q ∈ c.critical, (wheelCell e (f 1) (f 3) (f 4) q).card = q.card + 2 :=
  WheelSupplier.oneStep_statistics (child left e he c) f hf0
    (Finset.notMem_erase _ _) (hFresh.mono_left (Finset.erase_subset _ _))

/-- Nonempty, absent, ALL proper boundaries and antichain for the exact
transformed cells and the constructed Cout; no critical-data premise is added. -/
theorem certificate_cells : CriticalData (out).core
    (c.critical.image (wheelCell e (f 1) (f 3) (f 4))) := by
  rw [← certificate_critical left e he a b hedge f hf0 hFresh c]
  exact (out).cells

/-- Literal full-boundary attachment, including raw empty membership. -/
theorem certificate_boundary {s : Finset V} (hs : s ∈ (out).critical) :
    delta s ⊓ (out).core =
      (⟨{t | t ⊂ s}, fun u t hut hts => lt_of_le_of_lt hut hts⟩ : Family V) :=
  critical_intersection (out).core (out).critical (out).cells hs

/-- Exact computed terminal label. In the p=e case it is chosen from X when
nonempty and from the actual two-spoke interface R otherwise, never deleted e. -/
theorem certificate_vertex : (out).vertex =
    finishVertex X Rf e c.vertex
      (Finset.image_nonempty.mpr (by decide : Wheel.R.Nonempty)) :=
  WheelSupplier.oneStep_vertex (child left e he c) f hf0
    (Finset.notMem_erase _ _) (hFresh.mono_left (Finset.erase_subset _ _))

/-- The output core endpoint is a retained tree-edge label of the ACTUAL parent. -/
theorem certificate_survives : (out).vertex ∈ (g).data.ground ∧ (out).vertex ≠ e := by
  have hv : (out).vertex ∈ X ∪ Yf := (out).core_supported _ (out).vertex_mem (by simp)
  refine ⟨hv,?_⟩
  intro hvE
  rw [hvE] at hv
  rcases Finset.mem_union.mp hv with hx | hy
  · exact Finset.notMem_erase e left.ground hx
  · exact (Wheel.zero_outside_ground f) (hf0.symm ▸ hy)

/-- The p=e branch changes the actual core endpoint, including the X-empty
branch of the native compiler; no old e is asserted to survive. -/
theorem certificate_at_core (hp : c.vertex = e) :
    (∀ hX : (X).Nonempty, (out).vertex ∈ X) ∧
    (¬ (X).Nonempty → (out).vertex ∈ Rf) := by
  rw [certificate_vertex left e he a b hedge f hf0 hFresh c]
  constructor
  · intro hX
    simp only [finishVertex,if_pos hp,dif_pos hX]
    exact hX.choose_spec
  · intro hX
    simp only [finishVertex,if_pos hp,dif_neg hX]
    exact (show (Rf).Nonempty from
      Finset.image_nonempty.mpr (by decide : Wheel.R.Nonempty)).choose_spec

/-- Away from the selected edge the actual existing endpoint is retained. -/
theorem certificate_away_from_core (hp : c.vertex ≠ e) : (out).vertex = c.vertex := by
  rw [certificate_vertex left e he a b hedge f hf0 hFresh c]
  simp only [finishVertex,if_neg hp]

/-- Ordered (lower,upper) main list: child replay blocks, then filling blocks.
The RHS uses the ORIGINAL child main list and exact L1 constituents, including
its actual chosen Gamma, not an identity re-extracting the parent output. -/
theorem certificate_main_order : orderedPairs (out).main =
    WheelSupplier.oneStepMainFrom e f c.critical (orderedPairs c.main) := by
  change orderedPairs ((native left e he f hf0 hFresh c).main.cast
    (congrArg project (attachment_root left e he a b hedge f hf0 hFresh)).symm rfl) = _
  rw [orderedPairs_cast]
  exact WheelSupplier.oneStep_main_orderedPairs (child left e he c) f hf0
    (Finset.notMem_erase _ _) (hFresh.mono_left (Finset.erase_subset _ _))

/-- Ordered separate list on Cout ALONE: collar blocks, child-core replay,
then finishFacePairs. Its p=e cone enumerates ((X union Y).erase newApex);
p!=e uses Delta(p)*Delta(Z) union Delta(X)*E, and X-empty uses Delta(Y).
The actual Prop-valued Gamma choice is retained, not equated to Wheel.gamma. -/
theorem certificate_separate_order : orderedPairs (out).separate =
    WheelSupplier.oneStepSeparateFrom X e f c.critical c.vertex
      (orderedPairs c.separate) :=
  WheelSupplier.oneStep_separate_orderedPairs (child left e he c) f hf0
    (Finset.notMem_erase _ _) (hFresh.mono_left (Finset.erase_subset _ _))

/-- Every pair in either CONSTRUCTED list has exactly its lower and upper as
current cofaces, with a nonempty lower. No all-pair-freeness input is used. -/
theorem certificate_current_cofaces :
    (∀ P ∈ (out).main.pairs, P.lower.Nonempty ∧
      ∀ s ∈ P.ambient, P.lower ⊆ s → s = P.lower ∨ s = P.upper) ∧
    (∀ P ∈ (out).separate.pairs, P.lower.Nonempty ∧
      ∀ s ∈ P.ambient, P.lower ⊆ s → s = P.lower ∨ s = P.upper) := by
  have hc (P : CollapsePair V) : P.lower.Nonempty ∧
      ∀ s ∈ P.ambient, P.lower ⊆ s → s = P.lower ∨ s = P.upper := by
    refine ⟨P.lower_nonempty,?_⟩
    intro s hs hls
    by_cases h : s = P.lower
    · exact Or.inl h
    · exact Or.inr (P.free s hs (Finset.ssubset_iff_subset_ne.mpr ⟨hls,Ne.symm h⟩))
  exact ⟨fun P _ => hc P,fun P _ => hc P⟩

/-- These very lists retain their actual endpoints at EVERY evolving native
pair. Their CollapsePair ambients and freeness come from the real constructor. -/
theorem certificate_retained_endpoints :
    (∀ P ∈ (out).main.pairs, project (endpoint (out).core (out).critical) ≤ P.retained) ∧
    (∀ P ∈ (out).separate.pairs, project (delta {(out).vertex}) ≤ P.retained) :=
  ⟨fun _ h => (out).main.final_le_each_retained h,
   fun _ h => (out).separate.final_le_each_retained h⟩

/-- The actual main homotopy fixes every original coordinate of its ENTIRE
endpoint. The variable v ranges over all ambient labels, including ghosts. -/
theorem certificate_main_fixed (t : unitInterval)
    (x : Space (project (g).data.rows.root))
    (hx : x.val ∈ realization (project (endpoint (out).core (out).critical))) (v : V) :
    ((out).main.collapseHomotopy (t,x)).val v = x.val v :=
  compiler_main_fixed out t x hx v

/-- Separate homotopy has domain Cout alone and fixes its surviving endpoint
in the same original coordinates. It does not act on the main critical cells. -/
theorem certificate_separate_fixed (t : unitInterval)
    (x : Space (project (out).core))
    (hx : x.val ∈ realization (project (delta {(out).vertex}))) (v : V) :
    ((out).separate.collapseHomotopy (t,x)).val v = x.val v := by
  exact congrArg (fun z : Space (project (out).core) => z.val v)
    ((out).separate.collapseHomotopy_fixed t x hx)

/-- Native retractions/inclusions for the same actual main/separate lists and
endpoints. No abstract replacement space or assumed retraction is introduced. -/
theorem certificate_retractions
    (y : Space (project (endpoint (out).core (out).critical)))
    (z : Space (project (delta {(out).vertex}))) :
    (out).main.sequenceRetraction ((out).main.inclusion y) = y ∧
    (out).separate.sequenceRetraction ((out).separate.inclusion z) = z :=
  ⟨(out).main.sequenceRetraction_inclusion y,
   (out).separate.sequenceRetraction_inclusion z⟩

end Step

/-- Choose an orientation of a physical edge, not a path or a root. Sym2.ind
is the SAME unordered-pair eliminator used by G1's labelled_mem proof. -/
private def selectedEnds (left : GraphData VL V) (e : V) :
    {p : VL × VL // left.edge e = s(p.1,p.2)} := by
  have h : ∀ d : Sym2 VL, ∃ a b : VL, d = s(a,b) := by
    apply Sym2.ind
    intro a b
    exact ⟨a,b,rfl⟩
  let ha := h (left.edge e)
  let a := Classical.choose ha
  let hb := Classical.choose_spec ha
  let b := Classical.choose hb
  exact ⟨(a,b),Classical.choose_spec hb⟩

/-- The direct G3 handoff: ANY retained label gives a constructed actual
physical graph and a native certificate on THAT graph's actual raw root.
The dependent pair uses the existing PhysicalGlue and Certificate; it creates
no second state authority, graph construction or history. No endpoint orientation
is required from the caller. Freshness is only against the current ground. -/
def atRetainedEdge (left : GraphData VL V)
    (c : Certificate left.ground left.rows.root) (e : V) (he : e ∈ left.ground)
    (f : Wheel.Label ↪ V) (hf0 : f 0 = e)
    (hFresh : Disjoint left.ground (Wheel.Y.image f)) :
    Σ g : PhysicalGlue VL Wheel.Label V, Certificate (g).data.ground (g).data.rows.root :=
  let ab := selectedEnds left e
  ⟨attachment left e he ab.1.1 ab.1.2 ab.2 f hf0 hFresh,
   certificate left e he ab.1.1 ab.1.2 ab.2 f hf0 hFresh c⟩

/-- The returned graph really uses this left graph and fresh actual W4, and
BOTH exact L1 pair expansions are consumed by its graph-bound certificate.
This is a derived specification of the constructed result, not a state premise. -/
theorem atRetainedEdge_consumed (left : GraphData VL V)
    (c : Certificate left.ground left.rows.root) (e : V) (he : e ∈ left.ground)
    (f : Wheel.Label ↪ V) (hf0 : f 0 = e)
    (hFresh : Disjoint left.ground (Wheel.Y.image f)) :
    let S := atRetainedEdge left c e he f hf0 hFresh
    S.1.left = left ∧ S.1.right = Wheel.ambientGraph f ∧ S.1.e = e ∧
    S.1.data.ground = left.ground.erase e ∪ Wheel.Y.image f ∧
    S.2.critical = c.critical.image (wheelCell e (f 1) (f 3) (f 4)) ∧
    S.2.vertex ∈ S.1.data.ground ∧ S.2.vertex ≠ e ∧
    orderedPairs S.2.main =
      WheelSupplier.oneStepMainFrom e f c.critical (orderedPairs c.main) ∧
    orderedPairs S.2.separate =
      WheelSupplier.oneStepSeparateFrom (left.ground.erase e) e f c.critical c.vertex
        (orderedPairs c.separate) := by
  dsimp only [atRetainedEdge]
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_⟩
  · exact certificate_critical left e he (selectedEnds left e).1.1 (selectedEnds left e).1.2
      (selectedEnds left e).2 f hf0 hFresh c
  · exact (certificate_survives left e he (selectedEnds left e).1.1 (selectedEnds left e).1.2
      (selectedEnds left e).2 f hf0 hFresh c).1
  · exact (certificate_survives left e he (selectedEnds left e).1.1 (selectedEnds left e).1.2
      (selectedEnds left e).2 f hf0 hFresh c).2
  · exact certificate_main_order left e he (selectedEnds left e).1.1 (selectedEnds left e).1.2
      (selectedEnds left e).2 f hf0 hFresh c
  · exact certificate_separate_order left e he (selectedEnds left e).1.1 (selectedEnds left e).1.2
      (selectedEnds left e).2 f hf0 hFresh c

end D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate
