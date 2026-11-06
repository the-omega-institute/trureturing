/- GID: D5/S3/Geometry/FiniteCyclicNoncoverNativeEndpoints
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteCyclicNoncoverNativeEndpoints
   mirror-E: none(waiver:original-cyclic-native-endpoints)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Actual original cyclic native sequences expose cell boundaries, ordered pair coverage, all frames/counts, and full-endpoint coordinate equations. -/
import D5.S3.Geometry.FiniteCyclicNoncoverNative

/-! UNCOMPILED SOURCE. The let-bound data are constructed in the imported
module from C01, never assumed. Each conjunct exposes an actual native endpoint
on the same original V. Core freeness is asserted only in standalone C. -/
noncomputable section
open Set Finset
open scoped unitInterval
namespace D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints
open FiniteCyclicNoncoverCollapse FiniteCyclicNoncoverNative
open FiniteMatchingCoreClosure FiniteAcyclicMatchingCollapse
open FiniteAcyclicFaceMatching FiniteRelativeSimplicialCollapse
open FiniteElementaryCollapse FiniteSimplicialJoin FiniteConeCollapse
open FiniteCoordinateTruncation FiniteComponentClosure
open FiniteVertexDominationCollapse (faceSet mem_faceSet)
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All native endpoints for the original 3*q family; no desired datum is an input. -/
theorem native_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    let A := criticalData_zero q hq s
    let K := noncover (show 0 < 3*q by omega) s
    let X := X_zero q hq s
    let C := C_zero q hq s
    let S := main_zero q hq s
    let T := core_zero q hq s
    let PS := mainPairs_zero q hq s
    let PT := corePairs_zero q hq s
    let H := mainSDR_zero q hq s
    let G := coreSDR_zero q hq s
    (∀ a : Finset V, a ∈ X ↔ a ∈ C ∨ (a.Nonempty ∧ ∃ b ∈ A.critical, a ⊆ b)) ∧
    (∀ a : Finset V, a ∈ C ↔ a ∈ X ∧ a ∉ A.critical) ∧
    (∀ a ∈ A.critical, ∀ b : Finset V, b ⊆ a → (AugmentedFace C b ↔ b ≠ a)) ∧
    (∀ a ∈ X, a.card ≤ 2*q-1) ∧
    (A.critical.card = 2) ∧
    (S.pairs.map CollapsePair.lower).Nodup ∧
    (T.pairs.map CollapsePair.lower).Nodup ∧
    (∀ P ∈ S.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧
      (P.lower, P.upper) ∈ PS) ∧
    (∀ P ∈ T.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧
      (P.lower, P.upper) ∈ PT) ∧
    (∀ e ∈ (matching (by omega) s).pairs,
      ((∃ P ∈ S.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ X) ∧
      (e.1 ∈ C → ((∃ P ∈ T.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ vertexComplex A.p))) ∧
    (∀ i, i ≤ S.pairs.length → ∀ a : Finset V,
      a ∈ S.frames.getD i X ↔ a ∈ K ∧
        ∀ P ∈ S.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧
    (∀ i, i ≤ T.pairs.length → ∀ a : Finset V,
      a ∈ T.frames.getD i (vertexComplex A.p) ↔ a ∈ C ∧
        ∀ P ∈ T.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧
    (S.frames.getD 0 X = K ∧ T.frames.getD 0 (vertexComplex A.p) = C) ∧
    (S.frames.getD PS.length X = X ∧
      T.frames.getD PT.length (vertexComplex A.p) = vertexComplex (point (by omega) s)) ∧
    (S.frames.length = PS.length+1 ∧ T.frames.length = PT.length+1) ∧
    ((faceSet K).card = (faceSet X).card + 2*PS.length ∧
      (faceSet C).card = 1 + 2*PT.length) ∧
    ((faceSet X).card = (faceSet C).card + 2 ∧
      (faceSet K).card = 1 + 2 + 2*(PS.length+PT.length)) ∧
    (∀ t : I, ∀ x : Space K, x.val ∈ realization X → ∀ v : V,
      (H.homotopy (t, x)).val v = x.val v) ∧
    (∀ t : I, ∀ x : Space C, x.val ∈ realization (vertexComplex A.p) → ∀ v : V,
      (G.homotopy (t, x)).val v = x.val v) ∧
    (∀ x : Space K, ∀ v : V, (H.homotopy (0, x)).val v = x.val v ∧
      (H.homotopy (1, x)).val v = (H.retraction x).val v) ∧
    (∀ x : Space C, ∀ v : V, (G.homotopy (0, x)).val v = x.val v ∧
      (G.homotopy (1, x)).val v = (G.retraction x).val v) ∧
    (∀ y : Space X, ∀ v : V, (H.retraction (realizationInclusion A.X_le y)).val v = y.val v) ∧
    (∀ y : Space (vertexComplex A.p), ∀ v : V,
      (G.retraction (realizationInclusion A.vertex_le_C y)).val v = y.val v) ∧
    (∀ t : I, ∀ x : Space K, ∀ v : V, v ∉ ground s → (H.homotopy (t, x)).val v = 0) ∧
    (∀ t : I, ∀ x : Space C, ∀ v : V, v ∉ ground s → (G.homotopy (t, x)).val v = 0) := by
  dsimp only
  let A := criticalData_zero q hq s
  let ac := matching_acyclic (show 3 ≤ 3*q by omega) s
  have hc : A.critical.card = 2 := by
    simp [A, criticalData_zero, criticalA_ne_B q hq s]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact A.X_cell_equation
  · exact A.mem_C
  · intro a ha b hb
    exact A.boundary_in_core_iff ha hb
  · exact A.X_dimension
  · exact hc
  · exact A.main_lowers_nodup ac
  · exact A.core_lowers_nodup ac
  · intro P hP
    exact ⟨A.main_pair_original ac P hP, List.mem_map.mpr ⟨P, hP, rfl⟩⟩
  · intro P hP
    exact ⟨A.core_pair_original ac P hP, List.mem_map.mpr ⟨P, hP, rfl⟩⟩
  · intro e he
    exact ⟨A.main_pair_complete ac e he, fun hl => A.core_pair_complete ac e he hl⟩
  · exact A.main_frames ac
  · exact A.core_frames ac
  · exact ⟨Sequence.frames_source_zero _ _, Sequence.frames_source_zero _ _⟩
  · exact ⟨A.main_endpoint ac, A.core_endpoint ac⟩
  · exact ⟨A.main_frames_count ac, A.core_frames_count ac⟩
  · exact ⟨A.main_count ac, A.core_count ac⟩
  · constructor
    · simpa only [hc] using A.closure_face_count
    · simpa only [hc] using A.total_count ac
  · intro t x hx v
    exact congrArg (fun y => y.val v) (A.main_fixed ac t x hx)
  · intro t x hx v
    exact congrArg (fun y => y.val v) (A.core_fixed ac t x hx)
  · intro x v
    exact ⟨congrArg (fun y => y.val v) ((A.mainSDR ac).homotopy.apply_zero x),
      congrArg (fun y => y.val v) ((A.mainSDR ac).homotopy.apply_one x)⟩
  · intro x v
    exact ⟨congrArg (fun y => y.val v) ((A.coreSDR ac).homotopy.apply_zero x),
      congrArg (fun y => y.val v) ((A.coreSDR ac).homotopy.apply_one x)⟩
  · intro y v
    exact congrArg (fun y => y.val v) ((A.mainSDR ac).retraction_inclusion y)
  · intro y v
    exact congrArg (fun y => y.val v) ((A.coreSDR ac).retraction_inclusion y)
  · intro t x v hv
    exact ghost_coordinate (by omega) s ((A.mainSDR ac).homotopy (t, x)) v hv
  · intro t x v hv
    let hCK := A.C_le_X.trans A.X_le
    have hh := ghost_coordinate (show 0 < 3*q by omega) s
      (realizationInclusion hCK ((A.coreSDR ac).homotopy (t, x))) v hv
    exact hh

/-- All native endpoints for the original 3*q+1 family; no desired datum is an input. -/
theorem native_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :
    let A := criticalData_one q hq s
    let K := noncover (show 0 < 3*q+1 by omega) s
    let X := X_one q hq s
    let C := C_one q hq s
    let S := main_one q hq s
    let T := core_one q hq s
    let PS := mainPairs_one q hq s
    let PT := corePairs_one q hq s
    let H := mainSDR_one q hq s
    let G := coreSDR_one q hq s
    (∀ a : Finset V, a ∈ X ↔ a ∈ C ∨ (a.Nonempty ∧ ∃ b ∈ A.critical, a ⊆ b)) ∧
    (∀ a : Finset V, a ∈ C ↔ a ∈ X ∧ a ∉ A.critical) ∧
    (∀ a ∈ A.critical, ∀ b : Finset V, b ⊆ a → (AugmentedFace C b ↔ b ≠ a)) ∧
    (∀ a ∈ X, a.card ≤ 2*q) ∧
    (A.critical.card = 1) ∧
    (S.pairs.map CollapsePair.lower).Nodup ∧
    (T.pairs.map CollapsePair.lower).Nodup ∧
    (∀ P ∈ S.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧
      (P.lower, P.upper) ∈ PS) ∧
    (∀ P ∈ T.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧
      (P.lower, P.upper) ∈ PT) ∧
    (∀ e ∈ (matching (by omega) s).pairs,
      ((∃ P ∈ S.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ X) ∧
      (e.1 ∈ C → ((∃ P ∈ T.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ vertexComplex A.p))) ∧
    (∀ i, i ≤ S.pairs.length → ∀ a : Finset V,
      a ∈ S.frames.getD i X ↔ a ∈ K ∧
        ∀ P ∈ S.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧
    (∀ i, i ≤ T.pairs.length → ∀ a : Finset V,
      a ∈ T.frames.getD i (vertexComplex A.p) ↔ a ∈ C ∧
        ∀ P ∈ T.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧
    (S.frames.getD 0 X = K ∧ T.frames.getD 0 (vertexComplex A.p) = C) ∧
    (S.frames.getD PS.length X = X ∧
      T.frames.getD PT.length (vertexComplex A.p) = vertexComplex (point (by omega) s)) ∧
    (S.frames.length = PS.length+1 ∧ T.frames.length = PT.length+1) ∧
    ((faceSet K).card = (faceSet X).card + 2*PS.length ∧
      (faceSet C).card = 1 + 2*PT.length) ∧
    ((faceSet X).card = (faceSet C).card + 1 ∧
      (faceSet K).card = 1 + 1 + 2*(PS.length+PT.length)) ∧
    (∀ t : I, ∀ x : Space K, x.val ∈ realization X → ∀ v : V,
      (H.homotopy (t, x)).val v = x.val v) ∧
    (∀ t : I, ∀ x : Space C, x.val ∈ realization (vertexComplex A.p) → ∀ v : V,
      (G.homotopy (t, x)).val v = x.val v) ∧
    (∀ x : Space K, ∀ v : V, (H.homotopy (0, x)).val v = x.val v ∧
      (H.homotopy (1, x)).val v = (H.retraction x).val v) ∧
    (∀ x : Space C, ∀ v : V, (G.homotopy (0, x)).val v = x.val v ∧
      (G.homotopy (1, x)).val v = (G.retraction x).val v) ∧
    (∀ y : Space X, ∀ v : V, (H.retraction (realizationInclusion A.X_le y)).val v = y.val v) ∧
    (∀ y : Space (vertexComplex A.p), ∀ v : V,
      (G.retraction (realizationInclusion A.vertex_le_C y)).val v = y.val v) ∧
    (∀ t : I, ∀ x : Space K, ∀ v : V, v ∉ ground s → (H.homotopy (t, x)).val v = 0) ∧
    (∀ t : I, ∀ x : Space C, ∀ v : V, v ∉ ground s → (G.homotopy (t, x)).val v = 0) := by
  dsimp only
  let A := criticalData_one q hq s
  let ac := matching_acyclic (show 3 ≤ 3*q+1 by omega) s
  have hc : A.critical.card = 1 := by
    simp [A, criticalData_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact A.X_cell_equation
  · exact A.mem_C
  · intro a ha b hb
    exact A.boundary_in_core_iff ha hb
  · exact A.X_dimension
  · exact hc
  · exact A.main_lowers_nodup ac
  · exact A.core_lowers_nodup ac
  · intro P hP
    exact ⟨A.main_pair_original ac P hP, List.mem_map.mpr ⟨P, hP, rfl⟩⟩
  · intro P hP
    exact ⟨A.core_pair_original ac P hP, List.mem_map.mpr ⟨P, hP, rfl⟩⟩
  · intro e he
    exact ⟨A.main_pair_complete ac e he, fun hl => A.core_pair_complete ac e he hl⟩
  · exact A.main_frames ac
  · exact A.core_frames ac
  · exact ⟨Sequence.frames_source_zero _ _, Sequence.frames_source_zero _ _⟩
  · exact ⟨A.main_endpoint ac, A.core_endpoint ac⟩
  · exact ⟨A.main_frames_count ac, A.core_frames_count ac⟩
  · exact ⟨A.main_count ac, A.core_count ac⟩
  · constructor
    · simpa only [hc] using A.closure_face_count
    · simpa only [hc] using A.total_count ac
  · intro t x hx v
    exact congrArg (fun y => y.val v) (A.main_fixed ac t x hx)
  · intro t x hx v
    exact congrArg (fun y => y.val v) (A.core_fixed ac t x hx)
  · intro x v
    exact ⟨congrArg (fun y => y.val v) ((A.mainSDR ac).homotopy.apply_zero x),
      congrArg (fun y => y.val v) ((A.mainSDR ac).homotopy.apply_one x)⟩
  · intro x v
    exact ⟨congrArg (fun y => y.val v) ((A.coreSDR ac).homotopy.apply_zero x),
      congrArg (fun y => y.val v) ((A.coreSDR ac).homotopy.apply_one x)⟩
  · intro y v
    exact congrArg (fun y => y.val v) ((A.mainSDR ac).retraction_inclusion y)
  · intro y v
    exact congrArg (fun y => y.val v) ((A.coreSDR ac).retraction_inclusion y)
  · intro t x v hv
    exact ghost_coordinate (by omega) s ((A.mainSDR ac).homotopy (t, x)) v hv
  · intro t x v hv
    let hCK := A.C_le_X.trans A.X_le
    have hh := ghost_coordinate (show 0 < 3*q+1 by omega) s
      (realizationInclusion hCK ((A.coreSDR ac).homotopy (t, x))) v hv
    exact hh

/-- All native endpoints for the original 3*q+2 family; no desired datum is an input. -/
theorem native_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    let A := criticalData_two q hq s
    let K := noncover (show 0 < 3*q+2 by omega) s
    let X := X_two q hq s
    let C := C_two q hq s
    let S := main_two q hq s
    let T := core_two q hq s
    let PS := mainPairs_two q hq s
    let PT := corePairs_two q hq s
    let H := mainSDR_two q hq s
    let G := coreSDR_two q hq s
    (∀ a : Finset V, a ∈ X ↔ a ∈ C ∨ (a.Nonempty ∧ ∃ b ∈ A.critical, a ⊆ b)) ∧
    (∀ a : Finset V, a ∈ C ↔ a ∈ X ∧ a ∉ A.critical) ∧
    (∀ a ∈ A.critical, ∀ b : Finset V, b ⊆ a → (AugmentedFace C b ↔ b ≠ a)) ∧
    (∀ a ∈ X, a.card ≤ 2*q) ∧
    (A.critical.card = 1) ∧
    (S.pairs.map CollapsePair.lower).Nodup ∧
    (T.pairs.map CollapsePair.lower).Nodup ∧
    (∀ P ∈ S.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧
      (P.lower, P.upper) ∈ PS) ∧
    (∀ P ∈ T.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧
      (P.lower, P.upper) ∈ PT) ∧
    (∀ e ∈ (matching (by omega) s).pairs,
      ((∃ P ∈ S.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ X) ∧
      (e.1 ∈ C → ((∃ P ∈ T.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ vertexComplex A.p))) ∧
    (∀ i, i ≤ S.pairs.length → ∀ a : Finset V,
      a ∈ S.frames.getD i X ↔ a ∈ K ∧
        ∀ P ∈ S.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧
    (∀ i, i ≤ T.pairs.length → ∀ a : Finset V,
      a ∈ T.frames.getD i (vertexComplex A.p) ↔ a ∈ C ∧
        ∀ P ∈ T.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧
    (S.frames.getD 0 X = K ∧ T.frames.getD 0 (vertexComplex A.p) = C) ∧
    (S.frames.getD PS.length X = X ∧
      T.frames.getD PT.length (vertexComplex A.p) = vertexComplex (point (by omega) s)) ∧
    (S.frames.length = PS.length+1 ∧ T.frames.length = PT.length+1) ∧
    ((faceSet K).card = (faceSet X).card + 2*PS.length ∧
      (faceSet C).card = 1 + 2*PT.length) ∧
    ((faceSet X).card = (faceSet C).card + 1 ∧
      (faceSet K).card = 1 + 1 + 2*(PS.length+PT.length)) ∧
    (∀ t : I, ∀ x : Space K, x.val ∈ realization X → ∀ v : V,
      (H.homotopy (t, x)).val v = x.val v) ∧
    (∀ t : I, ∀ x : Space C, x.val ∈ realization (vertexComplex A.p) → ∀ v : V,
      (G.homotopy (t, x)).val v = x.val v) ∧
    (∀ x : Space K, ∀ v : V, (H.homotopy (0, x)).val v = x.val v ∧
      (H.homotopy (1, x)).val v = (H.retraction x).val v) ∧
    (∀ x : Space C, ∀ v : V, (G.homotopy (0, x)).val v = x.val v ∧
      (G.homotopy (1, x)).val v = (G.retraction x).val v) ∧
    (∀ y : Space X, ∀ v : V, (H.retraction (realizationInclusion A.X_le y)).val v = y.val v) ∧
    (∀ y : Space (vertexComplex A.p), ∀ v : V,
      (G.retraction (realizationInclusion A.vertex_le_C y)).val v = y.val v) ∧
    (∀ t : I, ∀ x : Space K, ∀ v : V, v ∉ ground s → (H.homotopy (t, x)).val v = 0) ∧
    (∀ t : I, ∀ x : Space C, ∀ v : V, v ∉ ground s → (G.homotopy (t, x)).val v = 0) := by
  dsimp only
  let A := criticalData_two q hq s
  let ac := matching_acyclic (show 3 ≤ 3*q+2 by omega) s
  have hc : A.critical.card = 1 := by
    simp [A, criticalData_two]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact A.X_cell_equation
  · exact A.mem_C
  · intro a ha b hb
    exact A.boundary_in_core_iff ha hb
  · exact A.X_dimension
  · exact hc
  · exact A.main_lowers_nodup ac
  · exact A.core_lowers_nodup ac
  · intro P hP
    exact ⟨A.main_pair_original ac P hP, List.mem_map.mpr ⟨P, hP, rfl⟩⟩
  · intro P hP
    exact ⟨A.core_pair_original ac P hP, List.mem_map.mpr ⟨P, hP, rfl⟩⟩
  · intro e he
    exact ⟨A.main_pair_complete ac e he, fun hl => A.core_pair_complete ac e he hl⟩
  · exact A.main_frames ac
  · exact A.core_frames ac
  · exact ⟨Sequence.frames_source_zero _ _, Sequence.frames_source_zero _ _⟩
  · exact ⟨A.main_endpoint ac, A.core_endpoint ac⟩
  · exact ⟨A.main_frames_count ac, A.core_frames_count ac⟩
  · exact ⟨A.main_count ac, A.core_count ac⟩
  · constructor
    · simpa only [hc] using A.closure_face_count
    · simpa only [hc] using A.total_count ac
  · intro t x hx v
    exact congrArg (fun y => y.val v) (A.main_fixed ac t x hx)
  · intro t x hx v
    exact congrArg (fun y => y.val v) (A.core_fixed ac t x hx)
  · intro x v
    exact ⟨congrArg (fun y => y.val v) ((A.mainSDR ac).homotopy.apply_zero x),
      congrArg (fun y => y.val v) ((A.mainSDR ac).homotopy.apply_one x)⟩
  · intro x v
    exact ⟨congrArg (fun y => y.val v) ((A.coreSDR ac).homotopy.apply_zero x),
      congrArg (fun y => y.val v) ((A.coreSDR ac).homotopy.apply_one x)⟩
  · intro y v
    exact congrArg (fun y => y.val v) ((A.mainSDR ac).retraction_inclusion y)
  · intro y v
    exact congrArg (fun y => y.val v) ((A.coreSDR ac).retraction_inclusion y)
  · intro t x v hv
    exact ghost_coordinate (by omega) s ((A.mainSDR ac).homotopy (t, x)) v hv
  · intro t x v hv
    let hCK := A.C_le_X.trans A.X_le
    have hh := ghost_coordinate (show 0 < 3*q+2 by omega) s
      (realizationInclusion hCK ((A.coreSDR ac).homotopy (t, x))) v hv
    exact hh

end D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints
