/- GID: D5/S3/Geometry/FiniteAcyclicMatchingCollapse
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteAcyclicMatchingCollapse
   mirror-E: none(waiver:finite-multiple-critical-collapse-engine)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Same-dimensional critical faces give an actual main collapse and a separate core-to-vertex collapse. -/
import D5.S3.Geometry.FiniteMatchingCoreClosure

/-! UNCOMPILED. This consumer constructs BOTH native sequences using the same
source-extraction proof. The second is a sequence on C alone. No step of it is
asserted free in X with the critical simplices retained. The disk collars,
attachments, and sphere conclusions are deliberately separate consumers. -/

noncomputable section
open Set Finset
open scoped unitInterval

namespace D5.S3.Geometry.FiniteAcyclicMatchingCollapse

open FiniteAcyclicFaceMatching FiniteMatchingCoreClosure
open FiniteMatchingCoreClosure.Pairing FiniteMatchingCollapse.Pairing
open FiniteMatchingCollapse FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
open FiniteComponentClosure (vertexComplex)
open FiniteVertexDominationCollapse (faceSet mem_faceSet)

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace CriticalData

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}
    (A : FiniteMatchingCoreClosure.CriticalData M)

theorem unmatched_in_X {s : Finset V} (hs : s ∈ K) (hu : M.Unmatched s) : s ∈ A.X := by
  rcases (A.unmatched s hs).mp hu with rfl | hc
  · exact A.point_in_X
  · exact A.critical_in_X hc

def mainSequence (hacyc : M.IsAcyclic) : Sequence K A.X :=
  M.collapseBetween hacyc A.X A.X_le A.X_saturated K le_rfl A.X_le
    M.saturated_self (fun s hs hu => A.unmatched_in_X hs hu)

def coreSequence (hacyc : M.IsAcyclic) : Sequence A.C (vertexComplex A.p) :=
  M.collapseBetween hacyc (vertexComplex A.p)
    (A.vertex_le_C.trans (A.C_le_X.trans A.X_le)) A.vertex_saturated
    A.C (A.C_le_X.trans A.X_le) A.vertex_le_C A.C_saturated (by
      intro s hs hu
      have he := (A.core_unmatched hs).mp hu
      exact Set.mem_singleton_iff.mpr he)

def mainPairs (hacyc : M.IsAcyclic) : List (Finset V × Finset V) :=
  (A.mainSequence hacyc).pairs.map fun P => (P.lower, P.upper)

def corePairs (hacyc : M.IsAcyclic) : List (Finset V × Finset V) :=
  (A.coreSequence hacyc).pairs.map fun P => (P.lower, P.upper)

theorem main_pair_original (hacyc : M.IsAcyclic) (P : CollapsePair V)
    (hP : P ∈ (A.mainSequence hacyc).pairs) : (P.lower, P.apex) ∈ M.pairs :=
  M.collapseBetween_pairs hacyc A.X A.X_le A.X_saturated K le_rfl A.X_le
    M.saturated_self (fun s hs hu => A.unmatched_in_X hs hu) P hP

theorem core_pair_original (hacyc : M.IsAcyclic) (P : CollapsePair V)
    (hP : P ∈ (A.coreSequence hacyc).pairs) : (P.lower, P.apex) ∈ M.pairs :=
  M.collapseBetween_pairs hacyc (vertexComplex A.p)
    (A.vertex_le_C.trans (A.C_le_X.trans A.X_le)) A.vertex_saturated
    A.C (A.C_le_X.trans A.X_le) A.vertex_le_C A.C_saturated _ P hP

theorem main_lowers_nodup (hacyc : M.IsAcyclic) :
    ((A.mainSequence hacyc).pairs.map CollapsePair.lower).Nodup :=
  sequence_lowers_nodup _

theorem core_lowers_nodup (hacyc : M.IsAcyclic) :
    ((A.coreSequence hacyc).pairs.map CollapsePair.lower).Nodup :=
  sequence_lowers_nodup _

theorem main_pair_complete (hacyc : M.IsAcyclic) (e : Finset V × V)
    (he : e ∈ M.pairs) :
    (∃ P ∈ (A.mainSequence hacyc).pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ A.X :=
  matching_pair_occurs M (A.mainSequence hacyc) (A.main_pair_original hacyc) e he (M.lower_mem he)

theorem core_pair_complete (hacyc : M.IsAcyclic) (e : Finset V × V)
    (he : e ∈ M.pairs) (hl : e.1 ∈ A.C) :
    (∃ P ∈ (A.coreSequence hacyc).pairs, (P.lower, P.apex) = e) ↔
      e.1 ∉ vertexComplex A.p :=
  matching_pair_occurs M (A.coreSequence hacyc) (A.core_pair_original hacyc) e he hl

theorem main_frames (hacyc : M.IsAcyclic) (i : Nat)
    (hi : i ≤ (A.mainSequence hacyc).pairs.length) (s : Finset V) :
    s ∈ (A.mainSequence hacyc).frames.getD i A.X ↔ s ∈ K ∧
      ∀ P ∈ (A.mainSequence hacyc).pairs.take i, s ≠ P.lower ∧ s ≠ P.upper :=
  frame_mem _ i hi s

theorem core_frames (hacyc : M.IsAcyclic) (i : Nat)
    (hi : i ≤ (A.coreSequence hacyc).pairs.length) (s : Finset V) :
    s ∈ (A.coreSequence hacyc).frames.getD i (vertexComplex A.p) ↔ s ∈ A.C ∧
      ∀ P ∈ (A.coreSequence hacyc).pairs.take i, s ≠ P.lower ∧ s ≠ P.upper :=
  frame_mem _ i hi s

theorem main_frames_count (hacyc : M.IsAcyclic) :
    (A.mainSequence hacyc).frames.length = (A.mainPairs hacyc).length + 1 := by
  simp only [mainPairs, List.length_map, Sequence.frames_length]

theorem core_frames_count (hacyc : M.IsAcyclic) :
    (A.coreSequence hacyc).frames.length = (A.corePairs hacyc).length + 1 := by
  simp only [corePairs, List.length_map, Sequence.frames_length]

theorem main_endpoint (hacyc : M.IsAcyclic) :
    (A.mainSequence hacyc).frames.getD (A.mainPairs hacyc).length A.X = A.X := by
  simpa only [mainPairs, List.length_map] using frames_terminal (A.mainSequence hacyc)

theorem core_endpoint (hacyc : M.IsAcyclic) :
    (A.coreSequence hacyc).frames.getD (A.corePairs hacyc).length (vertexComplex A.p) =
      vertexComplex A.p := by
  simpa only [corePairs, List.length_map] using frames_terminal (A.coreSequence hacyc)

theorem closure_face_count :
    (faceSet A.X).card = (faceSet A.C).card + A.critical.card := by
  classical
  have heq : faceSet A.X = faceSet A.C ∪ A.critical := by
    ext s
    simp only [mem_faceSet, Finset.mem_union, A.X_core_equation]
  have hd : Disjoint (faceSet A.C) A.critical := by
    apply Finset.disjoint_left.mpr
    intro s hs hc
    exact ((mem_faceSet A.C s).mp hs).2 hc
  rw [heq, Finset.card_union_of_disjoint hd]

theorem vertex_face_count : (faceSet (vertexComplex A.p)).card = 1 := by
  classical
  have he : faceSet (vertexComplex A.p) = {{A.p}} := by
    ext s
    simp only [mem_faceSet, Finset.mem_singleton]
    rfl
  rw [he, Finset.card_singleton]

theorem main_count (hacyc : M.IsAcyclic) :
    (faceSet K).card = (faceSet A.X).card + 2 * (A.mainPairs hacyc).length := by
  simpa only [mainPairs, List.length_map] using sequence_face_count (A.mainSequence hacyc)

theorem core_count (hacyc : M.IsAcyclic) :
    (faceSet A.C).card = 1 + 2 * (A.corePairs hacyc).length := by
  have h := sequence_face_count (A.coreSequence hacyc)
  simpa only [corePairs, List.length_map, A.vertex_face_count] using h

theorem total_count (hacyc : M.IsAcyclic) :
    (faceSet K).card = 1 + A.critical.card +
      2 * ((A.mainPairs hacyc).length + (A.corePairs hacyc).length) := by
  have h1 := A.main_count hacyc
  have h2 := A.core_count hacyc
  have h3 := A.closure_face_count
  omega

def mainSDR (hacyc : M.IsAcyclic) : RelativeSDR K A.X A.X_le :=
  (A.mainSequence hacyc).realize

/-- Standalone C-to-point SDR, never claimed relative to the retained cells. -/
def coreSDR (hacyc : M.IsAcyclic) : RelativeSDR A.C (vertexComplex A.p) A.vertex_le_C :=
  (A.coreSequence hacyc).realize

theorem main_fixed (hacyc : M.IsAcyclic) (t : I)
    (x : FiniteSimplicialJoin.Space K) (hx : x.val ∈ FiniteConeCollapse.realization A.X) :
    (A.mainSDR hacyc).homotopy (t, x) = x :=
  (A.mainSDR hacyc).homotopy.eq_fst t hx

theorem core_fixed (hacyc : M.IsAcyclic) (t : I)
    (x : FiniteSimplicialJoin.Space A.C)
    (hx : x.val ∈ FiniteConeCollapse.realization (vertexComplex A.p)) :
    (A.coreSDR hacyc).homotopy (t, x) = x :=
  (A.coreSDR hacyc).homotopy.eq_fst t hx

theorem discrete_core (hD : A.D = 1) : A.C = vertexComplex A.p := by
  apply le_antisymm _ A.vertex_le_C
  intro s hs
  have hu : M.Unmatched s := by
    intro e he hse
    have huX : upper e ∈ A.X := by
      rcases hse with rfl | rfl
      · exact (A.X_saturated e he).mp hs.1
      · exact hs.1
    have hc := A.X_dimension _ huX
    have hl := Finset.card_pos.mpr (M.lower_nonempty e he)
    have huc : (upper e).card = e.1.card + 1 :=
      Finset.card_insert_of_notMem (M.apex_notMem e he)
    omega
  exact Set.mem_singleton_iff.mpr ((A.core_unmatched hs).mp hu)

theorem discrete_X_equation (hD : A.D = 1) (s : Finset V) :
    s ∈ A.X ↔ s = {A.p} ∨ s ∈ A.critical := by
  rw [A.X_core_equation, A.discrete_core hD]
  rfl

theorem discrete_core_pairs (hD : A.D = 1) (hacyc : M.IsAcyclic) :
    A.corePairs hacyc = [] := by
  have hc := A.core_count hacyc
  rw [A.discrete_core hD, A.vertex_face_count] at hc
  apply List.length_eq_zero.mp
  omega

end CriticalData
end D5.S3.Geometry.FiniteAcyclicMatchingCollapse
