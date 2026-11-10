/- GID: D5/S3/Geometry/FiniteCyclicNoncoverNative
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteCyclicNoncoverNative
   mirror-E: none(waiver:original-cyclic-native-construction)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Exact cyclic survivors construct the actual CriticalData and native main/core sequences and coordinate SDRs on the original finite ambient type. -/
import D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors

/-! UNCOMPILED SOURCE. D is the SOURCE CARDINALITY bound 2q-1 or 2q.
Main K→X and standalone C→point are distinct native sequences. No claim of
core freeness in X with critical cells retained occurs anywhere in this file. -/
noncomputable section
open Set Finset
open scoped unitInterval
namespace D5.S3.Geometry.FiniteCyclicNoncoverNative
open FiniteCyclicNoncoverCollapse FiniteCyclicNoncoverUniversalSurvivors
open FiniteMatchingCoreClosure FiniteAcyclicMatchingCollapse
open FiniteAcyclicFaceMatching FiniteRelativeSimplicialCollapse
open FiniteElementaryCollapse FiniteSimplicialJoin FiniteConeCollapse
open FiniteCoordinateTruncation FiniteComponentClosure
open FiniteVertexDominationCollapse (faceSet mem_faceSet)
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem singleton_ne (p : V) (a : Finset V) (h : p ∉ a) :
    ({p} : Finset V) ≠ a := by
  intro he
  exact h (he ▸ Finset.mem_singleton_self p)

/-- Actual data for the original 3q matching, with no certificate premise. -/
def criticalData_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    FiniteMatchingCoreClosure.CriticalData (matching (by omega) s) where
  p := point (by omega) s
  critical := {criticalA q hq s, criticalB q hq s}
  D := 2*q-1
  positive := by omega
  point_mem := point_mem (by omega) s
  critical_mem := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact criticalA_mem q hq s
    · exact criticalB_mem q hq s
  point_not_critical := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨singleton_ne _ _ (criticalA_avoids_zero q hq s),
      singleton_ne _ _ (criticalB_avoids_zero q hq s)⟩
  cardinality := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact criticalA_card q hq s
    · exact criticalB_card q hq s
  unmatched := by
    intro a ha
    rw [unmatched_iff_remaining (by omega) s a ha, remaining_zero q hq s, Finset.mem_insert]

/-- Actual data for the original 3q+1 matching. -/
def criticalData_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :
    FiniteMatchingCoreClosure.CriticalData (matching (by omega) s) where
  p := point (by omega) s
  critical := {criticalOne q s}
  D := 2*q
  positive := by omega
  point_mem := point_mem (by omega) s
  critical_mem := by
    intro a ha
    have he := Finset.mem_singleton.mp ha
    simpa only [he] using criticalOne_mem q hq s
  point_not_critical := by
    exact fun h => singleton_ne _ _ (criticalOne_avoids_zero q s) (Finset.mem_singleton.mp h)
  cardinality := by
    intro a ha
    have he := Finset.mem_singleton.mp ha
    simpa only [he] using criticalOne_card q s
  unmatched := by
    intro a ha
    rw [unmatched_iff_remaining (by omega) s a ha, remaining_one q hq s, Finset.mem_insert]

/-- Actual data for the original 3q+2 matching. -/
def criticalData_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    FiniteMatchingCoreClosure.CriticalData (matching (by omega) s) where
  p := point (by omega) s
  critical := {criticalTwo q hq s}
  D := 2*q
  positive := by omega
  point_mem := point_mem (by omega) s
  critical_mem := by
    intro a ha
    have he := Finset.mem_singleton.mp ha
    simpa only [he] using criticalTwo_mem q hq s
  point_not_critical := by
    exact fun h => singleton_ne _ _ (criticalTwo_avoids_zero q hq s) (Finset.mem_singleton.mp h)
  cardinality := by
    intro a ha
    have he := Finset.mem_singleton.mp ha
    simpa only [he] using criticalTwo_card q hq s
  unmatched := by
    intro a ha
    rw [unmatched_iff_remaining (by omega) s a ha, remaining_two q hq s, Finset.mem_insert]

/-- Literal matching closure on the original V. -/
def X_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    PreAbstractSimplicialComplex V := (criticalData_zero q hq s).X
/-- Delete only the actual critical cells, retaining all proper boundaries. -/
def C_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    PreAbstractSimplicialComplex V := (criticalData_zero q hq s).C
/-- Apply the native finite acyclic extraction to original K→X. -/
def main_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    Sequence (noncover (by omega) s) (X_zero q hq s) :=
  (criticalData_zero q hq s).mainSequence (matching_acyclic (by omega) s)
/-- Apply the native extraction to standalone C→the original point. -/
def core_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    Sequence (C_zero q hq s) (vertexComplex (point (by omega) s)) :=
  (criticalData_zero q hq s).coreSequence (matching_acyclic (by omega) s)
/-- Ordered lower/upper ORIGINAL face pairs of the actual main sequence. -/
def mainPairs_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    List (Finset V × Finset V) := (main_zero q hq s).pairs.map fun P => (P.lower, P.upper)
/-- Ordered lower/upper pairs of standalone C, on the same V. -/
def corePairs_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    List (Finset V × Finset V) := (core_zero q hq s).pairs.map fun P => (P.lower, P.upper)
/-- Actual coordinate retractions and homotopy, fixed on the WHOLE X. -/
def mainSDR_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    RelativeSDR (noncover (by omega) s) (X_zero q hq s) (criticalData_zero q hq s).X_le :=
  (criticalData_zero q hq s).mainSDR (matching_acyclic (by omega) s)
/-- Actual coordinate SDR of standalone C, fixed on the whole point complex. -/
def coreSDR_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    RelativeSDR (C_zero q hq s) (vertexComplex (point (by omega) s))
      (criticalData_zero q hq s).vertex_le_C :=
  (criticalData_zero q hq s).coreSDR (matching_acyclic (by omega) s)

/-- Literal matching closure on the original V. -/
def X_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :
    PreAbstractSimplicialComplex V := (criticalData_one q hq s).X
/-- Delete only the actual critical cells, retaining all proper boundaries. -/
def C_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :
    PreAbstractSimplicialComplex V := (criticalData_one q hq s).C
/-- Apply the native finite acyclic extraction to original K→X. -/
def main_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :
    Sequence (noncover (by omega) s) (X_one q hq s) :=
  (criticalData_one q hq s).mainSequence (matching_acyclic (by omega) s)
/-- Apply the native extraction to standalone C→the original point. -/
def core_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :
    Sequence (C_one q hq s) (vertexComplex (point (by omega) s)) :=
  (criticalData_one q hq s).coreSequence (matching_acyclic (by omega) s)
/-- Ordered lower/upper ORIGINAL face pairs of the actual main sequence. -/
def mainPairs_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :
    List (Finset V × Finset V) := (main_one q hq s).pairs.map fun P => (P.lower, P.upper)
/-- Ordered lower/upper pairs of standalone C, on the same V. -/
def corePairs_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :
    List (Finset V × Finset V) := (core_one q hq s).pairs.map fun P => (P.lower, P.upper)
/-- Actual coordinate retractions and homotopy, fixed on the WHOLE X. -/
def mainSDR_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :
    RelativeSDR (noncover (by omega) s) (X_one q hq s) (criticalData_one q hq s).X_le :=
  (criticalData_one q hq s).mainSDR (matching_acyclic (by omega) s)
/-- Actual coordinate SDR of standalone C, fixed on the whole point complex. -/
def coreSDR_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :
    RelativeSDR (C_one q hq s) (vertexComplex (point (by omega) s))
      (criticalData_one q hq s).vertex_le_C :=
  (criticalData_one q hq s).coreSDR (matching_acyclic (by omega) s)

/-- Literal matching closure on the original V. -/
def X_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    PreAbstractSimplicialComplex V := (criticalData_two q hq s).X
/-- Delete only the actual critical cells, retaining all proper boundaries. -/
def C_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    PreAbstractSimplicialComplex V := (criticalData_two q hq s).C
/-- Apply the native finite acyclic extraction to original K→X. -/
def main_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    Sequence (noncover (by omega) s) (X_two q hq s) :=
  (criticalData_two q hq s).mainSequence (matching_acyclic (by omega) s)
/-- Apply the native extraction to standalone C→the original point. -/
def core_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    Sequence (C_two q hq s) (vertexComplex (point (by omega) s)) :=
  (criticalData_two q hq s).coreSequence (matching_acyclic (by omega) s)
/-- Ordered lower/upper ORIGINAL face pairs of the actual main sequence. -/
def mainPairs_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    List (Finset V × Finset V) := (main_two q hq s).pairs.map fun P => (P.lower, P.upper)
/-- Ordered lower/upper pairs of standalone C, on the same V. -/
def corePairs_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    List (Finset V × Finset V) := (core_two q hq s).pairs.map fun P => (P.lower, P.upper)
/-- Actual coordinate retractions and homotopy, fixed on the WHOLE X. -/
def mainSDR_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    RelativeSDR (noncover (by omega) s) (X_two q hq s) (criticalData_two q hq s).X_le :=
  (criticalData_two q hq s).mainSDR (matching_acyclic (by omega) s)
/-- Actual coordinate SDR of standalone C, fixed on the whole point complex. -/
def coreSDR_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    RelativeSDR (C_two q hq s) (vertexComplex (point (by omega) s))
      (criticalData_two q hq s).vertex_le_C :=
  (criticalData_two q hq s).coreSDR (matching_acyclic (by omega) s)

end D5.S3.Geometry.FiniteCyclicNoncoverNative
