import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds

namespace Reg.D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
abbrev scalarSignature : Signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
open _root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages
open _root_.D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds
open scoped Matrix.Norms.L2Operator

def late_adjacency_norm_le_readout : ∀ (_ : Unit) (_ : Unit), ℝ → ℝ := fun _ _ => Real.sqrt
abbrev late_adjacency_norm_le_actual : Realization scalarSignature :=
  realize scalarSignature late_adjacency_norm_le_readout (fun e => nomatch e)
abbrev late_adjacency_norm_le_arena : Arena where
  signature := scalarSignature
  Law R := ∀ k t : ℕ, ‖lateAdjacency k t‖ ≤
    2 * R.readout () () (3 * (3 * 2 ^ (k+t-k-1) : ℕ))
private def normBad : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ => -1) (fun e => nomatch e)
private theorem normBad_reject : ¬ late_adjacency_norm_le_arena.Law normBad := by
  intro h
  have hh : ‖lateAdjacency 0 0‖ ≤ -2 := by simpa [normBad, realize] using h 0 0
  linarith [norm_nonneg (lateAdjacency 0 0)]
def late_adjacency_norm_le_family : Registration late_adjacency_norm_le_arena
    (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds.late_adjacency_norm_le)) where
  actual := late_adjacency_norm_le_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds.late_adjacency_norm_le,
    normBad, normBad_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ normBad_reject
  dependence := by
    intro i; cases i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [late_adjacency_norm_le_actual, late_adjacency_norm_le_readout, realize]
def registration_late_adjacency_norm_le : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds.late_adjacency_norm_le) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds.late_adjacency_norm_le_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds.late_adjacency_norm_le_family
  realizationSource := none
  generated := false
  arena := .source ⟨late_adjacency_norm_le_arena⟩
  objectArena := .source ⟨late_adjacency_norm_le_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source late_adjacency_norm_le_arena ⟨late_adjacency_norm_le_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature late_adjacency_norm_le_readout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def late_adjacency_normalized_le_readout : ∀ (_ : Unit) (_ : Unit), ℝ → ℝ := fun _ _ x => (2:ℝ)^x
abbrev late_adjacency_normalized_le_actual : Realization scalarSignature :=
  realize scalarSignature late_adjacency_normalized_le_readout (fun e => nomatch e)
abbrev late_adjacency_normalized_le_arena : Arena where
  signature := scalarSignature
  Law R := ∀ k t : ℕ, 1 ≤ t → ‖lateAdjacency k t‖ / R.readout () () (((k+t:ℕ):ℝ)/2) ≤
    3 * Real.sqrt 2 / R.readout () () ((k:ℝ)/2)
private def normalizedBad : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x => if x = 0 then -1 else 1) (fun e => nomatch e)
private theorem normalizedBad_reject : ¬ late_adjacency_normalized_le_arena.Law normalizedBad := by
  intro h
  have hh : ‖lateAdjacency 0 1‖ ≤ -(3 * Real.sqrt 2) := by
    simpa [normalizedBad, realize, div_neg] using h 0 1 (by decide)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith [norm_nonneg (lateAdjacency 0 1)]
def late_adjacency_normalized_le_family : Registration late_adjacency_normalized_le_arena
    (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds.late_adjacency_normalized_le)) where
  actual := late_adjacency_normalized_le_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds.late_adjacency_normalized_le,
    normalizedBad, normalizedBad_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ normalizedBad_reject
  dependence := by
    intro i; cases i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [late_adjacency_normalized_le_actual, late_adjacency_normalized_le_readout, realize]
def registration_late_adjacency_normalized_le : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds.late_adjacency_normalized_le) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds.late_adjacency_normalized_le_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds.late_adjacency_normalized_le_family
  realizationSource := none
  generated := false
  arena := .source ⟨late_adjacency_normalized_le_arena⟩
  objectArena := .source ⟨late_adjacency_normalized_le_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source late_adjacency_normalized_le_arena ⟨late_adjacency_normalized_le_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature late_adjacency_normalized_le_readout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds
