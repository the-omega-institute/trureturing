import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.Apollonian.CutoffGramLimit

namespace Reg.D5.S3.Combinatorics.Apollonian.CutoffGramLimit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages
open _root_.D5.S3.Combinatorics.Apollonian.CutoffGramLimit
open LeanInformationAudit Filter
open scoped Topology
noncomputable section
abbrev scaleSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def scaling : ∀ (_ : Unit) (_ : Unit), ℕ → ℝ := fun _ _ n => ((2:ℝ)^n)⁻¹
abbrev actual : Realization scaleSignature := realize scaleSignature scaling (fun e => nomatch e)
abbrev gramArena : Arena where
  signature := scaleSignature
  Law R := ∀ k : ℕ, Tendsto (fun t => R.readout () () (k+t) •
    (cutoffBlock k t * (cutoffBlock k t).transpose)) atTop (nhds (limitingDiagonal k))
private def bad : Realization scaleSignature :=
  realize scaleSignature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem bad_reject : ¬ gramArena.Law bad := by
  intro h
  have hh : Tendsto (fun _ : ℕ => (0 : Matrix (Vertex 0) (Vertex 0) ℝ))
      atTop (nhds (limitingDiagonal 0)) := by simpa [bad, realize] using h 0
  have he := tendsto_nhds_unique tendsto_const_nhds hh
  have hv := congrArg (fun M : Matrix (Vertex 0) (Vertex 0) ℝ => M 0 0) he
  norm_num [limitingDiagonal, faceCount, Incident, corner] at hv

def normalized_gram_tendsto_family : Registration gramArena
    (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.CutoffGramLimit.normalized_gram_tendsto)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.CutoffGramLimit.normalized_gram_tendsto,
    bad, bad_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_reject
  dependence := by
    intro i; cases i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, scaling, realize]
def registration_normalized_gram_tendsto : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.CutoffGramLimit.normalized_gram_tendsto)
    (Realization scaleSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.CutoffGramLimit.normalized_gram_tendsto_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.CutoffGramLimit.normalized_gram_tendsto_family
  realizationSource := none
  generated := false
  arena := .source ⟨gramArena⟩
  objectArena := .source ⟨gramArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source gramArena ⟨normalized_gram_tendsto_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scaleSignature scaling (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Combinatorics.Apollonian.CutoffGramLimit
