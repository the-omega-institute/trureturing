import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.QutritMagicCoherenceBound
import Reg.Support.DependentFamily

/-! Source-bound audit of the pure-qutrit magic–coherence lower bound. -/

namespace Reg.D5.S3.Quantum.Information.QutritMagicCoherenceBound

open _root_.D5.S3.Quantum.Information.QutritMagicCoherenceBound
open _root_.D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation (l1Coherence)
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe sum negativity as the complex qutrit amplitude vector varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Fin 3 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => sumNegativity (rankOneDensity x)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Retain normalization and the complete coherence-dependent lower bound. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ x : Fin 3 → ℂ, ∑ i, Complex.normSq (x i) = 1 →
    l1Coherence (rankOneDensity x) / 2 *
        Real.sqrt (1 - l1Coherence (rankOneDensity x) / 2) ≤ r.readout () () x

private def basisVector : Fin 3 → ℂ := ![1, 0, 0]

private theorem basisVector_normalized : ∑ i, Complex.normSq (basisVector i) = 1 := by
  norm_num [basisVector, Fin.sum_univ_three]

private theorem basisVector_coherence : l1Coherence (rankOneDensity basisVector) = 0 := by
  unfold l1Coherence rankOneDensity
  norm_num [basisVector, Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_three]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h basisVector basisVector_normalized
  norm_num [basisVector_coherence, rejected, realize] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, basisVector, ?_⟩
  change sumNegativity (rankOneDensity (0 : Fin 3 → ℂ)) ≠
    sumNegativity (rankOneDensity basisVector)
  unfold sumNegativity wigner rankOneDensity
  norm_num [basisVector, Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_three]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Information.QutritMagicCoherenceBound.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.QutritMagicCoherenceBound.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.QutritMagicCoherenceBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ x => sumNegativity (rankOneDensity x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.QutritMagicCoherenceBound
    definition := some {
      owner := `D5.S3.Quantum.Information.QutritMagicCoherenceBound
      name := `D5.S3.Quantum.Information.QutritMagicCoherenceBound.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.QutritMagicCoherenceBound
