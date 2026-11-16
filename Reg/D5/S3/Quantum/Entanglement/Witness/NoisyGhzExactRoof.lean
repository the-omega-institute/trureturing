import Reg.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.Foundations
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Source-bound escape evidence for the independent-phase sum and the actual
finite-ensemble roof. The other theorem audits remain unfinished and are
disclosed in issue #27732; no validation is claimed for them. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
open LeanInformationAudit
open _root_.D5.S3.Quantum.Entanglement.OccupancyWordSectors
open _root_.D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof

abbrev roofSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ)
    (fun nd => Matrix (Word (Fin nd.2) nd.1) (Word (Fin nd.2) nd.1) ℂ) (fun _ => ℝ)

def roofActual : Realization roofSignature :=
  realize roofSignature (fun _ _ ρ => geometricMeasure ρ) (fun e => nomatch e)

def roofRejected : Realization roofSignature :=
  realize roofSignature (fun _ _ _ => -1) (fun e => nomatch e)

def roofArena : Arena where
  signature := roofSignature
  Law R := ∀ {n d : ℕ} (_hn : 3 ≤ n) (_hd : 3 ≤ d) {p : ℝ}
    (_hp : 0 ≤ p) (_hp1 : p ≤ 1),
    R.readout () ⟨n,d⟩ (noisyGhz n d p) = twoMeanOptimum d (noisyF n d p) (noisyY n d p) ∧
      geometricMeasure (noisyGhz n d p) =
        (max (Real.sqrt ((d-1 : ℝ)*(1-p+p/(wordCount n d : ℝ)))-
          Real.sqrt (p*(supportRank n d-1 : ℝ)/(wordCount n d : ℝ))) 0)^2/d

private theorem roof_rejected_law : ¬ roofArena.Law roofRejected := by
  intro h
  have hh := (h (n := 3) (d := 3) (by norm_num) (by norm_num)
    (p := 1) (by norm_num) (by norm_num)).1
  norm_num [roofRejected,realize,twoMeanOptimum,noisyF,noisyY,wordCount,supportRank,cutCount] at hh

def roofRegistration : Registration roofArena (roofArena.Law roofActual) where
  actual := roofActual
  bridge := Iff.rfl
  variation := ⟨@noisy_exact_roof,roofRejected,roof_rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    roofArena.Law roofActual roofRejected roof_rejected_law
  dependence := by
    change ObservationalDependence roofSignature roofActual
    intro i
    refine ⟨⟨3,3⟩,noisyGhz 3 3 0,noisyGhz 3 3 1,?_⟩
    change geometricMeasure (noisyGhz 3 3 0) ≠ geometricMeasure (noisyGhz 3 3 1)
    rw [(noisy_exact_roof (n := 3) (d := 3) (by norm_num) (by norm_num)
      (p := 0) (by norm_num) (by norm_num)).1,
      (noisy_exact_roof (n := 3) (d := 3) (by norm_num) (by norm_num)
      (p := 1) (by norm_num) (by norm_num)).1]
    norm_num [twoMeanOptimum,noisyF,noisyY,wordCount,supportRank,cutCount,twoMeanValue]

noncomputable def registration_roof :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.noisy_exact_roof)
    (type_of% (realize roofSignature (fun _ _ ρ => geometricMeasure ρ) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.roof_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.roofRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨roofArena⟩
  objectArena := .source ⟨roofArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source roofArena ⟨roofRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize roofSignature (fun _ _ ρ => geometricMeasure ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
