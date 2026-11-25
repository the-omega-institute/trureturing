import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Decoherence.FourLevelBathEntropyBudget
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Decoherence.FourLevelBathEntropyBudget

open Matrix
open scoped Kronecker
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Decoherence.FourLevelBathEntropyBudget
open _root_.D5.S3.Quantum.Decoherence.FourLevelBathObserver
open _root_.D5.S3.Quantum.Decoherence.FourLevelBathPhysical
open _root_.D5.S3.Quantum.Information.CoherentCopyCorrelationTax (copyMatrix copyMatrix_entry)
open GibbsBathBandwidth (gibbsWeight)

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : Bath → ℝ, Bath → System → ℂ) (fun _ => Qutrit) (fun _ => Tripartite)

/-- Read the evolved joint matrix at a fixed bath law and phase interaction. -/
def actual : Realization signature :=
  realize signature (fun _ s X => purifiedOutput s.1 (phaseUnitary s.2) X) (fun e => nomatch e)

def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Bath → ℝ) (z : Bath → System → ℂ)
    (_hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) (X : Qutrit),
    let V := (1 : Qutrit) ⊗ₖ recordEmbedding p z
    Vᴴ * V = 1 ∧ R.readout () ⟨p, z⟩ X = V * copyMatrix X * Vᴴ

private theorem nonzero_embedded_copy (p : Bath → ℝ) (z : Bath → System → ℂ)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) :
    let V := (1 : Qutrit) ⊗ₖ recordEmbedding p z
    V * copyMatrix (1 : Qutrit) * Vᴴ ≠ 0 := by
  let V := (1 : Qutrit) ⊗ₖ recordEmbedding p z
  change V * copyMatrix (1 : Qutrit) * Vᴴ ≠ 0
  have hV : Vᴴ * V = 1 := (purifiedOutput_isometricCopy p z hGram (1 : Qutrit)).1
  intro hzero
  have hcopy := congrArg (fun M : Tripartite => Vᴴ * M * V) hzero
  have hfactor : Vᴴ * (V * copyMatrix (1 : Qutrit) * Vᴴ) * V =
      copyMatrix (1 : Qutrit) := by
    calc
      _ = (Vᴴ * V) * copyMatrix (1 : Qutrit) * (Vᴴ * V) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.one_mul, Matrix.mul_one]
  rw [hfactor, Matrix.mul_zero, Matrix.zero_mul] at hcopy
  have hentry := congrArg
    (fun M : Matrix (System × System) (System × System) ℂ => M (0, 0) (0, 0)) hcopy
  have h10 : (1 : ℂ) = 0 := by
    simpa [copyMatrix_entry, Matrix.one_apply] using hentry
  exact one_ne_zero h10

private theorem zeroReadout_fails : ¬ arena.Law zeroReadout := by
  intro h
  obtain ⟨E, hE, _, hFeasible⟩ := feasible_fixed_bath_example 1 (by norm_num)
  obtain ⟨z, _, hGram⟩ := (fixed_bath_pinching_iff 1 E hE).1 hFeasible
  exact nonzero_embedded_copy (gibbsWeight 1 E) z hGram
    (h (gibbsWeight 1 E) z hGram (1 : Qutrit)).2.symm

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  obtain ⟨E, hE, _, hFeasible⟩ := feasible_fixed_bath_example 1 (by norm_num)
  let p := gibbsWeight 1 E
  obtain ⟨z, _, hGram⟩ := (fixed_bath_pinching_iff 1 E hE).1 hFeasible
  refine ⟨⟨p, z⟩, 0, 1, ?_⟩
  change purifiedOutput p (phaseUnitary z) (0 : Qutrit) ≠
    purifiedOutput p (phaseUnitary z) (1 : Qutrit)
  have hzero : purifiedOutput p (phaseUnitary z) (0 : Qutrit) = 0 := by
    apply Matrix.ext
    rintro ⟨i, x⟩ ⟨j, y⟩
    simp [purifiedOutput_entry]
  rw [hzero, (purifiedOutput_isometricCopy p z hGram (1 : Qutrit)).2]
  exact Ne.symm (nonzero_embedded_copy p z hGram)

def source_registration : Registration arena (type_of% @purifiedOutput_isometricCopy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨purifiedOutput_isometricCopy, zeroReadout, zeroReadout_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual zeroReadout
    zeroReadout_fails
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@purifiedOutput_isometricCopy) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Decoherence.FourLevelBathEntropyBudget.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Decoherence.FourLevelBathEntropyBudget.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ s X => purifiedOutput s.1 (phaseUnitary s.2) X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Decoherence.FourLevelBathEntropyBudget
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Decoherence.FourLevelBathEntropyBudget
