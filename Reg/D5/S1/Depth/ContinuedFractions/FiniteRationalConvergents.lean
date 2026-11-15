import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents

namespace Reg.D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents.Correspondence
open QuantumShorContinuedFractions
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℚ) (fun _ => List ℚ)
def actual : Realization signature :=
  realize signature (fun _ _ x => convergents x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (x z : ℚ), z ∈ R.readout () () x ↔ ∃ k, Real.convergent (x : ℝ) k = z
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 0 0).mpr ⟨0, by simp⟩
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change convergents 0 ≠ convergents 1
  norm_num [convergents, reduced, Int.fract]

def source_registration : Registration arena (type_of% @QuantumShorContinuedFractions.mem_convergents_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@QuantumShorContinuedFractions.mem_convergents_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@QuantumShorContinuedFractions.mem_convergents_iff) (Realization signature) Unit Unit := {
  unitName := `QuantumShorContinuedFractions.mem_convergents_iff.__information_unit
  realizationName := `Reg.D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents.Correspondence.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => convergents x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents.Correspondence

namespace Reg.D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents.Denominator
open QuantumShorContinuedFractions
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ r s => (reduced s r).den) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (s r : ℕ), 0 < r → R.readout () r s = r / Nat.gcd s r
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 1 (by decide)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  change (reduced 0 2).den ≠ (reduced 1 2).den
  rw [reduced_den _ _ (by decide), reduced_den _ _ (by decide)]
  norm_num

def source_registration : Registration arena (type_of% @QuantumShorContinuedFractions.reduced_den) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@QuantumShorContinuedFractions.reduced_den, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@QuantumShorContinuedFractions.reduced_den) (Realization signature) Unit Unit := {
  unitName := `QuantumShorContinuedFractions.reduced_den.__information_unit
  realizationName := `Reg.D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents.Denominator.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r s => (reduced s r).den) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents.Denominator

namespace Reg.D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents.TailDenominator
open QuantumShorContinuedFractions
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℚ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ x => ((Int.fract x)⁻¹).den) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => x.den) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ x : ℚ, Int.fract x ≠ 0 → R.readout () () x < x.den
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (1 / 2) (by norm_num [Int.fract])
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2 / 3, ?_⟩
  change ((Int.fract (0 : ℚ))⁻¹).den ≠ ((Int.fract (2 / 3 : ℚ))⁻¹).den
  norm_num [Int.fract]
  change 1 ≠ (reduced 3 2).den
  rw [reduced_den _ _ (by decide)]
  norm_num

def source_registration : Registration arena (type_of% @QuantumShorContinuedFractions.tail_den_lt) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@QuantumShorContinuedFractions.tail_den_lt, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@QuantumShorContinuedFractions.tail_den_lt) (Realization signature) Unit Unit := {
  unitName := `QuantumShorContinuedFractions.tail_den_lt.__information_unit
  realizationName := `Reg.D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents.TailDenominator.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => ((Int.fract x)⁻¹).den) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents.TailDenominator
