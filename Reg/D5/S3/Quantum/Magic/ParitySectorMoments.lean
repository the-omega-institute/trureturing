import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Magic.ParitySectorMoments
import Reg.Support.SingleDependentReadout

/-! # Escape Registration for Qudit Parity Sectors and Compressed Moments -/

namespace Reg.D5.S3.Quantum.Magic.ParitySectorMoments

open scoped BigOperators Matrix
open _root_.D5.S3.Quantum.Magic.SubspaceStabilizerEntropy
open _root_.D5.S3.Quantum.Magic.ParitySectorMoments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ParitySectorsBasesAndIsometries

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (d : ℕ) [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d),
    ((parityMatrix d) ^ 2 = 1 ∧ (parityMatrix d)ᴴ = parityMatrix d) ∧
    ((evenIsometry d)ᴴ * evenIsometry d = 1 ∧ evenIsometry d * (evenIsometry d)ᴴ = evenProjector d ∧
      LinearMap.range (evenIsometry d).mulVecLin = evenSectorSubspace d ∧
      Module.finrank ℂ (evenSectorSubspace d) = (O.readout () () d + 1) / 2) ∧
    ((oddIsometry d)ᴴ * oddIsometry d = 1 ∧ oddIsometry d * (oddIsometry d)ᴴ = oddProjector d ∧
      LinearMap.range (oddIsometry d).mulVecLin = oddSectorSubspace d ∧
      Module.finrank ℂ (oddSectorSubspace d) = (d - 1) / 2) ∧
    (∀ {S : Type} [Fintype S] [DecidableEq S] [NeZero (Fintype.card S)]
        (E : Matrix (ZMod d) S ℂ), Eᴴ * E = 1 →
      (LinearMap.range E.mulVecLin = evenSectorSubspace d →
        E * Eᴴ = evenProjector d ∧ Fintype.card S = (d + 1) / 2 ∧
        (∀ a : ZMod d × ZMod d, labelFourthMoment E a = labelFourthMoment (evenIsometry d) a) ∧
        aseGap E =
          @aseGap d _ (Fin ((d + 1) / 2)) _ ⟨by rw [Fintype.card_fin]; omega⟩ (evenIsometry d)) ∧
      (LinearMap.range E.mulVecLin = oddSectorSubspace d →
        E * Eᴴ = oddProjector d ∧ Fintype.card S = (d - 1) / 2 ∧
        (∀ a : ZMod d × ZMod d, labelFourthMoment E a = labelFourthMoment (oddIsometry d) a) ∧
        aseGap E =
          @aseGap d _ (Fin ((d - 1) / 2)) _ ⟨by rw [Fintype.card_fin]; omega⟩ (oddIsometry d)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad : Module.finrank ℂ (evenSectorSubspace 3) = 0 := by
    simpa [rejected, realize] using (h 3 (by omega) ⟨1, rfl⟩).2.1.2.2.2
  have hgood : Module.finrank ℂ (evenSectorSubspace 3) = 2 :=
    (parity_sectors_bases_and_isometries 3 (by omega) ⟨1, rfl⟩).2.1.2.2.2
  omega

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@parity_sectors_bases_and_isometries)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@parity_sectors_bases_and_isometries, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@parity_sectors_bases_and_isometries)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Magic.ParitySectorMoments.ParitySectorsBasesAndIsometries.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.ParitySectorMoments.ParitySectorsBasesAndIsometries.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.ParitySectorMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ParitySectorsBasesAndIsometries

namespace ParityCliffordLabelReduction

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (d : ℕ) [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d),
    (labelFourthMoment (evenIsometry d) (0, 0) = 1 ∧
      labelFourthMoment (oddIsometry d) (0, 0) = 1) ∧
    (∀ a : ZMod d × ZMod d, a ≠ (0, 0) →
      ∃ h : ℤ, Int.gcd h (O.readout () () d) = Int.gcd (a.1.val : ℤ) (Int.gcd (a.2.val : ℤ) d) ∧
        labelFourthMoment (evenIsometry d) a =
          labelFourthMoment (evenIsometry d) (0, (h : ZMod d)) ∧
        labelFourthMoment (oddIsometry d) a =
          labelFourthMoment (oddIsometry d) (0, (h : ZMod d)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  rcases (h 9 (by omega) ⟨4, rfl⟩).2 (0, 3) (by decide) with ⟨k, hk, _⟩
  simp only [rejected, realize, Nat.cast_one, Int.gcd_one_right] at hk
  revert hk; decide

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@parity_clifford_label_reduction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@parity_clifford_label_reduction, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@parity_clifford_label_reduction)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Magic.ParitySectorMoments.ParityCliffordLabelReduction.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.ParitySectorMoments.ParityCliffordLabelReduction.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.ParitySectorMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "body", "arg", "body", "fn", "arg",
        "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ParityCliffordLabelReduction

namespace ParityClockCompressionAndPowerSums

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (d : ℕ) [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d) (h : ℤ),
    ((evenIsometry d)ᴴ * paperDisplacement d (0, (h : ZMod d)) * evenIsometry d =
        Matrix.diagonal (fun idx => (evenClockDiag d h idx : ℂ)) ∧
      (oddIsometry d)ᴴ * paperDisplacement d (0, (h : ZMod d)) * oddIsometry d =
        Matrix.diagonal (fun idx => (oddClockDiag d h idx : ℂ))) ∧
    ((h : ZMod d) ≠ 0 →
      let n := d / Int.gcd h d
      (evenClockPowerSum d h 1 = 1 / 2 ∧ oddClockPowerSum d h 1 = -1 / 2) ∧
      (evenClockPowerSum d h 2 = ((O.readout () () d : ℝ) + 2) / 4 ∧
        oddClockPowerSum d h 2 = ((d : ℝ) - 2) / 4) ∧
      (evenClockPowerSum d h 3 = (if n = 3 then ((d : ℝ) + 4) / 8 else 1 / 2) ∧
        oddClockPowerSum d h 3 = (if n = 3 then ((d : ℝ) - 4) / 8 else -1 / 2)) ∧
      (evenClockPowerSum d h 4 = (3 * (d : ℝ) + 8) / 16 ∧
        oddClockPowerSum d h 4 = (3 * (d : ℝ) - 8) / 16))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad : evenClockPowerSum 3 1 2 = ((0 : ℝ) + 2) / 4 := by
    simpa [rejected, realize] using ((h 3 (by omega) ⟨1, rfl⟩ 1).2 (by decide)).2.1.1
  have hgood : evenClockPowerSum 3 1 2 = ((3 : ℝ) + 2) / 4 :=
    ((parity_clock_compression_and_power_sums 3 (by omega) ⟨1, rfl⟩ 1).2 (by decide)).2.1.1
  linarith

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@parity_clock_compression_and_power_sums)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@parity_clock_compression_and_power_sums, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@parity_clock_compression_and_power_sums)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Magic.ParitySectorMoments.ParityClockCompressionAndPowerSums.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.ParitySectorMoments.ParityClockCompressionAndPowerSums.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.ParitySectorMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "body", "arg", "fn", "arg",
        "fn", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ParityClockCompressionAndPowerSums

namespace ParityNonzeroLabelFourthMoment

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (d : ℕ) [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d) (a : ZMod d × ZMod d) (ha : a ≠ (0, 0)),
    (weylLabelOrder d a ≠ 3 →
      labelFourthMoment (evenIsometry d) a =
        (((3 : ℝ) / (((O.readout () () d : ℝ) + 1) * ((d : ℝ) + 3))) : ℂ) ∧
      labelFourthMoment (oddIsometry d) a = (((3 : ℝ) / (((d : ℝ) + 1) * ((d : ℝ) + 3))) : ℂ)) ∧
    (weylLabelOrder d a = 3 →
      labelFourthMoment (evenIsometry d) a =
        (((3 * (d : ℝ) + 35) / (((d : ℝ) + 1) * ((d : ℝ) + 5) * ((d : ℝ) + 7))) : ℂ) ∧
      labelFourthMoment (oddIsometry d) a =
        (((3 * (d : ℝ) - 5) / (((d : ℝ) - 1) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) : ℂ))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad : labelFourthMoment (evenIsometry 5) (0, 1) =
      (((3 : ℝ) / (((0 : ℝ) + 1) * ((5 : ℝ) + 3))) : ℂ) := by
    simpa [rejected, realize] using ((h 5 (by omega) ⟨2, rfl⟩ (0, 1) (by decide)).1 (by decide)).1
  have hgood : labelFourthMoment (evenIsometry 5) (0, 1) =
      (((3 : ℝ) / (((5 : ℝ) + 1) * ((5 : ℝ) + 3))) : ℂ) :=
    ((parity_nonzero_label_fourth_moment 5 (by omega) ⟨2, rfl⟩ (0, 1) (by decide)).1 (by decide)).1
  have heq := hgood.symm.trans hbad
  norm_num at heq

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@parity_nonzero_label_fourth_moment)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@parity_nonzero_label_fourth_moment, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@parity_nonzero_label_fourth_moment)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Magic.ParitySectorMoments.ParityNonzeroLabelFourthMoment.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.ParitySectorMoments.ParityNonzeroLabelFourthMoment.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.ParitySectorMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "arg",
        "arg", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ParityNonzeroLabelFourthMoment

end
end Reg.D5.S3.Quantum.Magic.ParitySectorMoments
