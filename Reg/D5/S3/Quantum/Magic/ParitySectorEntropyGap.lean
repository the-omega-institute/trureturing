import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Magic.ParitySectorEntropyGap
import Reg.Support.SingleDependentReadout

/-! # Escape Registration for Parity-Sector Stabilizer-Entropy Gaps -/

namespace Reg.D5.S3.Quantum.Magic.ParitySectorEntropyGap

open scoped BigOperators Matrix
open _root_.D5.S3.Quantum.Magic.SubspaceStabilizerEntropy
open _root_.D5.S3.Quantum.Magic.ParitySectorMoments
open _root_.D5.S3.Quantum.Magic.ParitySectorEntropyGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ParitySectorExtrinsicTerms

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (d : ℕ) [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d),
    (Finset.univ.filter (fun a : ZMod d × ZMod d => a ≠ (0, 0) ∧ weylLabelOrder d a = 3)).card =
      (if 3 ∣ d then 8 else 0) ∧
    (extrinsicScore (evenIsometry d) = (evenExtrinsicFormula (O.readout () () d) : ℂ) ∧
      extrinsicScore (oddIsometry d) = (oddExtrinsicFormula d : ℂ)) ∧
    (∀ {S : Type} [Fintype S] [DecidableEq S] [NeZero (Fintype.card S)]
        (E : Matrix (ZMod d) S ℂ), Eᴴ * E = 1 →
      (LinearMap.range E.mulVecLin = evenSectorSubspace d →
        extrinsicScore E = (evenExtrinsicFormula d : ℂ)) ∧
      (LinearMap.range E.mulVecLin = oddSectorSubspace d →
        extrinsicScore E = (oddExtrinsicFormula d : ℂ)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad : extrinsicScore (evenIsometry 3) = (evenExtrinsicFormula 1 : ℂ) := by
    simpa [rejected, realize] using (h 3 (by omega) ⟨1, rfl⟩).2.1.1
  have hgood : extrinsicScore (evenIsometry 3) = (evenExtrinsicFormula 3 : ℂ) :=
    (parity_sector_extrinsic_terms 3 (by omega) ⟨1, rfl⟩).2.1.1
  have heq : evenExtrinsicFormula 3 = evenExtrinsicFormula 1 :=
    Complex.ofReal_inj.mp (hgood.symm.trans hbad)
  norm_num [evenExtrinsicFormula] at heq

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@parity_sector_extrinsic_terms)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@parity_sector_extrinsic_terms, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@parity_sector_extrinsic_terms)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Magic.ParitySectorEntropyGap.ParitySectorExtrinsicTerms.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.ParitySectorEntropyGap.ParitySectorExtrinsicTerms.evidence
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
    owner := `D5.S3.Quantum.Magic.ParitySectorEntropyGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "arg", "arg",
        "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ParitySectorExtrinsicTerms

namespace ParitySectorGapsAndPositivity

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (d : ℕ) [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d),
    ((Odd ((d + 1) / 2) ↔ d % 4 = 1) ∧ (Odd ((d - 1) / 2) ↔ d % 4 = 3)) ∧
    (0 < evenGapFormula (O.readout () () d) ∧ 0 < oddGapFormula d) ∧
    (∀ {S : Type} [Fintype S] [DecidableEq S] [NeZero (Fintype.card S)]
        (E : Matrix (ZMod d) S ℂ), Eᴴ * E = 1 →
      (LinearMap.range E.mulVecLin = evenSectorSubspace d →
        aseGap E = (evenGapFormula d : ℂ) ∧
        (d % 4 = 1 ∧ ¬ (3 ∣ d) →
          aseGap E = ((2 * ((d : ℝ) - 1) / (((d : ℝ) + 3) * ((d : ℝ) + 5)) : ℝ) : ℂ)) ∧
        (d % 4 = 1 ∧ 3 ∣ d →
          aseGap E = ((2 * ((d : ℝ) ^ 2 + 4 * (d : ℝ) - 13) /
            (((d : ℝ) + 1) * ((d : ℝ) + 5) * ((d : ℝ) + 7)) : ℝ) : ℂ)) ∧
        (d % 4 = 3 ∧ ¬ (3 ∣ d) →
          aseGap E = ((2 * ((d : ℝ) + 1) / (((d : ℝ) + 3) * ((d : ℝ) + 7)) : ℝ) : ℂ)) ∧
        (d % 4 = 3 ∧ 3 ∣ d →
          aseGap E = ((2 * ((d : ℝ) ^ 3 + 7 * (d : ℝ) ^ 2 + 11 * (d : ℝ) - 27) /
            (((d : ℝ) + 1) * ((d : ℝ) + 3) * ((d : ℝ) + 5) * ((d : ℝ) + 7)) : ℝ) : ℂ)) ∧
        0 < (aseGap E).re ∧ (aseGap E).im = 0) ∧
      (LinearMap.range E.mulVecLin = oddSectorSubspace d →
        aseGap E = (oddGapFormula d : ℂ) ∧
        (d % 4 = 3 ∧ ¬ (3 ∣ d) → aseGap E = ((2 / ((d : ℝ) + 3) : ℝ) : ℂ)) ∧
        (d % 4 = 3 ∧ 3 ∣ d →
          aseGap E = ((2 * ((d : ℝ) ^ 3 + 5 * (d : ℝ) ^ 2 - (d : ℝ) + 27) /
            (((d : ℝ) - 1) * ((d : ℝ) + 1) * ((d : ℝ) + 3) * ((d : ℝ) + 5)) : ℝ) : ℂ)) ∧
        (d % 4 = 1 ∧ ¬ (3 ∣ d) →
          aseGap E = ((2 * ((d : ℝ) ^ 2 + 6 * (d : ℝ) + 17) /
            (((d : ℝ) + 1) * ((d : ℝ) + 3) * ((d : ℝ) + 5)) : ℝ) : ℂ)) ∧
        (d % 4 = 1 ∧ 3 ∣ d →
          aseGap E = ((2 * ((d : ℝ) ^ 2 + 2 * (d : ℝ) + 5) /
            (((d : ℝ) - 1) * ((d : ℝ) + 1) * ((d : ℝ) + 5)) : ℝ) : ℂ)) ∧
        0 < (aseGap E).re ∧ (aseGap E).im = 0))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad : 0 < evenGapFormula 0 := by
    simpa [rejected, realize] using (h 3 (by omega) ⟨1, rfl⟩).2.1.1
  norm_num [evenGapFormula] at hbad

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@parity_sector_gaps_and_positivity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@parity_sector_gaps_and_positivity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@parity_sector_gaps_and_positivity)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Magic.ParitySectorEntropyGap.ParitySectorGapsAndPositivity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.ParitySectorEntropyGap.ParitySectorGapsAndPositivity.evidence
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
    owner := `D5.S3.Quantum.Magic.ParitySectorEntropyGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ParitySectorGapsAndPositivity

namespace ParitySectorWholeSpaceComparison

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (d : ℕ) [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d) (hnd3 : ¬ (3 ∣ d)),
    (evenExtrinsicFormula d = 4 / ((O.readout () () d : ℝ) + 3) ∧
      oddExtrinsicFormula d = 4 / ((d : ℝ) + 3)) ∧
    intrinsicTerm d = ((3 / ((d : ℝ) + 2) : ℝ) : ℂ) ∧
    (3 / ((d : ℝ) + 2) < evenExtrinsicFormula d ∧
      3 / ((d : ℝ) + 2) < oddExtrinsicFormula d) ∧
    (evenGapFormula d < (@intrinsicTerm ((d + 1) / 2) ⟨by omega⟩).re - 3 / ((d : ℝ) + 2) ∧
      oddGapFormula d < (@intrinsicTerm ((d - 1) / 2) ⟨by omega⟩).re - 3 / ((d : ℝ) + 2))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad : evenExtrinsicFormula 5 = 4 / ((0 : ℝ) + 3) := by
    simpa [rejected, realize] using (h 5 (by omega) ⟨2, rfl⟩ (by omega)).1.1
  have hgood : evenExtrinsicFormula 5 = 4 / ((5 : ℝ) + 3) :=
    (parity_sector_whole_space_comparison 5 (by omega) ⟨2, rfl⟩ (by omega)).1.1
  linarith

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@parity_sector_whole_space_comparison)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@parity_sector_whole_space_comparison, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@parity_sector_whole_space_comparison)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Magic.ParitySectorEntropyGap.ParitySectorWholeSpaceComparison.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.ParitySectorEntropyGap.ParitySectorWholeSpaceComparison.evidence
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
    owner := `D5.S3.Quantum.Magic.ParitySectorEntropyGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg",
        "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ParitySectorWholeSpaceComparison

end
end Reg.D5.S3.Quantum.Magic.ParitySectorEntropyGap
