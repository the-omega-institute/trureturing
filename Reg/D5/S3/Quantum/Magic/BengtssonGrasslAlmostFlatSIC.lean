import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
import Reg.Support.SingleDependentReadout
import Reg.Support.AlmostFlatSICQutrit

namespace Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC

open _root_.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
open _root_.D5.S3.Observer.WindowRegister
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexConjugate

universe u

noncomputable section

/-- The exact equality operand of the coordinate-sum theorem. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} [NeZero d] (v : ZMod d → ℂ) (j : ZMod d),
    R.readout () () (star v ⬝ᵥ (shiftMatrix d ^ (-(2 * j)).val *ᵥ v))
      (∑ r, conj (v r) * v (r + 2 * j))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 1 inferInstance (fun _ => 0) 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  intro he
  have hbad : (1 : ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

def source_registration : Registration arena (type_of% @overlap_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@overlap_sum, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.overlap_sum)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.unit
  realizationName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_shift : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} [NeZero d] (n : ℕ) (v : ZMod d → ℂ) (r : ZMod d),
    R.readout () () ((shiftMatrix d ^ n *ᵥ v) r) (v (r - (n : ZMod d)))

private theorem rejected_law_shift : ¬ arena_shift.Law rejected := by
  intro h
  exact @h 1 inferInstance 0 (fun _ => 0) 0

def source_registration_shift : Registration arena_shift (type_of% @shift_pow_mulVec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@shift_pow_mulVec, rejected, rejected_law_shift⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_shift.Law actual rejected
    rejected_law_shift
  dependence := dependence

def registration_shift :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.shift_pow_mulVec)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.unit_shift
  realizationName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.source_registration_shift
  realizationSource := none
  generated := false
  arena := .source ⟨arena_shift⟩
  objectArena := .source ⟨arena_shift⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_shift ⟨source_registration_shift⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_displacement : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} [NeZero d] (v : ZMod d → ℂ) (a b : ZMod d),
    R.readout () () (star v ⬝ᵥ (_root_.D5.S3.Quantum.Algebra.WeylDisplacement.displacement d a b *ᵥ v))
      (∑ r, conj (v (r + a)) * v r * ZMod.stdAddChar (b * r))

private theorem rejected_law_displacement : ¬ arena_displacement.Law rejected := by
  intro h
  exact @h 1 inferInstance (fun _ => 0) 0 0

def source_registration_displacement : Registration arena_displacement (type_of% @displacement_overlap_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@displacement_overlap_sum, rejected, rejected_law_displacement⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_displacement.Law actual rejected
    rejected_law_displacement
  dependence := dependence

def registration_displacement :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.displacement_overlap_sum)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.unit_displacement
  realizationName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.source_registration_displacement
  realizationSource := none
  generated := false
  arena := .source ⟨arena_displacement⟩
  objectArena := .source ⟨arena_displacement⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_displacement ⟨source_registration_displacement⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_spectral : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} [NeZero d] (f : ZMod d → ℂ) (j : ZMod d),
    R.readout () () (∑ b : ZMod d, ZMod.stdAddChar (-(b * j)) *
      (conj (∑ r, ZMod.stdAddChar (b * r) * f r) * (∑ r, ZMod.stdAddChar (b * r) * f r)))
      ((d : ℂ) * ∑ r, conj (f r) * f (r + j))

private theorem rejected_law_spectral : ¬ arena_spectral.Law rejected := by
  intro h
  exact @h 1 inferInstance (fun _ => 0) 0

def source_registration_spectral : Registration arena_spectral (type_of% @spectral_autocorrelation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spectral_autocorrelation, rejected, rejected_law_spectral⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_spectral.Law actual rejected
    rejected_law_spectral
  dependence := dependence

def registration_spectral :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.spectral_autocorrelation)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.unit_spectral
  realizationName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.source_registration_spectral
  realizationSource := none
  generated := false
  arena := .source ⟨arena_spectral⟩
  objectArena := .source ⟨arena_spectral⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_spectral ⟨source_registration_spectral⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_quartic : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} [NeZero d] (v : ZMod d → ℂ) (K : ℝ),
    (∀ a b : ZMod d, ‖star v ⬝ᵥ (_root_.D5.S3.Quantum.Algebra.WeylDisplacement.displacement d a b *ᵥ v)‖ ^ 2 =
      K * (1 + if a = 0 ∧ b = 0 then (d : ℝ) else 0)) → ∀ j : ZMod d,
    R.readout () () (∑ r, conj (v (r + j)) ^ 2 * v r * v (r + 2 * j))
      (if j = 0 then (2 * K : ℂ) else 0)

private theorem rejected_law_quartic : ¬ arena_quartic.Law rejected := by
  intro h
  exact @h 1 inferInstance (fun _ => 0) 0 (by intro a b; simp [dotProduct, Pi.star_apply]) 0

def source_registration_quartic : Registration arena_quartic (type_of% @diagonal_quartic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagonal_quartic, rejected, rejected_law_quartic⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_quartic.Law actual rejected
    rejected_law_quartic
  dependence := dependence

def registration_quartic :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.diagonal_quartic)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.unit_quartic
  realizationName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.source_registration_quartic
  realizationSource := none
  generated := false
  arena := .source ⟨arena_quartic⟩
  objectArena := .source ⟨arena_quartic⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_quartic ⟨source_registration_quartic⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def flatOne : ZMod 1 → ℂ := fun _ =>
  Complex.I * (Real.sqrt (Real.sqrt ((1 : ℝ) + 1) + 2) : ℂ)

private theorem flatOne_almostFlat : IsAlmostFlat 1 flatOne := by
  refine ⟨by simp [flatOne], ?_⟩
  intro j hj
  exact (hj (Subsingleton.elim j 0)).elim

private theorem flatOne_sic :
    _root_.D5.S3.Quantum.Magic.ErewGoldsteinSICStabilizerRefutation.IsSICFiducial 1
      ((Real.sqrt (almostFlatNorm 1) : ℂ)⁻¹ • flatOne) := by
  have hL : 0 < almostFlatNorm 1 := by unfold almostFlatNorm; positivity
  have hs : (Real.sqrt (almostFlatNorm 1) : ℂ) ^ 2 = (almostFlatNorm 1 : ℂ) := by
    exact_mod_cast Real.sq_sqrt hL.le
  constructor
  · change star ((Real.sqrt (almostFlatNorm 1) : ℂ)⁻¹ • flatOne) ⬝ᵥ
      ((Real.sqrt (almostFlatNorm 1) : ℂ)⁻¹ • flatOne) = 1
    rw [star_smul, smul_dotProduct, dotProduct_smul, squared_norm flatOne_almostFlat]
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    calc
      _ = ((Real.sqrt (almostFlatNorm 1) : ℂ) ^ 2)⁻¹ * (almostFlatNorm 1 : ℂ) := by
        ring
      _ = 1 := by
        rw [hs]
        exact inv_mul_cancel₀ (by exact_mod_cast ne_of_gt hL)
  · intro a b h
    exact (h (Subsingleton.elim _ _)).elim

abbrev signatureReal : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actualReal : Realization signatureReal :=
  realize signatureReal (fun _ _ x y => x = y) (fun e => nomatch e)

def rejectedReal : Realization signatureReal :=
  realize signatureReal (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependenceReal : ObservationalDependence signatureReal actualReal := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

abbrev arena_reflection : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} [NeZero d] {v : ZMod d → ℂ}, IsAlmostFlat d v → ∀ r : ZMod d,
    R.readout () () (conj (v r)) (-v (-r))

private theorem rejected_law_reflection : ¬ arena_reflection.Law rejected := by
  intro h
  exact @h 1 inferInstance flatOne flatOne_almostFlat 0

def source_registration_reflection : Registration arena_reflection (type_of% @conjugate_reflection) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conjugate_reflection, rejected, rejected_law_reflection⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_reflection.Law actual rejected
    rejected_law_reflection
  dependence := dependence

def registration_reflection :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.conjugate_reflection)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.unit_reflection
  realizationName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.source_registration_reflection
  realizationSource := none
  generated := false
  arena := .source ⟨arena_reflection⟩
  objectArena := .source ⟨arena_reflection⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_reflection ⟨source_registration_reflection⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_coordinate : Arena where
  signature := signatureReal
  Law R := ∀ {d : ℕ} [NeZero d] {v : ZMod d → ℂ}, IsAlmostFlat d v → ∀ r : ZMod d,
    R.readout () () (‖v r‖ ^ 2) (1 + if r = 0 then Real.sqrt (d + 1) + 1 else 0)

private theorem rejected_law_coordinate : ¬ arena_coordinate.Law rejectedReal := by
  intro h
  exact @h 1 inferInstance flatOne flatOne_almostFlat 0

def source_registration_coordinate : Registration arena_coordinate (type_of% @coordinate_norm_sq) where
  actual := actualReal
  bridge := Iff.rfl
  variation := ⟨@coordinate_norm_sq, rejectedReal, rejected_law_coordinate⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_coordinate.Law actualReal rejectedReal
    rejected_law_coordinate
  dependence := dependenceReal

def registration_coordinate :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.coordinate_norm_sq)
      (Realization signatureReal) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.unit_coordinate
  realizationName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.source_registration_coordinate
  realizationSource := none
  generated := false
  arena := .source ⟨arena_coordinate⟩
  objectArena := .source ⟨arena_coordinate⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_coordinate ⟨source_registration_coordinate⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signatureReal (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_norm : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} [NeZero d] {v : ZMod d → ℂ}, IsAlmostFlat d v →
    R.readout () () (star v ⬝ᵥ v) (almostFlatNorm d : ℂ)

private theorem rejected_law_norm : ¬ arena_norm.Law rejected := by
  intro h
  exact @h 1 inferInstance flatOne flatOne_almostFlat

def source_registration_norm : Registration arena_norm (type_of% @squared_norm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@squared_norm, rejected, rejected_law_norm⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_norm.Law actual rejected
    rejected_law_norm
  dependence := dependence

def registration_norm :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.squared_norm)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.unit_norm
  realizationName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.source_registration_norm
  realizationSource := none
  generated := false
  arena := .source ⟨arena_norm⟩
  objectArena := .source ⟨arena_norm⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_norm ⟨source_registration_norm⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_sic : Arena where
  signature := signatureReal
  Law R := ∀ {d : ℕ} [NeZero d] {v : ZMod d → ℂ}, IsAlmostFlat d v →
    _root_.D5.S3.Quantum.Magic.ErewGoldsteinSICStabilizerRefutation.IsSICFiducial d
      ((Real.sqrt (almostFlatNorm d) : ℂ)⁻¹ • v) → ∀ a b : ZMod d,
    R.readout () () (‖star v ⬝ᵥ (_root_.D5.S3.Quantum.Algebra.WeylDisplacement.displacement d a b *ᵥ v)‖ ^ 2)
      ((Real.sqrt (d + 1) + 1) ^ 2 * (1 + if a = 0 ∧ b = 0 then (d : ℝ) else 0))

private theorem rejected_law_sic : ¬ arena_sic.Law rejectedReal := by
  intro h
  exact @h 1 inferInstance flatOne flatOne_almostFlat flatOne_sic 0 0

def source_registration_sic : Registration arena_sic (type_of% @sic_overlap_squares) where
  actual := actualReal
  bridge := Iff.rfl
  variation := ⟨@sic_overlap_squares, rejectedReal, rejected_law_sic⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_sic.Law actualReal rejectedReal
    rejected_law_sic
  dependence := dependenceReal

def registration_sic :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.sic_overlap_squares)
      (Realization signatureReal) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.unit_sic
  realizationName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.source_registration_sic
  realizationSource := none
  generated := false
  arena := .source ⟨arena_sic⟩
  objectArena := .source ⟨arena_sic⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_sic ⟨source_registration_sic⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signatureReal (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_convolution : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} [NeZero d] {v : ZMod d → ℂ}, IsAlmostFlat d v → ∀ j : ZMod d,
    R.readout () () (∑ r, conj (v r) * v (r + 2 * j)) (-∑ r, v r * v (2 * j - r))

private theorem rejected_law_convolution : ¬ arena_convolution.Law rejected := by
  intro h
  exact @h 1 inferInstance flatOne flatOne_almostFlat 0

def source_registration_convolution : Registration arena_convolution (type_of% @overlap_convolution) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@overlap_convolution, rejected, rejected_law_convolution⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_convolution.Law actual rejected
    rejected_law_convolution
  dependence := dependence

def registration_convolution :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.overlap_convolution)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.unit_convolution
  realizationName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.source_registration_convolution
  realizationSource := none
  generated := false
  arena := .source ⟨arena_convolution⟩
  objectArena := .source ⟨arena_convolution⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_convolution ⟨source_registration_convolution⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_midpoint : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} [NeZero d] {v : ZMod d → ℂ}, IsAlmostFlat d v →
    R.readout () () (∑ j : ZMod d, ∑ r, conj (v (r + j)) ^ 2 * v r * v (r + 2 * j))
      (-∑ k : ZMod d, conj (v k) ^ 2 * (∑ r, conj (v r) * v (r + 2 * k)))

private theorem rejected_law_midpoint : ¬ arena_midpoint.Law rejected := by
  intro h
  exact @h 1 inferInstance flatOne flatOne_almostFlat

def source_registration_midpoint : Registration arena_midpoint (type_of% @midpoint_contraction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@midpoint_contraction, rejected, rejected_law_midpoint⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_midpoint.Law actual rejected
    rejected_law_midpoint
  dependence := dependence

def registration_midpoint :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.midpoint_contraction)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.unit_midpoint
  realizationName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.source_registration_midpoint
  realizationSource := none
  generated := false
  arena := .source ⟨arena_midpoint⟩
  objectArena := .source ⟨arena_midpoint⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_midpoint ⟨source_registration_midpoint⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_saturation : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [DecidableEq ι] (S : Finset ι) (z A : ι → ℂ) (C : ℝ),
    (∀ k ∈ S, ‖z k‖ = 1) → (∀ k ∈ S, ‖A k‖ = C) →
    (∑ k ∈ S, conj (z k) ^ 2 * A k = (C * S.card : ℝ)) → ∀ k ∈ S,
    R.readout () () (A k) ((C : ℂ) * z k ^ 2)

private theorem rejected_law_saturation : ¬ arena_saturation.{u}.Law rejected := by
  intro h
  exact h ({ULift.up ()} : Finset (ULift.{u} Unit)) (fun _ => 1) (fun _ => 1) 1 (by simp) (by simp) (by simp) (ULift.up ()) (by simp)

def source_registration_saturation : Registration arena_saturation.{u} (type_of% @phase_saturation.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@phase_saturation.{u}, rejected, rejected_law_saturation⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_saturation.{u}.Law actual rejected
    rejected_law_saturation
  dependence := dependence

def registration_saturation :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.phase_saturation.{u})
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.unit_saturation
  realizationName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.source_registration_saturation
  realizationSource := none
  generated := false
  arena := .source ⟨arena_saturation.{u}⟩
  objectArena := .source ⟨arena_saturation.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_saturation.{u} ⟨source_registration_saturation.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_result : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) [NeZero d], Odd d → ∀ v : ZMod d → ℂ, IsAlmostFlat d v →
    _root_.D5.S3.Quantum.Magic.ErewGoldsteinSICStabilizerRefutation.IsSICFiducial d
      ((Real.sqrt (almostFlatNorm d) : ℂ)⁻¹ • v) → ∀ j : ZMod d, j ≠ 0 →
    R.readout () () (star v ⬝ᵥ (shiftMatrix d ^ (-(2 * j)).val *ᵥ v))
      (((Real.sqrt (d + 1) + 1 : ℝ) : ℂ) * v j ^ 2)

private theorem rejected_law_result : ¬ arena_result.Law rejected := by
  intro h
  exact @h 3 inferInstance ⟨1, rfl⟩ Reg.Support.AlmostFlatSICQutrit.vector
    Reg.Support.AlmostFlatSICQutrit.almostFlat Reg.Support.AlmostFlatSICQutrit.sic 1 (by decide)

def source_registration_result : Registration arena_result (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law_result⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_result.Law actual rejected
    rejected_law_result
  dependence := dependence

def registration_result :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.unit_result
  realizationName := `Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC.source_registration_result
  realizationSource := none
  generated := false
  arena := .source ⟨arena_result⟩
  objectArena := .source ⟨arena_result⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_result ⟨source_registration_result⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
