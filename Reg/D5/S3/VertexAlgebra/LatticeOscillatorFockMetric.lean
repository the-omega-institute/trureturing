import D5.S3.VertexAlgebra.LatticeOscillatorFockMetric
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockForm
open _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MvPolynomial
open scoped BigOperators Matrix

noncomputable section

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro axis; exact Fin.elim0 axis
  even_diagonal := by intro axis; exact Fin.elim0 axis

private theorem emptyHG : (0 : Matrix (Fin emptyLattice.rank) (Fin emptyLattice.rank) ℂ) *
    gramComplex emptyLattice = 1 := by
  exact funext fun axis => Fin.elim0 axis

private theorem emptyGH : gramComplex emptyLattice *
    (0 : Matrix (Fin emptyLattice.rank) (Fin emptyLattice.rank) ℂ) = 1 := by
  exact funext fun axis => Fin.elim0 axis

private theorem emptyPositive : (gramReal emptyLattice).PosDef := by
  constructor
  · exact funext fun axis => Fin.elim0 axis
  · intro vector nonzero
    exact False.elim (nonzero (Finsupp.ext fun axis => Fin.elim0 axis))

private theorem emptyFactorization :
    (fun axis other => (emptyLattice.G axis other : ℝ)) =
      (0 : Matrix (Fin emptyLattice.rank) (Fin emptyLattice.rank) ℝ) *
        Matrix.diagonal (fun _ => 0) *
          (0 : Matrix (Fin emptyLattice.rank) (Fin emptyLattice.rank) ℝ).transpose := by
  exact funext fun axis => Fin.elim0 axis

namespace Nondegeneracy

abbrev Params : Type := Σ data : LatticeData,
  Matrix (Fin data.rank) (Fin data.rank) ℂ

abbrev Form (data : LatticeData) :=
  Oscillator data →ₗ⋆[ℂ] Oscillator data →ₗ[ℂ] ℂ

abbrev signature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Params (fun parameter => Form parameter.1)
    (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ form => @decide form.Nondegenerate (Classical.propDecidable _))
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (data : LatticeData)
    (inverse : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (left_inverse : inverse * gramComplex data = 1)
    (right_inverse : gramComplex data * inverse = 1),
    observation.readout () ⟨data, inverse⟩ (fockForm data) = true

theorem exact_source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_nondegenerate)) ↔
      arena.Law actual := by
  classical
  constructor
  · intro source data inverse left_inverse right_inverse
    change decide ((fockForm data).Nondegenerate) = true
    exact decide_eq_true (source data inverse left_inverse right_inverse)
  · intro law data inverse left_inverse right_inverse
    exact of_decide_eq_true (law data inverse left_inverse right_inverse)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := law emptyLattice 0 emptyHG emptyGH
  change false = true at impossible
  cases impossible

private theorem zero_form_degenerate (data : LatticeData) :
    ¬ (0 : Form data).Nondegenerate := by
  intro separation
  have impossible := separation.1 1 (by intro right; simp)
  exact one_ne_zero impossible

theorem dependence : ObservationalDependence signature actual := by
  classical
  intro role
  refine ⟨⟨emptyLattice, 0⟩, 0, fockForm emptyLattice, ?_⟩
  change decide ((0 : Form emptyLattice).Nondegenerate) ≠
    decide ((fockForm emptyLattice).Nondegenerate)
  rw [decide_eq_false (zero_form_degenerate emptyLattice),
    decide_eq_true (fockForm_nondegenerate emptyLattice 0 emptyHG emptyGH)]
  decide

def familyRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_nondegenerate)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp fockForm_nondegenerate, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

end Nondegeneracy
namespace CoordinateFactorization

abbrev Params : Type := Σ data : LatticeData,
  Σ frame : Matrix (Fin data.rank) (Fin data.rank) ℝ,
    Σ diagonal : Fin data.rank → ℝ, Oscillator data

abbrev signature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Params (fun parameter => Oscillator parameter.1)
    (fun _ => ℂ)

def actual : Realization signature :=
  realize signature
    (fun _ parameter right => fockForm parameter.1 parameter.2.2.2 right)
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (data : LatticeData)
    (frame : Matrix (Fin data.rank) (Fin data.rank) ℝ) (diagonal : Fin data.rank → ℝ)
    (factorization : (fun axis other => (data.G axis other : ℝ)) =
      frame * Matrix.diagonal diagonal * frame.transpose) (left right : Oscillator data),
    observation.readout () ⟨data, frame, diagonal, left⟩ right =
      ∑ occupation ∈ (coordinateSubstitution data frame left).support,
        star (coeff occupation (coordinateSubstitution data frame left)) *
          (occupationWeight data diagonal occupation : ℂ) *
            coeff occupation (coordinateSubstitution data frame right)

theorem exact_source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_coordinate_factorization)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := law emptyLattice 0 (fun _ => 0) emptyFactorization 1 1
  change (0 : ℂ) = _ at impossible
  rw [← fockForm_coordinate_factorization emptyLattice 0 (fun _ => 0)
    emptyFactorization 1 1] at impossible
  simpa [fockForm_vacuum_left] using impossible

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨emptyLattice, 0, (fun _ => 0), 1⟩, 0, 1, ?_⟩
  change fockForm emptyLattice 1 0 ≠ fockForm emptyLattice 1 1
  simp [fockForm_vacuum_left]

def familyRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_coordinate_factorization)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp fockForm_coordinate_factorization, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

end CoordinateFactorization

namespace NormCoefficients

abbrev signature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature LatticeData Oscillator (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ data polynomial => fockForm data polynomial polynomial)
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (data : LatticeData) (positive : (gramReal data).PosDef)
    (polynomial : Oscillator data),
    observation.readout () data polynomial =
      (∑ occupation ∈ (coordinateSubstitution data (LDL.lower positive) polynomial).support,
        occupationWeight data (LDL.diagEntries positive) occupation * Complex.normSq
          (coeff occupation (coordinateSubstitution data (LDL.lower positive) polynomial)) : ℝ)

theorem exact_source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_norm_coefficients)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := law emptyLattice emptyPositive 1
  change (0 : ℂ) = _ at impossible
  rw [← fockForm_norm_coefficients emptyLattice emptyPositive 1] at impossible
  simpa [fockForm_vacuum_left] using impossible

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨emptyLattice, 0, 1, ?_⟩
  change fockForm emptyLattice 0 0 ≠ fockForm emptyLattice 1 1
  simp [fockForm_vacuum_left]

def familyRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_norm_coefficients)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp fockForm_norm_coefficients, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

end NormCoefficients
namespace Positivity

abbrev signature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature LatticeData Oscillator (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ data polynomial => (fockForm data polynomial polynomial).re)
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (data : LatticeData) (positive : (gramReal data).PosDef)
    (polynomial : Oscillator data) (nonzero : polynomial ≠ 0),
    0 < observation.readout () data polynomial

theorem exact_source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_positive)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := law emptyLattice emptyPositive 1 one_ne_zero
  exact (lt_irrefl (0 : ℝ)) impossible

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨emptyLattice, 0, 1, ?_⟩
  change (fockForm emptyLattice 0 0).re ≠ (fockForm emptyLattice 1 1).re
  simp [fockForm_vacuum_left]

def familyRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_positive)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp fockForm_positive, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

end Positivity

namespace OrthogonalMonomials

abbrev Params : Type := Σ data : LatticeData, Index data →₀ ℕ

abbrev signature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun parameter => Fin parameter.1.rank → ℝ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature
    (fun _ parameter diagonal => (occupationWeight parameter.1 diagonal parameter.2 : ℂ))
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (data : LatticeData) (positive : (gramReal data).PosDef)
    (left right : Index data →₀ ℕ),
    fockForm data
      (coordinateSubstitution data (LDL.lowerInv positive) (monomial left 1))
      (coordinateSubstitution data (LDL.lowerInv positive) (monomial right 1)) =
      if left = right then observation.readout () ⟨data, left⟩ (LDL.diagEntries positive)
      else 0

theorem exact_source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_orthogonal_monomials)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := law emptyLattice emptyPositive 0 0
  change fockForm emptyLattice
    (coordinateSubstitution emptyLattice (LDL.lowerInv emptyPositive) (monomial 0 1))
    (coordinateSubstitution emptyLattice (LDL.lowerInv emptyPositive) (monomial 0 1)) =
      if (0 : Index emptyLattice →₀ ℕ) = 0 then (0 : ℂ) else 0 at impossible
  rw [fockForm_orthogonal_monomials emptyLattice emptyPositive 0 0] at impossible
  simpa [occupationWeight] using impossible

private def oneLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intro axis other; rfl
  even_diagonal := by intro axis; exact ⟨1, by norm_num⟩

private def oneOccupation : Index oneLattice →₀ ℕ := Finsupp.single (⟨0, by decide⟩, 0) 1

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨oneLattice, oneOccupation⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  change (occupationWeight oneLattice (fun _ => 0) oneOccupation : ℂ) ≠
    (occupationWeight oneLattice (fun _ => 1) oneOccupation : ℂ)
  norm_num [occupationWeight, oneOccupation]

def familyRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_orthogonal_monomials)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp fockForm_orthogonal_monomials, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

end OrthogonalMonomials
namespace Nondegeneracy

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_nondegenerate)
      (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_nondegenerate.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.Nondegeneracy.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeOscillatorFockMetric
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Nondegeneracy

namespace CoordinateFactorization

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_coordinate_factorization)
      (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_coordinate_factorization.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.CoordinateFactorization.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeOscillatorFockMetric
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end CoordinateFactorization

namespace NormCoefficients

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_norm_coefficients)
      (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_norm_coefficients.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.NormCoefficients.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeOscillatorFockMetric
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end NormCoefficients

namespace Positivity

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_positive)
      (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_positive.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.Positivity.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeOscillatorFockMetric
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Positivity

namespace OrthogonalMonomials

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_orthogonal_monomials)
      (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.fockForm_orthogonal_monomials.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric.OrthogonalMonomials.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeOscillatorFockMetric
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end OrthogonalMonomials

end

end Reg.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric
