import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial

/-! Dependent equality readouts for the vacuum coefficients and the finite
lowering flow of the half-current Wick polynomial. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality (LatticeData Index Oscillator)
open _root_.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport (normalOrder)
open _root_.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial
  (word word_coeff eval_word_eq_lowering)
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset (oscillatorLower)
open scoped BigOperators

namespace Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature
  LatticeData Oscillator (fun D => Oscillator D → Prop)

def oscillatorEqual : Realization signature :=
  realize signature (fun _ _ p q => p = q) (fun e => nomatch e)

def oscillatorFalse : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i

private theorem oscillatorEqualDependence : ObservationalDependence signature oscillatorEqual := by
  intro role
  refine ⟨emptyLattice, 0, 1, ?_⟩
  intro equal
  have impossible : (1 : Oscillator emptyLattice) = 0 := Eq.mp (congrFun equal 0) rfl
  exact one_ne_zero impossible

namespace VacuumCoefficient

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (l : List (Index D)) (k : ℕ),
    R.readout () D (PowerSeries.coeff k (normalOrder D l) (1 : Oscillator D))
      ((word D l).coeff k)

private theorem rejectedLaw : ¬ arena.Law oscillatorFalse := by
  intro h
  exact h emptyLattice [] 0

def family : Registration arena (type_of% (@word_coeff)) where
  actual := oscillatorEqual
  bridge := Iff.rfl
  variation := ⟨word_coeff, oscillatorFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law oscillatorEqual oscillatorFalse rejectedLaw
  dependence := oscillatorEqualDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@word_coeff) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial.VacuumCoefficient.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial.VacuumCoefficient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature oscillatorEqual.readout oscillatorEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end VacuumCoefficient

namespace FiniteLowering

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (_hu : IsUnit D.G.det)
      (l : List (Index D)) (θ : ℂ) (N : ℕ) (_hN : (word D l).natDegree < N),
    R.readout () D ((word D l).eval (MvPolynomial.C θ))
      (∑ k ∈ Finset.range N, (θ ^ k / (k.factorial : ℂ)) • (oscillatorLower D ^ k)
        ((l.map (fun x => (MvPolynomial.X x : Oscillator D))).prod))

private theorem rejectedLaw : ¬ arena.Law oscillatorFalse := by
  intro h
  have hu : IsUnit emptyLattice.G.det := by
    change IsUnit (0 : Matrix (Fin 0) (Fin 0) ℤ).det
    simp
  exact h emptyLattice hu [] 0 1 (by simp [word])

def family : Registration arena (type_of% (@eval_word_eq_lowering)) where
  actual := oscillatorEqual
  bridge := Iff.rfl
  variation := ⟨eval_word_eq_lowering, oscillatorFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law oscillatorEqual oscillatorFalse rejectedLaw
  dependence := oscillatorEqualDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eval_word_eq_lowering) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial.FiniteLowering.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial.FiniteLowering.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature oscillatorEqual.readout oscillatorEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FiniteLowering

end Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial
