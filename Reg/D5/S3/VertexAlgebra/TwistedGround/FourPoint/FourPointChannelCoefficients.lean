import D5.S3.VertexAlgebra.TwistedGround.FourPoint.FourPointChannelCoefficients
import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

noncomputable section
open Filter
open scoped Topology
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization.SignQuotient
open TwistedGround.FourPoint.FourPointChannelCoefficients
open TwistedGround.FourPoint.OriginalFourMChargeGerm (diagonalSewn)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexNotEqual complexEqualDependence)
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.FourPointChannelCoefficients

def arena : Arena where
  signature := complexSignature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
      (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (H K : ℕ)
      (s : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D),
    let U := actualDiagonalNumerator D hD H K s P Q R S a
    let f := diagonalSewn D H K (s - H - K + 1) P Q R S a
    IsDiagonalNumerator D hu H K s P Q R S a U ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), readout.readout () () (U (-(z ^ 2))) ((f z + f (-z)) / 2)

private theorem inequality_fails : ¬ arena.Law complexNotEqual := by
  intro h
  obtain ⟨D, _, _, hu, hD, _⟩ :=
    _root_.D5.S3.Arith.Lattices.Golay.RealLeech.exists_positive_even_unimodular_gram
  have he := (actualDiagonalNumerator_spec D hu hD 0 0 0 0 0 0 0 0).2
  have hn := (h D hu hD 0 0 0 0 0 0 0 0).2
  have hf : ∀ᶠ _ in 𝓝 (0 : ℂ), False := (he.and hn).mono fun _ hboth ↦ hboth.2 hboth.1
  exact (NeBot.ne inferInstance) (eventually_false_iff_eq_bot.mp hf)

def family : Registration arena (type_of% @actualDiagonalNumerator_spec) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@actualDiagonalNumerator_spec, complexNotEqual, inequality_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexNotEqual inequality_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actualDiagonalNumerator_spec) (Realization complexSignature) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.FourPoint.FourPointChannelCoefficients.actualDiagonalNumerator_spec
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.FourPointChannelCoefficients.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.FourPointChannelCoefficients
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.FourPointChannelCoefficients
