import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarRadial

/-! A dependent observation of the complete actual radial source telescope. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticeSectorScalarNumerator LatticeSectorScalarRadial LatticeSugawaraCurrents SupportedChannelSeries
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords SupportedFieldWords.ActualFieldWordAdapter
open UniformGradedLocalCorrelator CollisionAbsoluteEvaluation.Labelled
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators VertexOperator
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarRadial

abbrev signature : Signature where
  Params := Unit
  State _ := MvPowerSeries (Fin 2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := MvPowerSeries (Fin 2) ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have bad : (1 : MvPowerSeries (Fin 2) ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero bad

abbrev arena : Arena where
  signature := signature
  Law a := ∀ (D : LatticeData) (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (α β : Charge D) (u : Sector D α) (v : Sector D β),
    ∃ N : ℕ, ∀ (γ : Charge D) (w : Sector D γ), ∃ A B : ℕ,
      ∃ P : MvPowerSeries (Fin 2) (Oscillator D),
      ∀ p : Oscillator D, ∃ R : MvPolynomial (Fin 2) ℂ,
        a.readout () () (R : MvPowerSeries (Fin 2) ℂ) (mapSeries (readout D p) P) ∧
        R.totalDegree ≤ (degreeBound D α β γ A B N p).toNat ∧
        let C := ![LatticeAllStateField.Y D (inclusion D α u),
          LatticeAllStateField.Y D (inclusion D β v)]
        let phi := (readout D p).comp (projection D (α + (β + γ)))
        let L := AddMonoidAlgebra.single ![-(A : ℤ), -(B : ℤ)] (1 : ℂ) *
          MvPolynomial.aeval (fun i : Fin 2 => variablePolynomial i) R
        let Q : CommonRational ℂ 2 := algebraMap _ _ L /
          algebraMap _ _ (pairPolynomial (0 : Fin 2) 1 ^ N)
        scalarWordCarrier 2 C (1 : Equiv.Perm (Fin 2)) (inclusion D γ w) phi =
          orderedRationalFor ℂ 2 1 Q ∧
        scalarWordCarrier 2 C (Equiv.swap (0 : Fin 2) 1) (inclusion D γ w) phi =
          orderedRationalFor ℂ 2 (Equiv.swap 0 1) Q ∧
        ∀ (x y : ℂ), x ≠ 0 → y ≠ 0 →
          (‖y‖ < ‖x‖ →
            Summable (fun e : Fin 2 → ℤ =>
              ‖readout D p (product D α β γ u v w (e 0) (e 1)) * x ^ e 0 * y ^ e 1‖) ∧
            HasSum (fun e : Fin 2 → ℤ =>
              readout D p (product D α β γ u v w (e 0) (e 1)) * x ^ e 0 * y ^ e 1)
              (MvPolynomial.eval ![x, y] R / (x ^ A * y ^ B * (x - y) ^ N)) ∧
            (∑' e : Fin 2 → ℤ,
              ‖readout D p (product D α β γ u v w (e 0) (e 1)) * x ^ e 0 * y ^ e 1‖) ≤
              laurentMajorant L ![x, y] * |‖x‖ - ‖y‖|⁻¹ ^ N) ∧
          (‖x‖ < ‖y‖ →
            Summable (fun e : Fin 2 → ℤ =>
              ‖readout D p (reverseProduct D α β γ u v w (e 0) (e 1)) * x ^ e 0 * y ^ e 1‖) ∧
            HasSum (fun e : Fin 2 → ℤ =>
              readout D p (reverseProduct D α β γ u v w (e 0) (e 1)) * x ^ e 0 * y ^ e 1)
              (MvPolynomial.eval ![x, y] R / (x ^ A * y ^ B * (x - y) ^ N)) ∧
            (∑' e : Fin 2 → ℤ,
              ‖readout D p (reverseProduct D α β γ u v w (e 0) (e 1)) * x ^ e 0 * y ^ e 1‖) ≤
              laurentMajorant L ![x, y] * |‖x‖ - ‖y‖|⁻¹ ^ N)

private def D0 : LatticeData :=
  ⟨0, 0, by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i⟩
private theorem inverse_left : (0 : Matrix (Fin D0.rank) (Fin D0.rank) ℂ) * gramComplex D0 = 1 := by
  ext i
  exact Fin.elim0 i
private theorem inverse_right : gramComplex D0 * (0 : Matrix (Fin D0.rank) (Fin D0.rank) ℂ) = 1 := by
  ext i
  exact Fin.elim0 i

private theorem bad : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N, rest⟩ := h D0 0 inverse_left inverse_right 0 0 0 0
  obtain ⟨A, B, P, tests⟩ := rest 0 0
  obtain ⟨R, hR⟩ := tests 0
  exact hR.1

def family : Registration arena (type_of% (@ordinary_actual_scalar_radial_rationality)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ordinary_actual_scalar_radial_rationality, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := dependence

def radialAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ordinary_actual_scalar_radial_rationality) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarRadial.radialUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarRadial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarRadial
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "body", "body", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarRadial
