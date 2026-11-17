import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianOccupationCoefficients

noncomputable section
universe u
open scoped BigOperators Topology Matrix
open Filter Metric
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open TwistedGround OriginalChargedRowSource OriginalGaussianExternalBlocks
open OriginalGaussianSourceMeans OriginalGaussianSourceGerm OriginalGaussianSewnAnalytic
open NativeAffineTransport OriginalSourceInverseCoefficient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open OriginalGaussianOccupationCoefficients

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianOccupationCoefficients

private abbrev hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0, rfl⟩
private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have h : hyperbolic.G.det = -1 := by decide
  rw [h]
  exact isUnit_neg_one
private def labels : Unit → External hyperbolic := fun _ => (false, (0, 0))

abbrev eqSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)
def eqActual : Realization eqSignature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def eqBad : Realization eqSignature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem eqDependence : ObservationalDependence eqSignature eqActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he




namespace original_finite_mixed_exponent_collect
def arena : Arena where
  signature := eqSignature
  Law A := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData) (a : Charge D)
    (N : ℕ) (e : X → External D) (z : ℂ) (x y : X → ℂ)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      ((leftRow D N e z).submatrix Sum.inl Sum.inl)‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      ((rightRow D N e z).submatrix Sum.inl Sum.inl)‖ < 1),
    A.readout () () (finiteMixedExponent D a N e (z, x, y)) (effectiveConstant D a N e z +
      (1 / 2 : ℂ) * ∑ i, ∑ j,
        originalEffectiveKernel D N e z i j * (Sum.elim x y i) * (Sum.elim x y j) +
      ∑ i, effectiveMean D a N e z i * Sum.elim x y i)
private theorem bad_fails : ¬ arena.{u}.Law eqBad := by
  intro h
  obtain ⟨r, hr, hr1, hc⟩ := original_rows_contract_on_germ hyperbolic 0 labels
  have he := hc 0 (by simpa using hr.le)
  exact @h (ULift.{u} Unit) inferInstance inferInstance hyperbolic 0 0 (fun _ => labels ()) 0 0 0 he.1 he.2.1
def evidence : Registration arena.{u} (type_of% (@original_finite_mixed_exponent_collect.{u})) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun {X} _ _ D a N e z x y hA hB => original_finite_mixed_exponent_collect D a N e z x y hA hB, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_finite_mixed_exponent_collect.{u}) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianOccupationCoefficients.original_finite_mixed_exponent_collect.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianOccupationCoefficients.original_finite_mixed_exponent_collect.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_finite_mixed_exponent_collect

namespace original_finite_sewing_energy_coefficient
def arena : Arena where
  signature := eqSignature
  Law A := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D) (N : ℕ) (e : X → External D)
    (x y : X → ℂ) (hx : ∀ j, ‖x j‖ ≤ 1) (hy : ∀ j, ‖y j‖ ≤ 1) (n : ℕ),
    A.readout () () (coefficient (2 * n) (fun z =>
      Complex.exp (-(D.rank : ℂ) / 2 * OriginalGaussianDeterminant.finiteLog N z) *
      Complex.exp (effectiveConstant D a N e z) *
      Complex.exp ((1 / 2 : ℂ) * ∑ i, ∑ j,
        originalEffectiveKernel D N e z i j * Sum.elim x y i * Sum.elim x y j +
        ∑ i, effectiveMean D a N e z i * Sum.elim x y i)))
      (∑ᶠ d : Internal D N →₀ ℕ,
        if internalEnergy D N d = n then rawOccupationTerm D a N e d x y else 0)
private theorem bad_fails : ¬ arena.{u}.Law eqBad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance hyperbolic hyperbolic_unit 0 0 (fun _ => labels ()) 0 0 (by simp) (by simp) 0
def evidence : Registration arena.{u} (type_of% (@original_finite_sewing_energy_coefficient.{u})) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun {X} _ _ D hu a N e x y hx hy n => original_finite_sewing_energy_coefficient D hu a N e x y hx hy n, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_finite_sewing_energy_coefficient.{u}) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianOccupationCoefficients.original_finite_sewing_energy_coefficient.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianOccupationCoefficients.original_finite_sewing_energy_coefficient.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_finite_sewing_energy_coefficient

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianOccupationCoefficients
