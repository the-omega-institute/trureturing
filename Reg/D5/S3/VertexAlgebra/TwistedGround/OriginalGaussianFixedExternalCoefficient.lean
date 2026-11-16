import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedExternalCoefficient

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
open NativeAffineExternalCoefficient OriginalGaussianFixedExternalCoefficient
open OriginalGaussianSourceRestriction FactorialFockMetric
open MvPolynomial

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedExternalCoefficient

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


abbrev rowParameter := Unit ⊕ (Σ D : LatticeData, ℕ)
abbrev rowState : rowParameter → Type
  | .inl _ => ℝ
  | .inr p => (Internal p.1 p.2 →₀ ℕ) → ℂ
abbrev rowOutput : rowParameter → Type
  | .inl _ => ℝ → Prop
  | .inr _ => ℂ → Prop
abbrev rowSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature rowParameter rowState rowOutput
def rowActual : Realization rowSignature := realize _
  (fun _ p => match p with
    | .inl _ => fun x y => x ≤ y
    | .inr _ => fun f y => HasSum f y) (fun e => nomatch e)
def rowBad : Realization rowSignature := realize _
  (fun _ p => match p with
    | .inl _ => fun _ _ => False
    | .inr _ => fun _ _ => False) (fun e => nomatch e)
private theorem rowDependence : ObservationalDependence rowSignature rowActual := by
  intro i
  refine ⟨.inl (), 0, 1, ?_⟩
  intro h
  have he : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
  norm_num at he

namespace original_fixed_external_sewing_on_germ
def arena : Arena where
  signature := rowSignature
  Law O := ∀ {X : Type u} [Fintype X] [DecidableEq X]
    (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) (N : ℕ)
    (e : X → External D) (h k : X →₀ ℕ),
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ B : (Internal D N →₀ ℕ) → ℝ, Summable B ∧
      (∀ z, ‖z‖ ≤ r → ∀ d, O.readout () (.inl ())
        ‖fullRowTerm D a N e h k d z‖ (B d)) ∧
      ∀ z, ‖z‖ ≤ r → O.readout () (.inr ⟨D, N⟩)
        (fun d => fullRowTerm D a N e h k d z) (finiteSewn D a e (h.sumElim k) N z)
private theorem bad_fails : ¬ arena.{u}.Law rowBad := by
  intro h
  obtain ⟨r, hr, hr1, B, hB, hb, hs⟩ := @h (ULift.{u} Unit) inferInstance inferInstance hyperbolic hyperbolic_unit 0 0 (fun _ => labels ()) 0 0
  exact hb 0 (by simpa using hr.le) 0
def evidence : Registration arena.{u} (type_of% (@original_fixed_external_sewing_on_germ.{u})) where
  actual := rowActual
  bridge := Iff.rfl
  variation := ⟨fun {X} _ _ D hu a N e h k =>
    original_fixed_external_sewing_on_germ D hu a N e h k, rowBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law rowActual rowBad bad_fails
  dependence := rowDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_fixed_external_sewing_on_germ.{u}) (Realization rowSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedExternalCoefficient.original_fixed_external_sewing_on_germ.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedExternalCoefficient.original_fixed_external_sewing_on_germ.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rowSignature rowActual.readout rowActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_fixed_external_sewing_on_germ

namespace original_finiteSewn_coefficient
def arena : Arena where
  signature := eqSignature
  Law O := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (N : ℕ) (e : X → External D) (h k : X →₀ ℕ) (n : ℕ),
    O.readout () () (coefficient (2 * n) (finiteSewn D a e (h.sumElim k) N)) (∑ᶠ d : {d : Internal D N →₀ ℕ // internalEnergy D N d = n},
        rawFullRowTerm D a N e h k d.val)
private theorem bad_fails : ¬ arena.{u}.Law eqBad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance hyperbolic hyperbolic_unit 0 0 (fun _ => labels ()) 0 0 0
def evidence : Registration arena.{u} (type_of% (@original_finiteSewn_coefficient.{u})) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun {X} _ _ D hu a N e h k n => original_finiteSewn_coefficient D hu a N e h k n, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_finiteSewn_coefficient.{u}) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedExternalCoefficient.original_finiteSewn_coefficient.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedExternalCoefficient.original_finiteSewn_coefficient.evidence
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
end original_finiteSewn_coefficient

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedExternalCoefficient
