import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient

noncomputable section
universe u v
open scoped BigOperators Topology Matrix ContDiff
open Filter Metric
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open TwistedGround OriginalChargedRowSource OriginalGaussianExternalBlocks
open OriginalGaussianSourceMeans OriginalGaussianSourceGerm OriginalGaussianSewnAnalytic
open NativeAffineTransport OriginalSourceInverseCoefficient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open OriginalGaussianOccupationCoefficients
open NativeAffineExternalCoefficient
open FactorialFockMetric
open MvPolynomial

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient

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

namespace native_affine_external_jet
def arena : Arena where
  signature := eqSignature
  Law O := ∀ {I : Type u} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (mu : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (l : List I) (N : ℕ) (hN : (jetOccupation l).degree ≤ N),
    O.readout () () (coordinateJet l (fun x => Complex.exp (eval x (affineExponent A mu))) 0 /
        (weight (jetOccupation l) : ℂ)) (OriginalChargedRowSource.affineCoefficient A mu (jetOccupation l))
private theorem bad_fails : ¬ arena.{u}.Law eqBad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance 0 0 (by intros; rfl) [] 0 (by simp [jetOccupation])
def evidence : Registration arena.{u} (type_of% (@native_affine_external_jet.{u})) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun {I} _ _ A mu hs l N hN => native_affine_external_jet A mu hs l N hN, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_affine_external_jet.{u}) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient.native_affine_external_jet.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient.native_affine_external_jet.evidence
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
end native_affine_external_jet

namespace native_affine_external_coefficient
def arena : Arena where
  signature := eqSignature
  Law O := ∀ {I : Type u} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (mu : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (N : ℕ) (hN : d.degree ≤ N),
    O.readout () () (externalCoefficient d (fun x => Complex.exp (eval x (affineExponent A mu)))) (OriginalChargedRowSource.affineCoefficient A mu d)
private theorem bad_fails : ¬ arena.{u}.Law eqBad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance 0 0 (by intros; rfl) 0 0 (by simp)
def evidence : Registration arena.{u} (type_of% (@native_affine_external_coefficient.{u})) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun {I} _ _ A mu hs d N hN => native_affine_external_coefficient A mu hs d N hN, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_affine_external_coefficient.{u}) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient.native_affine_external_coefficient.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient.native_affine_external_coefficient.evidence
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
end native_affine_external_coefficient

namespace native_mixed_external_coefficient
def arena : Arena where
  signature := eqSignature
  Law O := ∀ {I : Type u} [Fintype I] [DecidableEq I] {J : Type v} [Fintype J] [DecidableEq J] (C : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (m : I ⊕ J → ℂ) (hs : ∀ i j, C i j = C j i) (d : I →₀ ℕ) (h : J →₀ ℕ),
    O.readout () () (externalCoefficient h (fun x => Complex.exp (externalExponent C m x) *
      OriginalChargedRowSource.affineCoefficient (C.submatrix Sum.inl Sum.inl)
        (mixedMean C m x) d)) (OriginalChargedRowSource.affineCoefficient C m (d.sumElim h))
private theorem bad_fails : ¬ arena.{u,v}.Law eqBad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance (ULift.{v} Unit) inferInstance inferInstance 0 0 (by intros; rfl) 0 0
def evidence : Registration arena.{u,v} (type_of% (@native_mixed_external_coefficient.{u,v})) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun {I} _ _ J _ _ C m hs d h => native_mixed_external_coefficient C m hs d h, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u,v}.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_mixed_external_coefficient.{u,v}) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient.native_mixed_external_coefficient.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient.native_mixed_external_coefficient.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨evidence.{u,v}⟩
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
end native_mixed_external_coefficient

namespace externalPair_affine
def arena : Arena where
  signature := eqSignature
  Law O := ∀ {I : Type u} [Fintype I] [DecidableEq I] {J : Type v} [Fintype J] [DecidableEq J] (C : Matrix (I ⊕ J) (I ⊕ J) ℂ) (m : I ⊕ J → ℂ)
    (hs : ∀ i j, C i j = C j i) (h : I →₀ ℕ) (k : J →₀ ℕ) (c : ℂ),
    O.readout () () (externalPairCoefficient h k (fun x y => c * Complex.exp (eval (Sum.elim x y) (affineExponent C m)))) (c * OriginalChargedRowSource.affineCoefficient C m (h.sumElim k))
private theorem bad_fails : ¬ arena.{u,v}.Law eqBad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance (ULift.{v} Unit) inferInstance inferInstance 0 0 (by intros; rfl) 0 0 1
def evidence : Registration arena.{u,v} (type_of% (@externalPair_affine.{u,v})) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun {I} _ _ J _ _ C m hs h k c => externalPair_affine C m hs h k c, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u,v}.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalPair_affine.{u,v}) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient.externalPair_affine.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient.externalPair_affine.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨evidence.{u,v}⟩
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
end externalPair_affine


end Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient
