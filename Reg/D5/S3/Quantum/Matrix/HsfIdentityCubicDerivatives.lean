import D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit attempts for the actual CFC derivative bridge. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives
open _root_.D5.S3.Quantum.Matrix.HsfQubitCoupledCubic
open _root_.D5.S3.Quantum.Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives
noncomputable section
universe u

private structure MatrixScope where
  index : Type u
  finiteIndex : Fintype index
  decidableIndex : DecidableEq index
attribute [instance] MatrixScope.finiteIndex MatrixScope.decidableIndex

private abbrev derivativeSignature : Signature where
  Params := MatrixScope.{u}
  State s := (ℝ → Matrix s.index s.index ℂ) × Matrix s.index s.index ℂ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def derivativeActual : Realization derivativeSignature :=
  realize derivativeSignature (fun _ _ s => HasDerivAt s.1 s.2.1 s.2.2) (fun e => nomatch e)
private def derivativeRejected : Realization derivativeSignature :=
  realize derivativeSignature (fun _ _ _ => False) (fun e => nomatch e)

private theorem derivativeDependence : ObservationalDependence derivativeSignature.{u} derivativeActual := by
  intro i
  let p : MatrixScope.{u} := ⟨ULift.{u} Unit, inferInstance, inferInstance⟩
  refine ⟨p, ((fun _ => 0), 0, 0), ((fun _ => 0), 1, 0), ?_⟩
  intro h
  have hb : HasDerivAt (fun _ : ℝ => (0 : Matrix p.index p.index ℂ)) 1 0 :=
    Eq.mp h (hasDerivAt_const 0 0)
  have hz := (hasDerivAt_const (0 : ℝ) (0 : Matrix p.index p.index ℂ)).unique hb
  have he := congrArg (fun A : Matrix p.index p.index ℂ => A ⟨()⟩ ⟨()⟩) hz
  norm_num at he

private abbrev germSignature : Signature where
  Params := Unit
  State _ := (ℝ → ℝ) × (ℝ → ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
private def germActual : Realization germSignature :=
  realize germSignature (fun _ _ s => s.1 =ᶠ[𝓝 (0 : ℝ)] s.2) (fun e => nomatch e)
private def germRejected : Realization germSignature :=
  realize germSignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem germDependence : ObservationalDependence germSignature germActual := by
  intro i
  refine ⟨(), ((fun _ => 0), (fun _ => 0)), ((fun _ => 0), (fun _ => 1)), ?_⟩
  intro h
  have hh : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 0] fun _ => 1 := Eq.mp h Filter.EventuallyEq.rfl
  have := hh.eq_of_nhds
  norm_num at this

private abbrev jetSignature : Signature where
  Params := Unit
  State _ := ℝ × ℝ × ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
private def jetActual : Realization jetSignature :=
  realize jetSignature (fun _ _ s => s.1 = s.2.1 ∧ s.2.2.1 = s.2.2.2) (fun e => nomatch e)
private def jetRejected : Realization jetSignature :=
  realize jetSignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem jetDependence : ObservationalDependence jetSignature jetActual := by
  intro i
  exact ⟨(), (0,0,0,0), (1,0,0,0), by simp [jetActual, realize]⟩

private abbrev boundSignature : Signature where
  Params := Unit
  State _ := ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
private def boundActual : Realization boundSignature :=
  realize boundSignature (fun _ _ s => 0 ≤ s.1 ∧ |s.2| ≤ 5*s.1) (fun e => nomatch e)
private def boundRejected : Realization boundSignature :=
  realize boundSignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem boundDependence : ObservationalDependence boundSignature boundActual := by
  intro i
  exact ⟨(), (0,0), (-1,0), by norm_num [boundActual, realize]⟩

namespace CfcDerivative
private abbrev arena : Arena where
  signature := derivativeSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {K : Matrix n n ℂ}
    (hK : K.IsHermitian) (f : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (t : ℝ),
    (∀ i, HasDerivAt (fun s => f s (hK.eigenvalues i)) (g (hK.eigenvalues i)) t) →
    R.readout () ⟨n, inferInstance, inferInstance⟩ ((fun s => cfc (f s) K), cfc g K, t)
private theorem rejected_law : ¬ arena.{u}.Law derivativeRejected := by
  intro h
  exact h (n := ULift.{u} Unit) (K := 0) (by simp : (0 : Matrix _ _ ℂ).IsHermitian)
    (fun _ _ => 0) (fun _ => 0) 0 (fun _ => hasDerivAt_const 0 0)
private theorem sensitivity : Sensitivity arena.{u} derivativeActual := by
  constructor
  · intro i
    refine ⟨derivativeRejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.hasDerivAt_cfc.{u})) where
  actual := derivativeActual.{u}
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.hasDerivAt_cfc.{u}, derivativeRejected.{u}, rejected_law.{u}⟩
  sensitivity := sensitivity.{u}
  dependence := derivativeDependence.{u}

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.hasDerivAt_cfc.{u}) (Realization derivativeSignature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.CfcDerivative.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.CfcDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize derivativeSignature.{u} (fun _ _ s => HasDerivAt s.1 s.2.1 s.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end CfcDerivative

namespace AffineDerivative
private abbrev arena : Arena where
  signature := derivativeSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {K : Matrix n n ℂ}
    (hK : K.IsHermitian) (p t : ℝ),
    (∀ x ∈ spectrum ℝ K, 0 < 1+t*x) →
    R.readout () ⟨n, inferInstance, inferInstance⟩
      ((fun s : ℝ => CFC.rpow (1+s • K) p),
        p • (K*CFC.rpow (1+t • K) (p-1)), t)
private theorem rejected_law : ¬ arena.{u}.Law derivativeRejected := by
  intro h
  exact h (n := ULift.{u} Unit) (K := 0) (by simp : (0 : Matrix _ _ ℂ).IsHermitian) 0 0
    (by intros; norm_num)
private theorem sensitivity : Sensitivity arena.{u} derivativeActual := by
  constructor
  · intro i
    refine ⟨derivativeRejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.hasDerivAt_affine_rpow.{u})) where
  actual := derivativeActual.{u}
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.hasDerivAt_affine_rpow.{u}, derivativeRejected.{u}, rejected_law.{u}⟩
  sensitivity := sensitivity.{u}
  dependence := derivativeDependence.{u}

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.hasDerivAt_affine_rpow.{u}) (Realization derivativeSignature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.AffineDerivative.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.AffineDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize derivativeSignature.{u} (fun _ _ s => HasDerivAt s.1 s.2.1 s.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end AffineDerivative

namespace SandwichGerm
private abbrev arena : Arena where
  signature := germSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (X H K : Matrix n n ℂ), K.IsHermitian →
    R.readout () ()
      ((fun t : ℝ => (Matrix.trace ((CFC.rpow (1+t • K) (-(1 : ℝ)/3) * (X+t • H) *
        CFC.rpow (1+t • K) (-(1 : ℝ)/3))^3)).re),
       (fun t : ℝ => (Matrix.trace (((X+t • H)*CFC.rpow (1+t • K) (-(2 : ℝ)/3))^3)).re))
private theorem rejected_law : ¬ arena.{u}.Law germRejected := by
  intro h
  exact h (n := ULift.{u} Unit) 0 0 0 (by simp : (0 : Matrix _ _ ℂ).IsHermitian)
private theorem sensitivity : Sensitivity arena.{u} germActual := by
  constructor
  · intro i
    refine ⟨germRejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.sandwich_trace_germ.{u})) where
  actual := germActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.sandwich_trace_germ.{u}, germRejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := germDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.sandwich_trace_germ.{u}) (Realization germSignature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.SandwichGerm.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.SandwichGerm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize germSignature (fun _ _ s => s.1 =ᶠ[𝓝 (0 : ℝ)] s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end SandwichGerm

namespace CubicTrace
private abbrev arena : Arena where
  signature := jetSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (B B1 B2 B3 : ℝ → Matrix n n ℂ),
    (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt B (B1 t) t) →
    (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt B1 (B2 t) t) →
    HasDerivAt B2 (B3 0) 0 →
    R.readout () ()
      (iteratedDeriv 2 (fun t : ℝ => (Matrix.trace ((B t)^3)).re) 0,
       (Matrix.trace ((3 : ℝ) • (B2 0*B 0*B 0)+(6 : ℝ) • (B1 0*B1 0*B 0))).re,
       iteratedDeriv 3 (fun t : ℝ => (Matrix.trace ((B t)^3)).re) 0,
       (Matrix.trace ((3 : ℝ) • (B3 0*B 0*B 0)+(9 : ℝ) • (B2 0*B1 0*B 0)+
         (9 : ℝ) • (B2 0*B 0*B1 0)+(6 : ℝ) • (B1 0*B1 0*B1 0))).re)
private theorem rejected_law : ¬ arena.{u}.Law jetRejected := by
  intro h
  exact h (n := ULift.{u} Unit) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (Filter.Eventually.of_forall fun t => hasDerivAt_const t 0)
    (Filter.Eventually.of_forall fun t => hasDerivAt_const t 0) (hasDerivAt_const 0 0)
private theorem sensitivity : Sensitivity arena.{u} jetActual := by
  constructor
  · intro i
    refine ⟨jetRejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.cubic_trace_derivatives.{u})) where
  actual := jetActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.cubic_trace_derivatives.{u}, jetRejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := jetDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.cubic_trace_derivatives.{u}) (Realization jetSignature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.CubicTrace.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.CubicTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize jetSignature (fun _ _ s => s.1 = s.2.1 ∧ s.2.2.1 = s.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end CubicTrace

namespace AffineTrace
private abbrev arena : Arena where
  signature := jetSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (X H K : Matrix n n ℂ), K.IsHermitian → ∀ p : ℝ,
    let L := H+p • (X*K)
    let M := (2*p) • (H*K)+(p*(p-1)) • (X*K^2)
    let N := (3*p*(p-1)) • (H*K^2)+(p*(p-1)*(p-2)) • (X*K^3)
    R.readout () ()
      (iteratedDeriv 2 (fun t : ℝ => (Matrix.trace (((X+t • H)*CFC.rpow (1+t • K) p)^3)).re) 0,
       (Matrix.trace ((3 : ℝ) • (M*X*X)+(6 : ℝ) • (L*L*X))).re,
       iteratedDeriv 3 (fun t : ℝ => (Matrix.trace (((X+t • H)*CFC.rpow (1+t • K) p)^3)).re) 0,
       (Matrix.trace ((3 : ℝ) • (N*X*X)+(9 : ℝ) • (M*L*X)+
         (9 : ℝ) • (M*X*L)+(6 : ℝ) • (L*L*L))).re)
private theorem rejected_law : ¬ arena.{u}.Law jetRejected := by
  intro h
  exact h (n := ULift.{u} Unit) 0 0 0 (by simp : (0 : Matrix _ _ ℂ).IsHermitian) 0
private theorem sensitivity : Sensitivity arena.{u} jetActual := by
  constructor
  · intro i
    refine ⟨jetRejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.affine_power_cubic_derivatives.{u})) where
  actual := jetActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.affine_power_cubic_derivatives.{u}, jetRejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := jetDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.affine_power_cubic_derivatives.{u}) (Realization jetSignature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.AffineTrace.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.AffineTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize jetSignature (fun _ _ s => s.1 = s.2.1 ∧ s.2.2.1 = s.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end AffineTrace

namespace IdentityTrace
private abbrev arena : Arena where
  signature := jetSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (X H K : Matrix n n ℂ), K.IsHermitian →
    let phi := fun t : ℝ => (Matrix.trace ((CFC.rpow (1+t • K) (-(1 : ℝ)/3)*(X+t • H)*
      CFC.rpow (1+t • K) (-(1 : ℝ)/3))^3)).re
    R.readout () () (iteratedDeriv 2 phi 0, 2*HsfQubitMixedCubic.coefficient2 X H K,
      iteratedDeriv 3 phi 0, 6*HsfQubitMixedCubic.coefficient3 X H K)
private theorem rejected_law : ¬ arena.{u}.Law jetRejected := by
  intro h
  exact h (n := ULift.{u} Unit) 0 0 0 (by simp : (0 : Matrix _ _ ℂ).IsHermitian)
private theorem sensitivity : Sensitivity arena.{u} jetActual := by
  constructor
  · intro i
    refine ⟨jetRejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.identity_cubic_trace_derivatives.{u})) where
  actual := jetActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.identity_cubic_trace_derivatives.{u}, jetRejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := jetDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.identity_cubic_trace_derivatives.{u}) (Realization jetSignature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.IdentityTrace.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.IdentityTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize jetSignature (fun _ _ s => s.1 = s.2.1 ∧ s.2.2.1 = s.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end IdentityTrace

namespace QubitCompatibility
private abbrev arena : Arena where
  signature := boundSignature
  Law R := ∀ (a b : ℝ) (H K : Mat), 0 < a → 0 < b → H.IsHermitian → K.IsHermitian →
    (hermitian a b 0+H).PosSemidef → (hermitian a b 0-H).PosSemidef →
    (1+K).PosSemidef → (1-K).PosSemidef →
    let X := hermitian a b 0
    let phi := fun t : ℝ => (Matrix.trace ((CFC.rpow (1+t • K) (-(1 : ℝ)/3)*(X+t • H)*
      CFC.rpow (1+t • K) (-(1 : ℝ)/3))^3)).re
    R.readout () () (iteratedDeriv 2 phi 0, iteratedDeriv 3 phi 0)
private theorem rejected_law : ¬ arena.Law boundRejected := by
  intro h
  have he : hermitian 1 1 0 = (1 : Mat) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermitian]
  exact h 1 1 0 0 (by norm_num) (by norm_num) (by simp : (0 : Matrix _ _ ℂ).IsHermitian) (by simp : (0 : Matrix _ _ ℂ).IsHermitian)
    (by simpa [he] using Matrix.PosSemidef.one (n := Fin 2) (R := ℂ))
    (by simpa [he] using Matrix.PosSemidef.one (n := Fin 2) (R := ℂ))
    (by simpa using Matrix.PosSemidef.one (n := Fin 2) (R := ℂ))
    (by simpa using Matrix.PosSemidef.one (n := Fin 2) (R := ℂ))
private theorem sensitivity : Sensitivity arena boundActual := by
  constructor
  · intro i
    refine ⟨boundRejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.qubit_cubic_compatibility)) where
  actual := boundActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.qubit_cubic_compatibility, boundRejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := boundDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.qubit_cubic_compatibility) (Realization boundSignature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.QubitCompatibility.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.QubitCompatibility.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundSignature (fun _ _ s => 0 ≤ s.1 ∧ |s.2| ≤ 5*s.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end QubitCompatibility

namespace QubitPosdefCompatibility
private abbrev arena : Arena where
  signature := boundSignature
  Law R := ∀ (X H K : Mat), X.PosDef → H.IsHermitian → K.IsHermitian →
    (X+H).PosSemidef → (X-H).PosSemidef →
    (1+K).PosSemidef → (1-K).PosSemidef →
    let phi := fun t : ℝ => (Matrix.trace ((CFC.rpow (1+t • K) (-(1 : ℝ)/3)*(X+t • H)*
      CFC.rpow (1+t • K) (-(1 : ℝ)/3))^3)).re
    R.readout () () (iteratedDeriv 2 phi 0, iteratedDeriv 3 phi 0)
private theorem rejected_law : ¬ arena.Law boundRejected := by
  intro h
  exact h 1 0 0 Matrix.PosDef.one
    (by simp : (0 : Mat).IsHermitian) (by simp : (0 : Mat).IsHermitian)
    (by simpa using Matrix.PosSemidef.one (n := Fin 2) (R := ℂ))
    (by simpa using Matrix.PosSemidef.one (n := Fin 2) (R := ℂ))
    (by simpa using Matrix.PosSemidef.one (n := Fin 2) (R := ℂ))
    (by simpa using Matrix.PosSemidef.one (n := Fin 2) (R := ℂ))
private theorem sensitivity : Sensitivity arena boundActual := by
  constructor
  · intro i
    refine ⟨boundRejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.qubit_posdef_cubic_compatibility)) where
  actual := boundActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.qubit_posdef_cubic_compatibility, boundRejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := boundDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.qubit_posdef_cubic_compatibility) (Realization boundSignature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.QubitPosdefCompatibility.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives.QubitPosdefCompatibility.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundSignature (fun _ _ s => 0 ≤ s.1 ∧ |s.2| ≤ 5*s.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end QubitPosdefCompatibility

end
end Reg.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives
