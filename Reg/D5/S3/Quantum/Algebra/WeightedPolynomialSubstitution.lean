import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution
import Mathlib.Algebra.Ring.ULift
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
open Classical
namespace Reg.D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution
noncomputable section
open _root_.D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u v z

private abbrev single (P : Type u) (X : P → Type v) (Y : P → Type z) : Signature where
  Params := P
  State := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := Y
  Anchor := Empty
  finiteAnchor := inferInstance

private theorem sensitive {P : Type u} {X : P → Type v} {Y : P → Type z}
    (law : Realization (single P X Y) → Prop)
    (actual bad : Realization (single P X Y)) (hbad : ¬ law bad) :
    Sensitivity ⟨single P X Y, law⟩ actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, hbad⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

private theorem not_weight_one {τ R : Type*} [CommSemiring R] [Nontrivial R]
    (w : τ → ℕ) : ¬ HasTotalWeight w (1 : Polynomial (MvPolynomial τ R)) 1 := by
  intro h
  have h01 : (0 : ℕ) = 1 := by simpa using h 0 0 (by simp)
  exact Nat.zero_ne_one h01

private theorem not_signed_one {τ R : Type*} [CommSemiring R] [Nontrivial R]
    (w : τ → ℕ) :
    ¬ MvPolynomial.IsWeightedHomogeneous (fun x => (w x : ℤ)) (1 : MvPolynomial τ R) 1 := by
  intro h
  have h01 : (0 : ℤ) = 1 := by simpa using h (d := 0) (by simp)
  exact zero_ne_one h01

namespace Constant
structure Parameters where
  τ : Type u
  R : Type v
  inst : CommSemiring R
  w : τ → ℕ
  N : ℕ

attribute [instance] Parameters.inst
abbrev signature : Signature := single Parameters.{u,v} (fun p => MvPolynomial p.τ p.R) (fun p => Polynomial (MvPolynomial p.τ p.R))
def actual : Realization signature.{u,v} := realize signature.{u,v} (fun _ p x => Polynomial.C x) (fun e => nomatch e)
def rejected : Realization signature.{u,v} := realize signature.{u,v} (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {τ : Type u} {R : Type v} [CommSemiring R] {w : τ → ℕ}
      {N : ℕ} {p : MvPolynomial τ R}, MvPolynomial.IsWeightedHomogeneous w p N →
      HasTotalWeight w (r.readout () ⟨τ,R,inferInstance,w,N⟩ p) N
theorem source_bridge : (type_of% (@HasTotalWeight.C.{u,v})) ↔ arena.{u,v}.Law actual.{u,v} := Iff.rfl
private theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u,v} := by
  intro h
  exact not_weight_one (fun _ : ULift.{u} Unit => 1)
    (h (τ := ULift.{u} Unit) (R := ULift.{v} ℕ) (w := fun _ => 1)
      (p := 0) (N := 1) (MvPolynomial.isWeightedHomogeneous_zero _ _ _))
private theorem dependence : ObservationalDependence signature.{u,v} actual.{u,v} := by
  intro role
  refine ⟨⟨ULift.{u} Unit,ULift.{v} ℕ,inferInstance,fun _ => 1,0⟩,0,1,?_⟩
  simp [actual, realize]

def familyRegistration : Registration arena.{u,v} (type_of% (@HasTotalWeight.C.{u,v})) where
  actual := actual.{u,v}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@HasTotalWeight.C.{u,v}), rejected.{u,v}, rejected_law⟩
  sensitivity := sensitive arena.{u,v}.Law actual.{u,v} rejected.{u,v} rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@HasTotalWeight.C.{u,v}) (type_of% (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor)) Type Unit where
  unitName := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.HasTotalWeight.C.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.Constant.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution
    definition := none
    coordinates := #[0,1,3,4]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
end Constant

namespace CoverPower
structure Parameters where
  τ : Type u
  R : Type v
  inst : CommSemiring R
  w : τ → ℕ

attribute [instance] Parameters.inst
abbrev signature : Signature := single Parameters.{u,v} (fun p => ℕ) (fun p => Polynomial (MvPolynomial p.τ p.R))
def actual : Realization signature.{u,v} := realize signature.{u,v} (fun _ p x => Polynomial.X ^ x) (fun e => nomatch e)
def rejected : Realization signature.{u,v} := realize signature.{u,v} (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {τ : Type u} {R : Type v} [CommSemiring R] (w : τ → ℕ) (k : ℕ),
      HasTotalWeight w (r.readout () ⟨τ,R,inferInstance,w⟩ k) k
theorem source_bridge : (type_of% (@HasTotalWeight.X_pow.{u,v})) ↔ arena.{u,v}.Law actual.{u,v} := Iff.rfl
private theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u,v} := by
  intro h
  exact not_weight_one (fun _ : ULift.{u} Unit => 1)
    (h (τ := ULift.{u} Unit) (R := ULift.{v} ℕ) (fun _ => 1) 1)
private theorem dependence : ObservationalDependence signature.{u,v} actual.{u,v} := by
  intro role
  refine ⟨⟨ULift.{u} Unit,ULift.{v} ℕ,inferInstance,fun _ => 1⟩,0,1,?_⟩
  change (Polynomial.X ^ 0 : Polynomial (MvPolynomial (ULift.{u} Unit) (ULift.{v} ℕ))) ≠ Polynomial.X ^ 1
  intro h
  have hh := congrArg (fun P => Polynomial.coeff P 0) h
  simpa using hh

def familyRegistration : Registration arena.{u,v} (type_of% (@HasTotalWeight.X_pow.{u,v})) where
  actual := actual.{u,v}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@HasTotalWeight.X_pow.{u,v}), rejected.{u,v}, rejected_law⟩
  sensitivity := sensitive arena.{u,v}.Law actual.{u,v} rejected.{u,v} rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@HasTotalWeight.X_pow.{u,v}) (type_of% (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor)) Type Unit where
  unitName := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.HasTotalWeight.X_pow.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.CoverPower.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution
    definition := none
    coordinates := #[0,1,3]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
end CoverPower

namespace Product
structure Parameters where
  τ : Type u
  R : Type v
  inst : CommSemiring R
  w : τ → ℕ
  N : ℕ
  M : ℕ
  Q : Polynomial (MvPolynomial τ R)

attribute [instance] Parameters.inst
abbrev signature : Signature := single Parameters.{u,v} (fun p => Polynomial (MvPolynomial p.τ p.R)) (fun p => Polynomial (MvPolynomial p.τ p.R))
def actual : Realization signature.{u,v} := realize signature.{u,v} (fun _ p x => x * p.Q) (fun e => nomatch e)
def rejected : Realization signature.{u,v} := realize signature.{u,v} (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {τ : Type u} {R : Type v} [CommSemiring R] {w : τ → ℕ}
      {P Q : Polynomial (MvPolynomial τ R)} {N M : ℕ},
      HasTotalWeight w P N → HasTotalWeight w Q M →
      HasTotalWeight w (r.readout () ⟨τ,R,inferInstance,w,N,M,Q⟩ P) (N+M)
theorem source_bridge : (type_of% (@HasTotalWeight.mul.{u,v})) ↔ arena.{u,v}.Law actual.{u,v} := Iff.rfl
private theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u,v} := by
  intro h
  apply not_weight_one (R := ULift.{v} ℕ) (fun _ : ULift.{u} Unit => 1)
  exact h (τ := ULift.{u} Unit) (R := ULift.{v} ℕ) (w := fun _ => 1)
    (P := 0) (Q := 1) (N := 1) (M := 0)
    (by intro r d hd; exact (hd (by simp)).elim)
    (by simpa using HasTotalWeight.C (MvPolynomial.isWeightedHomogeneous_one (ULift.{v} ℕ) (fun _ : ULift.{u} Unit => 1)))
private theorem dependence : ObservationalDependence signature.{u,v} actual.{u,v} := by
  intro role
  refine ⟨⟨ULift.{u} Unit,ULift.{v} ℕ,inferInstance,fun _ => 1,0,0,1⟩,0,1,?_⟩
  simp [actual, realize]

def familyRegistration : Registration arena.{u,v} (type_of% (@HasTotalWeight.mul.{u,v})) where
  actual := actual.{u,v}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@HasTotalWeight.mul.{u,v}), rejected.{u,v}, rejected_law⟩
  sensitivity := sensitive arena.{u,v}.Law actual.{u,v} rejected.{u,v} rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@HasTotalWeight.mul.{u,v}) (type_of% (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor)) Type Unit where
  unitName := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.HasTotalWeight.mul.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.Product.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution
    definition := none
    coordinates := #[0,1,3,5,6,7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
end Product

namespace Difference
structure Parameters where
  τ : Type u
  R : Type v
  inst : CommRing R
  w : τ → ℕ
  N : ℕ
  Q : Polynomial (MvPolynomial τ R)

attribute [instance] Parameters.inst
abbrev signature : Signature := single Parameters.{u,v} (fun p => Polynomial (MvPolynomial p.τ p.R)) (fun p => Polynomial (MvPolynomial p.τ p.R))
def actual : Realization signature.{u,v} := realize signature.{u,v} (fun _ p x => x - p.Q) (fun e => nomatch e)
def rejected : Realization signature.{u,v} := realize signature.{u,v} (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {τ : Type u} {R : Type v} [CommRing R] {w : τ → ℕ}
      {P Q : Polynomial (MvPolynomial τ R)} {N : ℕ},
      HasTotalWeight w P N → HasTotalWeight w Q N →
      HasTotalWeight w (r.readout () ⟨τ,R,inferInstance,w,N,Q⟩ P) N
theorem source_bridge : (type_of% (@HasTotalWeight.sub.{u,v})) ↔ arena.{u,v}.Law actual.{u,v} := Iff.rfl
private theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u,v} := by
  intro h
  apply not_weight_one (R := ULift.{v} ℤ) (fun _ : ULift.{u} Unit => 1)
  exact h (τ := ULift.{u} Unit) (R := ULift.{v} ℤ) (w := fun _ => 1)
    (P := 0) (Q := 0) (N := 1)
    (by intro r d hd; exact (hd (by simp)).elim)
    (by intro r d hd; exact (hd (by simp)).elim)
private theorem dependence : ObservationalDependence signature.{u,v} actual.{u,v} := by
  intro role
  refine ⟨⟨ULift.{u} Unit,ULift.{v} ℤ,inferInstance,fun _ => 1,0,0⟩,0,1,?_⟩
  simp [actual, realize]

def familyRegistration : Registration arena.{u,v} (type_of% (@HasTotalWeight.sub.{u,v})) where
  actual := actual.{u,v}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@HasTotalWeight.sub.{u,v}), rejected.{u,v}, rejected_law⟩
  sensitivity := sensitive arena.{u,v}.Law actual.{u,v} rejected.{u,v} rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@HasTotalWeight.sub.{u,v}) (type_of% (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor)) Type Unit where
  unitName := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.HasTotalWeight.sub.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.Difference.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution
    definition := none
    coordinates := #[0,1,3,5,6]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
end Difference

namespace Coefficient
structure Parameters where
  τ : Type u
  R : Type v
  inst : CommSemiring R
  w : τ → ℕ
  N : ℕ
  r : ℕ

attribute [instance] Parameters.inst
abbrev signature : Signature := single Parameters.{u,v} (fun p => Polynomial (MvPolynomial p.τ p.R)) (fun p => MvPolynomial p.τ p.R)
def actual : Realization signature.{u,v} := realize signature.{u,v} (fun _ p x => x.coeff p.r) (fun e => nomatch e)
def rejected : Realization signature.{u,v} := realize signature.{u,v} (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {τ : Type u} {R : Type v} [CommSemiring R] {w : τ → ℕ}
      {P : Polynomial (MvPolynomial τ R)} {N : ℕ}, HasTotalWeight w P N → ∀ k : ℕ,
      MvPolynomial.IsWeightedHomogeneous (fun x => (w x : ℤ))
        (r.readout () ⟨τ,R,inferInstance,w,N,k⟩ P) ((N:ℤ)-k)
theorem source_bridge : (type_of% (@HasTotalWeight.coeff_homogeneous_int.{u,v})) ↔ arena.{u,v}.Law actual.{u,v} := Iff.rfl
private theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u,v} := by
  intro h
  apply not_signed_one (R := ULift.{v} ℕ) (fun _ : ULift.{u} Unit => 1)
  exact h (τ := ULift.{u} Unit) (R := ULift.{v} ℕ) (w := fun _ => 1)
    (P := 0) (N := 1) (by intro r d hd; exact (hd (by simp)).elim) 0
private theorem dependence : ObservationalDependence signature.{u,v} actual.{u,v} := by
  intro role
  refine ⟨⟨ULift.{u} Unit,ULift.{v} ℕ,inferInstance,fun _ => 1,0,0⟩,0,1,?_⟩
  simp [actual, realize]

def familyRegistration : Registration arena.{u,v} (type_of% (@HasTotalWeight.coeff_homogeneous_int.{u,v})) where
  actual := actual.{u,v}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@HasTotalWeight.coeff_homogeneous_int.{u,v}), rejected.{u,v}, rejected_law⟩
  sensitivity := sensitive arena.{u,v}.Law actual.{u,v} rejected.{u,v} rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@HasTotalWeight.coeff_homogeneous_int.{u,v}) (type_of% (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor)) Type Unit where
  unitName := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.HasTotalWeight.coeff_homogeneous_int.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.Coefficient.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution
    definition := none
    coordinates := #[0,1,3,5,7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
end Coefficient

namespace WeightCast
abbrev signature : Signature := single (Σ τ : Type u, τ → ℕ)
  (fun p => p.1 →₀ ℕ) (fun _ => ℤ)
def actual : Realization signature.{u} := realize signature.{u}
  (fun _ p d => Finsupp.weight (fun x => (p.2 x : ℤ)) d) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ p d => Finsupp.weight (fun x => (p.2 x : ℤ)) d + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {τ : Type u} (w : τ → ℕ) (d : τ →₀ ℕ),
    r.readout () ⟨τ,w⟩ d = (Finsupp.weight w d : ℤ)
theorem source_bridge : (type_of% (@weight_intCast.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := h (τ := ULift.{u} Unit) (fun _ => 1) 0
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro role
  refine ⟨⟨ULift.{u} Unit,fun _ => 1⟩,0,Finsupp.single (ULift.up ()) 1,?_⟩
  simp [actual, realize, Finsupp.weight_apply]

def familyRegistration : Registration arena.{u} (type_of% (@weight_intCast.{u})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@weight_intCast.{u}), rejected.{u}, rejected_law⟩
  sensitivity := sensitive arena.{u}.Law actual.{u} rejected.{u} rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weight_intCast.{u}) (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor)) Type Unit where
  unitName := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.weight_intCast.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.WeightCast.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.{u}.readout actual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
end WeightCast

namespace SignedCast
structure Parameters where
  τ : Type u
  R : Type v
  inst : CommSemiring R
  w : τ → ℕ
  N : ℕ
attribute [instance] Parameters.inst
abbrev signature : Signature := single Parameters.{u,v} (fun p => MvPolynomial p.τ p.R) (fun _ => Bool)
def actual : Realization signature.{u,v} := realize signature.{u,v}
  (fun _ p x => decide (MvPolynomial.IsWeightedHomogeneous (fun i => (p.w i : ℤ)) x (p.N : ℤ)))
  (fun e => nomatch e)
def rejected : Realization signature.{u,v} := realize signature.{u,v} (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {τ : Type u} {R : Type v} [CommSemiring R] {w : τ → ℕ}
    {p : MvPolynomial τ R} {N : ℕ}, MvPolynomial.IsWeightedHomogeneous w p N →
      r.readout () ⟨τ,R,inferInstance,w,N⟩ p = true
theorem source_bridge : (type_of% (@homogeneous_intCast.{u,v})) ↔ arena.{u,v}.Law actual.{u,v} := by
  simp only [arena, actual, realize, decide_eq_true_eq]
private theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u,v} := by
  intro h
  have hh := h (τ := ULift.{u} Unit) (R := ULift.{v} ℕ) (w := fun _ => 1)
    (p := 0) (N := 1) (MvPolynomial.isWeightedHomogeneous_zero _ _ _)
  exact Bool.false_ne_true hh
private theorem dependence : ObservationalDependence signature.{u,v} actual.{u,v} := by
  intro role
  refine ⟨⟨ULift.{u} Unit,ULift.{v} ℕ,inferInstance,fun _ => 1,1⟩,0,1,?_⟩
  change decide (MvPolynomial.IsWeightedHomogeneous _ (0 : MvPolynomial (ULift.{u} Unit) (ULift.{v} ℕ)) (1:ℤ)) ≠
    decide (MvPolynomial.IsWeightedHomogeneous _ (1 : MvPolynomial (ULift.{u} Unit) (ULift.{v} ℕ)) (1:ℤ))
  rw [decide_eq_true (MvPolynomial.isWeightedHomogeneous_zero _ _ _),
    decide_eq_false (not_signed_one (fun _ : ULift.{u} Unit => 1))]
  decide

def familyRegistration : Registration arena.{u,v} (type_of% (@homogeneous_intCast.{u,v})) where
  actual := actual.{u,v}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@homogeneous_intCast.{u,v}), rejected.{u,v}, rejected_law⟩
  sensitivity := sensitive arena.{u,v}.Law actual.{u,v} rejected.{u,v} rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@homogeneous_intCast.{u,v}) (type_of% (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor)) Type Unit where
  unitName := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.homogeneous_intCast.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.SignedCast.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} actual.{u,v}.readout actual.{u,v}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution
    definition := none
    coordinates := #[0,1,3,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
end SignedCast

namespace Evaluation
structure Parameters where
  σ : Type u
  τ : Type v
  R : Type z
  inst : CommSemiring R
  v : σ → ℕ
  w : τ → ℕ
  f : σ → Polynomial (MvPolynomial τ R)
  N : ℕ
attribute [instance] Parameters.inst
abbrev signature : Signature := single Parameters.{u,v,z} (fun p => MvPolynomial p.σ p.R)
  (fun p => Polynomial (MvPolynomial p.τ p.R))
def actual : Realization signature.{u,v,z} := realize signature.{u,v,z}
  (fun _ p x => MvPolynomial.eval₂ (algebraMap p.R (Polynomial (MvPolynomial p.τ p.R))) p.f x)
  (fun e => nomatch e)
def rejected : Realization signature.{u,v,z} := realize signature.{u,v,z} (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u,v,z}
  Law r := ∀ {σ : Type u} {τ : Type v} {R : Type z} [CommSemiring R]
    (v : σ → ℕ) (w : τ → ℕ) (f : σ → Polynomial (MvPolynomial τ R)),
    (∀ i, HasTotalWeight w (f i) (v i)) → ∀ (p : MvPolynomial σ R) (N : ℕ),
    MvPolynomial.IsWeightedHomogeneous v p N →
    HasTotalWeight w (r.readout () ⟨σ,τ,R,inferInstance,v,w,f,N⟩ p) N
theorem source_bridge : (type_of% (@eval2_totalWeight.{u,v,z})) ↔ arena.{u,v,z}.Law actual.{u,v,z} := Iff.rfl
private theorem rejected_law : ¬ arena.{u,v,z}.Law rejected.{u,v,z} := by
  intro h
  apply not_weight_one (R := ULift.{z} ℕ) (fun _ : ULift.{v} Unit => 1)
  exact h (σ := ULift.{u} Unit) (τ := ULift.{v} Unit) (R := ULift.{z} ℕ)
    (fun _ => 1) (fun _ => 1) (fun _ => 0)
    (by intro i r d hd; exact (hd (by simp)).elim) 0 1
    (MvPolynomial.isWeightedHomogeneous_zero _ _ _)
private theorem dependence : ObservationalDependence signature.{u,v,z} actual.{u,v,z} := by
  intro role
  refine ⟨⟨ULift.{u} Unit,ULift.{v} Unit,ULift.{z} ℕ,inferInstance,fun _ => 1,fun _ => 1,fun _ => 0,0⟩,0,1,?_⟩
  simp [actual, realize]

def familyRegistration : Registration arena.{u,v,z} (type_of% (@eval2_totalWeight.{u,v,z})) where
  actual := actual.{u,v,z}
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@eval2_totalWeight.{u,v,z}), rejected.{u,v,z}, rejected_law⟩
  sensitivity := sensitive arena.{u,v,z}.Law actual.{u,v,z} rejected.{u,v,z} rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eval2_totalWeight.{u,v,z}) (type_of% (realize signature.{u,v,z} actual.{u,v,z}.readout actual.{u,v,z}.anchor)) Type Unit where
  unitName := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.eval2_totalWeight.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.Evaluation.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,z}⟩
  objectArena := .source ⟨arena.{u,v,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,z} ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v,z} actual.{u,v,z}.readout actual.{u,v,z}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution
    definition := none
    coordinates := #[0,1,2,4,5,6,9]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
end Evaluation

end
end Reg.D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution
