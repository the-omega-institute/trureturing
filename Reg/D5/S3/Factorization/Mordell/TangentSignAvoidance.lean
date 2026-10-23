import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.Mordell.TangentSignAvoidance
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! Tangent readout variation over the full dependent field and covering family. -/

namespace Reg.D5.S3.Factorization.Mordell.TangentSignAvoidance

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace F
export _root_.D5.S3.Factorization.Mordell.FieldKummer (Context CoveringRep)
end F
namespace T
export _root_.D5.S3.Factorization.Mordell.TangentSignAvoidance (simultaneous_tangent_sign_avoidance)
end T

universe u
noncomputable section

structure Parameters where
  k : F.Context.{u}
  q : k.Carrier
  r : k.Carrier
  a : k.Carrier
  b : k.Carrier
  hqr : q*r ≠ 0

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := F.CoveringRep (p.q*p.r) (Units.mk0 p.q (left_ne_zero_of_mul p.hqr)) 1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p c =>
    ((15*p.r+1)/2*c.z₁+(15*p.r-1)/2*c.z₃-15*p.r*c.t ≠ 0) ∧
    (p.a*c.z₂-p.q*p.b*c.z₁-5*p.q*p.r*c.t ≠ 0)) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : F.Context.{u}) (q r a b : K.Carrier)
      (hqr : q*r ≠ 0) (_hr : 15*r ≠ 1) (_hab : a ≠ 0 ∨ b ≠ 0)
      (c : F.CoveringRep (q*r) (Units.mk0 q (left_ne_zero_of_mul hqr)) 1),
    ∃ c' : F.CoveringRep (q*r) (Units.mk0 q (left_ne_zero_of_mul hqr)) 1,
      (c'.t = c.t ∨ c'.t = -c.t) ∧ (c'.z₁ = c.z₁ ∨ c'.z₁ = -c.z₁) ∧
      (c'.z₂ = c.z₂ ∨ c'.z₂ = -c.z₂) ∧ (c'.z₃ = c.z₃ ∨ c'.z₃ = -c.z₃) ∧
      R.readout () ⟨K,q,r,a,b,hqr⟩ c'

private instance liftCharZero : CharZero (ULift.{u} ℚ) where
  cast_injective := by
    intro m n h
    exact Nat.cast_injective (congrArg ULift.down h : (m : ℚ) = (n : ℚ))
private abbrev rationalContext : F.Context.{u} :=
  ⟨ULift.{u} ℚ,inferInstance,inferInstance,inferInstance⟩
private abbrev testParameters : Parameters.{u} :=
  ⟨rationalContext,1,-1/5,0,1,by norm_num⟩
private def finiteRep : signature.State testParameters where
  t := 1
  z₁ := 1
  z₂ := 0
  z₃ := 2
  nonzero := Or.inl one_ne_zero
  eq₁₂ := by dsimp only [testParameters,rationalContext]; norm_num
  eq₁₃ := by dsimp only [testParameters,rationalContext]; norm_num
private def infiniteRep : signature.State testParameters where
  t := 0
  z₁ := 1
  z₂ := 1
  z₃ := 1
  nonzero := Or.inr (Or.inl one_ne_zero)
  eq₁₂ := by dsimp only [testParameters,rationalContext]; norm_num
  eq₁₃ := by dsimp only [testParameters,rationalContext]; norm_num

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨c',_,_,_,_,hf⟩ := h rationalContext 1 (-1/5) 0 1
    (by norm_num) (by norm_num) (Or.inr one_ne_zero) finiteRep
  exact hf

private theorem actualLaw : arena.{u}.Law actual := by
  intro K q r a b hqr hr hab c
  exact T.simultaneous_tangent_sign_avoidance q r a b hqr hr hab c

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨testParameters,infiniteRep,finiteRep,?_⟩
  have hi : actual.readout i testParameters infiniteRep := by
    change ((15*(-1/5 : ULift.{u} ℚ)+1)/2*1+(15*(-1/5)-1)/2*1-15*(-1/5)*0 ≠ 0) ∧ (0*1-1*1*1-5*1*(-1/5)*0 ≠ 0)
    norm_num
  have hf : ¬ actual.readout i testParameters finiteRep := by
    change ¬ (((15*(-1/5 : ULift.{u} ℚ)+1)/2*1+(15*(-1/5)-1)/2*2-15*(-1/5)*1 ≠ 0) ∧ (0*0-1*1*1-5*1*(-1/5)*1 ≠ 0))
    norm_num
  intro he
  exact hf (Eq.mp he hi)

def registration : Registration arena.{u}
    (type_of% (@T.simultaneous_tangent_sign_avoidance.{u})) where
  actual := actual
  bridge := by
    constructor
    · intro h K q r a b hqr hr hab c
      exact h q r a b hqr hr hab c
    · intro h K f cz q r a b hqr hr hab c
      classical
      exact h ⟨K,f,cz,inferInstance⟩ q r a b hqr hr hab c
  variation := ⟨actualLaw,rejected,rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejectedLaw⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def simultaneous_tangent_sign_avoidance_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@T.simultaneous_tangent_sign_avoidance.{u})
      (type_of% (realize signature.{u} (fun _ p c =>
        ((15*p.r+1)/2*c.z₁+(15*p.r-1)/2*c.z₃-15*p.r*c.t ≠ 0) ∧
        (p.a*c.z₂-p.q*p.b*c.z₁-5*p.q*p.r*c.t ≠ 0)) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.TangentSignAvoidance.simultaneous_tangent_sign_avoidance.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.TangentSignAvoidance.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨registration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ p c =>
    ((15*p.r+1)/2*c.z₁+(15*p.r-1)/2*c.z₃-15*p.r*c.t ≠ 0) ∧
    (p.a*c.z₂-p.q*p.b*c.z₁-5*p.q*p.r*c.t ≠ 0)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.TangentSignAvoidance, definition := none, coordinates := #[0], readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","body","body","arg","body","arg","arg","arg","arg"], stateBinder := 11, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `relaxedAutoImplicit, value := .bool false }]
}
#print axioms registration
#print axioms simultaneous_tangent_sign_avoidance_registration

end
end Reg.D5.S3.Factorization.Mordell.TangentSignAvoidance
