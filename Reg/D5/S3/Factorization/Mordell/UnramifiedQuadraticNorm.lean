import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

/-! Raw p-adic norm observations and the exact no-cancellation source law. -/
namespace Reg.D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace F
export _root_.D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm
  (norm_size tangent_norm_size common_tangent_parity)
end F
noncomputable section
instance (p : Nat.Primes) : Fact (p:ℕ).Prime := ⟨p.property⟩
abbrev Parameters := Σ p : Nat.Primes, ℤ_[p] × ℚ_[p]
abbrev signature : Signature where
  Params := Parameters
  State s := ℚ_[s.1]
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i s X => if i then (max ‖s.2.2‖ ‖X‖)^2
    else ‖s.2.2^2-(s.2.1:ℚ_[s.1])*X^2‖) (fun e => nomatch e)

def rejected (i : Bool) : Realization signature := realize signature
  (fun j s X => if j=i then actual.readout (!j) s X + 1 else actual.readout j s X)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Nat.Primes),
    ∀ (q : ℤ_[p]) (_hq : ¬ IsSquare (PadicInt.toZMod q)) (x y : ℚ_[p]),
    R.readout false ⟨p,q,x⟩ y = R.readout true ⟨p,q,x⟩ y

private theorem nonsquare_three : ¬ IsSquare (2 : ZMod 3) := by
  rintro ⟨x,hx⟩
  fin_cases x <;> revert hx <;> decide

private theorem rejected_negative (i : Bool) : ¬ arena.Law (rejected i) := by
  intro h
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hh := h ⟨3,by decide⟩ (2:ℤ_[3]) (by simpa only [map_ofNat] using nonsquare_three) 0 0
  cases i <;> norm_num [rejected,actual,realize] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine ⟨⟨⟨3,by decide⟩,2,0⟩,0,1,?_⟩
  intro hh
  cases i <;> norm_num [actual,realize] at hh
  have he := norm_eq_zero.mp hh.symm
  norm_num at he

def realization : Registration arena (type_of% (@F.norm_size)) where
  actual := actual
  bridge := by
    constructor
    · intro h p q hq x y; exact @h p inferInstance q hq x y
    · intro h p hp q hq x y; exact h ⟨p,hp.out⟩ q hq x y
  variation := ⟨(fun p q hq x y => F.norm_size q hq x y),rejected false,rejected_negative false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i,?_,rfl,rejected_negative i⟩
      intro j hj
      funext s X
      simp [rejected,realize,hj]
    · intro e; exact nomatch e
  dependence := actual_dependence

noncomputable def norm_size_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@F.norm_size)
      (type_of% (realize signature
        (fun i s X => if i then (max ‖s.2.2‖ ‖X‖)^2
          else ‖s.2.2^2-(s.2.1:ℚ_[s.1])*X^2‖) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm.norm_size.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm.realization,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨realization⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun i s X => if i then (max ‖s.2.2‖ ‖X‖)^2
      else ‖s.2.2^2-(s.2.1:ℚ_[s.1])*X^2‖) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm, definition := none,
    coordinates := #[0,2,4], readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg"],
      stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false },{
      path := #["body","body","body","body","body","body","arg"],
      stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false }]
}
#print axioms realization
#print axioms norm_size_registration
end
end Reg.D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm
