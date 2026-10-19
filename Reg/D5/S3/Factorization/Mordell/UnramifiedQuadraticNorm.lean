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

noncomputable section
namespace Tangent
abbrev Parameters := Σ p : Nat.Primes, ℤ_[p] × (ℚ_[p] × ℚ_[p] × ℚ_[p])
abbrev signature : Signature where
  Params := Parameters
  State s := ℚ_[s.1] × ℚ_[s.1]
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i s X =>
    let ell := s.2.2.1 * X.1 - (s.2.1:ℚ_[s.1]) * s.2.2.2.1 * X.2 - s.2.2.2.2
    if i then (max ‖ell‖ ‖s.2.2.1 * X.2 - s.2.2.2.1 * X.1‖)^2 else ‖ell‖)
  (fun e => nomatch e)

def rejected (i : Bool) : Realization signature := realize signature
  (fun j s X => if j=i then actual.readout (!j) s X + 1 else actual.readout j s X)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Nat.Primes) (q : ℤ_[p]) (_hq : ¬ IsSquare (PadicInt.toZMod q))
    (a b x y c : ℚ_[p]) (_hab : a^2-(q:ℚ_[p])*b^2=c)
    (_hxy : x^2-(q:ℚ_[p])*y^2=c) (_hc : ‖(2:ℚ_[p])*c‖=1),
    R.readout false ⟨p,q,a,b,c⟩ (x,y) = R.readout true ⟨p,q,a,b,c⟩ (x,y)

private theorem norm_two : ‖(2:ℚ_[3])‖=1 := by
  exact (Padic.norm_natCast_eq_one_iff (p:=3) (n:=2)).mpr (by decide)

private theorem rejected_negative (i : Bool) : ¬ arena.Law (rejected i) := by
  intro h
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hh := h ⟨3,by decide⟩ (2:ℤ_[3])
    (by simpa only [map_ofNat] using nonsquare_three) 1 0 1 0 1
    (by norm_num) (by norm_num) (by simpa using norm_two)
  cases i <;> norm_num [rejected,actual,realize] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine ⟨⟨⟨3,by decide⟩,2,1,0,1⟩,(0,0),(1,0),?_⟩
  cases i <;> norm_num [actual,realize]

def realization : Registration arena (type_of% (@F.tangent_norm_size)) where
  actual := actual
  bridge := by
    constructor
    · intro h p q hq a b x y c hab hxy hc
      exact @h p inferInstance q hq a b x y c hab hxy hc
    · intro h p hp q hq a b x y c hab hxy hc
      exact h ⟨p,hp.out⟩ q hq a b x y c hab hxy hc
  variation := ⟨(fun p q hq a b x y c hab hxy hc =>
    F.tangent_norm_size q hq a b x y c hab hxy hc),rejected false,rejected_negative false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i,?_,rfl,rejected_negative i⟩
      intro j hj
      funext s X
      simp [rejected,realize,hj]
    · intro e; exact nomatch e
  dependence := actual_dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@F.tangent_norm_size)
      (type_of% (realize signature
        (fun i s X =>
          let ell := s.2.2.1 * X.1 - (s.2.1:ℚ_[s.1]) * s.2.2.2.1 * X.2 - s.2.2.2.2
          if i then (max ‖ell‖ ‖s.2.2.1 * X.2 - s.2.2.2.1 * X.1‖)^2 else ‖ell‖)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm.tangent_norm_size.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm.Tangent.realization,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨realization⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun i s X =>
      let ell := s.2.2.1 * X.1 - (s.2.1:ℚ_[s.1]) * s.2.2.2.1 * X.2 - s.2.2.2.2
      if i then (max ‖ell‖ ‖s.2.2.1 * X.2 - s.2.2.2.1 * X.1‖)^2 else ‖ell‖)
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm, definition := none,
    coordinates := #[0,2,4,5,8], readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","fn","arg"], stateBinder := 6,
      functionOperand := false, stateOperand := none, booleanPredicate := false },{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","arg"], stateBinder := 6,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false }]
}
#print axioms realization
#print axioms registration
end Tangent

namespace CommonScale
abbrev Parameters := Σ p : Nat.Primes, ℤ_[p] × (Fin 7 → ℚ_[p])
abbrev signature : Signature where
  Params := Parameters
  State s := ℚ_[s.1]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ s := ℚ_[s.1]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ t => t) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Nat.Primes) (q : ℤ_[p]) (_hq : ¬ IsSquare (PadicInt.toZMod q))
    (c d a b t x y z : ℚ_[p]) (_hc : ‖c‖=1) (_hd : ‖d‖=1) (_h2 : ‖(2:ℚ_[p])‖=1)
    (_hab : a^2-(q:ℚ_[p])*b^2=d) (_hn : t≠0 ∨ x≠0 ∨ y≠0 ∨ z≠0)
    (_h₃ : x^2-(q:ℚ_[p])*y^2=d*t^2) (_h₂ : y^2-z^2=c*t^2),
    let T := R.readout () ⟨p,q,![c,d,a,b,x,y,z]⟩ t
    let X := x/T; let Y := y/T; let Z := z/T
    let e₂ := ((c+1)/2)*Y-((1-c)/2)*Z-c
    let e₃ := a*X-(q:ℚ_[p])*b*Y-d
    T≠0 ∧ ‖a‖≤1 ∧ ‖b‖≤1 ∧ ‖X‖≤1 ∧ ‖Y‖≤1 ∧ ‖Z‖≤1 ∧
    ‖e₂‖≤1 ∧ ‖e₃‖≤1 ∧ (e₂≠0 → Even e₂.valuation) ∧
    (e₃≠0 → Even e₃.valuation) ∧
    (‖T‖≤1 → (‖T‖=1 ∨ ‖x‖=1 ∨ ‖y‖=1 ∨ ‖z‖=1) →
      ‖T‖=1 ∧ (T*e₂≠0 → Even (T*e₂).valuation) ∧
      (T*e₃≠0 → Even (T*e₃).valuation))

private theorem rejected_negative : ¬ arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hh := h ⟨3,by decide⟩ (2:ℤ_[3])
    (by simpa only [map_ofNat] using nonsquare_three) (-1) 1 1 0 1 1 0 1
    (by norm_num) (by norm_num) Tangent.norm_two (by norm_num)
    (by simp) (by norm_num) (by norm_num)
  exact hh.1 rfl

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine ⟨⟨⟨3,by decide⟩,2,fun _ => 0⟩,0,1,?_⟩
  exact zero_ne_one

def realization : Registration arena (type_of% (@F.common_tangent_parity)) where
  actual := actual
  bridge := by
    constructor
    · intro h p q hq c d a b t x y z hc hd h2 hab hn h₃ h₂
      exact @h p inferInstance q hq c d a b t x y z hc hd h2 hab hn h₃ h₂
    · intro h p hp q hq c d a b t x y z hc hd h2 hab hn h₃ h₂
      exact h ⟨p,hp.out⟩ q hq c d a b t x y z hc hd h2 hab hn h₃ h₂
  variation := ⟨(fun p q hq c d a b t x y z hc hd h2 hab hn h₃ h₂ =>
    F.common_tangent_parity q hq c d a b t x y z hc hd h2 hab hn h₃ h₂),
    rejected,rejected_negative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_negative⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := actual_dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@F.common_tangent_parity)
      (type_of% (realize signature (fun _ _ t => t) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm.common_tangent_parity.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm.CommonScale.realization,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨realization⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ t => t) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm, definition := none,
    coordinates := #[0,2,4,5,6,7,9,10,11], readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","arg","fn","arg"], stateBinder := 8,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false }]
}
#print axioms realization
#print axioms registration
end CommonScale
end

end Reg.D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm
