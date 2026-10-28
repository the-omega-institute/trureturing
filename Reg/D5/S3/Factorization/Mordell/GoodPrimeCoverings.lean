import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.Mordell.GoodPrimeCoverings
import Reg.Support.DependentFamily

/-! The two pairs of homogeneous polynomial observations on common quadruples. -/

namespace Reg.D5.S3.Factorization.Mordell.GoodPrimeCoverings

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace F
export _root_.D5.S3.Factorization.Mordell.GoodPrimeCoverings (good_prime_common_tuples lambdaQuadrics muQuadrics)
end F

noncomputable section

abbrev Parameters := Σ _p : Nat.Primes, Σ _q : ℕ, ℕ

abbrev signature : Signature where
  Params := Parameters
  State s := Fin 4 → ℚ_[s.1]
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ s := ℚ_[s.1] × ℚ_[s.1]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i s Z => if i then
      F.muQuadrics s.1 s.2.1 Z
    else F.lambdaQuadrics s.1 s.2.1 Z)
  (fun e => nomatch e)

def rejected (i : Bool) : Realization signature := realize signature
  (fun j s Z => if j = i then
      (5*((s.2.1 : ℚ_[s.1])*(s.2.2 : ℚ_[s.1]))*Z 0^2+1,
        15*((s.2.1 : ℚ_[s.1])*(s.2.2 : ℚ_[s.1]))*Z 0^2)
    else actual.readout j s Z) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Nat.Primes) (q r : ℕ) (_hp : ¬ (p : ℕ) ∣ 30*q*r),
    ∃ (L M : Fin 4 → ℚ_[p]),
      (L 0 ≠ 0 ∨ L 1 ≠ 0 ∨ L 2 ≠ 0 ∨ L 3 ≠ 0) ∧
      (M 0 ≠ 0 ∨ M 1 ≠ 0 ∨ M 2 ≠ 0 ∨ M 3 ≠ 0) ∧
      R.readout false ⟨p,q,r⟩ L =
        (5*((q : ℚ_[p])*(r : ℚ_[p]))*L 0^2,15*((q : ℚ_[p])*(r : ℚ_[p]))*L 0^2) ∧
      R.readout true ⟨p,q,r⟩ M =
        (5*((q : ℚ_[p])*(r : ℚ_[p]))*M 0^2,15*((q : ℚ_[p])*(r : ℚ_[p]))*M 0^2)

private theorem rejected_negative (i : Bool) : ¬ arena.Law (rejected i) := by
  intro h
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨L,M,-,-,hL,hM⟩ := h ⟨7,by decide⟩ 1 1 (by norm_num)
  cases i
  · have hh := congrArg Prod.fst hL
    change 5*((1 : ℚ_[7])*1)*L 0^2+1 = 5*((1 : ℚ_[7])*1)*L 0^2 at hh
    have hn : (1 : ℚ_[7]) = 0 := by linear_combination hh
    exact one_ne_zero hn
  · have hh := congrArg Prod.fst hM
    change 5*((1 : ℚ_[7])*1)*M 0^2+1 = 5*((1 : ℚ_[7])*1)*M 0^2 at hh
    have hn : (1 : ℚ_[7]) = 0 := by linear_combination hh
    exact one_ne_zero hn

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  refine ⟨⟨⟨7,by decide⟩,1,1⟩,(fun _ : Fin 4 => (0 : ℚ_[7])),![0,0,1,0],?_⟩
  intro h
  have hh := congrArg Prod.fst h
  cases i <;> norm_num [actual,realize,F.lambdaQuadrics,F.muQuadrics] at hh

def realization : Registration arena (type_of% (@F.good_prime_common_tuples)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@F.good_prime_common_tuples,rejected false,rejected_negative false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i,?_,rfl,rejected_negative i⟩
      intro j hj
      funext s Z
      simp [rejected,realize,hj]
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def good_prime_common_tuples_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@F.good_prime_common_tuples)
      (type_of% (realize signature
        (fun i s Z => if i then
            F.muQuadrics s.1 s.2.1 Z
          else F.lambdaQuadrics s.1 s.2.1 Z)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.GoodPrimeCoverings.good_prime_common_tuples.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.GoodPrimeCoverings.realization,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨realization⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun i s Z => if i then
        F.muQuadrics s.1 s.2.1 Z
      else F.lambdaQuadrics s.1 s.2.1 Z)
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Factorization.Mordell.GoodPrimeCoverings, definition := none,
    coordinates := #[0,1,2], readouts := #[{
      path := #["body","body","body","body","arg","body","arg","body",
        "arg","arg","fn","arg","fn","arg"],
      stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false },{
      path := #["body","body","body","body","arg","body","arg","body",
        "arg","arg","arg","fn","arg"],
      stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]
}

#print axioms realization
#print axioms good_prime_common_tuples_registration

end
end Reg.D5.S3.Factorization.Mordell.GoodPrimeCoverings
