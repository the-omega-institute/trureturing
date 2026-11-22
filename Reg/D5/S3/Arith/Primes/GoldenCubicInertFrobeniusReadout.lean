import D5.S3.Arith.Primes.GoldenCubicInertFrobeniusReadout
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Algebra.Field.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Primes.GoldenCubicInertFrobeniusReadout
open _root_.D5.S3.Arith.Primes.GoldenCubicInertFrobeniusReadout
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ q => (q+1)/3) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {K : Type u} [Field K] (q : ℕ) [CharP K q]
    (_hp : q.Prime) (_hqgt : 3<q) (_hq : q%3=2) (x δ : K)
    (_hδ : δ^2=-3) (_hδF : δ^q = -δ) (_hx : x^q=x)
    (_hB : x^2+3 ≠ 0),
    let B := x^2+3
    let β := B*(-x+δ)
    let ω := (δ-1)/2
    let ε := β^(R.readout () () q)/B
    ε^3=1 ∧ β^((q^2-1)/3)=ε ∧ ω^3=1 ∧ ω≠1 ∧
      ∀ c : K, c^3=β →
      (∀ a : K, a^3=1 →
        (cardanoTerm B c a)^3 - 3*B*cardanoTerm B c a + 2*B*x=0 ∧
        (cardanoTerm B c a)^q=cardanoTerm B c (a/ε)) ∧
      (∀ a b : K, a^3=1 → b^3=1 → cardanoTerm B c a=cardanoTerm B c b → a=b) ∧
      ((cardanoTerm B c 1)^q=cardanoTerm B c 1 ↔ ε=1)

namespace Fixture
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

@[ext] structure Q25 where
  re : ZMod 5
  im : ZMod 5
deriving DecidableEq

instance : Fintype Q25 := Fintype.ofEquiv (ZMod 5 × ZMod 5)
  ⟨fun p => ⟨p.1,p.2⟩, fun x => (x.re,x.im), fun _=>rfl, fun _=>rfl⟩

instance : Zero Q25 := ⟨⟨0,0⟩⟩
instance : One Q25 := ⟨⟨1,0⟩⟩
instance : Add Q25 := ⟨fun a b => ⟨a.re+b.re,a.im+b.im⟩⟩
instance : Neg Q25 := ⟨fun a => ⟨-a.re,-a.im⟩⟩
instance : Mul Q25 := ⟨fun a b => ⟨a.re*b.re+2*a.im*b.im,a.re*b.im+a.im*b.re⟩⟩
instance : Inv Q25 := ⟨fun a =>
  let n := (a.re*a.re-2*a.im*a.im)⁻¹
  ⟨a.re*n,-a.im*n⟩⟩

@[simp] private theorem re_zero : (0:Q25).re=0 := rfl
@[simp] private theorem im_zero : (0:Q25).im=0 := rfl
@[simp] private theorem re_one : (1:Q25).re=1 := rfl
@[simp] private theorem im_one : (1:Q25).im=0 := rfl
@[simp] private theorem re_add (a b : Q25) : (a+b).re=a.re+b.re := rfl
@[simp] private theorem im_add (a b : Q25) : (a+b).im=a.im+b.im := rfl
@[simp] private theorem re_neg (a : Q25) : (-a).re= -a.re := rfl
@[simp] private theorem im_neg (a : Q25) : (-a).im= -a.im := rfl
@[simp] private theorem re_mul (a b : Q25) : (a*b).re=a.re*b.re+2*a.im*b.im := rfl
@[simp] private theorem im_mul (a b : Q25) : (a*b).im=a.re*b.im+a.im*b.re := rfl

instance : Field Q25 := Field.ofMinimalAxioms Q25
  (by intro a b c; ext <;> simp <;> ring)
  (by intro a; ext <;> simp)
  (by intro a; ext <;> simp)
  (by intro a b c; ext <;> simp <;> ring)
  (by intro a b; ext <;> simp <;> ring)
  (by intro a; ext <;> simp)
  (by decide +kernel)
  (by decide +kernel)
  (by intro a b c; ext <;> simp <;> ring)
  ⟨0,1,by decide +kernel⟩

private theorem re_nat (n : ℕ) : ((n:Q25).re) = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.cast_succ,Nat.cast_succ,re_add,re_one,ih]

private theorem im_nat (n : ℕ) : ((n:Q25).im) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.cast_succ,im_add,im_one,ih,zero_add]

instance : CharP Q25 5 where
  cast_eq_zero_iff n := by
    constructor
    · intro h
      have hh := congrArg Q25.re h
      rw [re_nat,re_zero] at hh
      exact (CharP.cast_eq_zero_iff (ZMod 5) 5 n).mp hh
    · intro h
      ext
      · exact (re_nat n).trans ((CharP.cast_eq_zero_iff (ZMod 5) 5 n).mpr h)
      · exact im_nat n

def δ : Q25 := ⟨0,1⟩
theorem delta_sq : δ^2=(-3:Q25) := by decide +kernel
theorem delta_frob : δ^5=-δ := by decide +kernel
theorem four_fixed : (4:Q25)^5=4 := by decide +kernel
theorem four_block_ne : (4:Q25)^2+3 ≠ 0 := by decide +kernel
theorem rejected_zero_digit :
    ((((4:Q25)^2+3)*(-(4:Q25)+δ))^0 / ((4:Q25)^2+3))^3 ≠ 1 := by
  decide +kernel

end Fixture

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Q := ULift.{u} Fixture.Q25
  have H := @h Q inferInstance 5 inferInstance
    (by decide) (by decide) (by decide) 4 ⟨Fixture.δ⟩
    (ULift.down_injective Fixture.delta_sq)
    (ULift.down_injective Fixture.delta_frob)
    (ULift.down_injective Fixture.four_fixed)
    (fun he => Fixture.four_block_ne (congrArg ULift.down he))
  exact Fixture.rejected_zero_digit (congrArg ULift.down H.1)


private theorem actual_dependence :
    actual.readout () () 5 ≠ actual.readout () () 11 := by decide +kernel

def family : Registration arena.{u} (type_of% @native_inert_readout.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_inert_readout.{u},rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := fun _ => ⟨(),5,11,actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@native_inert_readout.{u}) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Arith.Primes.GoldenCubicInertFrobeniusReadout.native_inert_readout.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenCubicInertFrobeniusReadout.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.GoldenCubicInertFrobeniusReadout
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "body","body","body","body","body","body","body","body",
        "value","fn","arg","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S3.Arith.Primes.GoldenCubicInertFrobeniusReadout
