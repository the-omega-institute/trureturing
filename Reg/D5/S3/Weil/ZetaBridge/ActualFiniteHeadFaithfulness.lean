/-
SOURCE_ONLY_UNCOMPILED. One source registration candidate for the exact pinned
actual_finite_head_faithful theorem. Its original owner and full telescope are
retained. The owner and its lower-chain dependency candidates are UNCOMPILED;
they are imported as proof candidates, not replaced by assumptions. No kernel,
axiom/proof-trust, Reg, source-selector, Scribe or CI acceptance is claimed.

The selected source operand is the original function v in the terminal v n.
Parameters are entire functions Int -> Complex, states are integers, and there
is one Unit role. The actual readout applies the parameter to its state; the
rejected readout is constant one. The pinned Realization API takes role before
parameter, hence fun _ v n => v n and r.readout () v n below. No identity-value
wrapper is inserted into the source or into the nullity premise. In particular,
couplingColumn c S v m retains its original coefficients and full arithmetic
symbol. The actual Law directly consumes the original theorem; the bridge is
Iff.rfl for the full statement, including arbitrary c, hc, S, v, M and hnull.
The dependence witness uses v n = (n : Complex), with integer states 0 and 1.
Law rejection uses c = 2, S = {0}, zero coefficients and M = 0, so the actual
columns vanish while the rejected conclusion would give (1 : Complex) = 0.

The pinned judge implementation has been inspected as source, not executed.
CompiledSourceScope.atPath records eight forall bodies (c, hc, S, v, M, hnull,
n, membership). In the raw Eq application, fn/arg reaches v n and the final fn
selects v. Coordinate 3 is the original v binder; its domain Int -> Complex
has no earlier-coordinate dependencies. The functionOperand branch requires
stateBinder = 0 as mode metadata, stateOperand = none and booleanPredicate =
false. It obtains the function's domain, appends a fresh integer state, and
applies the lifted original v to that state. Thus stateBinder = 0 in this mode
does not designate the original c binder as the mathematical state.

For the proposed raw context of size 8, that branch transports the state and
output using coordinate [3], and the observation using [3, 8]. The lifted body
uses only v and the fresh state. transport performs forward projection and
checks its raw inverse; no c, hc, S, M, hnull, n or membership is required in
the projected observation. packedType/packedValue use the single coordinate
directly, so the parameter is v itself. validateFields compares these types
and the entire projected state function with the actual readout at the single
role and parameter. CompiledSourceContract.validate separately reconstructs
the complete Law, checks declaration safety and operand use, and compares the
descriptor with the family's raw actual realization. The local bridge alone
does not establish any of these source-binding obligations.

All five signature universes are explicitly zero. The pinned polymorphic
Reg.Support.DependentFamily enrollment is imported, and the descriptor is a
literal application of its realize template. Source arena/objectArena and
realization are retained; continuation is unknown with no familyRecord or
escapeFrom. Both auto-implicit options remain false. Actual compiled Expr
paths, operand eligibility, coordinate transport/inverse, packed shapes,
universes, bridge/proofs, kernel/axiom closure, template enrollment, full Law
reconstruction, operand live use, descriptor binding, Reg/Scribe and required
CI checks all remain unperformed until the caller compiles and reports.
-/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open LeanInformationAudit

abbrev coefficientSignature : Signature.{0, 0, 0, 0, 0} where
  Params := ℤ → ℂ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def coefficientActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ v n => v n) (fun e => nomatch e)

def coefficientRejected : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ => (1 : ℂ)) (fun e => nomatch e)

private theorem coefficientDependence :
    ObservationalDependence coefficientSignature coefficientActual := by
  intro i
  refine ⟨(fun n : ℤ => (n : ℂ)), (0 : ℤ), (1 : ℤ), ?_⟩
  norm_num [coefficientActual, realize]

def actual_finite_head_faithful_arena : Arena where
  signature := coefficientSignature
  Law r := ∀ {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) (M : ℕ)
    (hnull : ∀ m : ℤ, (M : ℝ) < |(m : ℝ)| →
      _root_.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.couplingColumn c S v m = 0),
    ∀ n ∈ S, r.readout () v n = 0

private theorem actual_finite_head_faithful_actual_law :
    actual_finite_head_faithful_arena.Law coefficientActual := by
  exact @_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness.actual_finite_head_faithful

private theorem actual_finite_head_faithful_rejected_law :
    ¬ actual_finite_head_faithful_arena.Law coefficientRejected := by
  intro hall
  have hnull : ∀ m : ℤ, ((0 : ℕ) : ℝ) < |(m : ℝ)| →
      couplingColumn 2 ({0} : Finset ℤ) (fun _ => (0 : ℂ)) m = 0 := by
    intro m _
    simp [couplingColumn]
  have h : (1 : ℂ) = 0 :=
    hall (c := 2) (by decide) ({0} : Finset ℤ) (fun _ => (0 : ℂ))
      (0 : ℕ) hnull (0 : ℤ) (by simp)
  exact one_ne_zero h

def actual_finite_head_faithful_family :
    Registration actual_finite_head_faithful_arena
      (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness.actual_finite_head_faithful)) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨actual_finite_head_faithful_actual_law, coefficientRejected,
    actual_finite_head_faithful_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coefficientRejected, ?_, rfl, actual_finite_head_faithful_rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := coefficientDependence

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness.actual_finite_head_faithful)
    (type_of% coefficientActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness.actual_finite_head_faithful.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness.actual_finite_head_faithful_family
  realizationSource := none
  generated := false
  arena := .source ⟨actual_finite_head_faithful_arena⟩
  objectArena := .source ⟨actual_finite_head_faithful_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source actual_finite_head_faithful_arena ⟨actual_finite_head_faithful_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature (fun _ v n => v n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-!
Quantitative registration attempt, source only. The original registration_1
above is unchanged; its pinned acceptance record is declared_validated.
Nothing in that record accepts this new registration_2.

The selected function is the actual norm at the first positive-column branch
under Summable in actual_finite_head_polynomial_tail_lower. Its input is the
original complex column value and its output is real. The square remains a
separate original operation. There is no invented composite norm-square
operand. Only this occurrence is replaced in Law; the negative-branch norm
and both norms in the actual tsum bound retain their original meanings.

The four family slots are bridge, variation, sensitivity and dependence.
The actual Law consumes the full new theorem, including its existential
constants and eventual cutoff. Constant-one rejection uses the full telescope
at c=2, S={0}, v=1. At the claimed eventual cutoff, every rejected summand
is 1 plus a nonnegative squared norm. Its finite sums exceed its purported
tsum by Archimedean choice, contradicting summability. This does not rely on
replacing the existential conclusion by a pointwise or fixed-cutoff law.

Source selection is a proposal, not a compiled-source binding. Five initial
forall bodies are followed by the k/C/N0 existential predicates, N and its
cutoff proof, the left conjunct, the function argument of Summable (before
its explicit default summation filter), the j lambda, the positive addend,
the base of its square, and the norm function before its complex argument.
No original telescope coordinate is used by this norm function: coordinates
is empty, the proposed packed parameter is Unit, and the fresh state is ℂ.
functionOperand=true and stateBinder=0 follow the already enrolled template's
function-operand mode. The source selector must check the raw Expr path,
empty packing, implicit norm instance, universes and fresh-state transport.
The compiler, axiom closure, four-slot proofs, descriptor equality, source
binding, enrollment, Scribe and required CI are all caller-owned and pending.
-/

open scoped BigOperators

abbrev quantitativeNormSignature : Signature.{0, 0, 0, 0, 0} where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def quantitativeNormActual : Realization quantitativeNormSignature :=
  realize quantitativeNormSignature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def quantitativeNormRejected : Realization quantitativeNormSignature :=
  realize quantitativeNormSignature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

private theorem quantitativeNormDependence :
    ObservationalDependence quantitativeNormSignature quantitativeNormActual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  norm_num [quantitativeNormActual, realize]

def actual_finite_head_polynomial_tail_lower_arena : Arena where
  signature := quantitativeNormSignature
  Law r := ∀ {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) (hnonzero : ∃ n ∈ S, v n ≠ 0),
    ∃ k : ℕ, k < S.card ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N →
        Summable (fun j : ℕ =>
          (r.readout () () (couplingColumn c S v ((N + j + 1 : ℕ) : ℤ))) ^ 2 +
            ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2) ∧
        C / ((N : ℝ) + 1) ^ (2 * k + 1) ≤
          ∑' j : ℕ, (‖couplingColumn c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
            ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2)

private theorem actual_finite_head_polynomial_tail_lower_actual_law :
    actual_finite_head_polynomial_tail_lower_arena.Law quantitativeNormActual := by
  exact @_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness.actual_finite_head_polynomial_tail_lower

private theorem actual_finite_head_polynomial_tail_lower_rejected_law :
    ¬ actual_finite_head_polynomial_tail_lower_arena.Law quantitativeNormRejected := by
  intro hall
  have hn : ∃ n ∈ ({0} : Finset ℤ), (fun _ : ℤ => (1 : ℂ)) n ≠ 0 :=
    ⟨0, by simp, one_ne_zero⟩
  obtain ⟨k, hk, C, hC, N0, hN⟩ :=
    hall (c := 2) (by decide) ({0} : Finset ℤ) (fun _ => (1 : ℂ)) hn
  let f : ℕ → ℝ := fun j => (1 : ℝ) ^ 2 +
    ‖couplingColumn 2 ({0} : Finset ℤ) (fun _ => (1 : ℂ))
      (-((N0 + j + 1 : ℕ) : ℤ))‖ ^ 2
  have hs : Summable f := (hN N0 le_rfl).1
  have hnonneg (j : ℕ) : 0 ≤ f j := by dsimp [f]; positivity
  have hone (j : ℕ) : (1 : ℝ) ≤ f j := by
    dsimp only [f]
    nlinarith only [sq_nonneg
      ‖couplingColumn 2 ({0} : Finset ℤ) (fun _ => (1 : ℂ))
        (-((N0 + j + 1 : ℕ) : ℤ))‖]
  obtain ⟨r, hr⟩ := exists_nat_gt (∑' j : ℕ, f j)
  have hlower : (r : ℝ) ≤ ∑ j ∈ Finset.range r, f j := by
    calc
      (r : ℝ) = ∑ _j ∈ Finset.range r, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hone j)
  have hupper : (∑ j ∈ Finset.range r, f j) ≤ ∑' j : ℕ, f j :=
    Summable.sum_le_tsum (Finset.range r) (fun j _ => hnonneg j) hs
  exact (not_le_of_gt hr) (hlower.trans hupper)

def actual_finite_head_polynomial_tail_lower_family :
    Registration actual_finite_head_polynomial_tail_lower_arena
      (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness.actual_finite_head_polynomial_tail_lower)) where
  actual := quantitativeNormActual
  bridge := Iff.rfl
  variation := ⟨actual_finite_head_polynomial_tail_lower_actual_law, quantitativeNormRejected,
    actual_finite_head_polynomial_tail_lower_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨quantitativeNormRejected, ?_, rfl,
        actual_finite_head_polynomial_tail_lower_rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := quantitativeNormDependence

noncomputable def registration_2 : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness.actual_finite_head_polynomial_tail_lower)
    (type_of% quantitativeNormActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness.actual_finite_head_polynomial_tail_lower.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness.actual_finite_head_polynomial_tail_lower_family
  realizationSource := none
  generated := false
  arena := .source ⟨actual_finite_head_polynomial_tail_lower_arena⟩
  objectArena := .source ⟨actual_finite_head_polynomial_tail_lower_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source actual_finite_head_polynomial_tail_lower_arena
    ⟨actual_finite_head_polynomial_tail_lower_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize quantitativeNormSignature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "body", "arg", "arg", "body",
        "body", "body", "fn", "arg", "fn", "arg", "body",
        "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness
