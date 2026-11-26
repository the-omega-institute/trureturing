import D5.S3.Arith.Divisors.MakowskiSchinzel.PrimeDeletion
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact source bridges for the public coprime and prime-power abundancy identities. -/

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.PrimeDeletion

open _root_.D5.S3.Arith.MakowskiSchinzel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => n.abundancyIndex) (fun e => nomatch e)

abbrev mulArena : Arena where
  signature := signature
  Law R := ∀ {a b : ℕ}, a.Coprime b →
    R.readout () () (a * b) = R.readout () () a * R.readout () () b

private theorem mul_actual_law : mulArena.Law actual := @abundancy_mul

private theorem mul_source_bridge :
    (type_of% (@abundancy_mul)) ↔ mulArena.Law actual := Iff.rfl

abbrev powArena : Arena where
  signature := signature
  Law R := ∀ {r : ℕ}, r.Prime → ∀ k : ℕ, R.readout () () (r ^ k) = geom r k

private theorem pow_actual_law : powArena.Law actual := @abundancy_prime_pow

private theorem pow_source_bridge :
    (type_of% (@abundancy_prime_pow)) ↔ powArena.Law actual := Iff.rfl

def mulRejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem mul_rejected_law : ¬ mulArena.Law mulRejected := by
  intro h
  have hh := h (a := 1) (b := 1) (by decide)
  norm_num [mulRejected, realize] at hh

def mulEvidence : Registration mulArena (type_of% @abundancy_mul) where
  actual := actual
  bridge := mul_source_bridge
  variation := ⟨@mul_actual_law, mulRejected, mul_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨mulRejected, ?_, rfl, mul_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize, Nat.abundancyIndex]

def powRejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem pow_rejected_law : ¬ powArena.Law powRejected := by
  intro h
  have hh := h Nat.prime_two 0
  norm_num [powRejected, realize, geom] at hh

def powEvidence : Registration powArena (type_of% @abundancy_prime_pow) where
  actual := actual
  bridge := pow_source_bridge
  variation := ⟨@pow_actual_law, powRejected, pow_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨powRejected, ?_, rfl, pow_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize, Nat.abundancyIndex]

def mulAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abundancy_mul) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.MakowskiSchinzel.abundancy_mul.__information_unit
  realizationName := `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.PrimeDeletion.mulEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨mulArena⟩
  objectArena := .source ⟨mulArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source mulArena ⟨mulEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => n.abundancyIndex) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.PrimeDeletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def powAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abundancy_prime_pow) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.MakowskiSchinzel.abundancy_prime_pow.__information_unit
  realizationName := `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.PrimeDeletion.powEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨powArena⟩
  objectArena := .source ⟨powArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source powArena ⟨powEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => n.abundancyIndex) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.PrimeDeletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace primePowerProduct

abbrev signature : Signature where
  Params := ℕ → ℕ
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ e s => (∏ p ∈ s, p ^ e p).abundancyIndex)
    (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : Finset ℕ) (e : ℕ → ℕ),
    (∀ p ∈ s, e p ≠ 0 → p.Prime) →
      R.readout () e s = ∏ p ∈ s, geom p (e p)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := h ∅ (fun _ => 0) (by simp)
  norm_num [rejected, realize] at hh

def evidence : Registration arena
    (type_of% (@SmoothPredecessor.abundancy_prime_power_product)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@SmoothPredecessor.abundancy_prime_power_product, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(fun _ => 1), ∅, {2}, ?_⟩
    simp only [actual, realize, Finset.prod_empty, Finset.prod_singleton, pow_one]
    norm_num [Nat.abundancyIndex,
      show Nat.divisors 2 = {1, 2} from by decide]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@SmoothPredecessor.abundancy_prime_power_product)
    (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.abundancy_prime_power_product.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.PrimeDeletion.primePowerProduct.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ e s => (∏ p ∈ s, p ^ e p).abundancyIndex) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.PrimeDeletion
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end primePowerProduct

end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.PrimeDeletion
