import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound exact-order targets for the certificate soundness theorems. -/
noncomputable section
open _root_.D5.S3.Arith.PrimitiveRoot.SmallPrimes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ p => p - 1) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 1, 2, by decide⟩
private def two : PrimeValue := ⟨2, by decide⟩
private theorem order_two : orderOf (2 : ZMod 3) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

namespace PrimeSlot
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ} {q : PrimeValue} {ls : List PrimeValue},
    checkPrime p q ls = true →
      q.val.Prime ∧ q.val < p ∧ orderOf (q.val : ZMod p) = R.readout () () p
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (p := 3) (q := two) (ls := [two]) (by decide)
  have he : orderOf (2 : ZMod 3) = 0 := hh.2.2
  rw [order_two] at he
  omega
def family : Registration arena (type_of% @checkPrime_sound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@checkPrime_sound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@checkPrime_sound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.checkPrime_sound.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker.PrimeSlot.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p - 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end PrimeSlot

namespace Block
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {start count : ℕ} {rows : List Row},
    checkBlock start count rows = true →
      ∀ k, k < count → (start + 2 * k).Prime →
        ∃ q, q.Prime ∧ q < start + 2 * k ∧
          orderOf (q : ZMod (start + 2 * k)) = R.readout () () (start + 2 * k)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (start := 3) (count := 1) (rows := [.p two [two]])
    (by decide) 0 (by decide) (by decide)
  obtain ⟨q, hq, hlt, ho⟩ := hh
  have hq2 : q = 2 := by have := hq.two_le; omega
  subst q
  have he : orderOf (2 : ZMod 3) = 0 := ho
  rw [order_two] at he
  omega
def family : Registration arena (type_of% @checkBlock_sound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@checkBlock_sound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@checkBlock_sound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.checkBlock_sound.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker.Block.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p - 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Block

namespace Primality
abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ _ p => decide p.Prime) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ} {q : PrimeValue} {ls : List PrimeValue},
    checkPrime p q ls = true → R.readout () () p = true
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (p := 3) (q := two) (ls := [two]) (by decide)
  change false = true at hh
  cases hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 2, by decide⟩
def family : Registration arena (type_of% @checkPrime_prime) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using @checkPrime_prime,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@checkPrime_prime) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.checkPrime_prime.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker.Primality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => decide p.Prime) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Primality

namespace Append
abbrev signature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : ℕ, Σ _ : ℕ, ℕ) (fun _ => List Row) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ p xs => checkBlock p.1 (p.2.1 + p.2.2) xs)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {start n m : ℕ} {xs ys : List Row},
    checkBlock start n xs = true → checkBlock (start + 2 * n) m ys = true →
      R.readout () ⟨start, n, m⟩ (xs ++ ys) = true
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (start := 3) (n := 1) (m := 0) (xs := [.p two [two]]) (ys := [])
    (by decide) (by decide)
  change false = true at hh
  cases hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨⟨3, 1, 0⟩, [.p two [two]], [], by decide⟩
def family : Registration arena (type_of% @checkBlock_append) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@checkBlock_append, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@checkBlock_append) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.checkBlock_append.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker.Append.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p xs => checkBlock p.1 (p.2.1 + p.2.2) xs) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (List Row)
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Append

#print axioms Append.family
#print axioms Primality.family
#print axioms PrimeSlot.family
#print axioms Block.family
end Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker
