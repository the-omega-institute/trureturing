/- GID: D5/S3/Arith/FibonacciAtomic/LocalWiring/BoundedBinaryRecurrenceSharpness
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalWiring/BoundedBinaryRecurrenceSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact shorter-prefix counterexamples and uniform sharpness for binary recurrence streams. -/

import D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrence

/-! Two lawful streams witness every shorter cut, without any invertibility or
minimal-order requirement on the individual presentations. -/

namespace D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrenceSharpness

open scoped BigOperators
open BoundedBinaryRecurrence (Legal Recurrence bounded_binary_recurrence)
open PublicRowSeedReadiness (bitNat)

private def impulse (r i : Nat) : Bool := decide (i = r)

private def periodic (d r i : Nat) : Bool := decide (i % d = r)

/-- The executable pair at the requested cut: zero versus an impulse below d,
then a shorter transient versus its periodic extension. -/
def witnesses (d v : Nat) : (Nat → Bool) × (Nat → Bool) :=
  if v < d then (fun _ => false, impulse v)
  else (impulse (v-d), periodic d (v-d))

/-- Output of one of the two actual witnesses at their first divergent index.
False selects the first stream and true selects the second stream. -/
def witnessOutput (d v : Nat) (side : Bool) : Bool :=
  if side then (witnesses d v).2 v else (witnesses d v).1 v

/-- A single public prefix length must suffice for every pair in the class. -/
def UniformlySeparates (d v : Nat) : Prop :=
  ∀ s t : Nat → Bool, Legal d s → Legal d t →
    (∀ i < v, s i = t i) → ∀ i, s i = t i

private theorem zero_legal (d : Nat) : Legal d (fun _ => false) :=
  ⟨0, Nat.zero_le _, Fin.elim0, by intro i; simp [bitNat]⟩

private theorem impulse_legal {d r : Nat} (hr : r < d) : Legal d (impulse r) :=
  ⟨r+1, hr, fun _ => false, by
    intro i
    have hi : i+(r+1) ≠ r := by omega
    simp [impulse, bitNat, hi]⟩

private theorem periodic_legal {d : Nat} (hd : 1 ≤ d) (r : Nat) :
    Legal d (periodic d r) := by
  let zero : Fin d := ⟨0, hd⟩
  refine ⟨d, le_rfl, fun j => decide (j.val = 0), ?_⟩
  intro i
  have hs : (∑ j : Fin d, bitNat (decide (j.val = 0)) *
      bitNat (periodic d r (i+j.val))) = bitNat (periodic d r i) := by
    rw [Finset.sum_eq_single zero]
    · simp [zero, bitNat]
    · intro j _ hne
      have hj : j.val ≠ 0 := fun h => hne (Fin.ext h)
      simp [hj, bitNat]
    · simp
  rw [hs]
  have hperiod : periodic d r (i+d) = periodic d r i := by
    simp [periodic, Nat.add_mod_right]
  rw [hperiod]
  cases periodic d r i <;> decide

private theorem witnesses_legal (d v : Nat) (hd : 1 ≤ d) (hv : v < 2*d) :
    Legal d (witnesses d v).1 ∧ Legal d (witnesses d v).2 := by
  by_cases h : v < d
  · simpa only [witnesses, ite_eq_left h] using And.intro (zero_legal d) (impulse_legal h)
  · simpa only [witnesses, ite_eq_right h] using
      And.intro (impulse_legal (d := d) (r := v-d) (by omega)) (periodic_legal hd (v-d))

private theorem witnesses_agree (d v : Nat) (hv : v < 2*d) (i : Nat) (hi : i < v) :
    (witnesses d v).1 i = (witnesses d v).2 i := by
  by_cases h : v < d
  · simp [witnesses, h, impulse, Nat.ne_of_lt hi]
  · rw [witnesses, ite_eq_right h]
    by_cases h₁ : i < d
    · simp only [impulse, periodic, Nat.mod_eq_of_lt h₁]
    · have hmod : i % d = i-d := by
        have he : i-d+d = i := by omega
        calc
          i % d = (i-d+d) % d := congrArg (· % d) he.symm
          _ = (i-d) % d := Nat.add_mod_right _ _
          _ = i-d := Nat.mod_eq_of_lt (by omega)
      have hne : i ≠ v-d := by omega
      have hne' : i-d ≠ v-d := by omega
      simp [impulse, periodic, hmod, hne, hne']

private theorem witnesses_split (d v : Nat) (hv : v < 2*d) :
    (witnesses d v).1 v = false ∧ (witnesses d v).2 v = true := by
  by_cases h : v < d
  · simp [witnesses, h, impulse]
  · have hmod : v % d = v-d := by
      have he : v-d+d = v := by omega
      calc
        v % d = (v-d+d) % d := congrArg (· % d) he.symm
        _ = (v-d) % d := Nat.add_mod_right _ _
        _ = v-d := Nat.mod_eq_of_lt (by omega)
    have hne : v ≠ v-d := by omega
    simp [witnesses, h, impulse, periodic, hmod, hne]

/-- Every cut shorter than 2d has lawful matching witnesses with a different
next bit, and 2d is the least uniform sufficient prefix length. -/
theorem bounded_binary_recurrence_sharpness (d : Nat) (hd : 1 ≤ d) :
    (∀ (v : Nat), v < 2*d →
      (∀ side : Bool, witnessOutput d v side = side) ∧
      Legal d (witnesses d v).1 ∧ Legal d (witnesses d v).2 ∧
      (∀ i < v, (witnesses d v).1 i = (witnesses d v).2 i) ∧
      (witnesses d v).1 v ≠ (witnesses d v).2 v) ∧
    (∀ v : Nat, UniformlySeparates d v ↔ 2*d ≤ v) := by
  constructor
  · intro v hv
    obtain ⟨hl, hr⟩ := witnesses_legal d v hd hv
    obtain ⟨h₀, h₁⟩ := witnesses_split d v hv
    refine ⟨?_, hl, hr, witnesses_agree d v hv, by rw [h₀, h₁]; decide⟩
    intro side
    cases side
    · simpa only [witnessOutput, Bool.false_eq_true, ite_false] using h₀
    · simpa only [witnessOutput, ite_true] using h₁
  · intro v
    constructor
    · intro h
      by_contra! hv
      obtain ⟨hl, hr⟩ := witnesses_legal d v hd hv
      obtain ⟨h₀, h₁⟩ := witnesses_split d v hv
      have he := h _ _ hl hr (witnesses_agree d v hv) v
      rw [h₀, h₁] at he
      cases he
    · intro hv s t hs ht he
      apply (bounded_binary_recurrence d).2.1 s t hs ht
      exact congrArg List.ofFn (funext fun j : Fin (2*d) => he j.val (lt_of_lt_of_le j.isLt hv))

#print axioms bounded_binary_recurrence_sharpness

end D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrenceSharpness
