/- GID: D5/S3/Arith/FibonacciAtomic/FiniteScalarTraceKernel
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FiniteScalarTraceKernel
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite scalar deletion traces determine exact modular source kernels. -/

import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import D5.S1.Dynamics.ProfiniteCharacter
import D5.S1.Digit.Infinite.SuccessorContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.FiniteScalarTraceKernel

open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step quantity)
open D5.S1.Dynamics (ProfiniteIntegers)
open D5.S1.Dynamics.ProfiniteCharacter (residueProjection)
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open scoped CharTwo

local notation "Source" => LegalDigits × (ProfiniteIntegers × ProfiniteIntegers)
local notation "ρ" => fun (m : ℕ) (p : Source) =>
  (residueProjection m (Prod.fst (Prod.snd p)),
    residueProjection m (Prod.snd (Prod.snd p)))
local notation "bits" => fun (p : Source) (j : ℕ) => Bool.toNat (Subtype.val (Prod.fst p) j)

/-- Delete successive digits using the inverse Fibonacci matrix. -/
def trajectory {R : Type*} [CommRing R] (U : ℕ → R) (z : R × R) : ℕ → R × R
  | 0 => z
  | j + 1 => ((trajectory U z j).2 - (trajectory U z j).1 + U j,
      (trajectory U z j).1 - U j)

/-- The `r + 1` scalar readings modulo the positive modulus `m + 1`. -/
def scalarTrace (m r : ℕ) (p : Source) : Fin (r + 1) → ZMod (m + 1) :=
  fun j => quantity (trajectory (fun k => ((p.1.val k).toNat : ZMod (m + 1)))
    (residueProjection m p.2.1, residueProjection m p.2.2) j.val)

private theorem bounded_propagation {R : Type*} [CommRing R]
    (c c' f f' : ℕ → R) (r : ℕ)
    (hc : ∀ j, c j - c (j + 1) - c (j + 2) = f j)
    (hc' : ∀ j, c' j - c' (j + 1) - c' (j + 2) = f' j)
    (h0 : c 0 = c' 0) (h1 : c 1 = c' 1)
    (hf : ∀ j, j + 2 ≤ r → f j = f' j) :
    ∀ j, j ≤ r → c j = c' j := by
  intro j
  induction j using Nat.twoStepInduction with
  | zero => exact fun _ => h0
  | one => exact fun _ => h1
  | more j hj hj' =>
    intro hbound
    have he := hf j hbound
    have ha := hj (by omega)
    have hb := hj' (by omega)
    linear_combination ha - hb - hc j + hc' j - he

private theorem scalar_recurrence {R : Type*} [CommRing R]
    (U : ℕ → R) (z : R × R) (j : ℕ) :
    quantity (trajectory U z j) - quantity (trajectory U z (j + 1)) -
      quantity (trajectory U z (j + 2)) = 2 * U j + U (j + 1) := by
  simp only [trajectory, quantity]
  ring

private theorem trace_kernel {R : Type*} [CommRing R]
    (U U' : ℕ → R) (z z' : R × R) (r : ℕ) (hr : 1 ≤ r) :
    (∀ j, j ≤ r → quantity (trajectory U z j) = quantity (trajectory U' z' j)) ↔
      z' - z = (-3 * (U' 0 - U 0), 2 * (U' 0 - U 0)) ∧
        ∀ j, j + 2 ≤ r → 2 * (U' j - U j) + (U' (j + 1) - U (j + 1)) = 0 := by
  constructor
  · intro h
    have h0 := h 0 (by omega)
    have h1 := h 1 hr
    simp only [trajectory, quantity] at h0 h1
    refine ⟨?_, ?_⟩
    · apply Prod.ext
      · change z'.1 - z.1 = -3 * (U' 0 - U 0)
        linear_combination -2 * h0 + 3 * h1
      · change z'.2 - z.2 = 2 * (U' 0 - U 0)
        linear_combination h0 - 2 * h1
    · intro j hj
      have ha := h j (by omega)
      have hb := h (j + 1) (by omega)
      have hc := h (j + 2) hj
      linear_combination scalar_recurrence U z j - scalar_recurrence U' z' j -
        ha + hb + hc
  · rintro ⟨hz, hf⟩
    have hx := congrArg Prod.fst hz
    have hy := congrArg Prod.snd hz
    change z'.1 - z.1 = -3 * (U' 0 - U 0) at hx
    change z'.2 - z.2 = 2 * (U' 0 - U 0) at hy
    apply bounded_propagation
      (fun j => quantity (trajectory U z j)) (fun j => quantity (trajectory U' z' j))
      (fun j => 2 * U j + U (j + 1)) (fun j => 2 * U' j + U' (j + 1)) r
      (scalar_recurrence U z) (scalar_recurrence U' z')
    · simp only [trajectory, quantity]
      linear_combination -2 * hx - 3 * hy
    · simp only [trajectory, quantity]
      linear_combination -hx - 2 * hy
    · intro j hj
      linear_combination -hf j hj

private theorem source_kernel (m r : ℕ) (hr : 1 ≤ r) (p p' : Source) :
    scalarTrace m r p = scalarTrace m r p' ↔
      ρ m p' - ρ m p =
        (-3 * ((bits p' 0 : ZMod (m + 1)) - bits p 0),
          2 * ((bits p' 0 : ZMod (m + 1)) - bits p 0)) ∧
      ∀ j, j + 2 ≤ r →
        2 * ((bits p' j : ZMod (m + 1)) - bits p j) +
          ((bits p' (j + 1) : ZMod (m + 1)) - bits p (j + 1)) = 0 := by
  rw [← trace_kernel (fun j => (bits p j : ZMod (m + 1)))
    (fun j => (bits p' j : ZMod (m + 1))) (ρ m p) (ρ m p') r hr]
  constructor
  · intro h j hj
    exact congrFun h ⟨j, by omega⟩
  · intro h
    exact funext fun j => h j.val (by omega)

private theorem legal_pair_eq (m : ℕ) (hm : 3 ≤ m)
    (a b a' b' : Bool) (hab : ¬ (a = true ∧ b = true))
    (hab' : ¬ (a' = true ∧ b' = true))
    (h : ((2 * a.toNat + b.toNat : ℕ) : ZMod m) =
      ((2 * a'.toNat + b'.toNat : ℕ) : ZMod m)) : a = a' ∧ b = b' := by
  have ha : 2 * a.toNat + b.toNat < m := by
    cases a <;> cases b <;> simp_all <;> omega
  have hb : 2 * a'.toNat + b'.toNat < m := by
    cases a' <;> cases b' <;> simp_all <;> omega
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all

private theorem bit_eq_mod_two (a b : Bool)
    (h : (a.toNat : ZMod 2) = (b.toNat : ZMod 2)) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem large_modulus_kernel (m r : ℕ) (hm : 3 ≤ m + 1) (hr : 2 ≤ r)
    (p p' : Source) :
    scalarTrace m r p = scalarTrace m r p' ↔
      (∀ j, j < r → p.1.val j = p'.1.val j) ∧ ρ m p = ρ m p' := by
  rw [source_kernel m r (by omega)]
  constructor
  · rintro ⟨hz, hf⟩
    have pairs (j : ℕ) (hj : j + 2 ≤ r) :
        p.1.val j = p'.1.val j ∧ p.1.val (j + 1) = p'.1.val (j + 1) := by
      apply legal_pair_eq (m + 1) hm _ _ _ _ (p.1.property j) (p'.1.property j)
      push_cast
      linear_combination -hf j hj
    have hbits (j : ℕ) (hj : j < r) : p.1.val j = p'.1.val j := by
      by_cases h : j + 2 ≤ r
      · exact (pairs j h).1
      · have hjpos : 1 ≤ j := by omega
        have hp := (pairs (j - 1) (by omega)).2
        simpa [Nat.sub_add_cancel hjpos] using hp
    refine ⟨hbits, ?_⟩
    have h0 := hbits 0 (by omega)
    simp only [h0, sub_self, mul_zero] at hz
    exact (sub_eq_zero.mp hz).symm
  · rintro ⟨hb, hz⟩
    have h0 := hb 0 (by omega)
    refine ⟨by apply Prod.ext <;> simp [hz, h0], ?_⟩
    intro j hj
    simp [hb j (by omega), hb (j + 1) (by omega)]

private theorem parity_kernel (r : ℕ) (hr : 1 ≤ r) (p p' : Source) :
    scalarTrace 1 r p = scalarTrace 1 r p' ↔
      (∀ j, 1 ≤ j → j < r → p.1.val j = p'.1.val j) ∧
      trajectory (fun j => (bits p j : ZMod 2)) (ρ 1 p) 1 =
        trajectory (fun j => (bits p' j : ZMod 2)) (ρ 1 p') 1 := by
  rw [source_kernel 1 r hr]
  have initial :
      ρ 1 p' - ρ 1 p =
        (-3 * ((bits p' 0 : ZMod 2) - bits p 0),
          2 * ((bits p' 0 : ZMod 2) - bits p 0)) ↔
      trajectory (fun j => (bits p j : ZMod 2)) (ρ 1 p) 1 =
        trajectory (fun j => (bits p' j : ZMod 2)) (ρ 1 p') 1 := by
    simp only [trajectory, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
    simp only [CharTwo.two_eq_zero, CharTwo.neg_eq,
      show (3 : ZMod 2) = 1 by decide, one_mul, zero_mul]
    constructor
    · rintro ⟨hx, hy⟩
      constructor
      · linear_combination hx - hy
      · linear_combination -hx
    · rintro ⟨hx, hy⟩
      constructor
      · linear_combination -hy
      · linear_combination -hx - hy
  rw [initial]
  constructor
  · rintro ⟨hz, hf⟩
    refine ⟨?_, hz⟩
    intro j hj hbound
    apply bit_eq_mod_two
    have he := hf (j - 1) (by omega)
    have he' : (bits p' j : ZMod 2) - bits p j = 0 := by
      simpa only [CharTwo.two_eq_zero, zero_mul, zero_add,
        Nat.sub_add_cancel hj] using he
    exact (sub_eq_zero.mp he').symm
  · rintro ⟨hb, hz⟩
    refine ⟨hz, ?_⟩
    intro j hj
    simp [hb (j + 1) (by omega) (by omega)]

/-- The complete finite kernel, its boundary cases, and exact short-horizon data. -/
theorem result :
    (∀ (m r : ℕ), 1 ≤ r → ∀ p p' : Source,
      scalarTrace m r p = scalarTrace m r p' ↔
        ρ m p' - ρ m p =
          (-3 * ((bits p' 0 : ZMod (m + 1)) - bits p 0),
            2 * ((bits p' 0 : ZMod (m + 1)) - bits p 0)) ∧
        ∀ j, j + 2 ≤ r →
          2 * ((bits p' j : ZMod (m + 1)) - bits p j) +
            ((bits p' (j + 1) : ZMod (m + 1)) - bits p (j + 1)) = 0) ∧
    (∀ (m : ℕ) (p p' : Source),
      scalarTrace m 0 p = scalarTrace m 0 p' ↔ quantity (ρ m p) = quantity (ρ m p')) ∧
    (∀ (r : ℕ) (p p' : Source), scalarTrace 0 r p = scalarTrace 0 r p') ∧
    (∀ (m : ℕ) (p : Source),
      ρ m p =
        (2 * scalarTrace m 1 p 0 - 3 * (scalarTrace m 1 p 1 + bits p 0),
          -scalarTrace m 1 p 0 + 2 * (scalarTrace m 1 p 1 + bits p 0))) ∧
    (∀ (m r : ℕ), 3 ≤ m + 1 → 2 ≤ r → ∀ p p' : Source,
      scalarTrace m r p = scalarTrace m r p' ↔
        (∀ j, j < r → p.1.val j = p'.1.val j) ∧ ρ m p = ρ m p') ∧
    (∀ (r : ℕ), 1 ≤ r → ∀ p p' : Source,
      scalarTrace 1 r p = scalarTrace 1 r p' ↔
        (∀ j, 1 ≤ j → j < r → p.1.val j = p'.1.val j) ∧
        trajectory (fun j => (bits p j : ZMod 2)) (ρ 1 p) 1 =
          trajectory (fun j => (bits p' j : ZMod 2)) (ρ 1 p') 1) ∧
    (∀ p : Source,
      trajectory (fun j => (bits p j : ZMod 2)) (ρ 1 p) 1 =
        (scalarTrace 1 1 p 0 - scalarTrace 1 1 p 1, scalarTrace 1 1 p 1)) ∧
    (∀ (r : ℕ), 1 ≤ r → ∀ p p' : Source,
      scalarTrace 1 r p = scalarTrace 1 r p' →
        ρ 1 p' - ρ 1 p = ((bits p' 0 : ZMod 2) - bits p 0, 0)) ∧
    (∀ (r : ℕ), 1 ≤ r → ∀ p p' : Source,
      ρ 1 p = ρ 1 p' → scalarTrace 1 r p = scalarTrace 1 r p' →
        p.1.val 0 = p'.1.val 0) ∧
    (∀ (m r : ℕ) (p p' : Source),
      p.1 = p'.1 → ρ m p = ρ m p' → scalarTrace m r p = scalarTrace m r p') := by
  refine ⟨source_kernel, ?_, ?_, ?_, large_modulus_kernel, parity_kernel, ?_, ?_, ?_, ?_⟩
  · intro m p p'
    constructor
    · exact fun h => congrFun h 0
    · intro h
      funext j
      have hj : j.val = 0 := by omega
      simpa [scalarTrace, hj, trajectory] using h
  · intro r p p'
    letI : Subsingleton (ZMod (0 + 1)) := (ZMod.subsingleton_iff.mpr rfl)
    funext j
    exact Subsingleton.elim _ _
  · intro m p
    apply Prod.ext <;> simp only [scalarTrace, trajectory, quantity, Fin.val_zero,
      Fin.val_one] <;> ring
  · intro p
    apply Prod.ext <;> simp only [scalarTrace, trajectory, quantity, Fin.val_zero,
      Fin.val_one] <;> simp only [CharTwo.two_eq_zero, CharTwo.neg_eq,
        show (3 : ZMod 2) = 1 by decide, zero_mul, one_mul, sub_zero, zero_add] <;> ring
  · intro r hr p p' h
    have hz := ((source_kernel 1 r hr p p').mp h).1
    simpa only [CharTwo.two_eq_zero, CharTwo.neg_eq,
      show (3 : ZMod 2) = 1 by decide, zero_mul, one_mul] using hz
  · intro r hr p p' hz h
    have hv := ((source_kernel 1 r hr p p').mp h).1
    have hx := congrArg Prod.fst hv
    rw [hz, sub_self] at hx
    simp only [CharTwo.neg_eq, show (3 : ZMod 2) = 1 by decide, one_mul] at hx
    apply bit_eq_mod_two
    exact (sub_eq_zero.mp hx.symm).symm
  · intro m r p p' hbits hz
    unfold scalarTrace
    dsimp only at hz
    rw [hbits, hz]

end D5.S3.Arith.FibonacciAtomic.FiniteScalarTraceKernel

#print axioms D5.S3.Arith.FibonacciAtomic.FiniteScalarTraceKernel.result
