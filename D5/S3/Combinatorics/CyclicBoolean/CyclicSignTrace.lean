/- GID: D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CyclicBoolean/CyclicSignTrace
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Odd cyclic Boolean chi, its explicit inverse, and integer cyclic sign traces. -/

import D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Cyclic Boolean maps and the ordered sign-matrix model -/

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace

open D5.S3.QuantumBounds.MerminMeasurementDependence (bit_cases)

abbrev Word (n : ℕ) := ZMod n → ZMod 2

/-- The forward cyclic Boolean map, with repeated indices identified. -/
def chi {n : ℕ} (x : Word n) : Word n :=
  fun i => x i + x (i + 2) + x (i + 1) * x (i + 2)

/-- Integer signs of binary exponents. -/
def sign (z : ZMod 2) : ℤ := (-1) ^ z.val

/-- The source matrix at cyclic index k; its rows and columns are the two field elements. -/
def sourceMatrix {n : ℕ} (b a : Word n) (k : ZMod n) :
    Matrix (ZMod 2) (ZMod 2) ℤ :=
  fun s t => sign ((a k + a (k - 2) + b k) * s + a (k - 1) * s * t)

/-- The literal integer trace of the product in increasing representative order. -/
def sourceTrace {n : ℕ} (b a : Word n) : ℤ :=
  Matrix.trace (List.ofFn (fun k : Fin n => sourceMatrix b a (k.val : ZMod n))).prod

def traceSupport {n : ℕ} (b : Word n) : Set (Word n) :=
  {a | sourceTrace b a ≠ 0}

/-- The full positive odd-length question, without a support nonemptiness premise. -/
def claim : Prop :=
  ∀ m : ℕ, ∀ b : Word (2 * m + 1), b ≠ 0 →
    2 * m ≤ Module.finrank (ZMod 2)
      (affineSpan (ZMod 2) (traceSupport b)).direction

/-- The alternating product in the inverse formula. -/
def alternatingPrefix {n : ℕ} (y : Word n) (i : ZMod n) (t : ℕ) : ZMod 2 :=
  ∏ r ∈ Finset.range t, (1 + y (i + (2 * r + 1 : ℕ)))

/-- The truncated inverse polynomial at odd length 2m+1. -/
def inverse (m : ℕ) (y : Word (2 * m + 1)) : Word (2 * m + 1) :=
  fun i => ∑ r ∈ Finset.range (m + 1), alternatingPrefix y i r * y (i + (2 * r : ℕ))

private theorem bit_mul_one {a b : ZMod 2} (h : a * b = 1) : a = 1 ∧ b = 1 := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    norm_num at h <;> constructor <;> rfl

private theorem chi_recurrence {n : ℕ} (x : Word n) (i : ZMod n) :
    x i = chi x i + (1 + chi x (i + 1)) * x (i + 2) := by
  have hi : i + 1 + 1 = i + 2 := by ring
  have hi' : i + 1 + 2 = i + 3 := by ring
  simp only [chi, hi, hi']
  rcases bit_cases (x i) with h0 | h0 <;>
    rcases bit_cases (x (i + 1)) with h1 | h1 <;>
    rcases bit_cases (x (i + 2)) with h2 | h2 <;>
    rcases bit_cases (x (i + 3)) with h3 | h3 <;>
    simp [h0, h1, h2, h3, show (1 : ZMod 2) + 1 = 0 by decide]

private theorem recurrence_iterate {n : ℕ} (x : Word n) (i : ZMod n) (t : ℕ) :
    x i = (∑ r ∈ Finset.range t, alternatingPrefix (chi x) i r * chi x (i + (2 * r : ℕ))) +
      alternatingPrefix (chi x) i t * x (i + (2 * t : ℕ)) := by
  induction t with
  | zero => simp [alternatingPrefix]
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have hp : alternatingPrefix (chi x) i (t + 1) =
        alternatingPrefix (chi x) i t * (1 + chi x (i + (2 * t + 1 : ℕ))) := by
      simp [alternatingPrefix, Finset.prod_range_succ]
    rw [hp]
    have hr := chi_recurrence x (i + (2 * t : ℕ))
    have h1 : i + (2 * t : ℕ) + 1 = i + (2 * t + 1 : ℕ) := by push_cast; ring
    have h2 : i + (2 * t : ℕ) + 2 = i + (2 * (t + 1) : ℕ) := by push_cast; ring
    rw [h1, h2] at hr
    rw [ih]
    rw [hr]
    ring

private theorem twice_half (m : ℕ) :
    (2 : ZMod (2 * m + 1)) * (m + 1 : ℕ) = 1 := by
  have h := ZMod.natCast_self (2 * m + 1)
  push_cast at h ⊢
  linear_combination h

private theorem step_two_reaches (m : ℕ) (i k : ZMod (2 * m + 1)) :
    ∃ r : ℕ, i + (2 * r : ℕ) = k := by
  let a : ZMod (2 * m + 1) := (m + 1 : ℕ) * (k - i)
  refine ⟨a.val, ?_⟩
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  dsimp [a]
  rw [← mul_assoc, twice_half, one_mul]
  ring

private theorem chi_zero_fiber (m : ℕ) (x : Word (2 * m + 1))
    (h : chi x = 0) : x = 0 := by
  have step (i : ZMod (2 * m + 1)) : x i = x (i + 2) := by
    have hr := chi_recurrence x i
    simpa [h] using hr
  have orbit (i : ZMod (2 * m + 1)) (r : ℕ) : x (i + (2 * r : ℕ)) = x i := by
    induction r with
    | zero => simp
    | succ r ih =>
      have he : i + (2 * (r + 1) : ℕ) = (i + (2 * r : ℕ)) + 2 := by push_cast; ring
      rw [he, ← step, ih]
  have constant (i k : ZMod (2 * m + 1)) : x k = x i := by
    obtain ⟨r, hr⟩ := step_two_reaches m i k
    rw [← hr]
    exact orbit i r
  funext i
  have hh := congrFun h i
  simp only [chi, Pi.zero_apply] at hh
  rw [constant i (i + 1), constant i (i + 2)] at hh
  rcases bit_cases (x i) with hx | hx
  · exact hx
  · simp [hx, show (1 : ZMod 2) + 1 = 0 by decide] at hh



private theorem truncation_tail (m : ℕ) (x : Word (2 * m + 1))
    (i : ZMod (2 * m + 1)) :
    alternatingPrefix (chi x) i (m + 1) * x (i + (2 * (m + 1) : ℕ)) = 0 := by
  classical
  let y := chi x
  let j := i + 1
  by_contra htail
  have htail1 : alternatingPrefix y i (m + 1) *
      x (i + (2 * (m + 1) : ℕ)) = 1 := by
    rcases bit_cases (alternatingPrefix y i (m + 1) *
      x (i + (2 * (m + 1) : ℕ))) with h | h
    · exact (htail h).elim
    · exact h
  obtain ⟨hp, hx⟩ := bit_mul_one htail1
  have hidx : i + (2 * (m + 1) : ℕ) = j := by
    dsimp [j]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using congrArg (fun t => i + t) (twice_half m)
  have hxj : x j = 1 := by simpa only [hidx] using hx
  have hz (r : ℕ) (hr : r ≤ m) : y (j + (2 * r : ℕ)) = 0 := by
    have hpn : alternatingPrefix y i (m + 1) ≠ 0 := by rw [hp]; exact one_ne_zero
    have hf := (Finset.prod_ne_zero_iff.mp hpn) r (Finset.mem_range.mpr (by omega))
    change 1 + y (i + (2 * r + 1 : ℕ)) ≠ 0 at hf
    have he : i + (2 * r + 1 : ℕ) = j + (2 * r : ℕ) := by dsimp [j]; push_cast; ring
    rw [he] at hf
    rcases bit_cases (y (j + (2 * r : ℕ))) with h | h
    · exact h
    · rw [h] at hf
      exact (hf (by decide)).elim
  have hxstep (r : ℕ) (hr : r ≤ m + 1) : x (j + (2 * r : ℕ)) = 1 := by
    induction r with
    | zero => simpa using hxj
    | succ r ih =>
      have hprev : x (j + (2 * r : ℕ)) = 1 := ih (by omega)
      have hc := chi_recurrence x (j + (2 * r : ℕ))
      change x (j + (2 * r : ℕ)) =
        y (j + (2 * r : ℕ)) +
          (1 + y (j + (2 * r : ℕ) + 1)) * x (j + (2 * r : ℕ) + 2) at hc
      rw [hprev, hz r (by omega), zero_add] at hc
      have he : j + (2 * r : ℕ) + 2 = j + (2 * (r + 1) : ℕ) := by push_cast; ring
      rw [he] at hc
      exact (bit_mul_one hc.symm).2
  have hodd (r : ℕ) (hr : r ≤ m) : y (j + (2 * r + 1 : ℕ)) = 0 := by
    have hc := chi_recurrence x (j + (2 * r : ℕ))
    change x (j + (2 * r : ℕ)) =
      y (j + (2 * r : ℕ)) +
        (1 + y (j + (2 * r : ℕ) + 1)) * x (j + (2 * r : ℕ) + 2) at hc
    rw [hxstep r (by omega), hz r hr, zero_add] at hc
    have hh := (bit_mul_one hc.symm).1
    have he : j + (2 * r : ℕ) + 1 = j + (2 * r + 1 : ℕ) := by push_cast; ring
    rw [he] at hh
    exact add_left_cancel (show 1 + y (j + (2 * r + 1 : ℕ)) = 1 + 0 by simpa using hh)
  have hy : y = 0 := by
    funext k
    have hk : j + ((k - j).val : ZMod (2 * m + 1)) = k := by
      rw [ZMod.natCast_zmod_val]; ring
    have hlt := ZMod.val_lt (k - j)
    rcases Nat.even_or_odd (k - j).val with he | ho
    · obtain ⟨r, hr⟩ := he
      have heq : (k - j).val = 2 * r := by omega
      rw [← hk, heq]
      exact hz r (by omega)
    · obtain ⟨r, hr⟩ := ho
      have heq : (k - j).val = 2 * r + 1 := by omega
      rw [← hk, heq]
      exact hodd r (by omega)
  have hxx := chi_zero_fiber m x hy
  have hj0 := congrFun hxx j
  rw [hxj] at hj0
  exact one_ne_zero hj0

/-- The explicit inverse identity at every positive odd length, including one. -/
private theorem inverse_left (m : ℕ) (x : Word (2 * m + 1)) :
    inverse m (chi x) = x := by
  funext i
  have h := recurrence_iterate x i (m + 1)
  rw [truncation_tail, add_zero] at h
  exact h.symm

/-- The forward cyclic map is bijective at every positive odd length. -/
private theorem chi_bijective (m : ℕ) : Function.Bijective (@chi (2 * m + 1)) := by
  apply (Finite.injective_iff_bijective).mp
  exact (show Function.LeftInverse (inverse m) chi from inverse_left m).injective

/-- The explicit polynomial is both a left and a right inverse, at all odd lengths. -/
theorem inverse_spec (m : ℕ) :
    Function.LeftInverse (inverse m) chi ∧ Function.RightInverse (inverse m) chi := by
  refine ⟨inverse_left m, ?_⟩
  exact (show Function.LeftInverse (inverse m) chi from inverse_left m).rightInverse_of_surjective
    (chi_bijective m).surjective



/-- The binary dot product. -/
def dot {n : ℕ} [NeZero n] (a x : Word n) : ZMod 2 := ∑ i, a i * x i

/-- Unnormalized integer Walsh coefficients of a Boolean function. -/
def walsh {n : ℕ} [NeZero n] (f : Word n → ZMod 2) (a : Word n) : ℤ :=
  ∑ x, sign (f x + dot a x)

private theorem sign_add (a b : ZMod 2) : sign (a + b) = sign a * sign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    norm_num [sign, ZMod.val_one_eq_one_mod, ZMod.val_two_eq_two_mod, show (1 : ZMod 2) + 1 = 0 by decide]

private theorem sign_injective : Function.Injective sign := by
  intro a b h
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp_all [sign, ZMod.val_one_eq_one_mod]

private theorem dot_add_right {n : ℕ} [NeZero n] (a x y : Word n) :
    dot a (x + y) = dot a x + dot a y := by
  simp [dot, mul_add, Finset.sum_add_distrib]

private theorem dot_comm {n : ℕ} [NeZero n] (a x : Word n) : dot a x = dot x a := by
  simp only [dot, mul_comm]

private theorem character_sum {n : ℕ} [NeZero n] (x : Word n) :
    (∑ a, sign (dot a x)) = if x = 0 then (Fintype.card (Word n) : ℤ) else 0 := by
  classical
  let ch : AddChar (Word n) ℤ :=
    { toFun := fun a => sign (dot a x)
      map_zero_eq_one' := by simp [dot, sign]
      map_add_eq_mul' := by
        intro a b
        rw [dot_comm (a + b) x, dot_add_right, sign_add, dot_comm x a, dot_comm x b] }
  have he : ch = 0 ↔ x = 0 := by
    constructor
    · intro h
      funext i
      have hi := congrArg (fun c : AddChar (Word n) ℤ => c (Pi.single i 1)) h
      have hs : sign (x i) = sign 0 := by
        simpa [ch, dot, Pi.single_apply, sign] using hi
      exact sign_injective hs
    · intro h
      ext a
      simp [ch, h, dot, sign]
  have hc := AddChar.sum_eq_ite ch
  change (∑ a, sign (dot a x)) = if ch = 0 then _ else _ at hc
  simpa only [he] using hc

/-- Integer Fourier inversion, without normalization or a nonempty-support hypothesis. -/
theorem walsh_inversion {n : ℕ} [NeZero n] (f : Word n → ZMod 2) (y : Word n) :
    (∑ a, walsh f a * sign (dot a y)) =
      (Fintype.card (Word n) : ℤ) * sign (f y) := by
  classical
  unfold walsh
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hxy (x a : Word n) :
      sign (f x + dot a x) * sign (dot a y) =
        sign (f x) * sign (dot a (x + y)) := by
    rw [sign_add, dot_add_right, sign_add]
    ring
  simp_rw [hxy, ← Finset.mul_sum, character_sum]
  have hzero (x : Word n) : x + y = 0 ↔ x = y := by
    constructor
    · intro h
      have hy : y + y = 0 := by ext i; exact CharTwo.add_self_eq_zero _
      exact add_right_cancel (h.trans hy.symm)
    · rintro rfl
      ext i
      exact CharTwo.add_self_eq_zero _
  simp only [hzero]
  simp [mul_comm]

/-- Every Boolean function has at least one nonzero integer Walsh coefficient. -/
theorem walsh_support_nonempty {n : ℕ} [NeZero n] (f : Word n → ZMod 2) :
    ∃ a, walsh f a ≠ 0 := by
  by_contra h
  push Not at h
  have hi := walsh_inversion f 0
  simp only [h, zero_mul, Finset.sum_const_zero] at hi
  have hs : sign (f 0) ≠ 0 := by
    rcases bit_cases (f 0) with hf | hf <;> simp [hf, sign, ZMod.val_one_eq_one_mod]
  exact (mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hs) hi.symm

/-- The component of the explicit inverse associated with an arbitrary mask. -/
def inverseComponent (m : ℕ) (b : Word (2 * m + 1)) :
    Word (2 * m + 1) → ZMod 2 := fun y => dot b (inverse m y)

/-- Reindexing the exact Boolean phase sum uses the proved odd-cycle inverse. -/
theorem inverse_phase_sum (m : ℕ) (b a : Word (2 * m + 1)) :
    (∑ x, sign (dot b x + dot a (chi x))) = walsh (inverseComponent m b) a := by
  classical
  let e : Word (2 * m + 1) ≃ Word (2 * m + 1) :=
    { toFun := chi
      invFun := inverse m
      left_inv := (inverse_spec m).1
      right_inv := (inverse_spec m).2 }
  unfold walsh inverseComponent
  conv_rhs => rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro x _
  simp [e, (inverse_spec m).1 x]



/-- Nonemptiness of the exact cyclic Boolean phase support for every odd length and mask. -/
theorem inverse_phase_support_nonempty (m : ℕ) (b : Word (2 * m + 1)) :
    ∃ a : Word (2 * m + 1), (∑ x, sign (dot b x + dot a (chi x))) ≠ 0 := by
  obtain ⟨a, ha⟩ := walsh_support_nonempty (inverseComponent m b)
  exact ⟨a, by simpa only [inverse_phase_sum] using ha⟩

private theorem sign_mul_eq_self_iff {z : ZMod 2} {q : ℤ} (hq : q ≠ 0) :
    sign z * q = q ↔ z = 0 := by
  constructor
  · intro h
    rcases bit_cases z with rfl | rfl
    · rfl
    · norm_num [sign, ZMod.val_one_eq_one_mod] at h
      have hq0 : q = 0 := by
        linarith
      exact (hq hq0).elim
  · intro hz
    simp [hz, sign]

/-- A Boolean derivative is constant exactly when its Walsh support lies in the
corresponding character level set.  This is the Fourier bridge used before any
affine-hull dimension argument. -/
theorem walsh_constant_derivative_iff {n : ℕ} [NeZero n] (f : Word n → ZMod 2)
    (u : Word n) (c : ZMod 2) :
    (∀ y, f (y + u) + f y = c) ↔
      ∀ a, walsh f a ≠ 0 → dot a u = c := by
  classical
  let e : Word n ≃ Word n :=
    { toFun := fun y => y + u
      invFun := fun y => y + u
      left_inv := by
        intro y
        change (y + u) + u = y
        ext i
        change y i + u i + u i = y i
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      right_inv := by
        intro y
        change (y + u) + u = y
        ext i
        change y i + u i + u i = y i
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero] }
  constructor
  · intro hderiv a hwa
    have hsum : walsh f a = sign (c + dot a u) * walsh f a := by
      have hreindex :
          (∑ y, sign (f y + dot a y)) =
            ∑ y, sign (f (e y) + dot a (e y)) := by
        rw [← Equiv.sum_comp e]
      calc
        walsh f a = ∑ y, sign (f (e y) + dot a (e y)) := by
          unfold walsh
          exact hreindex
        _ =
            ∑ y, sign (c + dot a u) * sign (f y + dot a y) := by
          apply Finset.sum_congr rfl
          intro y hy
          dsimp [e]
          have hxy : f (y + u) + dot a (y + u) =
              (c + dot a u) + (f y + dot a y) := by
            calc
              f (y + u) + dot a (y + u) =
                  (f (y + u) + f y) + (f y + dot a (y + u)) := by
                    ring_nf
                    have htwo : (2 : ZMod 2) = 0 := by decide
                    rw [htwo, mul_zero, add_zero]
              _ = c + (f y + dot a (y + u)) := by rw [hderiv y]
              _ = (c + dot a u) + (f y + dot a y) := by
                rw [dot_add_right]
                ring
          rw [hxy, sign_add]
        _ = sign (c + dot a u) * walsh f a := by
          unfold walsh
          exact (Finset.mul_sum (s := Finset.univ)
            (f := fun y : Word n => sign (f y + dot a y)) (sign (c + dot a u))).symm
    have hs : sign (c + dot a u) * walsh f a = walsh f a := hsum.symm
    have hz : c + dot a u = 0 := (sign_mul_eq_self_iff hwa).mp hs
    apply add_left_cancel (a := c)
    calc
      c + dot a u = 0 := hz
      _ = c + c := (CharTwo.add_self_eq_zero c).symm
  · intro hsupport y
    have hinv := walsh_inversion f (y + u)
    have hinv' := walsh_inversion f y
    have hterms (a : Word n) :
        walsh f a * sign (dot a (y + u)) =
          sign c * (walsh f a * sign (dot a y)) := by
      by_cases hwa : walsh f a = 0
      · simp [hwa]
      · rw [dot_add_right, sign_add]
        rw [hsupport a hwa]
        simp [sign_add, mul_assoc, mul_left_comm, mul_comm]
    simp_rw [hterms] at hinv
    have hfac :
        (∑ a, sign c * (walsh f a * sign (dot a y))) =
          sign c * (∑ a, walsh f a * sign (dot a y)) := by
      exact (Finset.mul_sum (s := Finset.univ)
        (f := fun a : Word n => walsh f a * sign (dot a y)) (sign c)).symm
    rw [hfac, hinv'] at hinv
    have hcard : (Fintype.card (Word n) : ℤ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hinvEq :
        (Fintype.card (Word n) : ℤ) * sign (f (y + u)) =
          (Fintype.card (Word n) : ℤ) * (sign c * sign (f y)) := by
      calc
        (Fintype.card (Word n) : ℤ) * sign (f (y + u)) =
            sign c * ((Fintype.card (Word n) : ℤ) * sign (f y)) := by
          simpa only [hinv]
        _ = (Fintype.card (Word n) : ℤ) * (sign c * sign (f y)) := by ring
    have hsign : sign (f (y + u)) = sign c * sign (f y) :=
      mul_left_cancel₀ hcard hinvEq
    apply sign_injective
    calc
      sign (f (y + u) + f y) = sign (f (y + u)) * sign (f y) := by
        rw [sign_add]
      _ = (sign c * sign (f y)) * sign (f y) := by rw [hsign]
      _ = sign c := by
        rw [mul_assoc, ← sign_add, CharTwo.add_self_eq_zero]
        simp [sign]

/-! The next definitions package the nondegenerate binary dot pairing.  The
constant-derivative directions are represented as the comap of the dual
annihilator of the Walsh-support affine direction; the theorem below proves
that this representation is exact before any coefficient classification. -/

/-- The linear map sending a direction to its dot-product functional. -/
def dotDual {n : ℕ} [NeZero n] : Word n →ₗ[ZMod 2] Module.Dual (ZMod 2) (Word n) :=
  { toFun := fun u =>
      { toFun := fun a => dot a u
        map_add' := by
          intro a b
          simp [dot, add_mul, Finset.sum_add_distrib]
        map_smul' := by
          intro r a
          simp [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm,
            Finset.mul_sum] }
    map_add' := by
      intro u v
      apply LinearMap.ext
      intro a
      change dot a (u + v) = dot a u + dot a v
      rw [dot_add_right]
    map_smul' := by
      intro r u
      apply LinearMap.ext
      intro a
      change dot a (r • u) = r * dot a u
      simp [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm,
        Finset.mul_sum] }

private theorem dotDual_injective {n : ℕ} [NeZero n] :
    Function.Injective (dotDual (n := n)) := by
  intro u v huv
  funext i
  have hi := congrArg (fun ℓ : Module.Dual (ZMod 2) (Word n) =>
    ℓ (Pi.single i 1)) huv
  change dot (Pi.single i 1) u = dot (Pi.single i 1) v at hi
  simpa [dot, Pi.single_apply] using hi

/-- The binary dot pairing identifies the word space with its algebraic dual. -/
  noncomputable def dotDualEquiv {n : ℕ} [NeZero n] :
    Word n ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Word n) :=
  LinearMap.linearEquivOfInjective (dotDual (n := n)) (dotDual_injective (n := n))
    (Subspace.dual_finrank_eq (K := ZMod 2) (V := Word n)).symm

/-- Direction of the affine span of the nonzero Walsh support. -/
def walshSupportDirection {n : ℕ} [NeZero n] (f : Word n → ZMod 2) :
    Subspace (ZMod 2) (Word n) :=
  (affineSpan (ZMod 2) {a | walsh f a ≠ 0}).direction

/-- The canonical submodule of constant-character derivative directions. -/
def constantDerivativeSubmodule {n : ℕ} [NeZero n] (f : Word n → ZMod 2) :
    Subspace (ZMod 2) (Word n) :=
  Submodule.comap (dotDual (n := n)) (walshSupportDirection f).dualAnnihilator

/-- Constant derivatives are the dot-annihilator of Walsh-support differences,
and the two complementary directions have the exact finite-dimensional sum. -/
theorem constantDerivative_affineSpan_duality {n : ℕ} [NeZero n]
    (f : Word n → ZMod 2) :
    (∀ u, u ∈ constantDerivativeSubmodule f ↔
      ∃ c, ∀ y, f (y + u) + f y = c) ∧
      Module.finrank (ZMod 2) (constantDerivativeSubmodule f) +
          Module.finrank (ZMod 2) (walshSupportDirection f) =
        Module.finrank (ZMod 2) (Word n) := by
  classical
  let S : Set (Word n) := {a | walsh f a ≠ 0}
  let A : Subspace (ZMod 2) (Word n) := walshSupportDirection f
  obtain ⟨a₀, ha₀⟩ := walsh_support_nonempty f
  have ha₀S : a₀ ∈ S := ha₀
  have hdir : A = Submodule.span (ZMod 2) ((fun a : Word n => a - a₀) '' S) := by
    dsimp [A, walshSupportDirection, S]
    rw [direction_affineSpan,
      vectorSpan_eq_span_vsub_set_right (ZMod 2) (show a₀ ∈ {a | walsh f a ≠ 0} from ha₀)]
    congr 1
  have dot_add_left (x y z : Word n) : dot (x + y) z = dot x z + dot y z := by
    simp [dot, add_mul, Finset.sum_add_distrib]
  have dot_smul_left (r : ZMod 2) (x z : Word n) :
      dot (r • x) z = r * dot x z := by
    simp [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_comm,
      mul_left_comm]
  have hdual (u : Word n) :
      dotDual (n := n) u ∈ A.dualAnnihilator ↔
        ∀ a ∈ S, dot a u = dot a₀ u := by
    rw [hdir, Submodule.mem_dualAnnihilator]
    constructor
    · intro h a ha
      have hz := h (a - a₀)
        (Submodule.subset_span ⟨a, ha, by rfl⟩)
      change dot (a - a₀) u = 0 at hz
      have hdot : dot (a - a₀) u = dot a u + dot a₀ u := by
        rw [ZModModule.sub_eq_add]
        exact dot_add_left a a₀ u
      rw [hdot] at hz
      apply sub_eq_zero.mp
      simpa [ZModModule.sub_eq_add] using hz
    · intro h z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨a, ha, rfl⟩ := hz
          change dot (a - a₀) u = 0
          have hdot : dot (a - a₀) u = dot a u + dot a₀ u := by
            rw [ZModModule.sub_eq_add]
            exact dot_add_left a a₀ u
          rw [hdot, h a ha]
          exact CharTwo.add_self_eq_zero _
      | zero => simp [dot]
      | add x y hx hy =>
          change (dotDual (n := n) u) (x + y) = 0
          simp_all [map_add]
      | smul r x hx =>
          change (dotDual (n := n) u) (r • x) = 0
          simp_all [map_smul]
  have hmem (u : Word n) :
      u ∈ constantDerivativeSubmodule f ↔
        ∃ c, ∀ y, f (y + u) + f y = c := by
    change dotDual (n := n) u ∈ A.dualAnnihilator ↔ _
    constructor
    · intro hu
      refine ⟨dot a₀ u, ?_⟩
      apply (walsh_constant_derivative_iff f u (dot a₀ u)).mpr
      intro a ha
      exact (hdual u).mp hu a ha
    · rintro ⟨c, hc⟩
      apply (hdual u).mpr
      intro a ha
      have ha' := (walsh_constant_derivative_iff f u c).mp hc a ha
      have ha₀' := (walsh_constant_derivative_iff f u c).mp hc a₀ ha₀S
      exact ha'.trans ha₀'.symm
  have hmap :
      Submodule.map (dotDualEquiv (n := n)).toLinearMap (constantDerivativeSubmodule f) =
        A.dualAnnihilator := by
    ext φ
    constructor
    · rintro ⟨u, hu, rfl⟩
      change dotDual (n := n) u ∈ A.dualAnnihilator at hu
      change dotDual (n := n) u ∈ A.dualAnnihilator
      exact hu
    · intro hφ
      refine ⟨(dotDualEquiv (n := n)).symm φ, ?_, ?_⟩
      · change dotDual (n := n) ((dotDualEquiv (n := n)).symm φ) ∈ A.dualAnnihilator
        have heq := (dotDualEquiv (n := n)).apply_symm_apply φ
        change dotDual (n := n) ((dotDualEquiv (n := n)).symm φ) = φ at heq
        rw [heq]
        exact hφ
      · simp
  refine ⟨hmem, ?_⟩
  have hfin :
      Module.finrank (ZMod 2) (constantDerivativeSubmodule f) =
        Module.finrank (ZMod 2) A.dualAnnihilator := by
    calc
      Module.finrank (ZMod 2) (constantDerivativeSubmodule f) =
          Module.finrank (ZMod 2)
            (Submodule.map (dotDualEquiv (n := n)).toLinearMap
              (constantDerivativeSubmodule f)) :=
        ((dotDualEquiv (n := n)).finrank_map_eq _).symm
      _ = Module.finrank (ZMod 2) A.dualAnnihilator := by rw [hmap]
  calc
    Module.finrank (ZMod 2) (constantDerivativeSubmodule f) +
        Module.finrank (ZMod 2) (walshSupportDirection f) =
      Module.finrank (ZMod 2) A.dualAnnihilator + Module.finrank (ZMod 2) A := by
        rw [hfin]
    _ = Module.finrank (ZMod 2) (Word n) := by
      rw [add_comm, Subspace.finrank_add_finrank_dualAnnihilator_eq]

set_option backward.isDefEq.respectTransparency false in
private theorem ordered_product_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (M : Fin (r + 1) → Matrix ι ι ℤ) (i j : ι) :
    (List.ofFn M).prod i j =
      ∑ x : Fin r → ι, ∏ k : Fin (r + 1),
        M k (Fin.cons (α := fun _ => ι) i x k) (Fin.snoc (α := fun _ => ι) x j k) := by
  classical
  induction r generalizing i j with
  | zero => simp [List.ofFn_succ, Fin.prod_univ_succ, Fin.snoc_zero]
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    simp_rw [ih, Finset.mul_sum]
    trans ∑ p : ι × (Fin r → ι),
      M 0 i p.1 * ∏ k : Fin (r + 1),
        M k.succ (Fin.cons (α := fun _ => ι) p.1 p.2 k)
          (Fin.snoc (α := fun _ => ι) p.2 j k)
    · exact (Fintype.sum_prod_type (fun p : ι × (Fin r → ι) =>
        M 0 i p.1 * ∏ k : Fin (r + 1),
          M k.succ (Fin.cons (α := fun _ => ι) p.1 p.2 k)
            (Fin.snoc (α := fun _ => ι) p.2 j k))).symm
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r + 1) => ι))]
    apply Finset.sum_congr rfl
    intro x _
    change M 0 i x.1 * (∏ k : Fin (r + 1),
      M k.succ (Fin.cons (α := fun _ => ι) x.1 x.2 k)
        (Fin.snoc (α := fun _ => ι) x.2 j k)) =
      ∏ k : Fin (r + 1 + 1),
        M k (Fin.cons (α := fun _ => ι) i (Fin.cons x.1 x.2) k)
          (Fin.snoc (α := fun _ => ι) (Fin.cons x.1 x.2) j k)
    rw [← Fin.cons_snoc_eq_snoc_cons]
    conv_rhs => rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]

set_option backward.isDefEq.respectTransparency false in
private theorem cyclic_snoc {r : ℕ} (x : Fin (r + 1) → ZMod 2) (k : Fin (r + 1)) :
    Fin.snoc (α := fun _ => ZMod 2) (Fin.tail x) (x 0) k = x (k + (1 : Fin (r + 1))) := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp
  · simp [Fin.tail]

set_option backward.isDefEq.respectTransparency false in
private theorem ordered_trace_paths (r : ℕ)
    (M : Fin (r + 1) → Matrix (ZMod 2) (ZMod 2) ℤ) :
    Matrix.trace (List.ofFn M).prod =
      ∑ x : Fin (r + 1) → ZMod 2, ∏ k : Fin (r + 1), M k (x k) (x (k + (1 : Fin (r + 1)))) := by
  classical
  change (∑ i, (List.ofFn M).prod i i) = _
  calc
    _ = ∑ i, ∑ x : Fin r → ZMod 2, ∏ k : Fin (r + 1),
        M k (Fin.cons (α := fun _ => ZMod 2) i x k)
          (Fin.snoc (α := fun _ => ZMod 2) x i k) := by
      apply Finset.sum_congr rfl
      intro i _
      exact ordered_product_entry r M i i
    _ = ∑ p : ZMod 2 × (Fin r → ZMod 2), ∏ k : Fin (r + 1),
        M k (Fin.cons (α := fun _ => ZMod 2) p.1 p.2 k)
          (Fin.snoc (α := fun _ => ZMod 2) p.2 p.1 k) :=
      (Fintype.sum_prod_type (fun p : ZMod 2 × (Fin r → ZMod 2) =>
        ∏ k : Fin (r + 1), M k
          (Fin.cons (α := fun _ => ZMod 2) p.1 p.2 k)
          (Fin.snoc (α := fun _ => ZMod 2) p.2 p.1 k))).symm
    _ = _ := by
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r + 1) => ZMod 2))]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.prod_congr rfl
      intro k _
      change M k (Fin.cons (α := fun _ => ZMod 2) x.1 x.2 k)
          (Fin.snoc (α := fun _ => ZMod 2) x.2 x.1 k) =
        M k (Fin.cons (α := fun _ => ZMod 2) x.1 x.2 k)
          (Fin.cons (α := fun _ => ZMod 2) x.1 x.2 (k + 1))
      apply congrArg (M k (Fin.cons (α := fun _ => ZMod 2) x.1 x.2 k))
      simpa only [Fin.tail_cons, Fin.cons_zero] using
        cyclic_snoc (Fin.cons (α := fun _ => ZMod 2) x.1 x.2) k

private theorem sign_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | @insert i s hi ih => simp [hi, sign_add, ih]

private theorem cyclic_exponent {n : ℕ} [NeZero n] (b a x : Word n) :
    (∑ k, ((a k + a (k - 2) + b k) * x k + a (k - 1) * x k * x (k + 1))) =
      dot b x + dot a (chi x) := by
  classical
  have h2 : (∑ k, a (k - 2) * x k) = ∑ i, a i * x (i + 2) := by
    simpa using (Equiv.sum_comp (Equiv.addRight (2 : ZMod n))
      (fun k => a (k - 2) * x k)).symm
  have h1 : (∑ k, a (k - 1) * x k * x (k + 1)) =
      ∑ i, a i * x (i + 1) * x (i + 2) := by
    have hi (i : ZMod n) : i + 1 + 1 = i + 2 := by ring
    simpa only [Equiv.coe_addRight, add_sub_cancel_right, hi] using
      (Equiv.sum_comp (Equiv.addRight (1 : ZMod n))
        (fun k => a (k - 1) * x k * x (k + 1))).symm
  simp only [add_mul, Finset.sum_add_distrib, dot, chi, mul_add]
  rw [h2, h1]
  simp only [mul_assoc]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Expanding the literal ordered matrix trace gives the exact cyclic Boolean
phase sum, for every positive length, including coincident indices at length one. -/
theorem sourceTrace_eq_phase_sum {n : ℕ} [NeZero n] (b a : Word n) :
    sourceTrace b a = ∑ x, sign (dot b x + dot a (chi x)) := by
  classical
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ r =>
    rw [sourceTrace, ordered_trace_paths]
    let e : Word (r + 1) ≃ (Fin (r + 1) → ZMod 2) :=
      Equiv.arrowCongr (ZMod.finEquiv (r + 1)).symm.toEquiv (Equiv.refl _)
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro x _
    have he (k : Fin (r + 1)) : e x k = x ((ZMod.finEquiv (r + 1)) k) := rfl
    simp only [he, sourceMatrix]
    have hc (k : Fin (r + 1)) :
        (k.val : ZMod (r + 1)) = (ZMod.finEquiv (r + 1)) k := by
      change ((k.val : ZMod (r + 1))) = k
      exact ZMod.natCast_zmod_val ((ZMod.finEquiv (r + 1)) k)
    simp only [hc, map_add, map_one]
    rw [← sign_sum]
    apply congrArg sign
    rw [← cyclic_exponent b a x]
    exact Equiv.sum_comp (ZMod.finEquiv (r + 1)).toEquiv
      (fun k => (a k + a (k - 2) + b k) * x k + a (k - 1) * x k * x (k + 1))

/-- A squarefree monomial, evaluated on an actual binary word. -/
def booleanMonomial {n : ℕ} (s : Finset (ZMod n)) (z : Word n) : ZMod 2 :=
  ∏ i ∈ s, z i

/-- The indicator word of a finite set of cyclic coordinates. -/
noncomputable def indicatorWord {n : ℕ} (s : Finset (ZMod n)) : Word n :=
  fun i => if i ∈ s then 1 else 0

/-- Boolean coefficient extraction from function values, rather than a formal
polynomial whose evaluation might have a kernel. -/
noncomputable def booleanCoeff {n : ℕ} (f : Word n → ZMod 2)
    (s : Finset (ZMod n)) : ZMod 2 :=
  ∑ t ∈ s.powerset, f (indicatorWord t)

private theorem monomial_indicator {n : ℕ} (s t : Finset (ZMod n)) :
    booleanMonomial s (indicatorWord t) = if s ⊆ t then 1 else 0 := by
  classical
  by_cases h : s ⊆ t
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [indicatorWord, h hi]
  · obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero hi (by simp [indicatorWord, hit])

private theorem subset_parity {n : ℕ} (s t : Finset (ZMod n)) :
    (∑ v ∈ s.powerset, if t ⊆ v then (1 : ZMod 2) else 0) =
      if s = t then 1 else 0 := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty =>
      simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.subset_empty]
      simp only [eq_comm]
  | @insert i s hi ih =>
      rw [Finset.sum_powerset_insert hi]
      by_cases hit : i ∈ t
      · have hz : (∑ v ∈ s.powerset, if t ⊆ v then (1 : ZMod 2) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro v hv
          have hiv : i ∉ v := fun h => hi ((Finset.mem_powerset.mp hv) h)
          simp [show ¬t ⊆ v from fun h => hiv (h hit)]
        rw [hz, zero_add]
        simp_rw [Finset.subset_insert_iff]
        rw [ih]
        have he : s = t.erase i ↔ insert i s = t := by
          constructor
          · intro h
            rw [h, Finset.insert_erase hit]
          · intro h
            rw [← h, Finset.erase_insert hi]
        simp only [he]
      · have he (v : Finset (ZMod n)) : t ⊆ insert i v ↔ t ⊆ v :=
          Finset.subset_insert_iff_of_notMem hit
        simp_rw [he]
        rw [CharTwo.add_self_eq_zero]
        simp [show insert i s ≠ t from fun h => hit (h ▸ Finset.mem_insert_self i s)]

private theorem coeff_monomial {n : ℕ} (s t : Finset (ZMod n)) :
    booleanCoeff (booleanMonomial t) s = if s = t then 1 else 0 := by
  classical
  simp only [booleanCoeff, monomial_indicator]
  exact subset_parity s t

private theorem coeff_add {n : ℕ} (f g : Word n → ZMod 2)
    (s : Finset (ZMod n)) :
    booleanCoeff (fun z => f z + g z) s = booleanCoeff f s + booleanCoeff g s := by
  classical
  simp [booleanCoeff, Finset.sum_add_distrib]

private theorem coeff_sum {n : ℕ} {ι : Type*} (v : Finset ι)
    (f : ι → Word n → ZMod 2) (s : Finset (ZMod n)) :
    booleanCoeff (fun z => ∑ i ∈ v, f i z) s =
      ∑ i ∈ v, booleanCoeff (f i) s := by
  classical
  simp only [booleanCoeff]
  exact Finset.sum_comm

private theorem coeff_mul {n : ℕ} (a : ZMod 2) (f : Word n → ZMod 2)
    (s : Finset (ZMod n)) :
    booleanCoeff (fun z => a * f z) s = a * booleanCoeff f s := by
  classical
  simp [booleanCoeff, Finset.mul_sum]

private theorem coeff_constant {n : ℕ} (a : ZMod 2) (s : Finset (ZMod n))
    (hs : s.Nonempty) : booleanCoeff (fun _ : Word n => a) s = 0 := by
  have he : (fun _ : Word n => a) = fun z => a * booleanMonomial ∅ z := by
    funext z
    simp [booleanMonomial]
  rw [he, coeff_mul, coeff_monomial]
  simp [Finset.nonempty_iff_ne_empty.mp hs]

/-- The cyclic variable set in an alternating prefix. -/
def prefixVariables {n : ℕ} (i : ZMod n) (r : ℕ) : Finset (ZMod n) :=
  (Finset.range r).image (fun t => i + (2 * t + 1 : ℕ))

private theorem bit_square (a : ZMod 2) : a * a = a := by
  rcases bit_cases a with rfl | rfl <;> decide

private theorem monomial_insert {n : ℕ} (s : Finset (ZMod n))
    (i : ZMod n) (z : Word n) :
    booleanMonomial (insert i s) z = z i * booleanMonomial s z := by
  classical
  by_cases hi : i ∈ s
  · rw [Finset.insert_eq_of_mem hi]
    have hp : booleanMonomial s z = z i * booleanMonomial (s.erase i) z := by
      exact (Finset.mul_prod_erase s z hi).symm
    rw [hp, ← mul_assoc, bit_square]
  · exact Finset.prod_insert hi

private theorem prefix_monomial {n : ℕ} (z : Word n) (i : ZMod n) (r : ℕ) :
    alternatingPrefix (1 + z) i r = booleanMonomial (prefixVariables i r) z := by
  classical
  induction r with
  | zero => simp [alternatingPrefix, prefixVariables, booleanMonomial]
  | succ r ih =>
      have he : prefixVariables i (r + 1) = insert (i + (2 * r + 1 : ℕ))
          (prefixVariables i r) := by
        simp [prefixVariables, Finset.range_add_one, Finset.image_insert]
      rw [he, monomial_insert]
      simp only [alternatingPrefix, Finset.prod_range_succ] at ih ⊢
      rw [ih]
      have hz : 1 + (1 + z) (i + (2 * r + 1 : ℕ)) = z (i + (2 * r + 1 : ℕ)) := by
        change 1 + (1 + z _) = _
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      rw [hz, mul_comm]

private theorem shifted_inverse_expansion (m : ℕ) (b z : Word (2 * m + 1)) :
    inverseComponent m b (1 + z) =
      ∑ i, ∑ r ∈ Finset.range (m + 1), b i *
        (booleanMonomial (prefixVariables i r) z +
          booleanMonomial (insert (i + (2 * r : ℕ)) (prefixVariables i r)) z) := by
  classical
  simp only [inverseComponent, dot, inverse, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  rw [prefix_monomial, monomial_insert]
  change b i * (booleanMonomial _ z * (1 + z _)) = _
  ring

/-- Extract the coefficients of the shifted inverse component from its actual
function values. Coincident cyclic variables are identified by finite sets. -/
theorem inverse_component_boolean_coefficient (m : ℕ) (b : Word (2 * m + 1))
    (s : Finset (ZMod (2 * m + 1))) :
    booleanCoeff (fun z => inverseComponent m b (1 + z)) s =
      ∑ i, ∑ r ∈ Finset.range (m + 1), b i *
        ((if s = prefixVariables i r then 1 else 0) +
          (if s = insert (i + (2 * r : ℕ)) (prefixVariables i r) then 1 else 0)) := by
  classical
  have he := funext (shifted_inverse_expansion m b)
  rw [he, coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [coeff_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [coeff_mul, coeff_add, coeff_monomial, coeff_monomial]

/-- The coefficient at s in the derivative of the monomial at t. -/
noncomputable def monomialDerivativeCoeff {n : ℕ} (t s : Finset (ZMod n))
    (u : Word n) : ZMod 2 :=
  (if s ⊆ t then booleanMonomial (t \ s) u else 0) +
    (if s = t then 1 else 0)

private theorem coeff_translated_monomial {n : ℕ} (t s : Finset (ZMod n))
    (u : Word n) :
    booleanCoeff (fun z => booleanMonomial t (z + u)) s =
      if s ⊆ t then booleanMonomial (t \ s) u else 0 := by
  classical
  have he : (fun z => booleanMonomial t (z + u)) =
      fun z => ∑ v ∈ t.powerset,
        booleanMonomial (t \ v) u * booleanMonomial v z := by
    funext z
    simp only [booleanMonomial, Pi.add_apply, Finset.prod_add]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he, coeff_sum]
  simp_rw [coeff_mul, coeff_monomial]
  simp only [mul_ite, mul_one, mul_zero]
  simp [Finset.mem_powerset]

/-- Every nonconstant coefficient of a constant derivative of the actual
inverse component vanishes. This supplies the function-to-coefficient bridge
for the cyclic overlap classification, without assuming that classification. -/
theorem inverse_component_derivative_coefficients (m : ℕ)
    (b u : Word (2 * m + 1))
    (hc : ∃ c, ∀ y, inverseComponent m b (y + u) + inverseComponent m b y = c)
    (s : Finset (ZMod (2 * m + 1))) (hs : s.Nonempty) :
    (∑ i, ∑ r ∈ Finset.range (m + 1), b i *
      (monomialDerivativeCoeff (prefixVariables i r) s u +
        monomialDerivativeCoeff
          (insert (i + (2 * r : ℕ)) (prefixVariables i r)) s u)) = 0 := by
  classical
  obtain ⟨c, hc⟩ := hc
  have hconst : booleanCoeff (fun z =>
      inverseComponent m b (1 + (z + u)) + inverseComponent m b (1 + z)) s = 0 := by
    have he : (fun z => inverseComponent m b (1 + (z + u)) +
        inverseComponent m b (1 + z)) = fun _ => c := by
      funext z
      simpa only [add_assoc] using hc (1 + z)
    rw [he]
    exact coeff_constant c s hs
  have hshift : booleanCoeff (fun z => inverseComponent m b (1 + (z + u))) s =
      ∑ i, ∑ r ∈ Finset.range (m + 1), b i *
        ((if s ⊆ prefixVariables i r then
            booleanMonomial (prefixVariables i r \ s) u else 0) +
          (if s ⊆ insert (i + (2 * r : ℕ)) (prefixVariables i r) then
            booleanMonomial (insert (i + (2 * r : ℕ)) (prefixVariables i r) \ s) u
          else 0)) := by
    have he := funext (fun z => shifted_inverse_expansion m b (z + u))
    rw [he, coeff_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [coeff_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [coeff_mul, coeff_add, coeff_translated_monomial, coeff_translated_monomial]
  rw [coeff_add, hshift, inverse_component_boolean_coefficient] at hconst
  rw [← Finset.sum_add_distrib] at hconst
  convert hconst using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  simp only [monomialDerivativeCoeff]
  ring

/-- The highest-degree variable set in a shifted inverse coordinate. -/
def topVariables (m : ℕ) (i : ZMod (2 * m + 1)) : Finset (ZMod (2 * m + 1)) :=
  insert (i + (2 * m : ℕ)) (prefixVariables i m)

private theorem prefix_index_injective (m r : ℕ) (hr : r ≤ m)
    (i : ZMod (2 * m + 1)) :
    Set.InjOn (fun t : ℕ => i + (2 * t + 1 : ℕ)) (Finset.range r) := by
  intro a ha b hb hab
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  have he := (ZMod.natCast_eq_natCast_iff' (2 * a + 1) (2 * b + 1)
    (2 * m + 1)).mp (add_left_cancel hab)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
  omega

private theorem prefix_card (m r : ℕ) (hr : r ≤ m) (i : ZMod (2 * m + 1)) :
    (prefixVariables i r).card = r := by
  rw [prefixVariables, Finset.card_image_of_injOn (prefix_index_injective m r hr i),
    Finset.card_range]

private theorem endpoint_not_prefix (m r : ℕ) (hr : r ≤ m)
    (i : ZMod (2 * m + 1)) : i + (2 * r : ℕ) ∉ prefixVariables i r := by
  classical
  intro h
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
  have ha' := Finset.mem_range.mp ha
  have he' := (ZMod.natCast_eq_natCast_iff' (2 * a + 1) (2 * r)
    (2 * m + 1)).mp (add_left_cancel he)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he'
  omega

private theorem top_card (m : ℕ) (i : ZMod (2 * m + 1)) :
    (topVariables m i).card = m + 1 := by
  classical
  rw [topVariables, Finset.card_insert_of_notMem (endpoint_not_prefix m m le_rfl i),
    prefix_card m m le_rfl]

private theorem top_sum (m : ℕ) (i : ZMod (2 * m + 1)) :
    (∑ k ∈ topVariables m i, k) = (m + 1 : ℕ) * i +
      (((2 * m : ℕ) : ZMod (2 * m + 1)) +
        ∑ r ∈ Finset.range m, ((2 * r + 1 : ℕ) : ZMod (2 * m + 1))) := by
  classical
  rw [topVariables, Finset.sum_insert (endpoint_not_prefix m m le_rfl i)]
  unfold prefixVariables
  rw [Finset.sum_image (prefix_index_injective m m le_rfl i)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

private theorem top_injective (m : ℕ) : Function.Injective (topVariables m) := by
  intro i k hik
  have h := congrArg (fun s : Finset (ZMod (2 * m + 1)) => ∑ j ∈ s, j) hik
  rw [top_sum, top_sum] at h
  have he := add_right_cancel h
  have h2 := congrArg (fun z : ZMod (2 * m + 1) => 2 * z) he
  simpa only [← mul_assoc, twice_half, one_mul] using h2

/-- Every highest-degree monomial of the shifted inverse component has exactly
its original mask bit as coefficient, at every positive odd length. -/
theorem inverse_component_top_coefficient (m : ℕ) (b : Word (2 * m + 1))
    (i : ZMod (2 * m + 1)) :
    booleanCoeff (fun z => inverseComponent m b (1 + z)) (topVariables m i) = b i := by
  classical
  rw [inverse_component_boolean_coefficient]
  have hprefix (k : ZMod (2 * m + 1)) (r : ℕ) (hr : r ∈ Finset.range (m + 1)) :
      topVariables m i ≠ prefixVariables k r := by
    intro h
    have hc := congrArg Finset.card h
    rw [top_card, prefix_card m r (by simpa using hr)] at hc
    have := Finset.mem_range.mp hr
    omega
  have hterm (k : ZMod (2 * m + 1)) (r : ℕ) (hr : r ∈ Finset.range (m + 1)) :
      topVariables m i = insert (k + (2 * r : ℕ)) (prefixVariables k r) ↔
        r = m ∧ k = i := by
    constructor
    · intro h
      have hrm : r ≤ m := by simpa using hr
      have hc := congrArg Finset.card h
      rw [top_card, Finset.card_insert_of_notMem (endpoint_not_prefix m r hrm k),
        prefix_card m r hrm] at hc
      have hr' : r = m := by omega
      subst r
      exact ⟨rfl, (top_injective m h).symm⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hinner (k : ZMod (2 * m + 1)) :
      (∑ r ∈ Finset.range (m + 1), b k *
        ((if topVariables m i = prefixVariables k r then 1 else 0) +
          (if topVariables m i = insert (k + (2 * r : ℕ)) (prefixVariables k r)
          then 1 else 0))) = if k = i then b k else 0 := by
    have he : (∑ r ∈ Finset.range (m + 1), b k *
        ((if topVariables m i = prefixVariables k r then 1 else 0) +
          (if topVariables m i = insert (k + (2 * r : ℕ)) (prefixVariables k r)
          then 1 else 0))) =
        ∑ r ∈ Finset.range (m + 1), if r = m ∧ k = i then b k else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [if_neg (hprefix k r hr), zero_add, hterm k r hr, mul_ite,
        mul_one, mul_zero]
    rw [he]
    by_cases hk : k = i <;> simp [hk]
  simp_rw [hinner]
  simp

private theorem monomial_derivative_degree {n : ℕ} (t s : Finset (ZMod n))
    (u : Word n) (h : t.card ≤ s.card) : monomialDerivativeCoeff t s u = 0 := by
  classical
  by_cases hst : s ⊆ t
  · have he : s = t := Finset.eq_of_subset_of_card_le hst h
    subst t
    simp [monomialDerivativeCoeff, booleanMonomial, CharTwo.add_self_eq_zero]
  · have hne : s ≠ t := fun he => hst (he ▸ Finset.Subset.refl s)
    simp [monomialDerivativeCoeff, hst, hne]

/-- In degree m only deletions from the highest-degree monomials can contribute
to a constant inverse derivative. No cyclic overlap classification is assumed. -/
theorem inverse_component_top_derivative (m : ℕ) (hm : 0 < m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (s : Finset (ZMod (2 * m + 1))) (hs : s.card = m) :
    (∑ i, b i * (if s ⊆ topVariables m i then
      booleanMonomial (topVariables m i \ s) u else 0)) = 0 := by
  classical
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hc := (constantDerivative_affineSpan_duality (inverseComponent m b)).1 u |>.mp hu
  have hcoeff := inverse_component_derivative_coefficients m b u hc s hsne
  have hinner (i : ZMod (2 * m + 1)) :
      (∑ r ∈ Finset.range (m + 1), b i *
        (monomialDerivativeCoeff (prefixVariables i r) s u +
          monomialDerivativeCoeff
            (insert (i + (2 * r : ℕ)) (prefixVariables i r)) s u)) =
      b i * (if s ⊆ topVariables m i then
        booleanMonomial (topVariables m i \ s) u else 0) := by
    rw [Finset.sum_eq_single m]
    · rw [monomial_derivative_degree (prefixVariables i m) s u
        (by rw [prefix_card m m le_rfl, hs])]
      change b i * (0 + monomialDerivativeCoeff (topVariables m i) s u) = _
      have hne : s ≠ topVariables m i := by
        intro he
        have he' := congrArg Finset.card he
        rw [hs, top_card] at he'
        omega
      simp [monomialDerivativeCoeff, hne]
    · intro r hr hrm
      have hr' : r ≤ m := by simpa using hr
      have hrlt : r < m := by omega
      rw [monomial_derivative_degree (prefixVariables i r) s u
          (by rw [prefix_card m r hr', hs]; omega),
        monomial_derivative_degree
          (insert (i + (2 * r : ℕ)) (prefixVariables i r)) s u
          (by rw [Finset.card_insert_of_notMem (endpoint_not_prefix m r hr' i),
            prefix_card m r hr', hs]; omega)]
      simp
    · simp
  simpa only [hinner] using hcoeff

private theorem prefix_no_adjacent (m : ℕ) (i j : ZMod (2 * m + 1))
    (hj : j ∈ prefixVariables i m) : j + 1 ∉ prefixVariables i m := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
  intro h
  obtain ⟨b, hb, he⟩ := Finset.mem_image.mp h
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  have hx : ((2 * b + 1 : ℕ) : ZMod (2 * m + 1)) = (2 * a + 2 : ℕ) := by
    apply add_left_cancel (a := i)
    convert he using 1 <;> push_cast <;> ring
  have hx' := (ZMod.natCast_eq_natCast_iff' (2 * b + 1) (2 * a + 2)
    (2 * m + 1)).mp hx
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hx'
  omega

private theorem top_adjacent_pair (m : ℕ) (hm : 0 < m)
    (i j : ZMod (2 * m + 1))
    (hj : j ∈ topVariables m i) (hj' : j + 1 ∈ topVariables m i) :
    j = i + (2 * m - 1 : ℕ) := by
  classical
  have hstep : i + (2 * m : ℕ) + 1 = i := by
    have hz := ZMod.natCast_self (2 * m + 1)
    push_cast at hz ⊢
    linear_combination hz
  have hnot : i ∉ topVariables m i := by
    simp only [topVariables, Finset.mem_insert]
    rintro (he | he)
    · have hx : ((0 : ℕ) : ZMod (2 * m + 1)) = (2 * m : ℕ) := by
        simpa using (add_left_cancel (a := i) (show i + 0 = i + (2 * m : ℕ) by simpa using he))
      have hx' := (ZMod.natCast_eq_natCast_iff' 0 (2 * m) (2 * m + 1)).mp hx
      rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at hx'
      omega
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp he
      have ha' := Finset.mem_range.mp ha
      have hx : ((2 * a + 1 : ℕ) : ZMod (2 * m + 1)) = 0 := by
        exact add_left_cancel (he.trans (add_zero i).symm)
      have hx' := (ZMod.natCast_eq_natCast_iff' (2 * a + 1) 0 (2 * m + 1)).mp hx
      rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at hx'
      omega
  rcases Finset.mem_insert.mp hj with he | hp
  · exact (hnot (by simpa only [he, hstep] using hj')).elim
  · rcases Finset.mem_insert.mp hj' with he | hp'
    · have he' : j + 1 = i + (2 * m - 1 : ℕ) + 1 := by
        have hnat : 2 * m - 1 + 1 = 2 * m := by omega
        have hx := congrArg (fun r : ℕ => i + (r : ZMod (2 * m + 1))) hnat
        exact he.trans (by simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hx.symm)
      exact add_right_cancel he'
    · exact (prefix_no_adjacent m i j hp hp').elim

private theorem interior_deletion_unique (m : ℕ) (hm : 0 < m)
    (i a k : ZMod (2 * m + 1))
    (ha : a ≠ i + (2 * m - 1 : ℕ)) (ha' : a ≠ i + (2 * m : ℕ))
    (hsub : (topVariables m i).erase a ⊆ topVariables m k) : k = i := by
  classical
  let j : ZMod (2 * m + 1) := i + (2 * m - 1 : ℕ)
  have hlast : j ∈ prefixVariables i m := by
    refine Finset.mem_image.mpr ⟨m - 1, Finset.mem_range.mpr (by omega), ?_⟩
    dsimp [j]
    have hn : 2 * (m - 1) + 1 = 2 * m - 1 := by omega
    rw [hn]
  have hj : j ∈ (topVariables m i).erase a := by
    exact Finset.mem_erase.mpr ⟨Ne.symm ha, Finset.mem_insert_of_mem hlast⟩
  have hje : j + 1 = i + (2 * m : ℕ) := by
    dsimp [j]
    have hnat : 2 * m - 1 + 1 = 2 * m := by omega
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      congrArg (fun r : ℕ => i + (r : ZMod (2 * m + 1))) hnat
  have hj' : j + 1 ∈ (topVariables m i).erase a := by
    rw [hje]
    exact Finset.mem_erase.mpr ⟨Ne.symm ha', Finset.mem_insert_self _ _⟩
  have he := top_adjacent_pair m hm k j (hsub hj) (hsub hj')
  change i + (2 * m - 1 : ℕ) = k + (2 * m - 1 : ℕ) at he
  exact (add_right_cancel he).symm

private theorem inverse_component_interior_constraint (m : ℕ) (hm : 0 < m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (i a : ZMod (2 * m + 1)) (ha : a ∈ topVariables m i)
    (ha₁ : a ≠ i + (2 * m - 1 : ℕ)) (ha₂ : a ≠ i + (2 * m : ℕ)) :
    b i * u a = 0 := by
  classical
  let s := (topVariables m i).erase a
  have hs : s.card = m := by
    dsimp [s]
    rw [Finset.card_erase_of_mem ha, top_card]
    omega
  have hcoeff := inverse_component_top_derivative m hm b u hu s hs
  have hterm (k : ZMod (2 * m + 1)) :
      (if s ⊆ topVariables m k then
        booleanMonomial (topVariables m k \ s) u else 0) =
      if k = i then u a else 0 := by
    by_cases hk : k = i
    · subst k
      have hsub : s ⊆ topVariables m i := Finset.erase_subset _ _
      rw [if_pos hsub, if_pos rfl]
      have hdiff : topVariables m i \ s = {a} := by
        ext j
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton, s]
        constructor
        · rintro ⟨hj, hn⟩
          by_contra hja
          exact hn ⟨hja, hj⟩
        · rintro rfl
          simp [ha]
      simp [hdiff, booleanMonomial]
    · have hsub : ¬s ⊆ topVariables m k :=
        fun h => hk (interior_deletion_unique m hm i a k ha₁ ha₂ h)
      simp [hsub, hk]
  simp_rw [hterm] at hcoeff
  simpa [mul_ite] using hcoeff

private theorem prefix_injective (m : ℕ) :
    Function.Injective (fun i : ZMod (2 * m + 1) => prefixVariables i m) := by
  intro i k hik
  have hsum (j : ZMod (2 * m + 1)) :
      (∑ a ∈ prefixVariables j m, a) = (m : ZMod (2 * m + 1)) * j +
        ∑ r ∈ Finset.range m, ((2 * r + 1 : ℕ) : ZMod (2 * m + 1)) := by
    classical
    unfold prefixVariables
    rw [Finset.sum_image (prefix_index_injective m m le_rfl j)]
    simp [Finset.sum_add_distrib, nsmul_eq_mul]
  have he := congrArg (fun s : Finset (ZMod (2 * m + 1)) => ∑ a ∈ s, a) hik
  rw [hsum, hsum] at he
  have he' := congrArg (fun z : ZMod (2 * m + 1) => 2 * z) (add_right_cancel he)
  have hz := ZMod.natCast_self (2 * m + 1)
  push_cast at hz
  linear_combination (i - k) * hz - he'

private theorem top_shift (m : ℕ) (hm : 0 < m) (i : ZMod (2 * m + 1)) :
    topVariables m (i + 2) = insert i (prefixVariables i m) := by
  classical
  have hz := ZMod.natCast_self (2 * m + 1)
  have he : i + 2 + (2 * m : ℕ) = i + 1 := by
    push_cast at hz ⊢
    linear_combination hz
  have hw : i + 2 + (2 * (m - 1) + 1 : ℕ) = i := by
    have hn : 2 * (m - 1) + 1 + 2 = 2 * m + 1 := by omega
    have hx := congrArg (fun r : ℕ => i + (r : ZMod (2 * m + 1))) hn
    push_cast at hx hz ⊢
    linear_combination hx + hz
  ext a
  simp only [topVariables, Finset.mem_insert, prefixVariables, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro (rfl | ⟨r, hr, rfl⟩)
    · exact Or.inr ⟨0, hm, by simpa using he.symm⟩
    · by_cases hlast : r = m - 1
      · left
        simpa [hlast] using hw
      · right
        refine ⟨r + 1, by omega, ?_⟩
        push_cast
        ring
  · rintro (rfl | ⟨r, hr, rfl⟩)
    · right
      exact ⟨m - 1, by omega, hw⟩
    · by_cases hr0 : r = 0
      · left
        simpa [hr0] using he.symm
      · right
        refine ⟨r - 1, by omega, ?_⟩
        have hn : 2 * (r - 1) + 1 + 2 = 2 * r + 1 := by omega
        have hx := congrArg (fun t : ℕ => i + (t : ZMod (2 * m + 1))) hn
        push_cast at hx ⊢
        linear_combination hx

private theorem endpoint_deletion_overlap (m : ℕ) (hm : 0 < m)
    (i k : ZMod (2 * m + 1)) :
    prefixVariables i m ⊆ topVariables m k ↔ k = i ∨ k = i + 2 := by
  classical
  constructor
  · intro hsub
    by_cases he : k + (2 * m : ℕ) ∈ prefixVariables i m
    · have hn : k - 2 + 1 = k + (2 * m : ℕ) := by
        have hz := ZMod.natCast_self (2 * m + 1)
        push_cast at hz ⊢
        linear_combination -hz
      have hnot : k - 2 ∉ prefixVariables i m := by
        intro h
        exact prefix_no_adjacent m i (k - 2) h (hn.symm ▸ he)
      have ht : topVariables m k = insert (k - 2) (prefixVariables (k - 2) m) := by
        simpa using top_shift m hm (k - 2)
      have hs : prefixVariables i m ⊆ prefixVariables (k - 2) m := by
        intro a ha
        have ha' := hsub ha
        rw [ht] at ha'
        rcases Finset.mem_insert.mp ha' with rfl | ha'
        · exact (hnot ha).elim
        · exact ha'
      have heq := Finset.eq_of_subset_of_card_le hs
        (by rw [prefix_card m m le_rfl, prefix_card m m le_rfl])
      have hi := prefix_injective m heq
      right
      linear_combination -hi
    · have hs : prefixVariables i m ⊆ prefixVariables k m := by
        intro a ha
        rcases Finset.mem_insert.mp (hsub ha) with rfl | ha'
        · exact (he ha).elim
        · exact ha'
      have heq := Finset.eq_of_subset_of_card_le hs
        (by rw [prefix_card m m le_rfl, prefix_card m m le_rfl])
      exact Or.inl (prefix_injective m heq).symm
  · rintro (rfl | rfl)
    · exact Finset.subset_insert _ _
    · rw [top_shift m hm]
      exact Finset.subset_insert _ _

private theorem inverse_component_endpoint_constraint (m : ℕ) (hm : 0 < m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (i : ZMod (2 * m + 1)) :
    b i * u (i + (2 * m : ℕ)) = b (i + 2) * u i := by
  classical
  let s := prefixVariables i m
  have hs : s.card = m := prefix_card m m le_rfl i
  have hc := inverse_component_top_derivative m hm b u hu s hs
  have hi : i ∉ prefixVariables i m := by
    intro h
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp h
    have hr' := Finset.mem_range.mp hr
    have he' : ((2 * r + 1 : ℕ) : ZMod (2 * m + 1)) = 0 := by
      exact add_left_cancel (he.trans (add_zero i).symm)
    have hn := (ZMod.natCast_eq_natCast_iff' (2 * r + 1) 0 (2 * m + 1)).mp he'
    rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at hn
    omega
  have hterm (k : ZMod (2 * m + 1)) :
      (if s ⊆ topVariables m k then booleanMonomial (topVariables m k \ s) u else 0) =
      (if k = i then u (i + (2 * m : ℕ)) else 0) +
        (if k = i + 2 then u i else 0) := by
    have hne : i + 2 ≠ i := by
      intro h
      have he : (2 : ZMod (2 * m + 1)) = 0 := by linear_combination h
      have hn := (ZMod.natCast_eq_zero_iff 2 (2 * m + 1)).mp he
      have := Nat.le_of_dvd (by omega : 0 < 2) hn
      omega
    by_cases hk : k = i
    · subst k
      have hd : topVariables m i \ s = {i + (2 * m : ℕ)} := by
        dsimp [topVariables, s]
        ext a
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        have he := endpoint_not_prefix m m le_rfl i
        aesop
      have hsub : s ⊆ topVariables m i := Finset.subset_insert _ _
      simp [hsub, Ne.symm hne, hd, booleanMonomial]
    · by_cases hk' : k = i + 2
      · subst k
        have hd : topVariables m (i + 2) \ s = {i} := by
          rw [top_shift m hm]
          dsimp [s]
          simp [hi]
        have hsub : s ⊆ topVariables m (i + 2) :=
          (endpoint_deletion_overlap m hm i (i + 2)).mpr (Or.inr rfl)
        simp [hsub, hk, hd, booleanMonomial]
      · have hsub : ¬s ⊆ topVariables m k := by
          simpa only [s, endpoint_deletion_overlap m hm i k, not_or] using ⟨hk, hk'⟩
        simp [hsub, hk, hk']
  simp_rw [hterm, mul_add, mul_ite, mul_zero] at hc
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hc
  exact eq_of_sub_eq_zero (by simpa only [ZModModule.sub_eq_add] using hc)

private theorem prefix_start_injective (m r : ℕ) (hr : 0 < r) (hrm : r ≤ m) :
    Function.Injective (fun i : ZMod (2 * m + 1) => prefixVariables i r) := by
  intro i k hik
  change prefixVariables i r = prefixVariables k r at hik
  have hfirst : i + 1 ∈ prefixVariables k r := by
    rw [← hik]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hr, by simp⟩
  obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hfirst
  have ht' := Finset.mem_range.mp ht
  have hprev : i - 1 ∉ prefixVariables i r := by
    intro h
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp h
    have ha' := Finset.mem_range.mp ha
    have hx : ((2 * a + 2 : ℕ) : ZMod (2 * m + 1)) = 0 := by
      push_cast at hea ⊢
      linear_combination hea
    have hx' := (ZMod.natCast_eq_zero_iff (2 * a + 2) (2 * m + 1)).mp hx
    have hle := Nat.le_of_dvd (by omega : 0 < 2 * a + 2) hx'
    omega
  have ht0 : t = 0 := by
    by_contra h
    apply hprev
    rw [hik]
    refine Finset.mem_image.mpr ⟨t - 1, Finset.mem_range.mpr (by omega), ?_⟩
    have hn : 2 * (t - 1) + 1 + 2 = 2 * t + 1 := by omega
    have hx := congrArg (fun a : ℕ => k + (a : ZMod (2 * m + 1))) hn
    push_cast at he hx ⊢
    linear_combination he + hx
  simpa [ht0] using he.symm

private theorem inverse_component_prefix_fixed (m : ℕ) (hm : 0 < m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (i : ZMod (2 * m + 1)) (hb : b i ≠ 0)
    (r : ℕ) (hr : r < m) (z : Word (2 * m + 1)) :
    booleanMonomial (prefixVariables i r) (z + u) =
      booleanMonomial (prefixVariables i r) z := by
  classical
  apply Finset.prod_congr rfl
  intro a ha
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
  have ht' := Finset.mem_range.mp ht
  have hmem : i + (2 * t + 1 : ℕ) ∈ topVariables m i :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨t, Finset.mem_range.mpr (by omega), rfl⟩)
  have hne : i + (2 * t + 1 : ℕ) ≠ i + (2 * m - 1 : ℕ) := by
    intro h
    have he := (ZMod.natCast_eq_natCast_iff' (2 * t + 1) (2 * m - 1)
      (2 * m + 1)).mp (add_left_cancel h)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
    omega
  have hne' : i + (2 * t + 1 : ℕ) ≠ i + (2 * m : ℕ) := by
    intro h
    have he := (ZMod.natCast_eq_natCast_iff' (2 * t + 1) (2 * m)
      (2 * m + 1)).mp (add_left_cancel h)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
    omega
  have hz := inverse_component_interior_constraint m hm b u hu i _ hmem hne hne'
  have hzero := (mul_eq_zero.mp hz).resolve_left hb
  change z (i + (2 * t + 1 : ℕ)) + u (i + (2 * t + 1 : ℕ)) = _
  rw [hzero, add_zero]

private theorem monomial_prefix_succ {n : ℕ} (i : ZMod n) (r : ℕ) (z : Word n) :
    booleanMonomial (prefixVariables i (r + 1)) z =
      z (i + (2 * r + 1 : ℕ)) * booleanMonomial (prefixVariables i r) z := by
  classical
  have hs : prefixVariables i (r + 1) =
      insert (i + (2 * r + 1 : ℕ)) (prefixVariables i r) := by
    simp only [prefixVariables, Finset.range_add_one, Finset.image_insert]
  rw [hs, monomial_insert]

private theorem monomial_prefix_cons {n : ℕ} (i : ZMod n) (r : ℕ) (z : Word n) :
    booleanMonomial (prefixVariables (i - 2) (r + 1)) z =
      z (i - 1) * booleanMonomial (prefixVariables i r) z := by
  classical
  have hs : prefixVariables (i - 2) (r + 1) =
      insert (i - 1) (prefixVariables i r) := by
    ext a
    simp only [prefixVariables, Finset.mem_image, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨t, ht, rfl⟩
      by_cases ht0 : t = 0
      · left
        simp only [ht0, Nat.mul_zero, Nat.zero_add, Nat.cast_one]
        ring
      · right
        refine ⟨t - 1, by omega, ?_⟩
        have hn : 2 * (t - 1) + 1 + 2 = 2 * t + 1 := by omega
        have hx := congrArg (fun a : ℕ => (a : ZMod n)) hn
        push_cast at hx ⊢
        linear_combination hx
    · rintro (rfl | ⟨t, ht, rfl⟩)
      · exact ⟨0, by omega, by push_cast; ring⟩
      · refine ⟨t + 1, by omega, ?_⟩
        push_cast
        ring
  rw [hs, monomial_insert]

set_option maxHeartbeats 1000000 in
private theorem shifted_inverse_derivative_expansion (m : ℕ) (hm : 0 < m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (z : Word (2 * m + 1)) :
    inverseComponent m b (1 + (z + u)) + inverseComponent m b (1 + z) =
      (∑ i, ∑ r ∈ Finset.range m,
        b i * u (i + (2 * r : ℕ)) * booleanMonomial (prefixVariables i r) z) +
      ∑ i, b i * (u (i + (2 * m - 1 : ℕ)) *
          (1 + u (i + (2 * m : ℕ)))) *
        booleanMonomial (prefixVariables i (m - 1)) z := by
  classical
  have hlast : ∀ i : ZMod (2 * m + 1),
      i + (2 * m - 1 : ℕ) = i - 2 := by
    intro i
    have hn : 2 * m - 1 + 2 = 2 * m + 1 := by omega
    have hx := congrArg (fun a : ℕ => (a : ZMod (2 * m + 1))) hn
    have hz := ZMod.natCast_self (2 * m + 1)
    push_cast at hx hz
    linear_combination hx + hz
  have hend : ∀ i : ZMod (2 * m + 1), i + (2 * m : ℕ) = i - 1 := by
    intro i
    have hz := ZMod.natCast_self (2 * m + 1)
    push_cast at hz ⊢
    linear_combination hz
  have hlocal (i : ZMod (2 * m + 1)) :
      (∑ r ∈ Finset.range (m + 1), b i *
        (booleanMonomial (prefixVariables i r) (z + u) +
          booleanMonomial (insert (i + (2 * r : ℕ)) (prefixVariables i r)) (z + u))) +
      (∑ r ∈ Finset.range (m + 1), b i *
        (booleanMonomial (prefixVariables i r) z +
          booleanMonomial (insert (i + (2 * r : ℕ)) (prefixVariables i r)) z)) =
      (∑ r ∈ Finset.range m,
        b i * u (i + (2 * r : ℕ)) * booleanMonomial (prefixVariables i r) z) +
      b i * (u (i - 2) * (1 + u (i - 1))) *
        booleanMonomial (prefixVariables i (m - 1)) z +
      b i * u (i - 1) * booleanMonomial (prefixVariables i m) z +
      b i * u (i - 2) * booleanMonomial (prefixVariables (i - 2) m) z := by
    by_cases hb : b i = 0
    · simp [hb]
    · have hfixed := inverse_component_prefix_fixed m hm b u hu i hb
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hsmall :
          (∑ r ∈ Finset.range m, b i *
            (booleanMonomial (prefixVariables i r) (z + u) +
              booleanMonomial (insert (i + (2 * r : ℕ)) (prefixVariables i r)) (z + u))) +
          (∑ r ∈ Finset.range m, b i *
            (booleanMonomial (prefixVariables i r) z +
              booleanMonomial (insert (i + (2 * r : ℕ)) (prefixVariables i r)) z)) =
          ∑ r ∈ Finset.range m,
            b i * u (i + (2 * r : ℕ)) * booleanMonomial (prefixVariables i r) z := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        rw [monomial_insert, monomial_insert,
          hfixed r (Finset.mem_range.mp hr) z]
        simp only [Pi.add_apply]
        ring_nf
        simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, add_zero, zero_add]
      have hmp : m - 1 + 1 = m := by omega
      have hpz := monomial_prefix_succ i (m - 1) z
      have hpu := monomial_prefix_succ i (m - 1) (z + u)
      have hpc := monomial_prefix_cons i (m - 1) z
      have hn : 2 * (m - 1) + 1 = 2 * m - 1 := by omega
      rw [hmp, hn, hlast] at hpz hpu
      rw [hmp] at hpc
      rw [monomial_insert, monomial_insert, hpz, hpu,
        hfixed (m - 1) (by omega) z]
      simp only [Pi.add_apply, hend, hlast]
      rw [hpc]
      have htwo : (2 : ZMod 2) = 0 := by decide
      linear_combination (norm := (ring_nf; simp only [htwo, mul_zero, add_zero, zero_add]))
        hsmall
  rw [shifted_inverse_expansion, shifted_inverse_expansion, ← Finset.sum_add_distrib]
  simp_rw [hlocal]
  simp only [Finset.sum_add_distrib, hlast, hend]
  have hcancel :
      (∑ i, b i * u (i - 1) * booleanMonomial (prefixVariables i m) z) +
      (∑ i, b i * u (i - 2) * booleanMonomial (prefixVariables (i - 2) m) z) = 0 := by
    have hreindex := Equiv.sum_comp (Equiv.addRight (2 : ZMod (2 * m + 1)))
      (fun i => b i * u (i - 2) * booleanMonomial (prefixVariables (i - 2) m) z)
    change (∑ i, _) = _ at hreindex
    conv_lhs => rhs; rw [← hreindex]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    have hb := inverse_component_endpoint_constraint m hm b u hu i
    rw [hend] at hb
    simp only [Equiv.coe_addRight]
    change b i * u (i - 1) * booleanMonomial (prefixVariables i m) z +
      b (i + 2) * u (i + 2 - 2) *
        booleanMonomial (prefixVariables (i + 2 - 2) m) z = 0
    have hi : i + 2 - 2 = i := by ring
    rw [hi, ← hb]
    exact CharTwo.add_self_eq_zero _
  linear_combination hcancel

private theorem inverse_component_lower_constraint (m : ℕ) (hm : 2 ≤ m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (i : ZMod (2 * m + 1)) (r : ℕ) (hr : 0 < r) (hrm : r < m) :
    b i * (u (i + (2 * r : ℕ)) +
      if r = m - 1 then u (i + (2 * m - 1 : ℕ)) *
        (1 + u (i + (2 * m : ℕ))) else 0) = 0 := by
  classical
  let s := prefixVariables i r
  have hs : s.Nonempty := Finset.card_pos.mp (by
    change 0 < (prefixVariables i r).card
    rw [prefix_card m r (by omega)]
    exact hr)
  have hiff (k : ZMod (2 * m + 1)) (q : ℕ) (hq : q ≤ m) :
      s = prefixVariables k q ↔ q = r ∧ k = i := by
    constructor
    · intro h
      have hc := congrArg Finset.card h
      dsimp [s] at hc
      rw [prefix_card m r (by omega), prefix_card m q hq] at hc
      subst q
      exact ⟨rfl, (prefix_start_injective m r hr (by omega) h).symm⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hc : booleanCoeff (fun z =>
      (∑ k, ∑ q ∈ Finset.range m,
        b k * u (k + (2 * q : ℕ)) * booleanMonomial (prefixVariables k q) z) +
      ∑ k, b k * (u (k + (2 * m - 1 : ℕ)) *
        (1 + u (k + (2 * m : ℕ)))) *
        booleanMonomial (prefixVariables k (m - 1)) z) s = 0 := by
    have he := funext (shifted_inverse_derivative_expansion m (by omega) b u hu)
    rw [← he]
    obtain ⟨c, hc⟩ := (constantDerivative_affineSpan_duality (inverseComponent m b)).1 u |>.mp hu
    have hconst : (fun z => inverseComponent m b (1 + (z + u)) +
        inverseComponent m b (1 + z)) = fun _ => c := by
      funext z
      simpa only [add_assoc] using hc (1 + z)
    rw [hconst]
    exact coeff_constant c s hs
  rw [coeff_add, coeff_sum, coeff_sum] at hc
  simp_rw [coeff_sum, coeff_mul, coeff_monomial] at hc
  have hinner (k : ZMod (2 * m + 1)) :
      (∑ q ∈ Finset.range m, b k * u (k + (2 * q : ℕ)) *
        (if s = prefixVariables k q then 1 else 0)) =
      if k = i then b k * u (k + (2 * r : ℕ)) else 0 := by
    rw [Finset.sum_eq_single r]
    · simp only [hiff k r (by omega)]
      by_cases hk : k = i <;> simp [hk]
    · intro q hq hqr
      have hq' := Finset.mem_range.mp hq
      simp only [hiff k q (by omega), hqr, false_and, ite_false, mul_zero]
    · simp [Finset.mem_range.mpr hrm]
  simp_rw [hinner, hiff _ (m - 1) (by omega)] at hc
  by_cases hr' : r = m - 1
  · simp only [hr', eq_self_iff_true, true_and, ite_true, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hc
    simp only [hr', ite_true]
    convert hc using 1 <;> push_cast <;> ring
  · have hr'' : m - 1 ≠ r := Ne.symm hr'
    simp only [hr'', false_and, ite_false, mul_zero, Finset.sum_const_zero, add_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hc
    simp only [if_neg hr', add_zero]
    simpa only [Nat.cast_mul] using hc

private theorem inverse_component_annihilation (m : ℕ) (hm : 2 ≤ m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (i : ZMod (2 * m + 1)) (r : ℕ) (hr : 0 < r) (hrm : r ≤ 2 * m - 3) :
    b i * u (i + (r : ℕ)) = 0 := by
  have hmod : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases hmod with he | ho
  · have hr' : r = 2 * (r / 2) := by omega
    have hc := inverse_component_lower_constraint m hm b u hu i (r / 2)
      (by omega) (by omega)
    have hne : r / 2 ≠ m - 1 := by omega
    simpa only [if_neg hne, add_zero, ← hr'] using hc
  · have hr' : r = 2 * (r / 2) + 1 := by omega
    have hmem : i + (r : ℕ) ∈ topVariables m i := by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨r / 2, Finset.mem_range.mpr (by omega), by rw [← hr']⟩
    apply inverse_component_interior_constraint m (by omega) b u hu i _ hmem
    · intro h
      have he := (ZMod.natCast_eq_natCast_iff' r (2 * m - 1) (2 * m + 1)).mp
        (add_left_cancel h)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
      omega
    · intro h
      have he := (ZMod.natCast_eq_natCast_iff' r (2 * m) (2 * m + 1)).mp
        (add_left_cancel h)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
      omega

private theorem inverse_component_last_constraint (m : ℕ) (hm : 2 ≤ m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (i : ZMod (2 * m + 1)) :
    b i * (u (i - 3) + u (i - 2) * (1 + u (i - 1))) = 0 := by
  have hc := inverse_component_lower_constraint m hm b u hu i (m - 1)
    (by omega) (by omega)
  have hz := ZMod.natCast_self (2 * m + 1)
  have h₁ : i + (2 * (m - 1) : ℕ) = i - 3 := by
    have hn : 2 * (m - 1) + 3 = 2 * m + 1 := by omega
    have hx := congrArg (fun a : ℕ => (a : ZMod (2 * m + 1))) hn
    push_cast at hx hz ⊢
    linear_combination hx + hz
  have h₂ : i + (2 * m - 1 : ℕ) = i - 2 := by
    have hn : 2 * m - 1 + 2 = 2 * m + 1 := by omega
    have hx := congrArg (fun a : ℕ => (a : ZMod (2 * m + 1))) hn
    push_cast at hx hz ⊢
    linear_combination hx + hz
  have h₃ : i + (2 * m : ℕ) = i - 1 := by
    push_cast at hz ⊢
    linear_combination hz
  simpa only [ite_true, h₁, h₂, h₃] using hc

private theorem mask_boundary (m : ℕ) (b : Word (2 * m + 1)) (hb : b ≠ 0) :
    b = 1 ∨ ∃ i, b i = 1 ∧ b (i - 2) = 0 := by
  classical
  by_cases hone : b = 1
  · exact Or.inl hone
  right
  by_contra h
  have hstep (i : ZMod (2 * m + 1)) (hi : b i = 1) : b (i - 2) = 1 := by
    rcases bit_cases (b (i - 2)) with he | he
    · exact (h ⟨i, hi, he⟩).elim
    · exact he
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra hzero
    apply hb
    funext i
    exact not_ne_iff.mp (not_exists.mp hzero i)
  have hi' : b i = 1 := (bit_cases (b i)).resolve_left hi
  have hp (r : ℕ) : b (i - (2 * r : ℕ)) = 1 := by
    induction r with
    | zero => simpa using hi'
    | succ r ih =>
      have hs := hstep (i - (2 * r : ℕ)) ih
      convert hs using 1 <;> congr 1 <;> push_cast <;> ring
  apply hone
  funext k
  obtain ⟨r, hr⟩ := step_two_reaches m k i
  have hk : i - (2 * r : ℕ) = k := by linear_combination -hr
  simpa only [hk, Pi.one_apply] using hp r

private theorem coordinate_rank_bound {n : ℕ} [NeZero n]
    (D : Subspace (ZMod 2) (Word n)) (i : ZMod n)
    (hzero : ∀ u ∈ D, u i = 0 → u = 0) : Module.finrank (ZMod 2) D ≤ 1 := by
  let e : D →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun u => u.1 i
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hi : Function.Injective e := by
    intro u v huv
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hzero (u.1 - v.1) (D.sub_mem u.2 v.2)
    change u.1 i - v.1 i = 0
    exact sub_eq_zero.mpr huv
  simpa using (LinearMap.finrank_le_finrank_of_injective hi)

private theorem inverse_component_three_rank (b : Word 3) (hb : b ≠ 0) :
    Module.finrank (ZMod 2) (constantDerivativeSubmodule (inverseComponent 1 b)) ≤ 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra hzero
    apply hb
    funext i
    exact not_ne_iff.mp (not_exists.mp hzero i)
  have hbi : b i = 1 := (bit_cases (b i)).resolve_left hi
  apply coordinate_rank_bound _ i
  intro u hu hzero
  have h₂ : u (i + 2) = 0 := by
    have hc := inverse_component_endpoint_constraint 1 (by decide) b u hu i
    simpa [hbi, hzero] using hc
  have h₁ : u (i + 1) = 0 := by
    have hc := inverse_component_endpoint_constraint 1 (by decide) b u hu (i + 1)
    change b (i + 1) * u (i + 1 + 2) = b (i + 1 + 2) * u (i + 1) at hc
    have he : i + 1 + 2 = i := by
      have hz : (3 : ZMod 3) = 0 := by decide
      linear_combination hz
    rw [he, hbi, hzero, mul_zero, one_mul] at hc
    exact hc.symm
  funext k
  change u k = 0
  have hval := ZMod.val_lt (k - i)
  have hcast : (((k - i).val : ℕ) : ZMod 3) = k - i := ZMod.natCast_zmod_val _
  have hcases : k = i ∨ k = i + 1 ∨ k = i + 2 := by
    rcases (show (k - i).val = 0 ∨ (k - i).val = 1 ∨ (k - i).val = 2 by omega)
      with h | h | h
    · left
      rw [h] at hcast
      linear_combination -hcast
    · right; left
      rw [h] at hcast
      linear_combination -hcast
    · right; right
      rw [h] at hcast
      linear_combination -hcast
  rcases hcases with rfl | rfl | rfl
  · exact hzero
  · exact h₁
  · exact h₂

private theorem inverse_component_large_rank (m : ℕ) (hm : 2 ≤ m)
    (b : Word (2 * m + 1)) (hb : b ≠ 0) :
    Module.finrank (ZMod 2) (constantDerivativeSubmodule (inverseComponent m b)) ≤ 1 := by
  classical
  rcases mask_boundary m b hb with hone | ⟨i, hbi, hbprev⟩
  · apply coordinate_rank_bound _ 0
    intro u hu _
    funext k
    have hc := inverse_component_annihilation m hm b u hu (k - 1) 1 (by decide) (by omega)
    have hk : k - 1 + (1 : ℕ) = k := by ring
    simpa [hone, hk] using hc
  · apply coordinate_rank_bound _ i
    intro u hu hzero
    have hwrap (a : ℕ) (ha : a ≤ 2 * m + 1) :
        i + (2 * m + 1 - a : ℕ) = i - (a : ZMod (2 * m + 1)) := by
      rw [Nat.cast_sub ha, ZMod.natCast_self]
      ring
    have hend : i + (2 * m : ℕ) = i - 1 := by
      convert hwrap 1 (by omega) using 1 <;> congr 1 <;> omega
    have h₁ : u (i - 1) = 0 := by
      have hc := inverse_component_endpoint_constraint m (by omega) b u hu i
      simpa only [hend, hbi, hzero, one_mul, mul_zero] using hc
    have h₂ : u (i - 2) = 0 := by
      have hc := inverse_component_endpoint_constraint m (by omega) b u hu (i - 2)
      have hi : i - 2 + 2 = i := by ring
      rw [hi, hbprev, hbi, zero_mul, one_mul] at hc
      exact hc.symm
    have h₃ : u (i - 3) = 0 := by
      have hc := inverse_component_last_constraint m hm b u hu i
      simpa only [hbi, h₂, one_mul, zero_mul, add_zero] using hc
    funext k
    change u k = 0
    let r := (k - i).val
    have hr : r < 2 * m + 1 := ZMod.val_lt _
    have hk : i + (r : ZMod (2 * m + 1)) = k := by
      dsimp [r]
      rw [ZMod.natCast_zmod_val]
      ring
    by_cases hr0 : r = 0
    · have he : k = i := by simpa only [hr0, Nat.cast_zero, add_zero] using hk.symm
      simpa only [he] using hzero
    by_cases hr₁ : r = 2 * m
    · rw [hr₁, hend] at hk
      simpa only [← hk] using h₁
    by_cases hr₂ : r = 2 * m - 1
    · have he : r = 2 * m + 1 - 2 := by omega
      rw [he, hwrap 2 (by omega)] at hk
      simpa only [← hk, Nat.cast_ofNat] using h₂
    by_cases hr₃ : r = 2 * m - 2
    · have he : r = 2 * m + 1 - 3 := by omega
      rw [he, hwrap 3 (by omega)] at hk
      simpa only [← hk, Nat.cast_ofNat] using h₃
    have hc := inverse_component_annihilation m hm b u hu i r (by omega) (by omega)
    simpa only [hbi, hk, one_mul] using hc

/-- The literal ordered integer trace has affine support of codimension at most
one for every nonzero mask at every positive odd length. -/
theorem affine_trace_support_dimension (m : ℕ) (b : Word (2 * m + 1)) (hb : b ≠ 0) :
    2 * m ≤ Module.finrank (ZMod 2)
      (affineSpan (ZMod 2) (traceSupport b)).direction := by
  classical
  by_cases hm0 : m = 0
  · subst m
    exact Nat.zero_le _
  have hrank : Module.finrank (ZMod 2)
      (constantDerivativeSubmodule (inverseComponent m b)) ≤ 1 := by
    by_cases hm1 : m = 1
    · subst m
      exact inverse_component_three_rank b hb
    · exact inverse_component_large_rank m (by omega) b hb
  have hdual := (constantDerivative_affineSpan_duality (inverseComponent m b)).2
  have hfull : Module.finrank (ZMod 2) (Word (2 * m + 1)) = 2 * m + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, ZMod.card]
  rw [hfull] at hdual
  have hs : traceSupport b = {a | walsh (inverseComponent m b) a ≠ 0} := by
    ext a
    simp only [traceSupport, Set.mem_setOf_eq, sourceTrace_eq_phase_sum, inverse_phase_sum]
  have hdir : (affineSpan (ZMod 2) (traceSupport b)).direction =
      walshSupportDirection (inverseComponent m b) := by
    rw [hs]
    rfl
  have hdim : Module.finrank (ZMod 2) (affineSpan (ZMod 2) (traceSupport b)).direction =
      Module.finrank (ZMod 2) (walshSupportDirection (inverseComponent m b)) :=
    congrArg (fun D : Subspace (ZMod 2) (Word (2 * m + 1)) =>
      Module.finrank (ZMod 2) D) hdir
  rw [hdim]
  omega

end D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace
