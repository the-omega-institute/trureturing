/- GID: D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CyclicBoolean/CyclicSignTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd cyclic Boolean chi, its explicit inverse, and integer cyclic sign traces. -/

import D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

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

end D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace
