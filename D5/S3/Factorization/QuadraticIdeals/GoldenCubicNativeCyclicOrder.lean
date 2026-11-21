/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCyclicOrder
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCyclicOrder
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The denominator-two order of the native cyclic cubic has exact trace discriminant. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclic
import D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueMaximalOrder

/-!
# The denominator-two order of the native cyclic cubic

The three displayed generators form an actual integral subalgebra with known
trace discriminant. No maximality, prime-splitting classification, or
square-times-cube exclusion is included.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclicOrder

section IntegralOrder
/-! Integral multiplication constants for an arbitrary even parameter
L=2k, with B=L²+3. No square-times-cube hypothesis occurs. -/

def block (k : ℤ) : ℤ := 4 * k ^ 2 + 3

def coeffXz (k : ℤ) : ℤ := 6 * k ^ 2 + 4

def coeffZz (k : ℤ) : ℤ := 6 * k ^ 2 + 5

def coeffXzz (k : ℤ) : ℤ := -(3 * k ^ 2 + 2 + block k * k)

def coeffConstant (k : ℤ) : ℤ := block k * (2 * k)

variable {F : Type*} [Field F] [CharZero F]

/-- Explicit, denominator-free integral table on (1,x,(x²−x)/2). -/
theorem multiplication_table (k : ℤ) (x : F)
    (hx : x ^ 3 - 3 * (block k : F) * x + 2 * (coeffConstant k : F) = 0) :
    let z := (x ^ 2 - x) / 2
    let b := (coeffXz k : F)
    let c := (coeffXzz k : F)
    let e := (coeffZz k : F)
    let q := (coeffConstant k : F)
    x ^ 2 = x + 2 * z ∧ x * z = b * x - z - q ∧ z ^ 2 = c * x + e * z + q := by
  dsimp
  simp only [block, coeffXz, coeffXzz, coeffZz, coeffConstant,
    Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_ofNat] at hx ⊢
  constructor
  · ring
  constructor
  · linear_combination (1 / 2 : F) * hx
  · linear_combination ((x - 2) / 4) * hx

/-- The cubic relation on the third basis vector, obtained directly from
the integral table. -/
theorem z_root_eq (k : ℤ) (x : F)
    (hx : x ^ 3 - 3 * (block k : F) * x + 2 * (coeffConstant k : F) = 0) :
    let z := (x ^ 2 - x) / 2
    let b := (coeffXz k : F)
    let c := (coeffXzz k : F)
    let e := (coeffZz k : F)
    let q := (coeffConstant k : F)
    z ^ 3 - (b + e) * z ^ 2 + (b * e + c - q) * z + q * (c + b) = 0 := by
  dsimp only
  let z := (x ^ 2 - x) / 2
  let b := (coeffXz k : F)
  let c := (coeffXzz k : F)
  let e := (coeffZz k : F)
  let q := (coeffConstant k : F)
  change z ^ 3 - (b + e) * z ^ 2 + (b * e + c - q) * z + q * (c + b) = 0
  have h := multiplication_table k x hx
  have h1 : x * z = b * x - z - q := h.2.1
  have h2 : z ^ 2 = c * x + e * z + q := h.2.2
  linear_combination (z - b) * h2 + c * h1

/-- Closure of the literal three-generator ℤ-span under multiplication. -/
theorem order_span_mul_mem (k : ℤ) (x : F)
    (hx : x ^ 3 - 3 * (block k : F) * x + 2 * (coeffConstant k : F) = 0) :
    let z := (x ^ 2 - x) / 2
    let M := Submodule.span ℤ (Set.range (![1, x, z] : Fin 3 → F))
    ∀ s t : F, s ∈ M → t ∈ M → s * t ∈ M := by
  let z := (x ^ 2 - x) / 2
  let M := Submodule.span ℤ (Set.range (![1, x, z] : Fin 3 → F))
  change ∀ s t : F, s ∈ M → t ∈ M → s * t ∈ M
  have h : ∀ i : Fin 3, (![1, x, z] : Fin 3 → F) i ∈ M := fun i => Submodule.subset_span ⟨i, rfl⟩
  have h0 : 1 ∈ M := h 0
  have h1 : x ∈ M := h 1
  have h2 : z ∈ M := h 2
  have hsc (n : ℤ) {t : F} (ht : t ∈ M) : (n : F) * t ∈ M := by
    simpa only [Algebra.smul_def, eq_intCast] using M.smul_mem n ht
  have hnum (n : ℤ) : (n : F) ∈ M := by simpa only [mul_one] using hsc n h0
  have table := multiplication_table k x hx
  have hx2 : x ^ 2 ∈ M := by
    rw [table.1]
    exact M.add_mem h1 (by simpa only [Int.cast_ofNat] using hsc 2 h2)
  have hxz : x * z ∈ M := by
    rw [table.2.1]
    exact M.sub_mem (M.sub_mem (hsc _ h1) h2) (hnum _)
  have hz2 : z ^ 2 ∈ M := by
    rw [table.2.2]
    exact M.add_mem (M.add_mem (hsc _ h1) (hsc _ h2)) (hnum _)
  have hb (i j : Fin 3) : (![1, x, z] : Fin 3 → F) i * (![1, x, z] : Fin 3 → F) j ∈ M := by
    fin_cases i <;> fin_cases j
    · change (1 : F) * 1 ∈ M
      simpa only [one_mul] using h0
    · change (1 : F) * x ∈ M
      simpa only [one_mul] using h1
    · change (1 : F) * z ∈ M
      simpa only [one_mul] using h2
    · change x * 1 ∈ M
      simpa only [mul_one] using h1
    · change x * x ∈ M
      simpa only [pow_two] using hx2
    · exact hxz
    · change z * 1 ∈ M
      simpa only [mul_one] using h2
    · change z * x ∈ M
      rw [mul_comm]
      exact hxz
    · change z * z ∈ M
      simpa only [pow_two] using hz2
  intro s t hs ht
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨i, rfl⟩ := hs
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨j, rfl⟩ := ht
      exact hb i j
    | zero => simpa only [mul_zero] using M.zero_mem
    | add t₁ t₂ _ _ h₁ h₂ => simpa only [mul_add] using M.add_mem h₁ h₂
    | smul n t _ h₁ =>
      rw [mul_smul_comm]
      exact M.smul_mem n h₁
  | zero => simpa only [zero_mul] using M.zero_mem
  | add s₁ s₂ _ _ h₁ h₂ => simpa only [add_mul] using M.add_mem h₁ h₂
  | smul n s _ h₁ =>
    rw [smul_mul_assoc]
    exact M.smul_mem n h₁

/-- A genuine subalgebra, whose underlying integer lattice is exactly the
displayed three-generator span. -/
def cyclic_order (k : ℤ) (x : F)
    (hx : x ^ 3 - 3 * (block k : F) * x + 2 * (coeffConstant k : F) = 0) : Subalgebra ℤ F := by
  let z := (x ^ 2 - x) / 2
  let M := Submodule.span ℤ (Set.range (![1, x, z] : Fin 3 → F))
  have h1 : (1 : F) ∈ M := Submodule.subset_span ⟨0, rfl⟩
  exact {
    carrier := M
    mul_mem' := fun {a b} ha hb => order_span_mul_mem k x hx a b ha hb
    add_mem' := M.add_mem
    algebraMap_mem' := fun n => by
      change algebraMap ℤ F n ∈ M
      simpa only [Algebra.smul_def, mul_one] using M.smul_mem n h1
  }

theorem cyclic_order_toSubmodule (k : ℤ) (x : F)
    (hx : x ^ 3 - 3 * (block k : F) * x + 2 * (coeffConstant k : F) = 0) :
    (cyclic_order k x hx).toSubmodule =
      Submodule.span ℤ (Set.range (![1, x, (x ^ 2 - x) / 2] : Fin 3 → F)) := by
  rfl

open Polynomial D5.S1.Scale

variable {F : Type*} [Field F] [CharZero F]

/-- Both nontrivial order generators are integral by explicit monic cubic
relations, independently of any claim that the order is maximal. -/
theorem order_generators_integral (k : ℤ) (x : F)
    (hx : x ^ 3 - 3 * (block k : F) * x + 2 * (coeffConstant k : F) = 0) :
    IsIntegral ℤ x ∧ IsIntegral ℤ ((x ^ 2 - x) / 2) := by
  let z := (x ^ 2 - x) / 2
  let b := coeffXz k
  let c := coeffXzz k
  let e := coeffZz k
  let q := coeffConstant k
  constructor
  · let f : Cubic ℤ := ⟨1, 0, -3 * block k, 2 * q⟩
    refine ⟨f.toPoly, Cubic.monic_of_a_eq_one rfl, ?_⟩
    change Polynomial.aeval x f.toPoly = 0
    simp only [f, Cubic.toPoly, map_add, map_mul, map_pow, Polynomial.aeval_X,
      eq_intCast, map_intCast, map_neg, map_ofNat, map_zero, Int.cast_one,
      one_mul, zero_mul, add_zero]
    linear_combination hx
  · let f : Cubic ℤ := ⟨1, -(b + e), b * e + c - q, q * (c + b)⟩
    refine ⟨f.toPoly, Cubic.monic_of_a_eq_one rfl, ?_⟩
    change Polynomial.aeval z f.toPoly = 0
    simp only [f, Cubic.toPoly, map_add, map_mul, map_pow, Polynomial.aeval_X,
      eq_intCast, map_intCast, map_neg, map_sub, Int.cast_one, one_mul]
    have hz := z_root_eq k x hx
    dsimp only at hz
    change z ^ 3 - ((b : F) + (e : F)) * z ^ 2 + ((b : F) * (e : F) + (c : F) - (q : F)) * z +
      (q : F) * ((c : F) + (b : F)) = 0 at hz
    linear_combination hz

theorem cyclic_order_le_integralClosure (k : ℤ) (x : F)
    (hx : x ^ 3 - 3 * (block k : F) * x + 2 * (coeffConstant k : F) = 0) :
    cyclic_order k x hx ≤ integralClosure ℤ F := by
  change (cyclic_order k x hx).toSubmodule ≤ (integralClosure ℤ F).toSubmodule
  rw [cyclic_order_toSubmodule, Submodule.span_le]
  rintro y ⟨i, rfl⟩
  have h := order_generators_integral k x hx
  fin_cases i
  · exact isIntegral_one
  · exact h.1
  · exact h.2

/-- The actual Lucas half-parameter is even, since L is four modulo 72. -/
theorem native_even_half (j : ℕ) (hj : 1 ≤ j) :
    ∃ k : ℤ, Even k ∧ goldenLucas (3 ^ j) = 2 * k := by
  let L := goldenLucas (3 ^ j)
  have hLs : (L : ZMod 72) = (4 : ZMod 72) := (golden_cubic_lucas_block j hj).1
  have hd : (72 : ℤ) ∣ L - 4 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 4 L 72).mp (by simpa only [Int.cast_ofNat] using hLs.symm)
  obtain ⟨n, hn⟩ := hd
  refine ⟨2 + 36 * n, ⟨1 + 18 * n, by ring⟩, ?_⟩
  change L = 2 * (2 + 36 * n)
  omega

/-- Specialize the split-off denominator-two order to each actual Lucas
block. The half-parameter is derived from the native modulo-72 theorem. -/
theorem native_order (j : ℕ) (hj : 1 ≤ j) (x : F)
    (hx : let L := goldenLucas (3 ^ j)
          let B : ℤ := L ^ 2 + 3
          x ^ 3 - 3 * (B : F) * x + 2 * (B : F) * (L : F) = 0) :
    ∃ S : Subalgebra ℤ F, S ≤ integralClosure ℤ F ∧
      S.toSubmodule = Submodule.span ℤ (Set.range (![1, x, (x ^ 2 - x) / 2] : Fin 3 → F)) := by
  let L := goldenLucas (3 ^ j)
  obtain ⟨k, _, hL⟩ := native_even_half j hj
  change L = 2 * k at hL
  have hB : L ^ 2 + 3 = block k := by rw [hL]; unfold block; ring
  have hq : (L ^ 2 + 3) * L = coeffConstant k := by rw [hB, hL]; rfl
  have h : x ^ 3 - 3 * (block k : F) * x + 2 * (coeffConstant k : F) = 0 := by
    change x ^ 3 - 3 * ((L ^ 2 + 3 : ℤ) : F) * x + 2 * ((L ^ 2 + 3 : ℤ) : F) * (L : F) = 0 at hx
    rw [← hB, ← hq]
    push_cast
    push_cast at hx
    linear_combination hx
  exact ⟨cyclic_order k x h, cyclic_order_le_integralClosure k x h, cyclic_order_toSubmodule k x h⟩
end IntegralOrder

/-- For the actual parity class of the half-Lucas parameter, the integer
table reduces to x²=x, xz=z, z²=z at two. -/
theorem coeff_mod_two (k : ℤ) (hk : Even k) :
    (coeffXz k : ZMod 2) = 0 ∧
    (coeffXzz k : ZMod 2) = 0 ∧
    (coeffZz k : ZMod 2) = 1 ∧
    (coeffConstant k : ZMod 2) = 0 := by
  obtain ⟨t, ht⟩ := hk
  have hz : (k : ZMod 2) = 0 := by
    rw [ht, Int.cast_add, ← two_mul]
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
  simp only [coeffXz, coeffXzz, coeffZz, coeffConstant, block,
    Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_ofNat, hz]
  decide

/-- The three coordinate idempotents of the split reduction. This theorem
does not assert they are all nonzero in an arbitrary quotient ring. -/
theorem coordinate_idempotents {R : Type*} [CommRing R] (x z : R)
    (hx : x ^ 2 = x) (hz : z ^ 2 = z) (hxz : x * z = z) :
    let a := 1 - x
    let b := x - z
    a ^ 2 = a ∧ b ^ 2 = b ∧ z ^ 2 = z ∧ a * b = 0 ∧ a * z = 0 ∧ b * z = 0 ∧ a + b + z = 1 := by
  dsimp only
  refine ⟨?_, ?_, hz, ?_, ?_, ?_, ?_⟩
  · linear_combination hx
  · linear_combination hx + hz - 2 * hxz
  · linear_combination -hx + hxz
  · linear_combination -hxz
  · linear_combination hxz - hz
  · ring

/-- The actual coefficient reduction and the unreduced table imply
the displayed coordinate idempotents in every characteristic-two realization. -/
theorem cyclic_order_mod_two_idempotents {R : Type*} [CommRing R] [Algebra (ZMod 2) R]
    (k : ℤ) (hk : Even k) (x z : R)
    (hx : x ^ 2 = x + (2 : R) * z)
    (hxz : x * z = (coeffXz k : R) * x - z - (coeffConstant k : R))
    (hz : z ^ 2 = (coeffXzz k : R) * x + (coeffZz k : R) * z + (coeffConstant k : R)) :
    (1 - x) ^ 2 = 1 - x ∧ (x - z) ^ 2 = x - z ∧ z ^ 2 = z ∧
      (1 - x) * (x - z) = 0 ∧ (1 - x) * z = 0 ∧ (x - z) * z = 0 ∧ (1 - x) + (x - z) + z = 1 := by
  obtain ⟨hb, hc, he, hq⟩ := coeff_mod_two k hk
  have hbR : (coeffXz k : R) = 0 := by
    simpa only [map_intCast, map_zero] using congrArg (algebraMap (ZMod 2) R) hb
  have hcR : (coeffXzz k : R) = 0 := by
    simpa only [map_intCast, map_zero] using congrArg (algebraMap (ZMod 2) R) hc
  have heR : (coeffZz k : R) = 1 := by
    simpa only [map_intCast, map_one] using congrArg (algebraMap (ZMod 2) R) he
  have hqR : (coeffConstant k : R) = 0 := by
    simpa only [map_intCast, map_zero] using congrArg (algebraMap (ZMod 2) R) hq
  have h2 : (2 : R) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (algebraMap (ZMod 2) R) (show (2 : ZMod 2) = 0 by decide)
  have hm (z : R) : -z = z := by
    have hz0 := congrArg (·*z) h2
    linear_combination -hz0
  rw [h2, zero_mul, add_zero] at hx
  rw [hbR, hqR, zero_mul, zero_sub, sub_zero, hm] at hxz
  rw [hcR, heR, hqR, zero_mul, one_mul, zero_add, add_zero] at hz
  exact coordinate_idempotents x z hx hz hxz

open Algebra Matrix

/-- Exact trace discriminant of the literal three-vector order, if the
displayed vectors are marked as a rational basis. This is a lattice
discriminant, not a field discriminant or a maximality assertion. -/
theorem cyclic_order_discr {F : Type*} [Field F] [Algebra ℚ F]
    (k : ℤ) (x : F)
    (hx : x ^ 3 - 3 * (block k : F) * x + 2 * (coeffConstant k : F) = 0)
    (b : Module.Basis (Fin 3) ℚ F)
    (h0 : b 0 = 1) (h1 : b 1 = x) (h2 : b 2 = (x ^ 2 - x) / 2) :
    Algebra.discr ℚ b = 81 * (block k : ℚ) ^ 2 := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  let z := (x ^ 2 - x) / 2
  let d := (block k : ℚ)
  let p := (coeffXz k : ℚ)
  let q := (coeffConstant k : ℚ)
  let c := (coeffXzz k : ℚ)
  let e := (coeffZz k : ℚ)
  have htable := multiplication_table k x hx
  have hx2 : x * x = x + (2 : ℚ) • z := by
    rw [← pow_two, Algebra.smul_def, map_ofNat]
    exact htable.1
  have hxz : x * z = p • x - z - algebraMap ℚ F q := by
    simp only [Algebra.smul_def, p, q, map_intCast]
    exact htable.2.1
  have hz2 : z * z = c • x + e • z + algebraMap ℚ F q := by
    rw [← pow_two]
    simp only [Algebra.smul_def, c, e, q, map_intCast]
    exact htable.2.2
  have hrepr (a d e : ℚ) (i : Fin 3) :
      b.repr (a • b 0 + d • b 1 + e • b 2) i =
        a * (if i = 0 then 1 else 0) + d * (if i = 1 then 1 else 0)
          + e * (if i = 2 then 1 else 0) := by
    simp [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  have hx0 : x * b 0 = (0 : ℚ) • b 0 + 1 • b 1 + 0 • b 2 := by simp [h0, h1]
  have hx1 : x * b 1 = (0 : ℚ) • b 0 + (1 : ℚ) • b 1 + (2 : ℚ) • b 2 := by
    rw [h1, hx2]
    change b 2 = z at h2
    simp only [h2, zero_smul, one_smul, zero_add]
  have hx2' : x * b 2 = (-q) • b 0 + p • b 1 + (-1) • b 2 := by
    change b 2 = z at h2
    rw [h2, hxz]
    simp [h0, h1, Algebra.smul_def]
    ring
  have hz0 : z * b 0 = (0 : ℚ) • b 0 + 0 • b 1 + 1 • b 2 := by simp [h0, h2, z]
  have hz1 : z * b 1 = (-q) • b 0 + p • b 1 + (-1) • b 2 := by
    rw [h1, mul_comm, hxz]
    simp [h0, h2, z, Algebra.smul_def]
    ring
  have hz2' : z * b 2 = q • b 0 + c • b 1 + e • b 2 := by
    change b 2 = z at h2
    rw [h2, hz2]
    simp [h0, h1, Algebra.smul_def]
    ring
  have htx : trace ℚ F x = 0 := by
    rw [trace_eq_matrix_trace b, Matrix.trace, Fin.sum_univ_three]
    simp only [diag, leftMulMatrix_eq_repr_mul, hx0, hx1, hx2', hrepr]
    norm_num
  have htz : trace ℚ F z = p + e := by
    rw [trace_eq_matrix_trace b, Matrix.trace, Fin.sum_univ_three]
    simp only [diag, leftMulMatrix_eq_repr_mul, hz0, hz1, hz2', hrepr]
    norm_num
  have htc (r : ℚ) : trace ℚ F (algebraMap ℚ F r) = 3 * r := by
    simpa [three_nsmul, mul_add, two_mul, add_assoc, add_comm] using trace_algebraMap_of_basis b r
  have htc' (r : ℚ) : trace ℚ F (r : F) = 3 * r := by
    rw [← map_ratCast (algebraMap ℚ F) r]
    simpa using htc r
  have ht1 : trace ℚ F (1 : F) = 3 := by simpa using htc 1
  have htpe : p + e = 3 * d := by
    simp [p, e, d, coeffXz, coeffZz, block]
    ring
  have hG : traceMatrix ℚ b = !![3, 0, 3 * d;
                               0, 6 * d, -3 * d - 3 * q;
                               3 * d, -3 * d - 3 * q, 3 * e * d + 3 * q] := by
    ext i j
    change b 2 = z at h2
    fin_cases i <;> fin_cases j <;>
      simp [traceMatrix_apply, h0, h1, h2, hx2, hxz, hz2, htx,
        htz, ht1, htc', htpe, mul_comm z x] <;> ring
  rw [discr_def, hG, Matrix.det_fin_three]
  simp only [neg_mul, Fin.isValue, of_apply, cons_val', cons_val_zero,
    cons_val_fin_one, cons_val_one, cons_val, mul_zero, zero_mul, sub_zero, add_zero]
  dsimp [d, q, e, block, coeffConstant, coeffZz]
  push_cast
  ring

open D5.S1.Scale
open scoped IntermediateField

/-- Inside the canonical splitting field of each native block, the
denominator-two order is an actual integral rank-three lattice with
signed trace discriminant 81B². This does not assert maximality. -/
theorem actual_order_discriminant (j : ℕ) (hj : 1 ≤ j) :
    let l := goldenLucas (3 ^ j)
    let p := (GoldenCubicNativeCyclic.cubic (l : ℚ)).toPoly
    let K := p.SplittingField
    ∃ x : K, ∃ S : Subalgebra ℤ K, ∃ b : Module.Basis (Fin 3) ℚ K,
      GoldenCubicNativeCyclic.equation (l : K) x = 0 ∧
      S ≤ integralClosure ℤ K ∧
      S.toSubmodule = Submodule.span ℤ (Set.range b) ∧
      b 0 = 1 ∧ b 1 = x ∧ b 2 = (x ^ 2 - x) / 2 ∧
      Algebra.discr ℚ b = (81 : ℚ) * ((l : ℚ) ^ 2 + 3) ^ 2 := by
  classical
  let l := goldenLucas (3 ^ j)
  let p := (GoldenCubicNativeCyclic.cubic (l : ℚ)).toPoly
  let K := p.SplittingField
  obtain ⟨hfin, _, x, hx, hgen⟩ := GoldenCubicNativeCyclic.field_structure l (GoldenCubicNativeCyclic.native_lucas_mod j hj).1
  obtain ⟨b, h0, h1, h2⟩ := GoldenCubicThueMaximalOrder.cubic_power_basis x
    (IsIntegral.of_finite ℚ x) hgen hfin
  obtain ⟨b', h'0, h'1, h'2⟩ := CubicIntegralLattice.triangular_basis b
    (1 : ℚ) 0 (-(1 / 2)) (1 / 2) (by norm_num) (by norm_num)
  have hb0 : b' 0 = 1 := h'0.trans h0
  have hb1 : b' 1 = x := by rw [h'1, h1, one_smul]
  have hb2 : b' 2 = (x ^ 2 - x) / 2 := by
    rw [h'2, h0, h1, h2]
    simp [Algebra.smul_def, map_neg, map_ofNat]; ring
  have hx' : let L := goldenLucas (3 ^ j)
             let B : ℤ := L ^ 2 + 3
             x ^ 3 - 3 * (B : K) * x + 2 * (B : K) * (L : K) = 0 := by
    dsimp only
    simpa [GoldenCubicNativeCyclic.equation, Int.cast_add, Int.cast_pow, Int.cast_ofNat]
      using hx
  obtain ⟨S, hSint, hS⟩ := native_order j hj x hx'
  refine ⟨x, S, b', hx, hSint, hS.trans ?_, hb0, hb1, hb2, ?_⟩
  · have hb' : (![1, x, (x ^ 2 - x) / 2] : Fin 3 → K) = b' := by
      funext i; fin_cases i <;> simp [hb0, hb1, hb2]
    rw [hb']
  · obtain ⟨k, _, hk⟩ := native_even_half j hj
    change l = 2 * k at hk
    have hB : l ^ 2 + 3 = block k := by rw [hk]; unfold block; ring
    have hq : (l ^ 2 + 3) * l = coeffConstant k := by rw [hB, hk]; rfl
    have hy : x ^ 3 - 3 * (block k : K) * x + 2 * (coeffConstant k : K) = 0 := by
      have hbcast : (block k : K) = (l : K) ^ 2 + 3 := by
        simp only [← hB, Int.cast_add, Int.cast_pow, Int.cast_ofNat]
      have hqcast : (coeffConstant k : K) = ((l : K) ^ 2 + 3) * (l : K) := by
        calc
          (coeffConstant k : K) = (((l ^ 2 + 3) * l : ℤ) : K) :=
            congrArg (fun v : ℤ => (v : K)) hq.symm
          _ = ((l ^ 2 + 3 : ℤ) : K) * (l : K) := Int.cast_mul _ _
          _ = _ := by
            rw [hB, hbcast]
      rw [hbcast, hqcast, ← mul_assoc]
      exact hx
    change Algebra.discr ℚ b' = (81 : ℚ) * ((l : ℚ) ^ 2 + 3) ^ 2
    rw [cyclic_order_discr k x hy b' hb0 hb1 hb2,
      show (block k : ℚ) = (l : ℚ) ^ 2 + 3 by exact_mod_cast hB.symm]

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclicOrder
