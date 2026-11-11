/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetCommutant
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetCommutant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full actual-action Fp-linear commutant, unique Toeplitz coordinates, multiplication and units. -/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore

/-!
# Multiplication and shift coordinates of the original odd-prime jet commutant

The original polynomial representation is retained on `Polynomial.degreeLT K p`.
Only prime-field linearity is imposed on its endomorphisms. The lower blocks
are scalars and the highest block is an arbitrary prime-field-linear map.

The divided-monomial centralizer computation is classical. The original-action
logarithm and polynomial suppliers are reused from `OddPrimeJetDeformation`;
normal form and nilpotent-unit calculus are retained in `OddPrimeJetCommutantCore`.
This module proves ordered multiplication and the unique shift-coordinate finish.
No novelty is asserted.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant

open Polynomial Finset Module OddPrimeJetDeformation
open scoped BigOperators

universe uK
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type uK} [Field K] [Algebra (ZMod p) K]

local notation "F" => ZMod p
local notation "V" => Polynomial.degreeLT K p
local notation "E" => Multiplicative K
local notation "D" => derivativeEnd (p := p) (K := K)

def fieldScalar (a : K) : K →ₗ[F] K :=
  (Algebra.lsmul F K K a).restrictScalars F

private theorem scalar_power_mul (a b : K) (r s : ℕ) :
    (scalarMap (p := p) a * ((D).restrictScalars F) ^ r) *
        (scalarMap b * ((D).restrictScalars F) ^ s) =
      scalarMap (a * b) * ((D).restrictScalars F) ^ (r + s) := by
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, scalarMap_apply, restricted_derivative_pow_local,
    map_smul, smul_smul]
  rw [pow_add, Module.End.mul_apply]

private theorem scalar_power_top (a : K) (r : ℕ) (T : K →ₗ[F] K) :
    (scalarMap (p := p) a * ((D).restrictScalars F) ^ r) * topMap T =
      if r = 0 then topMap ((fieldScalar a).comp T) else 0 := by
  split_ifs with hr
  · subst r
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, pow_zero, Module.End.one_apply, topMap,
      LinearMap.comp_apply, LinearMap.restrictScalars_apply, scalarMap_apply]
    exact ((constantLinear (p := p) (K := K)).map_smul a _).symm
  · apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, topMap, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, restricted_derivative_pow_local]
    rw [derivative_pow_constant r (by omega), map_zero]
    rfl

private theorem top_scalar_power (T : K →ₗ[F] K) (a : K) (r : ℕ) :
    topMap (p := p) T * (scalarMap a * ((D).restrictScalars F) ^ r) =
      if r = 0 then topMap (T.comp (fieldScalar a)) else 0 := by
  split_ifs with hr
  · subst r
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, pow_zero, Module.End.one_apply, topMap,
      LinearMap.comp_apply, LinearMap.restrictScalars_apply, scalarMap_apply,
      restricted_derivative_pow_local, map_smul]
    rfl
  · apply LinearMap.ext
    intro v
    have hp : 2 < p := Fact.out
    have hz : (D ^ (p - 1)) ((D ^ r) v) = 0 := by
      rw [← Module.End.mul_apply, ← pow_add,
        pow_eq_zero_of_le (by omega : p ≤ (p - 1) + r) (derivative_pow_prime (p := p) (K := K))]
      rfl
    simp only [Module.End.mul_apply, topMap, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, restricted_derivative_pow_local,
      scalarMap_apply, map_smul, hz, smul_zero, map_zero, LinearMap.zero_apply]

theorem top_top (T U : K →ₗ[F] K) :
    topMap (p := p) T * topMap U = 0 := by
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, topMap, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, restricted_derivative_pow_local]
  rw [derivative_pow_constant (p - 1) (by have hp : 2 < p := Fact.out; omega)]
  simp

theorem topMap_add (T U : K →ₗ[F] K) :
    topMap (p := p) (T + U) = topMap T + topMap U := by
  apply LinearMap.ext
  intro v
  simp [topMap]

private theorem scalar_part_top (c : Fin p → K) (U : K →ₗ[F] K) :
    (∑ j : Fin p, scalarMap (p := p) (c j) * ((D).restrictScalars F) ^ (p - 1 - j.val)) *
        topMap U = topMap ((fieldScalar (c (leadingIndex (p := p)))).comp U) := by
  classical
  rw [Finset.sum_mul, Finset.sum_eq_single (leadingIndex (p := p))]
  · simpa only [leadingIndex, Nat.sub_self, pow_zero, mul_one, ite_true] using
      scalar_power_top (p := p) (c (leadingIndex (p := p))) 0 U
  · intro b hb hbl
    have hne : p - 1 - b.val ≠ 0 := by
      have hb' := b.isLt
      have hne' : b.val ≠ p - 1 := fun h => hbl (Fin.ext h)
      omega
    rw [scalar_power_top, if_neg hne]
  · simp

private theorem top_scalar_part (T : K →ₗ[F] K) (c : Fin p → K) :
    topMap (p := p) T *
        (∑ j : Fin p, scalarMap (c j) * ((D).restrictScalars F) ^ (p - 1 - j.val)) =
      topMap (T.comp (fieldScalar (c (leadingIndex (p := p))))) := by
  classical
  rw [Finset.mul_sum, Finset.sum_eq_single (leadingIndex (p := p))]
  · simpa only [leadingIndex, Nat.sub_self, pow_zero, mul_one, ite_true] using
      top_scalar_power (p := p) T (c (leadingIndex (p := p))) 0
  · intro b hb hbl
    have hne : p - 1 - b.val ≠ 0 := by
      have hb' := b.isLt
      have hne' : b.val ≠ p - 1 := fun h => hbl (Fin.ext h)
      omega
    rw [top_scalar_power, if_neg hne]
  · simp

private theorem multiplication_expansion (c d : Fin p → K) (T U : K →ₗ[F] K) :
    toeplitzDegree (p := p) c T * toeplitzDegree d U =
      (∑ i : Fin p, ∑ k : Fin p,
        scalarMap (c i * d k) * ((D).restrictScalars F) ^
          ((p - 1 - i.val) + (p - 1 - k.val))) +
      topMap ((fieldScalar (c (leadingIndex (p := p)))).comp U +
        T.comp (fieldScalar (d (leadingIndex (p := p))))) := by
  simp only [toeplitzDegree, add_mul, mul_add]
  rw [scalar_part_top, top_scalar_part, top_top, add_zero, topMap_add]
  simp only [Finset.sum_mul, Finset.mul_sum, scalar_power_mul]
  rw [Finset.sum_comm]
  abel

private theorem derivative_coefficient (j : Fin p) (w : V) :
    coefficientZero ((D ^ j.val) w) =
      (j.val.factorial : K) * (w : K[X]).coeff j.val := by
  change ((D ^ j.val) w : K[X]).coeff 0 = _
  rw [derivative_pow_coe_local, coeff_iterate_derivative]
  simp [Nat.descFactorial_eq_factorial_mul_choose]

private theorem topCoefficient_toeplitzDegree (c : Fin p → K) (hc : c 0 = 0)
    (T : K →ₗ[F] K) (j : Fin p) (z : K) :
    topCoefficient (toeplitzDegree (p := p) c T) j z =
      if j = 0 then T z else c j * z := by
  classical
  rw [topCoefficient_apply, derivative_coefficient, toeplitzDegree_topInput c hc,
    divided_sum_coefficient]
  have hf := factorial_ne_zero (K := K) j
  field_simp

private theorem topInput_derivative_coefficient (n : ℕ) (z : K) :
    coefficientZero ((D ^ n) (topInput (p := p) (K := K) z)) =
      if n = p - 1 then z else 0 := by
  classical
  change ((D ^ n) (topInput (p := p) (K := K) z) : K[X]).coeff 0 = _
  rw [derivative_pow_coe_local, coeff_iterate_derivative]
  by_cases hn : n = p - 1
  · subst n
    simp [topInput, dividedMonomial, Nat.descFactorial_eq_factorial_mul_choose,
      smul_eq_mul]
    have hf := factorial_ne_zero (K := K) (leadingIndex (p := p))
    dsimp only [leadingIndex] at hf
    field_simp
  · simp [topInput, dividedMonomial, hn, Nat.descFactorial_eq_factorial_mul_choose]

private theorem topCoefficient_scalar_power (a : K) (r : ℕ) (j : Fin p) (z : K) :
    topCoefficient (scalarMap (p := p) a * ((D).restrictScalars F) ^ r) j z =
      if j.val + r = p - 1 then a * z else 0 := by
  rw [topCoefficient_apply]
  simp only [Module.End.mul_apply, scalarMap_apply, restricted_derivative_pow_local,
    map_smul]
  rw [← Module.End.mul_apply, ← pow_add, topInput_derivative_coefficient]
  split_ifs <;> simp [smul_eq_mul]

private theorem topCoefficient_topMap (T : K →ₗ[F] K) (j : Fin p) (z : K) :
    topCoefficient (topMap (p := p) T) j z = if j = 0 then T z else 0 := by
  rw [topCoefficient_apply, topMap_topInput, dividedMonomial_zero]
  by_cases hj : j = 0
  · subst j; simp [coefficientZero, constantLinear]
  · rw [derivative_pow_constant j.val (by
      have hne : j.val ≠ 0 := fun h => hj (Fin.ext h)
      omega), map_zero, if_neg hj]

private theorem topCoefficient_add (X Y : V →ₗ[F] V) (j : Fin p) (z : K) :
    topCoefficient (X + Y) j z = topCoefficient X j z + topCoefficient Y j z := by
  simp [topCoefficient, map_add]

private theorem topCoefficient_sum {ι : Type*} (s : Finset ι)
    (f : ι → V →ₗ[F] V) (j : Fin p) (z : K) :
    topCoefficient (∑ i ∈ s, f i) j z = ∑ i ∈ s, topCoefficient (f i) j z := by
  simp [topCoefficient, map_sum]

/-- Scalar convolution, indexed by output divided degree rather than shift. -/
def productFamily (c d : Fin p → K) (j : Fin p) : K :=
  if j = 0 then 0 else ∑ i : Fin p, ∑ k : Fin p,
    if i.val + k.val = p - 1 + j.val then c i * d k else 0

def topConvolution (c d : Fin p → K) : K :=
  ∑ i : Fin p, ∑ k : Fin p,
    if i.val + k.val = p - 1 then c i * d k else 0

/-- Composition order is output scalar after U, and T after input scalar. -/
def productTop (c d : Fin p → K) (T U : K →ₗ[F] K) : K →ₗ[F] K :=
  (fieldScalar (c (leadingIndex (p := p)))).comp U +
    T.comp (fieldScalar (d (leadingIndex (p := p)))) + fieldScalar (topConvolution c d)

private theorem product_coordinate (c d : Fin p → K) (T U : K →ₗ[F] K)
    (j : Fin p) (z : K) :
    topCoefficient (toeplitzDegree (p := p) c T * toeplitzDegree d U) j z =
      if j = 0 then productTop c d T U z else productFamily c d j * z := by
  classical
  rw [multiplication_expansion, topCoefficient_add]
  simp only [topCoefficient_sum, topCoefficient_scalar_power, topCoefficient_topMap]
  have he (i k : Fin p) :
      (j.val + (p - 1 - i.val + (p - 1 - k.val)) = p - 1) ↔
        i.val + k.val = p - 1 + j.val := by
    have hi := i.isLt
    have hk := k.isLt
    omega
  simp_rw [he]
  by_cases hj : j = 0
  · subst j
    simp only [Fin.val_zero, Nat.add_zero, ite_true, productTop,
      LinearMap.add_apply, LinearMap.comp_apply]
    change (∑ i : Fin p, ∑ k : Fin p,
      if i.val + k.val = p - 1 then (c i * d k) * z else 0) +
        (c (leadingIndex (p := p)) * U z + T (d (leadingIndex (p := p)) * z)) =
      c (leadingIndex (p := p)) * U z + T (d (leadingIndex (p := p)) * z) +
        topConvolution c d * z
    simp only [topConvolution, Finset.sum_mul, ite_mul, zero_mul]
    ring
  · simp only [if_neg hj, productFamily, add_zero]
    simp only [Finset.sum_mul, ite_mul, zero_mul]

/-- Explicit multiplication of the unique scalar and arbitrary-top normal forms. -/
theorem toeplitzDegree_mul (c d : Fin p → K) (T U : K →ₗ[F] K) :
    toeplitzDegree (p := p) c T * toeplitzDegree d U =
      toeplitzDegree (productFamily c d) (productTop c d T U) := by
  refine commuting_ext _ _ ?_ (toeplitzDegree_derivative _ _) ?_
  · intro v
    simp only [Module.End.mul_apply]
    rw [toeplitzDegree_derivative, toeplitzDegree_derivative]
  · intro z
    rw [top_coefficient_reconstruct, top_coefficient_reconstruct]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [product_coordinate, topCoefficient_toeplitzDegree _ (by simp [productFamily])]

def shiftFamily (a : Fin (p - 1) → K) (j : Fin p) : K :=
  if h : j.val = 0 then 0 else a ⟨p - 1 - j.val, by have hj := j.isLt; omega⟩

private theorem shiftFamily_zero (a : Fin (p - 1) → K) : shiftFamily a (0 : Fin p) = 0 := by
  simp [shiftFamily]

private theorem toeplitz_as_degree (a : Fin (p - 1) → K) (T : K →ₗ[F] K) :
    toeplitz (p := p) a T = toeplitzDegree (shiftFamily a) T := by
  classical
  have hp : 2 < p := Fact.out
  unfold toeplitz toeplitzDegree
  apply congrArg (fun A : V →ₗ[F] V => A + topMap T)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin p))]
  have hz : scalarMap (p := p) (K := K) 0 = 0 := by
    apply LinearMap.ext
    intro v
    simp [scalarMap_apply]
  simp only [shiftFamily_zero, hz, zero_mul, add_zero]
  refine Finset.sum_bij (fun (r : Fin (p - 1)) _ => (⟨p - 1 - r.val, by have hr := r.isLt; omega⟩ : Fin p))
    ?_ ?_ ?_ ?_
  · intro r hr
    have hr' := r.isLt
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_zero] at hh
    omega
  · intro r hr s hs h
    have hr' := r.isLt
    have hs' := s.isLt
    apply Fin.ext
    have hh := congrArg Fin.val h
    change p - 1 - r.val = p - 1 - s.val at hh
    omega
  · intro j hj
    have hj0 : j.val ≠ 0 := by
      intro h
      exact (Finset.mem_erase.mp hj).1 (Fin.ext h)
    refine ⟨⟨p - 1 - j.val, by have hj' := j.isLt; omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    have hj' := j.isLt
    dsimp
    omega
  · intro r hr
    have hr' := r.isLt
    have hn : p - 1 - r.val ≠ 0 := by omega
    have he : p - 1 - (p - 1 - r.val) = r.val := by omega
    simp only [shiftFamily, dif_neg hn, he]

private theorem shiftFamily_surjective (c : Fin p → K) (hc : c 0 = 0) :
    ∃ a : Fin (p - 1) → K, shiftFamily a = c := by
  refine ⟨fun r => c ⟨p - 1 - r.val, by have hr := r.isLt; omega⟩, ?_⟩
  funext j
  by_cases hj : j.val = 0
  · have he : j = 0 := Fin.ext hj
    subst j
    simp [shiftFamily_zero, hc]
  · simp only [shiftFamily, dif_neg hj]
    congr 1
    apply Fin.ext
    have hj' := j.isLt
    dsimp
    omega

private theorem shiftFamily_injective (a b : Fin (p - 1) → K)
    (h : shiftFamily a = shiftFamily b) : a = b := by
  funext r
  have hr := r.isLt
  have hj : p - 1 - r.val < p := by omega
  have hn : p - 1 - r.val ≠ 0 := by omega
  have he := congrFun h (⟨p - 1 - r.val, hj⟩ : Fin p)
  have hh : p - 1 - (p - 1 - r.val) = r.val := by omega
  simpa only [shiftFamily, dif_neg hn, hh] using he

/-- Unique lower-Toeplitz scalars and a completely arbitrary top End_Fp(K) map,
for the actual labeled original action. -/
theorem actual_commutant_iff_unique_toeplitz (q : K →ₗ[F] K) (hq1 : q 1 = 0)
    (X : V →ₗ[F] V) :
    commutesOriginal (p := p) q X ↔
      ∃! C : (Fin (p - 1) → K) × (K →ₗ[F] K), X = toeplitz C.1 C.2 := by
  constructor
  · intro hX
    obtain ⟨c, T, hc, he⟩ := (actual_commutant_normal_form q hq1 X).mp hX
    obtain ⟨a, ha⟩ := shiftFamily_surjective c hc
    refine ⟨(a, T), ?_, ?_⟩
    · change X = toeplitz a T
      rw [toeplitz_as_degree, ha]; exact he
    · rintro ⟨b, U⟩ hU
      have h := toeplitzDegree_injective (shiftFamily b) (shiftFamily a)
        (shiftFamily_zero b) (shiftFamily_zero a) U T (by
          rw [← toeplitz_as_degree, ← toeplitz_as_degree, ← hU, toeplitz_as_degree, ha]
          exact he)
      exact Prod.ext (shiftFamily_injective b a h.1) h.2
  · rintro ⟨⟨a, T⟩, h, _⟩
    apply (actual_commutant_normal_form q hq1 X).mpr
    exact ⟨shiftFamily a, T, shiftFamily_zero a, h.trans (toeplitz_as_degree a T)⟩

end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant
