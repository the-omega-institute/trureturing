import D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample

/-!
# Rectangular polynomial tensor trace obstruction

For the original Elmer--Kadr polynomial contragredients, finite-field power sums
recover unsigned Hasse coefficients from the actual action at parameter `-a`.
Under `n + m + 2 ≤ card K`, every equivariant composite between `V_(n+m+1)`
and `V_(n+1) ⊗ V_(m+1)` has zero trace when `choose (n+m) n` vanishes in K.
The rectangular generator uses no parity assumption on either index.

Source: Elmer--Kadr, DOI 10.1007/s13366-026-00855-9, Conjecture 3.7(a).
The polynomial modules, actions and bases are those of
`ElmerKadrTensorCounterexample`; their signed coefficient convention is not used.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.RectangularTensorObstruction

open ElmerKadrTensorCounterexample
open scoped TensorProduct
open Finset Polynomial

universe uK

section PolynomialCoefficients

variable (K : Type uK) [Field K]

-- These are UNSIGNED Hasse coefficients: the actual contragredient action
-- at parameter -a has expansion sum a^k A_k. This removes sign scalars from
-- the generators, without changing or postulating any representation.
private def coefficient (d k : ℕ) : Module.End K (DualPower K d) :=
  Matrix.toLin (dualBasis K d) (dualBasis K d)
    (Matrix.of fun j i =>
      if j.val = i.val + k then (j.val.choose i.val : K) else 0)

private theorem coefficient_matrix (d k : ℕ) (i j : Fin d) :
    (dualBasis K d).repr (coefficient K d k (dualBasis K d i)) j =
      if j.val = i.val + k then (j.val.choose i.val : K) else 0 := by
  classical
  rw [← LinearMap.toMatrix_apply, coefficient, LinearMap.toMatrix_toLin]
  rfl

private theorem coefficient_basis_value (d k : ℕ) (i j : Fin d) :
    coefficient K d k (dualBasis K d i) (Polynomial.degreeLT.basis K d j) =
      if j.val = i.val + k then (j.val.choose i.val : K) else 0 := by
  simpa only [dualBasis, Module.Basis.dualBasis_repr]
    using coefficient_matrix K d k i j

-- Formula (12), proved on the ACTUAL polynomial translation dual.
private theorem action_basis_value (d : ℕ) (a : K) (i j : Fin d) :
    dualAction K d (Multiplicative.ofAdd a) (dualBasis K d i)
      (Polynomial.degreeLT.basis K d j) =
        (j.val.choose i.val : K) * (-a) ^ (j.val - i.val) := by
  change (Polynomial.degreeLT.basis K d).dualBasis i
    ((Polynomial.taylorLinearEquiv (-a) d)
      (Polynomial.degreeLT.basis K d j)) = _
  rw [Module.Basis.dualBasis_apply, Polynomial.degreeLT.basis_repr]
  change (Polynomial.taylor (-a)
    (Polynomial.degreeLT.basis K d j : K[X])).coeff i = _
  rw [Polynomial.degreeLT.basis_val, Polynomial.taylor_coeff,
    ← Polynomial.monomial_one_right_eq_X_pow, Polynomial.hasseDeriv_monomial]
  simp

private theorem action_expansion (r d : ℕ) (hrd : r ≤ d) (a : K) :
    dualAction K r (Multiplicative.ofAdd (-a)) =
      ∑ k : Fin d, a ^ k.val • coefficient K r k.val := by
  classical
  apply (dualBasis K r).ext
  intro i
  apply (Polynomial.degreeLT.basis K r).ext
  intro j
  simp only [LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul,
    smul_eq_mul]
  rw [action_basis_value, neg_neg]
  simp_rw [coefficient_basis_value]
  by_cases hij : i.val ≤ j.val
  · let k : Fin d := ⟨j.val - i.val, by have := j.isLt; omega⟩
    rw [Finset.sum_eq_single k]
    · dsimp only [k]
      rw [if_pos (by omega : j.val = i.val + (j.val - i.val))]
      ring
    · intro l _ hl
      have hne : j.val ≠ i.val + l.val := by
        intro he
        apply hl
        apply Fin.ext
        dsimp [k]
        omega
      simp [hne]
    · simp
  · have hchoose : j.val.choose i.val = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hchoose, Nat.cast_zero, zero_mul]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro k _
    have hne : j.val ≠ i.val + k.val := by omega
    simp [hne]

private theorem coefficient_basis_of_lt (d k : ℕ) (i : Fin d)
    (hi : i.val + k < d) :
    coefficient K d k (dualBasis K d i) =
      ((i.val + k).choose i.val : K) • dualBasis K d ⟨i.val + k, hi⟩ := by
  classical
  apply (Polynomial.degreeLT.basis K d).ext
  intro j
  rw [coefficient_basis_value]
  simp only [LinearMap.smul_apply, smul_eq_mul, dualBasis,
    Module.Basis.dualBasis_apply_self, Fin.ext_iff]
  split_ifs with h
  · rw [h, mul_one]
  · rw [mul_zero]

private theorem coefficient_basis_of_ge (d k : ℕ) (i : Fin d)
    (hi : d ≤ i.val + k) :
    coefficient K d k (dualBasis K d i) = 0 := by
  apply (Polynomial.degreeLT.basis K d).ext
  intro j
  rw [coefficient_basis_value, LinearMap.zero_apply]
  rw [if_neg (by have := j.isLt; omega)]

private theorem coefficient_cyclic (N : ℕ) (i : Fin (N + 1)) :
    coefficient K (N + 1) i.val (dualBasis K (N + 1) 0) =
      dualBasis K (N + 1) i := by
  rw [coefficient_basis_of_lt K (N + 1) i.val 0 (by simpa using i.isLt)]
  simp

private theorem coefficient_eval (d k : ℕ) (v : DualPower K d) (j : Fin d) :
    coefficient K d k v (Polynomial.degreeLT.basis K d j) =
      ∑ i : Fin d, (dualBasis K d).repr v i *
        (if j.val = i.val + k then (j.val.choose i.val : K) else 0) := by
  classical
  conv_lhs => rw [← (dualBasis K d).sum_repr v]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    coefficient_basis_value, smul_eq_mul]

private theorem coefficient_top (N : ℕ) (v : DualPower K (N + 1)) :
    coefficient K (N + 1) N v =
      v (Polynomial.degreeLT.basis K (N + 1) 0) •
        dualBasis K (N + 1) (Fin.last N) := by
  classical
  have hb (i : Fin (N + 1)) :
      coefficient K (N + 1) N (dualBasis K (N + 1) i) =
        if i = 0 then dualBasis K (N + 1) (Fin.last N) else 0 := by
    by_cases hi : i = 0
    · subst i
      simpa using coefficient_cyclic K N (Fin.last N)
    · rw [coefficient_basis_of_ge K (N + 1) N i (by
        have := Fin.pos_iff_ne_zero.mpr hi
        omega)]
      simp [hi]
  conv_lhs => rw [← (dualBasis K (N + 1)).sum_repr v]
  simp only [map_sum, map_smul, hb]
  simp [dualBasis, Module.Basis.dualBasis_repr]

private theorem coefficient_diagonal (N : ℕ)
    (v : DualPower K (N + 1)) (i : Fin (N + 1)) :
    coefficient K (N + 1) i.val v (Polynomial.degreeLT.basis K (N + 1) i) =
      v (Polynomial.degreeLT.basis K (N + 1) 0) := by
  classical
  rw [coefficient_eval, Finset.sum_eq_single 0]
  · simp [dualBasis, Module.Basis.dualBasis_repr]
  · intro j _ hj
    have hne : i.val ≠ j.val + i.val := by
      intro he
      apply hj
      apply Fin.ext
      change j.val = 0
      omega
    rw [if_neg hne, mul_zero]
  · simp

private theorem coefficient_top_coordinate_zero (n m : ℕ)
    (hchoose : ((n + m).choose n : K) = 0)
    (v : DualPower K (n + m + 1)) :
    coefficient K (n + m + 1) m v
      (Polynomial.degreeLT.basis K (n + m + 1) (Fin.last (n + m))) = 0 := by
  classical
  rw [coefficient_eval]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val = n
  · rw [if_pos (by simp only [Fin.val_last]; omega), Fin.val_last, hi, hchoose, mul_zero]
  · rw [if_neg (by simp only [Fin.val_last]; omega), mul_zero]

end PolynomialCoefficients

section FiniteFieldExtraction

variable {K : Type uK} [Field K] [Fintype K]

private theorem power_sum (s : ℕ) (hs : s ≠ 0) :
    (∑ a : K, a ^ s) = if Fintype.card K - 1 ∣ s then -1 else 0 := by
  classical
  let φ : Kˣ ↪ K := ⟨fun x => x, Units.val_injective⟩
  have hφ : univ.map φ = univ \ {(0 : K)} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and,
      mem_sdiff, mem_singleton, φ] using! isUnit_iff_ne_zero
  calc
    (∑ a : K, a ^ s) = ∑ a ∈ univ \ {(0 : K)}, a ^ s := by
      rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton,
        zero_pow hs, add_zero]
    _ = ∑ a : Kˣ, (a ^ s : K) := by simp [φ, ← hφ, univ.sum_map φ]
    _ = _ := FiniteField.sum_pow_units K s

-- d=N+1; d+1≤q is EXACTLY N+2≤q, not a characteristic bound.
-- The exponent lies strictly between 0 and 2(q-1), and its only possible
-- positive multiple of q-1 is q-1. This also treats the constant coefficient.
private theorem coefficient_pairing {d : ℕ} (hd : d + 1 ≤ Fintype.card K)
    (k t : Fin d) :
    -(∑ a : K, a ^ (Fintype.card K - 1 - k.val) * a ^ t.val) =
      if t = k then 1 else 0 := by
  classical
  have hk := k.isLt
  have ht := t.isLt
  have hpos : 0 < Fintype.card K - 1 - k.val + t.val := by omega
  have hlt : Fintype.card K - 1 - k.val + t.val <
      2 * (Fintype.card K - 1) := by omega
  simp_rw [← pow_add]
  rw [power_sum _ (by omega)]
  have hdiv : Fintype.card K - 1 ∣ Fintype.card K - 1 - k.val + t.val ↔ t = k := by
    constructor
    · rintro ⟨r, hr⟩
      have hr0 : r ≠ 0 := by
        intro he
        rw [he, mul_zero] at hr
        omega
      have hrlt : r < 2 := by
        by_contra he
        have hrge : 2 ≤ r := by omega
        have hmul := Nat.mul_le_mul_left (Fintype.card K - 1) hrge
        omega
      have hr1 : r = 1 := by omega
      rw [hr1, mul_one] at hr
      apply Fin.ext
      omega
    · intro he
      subst t
      exact ⟨1, by omega⟩
  simp only [hdiv]
  split_ifs <;> simp

private theorem recover_coefficients
    {E : Type*} [AddCommGroup E] [Module K E]
    {d : ℕ} (hd : d + 1 ≤ Fintype.card K) (A : Fin d → E) (k : Fin d) :
    -(∑ a : K, a ^ (Fintype.card K - 1 - k.val) •
      (∑ t : Fin d, a ^ t.val • A t)) = A k := by
  classical
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_smul, ← neg_smul, coefficient_pairing hd k]
  simp

private theorem recover_family
    {E I : Type*} [AddCommGroup E] [Module K E] [Fintype I]
    {d : ℕ} (hd : d + 1 ≤ Fintype.card K)
    (degree : I → Fin d) (A : I → E) (k : Fin d) :
    -(∑ a : K, a ^ (Fintype.card K - 1 - k.val) •
      (∑ i : I, a ^ (degree i).val • A i)) =
      ∑ i : I, if degree i = k then A i else 0 := by
  classical
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_smul, ← neg_smul, coefficient_pairing hd k]
  apply sum_congr rfl
  intro i _
  split_ifs <;> simp

-- A linear combination of actual finite-group actions. No coefficient
-- operator on any arbitrary intermediate tensor factor is postulated.
private def extracted {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (Multiplicative K) V) {d : ℕ} (k : Fin d) :
    Module.End K V :=
  -(∑ a : K, a ^ (Fintype.card K - 1 - k.val) •
    ρ (Multiplicative.ofAdd (-a)))

private theorem extract_dual_coefficient {r d : ℕ}
    (hrd : r ≤ d) (hd : d + 1 ≤ Fintype.card K) (k : Fin d) :
    coefficient K r k.val = extracted (dualAction K r) k := by
  unfold extracted
  simp_rw [action_expansion K r d hrd]
  exact (recover_coefficients hd (fun t => coefficient K r t.val) k).symm

private theorem extracted_intertwines
    {V Z : Type*} [AddCommGroup V] [Module K V] [AddCommGroup Z] [Module K Z]
    (ρ : Representation K (Multiplicative K) V)
    (σ : Representation K (Multiplicative K) Z)
    (f : ρ.IntertwiningMap σ) {d : ℕ} (k : Fin d) :
    f.toLinearMap.comp (extracted ρ k) =
      (extracted σ k).comp f.toLinearMap := by
  apply LinearMap.ext
  intro v
  simp only [extracted, LinearMap.comp_apply, LinearMap.neg_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, map_neg, map_sum, map_smul,
    Representation.IntertwiningMap.toLinearMap_apply, f.isIntertwining]

end FiniteFieldExtraction

section RectangularTensor

variable (K : Type uK) [Field K]

/-- The rectangular tensor of the original polynomial contragredients. -/
abbrev TensorSpace (n m : ℕ) := DualPower K (n + 1) ⊗[K] DualPower K (m + 1)

/-- Actual finite additive-group action, using the public original dualAction. -/
def tensorAction (n m : ℕ) : Representation K (Multiplicative K) (TensorSpace K n m) :=
  (dualAction K (n + 1)).tprod (dualAction K (m + 1))

private def tensorDegree (n m : ℕ) (i : Fin (n + 1) × Fin (m + 1)) :
    Fin (n + m + 1) :=
  ⟨i.1.val + i.2.val, by have := i.1.isLt; have := i.2.isLt; omega⟩

private def tensorCoefficient (n m : ℕ) (k : Fin (n + m + 1)) :
    Module.End K (TensorSpace K n m) :=
  ∑ i : Fin (n + 1) × Fin (m + 1), if tensorDegree n m i = k then
    TensorProduct.map (coefficient K (n + 1) i.1.val)
      (coefficient K (m + 1) i.2.val) else 0

private theorem tensor_action_expansion (n m : ℕ) (a : K) :
    tensorAction K n m (Multiplicative.ofAdd (-a)) =
      ∑ i : Fin (n + 1) × Fin (m + 1), a ^ (tensorDegree n m i).val •
        TensorProduct.map (coefficient K (n + 1) i.1.val)
          (coefficient K (m + 1) i.2.val) := by
  apply TensorProduct.ext'
  intro x y
  simp only [tensorAction, Representation.tprod_apply, TensorProduct.map_tmul,
    action_expansion K (n + 1) (n + 1) (le_refl (n + 1)),
    action_expansion K (m + 1) (m + 1) (le_refl (m + 1)),
    LinearMap.sum_apply, LinearMap.smul_apply, TensorProduct.sum_tmul,
    TensorProduct.tmul_sum, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    Finset.smul_sum, smul_smul, ← pow_add, Fintype.sum_prod_type, tensorDegree]
  rw [sum_comm]
  simp only [Nat.add_comm]

set_option maxRecDepth 2048 in
private theorem extract_tensor_coefficient [Fintype K] (n m : ℕ)
    (hsize : n + m + 2 ≤ Fintype.card K) (k : Fin (n + m + 1)) :
    tensorCoefficient K n m k = extracted (tensorAction K n m) k := by
  unfold extracted
  simp_rw [tensor_action_expansion]
  exact (recover_family (by omega : (n + m + 1) + 1 ≤ Fintype.card K)
    (tensorDegree n m)
    (fun i => TensorProduct.map (coefficient K (n + 1) i.1.val)
      (coefficient K (m + 1) i.2.val)) k).symm

private theorem tensor_coefficient_top (n m : ℕ) :
    tensorCoefficient K n m (Fin.last (n + m)) =
      TensorProduct.map (coefficient K (n + 1) n) (coefficient K (m + 1) m) := by
  classical
  rw [tensorCoefficient, Finset.sum_eq_single (Fin.last n, Fin.last m)]
  · simp [tensorDegree, Fin.ext_iff]
  · rintro ⟨u, v⟩ _ hne
    have hd : tensorDegree n m (u, v) ≠ Fin.last (n + m) := by
      intro he
      have hs : u.val + v.val = n + m := congrArg Fin.val he
      have hu := u.isLt
      have hv := v.isLt
      apply hne
      apply Prod.ext
      · apply Fin.ext
        change u.val = n
        omega
      · apply Fin.ext
        change v.val = m
        omega
    simp [hd]
  · simp

private theorem tensor_coefficient_top_range (n m : ℕ) (z : TensorSpace K n m) :
    ∃ c : K, tensorCoefficient K n m (Fin.last (n + m)) z =
      c • (dualBasis K (n + 1) (Fin.last n) ⊗ₜ[K]
        dualBasis K (m + 1) (Fin.last m)) := by
  rw [tensor_coefficient_top]
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x y =>
    refine ⟨x (Polynomial.degreeLT.basis K (n + 1) 0) *
      y (Polynomial.degreeLT.basis K (m + 1) 0), ?_⟩
    simp only [TensorProduct.map_tmul, coefficient_top, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul, smul_smul, mul_comm]
  | add x y hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, by rw [map_add, hc, hd, add_smul]⟩

private theorem tensor_coefficient_top_generator (n m : ℕ) :
    tensorCoefficient K n m (Fin.last (n + m))
      (dualBasis K (n + 1) 0 ⊗ₜ[K] dualBasis K (m + 1) 0) =
        dualBasis K (n + 1) (Fin.last n) ⊗ₜ[K]
          dualBasis K (m + 1) (Fin.last m) := by
  rw [tensor_coefficient_top, TensorProduct.map_tmul]
  have hn := coefficient_cyclic K n (Fin.last n)
  have hm := coefficient_cyclic K m (Fin.last m)
  simpa only [Fin.val_last] using congrArg₂ (fun x y => x ⊗ₜ[K] y) hn hm

-- This is the essential RECTANGULAR generator B_m(e_n tensor e_0)=w.
-- Unlike the old square proof, it needs no characteristic-specific binomial.
private theorem tensor_coefficient_middle_generator (n m : ℕ) :
    tensorCoefficient K n m ⟨m, by omega⟩
      (dualBasis K (n + 1) (Fin.last n) ⊗ₜ[K] dualBasis K (m + 1) 0) =
        dualBasis K (n + 1) (Fin.last n) ⊗ₜ[K]
          dualBasis K (m + 1) (Fin.last m) := by
  classical
  have hleft : coefficient K (n + 1) 0 (dualBasis K (n + 1) (Fin.last n)) =
      dualBasis K (n + 1) (Fin.last n) := by
    rw [coefficient_basis_of_lt K (n + 1) 0 (Fin.last n) (by simp)]
    simp only [Fin.val_last, Nat.add_zero, Nat.choose_self, Nat.cast_one, one_smul]
    rfl
  have hright : coefficient K (m + 1) m (dualBasis K (m + 1) 0) =
      dualBasis K (m + 1) (Fin.last m) := by
    simpa only [Fin.val_last] using coefficient_cyclic K m (Fin.last m)
  rw [tensorCoefficient, LinearMap.sum_apply,
    Finset.sum_eq_single (0, Fin.last m)]
  · rw [if_pos (by apply Fin.ext; simp [tensorDegree]), TensorProduct.map_tmul]
    change coefficient K (n + 1) 0 (dualBasis K (n + 1) (Fin.last n)) ⊗ₜ[K]
      coefficient K (m + 1) m (dualBasis K (m + 1) 0) = _
    rw [hleft, hright]
  · rintro ⟨u, v⟩ _ hne
    by_cases hd : tensorDegree n m (u, v) = (⟨m, by omega⟩ : Fin (n + m + 1))
    · rw [if_pos hd, TensorProduct.map_tmul]
      by_cases hu : u = 0
      · have hv : v = Fin.last m := by
          apply Fin.ext
          have hs : u.val + v.val = m := congrArg Fin.val hd
          have hu0 : u.val = 0 := congrArg Fin.val hu
          simpa only [hu0, zero_add, Fin.val_last] using hs
        exact (hne (Prod.ext hu hv)).elim
      · rw [coefficient_basis_of_ge K (n + 1) u.val (Fin.last n) (by
          have := Fin.pos_iff_ne_zero.mpr hu
          simp only [Fin.val_last]
          omega), TensorProduct.zero_tmul]
    · rw [if_neg hd, LinearMap.zero_apply]
  · simp

end RectangularTensor

section AllMorphisms

variable {K : Type uK} [Field K] [Fintype K]

-- Intertwining is DERIVED from actual group equivariance and finite-field
-- extraction; neither of these equalities is an assumption on a map.
private theorem forward_intertwines (n m : ℕ)
    (hsize : n + m + 2 ≤ Fintype.card K)
    (f : (dualAction K (n + m + 1)).IntertwiningMap (tensorAction K n m))
    (k : Fin (n + m + 1)) :
    f.toLinearMap.comp (coefficient K (n + m + 1) k.val) =
      (tensorCoefficient K n m k).comp f.toLinearMap := by
  rw [extract_dual_coefficient (le_refl (n + m + 1)) (by omega :
    (n + m + 1) + 1 ≤ Fintype.card K), extract_tensor_coefficient K n m hsize]
  exact extracted_intertwines _ _ f k

private theorem backward_intertwines (n m : ℕ)
    (hsize : n + m + 2 ≤ Fintype.card K)
    (g : (tensorAction K n m).IntertwiningMap (dualAction K (n + m + 1)))
    (k : Fin (n + m + 1)) :
    g.toLinearMap.comp (tensorCoefficient K n m k) =
      (coefficient K (n + m + 1) k.val).comp g.toLinearMap := by
  rw [extract_dual_coefficient (le_refl (n + m + 1)) (by omega :
    (n + m + 1) + 1 ≤ Fintype.card K), extract_tensor_coefficient K n m hsize]
  exact extracted_intertwines _ _ g k

/-- Every actual equivariant composite has zero top diagonal if the rectangular
binomial vanishes. This quantifies ALL group maps, with no torus, infinitesimal,
selected Hom basis or assumed coefficient-intertwining hypothesis. -/
theorem composition_top_coordinate_zero (n m : ℕ)
    (hsize : n + m + 2 ≤ Fintype.card K)
    (hchoose : ((n + m).choose n : K) = 0)
    (f : (dualAction K (n + m + 1)).IntertwiningMap (tensorAction K n m))
    (g : (tensorAction K n m).IntertwiningMap (dualAction K (n + m + 1))) :
    g (f (dualBasis K (n + m + 1) (Fin.last (n + m))))
      (Polynomial.degreeLT.basis K (n + m + 1) (Fin.last (n + m))) = 0 := by
  let w : TensorSpace K n m :=
    dualBasis K (n + 1) (Fin.last n) ⊗ₜ[K] dualBasis K (m + 1) (Fin.last m)
  have hg : g w (Polynomial.degreeLT.basis K (n + m + 1) (Fin.last (n + m))) = 0 := by
    have he := LinearMap.congr_fun
      (backward_intertwines n m hsize g ⟨m, by omega⟩)
      (dualBasis K (n + 1) (Fin.last n) ⊗ₜ[K] dualBasis K (m + 1) 0)
    simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply] at he
    rw [tensor_coefficient_middle_generator] at he
    change g w = coefficient K (n + m + 1) m
      (g (dualBasis K (n + 1) (Fin.last n) ⊗ₜ[K] dualBasis K (m + 1) 0)) at he
    rw [he]
    exact coefficient_top_coordinate_zero K n m hchoose _
  have hgline : g w =
      g (dualBasis K (n + 1) 0 ⊗ₜ[K] dualBasis K (m + 1) 0)
        (Polynomial.degreeLT.basis K (n + m + 1) 0) •
          dualBasis K (n + m + 1) (Fin.last (n + m)) := by
    have he := LinearMap.congr_fun
      (backward_intertwines n m hsize g (Fin.last (n + m)))
      (dualBasis K (n + 1) 0 ⊗ₜ[K] dualBasis K (m + 1) 0)
    simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply] at he
    rw [tensor_coefficient_top_generator] at he
    change g w = coefficient K (n + m + 1) (n + m)
      (g (dualBasis K (n + 1) 0 ⊗ₜ[K] dualBasis K (m + 1) 0)) at he
    simpa only [coefficient_top] using he
  have hgw : g w = 0 := by
    have hz := hg
    rw [hgline, LinearMap.smul_apply] at hz
    simp only [dualBasis, Module.Basis.dualBasis_apply_self, ite_true,
      smul_eq_mul, mul_one] at hz
    change g (dualBasis K (n + 1) 0 ⊗ₜ[K] dualBasis K (m + 1) 0)
      (Polynomial.degreeLT.basis K (n + m + 1) 0) = 0 at hz
    rw [hgline, hz, zero_smul]
  have hf : f (dualBasis K (n + m + 1) (Fin.last (n + m))) =
      tensorCoefficient K n m (Fin.last (n + m))
        (f (dualBasis K (n + m + 1) 0)) := by
    have he := LinearMap.congr_fun
      (forward_intertwines n m hsize f (Fin.last (n + m)))
      (dualBasis K (n + m + 1) 0)
    simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply] at he
    have hcyc : coefficient K (n + m + 1) (n + m)
        (dualBasis K (n + m + 1) 0) =
          dualBasis K (n + m + 1) (Fin.last (n + m)) := by
      simpa only [Fin.val_last] using coefficient_cyclic K (n + m) (Fin.last (n + m))
    change f (coefficient K (n + m + 1) (n + m) (dualBasis K (n + m + 1) 0)) =
      tensorCoefficient K n m (Fin.last (n + m))
        (f (dualBasis K (n + m + 1) 0)) at he
    rwa [hcyc] at he
  obtain ⟨c, hc⟩ := tensor_coefficient_top_range K n m
    (f (dualBasis K (n + m + 1) 0))
  change tensorCoefficient K n m (Fin.last (n + m))
    (f (dualBasis K (n + m + 1) 0)) = c • w at hc
  rw [hf, hc, map_smul, hgw, smul_zero, LinearMap.zero_apply]

/-- ALL actual equivariant endomorphisms have constant diagonal in the original
dual monomial basis. No binomial vanishing is needed for this assertion. -/
theorem endomorphism_constant_diagonal (N : ℕ)
    (hsize : N + 2 ≤ Fintype.card K)
    (h : (dualAction K (N + 1)).IntertwiningMap (dualAction K (N + 1)))
    (i : Fin (N + 1)) :
    h (dualBasis K (N + 1) i) (Polynomial.degreeLT.basis K (N + 1) i) =
      h (dualBasis K (N + 1) (Fin.last N))
        (Polynomial.degreeLT.basis K (N + 1) (Fin.last N)) := by
  have hd (j : Fin (N + 1)) :
      h (dualBasis K (N + 1) j) (Polynomial.degreeLT.basis K (N + 1) j) =
        h (dualBasis K (N + 1) 0) (Polynomial.degreeLT.basis K (N + 1) 0) := by
    have hcomm : h.toLinearMap.comp (coefficient K (N + 1) j.val) =
        (coefficient K (N + 1) j.val).comp h.toLinearMap := by
      rw [extract_dual_coefficient (le_refl (N + 1)) (by omega :
        (N + 1) + 1 ≤ Fintype.card K)]
      exact extracted_intertwines _ _ h j
    have he := congrArg (fun v : DualPower K (N + 1) =>
      v (Polynomial.degreeLT.basis K (N + 1) j))
        (LinearMap.congr_fun hcomm (dualBasis K (N + 1) 0))
    simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply] at he
    simpa only [coefficient_cyclic, coefficient_diagonal] using he
  exact (hd i).trans (hd (Fin.last N)).symm

/-- The trace is (N+1) times the top diagonal, in arbitrary characteristic. -/
theorem endomorphism_trace (N : ℕ)
    (hsize : N + 2 ≤ Fintype.card K)
    (h : (dualAction K (N + 1)).IntertwiningMap (dualAction K (N + 1))) :
    LinearMap.trace K (DualPower K (N + 1)) h.toLinearMap =
      ((N + 1 : ℕ) : K) * h (dualBasis K (N + 1) (Fin.last N))
        (Polynomial.degreeLT.basis K (N + 1) (Fin.last N)) := by
  classical
  calc
    LinearMap.trace K (DualPower K (N + 1)) h.toLinearMap =
        ∑ i : Fin (N + 1), h (dualBasis K (N + 1) i)
          (Polynomial.degreeLT.basis K (N + 1) i) := by
      rw [LinearMap.trace_eq_matrix_trace K (dualBasis K (N + 1))]
      simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, dualBasis,
        Module.Basis.dualBasis_repr, Representation.IntertwiningMap.toLinearMap_apply]
    _ = ∑ _i : Fin (N + 1), h (dualBasis K (N + 1) (Fin.last N))
        (Polynomial.degreeLT.basis K (N + 1) (Fin.last N)) :=
      sum_congr rfl (fun i _ => endomorphism_constant_diagonal N hsize h i)
    _ = _ := by simp [nsmul_eq_mul]

/-- The all-morphism trace obstruction for the later ORIGINAL relative-stable
trace bridge. This theorem itself assumes no relative norm witness. -/
theorem composition_trace_zero (n m : ℕ)
    (hsize : n + m + 2 ≤ Fintype.card K)
    (hchoose : ((n + m).choose n : K) = 0)
    (f : (dualAction K (n + m + 1)).IntertwiningMap (tensorAction K n m))
    (g : (tensorAction K n m).IntertwiningMap (dualAction K (n + m + 1))) :
    LinearMap.trace K (DualPower K (n + m + 1))
      (g.toLinearMap.comp f.toLinearMap) = 0 := by
  have ht := endomorphism_trace (n + m) hsize (g.comp f)
  change LinearMap.trace K (DualPower K (n + m + 1))
    (g.toLinearMap.comp f.toLinearMap) =
      ((n + m + 1 : ℕ) : K) * g (f (dualBasis K (n + m + 1) (Fin.last (n + m))))
        (Polynomial.degreeLT.basis K (n + m + 1) (Fin.last (n + m))) at ht
  rw [ht, composition_top_coordinate_zero n m hsize hchoose f g, mul_zero]

end AllMorphisms

end D5.S3.FiniteGroups.GroupAlgebra.RectangularTensorObstruction
