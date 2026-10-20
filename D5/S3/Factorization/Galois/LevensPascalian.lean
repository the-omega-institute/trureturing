/- GID: D5/S3/Factorization/Galois/LevensPascalian
   generality: I
   mirror-B: D5/B/S3/Factorization/Galois/LevensPascalian
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Factorization/Galois/LevensPascalian.claim; result=D5/S3/Factorization/Galois/LevensPascalian.result; claim=D5/S3/Factorization/Galois/LevensPascalian.claim
   digest: A square discriminant excludes the hyperoctahedral Galois group at index 49. -/

/-
admission_basis: open-problem-resolution (#19007; Refuted)
escape_witness: none
Escape audit unfinished for the publicized prerequisite: https://github.com/the-omega-institute/trureturing/issues/19098.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The definitions P, signFlip, hyperoctahedral and claim preserve the source formulas.
The root enumeration uses Fintype.equivFinOfCardEq and the subgroup uses Subgroup.fintype.
Direct frozen dependencies:
D5/S3/Zeros/Convolution/PerfectMatchingCount.involution_iff_cycleType
baseline private declaration statement_id:
sha256:032ffbf98691b838b1231829b519cf8523762968a33ccdb37bf63c8c91151ae5.
Per-declaration classification (same-delivery helpers inlined):
signFlip_sq: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: signFlip_cycleType.
signFlip_support: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: signFlip_cycleType.
signFlip_cycleType: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: involution_iff_cycleType; consumers: card_hyperoctahedral.
card_hyperoctahedral: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: involution_iff_cycleType; consumers: result.
c_value: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: discriminant_square, q_degree, q_separable, rational_vandermonde, resultant_q_derivative.
coeff_q: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: q_degree, q_lc, q_zero.
q_degree: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cardinal_bound, discriminant_square, q_lc, q_root_product, q_separable, rational_vandermonde, resultant_q_derivative.
q_lc: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: discriminant_square, q_root_product, q_separable.
q_zero: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: P49_ne_zero, q_ne_zero, resultant_q_derivative.
q_neg_one: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: resultant_q_derivative.
factorization: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: P49_ne_zero, cardinal_bound, q_splits_in_P.
differential: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: resultant_q_derivative.
resultant_q_derivative: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: discriminant_square, rational_vandermonde.
discriminant_square: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: q_separable.
rational_of_sq_eq_sq: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: rational_vandermonde, sign_eq_one_of_vandermonde_sq.
sign_eq_one_of_vandermonde_sq: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cardinal_bound.
card_bound_of_root_coordinates: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: none; consumers: cardinal_bound.
derivative_at_root_product: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: resultant_root_product.
root_pair_product: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: resultant_root_product.
resultant_root_product: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: rational_vandermonde.
q_ne_zero: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cardinal_bound, q_separable.
q_separable: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cardinal_bound, q_root_product, rational_vandermonde.
P49_ne_zero: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cardinal_bound, q_splits_in_P.
q_splits_in_P: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cardinal_bound.
q_root_product: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: rational_vandermonde.
rational_vandermonde: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cardinal_bound.
cardinal_bound: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: none; consumers: result.
result: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: involution_iff_cycleType; consumers: settling result.
P: proof_shape: not-applicable (definition or instance); escape_witness: none;
  Direct frozen dependencies: none; consumers: settling result.
signFlip: proof_shape: not-applicable (definition or instance); escape_witness: none;
  Direct frozen dependencies: none; consumers: card_hyperoctahedral, hyperoctahedral, signFlip_cycleType, signFlip_sq, signFlip_support.
hyperoctahedral: proof_shape: not-applicable (definition or instance); escape_witness: none;
  Direct frozen dependencies: none; consumers: settling result.
claim: proof_shape: not-applicable (definition or instance); escape_witness: none;
  Direct frozen dependencies: none; consumers: result.
q: proof_shape: not-applicable (definition or instance); escape_witness: none;
  Direct frozen dependencies: none; consumers: settling result.
c: proof_shape: not-applicable (definition or instance); escape_witness: none;
  Direct frozen dependencies: none; consumers: settling result.
Private definitions q and c are concrete polynomial and coefficient data.
No exact Galois group or general Pell family is asserted.
-/

import D5.S3.Zeros.Convolution.PerfectMatchingCount
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.FieldTheory.PolynomialGaloisGroup

set_option autoImplicit false
open scoped Classical

namespace D5.S3.Factorization.Galois.LevensPascalian

open Polynomial

/-- Levens, arXiv:2511.03082, Section 1: the Pascalian numbers `⟨n k⟩ = C(n, ⌊(n−k)/2⌋)` and the
`n`th Pascalian polynomial `P_n(z) = Σ_{k=0}^{n} ⟨n k⟩ z^{n−k}`. -/
noncomputable def P (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((n.choose ((n - k) / 2) : ℕ) : ℚ) * X ^ (n - k)

/-- The sign change on `{1, …, m} × {±1}`. -/
def signFlip (m : ℕ) : Equiv.Perm (Fin m × Bool) :=
  Equiv.prodCongr (Equiv.refl (Fin m)) (Equiv.swap false true)

/-- The `m`th hyperoctahedral group: the signed permutations of `m` letters, that is, the
permutations of `{1, …, m} × {±1}` commuting with the sign change. -/
def hyperoctahedral (m : ℕ) : Subgroup (Equiv.Perm (Fin m × Bool)) :=
  Subgroup.centralizer {signFlip m}

/-- Levens, arXiv:2511.03082, Conjecture 6.4 (second sentence): "For n = 2m + 1, the Galois group
of P_n(z) is the mth hyperoctahedral group." -/
def claim : Prop :=
  ∀ m : ℕ, 1 ≤ m → Nonempty ((P (2 * m + 1)).Gal ≃* hyperoctahedral m)

end D5.S3.Factorization.Galois.LevensPascalian

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedTactic false
namespace D5.S3.Factorization.Galois.LevensPascalian
open Equiv

private theorem signFlip_sq (m : ℕ) : signFlip m ^ 2 = 1 := by
  exact isSelfInv_iff_sq_eq_one.mp rfl

private theorem signFlip_support (m : ℕ) : (signFlip m).support = Finset.univ := by
  ext ⟨i,b⟩
  cases b <;> simp [Equiv.Perm.mem_support, signFlip]

private theorem signFlip_cycleType (m : ℕ) :
    (signFlip m).cycleType = Multiset.replicate m 2 := by
  apply (D5.S3.Zeros.Convolution.PerfectMatchingCount.involution_iff_cycleType m
    (by simp [Fintype.card_prod, mul_comm]) (signFlip m)).mp
  constructor
  · intro x
    exact congrArg (fun f : Equiv.Perm (Fin m × Bool) => f x) (signFlip_sq m)
  · intro x
    exact Equiv.Perm.mem_support.mp (signFlip_support m ▸ Finset.mem_univ x)

private theorem card_hyperoctahedral (m : ℕ) :
    Fintype.card (hyperoctahedral m) = 2 ^ m * m.factorial := by
  classical
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (Subgroup.centralizer {signFlip m}) = _
  rw [Equiv.Perm.nat_card_centralizer, signFlip_cycleType]
  by_cases hm : m = 0
  · subst m; simp
  · simp [hm, Fintype.card_prod, mul_comm]

end D5.S3.Factorization.Galois.LevensPascalian

namespace D5.S3.Factorization.Galois.LevensPascalian
open Polynomial
private noncomputable def q : ℚ[X] :=
  ∑ j ∈ Finset.range 25, C (((49 : ℕ).choose j : ℕ) : ℚ) * X ^ j
private noncomputable def c : ℚ := (49 : ℕ).choose 24
private theorem c_value : c = 63205303218876 := by
  exact Rat.ext rfl rfl
private theorem coeff_q (i : ℕ) : q.coeff i = if i < 25 then ((49 : ℕ).choose i : ℚ) else 0 := by
  classical
  simp [q, finsetSum_coeff]
private theorem q_degree : q.natDegree = 24 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · unfold q
    apply natDegree_sum_le_of_forall_le
    intro i hi
    exact (natDegree_C_mul_X_pow_le _ _).trans (by simpa only [Finset.mem_range] using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  · rw [coeff_q]
    change ((49 : ℕ).choose 24 : ℚ) ≠ 0
    change c ≠ 0
    rw [c_value]
    norm_num
private theorem q_lc : q.leadingCoeff = c := by
  rw [← coeff_natDegree, q_degree, coeff_q]
  norm_num [c]
private theorem q_zero : q.coeff 0 = 1 := by
  norm_num [coeff_q]
private theorem q_neg_one : q.eval (-1) = 25*c/49 := by
  norm_num [q, c, Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
private theorem factorization : P 49 = (1 + X) * q.comp (X ^ 2) := by
  norm_num [P, q, Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial, Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
private theorem differential : (1 + X) * q.derivative - C 49 * q = -C (25*c) * X^24 := by
  norm_num [q, c, Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial, derivative_add, derivative_mul, derivative_pow,
    map_ofNat, map_natCast]
  <;> ring
private theorem resultant_q_derivative : resultant q q.derivative 24 23 = 49 * 25^23 * c^23 := by
  have hd1 : (1 + X : ℚ[X]).natDegree = 1 := by
    simpa only [C_1, add_comm] using (natDegree_X_add_C (1 : ℚ))
  have hd : q.derivative.natDegree = 23 := by rw [natDegree_derivative, q_degree]
  have hp := resultant_mul_right q (1 + X) q.derivative 24 q_degree.le
  rw [hd1, hd] at hp
  have hl : resultant q (1+X) 24 1 = 25*c/49 := by
    have h := resultant_X_add_C_right q 24 1 q_degree.le
    norm_num [C_1, q_neg_one] at h
    have hg : (1+X : ℚ[X]) = X+C (1:ℚ) := by
      rw [Polynomial.C_1]
      exact add_comm _ _
    rw [hg]
    exact h
  have heq : (1+X)*q.derivative = (-C (25*c)*X^24) + q*C 49 := by
    linear_combination differential
  have hred := resultant_add_mul_right q (-C (25*c)*X^24) (C 49) 24 24
    (by simp) q_degree.le
  rw [← heq] at hred
  have hmono : resultant q (-C (25*c)*X^24) 24 24 = (25*c)^24 := by
    rw [← map_neg (C : ℚ →+* ℚ[X]), resultant_C_mul_right, resultant_X_pow_right _ _ _ q_degree.le,
      q_zero]
    norm_num [neg_pow]
  rw [hl, hred, hmono] at hp
  have hc : c ≠ 0 := by exact Rat.abs_pos_iff.mp rfl
  apply (mul_left_cancel₀ (show 25*c/49 ≠ 0 by exact div_ne_zero (mul_ne_zero (by norm_num) hc) (by norm_num)))
  rw [← hp]
  ring
private theorem discriminant_square : q.discr = (7 * 5^23 * c^11)^2 := by
  have hh := resultant_deriv (f := q) (by rw [← natDegree_pos_iff_degree_pos, q_degree]; norm_num)
  rw [q_degree, q_lc] at hh
  norm_num at hh
  have hc : c ≠ 0 := by exact Rat.abs_pos_iff.mp rfl
  apply mul_left_cancel₀ hc
  rw [← hh, resultant_q_derivative]
  norm_num [c_value]
end D5.S3.Factorization.Galois.LevensPascalian

namespace D5.S3.Factorization.Galois.LevensPascalian
open Matrix Equiv
private theorem rational_of_sq_eq_sq {K : Type*} [Field K] [Algebra ℚ K]
    (d : K) (a : ℚ) (h : d ^ 2 = (algebraMap ℚ K a)^2) :
    ∃ b : ℚ, d = algebraMap ℚ K b := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact ⟨a,h⟩
  · exact ⟨-a, by simpa using h⟩

private theorem sign_eq_one_of_vandermonde_sq {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    {n : ℕ} (r : Fin n → K) (σ : K ≃ₐ[ℚ] K) (π : Equiv.Perm (Fin n))
    (hr : Function.Injective r) (hσ : ∀ i, σ (r i) = r (π i))
    (a : ℚ) (hsq : (vandermonde r).det ^ 2 = (algebraMap ℚ K a)^2) :
    Equiv.Perm.sign π = 1 := by
  obtain ⟨b,hb⟩ := rational_of_sq_eq_sq _ a hsq
  have hfix : σ (vandermonde r).det = (vandermonde r).det := by
    rw [hb, σ.commutes]
  have he : σ.toRingHom.mapMatrix (vandermonde r) = (vandermonde r).submatrix π id := by
    ext i j
    simp [vandermonde_apply, hσ]
  have hd := RingHom.map_det σ.toRingHom (vandermonde r)
  rw [he, Matrix.det_permute] at hd
  have hn : (vandermonde r).det ≠ 0 := det_vandermonde_ne_zero_iff.mpr hr
  have hc : ((Equiv.Perm.sign π : ℤ) : K) = 1 := by
    apply mul_right_cancel₀ hn
    simpa [hfix] using hd.symm
  apply Units.ext
  exact Int.cast_injective (α := K) (by simpa only [Int.cast_one, Units.val_one] using hc)

end D5.S3.Factorization.Galois.LevensPascalian

namespace D5.S3.Factorization.Galois.LevensPascalian
open Polynomial Equiv
private theorem card_bound_of_root_coordinates (p : ℚ[X]) (n : ℕ)
    (x : Fin n → p.SplittingField) (π : p.Gal → Equiv.Perm (Fin n))
    (hπ : ∀ (σ : p.Gal) i, σ ((x i)^2) = (x (π σ i))^2)
    (heven : ∀ σ, Equiv.Perm.sign (π σ) = 1)
    (hcomplete : ∀ z ∈ p.rootSet p.SplittingField,
      z = -1 ∨ ∃ i, z = x i ∨ z = - x i) :
    Fintype.card p.Gal ≤ 2^n * Fintype.card (alternatingGroup (Fin n)) := by
  classical
  have hex : ∀ (σ : p.Gal) (i : Fin n), ∃ b : Bool,
      σ (x i) = if b then -x (π σ i) else x (π σ i) := by
    intro σ i
    have hs : σ (x i)^2 = x (π σ i)^2 := by simpa only [map_pow] using hπ σ i
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  choose s hs using hex
  let f : p.Gal → (Fin n → Bool) × alternatingGroup (Fin n) :=
    fun σ => (s σ, ⟨π σ, heven σ⟩)
  have hf : Function.Injective f := by
    intro σ τ h
    have hsign : s σ = s τ := congrArg Prod.fst h
    have hperm : π σ = π τ := congrArg (fun z => z.2.val) h
    have hx : ∀ i, σ (x i) = τ (x i) := by
      intro i
      rw [hs σ i, hs τ i, hsign, hperm]
    apply Polynomial.Gal.ext
    intro z hz
    rcases hcomplete z hz with h | ⟨i,h|h⟩
    · simp [h]
    · simpa [h] using hx i
    · simpa [h] using congrArg Neg.neg (hx i)
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] using hc

end D5.S3.Factorization.Galois.LevensPascalian

namespace D5.S3.Factorization.Galois.LevensPascalian
open Polynomial Finset Matrix
private theorem derivative_at_root_product {K : Type*} [Field K] {n : ℕ}
    (b : K) (r : Fin n → K) (i : Fin n) :
    (C b * ∏ j, (X - C (r j))).derivative.eval (r i) =
      b * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), (r i - r j) := by
  classical
  have h := Lagrange.eval_nodal_derivative_eval_node_eq
    (s := Finset.univ) (v := r) (Finset.mem_univ i)
  simpa [Lagrange.nodal, derivative_mul, Finset.compl_eq_univ_sdiff,
    Finset.sdiff_singleton_eq_erase, eval_prod] using congrArg (fun z : K => b * z) h

private theorem root_pair_product {K : Type*} [Field K] (r : Fin 24 → K) :
    (∏ i, ∏ j ∈ ({i}ᶜ : Finset (Fin 24)), (r i-r j)) = (vandermonde r).det^2 := by
  classical
  have hsignZ : (∏ i : Fin 24, ∏ j ∈ Ioi i, (-1 : ℤ)) = 1 := by
    exact Eq.symm (Int.neg_inj.mp rfl)
  have hsignK : (∏ i : Fin 24, ∏ j ∈ Ioi i, (-1 : K)) = 1 := by
    have hh := congrArg (Int.castRingHom K) hsignZ
    simpa only [map_prod, map_neg, map_one] using hh
  calc
    _ = ∏ i : Fin 24, ∏ j ∈ Ioi i, ((-1:K)*(r j-r i)^2) := by
      rw [← prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun i j => r j-r i)]
      apply Finset.prod_congr rfl
      intro i hi
      apply Finset.prod_congr rfl
      intro j hj
      ring
    _ = (∏ i : Fin 24, ∏ j ∈ Ioi i, (-1:K)) *
        (∏ i : Fin 24, ∏ j ∈ Ioi i, (r j-r i))^2 := by
      simp only [prod_mul_distrib, ← prod_pow]
    _ = _ := by rw [hsignK, one_mul, det_vandermonde]

private theorem resultant_root_product {K : Type*} [Field K] [CharZero K]
    (f : K[X]) (b : K) (r : Fin 24 → K)
    (hb : b ≠ 0) (hf : f = C b * ∏ i, (X-C (r i))) :
    resultant f f.derivative 24 23 = b^47 * (vandermonde r).det^2 := by
  classical
  have hprod : (∏ i : Fin 24, (X-C (r i))).natDegree = 24 := by
    simpa only [Lagrange.nodal, Finset.card_univ, Fintype.card_fin] using
      (Lagrange.natDegree_nodal (s := Finset.univ) (v := r))
  have hdeg : f.natDegree = 24 := by
    rw [hf, natDegree_C_mul hb, hprod]
  have hder : f.derivative.natDegree = 23 := by rw [natDegree_derivative, hdeg]
  have heval (i : Fin 24) : f.derivative.eval (r i) =
      b * ∏ j ∈ ({i}ᶜ : Finset (Fin 24)), (r i-r j) := by
    rw [hf]
    exact derivative_at_root_product b r i
  have hres : resultant (∏ i : Fin 24, (X-C (r i))) f.derivative 24 23 =
      ∏ i : Fin 24, f.derivative.eval (r i) := by
    have h := resultant_prod_left Finset.univ (fun i : Fin 24 => X-C (r i))
      f.derivative 23 (by simp) hder.le
    rw [hprod] at h
    simpa only [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ hder.le] using h
  calc
    _ = b^23 * resultant (∏ i : Fin 24, (X-C (r i))) f.derivative 24 23 := by
      nth_rw 1 [hf]
      exact resultant_C_mul_left _ _ _ _ _
    _ = b^23 * ∏ i : Fin 24, (b * ∏ j ∈ ({i}ᶜ : Finset (Fin 24)), (r i-r j)) := by
      rw [hres]; simp_rw [heval]
    _ = _ := by rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
        root_pair_product]; ring

end D5.S3.Factorization.Galois.LevensPascalian

namespace D5.S3.Factorization.Galois.LevensPascalian
open Polynomial Finset
private theorem q_ne_zero : q ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : ℚ[X] => f.coeff 0) h
  simpa [q_zero] using h0
private theorem q_separable : q.Separable := by
  rw [separable_def]
  have hn : resultant q q.derivative q.natDegree q.derivative.natDegree ≠ 0 := by
    have hd : q.discr ≠ 0 := by rw [discriminant_square]; norm_num [c_value]
    have hh := resultant_deriv (f := q)
      (by rw [← natDegree_pos_iff_degree_pos, q_degree]; norm_num)
    rw [q_degree, q_lc] at hh
    norm_num at hh
    rw [natDegree_derivative, q_degree, hh]
    exact mul_ne_zero (by rw [c_value]; norm_num) hd
  by_contra h
  exact hn (resultant_eq_zero_iff.mpr ⟨Or.inl q_ne_zero, h⟩)
private theorem P49_ne_zero : P 49 ≠ 0 := by
  intro h
  have hh := congrArg (eval 0) h
  rw [factorization] at hh
  simpa [eval_comp, ← coeff_zero_eq_eval_zero, q_zero] using hh
private theorem q_splits_in_P : (q.map (algebraMap ℚ (P 49).SplittingField)).Splits := by
  have hdvd : q.comp (X^2) ∣ P 49 := ⟨1+X, by rw [factorization]; ring⟩
  have hqc := (SplittingField.splits (P 49)).of_dvd (map_ne_zero P49_ne_zero)
    ((map_dvd_map' _).mpr hdvd)
  let φ := SplittingField.lift (q.comp (X^2)) hqc
  have hs := (Polynomial.Gal.splits_in_splittingField_of_comp q (X^2) (by simp)).map φ.toRingHom
  have hφ : φ.toRingHom.comp (algebraMap ℚ (q.comp (X^2)).SplittingField) =
      algebraMap ℚ (P 49).SplittingField := RingHom.ext (fun z => φ.commutes z)
  rw [Polynomial.map_map, hφ] at hs
  exact hs

private theorem q_root_product (K : Type*) [Field K] [Algebra ℚ K]
    (h : (q.map (algebraMap ℚ K)).Splits) :
    q.map (algebraMap ℚ K) = C (algebraMap ℚ K c) *
      ∏ i : Fin 24, (X-C (((Fintype.equivFinOfCardEq ((Polynomial.card_rootSet_eq_natDegree q_separable h).trans q_degree)).symm i : q.rootSet K) : K)) := by
  classical
  let e := (Fintype.equivFinOfCardEq ((Polynomial.card_rootSet_eq_natDegree q_separable h).trans q_degree)).symm
  have hp : ((q.map (algebraMap ℚ K)).roots.map (fun z => X-C z)).prod =
      ∏ z : q.rootSet K, (X-C (z:K)) := by
    change _ = ∏ z : ((q.map (algebraMap ℚ K)).roots.toFinset), (X-C (z:K))
    calc
      _ = ∏ z ∈ (q.map (algebraMap ℚ K)).roots.toFinset, (X-C z) := by
        change _ = (((q.map (algebraMap ℚ K)).roots.toFinset).val.map (fun z => X-C z)).prod
        rw [Multiset.toFinset_val, (Polynomial.nodup_roots (q_separable.map (f := algebraMap ℚ K))).dedup]
      _ = _ := (Finset.prod_coe_sort (q.map (algebraMap ℚ K)).roots.toFinset
        (fun z => X-C z)).symm
  have he : (∏ z : q.rootSet K, (X-C (z:K))) =
      ∏ i : Fin 24, (X-C ((e i : q.rootSet K):K)) :=
    (e.prod_comp (fun z : q.rootSet K => X-C (z:K))).symm
  rw [h.eq_prod_roots, leadingCoeff_map, q_lc, hp, he]
end D5.S3.Factorization.Galois.LevensPascalian

namespace D5.S3.Factorization.Galois.LevensPascalian
open Polynomial Matrix
private theorem rational_vandermonde (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    (h : (q.map (algebraMap ℚ K)).Splits) :
    ∃ a : ℚ, (vandermonde (fun i : Fin 24 => (((Fintype.equivFinOfCardEq ((Polynomial.card_rootSet_eq_natDegree q_separable h).trans q_degree)).symm i : q.rootSet K):K))).det =
      algebraMap ℚ K a := by
  classical
  let r : Fin 24 → K := fun i => (((Fintype.equivFinOfCardEq ((Polynomial.card_rootSet_eq_natDegree q_separable h).trans q_degree)).symm i : q.rootSet K):K)
  let b : K := algebraMap ℚ K c
  let D : K := (vandermonde r).det
  have hb : b ≠ 0 := (map_ne_zero (algebraMap ℚ K)).mpr (by rw [c_value]; norm_num)
  have hprod : q.map (algebraMap ℚ K) = C b * ∏ i : Fin 24, (X-C (r i)) :=
    q_root_product K h
  have hres : resultant (q.map (algebraMap ℚ K))
      (q.map (algebraMap ℚ K)).derivative 24 23 =
      algebraMap ℚ K (49 * 25^23 * c^23) := by
    rw [derivative_map, resultant_map_map, resultant_q_derivative]
  rw [resultant_root_product _ b r hb hprod] at hres
  have hres' : b^47 * D^2 = 49 * 25^23 * b^23 := by
    simpa only [map_mul, map_pow, map_ofNat] using hres
  have hs : (b^12 * D)^2 = (7*5^23:K)^2 := by
    apply mul_left_cancel₀ (pow_ne_zero 23 hb)
    linear_combination hres'
  obtain ⟨a,ha⟩ := rational_of_sq_eq_sq (b^12*D) (7*5^23)
    (by simpa only [map_mul, map_pow, map_ofNat] using hs)
  refine ⟨a/c^12, ?_⟩
  change D = _
  rw [map_div₀, map_pow]
  apply (eq_div_iff (pow_ne_zero 12 hb)).mpr
  simpa only [mul_comm] using ha
end D5.S3.Factorization.Galois.LevensPascalian

namespace D5.S3.Factorization.Galois.LevensPascalian
open Polynomial Equiv Matrix Finset
private theorem cardinal_bound : Fintype.card (P 49).Gal ≤
    2^24 * Fintype.card (alternatingGroup (Fin 24)) := by
  classical
  let K := (P 49).SplittingField
  let hsplit : (q.map (algebraMap ℚ K)).Splits := q_splits_in_P
  let e : Fin 24 ≃ q.rootSet K := (Fintype.equivFinOfCardEq ((Polynomial.card_rootSet_eq_natDegree q_separable hsplit).trans q_degree)).symm
  let r : Fin 24 → K := fun i => (e i : K)
  have hr : Function.Injective r := fun i j h => e.injective (Subtype.ext h)
  have hqc : ((q.comp (X^2)).map (algebraMap ℚ K)).Splits :=
    (SplittingField.splits (P 49)).of_dvd (map_ne_zero P49_ne_zero)
      ((map_dvd_map' _).mpr ⟨1+X, by rw [factorization]; ring⟩)
  have hex : ∀ i : Fin 24, ∃ x : K, x^2 = r i := by
    intro i
    have hdvd : (X-C (r i)) ∣ q.map (algebraMap ℚ K) :=
      dvd_iff_isRoot.mpr (by
        simpa only [IsRoot.def, eval_map_algebraMap] using (mem_rootSet.mp (e i).property).2)
    have hdvd' := map_dvd (compRingHom (X^2)) hdvd
    have hdvd'' : (X^2-C (r i)) ∣ (q.comp (X^2)).map (algebraMap ℚ K) := by
      simpa only [coe_compRingHom_apply, sub_comp, X_comp, C_comp, map_comp,
        Polynomial.map_pow, Polynomial.map_X] using hdvd'
    have hs := hqc.of_dvd (map_ne_zero (by
      intro h
      have hd := congrArg natDegree h
      rw [natDegree_comp, q_degree, natDegree_X_pow, natDegree_zero] at hd
      norm_num at hd)) hdvd''
    have hdegree : (X^2-C (r i) : K[X]).degree ≠ 0 := by
      apply degree_ne_of_natDegree_ne
      have hdeg : (X^2-C (r i) : K[X]).natDegree = 2 := by
        exact natDegree_X_pow_sub_C
      rw [hdeg]
      norm_num
    obtain ⟨z,hz⟩ := hs.exists_eval_eq_zero hdegree
    exact ⟨z, by simpa only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hz⟩
  choose x hx using hex
  letI : Fact ((q.map (algebraMap ℚ K)).Splits) := ⟨hsplit⟩
  let act (σ : (P 49).Gal) : Equiv.Perm (q.rootSet K) :=
    Polynomial.Gal.galActionHom q K (Polynomial.Gal.restrict q K σ)
  let π (σ : (P 49).Gal) : Equiv.Perm (Fin 24) := (e.trans (act σ)).trans e.symm
  have hact (σ : (P 49).Gal) (i : Fin 24) : σ (r i) = r (π σ i) := by
    dsimp [π,r]
    simp only [e.apply_symm_apply]
    exact (Polynomial.Gal.galActionHom_restrict q K σ (e i)).symm
  have hπ (σ : (P 49).Gal) (i : Fin 24) : σ ((x i)^2) = (x (π σ i))^2 := by
    rw [hx i, hx (π σ i)]
    exact hact σ i
  obtain ⟨a,ha⟩ := rational_vandermonde K hsplit
  have heven (σ : (P 49).Gal) : Equiv.Perm.sign (π σ) = 1 :=
    sign_eq_one_of_vandermonde_sq r σ (π σ) hr (hact σ) a
      (congrArg (fun z => z^2) ha)
  have hcomplete : ∀ z ∈ (P 49).rootSet K,
      z = -1 ∨ ∃ i, z = x i ∨ z = -x i := by
    intro z hz
    have hz' := aeval_eq_zero_of_mem_rootSet hz
    have hz'' : (1+z) * aeval (z^2) q = 0 := by
      simpa only [factorization, map_mul, map_add, map_one, aeval_X,
        aeval_comp, map_pow] using hz'
    rcases mul_eq_zero.mp hz'' with h | h
    · left; linear_combination h
    · right
      have hzq : z^2 ∈ q.rootSet K := mem_rootSet.mpr ⟨q_ne_zero,h⟩
      obtain ⟨i,hi⟩ := e.surjective ⟨z^2,hzq⟩
      refine ⟨i, ?_⟩
      have heq : z^2 = (x i)^2 := by
        rw [hx i]
        exact (congrArg Subtype.val hi).symm
      exact sq_eq_sq_iff_eq_or_eq_neg.mp heq
  exact card_bound_of_root_coordinates (P 49) 24 x π hπ heven hcomplete

theorem result : ¬ claim := by
  intro h
  obtain ⟨e⟩ := h 24 (by norm_num)
  have hc : Fintype.card (P 49).Gal = Fintype.card (hyperoctahedral 24) :=
    Fintype.card_congr e.toEquiv
  have hs : Fintype.card (P 49).Gal < Fintype.card (hyperoctahedral 24) :=
    lt_of_le_of_lt cardinal_bound (by
      rw [card_hyperoctahedral, card_alternatingGroup, Fintype.card_fin]
      norm_num [Nat.factorial])
  exact hs.ne hc
end D5.S3.Factorization.Galois.LevensPascalian
