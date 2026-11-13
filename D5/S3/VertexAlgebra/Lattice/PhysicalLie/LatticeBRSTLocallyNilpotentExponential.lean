/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTLocallyNilpotentExponential
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTLocallyNilpotentExponential
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: pointwise locally nilpotent Lie exponentials on the entire carrier. -/

/-
SOURCE_ONLY_UNCOMPILED. All proofs below are authored proofs, pending native
elaboration, kernel and assumption checks. The ambient derivation need only be
pointwise locally nilpotent. No finite-dimensionality or uniform exponent is used.

Construction: the bounded kernels are modules, with genuinely nilpotent restricted
endomorphisms. Exponential naturality is used only between bounded kernels.
Bracket preservation is a separate finite Leibniz convolution on the original Lie
algebra, with cutoff N + M, including zero bounds. The kernels are not asserted to
be Lie subalgebras. This is an auxiliary supplier for the original physical Weyl
construction, not a completion of that construction or the Monster/string goal.

Attribution: the bounded-kernel construction follows the completed, sealed Pro
mathematical advice supplied with this task. Mathlib's LieDerivation theory
(Frédéric Marbach) supplies the iterated Leibniz formula; its nilpotent exponential
theory supplies uniform naturality and the inverse/parameter identities. The
passage to pointwise cutoffs and the finite bracket convolution are implemented
here. The original partial source supplies the finite-cutoff starting point.
-/

import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTLocallyNilpotentExponential

/- Restriction of scalars is constructed, not an additional public hypothesis.
   The instance is local to this file and also supplies the bounded modules. -/
private abbrev complexRatModule (V : Type*) [AddCommGroup V] [Module ℂ V] : Module ℚ V :=
  Module.compHom V (algebraMap ℚ ℂ)

attribute [local instance] complexRatModule

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

private def truncatedExp (A : Module.End ℂ L) (t : ℂ) (N : ℕ) : Module.End ℂ L :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ)⁻¹ * t ^ n) • A ^ n

private theorem truncatedExp_apply (A : Module.End ℂ L) (t : ℂ) (N : ℕ) (x : L) :
    truncatedExp A t N x =
      ∑ n ∈ Finset.range N, ((n.factorial : ℂ)⁻¹ * t ^ n) • (A ^ n) x := by
  simp [truncatedExp]

private abbrev boundedKernel (A : Module.End ℂ L) (N : ℕ) := LinearMap.ker (A ^ N)

private def kernelEnd (A : Module.End ℂ L) (N : ℕ) :
    Module.End ℂ (boundedKernel A N) where
  toFun u := ⟨A (u : L), by
    change (A ^ N) (A (u : L)) = 0
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply,
      show (A ^ N) (u : L) = 0 from u.property, map_zero]⟩
  map_add' u v := Subtype.ext (map_add A (u : L) (v : L))
  map_smul' c u := Subtype.ext (map_smul A c (u : L))

private theorem kernelEnd_pow_coe (A : Module.End ℂ L) (N k : ℕ)
    (u : boundedKernel A N) :
    ((kernelEnd A N ^ k) u : L) = (A ^ k) (u : L) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change A ((kernelEnd A N ^ k) u : L) = (A ^ (k + 1)) (u : L)
    rw [ih, pow_succ', Module.End.mul_apply]

private theorem kernelEnd_pow_eq_zero (A : Module.End ℂ L) (N : ℕ) :
    kernelEnd A N ^ N = 0 := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  change ((kernelEnd A N ^ N) u : L) = 0
  rw [kernelEnd_pow_coe]
  exact u.property

private theorem scaled_kernelEnd_pow_eq_zero (A : Module.End ℂ L) (N : ℕ) (t : ℂ) :
    (t • kernelEnd A N) ^ N = 0 := by
  rw [smul_pow, kernelEnd_pow_eq_zero, smul_zero]

private def kernelExp (A : Module.End ℂ L) (N : ℕ) (t : ℂ) :
    Module.End ℂ (boundedKernel A N) := IsNilpotent.exp (t • kernelEnd A N)

private theorem kernelExp_coe (A : Module.End ℂ L) (N : ℕ) (t : ℂ)
    (u : boundedKernel A N) :
    (kernelExp A N t u : L) = truncatedExp A t N (u : L) := by
  change (boundedKernel A N).subtype (IsNilpotent.exp (t • kernelEnd A N) u) = _
  rw [IsNilpotent.exp_eq_sum (scaled_kernelEnd_pow_eq_zero A N t),
    LinearMap.sum_apply, map_sum, truncatedExp_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [LinearMap.smul_apply, map_rat_smul, smul_pow, LinearMap.smul_apply,
    map_smul]
  change (n.factorial : ℚ)⁻¹ • (t ^ n • ((kernelEnd A N ^ n) u : L)) = _
  rw [kernelEnd_pow_coe, ← Rat.cast_smul_eq_qsmul ℂ, smul_smul]
  simp only [Rat.cast_inv_nat]

private def kernelInclusion (A : Module.End ℂ L) (N K : ℕ) (hNK : N ≤ K) :
    boundedKernel A N →ₗ[ℂ] boundedKernel A K where
  toFun u := ⟨(u : L), Module.End.pow_map_zero_of_le hNK u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem kernelExp_natural (A : Module.End ℂ L) (N K : ℕ) (hNK : N ≤ K)
    (t : ℂ) :
    kernelExp A K t ∘ₗ kernelInclusion A N K hNK =
      kernelInclusion A N K hNK ∘ₗ kernelExp A N t := by
  change IsNilpotent.exp (t • kernelEnd A K) ∘ₗ kernelInclusion A N K hNK =
    kernelInclusion A N K hNK ∘ₗ IsNilpotent.exp (t • kernelEnd A N)
  apply Module.End.commute_exp_left_of_commute
    (fM := t • kernelEnd A N) (fN := t • kernelEnd A K)
    ⟨N, scaled_kernelEnd_pow_eq_zero A N t⟩
    ⟨K, scaled_kernelEnd_pow_eq_zero A K t⟩
  ext u
  rfl

private theorem truncatedExp_extend (A : Module.End ℂ L) (t : ℂ) (x : L)
    (N K : ℕ) (hx : (A ^ N) x = 0) (hNK : N ≤ K) :
    truncatedExp A t K x = truncatedExp A t N x := by
  let u : boundedKernel A N := ⟨x, hx⟩
  have h := congrArg
    (fun f : boundedKernel A N →ₗ[ℂ] boundedKernel A K => (f u : L))
    (kernelExp_natural A N K hNK t)
  calc
    truncatedExp A t K x =
        (kernelExp A K t (kernelInclusion A N K hNK u) : L) :=
      (kernelExp_coe A K t (kernelInclusion A N K hNK u)).symm
    _ = (kernelInclusion A N K hNK (kernelExp A N t u) : L) := h
    _ = (kernelExp A N t u : L) := rfl
    _ = truncatedExp A t N x := kernelExp_coe A N t u

private theorem truncatedExp_two_bounds (A : Module.End ℂ L) (t : ℂ) (x : L)
    (N K : ℕ) (hxN : (A ^ N) x = 0) (hxK : (A ^ K) x = 0) :
    truncatedExp A t N x = truncatedExp A t K x := by
  exact (truncatedExp_extend A t x N (max N K) hxN (le_max_left _ _)).symm.trans
    (truncatedExp_extend A t x K (max N K) hxK (le_max_right _ _))

private def pointwiseExp (A : Module.End ℂ L)
    (hloc : ∀ x : L, ∃ N : ℕ, (A ^ N) x = 0) (t : ℂ) (x : L) : L :=
  truncatedExp A t (Classical.choose (hloc x)) x

private theorem pointwiseExp_eq_cutoff (A : Module.End ℂ L)
    (hloc : ∀ x : L, ∃ N : ℕ, (A ^ N) x = 0) (t : ℂ) (x : L)
    (N : ℕ) (hx : (A ^ N) x = 0) :
    pointwiseExp A hloc t x = truncatedExp A t N x :=
  truncatedExp_two_bounds A t x (Classical.choose (hloc x)) N
    (Classical.choose_spec (hloc x)) hx

private def localExpLinear (A : Module.End ℂ L)
    (hloc : ∀ x : L, ∃ N : ℕ, (A ^ N) x = 0) (t : ℂ) : Module.End ℂ L where
  toFun := pointwiseExp A hloc t
  map_add' x y := by
    obtain ⟨N, hx⟩ := hloc x
    obtain ⟨M, hy⟩ := hloc y
    let K := max N M
    have hxK : (A ^ K) x = 0 := Module.End.pow_map_zero_of_le (le_max_left _ _) hx
    have hyK : (A ^ K) y = 0 := Module.End.pow_map_zero_of_le (le_max_right _ _) hy
    have hxyK : (A ^ K) (x + y) = 0 := by rw [map_add, hxK, hyK, add_zero]
    rw [pointwiseExp_eq_cutoff A hloc t (x + y) K hxyK,
      pointwiseExp_eq_cutoff A hloc t x K hxK,
      pointwiseExp_eq_cutoff A hloc t y K hyK]
    exact map_add (truncatedExp A t K) x y
  map_smul' c x := by
    obtain ⟨N, hx⟩ := hloc x
    have hcx : (A ^ N) (c • x) = 0 := by rw [map_smul, hx, smul_zero]
    rw [pointwiseExp_eq_cutoff A hloc t (c • x) N hcx,
      pointwiseExp_eq_cutoff A hloc t x N hx]
    exact map_smul (truncatedExp A t N) c x

private theorem localExpLinear_on_kernel (A : Module.End ℂ L)
    (hloc : ∀ x : L, ∃ N : ℕ, (A ^ N) x = 0) (N : ℕ) (t : ℂ)
    (u : boundedKernel A N) :
    localExpLinear A hloc t (u : L) = (kernelExp A N t u : L) := by
  exact (pointwiseExp_eq_cutoff A hloc t (u : L) N u.property).trans
    (kernelExp_coe A N t u).symm

private theorem localExpLinear_left_inv (A : Module.End ℂ L)
    (hloc : ∀ x : L, ∃ N : ℕ, (A ^ N) x = 0) (t : ℂ) (x : L) :
    localExpLinear A hloc (-t) (localExpLinear A hloc t x) = x := by
  obtain ⟨N, hx⟩ := hloc x
  let u : boundedKernel A N := ⟨x, hx⟩
  have he : kernelExp A N (-t) * kernelExp A N t = 1 := by
    change IsNilpotent.exp ((-t) • kernelEnd A N) *
      IsNilpotent.exp (t • kernelEnd A N) = 1
    rw [neg_smul]
    exact IsNilpotent.exp_neg_mul_exp_self ⟨N, scaled_kernelEnd_pow_eq_zero A N t⟩
  calc
    localExpLinear A hloc (-t) (localExpLinear A hloc t x) =
        localExpLinear A hloc (-t) (kernelExp A N t u : L) :=
      congrArg (localExpLinear A hloc (-t)) (localExpLinear_on_kernel A hloc N t u)
    _ = (kernelExp A N (-t) (kernelExp A N t u) : L) :=
      localExpLinear_on_kernel A hloc N (-t) (kernelExp A N t u)
    _ = x := by
      change ((kernelExp A N (-t) * kernelExp A N t) u : L) = x
      rw [he]
      rfl

private theorem localExpLinear_right_inv (A : Module.End ℂ L)
    (hloc : ∀ x : L, ∃ N : ℕ, (A ^ N) x = 0) (t : ℂ) (x : L) :
    localExpLinear A hloc t (localExpLinear A hloc (-t) x) = x := by
  obtain ⟨N, hx⟩ := hloc x
  let u : boundedKernel A N := ⟨x, hx⟩
  have he : kernelExp A N t * kernelExp A N (-t) = 1 := by
    change IsNilpotent.exp (t • kernelEnd A N) *
      IsNilpotent.exp ((-t) • kernelEnd A N) = 1
    rw [neg_smul]
    exact IsNilpotent.exp_mul_exp_neg_self ⟨N, scaled_kernelEnd_pow_eq_zero A N t⟩
  calc
    localExpLinear A hloc t (localExpLinear A hloc (-t) x) =
        localExpLinear A hloc t (kernelExp A N (-t) u : L) :=
      congrArg (localExpLinear A hloc t) (localExpLinear_on_kernel A hloc N (-t) u)
    _ = (kernelExp A N t (kernelExp A N (-t) u) : L) :=
      localExpLinear_on_kernel A hloc N t (kernelExp A N (-t) u)
    _ = x := by
      change ((kernelExp A N t * kernelExp A N (-t)) u : L) = x
      rw [he]
      rfl

private theorem pow_apply_lie (A : LieDerivation ℂ L L) (r : ℕ) (x y : L) :
    (A.toLinearMap ^ r) ⁅x, y⁆ =
      ∑ p ∈ Finset.antidiagonal r, (Nat.choose r p.1 : ℂ) •
        ⁅(A.toLinearMap ^ p.1) x, (A.toLinearMap ^ p.2) y⁆ := by
  simpa only [Module.End.pow_apply, LieDerivation.coeFn_coe,
    Nat.cast_smul_eq_nsmul] using A.iterate_apply_lie r x y

private theorem lie_killing_bound (A : LieDerivation ℂ L L) (x y : L) (N M : ℕ)
    (hx : (A.toLinearMap ^ N) x = 0) (hy : (A.toLinearMap ^ M) y = 0) :
    (A.toLinearMap ^ (N + M)) ⁅x, y⁆ = 0 := by
  rw [pow_apply_lie]
  apply Finset.sum_eq_zero
  intro p hp
  have hsum : p.1 + p.2 = N + M := Finset.mem_antidiagonal.mp hp
  rcases le_or_gt N p.1 with h | h
  · rw [Module.End.pow_map_zero_of_le h hx, zero_lie, smul_zero]
  · have hM : M ≤ p.2 := by omega
    rw [Module.End.pow_map_zero_of_le hM hy, lie_zero, smul_zero]

private theorem exp_coeff_choose (t : ℂ) (i j : ℕ) :
    (((i + j).factorial : ℂ)⁻¹ * t ^ (i + j)) * (Nat.choose (i + j) i : ℂ) =
      ((i.factorial : ℂ)⁻¹ * t ^ i) * ((j.factorial : ℂ)⁻¹ * t ^ j) := by
  have hi : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hj : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hij : ((i + j).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (i + j))
  have hf : (Nat.choose (i + j) i : ℂ) * (i.factorial : ℂ) * (j.factorial : ℂ) =
      ((i + j).factorial : ℂ) := by
    have hfNat : Nat.choose (i + j) i * i.factorial * j.factorial = (i + j).factorial := by
      simpa only [Nat.add_sub_cancel_left] using
        (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j))
    exact_mod_cast hfNat
  have hc : (Nat.choose (i + j) i : ℂ) =
      ((i + j).factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ)) :=
    (eq_div_iff (mul_ne_zero hi hj)).mpr (by simpa only [mul_assoc] using hf)
  rw [hc, pow_add]
  field_simp [hi, hj, hij]
  <;> ring

/- Reindex only the nonzero support. In particular no positivity assumption on
   either bound is needed: a zero side forces the entire support to be empty. -/
private theorem sum_antidiagonal_rectangle (F : ℕ × ℕ → L) (N M : ℕ)
    (hzero : ∀ i j, N ≤ i ∨ M ≤ j → F (i, j) = 0) :
    (∑ r ∈ Finset.range (N + M), ∑ p ∈ Finset.antidiagonal r, F p) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M, F (i, j) := by
  classical
  rw [Finset.sum_sigma', ← Finset.sum_product']
  refine Finset.sum_bij_ne_zero (fun rp _ _ => rp.2) ?_ ?_ ?_ ?_
  · intro rp hrp hne
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      by_contra hi
      exact hne (hzero rp.2.1 rp.2.2 (Or.inl (Nat.le_of_not_gt hi)))
    · apply Finset.mem_range.mpr
      by_contra hj
      exact hne (hzero rp.2.1 rp.2.2 (Or.inr (Nat.le_of_not_gt hj)))
  · rintro ⟨r, p⟩ ha hna ⟨s, q⟩ hb hnb hpq
    change p = q at hpq
    have hr : p.1 + p.2 = r := Finset.mem_antidiagonal.mp (Finset.mem_sigma.mp ha).2
    have hs : q.1 + q.2 = s := Finset.mem_antidiagonal.mp (Finset.mem_sigma.mp hb).2
    cases hpq
    have hrs : r = s := hr.symm.trans hs
    exact Sigma.ext hrs (HEq.refl p)
  · intro p hp hne
    have hi : p.1 < N := Finset.mem_range.mp (Finset.mem_product.mp hp).1
    have hj : p.2 < M := Finset.mem_range.mp (Finset.mem_product.mp hp).2
    refine ⟨⟨p.1 + p.2, p⟩, ?_, hne, rfl⟩
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_range.mpr (show p.1 + p.2 < N + M by omega),
        Finset.mem_antidiagonal.mpr rfl⟩
  · intro rp hrp hne
    rfl

private theorem truncatedExp_lie (A : LieDerivation ℂ L L) (t : ℂ) (x y : L)
    (N M : ℕ) (hx : (A.toLinearMap ^ N) x = 0) (hy : (A.toLinearMap ^ M) y = 0) :
    truncatedExp A.toLinearMap t (N + M) ⁅x, y⁆ =
      ⁅truncatedExp A.toLinearMap t N x, truncatedExp A.toLinearMap t M y⁆ := by
  let F : ℕ × ℕ → L := fun p =>
    (((p.1.factorial : ℂ)⁻¹ * t ^ p.1) * ((p.2.factorial : ℂ)⁻¹ * t ^ p.2)) •
      ⁅(A.toLinearMap ^ p.1) x, (A.toLinearMap ^ p.2) y⁆
  have hzero : ∀ i j, N ≤ i ∨ M ≤ j → F (i, j) = 0 := by
    intro i j h
    dsimp [F]
    rcases h with hi | hj
    · rw [Module.End.pow_map_zero_of_le hi hx, zero_lie, smul_zero]
    · rw [Module.End.pow_map_zero_of_le hj hy, lie_zero, smul_zero]
  calc
    truncatedExp A.toLinearMap t (N + M) ⁅x, y⁆ =
        ∑ r ∈ Finset.range (N + M), ∑ p ∈ Finset.antidiagonal r, F p := by
      rw [truncatedExp_apply]
      apply Finset.sum_congr rfl
      intro r hr
      rw [pow_apply_lie, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hsum : p.1 + p.2 = r := Finset.mem_antidiagonal.mp hp
      dsimp [F]
      rw [smul_smul, ← hsum, exp_coeff_choose]
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M, F (i, j) :=
      sum_antidiagonal_rectangle F N M hzero
    _ = ⁅truncatedExp A.toLinearMap t N x, truncatedExp A.toLinearMap t M y⁆ := by
      rw [truncatedExp_apply, truncatedExp_apply, sum_lie_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [F, smul_lie, lie_smul, smul_smul]
      rw [mul_comm ((i.factorial : ℂ)⁻¹ * t ^ i) ((j.factorial : ℂ)⁻¹ * t ^ j)]

/-- The exponential of a pointwise locally nilpotent complex Lie derivation,
acting on the entire original Lie algebra. Its inverse is the exponential at -t. -/
noncomputable def localExpLieEquiv (A : LieDerivation ℂ L L)
    (hloc : ∀ x : L, ∃ N : ℕ, (A.toLinearMap ^ N) x = 0) (t : ℂ) : L ≃ₗ⁅ℂ⁆ L :=
  { toLinearMap := localExpLinear A.toLinearMap hloc t
    map_lie' := by
      intro x y
      obtain ⟨N, hx⟩ := hloc x
      obtain ⟨M, hy⟩ := hloc y
      change pointwiseExp A.toLinearMap hloc t ⁅x, y⁆ =
        ⁅pointwiseExp A.toLinearMap hloc t x, pointwiseExp A.toLinearMap hloc t y⁆
      rw [pointwiseExp_eq_cutoff A.toLinearMap hloc t ⁅x, y⁆ (N + M)
        (lie_killing_bound A x y N M hx hy),
        pointwiseExp_eq_cutoff A.toLinearMap hloc t x N hx,
        pointwiseExp_eq_cutoff A.toLinearMap hloc t y M hy]
      exact truncatedExp_lie A t x y N M hx hy
    invFun := localExpLinear A.toLinearMap hloc (-t)
    left_inv := localExpLinear_left_inv A.toLinearMap hloc t
    right_inv := localExpLinear_right_inv A.toLinearMap hloc t }

/-- Every killing bound computes the exponential, including N = 0 and t = 0. -/
theorem localExpLieEquiv_apply_of_bound (A : LieDerivation ℂ L L)
    (hloc : ∀ x : L, ∃ N : ℕ, (A.toLinearMap ^ N) x = 0)
    (t : ℂ) (x : L) (N : ℕ) (hx : (A.toLinearMap ^ N) x = 0) :
    localExpLieEquiv A hloc t x =
      ∑ n ∈ Finset.range N, ((n.factorial : ℂ)⁻¹ * t ^ n) • (A.toLinearMap ^ n) x := by
  exact (pointwiseExp_eq_cutoff A.toLinearMap hloc t x N hx).trans
    (truncatedExp_apply A.toLinearMap t N x)

/-- The zero parameter acts as the identity, even on an infinite-dimensional carrier. -/
theorem localExpLieEquiv_zero_apply (A : LieDerivation ℂ L L)
    (hloc : ∀ x : L, ∃ N : ℕ, (A.toLinearMap ^ N) x = 0) (x : L) :
    localExpLieEquiv A hloc 0 x = x := by
  obtain ⟨N, hx⟩ := hloc x
  let u : boundedKernel A.toLinearMap N := ⟨x, hx⟩
  change localExpLinear A.toLinearMap hloc 0 x = x
  rw [localExpLinear_on_kernel A.toLinearMap hloc N 0 u]
  simp [kernelExp, u]

/-- The parameter-addition law is obtained on one common bounded kernel. -/
theorem localExpLieEquiv_add_apply (A : LieDerivation ℂ L L)
    (hloc : ∀ x : L, ∃ N : ℕ, (A.toLinearMap ^ N) x = 0) (s t : ℂ) (x : L) :
    localExpLieEquiv A hloc (s + t) x =
      localExpLieEquiv A hloc s (localExpLieEquiv A hloc t x) := by
  obtain ⟨N, hx⟩ := hloc x
  let u : boundedKernel A.toLinearMap N := ⟨x, hx⟩
  have hc : Commute (s • kernelEnd A.toLinearMap N) (t • kernelEnd A.toLinearMap N) := by
    change (s • kernelEnd A.toLinearMap N) * (t • kernelEnd A.toLinearMap N) =
      (t • kernelEnd A.toLinearMap N) * (s • kernelEnd A.toLinearMap N)
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm s t]
  have he : kernelExp A.toLinearMap N (s + t) =
      kernelExp A.toLinearMap N s * kernelExp A.toLinearMap N t := by
    change IsNilpotent.exp ((s + t) • kernelEnd A.toLinearMap N) = _
    rw [add_smul]
    exact IsNilpotent.exp_add_of_commute hc
      ⟨N, scaled_kernelEnd_pow_eq_zero A.toLinearMap N s⟩
      ⟨N, scaled_kernelEnd_pow_eq_zero A.toLinearMap N t⟩
  change localExpLinear A.toLinearMap hloc (s + t) x =
    localExpLinear A.toLinearMap hloc s (localExpLinear A.toLinearMap hloc t x)
  calc
    localExpLinear A.toLinearMap hloc (s + t) x =
        (kernelExp A.toLinearMap N (s + t) u : L) :=
      localExpLinear_on_kernel A.toLinearMap hloc N (s + t) u
    _ = (kernelExp A.toLinearMap N s (kernelExp A.toLinearMap N t u) : L) := by
      rw [he, Module.End.mul_apply]
    _ = localExpLinear A.toLinearMap hloc s (kernelExp A.toLinearMap N t u : L) :=
      (localExpLinear_on_kernel A.toLinearMap hloc N s (kernelExp A.toLinearMap N t u)).symm
    _ = localExpLinear A.toLinearMap hloc s (localExpLinear A.toLinearMap hloc t x) := by
      rw [localExpLinear_on_kernel A.toLinearMap hloc N t u]

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTLocallyNilpotentExponential
