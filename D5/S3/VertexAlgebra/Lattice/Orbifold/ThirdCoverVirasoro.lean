/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Order-three covering Virasoro modes and complementary fractional currents. -/

import D5.S3.VertexAlgebra.PolynomialFockLZeroSpectrum
import D5.S3.VertexAlgebra.PolynomialFockVirasoroCentral

/-!
The operators act on the full rank-one polynomial Fock space. The two
nonintegral frequency grids are the integer indices of residues one and two,
divided by three. This oscillator calculation supplies the complementary
mode pairing relevant to the P48q order-three orbifold.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverVirasoro

open PolynomialFockSugawaraSupport (Fock L mode normalPair normalPair_support_interval)
open PolynomialFockSugawaraCommutators (mode_heisenberg L_mode_commutator)
open PolynomialFockLZeroSpectrum (lZeroEigenspace lZero_spectrum)

/-- Restrict to multiples of three, rescale, and shift mode zero. -/
noncomputable def coverMode (m : ℤ) : Module.End ℂ Fock :=
  (1 / 3 : ℂ) • L (3 * m) + (if m = 0 then (1 / 9 : ℂ) else 0) • 1

/-- Normalize the native current at fractional frequency r / 3. -/
noncomputable def current (scale : ℂ) (r : ℤ) : Module.End ℂ Fock :=
  scale • mode r

private theorem commutator_smul_add_scalar
    (A B : Module.End ℂ Fock) (a u v : ℂ) :
    (a • A + u • 1) * (a • B + v • 1) - (a • B + v • 1) * (a • A + u • 1) =
      (a * a) • (A * B - B * A) := by
  simp only [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    one_mul, mul_one, smul_add, smul_smul, smul_sub, mul_comm v a, mul_comm a u, mul_comm v u]
  abel

/-- The actual covering operators satisfy the Virasoro relation at charge three. -/
theorem coverMode_commutator (n m : ℤ) :
    coverMode n * coverMode m - coverMode m * coverMode n =
      ((n : ℂ) - (m : ℂ)) • coverMode (n + m) +
        (if n + m = 0 then (3 * (((n : ℂ) ^ 3 - (n : ℂ)) / 12)) •
          (1 : Module.End ℂ Fock) else 0) := by
  have support : 3 * n + 3 * m = 0 ↔ n + m = 0 := by omega
  have linear :
      ((1 / 3 : ℂ) * (1 / 3 : ℂ)) * (((3 * n : ℤ) : ℂ) - ((3 * m : ℤ) : ℂ)) =
        ((n : ℂ) - (m : ℂ)) * (1 / 3 : ℂ) := by
    push_cast
    ring
  unfold coverMode
  rw [commutator_smul_add_scalar, PolynomialFockVirasoroCentral.L_commutator]
  simp only [support]
  simp only [← mul_add, smul_add, smul_smul, linear, add_assoc]
  congr 1
  by_cases h : n + m = 0
  · have hm : m = -n := by omega
    simp only [h, ite_true, smul_smul, ← add_smul]
    congr 1
    rw [hm]
    push_cast
    ring
  · simp [h]

/-- The normalized bracket has coefficient r / 3. For a fractional r / 3,
its support consists exactly of the opposite frequency on the complementary grid. -/
theorem current_commutator (scale : ℂ) (hScale : scale * scale = (3 : ℂ)⁻¹) (r s : ℤ) :
    let bracket := current scale r * current scale s - current scale s * current scale r
    bracket = (if r + s = 0 then ((r : ℂ) / 3) • (1 : Module.End ℂ Fock) else 0) ∧
      (r % 3 ≠ 0 → (bracket ≠ 0 ↔ r + s = 0 ∧ r % 3 + s % 3 = 3)) := by
  have commutator :
      current scale r * current scale s - current scale s * current scale r =
        if r + s = 0 then ((r : ℂ) / 3) • (1 : Module.End ℂ Fock) else 0 := by
    calc
      _ = (scale * scale) • (mode r * mode s - mode s * mode r) := by
        simp only [current, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, smul_sub]
      _ = _ := by
        rw [mode_heisenberg, hScale]
        by_cases h : r + s = 0
        · simp only [h, ite_true, smul_smul, div_eq_mul_inv, mul_comm]
        · simp [h]
  refine ⟨commutator, fun hr => ?_⟩
  rw [commutator]
  by_cases h : r + s = 0
  · have opposite : r % 3 + s % 3 = 3 := by omega
    have hr' : r ≠ 0 := by omega
    have coefficient : (r : ℂ) / 3 ≠ 0 := div_ne_zero (by exact_mod_cast hr') (by norm_num)
    simp [h, opposite, smul_ne_zero coefficient (one_ne_zero : (1 : Module.End ℂ Fock) ≠ 0)]
  · simp [h]

/-- Covering modes shift the frequency by m and preserve both fractional grids. -/
theorem coverMode_current_commutator (scale : ℂ) (m r : ℤ) :
    let bracket := coverMode m * current scale r - current scale r * coverMode m
    bracket = (-(r : ℂ) / 3) • current scale (3 * m + r) ∧
      (3 * m + r) % 3 = r % 3 ∧
      (scale * scale = (3 : ℂ)⁻¹ → r % 3 ≠ 0 → bracket ≠ 0) := by
  have commutator : coverMode m * current scale r - current scale r * coverMode m =
      (-(r : ℂ) / 3) • current scale (3 * m + r) := by
    calc
      _ = ((1 / 3 : ℂ) * scale) • (L (3 * m) * mode r - mode r * L (3 * m)) := by
        simp only [coverMode, current, add_mul, mul_add, Algebra.smul_mul_assoc,
          Algebra.mul_smul_comm, one_mul, mul_one, smul_smul, smul_sub]
        module
      _ = _ := by
        rw [L_mode_commutator]
        simp only [current, smul_smul]
        module
  have residue : (3 * m + r) % 3 = r % 3 := by omega
  refine ⟨commutator, residue, fun hScale hr => ?_⟩
  let t := 3 * m + r
  have ht : t % 3 ≠ 0 := by simpa only [t, residue] using hr
  have nonzero : current scale t ≠ 0 := by
    intro h
    have pair := ((current_commutator scale hScale t (-t)).2 ht).mpr
      (show t + -t = 0 ∧ t % 3 + (-t) % 3 = 3 by omega)
    exact pair (by simp [h])
  have hr' : r ≠ 0 := by omega
  have coefficient : -(r : ℂ) / 3 ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hr')) (by norm_num)
  rw [commutator]
  exact smul_ne_zero coefficient nonzero

/-- Raising the first covering vacuum descendant returns twice the vacuum shift. -/
theorem coverMode_first_vacuum_descendant :
    coverMode 1 (coverMode (-1) (1 : Fock)) = (2 / 9 : ℂ) • (1 : Fock) := by
  have zeroMode : coverMode 0 (1 : Fock) = (1 / 9 : ℂ) • (1 : Fock) := by
    have vacuum : (1 : Fock) ∈ lZeroEigenspace 0 := by
      rw [(lZero_spectrum 0).1]
      exact Submodule.subset_span ⟨⟨0, by rfl⟩, by simp⟩
    simp only [lZeroEigenspace, LinearMap.mem_ker, Nat.cast_zero, zero_smul, sub_zero] at vacuum
    simp [coverMode, vacuum]
  have positiveMode : coverMode 1 (1 : Fock) = 0 := by
    have term (k : ℤ) : normalPair (3 - k) k (1 : Fock) = 0 := by
      by_contra h
      have bounds := normalPair_support_interval 3 (1 : Fock)
        (show k ∈ Function.support (fun j : ℤ => normalPair (3 - j) j (1 : Fock)) from h)
      simp only [Set.mem_Ioo, MvPolynomial.vars_one, Finset.sup_empty] at bounds
      change 3 - (0 + 2 : ℤ) < k ∧ k < (0 + 2 : ℤ) at bounds
      omega
    have native : L 3 (1 : Fock) = 0 := by
      change (2 : ℂ)⁻¹ • (∑ᶠ k : ℤ, normalPair (3 - k) k (1 : Fock)) = 0
      simp [term]
    simp [coverMode, native]
  have relation := congrArg (fun T : Module.End ℂ Fock => T 1) (coverMode_commutator 1 (-1))
  norm_num [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    positiveMode, zeroMode, smul_smul] at relation
  exact relation

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverVirasoro
