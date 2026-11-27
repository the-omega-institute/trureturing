/- GID: D5/S3/Zeros/GRH/Lib/Adelic/Unitary/SpaceGram
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/Unitary/SpaceGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.Unitary.SpaceGram. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Unitary/SpaceGram.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.GaussSum.LocalHomUnit
import D5.S3.Zeros.GRH.Lib.Adelic.Unitary.SpaceDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Adelic points of unitary groups, levels and Haar measures (known result; see
Lib.Adelic.Reduction.MinkowskiSecond).

This file: Gram matrix of an adelically framed hermitian space is invertible and hermitian. -/

open Matrix

section

variable {E : Type*} [Field E] [NumberField E] {n : Type _} [Fintype n] {s : n → ℤˣ}

@[simp] lemma stdForm_mul_self : stdForm E s * stdForm E s = 1 := by
    simp [stdForm, funext_iff, ← Int.cast_mul]

omit [Fintype n] in
@[simp] lemma stdForm_one : stdForm (n := n) E 1 = 1 := congr(diagonal $(by aesop))

@[simp] lemma isUnit_stdForm : IsUnit (stdForm E s) := .of_mul_eq_one _ stdForm_mul_self

end

variable {E : Type*} [Field E] [CMType E] {n : Type _} [Fintype n] {s : n → ℤˣ} (V : Space E n s)

omit [Fintype n] in
@[simp] lemma stdForm_conjTranspose : (stdForm E s)ᴴ = stdForm E s := by aesop (add simp stdForm)

@[simp] lemma conjTranspose_map_toAdele {m k} (a : Matrix m k E) : (a.map toAdele)ᴴ =
  aᴴ.map toAdele := by aesop

lemma Space.map_J : V.J.map toAdele = V.x⁻¹.1ᴴ * stdForm E s * V.x⁻¹ :=
  (gram_inv_of_gram_eq V.gram_point).symm

/-- The matrix J over E of a space (J, x) is invertible. -/
@[simp] lemma Space.isUnit_J : IsUnit V.J := isUnit_of_mapMatrix toAdele (by simp [map_J])

lemma Space.map_J_inv_mul_map_J : V.J⁻¹.map toAdele * V.J.map toAdele = 1 :=
  GeneralLinearGroup.coe_map_inv_mul_map _ V.isUnit_J.unit

lemma Space.map_J_inv : V.J⁻¹.map toAdele = V.x * stdForm E s * V.x.1ᴴ := left_inv_eq_right_inv
    V.map_J_inv_mul_map_J (by simp [← mul_assoc, mul_eq_one_comm, gram_point])

/-- The matrix J over E of a space (J, x) is hermitian: Jᴴ = J. -/
lemma Space.isHermitian_J : V.J.IsHermitian := map_injective toAdele.injective (by
  simp [← conjTranspose_map_toAdele, map_J, mul_assoc])

lemma Space.conjTranspose_J : V.Jᴴ = V.J := V.isHermitian_J
