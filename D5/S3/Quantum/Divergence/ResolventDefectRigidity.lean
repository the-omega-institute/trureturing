/- GID: D5/S3/Quantum/Divergence/ResolventDefectRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ResolventDefectRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A saturated comparison contraction has a quantitative positive resolvent defect. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Resolvent defects for relative-modular comparisons

This is the contraction version of the positive resolvent comparison used in
Petz's equality theorem. It allows a nonzero comparison defect B - V* A V.
The distinguished vector must saturate the contraction: V* V b = b.
Trace-normalized square-root density vectors supply that condition in the
relative-modular application. Contraction alone does not imply it.

This module does not yet prove Petz equality, the integral representation of
the entropy defect, or support-corner reduction for singular states.
-/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Divergence.ResolventDefectRigidity

variable {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

omit [DecidableEq n] in
private theorem pair_re_swap (x y : n → ℂ) :
    (star x ⬝ᵥ y).re = (star y ⬝ᵥ x).re := by
  have h := congrArg Complex.re (Matrix.star_dotProduct x y)
  simpa using h

omit [DecidableEq n] in
private theorem hermitian_pair_re_swap (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (x y : n → ℂ) :
    (star x ⬝ᵥ (H *ᵥ y)).re = (star y ⬝ᵥ (H *ᵥ x)).re := by
  have h : star x ⬝ᵥ (H *ᵥ y) = star (star y ⬝ᵥ (H *ᵥ x)) := by
    rw [Matrix.star_dotProduct, Matrix.star_mulVec,
      ← Matrix.dotProduct_mulVec, hH.eq]
  simpa using congrArg Complex.re h

omit [DecidableEq n] [DecidableEq m] in
private theorem adjoint_pair (V : Matrix n m ℂ) (y : m → ℂ) (z : n → ℂ) :
    star (V *ᵥ y) ⬝ᵥ z = star y ⬝ᵥ (Vᴴ *ᵥ z) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]

omit [DecidableEq n] [DecidableEq m] in
private theorem comparison_energy (H : Matrix n n ℂ) (K : Matrix m m ℂ)
    (hH : H.IsHermitian) (V : Matrix n m ℂ)
    (a x : n → ℂ) (b y : m → ℂ)
    (hx : H *ᵥ x = a) (hy : K *ᵥ y = b) (hab : Vᴴ *ᵥ a = b) :
    (star a ⬝ᵥ x).re - (star b ⬝ᵥ y).re =
      (star (x - V *ᵥ y) ⬝ᵥ (H *ᵥ (x - V *ᵥ y))).re +
      (star y ⬝ᵥ ((K - Vᴴ * H * V) *ᵥ y)).re := by
  have hxx : (star x ⬝ᵥ (H *ᵥ x)).re = (star a ⬝ᵥ x).re := by
    rw [hx, pair_re_swap]
  have hyy : (star y ⬝ᵥ (K *ᵥ y)).re = (star b ⬝ᵥ y).re := by
    rw [hy, pair_re_swap]
  have hzx : (star (V *ᵥ y) ⬝ᵥ (H *ᵥ x)).re = (star b ⬝ᵥ y).re := by
    rw [hx, adjoint_pair, hab, pair_re_swap]
  have hxz : (star x ⬝ᵥ (H *ᵥ (V *ᵥ y))).re = (star b ⬝ᵥ y).re := by
    rw [hermitian_pair_re_swap H hH, hzx]
  have hzz : star y ⬝ᵥ ((Vᴴ * H * V) *ᵥ y) =
      star (V *ᵥ y) ⬝ᵥ (H *ᵥ (V *ᵥ y)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← adjoint_pair]
  simp only [Matrix.mulVec_sub, Matrix.sub_mulVec, star_sub,
    sub_dotProduct, dotProduct_sub, Complex.sub_re]
  rw [hxx, hyy, hzx, hxz, hzz]
  ring

private theorem complex_eq_zero_of_nonneg (z : ℂ) (hz : 0 ≤ z) (hre : z.re = 0) :
    z = 0 :=
  Complex.ext hre (Complex.nonneg_iff.mp hz).2.symm

omit [DecidableEq n] in
theorem contraction_saturation (V : Matrix n m ℂ) (hV : Vᴴ * V ≤ 1)
    (b : m → ℂ)
    (hb : (star (V *ᵥ b) ⬝ᵥ (V *ᵥ b)).re = (star b ⬝ᵥ b).re) :
    Vᴴ *ᵥ (V *ᵥ b) = b := by
  have hD : (1 - Vᴴ * V).PosSemidef := Matrix.le_iff.mp hV
  have hq : (star b ⬝ᵥ ((1 - Vᴴ * V) *ᵥ b)).re = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re,
      ← Matrix.mulVec_mulVec, ← adjoint_pair, hb, sub_self]
  have hz := (hD.dotProduct_mulVec_zero_iff (x := b)).mp
    (complex_eq_zero_of_nonneg _ (hD.dotProduct_mulVec_nonneg b) hq)
  have heq : b - Vᴴ *ᵥ (V *ᵥ b) = 0 := by
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec] using hz
  exact (sub_eq_zero.mp heq).symm

/-- A contraction comparison has a positive resolvent defect controlling the
actual vector-intertwining error. Zero defect is equivalent to simultaneous
vanishing of the intertwining error and comparison defect on the resolvent vector.
Norm saturation of the distinguished vector is essential. -/
theorem resolvent_defect_identity_and_bound
    (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (V : Matrix n m ℂ) (hV : Vᴴ * V ≤ 1)
    (hAB : Vᴴ * A * V ≤ B) (b : m → ℂ)
    (hb : (star (V *ᵥ b) ⬝ᵥ (V *ᵥ b)).re = (star b ⬝ᵥ b).re)
    (t : ℝ) (ht : 0 < t) :
    let H := A + t • (1 : Matrix n n ℂ)
    let K := B + t • (1 : Matrix m m ℂ)
    let a := V *ᵥ b
    let x := H⁻¹ *ᵥ a
    let y := K⁻¹ *ᵥ b
    let w := x - V *ᵥ y
    let C := K - Vᴴ * H * V
    let g := (star a ⬝ᵥ x).re - (star b ⬝ᵥ y).re
    g = (star w ⬝ᵥ (H *ᵥ w)).re + (star y ⬝ᵥ (C *ᵥ y)).re ∧
      t * (star w ⬝ᵥ w).re ≤ g ∧ (g = 0 ↔ w = 0 ∧ C *ᵥ y = 0) := by
  let H := A + t • (1 : Matrix n n ℂ)
  let K := B + t • (1 : Matrix m m ℂ)
  let a := V *ᵥ b
  let x := H⁻¹ *ᵥ a
  let y := K⁻¹ *ᵥ b
  let w := x - V *ᵥ y
  let C := K - Vᴴ * H * V
  let g := (star a ⬝ᵥ x).re - (star b ⬝ᵥ y).re
  change g = (star w ⬝ᵥ (H *ᵥ w)).re + (star y ⬝ᵥ (C *ᵥ y)).re ∧
    t * (star w ⬝ᵥ w).re ≤ g ∧ (g = 0 ↔ w = 0 ∧ C *ᵥ y = 0)
  have hH : H.PosDef := Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul ht)
  have hK : K.PosDef := Matrix.PosDef.posSemidef_add hB (Matrix.PosDef.one.smul ht)
  have hx : H *ᵥ x = a := by
    change H *ᵥ (H⁻¹ *ᵥ a) = a
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H
      ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit), Matrix.one_mulVec]
  have hy : K *ᵥ y = b := by
    change K *ᵥ (K⁻¹ *ᵥ b) = b
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv K
      ((Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit), Matrix.one_mulVec]
  have hidentity : g = (star w ⬝ᵥ (H *ᵥ w)).re +
      (star y ⬝ᵥ (C *ᵥ y)).re :=
    comparison_energy H K hH.isHermitian V a x b y hx hy
      (contraction_saturation V hV b hb)
  have hC : C.PosSemidef := by
    have h₁ := (Matrix.le_iff.mp hAB)
    have h₂ := (Matrix.le_iff.mp hV).smul ht.le
    have heq : C = (B - Vᴴ * A * V) + t • (1 - Vᴴ * V) := by
      dsimp only [C, H, K]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, smul_sub]
      abel
    rw [heq]
    exact h₁.add h₂
  have hcy : 0 ≤ (star y ⬝ᵥ (C *ᵥ y)).re :=
    (Complex.nonneg_iff.mp (hC.dotProduct_mulVec_nonneg y)).1
  have haw : 0 ≤ (star w ⬝ᵥ (A *ᵥ w)).re :=
    (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg w)).1
  have henergy : (star w ⬝ᵥ (H *ᵥ w)).re =
      (star w ⬝ᵥ (A *ᵥ w)).re + t * (star w ⬝ᵥ w).re := by
    simp [H, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul, Complex.real_smul]
  have hbound : t * (star w ⬝ᵥ w).re ≤ g := by
    rw [hidentity, henergy]
    linarith
  refine ⟨hidentity, hbound, ?_⟩
  constructor
  · intro hg
    have hqw : 0 ≤ (star w ⬝ᵥ w).re :=
      (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg w)).1
    have hqw0 : (star w ⬝ᵥ w).re = 0 := by
      rw [hg] at hbound
      nlinarith
    have hw : w = 0 := dotProduct_star_self_eq_zero.mp
      (complex_eq_zero_of_nonneg _ (dotProduct_star_self_nonneg w) hqw0)
    have hqy0 : (star y ⬝ᵥ (C *ᵥ y)).re = 0 := by
      simpa only [hw, star_zero, Matrix.mulVec_zero, dotProduct_zero,
        Complex.zero_re, zero_add] using hidentity.symm.trans hg
    exact ⟨hw, (hC.dotProduct_mulVec_zero_iff (x := y)).mp
      (complex_eq_zero_of_nonneg _ (hC.dotProduct_mulVec_nonneg y) hqy0)⟩
  · rintro ⟨hw, hCy⟩
    rw [hidentity, hw, hCy]
    simp

#print axioms resolvent_defect_identity_and_bound

end D5.S3.Quantum.Divergence.ResolventDefectRigidity
