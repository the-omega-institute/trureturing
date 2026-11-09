/- GID: D5/S3/Quantum/Matrix/NonsingularPencilStateBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/NonsingularPencilStateBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: Connected nonsingular Hermitian pencils give strict budgets for all positive functionals. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic

/-
The compact-sphere proof in quadratic_positive_open is adapted from
TauCetiProject/TauCeti, commit 8c1eaed7cd02e6fee2db1f66783fb8f03025d76d,
TauCeti/Analysis/Matrix/PosDef.lean, isOpen_setOfPred_re_dotProduct_pos.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude.
Replace this transplanted helper by a direct upstream application when the
pinned Mathlib supplies its equivalent statement.
-/

noncomputable section
open Matrix Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.NonsingularPencilStateBudget

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem quadratic_positive_open :
    IsOpen {M : Matrix n n ℂ | ∀ x : n → ℂ, x ≠ 0 →
      0 < (star x ⬝ᵥ M *ᵥ x).re} := by
  rw [isOpen_iff_mem_nhds]
  intro M hM
  have key : ∀ᶠ N in 𝓝 M, ∀ x ∈ Metric.sphere (0 : n → ℂ) 1,
      0 < (star x ⬝ᵥ N *ᵥ x).re := by
    refine (isCompact_sphere (0 : n → ℂ) 1).eventually_forall_of_forall_eventually
      fun y hy => ?_
    have hcont : Continuous fun z : Matrix n n ℂ × (n → ℂ) =>
        (star z.2 ⬝ᵥ z.1 *ᵥ z.2).re := by fun_prop
    exact (hcont.tendsto (M, y)).eventually_const_lt
      (hM y (ne_zero_of_mem_sphere one_ne_zero ⟨y, hy⟩))
  filter_upwards [key] with N hN x hx
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h := hN (‖x‖⁻¹ • x) (by simp [norm_smul, hx0.ne'])
  simp only [star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, RCLike.smul_re] at h
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hx0)).mp
    ((mul_pos_iff_of_pos_left (inv_pos.mpr hx0)).mp h)

private theorem connected_posDef {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (P : X → Matrix n n ℂ) (hP : Continuous P)
    (hH : ∀ a, (P a).IsHermitian) (hdet : ∀ a, (P a).det ≠ 0)
    (a₀ : X) (h₀ : (P a₀).PosDef) : ∀ a, (P a).PosDef := by
  have hc : IsClosed {a | (P a).PosDef} := by
    have heq : {a | (P a).PosDef} = {a | (P a).PosSemidef} := by
      ext a
      exact ⟨fun h => h.posSemidef, fun h => h.posDef_iff_det_ne_zero.mpr (hdet a)⟩
    rw [heq]
    exact Matrix.posSemidef_is_closed.preimage hP
  have ho : IsOpen {a | (P a).PosDef} := by
    convert quadratic_positive_open.preimage hP using 1
    ext a
    constructor
    · exact fun h x hx => h.re_dotProduct_pos hx
    · intro h
      exact Matrix.PosDef.of_dotProduct_mulVec_pos (hH a) fun x hx =>
        RCLike.pos_iff.mpr ⟨h x hx, (hH a).im_star_dotProduct_mulVec_self x⟩
  have hu := (IsClopen.eq_univ ⟨hc, ho⟩ ⟨a₀, h₀⟩)
  intro a
  have : a ∈ {a | (P a).PosDef} := by rw [hu]; trivial
  exact this

/-- The same matrix algebra carries every parameter and every positive reading. -/
def pencil (E K G : Matrix n n ℂ) (p q : ℝ) : Matrix n n ℂ :=
  E + (p ^ 2 + q ^ 2) • 1 - (2 * p) • K - (2 * q) • G

private theorem positive_reading {A : Matrix n n ℂ} (hA : A.PosDef)
    (φ : Matrix n n ℂ →ₚ[ℂ] ℂ) (hm : 0 < (φ 1).re) : 0 < (φ A).re := by
  haveI : Nonempty n := by
    by_contra h
    haveI : IsEmpty n := not_nonempty_iff.mp h
    have : (1 : Matrix n n ℂ) = 0 := Subsingleton.elim _ _
    simpa [this] using hm
  obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff A hA.isHermitian).mpr
    (fun x hx => hA.isStrictlyPositive.spectrum_pos hx)
  have hh := φ.monotone hle
  have hre := Complex.le_def.mp hh |>.1
  simp only [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul,
    map_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hre
  exact (mul_pos hr hm).trans_le hre

/-- Nonsingularity on the whole real plane, together with positivity at the origin,
forces a strict homogeneous budget for every positive complex-linear functional. -/
theorem strict_budget (E K G : Matrix n n ℂ) (hE : E.PosDef)
    (hK : K.IsHermitian) (hG : G.IsHermitian)
    (hdet : ∀ p q : ℝ, (pencil E K G p q).det ≠ 0)
    (φ : Matrix n n ℂ →ₚ[ℂ] ℂ) (hm : 0 < (φ 1).re) :
    (φ G).re ^ 2 + (φ K).re ^ 2 < (φ 1).re * (φ E).re := by
  let P : ℝ × ℝ → Matrix n n ℂ := fun a => pencil E K G a.1 a.2
  have hP : Continuous P := by unfold P pencil; fun_prop
  have hH (a : ℝ × ℝ) : (P a).IsHermitian :=
    ((hE.isHermitian.add ((isHermitian_one : (1 : Matrix n n ℂ).IsHermitian).smul
      (IsSelfAdjoint.all _))).sub (hK.smul (IsSelfAdjoint.all _))).sub
      (hG.smul (IsSelfAdjoint.all _))
  have h₀ : (P (0, 0)).PosDef := by simpa [P, pencil] using hE
  have hpos := connected_posDef P hP hH (fun a => hdet a.1 a.2) (0, 0) h₀
  have hh := positive_reading (hpos ((φ K).re / (φ 1).re, (φ G).re / (φ 1).re)) φ hm
  simp only [P, pencil, map_sub, map_add, ← Complex.coe_smul, map_smul,
    smul_eq_mul, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hh
  have hm0 := ne_of_gt hm
  field_simp at hh
  nlinarith [sq_nonneg ((φ G).re), sq_nonneg ((φ K).re)]

end D5.S3.Quantum.Matrix.NonsingularPencilStateBudget
