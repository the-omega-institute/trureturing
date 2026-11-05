/- GID: D5/S3/HilbertOperators/DavisKahanProjector
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/DavisKahanProjector
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Full arbitrary-RCLike complete-Hilbert common-gap Davis--Kahan projector norm bound. -/

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in
 docs/reports/brooks-suppliers/daviskahan-LICENSE.txt.
Authors: Jon Crall, GPT 5.6 High, Claude Fable 5, Claude Opus 5

Adapted from LeanPool/lean-pool at bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8,
whose DavisKahan sources originate in AIQ-Kitware's Davis--Kahan formalization
at 38e37da6e147cd0016da1eb05987c3edf7d95b39. Per-file attribution and source
correspondence are in Library/HilbertOperators/leanpool2026daviskahanprojector.md.
The full Apache 2.0 license and upstream NOTICE are retained in
 docs/reports/brooks-suppliers/daviskahan-LICENSE.txt and daviskahan-NOTICE.txt.

Modified file: combines the five attributed source units, expands their
quadratic-form and reducing-subspace predicates, and uses native pinned
Mathlib projection, invariance, and Pythagorean suppliers. Namespaces and
one private helper name are adapted; the mathematical scope is preserved.
Retire each redundant port when an equivalent declaration is available at
this repository's own future Mathlib pin, and directly reuse that declaration.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Semisimple
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs

/-! # Common-gap Davis--Kahan projector bound -/

open scoped InnerProductSpace

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace ContinuousLinearMap

theorem norm_le_of_abs_re_inner_map_self_le {C : E →L[𝕜] E} (hC : C.IsSymmetric)
    {κ : ℝ} (hκ : 0 ≤ κ) (h : ∀ x, |RCLike.re ⟪C x, x⟫_𝕜| ≤ κ * ‖x‖ ^ 2) : ‖C‖ ≤ κ := by
  rw [C.norm_eq_iSup_rayleighQuotient hC]
  refine ciSup_le fun x => ?_
  -- names the application so the norm bound applies to it directly.
  change |C.reApplyInnerSelf x / ‖x‖ ^ 2| ≤ κ
  rcases eq_or_ne x 0 with rfl | hx
  · simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hκ
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply, abs_div, abs_sq,
      div_le_iff₀ (by positivity)]
    exact h x

section SylvesterBound

variable {A : E →L[𝕜] E} {B : F →L[𝕜] F} {X Y : F →L[𝕜] E}

private theorem re_inner_ofReal_smul_one_sub_apply_self (A : E →L[𝕜] E) (r : ℝ) (x : E) :
    RCLike.re ⟪((r : 𝕜) • (1 : E →L[𝕜] E) - A) x, x⟫_𝕜
      = r * ‖x‖ ^ 2 - RCLike.re ⟪A x, x⟫_𝕜 := by
  simp only [sub_apply, smul_apply,
    one_apply_eq_self, inner_sub_left, inner_smul_left, RCLike.conj_ofReal,
    map_sub, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
private theorem isSymmetric_ofReal_smul_one_sub (hA : A.IsSymmetric) (r : ℝ) :
    (((r : 𝕜) • (1 : E →L[𝕜] E) - A)).IsSymmetric := fun x y => by
  simp only [ContinuousLinearMap.coe_coe, sub_apply,
    smul_apply, one_apply_eq_self, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
  congr 1
  exact hA x y
private theorem le_opNorm_of_le_re_inner_map_self {δ : ℝ}
    (hAc : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) {x₀ : E} (hx₀ : x₀ ≠ 0) : δ ≤ ‖A‖ := by
  have hupper : RCLike.re ⟪A x₀, x₀⟫_𝕜 ≤ ‖A‖ * ‖x₀‖ ^ 2 :=
    calc RCLike.re ⟪A x₀, x₀⟫_𝕜 ≤ ‖⟪A x₀, x₀⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ ‖A x₀‖ * ‖x₀‖ := norm_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖x₀‖ * ‖x₀‖ := by gcongr; exact A.le_opNorm x₀
      _ = ‖A‖ * ‖x₀‖ ^ 2 := by ring
  have hx₀2 : (0 : ℝ) < ‖x₀‖ ^ 2 := by positivity
  nlinarith [hAc x₀]
private theorem norm_opNorm_smul_one_sub_le (hA : A.IsSymmetric) {δ : ℝ} (hδA : δ ≤ ‖A‖)
    (hAc : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) :
    ‖(‖A‖ : 𝕜) • (1 : E →L[𝕜] E) - A‖ ≤ ‖A‖ - δ := by
  refine norm_le_of_abs_re_inner_map_self_le (isSymmetric_ofReal_smul_one_sub hA ‖A‖)
    (by linarith) fun x => ?_
  rw [re_inner_ofReal_smul_one_sub_apply_self]
  have hupper : RCLike.re ⟪A x, x⟫_𝕜 ≤ ‖A‖ * ‖x‖ ^ 2 :=
    calc RCLike.re ⟪A x, x⟫_𝕜 ≤ ‖⟪A x, x⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ ‖A x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖x‖ * ‖x‖ := by gcongr; exact A.le_opNorm x
      _ = ‖A‖ * ‖x‖ ^ 2 := by ring
  rw [abs_of_nonneg (by linarith)]
  linarith [hAc x]

end SylvesterBound

section RectangularAbstractSylvesterBound

variable {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X Y : E →L[𝕜] F}
variable {N : (E →L[𝕜] F) → ℝ}
  (hadd : ∀ f g : E →L[𝕜] F, N (f + g) ≤ N f + N g)
  (hsmul : ∀ (a : 𝕜) (f : E →L[𝕜] F), N (a • f) = ‖a‖ * N f)
  (hidealL : ∀ C : F →L[𝕜] F, ∀ f : E →L[𝕜] F,
    N (C ∘L f) ≤ ‖C‖ * N f)
  (hidealR : ∀ f : E →L[𝕜] F, ∀ C : E →L[𝕜] E,
    N (f ∘L C) ≤ N f * ‖C‖)

include hadd hsmul in
private theorem rectangular_nonneg_of_add_le_of_smul (f : E →L[𝕜] F) : 0 ≤ N f := by
  have hN0 : N 0 = 0 := by
    have h := hsmul 0 0
    rwa [zero_smul, norm_zero, zero_mul] at h
  have hneg : N (-f) = N f := by
    rw [show -f = (-1 : 𝕜) • f by rw [neg_one_smul], hsmul,
      norm_neg, norm_one, one_mul]
  have h := hadd f (-f)
  rw [add_neg_cancel, hN0, hneg] at h
  linarith
include hadd hsmul hidealL hidealR in
theorem le_div_of_comp_add_comp_eq_rectangular
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ)
    (hAc : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_𝕜)
    (hXY : A ∘L X + X ∘L B = Y) : N X ≤ N Y / (2 * δ) := by
  have hNY : 0 ≤ N Y := rectangular_nonneg_of_add_le_of_smul hadd hsmul Y
  rcases eq_or_ne X 0 with rfl | hX
  · have hN0 : N (0 : E →L[𝕜] F) = 0 := by
      have h := hsmul 0 0
      rwa [zero_smul, norm_zero, zero_mul] at h
    rw [hN0]
    positivity
  · obtain ⟨x₀, hx₀⟩ := DFunLike.ne_iff.mp hX
    simp only [zero_apply] at hx₀
    have hδA : δ ≤ ‖A‖ := le_opNorm_of_le_re_inner_map_self hAc hx₀
    have hδB : δ ≤ ‖B‖ :=
      le_opNorm_of_le_re_inner_map_self hBc (x₀ := x₀) fun hx₀' =>
        hx₀ (by rw [hx₀']; exact map_zero X)
    have habsorb : ((‖A‖ + ‖B‖ : ℝ) : 𝕜) • X
        = Y + ((‖A‖ : 𝕜) • 1 - A) ∘L X + X ∘L ((‖B‖ : 𝕜) • 1 - B) := by
      ext v
      have hv : A (X v) + X (B v) = Y v := by
        simpa [add_apply, ContinuousLinearMap.comp_apply] using
          congrArg (fun W : E →L[𝕜] F => W v) hXY
      simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, sub_apply,
        one_apply_eq_self, map_sub, map_smul]
      rw [← hv]
      push_cast
      module
    have hkey : (‖A‖ + ‖B‖) * N X
        ≤ N Y + (‖A‖ - δ) * N X + N X * (‖B‖ - δ) :=
      calc
        (‖A‖ + ‖B‖) * N X
            = N (((‖A‖ + ‖B‖ : ℝ) : 𝕜) • X) := by
                rw [hsmul, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
        _ = N (Y + ((‖A‖ : 𝕜) • 1 - A) ∘L X
              + X ∘L ((‖B‖ : 𝕜) • 1 - B)) := by rw [habsorb]
        _ ≤ N Y + N (((‖A‖ : 𝕜) • 1 - A) ∘L X)
              + N (X ∘L ((‖B‖ : 𝕜) • 1 - B)) := by
                have h1 := hadd
                  (Y + ((‖A‖ : 𝕜) • 1 - A) ∘L X)
                  (X ∘L ((‖B‖ : 𝕜) • 1 - B))
                have h2 := hadd Y (((‖A‖ : 𝕜) • 1 - A) ∘L X)
                linarith
        _ ≤ N Y + (‖A‖ - δ) * N X + N X * (‖B‖ - δ) := by
                gcongr
                · calc
                    N (((‖A‖ : 𝕜) • 1 - A) ∘L X)
                        ≤ ‖(‖A‖ : 𝕜) • 1 - A‖ * N X := hidealL _ _
                    _ ≤ (‖A‖ - δ) * N X := by
                        gcongr ?_ * _
                        · exact rectangular_nonneg_of_add_le_of_smul hadd hsmul X
                        · exact norm_opNorm_smul_one_sub_le hA hδA hAc
                · calc
                    N (X ∘L ((‖B‖ : 𝕜) • 1 - B))
                        ≤ N X * ‖(‖B‖ : 𝕜) • 1 - B‖ := hidealR _ _
                    _ ≤ N X * (‖B‖ - δ) := by
                        gcongr _ * ?_
                        · exact rectangular_nonneg_of_add_le_of_smul hadd hsmul X
                        · exact norm_opNorm_smul_one_sub_le hB hδB hBc
    have hexpand : (‖A‖ - δ) * N X + N X * (‖B‖ - δ)
        = (‖A‖ + ‖B‖) * N X - 2 * δ * N X := by ring
    have hfinal : 2 * δ * N X ≤ N Y := by linarith [hkey, hexpand]
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact hfinal
include hadd hsmul hidealL hidealR in
theorem le_div_of_comp_sub_comp_eq_rectangular
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {c g : ℝ} (hg : 0 < g)
    (hAc : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hXY : A ∘L X - X ∘L B = Y) : N X ≤ N Y / g := by
  set r : ℝ := c + g / 2 with hr
  have hA' : (A - (r : 𝕜) • (1 : F →L[𝕜] F)).IsSymmetric := fun x y => by
    simp only [ContinuousLinearMap.coe_coe, sub_apply, smul_apply, one_apply_eq_self,
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      RCLike.conj_ofReal]
    congr 1
    exact hA x y
  have hB' : ((r : 𝕜) • (1 : E →L[𝕜] E) - B).IsSymmetric :=
    isSymmetric_ofReal_smul_one_sub hB r
  have hAc' : ∀ x, g / 2 * ‖x‖ ^ 2
      ≤ RCLike.re ⟪(A - (r : 𝕜) • (1 : F →L[𝕜] F)) x, x⟫_𝕜 := by
    intro x
    have hneg : (A - (r : 𝕜) • (1 : F →L[𝕜] F)) x
        = -(((r : 𝕜) • (1 : F →L[𝕜] F) - A) x) := by
      simp [neg_sub]
    rw [hneg, inner_neg_left, map_neg,
      re_inner_ofReal_smul_one_sub_apply_self, hr]
    linarith [hAc x]
  have hBc' : ∀ x, g / 2 * ‖x‖ ^ 2
      ≤ RCLike.re ⟪((r : 𝕜) • (1 : E →L[𝕜] E) - B) x, x⟫_𝕜 := by
    intro x
    rw [re_inner_ofReal_smul_one_sub_apply_self, hr]
    linarith [hBc x]
  have hXY' : (A - (r : 𝕜) • (1 : F →L[𝕜] F)) ∘L X
      + X ∘L ((r : 𝕜) • (1 : E →L[𝕜] E) - B) = Y := by
    ext v
    have hv : A (X v) - X (B v) = Y v := by
      simpa [sub_apply, ContinuousLinearMap.comp_apply] using
        congrArg (fun W : E →L[𝕜] F => W v) hXY
    simp only [add_apply, ContinuousLinearMap.comp_apply, sub_apply, smul_apply,
      one_apply_eq_self, map_sub, map_smul, ← hv]
    module
  have hfin := le_div_of_comp_add_comp_eq_rectangular hadd hsmul hidealL hidealR
    hA' hB' (by linarith : (0 : ℝ) < g / 2) hAc' hBc' hXY'
  rwa [show 2 * (g / 2) = g by ring] at hfin

end RectangularAbstractSylvesterBound

section OperatorNormSylvesterBound

variable {A : E →L[𝕜] E} {B : F →L[𝕜] F} {X Y : F →L[𝕜] E}

theorem opNorm_le_div_of_comp_sub_comp_eq (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {c g : ℝ} (hg : 0 < g)
    (hAc : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ v, RCLike.re ⟪B v, v⟫_𝕜 ≤ c * ‖v‖ ^ 2)
    (hXY : A ∘L X - X ∘L B = Y) : ‖X‖ ≤ ‖Y‖ / g :=
  le_div_of_comp_sub_comp_eq_rectangular (N := fun f : F →L[𝕜] E => ‖f‖)
    (fun f g => norm_add_le f g) (fun a f => norm_smul a f)
    (fun C f => ContinuousLinearMap.opNorm_comp_le C f)
    (fun f C => ContinuousLinearMap.opNorm_comp_le f C)
    hA hB hg hAc hBc hXY

end OperatorNormSylvesterBound

end ContinuousLinearMap

end TauCeti


namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem re_inner_reducedExtension_self {R : E →ₗ[𝕜] E} {W : Submodule 𝕜 E}
    [W.HasOrthogonalProjection] (hinv : ∀ x ∈ W, R x ∈ W) (κ : ℝ) (x : E) :
    RCLike.re ⟪R (W.starProjection x)
        + ((κ : ℝ) : 𝕜) • (x - W.starProjection x), x⟫_𝕜
      = RCLike.re ⟪R (W.starProjection x), W.starProjection x⟫_𝕜
        + κ * ‖x - W.starProjection x‖ ^ 2 := by
  have hpx : W.starProjection x ∈ W := W.starProjection_apply_mem x
  have hrest : x - W.starProjection x ∈ Wᗮ :=
    W.sub_starProjection_mem_orthogonal x
  have hre : RCLike.re ⟪R (W.starProjection x)
        + ((κ : ℝ) : 𝕜) • (x - W.starProjection x), x⟫_𝕜
      = RCLike.re ⟪R (W.starProjection x), x⟫_𝕜
        + κ * RCLike.re ⟪x - W.starProjection x, x⟫_𝕜 := by
    rw [inner_add_left, inner_smul_left, RCLike.conj_ofReal, map_add,
      RCLike.re_ofReal_mul]
  have h1 : RCLike.re ⟪R (W.starProjection x), x⟫_𝕜
      = RCLike.re ⟪R (W.starProjection x), W.starProjection x⟫_𝕜 := by
    have hz : ⟪R (W.starProjection x), x - W.starProjection x⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hinv _ hpx) hrest
    have hsplit : ⟪R (W.starProjection x), x⟫_𝕜
        = ⟪R (W.starProjection x), W.starProjection x⟫_𝕜
          + ⟪R (W.starProjection x), x - W.starProjection x⟫_𝕜 := by
      rw [← inner_add_right]; congr 1; abel
    rw [hsplit, hz, add_zero]
  have h2 : RCLike.re ⟪x - W.starProjection x, x⟫_𝕜
      = ‖x - W.starProjection x‖ ^ 2 := by
    have hz : ⟪x - W.starProjection x, W.starProjection x⟫_𝕜 = 0 :=
      Submodule.inner_left_of_mem_orthogonal hpx hrest
    have hsplit : ⟪x - W.starProjection x, x⟫_𝕜
        = ⟪x - W.starProjection x, x - W.starProjection x⟫_𝕜 := by
      have h' : ⟪x - W.starProjection x, x⟫_𝕜
          = ⟪x - W.starProjection x, W.starProjection x⟫_𝕜
            + ⟪x - W.starProjection x, x - W.starProjection x⟫_𝕜 := by
        rw [← inner_add_right]; congr 1; abel
      rw [h', hz, zero_add]
    rw [hsplit, inner_self_eq_norm_sq]
  rw [hre, h1, h2]

end TauCeti


variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E]

namespace ContinuousLinearMap

theorem norm_add_eq_max_of_block {P A B : E →L[𝕜] E}
    (hPsa : IsSelfAdjoint P) (hPid : IsIdempotentElem P)
    (hPnorm : ∀ x, ‖P x‖ ≤ ‖x‖) (hcompnorm : ∀ x, ‖(1 - P) x‖ ≤ ‖x‖)
    (hAP : A * P = A) (hPA : P * A = A) (hBP : B * P = 0) (hPB : P * B = 0) :
    ‖A + B‖ = max ‖A‖ ‖B‖ := by
  have hPsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hPsa
  have hPsymC : ∀ x y, ⟪P x, y⟫_𝕜 = ⟪x, P y⟫_𝕜 := fun x y => hPsym x y
  have app : ∀ (f g : E →L[𝕜] E) (x : E), (f * g) x = f (g x) := fun _ _ _ => rfl
  have hAppx : ∀ x, A (P x) = A x := fun x => by
    rw [← app]; exact congrFun (congrArg DFunLike.coe hAP) x
  have hPArange : ∀ x, P (A x) = A x := fun x => by
    rw [← app]; exact congrFun (congrArg DFunLike.coe hPA) x
  have hPBker : ∀ x, P (B x) = 0 := fun x => by
    rw [← app]; have h := congrFun (congrArg DFunLike.coe hPB) x; simpa using h
  have hBPx : ∀ x, B (P x) = 0 := fun x => by
    rw [← app]; have h := congrFun (congrArg DFunLike.coe hBP) x; simpa using h
  have hBcpx : ∀ x, B ((1 - P) x) = B x := fun x => by
    have hb : B * (1 - P) = B := by rw [mul_sub, mul_one, hBP, sub_zero]
    rw [← app]; exact congrFun (congrArg DFunLike.coe hb) x
  have hPcx : ∀ x, P ((1 - P) x) = 0 := fun x => by
    have h0 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPid, sub_self]
    rw [← app]; have h := congrFun (congrArg DFunLike.coe h0) x; simpa using h
  have hApx : ∀ x, A ((1 - P) x) = 0 := fun x => by
    have h0 : A * (1 - P) = 0 := by rw [mul_sub, mul_one, hAP, sub_self]
    rw [← app]; have h := congrFun (congrArg DFunLike.coe h0) x; simpa using h
  have hpyth : ∀ x, ‖P x‖ ^ 2 + ‖(1 - P) x‖ ^ 2 = ‖x‖ ^ 2 := fun x => by
    have horth : ⟪P x, (1 - P) x⟫_𝕜 = 0 := by rw [hPsymC x ((1 - P) x), hPcx, inner_zero_right]
    have h := norm_add_sq (𝕜 := 𝕜) (P x) ((1 - P) x)
    rw [show P x + (1 - P) x = x by
      rw [sub_apply, one_apply_eq_self]; abel] at h
    simp only [horth, map_zero, mul_zero, add_zero] at h
    linarith
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (norm_nonneg _)) fun x => ?_
    have horthAB : ⟪A x, B x⟫_𝕜 = 0 := by
      rw [← hPArange x, hPsymC (A x) (B x), hPBker, inner_zero_right]
    have hnormsq : ‖(A + B) x‖ ^ 2 = ‖A x‖ ^ 2 + ‖B x‖ ^ 2 := by
      have h := norm_add_sq (𝕜 := 𝕜) (A x) (B x)
      simp only [horthAB, map_zero, mul_zero, add_zero] at h
      simp only [add_apply]; linarith
    have hAxle : ‖A x‖ ≤ max ‖A‖ ‖B‖ * ‖P x‖ := by
      rw [← hAppx x]
      exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact le_max_left _ _)
    have hBxle : ‖B x‖ ≤ max ‖A‖ ‖B‖ * ‖(1 - P) x‖ := by
      rw [← hBcpx x]
      exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact le_max_right _ _)
    have hM : (0:ℝ) ≤ max ‖A‖ ‖B‖ := le_max_of_le_left (norm_nonneg _)
    have hkey : ‖(A + B) x‖ ^ 2 ≤ (max ‖A‖ ‖B‖ * ‖x‖) ^ 2 := by
      have e : (max ‖A‖ ‖B‖ * ‖x‖) ^ 2
          = (max ‖A‖ ‖B‖)^2 * ‖P x‖^2 + (max ‖A‖ ‖B‖)^2 * ‖(1 - P) x‖^2 := by
        rw [mul_pow, ← hpyth x]; ring
      rw [hnormsq, e]
      gcongr
      · simpa only [mul_pow] using
          (sq_le_sq₀ (norm_nonneg (A x))
            (mul_nonneg hM (norm_nonneg (P x)))).2 hAxle
      · simpa only [mul_pow] using
          (sq_le_sq₀ (norm_nonneg (B x))
            (mul_nonneg hM (norm_nonneg ((1 - P) x)))).2 hBxle
    have hnn : (0:ℝ) ≤ max ‖A‖ ‖B‖ * ‖x‖ := mul_nonneg hM (norm_nonneg x)
    calc ‖(A + B) x‖ = Real.sqrt (‖(A + B) x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((max ‖A‖ ‖B‖ * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hkey
      _ = max ‖A‖ ‖B‖ * ‖x‖ := Real.sqrt_sq hnn
  · refine max_le ?_ ?_
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      have hval : A x = (A + B) (P x) := by
        rw [add_apply, hBPx, add_zero, hAppx]
      rw [hval]; exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hPnorm x)
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      have hval : B x = (A + B) ((1 - P) x) := by
        rw [add_apply, hApx, zero_add, hBcpx]
      rw [hval]; exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hcompnorm x)

end ContinuousLinearMap

namespace Submodule

theorem norm_starProjection_sub_eq_max (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ =
      max ‖(1 - V.starProjection) ∘L U.starProjection‖
          ‖(1 - U.starProjection) ∘L V.starProjection‖ := by
  set P := U.starProjection with hPdef
  set Q := V.starProjection with hQdef
  have hPsa : IsSelfAdjoint P := isSelfAdjoint_starProjection U
  have hQsa : IsSelfAdjoint Q := isSelfAdjoint_starProjection V
  have hPid : P * P = P := U.isIdempotentElem_starProjection
  have hQid : Q * Q = Q := V.isIdempotentElem_starProjection
  have hPnorm : ∀ x, ‖P x‖ ≤ ‖x‖ := U.norm_starProjection_apply_le
  have hcompeq : (1 - P : E →L[𝕜] E) = Uᗮ.starProjection := by
    rw [hPdef]; exact (Submodule.starProjection_orthogonal' U).symm
  have hcompnorm : ∀ x, ‖(1 - P) x‖ ≤ ‖x‖ := fun x => by
    rw [hcompeq]; exact Uᗮ.norm_starProjection_apply_le x
  set X : E →L[𝕜] E := (1 - Q) * P with hXdef
  set Y : E →L[𝕜] E := (1 - P) * Q with hYdef
  set A : E →L[𝕜] E := P * (1 - Q) * P with hAdef
  set B : E →L[𝕜] E := (1 - P) * Q * (1 - P) with hBdef
  have hQ1id : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hQid]; abel
  have hstarX : star X = P * (1 - Q) := by
    rw [hXdef, star_mul, hPsa.star_eq, star_sub, star_one, hQsa.star_eq]
  have hstarY : star Y = Q * (1 - P) := by
    rw [hYdef, star_mul, hQsa.star_eq, star_sub, star_one, hPsa.star_eq]
  have hnormA : ‖A‖ = ‖X‖ ^ 2 := by
    have h : star X * X = A := by
      rw [hstarX, hXdef, hAdef,
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        show (P * (1 - Q)) * ((1 - Q) * P) = P * ((1 - Q) * (1 - Q)) * P by noncomm_ring, hQ1id]
    calc
      ‖A‖ = ‖star X * X‖ := congrArg (fun T : E →L[𝕜] E => ‖T‖) h.symm
      _ = ‖X‖ * ‖X‖ := CStarRing.norm_star_mul_self
      _ = ‖X‖ ^ 2 := by rw [pow_two]
  have hnormB : ‖B‖ = ‖Y‖ ^ 2 := by
    have hQP : Q * Q = Q := hQid
    have h : Y * star Y = B := by
      rw [hstarY, hYdef, hBdef,
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        show ((1 - P) * Q) * (Q * (1 - P)) = (1 - P) * (Q * Q) * (1 - P) by noncomm_ring, hQP]
    calc
      ‖B‖ = ‖Y * star Y‖ := congrArg (fun T : E →L[𝕜] E => ‖T‖) h.symm
      _ = ‖Y‖ * ‖Y‖ := CStarRing.norm_self_mul_star
      _ = ‖Y‖ ^ 2 := by rw [pow_two]
  have hAP : A * P = A := by rw [hAdef, mul_assoc, hPid]
  have hPA : P * A = A := by rw [hAdef, ← mul_assoc, ← mul_assoc, hPid]
  have hBP : B * P = 0 := by
    rw [hBdef, mul_assoc, show (1 - P) * P = 0 by rw [sub_mul, one_mul, hPid, sub_self], mul_zero]
  have hPB : P * B = 0 := by
    simp only [hBdef, ← mul_assoc,
      show P * (1 - P) = 0 by rw [mul_sub, mul_one, hPid, sub_self], zero_mul]
  have hA' : A = P - P * Q * P := by rw [hAdef, mul_sub, mul_one, sub_mul, hPid]
  have hB' : B = Q - Q * P - P * Q + P * Q * P := by
    simp only [hBdef, sub_mul, one_mul, mul_sub, mul_one]; abel
  have hPQsq : (P - Q) * (P - Q) = A + B := by
    have lhs : (P - Q) * (P - Q) = P + Q - P * Q - Q * P := by
      rw [sub_mul, mul_sub, mul_sub, hPid, hQid]; abel
    rw [lhs, hA', hB']; abel
  have hnormPQ : ‖(P - Q) * (P - Q)‖ = ‖P - Q‖ ^ 2 := by
    exact (hPsa.sub hQsa).norm_mul_self
  have hblock : ‖A + B‖ = max ‖A‖ ‖B‖ :=
    ContinuousLinearMap.norm_add_eq_max_of_block hPsa hPid hPnorm hcompnorm hAP hPA hBP hPB
  have hsq : ‖(P - Q : E →L[𝕜] E)‖ ^ 2 = (max ‖X‖ ‖Y‖) ^ 2 := by
    rw [← hnormPQ, hPQsq, hblock, hnormA, hnormB]
    rcases le_total ‖X‖ ‖Y‖ with h | h
    · rw [max_eq_right h, max_eq_right (by gcongr)]
    · rw [max_eq_left h, max_eq_left (by gcongr)]
  have hfin : ‖(P - Q : E →L[𝕜] E)‖ = max ‖X‖ ‖Y‖ := by
    have h2 : (0 : ℝ) ≤ max ‖X‖ ‖Y‖ := le_max_of_le_left (norm_nonneg _)
    exact (sq_eq_sq₀ (norm_nonneg (P - Q : E →L[𝕜] E)) h2).mp hsq
  rw [hfin]
  rfl

end Submodule


namespace Submodule

open TauCeti
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]


omit [CompleteSpace E] in
/-- **The quadratic form of a reduced extension splits**, for an extension
packaged from a bounded `T` and a reducing subspace.

The mathematics is `TauCeti.re_inner_reducedExtension_self`, which is stated at
the value `T (P x) + κ • (x - P x)` and assumes only invariance; this wrapper
supplies the packaging and drops `Reduces` to its invariance half. -/
private theorem re_inner_bounded_reducedExtension_self {T : E →L[𝕜] E}
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection] (hW : (∀ x ∈ W, T x ∈ W) ∧ (∀ x ∈ Wᗮ, T x ∈ Wᗮ))
    (κ : ℝ) (x : E) :
    RCLike.re ⟪(T ∘L W.starProjection
        + ((κ : ℝ) : 𝕜) • (1 - W.starProjection)) x, x⟫_𝕜
      = RCLike.re ⟪T (W.starProjection x), W.starProjection x⟫_𝕜
        + κ * ‖x - W.starProjection x‖ ^ 2 := by
  have hval : (T ∘L W.starProjection
      + ((κ : ℝ) : 𝕜) • (1 - W.starProjection)) x
      = T (W.starProjection x) + ((κ : ℝ) : 𝕜) • (x - W.starProjection x) := by
    simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply, sub_apply,
      one_apply_eq_self]
  rw [hval]
  exact TauCeti.re_inner_reducedExtension_self (R := (T : E →ₗ[𝕜] E)) hW.1 κ x
/-- **The dimension-free operator-norm Davis--Kahan `sin Θ` theorem, coercivity
form.**  For self-adjoint `A, B` on an arbitrary Hilbert space, `U` reducing `A`
with quadratic form `≥ (c+g)‖·‖²` on `U`, and `V` reducing `B` with quadratic
form `≤ c‖·‖²` on `V`,

`‖P_V P_U‖ ≤ ‖B − A‖ / g`.

This is the genuine infinite-dimensional `sin Θ` bound: the analytic core is the
integral-free Sylvester estimate
`TauCeti.ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq` (no spectral
measure, no dimension or completeness hypothesis on the *bound* itself), and the
block construction `A ∘L P + (c+g)(1−P)`, `B ∘L Q + c(1−Q)` uses only the
dimension-free projection commutation
`ContinuousLinearMap.starProjection_apply_comm_of_reduces`.  The
spectrum-predicate forms (`sinTheta_perturbation`, `IntervalExteriorSeparated`)
follow from this once a bounded spectral theorem converts spectral separation to
these coercivity bounds. -/
theorem sinTheta_directed_coercive
    {A B : E →L[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : (∀ x ∈ U, A x ∈ U) ∧ (∀ x ∈ Uᗮ, A x ∈ Uᗮ))
    (hV : (∀ x ∈ V, B x ∈ V) ∧ (∀ x ∈ Vᗮ, B x ∈ Vᗮ))
    {c g : ℝ} (hg : 0 < g)
    (hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hVc : ∀ x ∈ V, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    ‖(V.starProjection ∘L U.starProjection : E →L[𝕜] E)‖ ≤ ‖B - A‖ / g := by
  set P := U.starProjection with hP
  set Q := V.starProjection with hQ
  set A' : E →L[𝕜] E := A ∘L P + ((c + g : ℝ) : 𝕜) • (1 - P) with hA'
  set B' : E →L[𝕜] E := B ∘L Q + ((c : ℝ) : 𝕜) • (1 - Q) with hB'
  set X : E →L[𝕜] E := P ∘L Q with hX
  set Y : E →L[𝕜] E := P ∘L (A - B) ∘L Q with hY
  have hPsa : IsSelfAdjoint P := isSelfAdjoint_starProjection U
  have hQsa : IsSelfAdjoint Q := isSelfAdjoint_starProjection V
  have hAsa : IsSelfAdjoint A := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hA
  have hBsa : IsSelfAdjoint B := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  have hcgsa : IsSelfAdjoint ((c + g : ℝ) : 𝕜) := isSelfAdjoint_iff.mpr (RCLike.conj_ofReal _)
  have hcsa : IsSelfAdjoint ((c : ℝ) : 𝕜) := isSelfAdjoint_iff.mpr (RCLike.conj_ofReal _)
  have hone : IsSelfAdjoint (1 : E →L[𝕜] E) := IsSelfAdjoint.one _
  -- commutations
  have hPid : IsIdempotentElem P := by rw [hP]; exact U.isIdempotentElem_starProjection
  have hQid : IsIdempotentElem Q := by rw [hQ]; exact V.isIdempotentElem_starProjection
  have hcommA' : Commute P A := by
    apply (ContinuousLinearMap.IsIdempotentElem.commute_iff hPid).2
    constructor
    · have hmem : U ∈ Module.End.invtSubmodule (A : E →ₗ[𝕜] E) := by
        change ∀ x ∈ U, A x ∈ U
        exact hU.1
      simpa [hP, Submodule.range_starProjection] using hmem
    · have hmem : Uᗮ ∈ Module.End.invtSubmodule (A : E →ₗ[𝕜] E) := by
        change ∀ x ∈ Uᗮ, A x ∈ Uᗮ
        exact hU.2
      simpa [hP, Submodule.ker_starProjection] using hmem
  have hcommB' : Commute Q B := by
    apply (ContinuousLinearMap.IsIdempotentElem.commute_iff hQid).2
    constructor
    · have hmem : V ∈ Module.End.invtSubmodule (B : E →ₗ[𝕜] E) := by
        change ∀ x ∈ V, B x ∈ V
        exact hV.1
      simpa [hQ, Submodule.range_starProjection] using hmem
    · have hmem : Vᗮ ∈ Module.End.invtSubmodule (B : E →ₗ[𝕜] E) := by
        change ∀ x ∈ Vᗮ, B x ∈ Vᗮ
        exact hV.2
      simpa [hQ, Submodule.ker_starProjection] using hmem
  have hcommA : A ∘L P = P ∘L A := by
    change A * P = P * A
    exact hcommA'.eq.symm
  have hcommB : B ∘L Q = Q ∘L B := by
    change B * Q = Q * B
    exact hcommB'.eq.symm
  have hcommA_apply : ∀ x, A (P x) = P (A x) := by
    intro x
    have h := congrArg (fun T : E →L[𝕜] E => T x) hcommA
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hcommB_apply : ∀ x, B (Q x) = Q (B x) := by
    intro x
    have h := congrArg (fun T : E →L[𝕜] E => T x) hcommB
    simpa only [ContinuousLinearMap.comp_apply] using h
  -- self-adjointness of A', B'
  have hA'sa : IsSelfAdjoint A' := by
    have h1 : IsSelfAdjoint (A ∘L P) := (IsSelfAdjoint.commute_iff hAsa hPsa).mp hcommA
    have h2 : IsSelfAdjoint (((c + g : ℝ) : 𝕜) • ((1 : E →L[𝕜] E) - P)) := by
      rw [isSelfAdjoint_iff, star_smul, hcgsa.star_eq, (hone.sub hPsa).star_eq]
    exact hA' ▸ h1.add h2
  have hB'sa : IsSelfAdjoint B' := by
    have h1 : IsSelfAdjoint (B ∘L Q) := (IsSelfAdjoint.commute_iff hBsa hQsa).mp hcommB
    have h2 : IsSelfAdjoint (((c : ℝ) : 𝕜) • ((1 : E →L[𝕜] E) - Q)) := by
      rw [isSelfAdjoint_iff, star_smul, hcsa.star_eq, (hone.sub hQsa).star_eq]
    exact hB' ▸ h1.add h2
  have hA'sym : A'.IsSymmetric := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hA'sa
  have hB'sym : B'.IsSymmetric := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hB'sa
  -- coercivity of A'
  have hA'c : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A' x, x⟫_𝕜 := by
    intro x
    have hpx : P x ∈ U := U.starProjection_apply_mem x
    have hre : RCLike.re ⟪A' x, x⟫_𝕜
        = RCLike.re ⟪A (P x), P x⟫_𝕜 + (c + g) * ‖x - P x‖ ^ 2 := by
      rw [hA', hP]; exact re_inner_bounded_reducedExtension_self hU (c + g) x
    have hpyth : ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 := by
      rw [hP]
      simpa only [Submodule.starProjection_orthogonal_val] using
        Submodule.norm_sq_eq_add_norm_sq_starProjection x U
    rw [hre, hpyth]
    nlinarith [hUc (P x) hpx]
  -- upper bound for B'
  have hB'c : ∀ x, RCLike.re ⟪B' x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
    intro x
    have hqx : Q x ∈ V := V.starProjection_apply_mem x
    have hre : RCLike.re ⟪B' x, x⟫_𝕜
        = RCLike.re ⟪B (Q x), Q x⟫_𝕜 + c * ‖x - Q x‖ ^ 2 := by
      rw [hB', hQ]; exact re_inner_bounded_reducedExtension_self hV c x
    have hpyth : ‖x‖ ^ 2 = ‖Q x‖ ^ 2 + ‖x - Q x‖ ^ 2 := by
      rw [hQ]
      simpa only [Submodule.starProjection_orthogonal_val] using
        Submodule.norm_sq_eq_add_norm_sq_starProjection x V
    rw [hre, hpyth]
    nlinarith [hVc (Q x) hqx]
  -- Sylvester relation A' X - X B' = Y
  have hsylv : A' ∘L X - X ∘L B' = Y := by
    change A' ∘L X - X ∘L B' = Y
    ext x
    have hQxV : Q x ∈ V := V.starProjection_apply_mem x
    have hPP : P (P (Q x)) = P (Q x) :=
      U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem (Q x))
    have hQrest : Q (x - Q x) = 0 := by
      have hQQ : Q (Q x) = Q x := V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
      rw [map_sub, hQQ, sub_self]
    have hQBQ : Q (B (Q x)) = B (Q x) := V.starProjection_eq_self_iff.mpr (hV.1 _ hQxV)
    have hAP : A (P (Q x)) = P (A (Q x)) :=
      hcommA_apply (Q x)
    have hAX : (A' ∘L X) x = A (P (Q x)) := by
      simp only [ContinuousLinearMap.comp_apply, hX, hA', add_apply,
        smul_apply, sub_apply,
        one_apply_eq_self, hPP, sub_self, smul_zero, add_zero]
    have hXB : (X ∘L B') x = P (B (Q x)) := by
      simp only [ContinuousLinearMap.comp_apply, hX, hB', add_apply,
        smul_apply, sub_apply,
        one_apply_eq_self, map_add, map_smul, hQBQ, hQrest, map_zero, smul_zero, add_zero]
    have hYx : Y x = P (A (Q x)) - P (B (Q x)) := by
      simp only [hY, ContinuousLinearMap.comp_apply, sub_apply, map_sub]
    rw [sub_apply, hAX, hXB, hYx, hAP]
  -- norm bound
  have hYnorm : ‖Y‖ ≤ ‖B - A‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have hc : ‖P ((A - B) (Q x))‖ ≤ ‖(A - B) (Q x)‖ := by
      rw [hP]; exact U.norm_starProjection_apply_le _
    calc ‖Y x‖ = ‖P ((A - B) (Q x))‖ := by simp only [hY, ContinuousLinearMap.comp_apply]
      _ ≤ ‖(A - B) (Q x)‖ := hc
      _ = ‖(B - A) (Q x)‖ := by rw [show A - B = -(B - A) by abel, neg_apply, norm_neg]
      _ ≤ ‖B - A‖ * ‖Q x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖B - A‖ * ‖x‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [hQ]; exact V.norm_starProjection_apply_le x
  have hXbound : ‖X‖ ≤ ‖B - A‖ / g :=
    (TauCeti.ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq
        hA'sym hB'sym hg hA'c hB'c hsylv).trans (by gcongr)
  have hstar : star (Q ∘L P : E →L[𝕜] E) = P ∘L Q := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      hPsa.star_eq, hQsa.star_eq]
  have : ‖(Q ∘L P : E →L[𝕜] E)‖ = ‖X‖ := by rw [hX, ← hstar]; exact (norm_star _).symm
  calc ‖(V.starProjection ∘L U.starProjection : E →L[𝕜] E)‖
      = ‖(Q ∘L P : E →L[𝕜] E)‖ := by rw [hP, hQ]
    _ = ‖X‖ := this
    _ ≤ ‖B - A‖ / g := hXbound

end Submodule


namespace Submodule

open TauCeti
open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **The sharp (factor-one) operator-norm Davis--Kahan projector theorem.**  With
a two-sided coercive spectral gap — `A`'s form `≥ (c+g)` on `U` and `≤ c` on
`Uᗮ`, `B`'s form `≥ (c+g)` on `W` and `≤ c` on `Wᗮ` — the orthogonal
projectors onto these reducing subspaces on an arbitrary `RCLike` Hilbert space
satisfy the sharp bound

`‖P_U − P_W‖ ≤ ‖B − A‖ / g`

with constant one and no equal-rank hypothesis.  Combines the projector-difference
identity `Submodule.norm_starProjection_sub_eq_max` with the two dimension-free
directed `sin Θ` estimates `Submodule.sinTheta_directed_coercive`. -/
theorem opNorm_starProjection_sub_le_of_coercive
    {A B : H →L[𝕜] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 H} [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hU : (∀ x ∈ U, A x ∈ U) ∧ (∀ x ∈ Uᗮ, A x ∈ Uᗮ))
    (hW : (∀ x ∈ W, B x ∈ W) ∧ (∀ x ∈ Wᗮ, B x ∈ Wᗮ))
    {c g : ℝ} (hg : 0 < g)
    (hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUlo : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hWc : ∀ x ∈ W, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_𝕜)
    (hWlo : ∀ x ∈ Wᗮ, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    ‖(U.starProjection - W.starProjection : H →L[𝕜] H)‖ ≤ ‖B - A‖ / g := by
  rw [U.norm_starProjection_sub_eq_max W]
  refine max_le ?_ ?_
  · rw [show (1 - W.starProjection : H →L[𝕜] H) = Wᗮ.starProjection from
      (Submodule.starProjection_orthogonal' W).symm]
    exact sinTheta_directed_coercive hA hB hU
      (by
        refine ⟨hW.2, ?_⟩
        have hmem : Wᗮ ∈ Module.End.invtSubmodule (B : H →ₗ[𝕜] H) := by
          change ∀ x ∈ Wᗮ, B x ∈ Wᗮ
          exact hW.2
        exact LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule hB hmem) hg hUc hWlo
  · rw [show (1 - U.starProjection : H →L[𝕜] H) = Uᗮ.starProjection from
      (Submodule.starProjection_orthogonal' U).symm]
    have h := sinTheta_directed_coercive hB hA hW
      (by
        refine ⟨hU.2, ?_⟩
        have hmem : Uᗮ ∈ Module.End.invtSubmodule (A : H →ₗ[𝕜] H) := by
          change ∀ x ∈ Uᗮ, A x ∈ Uᗮ
          exact hU.2
        exact LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule hA hmem) hg hWc hUlo
    rwa [show ‖A - B‖ = ‖B - A‖ from by rw [← neg_sub, norm_neg]] at h

end Submodule
