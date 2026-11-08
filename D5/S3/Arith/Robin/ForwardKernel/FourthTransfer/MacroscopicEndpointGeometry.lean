/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/MacroscopicEndpointGeometry
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthTransfer/MacroscopicEndpointGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Macroscopic endpoint derivatives and cell gaps give shared freezing geometry. -/

import D5.S3.Arith.Robin.ForwardKernel.MacroscopicVarianceDefs
import Mathlib.Analysis.Calculus.MeanValue

namespace D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.MacroscopicEndpointGeometry

open Set
open MacroscopicVarianceDefs MovingLengthCells

noncomputable section

/-- Frozen and moving endpoints have positive derivatives and a common image interval. -/
theorem macro_endpoint_geometry
    {a : ℝ → ℝ} {θ M L X l r c : ℝ}
    (ha : MacroscopicLengthBounds a M L) (hM : 0 ≤ M) (hX : 0 < X)
    (hl : X ≤ l) (hlr : l ≤ r) (hr : r ≤ 2 * X) (hc : c ∈ Icc (0 : ℝ) M)
    (hMX : M * X ^ θ ≤ X) (hLX : L * X ^ θ / X ≤ 1 / 2) :
    let p := fun x : ℝ => x + X ^ θ * c
    let q := fun x : ℝ => x + X ^ θ * a (x / X)
    ∃ q' : ℝ → ℝ,
      ContinuousOn p (Icc l r) ∧ ContinuousOn q (Icc l r) ∧
      (∀ x ∈ Icc l r, HasDerivWithinAt p 1 (Icc l r) x) ∧
      (∀ x ∈ Icc l r, HasDerivWithinAt q (q' x) (Icc l r) x) ∧
      (∀ x ∈ Icc l r, (1 / 2 : ℝ) ≤ q' x) ∧
      (∀ x ∈ Icc l r,
        p x ∈ Icc l (r + M * X ^ θ) ∧ q x ∈ Icc l (r + M * X ^ θ)) := by
  have hH : 0 < X ^ θ := Real.rpow_pos_of_pos hX _
  have hxmem (x : ℝ) (hx : x ∈ Icc l r) : x / X ∈ Icc (1 : ℝ) 2 :=
    ⟨(le_div_iff₀ hX).2 (by linarith [hx.1]),
      (div_le_iff₀ hX).2 (by linarith [hx.2])⟩
  have had : DifferentiableOn ℝ a (Icc (1 : ℝ) 2) :=
    ha.1.differentiableOn (by norm_num)
  have hcomp (x : ℝ) (hx : x ∈ Icc l r) :
      HasDerivWithinAt (fun x => a (x / X))
        (derivWithin a (Icc (1 : ℝ) 2) (x / X) / X) (Icc l r) x := by
    convert ((had (x / X) (hxmem x hx)).hasDerivWithinAt).comp x
      ((hasDerivAt_id x).div_const X).hasDerivWithinAt
      (fun y hy => hxmem y hy) using 1 <;> simp [div_eq_mul_inv, Function.comp_def]
  have hdq (x : ℝ) (hx : x ∈ Icc l r) :
      HasDerivWithinAt (fun x => x + X ^ θ * a (x / X))
        (1 + X ^ θ * (derivWithin a (Icc (1 : ℝ) 2) (x / X) / X)) (Icc l r) x :=
    (hasDerivWithinAt_id x _).add ((hcomp x hx).const_mul _)
  have hdp (x : ℝ) (_hx : x ∈ Icc l r) :
      HasDerivWithinAt (fun x => x + X ^ θ * c) 1 (Icc l r) x :=
    ((hasDerivAt_id x).add_const _).hasDerivWithinAt
  refine ⟨fun x => 1 + X ^ θ * (derivWithin a (Icc (1 : ℝ) 2) (x / X) / X),
    (fun x hx => (hdp x hx).continuousWithinAt),
    (fun x hx => (hdq x hx).continuousWithinAt), hdp, hdq, ?_, ?_⟩
  · intro x hx
    have hd := (abs_le.1 (ha.2.2 (x / X) (hxmem x hx))).1
    have hh := mul_le_mul_of_nonneg_left hd hH.le
    have hh' := div_le_div_of_nonneg_right hh hX.le
    ring_nf at hh' hLX ⊢
    linarith
  · intro x hx
    have hav := ha.2.1 (x / X) (hxmem x hx)
    constructor <;> constructor <;> nlinarith [hx.1, hx.2, hc.1, hc.2, hav.1, hav.2]

/-- A moving length differs from its cell's frozen length by at most the cell width times L. -/
theorem macro_cell_gap_le
    {a : ℝ → ℝ} {θ M L X : ℝ} {n j : ℕ}
    (ha : MacroscopicLengthBounds a M L) (hL : 0 ≤ L) (hX : 0 < X)
    (hn : 0 < n) (hj : j < n) :
    ∀ x ∈ Icc (cellPoint n j * X) (cellPoint n (j + 1) * X),
      |X ^ θ * (a (x / X) - a (cellPoint n j))| ≤ X ^ θ * L / (n : ℝ) := by
  have hH : 0 < X ^ θ := Real.rpow_pos_of_pos hX _
  have hu := cellPoint_mem hn hj.le
  have hv := cellPoint_mem hn (Nat.succ_le_of_lt hj)
  have hstep := cellPoint_step hn j
  intro x hx
  have hxm : x / X ∈ Icc (cellPoint n j) (cellPoint n (j + 1)) :=
    ⟨(le_div_iff₀ hX).2 (by simpa using hx.1), (div_le_iff₀ hX).2 hx.2⟩
  have hab := (convex_Icc (1 : ℝ) 2).norm_image_sub_le_of_norm_derivWithin_le
    (ha.1.differentiableOn (by norm_num)) (fun u hu => by
      simpa only [Real.norm_eq_abs] using ha.2.2 u hu) hu
    (show x / X ∈ Icc (1 : ℝ) 2 from ⟨hu.1.trans hxm.1, hxm.2.trans hv.2⟩)
  simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hxm.1)] at hab
  have hd : x / X - cellPoint n j ≤ 1 / n := by linarith [hxm.2]
  have hh := mul_le_mul_of_nonneg_left
    (hab.trans (mul_le_mul_of_nonneg_left hd hL)) hH.le
  rw [abs_mul, abs_of_pos hH]
  calc
    _ ≤ X ^ θ * (L * (1 / n)) := hh
    _ = X ^ θ * L / (n : ℝ) := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.MacroscopicEndpointGeometry
