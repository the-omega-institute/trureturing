/- GID: D5/S3/Geometry/MultiplicativeHornichHlawka
   generality: G
   mirror-B: D5/B/S3/Geometry/MultiplicativeHornichHlawka
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The multiplicative Hornich–Hlawka inequality holds in real and complex inner product spaces. -/

/- Source: Marinescu–Niculescu, arXiv:2407.03278, §6.
   admission_basis: open-problem-resolution (#15640; Proved)
   Direct frozen dependencies: none (pinned Mathlib only).
   escape_witness: none
   Reuse: EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist,
     InnerProductSpace.rclikeToReal, norm_add_sq_real, norm_sub_le, norm_add_le,
     le_of_sq_le_sq.
   Per-declaration proof_shape and live consumers:
     claim: proof_shape definition; consumer=result
     scalar_inequality: bind-only; consumer=result
     ptolemy_sum: bind-only; consumer=result
     frechet_identity: bind-only; consumer=result
     norm_triangle_four: bind-only; consumer=result
     result: bind-only; designated external open-problem resolution
   Ptolemy bounds the quadratic terms; the four triangle inequalities control
   the cubic terms through the Fréchet identity and a polynomial factorization. -/

import Mathlib.Geometry.Euclidean.Inversion.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace D5.S3.Geometry.MultiplicativeHornichHlawka

def claim : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (E : Type) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y z : E),
    (1 + ‖x + y‖) * (1 + ‖y + z‖) * (1 + ‖z + x‖) ≤
      (1 + ‖x‖) * (1 + ‖y‖) * (1 + ‖z‖) * (1 + ‖x + y + z‖)

private lemma scalar_inequality (a b c d u v w : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (huv : u * v ≤ a * c + b * d)
    (hvw : v * w ≤ a * b + c * d)
    (hwu : w * u ≤ b * c + a * d)
    (hf : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = u ^ 2 + v ^ 2 + w ^ 2)
    (hta : a ≤ b + c + d) (htb : b ≤ a + c + d)
    (htc : c ≤ a + b + d) (htd : d ≤ a + b + c) :
    (1 + u) * (1 + v) * (1 + w) ≤
      (1 + a) * (1 + b) * (1 + c) * (1 + d) := by
  have hpair : u * v + v * w + w * u ≤
      a * b + a * c + a * d + b * c + b * d + c * d := by
    linarith only [huv, hvw, hwu]
  have hsum_sq : (u + v + w) ^ 2 ≤ (a + b + c + d) ^ 2 := by
    nlinarith only [hf, hpair]
  have hsum : u + v + w ≤ a + b + c + d :=
    le_of_sq_le_sq hsum_sq (by positivity)
  have hdefect : 0 ≤ (a + b + c + d) ^ 2 -
      2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    have hA := mul_nonneg ha (sub_nonneg.mpr hta)
    have hB := mul_nonneg hb (sub_nonneg.mpr htb)
    have hC := mul_nonneg hc (sub_nonneg.mpr htc)
    have hD := mul_nonneg hd (sub_nonneg.mpr htd)
    nlinarith only [hA, hB, hC, hD]
  have hprod : (u * v * w) ^ 2 ≤
      (a * c + b * d) * (a * b + c * d) * (b * c + a * d) := by
    calc
      (u * v * w) ^ 2 = (u * v) * (v * w) * (w * u) := by ring
      _ ≤ (a * c + b * d) * (a * b + c * d) * (b * c + a * d) :=
        mul_le_mul (mul_le_mul huv hvw (by positivity) (by positivity)) hwu
          (by positivity) (by positivity)
  have hfactor :
      (a * b * c + a * b * d + a * c * d + b * c * d) ^ 2 -
        (a * c + b * d) * (a * b + c * d) * (b * c + a * d) =
      a * b * c * d * ((a + b + c + d) ^ 2 -
        2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) := by ring
  have hprod_bound :
      (a * c + b * d) * (a * b + c * d) * (b * c + a * d) ≤
        (a * b * c + a * b * d + a * c * d + b * c * d) ^ 2 := by
    exact sub_nonneg.mp (hfactor ▸ mul_nonneg (by positivity) hdefect)
  have hcubic : u * v * w ≤ a * b * c + a * b * d + a * c * d + b * c * d :=
    le_of_sq_le_sq (hprod.trans hprod_bound) (by positivity)
  have habcd : 0 ≤ a * b * c * d := by positivity
  nlinarith only [hsum, hpair, hcubic, habcd]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma ptolemy_sum (x y z : E) :
    ‖x + y‖ * ‖y + z‖ ≤ ‖x‖ * ‖z‖ + ‖y‖ * ‖x + y + z‖ := by
  have h := EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist
    (V := E) (0 : E) x (x + y) (x + y + z)
  simpa only [dist_eq_norm, zero_sub, norm_neg,
    show x - (x + y + z) = -(y + z) by abel,
    show x + y - (x + y + z) = -z by abel,
    show x - (x + y) = -y by abel] using h

private lemma frechet_identity (x y z : E) :
    ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 + ‖x + y + z‖ ^ 2 =
      ‖x + y‖ ^ 2 + ‖y + z‖ ^ 2 + ‖z + x‖ ^ 2 := by
  simp only [norm_add_sq_real, inner_add_left, real_inner_comm]
  ring

omit [InnerProductSpace ℝ E] in
private lemma norm_triangle_four (x y z : E) :
    ‖x‖ ≤ ‖y‖ + ‖z‖ + ‖x + y + z‖ := by
  calc
    ‖x‖ = ‖(x + y + z) - y - z‖ := by congr 1; abel
    _ ≤ ‖x + y + z‖ + ‖y‖ + ‖z‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = ‖y‖ + ‖z‖ + ‖x + y + z‖ := by ring

theorem result : claim := by
  intro 𝕜 _ E _ _ x y z
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
  apply scalar_inequality ‖x‖ ‖y‖ ‖z‖ ‖x + y + z‖
    ‖x + y‖ ‖y + z‖ ‖z + x‖
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  · exact ptolemy_sum x y z
  · simpa only [add_comm, add_left_comm, add_assoc, mul_comm] using ptolemy_sum y z x
  · simpa only [add_comm, add_left_comm, add_assoc, mul_comm] using ptolemy_sum z x y
  · exact frechet_identity x y z
  · exact norm_triangle_four x y z
  · simpa only [add_comm, add_left_comm, add_assoc] using norm_triangle_four y x z
  · simpa only [add_comm, add_left_comm, add_assoc] using norm_triangle_four z x y
  · exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

end D5.S3.Geometry.MultiplicativeHornichHlawka
