/- GID: D5/S3/VertexAlgebra/Analysis/OriginalInfiniteSmearing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Analysis/OriginalInfiniteSmearing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute operator-norm sums of the literal charged circle modes. -/

import D5.S3.VertexAlgebra.Analysis.OriginalModeExtension
import D5.S3.VertexAlgebra.Analysis.SmoothCircleFourier

/-! Smooth smearing in the sense of Carpi--Tomassini, arXiv:2303.14097v2.
The sum is in the actual Banach space of Sobolev operators, over all integers.
Finite energy support is not an output assertion. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology
namespace D5.S3.VertexAlgebra.Analysis.OriginalSmearing
open LatticeGeneratingFieldLocality
open SmoothCircleFourier
open private modeExtension_compatible from
  D5.S3.VertexAlgebra.Analysis.OriginalModeExtension
open private W_le from
  D5.S3.VertexAlgebra.Analysis.SmoothCircleFourier

open Model

variable (M : Model)

def Model.operatorTerm (a : Charge M.D) (f : Test) (k : ℕ) (m : ℤ) :
    M.Sobolev (M.order a+k) →L[ℂ] M.Sobolev k :=
  f.coefficient m • M.modeExtension a k m

private theorem operatorTerm_le (a : Charge M.D) (f : Test) (k : ℕ) (m : ℤ) :
    ‖M.operatorTerm a f k m‖ ≤ M.modeConstant a * f.weight (M.order a+k) m := by
  rw [operatorTerm, norm_smul]
  exact (mul_le_mul_of_nonneg_left (modeExtension_norm M a k m) (norm_nonneg _)).trans_eq
    (by dsimp [Test.weight]; ring)

private theorem operator_absolute (a : Charge M.D) (f : Test) (k : ℕ) :
    Summable (fun m : ℤ => ‖M.operatorTerm a f k m‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (operatorTerm_le M a f k)
    ((weighted_summable f (M.order a+k)).mul_left (M.modeConstant a))

private theorem operator_summable (a : Charge M.D) (f : Test) (k : ℕ) :
    Summable (M.operatorTerm a f k) :=
  (operator_absolute M a f k).of_norm_bounded (fun _ => le_rfl)

/-- A genuinely infinite sum in B(H_(2d+k), H_k). -/
def Model.smear (a : Charge M.D) (f : Test) (k : ℕ) :
    M.Sobolev (M.order a+k) →L[ℂ] M.Sobolev k := ∑' m : ℤ, M.operatorTerm a f k m

private theorem smear_norm (a : Charge M.D) (f : Test) (k : ℕ) :
    ‖M.smear a f k‖ ≤ M.modeConstant a * f.W (M.order a+k) := by
  calc
    _ ≤ ∑' m : ℤ, M.modeConstant a * f.weight (M.order a+k) m :=
      tsum_of_norm_bounded
        (((weighted_summable f (M.order a+k)).mul_left (M.modeConstant a)).hasSum)
        (operatorTerm_le M a f k)
    _ = _ := by rw [tsum_mul_left]; rfl

private theorem smear_vector_bound (a : Charge M.D) (f : Test) (k : ℕ)
    (x : M.Sobolev (M.order a+k)) :
    ‖M.smear a f k x‖ ≤ M.modeConstant a * f.W (M.order a+k) * ‖x‖ :=
  (M.smear a f k).le_opNorm x |>.trans
    (mul_le_mul_of_nonneg_right (smear_norm M a f k) (norm_nonneg _))

private theorem vector_summable (a : Charge M.D) (f : Test) (k : ℕ)
    (x : M.Sobolev (M.order a+k)) :
    Summable (fun m : ℤ => f.coefficient m • M.modeExtension a k m x) := by
  apply ((operator_absolute M a f k).mul_right ‖x‖).of_norm_bounded
  intro m
  change ‖M.operatorTerm a f k m x‖ ≤ ‖M.operatorTerm a f k m‖ * ‖x‖
  exact (M.operatorTerm a f k m).le_opNorm x

private theorem smear_apply (a : Charge M.D) (f : Test) (k : ℕ)
    (x : M.Sobolev (M.order a+k)) :
    M.smear a f k x = ∑' m : ℤ, f.coefficient m • M.modeExtension a k m x := by
  exact (ContinuousLinearMap.apply ℂ (M.Sobolev k) x).map_tsum
    (operator_summable M a f k)

private theorem smear_compatible (a : Charge M.D) (f : Test) (j k : ℕ) (hjk : j ≤ k)
    (x : M.Sobolev (M.order a+k)) :
    M.inclusion j k hjk (M.smear a f k x) =
      M.smear a f j
        (M.inclusion (M.order a+j) (M.order a+k) (Nat.add_le_add_left hjk _) x) := by
  rw [smear_apply, (M.inclusion j k hjk).map_tsum (vector_summable M a f k x),
    smear_apply]
  apply tsum_congr
  intro m
  rw [map_smul]
  have hh := congrArg (fun A => A x) (modeExtension_compatible M a j k hjk m)
  exact congrArg (fun y : M.Sobolev j => f.coefficient m • y) hh

/-- The smooth-test constant is finite as a consequence of smoothness. -/
private theorem smear_paper_bound (a : Charge M.D) (f : Test) (k : ℕ) :
    ‖M.smear a f k‖ ≤ M.modeConstant a *
      (f.jetNorm 0 + (2^(M.order a+k) * f.jetNorm (M.order a+k+2)) *
        (∑' m : ℤ, 1 / (m : ℝ)^2)) :=
  (smear_norm M a f k).trans
    (mul_le_mul_of_nonneg_left (W_le f _) (modeConstant_pos M a).le)

end D5.S3.VertexAlgebra.Analysis.OriginalSmearing
