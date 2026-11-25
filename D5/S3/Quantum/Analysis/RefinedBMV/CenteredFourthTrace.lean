/- GID: D5/S3/Quantum/Analysis/RefinedBMV/CenteredFourthTrace
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/CenteredFourthTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fourth trace comparison for a symmetrized power of a PSD factor. -/

import D5.S3.Quantum.Analysis.RefinedBMV44

/-! # Fourth trace comparison for centered products -/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RefinedBMV

open private trace_cycle_power from D5.S3.Quantum.Analysis.RefinedBMVTracePower

noncomputable section

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- The symmetrized power comparison for four factors, including singular
first factors. The Jordan product lives inside the real trace. -/
theorem fourth_trace_le_centered_power (A B : Mat) (hA : A.PosSemidef) (hB : B.IsHermitian)
    (r s : ℕ) :
    (trace ((A ^ (r + s) * B) ^ 4)).re ≤
      (trace ((A ^ r * ((1 / 2 : ℝ) • (A ^ s * B + B * A ^ s))) ^ 4)).re := by
  let X := CFC.sqrt A
  let Z := X ^ r
  let P := A ^ s
  let C := Z * B * Z
  let J := (1 / 2 : ℝ) • (P * B + B * P)
  have hX : X.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hsquare : X ^ 2 = A := by
    rw [pow_two]
    exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hZsquare : Z * Z = A ^ r := by
    dsimp only [Z]
    rw [← pow_two, ← pow_mul, Nat.mul_comm r 2, pow_mul, hsquare]
  have hZ : Z.IsHermitian := (hX.pow r).isHermitian
  have hP : P.PosSemidef := hA.pow s
  have hC : C.IsHermitian := by
    change Cᴴ = C
    simp only [C, conjTranspose_mul, hZ.eq, hB.eq, mul_assoc]
  have hComm : P * Z = Z * P := by
    dsimp only [P, Z]
    rw [← hsquare, ← pow_mul X 2 s, ← pow_add X (2 * s) r, ← pow_add X r (2 * s),
      Nat.add_comm (2 * s) r]
  have hProduct : trace ((A ^ (r + s) * B) ^ 4) = trace ((C * P) ^ 4) := by
    calc
      _ = trace (((P * Z) * (Z * B)) ^ 4) := by
        apply congrArg (fun M : Mat => trace (M ^ 4))
        rw [Nat.add_comm r s, pow_add, ← hZsquare]
        simp only [P, mul_assoc]
      _ = trace (((Z * B) * (P * Z)) ^ 4) := trace_cycle_power _ _ _
      _ = _ := by
        rw [hComm]
        dsimp only [C]
        simp only [mul_assoc]
  have hCentered : (1 / 2 : ℝ) • (C * P + (C * P)ᴴ) = Z * J * Z := by
    rw [conjTranspose_mul, hP.isHermitian.eq, hC.eq]
    simp only [J, Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul]
    have h₁ : C * P = Z * (B * P) * Z := by
      calc
        _ = Z * B * (Z * P) := by simp only [C, mul_assoc]
        _ = _ := by rw [← hComm]; simp only [mul_assoc]
    have h₂ : P * C = Z * (P * B) * Z := by
      calc
        _ = P * Z * B * Z := by simp only [C, mul_assoc]
        _ = _ := by rw [hComm]; simp only [mul_assoc]
    rw [h₁, h₂, add_comm (Z * (B * P) * Z)]
  have hTrace : trace (((1 / 2 : ℝ) • (C * P + (C * P)ᴴ)) ^ 4) =
      trace ((A ^ r * J) ^ 4) := by
    rw [hCentered, trace_cycle_power (Z * J) Z 4, ← mul_assoc, hZsquare]
  have h := trace_four_le_hermitian_part C P hC hP
  rw [← hProduct, hTrace] at h
  exact h

end
end RefinedBMV
