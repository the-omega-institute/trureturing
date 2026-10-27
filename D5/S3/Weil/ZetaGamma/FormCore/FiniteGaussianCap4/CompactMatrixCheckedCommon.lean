/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactMatrixCheckedCommon
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Shared actual analytic input and literal moment transport. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCore
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMomentBox64
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4FiniteCertificate
import D5.S0.Certificates.BoxCover.RationalIntervalExpression
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic


/- Shared transport only. Public declarations are consumed by the checked
entry fragments; all original numerical checking remains in those fragments. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

noncomputable section
namespace FiniteGaussianCap475
open Polynomial
open FiniteGaussianCap4.LaguerreSevenHalf.RationalModel
open D5.S0.Certificates.BoxCover.RationalIntervalExpression

def inputBox : Fin 62 → ℚ × ℚ :=
  Fin.cases (normalizationLower64, normalizationUpper64)
    (fun m => (WLower64 m, WUpper64 m))

def actualInput : Fin 62 → ℝ :=
  Fin.cases normalizationSquared (fun m => W m.val)

theorem actualInput_mem (k : Fin 62) :
    ((inputBox k).1 : ℝ) ≤ actualInput k ∧
      actualInput k ≤ ((inputBox k).2 : ℝ) := by
  refine Fin.cases ?_ ?_ k
  · exact normalizationSquared_bounds64
  · intro m
    exact W_bounds64 m

private theorem debitMoment_eq_W (m : ℕ) : debitMoment m = W m := by
  rw [(debitMoment_formula m).2]
  unfold W
  ring

/- Shared actual integral transport for every literal coefficient list. -/
theorem polynomialMoment_foldl (terms : List (ℕ × ℚ)) (p : ℚ[X]) :
    compactPolynomialMoment
      (terms.foldl (fun acc t => acc + monomial t.1 t.2) p) =
    terms.foldl (fun acc t => acc + (t.2 : ℝ) * W t.1)
      (compactPolynomialMoment p) := by
  induction terms generalizing p with
  | nil => rfl
  | cons t ts ih =>
    simpa only [List.foldl_cons, compactPolynomialMoment_add,
      compactPolynomialMoment_monomial, debitMoment_eq_W] using
      ih (p + monomial t.1 t.2)

end FiniteGaussianCap475
