/-
Original signed-complex Gamma assembly, composed from the natural finite owners.
The full-mu finite-energy generalizations live in BoundaryMuEntry; no finite
stub replaces them. This original gamma_entry proof consumes the completed
mu/rate identities and preserves every signed integer mode.
SOURCE ONLY / UNCOMPILED: no kernel, statement, axiom, Reg or CI acceptance.
-/
import D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation.BoundaryFiniteLower

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal Topology BigOperators

namespace D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation

open D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport

/-- The unchanged ORIGINAL signed complex Gamma matrix entry.
This source theorem has no bridge/equality premise. All m,n:Z are retained.
UNCOMPILED: it requires the three original-owner visibility edits and subsequent
native elaboration of this entire file, including the retained r4039 bodies. -/
theorem gamma_entry (L : ℝ) (hL : 0 < L) (m n : ℤ) :
    (∫ t : ℝ, (Zeta23.mu t:ℂ)*conj (Zeta23.paperFT (zeroMode L m) (t:ℂ))*
      Zeta23.paperFT (zeroMode L n) (t:ℂ)) =
      (((((Complex.digamma ((1/4:ℂ)+Complex.I*((omega L n/2:ℝ):ℂ))).re-
        Real.log Real.pi) * (if m=n then 1 else 0) + boundaryEntry L m n) : ℝ) : ℂ) := by
  letI : Fact (0 < L) := ⟨hL⟩
  rw [(mu_pairing_bridge L m n).2, full_rate_entry L m n]
  by_cases hmn : m=n
  · simp only [hmn, ite_true, mul_one, FormCore.LineFourier.actualIncrement]
    push_cast
    ring
  · simp [hmn]

end D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation
