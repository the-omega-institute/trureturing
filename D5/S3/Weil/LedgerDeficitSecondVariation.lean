/- GID: D5/S3/Weil/LedgerDeficitSecondVariation
   generality: I
   mirror-B: D5/B/S3/Weil/LedgerDeficitSecondVariation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define the squared norm-deficit second variation, a mirror-compatible zero address, and its Dirac measure embedding. -/

import D5.S3.Weil.CriticalLine
import D5.S3.Zeros.ZeroGeometry
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Dirac

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.LedgerDeficitSecondVariation

open D5.S3.Weil.Convention
open D5.S3.Weil.CriticalLine
open D5.S3.Weil.LabeledZeta
open D5.S3.Weil.ReflectionLedger
open D5.S3.Zeros.ZeroGeometry
open MeasureTheory Set
open scoped ENNReal

/- The curve is the squared distance of a positive norm from the unitary
   value.  The auxiliary parameter is dimensionless; the ledger displacement
   enters as its rate. -/
def normDeficitCurve (d : ℝ) : ℝ → ℝ :=
  fun u => (Real.exp ((-d) * u) - 1) ^ 2

/- The selected candidate is `((N - 1)^2)''(0)` with `N(u) = exp(-u)`,
   evaluated along the ledger displacement rate `d`. -/
def ledgerDeficitSecondVariation (d : ℝ) : ℝ :=
  iteratedDeriv 2 (normDeficitCurve d) 0

/-- The squared norm-deficit variation is exactly twice the squared ledger displacement. -/
theorem ledger_deficit_second_variation_eq (d : ℝ) :
    ledgerDeficitSecondVariation d = 2 * d ^ 2 := by
  let f : ℝ → ℝ := fun u => Real.exp ((-d) * u) - 1
  have hf : normDeficitCurve d = fun u => f u * f u := by
    funext u
    simp [normDeficitCurve, f, pow_two]
  rw [ledgerDeficitSecondVariation, hf]
  have hcont : ∀ n : ℕ, ContDiffAt ℝ n f 0 := by
    intro n
    dsimp [f]
    fun_prop
  change iteratedDeriv 2 (f * f) 0 = 2 * d ^ 2
  rw [iteratedDeriv_mul (hcont 2) (hcont 2)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_succ_self_right, Nat.choose_two_right]
  have hzero : f 0 = 0 := by
    simp [f]
  have hzero' : iteratedDeriv 0 f 0 = 0 := by
    simpa only [iteratedDeriv_zero] using hzero
  have hfirst : iteratedDeriv 1 f 0 = -d := by
    change iteratedDeriv 1 (fun u : ℝ => Real.exp ((-d) * u) - 1) 0 = -d
    rw [iteratedDeriv_fun_sub]
    · rw [iteratedDeriv_exp_const_mul]
      simp
    · exact (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffAt
    · exact contDiffAt_const
  rw [hzero', hfirst]
  ring_nf

/-- The selected second variation is nonnegative. -/
theorem ledger_deficit_second_variation_nonneg (d : ℝ) :
    0 ≤ ledgerDeficitSecondVariation d := by
  rw [ledger_deficit_second_variation_eq]
  positivity

/-- Mirroring reverses the signed ledger displacement but leaves its second variation unchanged. -/
theorem ledger_deficit_second_variation_neg (d : ℝ) :
    ledgerDeficitSecondVariation (-d) = ledgerDeficitSecondVariation d := by
  rw [ledger_deficit_second_variation_eq, ledger_deficit_second_variation_eq]
  ring

/-- The canonical zero address is its displacement from the mirror fixed locus. -/
def zeroLedgerAddress (rho : ℂ) : ℂ := rho - mirror rho

/-- The real-part length is the additive ledger length on complex addresses. -/
def realPartLedgerLength : LedgerLength ℂ :=
  { toFun := Complex.re
    map_zero' := by simp
    map_add' := by intro x y; simp }

/-- Addressing a zero by its mirror-antisymmetric coordinate gives a scalar ledger displacement. -/
def zeroAddressedScaling (rho : ℂ) : ℝ :=
  scalingLedger realPartLedgerLength rho (zeroLedgerAddress rho)

/-- The zero address changes sign under conjugate reflection. -/
theorem zero_ledger_address_mirror (rho : ℂ) :
    zeroLedgerAddress (mirror rho) = -zeroLedgerAddress rho := by
  simp [zeroLedgerAddress, mirror, reflection]

/-- The addressed scaling is twice the squared real displacement from the critical line. -/
theorem zero_addressed_scaling_eq (rho : ℂ) :
    zeroAddressedScaling rho =
      2 * (rho.re - criticalAbscissa) ^ 2 := by
  rw [zeroAddressedScaling, scalingLedger]
  simp [zeroLedgerAddress, realPartLedgerLength, mirror, reflection,
    criticalAbscissa]
  ring

/-- The zero-addressed second variation is mirror invariant. -/
theorem zero_addressed_variation_mirror (rho : ℂ) :
    ledgerDeficitSecondVariation (zeroAddressedScaling (mirror rho)) =
      ledgerDeficitSecondVariation (zeroAddressedScaling rho) := by
  rw [zero_addressed_scaling_eq, zero_addressed_scaling_eq]
  simp [mirror, reflection, criticalAbscissa]
  ring_nf

/-- Embed a nonnegative scalar at a spectral point as its weighted Dirac measure. -/
def scalarToDeficitMeasure (rho : ℂ) (w : ℝ) : Measure ℂ :=
  ENNReal.ofReal w • Measure.dirac rho

/-- The scalar-to-measure embedding preserves the mirror-paired two-point object. -/
def mirrorPairDeficitMeasure (rho : ℂ) (w : ℝ) : Measure ℂ :=
  scalarToDeficitMeasure rho w + scalarToDeficitMeasure (mirror rho) w

/-- Swapping a mirror pair leaves its embedded deficit measure unchanged. -/
theorem mirror_pair_deficit_measure_invariant (rho : ℂ) (w : ℝ) :
    mirrorPairDeficitMeasure (mirror rho) w =
      mirrorPairDeficitMeasure rho w := by
  simpa [mirrorPairDeficitMeasure, scalarToDeficitMeasure, mirror, reflection] using
    (add_comm (scalarToDeficitMeasure (mirror rho) w) (scalarToDeficitMeasure rho w))

/-- The complete zero-indexed address and measure readout. -/
def zeroDeficitMeasure (rho : ℂ) : Measure ℂ :=
  scalarToDeficitMeasure rho (ledgerDeficitSecondVariation (zeroAddressedScaling rho))

/-- A mirror pair has equal local deficit weights, while its signed scaling entries
    cancel at a common address. -/
theorem mirror_pair_zero_readout_compatibility {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (rho : ℂ) (a : A) :
    ledgerDeficitSecondVariation (scalingLedger length (mirror rho) a) =
        ledgerDeficitSecondVariation (scalingLedger length rho a) ∧
      scalingLedger length rho a + scalingLedger length (mirror rho) a = 0 := by
  constructor
  · rw [(mirror_reversal_spec length rho).1 a]
    exact ledger_deficit_second_variation_neg _
  · exact (mirror_pair_distinct_iff_off_line_and_cancels length rho).2 a

#print axioms ledger_deficit_second_variation_eq
#print axioms ledger_deficit_second_variation_neg
#print axioms zero_ledger_address_mirror
#print axioms zero_addressed_variation_mirror
#print axioms mirror_pair_deficit_measure_invariant
#print axioms mirror_pair_zero_readout_compatibility

end D5.S3.Weil.LedgerDeficitSecondVariation
