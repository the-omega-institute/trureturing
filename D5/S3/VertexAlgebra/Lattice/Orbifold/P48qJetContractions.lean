/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qJetContractions
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regular current-charge and current-current jet contraction kernels. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qJetNormalOrdering
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
Regular current–charge and current–current kernels for the P48q order-three twist.
Write the physical insertion coordinates as `w(1+s)` and `w(1+t)`. The
nonnegative strip in Bakalov–Kac (arXiv:math/0402315v3), (4.23)–(4.24), has
indices `r+n`. Summing the geometric kernel and removing the source pole
gives `((1+s)^(-r)-1)/s` for a charge at `w`. For a second current the
factor `r+n` in the bracket is the derivative in the second coordinate,
so the regular kernel is the `t` derivative of the corresponding divided
difference. These are the regular terms for the source products in (3.13).
The level-`d` and level-`e` jets take the Hasse coefficients in degrees
`d-1` and `e-1`. Restoring the scale gives `w⁻ᵈ` and `w⁻⁽ᵈ⁺ᵉ⁾`, respectively.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qJetContractions

open LatticeGeneratingFieldLocality (Charge)
open LatticeAllStateReconstruction (mu)
open ThirdTwistedIterate (currentAlong)
open ThirdEigenspacePairing (p48qAction p48qForm)
open P48qTwistedChargeAction (lattice)
open P48qThirdTwistedField (Cartan State chargeVector concreteChargedField)
open P48qJetNormalOrdering (normalOrderedCoeff)
open P48qCurrentChargedIterate (chargedGround normalOrderedCurrentCoeff stateField)
open scoped BigOperators VertexOperator

open private correction_on_residue choose_two from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

/-- The normalized scalar kernel with the simple pole removed. -/
def scalarKernel (r : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun i => Ring.choose (-r) (i + 1)

theorem scalarKernel_mul_X (r : ℂ) :
    scalarKernel r * PowerSeries.X = PowerSeries.binomialSeries ℂ (-r) - 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [show (PowerSeries.X : PowerSeries ℂ) = PowerSeries.X ^ 1 by rw [pow_one],
      PowerSeries.coeff_mul_X_pow]
    simp [scalarKernel, PowerSeries.binomialSeries_coeff, PowerSeries.coeff_one]

/-- The level-`d` Taylor coefficient with its actual charge pairing. -/
theorem scalarKernel_charge_coeff (r g : ℂ) (d : ℕ) (hd : 0 < d) :
    PowerSeries.coeff (d - 1) (scalarKernel r * PowerSeries.C g) =
      Ring.choose (-r) d * g := by
  rw [PowerSeries.coeff_mul_C, scalarKernel, PowerSeries.coeff_mk, Nat.sub_add_cancel hd]

/-- The coefficient of `s^i t^j` in the divided difference
`((1+s)^(-r) * (1+t)^r - 1)/(s-t)`. -/
def dividedKernelCoeff (r : ℂ) (i j : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (j + 1), Ring.choose (-r) (i + 1 + k) * Ring.choose r (j - k)

/-- On the horizontal axis, multiplication by `s-t` shifts the first index. -/
theorem dividedKernelCoeff_right_zero (r : ℂ) (i : ℕ) :
    dividedKernelCoeff r i 0 = Ring.choose (-r) (i + 1) := by
  simp [dividedKernelCoeff]

/-- On the vertical axis the negative shift gives the other binomial series.
The boundary condition uses the inverse-binomial convolution at positive degree. -/
theorem dividedKernelCoeff_left_zero (r : ℂ) (j : ℕ) :
    -dividedKernelCoeff r 0 j = Ring.choose r (j + 1) := by
  have h := Ring.add_choose_eq (j + 1) (Commute.all (-r) r)
  rw [neg_add_cancel, Ring.choose_zero_pos ℂ (Nat.succ_pos j),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ'] at h
  simp only [Nat.sub_zero, Ring.choose_zero_right, one_mul] at h
  have hsum : (∑ k ∈ Finset.range (j + 1),
      Ring.choose (-r) (k + 1) * Ring.choose r (j + 1 - (k + 1))) =
      dividedKernelCoeff r 0 j := by
    simp [dividedKernelCoeff, Nat.succ_sub_succ_eq_sub, Nat.add_comm]
  rw [hsum] at h
  linear_combination h

/-- In every positive bidegree this is the coefficient of `(s-t)Q`.
Together with the axes and the zero constant term, it verifies the full
numerator coefficientwise. The horizontal axis and this recurrence
determine every row by induction on the second index. -/
theorem dividedKernelCoeff_sub (r : ℂ) (i j : ℕ) :
    dividedKernelCoeff r i (j + 1) - dividedKernelCoeff r (i + 1) j =
      Ring.choose (-r) (i + 1) * Ring.choose r (j + 1) := by
  unfold dividedKernelCoeff
  rw [Finset.sum_range_succ']
  simp only [Nat.add_zero, Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
  have hsum : (∑ k ∈ Finset.range (j + 1),
      Ring.choose (-r) (i + 1 + (k + 1)) * Ring.choose r (j - k)) =
      ∑ k ∈ Finset.range (j + 1),
        Ring.choose (-r) (i + 1 + 1 + k) * Ring.choose r (j - k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show i + 1 + (k + 1) = i + 1 + 1 + k by omega]
  rw [hsum, add_sub_cancel_left]

private theorem choose_succ_mul (a : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * Ring.choose a (n + 1) = (a - n) * Ring.choose a n := by
  simpa only [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.cast_succ,
    Nat.add_sub_cancel_left, Ring.choose_one_right, mul_comm] using
    (Ring.choose_smul_choose a (n := n + 1) (k := n) (Nat.le_succ n))

private theorem choose_succ_mul_lower (a : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * Ring.choose a (n + 1) = a * Ring.choose (a - 1) n := by
  simpa only [Nat.choose_one_right, nsmul_eq_mul, Nat.cast_succ, Nat.cast_one, Nat.cast_zero,
    zero_add,
    Nat.add_sub_cancel, Ring.choose_one_right] using
    (Ring.choose_smul_choose a (n := n + 1) (k := 1) (Nat.succ_le_succ (Nat.zero_le n)))

private theorem telescope_step (r : ℂ) (n m : ℕ) :
    (n : ℂ) * Ring.choose (-r) n * Ring.choose (r - 1) (m + 1) -
      ((n : ℂ) + 1) * Ring.choose (-r) (n + 1) * Ring.choose (r - 1) m =
    ((n : ℂ) + m + 1) * (Ring.choose (-r) n * Ring.choose r (m + 1)) := by
  have hPascal : Ring.choose r (m + 1) =
      Ring.choose (r - 1) m + Ring.choose (r - 1) (m + 1) := by
    simpa only [sub_add_cancel] using Ring.choose_succ_succ (r - 1) m
  rw [choose_succ_mul]
  calc
    _ = Ring.choose (-r) n *
        ((n : ℂ) * (Ring.choose (r - 1) m + Ring.choose (r - 1) (m + 1)) +
          r * Ring.choose (r - 1) m) := by ring
    _ = _ := by rw [← hPascal, ← choose_succ_mul_lower]; ring

/-- The finite binomial sum telescopes to its initial weighted term.
The summand at `k=e` equals the final term of the telescope after division
by `d+e`. -/
theorem pairConvolution_closed (r : ℂ) (d e : ℕ) (hd : 0 < d) :
    (∑ k ∈ Finset.range (e + 1), Ring.choose (-r) (d + k) * Ring.choose r (e - k)) =
      (d : ℂ) / ((d : ℂ) + e) * Ring.choose (-r) d * Ring.choose (r - 1) e := by
  let G (k : ℕ) := ((d : ℂ) + k) * Ring.choose (-r) (d + k) * Ring.choose (r - 1) (e - k)
  have hstep (k : ℕ) (hk : k ∈ Finset.range e) :
      ((d : ℂ) + e) * (Ring.choose (-r) (d + k) * Ring.choose r (e - k)) =
        G k - G (k + 1) := by
    have h := Finset.mem_range.mp hk
    have he : e - k = (e - (k + 1)) + 1 := by omega
    have htotal : d + k + (e - (k + 1)) + 1 = d + e := by omega
    have hcast := congrArg (fun u : ℕ => (u : ℂ)) htotal
    push_cast at hcast
    have hG := telescope_step r (d + k) (e - (k + 1))
    push_cast at hG
    rw [hcast, ← he] at hG
    simpa only [G, Nat.cast_succ, Nat.add_assoc, add_assoc] using hG.symm
  have hsum :
      ((d : ℂ) + e) *
        (∑ k ∈ Finset.range (e + 1), Ring.choose (-r) (d + k) * Ring.choose r (e - k)) =
      G 0 := by
    rw [Finset.sum_range_succ, mul_add, Finset.mul_sum, Finset.sum_congr rfl hstep,
      Finset.sum_range_sub']
    simp only [G, Nat.sub_self, Ring.choose_zero_right, mul_one, sub_add_cancel]
  have hden : (d : ℂ) + e ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < d + e by omega))
  calc
    _ = G 0 / ((d : ℂ) + e) := (eq_div_iff hden).2 (by simpa only [mul_comm] using hsum)
    _ = _ := by simp only [G, Nat.cast_zero, add_zero, Nat.sub_zero, div_eq_mul_inv]; ring

/-- The `s^(d-1)t^(e-1)` coefficient of the formal `t` derivative of `Q`
at positive source levels. -/
def pairJetCoeff (r : ℂ) (d e : ℕ) : ℂ :=
  (e : ℂ) * dividedKernelCoeff r (d - 1) e

theorem pairJetCoeff_closed (r : ℂ) (d e : ℕ) (hd : 0 < d) :
    pairJetCoeff r d e =
      ((d : ℂ) * e) / ((d : ℂ) + e) * Ring.choose (-r) d * Ring.choose (r - 1) e := by
  rw [pairJetCoeff, dividedKernelCoeff, Nat.sub_add_cancel hd, pairConvolution_closed r d e hd]
  simp only [div_eq_mul_inv]
  ring

/-- The closed form with the Gram pairing, computed by formal differentiation
in the second variable in the row of first degree `d - 1`. -/
theorem pairKernel_derivative_coeff (r g : ℂ) (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    PowerSeries.coeff (e - 1)
        (PowerSeries.derivative (PowerSeries.mk (dividedKernelCoeff r (d - 1))) *
          PowerSeries.C g) =
      ((d : ℂ) * e) / ((d : ℂ) + e) * Ring.choose (-r) d * Ring.choose (r - 1) e * g := by
  rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_derivative, PowerSeries.coeff_mk,
    ← Nat.cast_add_one, Nat.sub_add_cancel he, mul_comm (dividedKernelCoeff r (d - 1) e)]
  rw [← pairJetCoeff, pairJetCoeff_closed r d e hd]

/-- Exchanging the two moving-residue slots exchanges their fractional parts. -/
theorem pairJetCoeff_swap (r : ℂ) (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    pairJetCoeff r d e = pairJetCoeff (1 - r) e d := by
  rw [pairJetCoeff_closed r d e hd, pairJetCoeff_closed (1 - r) e d he,
    show -(1 - r) = r - 1 by ring, show 1 - r - 1 = -r by ring,
    add_comm (e : ℂ) d, mul_comm (e : ℂ) d]
  ring

theorem scalarKernel_zero : scalarKernel 0 = 0 := by
  ext n
  simp [scalarKernel, Ring.choose_zero_succ]

theorem pairJetCoeff_zero (d e : ℕ) (hd : 0 < d) : pairJetCoeff 0 d e = 0 := by
  rw [pairJetCoeff_closed _ _ _ hd]
  simp [Ring.choose_zero_pos ℂ hd]

/-- The kernel supplies the scalar in the existing higher current–charge
correction, with the physical shift `3d` on the cover. -/
theorem higherCorrection_eq_scalarKernel (a : Charge lattice) (u : Cartan) (r d : ℕ)
    (hd : 0 < d) (k : ℤ) (w : State) :
    P48qHigherCurrentIterate.higherCorrection a u r d k w =
      PowerSeries.coeff (d - 1)
        (scalarKernel ((r : ℂ) / 3) * PowerSeries.C (p48qForm u (chargeVector a))) •
      HVertexOperator.coeff (concreteChargedField a) (k + 3 * (d : ℤ)) w := by
  rw [scalarKernel_charge_coeff _ _ _ hd, P48qHigherCurrentIterate.higherCorrection, smul_smul]
  rfl

/-- At the first level the kernel gives the checked field on the actual
source negative-one product, using the jet normal order. -/
theorem currentCharge_first_coeff (a : Charge lattice) (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (k : ℤ) (w : State) :
    HVertexOperator.coeff (stateField (mu lattice (currentAlong lattice u) (-1) (chargedGround a)))
        k w =
      normalOrderedCoeff a k [(u, 1)] w +
      PowerSeries.coeff 0
        (scalarKernel ((r : ℂ) / 3) * PowerSeries.C (p48qForm u (chargeVector a))) •
      HVertexOperator.coeff (concreteChargedField a) (k + 3) w := by
  have hc :
      PowerSeries.coeff 0
        (scalarKernel ((r : ℂ) / 3) * PowerSeries.C (p48qForm u (chargeVector a))) =
      Ring.choose (-((r : ℂ) / 3)) 1 * p48qForm u (chargeVector a) :=
    scalarKernel_charge_coeff _ _ 1 (by decide)
  rw [P48qCurrentChargedIterate.source_minus_one_field a u r hr hu k,
    P48qJetNormalOrdering.normalOrderedCoeff_singleton_apply, hc, Ring.choose_one_right]
  simp [P48qJetNormalOrdering.jetWeight, normalOrderedCurrentCoeff,
    LinearMap.smul_apply, neg_smul, sub_eq_add_neg, neg_mul]
  rfl

theorem pairJetCoeff_one_one (r : ℂ) : pairJetCoeff r 1 1 = r * (1 - r) / 2 := by
  rw [pairJetCoeff_closed r 1 1 (by decide)]
  simp only [Nat.cast_one, one_mul, Ring.choose_one_right]
  ring

/-- The two first jets give the exact identity coefficient of the checked
quadratic state field. Its physical shift is `6` on the cover. -/
theorem currentPair_first_coeff (u v : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (M : ℤ) :
    HVertexOperator.coeff
      (P48qQuadraticStateField.neutralStateField (P48qQuadraticStateField.currentProduct u v 0))
      (-M - 6) =
    P48qQuadraticStateField.orderedMode M u v +
      if M = 0 then (pairJetCoeff ((r : ℂ) / 3) 1 1 * p48qForm u v) • (1 : Module.End ℂ State)
      else 0 := by
  have hc : -(Ring.choose ((r : ℂ) / 3) 2 * p48qForm u v) =
      pairJetCoeff ((r : ℂ) / 3) 1 1 * p48qForm u v := by
    rw [choose_two, pairJetCoeff_one_one]
    ring
  rw [P48qQuadraticStateField.neutralStateField_pair_coeff, correction_on_residue u v r hr hu, hc]

#print axioms scalarKernel_mul_X
#print axioms scalarKernel_charge_coeff
#print axioms dividedKernelCoeff_right_zero
#print axioms dividedKernelCoeff_left_zero
#print axioms dividedKernelCoeff_sub
#print axioms pairConvolution_closed
#print axioms pairJetCoeff_closed
#print axioms pairKernel_derivative_coeff
#print axioms pairJetCoeff_swap
#print axioms scalarKernel_zero
#print axioms pairJetCoeff_zero
#print axioms higherCorrection_eq_scalarKernel
#print axioms currentCharge_first_coeff
#print axioms pairJetCoeff_one_one
#print axioms currentPair_first_coeff

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qJetContractions
