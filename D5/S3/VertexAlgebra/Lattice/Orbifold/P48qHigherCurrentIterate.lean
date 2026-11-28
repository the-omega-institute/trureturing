/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qHigherCurrentIterate
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary negative source modes as signed Hasse-weighted oscillator insertions. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCurrentChargedIterate
import Mathlib.RingTheory.Binomial

/-!
The arbitrary negative source-mode layer for the order-three charged ground.
The source mode `-d` is transported to the degree `d - 1` oscillator on the
original charge sector.  On the signed cover strip the corresponding normal
coefficient is recorded with its Hasse weight, and the scalar correction is
kept explicit.  A finite inverse-binomial identity is supplied for the actual
P48q ordered terms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qHigherCurrentIterate

open LatticeGeneratingFieldLocality (Carrier Charge Oscillator)
open LatticeAllStateReconstruction (mu)
open LatticeActualConformalState (current_state_field)
open LatticeFiniteNegativeGeneration (neutralField neutralPolynomialMode)
open LatticeSugawaraCurrents (neutralField_ncoeff)
open ThirdTwistedIterate (currentAlong)
open ThirdEigenspacePairing (p48qForm p48qAction)
open P48qTwistedChargeAction (lattice)
open P48qThirdTwistedField
  (Cartan State chargeVector fieldCoeff fixedDualBases concreteChargedField)
open P48qTwistedHeisenberg (mode modeLinear mode_projectAt)
open P48qCurrentChargedIterate
  (orderedTerm orderedTerm_fields orderedTerm_support chargedGround contraction
    normalOrderedCurrentCoeff stateField source_minus_one_field)
open scoped BigOperators VertexOperator

open private neutral_negative_single from D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open private projectAt_off_residue from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField

noncomputable section

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

/-- The degree `d - 1` oscillator carried by a negative source mode `-d`. -/
def sourceOscillator (u : Cartan) (d : ℕ) : Oscillator lattice :=
  ∑ i : Fin lattice.rank, u i • MvPolynomial.X (i, d - 1)

/-- The actual charge-sector state produced by the negative source mode. -/
def chargedNegativeSource (a : Charge lattice) (u : Cartan) (d : ℕ) : Carrier lattice :=
  Finsupp.single a (sourceOscillator u d)

/-- The source-mode transport is literal on the original carrier. -/
theorem source_product_negative (a : Charge lattice) (u : Cartan) (d : ℕ) (hd : 0 < d) :
    mu lattice (currentAlong lattice u) (-(d : ℤ)) (chargedGround a) =
      chargedNegativeSource a u d := by
  have h (i : Fin lattice.rank) :
      VertexOperator.ncoeff (neutralField lattice i) (-(d : ℤ)) (chargedGround a) =
      Finsupp.single a (MvPolynomial.X (i, d - 1)) := by
    simpa only [chargedGround,
      show -((d - 1 : ℕ) : ℤ) - 1 = -(d : ℤ) by omega, mul_one] using
      (neutral_negative_single lattice i (d - 1) a (1 : Oscillator lattice))
  have source_modes_local :
      mu lattice (currentAlong lattice u) (-(d : ℤ)) (chargedGround a) =
        ∑ i : Fin lattice.rank, u i •
          (VertexOperator.ncoeff (neutralField lattice i) (-(d : ℤ))
            (chargedGround a)) := by
    simp only [mu, currentAlong, map_sum, map_smul, current_state_field,
      neutralField_ncoeff, Finset.sum_apply, Pi.smul_apply, LinearMap.sum_apply,
      LinearMap.smul_apply]
  rw [source_modes_local]
  simp_rw [h]
  change (∑ i : Fin lattice.rank, u i •
      (Finsupp.lsingle a : Oscillator lattice →ₗ[ℂ] Carrier lattice)
        (MvPolynomial.X (i, d - 1))) =
    (Finsupp.lsingle a : Oscillator lattice →ₗ[ℂ] Carrier lattice)
      (sourceOscillator u d)
  simp only [sourceOscillator, map_sum, map_smul]

/-- The signed integer on the cover strip `m = 3 i + r`. -/
def signedStripIndex (r : ℕ) (m : ℤ) : ℤ :=
  (m - (r : ℤ)) / 3

/-- Hasse weight of level `d` on the signed strip. -/
def hasseWeight (r : ℕ) (m : ℤ) (d : ℕ) : ℂ :=
  Ring.choose (-((signedStripIndex r m : ℤ) : ℂ) - 1) (d - 1)

/-- One weighted summand of the level-`d` charged normal coefficient. -/
def higherNormalTerm (a : Charge lattice) (u : Cartan) (r d : ℕ) (k m : ℤ) (w : State) : State :=
  if m % 3 = (r : ℤ) then
    hasseWeight r m d • orderedTerm a (k + 3 * (d - 1 : ℕ)) m u w
  else 0

/-- The signed-strip Hasse-normal coefficient, with the residue condition explicit. -/
def higherNormalCoeff (a : Charge lattice) (u : Cartan) (r d : ℕ) (k : ℤ) (w : State) : State :=
  ∑ᶠ m : ℤ, higherNormalTerm a u r d k m w

theorem higherNormalCoeff_finite (a : Charge lattice) (u : Cartan)
    (r d : ℕ) (k : ℤ) (w : State) :
    Function.HasFiniteSupport (fun m : ℤ =>
      if m % 3 = (r : ℤ) then
        hasseWeight r m d • orderedTerm a (k + 3 * (d - 1 : ℕ)) m u w else 0) := by
  let f : ℤ → State := fun m =>
    hasseWeight r m d • orderedTerm a (k + 3 * (d - 1 : ℕ)) m u w
  have hf : Function.HasFiniteSupport f := by
    let I := Finset.Icc (min 0 (P48qThirdTwistedField.lowerBound a w -
      (k + 3 * (d - 1 : ℕ)) - 3))
      (P48qFixedCurrentIterate.coverBound w : ℤ)
    have hbase : Function.HasFiniteSupport
        (fun m : ℤ => orderedTerm a (k + 3 * (d - 1 : ℕ)) m u w) :=
      I.finite_toSet.subset (orderedTerm_support a u
        (k + 3 * (d - 1 : ℕ)) w)
    exact hbase.smul_right (fun m : ℤ => hasseWeight r m d)
  let g : ℤ → State := fun m => if m % 3 = (r : ℤ) then f m else 0
  have hg : Function.support g ⊆ Function.support f := by
    intro m hm
    change g m ≠ 0 at hm
    change f m ≠ 0
    by_contra hz
    simp [g, hz] at hm
  have hfinite : Function.HasFiniteSupport g := hf.subset hg
  simpa only [g, f] using hfinite

/-- The explicit level-`d` correction uses the charged zero-current pairing and
the coefficient shifted by `3 d`, which is the cover form of `z⁻ᵈ`. -/
def higherCorrection (a : Charge lattice) (u : Cartan) (r d : ℕ) (k : ℤ) (w : State) : State :=
  Ring.choose (-((r : ℂ) / 3)) d •
    (p48qForm u (chargeVector a) •
      fieldCoeff fixedDualBases a (k + 3 * (d : ℤ)) w)

/-- The noncircular candidate coefficient at arbitrary negative source depth. -/
def higherCorrectedCoeff (a : Charge lattice) (u : Cartan) (r d : ℕ) (k : ℤ) (w : State) : State :=
  higherNormalCoeff a u r d k w + higherCorrection a u r d k w

/-- The level-one correction has exactly the sign in the compiled -1 field. -/
theorem higherCorrection_one_sign (a : Charge lattice) (u : Cartan) (r : ℕ) (k : ℤ)
    (w : State) :
    higherCorrection a u r 1 k w =
      -(((r : ℂ) / 3) * p48qForm u (chargeVector a)) •
        fieldCoeff fixedDualBases a (k + 3) w := by
  simp only [higherCorrection, Ring.choose_one_right, smul_smul,
    Int.cast_one, mul_one, Nat.cast_one]
  module

private theorem finite_convolution
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a c : ℂ) (K : ℕ) (v : ℕ → V) (hv : ∀ n, K ≤ n → v n = 0) :
    (∑ j ∈ Finset.range K, Ring.choose a j •
      (∑ k ∈ Finset.range K, Ring.choose c k • v (j + k))) =
    ∑ n ∈ Finset.range K, Ring.choose (a + c) n • v n := by
  classical
  simp_rw [Finset.smul_sum, smul_smul]
  calc
    _ = ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range (K - j),
        (Ring.choose a j * Ring.choose c k) • v (j + k) := by
      apply Finset.sum_congr rfl
      intro j hj
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.sub_le K j))
      intro k hk outside
      rw [hv (j + k) (by simp only [Finset.mem_range] at outside; omega), smul_zero]
    _ = ∑ n ∈ Finset.range K, ∑ j ∈ Finset.range (n + 1),
        (Ring.choose a j * Ring.choose c (n - j)) • v n := by
      rw [← Finset.sum_range_diag_flip]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.add_sub_of_le (by simpa using Finset.mem_range.mp hj)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Finset.sum_smul, Ring.add_choose_eq n (Commute.all _ _),
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private theorem finite_zero_transform
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K : ℕ) (hK : 0 < K) (v : ℕ → V) :
    (∑ n ∈ Finset.range K, Ring.choose (0 : ℂ) n • v n) = v 0 := by
  rw [Finset.sum_eq_single 0]
  · simp
  · intro n hn hne
    rw [Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hne), zero_smul]
  · simp only [Finset.mem_range, hK, not_true_eq_false, IsEmpty.forall_iff]

/-- Finite inverse-binomial convolution on the actual signed P48q ordered terms. -/
def strippedOrderedTerm (a : Charge lattice) (u : Cartan) (r d : ℕ)
    (k : ℤ) (w : State) (n : ℕ) : State :=
  orderedTerm a (k + 3 * (d - 1 : ℕ))
    (3 * (n : ℤ) + (r : ℤ)) u w

theorem orderedTerm_inverse_binomial
    (a : Charge lattice) (u : Cartan) (r : ℕ) (d : ℕ)
    (k : ℤ) (w : State) (K : ℕ) (hK : 0 < K)
    (hv : ∀ n, K ≤ n → strippedOrderedTerm a u r d k w n = 0) :
    (∑ j ∈ Finset.range K, Ring.choose (-((r : ℂ) / 3)) j •
      (∑ n ∈ Finset.range K, Ring.choose ((r : ℂ) / 3) n •
        strippedOrderedTerm a u r d k w (j + n))) =
      strippedOrderedTerm a u r d k w 0 := by
  let v : ℕ → State := strippedOrderedTerm a u r d k w
  have hconv := finite_convolution (-((r : ℂ) / 3)) ((r : ℂ) / 3) K v
    hv
  rw [show -((r : ℂ) / 3) + (r : ℂ) / 3 = 0 by ring,
    finite_zero_transform K hK v] at hconv
  simpa only [v, strippedOrderedTerm, Nat.cast_add, Int.cast_add, Int.cast_mul] using hconv

theorem hasseWeight_signed_strip (r : ℕ) (m : ℤ) (hr : m % 3 = (r : ℤ)) (d : ℕ) :
    hasseWeight r m d = Ring.choose (-((signedStripIndex r m : ℤ) : ℂ) - 1) (d - 1) := by
  rfl

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qHigherCurrentIterate
