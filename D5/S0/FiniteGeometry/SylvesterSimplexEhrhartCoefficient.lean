/- GID: D5/S0/FiniteGeometry/SylvesterSimplexEhrhartCoefficient
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/SylvesterSimplexEhrhartCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact restricted-partition coefficients for the source Sylvester simplex. -/

import D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity
import D5.S0.FiniteGeometry.SylvesterSimplexEhrhartSamples
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.RootsOfUnity.Complex

noncomputable section

namespace D5.S0.FiniteGeometry.SylvesterSimplexEhrhartCoefficient

open scoped BigOperators

open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open private axisScale_pos baseWeight base_axisScale_dvd_mass sylvester_sub_one_eq_prod
  two_le_sylvester from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open private partitionWeight partitionWeight_pos partitionWeight_dvd_period restrictedPartitionSeries
  geometricFactor geometricFactor_mul_one_sub_X_pow baseSamplePolynomial
  coeff_restrictedPartitionSeries_period_eq_eval interiorSamplePolynomial
  coeff_restrictedPartitionSeries_period_sub_one_eq_eval from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartSamples


private def rootLocalCoordinate (ζ : ℂ) (M : ℕ) : PowerSeries ℂ :=
  PowerSeries.C ζ *
    PowerSeries.rescale (-(M : ℂ)⁻¹) (PowerSeries.exp ℂ)

private lemma rootLocalCoordinate_pow_partitionWeight (d : ℕ) (hd : 1 ≤ d)
    (ζ : ℂ) (j : Option (Fin d)) :
    rootLocalCoordinate ζ
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) ^
        partitionWeight d j =
      PowerSeries.C (ζ ^ partitionWeight d j) *
        PowerSeries.rescale
          (-(((D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) /
            partitionWeight d j : ℕ) : ℂ)⁻¹)
          (PowerSeries.exp ℂ) := by
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  let w := partitionWeight d j
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd))
  have hw : 0 < w := partitionWeight_pos d hd j
  have hdiv : w ∣ M := partitionWeight_dvd_period d hd j
  have hMw : M / w * w = M := Nat.div_mul_cancel hdiv
  have hquot : 0 < M / w := Nat.div_pos (Nat.le_of_dvd hM hdiv) hw
  rw [rootLocalCoordinate, mul_pow, map_pow]
  congr 1
  rw [← map_pow (PowerSeries.rescale (-(M : ℂ)⁻¹)),
    PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.rescale_rescale]
  apply congrArg (fun a : ℂ => PowerSeries.rescale a (PowerSeries.exp ℂ))
  rw [mul_neg, neg_inj]
  change (w : ℂ) * (M : ℂ)⁻¹ = ((M / w : ℕ) : ℂ)⁻¹
  have hprod : M = w * (M / w) := by
    simpa [Nat.mul_comm] using hMw.symm
  have hprodC : (M : ℂ) = (w : ℂ) * (M / w : ℕ) := by
    exact_mod_cast hprod
  rw [hprodC]
  field_simp [Nat.ne_of_gt hw, Nat.ne_of_gt hquot]

/-- The actual denominator factor attached to one source partition weight in
the local coordinate `z = ζ exp (-y/M)`. -/
private def rootDenominatorFactor (d : ℕ) (ζ : ℂ) (j : Option (Fin d)) :
    PowerSeries ℂ :=
  1 - rootLocalCoordinate ζ
      (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) ^
        partitionWeight d j

private lemma rootDenominatorFactor_coeff_zero (d : ℕ) (hd : 1 ≤ d)
    (ζ : ℂ) (j : Option (Fin d)) :
    PowerSeries.coeff 0 (rootDenominatorFactor d ζ j) =
      1 - ζ ^ partitionWeight d j := by
  have hconstant (a : ℂ) :
      PowerSeries.constantCoeff
          (PowerSeries.rescale a (PowerSeries.exp ℂ)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, pow_zero, one_mul, PowerSeries.coeff_exp]
    norm_num
  rw [rootDenominatorFactor, rootLocalCoordinate_pow_partitionWeight d hd]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [hconstant]

/-- The first root jet is the phase times the exact reciprocal source scale.
For a vanishing factor the phase is one, leaving the Jacobian `1 / s_i`. -/
private lemma rootDenominatorFactor_coeff_one (d : ℕ) (hd : 1 ≤ d)
    (ζ : ℂ) (j : Option (Fin d)) :
    PowerSeries.coeff 1 (rootDenominatorFactor d ζ j) =
      ζ ^ partitionWeight d j *
        (((D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) /
          partitionWeight d j : ℕ) : ℂ)⁻¹ := by
  have hconstant (a : ℂ) :
      PowerSeries.constantCoeff
          (PowerSeries.rescale a (PowerSeries.exp ℂ)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, pow_zero, one_mul, PowerSeries.coeff_exp]
    norm_num
  have hconstantPow (a : ℂ) (n : ℕ) :
      PowerSeries.coeff 1 ((PowerSeries.C a : PowerSeries ℂ) ^ n) = 0 := by
    rw [PowerSeries.coeff_one_pow]
    simp
  rw [rootDenominatorFactor, rootLocalCoordinate_pow_partitionWeight d hd]
  rw [map_sub, PowerSeries.coeff_one, if_neg one_ne_zero,
    PowerSeries.coeff_one_mul]
  simp [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, hconstant, hconstantPow]
  ring_nf

/-- Removing the forced local `X` from a denominator factor. -/
private def rootVanishingQuotient (d : ℕ) (ζ : ℂ) (j : Option (Fin d)) :
    PowerSeries ℂ :=
  PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (rootDenominatorFactor d ζ j)

private lemma rootDenominatorFactor_eq_quotient_mul_X (d : ℕ) (hd : 1 ≤ d)
    (ζ : ℂ) (j : Option (Fin d)) (hroot : ζ ^ partitionWeight d j = 1) :
    rootDenominatorFactor d ζ j = rootVanishingQuotient d ζ j * PowerSeries.X := by
  have hconstant : PowerSeries.constantCoeff (rootDenominatorFactor d ζ j) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff,
      rootDenominatorFactor_coeff_zero d hd, hroot, sub_self]
  simpa [rootVanishingQuotient, hconstant] using
    PowerSeries.eq_shift_mul_X_add_const (rootDenominatorFactor d ζ j)

private lemma rootVanishingQuotient_constantCoeff (d : ℕ) (hd : 1 ≤ d)
    (ζ : ℂ) (j : Option (Fin d)) (hroot : ζ ^ partitionWeight d j = 1) :
    PowerSeries.constantCoeff (rootVanishingQuotient d ζ j) =
      (((D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) /
        partitionWeight d j : ℕ) : ℂ)⁻¹ := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [rootVanishingQuotient, PowerSeries.coeff_mk, zero_add]
  rw [rootDenominatorFactor_coeff_one d hd, hroot, one_mul]

/-- A set of vanishing source factors contributes exactly one local `X` per
factor.  This is the source-specific pole-order input for the later jet cut. -/
private lemma rootVanishingProduct_factorization (d : ℕ) (hd : 1 ≤ d)
    (ζ : ℂ) (S : Finset (Option (Fin d)))
    (hS : ∀ j ∈ S, ζ ^ partitionWeight d j = 1) :
    ∏ j ∈ S, rootDenominatorFactor d ζ j =
      (∏ j ∈ S, rootVanishingQuotient d ζ j) * PowerSeries.X ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj,
        rootDenominatorFactor_eq_quotient_mul_X d hd ζ j (hS j (by simp)),
        ih (fun i hi => hS i (by simp [hi])), Finset.card_insert_of_notMem hj, pow_succ]
      ring

/-- The leading coefficient after removing all forced local `X` factors is
the exact product of the reciprocal source scales. -/
private lemma rootVanishingProduct_leadingCoefficient (d : ℕ) (hd : 1 ≤ d)
    (ζ : ℂ) (S : Finset (Option (Fin d)))
    (hS : ∀ j ∈ S, ζ ^ partitionWeight d j = 1) :
    PowerSeries.constantCoeff (∏ j ∈ S, rootVanishingQuotient d ζ j) =
      ∏ j ∈ S,
        (((D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) /
          partitionWeight d j : ℕ) : ℂ)⁻¹ := by
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  exact rootVanishingQuotient_constantCoeff d hd ζ j (hS j hj)

private def sourceDenominator (d : ℕ) : Polynomial ℂ :=
  ∏ j : Option (Fin d),
    (1 - Polynomial.X ^ partitionWeight d j)

private def sourcePoleOrder (d : ℕ) (ζ : ℂ) : ℕ :=
  (Finset.univ.filter fun j : Option (Fin d) =>
    ζ ^ partitionWeight d j = 1).card

private def sourceRootSupport (d : ℕ) (ζ : ℂ) : Finset (Option (Fin d)) :=
  Finset.univ.filter fun j => ζ ^ partitionWeight d j ≠ 1

private def sourceVanishingFactors (d : ℕ) (ζ : ℂ) : Finset (Option (Fin d)) :=
  Finset.univ.filter fun j => ζ ^ partitionWeight d j = 1

/-- After the forced local powers of `X` are removed, this is the remaining
source denominator in the coordinate `z = ζ exp (-y/M)`. -/
private def sourceLocalRegularDenominator (d : ℕ) (ζ : ℂ) : PowerSeries ℂ :=
  (∏ j ∈ sourceVanishingFactors d ζ, rootVanishingQuotient d ζ j) *
    ∏ j ∈ sourceRootSupport d ζ, rootDenominatorFactor d ζ j

private def sourceLocalRegularInverse (d : ℕ) (ζ : ℂ) : PowerSeries ℂ :=
  (sourceLocalRegularDenominator d ζ)⁻¹

/-- The regular exponential jet occurring after the coefficient-residue
substitution.  The shift `c` is integral so the two actual samples `c=0,-1`
use the same object. -/
private def sourceExponentialLocalJet (d : ℕ) (ζ : ℂ) (c : ℤ) : PowerSeries ℂ :=
  PowerSeries.rescale
      ((c : ℂ) *
        (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1 : ℂ)⁻¹)
      (PowerSeries.exp ℂ) *
    sourceLocalRegularInverse d ζ

private lemma sourcePoleOrder_add_support_card (d : ℕ) (ζ : ℂ) :
    sourcePoleOrder d ζ + (sourceRootSupport d ζ).card = d + 1 := by
  classical
  rw [sourcePoleOrder, sourceRootSupport]
  simpa [Fintype.card_option, Fintype.card_fin] using
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Option (Fin d))))
      (p := fun j => ζ ^ partitionWeight d j = 1)

/-- The residue index is six minus the number of nonvanishing source factors.
At a nontrivial root those factors include the two copies of `1-z`, leaving
the paper's index `4-|R|`; at one the support is empty and the index is six. -/
private lemma sourceLocalCutoff_eq_six_sub_support (d : ℕ) (hd : 6 ≤ d)
    (ζ : ℂ) :
    sourcePoleOrder d ζ - (d - 6) - 1 = 6 - (sourceRootSupport d ζ).card := by
  have hcard := sourcePoleOrder_add_support_card d ζ
  omega

/-- The literal local denominator has exactly `sourcePoleOrder` forced powers
of the local coordinate and no discarded factor. -/
private lemma sourceLocalDenominator_factorization (d : ℕ) (hd : 1 ≤ d)
    (ζ : ℂ) :
    ∏ j : Option (Fin d), rootDenominatorFactor d ζ j =
      sourceLocalRegularDenominator d ζ * PowerSeries.X ^ sourcePoleOrder d ζ := by
  classical
  let V := sourceVanishingFactors d ζ
  let R := sourceRootSupport d ζ
  have hV :
      ∏ j ∈ V, rootDenominatorFactor d ζ j =
        (∏ j ∈ V, rootVanishingQuotient d ζ j) * PowerSeries.X ^ V.card := by
    apply rootVanishingProduct_factorization d hd
    intro j hj
    simpa [V, sourceVanishingFactors] using hj
  have hsplit :
      (∏ j ∈ V, rootDenominatorFactor d ζ j) *
          (∏ j ∈ R, rootDenominatorFactor d ζ j) =
        ∏ j : Option (Fin d), rootDenominatorFactor d ζ j := by
    simpa [V, R, sourceVanishingFactors, sourceRootSupport] using
      Finset.prod_filter_mul_prod_filter_not
        (s := (Finset.univ : Finset (Option (Fin d))))
        (p := fun j => ζ ^ partitionWeight d j = 1)
        (f := fun j => rootDenominatorFactor d ζ j)
  rw [← hsplit, hV]
  simp only [sourceLocalRegularDenominator, sourcePoleOrder, V, R,
    sourceVanishingFactors, sourceRootSupport]
  ring

private lemma sourceLocalRegularDenominator_constantCoeff (d : ℕ) (hd : 1 ≤ d)
    (ζ : ℂ) :
    PowerSeries.constantCoeff (sourceLocalRegularDenominator d ζ) =
      (∏ j ∈ sourceVanishingFactors d ζ,
          (((D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) /
            partitionWeight d j : ℕ) : ℂ)⁻¹) *
        ∏ j ∈ sourceRootSupport d ζ, (1 - ζ ^ partitionWeight d j) := by
  classical
  rw [sourceLocalRegularDenominator, map_mul, map_prod, map_prod]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro j hj
    exact rootVanishingQuotient_constantCoeff d hd ζ j (by
      simpa [sourceVanishingFactors] using hj)
  · apply Finset.prod_congr rfl
    intro j hj
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      rootDenominatorFactor_coeff_zero d hd]

/-- The regularized local inverse exposes the exact source Jacobian before any
sign estimate: every vanishing factor contributes its reciprocal source scale,
and every nonvanishing factor retains its root phase. -/
private lemma sourceLocalRegularInverse_constantCoeff (d : ℕ) (hd : 1 ≤ d)
    (ζ : ℂ) :
    PowerSeries.constantCoeff (sourceLocalRegularInverse d ζ) =
      ((∏ j ∈ sourceVanishingFactors d ζ,
          (((D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) /
            partitionWeight d j : ℕ) : ℂ)⁻¹) *
        ∏ j ∈ sourceRootSupport d ζ, (1 - ζ ^ partitionWeight d j))⁻¹ := by
  rw [sourceLocalRegularInverse, PowerSeries.constantCoeff_inv,
    sourceLocalRegularDenominator_constantCoeff d hd]

private lemma sourceScaleProduct (d : ℕ) (hd : 1 ≤ d) :
    ∏ j : Option (Fin d),
        (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) /
          partitionWeight d j =
      (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) ^ 3 := by
  classical
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd))
  have hsome (i : Fin d) : M / partitionWeight d (some i) = axisScale d 0 i := by
    apply Nat.div_eq_of_eq_mul_left (partitionWeight_pos d hd (some i))
    rw [partitionWeight, baseWeight]
    simpa [M, Nat.mul_comm] using
      (Nat.div_mul_cancel (base_axisScale_dvd_mass d hd i)).symm
  have hshift (n : ℕ) :
      ∏ i ∈ Finset.range n,
          D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i + 1) =
        D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (n + 1) - 1 := by
    induction n with
    | zero => simp [D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester]
    | succ n ih =>
        rw [Finset.prod_range_succ, ih]
        simp [D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester,
          Nat.mul_comm]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  rw [Fintype.prod_option]
  simp only [partitionWeight, Nat.div_one]
  rw [show (∏ i : Fin (n + 1),
        (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (n + 1) - 1) /
          baseWeight (n + 1) i) =
      ∏ i : Fin (n + 1), axisScale (n + 1) 0 i by
        apply Fintype.prod_congr
        intro i
        simpa [partitionWeight, M] using hsome i]
  rw [Fin.prod_univ_castSucc]
  have hcast (i : Fin n) :
      axisScale (n + 1) 0 i.castSucc =
        D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.val + 1) := by
    rw [axisScale, if_neg (by simp only [Fin.val_castSucc]; omega)]
    rfl
  have hlast : axisScale (n + 1) 0 (Fin.last n) = M := by
    simp [axisScale, M]
  simp_rw [hcast]
  rw [hlast]
  have hmiddle :
      (∏ i : Fin n,
          D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.val + 1)) =
        M := by
    calc
      (∏ i : Fin n,
          D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i.val + 1)) =
          ∏ i ∈ Finset.range n,
            D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i + 1) :=
        Fin.prod_univ_eq_prod_range
          (fun i ↦ D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester (i + 1)) n
      _ = M := hshift n
  rw [hmiddle]
  change M * (M * M) = M ^ 3
  ring

/-- At the pole `ζ=1` all source factors vanish.  The residue Jacobian is
exactly `M^2`: one factor `M` is cancelled by `dz/z=-dy/M`. -/
private lemma sourcePoleOne_jacobian (d : ℕ) (hd : 1 ≤ d) :
    (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1 : ℂ)⁻¹ *
        PowerSeries.constantCoeff (sourceLocalRegularInverse d 1) =
      (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1 : ℂ) ^ 2 := by
  classical
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd))
  rw [sourceLocalRegularInverse_constantCoeff d hd]
  have hvanish : sourceVanishingFactors d 1 = Finset.univ := by
    ext j
    simp [sourceVanishingFactors]
  have hsupport : sourceRootSupport d 1 = ∅ := by
    ext j
    simp [sourceRootSupport]
  rw [hvanish, hsupport]
  simp only [Finset.prod_empty, mul_one]
  rw [Finset.prod_inv_distrib]
  have hscaleC :
      (∏ j : Option (Fin d),
          (((D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) /
            partitionWeight d j : ℕ) : ℂ)) = (M : ℂ) ^ 3 := by
    exact_mod_cast sourceScaleProduct d hd
  rw [hscaleC, inv_inv]
  have hMC :
      (M : ℂ) =
        (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d : ℂ) - 1 := by
    dsimp [M]
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [← hMC]
  field_simp [Nat.ne_of_gt hM]

/-- The polynomial in the sample parameter produced by the actual local
substitution at one root.  Its coefficients are the finite exponential
convolution below the pole order, including the integral sample shift phase. -/
private def sourceLocalRootContributionPolynomial (d : ℕ) (ζ : ℂ) (c : ℤ) :
    Polynomial ℂ :=
  Polynomial.C
      (ζ ^ (-c) *
        (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1 : ℂ)⁻¹) *
    ∑ m ∈ Finset.range (sourcePoleOrder d ζ),
      Polynomial.C
          ((m.factorial : ℂ)⁻¹ *
            PowerSeries.coeff (sourcePoleOrder d ζ - m - 1)
              (sourceExponentialLocalJet d ζ c)) * Polynomial.X ^ m

/-- Evaluating the local contribution polynomial is exactly the residue-index
coefficient of `exp (t*y)` times the regularized literal source denominator. -/
private lemma sourceLocalRootContributionPolynomial_eval (d t : ℕ) (ζ : ℂ) (c : ℤ)
    (hpole : 0 < sourcePoleOrder d ζ) :
    (sourceLocalRootContributionPolynomial d ζ c).eval (t : ℂ) =
      ζ ^ (-c) *
        (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1 : ℂ)⁻¹ *
          PowerSeries.coeff (sourcePoleOrder d ζ - 1)
            (PowerSeries.rescale (t : ℂ) (PowerSeries.exp ℂ) *
              sourceExponentialLocalJet d ζ c) := by
  rw [sourceLocalRootContributionPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_finsetSum]
  apply congrArg (ζ ^ (-c) *
    (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1 : ℂ)⁻¹ * ·)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Nat.succ_eq_add_one]
  rw [show sourcePoleOrder d ζ - 1 + 1 = sourcePoleOrder d ζ by omega]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp, map_div, map_one,
    map_natCast, one_div, one_mul]
  rw [show sourcePoleOrder d ζ - m - 1 = sourcePoleOrder d ζ - 1 - m by
    have := Finset.mem_range.mp hm
    omega]
  rw [map_inv₀]
  norm_num
  ring

/-- The target monomial coefficient of the actual local residue polynomial.
The phase, `1/M`, factorial, and the sharp `6-|support|` jet index are all
visible before any sign or absolute-value estimate. -/
private lemma sourceLocalRootContributionPolynomial_target_coeff (d : ℕ) (hd : 6 ≤ d)
    (ζ : ℂ) (c : ℤ) (hsupport : (sourceRootSupport d ζ).card ≤ 6) :
    (sourceLocalRootContributionPolynomial d ζ c).coeff (d - 6) =
      ζ ^ (-c) *
        (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1 : ℂ)⁻¹ *
          ((d - 6).factorial : ℂ)⁻¹ *
            PowerSeries.coeff (6 - (sourceRootSupport d ζ).card)
              (sourceExponentialLocalJet d ζ c) := by
  have hcard := sourcePoleOrder_add_support_card d ζ
  have hlt : d - 6 < sourcePoleOrder d ζ := by omega
  rw [sourceLocalRootContributionPolynomial, Polynomial.coeff_C_mul]
  have hcoeff :
      (∑ m ∈ Finset.range (sourcePoleOrder d ζ),
        Polynomial.C
            ((m.factorial : ℂ)⁻¹ *
              PowerSeries.coeff (sourcePoleOrder d ζ - m - 1)
                (sourceExponentialLocalJet d ζ c)) * Polynomial.X ^ m).coeff (d - 6) =
        ((d - 6).factorial : ℂ)⁻¹ *
          PowerSeries.coeff (sourcePoleOrder d ζ - (d - 6) - 1)
            (sourceExponentialLocalJet d ζ c) := by
    change Polynomial.lcoeff ℂ (d - 6)
        (∑ m ∈ Finset.range (sourcePoleOrder d ζ),
          Polynomial.C
              ((m.factorial : ℂ)⁻¹ *
                PowerSeries.coeff (sourcePoleOrder d ζ - m - 1)
                  (sourceExponentialLocalJet d ζ c)) * Polynomial.X ^ m) = _
    rw [map_sum]
    simp only [Polynomial.lcoeff_apply]
    rw [Finset.sum_eq_single (d - 6)]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro m hm hne
      rw [Polynomial.coeff_C_mul_X_pow, if_neg hne.symm]
    · simp [hlt]
  rw [hcoeff, sourceLocalCutoff_eq_six_sub_support d hd ζ]
  ring

/-- At the pole one, divide the regular source jet by its exact leading
Jacobian `M^3`; the residue differential then leaves the audited `M^2`. -/
private def sourcePoleOneNormalizedJet (d : ℕ) (c : ℤ) : PowerSeries ℂ :=
  PowerSeries.C
      ((D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1 : ℂ) ^ 3)⁻¹ *
    sourceExponentialLocalJet d 1 c

/-- The pole-at-one target coefficient has the exact external factor
`M^2/(d-6)!`; no power of the source period is hidden in the normalized jet. -/
private lemma sourceLocalRootContributionPolynomial_one_target_coeff
    (d : ℕ) (hd : 6 ≤ d) (c : ℤ) :
    (sourceLocalRootContributionPolynomial d 1 c).coeff (d - 6) =
      (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1 : ℂ) ^ 2 *
        ((d - 6).factorial : ℂ)⁻¹ *
          PowerSeries.coeff 6 (sourcePoleOneNormalizedJet d c) := by
  have hsupport : sourceRootSupport d 1 = ∅ := by
    classical
    ext j
    simp [sourceRootSupport]
  rw [sourceLocalRootContributionPolynomial_target_coeff d hd 1 c (by simp [hsupport]),
    hsupport]
  simp only [Finset.card_empty, Nat.sub_zero, one_zpow]
  rw [sourcePoleOneNormalizedJet, PowerSeries.coeff_C_mul]
  have hsylvester :
      1 < D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d :=
    lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d (by omega))
  have hM :
      (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1 : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast ne_of_gt hsylvester
  field_simp

private def sourceGeneratingSeries (d : ℕ) : PowerSeries ℂ :=
  PowerSeries.map (Rat.castHom ℂ) (restrictedPartitionSeries d)

/-- The literal source denominator factors over the `M`-th roots with exactly
the number of vanishing source factors as the exponent. -/
private lemma sourceDenominator_root_factorization (d : ℕ) (hd : 1 ≤ d) :
    sourceDenominator d =
      (-1 : Polynomial ℂ) ^ (d + 1) *
        ∏ ζ ∈ Polynomial.nthRootsFinset
            (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1)
            (1 : ℂ),
          (Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ := by
  classical
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  let roots := Polynomial.nthRootsFinset M (1 : ℂ)
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd))
  have hfactor (j : Option (Fin d)) :
      (1 - Polynomial.X ^ partitionWeight d j : Polynomial ℂ) =
        -∏ ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ) with
            ζ ^ partitionWeight d j = 1,
          (Polynomial.X - Polynomial.C ζ) := by
    have hw := partitionWeight_pos d hd j
    have hdiv := partitionWeight_dvd_period d hd j
    have hroots :
        (Polynomial.nthRootsFinset M (1 : ℂ)).filter
            (fun ζ => ζ ^ partitionWeight d j = 1) =
          Polynomial.nthRootsFinset (partitionWeight d j) (1 : ℂ) := by
      ext ζ
      simp only [Finset.mem_filter, Polynomial.mem_nthRootsFinset hM,
        Polynomial.mem_nthRootsFinset hw]
      constructor
      · exact fun h => h.2
      · intro hζ
        refine ⟨?_, hζ⟩
        obtain ⟨a, ha⟩ := hdiv
        change ζ ^
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) = 1
        rw [ha, pow_mul, hζ, one_pow]
    rw [hroots,
      ← Polynomial.X_pow_sub_one_eq_prod hw
        (Complex.isPrimitiveRoot_exp (partitionWeight d j) hw.ne')]
    ring
  rw [sourceDenominator]
  simp_rw [hfactor]
  rw [Finset.prod_neg]
  simp only [Finset.card_univ, Fintype.card_option, Fintype.card_fin]
  congr 1
  simp only [Finset.prod_filter]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro ζ hζ
  rw [← Finset.prod_filter, Finset.prod_const]
  rfl

/-- The mapped literal source series is the inverse of its mapped denominator. -/
private lemma sourceGeneratingSeries_mul_denominator (d : ℕ) (hd : 1 ≤ d) :
    sourceGeneratingSeries d *
        algebraMap (Polynomial ℂ) (PowerSeries ℂ) (sourceDenominator d) = 1 := by
  classical
  rw [sourceGeneratingSeries, restrictedPartitionSeries, sourceDenominator, map_prod,
    map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j hj
  have h := congrArg (PowerSeries.map (Rat.castHom ℂ))
    (geometricFactor_mul_one_sub_X_pow (partitionWeight d j)
      (partitionWeight_pos d hd j))
  simpa [PowerSeries.algebraMap_apply'] using h

private def sourceRootExpansion (d : ℕ) : PowerSeries ℂ :=
  (-1 : PowerSeries ℂ) ^ (d + 1) *
    ∏ ζ ∈ Polynomial.nthRootsFinset
        (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1)
        (1 : ℂ),
      (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
        (Polynomial.X - Polynomial.C ζ))⁻¹ ^ sourcePoleOrder d ζ

private lemma sourceRootExpansion_mul_denominator (d : ℕ) (hd : 1 ≤ d) :
    sourceRootExpansion d *
        algebraMap (Polynomial ℂ) (PowerSeries ℂ) (sourceDenominator d) = 1 := by
  classical
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd))
  have hfactor (ζ : ℂ) (hζ : ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ)) :
      (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
          (Polynomial.X - Polynomial.C ζ))⁻¹ ^ sourcePoleOrder d ζ *
        algebraMap (Polynomial ℂ) (PowerSeries ℂ)
          (Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ = 1 := by
    have hζpow : ζ ^ M = 1 :=
      (Polynomial.mem_nthRootsFinset hM (1 : ℂ)).mp hζ
    have hζzero : ζ ≠ 0 := by
      intro hzero
      have : (0 : ℂ) = 1 := by simpa [hzero, zero_pow hM.ne'] using hζpow
      exact zero_ne_one this
    rw [← mul_pow, PowerSeries.inv_mul_cancel, one_pow]
    simpa [PowerSeries.algebraMap_apply'] using hζzero
  rw [sourceRootExpansion, sourceDenominator_root_factorization d hd, map_mul, map_pow,
    map_prod]
  simp_rw [map_pow]
  simp only [map_neg, map_one]
  have hprod :
      (∏ ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ),
          (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
            (Polynomial.X - Polynomial.C ζ))⁻¹ ^ sourcePoleOrder d ζ) *
        (∏ ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ),
          algebraMap (Polynomial ℂ) (PowerSeries ℂ)
            (Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one hfactor
  change
    ((-1 : PowerSeries ℂ) ^ (d + 1) *
        ∏ ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ),
          (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
            (Polynomial.X - Polynomial.C ζ))⁻¹ ^ sourcePoleOrder d ζ) *
      ((-1 : PowerSeries ℂ) ^ (d + 1) *
        ∏ ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ),
          algebraMap (Polynomial ℂ) (PowerSeries ℂ)
            (Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ) = 1
  calc
    _ = ((-1 : PowerSeries ℂ) ^ (d + 1) * (-1) ^ (d + 1)) *
        ((∏ ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ),
            (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
              (Polynomial.X - Polynomial.C ζ))⁻¹ ^ sourcePoleOrder d ζ) *
          ∏ ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ),
            algebraMap (Polynomial ℂ) (PowerSeries ℂ)
              (Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ) := by ring
    _ = 1 := by
      rw [hprod, mul_one, ← mul_pow]
      simp

/-- The actual inverse source denominator has root-indexed principal parts, and
their ordinary coefficients retain the exact root phase and pole order.  The
same coefficient family recovers both literal source sample polynomials. -/
private lemma sourceRootExpansion_principalPart_coefficients (d : ℕ) (hd : 1 ≤ d) :
    let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
    ∃ (a : (ζ : ℂ) → Fin (sourcePoleOrder d ζ) → ℂ),
      sourceRootExpansion d =
          ∑ ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ), ∑ j,
            PowerSeries.C (a ζ j) *
              (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
                (Polynomial.X - Polynomial.C ζ))⁻¹ ^ (j.1 + 1) ∧
      (∀ n : ℕ,
        PowerSeries.coeff n (sourceRootExpansion d) =
          ∑ ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ), ∑ j,
            a ζ j * (-1 : ℂ) ^ (j.1 + 1) *
              (ζ ^ (n + (j.1 + 1)))⁻¹ *
                (Nat.choose (j.1 + n) j.1 : ℂ)) ∧
      (∀ t : ℕ,
        Rat.castHom ℂ ((baseSamplePolynomial d).eval (t : ℚ)) =
          ∑ ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ), ∑ j,
            a ζ j * (-1 : ℂ) ^ (j.1 + 1) *
              (ζ ^ (t * M + (j.1 + 1)))⁻¹ *
                (Nat.choose (j.1 + t * M) j.1 : ℂ)) ∧
      ∀ t : ℕ, 1 ≤ t →
        Rat.castHom ℂ ((interiorSamplePolynomial d).eval (t : ℚ)) =
          ∑ ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ), ∑ j,
            a ζ j * (-1 : ℂ) ^ (j.1 + 1) *
              (ζ ^ (t * M - 1 + (j.1 + 1)))⁻¹ *
                (Nat.choose (j.1 + (t * M - 1)) j.1 : ℂ) := by
  classical
  dsimp only
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd))
  have hrootNonzero (ζ : ℂ) (hζ : ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ)) : ζ ≠ 0 := by
    have hζpow : ζ ^ M = 1 := (Polynomial.mem_nthRootsFinset hM (1 : ℂ)).mp hζ
    intro hzero
    have : (0 : ℂ) = 1 := by simpa [hzero, zero_pow hM.ne'] using hζpow
    exact zero_ne_one this
  have hlinearInverse (ζ : ℂ) (hζ : ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ)) :
      (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
        (Polynomial.X - Polynomial.C ζ))⁻¹ =
          -PowerSeries.invUnitsSub (Units.mk0 ζ (hrootNonzero ζ hζ)) := by
    have hconstant :
        PowerSeries.constantCoeff
            (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
              (Polynomial.X - Polynomial.C ζ)) ≠ 0 := by
      simpa [PowerSeries.algebraMap_apply'] using neg_ne_zero.mpr (hrootNonzero ζ hζ)
    apply (PowerSeries.inv_eq_iff_mul_eq_one hconstant).2
    have hlinearMap :
        algebraMap (Polynomial ℂ) (PowerSeries ℂ)
            (Polynomial.X - Polynomial.C ζ) =
          PowerSeries.X - PowerSeries.C ζ := by
      simp [PowerSeries.algebraMap_apply', PowerSeries.map_id]
    calc
      -PowerSeries.invUnitsSub (Units.mk0 ζ (hrootNonzero ζ hζ)) *
          algebraMap (Polynomial ℂ) (PowerSeries ℂ)
            (Polynomial.X - Polynomial.C ζ) =
          PowerSeries.invUnitsSub (Units.mk0 ζ (hrootNonzero ζ hζ)) *
            (PowerSeries.C ζ - PowerSeries.X) := by
              rw [hlinearMap]
              ring
      _ = 1 := PowerSeries.invUnitsSub_mul_sub
        (Units.mk0 ζ (hrootNonzero ζ hζ))
  have hprincipalCoeff (ζ : ℂ)
      (hζ : ζ ∈ Polynomial.nthRootsFinset M (1 : ℂ)) (j : ℕ) (n : ℕ) :
      PowerSeries.coeff n
          ((algebraMap (Polynomial ℂ) (PowerSeries ℂ)
            (Polynomial.X - Polynomial.C ζ))⁻¹ ^ (j + 1)) =
        (-1 : ℂ) ^ (j + 1) * (ζ ^ (n + (j + 1)))⁻¹ *
          (Nat.choose (j + n) j : ℂ) := by
    rw [hlinearInverse ζ hζ, neg_pow]
    have hinvUnits :
        PowerSeries.invUnitsSub (Units.mk0 ζ (hrootNonzero ζ hζ)) =
          PowerSeries.C ζ⁻¹ *
            PowerSeries.rescale ζ⁻¹ (PowerSeries.mk 1 : PowerSeries ℂ) := by
      ext m
      simp only [PowerSeries.coeff_invUnitsSub, one_divp, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_rescale, PowerSeries.coeff_mk, Pi.one_apply]
      simp [pow_succ, inv_pow, mul_comm]
    have hrescalePow :
        (PowerSeries.rescale ζ⁻¹ (PowerSeries.mk 1 : PowerSeries ℂ)) ^ (j + 1) =
          PowerSeries.rescale ζ⁻¹ ((PowerSeries.mk 1 : PowerSeries ℂ) ^ (j + 1)) :=
      (map_pow (PowerSeries.rescale ζ⁻¹) (PowerSeries.mk 1 : PowerSeries ℂ) (j + 1)).symm
    rw [hinvUnits, mul_pow, hrescalePow]
    rw [PowerSeries.mk_one_pow_eq_mk_choose_add]
    have hsign : ((-1 : PowerSeries ℂ) ^ (j + 1)) =
        PowerSeries.C ((-1 : ℂ) ^ (j + 1)) := by
      rw [show (-1 : PowerSeries ℂ) = PowerSeries.C (-1 : ℂ) by simp, ← map_pow]
    have hrootPow : (PowerSeries.C ζ⁻¹ : PowerSeries ℂ) ^ (j + 1) =
        PowerSeries.C (ζ⁻¹ ^ (j + 1)) := by
      rw [← map_pow]
    rw [hsign, hrootPow, ← mul_assoc, ← map_mul]
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
    push_cast
    have hpowadd : ζ⁻¹ ^ (j + 1) * ζ⁻¹ ^ n = ζ⁻¹ ^ (n + (j + 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [← inv_pow]
    calc
      (-1 : ℂ) ^ (j + 1) * ζ⁻¹ ^ (j + 1) *
            (ζ⁻¹ ^ n * (Nat.choose (j + n) j : ℂ)) =
          (-1 : ℂ) ^ (j + 1) *
            (ζ⁻¹ ^ (j + 1) * ζ⁻¹ ^ n) *
              (Nat.choose (j + n) j : ℂ) := by ring
      _ = _ := by rw [hpowadd]
  let roots := Polynomial.nthRootsFinset M (1 : ℂ)
  have hlinearMonic : ∀ ζ ∈ roots, (Polynomial.X - Polynomial.C ζ).Monic := by
    intro ζ hζ
    exact Polynomial.monic_X_sub_C ζ
  have hlinearCoprime : Set.Pairwise (↑roots : Set ℂ) fun ζ η =>
      IsCoprime (Polynomial.X - Polynomial.C ζ)
        (Polynomial.X - Polynomial.C η) := by
    intro ζ hζ η hη hne
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero_of_ne hne).isUnit
  have hinverse (ζ : ℂ) (hζ : ζ ∈ roots) :
      (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
          (Polynomial.X - Polynomial.C ζ))⁻¹ *
        algebraMap (Polynomial ℂ) (PowerSeries ℂ)
          (Polynomial.X - Polynomial.C ζ) = 1 := by
    rw [PowerSeries.inv_mul_cancel]
    simpa [PowerSeries.algebraMap_apply'] using neg_ne_zero.mpr (hrootNonzero ζ hζ)
  obtain ⟨q, r, hr, hpoly⟩ :=
    Polynomial.eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow
      ((-1 : Polynomial ℂ) ^ (d + 1)) hlinearMonic hlinearCoprime
      (sourcePoleOrder d)
  let D : Polynomial ℂ := ∏ ζ ∈ roots,
    (Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ
  let R : Polynomial ℂ := ∑ ζ ∈ roots, ∑ j,
    r ζ j * (Polynomial.X - Polynomial.C ζ) ^ j.1 *
      ∏ η ∈ roots.erase ζ,
        (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η
  have hDMonic : D.Monic := by
    apply Polynomial.monic_prod_of_monic
    intro ζ hζ
    exact (hlinearMonic ζ hζ).pow _
  have hinner (ζ : ℂ) (hζ : ζ ∈ roots) :
      (∑ j, r ζ j * (Polynomial.X - Polynomial.C ζ) ^ j.1).degree <
        ((Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ).degree := by
    refine (Polynomial.degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff ?_).2 fun j _ => ?_)
    · rw [bot_lt_iff_ne_bot, Polynomial.degree_ne_bot]
      exact ((hlinearMonic ζ hζ).pow _).ne_zero
    · refine (Polynomial.degree_mul_le _ _).trans_lt ?_
      rw [Polynomial.degree_eq_natDegree ((hlinearMonic ζ hζ).pow j.1).ne_zero,
        (hlinearMonic ζ hζ).natDegree_pow,
        Polynomial.degree_eq_natDegree ((hlinearMonic ζ hζ).pow _).ne_zero,
        (hlinearMonic ζ hζ).natDegree_pow]
      conv_rhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 j.neZero.ne)]
      rw [Nat.add_one_mul, Nat.add_comm, Nat.cast_add,
        ← Polynomial.degree_eq_natDegree (hlinearMonic ζ hζ).ne_zero]
      refine WithBot.add_lt_add_of_lt_of_le (WithBot.natCast_ne_bot _) (hr ζ hζ j) ?_
      exact Nat.cast_le.2 (Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt j.isLt))
  have hRdegree : R.degree < D.degree := by
    refine (Polynomial.degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff ?_).2 fun ζ hζ => ?_)
    · rw [bot_lt_iff_ne_bot, Polynomial.degree_ne_bot]
      exact hDMonic.ne_zero
    · rw [← Finset.sum_mul, show D = ∏ η ∈ roots,
          (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η from rfl,
        ← Finset.mul_prod_erase roots
          (fun η => (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η) hζ,
        mul_comm ((Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ),
        ((hlinearMonic ζ hζ).pow _).degree_mul]
      refine (Polynomial.degree_mul_le _ _).trans_lt ?_
      have hnotbot :
          (∏ η ∈ roots.erase ζ,
            (Polynomial.X - Polynomial.C η) ^ sourcePoleOrder d η).degree ≠ ⊥ := by
        rw [Polynomial.degree_ne_bot]
        exact (Polynomial.monic_prod_of_monic _ _ fun η hη =>
          (hlinearMonic η (Finset.mem_of_mem_erase hη)).pow _).ne_zero
      rw [add_comm, WithBot.add_lt_add_iff_left hnotbot]
      exact hinner ζ hζ
  have hqDiv : ((-1 : Polynomial ℂ) ^ (d + 1)) /ₘ D = q := by
    apply (Polynomial.div_modByMonic_unique q R hDMonic ⟨?_, hRdegree⟩).1
    dsimp [D, R]
    rw [mul_comm]
    simpa [add_comm] using hpoly.symm
  have hDdegree : 0 < D.natDegree := by
    change 0 < (∏ ζ ∈ roots,
      (Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ).natDegree
    rw [Polynomial.natDegree_prod_of_monic
      (s := roots)
      (f := fun ζ => (Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ)
      (h := fun ζ hζ => (hlinearMonic ζ hζ).pow _)]
    have hone : (1 : ℂ) ∈ roots := Polynomial.one_mem_nthRootsFinset hM
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun ζ _ => Nat.zero_le _) hone)
    rw [(Polynomial.monic_X_sub_C (1 : ℂ)).natDegree_pow,
      Polynomial.natDegree_X_sub_C, Nat.mul_one]
    simp [sourcePoleOrder]
  have hqZero : q = 0 := by
    rw [← hqDiv, Polynomial.divByMonic_eq_zero_iff hDMonic]
    have hnumDegree : ((-1 : Polynomial ℂ) ^ (d + 1)).degree = 0 := by simp
    rw [hnumDegree, Polynomial.degree_eq_natDegree hDMonic.ne_zero]
    exact_mod_cast hDdegree
  have hdecomp :
      sourceRootExpansion d =
        algebraMap (Polynomial ℂ) (PowerSeries ℂ) q + ∑ ζ ∈ roots,
          ∑ j : Fin (sourcePoleOrder d ζ),
          algebraMap (Polynomial ℂ) (PowerSeries ℂ) (r ζ j.rev) *
            (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
              (Polynomial.X - Polynomial.C ζ))⁻¹ ^ (j.1 + 1) := by
    rw [sourceRootExpansion]
    change (-1 : PowerSeries ℂ) ^ (d + 1) *
      ∏ ζ ∈ roots, (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
        (Polynomial.X - Polynomial.C ζ))⁻¹ ^ sourcePoleOrder d ζ = _
    rw [show (-1 : PowerSeries ℂ) ^ (d + 1) =
      algebraMap (Polynomial ℂ) (PowerSeries ℂ)
        ((-1 : Polynomial ℂ) ^ (d + 1)) by simp]
    rw [hpoly, map_add, map_mul, map_prod, add_mul, mul_assoc,
      ← Finset.prod_mul_distrib]
    have hc (ζ : ℂ) (hζ : ζ ∈ roots) :
        algebraMap (Polynomial ℂ) (PowerSeries ℂ)
              ((Polynomial.X - Polynomial.C ζ) ^ sourcePoleOrder d ζ) *
            (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
              (Polynomial.X - Polynomial.C ζ))⁻¹ ^ sourcePoleOrder d ζ = 1 := by
      rw [map_pow, ← mul_pow, mul_comm, hinverse ζ hζ, one_pow]
    rw [Finset.prod_congr rfl hc, Finset.prod_const_one, mul_one, add_right_inj,
      map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ζ hζ => ?_
    rw [map_sum, Finset.sum_mul, ← Equiv.sum_comp Fin.revPerm]
    refine Fintype.sum_congr _ _ fun j => ?_
    rw [Fin.revPerm_apply, map_mul, map_prod, ← Finset.prod_erase_mul roots _ hζ,
      ← mul_rotate', mul_assoc, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl fun η hη => hc η (Finset.mem_of_mem_erase hη),
      Finset.prod_const_one, mul_one, map_mul, map_pow, mul_left_comm]
    refine congrArg (_ * ·) ?_
    rw [← mul_one
        ((algebraMap (Polynomial ℂ) (PowerSeries ℂ)
          (Polynomial.X - Polynomial.C ζ))⁻¹ ^ (j.1 + 1)),
      ← @one_pow (PowerSeries ℂ) _ j.rev, ← hinverse ζ hζ, mul_pow,
      ← mul_assoc, ← pow_add, Fin.val_rev, Nat.add_sub_cancel' (by lia)]
  have hrConstant (ζ : ℂ) (hζ : ζ ∈ roots) (j : Fin (sourcePoleOrder d ζ)) :
      r ζ j = Polynomial.C ((r ζ j).coeff 0) := by
    apply Polynomial.eq_C_of_degree_le_zero
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro n hn
    apply Polynomial.coeff_eq_zero_of_degree_lt
    calc
      (r ζ j).degree < (Polynomial.X - Polynomial.C ζ).degree := hr ζ hζ j
      _ = 1 := Polynomial.degree_X_sub_C ζ
      _ ≤ n := by exact_mod_cast hn
  have hseries :
      sourceRootExpansion d =
        algebraMap (Polynomial ℂ) (PowerSeries ℂ) q +
          ∑ ζ ∈ roots, ∑ j : Fin (sourcePoleOrder d ζ),
            PowerSeries.C ((r ζ j.rev).coeff 0) *
              (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
                (Polynomial.X - Polynomial.C ζ))⁻¹ ^ (j.1 + 1) := by
    calc
      sourceRootExpansion d =
          algebraMap (Polynomial ℂ) (PowerSeries ℂ) q +
            ∑ ζ ∈ roots, ∑ j : Fin (sourcePoleOrder d ζ),
              algebraMap (Polynomial ℂ) (PowerSeries ℂ) (r ζ j.rev) *
                (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
                  (Polynomial.X - Polynomial.C ζ))⁻¹ ^ (j.1 + 1) := by
            simpa [sourceRootExpansion, roots] using hdecomp
      _ = _ := by
        apply congrArg (fun x => algebraMap (Polynomial ℂ) (PowerSeries ℂ) q + x)
        apply Finset.sum_congr rfl
        intro ζ hζ
        apply Fintype.sum_congr
        intro j
        rw [hrConstant ζ hζ j.rev]
        have hmapC (c : ℂ) :
            algebraMap (Polynomial ℂ) (PowerSeries ℂ) (Polynomial.C c) =
              PowerSeries.C c := by
          simp [PowerSeries.algebraMap_apply', PowerSeries.map_id]
        rw [hmapC]
        simp
  let a : (ζ : ℂ) → Fin (sourcePoleOrder d ζ) → ℂ :=
    fun ζ j => (r ζ j.rev).coeff 0
  have haSeries :
      sourceRootExpansion d =
        ∑ ζ ∈ roots, ∑ j,
          PowerSeries.C (a ζ j) *
            (algebraMap (Polynomial ℂ) (PowerSeries ℂ)
              (Polynomial.X - Polynomial.C ζ))⁻¹ ^ (j.1 + 1) := by
    simpa [a, roots, hqZero] using hseries
  have haCoeff (n : ℕ) :
      PowerSeries.coeff n (sourceRootExpansion d) =
        ∑ ζ ∈ roots, ∑ j,
          a ζ j * (-1 : ℂ) ^ (j.1 + 1) *
            (ζ ^ (n + (j.1 + 1)))⁻¹ *
              (Nat.choose (j.1 + n) j.1 : ℂ) := by
    rw [hseries]
    have hcoeffMap (p : Polynomial ℂ) :
        PowerSeries.coeff n
            (algebraMap (Polynomial ℂ) (PowerSeries ℂ) p) = p.coeff n := by
      simp [PowerSeries.algebraMap_apply', PowerSeries.map_id]
    rw [map_add, hcoeffMap, hqZero]
    simp only [map_sum, PowerSeries.coeff_C_mul, Polynomial.coeff_zero, zero_add]
    apply Finset.sum_congr rfl
    intro ζ hζ
    apply Fintype.sum_congr
    intro j
    rw [hprincipalCoeff ζ hζ j.1 n]
    ring
  have heq : sourceRootExpansion d = sourceGeneratingSeries d := by
    have hsource := sourceGeneratingSeries_mul_denominator d hd
    have hroot := sourceRootExpansion_mul_denominator d hd
    calc
      sourceRootExpansion d = 1 * sourceRootExpansion d := (one_mul _).symm
      _ = (sourceGeneratingSeries d *
          algebraMap (Polynomial ℂ) (PowerSeries ℂ) (sourceDenominator d)) *
            sourceRootExpansion d := by rw [hsource]
      _ = sourceGeneratingSeries d *
          (sourceRootExpansion d *
            algebraMap (Polynomial ℂ) (PowerSeries ℂ) (sourceDenominator d)) := by ring
      _ = sourceGeneratingSeries d := by rw [hroot, mul_one]
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · simpa [roots] using haSeries
  · simpa [roots] using haCoeff
  · intro t
    calc
      Rat.castHom ℂ ((baseSamplePolynomial d).eval (t : ℚ)) =
          PowerSeries.coeff (t * M) (sourceRootExpansion d) := by
            rw [heq, sourceGeneratingSeries, PowerSeries.coeff_map,
              coeff_restrictedPartitionSeries_period_eq_eval d t hd]
      _ = _ := haCoeff (t * M)
  · intro t ht
    calc
      Rat.castHom ℂ ((interiorSamplePolynomial d).eval (t : ℚ)) =
          PowerSeries.coeff (t * M - 1) (sourceRootExpansion d) := by
            rw [heq, sourceGeneratingSeries, PowerSeries.coeff_map,
              coeff_restrictedPartitionSeries_period_sub_one_eq_eval d t hd ht]
      _ = _ := haCoeff (t * M - 1)

end D5.S0.FiniteGeometry.SylvesterSimplexEhrhartCoefficient
