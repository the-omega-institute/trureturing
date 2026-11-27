/- GID: D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Single oscillator reduction on signed fixed charge orbits. -/

import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2GroundCharge

/-!
Single-oscillator charge reduction in the intrinsic fixed lattice C₂ quotient.
The variable X (i, k) is the creation current of index k + 1.
The quadratic calculation follows Step B of the charge-reduction derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.ActualFixedC2

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualStateFieldCalculus LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeSugawaraConformal LatticeActualVertexAlgebra LatticeInvolution LatticePositiveEnergy MvPolynomial
open StateFieldResidueReconstruction (integerBinomial)
open scoped VertexOperator

open private embed jet single_state_field quadratic_pair_as_product
  from D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralMonomials
open private finite_sum_mem from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra
open private derivative_modes derivative_creation
  from D5.S3.VertexAlgebra.LatticeAllStateField
open private E ground Gi Gi_neg neutral_ground charge_contract chargePolynomial_neg mu_add_right
  from D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
open private fixedGroundOrbit_val ground_pairing from D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2GroundCharge

noncomputable section

local instance (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

/-- The fixed state supported on the charge orbit of c with polynomial p at c
and its involute at -c, added at coincident charges. -/
def fixedChargedPolynomial (D : LatticeData) (c : Charge D) (p : Oscillator D) :
    FixedCarrier D :=
  ⟨Finsupp.single c p + Finsupp.single (-c) (sigma D p), by
    rw [mem_fixedSpace, map_add]
    change thetaLinear D (Finsupp.single c p) +
      thetaLinear D (Finsupp.single (-c) (sigma D p)) = _
    rw [theta_single, theta_single, neg_neg, sigma_involutive D p, add_comm]⟩

/-- The fixed oscillator h_i(-k-1)(e^c - e^(-c)). -/
def fixedChargedOscillator (D : LatticeData) (i : Fin D.rank) (k : ℕ) (c : Charge D) :
    FixedCarrier D :=
  fixedChargedPolynomial D c (X (i, k))

@[simp] theorem fixed_charged_oscillator_zero (D : LatticeData) (i : Fin D.rank)
    (c : Charge D) : fixedChargedOscillator D i 0 c = fixedFirstOscillator D i c := by
  apply Subtype.ext
  simp [fixedChargedOscillator, fixedChargedPolynomial, fixedFirstOscillator, sub_eq_add_neg]

private theorem quadratic_iterate (D : LatticeData) (x y : Index D)
    (v : Carrier D) (m : ℤ) :
    let first (j : ℕ) := ((jet D x)[[-(j : ℤ) - 1]])
      (((jet D y)[[m + j]]) v)
    let second (j : ℕ) := ((jet D y)[[m - 1 - (j : ℤ)]])
      (((jet D x)[[j]]) v)
    Function.HasFiniteSupport first ∧ Function.HasFiniteSupport second ∧
      mu D (neutralPair D x.1 y.1 x.2 y.2).val m v =
        (∑ᶠ j, first j) + (∑ᶠ j, second j) := by
  have h := stateField_iterate D (embed D (X x))
    (embed D (X y)) v (-1) m
  dsimp only at h
  simp_rw [show ∀ j : ℕ, (-1 : ℂ)^j * ((Ring.choose (-1) j : ℤ) : ℂ) = 1
    from minus_one_binomial] at h
  rw [quadratic_pair_as_product]
  simpa only [one_smul, show (-1 : ℂ)^(-1 : ℤ) = -1 by norm_num, neg_one_smul,
    sub_neg_eq_add, show ∀ j : ℕ, (-1 : ℤ) - j = -(j : ℤ) - 1 by intro j; omega,
    show ∀ t : ℕ, (-1 : ℤ) + m - t = m - 1 - t by intro t; omega,
    neg_neg, ← single_state_field, mu] using h

private theorem jet_zero_order (D : LatticeData) (i : Fin D.rank) (m : ℤ) :
    ((jet D (i, 0))[[m]]) = neutralMode D i m := by
  rw [derivative_modes]
  simp

private theorem jet_minus_two (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (c : Charge D) (p : Oscillator D) :
    ((jet D (i, k))[[-2]]) (Finsupp.single c p) =
      (k + 1 : ℂ) • Finsupp.single c (X (i, k + 1) * p) := by
  rw [derivative_modes, LinearMap.smul_apply]
  rw [show -(-2 : ℤ) - 1 + (k : ℤ) = ((k + 1 : ℕ) : ℤ) by omega,
    Ring.choose_natCast, Nat.choose_succ_self_right]
  rw [show (-2 : ℤ) - k = -((k + 1 : ℕ) : ℤ) - 1 by omega,
    neutralMode_single, neutralPolynomialMode_negative]
  simp

private theorem jet_on_ground_nonnegative (D : LatticeData) (i : Fin D.rank) (k j : ℕ)
    (c : Charge D) :
    ((jet D (i, k))[[j]]) (ground D c) =
      if j = k then ((-1 : ℂ)^k * Gi D i c) • ground D c else 0 := by
  rw [derivative_modes, LinearMap.smul_apply]
  rcases lt_trichotomy j k with h | rfl | h
  · obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -(j : ℤ) - 1 + k by omega)
    change ((Ring.choose (-(j : ℤ) - 1 + k) k : ℤ) : ℂ) • _ = _
    rw [hr, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (show r < k by omega)]
    simp [h.ne]
  · have hsign : ((Ring.choose (-1 : ℤ) j : ℤ) : ℂ) = (-1 : ℂ)^j := by
      rw [Ring.choose_neg', Ring.multichoose_one]
      simp [Units.smul_def]
    simp only [sub_self, show ∀ t : ℤ,
      -t - 1 + t = -1 by intro t; omega, hsign, ite_true,
      neutral_ground D i c 0 le_rfl, smul_smul]
  · have hp : (0 : ℤ) < (j : ℤ) - k := by omega
    rw [neutral_ground D i c _ hp.le, ite_eq_right hp.ne', smul_zero, ite_eq_right h.ne']

private theorem quadratic_on_charged_ground (D : LatticeData) (i j : Fin D.rank)
    (k : ℕ) (c : Charge D) :
    mu D (neutralPair D i j k 0).val (-1) (ground D c) =
      Finsupp.single c (X (i, k) * X (j, 0)) +
        ((k + 1 : ℂ) * Gi D j c) • Finsupp.single c (X (i, k + 1)) +
        ((-1 : ℂ)^k * Gi D i c) • Finsupp.single c (X (j, k + 1)) := by
  let first (t : ℕ) := ((jet D (i, k))[[-(t : ℤ) - 1]])
    (((jet D (j, 0))[[(-1 : ℤ) + t]]) (ground D c))
  let second (t : ℕ) := ((jet D (j, 0))[[-1 - 1 - (t : ℤ)]])
    (((jet D (i, k))[[t]]) (ground D c))
  obtain ⟨_, _, h⟩ : Function.HasFiniteSupport first ∧ Function.HasFiniteSupport second ∧
      mu D (neutralPair D i j k 0).val (-1) (ground D c) =
        (∑ᶠ t, first t) + (∑ᶠ t, second t) :=
    quadratic_iterate D (i, k) (j, 0) (ground D c) (-1)
  rw [h, finsum_eq_sum_of_support_subset first (s := ({0, 1} : Finset ℕ)),
    finsum_eq_single second k]
  · rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    have h₀ : first 0 = Finsupp.single c (X (i, k) * X (j, 0)) := by
      show ((jet D (i, k))[[-1]]) (((jet D (j, 0))[[-1]]) (Finsupp.single c 1)) = _
      rw [derivative_creation, mul_one, derivative_creation]
    have h₁ : first 1 =
        ((k + 1 : ℂ) * Gi D j c) • Finsupp.single c (X (i, k + 1)) := by
      show ((jet D (i, k))[[-2]]) (((jet D (j, 0))[[0]]) (ground D c)) = _
      rw [jet_zero_order, neutral_ground D j c 0 le_rfl, ite_eq_left rfl,
        map_smul, ground, jet_minus_two, mul_one, smul_smul, mul_comm (Gi D j c)]
    have hk : second k =
        ((-1 : ℂ)^k * Gi D i c) • Finsupp.single c (X (j, k + 1)) := by
      dsimp only [second]
      rw [jet_on_ground_nonnegative, ite_eq_left rfl, jet_zero_order, map_smul, ground,
        show (-1 : ℤ) - 1 - (k : ℤ) = -((k + 1 : ℕ) : ℤ) - 1 by omega,
        neutralMode_single, neutralPolynomialMode_negative, LinearMap.mulLeft_apply, mul_one]
    rw [h₀, h₁, hk]
  · intro t ht
    simp only [second, jet_on_ground_nonnegative, ite_eq_right ht, map_zero]
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hn
    have hp : 0 < (-1 : ℤ) + t := by omega
    have hz : first t = 0 := by
      dsimp only [first]
      rw [jet_zero_order, neutral_ground D j c _ hp.le, ite_eq_right hp.ne', map_zero]
    exact ht hz

/-- The actual fixed quadratic (-1) mode on the invariant charged ground.
The differentiated factor is the first factor in the iterate. -/
theorem fixed_charged_quadratic_product (D : LatticeData) (i j : Fin D.rank)
    (k : ℕ) (c : Charge D) :
    fixedMode D (neutralPair D i j k 0) (-1) (fixedGroundOrbit D c) =
      fixedChargedPolynomial D c (X (i, k) * X (j, 0)) +
      ((k + 1 : ℂ) * Gi D j c) • fixedChargedOscillator D i (k + 1) c +
      ((-1 : ℂ)^k * Gi D i c) • fixedChargedOscillator D j (k + 1) c := by
  apply Subtype.ext
  change mu D (neutralPair D i j k 0).val (-1) (fixedGroundOrbit D c).val = _
  rw [fixedGroundOrbit_val, E, mu_add_right, quadratic_on_charged_ground,
    quadratic_on_charged_ground]
  simp only [fixedChargedOscillator, fixedChargedPolynomial, map_mul, sigma_X,
    neg_mul_neg, Submodule.coe_add, Submodule.coe_smul_of_tower]
  simp only [Gi_neg, mul_neg, neg_smul, Finsupp.single_neg, smul_add, smul_neg]
  abel

/-- Translation of the fixed single oscillator includes the charged
polynomial from the translation of the ground factors. -/
theorem fixed_charged_oscillator_translation (D : LatticeData) (i : Fin D.rank)
    (k : ℕ) (c : Charge D) :
    fixedTranslation D (fixedChargedOscillator D i k c) =
      (k + 1 : ℂ) • fixedChargedOscillator D i (k + 1) c +
      ∑ j : Fin D.rank, (c j : ℂ) • fixedChargedPolynomial D c (X (i, k) * X (j, 0)) := by
  apply Subtype.ext
  change translation D (fixedChargedOscillator D i k c).val =
    (fixedSpace D).subtype ((k + 1 : ℂ) • fixedChargedOscillator D i (k + 1) c +
      ∑ j : Fin D.rank, (c j : ℂ) • fixedChargedPolynomial D c (X (i, k) * X (j, 0)))
  simp only [map_add, map_sum, map_smul, Submodule.subtype_apply,
    fixedChargedOscillator, fixedChargedPolynomial, map_mul, sigma_X, neg_mul_neg,
    Finsupp.single_neg]
  simp only [map_neg, translation_single, oscillatorDerivation,
    MvPolynomial.mkDerivation_X, chargePolynomial_neg, neg_mul,
    Finsupp.single_add, Finsupp.smul_single, smul_add, smul_neg, neg_add_rev]
  simp only [chargePolynomial, Finset.sum_mul, smul_mul_assoc, Finsupp.single_finsetSum]
  rw [Finset.sum_add_distrib]
  simp_rw [mul_comm (X (_, 0) : Oscillator D) (X (i, k))]
  simp only [Finsupp.single_neg, neg_neg, Finsupp.single_finsetSum]
  ac_rfl

/-- The single oscillator in the direction of the charge itself. -/
def fixedChargeDirection (D : LatticeData) (k : ℕ) (c : Charge D) : FixedCarrier D :=
  ∑ i : Fin D.rank, (c i : ℂ) • fixedChargedOscillator D i k c

/-- The sum of actual quadratic modes with second factor in the charge direction. -/
def chargeQuadraticMode (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (c : Charge D) : Module.End ℂ (FixedCarrier D) :=
  ∑ j : Fin D.rank, (c j : ℂ) • fixedMode D (neutralPair D i j k 0) (-1)

/-- The weighted sum is the actual fixed (-1) mode of the weighted quadratic state. -/
theorem charge_quadratic_mode_eq_fixedMode (D : LatticeData) (i : Fin D.rank)
    (k : ℕ) (c : Charge D) :
    chargeQuadraticMode D i k c =
      fixedMode D (∑ j : Fin D.rank, (c j : ℂ) • neutralPair D i j k 0) (-1) := by
  let q (j : Fin D.rank) := neutralPair D i j k 0
  symm
  change ((fixedY D (∑ j : Fin D.rank, (c j : ℂ) • q j))[[-1]]) = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  change (∑ j : Fin D.rank, (c j : ℂ) • ((fixedField D (q j))[[-1]])) = _
  simp only [fixedField_ncoeff, chargeQuadraticMode, q]

private theorem charge_quadratic_mode_ground (D : LatticeData)
    (i : Fin D.rank) (k : ℕ) (c : Charge D) :
    chargeQuadraticMode D i k c (fixedGroundOrbit D c) -
      fixedTranslation D (fixedChargedOscillator D i k c) =
      ((k + 1 : ℂ) * ((bilinear D c c : ℂ) - 1)) • fixedChargedOscillator D i (k + 1) c +
      ((-1 : ℂ)^k * (bilinear D (unitCharge D i) c : ℂ)) •
        fixedChargeDirection D (k + 1) c := by
  have hB :
      (∑ j : Fin D.rank, (c j : ℂ) • ((k + 1 : ℂ) * Gi D j c) •
        fixedChargedOscillator D i (k + 1) c) =
      ((k + 1 : ℂ) * (bilinear D c c : ℂ)) • fixedChargedOscillator D i (k + 1) c := by
    simp_rw [smul_smul, mul_left_comm (c _ : ℂ) (k + 1 : ℂ), ← Finset.sum_smul,
      ← Finset.mul_sum, charge_contract]
  have hp :
      (∑ j : Fin D.rank, (c j : ℂ) • ((-1 : ℂ)^k * Gi D i c) •
        fixedChargedOscillator D j (k + 1) c) =
      ((-1 : ℂ)^k * (bilinear D (unitCharge D i) c : ℂ)) •
        fixedChargeDirection D (k + 1) c := by
    simp_rw [ground_pairing, smul_comm (c _ : ℂ) ((-1 : ℂ)^k * Gi D i c),
      ← Finset.smul_sum, fixedChargeDirection]
  unfold chargeQuadraticMode
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  simp_rw [fixed_charged_quadratic_product, smul_add, Finset.sum_add_distrib]
  rw [hB, hp, fixed_charged_oscillator_translation, mul_sub, mul_one, sub_smul]
  abel

/-- For n = k + 1 the quotient coefficients are n(B - 1) and
(-1)^k times the Gram pairing of the first factor with the charge. -/
theorem fixed_charged_oscillator_recurrence (D : LatticeData)
    (i : Fin D.rank) (k : ℕ) (c : Charge D) :
    (fixedC2 D).mkQ (chargeQuadraticMode D i k c (fixedGroundOrbit D c)) =
      ((k + 1 : ℂ) * ((bilinear D c c : ℂ) - 1)) •
        (fixedC2 D).mkQ (fixedChargedOscillator D i (k + 1) c) +
      ((-1 : ℂ)^k * (bilinear D (unitCharge D i) c : ℂ)) •
        (fixedC2 D).mkQ (fixedChargeDirection D (k + 1) c) := by
  have he := congrArg (fixedC2 D).mkQ (charge_quadratic_mode_ground D i k c)
  have hT := (Submodule.Quotient.mk_eq_zero (p := fixedC2 D)).mpr
    (translation_mem_fixedC2 D (fixedChargedOscillator D i k c))
  simpa only [map_sub, map_add, map_smul, sub_zero, show (fixedC2 D).mkQ
    (fixedTranslation D (fixedChargedOscillator D i k c)) = 0 from hT] using he

theorem charged_direction_coefficient_ne_zero (B : ℤ) (hB : 4 ≤ B) (k : ℕ) :
    (k + 1 : ℂ) * ((B : ℂ) - 1) + (-1 : ℂ)^k * (B : ℂ) ≠ 0 := by
  have hpos : 0 < ((k : ℤ) + 1) * (B - 1) + (-1 : ℤ)^k * B := by
    rcases Nat.even_or_odd k with he | ho
    · rw [he.neg_one_pow, one_mul]
      exact add_pos (mul_pos (by omega) (by omega)) (by omega)
    · rw [ho.neg_one_pow, neg_one_mul]
      have hk : 1 ≤ (k : ℤ) := by exact_mod_cast ho.pos
      nlinarith [mul_nonneg (show 0 ≤ (k : ℤ) - 1 by omega)
        (show 0 ≤ B - 1 by omega)]
  exact_mod_cast hpos.ne'

/-- Over any subspace containing intrinsic C₂, the indicated actual (-1)
products isolate every higher single oscillator when the charge norm is at least four. -/
theorem fixed_higher_oscillator_mem (D : LatticeData) (c : Charge D)
    (hB : 4 ≤ bilinear D c c) (k : ℕ) (S : Submodule ℂ (FixedCarrier D))
    (hC : fixedC2 D ≤ S)
    (hm : ∀ i : Fin D.rank, chargeQuadraticMode D i k c (fixedGroundOrbit D c) ∈ S)
    (i : Fin D.rank) : fixedChargedOscillator D i (k + 1) c ∈ S := by
  let B := (bilinear D c c : ℂ)
  let A := (k + 1 : ℂ) * (B - 1)
  let H := fixedChargeDirection D (k + 1) c
  have hcoeff (j : Fin D.rank) :
      A • fixedChargedOscillator D j (k + 1) c +
        ((-1 : ℂ)^k * Gi D j c) • H ∈ S := by
    have h := S.sub_mem (hm j) (hC (translation_mem_fixedC2 D
      (fixedChargedOscillator D j k c)))
    rw [charge_quadratic_mode_ground, ground_pairing] at h
    exact h
  have hsum := S.sum_mem (t := Finset.univ) fun j _ => S.smul_mem (c j : ℂ) (hcoeff j)
  have leftSum :
      (∑ j : Fin D.rank, (c j : ℂ) • A • fixedChargedOscillator D j (k + 1) c) = A • H := by
    simp_rw [smul_comm (c _ : ℂ) A, ← Finset.smul_sum]
    rfl
  have rightSum :
      (∑ j : Fin D.rank, (c j : ℂ) • ((-1 : ℂ)^k * Gi D j c) • H) =
        ((-1 : ℂ)^k * B) • H := by
    simp_rw [smul_smul, mul_left_comm (c _ : ℂ) ((-1 : ℂ)^k), ← Finset.sum_smul,
      ← Finset.mul_sum, charge_contract]
    rfl
  simp_rw [smul_add, Finset.sum_add_distrib, leftSum, rightSum, ← add_smul] at hsum
  have hd : A + (-1 : ℂ)^k * B ≠ 0 := charged_direction_coefficient_ne_zero _ hB k
  have hH : H ∈ S := by
    simpa only [smul_smul, inv_mul_cancel₀ hd, one_smul] using
      S.smul_mem (A + (-1 : ℂ)^k * B)⁻¹ hsum
  have hsingle := S.sub_mem (hcoeff i) (S.smul_mem ((-1 : ℂ)^k * Gi D i c) hH)
  rw [add_sub_cancel_right] at hsingle
  have hA : A ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast Nat.succ_ne_zero k
    · dsimp [B]
      exact_mod_cast (show bilinear D c c - 1 ≠ 0 by omega)
  simpa only [smul_smul, inv_mul_cancel₀ hA, one_smul] using S.smul_mem A⁻¹ hsingle

/-- Fixed states supported on one charge orbit, including the neutral orbit at zero. -/
def fixedChargeOrbit (D : LatticeData) (c : Charge D) : Submodule ℂ (FixedCarrier D) :=
  (Finsupp.supported (Oscillator D) ℂ ({c, -c} : Set (Charge D))).comap
    (fixedSpace D).subtype

theorem fixed_creation_mem_charge_orbit (D : LatticeData) (a c : Charge D) (r : ℤ) :
    fixedCreationOrbit D a c r ∈ fixedChargeOrbit D c := by
  change Finsupp.single c (creationCoeff D a r) +
    Finsupp.single (-c) (creationCoeff D (-a) r) ∈
    Finsupp.supported (Oscillator D) ℂ ({c, -c} : Set (Charge D))
  exact Submodule.add_mem _ (Finsupp.single_mem_supported ℂ _ (by simp))
    (Finsupp.single_mem_supported ℂ _ (by simp))

private theorem neutral_mode_preserves_support (D : LatticeData) (x : Index D)
    (m : ℤ) (s : Set (Charge D)) (v : Carrier D)
    (hv : v ∈ Finsupp.supported (Oscillator D) ℂ s) :
    ((jet D x)[[m]]) v ∈ Finsupp.supported (Oscillator D) ℂ s := by
  rw [derivative_modes, LinearMap.smul_apply]
  apply Submodule.smul_mem
  have he : neutralMode D x.1 (m - x.2) v =
      ∑ a ∈ v.support, neutralMode D x.1 (m - x.2) (Finsupp.single a (v a)) := by
    rw [← map_sum]
    exact congrArg (neutralMode D x.1 (m - x.2)) (Finsupp.sum_single v).symm
  rw [he]
  apply Submodule.sum_mem
  intro a ha
  rw [neutralMode_single]
  exact Finsupp.single_mem_supported ℂ _ ((Finsupp.mem_supported ℂ v).mp hv ha)

/-- All actual modes of a neutral quadratic preserve each fixed charge orbit. -/
theorem fixed_quadratic_preserves_charge_orbit (D : LatticeData) (x y : Index D)
    (m : ℤ) (c : Charge D) (v : FixedCarrier D) (hv : v ∈ fixedChargeOrbit D c) :
    fixedMode D (neutralPair D x.1 y.1 x.2 y.2) m v ∈ fixedChargeOrbit D c := by
  let s : Set (Charge D) := {c, -c}
  let W := Finsupp.supported (Oscillator D) ℂ s
  change v.val ∈ W at hv
  change mu D (neutralPair D x.1 y.1 x.2 y.2).val m v.val ∈ W
  obtain ⟨hf, hg, he⟩ := quadratic_iterate D x y v.val m
  rw [he]
  refine W.add_mem (finite_sum_mem W _ hf fun j => ?_) (finite_sum_mem W _ hg fun j => ?_)
  · exact neutral_mode_preserves_support D x _ s _ (neutral_mode_preserves_support D y _ s _ hv)
  · exact neutral_mode_preserves_support D y _ s _ (neutral_mode_preserves_support D x _ s _ hv)

private theorem quadratic_mem_c2_sup_orbit (D : LatticeData) (x y : Index D)
    (m : ℤ) (hm : m = 0 ∨ m = -1) (c : Charge D)
    (v : FixedCarrier D) (hv : v ∈ fixedC2 D ⊔ fixedChargeOrbit D c) :
    fixedMode D (neutralPair D x.1 y.1 x.2 y.2) m v ∈ fixedC2 D ⊔ fixedChargeOrbit D c := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  apply Submodule.add_mem
  · apply le_sup_left (b := fixedChargeOrbit D c)
    rcases hm with rfl | rfl
    · exact fixed_zero_mode_mem_c2 D _ _ hu
    · exact fixed_product_mem_c2 D _ _ hu
  · exact le_sup_right (a := fixedC2 D) (fixed_quadratic_preserves_charge_orbit D x y m c w hw)

private theorem first_oscillator_mem_sup_orbit (D : LatticeData) (i : Fin D.rank)
    (c δ : Charge D) (hB : 4 ≤ bilinear D c c)
    (hE : fixedGroundOrbit D c ∈ fixedC2 D ⊔ fixedChargeOrbit D δ) :
    fixedFirstOscillator D i c ∈ fixedC2 D ⊔ fixedChargeOrbit D δ := by
  let S := fixedC2 D ⊔ fixedChargeOrbit D δ
  let v := ∑ j : Fin D.rank, (c j : ℂ) •
    fixedMode D (neutralPair D i j 0 0) 0 (fixedGroundOrbit D c)
  have hv : v ∈ S := S.sum_mem fun j _ => S.smul_mem _ <|
    quadratic_mem_c2_sup_orbit D (i, 0) (j, 0) 0 (Or.inl rfl) δ _ hE
  have he : (fixedC2 D).mkQ v =
      (fixedC2 D).mkQ ((bilinear D c c : ℂ) • fixedFirstOscillator D i c) := by
    simpa only [v, map_sum, map_smul] using fixed_first_oscillator_class D i c
  have hc : (bilinear D c c : ℂ) • fixedFirstOscillator D i c - v ∈ fixedC2 D := by
    apply (Submodule.Quotient.mk_eq_zero (p := fixedC2 D)).mp
    change (fixedC2 D).mkQ (_ - _) = 0
    rw [map_sub, he, sub_self]
  have h := S.add_mem (le_sup_left (b := fixedChargeOrbit D δ) hc) hv
  rw [sub_add_cancel] at h
  have hne : (bilinear D c c : ℂ) ≠ 0 := by
    exact_mod_cast (show bilinear D c c ≠ 0 by omega)
  simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using
    S.smul_mem (bilinear D c c : ℂ)⁻¹ h

/-- A ground reduction into one orbit extends to every single oscillator
by the zero and (-1) modes of actual neutral quadratics. -/
theorem fixed_charged_oscillator_mem_sup_orbit (D : LatticeData) (c δ : Charge D)
    (hB : 4 ≤ bilinear D c c)
    (hE : fixedGroundOrbit D c ∈ fixedC2 D ⊔ fixedChargeOrbit D δ)
    (i : Fin D.rank) (k : ℕ) :
    fixedChargedOscillator D i k c ∈ fixedC2 D ⊔ fixedChargeOrbit D δ := by
  cases k with
  | zero =>
    rw [fixed_charged_oscillator_zero]
    exact first_oscillator_mem_sup_orbit D i c δ hB hE
  | succ k =>
    apply fixed_higher_oscillator_mem D c hB k _ le_sup_left _ i
    intro j
    simp only [chargeQuadraticMode, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ <|
      quadratic_mem_c2_sup_orbit D (j, k) (l, 0) (-1) (Or.inr rfl) δ _ hE

private theorem ground_mem_sup_orbit (D : LatticeData) (a c δ : Charge D) (r : ℤ)
    (h : (fixedC2 D).mkQ (fixedGroundOrbit D c) =
      -(fixedC2 D).mkQ (fixedCreationOrbit D a δ r)) :
    fixedGroundOrbit D c ∈ fixedC2 D ⊔ fixedChargeOrbit D δ := by
  rw [← add_sub_cancel_right (fixedGroundOrbit D c) (fixedCreationOrbit D a δ r)]
  apply Submodule.sub_mem
  · apply le_sup_left (b := fixedChargeOrbit D δ)
    apply (Submodule.Quotient.mk_eq_zero (p := fixedC2 D)).mp
    change (fixedC2 D).mkQ (_ + _) = 0
    rw [map_add, h, neg_add_cancel]
  · exact le_sup_right (a := fixedC2 D) (fixed_creation_mem_charge_orbit D a δ r)

/-- A positive ground pairing reduces every single oscillator to the strictly
smaller orbit in the intrinsic fixed C₂ quotient. -/
theorem fixed_charged_oscillator_two_orbit_reduction (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (a b : Charge D) (hs : 0 < bilinear D a b) (i : Fin D.rank) (k : ℕ) :
    fixedChargedOscillator D i k (a + b) ∈ fixedC2 D ⊔ fixedChargeOrbit D (a - b) := by
  have hlo := chargeEnergy_nonneg D hD (a - b)
  have he := two_chargeEnergy D (a - b)
  have hd := ground_orbit_norm_difference D a b
  have hB : 4 ≤ bilinear D (a + b) (a + b) := by omega
  exact fixed_charged_oscillator_mem_sup_orbit D (a + b) (a - b) hB
    (ground_mem_sup_orbit D _ _ _ _ (fixed_ground_two_orbit_relation D a b hs)) i k

/-- The signed basis step for an outside-short Leech charge works at every
single-oscillator index and chooses the same lower orbit for all indices. -/
theorem leech_fixed_charged_oscillator_step_outside_short (c : Charge ActualLeechHyperbolic.leechData)
    (hc : c ∉ ActualC2Cofinite.shortCharges ActualLeechHyperbolic.leechData) :
    let D := ActualLeechHyperbolic.leechData
    ∃ (i : Fin D.rank) (a : Charge D),
      (a = unitCharge D i ∨ a = -unitCharge D i) ∧
      let δ := c - (2 : ℤ) • a
      (chargeEnergy D δ).toNat < (chargeEnergy D c).toNat ∧
      ∀ (h : Fin D.rank → ℂ) (k : ℕ),
        (∑ j : Fin D.rank, h j • fixedChargedOscillator D j k c) ∈
          fixedC2 D ⊔ fixedChargeOrbit D δ := by
  dsimp only
  let D := ActualLeechHyperbolic.leechData
  obtain ⟨i, a, ha, hs, hground, henergy, hdecrease⟩ :=
    leech_fixed_ground_charge_step_outside_short c hc
  let δ := c - (2 : ℤ) • a
  have hnonneg := chargeEnergy_nonneg D ActualLeechHyperbolic.leech_spec.2.2.1 δ
  have he := two_chargeEnergy D c
  have hB : 4 ≤ bilinear D c c := by
    change 4 ≤ bilinear ActualLeechHyperbolic.leechData c c
    change 0 ≤ chargeEnergy ActualLeechHyperbolic.leechData (c - (2 : ℤ) • a) at hnonneg
    change 2 * chargeEnergy ActualLeechHyperbolic.leechData c =
      bilinear ActualLeechHyperbolic.leechData c c at he
    omega
  refine ⟨i, a, ha, hdecrease, fun h k => Submodule.sum_mem _ fun j _ => ?_⟩
  exact Submodule.smul_mem _ (h j) <|
    fixed_charged_oscillator_mem_sup_orbit D c δ hB (ground_mem_sup_orbit D _ _ _ _ hground) j k

end

end D5.S3.VertexAlgebra.Lattice.ActualFixedC2

#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_charged_oscillator_zero
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_charged_quadratic_product
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_charged_oscillator_translation
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.charge_quadratic_mode_eq_fixedMode
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_charged_oscillator_recurrence
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.charged_direction_coefficient_ne_zero
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_higher_oscillator_mem
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_creation_mem_charge_orbit
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_quadratic_preserves_charge_orbit
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_charged_oscillator_mem_sup_orbit
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_charged_oscillator_two_orbit_reduction
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.leech_fixed_charged_oscillator_step_outside_short
