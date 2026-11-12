/-
SOURCE_ONLY_UNCOMPILED / SOURCE_ONLY_UNACCEPTED

Normalized transport on the original dual-coset carrier and original all-state
action.  No positivity, inverse Gram matrix, classification, or additional
target law is used.  The cocycle is the original half-diagonal cocycle.

The map from the beta + G n sector to the beta sector is
  single l p |-> epsilon D l n • single (l + n) p.
Its inverse is epsilon D (-n) n ^ (-1) • T_(beta + G n,-n).
The normal-word proof below uses literal raw coefficients of dividedDerivative
and the two separately finite families in normalMinusOne.  Vacuum generation
uses the charged mode -sum_i a_i beta_i - 1, followed by negative current modes.

This is a source implementation, without a compiler invocation or native
acceptance claim.  The original research programme remains incomplete.
-/

import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule
import D5.S3.VertexAlgebra.LatticeActualProductKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace D5.S3.VertexAlgebra.LatticeDualCosetTransport

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeDualCosetModule FieldNormalProduct MvPolynomial
open D5.S3.VertexAlgebra.LatticeActualGeneratorLocality
open scoped BigOperators VertexOperator Matrix

-- These are actual private declarations in the sealed original modules.
open private injection_single variable_state_field
  from D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule
open private derivative_zero from D5.S3.VertexAlgebra.LatticeAllStateField

universe u

noncomputable section

/-- The integral Gram shift; no nondegeneracy assumption is needed. -/
def shiftedCharge (D : LatticeData) (β n : Charge D) : Charge D :=
  β + D.G.mulVec n

@[simp] theorem shiftedCharge_zero (D : LatticeData) (β : Charge D) :
    shiftedCharge D β 0 = β := by
  simp [shiftedCharge]

@[simp] theorem shiftedCharge_cancel (D : LatticeData) (β n : Charge D) :
    shiftedCharge D (shiftedCharge D β n) (-n) = β := by
  simp [shiftedCharge, Matrix.mulVec_neg, add_assoc]

private theorem dot_shift (D : LatticeData) (a β n : Charge D) :
    (∑ i, a i * shiftedCharge D β n i) =
      (∑ i, a i * β i) + bilinear D a n := by
  simp only [shiftedCharge, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [bilinear, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem bilinear_input_shift (D : LatticeData) (a l β n : Charge D) :
    bilinear D a (l + n) + (∑ i, a i * β i) =
      bilinear D a l + (∑ i, a i * shiftedCharge D β n i) := by
  rw [bilinear_add_right, dot_shift]
  ring

/-- The cocycle identity in the precise order required by transport. -/
theorem epsilon_transport (D : LatticeData) (l a n : Charge D) :
    epsilon D l n * epsilon D a (l + n) =
      epsilon D a l * epsilon D (a + l) n := by
  simpa only [mul_comm] using epsilon_ordered D a l n

theorem epsilon_opposite (D : LatticeData) (n : Charge D) :
    epsilon D n (-n) = epsilon D (-n) n := by
  unfold epsilon lowerCocycleExponent
  simp only [Pi.neg_apply, mul_neg, neg_mul]

@[simp] theorem epsilon_zero_left (D : LatticeData) (n : Charge D) :
    epsilon D 0 n = 1 := by
  simp [epsilon, lowerCocycleExponent, paritySign]

@[simp] theorem epsilon_zero_right (D : LatticeData) (n : Charge D) :
    epsilon D n 0 = 1 := by
  simp [epsilon, lowerCocycleExponent, paritySign]

private theorem epsilon_nonzero (D : LatticeData) (a b : Charge D) :
    epsilon D a b ≠ 0 := by
  unfold epsilon paritySign
  split_ifs <;> norm_num

/-- The prescribed map on the actual full finite-charge carrier. -/
def transport (D : LatticeData) (β n : Charge D) :
    Carrier D →ₗ[ℂ] Carrier D :=
  Finsupp.lsum ℂ (fun l : Charge D =>
    (epsilon D l n) • (Finsupp.lsingle (l + n)))

@[simp] theorem transport_single (D : LatticeData) (β n l : Charge D)
    (p : Oscillator D) :
    transport D β n (Finsupp.single l p) =
      epsilon D l n • Finsupp.single (l + n) p := by
  simp [transport]

/-- The forward vacuum is literally the prescribed ground vector. -/
theorem transport_vacuum (D : LatticeData) (β n : Charge D) :
    transport D β n (Finsupp.single (0 : Charge D) (1 : Oscillator D)) =
      Finsupp.single n 1 := by
  simp only [transport_single, epsilon_zero_left, one_smul, zero_add]

/-- The inverse includes the indispensable half-diagonal sign. -/
def transportInverse (D : LatticeData) (β n : Charge D) :
    Carrier D →ₗ[ℂ] Carrier D :=
  (epsilon D (-n) n)⁻¹ • transport D (shiftedCharge D β n) (-n)

@[simp] theorem transportInverse_single (D : LatticeData) (β n l : Charge D)
    (p : Oscillator D) :
    transportInverse D β n (Finsupp.single l p) =
      ((epsilon D (-n) n)⁻¹ * epsilon D l (-n)) •
        Finsupp.single (l - n) p := by
  simp only [transportInverse, LinearMap.smul_apply, transport_single,
    smul_smul, sub_eq_add_neg]

private theorem inverse_cocycle_left (D : LatticeData) (l n : Charge D) :
    (epsilon D (-n) n)⁻¹ *
      (epsilon D l n * epsilon D (l + n) (-n)) = 1 := by
  rw [← epsilon_ordered, add_neg_cancel, epsilon_zero_right, one_mul,
    epsilon_opposite, inv_mul_cancel₀ (epsilon_nonzero D (-n) n)]

private theorem inverse_cocycle_right (D : LatticeData) (l n : Charge D) :
    (epsilon D (-n) n)⁻¹ *
      (epsilon D l (-n) * epsilon D (l - n) n) = 1 := by
  rw [sub_eq_add_neg, ← epsilon_ordered, neg_add_cancel,
    epsilon_zero_right, one_mul, inv_mul_cancel₀ (epsilon_nonzero D (-n) n)]

theorem transportInverse_left (D : LatticeData) (β n : Charge D) :
    (transportInverse D β n).comp (transport D β n) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro l p
  simp only [LinearMap.comp_apply, transport_single, transportInverse_single,
    map_smul, smul_smul, sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero,
    LinearMap.id_apply]
  have hs : epsilon D l n *
      ((epsilon D (-n) n)⁻¹ * epsilon D (l + n) (-n)) = 1 := by
    calc
      _ = (epsilon D (-n) n)⁻¹ *
          (epsilon D l n * epsilon D (l + n) (-n)) := by ring
      _ = 1 := inverse_cocycle_left D l n
  rw [hs, one_smul]

theorem transportInverse_right (D : LatticeData) (β n : Charge D) :
    (transport D β n).comp (transportInverse D β n) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro l p
  simp only [LinearMap.comp_apply, transportInverse_single, transport_single,
    map_smul, smul_smul, sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero,
    LinearMap.id_apply]
  rw [mul_assoc]
  have hs := inverse_cocycle_right D l n
  simp only [sub_eq_add_neg] at hs
  rw [hs, one_smul]

@[simp] theorem transport_zero (D : LatticeData) (β : Charge D) :
    transport D β 0 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro l p
  simp [transport_single]

@[simp] theorem transportInverse_zero (D : LatticeData) (β : Charge D) :
    transportInverse D β 0 = LinearMap.id := by
  simp [transportInverse]

/-- The actual linear equivalence; its all-state action law is proved below. -/
def transportLinearEquiv (D : LatticeData) (β n : Charge D) :
    Carrier D ≃ₗ[ℂ] Carrier D where
  toLinearMap := transport D β n
  invFun := transportInverse D β n
  left_inv v := by
    have h := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v)
      (transportInverse_left D β n)
    exact h
  right_inv v := by
    have h := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v)
      (transportInverse_right D β n)
    exact h

private theorem shiftedCurrentPolynomial_shift (D : LatticeData) (β n l : Charge D)
    (i : Fin D.rank) (m : ℤ) :
    shiftedCurrentPolynomial D (shiftedCharge D β n) 1 i l m =
      shiftedCurrentPolynomial D β 1 i (l + n) m := by
  have hz : bilinear D (unitCharge D i) l + shiftedCharge D β n i =
      bilinear D (unitCharge D i) (l + n) + β i := by
    simpa [unitCharge] using (bilinear_input_shift D (unitCharge D i) l β n).symm
  by_cases hm : m < 0
  · simp [shiftedCurrentPolynomial, hm]
  · by_cases h0 : m = 0
    · simp only [shiftedCurrentPolynomial, hm, h0, ↓reduceIte, one_mul, hz]
    · simp [shiftedCurrentPolynomial, hm, h0]

private theorem transport_current_single (D : LatticeData) (β n : Charge D)
    (i : Fin D.rank) (l : Charge D) (p : Oscillator D) (m : ℤ) :
    transport D β n
        (((action D (shiftedCharge D β n)
          (Finsupp.single (0 : Charge D) (X (i, 0))))[[m]]) (Finsupp.single l p)) =
      ((action D β (Finsupp.single (0 : Charge D) (X (i, 0))))[[m]])
        (transport D β n (Finsupp.single l p)) := by
  rw [action_current_coefficients, transport_single, transport_single,
    map_smul, action_current_coefficients, shiftedCurrentPolynomial_shift]

/-- Every current mode intertwines on every full input, before word induction. -/
theorem transport_current_mode (D : LatticeData) (β n : Charge D)
    (i : Fin D.rank) (m : ℤ) (v : Carrier D) :
    transport D β n
        (((action D (shiftedCharge D β n)
          (Finsupp.single (0 : Charge D) (X (i, 0))))[[m]]) v) =
      ((action D β (Finsupp.single (0 : Charge D) (X (i, 0))))[[m]])
        (transport D β n v) := by
  have h : (transport D β n).comp
        ((action D (shiftedCharge D β n)
          (Finsupp.single (0 : Charge D) (X (i, 0))))[[m]]) =
      ((action D β (Finsupp.single (0 : Charge D) (X (i, 0))))[[m]]).comp
        (transport D β n) := by
    apply Finsupp.lhom_ext
    intro l p
    exact transport_current_single D β n i l p m
  exact congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v) h

private theorem transport_ground_single (D : LatticeData) (β n : Charge D)
    (a l : Charge D) (p : Oscillator D) (m : ℤ) :
    transport D β n
        (((action D (shiftedCharge D β n)
          (Finsupp.single a (1 : Oscillator D)))[[m]]) (Finsupp.single l p)) =
      ((action D β (Finsupp.single a (1 : Oscillator D)))[[m]])
        (transport D β n (Finsupp.single l p)) := by
  have hind (d : ℕ) :
      -m - 1 - bilinear D a l - (∑ i, a i * shiftedCharge D β n i) + d =
        -m - 1 - bilinear D a (l + n) - (∑ i, a i * β i) + d := by
    have h := bilinear_input_shift D a l β n
    omega
  rw [action_ground_coefficients, transport_single, map_smul,
    action_ground_coefficients]
  simp only [shiftedRawSingle, one_mul, map_smul, transport_single, smul_smul]
  simp_rw [hind]
  rw [epsilon_transport D l a n, add_assoc]

/-- Every charged mode intertwines on every full input. -/
theorem transport_ground_mode (D : LatticeData) (β n a : Charge D)
    (m : ℤ) (v : Carrier D) :
    transport D β n
        (((action D (shiftedCharge D β n)
          (Finsupp.single a (1 : Oscillator D)))[[m]]) v) =
      ((action D β (Finsupp.single a (1 : Oscillator D)))[[m]])
        (transport D β n v) := by
  have h : (transport D β n).comp
        ((action D (shiftedCharge D β n) (Finsupp.single a (1 : Oscillator D)))[[m]]) =
      ((action D β (Finsupp.single a (1 : Oscillator D)))[[m]]).comp
        (transport D β n) := by
    apply Finsupp.lhom_ext
    intro l p
    exact transport_ground_single D β n a l p m
  exact congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v) h

private theorem action_ground_field (D : LatticeData) (β a : Charge D) :
    action D β (Finsupp.single a (1 : Oscillator D)) =
      compress D β 1 (actualField (auxiliary D β) (liftCharge D β 0 a)) := by
  change compress D β 1 (Y (auxiliary D β)
    (injection D β 0 (Finsupp.single a (1 : Oscillator D)))) = _
  rw [injection_single, map_one, stateField_ground]

private theorem action_current_field (D : LatticeData) (β : Charge D)
    (i : Fin D.rank) :
    action D β (Finsupp.single (0 : Charge D) (X (i, 0))) =
      compress D β 1 (neutralField (auxiliary D β) i.castSucc) := by
  have hz : liftCharge D β 0 0 = 0 := by
    funext j
    induction j using Fin.lastCases <;> simp [liftCharge]
  have hj : injection D β 0 (Finsupp.single (0 : Charge D) (X (i, 0))) =
      Finsupp.single (0 : Charge (auxiliary D β)) (X (i.castSucc, 0)) := by
    simp [injection_single, hz, polynomialInjection, liftIndex]
  change compress D β 1 (Y (auxiliary D β) _) = _
  rw [hj, variable_state_field, derivative_zero]

/-- Raw coefficient -m-1+k converts to mode m-k, with an integer binomial. -/
private theorem intertwines_dividedDerivative (D : LatticeData)
    (T : Carrier D →ₗ[ℂ] Carrier D) (A B : VertexOperator ℂ (Carrier D))
    (h : ∀ (m : ℤ) (v : Carrier D), T ((A[[m]]) v) = (B[[m]]) (T v))
    (k : ℕ) (m : ℤ) (v : Carrier D) :
    T (((dividedDerivative k A)[[m]]) v) =
      ((dividedDerivative k B)[[m]]) (T v) := by
  change T (Ring.choose (-m - 1 + k) k •
      HVertexOperator.coeff A (-m - 1 + k) v) =
    Ring.choose (-m - 1 + k) k •
      HVertexOperator.coeff B (-m - 1 + k) (T v)
  rw [map_zsmul, VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    show -(-m - 1 + (k : ℤ)) - 1 = m - k by omega, h]

/-- Both normal-product families are mapped using their own actual truncation. -/
private theorem intertwines_normalMinusOne (D : LatticeData)
    (T : Carrier D →ₗ[ℂ] Carrier D)
    (A A' B B' : VertexOperator ℂ (Carrier D))
    (hA : ∀ (m : ℤ) (v : Carrier D), T ((A[[m]]) v) = (B[[m]]) (T v))
    (hA' : ∀ (m : ℤ) (v : Carrier D), T ((A'[[m]]) v) = (B'[[m]]) (T v))
    (m : ℤ) (v : Carrier D) :
    T (((normalMinusOne A A').1[[m]]) v) =
      ((normalMinusOne B B').1[[m]]) (T v) := by
  classical
  have finiteFirst : Function.HasFiniteSupport (fun j : ℕ =>
      (A[[-(j : ℤ) - 1]]) ((A'[[m + j]]) v)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (A' v)).order - m).toNat, ?_⟩
    intro j hj
    contrapose! hj
    have hv : (A'[[m + j]]) v = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [hv]
  have finiteSecond : Function.HasFiniteSupport (fun j : ℕ =>
      (A'[[m - j - 1]]) ((A[[j]]) v)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (A v)).order - 1).toNat, ?_⟩
    intro j hj
    contrapose! hj
    have hv : (A[[j]]) v = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [hv]
  rw [(normalMinusOne A A').2, (normalMinusOne B B').2, map_add,
    map_finsum _ finiteFirst, map_finsum _ finiteSecond]
  congr 1 <;> apply finsum_congr <;> intro j
  · rw [hA, hA']
  · rw [hA', hA]

private theorem word_transport_induction (D : LatticeData) (β n l : Charge D)
    (w : List (Index D)) :
    ∀ (m : ℤ) (v : Carrier D),
      transport D β n (((shiftedWord D (shiftedCharge D β n) l w)[[m]]) v) =
        ((shiftedWord D β l w)[[m]]) (transport D β n v) := by
  induction w with
  | nil =>
    intro m v
    rw [shiftedWord, shiftedWord, ← action_ground_field, ← action_ground_field]
    exact transport_ground_mode D β n l m v
  | cons x w ih =>
    intro m v
    rw [shiftedWord, shiftedWord]
    apply intertwines_normalMinusOne D (transport D β n)
    · intro j z
      apply intertwines_dividedDerivative D (transport D β n)
      intro r y
      rw [← action_current_field, ← action_current_field]
      exact transport_current_mode D β n x.1 r y
    · exact ih

/-- Full transport: all original states, every integer mode, every full input. -/
theorem transport_all_modes (D : LatticeData) (β n : Charge D)
    (a v : Carrier D) (m : ℤ) :
    transport D β n (((action D (shiftedCharge D β n) a)[[m]]) v) =
      ((action D β a)[[m]]) (transport D β n v) := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, ha, hb]
  | single l p =>
    induction p using MvPolynomial.induction_on' with
    | add p q hp hq =>
      simp only [map_add, Finsupp.single_add, Pi.add_apply,
        LinearMap.add_apply, hp, hq]
    | monomial e c =>
      have hc : monomial e c = c • (monomial e 1 : Oscillator D) := by
        rw [smul_monomial]
        simp only [smul_eq_mul, mul_one]
      rw [hc, ← Finsupp.smul_single]
      simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]
      congr 1
      rw [action_monomial, action_monomial]
      exact word_transport_induction D β n l (occurrences D e) m v

/-- The explicit inverse also intertwines all original states and integer modes. -/
theorem transportInverse_all_modes (D : LatticeData) (β n : Charge D)
    (a v : Carrier D) (m : ℤ) :
    transportInverse D β n (((action D β a)[[m]]) v) =
      ((action D (shiftedCharge D β n) a)[[m]]) (transportInverse D β n v) := by
  have h := transport_all_modes D (shiftedCharge D β n) (-n) a v m
  rw [shiftedCharge_cancel] at h
  simpa only [transportInverse, LinearMap.smul_apply, map_smul] using
    congrArg (fun z : Carrier D => (epsilon D (-n) n)⁻¹ • z) h

/-- The normalized leading-ground S formula, without choosing any mode. -/
theorem leading_ground_S_normalization (D : LatticeData) (β n a l : Charge D)
    (m : ℤ) :
    transport D β n
        (((action D (shiftedCharge D β n)
          (Finsupp.single a (1 : Oscillator D)))[[m]]) (Finsupp.single l 1)) =
      epsilon D l n •
        (((action D β (Finsupp.single a (1 : Oscillator D)))[[m]])
          (Finsupp.single (l + n) 1)) := by
  rw [transport_ground_mode, transport_single, map_smul]

/-- Charged generation from the exact vacuum uses -a.dot.beta-1. -/
theorem source_ground_vacuum (D : LatticeData) (β a : Charge D) :
    ((action D β (Finsupp.single a (1 : Oscillator D)))
        [[-(∑ i, a i * β i) - 1]])
        (Finsupp.single (0 : Charge D) (1 : Oscillator D)) =
      Finsupp.single a 1 := by
  classical
  rw [action_ground_coefficients]
  have ht : translatedPolynomial D a (1 : Oscillator D) = 1 := by
    simp [translatedPolynomial]
  have hs : (1 : Polynomial (Oscillator D)).support = {0} := by
    simpa using Polynomial.support_C
      (show (1 : Oscillator D) ≠ 0 from one_ne_zero)
  have hm : -(-(∑ i, a i * β i) - 1) - 1 = (∑ i, a i * β i) := by omega
  simp only [shiftedRawSingle, ht, hs, Finset.sum_singleton]
  rw [hm]
  simp [bilinear, epsilon_zero_right, creationCoeff,
    LatticeSugawaraConformal.exponential_constant]

theorem source_current_negative_variable (D : LatticeData) (β l : Charge D)
    (p : Oscillator D) (i : Fin D.rank) (k : ℕ) :
    ((action D β (Finsupp.single (0 : Charge D) (X (i, 0))))[[-(k : ℤ) - 1]])
        (Finsupp.single l p) = Finsupp.single l (X (i, k) * p) := by
  rw [action_current_coefficients]
  simp [shiftedCurrentPolynomial, show -(k : ℤ) - 1 < 0 by omega,
    show -(-(k : ℤ) - 1) - 1 = (k : ℤ) by omega]

/-- Actual vacuum cyclicity as induction under all the original sector modes. -/
theorem vacuum_mode_induction (D : LatticeData) (β : Charge D)
    (P : Carrier D → Prop) (hzero : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : ℂ) x, P x → P (c • x))
    (hmode : ∀ (a : Carrier D) (m : ℤ) (x : Carrier D),
      P x → P (((action D β a)[[m]]) x))
    (hvac : P (Finsupp.single (0 : Charge D) (1 : Oscillator D)))
    (v : Carrier D) : P v := by
  have hground (a : Charge D) : P (Finsupp.single a (1 : Oscillator D)) := by
    rw [← source_ground_vacuum D β a]
    exact hmode _ _ _ hvac
  have hpoly (a : Charge D) (p : Oscillator D) : P (Finsupp.single a p) := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      have hc : (C c : Oscillator D) = c • (1 : Oscillator D) := by
        simp [MvPolynomial.smul_eq_C_mul]
      rw [hc, ← Finsupp.smul_single]
      exact hsmul c _ (hground a)
    | add p q hp hq =>
      rw [Finsupp.single_add]
      exact hadd _ _ hp hq
    | mul_X p x hp =>
      have hgen :
          ((action D β (Finsupp.single (0 : Charge D) (X (x.1, 0))))
              [[-(x.2 : ℤ) - 1]]) (Finsupp.single a p) =
            Finsupp.single a (p * X x) := by
        simpa only [Prod.mk.eta, mul_comm] using
          source_current_negative_variable D β a p x.1 x.2
      rw [← hgen]
      exact hmode _ _ _ hp
  induction v using Finsupp.induction_linear with
  | zero => exact hzero
  | add x y hx hy => exact hadd x y hx hy
  | single a p => exact hpoly a p

/-- Full actual intertwiners into any independent-universe target are determined
by the exact vacuum value.  The target only supplies its actual mode action. -/
theorem modeHom_ext_of_vacuum (D : LatticeData) (β : Charge D)
    {M : Type u} [AddCommGroup M] [Module ℂ M]
    (target : Carrier D → ℤ → Module.End ℂ M)
    (f g : Carrier D →ₗ[ℂ] M)
    (hf : ∀ (a : Carrier D) (m : ℤ) (v : Carrier D),
      f (((action D β a)[[m]]) v) = target a m (f v))
    (hg : ∀ (a : Carrier D) (m : ℤ) (v : Carrier D),
      g (((action D β a)[[m]]) v) = target a m (g v))
    (h0 : f (Finsupp.single (0 : Charge D) (1 : Oscillator D)) =
      g (Finsupp.single (0 : Charge D) (1 : Oscillator D))) : f = g := by
  apply LinearMap.ext
  intro v
  apply vacuum_mode_induction D β (fun x => f x = g x)
  · simp only [map_zero]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro c x hx
    simp only [map_smul, hx]
  · intro a m x hx
    rw [hf, hg, hx]
  · exact h0

end
end D5.S3.VertexAlgebra.LatticeDualCosetTransport
