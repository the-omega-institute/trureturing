/-
SOURCE_ONLY_UNCOMPILED. Actual source states and all integer module modes.
No spectral, projector, charged-group-law, or classification premise.

Conventions and paper route: sealed answer.txt SHA256 268eb1b46525c501999151966727ec85c86270bbf2927dd472ea15b42c89e79d.
Actual coefficient and translation suppliers retain the Bakalov--Kac,
Carnahan, and Kytölä attribution recorded in their source files.
The original lower-triangular PLUS half-diagonal epsilon is used literally.
-/
import D5.S3.VertexAlgebra.Modules.ActualCurrentTaylor
import D5.S3.VertexAlgebra.LatticeActualStateDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualChargedGroundCalculus

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeSugawaraConformal LatticeSugawaraCurrents
open FullJacobiCurrentTransport ActualCurrentTaylor
open D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock
open StateFieldResidueReconstruction (integerBinomial)

universe u
variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

def groundState (D : LatticeData) (α : Charge D) : Carrier D := Finsupp.single α 1

abbrev E (J : FullJacobiLatticeModule D M) (α : Charge D) (m : ℤ) : Module.End ℂ M :=
  mode J (groundState D α) m

def Hcharge (J : FullJacobiLatticeModule D M) (α : Charge D) (m : ℤ) : Module.End ℂ M :=
  ∑ i, (α i : ℂ) • current J i m

def chargeState (D : LatticeData) (α : Charge D) : Carrier D :=
  ∑ i, (α i : ℂ) • currentState D i

theorem chargeState_mode (J : FullJacobiLatticeModule D M) (α : Charge D) (m : ℤ) :
    mode J (chargeState D α) m = Hcharge J α m := by
  simp [chargeState, Hcharge, mode, current]

/-- Direct original-source computation, including all positive products. -/
theorem source_current_ground (i : Fin D.rank) (α : Charge D) (k : ℕ) :
    sourceProduct D (currentState D i) k (groundState D α) =
      if k = 0 then (bilinear D (unitCharge D i) α : ℂ) • groundState D α else 0 := by
  classical
  rw [sourceProduct, current_state_field, neutralField_ncoeff]
  by_cases hk : k = 0
  · simp [hk, groundState, neutralMode, neutralPolynomialMode, Finsupp.smul_single]
  · simp [hk, groundState, neutralMode, neutralPolynomialMode,
      show ¬ (k : ℤ) < 0 by omega, show (k : ℤ) ≠ 0 by omega]

/-- This identifies Te^alpha with the ACTUAL negative-one source current
product, rather than imposing module translation on M. -/
theorem source_translation_ground (α : Charge D) :
    translation D (groundState D α) =
      sourceProduct D (chargeState D α) (-1) (groundState D α) := by
  classical
  simp [groundState, translation_single, chargePolynomial, chargeState,
    sourceProduct, current_state_field, neutralField_ncoeff,
    neutralMode, neutralPolynomialMode, Finsupp.single_finset_sum,
    Finsupp.smul_single]

/-- Genuine original field coefficient on a pure-charge input. -/
theorem source_ground_product (α β : Charge D) (m : ℤ) :
    sourceProduct D (groundState D α) m (groundState D β) =
      epsilon D α β • Finsupp.single (α + β)
        (creationCoeff D α (-m - 1 - bilinear D α β)) := by
  classical
  rw [sourceProduct, groundState, stateField_ground, actualField,
    VertexOperator.ncoeff_of_coeff]
  change rawCoeff D α (-m - 1) (Finsupp.single β 1) = _
  rw [(actual_creation_coefficient_transport D α α).2.2.1]
  have hs : (1 : Polynomial (Oscillator D)).support = {0} := by
    simpa using Polynomial.support_C (show (1 : Oscillator D) ≠ 0 from one_ne_zero)
  simp [groundState, rawSingle, translatedPolynomial, hs]

theorem source_ground_leading (α β : Charge D) :
    sourceProduct D (groundState D α) (-bilinear D α β - 1) (groundState D β) =
      epsilon D α β • groundState D (α + β) := by
  rw [source_ground_product]
  simp [show -(-bilinear D α β - 1) - 1 - bilinear D α β = 0 by omega,
    creationCoeff, exponential_constant, groundState]

theorem source_ground_above_leading (α β : Charge D) (j : ℕ) (hj : j ≠ 0) :
    sourceProduct D (groundState D α) (-bilinear D α β - 1 + j)
      (groundState D β) = 0 := by
  rw [source_ground_product]
  rw [creationCoeff, dif_pos (by omega)]
  simp

theorem original_epsilon_nonzero (α β : Charge D) : epsilon D α β ≠ 0 := by
  unfold epsilon paritySign
  split_ifs <;> norm_num

theorem original_epsilon_opposite (α : Charge D) :
    epsilon D (-α) α = epsilon D α (-α) := by
  unfold epsilon lowerCocycleExponent
  congr 1
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [Pi.neg_apply]
    ring
  · simp only [Pi.neg_apply]
    ring

variable (J : FullJacobiLatticeModule D M)

/-- All-integer actual current--charge commutator, extracted from r=0. -/
theorem current_E_commutator (i : Fin D.rank) (α : Charge D) (m t : ℤ) :
    current J i m * E J α t - E J α t * current J i m =
      (bilinear D (unitCharge D i) α : ℂ) • E J α (m + t) := by
  classical
  rw [module_mode_commutator, finsum_eq_single _ 0]
  · have hs : sourceProduct D (currentState D i) (0 : ℤ) (groundState D α) =
        (bilinear D (unitCharge D i) α : ℂ) • groundState D α := by
      simpa using source_current_ground i α 0
    simp only [commutatorTerm, Nat.cast_zero, sub_zero]
    rw [hs]
    simp [mode, E, integerBinomial]
  · intro k hk
    simp [commutatorTerm, source_current_ground, hk, mode]

theorem current_E_apply (i : Fin D.rank) (α : Charge D) (m t : ℤ) (v : M) :
    current J i m (E J α t v) = E J α t (current J i m v) +
      (bilinear D (unitCharge D i) α : ℂ) • E J α (m + t) v := by
  have h := LinearMap.congr_fun (current_E_commutator J i α m t) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

theorem charge_current_preserves_Omega (α : Charge D) (v : M) (hv : v ∈ Omega J) :
    Hcharge J α 0 v ∈ Omega J := by
  rw [mem_Omega] at hv ⊢
  intro i r
  simp only [Hcharge, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro j hj
  rw [← WeylData.commute_apply _ _ (zero_current_commutes_current J j i _) v,
    hv i r, map_zero, smul_zero]

/-- Both mixed-Jacobi families are genuinely finite before normal-product
rewriting. This is the p=0, r=-1 specialization of the actual adapter. -/
theorem module_normal_product (a b : Carrier D) (s : ℤ) (v : M) :
    mode J (sourceProduct D a (-1) b) s v =
      (∑ᶠ j : ℕ, mode J a (-1 - j) (mode J b (s + j) v)) +
      (∑ᶠ j : ℕ, mode J b (s - 1 - j) (mode J a j v)) := by
  obtain ⟨hf, hs, h⟩ := module_iterate J a b v (-1) s
  have eh (j : ℕ) := LatticeActualStateFieldCalculus.minus_one_binomial j
  simpa only [jacobiFirst, jacobiSecond, zero_add, eh, one_smul,
    show StateFieldResidueReconstruction.epsilon (-1) = -1 by norm_num
      [StateFieldResidueReconstruction.epsilon], neg_smul, map_neg,
    finsum_neg_distrib, sub_neg_eq_add,
    show ∀ j : ℕ, s + -1 - j = s - 1 - j from fun j => by omega] using h

/-- Explicit finite opposite-charge mixed-Jacobi witness. Its p is an
actual E_-alpha cutoff, never an eigenvalue or spectral hypothesis. -/
theorem opposite_charge_finite_witness (α : Charge D) (q : ℕ)
    (hq : (q : ℤ) = bilinear D α α) (hqpos : 0 < q)
    (p : ℤ) (v : M) (hcut : ∀ n : ℤ, p ≤ n → E J (-α) n v = 0) :
    epsilon D (-α) α • v =
      ∑ j ∈ Finset.range q,
        (((-1 : ℂ)^j) * integerBinomial ((q : ℤ) - 1) j) •
          E J (-α) (p + q - 1 - j) (E J α (-p - 1 + j) v) := by
  classical
  obtain ⟨hl, hf, hs, h⟩ := J.borcherds (groundState D (-α)) (groundState D α)
    v p (-p - 1) ((q : ℤ) - 1)
  have hpair : bilinear D (-α) α = -(q : ℤ) := by
    rw [bilinear_neg_left, ← hq]
  have hsource (j : ℕ) :
      sourceProduct D (groundState D (-α)) ((q : ℤ) - 1 + j) (groundState D α) =
        if j = 0 then epsilon D (-α) α • LatticeAllStateField.vacuum D else 0 := by
    by_cases hj : j = 0
    · subst j
      have hi : (q : ℤ) - 1 + (0 : ℕ) = -bilinear D (-α) α - 1 := by omega
      rw [hi, source_ground_leading]
      simp [groundState, LatticeAllStateField.vacuum]
    · rw [if_neg hj]
      have hi : (q : ℤ) - 1 + (j : ℤ) = -bilinear D (-α) α - 1 + j := by omega
      rw [hi]
      exact source_ground_above_leading (-α) α j hj
  have hleft : (∑ᶠ j : ℕ, jacobiLeft J.stateField
      (groundState D (-α)) (groundState D α) v p (-p - 1) ((q : ℤ) - 1) j) =
        epsilon D (-α) α • v := by
    rw [finsum_eq_single _ 0]
    · have hz := hsource 0
      simp only [Nat.cast_zero, add_zero] at hz
      simp [jacobiLeft, hz, integerBinomial, mode, J.vacuum_field,
        FieldNormalProduct.identityField, VertexOperator.ncoeff_of_coeff,
        show p + (-p - 1) = -1 by omega]
    · intro j hj
      simp [jacobiLeft, hsource, hj, mode]
  have hsecond (j : ℕ) : jacobiSecond J.stateField
      (groundState D (-α)) (groundState D α) v p (-p - 1) ((q : ℤ) - 1) j = 0 := by
    simp [jacobiSecond, hcut (p + j) (by omega), E, mode]
  have hfirst : (∑ᶠ j : ℕ, jacobiFirst J.stateField
      (groundState D (-α)) (groundState D α) v p (-p - 1) ((q : ℤ) - 1) j) =
      ∑ j ∈ Finset.range q,
        (((-1 : ℂ)^j) * integerBinomial ((q : ℤ) - 1) j) •
          E J (-α) (p + q - 1 - j) (E J α (-p - 1 + j) v) := by
    have hfinite : (∑ᶠ j : ℕ, jacobiFirst J.stateField
        (groundState D (-α)) (groundState D α) v p (-p - 1) ((q : ℤ) - 1) j) =
        ∑ j ∈ Finset.range q, jacobiFirst J.stateField
          (groundState D (-α)) (groundState D α) v p (-p - 1) ((q : ℤ) - 1) j := by
      apply finsum_eq_sum_of_support_subset
      intro j hj
      by_contra hout
      have hlarge : q ≤ j := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hout
      have hbin : integerBinomial ((q : ℤ) - 1) j = 0 := by
        unfold integerBinomial
        rw [show (q : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) by omega,
          Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
        simp
      exact hj (by simp [jacobiFirst, hbin])
    rw [hfinite]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [jacobiFirst, E, mode,
      show p + ((q : ℤ) - 1) - j = p + q - 1 - j by omega]
  simp_rw [smul_sub] at h
  change (∑ᶠ j : ℕ, jacobiLeft J.stateField _ _ _ _ _ _ j) =
    ∑ᶠ j : ℕ, (jacobiFirst J.stateField _ _ _ _ _ _ j -
      jacobiSecond J.stateField _ _ _ _ _ _ j) at h
  rw [finsum_sub_distrib hf hs, hleft, hfirst] at h
  simpa only [hsecond, finsum_zero, sub_zero] using h

variable (hNil : OriginalPositiveNilpotence J)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

/-- The actual dressed coefficient on the actual positive-current vacuum. -/
def Z (α : Charge D) (m : ℤ) : Module.End ℂ (Omega J) :=
  (((Pi J hNil H hHG).comp (E J α m)).codRestrict (Omega J)
    (fun v => Pi_mem J hNil H hHG hGH (E J α m v))).comp (Omega J).subtype

@[simp] theorem Z_coe (α : Charge D) (m : ℤ) (v : Omega J) :
    (Z J hNil H hHG hGH α m v : M) = Pi J hNil H hHG (E J α m v) := rfl

def Hzero (α : Charge D) : Module.End ℂ (Omega J) :=
  (Hcharge J α 0).restrict (charge_current_preserves_Omega J α)

@[simp] theorem Hzero_coe (α : Charge D) (v : Omega J) :
    (Hzero J α v : M) = Hcharge J α 0 v := rfl

theorem Pi_Hcharge_zero (α : Charge D) (v : M) :
    Pi J hNil H hHG (Hcharge J α 0 v) =
      Hcharge J α 0 (Pi J hNil H hHG v) := by
  simp only [Hcharge, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [WeylData.commute_apply _ _ (zero_current_commutes_Pi J hNil H hHG i) v]

theorem Pi_Hcharge_negative (α : Charge D) (j : ℕ) (v : M) :
    Pi J hNil H hHG (Hcharge J α (-1 - j) v) = 0 := by
  simp only [Hcharge, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro i hi
  have he : (-1 : ℤ) - j = -(j : ℤ) - 1 := by omega
  rw [he, show current J i (-(j : ℤ) - 1) = creation J i j from rfl,
    Pi_creation, smul_zero]

/-- Exact right zero-mode eigenrelation, derived from the actual source
translation and p=0/r=-1 mixed Jacobi. This is NOT a spectral assumption. -/
theorem Z_Hzero (α : Charge D) (m : ℤ) (v : Omega J) :
    Z J hNil H hHG hGH α m (Hzero J α v) =
      (-(m + 1 : ℤ) : ℂ) • Z J hNil H hHG hGH α m v := by
  classical
  have hnormal := module_normal_product J (chargeState D α) (groundState D α)
    (m + 1) v.val
  rw [← source_translation_ground] at hnormal
  have ht := LinearMap.congr_fun (module_translation_modes J (groundState D α) (m + 1)) v.val
  have hi : m + 1 - 1 = m := by omega
  rw [hi] at ht
  change mode J (translation D (groundState D α)) (m + 1) v.val =
    -((m + 1 : ℤ) : ℂ) • E J α m v.val at ht
  rw [ht] at hnormal
  obtain ⟨hf, hs, _⟩ := module_iterate J (chargeState D α) (groundState D α)
    v.val (-1) (m + 1)
  let f : ℕ → M := fun j => Hcharge J α (-1 - j) (E J α (m + 1 + j) v.val)
  let g : ℕ → M := fun j => E J α (m - j) (Hcharge J α j v.val)
  have ff : Function.HasFiniteSupport f := by
    convert hf using 1
    funext j
    simp [f, jacobiFirst, LatticeActualStateFieldCalculus.minus_one_binomial,
      chargeState_mode, mode]
  have fg : Function.HasFiniteSupport g := by
    apply hs.subset
    intro j hj
    simpa [g, jacobiSecond, LatticeActualStateFieldCalculus.minus_one_binomial,
      StateFieldResidueReconstruction.epsilon, chargeState_mode, mode,
      show ∀ j : ℕ, m + 1 + -1 - j = m - j from fun j => by omega] using hj
  have gn (j : ℕ) (hj : j ≠ 0) : g j = 0 := by
    have hv : Hcharge J α j v.val = 0 := by
      simp only [Hcharge, LinearMap.sum_apply, LinearMap.smul_apply]
      apply Finset.sum_eq_zero
      intro i hi
      have hindex : (j : ℤ) = ((j - 1 : ℕ) : ℤ) + 1 := by omega
      rw [hindex, (mem_Omega J v.val).mp v.property i (j - 1), smul_zero]
    simp [g, hv]
  have fgzero : (∑ᶠ j : ℕ, g j) = E J α m (Hcharge J α 0 v.val) := by
    rw [finsum_eq_single _ 0 gn]
    simp [g]
  have hnormal' : -((m + 1 : ℤ) : ℂ) • E J α m v.val =
      (∑ᶠ j : ℕ, f j) + (∑ᶠ j : ℕ, g j) := by
    simpa only [f, g, chargeState_mode,
      show ∀ j : ℕ, m + 1 - 1 - j = m - j from fun j => by omega] using hnormal
  have hp := congrArg (Pi J hNil H hHG) hnormal'
  rw [map_smul, map_add, map_finsum _ ff, fgzero] at hp
  have hfzero : (∑ᶠ j : ℕ, Pi J hNil H hHG (f j)) = 0 := by
    simp only [f, Pi_Hcharge_negative, finsum_zero]
  rw [hfzero, zero_add] at hp
  apply Subtype.ext
  simpa only [Z_coe, Hzero_coe, Submodule.coe_smul] using hp.symm

/-- Zero-current commutator on Z, for every original basis current. -/
theorem current_zero_Z (i : Fin D.rank) (α : Charge D) (m : ℤ) (v : Omega J) :
    current J i 0 (Z J hNil H hHG hGH α m v : M) =
      Pi J hNil H hHG (E J α m (current J i 0 v.val)) +
        (bilinear D (unitCharge D i) α : ℂ) • (Z J hNil H hHG hGH α m v : M) := by
  rw [Z_coe, WeylData.commute_apply _ _
    (zero_current_commutes_Pi J hNil H hHG i) _, current_E_apply]
  simp only [zero_add, map_add, map_smul, Z_coe]

/-- Single-creator commutation is valid on all M and all integer modes. -/
theorem E_creation (α : Charge D) (s : ℤ) (x : Index D) (v : M) :
    E J α s (creation J x.1 x.2 v) =
      creation J x.1 x.2 (E J α s v) -
        (bilinear D (unitCharge D x.1) α : ℂ) • E J α (s - (x.2 + 1)) v := by
  have h := current_E_apply J x.1 α (-(x.2 : ℤ) - 1) s v
  change creation J x.1 x.2 (E J α s v) =
    E J α s (creation J x.1 x.2 v) + _ at h
  have hi : -(x.2 : ℤ) - 1 + s = s - (x.2 + 1) := by omega
  rw [hi] at h
  exact (eq_sub_iff_add_eq.mpr h.symm)

/-- Actual finite creator words; no positivity of any form on M occurs. -/
def creatorWord : List (Index D) → Module.End ℂ M
  | [] => 1
  | x :: xs => creation J x.1 x.2 * creatorWord xs

def wordWeight : List (Index D) → ℕ
  | [] => 0
  | x :: xs => x.2 + 1 + wordWeight xs

def wordScalar (α : Charge D) : List (Index D) → ℂ
  | [] => 1
  | x :: xs => -(bilinear D (unitCharge D x.1) α : ℂ) * wordScalar α xs

/-- Complete projected finite-word commutation. Every discarded summand
has an ACTUAL creator on the far left and is killed by Pi_creation. -/
theorem Pi_E_creatorWord (α : Charge D) (xs : List (Index D)) (s : ℤ) (v : M) :
    Pi J hNil H hHG (E J α s (creatorWord J xs v)) =
      wordScalar α xs • Pi J hNil H hHG (E J α (s - wordWeight xs) v) := by
  induction xs generalizing s with
  | nil => simp [creatorWord, wordScalar, wordWeight]
  | cons x xs ih =>
    rw [creatorWord, Module.End.mul_apply, E_creation, map_sub, map_smul,
      Pi_creation, zero_sub, ih, ← neg_smul, smul_smul]
    simp only [wordScalar, wordWeight, Nat.cast_add, Nat.cast_one]
    congr 2
    ring

theorem weighted_unit_pairing (γ α : Charge D) :
    (∑ i, (γ i : ℂ) * (bilinear D (unitCharge D i) α : ℂ)) =
      (bilinear D γ α : ℂ) := by
  simp [bilinear, unitCharge, Finset.mul_sum, mul_assoc]

/-- The complete charged zero-current commutator on the actual vacuum. -/
theorem Hzero_Z_commutator (γ α : Charge D) (m : ℤ) (v : Omega J) :
    Hzero J γ (Z J hNil H hHG hGH α m v) =
      Z J hNil H hHG hGH α m (Hzero J γ v) +
        (bilinear D γ α : ℂ) • Z J hNil H hHG hGH α m v := by
  apply Subtype.ext
  change Hcharge J γ 0 (Z J hNil H hHG hGH α m v : M) = _
  rw [Hcharge]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  simp_rw [current_zero_Z J hNil H hHG hGH]
  simp only [smul_add, Finset.sum_add_distrib, smul_smul,
    ← Finset.sum_smul, weighted_unit_pairing]
  simp only [Submodule.coe_add, Submodule.coe_smul, Z_coe, Hzero_coe,
    Hcharge, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]

theorem Hzero_neg (α : Charge D) : Hzero J (-α) = -Hzero J α := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  simp [Hzero_coe, Hcharge, neg_smul, Finset.sum_neg_distrib]

/-- Exact left eigenrelation of a single actual dressed coefficient. -/
theorem Hzero_Z (α : Charge D) (m : ℤ) (v : Omega J) :
    Hzero J α (Z J hNil H hHG hGH α m v) =
      ((bilinear D α α - m - 1 : ℤ) : ℂ) • Z J hNil H hHG hGH α m v := by
  rw [Hzero_Z_commutator, Z_Hzero, ← add_smul]
  congr 1
  push_cast
  ring

theorem Hzero_Z_opposite (α : Charge D) (s : ℤ) (v : Omega J) :
    Hzero J α (Z J hNil H hHG hGH (-α) s v) =
      ((s + 1 - bilinear D α α : ℤ) : ℂ) • Z J hNil H hHG hGH (-α) s v := by
  have h := Hzero_Z J hNil H hHG hGH (-α) s v
  rw [Hzero_neg] at h
  have hnorm : bilinear D (-α) (-α) = bilinear D α α := by
    rw [bilinear_neg_left, bilinear_neg_right, neg_neg]
  rw [hnorm] at h
  have he := congrArg (fun z : Omega J => -z) h
  simp only [LinearMap.neg_apply, neg_neg, ← neg_smul] at he
  rw [he]
  congr 1
  push_cast
  ring

/-- The requested Q is defined by actual charged modes, without any
assertion of resolution, orthogonality, or eigenvalues as input data. -/
def Q (α : Charge D) (a : ℤ) : Module.End ℂ (Omega J) :=
  (epsilon D (-α) α)⁻¹ •
    (Z J hNil H hHG hGH (-α) (bilinear D α α + a - 1) *
      Z J hNil H hHG hGH α (-a - 1))

/-- Both sides of Q are genuine integral eigenrelations, even before
resolution or orthogonality has been proved. -/
theorem Hzero_Q (α : Charge D) (a : ℤ) (v : Omega J) :
    Hzero J α (Q J hNil H hHG hGH α a v) =
      (a : ℂ) • Q J hNil H hHG hGH α a v := by
  simp only [Q, LinearMap.smul_apply, Module.End.mul_apply, map_smul,
    Hzero_Z_opposite]
  have hi : bilinear D α α + a - 1 + 1 - bilinear D α α = a := by omega
  rw [hi, smul_comm]

theorem Q_Hzero (α : Charge D) (a : ℤ) (v : Omega J) :
    Q J hNil H hHG hGH α a (Hzero J α v) =
      (a : ℂ) • Q J hNil H hHG hGH α a v := by
  simp only [Q, LinearMap.smul_apply, Module.End.mul_apply, Z_Hzero, map_smul]
  have hi : -((-a - 1 + 1 : ℤ) : ℂ) = (a : ℂ) := by push_cast; ring
  rw [hi, smul_comm]

/-- This is a consequence of the derived right eigenrelation, and does
not assume semisimplicity or that the given eigenspace spans Omega. -/
theorem Q_kills_other_eigenvector (α : Charge D) (a b : ℤ) (hab : a ≠ b)
    (v : Omega J) (hv : Hzero J α v = (b : ℂ) • v) :
    Q J hNil H hHG hGH α a v = 0 := by
  have h := Q_Hzero J hNil H hHG hGH α a v
  rw [hv, map_smul] at h
  have hs : (b - a : ℂ) • Q J hNil H hHG hGH α a v = 0 := by
    rw [sub_smul, h, sub_self]
  have hn : (b - a : ℂ) ≠ 0 := sub_ne_zero.mpr (by
    intro he
    exact hab (Int.cast_injective he).symm)
  exact (smul_eq_zero.mp hs).resolve_left hn

end D5.S3.VertexAlgebra.Modules.ActualChargedGroundCalculus
