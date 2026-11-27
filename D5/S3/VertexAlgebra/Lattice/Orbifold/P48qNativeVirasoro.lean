import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeResidueIterate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalZero
import D5.S3.VertexAlgebra.LatticeActualConformalWard
import D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
import D5.S3.VertexAlgebra.LatticeActualVertexAlgebra

/-!
The invariant conformal state of the native P48q twisted field gives
Virasoro operators on the full native Fock carrier. The two residue
specializations are Bakalov–Kac, arXiv:math/0402315v3, equation (3.7).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeVirasoro

open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeActualConformalState (omega omega_modes)
open LatticeActualConformalWard (omega_product)
open LatticeAllStateField (Y vacuum stateField_creation stateField_creativity)
open LatticeAllStateReconstruction (mu)
open LatticeGeneratingFieldLocality (Carrier LatticeData)
open LatticeSugawaraCurrents (sugawaraMode gramComplex)
open LatticeSugawaraConformal (translation sugawaraMode_minus_one_eq_translation)
open LatticeActualVertexAlgebra (translation_as_mode)
open LatticeSugawaraVirasoro (sugawaraMode_virasoro)
open NativeStandardThirdLift (standardLift standardLift_compatible standardLift_omega)
open P48qAllJetWickField (NativeStates nativeField nativeField_ground)
open P48qNativeConformalZero (native_conformal_coeff_neg_six_eq_totalLZero)
open P48qNativeCurrentLocality (Field stripResidue stripResidue_coeff nativeField_inResidue
  coverDelta coverComm)
open P48qNativePairwiseLocality (nativeField_pairwise_locality)
open P48qNativeResidueIterate (nativeField_twisted_borcherds adjustedResidue_twisted_borcherds
  adjustedResidue_eigenstate_first)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qTwistedGeneratorVacuum (concreteChargedField_zero_coeff)
open P48qTwistedStateEnergy (totalLZero)
open SignedFieldResidueLocality (residueField residueCoefficient residueLeft residueRight negativeResidue)
open FieldNormalProduct (dividedDerivative)
open SignedFieldNormalProductLocality (signedNormalMinusOne)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private deltaCoverEnd coverOrder_mono ordinary_residue_mode from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality
open private cover_mono from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeResidueIterate

noncomputable section

local notation "Ω" => omega lattice (actualInverse lattice)
local notation "vac" => vacuum lattice
local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "C" => HVertexOperator.coeff

private theorem strip_mode (s : ℤ) (A : Field) (i : ℤ) :
    (stripResidue s A)[[i]] = C A (s - 3 * (i + 1)) := by
  simp only [VertexOperator.ncoeff_apply, stripResidue_coeff]
  rw [show 3 * (-i - 1) + s = s - 3 * (i + 1) by omega]

private theorem vacuum_coeff (k : ℤ) :
    C (nativeField vac) k = if k = 0 then (1 : Module.End ℂ State) else 0 := by
  rw [vacuum, nativeField_ground]
  exact concreteChargedField_zero_coeff k

private theorem vacuum_mode (q : ℤ) :
    (stripResidue 0 (nativeField vac))[[q]] =
      if q = -1 then (1 : Module.End ℂ State) else 0 := by
  simp only [strip_mode, vacuum_coeff, show (0 : ℤ) - 3 * (q + 1) = 0 ↔ q = -1 by omega]

private theorem residue_minus_two_identity_right_mode
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : VertexOperator ℂ V)
    (hB : ∀ i : ℤ, B[[i]] = if i = -1 then LinearMap.id else 0) (q : ℤ) :
    ((residueField 1 (-2) A B).operator)[[q]] = -(q : ℂ) • A[[q - 1]] := by
  rw [show (-2 : ℤ) = -(↑(1 : ℕ) : ℤ) - 1 by norm_num, negativeResidue]
  apply LinearMap.ext
  intro v
  trans ((dividedDerivative 1 A)[[q]]) v
  · rw [(signedNormalMinusOne 1 (dividedDerivative 1 A) B).2, one_smul]
    by_cases hq : q < 0
    · have rightZero (j : ℕ) : q - j - 1 ≠ (-1 : ℤ) := by omega
      simp only [hB, rightZero, ite_false, LinearMap.zero_apply, finsum_zero, add_zero]
      let n := (-q - 1).toNat
      have hn : (n : ℤ) = -q - 1 := Int.toNat_of_nonneg (by omega)
      have index : q + (n : ℤ) = -1 := by omega
      have mode : -(n : ℤ) - 1 = q := by omega
      rw [finsum_eq_single _ n]
      · rw [ite_eq_left index, LinearMap.id_apply, mode]
      · intro j hj
        have miss : q + (j : ℤ) ≠ -1 := by omega
        simp [miss]
    · have leftZero (j : ℕ) : q + j ≠ (-1 : ℤ) := by omega
      simp only [hB, leftZero, ite_false, LinearMap.zero_apply, map_zero,
        finsum_zero, zero_add]
      let n := q.toNat
      have mode : (n : ℤ) = q := Int.toNat_of_nonneg (by omega)
      have index : q - (n : ℤ) - 1 = -1 := by omega
      rw [finsum_eq_single _ n]
      · rw [ite_eq_left index, LinearMap.id_apply, mode]
      · intro j hj
        have miss : q - (j : ℤ) - 1 ≠ -1 := by omega
        simp [miss]
  · change Ring.choose (-q - 1 + 1) 1 • HVertexOperator.coeff A (-q - 1 + 1) v = _
    rw [Ring.choose_one_right, VertexOperator.coeff_eq_ncoeff,
      show -(-q - 1 + 1) - 1 = q - 1 by omega, ← Int.cast_smul_eq_zsmul ℂ]
    simp only [sub_add_cancel, Int.cast_neg, LinearMap.smul_apply]

/-- The vacuum minus-two product differentiates the native field at physical
mode `q - s / 3` for every state of lift eigenvalue `ζ ^ s`. -/
theorem native_vacuum_minus_two_fractional_mode (a : NativeStates) (s : ℤ)
    (ha : σ a = ζ ^ s • a) (q : ℤ) :
    C (nativeField (mu lattice a (-2) vac)) (s - 3 * (q + 1)) =
      -((q : ℂ) - (s : ℂ) / 3) • C (nativeField a) (s - 3 * q) := by
  have hv : σ vac = ζ ^ (0 : ℤ) • vac := by
    simpa only [zpow_zero, one_smul] using (standardLift_compatible lattice g g_cube g_isometry).1
  obtain ⟨N, hN⟩ := nativeField_twisted_borcherds a vac s 0 ha hv
  let term (j : ℕ) := Ring.choose (-((s : ℂ) / 3)) j •
    C (nativeField (mu lattice a (-2 + (j : ℤ)) vac)) (s - 3 * (q - (j : ℤ) + 1))
  have h := hN 0 q (-2)
  simp only [Int.cast_zero, zero_sub, add_zero, zero_add] at h
  rw [show s - 3 * 0 = s by omega] at h
  change _ = ∑ j ∈ Finset.range ((N : ℤ) - (-2)).toNat, term j at h
  have hsum :
      (∑ j ∈ Finset.range 2, term j) =
        ∑ j ∈ Finset.range ((N : ℤ) - (-2)).toNat, term j := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    have hj' : 0 ≤ (-2 : ℤ) + (j : ℤ) := by
      rw [Finset.mem_range, not_lt] at hj
      omega
    change term j = 0
    have hz : mu lattice a (-2 + (j : ℤ)) vac = 0 :=
      stateField_creativity lattice a _ hj'
    simp only [term, hz, map_zero, Pi.zero_apply, smul_zero]
  rw [residue_minus_two_identity_right_mode _ _ vacuum_mode, strip_mode,
    show s - 3 * (q - 1 + 1) = s - 3 * q by omega, ← hsum] at h
  have hcreate : mu lattice a (-1) vac = a := stateField_creation lattice a
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, term,
    Ring.choose_zero_right, Ring.choose_one_right, one_smul, Nat.cast_zero, Nat.cast_one,
    add_zero, sub_zero, show (-2 : ℤ) + 1 = -1 by decide, hcreate,
    show s - 3 * (q - 1 + 1) = s - 3 * q by omega] at h
  rw [eq_sub_of_add_eq h.symm, ← sub_smul]
  congr 1
  ring

private theorem vacuum_minus_two_residue_mode (a : NativeStates) (q : ℤ) :
    ((residueField 1 (-2) (stripResidue 0 (nativeField a))
      (stripResidue 0 (nativeField vac))).operator)[[q]] =
      -(q : ℂ) • (stripResidue 0 (nativeField a))[[q - 1]] := by
  exact residue_minus_two_identity_right_mode _ _ vacuum_mode q

/-- The vacuum minus-two product differentiates the native field in the
physical variable at every integral mode of a lift-invariant state. -/
theorem native_vacuum_minus_two_mode (a : NativeStates) (ha : σ a = a) (q : ℤ) :
    C (nativeField (mu lattice a (-2) vac)) (-3 * (q + 1)) =
      -(q : ℂ) • C (nativeField a) (-3 * q) := by
  have ha₀ : σ a = ζ ^ (0 : ℤ) • a := by simpa only [zpow_zero, one_smul] using ha
  have hv₀ : σ vac = ζ ^ (0 : ℤ) • vac := by
    simpa only [zpow_zero, one_smul] using (standardLift_compatible lattice g g_cube g_isometry).1
  obtain ⟨N, hN⟩ := nativeField_twisted_borcherds a vac 0 0 ha₀ hv₀
  have h := hN 0 q (-2)
  simp only [Int.cast_zero, zero_div, sub_zero, zero_add, zero_sub, ← neg_mul] at h
  rw [show (0 : ℤ) - 3 * 0 = 0 by omega] at h
  rw [Finset.sum_eq_single 0] at h
  · simp only [Ring.choose_zero_right, one_smul, Nat.cast_zero, add_zero, sub_zero] at h
    rw [← h, vacuum_minus_two_residue_mode, strip_mode]
    rw [show (0 : ℤ) - 3 * (q - 1 + 1) = -3 * q by omega]
  · intro j _ hj
    rw [Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj), zero_smul]
  · intro hzero
    exact (hzero (Finset.mem_range.mpr (by omega))).elim

private theorem source_conformal_products_checked (D : LatticeData) (hrank : D.rank = 48)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    mu D (omega D H) 0 (omega D H) = translation D (omega D H) ∧
    mu D (omega D H) 1 (omega D H) = (2 : ℂ) • omega D H ∧
    mu D (omega D H) 2 (omega D H) = 0 ∧
    mu D (omega D H) 3 (omega D H) = (24 : ℂ) • vacuum D ∧
    (∀ j : ℤ, 4 ≤ j → mu D (omega D H) j (omega D H) = 0) := by
  have hCreation : sugawaraMode D H (-2) (vacuum D) = omega D H := by
    rw [← omega_modes D H (-2)]
    exact stateField_creation D (omega D H)
  have hVacuum (m : ℤ) (hm : -1 ≤ m) : sugawaraMode D H m (vacuum D) = 0 := by
    rw [← omega_modes D H m]
    exact stateField_creativity D (omega D H) (m + 1) (by omega)
  have hProduct (j : ℤ) (hj : 0 ≤ j) :
      mu D (omega D H) j (omega D H) =
        ((j + 1 : ℤ) : ℂ) • sugawaraMode D H (j - 3) (vacuum D) +
        (if j = 3 then (D.rank : ℂ) / 12 * (((j - 1 : ℤ) : ℂ)^3 - (j - 1 : ℤ))
          else 0) • vacuum D := by
    have h := congrArg (fun A : Module.End ℂ (Carrier D) => A (vacuum D))
      (sugawaraMode_virasoro D H hHG hGH (j - 1) (-2))
    rw [omega_product]
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, hCreation,
      hVacuum (j - 1) (by omega), map_zero, sub_zero,
      show j - 1 - (-2) = j + 1 by omega,
      show j - 1 + (-2) = j - 3 by omega,
      show (j - 3 = 0) ↔ j = 3 by omega] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [omega_product]
    exact LinearMap.congr_fun (sugawaraMode_minus_one_eq_translation D H hHG hGH)
      (omega D H)
  · rw [hProduct 1 (by omega), show (1 : ℤ) - 3 = -2 by omega, hCreation]
    norm_num
  · rw [hProduct 2 (by omega), hVacuum _ (by omega)]
    norm_num
  · rw [hProduct 3 (by omega), hVacuum _ (by omega), hrank]
    norm_num
  · intro j hj
    rw [hProduct j (by omega), hVacuum _ (by omega), ite_eq_right (by omega),
      smul_zero, zero_smul, add_zero]

private theorem source_conformal_products (j : ℕ) :
    mu lattice Ω (j : ℤ) Ω =
      if j = 0 then mu lattice Ω (-2) vac
      else if j = 1 then (2 : ℂ) • Ω
      else if j = 3 then (24 : ℂ) • vac
      else 0 := by
  obtain ⟨h0, h1, h2, h3, hge⟩ :=
    source_conformal_products_checked lattice rfl (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
  by_cases hj0 : j = 0
  · subst j
    change mu lattice Ω 0 Ω = mu lattice Ω (-2) vac
    simpa only [translation_as_mode, mu] using h0
  by_cases hj1 : j = 1
  · subst j
    exact h1
  by_cases hj2 : j = 2
  · subst j
    simpa only [Nat.cast_ofNat, ite_eq_right (by decide : (2 : ℕ) ≠ 0),
      ite_eq_right (by decide : (2 : ℕ) ≠ 1), ite_eq_right (by decide : (2 : ℕ) ≠ 3)] using h2
  by_cases hj3 : j = 3
  · subst j
    exact h3
  rw [ite_eq_right hj0, ite_eq_right hj1, ite_eq_right hj3]
  exact hge _ (by omega)

set_option maxHeartbeats 2000000 in
-- The concrete rank-48 carrier and inverse Gram coefficients require extra elaboration.
/-- Virasoro at central charge 48 on the Laurent coefficients of the actual
native conformal field. -/
theorem native_conformal_virasoro (m n : ℤ) :
    let L : ℤ → Module.End ℂ State := fun i => C (nativeField Ω) (-3 * (i + 2))
    L m * L n - L n * L m =
      ((m - n : ℤ) : ℂ) • L (m + n) +
        (if m + n = 0 then 4 * ((m : ℂ)^3 - (m : ℂ)) else 0) • (1 : Module.End ℂ State) := by
  intro L
  have hΩ : σ Ω = Ω :=
    standardLift_omega lattice g g_cube g_isometry (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit)
  have hΩ₀ : σ Ω = ζ ^ (0 : ℤ) • Ω := by
    simpa only [zpow_zero, one_smul] using hΩ
  let A := nativeField Ω
  obtain ⟨K, hK⟩ := nativeField_pairwise_locality Ω Ω
  let N := max K 4
  have hK' : (deltaCoverEnd ^ K) (coverComm A A) = 0 := by
    rw [Module.End.pow_apply]
    exact hK
  have hN : coverDelta^[N] (coverComm A A) = 0 := by
    have hN' := coverOrder_mono (le_max_left K 4) hK'
    rw [Module.End.pow_apply] at hN'
    exact hN'
  have hA := nativeField_inResidue Ω 0 hΩ₀
  have h := adjustedResidue_twisted_borcherds 0 0 A A N
    (fun r => nativeField (mu lattice Ω r Ω)) hA hA hN
    (fun r => adjustedResidue_eigenstate_first Ω Ω 0 0 hΩ₀ hΩ₀ N hN r)
    (m + 1) (n + 1) 0
  let term (j : ℕ) := Ring.choose (((m + 1 : ℤ) : ℂ)) j •
    C (nativeField (mu lattice Ω (j : ℤ) Ω))
      (-3 * (m + 1 + (n + 1) - (j : ℤ) + 1))
  simp only [Int.cast_zero, zero_div, sub_zero, zero_add, zero_sub, ← neg_mul,
    Int.toNat_natCast] at h
  rw [show (0 : ℤ) - 3 * (m + 1) = -3 * (m + 1) by ring] at h
  change ((residueField 1 0 (stripResidue (-3 * (m + 1)) A)
    (stripResidue 0 A)).operator)[[n + 1]] = ∑ j ∈ Finset.range N, term j at h
  have hcomm :
      ((residueField 1 0 (stripResidue (-3 * (m + 1)) A)
        (stripResidue 0 A)).operator)[[n + 1]] = L m * L n - L n * L m := by
    have hr := ordinary_residue_mode (stripResidue (-3 * (m + 1)) A)
      (stripResidue 0 A) 0 (n + 1)
    change ((residueField 1 0 (stripResidue (-3 * (m + 1)) A)
      (stripResidue 0 A)).operator)[[n + 1]] = _ at hr
    change _ = C A (-3 * (m + 2)) * C A (-3 * (n + 2)) -
      C A (-3 * (n + 2)) * C A (-3 * (m + 2))
    simpa only [Function.iterate_zero, id_eq,
      FieldNormalProductLocality.commutator, strip_mode,
      show -3 * (m + 1) - 3 * ((0 : ℤ) + 1) = -3 * (m + 2) by omega,
      show (0 : ℤ) - 3 * (n + 1 + 1) = -3 * (n + 2) by omega] using hr
  have hsum : (∑ j ∈ Finset.range 4, term j) = ∑ j ∈ Finset.range N, term j := by
    apply Finset.sum_subset (Finset.range_mono (le_max_right K 4))
    intro j _ hj
    have hj₄ : 4 ≤ j := Nat.le_of_not_gt fun hlt => hj (Finset.mem_range.mpr hlt)
    simp only [term, source_conformal_products, ite_eq_right (show j ≠ 0 by omega),
      ite_eq_right (show j ≠ 1 by omega), ite_eq_right (show j ≠ 3 by omega),
      map_zero, Pi.zero_apply, smul_zero]
  have h0 : term 0 = -((m + n + 2 : ℤ) : ℂ) • L (m + n) := by
    simp only [term, Ring.choose_zero_right, one_smul, source_conformal_products,
      ite_true, Nat.cast_zero, sub_zero]
    rw [show m + 1 + (n + 1) + 1 = m + n + 2 + 1 by omega,
      native_vacuum_minus_two_mode Ω hΩ (m + n + 2)] <;> rfl
  have h1 : term 1 = (((m + 1 : ℤ) : ℂ) * 2) • L (m + n) := by
    simp only [term, Ring.choose_one_right, source_conformal_products,
      ite_eq_right (by decide : (1 : ℕ) ≠ 0), ite_true, Nat.cast_one, map_smul, Pi.smul_apply,
      smul_smul]
    rw [show m + 1 + (n + 1) - 1 + 1 = m + n + 2 by omega] <;> rfl
  have h2 : term 2 = 0 := by
    simp only [term, source_conformal_products, ite_eq_right (by decide : (2 : ℕ) ≠ 0),
      ite_eq_right (by decide : (2 : ℕ) ≠ 1), ite_eq_right (by decide : (2 : ℕ) ≠ 3),
      map_zero, Pi.zero_apply, smul_zero]
  have h3 : term 3 = (Ring.choose (((m + 1 : ℤ) : ℂ)) 3 * 24) •
      (if m + n = 0 then (1 : Module.End ℂ State) else 0) := by
    simp only [term, source_conformal_products, ite_eq_right (by decide : (3 : ℕ) ≠ 0),
      ite_eq_right (by decide : (3 : ℕ) ≠ 1), ite_true, map_smul, Pi.smul_apply, smul_smul,
      vacuum_coeff]
    simp only [show -3 * (m + 1 + (n + 1) - ((3 : ℕ) : ℤ) + 1) = 0 ↔ m + n = 0 by omega]
  have hcentral : Ring.choose (((m + 1 : ℤ) : ℂ)) 3 * 24 =
      4 * ((m : ℂ)^3 - (m : ℂ)) := by
    have hchoose := Ring.descPochhammer_eq_factorial_smul_choose (m + 1) 3
    norm_num [descPochhammer_succ_right, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, Polynomial.smeval_one, nsmul_eq_mul] at hchoose
    rw [show (2 : Polynomial ℤ) = Polynomial.C 2 by norm_num, Polynomial.smeval_C] at hchoose
    norm_num at hchoose
    have hcast := congrArg (fun i : ℤ => (i : ℂ)) hchoose
    push_cast at hcast
    rw [← show ((Ring.choose (m + 1) 3 : ℤ) : ℂ) =
      Ring.choose (((m + 1 : ℤ) : ℂ)) 3 from Ring.map_choose (Int.castRingHom ℂ) (m + 1) 3]
    linear_combination -(4 : ℂ) * hcast
  rw [← hcomm, h, ← hsum]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [h0, h1, h2, h3, add_zero]
  rw [← add_smul, hcentral]
  have hlinear : -((m + n + 2 : ℤ) : ℂ) + ((m + 1 : ℤ) : ℂ) * 2 =
      ((m - n : ℤ) : ℂ) := by
    push_cast
    ring
  rw [hlinear]
  by_cases hmn : m + n = 0 <;> simp [hmn]

set_option maxHeartbeats 2000000 in
/-- The actual twisted energy operator acts on every physical mode `q - s / 3`
of a lift eigenstate by the zero-mode Ward identity. -/
theorem native_LZero_ward (a : NativeStates) (s : ℤ) (ha : σ a = ζ ^ s • a) (q : ℤ) :
    let B := C (nativeField a) (s - 3 * (q + 1))
    totalLZero * B - B * totalLZero =
      C (nativeField (sugawaraMode lattice (actualInverse lattice) 0 a))
        (s - 3 * (q + 1)) - ((q : ℂ) - (s : ℂ) / 3 + 1) • B := by
  intro B
  have hHG := actualInverse_left lattice gram_det_unit
  have hGH := actualInverse_right lattice gram_det_unit
  have hΩ : σ Ω = ζ ^ (0 : ℤ) • Ω := by
    simpa only [zpow_zero, one_smul] using
      standardLift_omega lattice g g_cube g_isometry (actualInverse lattice) hHG
  let X := nativeField Ω
  let Y := nativeField a
  obtain ⟨K, hK⟩ := nativeField_pairwise_locality Ω a
  let N := max K 2
  have hN : coverDelta^[N] (coverComm X Y) = 0 :=
    cover_mono (le_max_left K 2) hK
  have h := adjustedResidue_twisted_borcherds 0 s X Y N
    (fun j => nativeField (mu lattice Ω j a))
    (nativeField_inResidue Ω 0 hΩ) (nativeField_inResidue a s ha) hN
    (adjustedResidue_eigenstate_first Ω a 0 s hΩ ha N hN) 1 q 0
  let term (j : ℕ) := Ring.choose (1 : ℂ) j •
    C (nativeField (mu lattice Ω (j : ℤ) a)) (s - 3 * (1 + q - (j : ℤ) + 1))
  simp only [Int.cast_one, Int.cast_zero, zero_div, sub_zero, zero_add, Int.toNat_natCast] at h
  rw [show (0 : ℤ) - 3 * 1 = -3 by decide] at h
  change _ = ∑ j ∈ Finset.range N, term j at h
  have hcomm :
      ((residueField 1 0 (stripResidue (-3) X) (stripResidue s Y)).operator)[[q]] =
        C X (-6) * B - B * C X (-6) := by
    have hr := ordinary_residue_mode (stripResidue (-3) X) (stripResidue s Y) 0 q
    change ((residueField 1 0 (stripResidue (-3) X) (stripResidue s Y)).operator)[[q]] = _ at hr
    simpa only [Function.iterate_zero, id_eq, FieldNormalProductLocality.commutator,
      strip_mode, show (-3 : ℤ) - 3 * (0 + 1) = -6 by decide] using hr
  have hsum : (∑ j ∈ Finset.range 2, term j) = ∑ j ∈ Finset.range N, term j := by
    apply Finset.sum_subset (Finset.range_mono (le_max_right K 2))
    intro j _ hj
    have hj' : 1 < j := by
      rw [Finset.mem_range, not_lt] at hj
      omega
    have hchoose : Ring.choose (1 : ℂ) j = 0 := by
      rw [show (1 : ℂ) = ((1 : ℕ) : ℂ) by simp, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt hj', Nat.cast_zero]
    simp only [term, hchoose, zero_smul]
  have htranslation : mu lattice Ω 0 a = mu lattice a (-2) vac := by
    rw [omega_product, show (0 : ℤ) - 1 = -1 by decide,
      sugawaraMode_minus_one_eq_translation lattice (actualInverse lattice) hHG hGH,
      translation_as_mode]
    rfl
  have h0 : term 0 = -((q : ℂ) - (s : ℂ) / 3 + 1) • B := by
    simp only [term, Ring.choose_zero_right, one_smul, Nat.cast_zero, sub_zero, htranslation]
    rw [show s - 3 * (1 + q + 1) = s - 3 * ((q + 1) + 1) by omega,
      native_vacuum_minus_two_fractional_mode a s ha (q + 1),
      show ((q + 1 : ℤ) : ℂ) - (s : ℂ) / 3 = (q : ℂ) - (s : ℂ) / 3 + 1 by
        push_cast
        ring]
  have h1 : term 1 =
      C (nativeField (sugawaraMode lattice (actualInverse lattice) 0 a))
        (s - 3 * (q + 1)) := by
    simp only [term, Ring.choose_one_right, one_smul, Nat.cast_one, omega_product,
      sub_self, show s - 3 * (1 + q - 1 + 1) = s - 3 * (q + 1) by omega]
  rw [← native_conformal_coeff_neg_six_eq_totalLZero, ← hcomm, h, ← hsum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1]
  rw [neg_smul, neg_add_eq_sub]

#print axioms native_vacuum_minus_two_fractional_mode
#print axioms native_LZero_ward
#print axioms native_vacuum_minus_two_mode
#print axioms native_conformal_virasoro

run_cmd do
  for name in [``native_vacuum_minus_two_fractional_mode, ``native_LZero_ward,
      ``native_vacuum_minus_two_mode, ``native_conformal_virasoro] do
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.contains ``propext &&
        axioms.contains ``Classical.choice && axioms.contains ``Quot.sound do
      throwError "Unexpected axiom closure for {name}: {axioms}"

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeVirasoro
