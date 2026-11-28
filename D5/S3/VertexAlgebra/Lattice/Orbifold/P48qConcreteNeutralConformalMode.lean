/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qConcreteNeutralConformalMode
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The concrete neutral conformal coefficient and its exact P48q energy spectrum. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedCurrentCasimir
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingCurrentZero
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFullEnergySpectrum
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteEnergyEigenspaces
import Batteries.Tactic.OpenPrivate

/-! The cover coefficient of the actual P48q conformal state in the concrete
neutral field, computed by the fixed and moving normal orders. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConcreteNeutralConformalMode

open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalState (omega)
open LatticeGeneratingFieldLocality (Carrier)
open P48qConformalVectorDecomposition (currentPair currentPair_comm omega_decomposition)
open P48qFixedCurrentCasimir (totalLZero_apply_fixedCurrent)
open P48qFixedCurrentIterate (normalOrderedTerm normalOrderedZero zeroTerm)
open P48qMomentumEnergy (Fixed fixedBasis fixedGram fixedGramDual)
open P48qMovingCurrentZero (coverVariable firstDirection secondDirection orderedPair
  orderedZero pairLZero movingLZero movingLZero_apply)
open P48qQuadraticStateField (quadraticStates neutralStates neutralStateField currentProduct
  neutralStateField_pair_coeff orderedTerm orderedMode correction correction_eq)
open P48qThirdTwistedField (Cartan State creator annihilatorDual fixedDualBases
  frequency pair_modes)
open P48qTwistedChargeAction (lattice)
open P48qTwistedHeisenberg (mode modeLinear project projectAt projectAt_eq_fourier
  project_action mode_projectAt annCoordinates creCoordinates scale movingGram
  movingGram_eq_pairing)
open P48qTwistedStateEnergy (totalLZero)
open ThirdEigenspacePairing (p48qAction p48qForm p48qBasis p48qOppositeBasis)
open ThirdTwistedQuadratic (residue)
open MvPolynomial
open scoped BigOperators

open private formSymmetric from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

noncomputable section

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

private theorem zetaPrimitive : IsPrimitiveRoot ζ 3 :=
  IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive

private theorem root_cube (r : ℕ) : (ζ ^ r) ^ 3 = 1 := by
  rw [pow_right_comm, zetaPrimitive.pow_eq_one, one_pow]

private theorem root_square_square (r : ℕ) : ((ζ ^ r) ^ 2) ^ 2 = ζ ^ r := by
  calc
    ((ζ ^ r) ^ 2) ^ 2 = (ζ ^ r) ^ 3 * ζ ^ r := by ring
    _ = ζ ^ r := by rw [root_cube, one_mul]

private theorem fixed_action (u : Fixed) : p48qAction (u : Cartan) = (u : Cartan) := by
  simpa only [Fixed, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    using u.property

private theorem first_action (i : Fin 16) :
    p48qAction (firstDirection i) = (ζ ^ (1 : ℕ)) ^ 2 • firstDirection i := by
  simpa only [firstDirection, pow_one] using
    Module.End.mem_eigenspace_iff.mp (p48qOppositeBasis zetaPrimitive i).property

private theorem projectAt_zero_off_residue (a : Cartan) {r : ℕ} (hr : r < 3)
    (ha : p48qAction a = (ζ ^ r) ^ 2 • a) {k : ℤ} (hk : k ∉ residue (r : ℤ)) :
    projectAt k a = 0 := by
  let s := (k % 3).toNat
  have hs : (s : ℤ) = k % 3 := Int.toNat_of_nonneg (Int.emod_nonneg k (by decide))
  have hslt : s < 3 := by omega
  have hsr : s ≠ r := by
    intro h
    apply hk
    change k % 3 = (r : ℤ)
    rw [← hs, h]
  have hroot : (ζ ^ s) ^ 2 ≠ (ζ ^ r) ^ 2 := by
    intro h
    apply hsr
    apply zetaPrimitive.pow_inj hslt hr
    have hsquare := congrArg (fun z : ℂ => z ^ 2) h
    change ((ζ ^ s) ^ 2) ^ 2 = ((ζ ^ r) ^ 2) ^ 2 at hsquare
    rwa [root_square_square s, root_square_square r] at hsquare
  have hcomm : p48qAction (project (ζ ^ s) a) = project (ζ ^ s) (p48qAction a) := by
    simp only [project, map_add, map_smul]
  have hact : p48qAction (project (ζ ^ s) a) = (ζ ^ r) ^ 2 • project (ζ ^ s) a := by
    rw [hcomm, ha]
    simp only [project, map_smul]
    rw [smul_comm (ζ ^ s) ((ζ ^ r) ^ 2), smul_comm ((ζ ^ s) ^ 2) ((ζ ^ r) ^ 2),
      ← smul_add, ← smul_add, smul_comm ((3 : ℂ)⁻¹) ((ζ ^ r) ^ 2)]
  have hzero : ((ζ ^ s) ^ 2 - (ζ ^ r) ^ 2) • project (ζ ^ s) a = 0 := by
    rw [sub_smul, ← project_action _ (root_cube s), ← hact, sub_self]
  rw [projectAt_eq_fourier]
  exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hroot)

private theorem orderedMode_on_residue (a b : Cartan) {r : ℕ} (hr : r < 3)
    (ha : p48qAction a = (ζ ^ r) ^ 2 • a) (w : State) :
    orderedMode 0 a b w = ∑ᶠ k ∈ residue (r : ℤ), orderedTerm 0 a b k w := by
  let term := fun k : ℤ => orderedTerm 0 a b k w
  have hs : Function.support term ⊆ residue (r : ℤ) := by
    intro k hk
    by_contra hoff
    have hm : mode a k = 0 := by
      rw [← mode_projectAt a k, projectAt_zero_off_residue a hr ha hoff]
      exact (modeLinear k).map_zero
    apply hk
    change orderedTerm 0 a b k w = 0
    simp [orderedTerm, normalOrderedTerm, hm]
  change (∑ᶠ k : ℤ, term k) = ∑ᶠ k ∈ residue (r : ℤ), term k
  rw [← finsum_mem_univ (f := term)]
  apply finsum_mem_inter_support_eq
  rw [Set.univ_inter, Set.inter_eq_right.mpr hs]

private theorem fixed_coordinates (u : Fixed) (n : ℕ) (i : Fin 16) :
    annCoordinates u (3 * n + 2) i = fixedGram u (fixedBasis i) ∧
    creCoordinates u (3 * n + 2) i = fixedGram u (fixedGramDual fixedBasis i) := by
  have h : frequency (i, 3 * n + 2) % 3 = 0 := by
    change (3 * n + 2 + 1) % 3 = 0
    omega
  constructor
  · change p48qForm (u : Cartan) (creator fixedDualBases (i, 3 * n + 2)) =
      p48qForm (u : Cartan) (fixedBasis i : Cartan)
    simp only [creator, h, ite_true, fixedDualBases, Module.Basis.map_apply,
      LinearEquiv.coe_ofEq_apply]
  · change p48qForm (u : Cartan) (annihilatorDual fixedDualBases (i, 3 * n + 2)) =
      p48qForm (u : Cartan) (fixedGramDual fixedBasis i : Cartan)
    simp only [annihilatorDual, h, ite_true, fixedDualBases, Module.Basis.map_apply,
      LinearEquiv.coe_ofEq_apply]

private theorem mode_fixed (u : Fixed) (k : ℤ) :
    mode (u : Cartan) (3 * k) = P48qFixedCurrentIterate.currentMode u k := by
  apply LinearMap.ext
  intro w
  apply Finsupp.ext
  intro p
  cases k with
  | ofNat n =>
    cases n with
    | zero =>
      change mode (u : Cartan) 0 w p = P48qFixedCurrentIterate.zeroMode u w p
      rw [P48qTwistedHeisenberg.mode_zero_apply, P48qFixedCurrentIterate.zeroMode_apply]
      rfl
    | succ n =>
      have hk : 3 * Int.ofNat (n + 1) = Int.ofNat (3 * n + 2 + 1) := by
        change 3 * ((n + 1 : ℕ) : ℤ) = ((3 * n + 2 + 1 : ℕ) : ℤ)
        push_cast
        omega
      rw [hk, P48qTwistedHeisenberg.mode_positive_apply]
      have h (i : Fin 16) := (fixed_coordinates u n i).1
      simp only [P48qFixedCurrentIterate.currentMode, Finsupp.mapRange.linearMap_apply,
        Finsupp.mapRange_apply, P48qFixedCurrentIterate.annihilationMode_apply, h, scale,
        P48qFixedCurrentIterate.fixedVariable, frequency]
  | negSucc n =>
    have hk : 3 * Int.negSucc n = Int.negSucc (3 * n + 2) := by omega
    rw [hk, P48qTwistedHeisenberg.mode_negative_apply]
    have h (i : Fin 16) := (fixed_coordinates u n i).2
    simp only [P48qFixedCurrentIterate.currentMode, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_apply, LinearMap.mulLeft_apply, P48qFixedCurrentIterate.creationPolynomial,
      P48qFixedCurrentIterate.fixedVariable, h, Finset.sum_mul, smul_mul_assoc]

private theorem orderedMode_fixed (u v : Fixed) :
    orderedMode 0 u v = normalOrderedZero u v := by
  have hu : p48qAction (u : Cartan) = (ζ ^ (0 : ℕ)) ^ 2 • (u : Cartan) := by
    simpa only [pow_zero, one_pow, one_smul] using fixed_action u
  have hRange : Set.range (fun k : ℤ => 3 * k) = residue 0 := by
    ext k
    constructor
    · rintro ⟨n, rfl⟩
      change (3 * n) % 3 = 0
      omega
    · intro hk
      change k % 3 = 0 at hk
      refine ⟨k / 3, ?_⟩
      change 3 * (k / 3) = k
      omega
  have hInjective : Function.Injective (fun k : ℤ => 3 * k) := by
    intro k l h
    change 3 * k = 3 * l at h
    omega
  apply LinearMap.ext
  intro w
  change orderedMode 0 u v w = ∑ᶠ k : ℤ, zeroTerm u v k w
  calc
    _ = ∑ᶠ k ∈ residue 0, orderedTerm 0 u v k w :=
      orderedMode_on_residue (u : Cartan) (v : Cartan) (by decide) hu w
    _ = ∑ᶠ k : ℤ, orderedTerm 0 u v (3 * k) w := by
      rw [← hRange]
      exact finsum_mem_range hInjective
    _ = _ := by
      apply finsum_congr
      intro k
      have hsign : 3 * k < 0 ↔ k < 0 := by omega
      have hneg : -(3 * k) = 3 * (-k) := by omega
      simp only [orderedTerm, zeroTerm, normalOrderedTerm, zero_sub, hneg, hsign,
        mode_fixed u k, mode_fixed v (-k)]

private theorem moving_positive_mode (i : Fin 16) {r k : ℤ} (hr : k % 3 = r) (hk : 0 < k) :
    mode (annihilatorDual fixedDualBases (coverVariable i k)) k =
      P48qMovingCurrentZero.currentMode r i k := by
  cases k with
  | negSucc n => omega
  | ofNat n =>
    cases n with
    | zero => exact (lt_irrefl (0 : ℤ) hk).elim
    | succ n =>
      apply LinearMap.ext
      intro w
      apply Finsupp.ext
      intro p
      have h (j : Fin 16) :
          annCoordinates (annihilatorDual fixedDualBases (i, n)) n j =
            if j = i then 1 else 0 :=
        (formSymmetric.eq _ _).trans (pair_modes fixedDualBases j i n)
      rw [P48qMovingCurrentZero.currentMode_positive_apply i hr hk]
      change mode (annihilatorDual fixedDualBases (i, n)) (.ofNat (n + 1)) w p =
        scale n • pderiv (i, n) (w p)
      simp only [P48qTwistedHeisenberg.mode_positive_apply, h, mul_ite, mul_one, mul_zero,
        ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem moving_negative_mode (i : Fin 16) {r k : ℤ} (hr : k % 3 = r) (hk : k < 0) :
    mode (creator fixedDualBases (coverVariable i k)) k =
      P48qMovingCurrentZero.currentMode r i k := by
  cases k with
  | ofNat n => exact (not_lt_of_ge (Int.natCast_nonneg n) hk).elim
  | negSucc n =>
    apply LinearMap.ext
    intro w
    apply Finsupp.ext
    intro p
    have h (j : Fin 16) :
        creCoordinates (creator fixedDualBases (i, n)) n j = if i = j then 1 else 0 :=
      pair_modes fixedDualBases i j n
    rw [P48qMovingCurrentZero.currentMode_negative_apply i hr hk]
    change mode (creator fixedDualBases (i, n)) (.negSucc n) w p = X (i, n) * w p
    simp only [P48qTwistedHeisenberg.mode_negative_apply, h, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem moving_modes (i : Fin 16) {k : ℤ} (hk : k ∈ residue 1) :
    mode (firstDirection i) k = P48qMovingCurrentZero.currentMode 1 i k ∧
      mode (secondDirection i) (-k) = P48qMovingCurrentZero.currentMode 2 i (-k) := by
  obtain ⟨hc, ha⟩ := P48qMovingCurrentZero.directions_coverVariable fixedDualBases i hk
  change k % 3 = 1 at hk
  have hopp : (-k) % 3 = 2 := by omega
  have hv : coverVariable i (-k) = coverVariable i k := by
    simp only [coverVariable, Int.natAbs_neg]
  by_cases h : k < 0
  · simp only [h, ite_true] at hc ha
    constructor
    · rw [← hc]
      exact moving_negative_mode i hk h
    · rw [← ha, ← hv]
      exact moving_positive_mode i hopp (by omega)
  · simp only [h, ite_false] at hc ha
    constructor
    · rw [← ha]
      exact moving_positive_mode i hk (by omega)
    · rw [← hc, ← hv]
      exact moving_negative_mode i hopp (by omega)

private theorem orderedMode_moving (i : Fin 16) :
    orderedMode 0 (firstDirection i) (secondDirection i) = orderedZero i := by
  apply LinearMap.ext
  intro w
  change orderedMode 0 (firstDirection i) (secondDirection i) w =
    ∑ᶠ k ∈ residue 1, orderedPair i 0 k w
  rw [orderedMode_on_residue _ _ (r := 1) (by decide) (first_action i)]
  refine finsum_mem_congr rfl fun k hk => ?_
  obtain ⟨hFirst, hSecond⟩ := moving_modes i hk
  simp only [orderedTerm, normalOrderedTerm, orderedPair, Int.mul_zero, zero_sub, hFirst, hSecond]

private theorem fixed_correction (u v : Fixed) : correction (u : Cartan) (v : Cartan) = 0 := by
  have hu : p48qAction (u : Cartan) = (ζ ^ (0 : ℕ)) ^ 2 • (u : Cartan) := by
    simpa only [pow_zero, one_pow, one_smul] using fixed_action u
  have h₁ : projectAt 1 (u : Cartan) = 0 :=
    projectAt_zero_off_residue _ (r := 0) (k := 1) (by decide) hu
      (show (1 : ℤ) % 3 ≠ (0 : ℤ) by decide)
  have h₂ : projectAt 2 (u : Cartan) = 0 :=
    projectAt_zero_off_residue _ (r := 0) (k := 2) (by decide) hu
      (show (2 : ℤ) % 3 ≠ (0 : ℤ) by decide)
  rw [correction_eq]
  simp only [movingGram, Nat.cast_one, Nat.cast_ofNat, h₁, h₂, map_zero,
    LinearMap.zero_apply, add_zero, zero_div]

private theorem moving_correction (i : Fin 16) :
    correction (firstDirection i) (secondDirection i) = 1 / 9 := by
  have h₂ : projectAt 2 (firstDirection i) = 0 :=
    projectAt_zero_off_residue _ (r := 1) (k := 2) (by decide) (first_action i)
      (show (2 : ℤ) % 3 ≠ (1 : ℤ) by decide)
  have hGram : movingGram 2 (firstDirection i) (secondDirection i) = 0 := by
    simp only [movingGram, Nat.cast_ofNat, h₂, map_zero, LinearMap.zero_apply]
  rw [correction_eq, movingGram_eq_pairing 1 (Or.inl rfl) _ _ (first_action i), hGram,
    P48qMovingCurrentZero.pair_directions]
  simp only [eq_self, ite_true, add_zero]

private theorem fixed_pair_coeff (u v : Fixed) :
    HVertexOperator.coeff (neutralStateField (currentProduct u v 0)) (-6) =
      normalOrderedZero u v := by
  have h := neutralStateField_pair_coeff (u : Cartan) (v : Cartan) 0
  rw [orderedMode_fixed u v, fixed_correction u v] at h
  simpa only [neg_zero, zero_sub, eq_self, ite_true, zero_smul, add_zero] using h

private theorem moving_pair_coeff (i : Fin 16) :
    HVertexOperator.coeff
        (neutralStateField (currentProduct (firstDirection i) (secondDirection i) 0)) (-6) =
      pairLZero i := by
  have h := neutralStateField_pair_coeff (firstDirection i) (secondDirection i) 0
  rw [orderedMode_moving i, moving_correction i] at h
  simpa only [neg_zero, zero_sub, eq_self, ite_true, pairLZero, Module.End.one_eq_id] using h

private theorem omega_decomposition_signed :
    omega lattice (actualInverse lattice) =
      (2 : ℂ)⁻¹ • (∑ i : Fin 16, currentPair (fixedBasis i) (fixedGramDual fixedBasis i)) +
        ∑ i : Fin 16, currentPair (firstDirection i) (secondDirection i) := by
  have hMoving :
      (∑ i : Fin 16, currentPair (p48qBasis zetaPrimitive i) (p48qOppositeBasis zetaPrimitive i)) =
        ∑ i : Fin 16, currentPair (firstDirection i) (secondDirection i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simpa only [firstDirection, secondDirection] using
      currentPair_comm (p48qBasis zetaPrimitive i) (p48qOppositeBasis zetaPrimitive i)
  rw [omega_decomposition zetaPrimitive, hMoving]

/-- The actual conformal vector is in the span of lattice current products. -/
theorem omega_mem_quadraticStates : omega lattice (actualInverse lattice) ∈ quadraticStates := by
  have hPair (u v : Cartan) : currentPair u v ∈ quadraticStates := by
    unfold quadraticStates
    exact Submodule.subset_span ⟨(u, v), rfl⟩
  rw [omega_decomposition_signed]
  exact quadraticStates.add_mem
    (quadraticStates.smul_mem _ (quadraticStates.sum_mem fun i _ => hPair _ _))
    (quadraticStates.sum_mem fun i _ => hPair _ _)

private theorem quadraticStates_le_neutralStates : quadraticStates ≤ neutralStates := by
  unfold quadraticStates neutralStates
  exact Submodule.span_mono fun _ h => Or.inr (Or.inr h)

/-- The actual lattice conformal state with its neutral-span membership. -/
def conformalState : neutralStates :=
  ⟨omega lattice (actualInverse lattice),
    quadraticStates_le_neutralStates omega_mem_quadraticStates⟩

private theorem conformalState_decomposition :
    conformalState =
      (2 : ℂ)⁻¹ • (∑ i : Fin 16, currentProduct (fixedBasis i) (fixedGramDual fixedBasis i) 0) +
        ∑ i : Fin 16, currentProduct (firstDirection i) (secondDirection i) 0 := by
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum]
  exact omega_decomposition_signed

/-- The coefficient of `x⁻⁶`, or `z⁻²` for `z = x³`, of the
concrete neutral field of the actual P48q conformal state. -/
theorem conformal_coeff_neg_six_eq_totalLZero :
    HVertexOperator.coeff (neutralStateField conformalState) (-6) = totalLZero := by
  calc
    HVertexOperator.coeff (neutralStateField conformalState) (-6) =
        (2 : ℂ)⁻¹ • (∑ i : Fin 16,
          normalOrderedZero (fixedBasis i) (fixedGramDual fixedBasis i)) + movingLZero := by
      rw [conformalState_decomposition]
      simp only [map_add, map_smul, map_sum, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
        fixed_pair_coeff, moving_pair_coeff, movingLZero]
    _ = totalLZero := by
      apply LinearMap.ext
      intro w
      apply Finsupp.ext
      intro p
      simp only [LinearMap.add_apply, Finsupp.add_apply, movingLZero_apply,
        totalLZero_apply_fixedCurrent, Nat.dvd_iff_mod_eq_zero, add_assoc]

/-- The algebraic point spectrum is `16 / 9 + ℕ / 3`, with finite-dimensional
eigenspaces and an empty intersection with the integral eigenvalues. -/
theorem conformal_coeff_neg_six_spectrum :
    (∀ a : ℂ, (∃ v : State, v ≠ 0 ∧
      HVertexOperator.coeff (neutralStateField conformalState) (-6) v = a • v) ↔
        ∃ n : ℕ, a = 16 / 9 + (n : ℂ) / 3) ∧
    (∀ z : ℤ, ¬ ∃ v : State, v ≠ 0 ∧
      HVertexOperator.coeff (neutralStateField conformalState) (-6) v = (z : ℂ) • v) ∧
    (∀ a : ℂ, FiniteDimensional ℂ
      (Module.End.eigenspace
        (HVertexOperator.coeff (neutralStateField conformalState) (-6)) a)) := by
  rw [conformal_coeff_neg_six_eq_totalLZero]
  exact ⟨P48qFullEnergySpectrum.totalLZero_exact_eigenvalues,
    P48qFullEnergySpectrum.totalLZero_no_integral_eigenvalue,
    P48qFiniteEnergyEigenspaces.totalLZero_eigenspace_finiteDimensional⟩

end

#print axioms conformal_coeff_neg_six_eq_totalLZero
#print axioms conformal_coeff_neg_six_spectrum

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConcreteNeutralConformalMode
