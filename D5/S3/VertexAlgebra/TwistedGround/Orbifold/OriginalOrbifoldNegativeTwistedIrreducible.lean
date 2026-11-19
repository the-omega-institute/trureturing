/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNegativeTwistedIrreducible
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNegativeTwistedIrreducible
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed physical modes act irreducibly on the negative twisted Leech module. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedOscillatorAction
import D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades

/-! First-oscillator charge modes and irreducibility of the negative twisted Leech slice. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldNegativeTwistedIrreducible

open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockParityT (actualParity)
open LatticeSugawaraConformal (chargePolynomial)
open LatticeInvolution (FixedCarrier theta sigmaLinear sigma_X)
open LatticePositiveEnergy (chargeEnergy two_chargeEnergy)
open HalfFock.LatticeHalfFockParityField (paritySpace correctedField_target_parity)
open ActualLeechHyperbolic (leechData leech_spec)
open OriginalOrbifoldSectorModules (fixedParityY)
open OriginalOrbifoldTwistedGroundAction (fixedCharge)
open OriginalOrbifoldTwistedOscillatorAction (tensorPair_mem_of_fixed_modes)
open LatticeTwistedGroundRealization (actual_twisted_ground_representation)
open LatticeTwistedGroundRealization.SignQuotient (Extension)
open OperatorAlgebra (actual_operator_algebra chargeOperator integralLift)
open MvPolynomial
open scoped BigOperators TensorProduct VertexOperator

open private half_creation_zero half_creation_one charged_X_tail from
  D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades
open private chargeState from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedGroundAction
open private fixedParitySlice_mode_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldSectorModules
open private tensorCurrent_product_mem tensorCurrent_parity current_stable_extension
  tensor_mem_of_ground_and_currents from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedOscillatorAction
open private partialEnd partialEnd_mem_of_currents from
  D5.S3.VertexAlgebra.ActualTensorGroundIntersection

noncomputable section

local notation "D" => leechData
local notation "hu" => And.left (And.right leech_spec)

abbrev NegativeTwisted := paritySpace D hu (-1)

local notation "G" => ActualGround D hu
local notation "T" => ActualTensor D hu

/-- The oscillator polynomial of a vector in the first half-oscillator grade. -/
def firstOscillator (u : Fin leechData.rank → ℂ) : Oscillator D :=
  ∑ i, u i • X (i, 0)

local notation "B" => fun (α : Charge D) (i : Fin leechData.rank) =>
  (bilinear D α (unitCharge D i) : ℂ)

private theorem oscillatorCoefficient_X (α : Charge D) (i : Fin leechData.rank) :
    oscillatorCoefficient D α (-chargeNorm D α) (X (i, 0)) =
      X (i, 0) - (2 * B α i) • chargePolynomial D α := by
  classical
  change (∑ᶠ n : ℕ, oscillatorTerm D α (-chargeNorm D α) (X (i, 0)) n) = _
  rw [finsum_eq_sum_of_support_subset _ (charged_X_tail D α i (-chargeNorm D α))]
  simp [oscillatorTerm, halfTranslatedPolynomial, halfTranslationVariable, omega,
    half_creation_zero, half_creation_one, smul_smul]
  module

private theorem oscillatorCoefficient_first (α : Charge D) (u : Fin leechData.rank → ℂ) :
    oscillatorCoefficient D α (-chargeNorm D α) (firstOscillator u) =
      firstOscillator u - (2 * ∑ i, u i * B α i) • chargePolynomial D α := by
  simp only [firstOscillator, map_sum, map_smul, oscillatorCoefficient_X, smul_sub,
    Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul, Finset.mul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem sigma_first (u : Fin leechData.rank → ℂ) :
    sigmaLinear D (firstOscillator u) = -firstOscillator u := by
  simp only [firstOscillator, map_sum, map_smul, show ∀ i : Fin leechData.rank,
    sigmaLinear D (X (i, 0)) = -X (i, 0) from fun i => sigma_X D (i, 0),
    smul_neg, Finset.sum_neg_distrib]

private theorem parity_first (u : Fin leechData.rank → ℂ) (g : G) :
    actualParity D hu (firstOscillator u ⊗ₜ[ℂ] g) =
      -(firstOscillator u ⊗ₜ[ℂ] g) := by
  simp [actualParity, sigma_first, TensorProduct.neg_tmul]

private theorem negative_parity (v : NegativeTwisted) :
    actualParity D hu v.val = -v.val := by
  simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.neg_apply, sub_eq_zero, neg_smul, one_smul] using v.property

set_option maxHeartbeats 1000000 in
-- The physical mode is compared with a raw coefficient on the ambient tensor.
/-- On every first-oscillator tensor, the physical zero mode of the literal fixed
charge average acts by the normalized ground action and a rank-one oscillator
correction. The formula applies to every integral charge. -/
theorem fixed_charge_zero_mode_on_first (α : Charge D) (u : Fin leechData.rank → ℂ) (g : G)
    (v : NegativeTwisted) (hv : v.val = firstOscillator u ⊗ₜ[ℂ] g) :
    (((fixedParityY D hu (-1) (fixedCharge α))[[chargeEnergy D α - 1]]) v).val =
      chargeScalar D α •
        ((firstOscillator u - (2 * ∑ i, u i * B α i) • chargePolynomial D α) ⊗ₜ[ℂ]
          groundAction D hu α g) := by
  let e := -chargeNorm D α
  have he : -2 * (chargeEnergy D α - 1) - 2 = e := by
    dsimp [e, chargeNorm]
    rw [← two_chargeEnergy]
    ring
  have mode_val :
      (((fixedParityY D hu (-1) (fixedCharge α))[[chargeEnergy D α - 1]]) v).val =
      (correctedField D hu (fixedCharge α).val).coeff
        (-2 * (chargeEnergy D α - 1) - 2) v.val :=
    fixedParitySlice_mode_val D hu (-1) (fixedCharge α) (chargeEnergy D α - 1) v
  rw [mode_val, he, hv]
  let x := firstOscillator u ⊗ₜ[ℂ] g
  let p := firstOscillator u - (2 * ∑ i, u i * B α i) • chargePolynomial D α
  let y := chargeScalar D α • (p ⊗ₜ[ℂ] groundAction D hu α g)
  have charged : (correctedField D hu (chargeState α)).coeff e x = y := by
    rw [chargeState, corrected_singleton_coeff_charged]
    change chargedCoefficient D hu α e x = y
    simp only [chargedCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul,
      e, x, oscillatorCoefficient_first, y, p]
  have hp : sigmaLinear D p = -p := by
    have hcharge : sigmaLinear D (chargePolynomial D α) = -chargePolynomial D α :=
      sigma_first (fun i => (α i : ℂ))
    simp only [p, map_sub, map_smul, sigma_first, hcharge, smul_neg]
    abel
  have hy : actualParity D hu y = -y := by
    simp [y, actualParity, hp, TensorProduct.neg_tmul, smul_neg]
  have reflected := correctedField_target_parity D hu (chargeState α) e x
  have hx : actualParity D hu x = -x := parity_first u g
  rw [charged, hx, hy, map_neg, neg_inj] at reflected
  change (correctedField D hu ((1 / 2 : ℂ) •
    (chargeState α + theta D (chargeState α)))).coeff e x = y
  simp only [map_smul, map_add, Pi.smul_apply, Pi.add_apply, LinearMap.smul_apply,
    LinearMap.add_apply, charged, ← reflected]
  rw [← two_smul ℂ, smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]

private theorem orthogonal_first (α : Charge D) :
    ∃ (u : Fin leechData.rank → ℂ) (j : Fin leechData.rank),
      u j = 1 ∧ (∑ i, u i * B α i) = 0 := by
  let i : Fin leechData.rank := Fin.cast leech_spec.1.symm (0 : Fin 24)
  let j : Fin leechData.rank := Fin.cast leech_spec.1.symm (1 : Fin 24)
  have hji : j ≠ i := by
    intro h
    have hval := congrArg Fin.val h
    norm_num [i, j] at hval
  have contract (k : Fin leechData.rank) (c : ℂ) :
      (∑ l, Pi.single (M := fun _ : Fin leechData.rank => ℂ) k c l * B α l) = c * B α k := by
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
    · simp
    · intro l _ hl
      simp [Pi.single_eq_of_ne hl]
  by_cases h : B α i = 0
  · exact ⟨Pi.single i 1, i, by simp, by rw [contract, h, mul_zero]⟩
  · let c := B α j / B α i
    refine ⟨Pi.single j 1 - Pi.single i c, j, ?_, ?_⟩
    · simp [Pi.sub_apply, Pi.single_eq_of_ne hji]
    · simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, contract, one_mul]
      rw [show c * B α i = B α j from div_mul_cancel₀ _ h, sub_self]

private theorem first_mem_of_ground (U : Submodule ℂ T)
    (current_U : ∀ i m, U ≤ U.comap (tensorCurrent D G i m))
    (u : Fin leechData.rank → ℂ) (g : G) (hg : ((1 : Oscillator D) ⊗ₜ[ℂ] g) ∈ U) :
    firstOscillator u ⊗ₜ[ℂ] g ∈ U := by
  simp only [firstOscillator, TensorProduct.sum_tmul, ← TensorProduct.smul_tmul']
  apply U.sum_mem
  intro i _
  apply U.smul_mem
  have h : tensorCurrent D G i (-1) ((1 : Oscillator D) ⊗ₜ[ℂ] g) ∈ U :=
    current_U i (-1) hg
  have hcreation : current D i (-1) = LinearMap.mulLeft ℂ (X (i, 0)) :=
    current_negative D i 0
  simpa only [tensorCurrent, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
    hcreation, LinearMap.mulLeft_apply, mul_one] using h

private theorem vacuum_mem_of_first (U : Submodule ℂ T)
    (current_U : ∀ i m, U ≤ U.comap (tensorCurrent D G i m))
    (u : Fin leechData.rank → ℂ) (j : Fin leechData.rank) (hj : u j = 1) (g : G)
    (hg : firstOscillator u ⊗ₜ[ℂ] g ∈ U) :
    ((1 : Oscillator D) ⊗ₜ[ℂ] g) ∈ U := by
  have h := partialEnd_mem_of_currents D hu U
    (fun i k _ hw => current_U i (k : ℤ) hw) (j, 0) _ hg
  have hp : pderiv (j, 0) (firstOscillator u) = 1 := by
    simp only [firstOscillator, map_sum, Derivation.map_smul]
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro i _ h
      have hne : ((i, 0) : Index D) ≠ (j, 0) := fun he => h (congrArg Prod.fst he)
      rw [pderiv_X_of_ne hne, smul_zero]
    · simp
  simpa only [partialEnd, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
    Derivation.coeFn_coe, hp] using h

private theorem ground_action_span : Submodule.span ℂ
    (Set.range (groundAction D hu)) = ⊤ := by
  have spec := Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation D hu))
  obtain ⟨algebra⟩ := actual_operator_algebra D hu (groundRank D hu)
    spec.1 (groundRepresentation D hu) spec.2.2.1
  apply top_unique
  rw [← algebra.full_span]
  apply Submodule.span_mono
  rintro _ ⟨q, rfl⟩
  exact ⟨integralLift D q, rfl⟩

private theorem ground_eq_top (K : Submodule ℂ G) (g : G) (hg : g ∈ K) (hg0 : g ≠ 0)
    (stable : ∀ α (w : G), w ∈ K → groundAction D hu α w ∈ K) :
    K = ⊤ := by
  let evaluation : Module.End ℂ G →ₗ[ℂ] G := LinearMap.applyₗ g
  have hspan : Submodule.span ℂ (Set.range (groundAction D hu)) ≤
      K.comap evaluation := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, rfl⟩
    exact stable α g hg
  rw [ground_action_span] at hspan
  let : Module.Free ℂ G := Module.Free.of_divisionRing ℂ G
  let : Module.Projective ℂ G := Module.Projective.of_free
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hg0
  apply top_unique
  intro w _
  have hm := hspan (show f.smulRight w ∈ (⊤ : Submodule ℂ (Module.End ℂ G)) from trivial)
  change f g • w ∈ K at hm
  rwa [hf, one_smul] at hm

set_option maxHeartbeats 1600000 in
-- The subspace argument compares the sector subtype with both ambient tensor factors.
/-- The actual negative twisted Leech module is irreducible under every
physical mode of every theta-fixed source. -/
theorem negative_twisted_irreducible (S : Submodule ℂ NegativeTwisted)
    (stable : ∀ (a : FixedCarrier D) (n : ℤ) (v : NegativeTwisted),
      v ∈ S → ((fixedParityY D hu (-1) a)[[n]]) v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  classical
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  let W := S.map (paritySpace D hu (-1)).subtype
  have mem_W (v : NegativeTwisted) : v.val ∈ W ↔ v ∈ S := by
    constructor
    · rintro ⟨w, hw, he⟩
      exact (Subtype.ext he : w = v) ▸ hw
    · exact fun hv => ⟨v, hv, rfl⟩
  let currents := fun a : Fin leechData.rank × ℤ => tensorCurrent D G a.1 a.2
  have pair_mem (i j : Fin leechData.rank) (m n : ℤ) (w : T) (hw : w ∈ W) :
      tensorPair D G i j m n w ∈ W := by
    obtain ⟨v, hv, rfl⟩ := hw
    exact tensorPair_mem_of_fixed_modes D hu (-1) S stable i j m n v hv
  obtain ⟨U, W_le_U, hcurrents, odd_U⟩ :=
    current_stable_extension W (-actualParity D hu) currents (by
      rintro _ ⟨v, _, rfl⟩
      change -actualParity D hu v.val = v.val
      rw [negative_parity, neg_neg])
      (by
        intro a w
        simp only [LinearMap.neg_apply, currents, tensorCurrent_parity, map_neg, neg_neg])
      (fun a b w hw => tensorCurrent_product_mem D hu W pair_mem a.1 b.1 a.2 b.2 w hw)
  have current_U (i : Fin leechData.rank) (m : ℤ) : U ≤ U.comap (tensorCurrent D G i m) :=
    hcurrents (i, m)
  have U_ne_bot : U ≠ ⊥ := by
    obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    intro hU
    have h := W_le_U ((mem_W v).mpr hv)
    rw [hU, Submodule.mem_bot] at h
    exact hne (Subtype.ext h)
  obtain ⟨g, g_ne, hg⟩ :=
    ActualTensorGroundIntersection.nonzero_current_stable_submodule_meets_ground D hu
      U U_ne_bot (fun i k _ hw => current_U i (k : ℤ) hw)
  let K := U.comap (TensorProduct.mk ℂ (Oscillator D) G 1)
  have stable_K (α : Charge D) (w : G) (hw : w ∈ K) : groundAction D hu α w ∈ K := by
    obtain ⟨u, j, hj, horth⟩ := orthogonal_first α
    let v : NegativeTwisted := ⟨firstOscillator u ⊗ₜ[ℂ] w, by
      simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, LinearMap.neg_apply, sub_eq_zero, neg_smul, one_smul]
      exact parity_first u w⟩
    have hvU : v.val ∈ U := first_mem_of_ground U current_U u w hw
    have hvS : v ∈ S := (mem_W v).mp
      (odd_U _ hvU (by simp only [LinearMap.neg_apply, negative_parity, neg_neg]))
    have hmode := W_le_U ((mem_W _).mpr (stable (fixedCharge α) (chargeEnergy D α - 1) v hvS))
    rw [fixed_charge_zero_mode_on_first α u w v rfl, horth, mul_zero, zero_smul,
      sub_zero] at hmode
    have hscalar : chargeScalar D α ≠ 0 := zpow_ne_zero _ (by norm_num)
    have hfirst := U.smul_mem (chargeScalar D α)⁻¹ hmode
    rw [smul_smul, inv_mul_cancel₀ hscalar, one_smul] at hfirst
    exact vacuum_mem_of_first U current_U u j hj (groundAction D hu α w) hfirst
  have hK : K = ⊤ := ground_eq_top K g hg g_ne stable_K
  have all_ground (w : G) : ((1 : Oscillator D) ⊗ₜ[ℂ] w) ∈ U := by
    have h : w ∈ K := hK.symm ▸ Submodule.mem_top
    exact h
  apply top_unique
  intro v _
  exact (mem_W v).mp (odd_U v.val
    (tensor_mem_of_ground_and_currents D hu U current_U all_ground v.val)
    (by simp only [LinearMap.neg_apply, negative_parity, neg_neg]))

#print axioms fixed_charge_zero_mode_on_first
#print axioms negative_twisted_irreducible

end
end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldNegativeTwistedIrreducible
