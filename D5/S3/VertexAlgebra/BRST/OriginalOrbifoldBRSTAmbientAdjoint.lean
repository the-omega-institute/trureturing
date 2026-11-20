/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTAmbientAdjoint
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTAmbientAdjoint
   mirror-E: none(waiver:algebraic-original-brst-ambient-adjoint)
   anchors: []
   utility: none
   digest: Native tensor basis BPZ adjunction implies invariance of the physical form. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTRelativeDescentAdjoint
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTTensorBPZ

/-! The finite support of a descent state consists of even weight-one basis vectors.
The basis adjunctions can first be added at a common cutoff. The annihilation of
the full descent state then gives the adjunction at its own cutoff. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTAmbientAdjoint

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock)
open OriginalOrbifoldCriticalMatter (Matter State b matterDatum)
open OriginalOrbifoldBRSTStateField (Y)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTZeroEnergy (FullLabel fullBasis totalEnergy totalL0 totalL0_coeff)
open OriginalOrbifoldBRSTDescent (descent relativeCycles)
open OriginalOrbifoldBRSTDescentAdjointHomotopy (descentAdjointCorrection)
open OriginalOrbifoldBRSTBPZWard (betaTotal)
open OriginalOrbifoldBRSTPhysicalPairing (physicalBPZ)
open OriginalOrbifoldBRSTPhysicalLie (DegreeOne)
open OriginalOrbifoldBRSTRelativeDescentAdjoint
  (AmbientDescentAdjunction physicalBPZ_bracket_skew_adjoint)
open StateField.BorcherdsPermutations (dividedTranslation modesOfStateField)
open StateFieldResidueReconstruction (epsilon)

open private b_parity from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent
open private total_b correctionTerm from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescentAdjointHomotopy
open private parity_basis number_one_parity from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalLie

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

local notation "L₁" => VirasoroBRST.Ltotal matterDatum 1
local notation "DT" => dividedTranslation L₁
local notation "modes" => modesOfStateField Y

/-- The zero-mode specialization of
`OriginalOrbifoldBRSTTensorBPZ.betaTotal_mode_adjoint_tmul` at total weight one
and even ghost parity, with an annihilating cutoff for each basis vector. -/
def WeightOneBasisAdjunction : Prop :=
  ∀ i : FullLabel, totalEnergy i = 1 → Even i.2.2.card →
    ∃ cutoff : ℕ, (∀ j, cutoff ≤ j → DT j (fullBasis i) = 0) ∧
      ∀ (a c : Matter) (x y : Fock),
        betaTotal (((Y (fullBasis i))[[0]]) (a ⊗ₜ[ℂ] x)) (c ⊗ₜ[ℂ] y) =
          epsilon 1 * ∑ j ∈ Finset.range cutoff,
            betaTotal (a ⊗ₜ[ℂ] x)
              (((Y (DT j (fullBasis i)))[[-(j : ℤ)]]) (c ⊗ₜ[ℂ] y))

private def oppositeModes (cutoff : ℕ) : State →ₗ[ℂ] Module.End ℂ State :=
  ∑ j ∈ Finset.range cutoff, (modes (-(j : ℤ))).comp (DT j)

private theorem oppositeModes_apply (cutoff : ℕ) (s y : State) :
    oppositeModes cutoff s y =
      ∑ j ∈ Finset.range cutoff, modes (-(j : ℤ)) (DT j s) y := by
  simp only [oppositeModes, LinearMap.sum_apply, LinearMap.comp_apply]

private theorem oppositeModes_eq_of_le {small large : ℕ} (hle : small ≤ large) (s : State)
    (hzero : ∀ j, small ≤ j → DT j s = 0) :
    oppositeModes small s = oppositeModes large s := by
  apply LinearMap.ext
  intro y
  simp only [oppositeModes_apply]
  apply Finset.sum_subset (Finset.range_mono hle)
  intro j _ hj
  have hj' : small ≤ j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
  rw [hzero j hj', map_zero, LinearMap.zero_apply]

private theorem parity_coeff (s : State) (i : FullLabel) :
    fullBasis.repr (parity s) i = (-1 : ℂ) ^ i.2.2.card * fullBasis.repr s i := by
  classical
  let coeff : State →ₗ[ℂ] ℂ := (Finsupp.lapply i).comp fullBasis.repr.toLinearMap
  have h : coeff.comp parity = (-1 : ℂ) ^ i.2.2.card • coeff := by
    apply fullBasis.ext
    intro k
    change fullBasis.repr (parity (fullBasis k)) i =
      (-1 : ℂ) ^ i.2.2.card * fullBasis.repr (fullBasis k) i
    rw [parity_basis, fullBasis.repr.map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases hki : k = i
    · subst k
      rfl
    · simp only [fullBasis.repr_self, Finsupp.single_eq_of_ne' hki, mul_zero]
  exact LinearMap.congr_fun h s

private theorem weightOne_even_of_mem_support (s : State) (he : totalL0 s = s)
    (hp : parity s = s) (i : FullLabel) (hi : i ∈ (fullBasis.repr s).support) :
    totalEnergy i = 1 ∧ Even i.2.2.card := by
  have hnz := Finsupp.mem_support_iff.mp hi
  have henergy := totalL0_coeff s i
  rw [he] at henergy
  have hparity := parity_coeff s i
  rw [hp] at hparity
  have he' : (totalEnergy i : ℂ) = (1 : ℂ) :=
    mul_right_cancel₀ hnz (henergy.symm.trans (one_mul _).symm)
  have hp' : (-1 : ℂ) ^ i.2.2.card = 1 :=
    mul_right_cancel₀ hnz (hparity.symm.trans (one_mul _).symm)
  exact ⟨by exact_mod_cast he',
    (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)).mp hp'⟩

set_option maxHeartbeats 800000 in
-- Tensor extensionality elaborates the two nested linear maps on the native carrier.
private theorem adjunction_of_pure_testers (s : State) (cutoff : ℕ)
    (h : ∀ (a c : Matter) (x y : Fock),
      betaTotal (modes 0 s (a ⊗ₜ[ℂ] x)) (c ⊗ₜ[ℂ] y) =
        epsilon 1 * ∑ j ∈ Finset.range cutoff,
          betaTotal (a ⊗ₜ[ℂ] x) (modes (-(j : ℤ)) (DT j s) (c ⊗ₜ[ℂ] y)))
    (x y : State) :
    betaTotal (modes 0 s x) y = -betaTotal x (oppositeModes cutoff s y) := by
  let left : LinearMap.BilinForm ℂ State := LinearMap.comp betaTotal (modes 0 s)
  let right : LinearMap.BilinForm ℂ State :=
    (LinearMap.comp betaTotal.flip (-(oppositeModes cutoff s))).flip
  have hform : left = right := by
    apply TensorProduct.ext'
    intro a p
    apply TensorProduct.ext'
    intro c q
    change betaTotal (modes 0 s (a ⊗ₜ[ℂ] p)) (c ⊗ₜ[ℂ] q) =
      betaTotal (a ⊗ₜ[ℂ] p) (-(oppositeModes cutoff s (c ⊗ₜ[ℂ] q)))
    rw [map_neg, oppositeModes_apply, map_sum]
    simpa only [epsilon, zpow_one, neg_one_mul] using h a c p q
  have hxy : betaTotal (modes 0 s x) y = betaTotal x (-(oppositeModes cutoff s y)) :=
    LinearMap.congr_fun (LinearMap.congr_fun hform x) y
  simpa only [map_neg] using hxy

private theorem weightOne_zero_mode_adjoint (hb : WeightOneBasisAdjunction)
    (s : State) (he : totalL0 s = s) (hp : parity s = s) (cutoff : ℕ)
    (hs : ∀ j, cutoff ≤ j → DT j s = 0) (x y : State) :
    betaTotal (modes 0 s x) y = -betaTotal x (oppositeModes cutoff s y) := by
  classical
  let support := (fullBasis.repr s).support
  have basisData (i : support) :=
    hb i (weightOne_even_of_mem_support s he hp i i.property).1
      (weightOne_even_of_mem_support s he hp i i.property).2
  choose basisCutoff hzero hadj using basisData
  let bound := max cutoff (support.attach.sup basisCutoff)
  let left : State →ₗ[ℂ] ℂ :=
    (betaTotal.flip y).comp ((LinearMap.applyₗ (R := ℂ) x).comp (modes 0))
  let right : State →ₗ[ℂ] ℂ :=
    -((betaTotal x).comp ((LinearMap.applyₗ (R := ℂ) y).comp (oppositeModes bound)))
  have honBasis (i : FullLabel) (hi : i ∈ support) :
      left (fullBasis i) = right (fullBasis i) := by
    let label : support := ⟨i, hi⟩
    have hle : basisCutoff label ≤ bound :=
      (Finset.le_sup (f := basisCutoff) (Finset.mem_attach support label)).trans (le_max_right _ _)
    change betaTotal (modes 0 (fullBasis i) x) y =
      -betaTotal x (oppositeModes bound (fullBasis i) y)
    rw [← oppositeModes_eq_of_le hle (fullBasis i) (hzero label)]
    exact adjunction_of_pure_testers (fullBasis i) (basisCutoff label) (hadj label) x y
  have hexpand : s = ∑ i ∈ support, fullBasis.repr s i • fullBasis i := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      (fullBasis.linearCombination_repr s).symm
  have hsum : left s = right s := by
    conv_lhs => rw [hexpand]
    conv_rhs => rw [hexpand]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [honBasis i hi]
  rw [oppositeModes_eq_of_le (le_max_left cutoff _) s hs]
  exact hsum

private theorem divided_eq_zero_of_pow_eq_zero (s : State) (cutoff : ℕ)
    (h : (L₁ ^ cutoff) s = 0) (j : ℕ) (hj : cutoff ≤ j) : DT j s = 0 := by
  have hj' : j = j - cutoff + cutoff := by omega
  simp only [dividedTranslation, LinearMap.smul_apply]
  rw [hj', pow_add, Module.End.mul_apply, h, map_zero, smul_zero]

private theorem oppositeModes_descent (n : ℕ) (u y : State) :
    oppositeModes (n + 1) (b (-1) u) y = descent u y + descentAdjointCorrection n u y := by
  rw [oppositeModes_apply, Finset.sum_range_succ']
  have hhead : modes (-((0 : ℕ) : ℤ)) (DT 0 (b (-1) u)) y = descent u y := by
    simpa only [Nat.cast_zero, neg_zero, dividedTranslation, Nat.factorial_zero, Nat.cast_one,
      inv_one, pow_zero, one_smul, Module.End.one_apply] using
      (show modes 0 (b (-1) u) y = descent u y from rfl)
  rw [hhead, descentAdjointCorrection]
  refine (add_comm _ _).trans (congrArg (descent u y + ·) ?_)
  apply Finset.sum_congr rfl
  intro j _
  rw [show -((j + 1 : ℕ) : ℤ) = -(j : ℤ) - 1 by omega]
  simp only [correctionTerm, dividedTranslation, LinearMap.smul_apply, map_smul]
  rfl

/-- The finite signed adjunctions of the even weight-one basis states imply
the corrected ambient descent adjunction of every odd relative cycle. -/
theorem ambientDescentAdjunction_of_basis (hb : WeightOneBasisAdjunction) (u : relativeCycles)
    (hp : parity (u.1 : State) = -(u.1 : State)) :
    AmbientDescentAdjunction (u.1 : State) := by
  have hu := u.1.property
  change b 0 (u.1 : State) = 0 ∧ totalL0 (u.1 : State) = 0 at hu
  have hweight : totalL0 (b (-1) (u.1 : State)) = b (-1) (u.1 : State) := by
    simpa only [hu.2, map_zero, sub_zero, zero_sub, zero_add, neg_neg, Int.cast_one, one_smul]
      using total_b 0 (-1) (u.1 : State)
  have heven : parity (b (-1) (u.1 : State)) = b (-1) (u.1 : State) := by
    rw [b_parity, hp, map_neg, neg_neg]
  intro n hn x y
  have h := weightOne_zero_mode_adjoint hb (b (-1) (u.1 : State)) hweight heven (n + 1)
    (divided_eq_zero_of_pow_eq_zero _ _ hn) x y
  rw [oppositeModes_descent] at h
  exact h

/-- The original physical adjoint action preserves the physical BPZ form under
the finite signed basis adjunction hypothesis. -/
theorem physicalBPZ_bracket_skew_adjoint_of_basis (hb : WeightOneBasisAdjunction)
    (a b c : DegreeOne) :
    physicalBPZ ⁅a, b⁆ c = -physicalBPZ b ⁅a, c⁆ := by
  apply physicalBPZ_bracket_skew_adjoint _ a b c
  intro u hu
  exact ambientDescentAdjunction_of_basis hb u (number_one_parity (u.1 : State) hu)

set_option maxHeartbeats 800000 in
-- The Lie skew law and the form use instances on the native quotient eigenspace.
/-- The induced BPZ form on the native ghost-number-one Lie algebra is invariant
under the finite signed basis adjunction hypothesis. -/
theorem physicalBPZ_invariant_of_basis (hb : WeightOneBasisAdjunction) (a b c : DegreeOne) :
    physicalBPZ ⁅a, b⁆ c = physicalBPZ a ⁅b, c⁆ := by
  calc
    physicalBPZ ⁅a, b⁆ c = physicalBPZ (-⁅b, a⁆) c :=
      congrArg (fun z : DegreeOne => physicalBPZ z c) (lie_skew a b).symm
    _ = -physicalBPZ ⁅b, a⁆ c := LinearMap.congr_fun (physicalBPZ.map_neg ⁅b, a⁆) c
    _ = physicalBPZ a ⁅b, c⁆ :=
      (congrArg (fun z : ℂ => -z) (physicalBPZ_bracket_skew_adjoint_of_basis hb b a c)).trans
        (neg_neg _)

#print axioms WeightOneBasisAdjunction
#print axioms ambientDescentAdjunction_of_basis
#print axioms physicalBPZ_bracket_skew_adjoint_of_basis
#print axioms physicalBPZ_invariant_of_basis

end
end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTAmbientAdjoint
