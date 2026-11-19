/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalOrbifoldFaithfulness
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalOrbifoldFaithfulness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original twisted vacuum coefficient and faithful fixed-sector action. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalSourceModeTransport
import Batteries.Tactic.OpenPrivate

/-! The weight-two twisted pairing supplies the fixed vacuum in mode three.
The original mixed Jacobi law then detects every fixed state. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

open LatticeGeneratingFieldLocality LatticeHalfFock LatticeAllStateField
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockGradedTrace
open LatticePositiveEnergy LatticeInvolution
open HalfFock.LatticeHalfFockParityField ActualChargedAdjoint
open ActualOddGradeOrthogonality HalfFock.ActualEnergyCovariance
open OriginalFourMChargeCoset (originalI originalI_homogeneous)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open private basis_parity from D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
open private weight_two_vacuum_pairing from D5.S3.VertexAlgebra.TwistedGround.MixedJacobi
open private sourceGradePairingEquiv sourceGradePairingEquiv_evaluation from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction

/-- The literal original mode `I₃` takes a pair of actual negative twisted
states to the fixed vacuum for every supported rank-24 lattice. -/
theorem originalI_three_eq_vacuum (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24) :
    ∃ u v : paritySpace D hu (-1), originalI D hu hD 3 u v = fixedVacuum D := by
  classical
  let b := actualAmbientBasis D hu
  let i : OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu) :=
    (Finsupp.single (⟨0, by omega⟩, 0) 1, 0)
  have iw : oddWeight D i.1 = 1 := by
    simp [i, oddWeight, Finsupp.weight_single, LatticeHalfFockChargedCoefficients.omega]
  have detects : ∃ x : ActualTensor D hu, actualForm D hu x (b i) ≠ 0 := by
    by_contra absent
    push Not at absent
    exact b.ne_zero i ((actualForm_nondegenerate D hu).2 _ absent)
  obtain ⟨x, hx⟩ := detects
  have detects_basis : ∃ j, actualForm D hu (b j) (b i) ≠ 0 := by
    by_contra absent
    push Not at absent
    apply hx
    rw [← b.linearCombination_repr x]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
      LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
    simp [absent]
  obtain ⟨j, hj⟩ := detects_basis
  have jw : oddWeight D j.1 = 1 := by
    by_contra different
    apply hj
    apply actualForm_oddGrade_orthogonal D hu (oddWeight D j.1) 1 (b j) (b i)
    · simpa only [Int.cast_natCast] using actual_basis_eigenvalue D hu j.1 j.2
    · simpa [iw] using actual_basis_eigenvalue D hu i.1 i.2
    · exact_mod_cast different
  have weight_two (k : OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu))
      (hk : oddWeight D k.1 = 1) : actualTensorL0 D hu (b k) = (2 : ℂ) • b k := by
    rw [actual_basis_eigenvalue, hk, h24]
    norm_num [b]
  have negative (k : OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu))
      (hk : oddWeight D k.1 = 1) : b k ∈ paritySpace D hu (-1) := by
    simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    simpa only [hk, pow_one] using basis_parity D hu k
  let u : paritySpace D hu (-1) := ⟨b i, negative i iw⟩
  let v : paritySpace D hu (-1) := ⟨b j, negative j jw⟩
  let vac : fixedGrade D 0 :=
    ⟨vacuum D, ⟨by rw [grade_zero D hD]; exact Submodule.mem_span_singleton_self _,
      (fixedVacuum D).property⟩⟩
  let f := normalizedCoefficient D hu 3 u v 0
  let z := (sourceGradePairingEquiv D hu hD 0).symm f
  have hI : originalI D hu hD 3 u v = ⟨z.val, z.property.2⟩ :=
    originalI_homogeneous D hu hD h24 2 2 3 u v (weight_two i iw) (weight_two j jw)
  have hpair := sourceGradePairingEquiv_evaluation D hu hD 0 f vac
  rw [weight_two_vacuum_pairing D hu h24 u v (weight_two i iw) (weight_two j jw) vac rfl]
    at hpair
  have hz : z.val ≠ 0 := by
    intro hz
    change sourcePairing D z.val vac.val = _ at hpair
    rw [hz, map_zero, LinearMap.zero_apply] at hpair
    exact hj hpair.symm
  have hgrade : z.val ∈ Submodule.span ℂ {vacuum D} := grade_zero D hD ▸ z.property.1
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgrade
  have hc0 : c ≠ 0 := by
    intro h
    exact hz (by simpa [h] using hc.symm)
  have hscalar : originalI D hu hD 3 u v = c • fixedVacuum D := by
    rw [hI]
    apply Subtype.ext
    exact hc.symm
  refine ⟨u, c⁻¹ • v, ?_⟩
  rw [map_smul, hscalar, smul_smul, inv_mul_cancel₀ hc0, one_smul]

/-- The original fixed-sector field is faithful on the actual negative
twisted sector when all its integer modes are tested. -/
theorem fixedParitySlice_faithful (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (a : FixedCarrier D)
    (ha : ∀ (n : ℤ) (w : paritySpace D hu (-1)),
      ((fixedParitySlice D hu (-1) a)[[n]]) w = 0) : a = 0 := by
  obtain ⟨u, v, hvac⟩ := originalI_three_eq_vacuum D hu hD h24
  have h := original_mixed_jacobi D hu hD h24 (-1) 3 0 a u v
  simp only [ha, map_zero, LinearMap.zero_apply, smul_zero, finsum_zero, sub_zero] at h
  rw [finsum_eq_single _ 0] at h
  · have hcreate := fixed_creation D a
    change fixedMode D a (-1) (fixedVacuum D) = a at hcreate
    simpa only [Nat.cast_zero, add_zero, sub_zero, Int.cast_zero, pow_zero,
      Ring.choose_zero_right, mul_one, one_smul, hvac, hcreate] using h.symm
  · intro j hj
    simp only [Int.cast_zero, Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj), mul_zero, zero_smul]

end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
