/- GID: D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumClass
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostBrstVacuumClass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original vacuum is closed and its actual coefficient excludes every original BRST preimage. -/

/-
proof_shape: vacuum_closed: content
proof_shape: epsilon_Q: content
proof_shape: epsilon_vacuum: bind-only; consumed by vacuum_not_mem_range
proof_shape: vacuum_not_mem_range: content
admission_basis: escape-witness
escape_witness: Signed insertion cannot produce the empty ghost coefficient,
and each negative actual matter normal summand has zero constant coefficient.
The two original outer-order branches annihilate this tensor coefficient on
all states. The zero-charge ground calculation also includes modes -1 and 0.
Utility is none: the scope is every original algebraic state and arbitrary
finite-rank lattice data and complex matrices, not a finite certified instance.
-/

import D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
import D5.S3.VertexAlgebra.BcGhostVacuum
import D5.S3.VertexAlgebra.LatticeSugawaraVirasoro

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
  LatticeSugawaraCurrents LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

private def ghostCoefficient {K : Type*} [CommRing K] : Fock K →ₗ[K] K :=
  Finsupp.lapply ∅

private def matterCoefficient (D : LatticeData) : Carrier D →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ (0 : Index D →₀ ℕ)).comp
    (Finsupp.lapply (0 : Charge D))

def vacuumVector (D : LatticeData) : State D :=
  Finsupp.single (0 : Charge D) (1 : Oscillator D) ⊗ₜ[ℂ]
    (BcGhostFockSupport.vacuum : Fock ℂ)

def epsilon (D : LatticeData) : State D →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map (matterCoefficient D) (ghostCoefficient (K := ℂ)))

private theorem epsilon_tmul (D : LatticeData) (u : Carrier D) (g : Fock ℂ) :
    epsilon D (u ⊗ₜ[ℂ] g) = matterCoefficient D u * ghostCoefficient g := by
  simp [epsilon, smul_eq_mul]

section Ghost

variable {K : Type*} [CommRing K]

private theorem ghostCoefficient_create (site : ℕ) (g : Fock K) :
    ghostCoefficient (create site g) = 0 := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add first second hfirst hsecond => simp [hfirst, hsecond]
  | single support scalar =>
      have nonempty : insert site support ≠ (∅ : Finset ℕ) := Finset.insert_ne_empty _ _
      by_cases occupied : site ∈ support <;>
        simp [ghostCoefficient, create, Finsupp.linearCombination_single,
          createBasis, occupied, nonempty, Ne.symm nonempty]

private theorem ghostCoefficient_c (mode : ℤ) (bound : mode ≤ 1) (g : Fock K) :
    ghostCoefficient (c mode g) = 0 := by
  rw [c, if_pos bound]
  exact ghostCoefficient_create _ g

private theorem ghostCoefficient_negative_pair (mode index : ℤ) (bound : mode ≤ -2)
    (g : Fock K) : ghostCoefficient (normalPair (mode + index) (-index) g) = 0 := by
  by_cases firstCreator : mode + index ≤ -2
  · simp only [normalPair, if_pos firstCreator, LinearMap.comp_apply,
      b, if_pos firstCreator]
    exact ghostCoefficient_create _ _
  · have secondCreator : -index ≤ 1 := by omega
    simp only [normalPair, if_neg firstCreator, LinearMap.neg_apply,
      LinearMap.comp_apply, map_neg]
    rw [ghostCoefficient_c (-index) secondCreator]
    exact neg_zero

private theorem ghostCoefficient_negative_L (mode : ℤ) (bound : mode ≤ -2)
    (g : Fock K) : ghostCoefficient (L mode g) = 0 := by
  classical
  rw [L_interval_sum mode g (-cutoff mode g) (cutoff mode g) le_rfl le_rfl,
    map_sum]
  apply Finset.sum_eq_zero
  intro index member
  rw [map_smul, ghostCoefficient_negative_pair mode index bound g, smul_zero]

end Ghost

private theorem matterCoefficient_negative_neutral (D : LatticeData)
    (axis : Fin D.rank) (mode : ℤ) (negative : mode < 0) (u : Carrier D) :
    matterCoefficient D (neutralMode D axis mode u) = 0 := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add first second hfirst hsecond => simp [hfirst, hsecond]
  | single charge polynomial =>
      rw [neutralMode_single]
      by_cases zeroCharge : charge = 0
      · subst charge
        simp only [matterCoefficient, LinearMap.comp_apply, Finsupp.lapply_apply,
          Finsupp.single_eq_same, MvPolynomial.lcoeff_apply]
        change MvPolynomial.constantCoeff
          (neutralPolynomialMode D axis 0 mode polynomial) = 0
        simp [neutralPolynomialMode, negative, LinearMap.mulLeft_apply, map_mul]
      · change MvPolynomial.constantCoeff
          ((Finsupp.single charge (neutralPolynomialMode D axis charge mode polynomial)) 0) = 0
        simp [Finsupp.single_apply, zeroCharge, Ne.symm zeroCharge]

private theorem matterCoefficient_negative_normal (D : LatticeData)
    (first second : Fin D.rank) (mode index : ℤ) (negative : mode < 0)
    (u : Carrier D) :
    matterCoefficient D (normalSummand D first second index (mode - index) u) = 0 := by
  by_cases firstNegative : index < 0
  · simp only [normalSummand, if_pos firstNegative, Module.End.mul_apply]
    exact matterCoefficient_negative_neutral D first index firstNegative _
  · have secondNegative : mode - index < 0 := by omega
    simp only [normalSummand, if_neg firstNegative, Module.End.mul_apply]
    exact matterCoefficient_negative_neutral D second (mode - index) secondNegative _

private theorem matterCoefficient_negative_sugawara (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ) (negative : mode < 0)
    (u : Carrier D) : matterCoefficient D (sugawaraMode D H mode u) = 0 := by
  classical
  rw [sugawaraMode_interval_sum]
  simp only [map_smul, map_sum, RingHom.id_apply]
  simp only [matterCoefficient_negative_normal D _ _ mode _ negative u,
    smul_zero, Finset.sum_const_zero]

private theorem neutral_ground_nonnegative (D : LatticeData) (axis : Fin D.rank)
    (mode : ℤ) (nonnegative : 0 ≤ mode) :
    neutralMode D axis mode (Finsupp.single (0 : Charge D) (1 : Oscillator D)) = 0 := by
  by_cases zeroMode : mode = 0
  · subst mode
    simp [neutralMode_single, neutralPolynomialMode, bilinear]
  · apply neutralMode_vanish
    simpa only [LatticeSugawaraVirasoro.ground_frequency_bound, Nat.cast_zero] using
      (show 0 < mode by omega)

theorem normal_ground_annihilation (D : LatticeData)
    (first second : Fin D.rank) (mode index : ℤ) (bound : -1 ≤ mode) :
    normalSummand D first second index (mode - index)
      (Finsupp.single (0 : Charge D) (1 : Oscillator D)) = 0 := by
  by_cases firstNegative : index < 0
  · have secondNonnegative : 0 ≤ mode - index := by omega
    simp only [normalSummand, if_pos firstNegative, Module.End.mul_apply,
      neutral_ground_nonnegative D second (mode - index) secondNonnegative, map_zero]
  · have firstNonnegative : 0 ≤ index := by omega
    simp only [normalSummand, if_neg firstNegative, Module.End.mul_apply,
      neutral_ground_nonnegative D first index firstNonnegative, map_zero]

theorem sugawara_ground_annihilation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ) (bound : -1 ≤ mode) :
    sugawaraMode D H mode (Finsupp.single (0 : Charge D) (1 : Oscillator D)) = 0 := by
  classical
  rw [sugawaraMode_interval_sum]
  simp only [normal_ground_annihilation D _ _ mode _ bound,
    smul_zero, Finset.sum_const_zero]

private theorem epsilon_A_tmul (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ)
    (u : Carrier D) (g : Fock ℂ) : epsilon D (A D H mode (u ⊗ₜ[ℂ] g)) = 0 := by
  by_cases nonnegativeBranch : -1 ≤ mode
  · simp only [A, N, if_pos nonnegativeBranch, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, M, C, G, TensorProduct.map_tmul,
      LinearMap.id_apply, map_add, map_smul, RingHom.id_apply, epsilon_tmul]
    rw [ghostCoefficient_c (-mode) (by omega) g,
      ghostCoefficient_c (-mode) (by omega) (L mode g)]
    simp
  · simp only [A, N, if_neg nonnegativeBranch, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, M, C, G, TensorProduct.map_tmul,
      LinearMap.id_apply, map_add, map_smul, RingHom.id_apply, epsilon_tmul]
    rw [matterCoefficient_negative_sugawara D H mode (by omega) u,
      ghostCoefficient_negative_L mode (by omega) (c (-mode) g)]
    simp

private theorem epsilon_A (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ) (state : State D) :
    epsilon D (A D H mode state) = 0 := by
  induction state using TensorProduct.induction_on with
  | zero => simp
  | tmul matter ghost => exact epsilon_A_tmul D H mode matter ghost
  | add first second hfirst hsecond => simp [hfirst, hsecond]

private theorem A_vacuum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ) :
    A D H mode (vacuumVector D) = 0 := by
  by_cases nonnegativeBranch : -1 ≤ mode
  · simp [A, N, nonnegativeBranch, M, C, G, vacuumVector,
      sugawara_ground_annihilation D H mode nonnegativeBranch,
      BcGhostVacuum.L_vacuum_annihilation mode nonnegativeBranch]
  · have ghostVacuum : c (K := ℂ) (-mode) vacuum = 0 := by
      rw [c, if_neg (show ¬ -mode ≤ 1 by omega)]
      apply annihilate_eq_zero
      simp [occupied, vacuum]
    simp [A, N, nonnegativeBranch, M, C, G, vacuumVector, ghostVacuum]

theorem vacuum_closed (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Q D H (vacuumVector D) = 0 := by
  classical
  change (∑ᶠ mode : ℤ, A D H mode (vacuumVector D)) = 0
  rw [finsum_eq_sum _ (A_finite D H (vacuumVector D))]
  apply Finset.sum_eq_zero
  intro mode member
  exact A_vacuum D H mode

theorem epsilon_Q (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (state : State D) :
    epsilon D (Q D H state) = 0 := by
  have transport := (epsilon D).toAddMonoidHom.map_finsum (A_finite D H state)
  simp only [LinearMap.toAddMonoidHom_coe] at transport
  change epsilon D (∑ᶠ mode : ℤ, A D H mode state) = 0
  rw [transport]
  simp only [epsilon_A, finsum_zero]

theorem epsilon_vacuum (D : LatticeData) : epsilon D (vacuumVector D) = 1 := by
  simp [vacuumVector, epsilon, matterCoefficient, ghostCoefficient, vacuum,
    MvPolynomial.lcoeff_apply]

theorem vacuum_not_mem_range (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    vacuumVector D ∉ LinearMap.range (Q D H) := by
  rintro ⟨state, preimage⟩
  have zeroCoefficient := epsilon_Q D H state
  rw [preimage, epsilon_vacuum] at zeroCoefficient
  exact one_ne_zero zeroCoefficient

#print axioms vacuum_closed
#print axioms epsilon_Q
#print axioms epsilon_vacuum
#print axioms vacuum_not_mem_range

end

end D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass
