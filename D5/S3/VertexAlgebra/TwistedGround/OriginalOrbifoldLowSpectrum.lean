/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalOrbifoldLowSpectrum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalOrbifoldLowSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original Golay–Leech orbifold has weight dimensions 1, 0 and 196884. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldConformal
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
import D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum
import D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades
import D5.S3.VertexAlgebra.HalfFock.NormFourFirstGradeSpectrum
import D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction

/-! The spectrum of the conformal zero mode on the original two-sector carrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldLowSpectrum

open Module.End (eigenspace mem_eigenspace_iff)
open OriginalOrbifoldField (Carrier vacuumState)
open OriginalOrbifoldConformal (L L_fixed_apply L_zero_fixed_coeff L_zero_twisted
  L_zero_twisted_coeff)
open LatticeGeneratingFieldLocality (LatticeData)
open LatticeInvolution (FixedCarrier fixedSpace mem_fixedSpace)
open LatticePositiveEnergy (carrierCoeffEquiv energy gradeProjection gradeProjection_coeff
  stateEnergies stateEnergies_nonneg sum_gradeProjections)
open SourceBPZ.ThetaReflectionAction (thetaRep_apply_one thetaRep_gradeProjection_commute)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockParityT (actualParity actualParity_on_grade_basis)
open LatticeHalfFockChargedTensorCoefficients (ActualTensor groundRank)
open LatticeTwistedGroundRealization (Half)
open LatticeHalfFockGradedTrace
open HalfFock.NormFourFirstGradeSpectrum
open Lattice.InvolutionRootlessLowGrades (actual_theta_fixed_rootless_low_spectrum)
open Lattice.LeechLowSpectrum (normFourEquiv)
open ActualLeechHyperbolic (leechData leechCoordinates leech_spec)
open D5.S3.Arith.Lattices.Golay
open private no_roots from D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum
open private canonicalFixedEnergy_eq_fixedGrade fixedGrade_zero_eq from
  D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades

noncomputable section

variable (D : LatticeData) (hu : IsUnit D.G.det)
  (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

private abbrev fixedEnergy (μ : ℂ) :=
  fixedSpace D ⊓ (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace μ

private abbrev oddEnergy (μ : ℂ) :=
  paritySpace D hu (-1) ⊓ (actualTensorL0 D hu).eigenspace μ

private theorem mem_eigenspace_sectors (μ : ℂ) (a : Carrier D hu) :
    a ∈ (L D hu hD 0).eigenspace μ ↔
      a.1.val ∈ fixedEnergy D μ ∧ a.2.val ∈ oddEnergy D hu μ := by
  have hinv : actualInverse D = (gramComplex D)⁻¹ :=
    (Matrix.inv_eq_left_inv (actualInverse_left D hu)).symm
  rw [mem_eigenspace_iff]
  constructor
  · intro ha
    refine ⟨⟨a.1.property, mem_eigenspace_iff.mpr ?_⟩,
      ⟨a.2.property, mem_eigenspace_iff.mpr ?_⟩⟩
    · rw [← hinv, ← L_fixed_apply D hu hD 0 a, ha]
      rfl
    · rw [← L_zero_twisted D hu hD a, ha]
      rfl
  · rintro ⟨hf, ht⟩
    apply Prod.ext <;> apply Subtype.ext
    · rw [L_fixed_apply, hinv]
      exact mem_eigenspace_iff.mp hf.2
    · rw [L_zero_twisted]
      exact mem_eigenspace_iff.mp ht.2

/-- Projection of the original zero-mode eigenspace onto its two sector intersections. -/
def eigenspaceEquiv (μ : ℂ) :
    (L D hu hD 0).eigenspace μ ≃ₗ[ℂ] fixedEnergy D μ × oddEnergy D hu μ where
  toFun a :=
    let ha := (mem_eigenspace_sectors D hu hD μ a.val).mp a.property
    (⟨a.val.1.val, ha.1⟩, ⟨a.val.2.val, ha.2⟩)
  invFun p := ⟨(⟨p.1.val, p.1.property.1⟩, ⟨p.2.val, p.2.property.1⟩),
    (mem_eigenspace_sectors D hu hD μ _).mpr ⟨p.1.property, p.2.property⟩⟩
  left_inv _ := Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl))
  right_inv _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  map_add' _ _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  map_smul' _ _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

private theorem actualParity_repr (v : ActualTensor D hu)
    (i : OddMonomial D × Half (groundRank D hu)) :
    (actualAmbientBasis D hu).repr (actualParity D hu v) i =
      (-1 : ℂ) ^ oddWeight D i.1 * (actualAmbientBasis D hu).repr v i := by
  let b := actualAmbientBasis D hu
  let coord : ActualTensor D hu →ₗ[ℂ] ℂ :=
    (Finsupp.lapply i).comp b.repr.toLinearMap
  have heq : coord.comp (actualParity D hu) = ((-1 : ℂ) ^ oddWeight D i.1) • coord := by
    apply b.ext
    intro j
    have hj := actualParity_on_grade_basis D hu (oddWeight D j.1)
      (⟨j.1, rfl⟩, j.2)
    rw [actualGradeBasis_coe, actualGradeVector] at hj
    change actualParity D hu (b j) = _ at hj
    change coord (actualParity D hu (b j)) = (-1 : ℂ) ^ oddWeight D i.1 * coord (b j)
    rw [hj, map_smul]
    change (-1 : ℂ) ^ oddWeight D j.1 * b.repr (b j) i =
      (-1 : ℂ) ^ oddWeight D i.1 * b.repr (b j) i
    by_cases h : i = j
    · subst j
      rfl
    · simp [Module.Basis.repr_self, h]
  exact LinearMap.congr_fun heq v

private theorem oddWeight_of_nonzero_coeff
    {v : ActualTensor D hu} (hv : v ∈ paritySpace D hu (-1))
    {i : OddMonomial D × Half (groundRank D hu)}
    (hi : (actualAmbientBasis D hu).repr v i ≠ 0) :
    oddWeight D i.1 % 2 = 1 := by
  simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
  have he := congrArg (fun w => (actualAmbientBasis D hu).repr w i)
    hv
  rw [actualParity_repr] at he
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at he
  have hs := mul_right_cancel₀ hi he
  rw [neg_one_pow_eq_pow_mod_two] at hs
  by_contra hn
  have hz : oddWeight D i.1 % 2 = 0 := by omega
  norm_num [hz] at hs

private theorem odd_eigenvalue {d : OddMonomial D}
    (h24 : D.rank = 24) (hd : oddWeight D d % 2 = 1) :
    (oddWeight D d : ℂ) / 2 + (D.rank : ℂ) / 16 =
      ((oddWeight D d / 2 + 2 : ℕ) : ℂ) := by
  have hn : oddWeight D d = 2 * (oddWeight D d / 2) + 1 := by omega
  have hc : (oddWeight D d : ℂ) = 2 * ((oddWeight D d / 2 : ℕ) : ℂ) + 1 := by
    exact_mod_cast hn
  rw [hc, h24, Nat.cast_add]
  push_cast
  ring

include hD in
private theorem oddEnergy_eq_bot (h24 : D.rank = 24) (n : ℕ) (hn : n < 2) :
    oddEnergy D hu (n : ℂ) = ⊥ := by
  refine le_antisymm (fun v hv => ?_) bot_le
  rw [Submodule.mem_bot]
  apply (actualAmbientBasis D hu).repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  by_contra hi
  let a : Carrier D hu := (0, ⟨v, hv.1⟩)
  have h := L_zero_twisted_coeff D hu hD a i
  rw [L_zero_twisted, show a.2.val = v from rfl,
    mem_eigenspace_iff.mp hv.2,
    odd_eigenvalue D h24 (oddWeight_of_nonzero_coeff D hu hv.1 hi)] at h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  have he := mul_right_cancel₀ hi h
  have hn' : n = oddWeight D i.1 / 2 + 2 := by exact_mod_cast he
  omega

include hD in
private theorem fixedEnergy_finite (μ : ℂ) (n : ℤ) (hμ : (n : ℂ) = μ) :
    FiniteDimensional ℂ (fixedEnergy D μ) := by
  subst μ
  unfold fixedEnergy
  rw [canonicalFixedEnergy_eq_fixedGrade D hD n]
  let := LatticePositiveEnergy.grade_finiteDimensional D hD n
  exact Submodule.finiteDimensional_of_le inf_le_right

/-- For the original orbifold, weight zero is the line of the original vacuum. -/
theorem eigenspace_zero_eq_vacuum (h24 : D.rank = 24) :
    (L D hu hD 0).eigenspace 0 = Submodule.span ℂ {vacuumState D hu} := by
  have hf := canonicalFixedEnergy_eq_fixedGrade D hD 0
  rw [Int.cast_zero, fixedGrade_zero_eq D hD,
    LatticePositiveEnergy.grade_zero D hD] at hf
  change fixedEnergy D 0 = _ at hf
  have ht := oddEnergy_eq_bot D hu hD h24 0 (by decide)
  rw [Nat.cast_zero] at ht
  ext a
  rw [mem_eigenspace_sectors, hf, ht, Submodule.mem_bot,
    Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨⟨c, hc⟩, hz⟩
    refine ⟨c, Prod.ext (Subtype.ext hc) (Subtype.ext ?_)⟩
    change c • (0 : ActualTensor D hu) = a.2.val
    rw [smul_zero, hz]
  · rintro ⟨c, rfl⟩
    exact ⟨⟨c, rfl⟩, by simp [vacuumState]⟩

private theorem finrank_eigenspace (μ : ℂ)
    [FiniteDimensional ℂ (fixedEnergy D μ)] [FiniteDimensional ℂ (oddEnergy D hu μ)] :
    FiniteDimensional ℂ ((L D hu hD 0).eigenspace μ) ∧
    Module.finrank ℂ ((L D hu hD 0).eigenspace μ) =
      Module.finrank ℂ (fixedEnergy D μ) + Module.finrank ℂ (oddEnergy D hu μ) := by
  let e := eigenspaceEquiv D hu hD μ
  exact ⟨Module.Finite.of_injective e.toLinearMap e.injective,
    e.finrank_eq.trans Module.finrank_prod⟩

set_option maxHeartbeats 1000000 in
-- Transporting all six sector finiteness instances across the concrete lattice costs heartbeats.
/-- The actual Golay–Leech fixed and twisted sectors contribute respectively
`300 + 98280` and `98304` in weight two. The first three eigenspaces of
the original conformal zero mode have dimensions `1, 0, 196884`. -/
theorem actual_leech_low_spectrum :
    let D := leechData
    let hu := leech_spec.2.1
    let hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)) := leech_spec.2.2.1
    let A := L D hu hD 0
    FiniteDimensional ℂ (A.eigenspace 0) ∧
    FiniteDimensional ℂ (A.eigenspace 1) ∧
    FiniteDimensional ℂ (A.eigenspace 2) ∧
    Module.finrank ℂ (A.eigenspace 0) = 1 ∧
    Module.finrank ℂ (A.eigenspace 1) = 0 ∧
    Module.finrank ℂ (A.eigenspace 2) = 196884 ∧
    A.eigenspace 0 = Submodule.span ℂ {vacuumState D hu} := by
  dsimp only
  let hu := leech_spec.2.1
  let hD : Matrix.PosDef (leechData.G.map (Int.cast : ℤ → ℝ)) := leech_spec.2.2.1
  have h24 := leech_spec.1
  have hroot := no_roots leechCoordinates leech_spec.2.2.2
  let shell := normFourEquiv leechData leechCoordinates leech_spec.2.2.2
  have hcard := (Nat.card_congr shell).trans LeechMinimalCount.shortest_vectors_card
  obtain ⟨hf0, hf1, hf2⟩ := actual_theta_fixed_rootless_low_spectrum leechData hD hroot
  change Module.finrank ℂ (fixedEnergy leechData 2) = _ at hf2
  rw [h24, hcard] at hf2
  change Module.finrank ℂ (fixedEnergy leechData 2) = 300 + 98280 at hf2
  have ht0 : oddEnergy leechData hu 0 = ⊥ := by
    simpa using oddEnergy_eq_bot leechData hu hD h24 0 (by decide)
  have ht1 : oddEnergy leechData hu 1 = ⊥ := by
    simpa using oddEnergy_eq_bot leechData hu hD h24 1 (by decide)
  have ht2 : oddEnergy leechData hu 2 = actualGrade leechData hu 1 :=
    (actual_grade_one_eq_parity_minus_energy_two leechData hu h24).symm
  have := fixedEnergy_finite leechData hD 0 0 Int.cast_zero
  have := fixedEnergy_finite leechData hD 1 1 Int.cast_one
  have := fixedEnergy_finite leechData hD 2 2 (Int.cast_ofNat 2)
  have : FiniteDimensional ℂ (oddEnergy leechData hu 0) := ht0 ▸ inferInstance
  have : FiniteDimensional ℂ (oddEnergy leechData hu 1) := ht1 ▸ inferInstance
  have : FiniteDimensional ℂ (oddEnergy leechData hu 2) := ht2 ▸ inferInstance
  obtain ⟨hd0, h0⟩ := finrank_eigenspace leechData hu hD 0
  obtain ⟨hd1, h1⟩ := finrank_eigenspace leechData hu hD 1
  obtain ⟨hd2, h2⟩ := finrank_eigenspace leechData hu hD 2
  have hn2 := (actual_rank24_grade_one_finrank_98304 leechData hu h24).2.1
  refine ⟨hd0, hd1, hd2, ?_, ?_, ?_, eigenspace_zero_eq_vacuum leechData hu hD h24⟩
  · rwa [hf0, ht0, finrank_bot, add_zero] at h0
  · rwa [hf1, ht1, finrank_bot, add_zero] at h1
  · rw [hf2, ht2, hn2] at h2
    exact h2

private theorem fixed_mem_weight_sup (a : FixedCarrier D) :
    (a, 0) ∈ ⨆ n : ℕ, (L D hu hD 0).eigenspace (n : ℂ) := by
  classical
  let v (m : ℤ) : FixedCarrier D :=
    ⟨gradeProjection D m a.val, (mem_fixedSpace D _).mpr (by
      have h := thetaRep_gradeProjection_commute D m a.val
      simpa only [thetaRep_apply_one, (mem_fixedSpace D _).mp a.property] using h)⟩
  have hv : ∑ m ∈ stateEnergies D a.val, v m = a := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum] using sum_gradeProjections D a.val
  let incl := LinearMap.inl ℂ (FixedCarrier D) (paritySpace D hu (-1))
  change incl a ∈ _
  rw [← hv, map_sum]
  apply Submodule.sum_mem
  intro m hm
  have hn : ((m.toNat : ℕ) : ℂ) = (m : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg (stateEnergies_nonneg hD a.val m hm)
  apply (le_iSup (fun n : ℕ => (L D hu hD 0).eigenspace (n : ℂ)) m.toNat)
  rw [hn, mem_eigenspace_iff]
  apply Prod.ext <;> apply Subtype.ext
  · apply (carrierCoeffEquiv D).injective
    ext j
    rw [L_zero_fixed_coeff]
    change (energy D j : ℂ) * carrierCoeffEquiv D (gradeProjection D m a.val) j =
      carrierCoeffEquiv D ((m : ℂ) • gradeProjection D m a.val) j
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, gradeProjection_coeff]
    split_ifs with hj
    · rw [hj]
    · simp
  · rw [L_zero_twisted]
    change actualTensorL0 D hu 0 = (m : ℂ) • 0
    simp

private theorem odd_mem_weight_sup (h24 : D.rank = 24) (a : paritySpace D hu (-1)) :
    (0, a) ∈ ⨆ n : ℕ, (L D hu hD 0).eigenspace (n : ℂ) := by
  classical
  let b := actualAmbientBasis D hu
  let s := (b.repr a.val).support
  have hodd (j : s) : oddWeight D j.val.1 % 2 = 1 :=
    oddWeight_of_nonzero_coeff D hu a.property (Finsupp.mem_support_iff.mp j.property)
  let v (j : s) : paritySpace D hu (-1) :=
    ⟨b j.val, by
      have hp := actualParity_on_grade_basis D hu (oddWeight D j.val.1)
        (⟨j.val.1, rfl⟩, j.val.2)
      rw [actualGradeBasis_coe, actualGradeVector] at hp
      change actualParity D hu (b j.val) = _ at hp
      rw [neg_one_pow_eq_pow_mod_two, hodd j, pow_one] at hp
      simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] using hp⟩
  have hv : ∑ j ∈ s.attach, b.repr a.val j.val • v j = a := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    change (∑ j ∈ s.attach, b.repr a.val j.val • b j.val) = a.val
    calc
      _ = ∑ j ∈ s, b.repr a.val j • b j :=
        Finset.sum_attach s (fun j => b.repr a.val j • b j)
      _ = a.val := b.linearCombination_repr a.val
  let incl := LinearMap.inr ℂ (FixedCarrier D) (paritySpace D hu (-1))
  change incl a ∈ _
  rw [← hv, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul]
  apply Submodule.smul_mem
  apply (le_iSup (fun n : ℕ => (L D hu hD 0).eigenspace (n : ℂ))
    (oddWeight D j.val.1 / 2 + 2))
  rw [mem_eigenspace_iff]
  apply Prod.ext <;> apply Subtype.ext
  · rw [L_fixed_apply]
    change sugawaraMode D (actualInverse D) 0 0 =
      ((oddWeight D j.val.1 / 2 + 2 : ℕ) : ℂ) • 0
    simp
  · rw [L_zero_twisted]
    change actualTensorL0 D hu (b j.val) =
      ((oddWeight D j.val.1 / 2 + 2 : ℕ) : ℂ) • b j.val
    rw [actual_basis_eigenvalue, add_comm ((D.rank : ℂ) / 16),
      odd_eigenvalue D h24 (hodd j)]

include hD in
private theorem oddEnergy_finite (h24 : D.rank = 24) (n : ℕ) :
    FiniteDimensional ℂ (oddEnergy D hu (n : ℂ)) := by
  by_cases hn : n < 2
  · rw [oddEnergy_eq_bot D hu hD h24 n hn]
    infer_instance
  · let k := n - 2
    have hk : n = k + 2 := by omega
    have hc : (D.rank : ℂ) / 16 + ((2 * k + 1 : ℕ) : ℂ) / 2 = (n : ℂ) := by
      rw [h24, hk]
      push_cast
      ring
    refine Submodule.finiteDimensional_of_le (S₂ := actualGrade D hu (2 * k + 1)) ?_
    intro v hv
    simp only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, hc]
    exact mem_eigenspace_iff.mp hv.2

private theorem positiveIntegral (h24 : D.rank = 24) :
    DirectSum.IsInternal (fun n : ℕ => (L D hu hD 0).eigenspace (n : ℂ)) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (L D hu hD 0).eigenspaces_iSupIndep.comp Nat.cast_injective
  · apply top_unique
    intro a _
    have hf := fixed_mem_weight_sup D hu hD a.1
    have ht := odd_mem_weight_sup D hu hD h24 a.2
    simpa using Submodule.add_mem _ hf ht

/-- The original Golay–Leech carrier is the internal direct sum of its
nonnegative integer conformal weights, with every complex eigenspace finite. -/
theorem actual_leech_positive_integral_grading :
    let D := leechData
    let hu := leech_spec.2.1
    let hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)) := leech_spec.2.2.1
    let A := L D hu hD 0
    DirectSum.IsInternal (fun n : ℕ => A.eigenspace (n : ℂ)) ∧
    (∀ μ : ℂ, (¬ ∃ n : ℕ, (n : ℂ) = μ) → A.eigenspace μ = ⊥) ∧
    (∀ μ : ℂ, FiniteDimensional ℂ (A.eigenspace μ)) := by
  classical
  dsimp only
  let hu := leech_spec.2.1
  let hD : Matrix.PosDef (leechData.G.map (Int.cast : ℤ → ℝ)) := leech_spec.2.2.1
  let A := L leechData hu hD 0
  have h24 := leech_spec.1
  have hds := positiveIntegral leechData hu hD h24
  have htop := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp hds |>.2
  have hbot (μ : ℂ) (hμ : ¬ ∃ n : ℕ, (n : ℂ) = μ) : A.eigenspace μ = ⊥ := by
    have hle : (⨆ n : ℕ, A.eigenspace (n : ℂ)) ≤ ⨆ j : ℂ, ⨆ _ : j ≠ μ, A.eigenspace j :=
      iSup_le fun n => le_iSup_of_le (n : ℂ) (le_iSup_of_le (fun he => hμ ⟨n, he⟩) le_rfl)
    have hd := (A.eigenspaces_iSupIndep μ).mono_right hle
    change (⨆ n : ℕ, A.eigenspace (n : ℂ)) = ⊤ at htop
    rw [htop, disjoint_iff, inf_top_eq] at hd
    exact hd
  refine ⟨hds, hbot, ?_⟩
  intro μ
  by_cases hμ : ∃ n : ℕ, (n : ℂ) = μ
  · obtain ⟨n, rfl⟩ := hμ
    have := fixedEnergy_finite leechData hD (n : ℂ) (n : ℤ) (Int.cast_natCast n)
    have := oddEnergy_finite leechData hu hD h24 n
    exact (finrank_eigenspace leechData hu hD (n : ℂ)).1
  · rw [hbot μ hμ]
    infer_instance

#print axioms eigenspaceEquiv
#print axioms eigenspace_zero_eq_vacuum
#print axioms actual_leech_low_spectrum
#print axioms actual_leech_positive_integral_grading

end
end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldLowSpectrum
