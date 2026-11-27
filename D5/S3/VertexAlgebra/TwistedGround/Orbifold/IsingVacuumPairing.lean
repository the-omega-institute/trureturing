/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nondegenerate original mode-three vacuum channels on the twisted Ising eigenspaces. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.IsingPrimaryCoupling
import D5.S3.VertexAlgebra.Lattice.NormFourCosetVirasoro
import D5.S3.VertexAlgebra.Lattice.NormFourZhuAlgebra.Core
import Batteries.Tactic.OpenPrivate

/-! The grade-two negative twisted space has a vacuum pairing for each
signed norm-four axis. The fixed-source vacuum detector and the actual
grade-one projectors identify its nondegenerate Ising blocks. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.FixedSourceIsing

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open LatticeInvolution (FixedCarrier fixedMode fixedSpace fixedVacuum fixed_creativity
  fixedY_mode_val)
open HalfFock.LatticeHalfFockParityField (paritySpace fixedParitySlice)
open HalfFock.NormFourFirstGradeSpectrum
open HalfFock.NormFourLowestGrades (actualGradeOneZeroMode)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeHalfFockChargedTensorCoefficients (ActualTensor)
open LatticeHalfFockGradedTrace (actualGrade oddWeight actualTensorL0 actualAmbientBasis
  actual_basis_eigenvalue)
open LatticeAllStateField (vacuum)
open ActualChargedAdjoint (actualForm actualForm_nondegenerate)
open OriginalFourMChargeCoset (originalI originalI_three_eq_vacuum_smul)
open SourceBPZ.OriginalSourceCoevaluation (gradeVacuum)
open SourceBPZ.OriginalSourcePairing (sourcePairing sourcePairing_vacuum)
open LatticeHalfFockCorrectedField (correctedField)
open scoped VertexOperator BigOperators

open private energyTwoEigenspaceEquiv from
  D5.S3.VertexAlgebra.HalfFock.NormFourFirstGradeSpectrum
open private weight_two_vacuum_pairing from D5.S3.VertexAlgebra.TwistedGround.MixedJacobi

variable {D : LatticeData} {hu : IsUnit D.G.det}
  {hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))}
  {h24 : D.rank = 24} {a : Charge D} {ha : bilinear D a a = 4} {s : ℂ}

local notation "E" => parityMinusEnergyTwo D hu
local notation "W" => Module.End.eigenspace (parityMinusEnergyTwoZeroMode D hu h24 a ha s)
private theorem energyTwo_le_negativeParity (D : LatticeData) (hu : IsUnit D.G.det) :
    parityMinusEnergyTwo D hu ≤ paritySpace D hu (-1) := fun _ hx => hx.1

local notation "ι" => (Submodule.inclusion (energyTwo_le_negativeParity D hu))
local notation "B" => LinearMap.BilinForm.restrict (LinearMap.flip (actualForm D hu)) E
local notation "Allowed" => fun h : ℂ => h = 0 ∨ h = 1 / 2 ∨ h = 1 / 16

private theorem signed_axis_grade_two (hu : IsUnit D.G.det)
    (ha : bilinear D a a = 4) :
    (normFourFixedSource D a s).val ∈ LatticePositiveEnergy.grade D 2 := by
  let H := actualInverse D
  have hHG := actualInverse_left D hu
  have hGH := actualInverse_right D hu
  let e := Lattice.NormFourVirasoroVector.vector D a s
  change e ∈ LatticePositiveEnergy.grade D 2
  apply (LatticePositiveEnergy.actualL0_eigen_iff_grade D H hHG hGH 2 e).mp
  have h := ((Lattice.NormFourCosetVirasoro.mixed_products
    D H hHG hGH a ha s).1 1 (by omega)).1
  rw [LatticeActualConformalWard.omega_product] at h
  norm_num at h
  simpa only [Int.cast_ofNat, e] using h

/-- Every positive signed Ising mode kills the actual negative physical
energy-two space. -/
theorem oddAxisMode_pos_eq_zero_energyTwo (u : E) (k : ℤ) (hk : 0 < k)
    (h24 : D.rank = 24) (ha : bilinear D a a = 4) :
    oddAxisMode D hu a s k (ι u) = 0 := by
  apply Subtype.ext
  simp only [oddAxisMode, fixedParitySlice, VertexOperator.ncoeff_of_coeff]
  change (correctedField D hu (normFourFixedSource D a s).val).coeff
    (2 * (-(k + 1) - 1)) u.val = 0
  rw [show 2 * (-(k + 1) - 1) = -2 * (k + 1) - 2 by omega]
  exact Lattice.NormFourZhuAlgebra.Core.high_coefficient_zero D hu 2 _
    (signed_axis_grade_two hu ha) u.val
    ((actual_grade_one_eq_parity_minus_energy_two D hu h24).ge u.property)
    (k + 1) (by omega)

private theorem oddAxisMode_zero_on_eigenspace (hs : s ^ 2 = 1) {h : ℂ} (u : W h) :
    oddAxisMode D hu a s 0 (ι u.val) = h • ι u.val := by
  apply Subtype.ext
  have hp := (actual_parity_minus_energy_two_multiplicities D hu h24 a ha s hs).1 u.val
  have hv := congrArg (fun x : E => x.val) (Module.End.mem_eigenspace_iff.mp u.property)
  exact hp.symm.trans hv

/-- The actual two-twisted mode three on physical energy two is the
ordered twisted form times the fixed vacuum. -/
theorem originalI_three_energyTwo (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (h24 : D.rank = 24) (u v : E) :
    originalI D hu hD 3 (ι u) (ι v) = B u v • fixedVacuum D := by
  let vac : MixedIntertwiner.fixedGrade D 0 := gradeVacuum D
  have hu₂ : actualTensorL0 D hu u.val = (2 : ℂ) • u.val :=
    Module.End.mem_eigenspace_iff.mp u.property.2
  have hv₂ : actualTensorL0 D hu v.val = (2 : ℂ) • v.val :=
    Module.End.mem_eigenspace_iff.mp v.property.2
  rw [originalI_three_eq_vacuum_smul D hu hD h24 (ι u) (ι v) hu₂ hv₂ vac rfl,
    weight_two_vacuum_pairing D hu h24 (ι u) (ι v) hu₂ hv₂ vac rfl]
  rfl

private def vacuumDetector (D : LatticeData) : FixedCarrier D →ₗ[ℂ] ℂ :=
  ((sourcePairing D).flip (vacuum D)).comp (fixedSpace D).subtype

private theorem vacuumDetector_axis_nonpos (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (ha : bilinear D a a = 4) (k : ℤ) (hk : k ≤ 0) (z : FixedCarrier D) :
    vacuumDetector D (fixedMode D (normFourFixedSource D a s) (k + 1) z) = 0 := by
  let e := normFourFixedSource D a s
  have he : e.val ∈ LatticePositiveEnergy.grade D 2 := signed_axis_grade_two hu ha
  change sourcePairing D (((LatticeAllStateField.Y D e.val)[[k + 1]]) z.val) (vacuum D) = 0
  rw [← LatticePositiveEnergy.sum_gradeProjections D z.val]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  let x := LatticePositiveEnergy.gradeProjection D n z.val
  have hx := LatticePositiveEnergy.gradeProjection_mem D n z.val
  by_cases hz : n - k = 0
  · have hn₀ := LatticePositiveEnergy.stateEnergies_nonneg hD z.val n hn
    have hnz : n = 0 := by omega
    have hkz : k = 0 := by omega
    have hx₀ : x ∈ LatticePositiveEnergy.grade D 0 := by
      rw [← hnz]
      exact hx
    rw [LatticePositiveEnergy.grade_zero D hD] at hx₀
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx₀
    change sourcePairing D (((LatticeAllStateField.Y D e.val)[[k + 1]]) x) (vacuum D) = 0
    rw [hkz, zero_add, ← hc, map_smul]
    have hzero := congrArg (fun w : FixedCarrier D => w.val) (fixed_creativity D e 1 (by omega))
    rw [fixedY_mode_val] at hzero
    change (((LatticeAllStateField.Y D e.val)[[1]]) (vacuum D)) = 0 at hzero
    simp only [hzero, smul_zero, map_zero, LinearMap.zero_apply]
  · have hg := LatticePositiveEnergy.positive_actual_mode_grade D hD 2 n
      (k + 1) e.val x he hx
    rw [show (2 : ℤ) + n - (k + 1) - 1 = n - k by omega] at hg
    exact SourceBPZ.SourcePairingLaws.sourcePairing_grade D _ _ hz _ _ hg
      (gradeVacuum D).property.1

private theorem vacuumPairing_offDiagonal
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (hs : s ^ 2 = 1) {h j : ℂ}
    (hh : Allowed h) (hj : Allowed j) (hne : h ≠ j) (u : W h) (v : W j) :
    B u.val v.val = 0 := by
  have hEll0 (z : FixedCarrier D) :
      vacuumDetector D (fixedMode D (normFourFixedSource D a s) 1 z) = 0 * vacuumDetector D z := by
    simpa only [zero_add, zero_mul] using
      vacuumDetector_axis_nonpos hu (s := s) hD ha 0 le_rfl z
  by_contra hB
  have hNonzero : vacuumDetector D (originalI D hu hD 3 (ι u.val) (ι v.val)) ≠ 0 := by
    have hVac : vacuumDetector D (fixedVacuum D) = 1 := sourcePairing_vacuum D
    rwa [originalI_three_energyTwo hD h24, map_smul, hVac, smul_eq_mul, mul_one]
  have tab := originalI_ising_primary_selection (hD := hD) (a := a) (s := s)
    h24 (vacuumDetector D) hEll0
    (fun k hk z => vacuumDetector_axis_nonpos hu hD ha k (le_of_lt hk) z)
    ha hs 3 (ι u.val) (ι v.val) (oddAxisMode_zero_on_eigenspace hs u)
    (oddAxisMode_zero_on_eigenspace hs v)
    (fun k hk => oddAxisMode_pos_eq_zero_energyTwo u.val k hk h24 ha)
    (fun k hk => oddAxisMode_pos_eq_zero_energyTwo v.val k hk h24 ha)
    hh hj (Or.inl rfl) hNonzero
  apply hne
  rcases tab with ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩ | ⟨h₁, h₂, _⟩ | ⟨_, hz⟩ | ⟨h₁, h₂, _⟩
  · exact h₁.trans h₂
  · exact h₁.symm.trans h₂.symm
  · exact h₁.trans h₂.symm
  · norm_num at hz
  · exact h₁.trans h₂.symm

/-- Two different allowed Ising weights have zero actual two-twisted mode three. -/
theorem originalI_three_offDiagonal (hs : s ^ 2 = 1) {h j : ℂ}
    (hh : Allowed h) (hj : Allowed j) (hne : h ≠ j) (u : W h) (v : W j) :
    originalI D hu hD 3 (ι u.val) (ι v.val) = 0 := by
  rw [originalI_three_energyTwo hD h24, vacuumPairing_offDiagonal hD hs hh hj hne u v,
    zero_smul]

private theorem energyTwo_left_radical (h24 : D.rank = 24) (u : E)
    (hr : ∀ v : E, B u v = 0) : u = 0 := by
  let b := actualAmbientBasis D hu
  have hu₁ : actualTensorL0 D hu u.val =
      ((D.rank : ℂ) / 16 + ((1 : ℤ) : ℂ) / 2) • u.val := by
    have hu₂ : actualTensorL0 D hu u.val = (2 : ℂ) • u.val :=
      Module.End.mem_eigenspace_iff.mp u.property.2
    rw [hu₂, h24]
    norm_num
  have hzero : (actualForm D hu).flip u.val = 0 := by
    apply b.ext
    intro i
    change actualForm D hu (b i) u.val = 0
    have hi := actual_basis_eigenvalue D hu i.1 i.2
    by_cases hi₁ : oddWeight D i.1 = 1
    · have hg : b i ∈ actualGrade D hu 1 := by
        rw [actualGrade, LinearMap.mem_ker]
        apply sub_eq_zero.mpr
        change actualTensorL0 D hu (b i) = ((D.rank : ℂ) / 16 + ((1 : ℕ) : ℂ) / 2) • b i
        simpa only [hi₁, Prod.eta, b] using hi
      exact hr ⟨b i, (actual_grade_one_eq_parity_minus_energy_two D hu h24).le hg⟩
    · exact ActualOddGradeOrthogonality.actualForm_oddGrade_orthogonal D hu
        (oddWeight D i.1 : ℤ) 1 (b i) u.val
        (by simpa only [Int.cast_natCast] using hi) hu₁ (by exact_mod_cast hi₁)
  exact Subtype.ext ((actualForm_nondegenerate D hu).2 u.val
    (fun w => LinearMap.congr_fun hzero w))

/-- The actual vacuum pairing has zero left and right radicals on each of
the three allowed axis eigenspaces. -/
theorem vacuumPairing_nondegenerate (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hs : s ^ 2 = 1) {h : ℂ} (hh : Allowed h) :
    ((B).restrict (W h)).Nondegenerate := by
  have leftRadical (u : W h) (hr : ∀ v : W h, B u.val v.val = 0) : u = 0 := by
    apply Subtype.ext
    apply energyTwo_left_radical h24 u.val
    intro w
    let w' : actualGrade D hu 1 :=
      ⟨w.val, (actual_grade_one_eq_parity_minus_energy_two D hu h24).ge w.property⟩
    obtain ⟨hsum, _, hRange₀, hRange₁₆, hRange₁₂⟩ := actual_projectors_complete D hu a ha s hs
    let lift (j : ℂ) (p : Module.End ℂ (actualGrade D hu 1))
        (hrange : LinearMap.range p = (actualGradeOneZeroMode D hu a ha s).eigenspace j) : W j :=
      energyTwoEigenspaceEquiv D hu h24 a ha s j ⟨p w', hrange ▸ ⟨w', rfl⟩⟩
    let w₀ := lift 0 (actualProjectorZero D hu a s) hRange₀
    let w₁₆ := lift (1 / 16) (actualProjectorSixteen D hu a s) hRange₁₆
    let w₁₂ := lift (1 / 2) (actualProjectorHalf D hu a s) hRange₁₂
    have hw : w₀.val + w₁₆.val + w₁₂.val = w := by
      apply Subtype.ext
      exact congrArg (fun z : actualGrade D hu 1 => z.val) (LinearMap.congr_fun hsum w')
    have pair_zero {j : ℂ} (hj : Allowed j) (v : W j) : B u.val v.val = 0 := by
      by_cases heq : h = j
      · subst j
        exact hr v
      · exact vacuumPairing_offDiagonal hD hs hh hj heq u v
    rw [← hw, map_add, map_add, pair_zero (Or.inl rfl) w₀,
      pair_zero (Or.inr (Or.inr rfl)) w₁₆, pair_zero (Or.inr (Or.inl rfl)) w₁₂]
    simp
  refine ⟨leftRadical, ?_⟩
  intro v hv
  apply leftRadical v
  intro u
  change actualForm D hu u.val.val v.val.val = 0
  rw [(ActualPairingSymmetry.actualForm_symmetric D hu).eq]
  exact hv u

/-- Each nonzero vector in a physical energy-two Ising block has a partner
in that same block whose actual assembled mode-three product is the vacuum. -/
theorem exists_sameWeight_vacuum_partner (hs : s ^ 2 = 1) {h : ℂ} (hh : Allowed h)
    (u : W h) (hne : u ≠ 0) :
    ∃ v : W h, ((OriginalOrbifoldField.Y D hu hD (0, ι u.val))[[3]]) (0, ι v.val) =
      OriginalOrbifoldField.vacuumState D hu := by
  have hv : ∃ v : W h, B u.val v.val ≠ 0 := by
    by_contra! hall
    exact hne ((vacuumPairing_nondegenerate hD hs hh).1 u hall)
  obtain ⟨v, hv⟩ := hv
  let c := B u.val v.val
  have hc : c ≠ 0 := hv
  refine ⟨c⁻¹ • v, ?_⟩
  rw [OriginalOrbifoldField.Y_ncoeff_apply]
  simp only [map_zero, zero_add, add_zero]
  have hscale : ι ((c⁻¹ • v : W h).val) = c⁻¹ • ι v.val := by
    exact map_smul ι _ v.val
  rw [hscale, map_smul, originalI_three_energyTwo hD h24]
  change (c⁻¹ • (c • fixedVacuum D), 0) = (fixedVacuum D, 0)
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.FixedSourceIsing
