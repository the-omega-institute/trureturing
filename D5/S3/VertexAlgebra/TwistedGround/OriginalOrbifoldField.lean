/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalOrbifoldField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalOrbifoldField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original four field blocks with lower truncation and vacuum on the two-sector sum. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCoefficients
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.FirstSourceClosure

/-! The fixed lattice sector and the negative twisted sector carry one
field with four original coefficient blocks. -/

set_option autoImplicit false
noncomputable section
open scoped VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldField

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeInvolution
open LatticeHalfFockCorrectedField
open HalfFock.LatticeHalfFockParityField MixedIntertwiner
open OriginalFourMChargeCoset (originalI originalI_truncation)
open StateFieldResidueReconstruction (integerBinomial)
open private mixedMode from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
open private rightTerm from D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew
open private vacuum_coeff from D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds

/-- The original fixed sector and the original negative twisted sector. -/
abbrev Carrier (D : LatticeData) (hu : IsUnit D.G.det) :=
  FixedCarrier D × paritySpace D hu (-1)

/-- The fixed-sector vacuum embedded in the two-sector carrier. -/
def vacuumState (D : LatticeData) (hu : IsUnit D.G.det) : Carrier D hu :=
  (fixedVacuum D, 0)

private def fixedModeInSource (D : LatticeData) (n : ℤ) :
    FixedCarrier D →ₗ[ℂ] Module.End ℂ (FixedCarrier D) :=
  (LinearMap.proj n).comp (VertexOperator.ncoeff.comp (fixedY D))

private theorem fixedY_ncoeff (D : LatticeData) (a : FixedCarrier D) (n : ℤ) :
    (fixedY D a)[[n]] = fixedMode D a n :=
  fixedField_ncoeff D a n

private theorem fixedModeInSource_apply (D : LatticeData) (n : ℤ) (a : FixedCarrier D) :
    fixedModeInSource D n a = fixedMode D a n :=
  fixedY_ncoeff D a n

private def blockMode {F T : Type*} [AddCommGroup F] [Module ℂ F]
    [AddCommGroup T] [Module ℂ T]
    (fixed : F →ₗ[ℂ] F →ₗ[ℂ] F) (mixed : F →ₗ[ℂ] T →ₗ[ℂ] T)
    (right : T →ₗ[ℂ] F →ₗ[ℂ] T) (twisted : T →ₗ[ℂ] T →ₗ[ℂ] F) :
    F × T →ₗ[ℂ] Module.End ℂ (F × T) where
  toFun a := ((fixed a.1).coprod (twisted a.2)).prod
    ((mixed a.1).comp (LinearMap.snd ℂ F T) + (right a.2).comp (LinearMap.fst ℂ F T))
  map_add' a b := by
    apply LinearMap.ext
    intro c
    simp only [LinearMap.prod_apply, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
    exact Prod.ext (add_add_add_comm _ _ _ _) (add_add_add_comm _ _ _ _)
  map_smul' z a := by
    apply LinearMap.ext
    intro b
    change
      (fixed (z • a.1) b.1 + twisted (z • a.2) b.2,
        mixed (z • a.1) b.2 + right (z • a.2) b.1) =
      (z • (fixed a.1 b.1 + twisted a.2 b.2), z • (mixed a.1 b.2 + right a.2 b.1))
    simp only [map_smul, LinearMap.smul_apply, smul_add]

/-- The four normalized mode blocks of the original two-sector field. -/
def mode (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℤ) :
    Carrier D hu →ₗ[ℂ] Module.End ℂ (Carrier D hu) :=
  blockMode (fixedModeInSource D n) (mixedMode D hu n)
    (originalRightCoefficient D hu n) (originalI D hu hD n)

private theorem mode_apply (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℤ) (a b : Carrier D hu) :
    mode D hu hD n a b =
      (fixedMode D a.1 n b.1 + originalI D hu hD n a.2 b.2,
        mixedMode D hu n a.1 b.2 + originalRightCoefficient D hu n a.2 b.1) := by
  change (fixedModeInSource D n a.1 b.1 + originalI D hu hD n a.2 b.2,
    mixedMode D hu n a.1 b.2 + originalRightCoefficient D hu n a.2 b.1) = _
  rw [fixedModeInSource_apply]

private theorem has_mode_tail {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : VertexOperator ℂ V) (v : V) : ∃ N : ℤ, ∀ n ≥ N, (A[[n]]) v = 0 := by
  let order := ((HahnModule.of ℂ).symm (A v)).order
  refine ⟨-order, fun n hn => VertexOperator.ncoeff_eq_zero_of_lt_order A n v ?_⟩
  change -n - 1 < order
  omega

/-- The mixed carrier has lower truncation for every pair of actual states. -/
theorem mode_tail (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a b : Carrier D hu) :
    ∃ N : ℤ, ∀ n ≥ N, mode D hu hD n a b = 0 := by
  obtain ⟨A, hA⟩ := has_mode_tail (fixedY D a.1) b.1
  obtain ⟨B, hB⟩ := has_mode_tail (fixedParitySlice D hu (-1) a.1) b.2
  obtain ⟨C, hC⟩ := has_mode_tail (fixedParitySlice D hu (-1) b.1) a.2
  let E : ℤ := (ActualEnergyRestrictedDual.maxOddWeight D hu a.2.val : ℤ) +
    (ActualEnergyRestrictedDual.maxOddWeight D hu b.2.val : ℤ) + 4
  let N := max (max A B) (max C E)
  refine ⟨N, fun n hn => ?_⟩
  have hAn := hA n ((le_max_left A B).trans ((le_max_left _ _).trans hn))
  have hBn := hB n ((le_max_right A B).trans ((le_max_left _ _).trans hn))
  have hCn : C ≤ n := (le_max_left C E).trans ((le_max_right _ _).trans hn)
  have hEn : E ≤ n := (le_max_right C E).trans ((le_max_right _ _).trans hn)
  have hI := originalI_truncation D hu hD a.2 b.2 n (by dsimp [E] at hEn; omega)
  have hR : originalRightCoefficient D hu n a.2 b.1 = 0 := by
    change (∑ᶠ ell, rightTerm D hu n a.2 b.1 ell) = 0
    apply finsum_eq_zero_of_forall_eq_zero
    intro ell
    have he : C ≤ n + (ell : ℤ) := by omega
    rw [rightTerm, show mixedMode D hu (n + (ell : ℤ)) b.1 a.2 = 0 from hC _ he,
      map_zero, smul_zero]
  rw [fixedY_ncoeff] at hAn
  change mixedMode D hu n a.1 b.2 = 0 at hBn
  rw [mode_apply, hAn, hI, hBn, hR, add_zero, add_zero]
  rfl

private def fieldFor (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Carrier D hu) :
    VertexOperator ℂ (Carrier D hu) :=
  VertexOperator.of_coeff (fun k => mode D hu hD (-k - 1) a) (by
    intro b
    obtain ⟨N, hN⟩ := mode_tail D hu hD a b
    refine ⟨-N, fun k hk => ?_⟩
    by_contra h
    exact hk (hN (-k - 1) (by omega)))

private theorem fieldFor_ncoeff (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Carrier D hu) (n : ℤ) :
    (fieldFor D hu hD a)[[n]] = mode D hu hD n a := by
  rw [fieldFor, VertexOperator.ncoeff_of_coeff, show -(-n - 1) - 1 = n by omega]

/-- The assembled field is linear in its state and has the actual sector modes. -/
def Y (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    Carrier D hu →ₗ[ℂ] VertexOperator ℂ (Carrier D hu) where
  toFun := fieldFor D hu hD
  map_add' a b := by
    apply HVertexOperator.coeff_inj
    funext k
    simp only [VertexOperator.coeff_eq_ncoeff, map_add, Pi.add_apply, fieldFor_ncoeff]
  map_smul' z a := by
    apply HVertexOperator.coeff_inj
    funext k
    simp only [VertexOperator.coeff_eq_ncoeff, map_smul, Pi.smul_apply, fieldFor_ncoeff,
      RingHom.id_apply]

@[simp] theorem Y_ncoeff (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Carrier D hu) (n : ℤ) :
    (Y D hu hD a)[[n]] = mode D hu hD n a :=
  fieldFor_ncoeff D hu hD a n

/-- The normalized coefficient of the assembled field on any two states. -/
theorem Y_ncoeff_apply (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℤ) (a b : Carrier D hu) :
    ((Y D hu hD a)[[n]]) b =
      (fixedMode D a.1 n b.1 + originalI D hu hD n a.2 b.2,
        ((fixedParitySlice D hu (-1) a.1)[[n]]) b.2 + originalRightCoefficient D hu n a.2 b.1) := by
  rw [Y_ncoeff]
  exact mode_apply D hu hD n a b

/-- A fixed source acts on each sector by its own fixed-source field. -/
theorem Y_fixed_ncoeff_apply (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℤ)
    (a : FixedCarrier D) (b : Carrier D hu) :
    ((Y D hu hD (a, 0))[[n]]) b =
      (fixedMode D a n b.1, ((fixedParitySlice D hu (-1) a)[[n]]) b.2) := by
  rw [Y_ncoeff_apply]
  simp only [map_zero, LinearMap.zero_apply, add_zero]

/-- The ordinary fixed-source Borcherds identity on the actual negative parity space. -/
theorem fixedParitySlice_borcherds (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : FixedCarrier D) (u : paritySpace D hu (-1)) (p q r : ℤ) :
    let ρ := fun (c : FixedCarrier D) (n : ℤ) => (fixedParitySlice D hu (-1) c)[[n]]
    let left := fun i : ℕ => integerBinomial p i • ρ (fixedMode D a (r+i) b) (p+q-i) u
    let first := fun i : ℕ =>
      (((-1 : ℂ)^i)*integerBinomial r i) • ρ a (p+r-i) (ρ b (q+i) u)
    let second := fun i : ℕ =>
      (((-1 : ℂ)^i)*integerBinomial r i) •
        (StateFieldResidueReconstruction.epsilon r • ρ b (q+r-i) (ρ a (p+i) u))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
        (∑ᶠ i : ℕ, left i) = ∑ᶠ i : ℕ,
          (((-1 : ℂ)^i)*integerBinomial r i) •
            (ρ a (p+r-i) (ρ b (q+i) u) -
              StateFieldResidueReconstruction.epsilon r • ρ b (q+r-i) (ρ a (p+i) u)) := by
  have eigen : theta D a.val = (-1 : ℂ) ^ (0 : ℤ) • a.val := by
    simpa only [zpow_zero, one_smul] using (mem_fixedSpace D a.val).mp a.property
  have native := LatticeHalfFockGroundRightCurrentTransport.first_eigen_arbitrary_second
    D hu a.val 0 eigen b.val 0
  unfold LatticeHalfFockGroundRightCurrentTransport.OriginalCompatible
    LatticeHalfFockGroundRightCurrentTransport.Calculus.fullLaw at native
  have binom (n : ℤ) (i : ℕ) : integerBinomial n i = Ring.choose (n : ℂ) i :=
    Ring.map_choose (Int.castRingHom ℂ) n i
  have h := native p q r u.val
  unfold LatticeHalfFockGroundRightCurrentTransport.Calculus.leftTerm
    LatticeHalfFockGroundRightCurrentTransport.Calculus.firstTerm
    LatticeHalfFockGroundRightCurrentTransport.Calculus.secondTerm
    LatticeHalfFockGroundRightCurrentTransport.residueWeight at h
  simp only [LatticeHalfFockPhysicalRescaling.physicalSlice_mode,
    Int.cast_zero, zero_div, add_zero, sub_zero, ← binom] at h
  let incl := (paritySpace D hu (-1)).subtype
  have injective : Function.Injective incl := Subtype.val_injective
  have incl_apply (v : paritySpace D hu (-1)) : incl v = v.val := rfl
  have mode_val (c : FixedCarrier D) (n : ℤ) (v : paritySpace D hu (-1)) :
      (((fixedParitySlice D hu (-1) c)[[n]]) v).val =
        (correctedField D hu c.val).coeff (-2*n-2) v.val := by
    change (correctedField D hu c.val).coeff (2*(-n-1)) v.val = _
    rw [show 2*(-n-1) = -2*n-2 by omega]
  have fixed_val (n : ℤ) :
      (fixedMode D a n b).val = LatticeAllStateReconstruction.mu D a.val n b.val := rfl
  have finite_lift (f : ℕ → paritySpace D hu (-1))
      (hf : Function.HasFiniteSupport (fun i => incl (f i))) :
      Function.HasFiniteSupport f := by
    apply hf.subset
    intro i hi hz
    exact hi (injective (hz.trans (map_zero incl).symm))
  have sum_map (f : ℕ → paritySpace D hu (-1)) :
      incl (∑ᶠ i, f i) = ∑ᶠ i, incl (f i) :=
    incl.toAddMonoidHom.map_finsum_of_injective injective f
  dsimp only
  refine ⟨finite_lift _ ?_, finite_lift _ ?_, finite_lift _ ?_, ?_⟩
  · simpa only [incl_apply, Submodule.coe_smul, mode_val, fixed_val] using h.1
  · simpa only [incl_apply, Submodule.coe_smul, mode_val] using h.2.1
  · simpa only [incl_apply, Submodule.coe_smul, mode_val,
      StateFieldResidueReconstruction.epsilon] using h.2.2.1
  · apply injective
    simp_rw [smul_sub]
    simp only [sum_map, incl_apply, Submodule.coe_sub, Submodule.coe_smul,
      mode_val, fixed_val, StateFieldResidueReconstruction.epsilon]
    rw [finsum_sub_distrib h.2.1 h.2.2.1]
    exact h.2.2.2

/-- All signed Borcherds coefficients of the assembled field on two fixed inputs
and one negative twisted input. -/
theorem Y_borcherds_vvm (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (a b : FixedCarrier D) (u : paritySpace D hu (-1)) (p q r : ℤ) :
    let x : Carrier D hu := (a, 0)
    let y : Carrier D hu := (b, 0)
    let z : Carrier D hu := (0, u)
    let μ := fun (c : Carrier D hu) (n : ℤ) => (Y D hu hD c)[[n]]
    let left := fun i : ℕ => integerBinomial p i • μ (μ x (r+i) y) (p+q-i) z
    let first := fun i : ℕ =>
      (((-1 : ℂ)^i)*integerBinomial r i) • μ x (p+r-i) (μ y (q+i) z)
    let second := fun i : ℕ =>
      (((-1 : ℂ)^i)*integerBinomial r i) •
        (StateFieldResidueReconstruction.epsilon r • μ y (q+r-i) (μ x (p+i) z))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
        (∑ᶠ i : ℕ, left i) = ∑ᶠ i : ℕ,
          (((-1 : ℂ)^i)*integerBinomial r i) •
            (μ x (p+r-i) (μ y (q+i) z) -
              StateFieldResidueReconstruction.epsilon r • μ y (q+r-i) (μ x (p+i) z)) := by
  let incl := LinearMap.inr ℂ (FixedCarrier D) (paritySpace D hu (-1))
  have incl_apply (v : paritySpace D hu (-1)) : incl v = (0, v) := rfl
  have injective : Function.Injective incl := LinearMap.inr_injective
  have smul_twisted (s : ℂ) (v : paritySpace D hu (-1)) :
      s • ((0, v) : Carrier D hu) = (0, s • v) := (map_smul incl s v).symm
  have sub_twisted (v w : paritySpace D hu (-1)) :
      ((0, v) : Carrier D hu) - (0, w) = (0, v - w) := (map_sub incl v w).symm
  have on_fixed (c d : FixedCarrier D) (n : ℤ) :
      ((Y D hu hD (c, 0))[[n]]) (d, 0) = (fixedMode D c n d, 0) := by
    rw [Y_fixed_ncoeff_apply]
    simp only [map_zero]
  have on_twisted (c : FixedCarrier D) (v : paritySpace D hu (-1)) (n : ℤ) :
      ((Y D hu hD (c, 0))[[n]]) (0, v) = (0, ((fixedParitySlice D hu (-1) c)[[n]]) v) := by
    rw [Y_fixed_ncoeff_apply]
    simp only [map_zero]
  have finite_map (f : ℕ → paritySpace D hu (-1)) (hf : Function.HasFiniteSupport f) :
      Function.HasFiniteSupport (fun i => incl (f i)) :=
    hf.subset (Function.support_comp_subset (map_zero incl) f)
  have sum_map (f : ℕ → paritySpace D hu (-1)) :
      incl (∑ᶠ i, f i) = ∑ᶠ i, incl (f i) :=
    incl.toAddMonoidHom.map_finsum_of_injective injective f
  obtain ⟨hl, hf, hs, h⟩ := fixedParitySlice_borcherds D hu a b u p q r
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [on_fixed, on_twisted, smul_twisted, incl_apply] using finite_map _ hl
  · simpa only [on_twisted, smul_twisted, incl_apply] using finite_map _ hf
  · simpa only [on_twisted, smul_twisted, incl_apply] using finite_map _ hs
  · simpa only [on_fixed, on_twisted, sum_map, smul_twisted, sub_twisted, incl_apply]
      using congrArg incl h

/-- A negative twisted source exchanges the two sectors by the original coefficients. -/
theorem Y_twisted_ncoeff_apply (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℤ)
    (u : paritySpace D hu (-1)) (b : Carrier D hu) :
    ((Y D hu hD (0, u))[[n]]) b =
      (originalI D hu hD n u b.2, originalRightCoefficient D hu n u b.1) := by
  rw [Y_ncoeff, mode_apply]
  have hzero : fixedMode D 0 n = 0 := by rw [← fixedModeInSource_apply, map_zero]
  simp only [hzero, map_zero, LinearMap.zero_apply, zero_add]

private theorem mixed_vacuum (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℤ) (v : paritySpace D hu (-1)) :
    mixedMode D hu n (fixedVacuum D) v = if n = -1 then v else 0 := by
  apply Subtype.ext
  change (correctedField D hu (LatticeAllStateField.vacuum D)).coeff
    (2 * (-n - 1)) v.val = _
  rw [vacuum_coeff]
  by_cases h : n = -1
  · simp [h]
  · have he : 2 * (-n - 1) ≠ 0 := by omega
    simp [h, he]

private theorem right_vacuum_ncoeff (D : LatticeData) (hu : IsUnit D.G.det)
    (u : paritySpace D hu (-1)) (n : ℤ) (hn : -1 ≤ n) :
    originalRightCoefficient D hu n u (fixedVacuum D) = if n = -1 then u else 0 := by
  classical
  change (∑ᶠ ell, rightTerm D hu n u (fixedVacuum D) ell) = _
  rw [finsum_eq_single _ 0]
  · by_cases he : n = -1
    · simp [he, rightTerm, mixed_vacuum]
    · simp [he, rightTerm, mixed_vacuum]
  · intro ell he
    have hn' : n + (ell : ℤ) ≠ -1 := by omega
    simp [rightTerm, mixed_vacuum, hn']

/-- The assembled vacuum field has only the identity mode. -/
theorem vacuum_ncoeff (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℤ) (b : Carrier D hu) :
    ((Y D hu hD (vacuumState D hu))[[n]]) b = if n = -1 then b else 0 := by
  rw [vacuumState, Y_fixed_ncoeff_apply]
  change (fixedMode D (fixedVacuum D) n b.1, mixedMode D hu n (fixedVacuum D) b.2) = _
  have h : fixedMode D (fixedVacuum D) n b.1 = if n = -1 then b.1 else 0 := by
    apply Subtype.ext
    rw [← fixedY_ncoeff, fixedY_mode_val]
    change ((LatticeAllStateField.Y D (LatticeAllStateField.vacuum D))[[n]]) b.1.val = _
    rw [stateField_vacuum, identity_modes]
    split_ifs <;> rfl
  simp only [h, mixed_vacuum]
  by_cases hn : n = -1 <;> simp [hn]

/-- Creation and regularity on the assembled vacuum. -/
theorem creation_ncoeff (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Carrier D hu)
    (n : ℤ) (hn : -1 ≤ n) :
    ((Y D hu hD a)[[n]]) (vacuumState D hu) = if n = -1 then a else 0 := by
  rw [Y_ncoeff_apply]
  have h : fixedMode D a.1 n (fixedVacuum D) = if n = -1 then a.1 else 0 := by
    rw [← fixedY_ncoeff]
    by_cases he : n = -1
    · simpa [he] using fixed_creation D a.1
    · rw [ite_eq_right he]
      exact fixed_creativity D a.1 n (by omega)
  simp only [vacuumState, h, right_vacuum_ncoeff D hu a.2 n hn, map_zero, add_zero, zero_add]
  by_cases he : n = -1 <;> simp [he]

#print axioms Y
#print axioms Y_ncoeff_apply
#print axioms Y_fixed_ncoeff_apply
#print axioms fixedParitySlice_borcherds
#print axioms Y_borcherds_vvm
#print axioms Y_twisted_ncoeff_apply
#print axioms mode_tail
#print axioms vacuum_ncoeff
#print axioms creation_ncoeff

end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldField
