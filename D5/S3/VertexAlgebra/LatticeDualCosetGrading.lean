/- GID: D5/S3/VertexAlgebra/LatticeDualCosetGrading
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeDualCosetGrading
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual dual-coset modules decompose into finite-dimensional energy eigenspaces and obey all-state mode grading. -/

import D5.S3.VertexAlgebra.LatticeDualCosetPositiveEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace D5.S3.VertexAlgebra.LatticeDualCosetEnergy
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeSugawaraConformal LatticeSugawaraCurrents LatticeDualCosetConformal
open LatticeDualCosetModule
open scoped BigOperators VertexOperator DirectSum
noncomputable section

variable (D : LatticeData)

private def coefficientGrade {Q : Type*} [DecidableEq Q] (w : Label D → Q) (q : Q) :
    Submodule ℂ (Carrier D) :=
  (Finsupp.supported ℂ ℂ {a : Label D | w a=q}).comap (carrierCoeffEquiv D).toLinearMap

private theorem coefficient_mem {Q : Type*} [DecidableEq Q] (w : Label D → Q) (q : Q) (v : Carrier D) :
    v ∈ coefficientGrade D w q ↔
      ∀ a : Label D, w a ≠ q → carrierCoeffEquiv D v a=0 := by
  change carrierCoeffEquiv D v ∈ Finsupp.supported ℂ ℂ _ ↔ _
  exact Finsupp.mem_supported' ℂ _

private def coefficientProjection {Q : Type*} [DecidableEq Q] (w : Label D → Q) (q : Q) :
    Module.End ℂ (Carrier D) := by
  classical
  exact (carrierCoeffEquiv D).symm.toLinearMap.comp
    ((Finsupp.supported ℂ ℂ {a : Label D | w a=q}).subtype.comp
      ((Finsupp.restrictDom ℂ ℂ {a : Label D | w a=q}).comp
        (carrierCoeffEquiv D).toLinearMap))

private theorem projection_coeff {Q : Type*} [DecidableEq Q] (w : Label D → Q) (q : Q)
    (v : Carrier D) (a : Label D) :
    carrierCoeffEquiv D (coefficientProjection D w q v) a =
      if w a=q then carrierCoeffEquiv D v a else 0 := by
  classical
  simp [coefficientProjection,Finsupp.filter_apply]

private theorem projection_mem {Q : Type*} [DecidableEq Q] (w : Label D → Q) (q : Q) (v : Carrier D) :
    coefficientProjection D w q v ∈ coefficientGrade D w q := by
  rw [coefficient_mem]
  intro a ha
  simp [projection_coeff,ha]

private theorem projection_sum {Q : Type*} [DecidableEq Q] (w : Label D → Q) (v : Carrier D) :
    ∑ q ∈ (carrierCoeffEquiv D v).support.image w, coefficientProjection D w q v = v := by
  classical
  apply (carrierCoeffEquiv D).injective
  ext a
  change ((Finsupp.lapply a).comp (carrierCoeffEquiv D).toLinearMap)
    (∑ q ∈ (carrierCoeffEquiv D v).support.image w, coefficientProjection D w q v) = _
  rw [map_sum]
  change (∑ q ∈ (carrierCoeffEquiv D v).support.image w,
    carrierCoeffEquiv D (coefficientProjection D w q v) a) = _
  simp_rw [projection_coeff]
  by_cases ha : a ∈ (carrierCoeffEquiv D v).support
  · have he : w a ∈ (carrierCoeffEquiv D v).support.image w := Finset.mem_image.mpr ⟨a,ha,rfl⟩
    simp [Finset.sum_ite_eq',he]
  · simp [Finsupp.notMem_support_iff.mp ha]

private theorem coefficient_internal {Q : Type*} [DecidableEq Q] (w : Label D → Q) :
    DirectSum.IsInternal (coefficientGrade D w) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · intro q
    rw [disjoint_iff_inf_le]
    rintro v ⟨hv,ho⟩
    rw [Submodule.mem_bot]
    apply (carrierCoeffEquiv D).injective
    ext a
    by_cases ha : w a=q
    · let f : Carrier D →ₗ[ℂ] ℂ := (Finsupp.lapply a).comp (carrierCoeffEquiv D).toLinearMap
      have hle : (⨆ j ≠ q, coefficientGrade D w j) ≤ LinearMap.ker f := by
        apply iSup₂_le
        intro j hj x hx
        exact (coefficient_mem D w j x).mp hx a (by rw [ha]; exact Ne.symm hj)
      exact hle ho
    · exact (coefficient_mem D w q v).mp hv a ha
  · apply top_unique
    intro v _
    rw [← projection_sum D w v]
    apply Submodule.sum_mem
    intro q _
    exact (le_iSup (coefficientGrade D w) q) (projection_mem D w q v)

private def coefficientDecomposition {Q : Type*} [DecidableEq Q] (w : Label D → Q) :
    Carrier D ≃ₗ[ℂ] (⨁ q : Q, coefficientGrade D w q) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap (coefficientGrade D w))
    (coefficient_internal D w)).symm

/-- The global minimum is constructed from a finite nonempty sublevel. -/
def minimizingCharge (μ : Fin D.rank → ℚ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) : Charge D :=
  Classical.choose (attained_minimum D μ hD)

private theorem minimum_spec (μ : Fin D.rank → ℚ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    0 ≤ chargeWeight D μ (minimizingCharge D μ hD) ∧
      ∀ γ, chargeWeight D μ (minimizingCharge D μ hD) ≤ chargeWeight D μ γ :=
  Classical.choose_spec (attained_minimum D μ hD)

private def naturalLevel (β : Charge D) (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j=(β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Label D) : ℕ :=
  Classical.choose (weight_levels D β μ hDual (minimizingCharge D μ hD)
    (minimum_spec D μ hD).2 a)

private theorem naturalLevel_spec (β : Charge D) (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j=(β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Label D) :
    weight D μ a = chargeWeight D μ (minimizingCharge D μ hD) +
      (naturalLevel D β μ hDual hD a : ℚ) :=
  Classical.choose_spec (weight_levels D β μ hDual (minimizingCharge D μ hD)
    (minimum_spec D μ hD).2 a)

/-- Full all-state homogeneous covariance for every integer original input mode. -/
theorem actual_mode_grade (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D=1) (hGH : gramComplex D * H=1)
    (μ : Fin D.rank → ℚ) (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j=(β i : ℚ))
    (k q : ℤ) (e : ℚ) (a v : Carrier D)
    (ha : a ∈ grade D k) (hv : v ∈ rationalGrade D μ e) :
    ((action D β a)[[q]]) v ∈ rationalGrade D μ (e+(k : ℚ)-(q : ℚ)-1) := by
  apply (moduleL_eigen_iff D β H hHG hGH μ hDual _ _).mp
  have hea := (actualL0_eigen_iff_grade D H hHG hGH k a).mpr ha
  have hev := (moduleL_eigen_iff D β H hHG hGH μ hDual e v).mpr hv
  have h := LinearMap.congr_fun (energy_covariance D β H hHG hGH a q) v
  simp only [LinearMap.sub_apply,Module.End.mul_apply,hea,hev,map_smul,
    LinearMap.smul_apply,Pi.smul_apply] at h
  push_cast
  linear_combination (norm := module) h

/-- Finite-dimensional actual energy spaces and a natural-indexed internal decomposition. -/
theorem positive_energy (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D=1) (hGH : gramComplex D * H=1)
    (μ : Fin D.rank → ℚ) (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j=(β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    ∃ γ₀ : Charge D, let h := chargeWeight D μ γ₀;
      0≤h ∧ (∀ γ, h≤chargeWeight D μ γ) ∧
      (∀ a : Label D, ∃ n : ℕ, weight D μ a=h+(n : ℚ)) ∧
      (∀ e : ℚ, FiniteDimensional ℂ ((moduleL D β H 0).eigenspace (e : ℂ))) ∧
      Nonempty (Carrier D ≃ₗ[ℂ]
        (⨁ n : ℕ, (moduleL D β H 0).eigenspace ((h+(n : ℚ)) : ℂ))) := by
  classical
  let γ₀ := minimizingCharge D μ hD
  refine ⟨γ₀,(minimum_spec D μ hD).1,(minimum_spec D μ hD).2,
    weight_levels D β μ hDual γ₀ (minimum_spec D μ hD).2,
    eigenspace_finiteDimensional D β H hHG hGH μ hDual hD,?_⟩
  have he (n : ℕ) : coefficientGrade D (naturalLevel D β μ hDual hD) n =
      (moduleL D β H 0).eigenspace ((chargeWeight D μ γ₀+(n : ℚ)) : ℂ) := by
    ext v
    rw [Module.End.mem_eigenspace_iff]
    have hi := moduleL_eigen_iff D β H hHG hGH μ hDual
      (chargeWeight D μ γ₀+(n : ℚ)) v
    simp only [Rat.cast_add] at hi
    rw [hi]
    have hs : {a : Label D | naturalLevel D β μ hDual hD a=n} =
        {a : Label D | weight D μ a=chargeWeight D μ γ₀+(n : ℚ)} := by
      ext a
      rw [naturalLevel_spec D β μ hDual hD]
      simp only [add_left_cancel_iff,Nat.cast_inj]
    simp only [coefficientGrade,rationalGrade,hs]
  exact ⟨(coefficientDecomposition D (naturalLevel D β μ hDual hD)).trans
    (DirectSum.congrLinearEquiv (fun n => LinearEquiv.ofEq _ _ (he n)))⟩

end
end D5.S3.VertexAlgebra.LatticeDualCosetEnergy
