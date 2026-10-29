/- GID: D5/S3/VertexAlgebra/LatticeDualCosetEnergyEndpoints
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeDualCosetEnergyEndpoints
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The constructed bottom is an actual eigenvalue in every rank and every complex eigenspace is finite dimensional. -/

import D5.S3.VertexAlgebra.LatticeDualCosetSpectrum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeDualCosetEnergy
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeDualCosetConformal
open LatticeSugawaraCurrents LatticeSugawaraConformal
open scoped BigOperators
noncomputable section
variable (D : LatticeData)

/-- The constructed minimum is an actual eigenvalue, including in rank zero. -/
theorem bottom_eigenvector (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D=1) (hGH : gramComplex D * H=1)
    (μ : Fin D.rank → ℚ) (hDual : ∀ i,∑ j,(D.G i j : ℚ)*μ j=(β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    ∃ v : Carrier D, v ≠ 0 ∧ moduleL D β H 0 v =
      (chargeWeight D μ (minimizingCharge D μ hD) : ℂ) • v := by
  let a : Label D := (minimizingCharge D μ hD,0)
  refine ⟨carrierBasis D a,(carrierBasis D).ne_zero a,?_⟩
  rw [moduleL_basis_zero D β H hHG hGH μ hDual]
  congr 1
  simp [a,weight,oscillatorEnergy]

/-- Complex eigenvalues outside the proved energy image have zero eigenspace. -/
theorem all_eigenspaces_finiteDimensional (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D=1) (hGH : gramComplex D * H=1)
    (μ : Fin D.rank → ℚ) (hDual : ∀ i,∑ j,(D.G i j : ℚ)*μ j=(β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (λ : ℂ) :
    FiniteDimensional ℂ ((moduleL D β H 0).eigenspace λ) := by
  classical
  by_cases hv : ∃ v : Carrier D, v ≠ 0 ∧ moduleL D β H 0 v=λ • v
  · obtain ⟨n,rfl⟩ := point_spectrum_subset D β H hHG hGH μ hDual hD λ hv
    exact eigenspace_finiteDimensional D β H hHG hGH μ hDual hD _
  · have hz : (moduleL D β H 0).eigenspace λ = ⊥ := by
      apply Submodule.eq_bot_iff.mpr
      intro v he
      by_contra hn
      exact hv ⟨v,hn,(Module.End.mem_eigenspace_iff).mp he⟩
    rw [hz]
    infer_instance

end
end D5.S3.VertexAlgebra.LatticeDualCosetEnergy
