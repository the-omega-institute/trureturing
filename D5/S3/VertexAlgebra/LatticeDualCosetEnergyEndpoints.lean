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

set_option maxHeartbeats 4000000 in
/-- Complex eigenvalues outside the proved energy image have zero eigenspace. -/
theorem all_eigenspaces_finiteDimensional (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D=1) (hGH : gramComplex D * H=1)
    (μ : Fin D.rank → ℚ) (hDual : ∀ i,∑ j,(D.G i j : ℚ)*μ j=(β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (z : ℂ) :
    FiniteDimensional ℂ ((moduleL D β H 0).eigenspace z) := by
  classical
  by_cases hv : ∃ v : Carrier D, v ≠ 0 ∧ moduleL D β H 0 v=z • v
  · obtain ⟨n,hn⟩ := point_spectrum_subset D β H hHG hGH μ hDual hD z hv
    let e : ℚ := chargeWeight D μ (minimizingCharge D μ hD)+(n : ℚ)
    have he : z=(e : ℂ) := by
      simpa only [e,Rat.cast_add] using hn
    rw [he]
    exact eigenspace_finiteDimensional D β H hHG hGH μ hDual hD e
  · have hz : (moduleL D β H 0).eigenspace z = ⊥ := by
      apply (Submodule.eq_bot_iff _).mpr
      intro v he
      by_contra hn
      exact hv ⟨v,hn,(Module.End.mem_eigenspace_iff).mp he⟩
    rw [hz]
    infer_instance


/-- The half-shifted rank-one bottom contains two independent actual eigenvectors. -/
theorem half_shift_actual_bottom_multiplicity :
    let E := halfShiftLattice
    let μ : Fin E.rank → ℚ := fun _ => 1/2
    let H : Matrix (Fin E.rank) (Fin E.rank) ℂ := fun _ _ => 1/2
    (∀ γ : Charge E, 1/4 ≤ chargeWeight E μ γ) ∧
      ∃ v : Fin 2 → Carrier E, LinearIndependent ℂ v ∧
        ∀ t, moduleL E (fun _ => 1) H 0 (v t) = (1/4 : ℂ) • v t := by
  classical
  dsimp only
  let E := halfShiftLattice
  let μ : Fin E.rank → ℚ := fun _ => 1/2
  let H : Matrix (Fin E.rank) (Fin E.rank) ℂ := fun _ _ => 1/2
  have hHG : H * gramComplex E = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    change (∑ k : Fin 1,(1/2 : ℂ)*2)=1
    norm_num
  have hGH : gramComplex E * H = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    change (∑ k : Fin 1,(2 : ℂ)*(1/2))=1
    norm_num
  have hDual : ∀ i,∑ j,(E.G i j : ℚ)*μ j=((fun _ => 1 : Charge E) i : ℚ) := by
    intro i
    change (∑ k : Fin 1,(2 : ℚ)*(1/2))=1
    norm_num
  obtain ⟨γ,δ,hne,hγ,hδ,hmin⟩ := (half_shift_two_minima).2
  refine ⟨hmin,?_⟩
  let a : Fin 2 → Label E := fun t => (if t=0 then γ else δ,0)
  have ha : Function.Injective a := by
    intro s t h
    fin_cases s <;> fin_cases t
    · rfl
    · exact False.elim (hne (by simpa [a] using congrArg Prod.fst h))
    · exact False.elim (hne (by simpa [a] using (congrArg Prod.fst h).symm))
    · rfl
  refine ⟨fun t => carrierBasis E (a t),(carrierBasis E).linearIndependent.comp a ha,?_⟩
  intro t
  rw [moduleL_basis_zero E (fun _ => 1) H hHG hGH μ hDual]
  have hw : weight E μ (a t)=1/4 := by
    fin_cases t
    · simpa [a,weight,oscillatorEnergy,E,μ] using hγ
    · simpa [a,weight,oscillatorEnergy,E,μ] using hδ
  rw [hw]
  norm_num

end
end D5.S3.VertexAlgebra.LatticeDualCosetEnergy
