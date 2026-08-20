/- GID: D5/S3/Observer/Tomography/VectorShellEnergy
   generality: G
   mirror-B: D5/B/S3/Observer/Tomography/VectorShellEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Orthogonal Hilbert-sum components give shell energies and unit total mass. -/

import Mathlib.Analysis.InnerProductSpace.l2Space

/- Library-search audit trail (2026-08-18):
   * Pinned Mathlib supplies `lp.norm_rpow_eq_tsum` and
     `IsHilbertSum.linearIsometryEquiv`; both are applied directly below.
   * `OrthogonalFamily.norm_sum` and `summable_iff_norm_sq_summable` are exact
     finite and convergence support, while `Summable.tsum_sum` splits the two
     distinguished components from the countable shell family.
   * Repository search found finite-stage and one-step shell decompositions in
     `FiniteStageExpansion` and `InnovationEnergyRecurrence`, but no equal or
     stronger infinite energy identity with its unit-vector probability clause. -/

namespace D5.S3.Observer.Tomography.VectorShellEnergy

noncomputable section

open scoped lp

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]
variable {G : Fin 2 ⊕ ℕ -> Type v}
  [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℝ (G i)]

/-- The ambient vector contributed by one coordinate of an internal Hilbert sum. -/
noncomputable def hilbertSumComponent
    (V : ∀ i, G i →ₗᵢ[ℝ] H) (hV : IsHilbertSum ℝ G V)
    (i : Fin 2 ⊕ ℕ) (psi : H) : H :=
  V i (hV.linearIsometryEquiv psi i)

/-- The distinguished initial component. -/
noncomputable def initialComponent
    (V : ∀ i, G i →ₗᵢ[ℝ] H) (hV : IsHilbertSum ℝ G V)
    (psi : H) : H :=
  hilbertSumComponent V hV (Sum.inl 0) psi

/-- The component in the `n`-th extracted shell, where `n = 0` represents source shell one. -/
noncomputable def extractedComponent
    (V : ∀ i, G i →ₗᵢ[ℝ] H) (hV : IsHilbertSum ℝ G V)
    (n : ℕ) (psi : H) : H :=
  hilbertSumComponent V hV (Sum.inr n) psi

/-- The distinguished residual component after all finite shells. -/
noncomputable def residualComponent
    (V : ∀ i, G i →ₗᵢ[ℝ] H) (hV : IsHilbertSum ℝ G V)
    (psi : H) : H :=
  hilbertSumComponent V hV (Sum.inl 1) psi

/-- A complete orthogonal shell decomposition splits every vector's squared norm
into initial, countably extracted, and residual energies. For a unit vector the
same nonnegative weights have total mass one. -/
theorem vector_shell_energy_decomposition
    (V : ∀ i, G i →ₗᵢ[ℝ] H) (hV : IsHilbertSum ℝ G V) (psi : H) :
    (‖psi‖ ^ 2 =
      ‖initialComponent V hV psi‖ ^ 2 +
        ∑' n : ℕ, ‖extractedComponent V hV n psi‖ ^ 2 +
        ‖residualComponent V hV psi‖ ^ 2) ∧
      (‖psi‖ = 1 ->
        0 ≤ ‖initialComponent V hV psi‖ ^ 2 ∧
          (∀ n : ℕ, 0 ≤ ‖extractedComponent V hV n psi‖ ^ 2) ∧
          0 ≤ ‖residualComponent V hV psi‖ ^ 2 ∧
          ‖initialComponent V hV psi‖ ^ 2 +
            ∑' n : ℕ, ‖extractedComponent V hV n psi‖ ^ 2 +
            ‖residualComponent V hV psi‖ ^ 2 = 1) := by
  let w : lp G 2 := hV.linearIsometryEquiv psi
  let energy : Fin 2 ⊕ ℕ -> ℝ := fun i => ‖w i‖ ^ 2
  have htwo : 0 < (2 : ENNReal).toReal := by norm_num
  have hsummable : Summable energy := by
    simpa [energy] using (lp.memℓp w).summable htwo
  have hleft : Summable (energy ∘ Sum.inl) :=
    hsummable.comp_injective Sum.inl_injective
  have hright : Summable (energy ∘ Sum.inr) :=
    hsummable.comp_injective Sum.inr_injective
  have hsplit :
      (∑' i : Fin 2 ⊕ ℕ, energy i) =
        energy (Sum.inl 0) + energy (Sum.inl 1) +
          ∑' n : ℕ, energy (Sum.inr n) := by
    rw [Summable.tsum_sum hleft hright, tsum_fintype]
    simp only [Fin.sum_univ_two]
  have hnorm : ‖psi‖ ^ 2 = ∑' i : Fin 2 ⊕ ℕ, energy i := by
    calc
      ‖psi‖ ^ 2 = ‖w‖ ^ 2 := by rw [hV.linearIsometryEquiv.norm_map]
      _ = ∑' i : Fin 2 ⊕ ℕ, ‖w i‖ ^ 2 := by
        simpa using lp.norm_rpow_eq_tsum
          (p := (2 : ENNReal)) (by norm_num) w
      _ = ∑' i : Fin 2 ⊕ ℕ, energy i := by rfl
  have henergy :
      ‖psi‖ ^ 2 =
        ‖initialComponent V hV psi‖ ^ 2 +
          ∑' n : ℕ, ‖extractedComponent V hV n psi‖ ^ 2 +
          ‖residualComponent V hV psi‖ ^ 2 := by
    rw [hnorm, hsplit]
    simp only [initialComponent, extractedComponent, residualComponent,
      hilbertSumComponent, LinearIsometry.norm_map, w, energy]
    ring
  refine ⟨henergy, ?_⟩
  intro hunit
  refine ⟨sq_nonneg _, fun n => sq_nonneg _, sq_nonneg _, ?_⟩
  rw [← henergy, hunit]
  norm_num

/-- The hypotheses have a concrete model: the standard Hilbert basis of an `l2` space. -/
example :
    let I := Fin 2 ⊕ ℕ
    let E := lp (fun _ : I => ℝ) 2
    let b : HilbertBasis I ℝ E := default
    IsHilbertSum ℝ (fun _ : I => ℝ)
      (fun i => LinearIsometry.toSpanSingleton ℝ E (b.orthonormal.1 i)) := by
  dsimp
  exact (default : HilbertBasis (Fin 2 ⊕ ℕ) ℝ
      (lp (fun _ : Fin 2 ⊕ ℕ => ℝ) 2)).orthonormal.isHilbertSum
    (by rw [HilbertBasis.dense_span])

#print axioms vector_shell_energy_decomposition

end

end D5.S3.Observer.Tomography.VectorShellEnergy
