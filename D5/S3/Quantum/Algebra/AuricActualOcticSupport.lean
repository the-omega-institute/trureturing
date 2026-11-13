/- GID: D5/S3/Quantum/Algebra/AuricActualOcticSupport
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/AuricActualOcticSupport
   mirror-E: none(waiver:symbolic-support-connectivity)
   anchors: []
   utility: none
   digest: Strong connectivity of the same actual octic inverse-obstruction matrix. -/

import D5.S3.Quantum.Algebra.AuricActualOcticWindow

set_option autoImplicit false
noncomputable section

namespace D5.S3.Quantum.Algebra.AuricActualOcticWindow

open Module LinearMap
open scoped TensorProduct Classical

variable {F D : Type*} [Field F] [Field D] [Algebra F D]

section ActualSupport

variable (K : Type*) [Field K] [Algebra F K]
variable [FiniteDimensional F D] [CharZero F] [FiniteDimensional F K] [Normal F K]
variable [Algebra D K] [IsScalarTower F D K]

/-- The same actual inverse-obstruction matrix has strongly connected nonzero support,
including after extension of its coefficients to any field. -/
theorem general43_2_support (L : Type*) [Field L] [Algebra K L]
    (W : Submodule F D) (hD : finrank F D = 8) (hW : finrank F W = 4)
    (hE : {c : D | ∀ w ∈ W, c * w ∈ W} = Set.range (algebraMap F D))
    (a : D) (ha : a ∉ quotientSet W) :
    ∃ e : K ⊗[F] D ≃ₐ[K] ((D →ₐ[F] K) → K),
      (∀ (c : K) (d : D) (σ : D →ₐ[F] K), e (c ⊗ₜ[F] d) σ = c * σ d) ∧
      let n := e.toLinearMap ∘ₗ (actualOperator W hD hW a ha).baseChange K ∘ₗ e.symm.toLinearMap
      let N := LinearMap.toMatrix' n
      (∀ σ τ, Relation.ReflTransGen (fun i j => N i j ≠ 0) σ τ) ∧
      (∀ σ τ, Relation.ReflTransGen (fun i j => algebraMap K L (N i j) ≠ 0) σ τ) := by
  classical
  obtain ⟨_, e, he, hn⟩ := general43_2_cut_free K W hD hW hE a ha
  let U := (W.baseChange K).map e.toLinearMap
  let n := e.toLinearMap ∘ₗ (actualOperator W hD hW a ha).baseChange K ∘ₗ e.symm.toLinearMap
  let N := LinearMap.toMatrix' n
  change n.comp n = 0 ∧ n.range = U ∧ n.ker = U ∧ N * N = 0 ∧ N.rank = 4 ∧ _ at hn
  obtain ⟨_, hrange, hker, _, _, _, hstrict, _⟩ := hn
  have hΩ : Fintype.card (D →ₐ[F] K) = 8 := by
    apply (AlgHom.card_of_splits F D K _).trans hD
    intro d
    have hh := Normal.splits (inferInstance : Normal F K) (algebraMap D K d)
    rwa [minpoly.algebraMap_eq (algebraMap D K).injective] at hh
  have hU : finrank K U = 4 := by
    dsimp [U]
    rw [LinearEquiv.finrank_map_eq]
    rw [← (Submodule.toBaseChange.toLinearEquiv K W).finrank_eq,
      Module.finrank_baseChange, hW]
  have hcross (S : Finset (D →ₐ[F] K)) (hs : S.Nonempty) (ht : Sᶜ.Nonempty) :
      0 < (N.submatrix (fun i : S => (i : D →ₐ[F] K))
        (fun j : ↥(Sᶜ) => (j : D →ₐ[F] K))).rank := by
    have hl := cross_rank_bound U n hker hrange hΩ hU S
    have hu := hstrict S hs ht
    rw [← crossRank_matrix] at hl
    change S.card + 1 ≤ 2 * rowRank U S at hu
    change 2 * rowRank U S ≤ S.card +
      (N.submatrix (fun i : S => (i : D →ₐ[F] K))
        (fun j : ↥(Sᶜ) => (j : D →ₐ[F] K))).rank at hl
    omega
  have hreach : ∀ σ τ, Relation.ReflTransGen (fun i j => N i j ≠ 0) σ τ := by
    intro σ τ
    by_contra hnot
    let S : Finset (D →ₐ[F] K) := Finset.univ.filter
      (fun i => Relation.ReflTransGen (fun i j => N i j ≠ 0) i τ)
    have hmem (i : D →ₐ[F] K) : i ∈ S ↔
        Relation.ReflTransGen (fun i j => N i j ≠ 0) i τ := by simp [S]
    have hs : S.Nonempty := ⟨τ, (hmem τ).mpr .refl⟩
    have ht : Sᶜ.Nonempty := ⟨σ, Finset.mem_compl.mpr (by simpa [hmem] using hnot)⟩
    have hz : N.submatrix (fun i : ↥(Sᶜ) => (i : D →ₐ[F] K))
        (fun j : S => (j : D →ₐ[F] K)) = 0 := by
      ext i j
      change N i j = 0
      by_contra hij
      exact (Finset.mem_compl.mp i.property) ((hmem i).mpr
        (Relation.ReflTransGen.head hij ((hmem j).mp j.property)))
    have hh := hcross Sᶜ ht (by simpa using hs)
    simp only [compl_compl] at hh
    rw [hz, Matrix.rank_zero] at hh
    omega
  refine ⟨e, he, hreach, ?_⟩
  intro σ τ
  exact (hreach σ τ).mono (fun i j hij => by
    exact fun hz => hij ((algebraMap K L).injective (by simpa using hz)))

end ActualSupport

end D5.S3.Quantum.Algebra.AuricActualOcticWindow
