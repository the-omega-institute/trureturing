/- GID: D5/S3/Zeros/GRH/New/Selmer/RibetCramer
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/RibetCramer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.RibetCramer. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/RibetCramer.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.PartialDerivComm
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Ribet's method with congruent blocks and tied auxiliary primes (see
New.Selmer.RibetElement).

This file: Ribet's operator by Cramer's rule twice; normalising element; Amitsur for families. -/
seal Finset.univ Finset.sum Finset.prod


open Matrix Algebra Submodule Polynomial MonoidAlgebra Finset
variable {O Y σ G L R N Λ : Type*} [CommRing O] [Fintype σ] [Group G] [CommRing L] [Algebra O L]
  [CommRing R] [Algebra R L] {S : Subalgebra R (Y → L)} [Fintype N] [Ring Λ] [Algebra R Λ]

/-- The R-algebra isomorphism from N × N matrices whose entries are σ × σ matrices over L onto
(N × σ) × (N × σ) matrices over L, flattening blocks. -/
@[simps!] def blockFlattenAlgEquiv N [Fintype N] :
    Matrix N N (Matrix σ σ L) ≃ₐ[R] Matrix (N × σ) (N × σ) L :=
  { compRingEquiv .. with commutes' _ := (comp_diagonal_diagonal _).trans (diagonal_classical _) }

attribute [local simp] sub_mul det_apply' mul_assoc dotProduct add_mem Matrix.mul_apply

/-- Amitsur's formula for matrices: if all characteristic polynomials of ρ(w), w ∈ Λ, are
defined over R, so are those of square matrices over Λ read through ρ as block matrices.

Known result: Amitsur's formula for the characteristic polynomial of a sum (integrality
consequence). -/
lemma amitsur_charpoly_mem_matrix (ρ : Λ →ₐ[R] Matrix σ σ L) (c : ∀ w k, (ρ w).charpoly.coeff k ∈
    (algebraMap R L).range) (P : Matrix N N Λ) k :
    (comp N N σ σ L (P.map ρ)).charpoly.coeff k ∈ (algebraMap R L).range :=
  let φ := (blockFlattenAlgEquiv N).toAlgHom.comp ρ.mapMatrix; amitsur_charpoly_mem_of_span φ
    (top_unique fun P _ ↦ P.matrix_eq_sum_single ▸ sum_mem fun q _ ↦ subset_span fun k ↦ by
    erw [show φ _ = (φ 1).submatrix id (q, ·) * (φ P).submatrix (q, ·) id by
      ext ⟨⟩; simp [φ, one_apply, Matrix.sum_apply, Matrix.single, ite_and, -map_sum]
      aesop, ← coeff_X_pow_mul, charpoly_mul_comm', coeff_X_pow_mul', map_one, mul_submatrix_one 1]
    split; apply c (P q q); simp) P k

/-- Ribet's construction for representations u_x of O[G] with characteristic polynomials over S.
Let the O[G]-linear form V send the rows of M into 𝔞·V(w) plus the left ideal of r with all tr
u(rg) ∈ 𝒥. Some f ∈ S equals det u_x(M)·tr u_x(h) where u_x(𝔞h) = 0, and f·det u(V(w)) ∈ 𝒥. -/
lemma exists_ribet_element_cramer [Nonempty σ] (u : Y → O[G] →ₐ[O] Matrix σ σ O) (κ : O →+* S) (h₁ :
    (algebraMap S (Y → L)).comp κ = algebraMap ..) (h₂ : ∀ g k, (fun x ↦ ((u x (.single g 1)).map
    (algebraMap O L)).charpoly.coeff k) ∈ S) (𝒥 : Submodule S (Y → L)) w (V : _ →ₗ[O[G]] O[G]) β
    (hβ : ∀ x, β x = algebraMap O L (u x (V w)).det) : β ∈ S ∧ ∀ h (M : Matrix N N O[G]) {𝔞}, (∀ p,
    V (M p) ∈ span _ {r | ∀ g, (fun x ↦ algebraMap O _ (u x r * u x (.single g 1)).trace) ∈ 𝒥} ⊔
    .map (.mulRight O[G] (V w)) 𝔞) → ∃ f : S, (∀ x, (∀ m ∈ 𝔞, u x (m * h) = 0) → f.1 x =
    algebraMap O L (((comp ..) (M.map (u x))).det * (u x h).trace)) ∧ f.1 * β ∈ 𝒥 := by
  let ρ := lift S _ G (piRingEquiv.symm.toMonoidHom.comp (.pi ((lift ..).symm ∘
    (ofId O L).mapMatrix.comp ∘ u)))
  have c := amitsur_charpoly_mem_of_span ρ (eq_top_mono (span_mono (Set.range_subset_iff.2 fun g k ↦
    ⟨⟨_, h₂ g k⟩, by ext x; simpa [ρ] using! ext_iff.1 (charpoly_map (ρ (.single g 1))
    (Pi.evalRingHom _ x)) k⟩)) (basis ..).span_eq)
  let ι := mapRingHom G κ
  have he x r i j : ρ (ι r) i j x = algebraMap O L (u x r i j) := by
    rw [lift_unique' (u x)]
    induction r using induction_linear <;> simp_all +zetaDelta [S.smul_def, RingHom.ext_iff]
  obtain ⟨η, ⟨_, H⟩, ⟨rfl⟩⟩ := exists_adjugate_of_charpoly_mem ρ c (ι (V w))
  use by convert H; simp [*, funext_iff], fun h M _ hM ↦ ?_
  choose m hm _ using by simpa [Submodule.mem_sup, ← eq_sub_iff_add_eq] using hM
  obtain ⟨W, ⟨_, F⟩, rfl, ⟨e⟩⟩ := exists_adjugate_of_charpoly_mem ((blockFlattenAlgEquiv
    N).toAlgHom.comp ρ.mapMatrix) (amitsur_charpoly_mem_matrix ρ c) (M.map ι)
  have e i j : ρ _ = ρ _ := ext (congrFun₂ e ⟨i, ·⟩ ⟨j, ·⟩)
  let a := (⟨_, F⟩ : S) • 1 - ι ∘ w ᵥ* W ⬝ᵥ ι ∘ m
  obtain ⟨⟨⟩, rfl⟩ := trace_eq_neg_charpoly_coeff (ρ _) ▸ neg_mem (c (a * ι h) _)
  use ⟨_, ‹_›⟩, by simp! +contextual [a, Matrix.trace, sum_mul, *, map_mul ρ, ← ι.map_mul, -map_mul,
    (algebraMap ..).map_mul, S.smul_def]
  convert sum_mem fun p _ ↦ span_induction (p := fun r _ ↦ ∀ b, (ρ (b * ι r)).trace ∈ 𝒥)
    (fun r g b ↦ ?_) ?_ ?_ ?_ (hm p) (η * ι h * (ι ∘ w ᵥ* W) p)
  simp [← trace_sum, ← mul_sum]; rw [trace_mul_comm, (_ : ∑ _, _ = ρ (a * ι (V w)))]
  ext; simp [(ρ η).trace_mul_comm, S.smul_def, *]; ring
  simpa! [mulVec, vecMul, *, V.pi_apply_eq_sum_univ w, V.pi_apply_eq_sum_univ (M _),
    one_apply, smul_sum, apply_ite, sum_mul, a, mul_sub, -Matrix.mul_apply]
    using congr(ρ $((M.map ι).dotProduct_mulVec (_ ᵥ* W) _))
  induction b using induction_on
  convert g ‹_›; simp [↓(u _ r).trace_mul_comm, ← he, ι, Matrix.trace]
  all_goals simp +contextual [mul_add, add_mul, smul_mem, ← mul_assoc, ι.map_mul, -map_mul, *]

/-- The finitely supported function [γa] − y[a] + pΣ_g θ(g)[g] on G; paired with u − 1 it gives
(u(γa) − 1) − y(u(a) − 1) + pΣθ(g)(u(g) − 1). -/
noncomputable def ribetNormaliser (γ a : G) (y p : R) (θ : G →₀ ℕ) : G →₀ R :=
  .single (γ * a) 1 - .single a y + p • θ.linearCombination ℕ (.single · 1)
