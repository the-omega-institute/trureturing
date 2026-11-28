/- GID: D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/NormalizedLaplacian
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/NormalizedLaplacian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized-Laplacian cospectrality in both closed-neighborhood corona orders. -/

module

public import D5.S3.Combinatorics.SpectralGraph.ClosedNeighborhoodCorona.Blocks
public import D5.S3.Combinatorics.SpectralGraph.ClosedNeighborhoodCorona.RegularIntertwiner
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import OmegaBuild.Commands

/-! # Normalized Laplacian of a closed-neighborhood corona

The inverse square root of the degree is zero at isolated vertices, as in
the survey's normalized Laplacian convention.
-/

compile_only_with_mathlib

set_option autoImplicit false

open Matrix
open scoped Kronecker

namespace ClosedNeighborhoodCorona

public section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The inverse square-root degree, with the value at zero fixed to zero. -/
private noncomputable def inverseSqrtDegree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℝ :=
  if G.degree v = 0 then 0 else (Real.sqrt (G.degree v : ℝ))⁻¹

/-- The diagonal inverse-square-root degree matrix. -/
private noncomputable def degreeScale (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  diagonal (inverseSqrtDegree G)

/-- The normalized Laplacian, with isolated vertices contributing zero rows. -/
noncomputable def normalizedLaplacian (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  degreeScale G * (diagonal (fun v => (G.degree v : ℝ)) - G.adjMatrix ℝ) * degreeScale G

private theorem charpoly_of_orthogonal_intertwining
    {A B U : Matrix V V ℝ} (h₁ : Uᵀ * U = 1) (h₂ : U * Uᵀ = 1)
    (h : U * A = B * U) : A.charpoly = B.charpoly := by
  apply Matrix.charpoly_eq_of_mul_eq_mul (P := Uᵀ)
  · have hd : Uᵀ.det * U.det = 1 := by
      rw [← det_mul, h₁, det_one]
    intro hz
    rw [hz, zero_mul] at hd
    exact zero_ne_one hd
  · calc
      A * Uᵀ = (Uᵀ * U) * A * Uᵀ := by rw [h₁, one_mul]
      _ = Uᵀ * (U * A) * Uᵀ := by rw [Matrix.mul_assoc Uᵀ U A]
      _ = Uᵀ * B := by rw [h, Matrix.mul_assoc Uᵀ, Matrix.mul_assoc B, h₂, mul_one]

/-- A block-diagonal lift of an orthogonal map on the base and its copies. -/
private noncomputable def blockLift (U : Matrix V V ℝ) (W : Type*) [DecidableEq W] :
    Matrix (V ⊕ (V × W)) (V ⊕ (V × W)) ℝ :=
  fromBlocks U 0 0 (U ⊗ₖ (1 : Matrix W W ℝ))

private theorem blockLift_orthogonal {W : Type*} [Fintype W] [DecidableEq W]
    {U : Matrix V V ℝ} (h₁ : Uᵀ * U = 1) (h₂ : U * Uᵀ = 1) :
    (blockLift U W)ᵀ * blockLift U W = 1 ∧
      blockLift U W * (blockLift U W)ᵀ = 1 := by
  simp [blockLift, fromBlocks_transpose, fromBlocks_multiply, ← kroneckerMap_transpose,
    ← mul_kronecker_mul, h₁, h₂, fromBlocks_one]

private theorem blockLift_adjacency
    {W : Type*} [Fintype W] [DecidableEq W]
    (G₁ G₂ : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] [DecidableRel H.Adj]
    {U : Matrix V V ℝ} (hU : U * G₁.adjMatrix ℝ = G₂.adjMatrix ℝ * U) :
    blockLift U W * (corona G₁ H).adjMatrix ℝ =
      (corona G₂ H).adjMatrix ℝ * blockLift U W := by
  let C₁ := G₁.adjMatrix ℝ + 1
  let C₂ := G₂.adjMatrix ℝ + 1
  have hC : U * C₁ = C₂ * U := by
    simp [C₁, C₂, Matrix.mul_add, Matrix.add_mul, hU]
  have hC₁ : C₁.IsSymm := by
    simp [IsSymm, C₁, G₁.isSymm_adjMatrix.eq]
  have hC₂ : C₂.IsSymm := by
    simp [IsSymm, C₂, G₂.isSymm_adjMatrix.eq]
  have hUpper :
      U * (of fun v (p : V × W) => C₁ v p.1) =
        (of fun v (p : V × W) => C₂ v p.1) * (U ⊗ₖ (1 : Matrix W W ℝ)) := by
    ext v ⟨u, w⟩
    simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply] using
      congrFun (congrFun hC v) u
  have hLower :
      (U ⊗ₖ (1 : Matrix W W ℝ)) * (of fun v (p : V × W) => C₁ v p.1)ᵀ =
        (of fun v (p : V × W) => C₂ v p.1)ᵀ * U := by
    ext ⟨v, w⟩ u
    simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, hC₁.apply,
      hC₂.apply] using congrFun (congrFun hC v) u
  simp only [C₁, C₂] at hUpper hLower
  rw [adjMatrix_corona, adjMatrix_corona]
  simp only [blockLift, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add,
    add_zero, ← mul_kronecker_mul, one_mul, mul_one, hU, hUpper, hLower]

private theorem normalized_laplacian_charpoly_of_intertwining
    {K₁ K₂ : SimpleGraph V} [DecidableRel K₁.Adj] [DecidableRel K₂.Adj]
    {P : Matrix V V ℝ} (h₁ : Pᵀ * P = 1) (h₂ : P * Pᵀ = 1)
    (hScale : P * degreeScale K₁ = degreeScale K₂ * P)
    (hCore : P * (diagonal (fun x => (K₁.degree x : ℝ)) - K₁.adjMatrix ℝ) =
      (diagonal (fun x => (K₂.degree x : ℝ)) - K₂.adjMatrix ℝ) * P) :
    (normalizedLaplacian K₁).charpoly = (normalizedLaplacian K₂).charpoly := by
  apply charpoly_of_orthogonal_intertwining h₁ h₂
  unfold normalizedLaplacian
  rw [← Matrix.mul_assoc P, ← Matrix.mul_assoc P,
    hScale, Matrix.mul_assoc (degreeScale K₂), hCore,
    Matrix.mul_assoc (degreeScale K₂), Matrix.mul_assoc _ P, hScale]
  simp only [Matrix.mul_assoc]

/- The following algebraic bridge isolates the only degree-scaling obligation.
The degree calculation includes the zero-degree branch. -/
private theorem normalized_laplacian_similarity_of_block
    {W : Type*} [Fintype W] [DecidableEq W]
    {G₁ G₂ : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] [DecidableRel H.Adj]
    {U : Matrix V V ℝ}
    (h₁ : Uᵀ * U = 1) (h₂ : U * Uᵀ = 1)
    (hScale : blockLift U W * degreeScale (corona G₁ H) =
      degreeScale (corona G₂ H) * blockLift U W)
    (hCore : blockLift U W *
      (diagonal (fun x => ((corona G₁ H).degree x : ℝ)) -
        (corona G₁ H).adjMatrix ℝ) =
      (diagonal (fun x => ((corona G₂ H).degree x : ℝ)) -
        (corona G₂ H).adjMatrix ℝ) * blockLift U W) :
    (normalizedLaplacian (corona G₁ H)).charpoly =
      (normalizedLaplacian (corona G₂ H)).charpoly := by
  obtain ⟨hLift₁, hLift₂⟩ := blockLift_orthogonal h₁ h₂ (W := W)
  exact normalized_laplacian_charpoly_of_intertwining hLift₁ hLift₂ hScale hCore

omit [DecidableEq V] in
private theorem degree_eq_of_regular_intertwiner
    {G₁ G₂ : SimpleGraph V} [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    {d₁ d₂ : ℕ} (hG₁ : G₁.IsRegularOfDegree d₁) (hG₂ : G₂.IsRegularOfDegree d₂)
    {U : Matrix V V ℝ} (hAdj : U * G₁.adjMatrix ℝ = G₂.adjMatrix ℝ * U)
    (hOne : U *ᵥ (1 : V → ℝ) = 1) (v u : V) : G₁.degree v = G₂.degree u := by
  have rowSum {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
      (hG : G.IsRegularOfDegree d) : G.adjMatrix ℝ *ᵥ (1 : V → ℝ) = (d : ℝ) • 1 := by
    funext x
    change (G.adjMatrix ℝ *ᵥ Function.const V 1) x = (d : ℝ) * 1
    exact SimpleGraph.adjMatrix_mulVec_const_apply_of_regular hG
  have h := congrArg (fun M : Matrix V V ℝ => M *ᵥ (1 : V → ℝ)) hAdj
  simp only [← mulVec_mulVec, rowSum hG₁, mulVec_smul, hOne, rowSum hG₂] at h
  have hd : (d₁ : ℝ) = d₂ := by
    simpa using congrFun h v
  rw [hG₁.degree_eq, hG₂.degree_eq, Nat.cast_inj.mp hd]

private theorem diagonal_degree_intertwining
    {K₁ K₂ : SimpleGraph V} [DecidableRel K₁.Adj] [DecidableRel K₂.Adj]
    {P : Matrix V V ℝ} (hDegree : ∀ i j, P i j ≠ 0 → K₁.degree j = K₂.degree i)
    (f : ℕ → ℝ) :
    P * diagonal (fun j => f (K₁.degree j)) = diagonal (fun i => f (K₂.degree i)) * P := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : P i j = 0
  · rw [h, zero_mul, mul_zero]
  · rw [hDegree i j h, mul_comm]

private theorem blockLift_degree
    {W : Type*} [Fintype W] [DecidableEq W]
    {G₁ G₂ : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] [DecidableRel H.Adj]
    {U : Matrix V V ℝ} (hDegree : ∀ v u, G₁.degree u = G₂.degree v) :
    ∀ i j, blockLift U W i j ≠ 0 → (corona G₁ H).degree j = (corona G₂ H).degree i := by
  intro i j hij
  rcases i with v | ⟨v, w⟩ <;> rcases j with u | ⟨u, z⟩
  · simp only [degree_corona_inl, hDegree v u]
  · exact (hij rfl).elim
  · exact (hij rfl).elim
  · have hwz : w = z := by
      by_contra h
      apply hij
      simp [blockLift, Matrix.one_apply_ne h]
    subst z
    simp only [degree_corona_inr, hDegree v u]

/-- Adjacency-cospectral regular base graphs give normalized-Laplacian cospectral
closed-neighborhood coronas with the same attached graph. -/
private theorem normalized_laplacian_charpoly_corona_regular_base
    {W : Type*} [Fintype W] [DecidableEq W]
    (G₁ G₂ : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] [DecidableRel H.Adj]
    {d₁ d₂ : ℕ} (hG₁ : G₁.IsRegularOfDegree d₁) (hG₂ : G₂.IsRegularOfDegree d₂)
    (hχ : (G₁.adjMatrix ℝ).charpoly = (G₂.adjMatrix ℝ).charpoly) :
    (normalizedLaplacian (corona G₁ H)).charpoly =
      (normalizedLaplacian (corona G₂ H)).charpoly := by
  obtain ⟨U, h₁, h₂, hAdj, hOne⟩ := exists_orthogonal_adjacency_intertwiner G₁ G₂ hG₁ hG₂ hχ
  have hDegree := blockLift_degree (H := H)
    (U := U) (fun v u => degree_eq_of_regular_intertwiner hG₁ hG₂ hAdj hOne u v)
  apply normalized_laplacian_similarity_of_block h₁ h₂
  · exact diagonal_degree_intertwining hDegree
      (fun d => if d = 0 then 0 else (Real.sqrt (d : ℝ))⁻¹)
  · rw [Matrix.mul_sub, Matrix.sub_mul,
      diagonal_degree_intertwining hDegree (fun d => (d : ℝ)),
      blockLift_adjacency G₁ G₂ H hAdj]

private noncomputable def copyLift {W : Type*} [DecidableEq W] (U : Matrix V V ℝ) :
    Matrix (W ⊕ (W × V)) (W ⊕ (W × V)) ℝ :=
  fromBlocks 1 0 0 ((1 : Matrix W W ℝ) ⊗ₖ U)

private theorem copyLift_orthogonal {W : Type*} [Fintype W] [DecidableEq W]
    {U : Matrix V V ℝ} (h₁ : Uᵀ * U = 1) (h₂ : U * Uᵀ = 1) :
    (copyLift (W := W) U)ᵀ * copyLift U = 1 ∧
      copyLift (W := W) U * (copyLift U)ᵀ = 1 := by
  simp [copyLift, fromBlocks_transpose, fromBlocks_multiply, ← kroneckerMap_transpose,
    ← mul_kronecker_mul, h₁, h₂, fromBlocks_one]

private theorem copyLift_adjacency
    {W : Type*} [Fintype W] [DecidableEq W]
    (G₁ G₂ : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] [DecidableRel H.Adj]
    {U : Matrix V V ℝ} (h₁ : Uᵀ * U = 1)
    (hAdj : U * G₁.adjMatrix ℝ = G₂.adjMatrix ℝ * U)
    (hOne : U *ᵥ (1 : V → ℝ) = 1) :
    copyLift U * (corona H G₁).adjMatrix ℝ =
      (corona H G₂).adjMatrix ℝ * copyLift U := by
  have hTranspose : Uᵀ *ᵥ (1 : V → ℝ) = 1 := by
    calc
      Uᵀ *ᵥ (1 : V → ℝ) = Uᵀ *ᵥ (U *ᵥ (1 : V → ℝ)) := by rw [hOne]
      _ = 1 := by rw [mulVec_mulVec, h₁, one_mulVec]
  have hRow (v : V) : ∑ u, U v u = 1 := by
    simpa [mulVec, dotProduct] using congrFun hOne v
  have hCol (v : V) : ∑ u, U u v = 1 := by
    simpa [mulVec, dotProduct] using congrFun hTranspose v
  let B : Matrix W (W × V) ℝ := of fun w p => (H.adjMatrix ℝ + 1) w p.1
  have hUpper : B * ((1 : Matrix W W ℝ) ⊗ₖ U) = B := by
    ext w ⟨z, v⟩
    simp [B, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, ite_mul, mul_ite]
    let c := (H.adjMatrix ℝ + 1) w z
    calc
      (∑ x, c * U x v) = c * (∑ x, U x v) :=
        (Finset.mul_sum Finset.univ (fun x => U x v) c).symm
      _ = c := by rw [hCol, mul_one]
  have hLower : ((1 : Matrix W W ℝ) ⊗ₖ U) * Bᵀ = Bᵀ := by
    ext ⟨w, v⟩ z
    simp [B, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, ite_mul]
    let c := (H.adjMatrix ℝ + 1) z w
    calc
      (∑ x, U v x * c) = (∑ x, U v x) * c :=
        (Finset.sum_mul Finset.univ (fun x => U v x) c).symm
      _ = c := by rw [hRow, one_mul]
  rw [adjMatrix_corona, adjMatrix_corona]
  change
    copyLift U * fromBlocks (H.adjMatrix ℝ) B Bᵀ ((1 : Matrix W W ℝ) ⊗ₖ G₁.adjMatrix ℝ) =
      fromBlocks (H.adjMatrix ℝ) B Bᵀ ((1 : Matrix W W ℝ) ⊗ₖ G₂.adjMatrix ℝ) * copyLift U
  simp only [copyLift, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add,
    add_zero, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hAdj, hUpper, hLower]

omit [DecidableEq V] in
private theorem copyLift_degree
    {W : Type*} [Fintype W] [DecidableEq W]
    {G₁ G₂ : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] [DecidableRel H.Adj]
    {U : Matrix V V ℝ} (hDegree : ∀ v u, G₁.degree u = G₂.degree v) :
    ∀ i j, copyLift U i j ≠ 0 → (corona H G₁).degree j = (corona H G₂).degree i := by
  intro i j hij
  rcases i with w | ⟨w, v⟩ <;> rcases j with z | ⟨z, u⟩
  · have hwz : w = z := by
      by_contra h
      exact hij (Matrix.one_apply_ne h)
    subst z
    simp only [degree_corona_inl]
  · exact (hij rfl).elim
  · exact (hij rfl).elim
  · have hwz : w = z := by
      by_contra h
      apply hij
      simp [copyLift, Matrix.one_apply_ne h]
    subst z
    simp only [degree_corona_inr, hDegree v u]

/-- Adjacency-cospectral regular attached graphs give normalized-Laplacian
cospectral closed-neighborhood coronas over the same base graph. -/
private theorem normalized_laplacian_charpoly_corona_regular_attached
    {W : Type*} [Fintype W] [DecidableEq W]
    (G₁ G₂ : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] [DecidableRel H.Adj]
    {d₁ d₂ : ℕ} (hG₁ : G₁.IsRegularOfDegree d₁) (hG₂ : G₂.IsRegularOfDegree d₂)
    (hχ : (G₁.adjMatrix ℝ).charpoly = (G₂.adjMatrix ℝ).charpoly) :
    (normalizedLaplacian (corona H G₁)).charpoly =
      (normalizedLaplacian (corona H G₂)).charpoly := by
  obtain ⟨U, h₁, h₂, hAdj, hOne⟩ := exists_orthogonal_adjacency_intertwiner G₁ G₂ hG₁ hG₂ hχ
  obtain ⟨hLift₁, hLift₂⟩ := copyLift_orthogonal h₁ h₂ (W := W)
  have hDegree := copyLift_degree (H := H)
    (U := U) (fun v u => degree_eq_of_regular_intertwiner hG₁ hG₂ hAdj hOne u v)
  apply normalized_laplacian_charpoly_of_intertwining hLift₁ hLift₂
  · exact diagonal_degree_intertwining hDegree
      (fun d => if d = 0 then 0 else (Real.sqrt (d : ℝ))⁻¹)
  · rw [Matrix.mul_sub, Matrix.sub_mul,
      diagonal_degree_intertwining hDegree (fun d => (d : ℝ)),
      copyLift_adjacency G₁ G₂ H h₁ hAdj hOne]

private def coronaIso {X V' W W' : Type*}
    {G : SimpleGraph X} {G' : SimpleGraph V'} {H : SimpleGraph W} {H' : SimpleGraph W'}
    (e : G ≃g G') (f : H ≃g H') : corona G H ≃g corona G' H' where
  toEquiv := e.toEquiv.sumCongr (e.toEquiv.prodCongr f.toEquiv)
  map_rel_iff' := by
    intro i j
    rcases i with v | ⟨v, w⟩ <;> rcases j with u | ⟨u, z⟩
    · exact e.map_rel_iff
    · exact or_congr e.injective.eq_iff e.map_rel_iff
    · exact or_congr e.injective.eq_iff e.map_rel_iff
    · exact and_congr e.injective.eq_iff f.map_rel_iff

private theorem normalized_laplacian_charpoly_iso
    {V' : Type*} [Fintype V'] [DecidableEq V']
    {G : SimpleGraph V} {G' : SimpleGraph V'} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (e : G ≃g G') :
    (normalizedLaplacian G).charpoly = (normalizedLaplacian G').charpoly := by
  let R := Matrix.reindexAlgEquiv ℝ ℝ e.toEquiv
  have hDiag (f : ℕ → ℝ) :
      R (diagonal (fun v => f (G.degree v))) = diagonal (fun v => f (G'.degree v)) := by
    change (diagonal (fun v => f (G.degree v))).submatrix e.toEquiv.symm e.toEquiv.symm = _
    rw [submatrix_diagonal_equiv]
    congr 1
    funext v
    exact congrArg f (e.symm.degree_eq v)
  have hAdj : R (G.adjMatrix ℝ) = G'.adjMatrix ℝ := e.reindex_adjMatrix ℝ
  have hScale : R (degreeScale G) = degreeScale G' :=
    hDiag (fun d => if d = 0 then 0 else (Real.sqrt (d : ℝ))⁻¹)
  have hLap : R (normalizedLaplacian G) = normalizedLaplacian G' := by
    simp only [normalizedLaplacian, map_mul, map_sub, hScale, hDiag, hAdj]
  rw [← hLap]
  exact (Matrix.charpoly_reindex e.toEquiv _).symm

/-- Question 5.21 of Sason, Krupnik, Hamud and Berman. Adjacency-cospectral
regular graphs give normalized-Laplacian cospectral closed-neighborhood
coronas, both as the base and as the attached graph. -/
theorem normalized_laplacian_charpoly_corona
    {V' W : Type*} [Fintype V'] [Fintype W] [DecidableEq V'] [DecidableEq W]
    (G₁ : SimpleGraph V) (G₂ : SimpleGraph V') (H : SimpleGraph W)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] [DecidableRel H.Adj]
    {d₁ d₂ : ℕ} (hG₁ : G₁.IsRegularOfDegree d₁) (hG₂ : G₂.IsRegularOfDegree d₂)
    (hχ : (G₁.adjMatrix ℝ).charpoly = (G₂.adjMatrix ℝ).charpoly) :
    ((normalizedLaplacian (corona G₁ H)).charpoly =
      (normalizedLaplacian (corona G₂ H)).charpoly) ∧
    ((normalizedLaplacian (corona H G₁)).charpoly =
      (normalizedLaplacian (corona H G₂)).charpoly) := by
  have hCard : Fintype.card V = Fintype.card V' := by
    simpa only [Matrix.charpoly_natDegree_eq_dim] using congrArg Polynomial.natDegree hχ
  let e : V ≃ V' := Fintype.equivOfCardEq hCard
  let K := G₂.comap e
  let i : K ≃g G₂ := SimpleGraph.Iso.comap e G₂
  have hK : K.IsRegularOfDegree d₂ := fun v => (i.degree_eq v).symm.trans (hG₂.degree_eq (i v))
  have hKχ : (G₁.adjMatrix ℝ).charpoly = (K.adjMatrix ℝ).charpoly := by
    rw [hχ, ← i.reindex_adjMatrix ℝ, Matrix.charpoly_reindex]
  exact ⟨(normalized_laplacian_charpoly_corona_regular_base G₁ K H hG₁ hK hKχ).trans
      (normalized_laplacian_charpoly_iso (coronaIso i (RelIso.refl H.Adj))),
    (normalized_laplacian_charpoly_corona_regular_attached G₁ K H hG₁ hK hKχ).trans
      (normalized_laplacian_charpoly_iso (coronaIso (RelIso.refl H.Adj) i))⟩

end

end ClosedNeighborhoodCorona
