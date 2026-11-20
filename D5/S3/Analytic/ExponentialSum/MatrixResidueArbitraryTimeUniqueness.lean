import D5.S3.Analytic.ExponentialSum.SignedResidueRankBudget
import D5.S3.Analytic.ExponentialSum.SignedMomentRankUniqueness
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Arbitrary-time uniqueness for matrix residues

The orthogonal complement of the span of the difference ranges is their
common kernel. In coordinates for this splitting, only the upper block of
a difference can be nonzero. The common-block rank budget then applies on
the upper carrier, where the compressed differences have trivial common kernel.
-/

noncomputable section

open Matrix RHLinalg Submodule
open scoped BigOperators ComplexOrder

namespace MatrixResidueArbitraryTimeUniqueness

variable {d : Type*} [Fintype d]

private theorem rotation_mulVec_zero_iff [DecidableEq d] {k : Type*} [Fintype k]
    (U : Matrix d k ℂ) (hUU : U * Uᴴ = 1) (M : Matrix d d ℂ) (z : k → ℂ) :
    (Uᴴ * M * U) *ᵥ z = 0 ↔ M *ᵥ (U *ᵥ z) = 0 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro hz
    have h := congrArg (fun y : k → ℂ => U *ᵥ y) hz
    rwa [Matrix.mulVec_mulVec _ U Uᴴ, hUU, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  · intro hz
    rw [hz, Matrix.mulVec_zero]

/-- One orthonormal change of coordinates supports a Hermitian family on
the span of its actual ranges. The upper blocks have trivial common kernel. -/
theorem exists_supported_rotation [DecidableEq d] {ι : Type*}
    (D : ι → Matrix d d ℂ) (hD : ∀ i, (D i).IsHermitian) :
    ∃ (w c : ℕ) (U : Matrix d (Fin w ⊕ Fin c) ℂ),
      w + c = Fintype.card d ∧
      w = Module.finrank ℂ ↥(⨆ i, LinearMap.range (D i).toEuclideanLin) ∧
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      (∀ i, Uᴴ * D i * U = fromBlocks (Uᴴ * D i * U).toBlocks₁₁ 0 0 0) ∧
      (∀ v : Fin w → ℂ, (∀ i, (Uᴴ * D i * U).toBlocks₁₁ *ᵥ v = 0) → v = 0) := by
  classical
  let T : ι → EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d :=
    fun i => (D i).toEuclideanLin
  let W := ⨆ i, LinearMap.range (T i)
  have hRangeOrthogonal (i : ι) : (LinearMap.range (T i))ᗮ = LinearMap.ker (T i) :=
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hD i)).orthogonal_range
  have hOrthogonal : Wᗮ = ⨅ i, LinearMap.ker (T i) := by
    dsimp only [W]
    rw [← Submodule.iInf_orthogonal]
    simp only [hRangeOrthogonal]
  let w := Module.finrank ℂ W
  let c := Module.finrank ℂ Wᗮ
  let bW := stdOrthonormalBasis ℂ W
  let bC := stdOrthonormalBasis ℂ Wᗮ
  let b : OrthonormalBasis (Fin w ⊕ Fin c) ℂ (EuclideanSpace ℂ d) :=
    (bW.prod bC).map W.orthogonalDecomposition.symm
  have hLeft (j : Fin w) : b (Sum.inl j) ∈ W := by
    simp [b, OrthonormalBasis.prod_apply]
  have hRight (j : Fin c) : b (Sum.inr j) ∈ Wᗮ := by
    simp [b, OrthonormalBasis.prod_apply]
  let a := EuclideanSpace.basisFun d ℂ
  let U : Matrix d (Fin w ⊕ Fin c) ℂ := a.toBasis.toMatrix b.toBasis
  have hU : Uᴴ * U = 1 := a.toMatrix_orthonormalBasis_conjTranspose_mul_self b
  have hUU : U * Uᴴ = 1 := a.toMatrix_orthonormalBasis_self_mul_conjTranspose b
  have hCard : w + c = Fintype.card d := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      Fintype.card_congr (b.toBasis.indexEquiv a.toBasis)
  have hEntry (i : d) (j : Fin w ⊕ Fin c) : U i j = b j i := by
    simp only [U, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, a, EuclideanSpace.basisFun_repr]
  have hColumn (j : Fin w ⊕ Fin c) :
      WithLp.toLp 2 (U *ᵥ Pi.single j 1) = b j := by
    rw [Matrix.mulVec_single_one]
    apply (WithLp.linearEquiv 2 ℂ (d → ℂ)).injective
    exact funext fun i => hEntry i j
  have hLift (z : Fin w ⊕ Fin c → ℂ) :
      WithLp.toLp 2 (U *ᵥ z) = ∑ j, z j • b j := by
    apply (WithLp.linearEquiv 2 ℂ (d → ℂ)).injective
    rw [map_sum]
    simp_rw [map_smul]
    change U *ᵥ z = ∑ j, z j • WithLp.ofLp (b j)
    funext i
    simp only [Matrix.mulVec, dotProduct, hEntry, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, mul_comm]
  have hAction (i : ι) (z : Fin w ⊕ Fin c → ℂ) :
      T i (WithLp.toLp 2 (U *ᵥ z)) = 0 ↔ (Uᴴ * D i * U) *ᵥ z = 0 := by
    rw [rotation_mulVec_zero_iff U hUU]
    change WithLp.toLp 2 (D i *ᵥ (U *ᵥ z)) =
      WithLp.toLp 2 (0 : d → ℂ) ↔ _
    exact ⟨fun h => congrArg (fun y : EuclideanSpace ℂ d => WithLp.ofLp y) h,
      fun h => congrArg (WithLp.toLp 2) h⟩

  have hRightColumn (i : ι) (j : Fin c) (k : Fin w ⊕ Fin c) :
      (Uᴴ * D i * U) k (Sum.inr j) = 0 := by
    have hj := hRight j
    rw [hOrthogonal] at hj
    have hz : T i (b (Sum.inr j)) = 0 :=
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hj i)
    rw [← hColumn (Sum.inr j)] at hz
    have hv := (hAction i (Pi.single (Sum.inr j) 1)).mp hz
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using
      congrFun hv k
  have hSupported (i : ι) :
      Uᴴ * D i * U = fromBlocks (Uᴴ * D i * U).toBlocks₁₁ 0 0 0 := by
    let M := Uᴴ * D i * U
    have hM : M.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul U (hD i)
    have hBottomLeft (j : Fin c) (k : Fin w) : M (Sum.inr j) (Sum.inl k) = 0 := by
      have h := congrArg (fun N : Matrix (Fin w ⊕ Fin c) (Fin w ⊕ Fin c) ℂ =>
        N (Sum.inr j) (Sum.inl k)) hM.eq
      simpa only [Matrix.conjTranspose_apply, show M (Sum.inl k) (Sum.inr j) = 0
        from hRightColumn i j (Sum.inl k), star_zero] using h.symm
    change M = fromBlocks M.toBlocks₁₁ 0 0 0
    apply Matrix.ext
    intro j k
    cases j with
    | inl j =>
      cases k with
      | inl k => rfl
      | inr k => exact hRightColumn i k (Sum.inl j)
    | inr j =>
      cases k with
      | inl k => exact hBottomLeft j k
      | inr k => exact hRightColumn i k (Sum.inr j)

  refine ⟨w, c, U, hCard, rfl, hU, hUU, hSupported, ?_⟩
  intro v hv
  let z : Fin w ⊕ Fin c → ℂ := Sum.elim v 0
  let q : EuclideanSpace ℂ d := WithLp.toLp 2 (U *ᵥ z)
  have hqW : q ∈ W := by
    dsimp only [q]
    rw [hLift, Fintype.sum_sum_type]
    simp only [z, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero]
    exact W.sum_mem fun j _ => W.smul_mem (v j) (hLeft j)
  have hqPerp : q ∈ Wᗮ := by
    rw [hOrthogonal]
    apply (Submodule.mem_iInf _).mpr
    intro i
    apply LinearMap.mem_ker.mpr
    change T i (WithLp.toLp 2 (U *ᵥ z)) = 0
    apply (hAction i z).mpr
    have hUpper : z ∘ Sum.inl = v := rfl
    have hLower : z ∘ Sum.inr = 0 := rfl
    rw [hSupported i, Matrix.fromBlocks_mulVec, hUpper, hLower, hv i]
    apply funext
    intro j
    cases j <;> simp only [Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero, Sum.elim_inl,
      Sum.elim_inr, Pi.zero_apply]
  have hq : q = 0 := (Submodule.disjoint_def.mp W.orthogonal_disjoint) q hqW hqPerp
  have hz := congrArg (fun y : EuclideanSpace ℂ d => Uᴴ *ᵥ WithLp.ofLp y) hq
  have hz' : Uᴴ *ᵥ (U *ᵥ z) = Uᴴ *ᵥ 0 := hz
  rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec, Matrix.mulVec_zero] at hz'
  exact funext fun j => congrFun hz' (Sum.inl j)

private def rotate {k : Type*} [Fintype k] (U : Matrix d k ℂ) :
    Matrix d d ℂ →ₗ[ℝ] Matrix k k ℂ :=
  (mulRightLinearMap k ℝ U).comp (mulLeftLinearMap d ℝ Uᴴ)

private def upperBlock {a b : Type*} :
    Matrix (a ⊕ b) (a ⊕ b) ℂ →ₗ[ℝ] Matrix a a ℂ where
  toFun := Matrix.toBlocks₁₁
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem fromBlocks_of_isHermitian {a b : Type*}
    {M : Matrix (a ⊕ b) (a ⊕ b) ℂ} (hM : M.IsHermitian) :
    fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ (M.toBlocks₁₂)ᴴ M.toBlocks₂₂ = M := by
  have h : (M.toBlocks₁₂)ᴴ = M.toBlocks₂₁ := by
    apply Matrix.ext
    intro i j
    exact congrArg (fun N : Matrix (a ⊕ b) (a ⊕ b) ℂ =>
      N (Sum.inr i) (Sum.inl j)) hM.eq
  rw [h, Matrix.fromBlocks_toBlocks]

/-- Two finite PSD residue families with the stated rank budgets agree on
their carrier if they have equal moments at at least `2 * r + 2` distinct
real times. Positive definiteness of the first total suffices for the rank step. -/
theorem eq_on_carrier_of_exponential_moments
    (carrier times : Finset ℝ) (r : ℕ) (htimes : 2 * r + 2 ≤ times.card)
    (A B : ℝ → Matrix d d ℂ)
    (hA : ∀ x ∈ carrier, (A x).PosSemidef)
    (hB : ∀ x ∈ carrier, (B x).PosSemidef)
    (htotal : (∑ x ∈ carrier, A x).PosDef)
    (hbudgetA : (∑ x ∈ carrier, (A x).rank) ≤ Fintype.card d + r)
    (hbudgetB : (∑ x ∈ carrier, (B x).rank) ≤ Fintype.card d + r)
    (hmoment : ∀ t ∈ times,
      (∑ x ∈ carrier, Real.exp (-t * x) • A x) =
        ∑ x ∈ carrier, Real.exp (-t * x) • B x) :
    ∀ x ∈ carrier, A x = B x := by
  classical
  obtain ⟨w, c, U, hCard, _, hU, hUU, hSupported, hTrivial⟩ :=
    exists_supported_rotation (fun x : carrier => A x - B x)
      (fun x => (hA x x.property).isHermitian.sub (hB x x.property).isHermitian)
  let k := Fin w ⊕ Fin c
  have hUInjective : Function.Injective U.mulVec := by
    intro x y h
    have he := congrArg (fun z : d → ℂ => Uᴴ *ᵥ z) h
    simpa only [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec] using he
  have hRotateInjective : Function.Injective (rotate U) := by
    have hRecover (M : Matrix d d ℂ) : U * (rotate U M) * Uᴴ = M := by
      change U * (Uᴴ * M * U) * Uᴴ = M
      calc
        _ = (U * Uᴴ) * M * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
        _ = M := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
    intro M N h
    rw [← hRecover M, ← hRecover N, h]
  -- Zero extension allows the signed-moment theorem to use a family on all real rates.
  let extend (M : ℝ → Matrix d d ℂ) (x : ℝ) : Matrix d d ℂ :=
    if x ∈ carrier then M x else 0
  let A' := fun x => rotate U (extend A x)
  let B' := fun x => rotate U (extend B x)
  have hPSD (M : ℝ → Matrix d d ℂ) (hM : ∀ x ∈ carrier, (M x).PosSemidef) (x : ℝ) :
      (rotate U (extend M x)).PosSemidef := by
    have h : (extend M x).PosSemidef := by
      by_cases hx : x ∈ carrier
      · simpa only [extend, ite_eq_left hx] using hM x hx
      · simpa only [extend, ite_eq_right hx] using
          (Matrix.PosSemidef.zero : (0 : Matrix d d ℂ).PosSemidef)
    exact h.conjTranspose_mul_mul_same U
  let A₀ := fun x => (A' x).toBlocks₁₁
  let B₀ := fun x => (B' x).toBlocks₁₁
  let E := fun x => (A' x).toBlocks₁₂
  let C := fun x => (A' x).toBlocks₂₂
  let D := fun x => A₀ x - B₀ x
  let compress : Matrix d d ℂ →ₗ[ℝ] Matrix (Fin w) (Fin w) ℂ :=
    upperBlock.comp (rotate U)
  have hD (x : ℝ) : (D x).IsHermitian :=
    ((hPSD A hA x).isHermitian.submatrix (Sum.inl : Fin w → k)).sub
      ((hPSD B hB x).isHermitian.submatrix (Sum.inl : Fin w → k))
  have hRotateDiff (x : ℝ) (hx : x ∈ carrier) :
      rotate U (A x - B x) = A' x - B' x := by
    simpa only [A', B', extend, ite_eq_left hx] using map_sub (rotate U) (A x) (B x)
  have hCompress (x : ℝ) (hx : x ∈ carrier) : compress (A x - B x) = D x := by
    calc
      compress (A x - B x) = upperBlock (A' x - B' x) :=
        congrArg (fun M : Matrix k k ℂ => upperBlock M) (hRotateDiff x hx)
      _ = upperBlock (A' x) - upperBlock (B' x) := map_sub upperBlock _ _
      _ = D x := rfl
  have hDifference (x : ℝ) (hx : x ∈ carrier) :
      A' x - B' x = fromBlocks (D x) (0 : Matrix (Fin w) (Fin c) ℂ) 0 0 := by
    calc
      A' x - B' x = rotate U (A x - B x) := (hRotateDiff x hx).symm
      _ = fromBlocks (compress (A x - B x)) 0 0 0 := hSupported ⟨x, hx⟩
      _ = fromBlocks (D x) 0 0 0 := by rw [hCompress x hx]
  have hUpperRight (x : carrier) : (B' x).toBlocks₁₂ = E x := by
    apply Matrix.ext
    intro i j
    symm
    apply sub_eq_zero.mp
    exact congrArg (fun M : Matrix k k ℂ => M (Sum.inl i) (Sum.inr j))
      (hDifference x x.property)
  have hLower (x : carrier) : (B' x).toBlocks₂₂ = C x := by
    apply Matrix.ext
    intro i j
    symm
    apply sub_eq_zero.mp
    exact congrArg (fun M : Matrix k k ℂ => M (Sum.inr i) (Sum.inr j))
      (hDifference x x.property)
  have hAForm (x : carrier) : fromBlocks (A₀ x) (E x) (E x)ᴴ (C x) = A' x :=
    fromBlocks_of_isHermitian (hPSD A hA x).isHermitian
  have hBForm (x : carrier) : fromBlocks (B₀ x) (E x) (E x)ᴴ (C x) = B' x := by
    rw [← hUpperRight x, ← hLower x]
    exact fromBlocks_of_isHermitian (hPSD B hB x).isHermitian
  have hABlock (x : carrier) : (fromBlocks (A₀ x) (E x) (E x)ᴴ (C x)).PosSemidef := by
    rw [hAForm]
    exact hPSD A hA x
  have hBBlock (x : carrier) : (fromBlocks (B₀ x) (E x) (E x)ᴴ (C x)).PosSemidef := by
    rw [hBForm]
    exact hPSD B hB x
  have hTotalBlock : (∑ x : carrier, fromBlocks (A₀ x) (E x) (E x)ᴴ (C x)).PosDef := by
    have he : (∑ x : carrier, A' x) = rotate U (∑ x ∈ carrier, A x) := by
      rw [map_sum, Finset.sum_subtype carrier (fun _ => Iff.rfl)]
      exact Finset.sum_congr rfl fun x _ => by simp only [A', extend, ite_eq_left x.property]
    simp only [hAForm, he]
    exact htotal.conjTranspose_mul_mul_same hUInjective
  have hRotatedBudget (M : ℝ → Matrix d d ℂ)
      (hM : (∑ x ∈ carrier, (M x).rank) ≤ Fintype.card d + r) :
      (∑ x : carrier, (rotate U (extend M x)).rank) ≤
        Fintype.card (Fin w) + Fintype.card (Fin c) + r := by
    rw [Finset.sum_subtype carrier (fun _ => Iff.rfl)] at hM
    have hstep : (∑ x : carrier, (rotate U (extend M x)).rank) ≤
        ∑ x : carrier, (M x).rank := by
      apply Finset.sum_le_sum
      intro x _
      change (Uᴴ * (if (x : ℝ) ∈ carrier then M x else 0) * U).rank ≤ (M x).rank
      rw [ite_eq_left x.property]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    simpa only [Fintype.card_fin, hCard] using hstep.trans hM
  have hSignedBudget :
      (∑ x ∈ carrier, (hermPosPart (hD x)).rank) ≤ Fintype.card (Fin w) + r ∧
      (∑ x ∈ carrier, (hermNegPart (hD x)).rank) ≤ Fintype.card (Fin w) + r := by
    have h := SignedResidueRankBudget.sum_signed_parts_rank_budget hABlock hBBlock hTotalBlock
      (by simpa only [hAForm] using hRotatedBudget A hbudgetA)
      (by simpa only [hBForm] using hRotatedBudget B hbudgetB)
    constructor
    · rw [Finset.sum_subtype carrier (fun _ => Iff.rfl)]
      exact h.1
    · rw [Finset.sum_subtype carrier (fun _ => Iff.rfl)]
      exact h.2

  have hCompressedMoment (t : ℝ) (ht : t ∈ times) :
      ∑ x ∈ carrier, Real.exp (-t * x) • D x = 0 := by
    have hs : ∑ x ∈ carrier, Real.exp (-t * x) • (A x - B x) = 0 := by
      simpa only [smul_sub, Finset.sum_sub_distrib, sub_eq_zero] using hmoment t ht
    calc
      _ = ∑ x ∈ carrier, Real.exp (-t * x) • compress (A x - B x) :=
        Finset.sum_congr rfl fun x hx => by rw [hCompress x hx]
      _ = compress (∑ x ∈ carrier, Real.exp (-t * x) • (A x - B x)) := by
        simp only [map_sum, map_smul]
      _ = 0 := by rw [hs, map_zero]
  have hCompressedKernel (v : Fin w → ℂ) :
      (∀ x ∈ carrier, D x *ᵥ v = 0) → v = 0 := by
    intro hv
    apply hTrivial v
    intro x
    change compress (A x - B x) *ᵥ v = 0
    rw [hCompress x x.property]
    exact hv x x.property
  have hZero := SignedMomentRankUniqueness.signed_residue_eq_zero_of_trivial_common_kernel
    carrier times r htimes D hD hSignedBudget.1 hSignedBudget.2
    hCompressedMoment hCompressedKernel
  intro x hx
  apply hRotateInjective
  apply sub_eq_zero.mp
  change rotate U (A x) - rotate U (B x) = 0
  rw [show rotate U (A x) - rotate U (B x) = A' x - B' x by
    simp only [A', B', extend, ite_eq_left hx], hDifference x hx, hZero x hx]
  exact Matrix.fromBlocks_zero

/-- The common positive definite total supplies the moment at time zero.
Thus `2 * r + 1` distinct positive sample times suffice. -/
theorem eq_on_carrier_of_positive_time_samples
    (carrier times : Finset ℝ) (r : ℕ)
    (hpositive : ∀ t ∈ times, 0 < t) (htimes : 2 * r + 1 ≤ times.card)
    (A B : ℝ → Matrix d d ℂ)
    (hA : ∀ x ∈ carrier, (A x).PosSemidef)
    (hB : ∀ x ∈ carrier, (B x).PosSemidef)
    (htotal : (∑ x ∈ carrier, A x).PosDef)
    (hMass : (∑ x ∈ carrier, A x) = ∑ x ∈ carrier, B x)
    (hbudgetA : (∑ x ∈ carrier, (A x).rank) ≤ Fintype.card d + r)
    (hbudgetB : (∑ x ∈ carrier, (B x).rank) ≤ Fintype.card d + r)
    (hsample : ∀ t ∈ times,
      (∑ x ∈ carrier, Real.exp (-t * x) • A x) =
        ∑ x ∈ carrier, Real.exp (-t * x) • B x) :
    ∀ x ∈ carrier, A x = B x := by
  have hNotMem : (0 : ℝ) ∉ times := fun h => (lt_irrefl 0) (hpositive 0 h)
  have hCount : 2 * r + 2 ≤ (insert (0 : ℝ) times).card := by
    rw [Finset.card_insert_of_notMem hNotMem]
    omega
  apply eq_on_carrier_of_exponential_moments carrier (insert 0 times) r hCount A B
    hA hB htotal hbudgetA hbudgetB
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · simpa only [neg_zero, zero_mul, Real.exp_zero, one_smul] using hMass
  · exact hsample t ht

end MatrixResidueArbitraryTimeUniqueness
