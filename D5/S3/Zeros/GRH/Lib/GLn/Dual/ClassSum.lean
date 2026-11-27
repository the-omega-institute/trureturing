/- GID: D5/S3/Zeros/GRH/Lib/GLn/Dual/ClassSum
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GLn/Dual/ClassSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GLn.Dual.ClassSum. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GLn/Dual/ClassSum.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GLn.Dual.MixedCartan
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.BlockMatrices
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Dual of a Weyl module by Jacobi's complementary minors; Cartan component (known result;
see Lib.GLn.Branching.Branching).

Part of: Abstract Hecke operators of a pair (G,K), level eigenspaces, weighted class sums (known
result; see Lib.Adelic.Hecke.ClassMean).

This file: Tensors on complementary blocks lie in the Cartan component; integral, isometric,
equivariant product. Linearity, Fubini and integrality of class sums weighted by automorphism
groups. -/

open HasFiniteType Fintype PolyRep Kronecker Matrix Sum

variable {Φ n N m R L : Type} [CommRing R] [Fintype Φ] [Fintype n] [Fintype N] [Fintype m]
  {kp km : Φ → _} [NormedField L] [IsUltrametricDist L] (ε : N ⊕ m ≃ n)

omit [Fintype n] in
lemma map_intCast_mul_mulVec (A : Matrix n m ℤ) (B : Matrix m N ℤ) (v : N → R) :
    (A * B).map (↑) *ᵥ v = A.map (↑) *ᵥ B.map (↑) *ᵥ v := by simp [← Int.coe_castRingHom]

lemma leftInv_mulVec_mixedCartan {η} : (mixedCartan ..).2.choose.map (@Int.cast R _) *ᵥ (mixedCartan
  n kp km).1.map (↑) *ᵥ η = η := by simp [↓← map_intCast_mul_mulVec, (mixedCartan ..).2.choose_spec]

lemma norm_schur_mulVec_le (F : FitsRanks N n kp) {A : _ → Matrix n N L} (h : ∀ τ i j, ‖A τ i
  j‖ ≤ 1) v : ‖schur kp A *ᵥ v‖ ≤ ‖v‖ := one_mul ‖v‖ ▸ norm_mulVec_le (congr($(schur_map F
  (⟨_, h · · ·⟩) NormedField.valuation.integer.subtype) · · ∈ _).ge (Subtype.prop _)) v

/-- The condition that |N| ≤ |n| and that the column multiplicities kp(τ, h) vanish for all τ
and all heights h with |N| ≤ h < |n|. -/
abbrev HasColumnsBelow n N [Fintype n] [Fintype N] (kp : Φ → _) := FitsRanks N n kp ∧
  schurDetExp N n kp = 0

/-- The bilinear product of vectors of weights kp, km: tensor their Schur images under the
N-columns of g and the m-columns of g⁻ᵀ, then apply an integral left inverse of `mixedCartan`. -/
noncomputable def cartanProduct (g : Φ → GL n R) :=
  ((vecMulVecBilin ..).compl₁₂ (schur kp (g · |>.1.submatrix
  id (ε ∘ inl))).mulVecLin (schur km fun τ ↦ (g τ)⁻¹.1ᵀ.submatrix id (ε ∘ inr)).mulVecLin).compr₂
  (((mixedCartan ..).2.choose.map (↑)).mulVecLin ∘ₗ .pi fun p ↦ entryLinearMap _ _ p.1 p.2)

lemma HasColumnsBelow.schur_mul_schur (hN : HasColumnsBelow n N kp) (A : Φ → Matrix n N R) (B : Φ →
  Matrix N N R) :
  schur kp A * schur kp B = schur _ fun τ ↦ A τ * B τ := by simp_all [schur_mul_right]

variable (hN : HasColumnsBelow n N kp) (hm : HasColumnsBelow n m km) (ε :
  N ⊕ m ≃ n) {K : Type} [Field K] [CharZero K]

include hN hm

omit [CharZero K] in
lemma map_cartanProduct (y : WeylIndex N kp → ℂ) (η : WeylIndex m km → ℂ) (f : ℂ →+* K) :
  f ∘ cartanProduct ε 1 y η = cartanProduct ε 1 (f ∘ y) (f ∘ η) :=
  funext (by simp_all [cartanProduct, ← mul_inclMatrix, ← map_inclMatrix f, schur_map, entrywise])

lemma mixedCartan_mulVec_cartanProduct y η : (mixedCartan n kp km).1.map (↑) *ᵥ cartanProduct ε 1 y
  η = (vecMulVec (schur _ (fun _ ↦ inclMatrix K (ε ∘ inl)) *ᵥ y) (schur _ (fun _ ↦
  inclMatrix K (ε ∘ inr)) *ᵥ η))ᵀ.vec := by exact congr($((ext_schur_weylEval (rowPos N) fun u y _ ↦
  ext_schur_weylEval (rowPos m) fun w η _ ↦ by
  let δ := (((equivFin N).sumCongr ((equivFin m).trans Fin.revPerm)).trans finSumFinEquiv).trans
    ((finCongr (by simp [← card_congr ε])).trans (equivFin n).symm)
  simp [cartanProduct, -mulVec_mulVec]; erw [(_ : LinearMap.pi _ _ = _), leftInv_mulVec_mixedCartan]
  any_goals rw [(mixedCartan ..).5 fun τ ↦ (by simp : IsUnit (reindex ε δ (fromBlocks (u τ) 0 0
    (w τ)ᵀ⁻¹))).unit, MixedCartanEmbedding.top]
  ext; simp [*, ← card_congr ε, schur_mulVec_weylEval_of_detExp_zero,
    inv_fromBlocks_zero₂₁_of_isUnit_iff', weylEval, nablaBasis, tableauPoly,
    minor, RingHom.map_det, map]
  convert mul_comm .. <;> simp [← ε.symm_apply_eq, permArray, reindex_equiv δ, δ] <;> cases ε.symm
    _ <;> simp <;> grind [Finset.univ.sum_eq_zero, Fin] : .compr₂ _ (mulVecLin _) = ((vecMulVecBilin
  ..).compl₁₂ (mulVecLin _) (mulVecLin _)).compr₂ (.pi fun _ ↦ entryLinearMap ..))) y η)

lemma weylRep_cartanProduct y η (g : _ → GL n K) :
  weylRep (mixedWeight n kp km) (-∑ i ∈ .Ico 1 (card n), km · i) g *ᵥ cartanProduct ε 1 y η =
  cartanProduct ε g y η := leftInv_mulVec_mixedCartan.symm.trans (congrArg _ (funext (by
  simp_all [↓MixedCartanEmbedding.intertwines, mixedCartan_mulVec_cartanProduct, mul_inclMatrix,
    HasColumnsBelow, mul_comm])))

lemma weylNormSq_cartanProduct (y : WeylIndex N kp → ℂ) (η : WeylIndex m km → ℂ)
    : weylNormSq (cartanProduct ε 1 y η) =
  weylNormSq y * weylNormSq η := have h := mixedCartan_mulVec_cartanProduct hN hm ε y η
  by convert congr((star $h ⬝ᵥ weylGramOver ⊗ₖ weylGramOver *ᵥ $h).re)
     simp [weylNormSq, star_mulVec, dotProduct_mulVec, ← (mixedCartan ..).3, -mulVec_mulVec]
     congr 3 with; simp [mul_apply]
     simp_all [↓map_vecMulVec_star, star_mulVec, ← dotProduct_mulVec, ← coe_weylNormSq,
       schur_conjTranspose_weylGram_schur, mul_comm, inclMatrix, ← ext_iff, mul_apply]

attribute [local simp] Finset.smul_sum classSum smul_smul

variable {G G' W W'} [Group G] [Group G'] {Γ} {K : Subgroup G} {Γ' K'} [AddCommGroup W] [Module ℚ W]
  [AddCommGroup W'] [Module ℚ W'] [TopologicalSpace G] [TopologicalSpace G'] [@HasFiniteType G _ Γ K
  _] [@HasFiniteType G' _ Γ' K' _] {A} [Ring A] [Algebra ℚ A] (a : A) (f : G → A)

omit hN hm

lemma map_classSum {F} [FunLike F W _] [AddMonoidHomClass F W W'] (L : F) f :
    L (classSum Γ K f) = classSum Γ K (L <| f ·) := by simp [map_rat_smul]

lemma classSum_sum {ι} s (f : ι → _ → W) :
    classSum Γ K (∑ i ∈ s, f i ·) = ∑ i ∈ s, classSum Γ K (f i) := by simpa using Finset.sum_comm

lemma classSum_comm (f : G → _ → W) : classSum Γ K (classSum Γ' K' <| f ·) = classSum Γ' K' fun g' ↦
    classSum Γ K (f · g') := by simpa [mul_comm] using Finset.sum_comm

lemma mul_classSum : a * classSum Γ K f = classSum Γ K (a * f ·) := by simp [Finset.mul_sum]

@[simp] lemma classSum_mul : classSum Γ K f * a = classSum Γ K (f · * a) := by simp [Finset.sum_mul]

lemma smul_classSum_mem {S} [SetLike S W] [AddSubmonoidClass S W] (p : S) {M} (hM : ∀ g, Nat.card
    (classAut Γ K g) ∣ M) {f} (hf : ∀ g, f g ∈ p) : M • classSum Γ K f ∈ p := by simp_all [
  ← smul_assoc, ← division_def, ← Nat.cast_div_charZero, Nat.cast_smul_eq_nsmul, sum_mem, nsmul_mem]

lemma classSum_le_card_mul_sq {f M} (h : ∀ g, √(f g) ≤ M) : classSum Γ K f ≤ Nat.card (DoubleCosets
  Γ K) * M ^ 2 := by simp_all [Real.sqrt_le_iff]; grw [(h _).2, Nat.cast_inv_le_one]; simp
