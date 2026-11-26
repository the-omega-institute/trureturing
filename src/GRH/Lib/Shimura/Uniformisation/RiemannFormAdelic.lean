import GRH.Lib.General.Geometry.LocalTerms
import GRH.Lib.Shimura.AbelianScheme.ThetaFamily
import GRH.Lib.Shimura.IntegralModel.NeatLevel
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number
(known result; see Lib.Shimura.Uniformisation.AppellHumbert).

Part of: Integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation (known
result; see Lib.Shimura.IntegralModel.ModelExistence).

This file: Ball and fibre spaces; E⊗R acts complex-linearly through a period map. `Model`: an
integral tower of Kuga–Sato varieties with covers and Hecke legs. Riemann form on rational vectors
as a trace and via the adelic character. -/

open Matrix NumberField Module Fintype CategoryTheory AlgebraicGeometry Finset FourierTransform
variable (E n) [Field E] [CMBase E] [Fintype.{0} n]

/-- The complex vector space ℂ^(n−1), which contains the parameter domains of the families of
periods. -/
abbrev BallBase := Fin (Fintype.card n - 1) → ℂ

/-- The complex vector space C × C^(n−1) × the product of copies of C^n over the infinite places
of E other than v₀. -/
abbrev BallFibre := (ℂ × BallBase n) × ({v : InfinitePlace E // v ≠ v₀} → n → ℂ)

variable {E n V V'} [FinComplexSpace V] [FinComplexSpace V'] {ℓ} {Q : RealVectors E n ≃L[ℝ] V} (h :
  IsPeriodMap ℓ Q)

lemma smul_re_im (a : ℂ) (z : V) : a • z = a.re • z + a.im • Complex.I • z := by match_scalars; simp

include h

omit h in
lemma IsPeriodMap.finrank_eq_abelianDim (_ : IsPeriodMap ℓ Q) : finrank ℂ V = abelianDim E n := by
  simpa [abelianDim, ↓finrank_real_of_complex] using Q.symm.finrank_eq

lemma IsPeriodMap.ratConj_eq {J R} (p : IsPeriodMap J R) {z : GL n E} (F : V →ₗ[ℂ] V') (k : ∀ w,
  F (Q w) = R (realVecAction z w)) : ratConj z ℓ = J :=
  (z.map _).mul_inv_eq_iff_eq_mul.2 (ext_iff_mulVec.2 fun u
  ↦ by simpa [k, ← p _, funext_iff] using congr((R.symm (F $(h (u · • 1))) · v₀)))

/-- For a period map Q, the ring homomorphism sending c in E ⊗ ℝ to the complex-linear
endomorphism Q∘c∘Q⁻¹ of V. -/
@[simps! apply_apply] noncomputable def IsPeriodMap.complexMul : (InfinitePlace E → ℂ) →+* V →L[ℂ]
  V := by use! fun c ↦ {Q.arrowCongr Q (c • 1) with map_smul' a := by simp [↓reindex_equiv Q, ← h _,
  ← Q.symm.injective.eq_iff, smul_re_im a, funext_iff, entrywise,
  Finset.mul_sum, mul_left_comm]} <;> simp [mul_smul, DFunLike.ext_iff, add_smul]

omit h

/-- A tower of projective R-schemes with smooth base, Hecke maps and multiplications m α, with
uniformisation of complex points, Galois covers, tangent maps at fixed points and the
congruence relation at safe places. -/
structure Model {E} [Field E] [CMBase E] n [Fintype n]
  d₀ [HasQuadSubfield d₀ E] 𝔑 ν (R : Subalgebra (𝓞 E) E) where
  (Z) W : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n) → Over (Spec ⟨R⟩)
  s _i : Set (GL n (𝔸f E))
  leg i : GL n (𝔸f E) ⧸ levelGU n 𝔑 → (W i ⟶ Z)
  one_mem i : 1 ∈ s i
  eventually_translate {g} j : g ∈ GUPlus E n → ∀ᶠ i in .atTop, g ∈ s i ∧ ∃ f, ∀ q ∈ s j,
    f ≫ leg j q = leg i (g * q)
  Δ _i : FiniteGrp
  deck i : Δ i →* End (W i)
  deck_comp_leg i δ : ∃ κ : levelGU n 𝔑, ∀ q ∈ s i,
    (deck i δ).asHom ≫ leg i q = leg i (κ.1 * q)
  m _α : Z ⟶ Z
  point _i : ModuliPoint E n ν → (specOver R ℂ ⟶ _)
  point_surjective i : (point i).Surjective
  point_eq_iff i a b : point i a ≫ leg i ⟦1⟧ = point i b ≫ leg i ⟦1⟧ ↔ ∃ z,
    a.IsLevelIso (levelGU n 𝔑) z b
  point_leg {i} g α a : ↑g ∈ s i → point i a ≫ leg i g.1 ≫ m α = point i (a.act g α) ≫ leg i ⟦1⟧
  (d) smooth : SmoothOfRelativeDimension d Z.hom
  [proper : IsProper Z.hom]
  [projective (i) : HasProjEmbedding (W i).hom]
  [reduction (i) : IsReduced (W i).left]
  covering i : IsGaloisCovering (leg i ⟦1⟧) (deck i)
  tangent i g α a z μ : g.1 ∈ s i → z.1.charpoly.Separable → a.reflection = eigenReflection True z
    μ → (a.act g α).IsLevelIso (levelGU n 𝔑) z a → IsTangentPoly d ((algPoints ..).map (leg i ⟦1⟧))
    ((algPoints ..).map (leg i g.1 ≫ m α)) ⟨point i a⟩ (localTerm α z.1.charpoly μ)
  congruence w : IsSafe 𝔑 w.1 → ∀ i (𝔭 : Set R), (∀ c ∈ w.1.1, algebraMap _ _ c ∈ 𝔭) →
    (∀ A, heckeIsogeny w A ∈ s i) → let r (A : Submodule _ (n → _)) := finrank (ResField w.1) A
    ∀ ⦃p f⦄ [Fact p.Prime], w.1.q = p ^ f → CongruenceRelation (fun A ↦ (-1) ^ r A * w.1.q ^
      (r A).choose 2) 𝔭 p (fun A ↦ (Fintype.card n - r A) * f) (leg i <| heckeIsogeny w ·)

variable {E : _} [Field E] [CMBase E] (D : PEL E) {D' : PEL E} {β' : Matrix D'.Index D'.Index E}

/-- For a matrix β over E, the real bilinear form (y, z) ↦ Σ_v 2 Re(Φ_v(ξ)·z_vᴴ Φ_v(β) y_v) on
(E ⊗ ℝ)ⁿ, with ξ from the datum D. -/
noncomputable def polarisationForm β := by apply LinearMap.mk₂ ℝ fun y z : RealVectors E D.Index ↦
  ∑ v, 2 * (Φ v D.ξ * star (z · v) ⬝ᵥ .map β (Φ v) *ᵥ (y · v)).re <;> simp [entrywise, mul_sum,
  -sum_sub_distrib, ← sum_add_distrib] <;> grind

/-- A polarised period map for (g, ℓ): a period map Q, a hermitian β with gᴴβg a unit of Ẑ, and
B with symmetric real part whose positive Riemann form pulls back to `polarisationForm`. -/
structure PeriodMap (g : GL D.Index (𝔸f E)) ℓ V [FinComplexSpace V] where
  (β Q) B : @LatticeForm V _ (classLattice g ⊥ Q)
  isFrameFor : IsFrameFor β g
  isPeriodMap : IsPeriodMap ℓ Q
  re_symm u v : (B u v).re = (B v u).re
  riemannForm_eq y z : B.riemannForm (Q y) (Q z) = polarisationForm D β y z
  isPosRiemann : IsPosRiemann B

/-- For a unit ν of the integral finite adeles of ℚ and a finite adele a of E, one has ψ_f(νa) =
1 if and only if ψ_f(a) = 1. -/
lemma ψf_unit_eq_one (ν : (Ô ℚ)ˣ) {a} : ψf E (finAdeleIncl ℚ E ν * a) = 1 ↔ ψf E a = 1 :=
  have k {a} (h : _ = 1) := dense_Ô.eq (f := (ψf E <| finAdeleIncl ℚ E ·.1 * a)) (g := 1) (by
    simp [h, ← zsmul_eq_mul, reindex_equiv Rat.ringOfIntegersEquiv.symm, AddChar.map_zsmul_eq_zpow])
  ⟨(by simpa [← mul_assoc, ← map_mul, ← Subring.coe_mul] using k · ν.2), (k · ν)⟩

@[simp] lemma polarisationForm_toRealVectors y z :
  polarisationForm _ β' (toRealVectors y) (toRealVectors z) = Algebra.trace ℚ E
  (D'.ξ * star z ⬝ᵥ β' *ᵥ y) := by simp [polarisationForm, trace_eq_sum_Φ, entrywise]

/-- If gᴴβg = a·1 with a a finite adele, then exp(2πi ∑_v 2 Re Φ_v(ξ zᴴβy)) = ψ_f(a ξ
(g⁻¹z)ᴴ(g⁻¹y)) for all y, z in Eⁿ, with ξ from the datum D. -/
lemma fourierChar_polarisationForm {g a} (h : g.1ᴴ * β'.map (algebraMap ..) * g.1 = a • 1) y z :
    𝐞 (polarisationForm _ β' (toRealVectors y) (toRealVectors z)) =
  ψf E (a * xiForm D'.ξ (frameCoords g y) (frameCoords g z)) := by
  simp [← ψf_eq, frameCoords, xiForm, star_mulVec_dotProduct]
  simp [dotProduct, RingHom.map_mulVec, ← gram_inv_of_gram_eq h, mul_sum, mul_left_comm a]
  rfl
