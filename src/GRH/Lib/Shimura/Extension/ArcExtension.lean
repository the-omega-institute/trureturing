import GRH.Lib.Shimura.ThetaGroup.ComplexComparison
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Homomorphisms and line bundles of abelian schemes extend from the generic fibre.
The form here holds over any valuation ring of the complex numbers (not noetherian, any rank), but
only for maps of complex tori that multiply a theta polarisation, whose kernel is killed by a unit
of the ring, by an integer. The map and the identity of bundle classes extend together, and points
extend by properness. Source: S. Bosch, W. Lütkebohmert, M. Raynaud, Néron Models (1990), 1.2/8 and
4.4/1; G. Faltings, C.-L. Chai, Degeneration of Abelian Varieties (1990), I.2.7; L. Moret-Bailly,
Pinceaux de variétés abéliennes, Astérisque 129 (1985), II.3.5.

This file: Polarisation-multiplying isogenies of complex tori extend to abelian schemes over
valuation rings. -/


open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory Over Category LineBundle PointFn
variable {V ι κ O} [FinComplexSpace V] [CommRing O] [ValuativeArc O] {A A' :
  Over (Spec ⟨O⟩)} [AddObj A'] {s' : V →+ (_ ⟶ A')} [Finite κ] [IsAbelianScheme A] [Finite ι] (u :
  Uniformisation A V) {N : LineBundle _ ι} {B χ θ} (h : HasThetaCoords u.L (atGeneric
  u.expMap) N B χ θ) [IsPosRiemann B] (k₀ : ∀ l ∈ u.L, s' l = 0) {n : ℕ} (hn : IsUnit (n : O)) (H :
  ∀ a ∈ B.dualLattice, n • a ∈ u.L ∧ ∃ Φ, IsTranslationLift N (u.expMap a) Φ) [IsProper A'.hom] {M :
  LineBundle _ κ} (hM : M.IsProjEmbedding A'.hom)
include h k₀ hn H hM
attribute [local simp ←] comp_left Pic.pull_picClass Pic.pull_comp

attribute [local simp] IsSection IsLinearSystem IsRegularOn landsIn_iInf pow in
/-- Let the homomorphism π: A' → A carry s' (zero on L) to u; N and the embedding M have one
positive theta type; ν*π*N ⊗ M^{n²} ≅ ν*M ⊗ π*N^{n²} (ν = n, a unit); nL^∨ ⊂ L; translations
by u(L^∨) fix N. Then π has a section e with e∘u = s', e*M ≅ N. -/
lemma exists_section_of_hasThetaCoords π [IsAdditive π] {f ν m} (m0 : n ^ 2 = m) (F : ∀ z, s' z ≫
  π = u.expMap z) (t : HasThetaCoords _ (atGeneric s') M B χ f) (g : (n • 𝟙 A').left = ν) (hw :
  (((N.pull π.left).pull ν).mul (M.pow m)).picClass =
  ((M.pull ν).mul ((N.pull π.left).pow m)).picClass) :
  ∃ e, (∀ z, u.expMap z ≫ e = s' z) ∧ (M.pull e.left).picClass = N.picClass ∧ e ≫ π = 𝟙 A := by
  have ⟨hν, F'⟩ : (∀ z, atGeneric s' ((n : V →L[ℂ] V) z) = atGeneric s' z ≫ ν) ∧ ∀ z,
    atGeneric u.expMap z = atGeneric s' z ≫ π.1 := by simp [atGeneric, F, ← g]
  obtain ⟨⟨w, hw⟩, ⟨Γ, p, P, _, hP, D⟩, d, v, m0 : m ≠ 0⟩ := picClass_eq_iff.1 hw,
    exists_reduced_closure
    (atGeneric s'), isSeparatingFamily_atGeneric u.4, h.pull 1 F' fun _ ↦ id, by aesop
  obtain ⟨⟨γ, γ0, r, e, Z⟩, _, -, -, κ, G⟩ := exists_sections_of_translation_stable (N := ⊤) u h hn
    (by simp_all) (by simp) t.3 _ (ne_of_apply_ne (· 0) (t.4 0).ne_zero.choose_spec),
    d.2.surjective (p ≫ π.1) P (by grind), ((v.pull _ hν).mul (t.pow _)).riemannForm_eq_of_isFrame
    ((t.pull _ hν).mul (v.pow _)) hw (t.holomorphicAt hM)
  have ⟨W, c, I⟩ := exists_picClass_eq_pull_hyperplane (p ≫ π.1) (r · |>.1.2.1) fun i K _ ζ o ↦
    by_contra fun z ↦ Z K (ζ ≫ p ≫ π.1) fun z₀ hz j a ↦ by_cases ((r j).1.2.2 a _ _) fun ha ↦ by
    have ⟨T, E, c, C⟩ : ∃ T, T ≫ ν = ν ∧ (∀ x, atGeneric s' x ≫ T = atGeneric s' (x + z₀)) ∧
      π.1 ≫ (translation (u.expMap z₀)).1 = T ≫ π.1 :=
      ⟨(translation (s' z₀)).1, by simp [atGeneric, ← g, ← comp_nsmul _, ← map_nsmul, *, -g]⟩
    let Q := M.mul (N.pull π.1)
    obtain ⟨⟨⟨b, b₁, b', i'⟩, _⟩, u, ⟨_, Y, J, X'⟩, _⟩ := (M.mul ((M.pull T).mul (Q.pull ν))
      ).exists_landsIn (ζ ≫ p), (hw.2 · ⟨K⟩), t, (r · |>.1.2.1)
    let φ b i j := w ((i', fun _ ↦ b), b', fun _ ↦ i) * ((r j).1.1 i ^ m).pull π.1
    simp [IsHomogCoords, C, Q, IsFrame] at *
    refine .mp ?_ (@D.pointFn_ext _ _ _ (p ⁻¹ᵁ (Q.opens (b, i) ⊓ T ⁻¹ᵁ Q.opens (b₁,
      a) ⊓ ν ⁻¹ᵁ Q.opens (b', i'))) ((φ b i b * (M.transition b₁ j ^ m).pull T).pull p)
      ((φ b₁ a j).pull (p ≫ T)) ?_ ?_ (by simp +contextual [
      Q, φ, G, e, ← assoc, hP, c, ← hν, h.4 .., X', ← F', (h.3 _).2, (J _).2, H _ hz, Y.ne_zero,
      mul_pow, div_pow, field]) _ ζ ?_) <;> simp +contextual [Q, φ, *, reassoc_of% E]
  exact (d.exists_map_of_coords (ProjSpace.isLinearSystem_hyperplaneBundle.pull W) hM
    (h.4 · |>.ne_zero.elim fun i x ↦ by
    simpa [IsHomogCoords, *, -F', field] using! I i _ _ ((h.4 ..).1.2 x.isUnit)) t.4).imp
    fun e ⟨h, E⟩ ↦ ⟨(bijective_restrict_genericPt.1 <| h ·), E ▸ c.symm, d.hom_ext (by grind)⟩

attribute [-simp] lift_left
attribute [local simp ←] fst_left snd_left

/-- Let A = V/Λ over O and s': V → A'(O) additive killing Λ, with embeddings N, M obeying the
parallelogram law and theta coordinates of positive type (B, χ), resp. (μB, χ^μ). If Λ^∨ maps into
K(N) and nΛ^∨ ⊂ Λ, n a unit, then s' comes from a homomorphism ψ with ψ^*[M] = μ[N].

Known result: Homomorphisms and line bundles of abelian schemes extend from the generic fibre. -/
lemma exists_hom_of_hasThetaCoords (hN : N.IsProjEmbedding A.hom) (c : N.picClass.ParallelogramLaw)
  (c' : M.picClass.ParallelogramLaw) {μ θ'} (h' : HasThetaCoords _ (atGeneric s') M
  (μ • B) (χ ^ μ) θ') : ∃ ψ, IsAdditive ψ ∧ (∀ z, u.expMap z ≫ ψ = s' z) ∧ M.picClass.pull ψ.left =
  μ • N.picClass := by
  have ⟨k, hm⟩ : ∃ k, IsUnit (↑(μ + .succ k) : O) := by
    by_contra! H; simpa using (IsLocalRing.maximalIdeal O).sub_mem (H μ.succ) (H μ)
  have ⟨e, he, C, i⟩ := exists_section_of_hasThetaCoords (s' :=
    .mk' (fun z ↦ lift (u.expMap z) (s' z)) (by bound)) u (h.pow _)
    (by aesop) (mod_cast hm.mul hn) ?_ ((hM.of_isPullback (.flip (.of_hasPullback ..))).mul (hN.pow
    ?_)) (fst ..) rfl ?_ (add_smul μ _ B ▸ pow_add χ .. ▸ (h'.pull 1 ?_).mul ((h.pow k.succ).pull 1
    ?_)) rfl (by linear_combination (norm := (simp; module)) (μ • congr($(pull_nsmul_eq_sq_smul c _
    ).pull (fst _ A').1) - congr($(pull_nsmul_eq_sq_smul c' _).pull (snd A _).1)))
  use e ≫ snd .., isAdditive_of_universal ((@isSeparatingFamily_atGeneric _ _ _ _
    (by simp [-fst_left]; infer_instance) _ _ _
    (homEquivToProd.symm.surjective.comp (u.4.prodMap u.4))).hom_ext ?_), ?_, (by simp_all
    [add_smul]) <;> simp [reassoc_of% comp_add, ← comp_add _, ← map_add, reassoc_of% he]
  all_goals simp_all [atGeneric, exists_isTranslationLift_iff, mem_dualLattice_nsmul, mul_nsmul,
    c.nsmul_class_pairing, ← comp_nsmul, ← map_nsmul]
