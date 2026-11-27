/- GID: D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/HodgeTateVectors
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/HodgeTateVectors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicComparison.HodgeTate.HodgeTateVectors. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicComparison/HodgeTate/HodgeTateVectors.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicComparison.CrystallineFrobenius.CrystallineCohomology
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: The Hodge–Tate map from Hodge cohomology to p-adic étale cohomology. Only the
natural multiplicative map into the part of weight h is built here, from the torsor of lifts modulo
the square of the kernel of Fontaine's map. Bijectivity is not proved. Source: Scholze, p-adic Hodge
theory for rigid-analytic varieties, Forum Math. Pi 1 (2013), Cor. 1.8; construction as in Bhatt,
The Hodge–Tate decomposition via perfectoid spaces, Arizona Winter School 2017, §3.4.

This file: Hodge classes map naturally to vectors of Hodge–Tate weight h in étale cohomology. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor

open AlgebraicGeometry CategoryTheory PairRestrictBijective H freeAb ModuleCat.Algebra

/-- Let Y (smooth, charted over Ω) and W be proper over R, A a place of Ω above p containing R,
k ≅ Q̄_p compatibly over E. For x ∈ Hdg^q(Y_E), some v ∈ ℂ_p ⊗ V^{q+h}(Y) of Hodge–Tate
weight h for the decomposition group of A over E and semilinear Θ satisfy λ_h(u^*x) =
Θ(u^*v) for all u: W → Y.

Known result: Hodge–Tate map from Hodge cohomology to p-adic étale cohomology. -/
lemma exists_hasHodgeTateWeight {p h : ℕ} {R :
  CommRingCat} {E k : Type} [Field k] [Field E] [EmbeddedInQpBar p k] [Algebra R Ω] [Algebra R E]
  [Algebra E k] [Algebra E Ω] [IsScalarTower R E Ω] {Y} [IsCharted Y Ω] [IsProper Y.hom] {A} [I :
  PadicPlaceEmbedding E A p] (hR : ∀ r, algebraMap R Ω r ∈ A) (he : ∀ x, algebraMap k
  _ (algebraMap E k x) = I.e (algebraMap E Ω x)) d [SmoothOfRelativeDimension d Y.hom] ε (hk :
  ∀ z, algebraMap k (PadicAlgCl p) (ε z) = z) {W} [IsProper W.hom] {q} (x : HodgeH _ q) : ∃ v, ∃ Θ :
  _ →ₛₗ[ε] _, HasHodgeTateWeight (ellAdicCohom.galoisAction R Ω (decompGroup Gal(Ω/E) A) Y (q + h))
  h v ∧ ∀ u : W ⟶ Y, hodgeTateMap h (x.map (freeAb.map ((algPoints E R).map u))).baseChange =
  Θ ((((ellAdicCohom ..).map u.op).hom.restrictScalars _).baseChange _ v) := by
  obtain ⟨⟨e, ⟨⟨⟩, hj⟩, _⟩, θ, hθ⟩ := I, exists_periodAlg_iso_genericAlg
  algebraize [theta.comp (algebraMap ℤ_[p] _), (algebraMap E k).comp (algebraMap R E),
    (.codRestrict (.comp (algebraMap ..) (e.comp _)) _ (by simpa) : R →+* OC)]
  have := IsScalarTower.of_algebraMap_eq (S := OC) ((OC.toPadicIntAlgHom _).2 · |>.symm)
  choose J h₁ h₂ h₃ using exists_period_map (R := R) (by tauto) _ θ _ hj isPeriodRingPair_OC
  let B {n} W [IsProper W.hom] : H (genericOver ⋙ restrictAlg E k ⋙ freeAb (algPointsOf E R W))
    genericCoeff n ≃ₗ[k] _ := .ofBijective (mapₗ ..) (IsCohomEquiv.of_bijective (p :=
    toGenericPoints k (congrArg (algebraMap ..) <|
    IsScalarTower.algebraMap_apply R E Ω · ▸ he _) W) (·.bijective_generic_points) n)
  have S W z y : J W (z • y) = ε z • J W y := by
    erw [← (J W).map_smul, RingHom.comp_apply, hk, IsScalarTower.algebraMap_smul]
  refine (exists_hodgeTateMap_eq ?D h x.baseChange).elim fun ξ hξ ↦ ((h₃ Y).2 (B Y ξ)).elim fun v
    hv ↦ ⟨v, restrictToPairs ∘ₛₗ (B W).symm.comp ⟨_, S W⟩, fun g ↦ (h₃ Y).1 ((h₂ Y g _ _ (by
    intros; erw [hθ, hθ, PadicTest.structMap_twist]; rfl) _).trans (hv ▸
    (Comparison.map_pull_eq_pull_map (by exact hom_ext fun A _ ↦ congr(.of ⟨$(Over.OverMorphism.ext
    ((Spec.map_comp_assoc (CommRingCat.ofHom (algebraMap A.ProdRing A.GenericRing)) (𝟙 _)
    _).symm.trans (Spec.map_comp_assoc (𝟙 _) (CommRingCat.ofHom
    (algebraMap A.ProdRing A.GenericRing)) _)))⟩)) ..).symm.trans ((congrArg (B Y)
    (injective_restrictToPairs ?D (hodgeTateMap_galois_twist (by simp [*]) hξ (hk _)))).trans (by
    simp [algebra_compatible_smul (PadicAlgCl p), *])))), fun u ↦ by
    simp [hodgeTateMap_map, *, ← restrictToPairs_map]; rw [(B W).symm_apply_eq.2]
    erw [← map_comp, ← map_comp]; congr 2; exact hom_ext⟩
  apply (hasAtlas_algPoints d).isChartCovered.pairRestrictBijective
