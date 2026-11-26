import OmegaMath.NumberTheory.GRH.Lib.PadicComparison.HodgeTate.GaloisTwist
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Hodge–Tate map from Hodge cohomology to p-adic étale cohomology (known result; see
Lib.PadicComparison.HodgeTate.HodgeTateVectors).

This file: Galois acts on Hodge–Tate images of degree h through a cyclotomic power. -/


open CategoryTheory Functor TotalH HodgeTatePair
variable {p k E} [Field k] [EmbeddedInQpBar p k] {g : Gp p} [Field E] [Algebra E k]
  (hg : ∀ z : E, g (algebraMap k _ (algebraMap E k z)) = algebraMap k _ (algebraMap E k z))

/-- Let g ∈ G_p fix E, let t ∈ k equal χ(g⁻¹), and let x be a Hodge class over E with λ_h(x_k) =
`restrictToPairs` ξ. Then t^h ξ and the pull-back of ξ along the g-twist of tests have the
same image under `restrictToPairs`. -/
theorem hodgeTateMap_galois_twist {N : AbFunctor (CommAlg E)} {q h n} {x : HodgeH N q} {t ξ} (hξ :
  hodgeTateMap h x.baseChange = restrictToPairs ξ)
  (ht : algebraMap k (PadicAlgCl p) t = algebraMap _ _ (cyclotomicGp g⁻¹).1) :
  let τ : genericOver ⋙ restrictAlg E k ⟶ PadicTest.twist g ⋙ genericOver ⋙ restrictAlg E k :=
    .mk fun c ↦ CommAlg.homOfRingHom (.id c.GenericRing)
    fun z ↦ by symm; erw [c.structMap_twist, smul_coe_Cp, hg]; rfl
  restrictToPairs ((Comparison.of _ (twistGenericCoeff g)).pull (whiskerRight τ N) n ξ : type_of%
    ξ) = restrictToPairs (t ^ h • ξ) := by
  intro τ
  let φ := (@HodgeTest.baseComparison k _ E _ _).φ
  let σ : _ ⟶ HodgeTatePair.galTwist g ⋙ toHodgeTest ⋙ φ :=
    toHodgeTest.whiskerLeft (HodgeTest.scaleModule t φ) ≫ .mk (⟨τ ·.test, .id⟩)
  let S := whiskerRight σ HodgeTest.sqZeroExt
  obtain ⟨T, hT⟩ : ∃ T : pairAlg ⋙ restrictAlg E k ⟶ HodgeTatePair.galTwist g ⋙ pairAlg ⋙
    restrictAlg .., ∀ X x, (T X x).1.2 = S X x.1.2 := ⟨⟨fun X ↦ CommAlg.homOfRingHom
    ((RingHom.prodMap (.id _) (S X).1.1).restrict _ _ (by tauto)) fun z ↦ Subtype.ext
    (Prod.ext ((congrArg _ (hg z).symm).trans congr($((PadicTest.twist g X.test).uniqueLift.2
    ⟨X.test.uniqueLift.1.1.1.comp (.restrictScalars _ g.toAlgHom), fun _ ↦ (X.test.uniqueLift.1.1.2
    _).trans (smul_coe_Cp g _ ▸ X.test.structMap_twist ..).symm⟩).1 _)) ((S X).1.2 z)), fun X Y
    f ↦ by ext; exact Subtype.ext (Prod.ext (congrArg (_ + ·) ((thickeningOver.mulMu_twist g Y.test
    _).trans (congrArg _ (show _ = (f.2 (t • _)).1 by
    erw [← ht, ← algebraMap_smul X.GenericRing, map_smulₛₗ, RingHom.coe_coe, AlgHom.commutes]
    rfl)))) congr($(S.2 f) _))⟩, by tauto⟩
  rw [restrictToPairs.map_smul]; erw [← hξ, ← comp_smul, ← scaleModule_comp_contractionPow,
    ← contractionPow_galTwist g, homClass_comp_homClass_comp]
  refine .trans ?_ ((congrArg _ ((TotalH.map_comp_assoc (restrictAlong _) _).symm.trans
    congr(comp (.map _ $hξ) _))).symm.trans
    (comp_assoc_of_sq (pull_twist (Comparison.pull_trans _) σ (whiskerRight T N) (by ext; rfl) (by
    ext : 2; simpa using! (N.map_commSq ⟨by ext; apply hT⟩).w)) _))
  erw [map_of, of_comp_homClass, homClass_comp_of]; simp [restrictToPairs, Comparison.pull, H.map,
    H.push, mapExactFunctor_mapExactFunctor]; congr 3 with : 2
  exact (N.map_commSq ⟨by ext; apply congr($(hT ..).1)⟩).w.symm
