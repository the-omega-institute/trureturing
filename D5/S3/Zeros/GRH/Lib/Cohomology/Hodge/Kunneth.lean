/- GID: D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/Kunneth
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Cohomology/Hodge/Kunneth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Cohomology.Hodge.Kunneth. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cohomology/Hodge/Kunneth.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cohomology.Duality.Contraction
import D5.S3.Zeros.GRH.Lib.Cohomology.Hodge.DepthVanishing
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols) (known result; see Lib.Cohomology.Hodge.FixedPointFormula).

This file: Künneth formula in Hodge cohomology, surjectivity of the cross product. -/

open Algebra.TensorProduct AddSubmonoid CategoryTheory Comparison CommAlgCat IsCohomEquiv Finset
  Finsupp TotalH TensorProduct CartesianMonoidalCategory MonoidalCategory Module.Basis Abelian.Ext

seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
/-- Künneth: over a field k of characteristic 0, if X has an atlas of dimension d, every class
in Hdg^n(X × X) is a finite sum of cross products x × y of Hodge classes on X. -/
lemma kunneth {k} [Field k] [CharZero k] {X d n} [hX : HasAtlas d X] (z : HodgeH _ n) :
    z ∈ AddSubmonoid.closure {z | ∃ a b e,
  ∃ (x : HodgeH (freeAb.obj X) a) (y : HodgeH (freeAb.obj X) b), z = .map (freeAb.prod X X)
  (_root_.cup (@exteriorAlg k _).mulPairing x y e :)} := hX.exists_isCharting.elim fun V ⟨h, t⟩ ↦ by
  have hU := hasZariskiDescent_hodgeCoeff (h.whisker _)
  have u {P} (hP : IsClosedClass P) (h : ∀ c, P (freeAb _)) : P (freeAb (V.whisker _).toFunctor) :=
    t _ (hP.comap (restrictAlong _)) fun b _ ↦
    hP.of_bijective _ b.exists_univPoint.choose_spec.2 (h _)
  refine (mem_map_iff_mem (((hU.preimage (fst ..)).inf (hU.preimage (snd ..))).isCohomEquiv n).1).1
    ((DirectSum.of_eq_same ..).subst ((((of_isIso (freeAb.map (NatIso.ofComponents fun _ ↦
    (Equiv.Set.prod ..).toIso).1 ≫ freeAb.prod (V.whisker _).toFunctor _)).bijective_totalH.comp
    (u (isClosedClass_lerayHirsch (Φ := abTensor _) (θ := fun i : Σ n,
    ofVectorSpaceIndex k (H _ _ n) ↦ H.push _ exteriorAlg.mulPairing _ (i.2.1.mapExactFunctor
    (abTensor.flip _)))) fun c ↦ ?_)).2.forall (p := (· n ∈ _))).2 (·.induction_linear (by simp)
    (by simp_all [add_mem]) fun ⟨a, x, _⟩ y ↦ ((hU.isCohomEquiv _).2 x).elim fun _ e ↦ ?_) _))
  -- U × c: the basis of H(U) is exchanged for a basis b of the forms on c
  let b := (ofVectorSpace k _).smulTower c.formBasis
  refine (bijective_iff_of_comm_sq (·.induction_linear (by simp [↓map_zero])
    (by simp_all [↓map_add]) fun _ r ↦ ?_) (curryAddEquiv.trans
    (mapRange.addEquiv (b.repr.symm.toAddEquiv.trans (.trans (.symm .ulift) (sectionEquiv
    hodgeCoeff _))))).bijective (u (isClosedClass_lerayHirsch (Φ := abTensor.flip _) (θ := fun j ↦
    mk₀ ((abTensor _).map ((homReprEquiv c hodgeCoeff).symm ⟨b j⟩) ≫ exteriorAlg.mulPairing)))
    fun c' ↦ ?_)).1 (Finsupp.domLCongr (.prodComm ..) ≪≫ₗ curryLinearEquiv k ≪≫ₗ
    mapRange.linearEquiv (DFinsupp.basis fun _ ↦ ofVectorSpace ..).repr.symm).bijective
  simp [DFinsupp.basis]
  conv_rhs => rw [lerayHirsch_single, TotalH.smul_eq_comp, map_comp_assoc, map_homClass,
    ← homClass_comp]
  conv_lhs => erw [lerayHirsch_single, map_homClass, (mk₀_bijective ..).1 ((push_homReprEquiv_symm
    (CoeffAction.act r).asHom ..).symm.trans (mk₀_comp_mk₀ ..)), toTotalH, ← of_comp_homClass,
    ← map_of, ← TotalH.comp_assoc_of_sq (naturality (abTensor.flip.map _) _), ← homClass_comp]
  congr 2
  exact abTensor_hom_ext fun _ _ _ ↦
    congrArg _ ((mul_smul_comm r ..).trans (smul_mul_assoc ..).symm)
  -- c' × c: the product is affine, and its forms are the tensor product
  let z : (reprBy c' ⊗ reprBy c) ⟨c'.baseAlg ⊗ c.baseAlg, _ ⊕ₗ _⟩ :=
    (⟨ofHom includeLeft, semilinearOfBasis _
    ((Pi.single · 1) ∘ .inl)⟩, ⟨ofHom includeRight, semilinearOfBasis _ ((Pi.single · 1) ∘ .inr)⟩)
  let s {c I} g (ε : I → ℤˣ) := ((HodgeTest.formBasis.reindex g).groupSMul
    ε).repr.symm.toAddEquiv.trans (.trans (.symm .ulift) (sectionEquiv (@hodgeCoeff k _) c))
  refine' ((of_isIso (freeAb.map (isoOfAppBijective (pointMap z) fun B ↦ .of_existsUnique _
    fun ⟨⟨f⟩, ⟨g⟩⟩ ↦ (existsUnique_tensor_desc f.1 g.1).elim fun _ ⟨a, b⟩ _ ↦ by
    refine' ⟨⟨_, semilinearOfBasis _ (Sum.rec _ _)⟩, congr((⟨$(HodgeTest.hom_ext a _)⟩,
      ⟨$(HodgeTest.hom_ext b _)⟩)), _⟩ <;> try exact fun _ ↦
      (congrArg _ (semilinearOfBasis_single ..)).trans (semilinearOfBasis_single ..)
    rintro _ ⟨⟩; exact congr(⟨$(HodgeTest.hom_ext (by tauto)
      (by rintro ⟨⟩ <;> exact .symm ((semilinearOfBasis_single ..).trans (congrArg _
      (semilinearOfBasis_single ..)))))⟩)).1 ≫ freeAb.prod ..)).bijective_totalH.of_comp_iff' _).1
    ((bijective_iff_of_comm_sq (curryAddEquiv.surjective.forall.2 (·.induction_linear
    (by simp [↓map_zero]) (by simp_all [↓map_add, -mapRange.addEquiv_apply]) fun ⟨⟨_, _⟩, _⟩ _ ↦ _))
    (mapRange.addEquiv (s 1 1)).bijective (s sumEquiv.1 (Function.uncurry _)).bijective).1
    ((equivFinsuppOfBasisRight b).symm ≪≫ₗ (c.formBasis.repr.restrictScalars _).lTensor _ ≪≫ₗ
    finsuppTensorFinsupp ..).bijective)
  swap; simp [s, b, lerayHirsch_single, groupSMul]
  conv_lhs => erw [map_homClass, homClass_comp_homClass_comp, ← homClass_comp]
  refine congrArg _ ((Equiv.eq_symm_apply _).2 (congr(exteriorAlg.mulPairing _ ($(add_zero _) ⊗ₜ
    $(add_zero _))).trans (congrArg _ (?_ : exteriorMap z.1.1.2 _ * exteriorMap z.2.1.2 _ = _))))
  erw [exteriorMap_smul, exteriorMap_smul, smul_mul_smul, exteriorMap_formBasis _ (.sumLexInl ..)
    (semilinearOfBasis_single _ _), exteriorMap_formBasis _ (.sumLexInr ..)
    (semilinearOfBasis_single _ _), ExteriorAlgebra.basis_mul_of_disjoint (I := Lex _)
    _ ⟨_, rfl⟩ ⟨_, rfl⟩ (disjoint_map_inl_map_inr ..)]; simp [z]; rfl
  -- U × U: every class is a sum of products of classes that extend to X
  apply y.induction_on .. <;> simp_all [add_mem, lerayHirsch_single, comp_of, DirectSum.of_apply,
    dite_mem, (hU.isCohomEquiv _).2.forall]
  exact fun | _, _, rfl => e ▸ ⟨_, subset_closure ⟨a, by tauto⟩, (H.map_comp ..).symm.trans
    ((cup_map (h := freeAb.hom_ext) ..).trans (congrArg _ (comp_assoc_of_third_deg_zero ..)))⟩
