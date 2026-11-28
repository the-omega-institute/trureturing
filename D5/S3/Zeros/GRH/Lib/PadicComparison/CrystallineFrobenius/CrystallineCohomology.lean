/- GID: D5/S3/Zeros/GRH/Lib/PadicComparison/CrystallineFrobenius/CrystallineCohomology
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicComparison/CrystallineFrobenius/CrystallineCohomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicComparison.CrystallineFrobenius.CrystallineCohomology. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicComparison/CrystallineFrobenius/CrystallineCohomology.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicComparison.Primitive.PrimitiveComparison
import D5.S3.Zeros.GRH.Lib.PadicComparison.HodgeTate.GaloisWeight
import D5.S3.Zeros.GRH.Lib.PadicComparison.CrystallineFrobenius.DenseRelation
import D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline.RegularityFrobenius
import D5.S3.Zeros.GRH.Lib.PadicComparison.Crystalline.CrystallineClasses
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: The congruence relation for the crystalline Frobenius. In the literature,
characteristic polynomials are compared through cycle classes. Here a relation among Frobenius
twists of maps, given on points of the special fibre, is carried directly to a relation among
operators on crystalline invariants. Source: Scholl, Motives for modular forms, 1990, Invent. Math.
100, §4.2.3, through Katz–Messing, Some consequences of the Riemann hypothesis for varieties over
finite fields, 1974, Invent. Math. 23, Thm 2(2); for a ramified base, Berthelot–Ogus, F-isocrystals
and de Rham cohomology I, 1983, Invent. Math. 72.

Known result: For smooth proper reduction, ℓ-adic cohomology is unramified and Frobenius relations
pass to it. Here, over the valuation ring of a place, a relation among Frobenius-twisted maps that
holds at every geometric point of the special fibre holds on ℓ-adic cohomology. In particular,
inertia acts trivially. Source: Stacks project, Tags 0GKD (SGA4 XVI 2.2) and 03SN (SGA5 XV);
Deligne, Formes modulaires et représentations ℓ-adiques, Sém. Bourbaki 355 (1969).

Known result: The primitive comparison theorem and the period isomorphism. The version here is for
constant coefficients and smooth proper algebraic varieties, with cohomology on test rings and the
maximal ideal put into the coefficients. It is deduced from the duality comparison on products of
projective lines, without almost finiteness. Source: P. Scholze, p-adic Hodge theory for
rigid-analytic varieties, Forum Math. Pi 1 (2013), Thm 1.3 and 5.1; for the method, B. Zavyalov,
Poincaré duality in abstract 6-functor formalisms, arXiv 2301.03821, Thm 3.3.3 and Appl. 1.3.4;
Li–Reinecke–Zavyalov, arXiv 2410.08200, §6.4.

Known result: Finiteness and Galois continuity of p-adic étale cohomology. The version here is for
smooth proper varieties over an algebraic closure of Q and constant coefficients, with integral
coefficients defined as Witt vectors of the mod p functions. Finiteness is lifted from finiteness
modulo p, which comes with the primitive comparison. Source: SGA 4, Exp. XIV (Artin), finiteness for
proper morphisms; Scholze 2013 Thm 1.1; by duality, Zavyalov arXiv 2301.03821 Appl. 1.3.4.

This file: p-adic etale cohomology of smooth proper varieties is finite with continuous Galois
action. Natural Galois-equivariant period map, bijective for smooth proper varieties. Frobenius
relations on special-fibre points pass to l-adic cohomology; inertia acts trivially. p-adic
cohomology is crystalline and its Frobenius satisfies the congruence relation. -/

section

open CategoryTheory ModuleCat.Algebra
variable {p} [ThePrime p] {R : CommRingCat} [Algebra R Ω] {Y} [@IsCharted R Y Ω _ _]
  [AlgebraicGeometry.IsProper Y.hom]

/-- Let Ω, the algebraic closure of ℚ, be an R-algebra, and Y proper over R and charted over Ω
(`IsCharted`). Then Hⁿ(Y_Ω, ℤ_p), computed on test rings, is a finitely generated
ℤ_p-module for every n.

Known result: Finiteness and Galois continuity of p-adic étale cohomology. -/
lemma finite_padic_cohomology n : Module.Finite ℤ_[p] (H (freeAb (testIncl ⋙ geomPoints R Ω Y))
  ellAdicCoeff n) := let := (IsAlgClosed.lift : Ω →ₐ[ℚ] ℂ_[p]).toAlgebra
  finite_H_ellAdicCoeff ((finite_and_primitive_comparison Ω (isAcyclicAt_almostCoeff (N :=
    Unit) (by simp)) Y).2.1 n)

instance {n} : Module.Finite ℚ_[p] (ellAdicCohom R Ω n ⟨Y⟩) :=
  (finite_padic_cohomology n).base_change ..

/-- Let Ω be an algebraic closure of ℚ, Y proper over R and charted over Ω, and Γ the profinite
Galois group of Ω over a field K, acting R-linearly. Then g ↦ l(gx) is continuous for x in
V^n(Y) and ℚ_p-linear l: V^n(Y) → Q̄_p^N.

Known result: Finiteness and Galois continuity of p-adic étale cohomology. -/
lemma ellAdicCohom.continuous_galoisAction n K [Field K] [Algebra K Ω] [Algebra R K] [IsScalarTower
  R K Ω] [G : IsProGalois Gal(Ω/K) K Ω] x {N} (l : _ →ₗ[ℚ_[p]] Fin N → PadicAlgCl p) :
  Continuous fun g ↦ l (galoisAction R Ω Gal(Ω/K) Y n g x) := by
  obtain ⟨S, rfl⟩ := x.exists_finset; erw [funext fun _ ↦ map_sum (l ∘ₗ _) ..]
  refine continuous_finsetSum S fun ⟨a, t⟩ _ ↦ .of_at fun g₀ ↦
    tendsto_sub_nhds_zero_iff.1 fun U hU ↦ (map_mul_left_nhds_one _).ge (Filter.mem_map.2 ?_)
  let L := (l ∘ₗ (galoisAction ..) g₀).restrictScalars ℤ_[p] ∘ₗ (TensorProduct.mk ..) a
  obtain ⟨k, b, q, w⟩ := (((tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
    ).eventually (((Submodule.isCompact_of_fg
    (.map L (finite_padic_cohomology n).1)).isVonNBounded ℚ_[p] hU).eventually_nhds_zero
    (mem_of_mem_nhds hU))).and (.of_forall exists_ellAdicCoeff_modShortExact_pow)).exists
  obtain ⟨s, z, ht⟩ := ((isProperOver_pointsToBase Y.hom).isCohomContinuous.isFilteredColimit_adjoin
    _ Ω (𝟙 _) n).2 (t.push _ q n)
  filter_upwards [s.eventually_all.2 fun b _ ↦ (G.6 b).mem_nhds rfl] with g hg
  simp; refine (w.exists_smul_eq_of_push_eq_zero _ ?_).elim fun _ e ↦
    map_sub L .. ▸ congr(L $e) ▸ by simpa using! b (by simp)
  erw [map_sub, sub_eq_zero, ← H.map_push, ← ht, ← HV.map_comp, ← Functor.map_comp, ← op_comp]
  congr with a; exact (g.toAlgHom.restrictScalars R).adjoin_le_equalizer 1 hg a.2

open TensorProduct Function AlgebraicGeometry Functor AlgebraTensorModule Comparison PadicTest
  Module
variable {p : _} [ThePrime p] {R : CommRingCat} [Algebra R OC] [Algebra R Ω] {e : Ω →+* PadicAlgCl
  p} (he : ∀ r, e (algebraMap R Ω r) = (algebraMap R OC r).1) {S} [CommRing S] [Algebra Ainf S]
  [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] Ainf S] (K) [CommRing K] [Algebra S K] [Algebra ℚ_[p] K]
  [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [IsScalarTower ℤ_[p] S K] {Ψ} (θ :
  asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ) (n) {Γ} [Group Γ] [MulSemiringAction Γ Ω]
  [SMulCommClass Γ R Ω] {j : Γ → Gp p} (hj : ∀ g x, j g (e x) = e (g • x))

/-- For g in Γ acting on Ω over R, with j(g)e = eg, the identity of each p-adic test as an
R-algebra map to its twist by j(g). -/
noncomputable def toTwistAlg g :
  algFunctor ⋙ restrictAlg R _ ⟶ PadicTest.twist (j g) ⋙ algFunctor ⋙ restrictAlg R _ :=
  .mk (CommAlg.homOfRingHom (.id _) fun z ↦ congrArg ·.structureMap (by ext; simp [← he, hj]))

instance (M : ModuleCat ℚ_[p]) : CompatibleSMul ℤ_[p] ℚ_[p] K M :=
  IsLocalization.tensorProduct_compatibleSMul (nonZeroDivisors _) ..

/-- The period map. For a period pair (S, K) (`IsPeriodRingPair`), K flat over S, and Ψ ≅ K ⊗_S
`periodAlg` S on tilts: K-linear J : K ⊗_{ℤ_p} V^n(Y) → H^n(Y on p-adic tests, Ψ),
natural in Y, compatible with Γ-twists, bijective for Y proper and charted over `Ω`.

Known result: Primitive comparison theorem and period isomorphism. -/
lemma exists_period_map [Flat S K] (h : IsPeriodRingPair p S K) : ∃ J : ∀ Y,
  K ⊗[ℤ_[p]] ellAdicCohom R Ω n ⟨Y⟩ →ₗ[K] H _ _ n, (∀ W Y (f : W ⟶ Y) x,
  J W ((((ellAdicCohom ..).map f.op).hom.restrictScalars _).baseChange _ x) = .map _ (freeAb.map
  (testPoints.map f)) n (J Y x)) ∧ (∀ Y g σ (β : PadicTest.twist (j g) ⋙ moduleCoeff Ψ ⟶ moduleCoeff
  Ψ), (∀ c a (w : WittVector p (TiltRing c)), (∀ i, w.coeff i ^ p = w.coeff i) → β c ⟨θ.1 _
  (a ⊗ₜ .of _ _ (1 ⊗ₜ w))⟩ = ⟨θ.1 c (σ a ⊗ₜ .of _ _ (1 ⊗ₜ w))⟩) → ∀ x, J Y (.map σ (.restrictScalars
  _ ((ellAdicCohom.galoisAction ..) g)) x) = (of _ β).pull (freeAbMap (whiskerRight
  (toTwistAlg he hj g) _)) n (J Y x)) ∧ ∀ Y [IsCharted Y Ω] [IsProper Y.hom], Bijective (J Y) := by
  let E Y := equivOfCompatibleSMul ℚ_[p] ℤ_[p] K K (ellAdicCohom R Ω n ⟨Y⟩) ≪≫ₗ cancelBaseChange ..
  obtain ⟨⟨b, hb, hB⟩, _⟩ := exists_primitive_period_comparison K θ h, Flat.trans ℤ_[p] ℚ_[p] K
  algebraize [(algebraMap _ ℂ_[p]).comp e]
  let J Y (α : freeAb (testPoints Y) ⟶ _) := pullₗ b α n ∘ₗ baseChangeMap .. ∘ₗ (E Y).1
  have hT Y α a x : J Y α ((E Y).symm (a ⊗ₜ x)) = pull ⟨_,
    whiskerLeft _ (tensorWith.mk _ a _) ≫ coeffMap b⟩ α
    n x := by simpa [J] using! (pull_push ⟨_, _⟩ (h := rfl) ..).trans (Abelian.Ext.comp_mk₀_id _)
  refine ⟨(J · _), fun _ _ _ ↦ ?_, fun _ _ _ β hβ ↦ ?_, fun Y ↦
    (finite_and_primitive_comparison Ω (isAcyclicAt_almostCoeff h.pFlat_smul_eq_zero)
    Y).elim fun hN P ↦ (hB hN (isAffinelyCovered_algPoints (ι := algFunctor) (·.isTest.2)
    _).hasFlatBaseChange finite_padic_cohomology (P.2 he) n).comp ((hN ..).comp (E Y).bijective)⟩
  all_goals refine (reindex_equiv (E _).symm).1.2 (·.inductionOn (fun a x ↦ (hT _ _ _
    (x.map _ _ n)).trans ?_) (by simp_all))
  · simpa [hT] using (map_pull_eq_pull_map ..).symm
  simp [hT, pull_trans, ← map_pull_eq_pull_map (Category.id_comp _)]
  refine (congrArg (pull _ · n x) (freeAb.hom_ext fun _ _ ↦ congrArg FreeAbelianGroup.of
    (baseChangeOf.ext (congrArg ULift.up (Spec.map_comp_assoc (𝟙 _) ..)) fun x ↦ by
    erw [eq_comm, structMap_twist, smul_coe_Cp,
      hj]; rfl))).trans congr(pull ⟨_, $(?_)⟩ _ n x); ext d ⟨y⟩
  exact .trans congr(⟨$(hb ..)⟩) (congr(β d ⟨$(hb ..)⟩).trans (hβ _ _ _ fun i ↦
    (map_pow ..).symm.trans (congrArg _ (LocallyConstant.ext fun _ ↦ ZMod.pow_card _)))).symm

end

namespace ellAdicCohom

open CategoryTheory AlgebraicGeometry CommRingCat ellAdicPull Comparison
variable {ℓ} [ThePrime ℓ] {R : CommRingCat} [Algebra R Ω] {Γ} [Group Γ] [MulSemiringAction Γ
  Ω] [SMulCommClass Γ R Ω] {A : ClosurePlace} (hR : ∀ r, algebraMap R Ω r ∈ A) (hℓ : IsUnit (ℓ : A))
  {W Y : Over (Spec R)} [IsCharted Y R] [IsProper Y.hom] {n p f : ℕ} [Fact p.Prime] (hp :
  A.valuation p < 1) {U : PointFunctor} (hX : ∀ B, U B → (p : B) = 0) (j)

/-- For a functor U on rings with points only in rings where p = 0, the endomorphism sending x
in U(B) to its image under b ↦ b^(p^j). -/
def frobEnd : U ⟶ U := ⟨fun B ↦ ↾fun x ↦ U.map (ofHom (frobPow (hX B x) j)) x,
  by intros; ext; dsimp; simp_rw [← U.map_comp_apply]; congr 3; aesop⟩

/-- Absolute Frobenius acts trivially on ℓ-adic cohomology: if p = 0 in every ring B where U has
a point, the endomorphism of U induced by b ↦ b^(p^j) pulls back to the identity of ℚ_ℓ ⊗
Hⁿ(U, ℤ_ℓ). -/
lemma ellAdicPull_frobEnd : ellAdicPull n (freeAb.map (mapOnTests (frobEnd hX j))) = 1 := by
  ext; exact congrArg (_ ⊗ₜ ·) ((hasUnivPoints_elements.isBijective n).1 ((map_pull_eq_pull_map
    (by rfl) ..).symm.trans ((H.map_id _).trans (congr($(pull_whiskerRight (⟨fun A ↦
    ⟨ofHom (frobPow (hX _ A.2) _)⟩, by intros; ext; exact (map_pow ..).symm⟩ : elementsProj
    (testIncl ⋙ U) ⟶ _) ..) _).symm.trans congr(pull ⟨_, $(by ext A ⟨⟨⟩⟩; congrm ⟨⟨fun i ↦ ⟨_ ∘
    $(by ext q; simp [q.2.pow_mem_iff_mem, NeZero.pos]), _⟩⟩⟩)⟩ _ n _)))))

include hR hℓ hp

/-- Congruence relation in ℓ-adic cohomology. Let W, Y be proper over R, Y as in `IsCharted`,
A ⊂ Ω a valuation ring over R of residue characteristic p ≠ ℓ, g a p^f-Frobenius at A. The
congruence relation `CongruenceRelation` above A gives ∑ mᵢ uᵢ^* g^(−eᵢ) = 0 on V^n(Y).

Known result: Smooth proper reduction: unramified ℓ-adic cohomology; Frobenius relations pass to
it. -/
lemma congruence_relation [IsProper W.hom] {g} (hg : IsFrob A (p ^ f) g) {I : Type} [Fintype I] (u :
  I → (W ⟶ Y)) (e : I → ℕ) m (h : CongruenceRelation m (algebraMap R Ω ⁻¹' A.nonunits) p (e · * f)
  u) x : ∑ i, m i • (ellAdicCohom ..).map (u i).op (galoisAction R Ω Γ Y n (g⁻¹ ^ e i) x) = 0 := by
  algebraize [RingHom.codRestrict _ A hR]
  obtain ⟨y, rfl⟩ := (isCohomEquiv_generic_fibre hp hℓ Y).bijective_ellAdicPull.2 x
  let σ i := (MulSemiringAction.toRingHom ..).restrict A A (mem_decompGroup_iff.1
    (pow_mem (inv_mem hg.1) (e i)) · |>.2)
  let mv i : baseChangeOf .. ⟶ (geomPoints ..) Y := (geomPoints ..).2 (u i) ≫ baseChangeTransition _
    (ofHom (σ i)) (by ext r; exact smul_algebraMap _ r)
  let F i := frobEnd (fun _ x ↦ by simpa using x.2 p hp) (e i * f) ≫
    (zeroPoints (fibreProd.snd ..) (A · < 1)).ι ≫ mv i
  conv_lhs => enter [2, i]; erw [comp, ← freeAb.4, comp, ← freeAb.4, freeAb.4 (mapOnTests
    (baseChangeTransition _ (ofHom A.subtype) rfl)) (mapOnTests (mv i)), ← comp, ← map_zsmul]
  have := by
    simpa [← comp] using congr(ellAdicPull n $(relationLocus_sum_eq_zero m (mapOnTests <| F ·)) y)
  refine (map_sum ..).symm.trans ((congrArg _ ((Set.ext A.valuation_lt_one_iff ▸
    ((isProperOver_pointsToBase _).baseChange _).proper_base_change hℓ :
    IsCohomEquiv ..).bijective_ellAdicPull.1 ((((isProperOver_pointsToBase _).baseChange
    _).isCohomDense_of_coincidences F fun z B x H ↦ ?_).isCohomEquiv.bijective_ellAdicPull.1
    (by simpa [F, ← comp, ellAdicPull_frobEnd])))).trans (map_zero _))
  have hP i a := z.2 (a - σ i a ^ _) (by simpa [σ] using! (hg.pow (e i)).2 (σ i a) (by simp))
  exact (@h _ _ (.of_eq_zero Fact.out (by simpa using z.2 p hp)) _ (congr($(z.1.2).1.1 ·).trans <|
    z.2 _ ·)).mono fun i j h ↦ H (baseChangeOf.ext congr(⟨$h⟩) fun a ↦ by
    simpa [← pow_mul'] using! (hP i a).trans (hP j a).symm)

/-- For Y proper and charted over R (`IsCharted`), Ω the algebraic closure of ℚ, A a
valuation subring of Ω containing the image of R, with ℓ a unit and positive residue
characteristic, the inertia group of A in Γ acts trivially on V^n(Y).

Known result: Smooth proper reduction: unramified ℓ-adic cohomology; Frobenius relations pass to
it. -/
lemma galoisAction_eq_one_of_inertia {g} (hg : g ∈ inertiaGroup Γ A) :
  galoisAction R Ω Γ Y n g = 1 := by ext; simpa [neg_add_eq_iff_eq_add] using (congruence_relation
  hR hℓ hp (f := 0) (inv_mem hg) ![𝟙 _, 𝟙 _] (↑) ![-1, 1] (by simp [CongruenceRelation, Cancels]) _)

end ellAdicCohom

open CategoryTheory AlgebraicGeometry TensorProduct Ideal WittVector Fact CharP Comparison
  Algebra.TensorProduct ConcreteCategory PadicTest ModuleCat.Algebra MulSemiringAction Function
  ULift Set

seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
/-- R noetherian, mapping into the place A above p of Ω ≅ ℚ̄; W, Y proper over R, charted over Ω, Y
also over R; (γ_i, a_i) Weil pairs at A. If ∑ m_i[Frob^{a_i}u_i(x)] = 0 at field points x of W above
A, then V^n(Y) is crystalline and ∑ m_i u_i^*β_{γ_i,a_i} = 0.

Known result: Congruence relation for the crystalline Frobenius. -/
lemma ellAdicCohom.isCrystalline_and_linearFrob_rel {p} [ThePrime p] {R :
  CommRingCat} K [Field K] [Algebra R Ω] [Algebra K Ω] [Algebra R K] [IsScalarTower R K Ω] {A} [I :
  PadicPlaceEmbedding K A p] (hR : ∀ r, algebraMap R Ω r ∈ A) {W Y} [IsNoetherianRing R] [sm :
  IsCharted Y R] [IsCharted Y Ω] [IsProper Y.hom] n [IsProper W.hom] [IsCharted W Ω] {ι}
  [Fintype.{0} ι] (u : ι → (W ⟶ Y)) (a γ : ι → _) m (h : CongruenceRelation m
  {r | A.valuation (algebraMap R Ω r) < 1} p a u) (hW : ∀ i, IsWeilPair (I.toGp (γ i))
  (a i)) : let ρ := galoisAction R Ω _ Y n; IsCrystalline ρ ∧ ∑ i, m i • (((ellAdicCohom ..).map
    (u i).op).hom.restrictScalars _).baseChange _ ∘ₗ linearFrob ρ (γ i) (a i) = 0 := by
  intro ρ
  obtain ⟨⟨_, -, -, -, _, ⟨g, rfl⟩, w⟩, @⟨I, e, ⟨⟨⟩, hj⟩, _⟩⟩ :=
    Lift.exists_kummer_chart (decompGroup Gal(Ω/K) A), I
  let σ := ((algebraMap ..).comp (e.comp _)).codRestrict 𝓞_ℂ_[p] (by simpa)
  have hσ r : (e (algebraMap R Ω r) : ℂ_[p]) = σ r := rfl
  let := σ.toAlgebra
  let 𝔭 := (IsLocalRing.maximalIdeal _).comap σ
  let k := R ⧸ 𝔭
  have hk r :
    r ∈ 𝔭 ↔ ‖e (algebraMap _ Ω r)‖ < 1 := by simp [𝔭, OC.dvd_iff_norm_le, isUnit_iff_dvd_one, ←hσ]
  have hf {s f} (w : IsWeilPair (I.toGp s) f) : ∀ z : k, z ^ _ = z := Quot.ind fun r ↦
    Ideal.Quotient.eq.2
    (by simpa [← map_inv, *, norm_sub_rev] using w.2 _ ((intQpBar p).valuation_le_one ⟨_, hR r⟩))
  have : Finite k := .of_not_infinite fun _ ↦ absurd (Polynomial.funext (R := k) (by
    simpa using @hf g⁻¹ _ (by simpa)))
    (Polynomial.monic_X_pow_sub (p := .X) (by simp [one_lt_pow₀, out])).ne_zero
  let := (Finite.isField_of_domain k).toField
  have : CharP k p := .of_eq_zero out (Quotient.eq_zero_iff_mem.2 (by simp [𝔭, out]))
  obtain ⟨⟨M, hM⟩, y, hy⟩ := exists_cancels_frobPow_locally m a u 𝔭 (by simp [𝔭,
    out]) (by simpa [← hk,
    val_comap_lt_one] using h), IsBezout.isPrincipal_of_FG _ (𝔭.fg_of_isNoetherianRing.map σ)
  obtain ⟨⟨V, hV⟩, x, rfl⟩ := sm.1, IsAIC.exists_pow_eq (M + 1) y
  obtain ⟨⟨N, hN⟩, hy⟩ := OC.exists_dvd_pow (mt (.pow _) (map_comap_le (hy.ge (subset_span rfl))))
    (NeZero.ne ↑p), (mem_span_singleton.1 <| hy ▸ mem_map_of_mem σ (x := ·) ·)
  obtain ⟨hP, _, hA, h0⟩ := exists_crysPeriodAlgebra hN
  obtain ⟨g, hg', G'⟩ := hP.existsUnique_witt_lift (cast_eq_zero ..) (Ideal.Quotient.lift 𝔭
    (ocToAmaxModPd.comp σ) (hy · · |>.elim (by simp +contextual [h0])))
  algebraize [g]
  let v a (hf : ∀ z : k, z ^ p ^ a = z) := toCrysPoints V (r :=
    .comp (constantCoeff.liftOfRightInverse (teichmuller p) .refl ⟨pdQuotientMk
    _, by simp [IsCompleteTorsionFree.p_mem_pdIdeal, witt_reduction_spec k]⟩) (algebraMap _ k))
    ⟨fun B ↦ CommAlg.homOfRingHom (frobPow B.p_eq_zero_mod_pdIdeal a) fun z ↦
    .symm (congr(pdQuotientMap _ $((hg' (teichmuller p ⟦z⟧)).trans ((congrArg _ (hf _).symm).trans
    (map_pow ..)))).trans (map_pow ..)), by intros; ext; exact (map_pow ..).symm⟩
  choose J Jn Js JY using (exists_period_map hσ Bcris (.refl _) · hj hP.2)
  have A := (hasPartitions_periodAlg (S :=
    Amax) Bcris (.refl _)).hasZariskiDescent (𝟙 _) (by simp) (·.isTest.2)
  have U := A (hV.1.whisker (algFunctor ⋙ restrictAlg R _))
  let E n := LinearEquiv.ofBijective (H.mapₗ .. ∘ₗ J n Y) ((U.isCohomEquiv n).comp (JY ..))
  let P a hf := crysComparison.pull (freeAbMap (v a hf)) n
  choose C hC using fun z ↦ (E n).surjective (P 0 pow_one z)
  have key {a} γ hf z : E n (tensorAction _ ((a, toGp γ) : FrobGal) (ρ γ) (C z)) = P a hf z :=
    let F := toRingHom FrobGal Amax (a, toGp γ)
    let τ := Functor.whiskerRight ((baseChangeTranspose (PadicTest.twist (toGp γ) ⋙ tilt ⋙
      wittFunctor) (tilt ⋙ wittFunctor ⋙ algBaseChange _ ⋙ @restrictAlg _ _ _ _ F.toAlgebra)).2
      ⟨fun c ↦ CommAlg.homOfRingHom (includeRight.1.comp
      (map (iterateFrobenius c.TiltRing p a))) fun _ ↦ .trans (congrArg (tmul _ 1) (ext fun _ ↦ by
      exact congr($(tiltMap_comp ..)^_).trans (map_pow ..).symm)) ((includeRight.2 _).trans
      congr($(hA ..) ⊗ₜ _).symm), by intros; ext; exact congrArg (tmul _ 1) (ext fun _ ↦ (map_pow
      (tiltMap ..) ..).symm)⟩) (restrictAlg ℤ _ ⋙ algCompletion ℤ p ⋙ forget₂ _ CommRingCat)
    have hτ {c a w b v} (h : F a = b) (k : _ = v) : τ c (.of _ _ (a ⊗ₜ w)) = .of _ _ (b ⊗ₜ v) :=
      (adicMap_algebraMap ..).trans (congrArg _ congr($((mul_one _).trans h) ⊗ₜ $k))
    let β := (baseChangeTranspose (_ ⋙ _ ⋙ periodAlg ..) ((_ ⋙ periodAlg ..) ⋙ algBaseChange Bcris ⋙
      @restrictAlg _ _ _ _ (toRingHom FrobGal _ (a, _)).toAlgebra)).2 ⟨fun c ↦ CommAlg.homOfRingHom
      (includeRight.1.comp (τ c).hom) fun _ ↦ .trans congr(1 ⊗ₜ $(hτ rfl (map_one _)))
      ((includeRight.2 _).trans congr($(smul_algebraMap_eq_algebraMap_smul ..) ⊗ₜ _).symm),
      by intros; ext; exact congr(1 ⊗ₜ $(τ.naturality_apply ..))⟩
    have fix w := congr($(G' (F.comp g) fun w ↦ congr(pdQuotientMap F $(hg'
      w)).trans ((w.1 0).inductionOn fun z ↦ (untilt_surjective_of_isAIC (σ z)).elim fun t h ↦
      (congrArg _ (h ▸ ocToAmaxModPd_untilt t)).trans (hf ⟦z⟧ ▸ show _ = ocToAmaxModPd (σ
      _) by erw [map_pow, ← (Subtype.ext (by simp [← hσ, hj]) : toGp γ • σ z = σ z), ← h,
      ← untilt_frobGal_smul (a, _), ocToAmaxModPd_untilt, ← smul_teichmuller, ← hA]; rfl))) w)
    let σ : _ ⋙ crysComparison.φ ⟶ crysComparison.φ := ⟨fun c ↦ ⟨ofHom ⟨(τ c).hom, fun _ ↦
      hτ (fix ..) (map_one _)⟩⟩, by intros; ext; apply τ.naturality_apply⟩
    let N := freeAb V.toFunctor
    .trans (congrArg (H.map _ _ n) (Js n Y _ _ (Functor.whiskerRight β (restrictAlg ℤ _ ⋙
      moduleCoeff (asModules (𝟭 _))) :) (fun _ _ _ h ↦ congrArg up (congrArg₂ (tmul _) (mul_one _)
      (hτ (map_one _) (ext fun i ↦ congr($(pow_iterate ..) _).symm.trans (iterate_fixed (h i) _)))))
      _)) (.trans (map_pull_eq_pull_map
      (b := (Functor.whiskerRight (toTwistAlg hσ hj γ) N :)) ..) (.trans (congrArg _ (hC z)) (.trans
      (pull_trans ..) ((congrArg (pull ⟨_, ·⟩ _ n z) (by ext; exact congr(⟨$(by simp) ⊗ₜ _⟩))).trans
      (congr($(pull_whiskerRight σ crysComparison.coeffHom _) z).trans (congrArg (pull _ · n z) (by
    ext c : 2
    exact ((N.map_comp ..).trans congr($(N.map_comp ..) ≫ _)).symm.trans (congrArg _ (ext_apply
      (untilt_surjective_of_isAIC (R := c.ProdRing).forall.2 fun x ↦
      (congrArg _ (fontaineTheta_teichmuller x)).symm.trans (congr(pdQuotientMap (τ
      c).hom $((pow_one _).trans (testToThickening_theta ..))).trans ((congrArg _ (hτ (map_one _)
      (map_teichmuller ..))).trans ((testToThickening_theta ..).symm.trans (.trans
      (congrArg _ ((fontaineTheta_teichmuller _).trans (map_pow ..))) (map_pow ..)))))))))))))))
  have S : Submodule.span Bcris (.range C) = ⊤ := by
    simp [← Submodule.map_eq_top_iff (e := E n), Submodule.map_span, ← range_comp', hC]
    exact span_range_crysComparison_pull_eq_top V _ (isoOfAppBijective _ fun _ ↦
      (funext pow_one).symm.subst bijective_id).isIso_hom (witt_reduction_spec k k).2.1 hV
      (irreducible p) (.equiv <| equivOfCompatibleSMul _ ℚ_[p] .. ≪≫ₗ E ·) n
  have D {F} z : C z ∈ fixedPeriods ρ _ F := .of_forall fun g ↦
    (E n).injective (hC z ▸ key g pow_one z)
  refine (iff_self_and.2 fun c ↦ LinearMap.ext_on_range S fun z ↦ ?_).1
    (eq_top_mono (Submodule.span_mono (range_subset_iff.2 D)) S)
  let T := ⨅ i, (V.whisker _).preimage (testPoints.map (u i))
  refine (JY ..).1 (((InfClosed.iInf_mem (s := IsCohomDense _) (fun _ a _ ↦
    a.inf) .of_top_le fun _ ↦ U.preimage _ : T ∈ _).isCohomEquiv n).1 ?_)
  simp [linearFrob_apply c.isPotCrys (hW _), D, Jn, H.map_map]
  exact .trans congr(∑ i, m i • $(congr(H.map _ $freeAb.hom_ext n _).trans
    ((H.map_comp ..).trans ((congrArg _ (key _ (hf (hW i)) z)).trans (H.map_map (T.homOfLe (iInf_le
    _ i) ≫ Subfunctor.fromPreimage ..) ..))))) (H.sum_map_eq_zero_of_relationLocus _ _ (A fun c w ↦
    (hM _ _ hN hy c (T.ι.1 c w) · · |>.imp fun _ ↦ .imp_right fun e B f b ↦ ((congrArg _
    (by funext; exact ((_ ≫= Category.assoc ..).trans (Spec.map_comp_assoc ..).symm))).mpr (e _
    (CrysTest.p_eq_zero_mod_pdIdeal _) _ (by exact b.map (testToThickening B).hom)
    ((((testToThickening B).hom.comp f).2 _).trans (congr(pdQuotientMap _ $h0).trans (map_zero
    _))))).mono fun _ _ e ↦ Subtype.ext (down_injective (Over.OverMorphism.ext e)))).isCohomEquiv _)
