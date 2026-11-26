import OmegaMath.NumberTheory.GRH.Lib.Shimura.GoodReduction.ThetaOrthogonality
import OmegaMath.NumberTheory.GRH.Lib.Shimura.AbelianScheme.ThetaFamily
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number
(known result; see Lib.Shimura.Uniformisation.AppellHumbert).

This file: Rigid objects: theta coordinates span sections; theta law over local rings.
Multiplication by nonzero a is an isogeny; counting torsion points over C. Line bundles with theta
coordinates: pull-back, product, translation, uniqueness in Appell-Humbert. -/

variable {E : Type} [Field E] [CMBase E] {D : PEL E} {Z : AlgebraicGeometry.Scheme}
  {τ : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of (NumberField.RingOfIntegers E))}
  {X : ThetaFamily D Z τ} {R : Type} [CommRing R]

/-- On every pull-back of x to a noetherian local ring B, global functions on the abelian scheme
are constant and the coordinates span H⁰(N) over B. -/
def ThetaObject.IsRigid (x : ThetaObject X (AlgebraicGeometry.Spec ⟨R⟩)) := ∀ ⦃B⦄ [CommRing B]
  [IsLocalRing B] [IsNoetherianRing B] ⦃y : ThetaObject X (AlgebraicGeometry.Spec ⟨B⟩)⦄ ⦃b⦄,
  y.IsPullbackAlong b x → HasConstFunctions y.groupScheme.hom ∧
  Submodule.span B (.range (coordSection y.isProjEmbedding.1)) = ⊤

lemma ThetaObject.obj_isThetaStructure (x : ThetaObject X (AlgebraicGeometry.Spec ⟨R⟩))
  [IsLocalRing R] : IsThetaStructure (D.lagrangian.addSubgroupOf _)
  (.comp x.levelPoints (AddSubgroup.inclusion D.T_le_levelTorsion)) x.isProjEmbedding.1
  (X.theta_law _ x.isGroupBaseChange).choose := Exists.choose_spec _

open Nat AddSubgroup AlgebraicGeometry CategoryTheory FractionalIdeal LinearMap NumberField
  Submodule MonoidalCategory Complex Finset LineBundle
section

variable {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n]

/-- For a non-zero ideal I of O_E, the submodule of (𝔸_f / Ô)ⁿ killed by I has N(I)^|n|
elements, where N(I) is the absolute norm and |n| the size of the index set. -/
lemma card_torsionBySet_adelicTorsion {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) :
    .card (torsionBySet (𝓞 E) (_root_.AdelicTorsion E n) I) = I.absNorm ^ Fintype.card n := by
  let J := (coeIdealHom (nonZeroDivisors _) E I)⁻¹.coeToSubmodule.subtype
  rw [← (torsionBySet ..).map_comap_eq_of_surjective frameTorsionClass_surjective,
    (_ : .comap .. = (J.compLeft n).range), ← range_comp,
    ← card_congr (quotKerEquivRange _).toEquiv, ker_comp, ker_frameTorsionClass_one]
  exact (index_pi fun _ ↦ (Submodule.comap J 1).toAddSubgroup).trans (Finset.prod_eq_pow_card fun _
    _ ↦ .trans (by simpa using! card_congr (quotientEquiv _ 1 1 _ (by aesop) (by simp [mem_inv_iff,
    *]) coeIdeal_le_one (by simpa) (by simpa)).toEquiv) ((relIndex_map_map_of_injective _ ⊤
    (AddSubgroupClass.subtype_injective _)).trans (relIndex_top_right _)))
  ext; simp [← map_smul_of_tower, ← mem_ker, ker_frameTorsionClass_one, J, range_compLeft,
    mem_inv_iff, *, Algebra.smul_def, mul_comm, @forall_comm n, -map_smul, -LinearMap.map_smulₛₗ]

end

variable {E : Type} [Field E] [CMBase E] {D : PEL E} {R : CommRingCat}
  {Z : AlgebraicGeometry.Scheme}
  {τ : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of (NumberField.RingOfIntegers E))}
  {X : ThetaFamily D Z τ} (y : ThetaObject X (Spec R)) [IsLocalRing R]

/-- On the abelian scheme of an object y over a local ring, multiplication by a non-zero element
a of O_E is finite, flat and surjective. -/
lemma ThetaObject.finite_flat_surjective_smul {a : 𝓞 E} (ha : a ≠ 0) :
  IsIsogeny (a • 𝟙 y.groupScheme) := by
  choose c e using Ideal.mem_span_singleton'.1 (Ideal.span {a}).absNorm_mem
  refine finite_flat_of_quasiFinite _ (@.of_comp _ _ _ _ (c • 𝟙 y.groupScheme).1 ?_) (@.of_comp _ _
    _ (c • 𝟙 y.groupScheme).1 _ ?_) <;> simp_all [← Over.comp_left, smul_smul, mul_comm,
    cast_smul_eq_nsmul,
    -cast_natAbs, IsAbelianScheme.nsmul_surjective, locallyQuasiFinite_of_pull_picClass
    y.isProjEmbedding _ (pull_nsmul_eq_sq_smul y.hasClassLaws.1 _)]

/-- Let A be the abelian variety of an object of the family over ℂ. Every injective O_E-linear
map (𝔸_f / Ô)ⁿ → A(ℂ) has all torsion points of A(ℂ) in its image. -/
lemma ThetaObject.exists_apply_eq_of_torsion (x : ThetaObject X (Spec ⟨ℂ⟩)) {f :
  _root_.AdelicTorsion E D.Index →ₗ[𝓞 E] 𝟙_ _ ⟶ x.groupScheme} (i : (⇑f).Injective) y : (∃ m ≠ 0,
  m • y = 0) → ∃ l, f l = y | ⟨m, hm, h⟩ => have c :=
    (x.isProjEmbedding.nonempty_uniformisation x.smoothOfRelativeDimension).some.card_torsion hm
  have := finite_of_card_ne_zero (c.trans_ne (by aesop))
  (((Subtype.map_injective (by simp_all [← map_nsmul, cast_smul_eq_nsmul])
    i).bijective_of_nat_card_le
    ((card_torsionBySet_adelicTorsion (I := Ideal.span {↑m}) (by simpa)).trans_ge (c.trans (by
    simp [↓Ideal.absNorm_span_natCast, finrank_eq_two_mul_card_infinitePlace, RingOfIntegers.rank,
      abelianDim, ↓Module.finrank_fin_fun]; ring)).le)).2 ⟨y, h⟩).rec (⟨·, congr($(·))⟩)

variable {O : Type} [CommRing O] [ValuativeArc O]
  {X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of O))} {ι κ V V' : Type}
  [FinComplexSpace V] [FinComplexSpace V'] {L : Submodule ℤ V} {B : LatticeForm L}
  {B' : LatticeForm L} {χ : V → ℂ} {χ' : V → ℂ} {θ : V → ι → ℂ} {θ' : V → κ → ℂ}
  {S : AlgebraicGeometry.Scheme} {e : V → (AlgebraicGeometry.Spec (CommRingCat.of ℂ) ⟶ S)}
  {N : LineBundle S ι} {M : LineBundle S κ} [AddObj X] (u : Uniformisation (O := O) X V)
  (h : @HasThetaCoords S ι V _ L e N B χ θ) (h' : HasThetaCoords (ι := κ) L e M B' χ' θ')

attribute [local simp, local grind] ofLinearComb IsHomogCoords atGeneric IsSection IsFrame

lemma Uniformisation.atGeneric_add a z : atGeneric u.expMap (z + a) =
  atGeneric u.expMap z ≫ (translation (u.expMap a)).1 := by simp [← Over.comp_left]

namespace HasThetaCoords

include h

lemma pull {S' L' e' f} F (he : ∀ z, e (F z) = e' z ≫ f) (hF : ∀ l ∈ L', F l ∈ L := by aesop) :
    @HasThetaCoords S' _ V' _ L' e' (N.pull f) (B.pullForm F) (χ ∘ F) (θ ∘ F) :=
  ⟨h.1.pull f, h.rec (by simp_all [isAppellHumbert_iff, riemannForm]),
  (h.3 · |>.imp (by fun_prop) (by aesop)), (he · ▸ h.4 _ :)⟩

/-- If θ gives theta coordinates of type (B, χ) for N along e, then the monomials of degree m in
θ give theta coordinates of type (mB, χ^m) for the m-th power of N. -/
lemma pow m : HasThetaCoords L e (N.pow m) (m • B) (χ ^ m) fun z i ↦ ∏ a, θ z (i a) := by
  obtain ⟨⟨⟩, ⟨⟩⟩ := forall_and.1 h.3, h
  constructor <;> simp_all [IsLinearSystem.pi, IsAppellHumbert.nsmul, thetaSpace, mul_pow,
    landsIn_iInf, LineBundle.pow, prod_eq_zero_iff, ← exp_nsmul, mul_div]; fun_prop

lemma pull_translate {f a} (he : ∀ z, e (z + a) = e z ≫ f) : HasThetaCoords L e (N.pull f) B
  (fun l ↦ χ l * B.riemannPhase l a) fun z i ↦ B.thetaShift a (θ · i) z := ⟨h.1.pull f,
  h.2.shift a, by simp [↓h.2.thetaShift_mem, h.3], (he · ▸ h.4 _ |>.smul (by simp))⟩

include h'

lemma mul : HasThetaCoords L e (N.mul M) (B + B') (χ * χ') fun z p ↦ θ z p.1 * θ' z p.2 := ⟨h.1.mul
  h'.1, h.2.add h'.2, fun _ ↦ thetaSpace.mul (h.3 _) (h'.3 _), fun _ ↦ (h.4 _).mul (h'.4 _)⟩

/-- Let e be holomorphic, and let θ, θ' be theta coordinates along e of N, M, of types (B, χ),
(B', χ') for L. A section w of N ⊗ M⁻¹, L-periodic along e, pulls back to Gθ'_a/θ_i where
θ_iθ'_a ≠ 0, for a theta function G of type (B − B', χ/χ'). -/
lemma exists_theta_of_isSection {w} (hw : (N.mul M.inv).IsSection w) (he : ∀ z,
  HolomorphicAt e z) (hL : ∀ᵉ (l ∈ L) (z) (i), w i
  _ (e (z + l)) = w i _ (e z) := by grind [atGeneric]) : ∃ G ∈ (B + -B').thetaSpace (χ * χ'⁻¹), ∀ i
  a z, θ z i ≠ 0 → θ' z a ≠ 0 → w (i, a) _ (e z) = G z * θ' z a / θ z i := by
  choose p hp using (exists_landsIn _ <| e ·)
  use! fun z ↦ w (p z) _ (e z) * θ z (p z).1 / θ' z (p z).2, fun z ↦ (he z (hw.1 _)
    (hp z)).elim fun a b ↦ ((b.differentiableAt.mul ((h.3 (p z).1).1 z)).mul (((h'.3 (p z).2).1
    z).inv ?_)).congr_of_eventuallyEq (a.mono ?_) <;> cases_type* HasThetaCoords <;>
    simp [thetaSpace, add_div, exp_add, exp_neg, neg_div, field] at * <;> grind

/-- Let N, M have theta coordinates θ, θ' of types (B, χ), (B', χ') for a full lattice L along a
holomorphic L-periodic e, and w trivialise N ⊗ M⁻¹. Then Riemann forms agree, χ = χ' on L,
and w_{ia}(e z) = c·exp((B(z,z) − B'(z,z))/2)·θ'_a(z)/θ_i(z) where both are non-zero, c
constant. -/
lemma riemannForm_eq_of_isFrame [IsFullRankLattice L] {w} (r : (N.mul M.inv).IsFrame w) (o : ∀ z,
  HolomorphicAt e z := by intro; apply (Uniformisation.immersive ..).1) (k : ∀ l ∈ L, ∀ z,
  e (z + l) = e z := by grind [atGeneric]) : B.riemannForm = B'.riemannForm ∧ (∀ l ∈ L, χ l =
  χ' l) ∧ ∃ c, ∀ i a z, θ z i ≠ 0 → θ' z a ≠ 0 → w (i, a) _ (e z) = c * exp ((B z z - B' z z) / 2) *
  θ' z a / θ z i := (h.exists_theta_of_isSection h' r.1 o).elim fun G H ↦ .imp_right
  (.imp_right (⟨G 0, ·⟩)) (by grind [by simpa using ((h.2.add h'.2.neg).eq_exp_of_ne_zero H.1 fun z
  ↦ by grind [(N.mul M.inv).exists_landsIn (e z), HasThetaCoords, landsIn_inf, mul_opens, inv_opens,
  isUnit_iff_ne_zero])])
