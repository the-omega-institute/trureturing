import GRH.Lib.Cohomology.ProjectiveLine.LineChernClass
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Comparison of cohomology theories by duality: a diagonal kernel on products of P¹
(known result; see Lib.Cohomology.ProjectiveLine.NormalizationPullback).

This file: Moving a supported kernel class between points of (P^1)^d one coordinate at a time. -/

open CategoryTheory Fin TotalH

seal TorsionCoeff.mulClass

variable {C} [Category C] {ℓ A} [CommRing A] [InvertsPrime A ℓ] {g : C ⥤ TestOver A} {d} (Θ :
  Theory g) {X} (I : IdealFamily (ringOf (elementsProj X ⋙ 𝟭 _))) (q : (g ⋙ X).sections)

/-- For a section q of (P¹)^ι along g and i in ι, its i-th component, a section of P¹ along g. -/
def projLinePow.component {ι} (q : (ringOf g ⋙ projLinePow ι).sections) (i : ι) :
  (projLineAlong g).sections := ⟨_, (congr($(q.2 ·) i))⟩

namespace IdealFamily

/-- For a compatible family I of ideals on the elements of X, the subfunctor of X of points x in
X(c) at which I is the unit ideal. -/
def topPoints : Subfunctor X :=
  ⟨fun c ↦ {x | I.I (X.elementsMk c x) = ⊤}, fun f _ ↦ I.topLocus.2 ⟨f, rfl⟩ (a := ⟨⟩)⟩

/-- The morphism ℤ[pt]/ℤ[O] → (ℤ[X]/ℤ[sp])∘g induced by the section q, where sp ⊂ X and O ⊂ pt
are the loci where I and its pull-back along q are the unit ideal. -/
def atSection : relFreeAb (I.whisker (sectionLift g q)).topLocus ⟶ g ⋙ relFreeAb I.topPoints :=
  relFreeAb.map (U := I.topPoints.whisker g) (sectionMap q) le_rfl

/-- The isomorphism of total Ext groups into Θ given by pull-back along `IdealFamily.constToZeros`
(constants mod ℓ to functions on the zeros of I), restricted along the section q. -/
noncomputable def zerosEquiv := AddEquiv.ofBijective _ (I.isCohomEquiv_constToZeros
  (sectionLift g q) Theory.locallyConstant.onElements rfl Θ.zariski_descent).bijective_totalH

/-- Extension of a class on (ℤ[X]/ℤ[sp])/ℓ along g to a class on the zeros of I along q: pull back
along q, then invert the bijection induced by `IdealFamily.constToZeros`. -/
noncomputable def extendToZeros := (I.zerosEquiv Θ q).symm.toAddMonoidHom.comp
    (pullbackAlong (abCoker.desc (I.atSection q ≫ abCoker.π _) (by simpa using
  _ ≫= shortExact_nsmul_abCoker.1) : abCoker (ℓ • 𝟙 _) ⟶ _))

/-- Let maximal ideals of each g(c) be kernels of maps g(f), and t send d sections of P¹,
pointwise, to sections of X. Each class δ supported where I is proper at t(q) has a δ' at
t(q') such that, after any restriction φ and in any theory Θ, δT = t(q)^*w implies δ'T =
t(q')^*w · ∏_j (η_{q_j} + η_{q'_j}). -/
lemma exists_move_kernel (K : TorsionCoeff g) (hQ : ∀ c m, m.IsMaximal → ∃ d f, RingHom.ker ((ringOf
  g).map (f : c ⟶ d)).hom = m) (t : (_ → (projLineAlong g).sections) → (g ⋙ X).sections) (h :
  ∀ {r r'} c, (∀ j, (r j).1 c = (r' j).1 c) → (t r).1 c = (t r').1 c) : ∀ q q' (δ : TotalH _ K.F),
  ∃ δ', ∀ C' [Category C'] (φ : C' ⥤ C) (Θ : Theory (φ ⋙ g)) T w, mapThenComp (restrictAlong φ)
  T δ = pullbackAlong (φ.whiskerLeft (I.atSection (t q))) w → mapThenComp _ T δ' =
  pullbackAlong (φ.whiskerLeft (I.atSection (t q'))) (foldr d (fun j ↦ comp.flip
  (Θ.etaAt (φ.whiskerLeft (freeAbSectionMap (q j) + freeAbSectionMap (q' j)))).toTotalH) w) := by
  induction' d with d ih <;> simp only [forall_fin_zero_pi, forall_fin_succ_pi]
  bound
  intro x q x' q' δ
  obtain ⟨⟨J, z, ξ, e⟩, δ, h₁⟩ := exists_etaClass_supported_diagonal x x',
    ih _ (h · <| cases rfl ·) q q' δ
  let L x := I.whisker (sectionLift g (t (cons x q')))
  replace z c k := @h (cons x q') (cons _ q') c (cases (z c k) (by simp))
  have E : IsLocallyEverything _ (((L x').topLocus ⊓ ((L x).topLocus ⊔ J.topLocus)).preimage
    (L _).topLocus.ι) := fun c y m M ↦ (hQ c m M).elim
    fun _ ⟨f, k⟩ ↦ have n T := k ▸ map_eq T f ▸ Ideal.map_eq_bot_iff_le_ker _
    by cases not_or_of_imp fun a b ↦ M.ne_top (eq_top_mono ((n _).1 (congr(I.I (.mk $(z _ ((n _).2
      b)))) ▸ (n (L _)).2 a))
      y.2) <;> peel exists_notMem_eq_top _ ‹_› <;> use Subtype.prop _, by tauto
  refine ((relFreeAb.isCohomEquiv_of_le inf_le_left (K.zariski_descent E)).bijective_totalH.2
    ((K.mulClass ξ.toTotalH (pullbackAlong (relFreeAb.map (𝟙 _) inf_le_left) δ)).pullbackAlong
    (relFreeAb.map {app _ := ↾Function.diag} (by rintro _ _ ⟨_, ⟨⟩⟩ <;> tauto) ≫ relFreeAb.prod
    ..))).imp fun y hy C' _ φ Θ T w k ↦ (relFreeAb.isCohomEquiv_of_le (U' := (L _).topLocus.whisker
    φ ⊓ .whisker (_ ⊔ _) φ) inf_le_left (Θ.zariski_descent (E.whisker φ))).bijective_totalH.1 ?_
  obtain ⟨hy, e⟩ := congr(T.mapThenComp _ $hy), congr(($e).map (restrictAlong φ))
  simp only [map_homClass_comp, map_of, mapThenComp_comp map_homClass, ↓map_restrictAlong_etaClass,
    K.mulClass_naturality, foldr_succ] at *
  erw [hy, h₁ _ _ Θ _ _ k, homClass_comp_homClass_comp,
    Θ.mulClass_congr_of_eq_on_zeros (J.whisker φ) _ (a' := φ.whiskerLeft (relFreeAb.map (𝟙 _)
    inf_le_right ≫ I.atSection _)), ← Θ.mulClass_eq_comp_etaAt _ (relFreeAb.π _),
    homClass_comp_homClass_comp, homClass_comp_homClass_comp, homClass_comp_homClass_comp]
  exacts [congr(pullbackAlong $(relFreeAb.hom_ext fun _ _ ↦ .refl (_ ⊗ₜ _)) _), e, fun c k ↦
    AddCommGrpCat.ext (relFreeAb.mem_of_mk_mem (A := φ _) (AddMonoidHom.eqLocus ..) fun _ ↦
    congrArg (relFreeAb.mk _) (z _ k))]
