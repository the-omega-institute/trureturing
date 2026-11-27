/- GID: D5/S3/Zeros/GRH/Lib/PadicComparison/Duality/IntegrationOverLine
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicComparison/Duality/IntegrationOverLine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicComparison.Duality.IntegrationOverLine. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicComparison/Duality/IntegrationOverLine.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicComparison.Duality.MovingKernel
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Comparison of cohomology theories by duality: a diagonal kernel on products of P¹
(known result; see Lib.Cohomology.ProjectiveLine.NormalizationPullback).

This file: Integration along P¹, natural operations, retract argument with the diagonal kernel on
(P¹)^d. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor

noncomputable section


open CategoryTheory Fin TotalH Functor.Elements Finsupp
open Function hiding comp comp_id id_comp
set_option backward.isDefEq.respectTransparency false
variable {C C' D} [Category C] [Category C'] [Category D] {ℓ A} [CommRing A] [InvertsPrime A ℓ]
  {g : C ⥤ TestOver A} {M : TorsionCoeff g} {S F : AbFunctor C} (φ : C' ⥤ C) (ψ : D ⥤ C') (x :
  TotalH S F)

lemma map_restrictAlong_restrictAlong : map (restrictAlong ψ) (map (restrictAlong φ) x) =
  map (restrictAlong (ψ ⋙ φ)) x := TotalH.map_map ..

variable (h : M.HasLineFormula) {φ} {M' : TorsionCoeff (φ ⋙ g)} (β : φ ⋙ M.F ⟶ M'.F)

lemma lineBasis_naturality T i (x : TotalH S _) : mapThenComp _ (M'.lineBasis i).toTotalH
  (mapThenComp (restrictAlong φ) T x) = mapThenComp (restrictAlong (precomp φ
  _)) (.map (restrictAlong (elementsProj _)) T) (mapThenComp _ (M.lineBasis i).toTotalH x) := by
  cases i <;> erw [map_comp_assoc, map_comp_assoc, map_restrictAlong_restrictAlong,
    map_restrictAlong_restrictAlong]
  erw [M.onElements.etaAt_naturality (precomp ..) M'.onElements, TorsionCoeff.lineBasis]; rfl
  erw [map_homClass, comp_id, id_comp]; rfl

namespace TorsionCoeff.HasLineFormula

lemma bijective_iff_of_hasUnivPoints {Y Y'} {u : Y' ⟶ φ ⋙ Y} (k : (Comparison.of φ β).HasUnivPoints
  u) : IsLerayHirschBasis M.lineBasis (freeAb Y) ↔ IsLerayHirschBasis M'.lineBasis (freeAb Y') :=
  Comparison.bijective_iff_of_comm_sq (lerayHirsch_naturality _ (.comp ..) (r' := .comp ..) fun _
  _ ↦ by erw [map_comp_assoc, lineBasis_naturality, map_homClass, map_homClass]; rfl)
  (mapRange_bijective _ _ k.isBijective.bijective_totalH) k.on_elements.isBijective.bijective_totalH

protected lemma onElements (h : M.HasLineFormula) {X} : M.onElements (X := X).HasLineFormula :=
  lerayHirsch_bijective_of_repr
  (hasUnivPoints_reprBy_elements · |> bijective_iff_of_hasUnivPoints _ |>.1 (h _))

/-- Integration over the projective line: given the projective line formula for M, the map
sending a class a + ηb over the points of P¹ to b. -/
def integrate : TotalH (elementsProj (projLineAlong g) ⋙ S) (elementsProj _ ⋙ M.F) →+ TotalH S
  M.F := (applyAddHom false).comp (LinearEquiv.ofBijective _ (h S)).symm.toAddMonoidHom

lemma integrate_naturality (k : M'.HasLineFormula) {T} {f f' : _ →+ _} (e : ∀ w,
  lerayHirsch M'.lineBasis T (w.mapRange f f.map_zero) = f' (lerayHirsch M.lineBasis S w)) : ∀ x,
  f (h.integrate x) = k.integrate (f' x) := (h S).2.forall.2 (e · ▸ by simp [integrate])

lemma integrate_mul_cupClass y ξ :
  h.integrate (S := S) (comp (.map _ y) (.of _ 2 M.cupClass + .map (restrictAlong _) ξ)) = y := by
  erw [map_add, ← map_comp, ← lerayHirsch_single M.lineBasis false,
    ← (lerayHirsch_single M.lineBasis true _).trans comp_id]
  simp [integrate]

end TorsionCoeff.HasLineFormula

/-- A theory along g with morphisms b_i to its coefficient from the locally constant ℤ/ℓ-valued
functions, such that it and `Theory.locallyConstant` satisfy the projective line formula. -/
structure ComparedTheory (g : C ⥤ TestOver A) extends Theory g where
  I : Type
  b : I → H (restrictAlong g Theory.locallyConstant.F) F 0
  line_formula : toTorsionCoeff.HasLineFormula
  line_formula_const : Theory.locallyConstant (A := A).HasLineFormula

variable (A) in
/-- A functor g from some category to tests over A, a theory along g satisfying the projective
line formula, and d compatible points of P¹ over the rings g(c). -/
structure LineStage d where
  {C : _} [category : Category C] {g : C ⥤ TestOver A}
  Θ : Theory g
  line_formula : Θ.HasLineFormula
  points : (ringOf g ⋙ projLinePow (Fin d)).sections

attribute [instance] LineStage.category

/-- Operations with d parameters: additive maps from total Ext(N∘g, Θ) to total Ext(N'∘g, Θ),
for every g, theory Θ with the projective line formula and section of (P¹)^d, commuting with
comparisons along functors. -/
structure NaturalOp d (N N' : AbFunctor (TestOver A)) where
  app (t : LineStage A d) : TotalH (t.g ⋙ N) _ →+ TotalH (t.g ⋙ N') t.Θ.F
  naturality : ∀ {C} [Category C] (t : LineStage A d) (φ : C ⥤ _) (Θ : Theory (φ ⋙ t.g)) l b x,
    mapThenComp (restrictAlong φ) b (app t x) =
    app ⟨Θ, l, φ.sectionsPrecomp t.points⟩ (mapThenComp _ b x)

variable {N N' : AbFunctor (TestOver A)} {d ι} [Fintype ι]

/-- The restriction of t to the category of pairs (c, x) with x ∈ P¹(g(c)), with the
tautological point x placed before the d points of t. -/
def LineStage.consTautPoint (t : LineStage A d) : LineStage A (d + 1) :=
  ⟨t.Θ.onElements (X := projLineAlong _), t.line_formula.onElements, (cons ·.2
  _), (funext <| cases ·.2 (congrFun (t.points.2 _)))⟩

/-- Integrating out the first parameter of r: pull back to the points of P¹, apply r with the
tautological point as first parameter, and integrate over the line. -/
def NaturalOp.integrate (r : NaturalOp (d + 1) N N') : NaturalOp d N N' :=
  ⟨fun t ↦ t.line_formula.integrate.comp ((r.app t.consTautPoint).comp _), fun t _ K _ b x ↦
  (t.line_formula.integrate_naturality _ (lerayHirsch_naturality _ _ (lineBasis_naturality b))
  _).trans (congrArg _ ((r.naturality t.consTautPoint (precomp ..) K.onElements ..).trans (congrArg
  _ ((congrArg _ comp_id).symm.trans ((lineBasis_naturality b true x).symm.trans comp_id)))))⟩

/-- If g: I → P is a homomorphism of additive groups whose kernel is the image of a map f: K →
I, and K and P are finite, then I is finite. -/
lemma finite_of_exact {K I P} [AddGroup I] [AddGroup P] {f : K → I} {g : I →+ P} (h :
  Exact f g) [Finite K] [Finite P] : Finite I :=
  g.finite_iff_finite_ker_range.2 ⟨(Set.toFinite _).subset (h · |>.1), inferInstance⟩

namespace ComparedTheory

variable (D : ComparedTheory g) {m} (I : IdealFamily (ringOf (testOfPoint A (projLinePow (Fin m)))))

/-- For N on tests over A: total Ext(N, L) is finite, L the locally constant ℤ/ℓ-valued
functions, and the b_i identify ⊕_i Ext(N, L) with total Ext(N∘g, F), F the coefficient of
D. -/
def IsGood N := IsLerayHirschBasis D.b N ∧ Finite (TotalH N (locConstAlong (𝟭 _)))

lemma isClosedClass_isGood : IsClosedClass D.IsGood := ⟨fun N e ↦ ⟨isClosedClass_lerayHirsch.1 N
  e, have := H.subsingleton_of_id_eq_zero e; inferInstance⟩, fun X h ⟨k, _⟩ ↦
  (isClosedClass_lerayHirsch.2 X h k).and ⟨fun _ ↦ finite_of_exact (exact_triangle h _).2.2, fun _ ↦
  finite_of_exact (exact_triangle h _).1⟩⟩

lemma isGood_of_shortExact {X} (h : ShortComplex.ShortExact X) : D.IsGood X.X₂ → D.IsGood X.X₃ →
  D.IsGood X.X₁ := fun ⟨a, _⟩ ⟨b, _⟩ ↦ ⟨bijective_lerayHirsch_iff.2 (((lerayHirsch.longExact_hom
  h).rotate.five_lemma (bijective_lerayHirsch_iff.1 a)).1 (bijective_lerayHirsch_iff.1 b) ·.succ),
  finite_of_exact (exact_triangle h _).2.1⟩

lemma isGood_iff_of_isCohomEquiv (α : N ⟶ N') (h : ∀ {C} [Category C] {F} (g : C ⥤ _),
  HasZariskiDescent (ringOf g) F → IsCohomEquiv F
  (g.whiskerLeft α)) : D.IsGood N ↔ D.IsGood N' := have := (h _
    Theory.locallyConstant.zariski_descent).bijective_totalH; ((Comparison.bijective_iff_of_comm_sq
    (lerayHirsch_mapRange_comp _ map_homClass) (mapRange_bijective _ _ this)
    (h _ D.zariski_descent).bijective_totalH).and this.finite_iff).symm

lemma isGood_of_retract [HasFlatValues N] (r : ι → NaturalOp 0 _ N') (ρ : ι → NaturalOp 0 _ N) (h :
  ∀ t x, ∑ i, (ρ i).app t ((r i).app t x) =
  pullbackAlong (t.g.whiskerLeft (abCoker.π (ℓ • 𝟙 N))) x) (k : D.IsGood N') : D.IsGood N :=
  let o : LineStage A 0 := ⟨_, D.line_formula_const, nofun, fun _ ↦ funext nofun⟩
  have t {N M} (r : NaturalOp 0 N M) :=
    lerayHirsch_naturality _ (r.app o) (r.naturality o g _ D.line_formula <| D.b · |>.toTotalH)
  have s : Surjective _ := D.comp_abCoker_surjective (N :=
    g ⋙ N).forall.2 (h ⟨_, D.line_formula, g.sectionsPrecomp o.points⟩ ·
    ▸ (LinearMap.range _).sum_mem fun i _ ↦ (k.1.2 _).imp' _ (t _ · |>.trans <| congrArg _ ·))
  ⟨⟨.of_ker _ ((mapRange_surjective _ _ o.Θ.comp_abCoker_surjective).forall.2 fun w z ↦
    (s.exists.1 (((exact_triangle (shortExact_nsmul_abCoker.2.map_of_exact _) _).2.2 _).1
    ((lerayHirsch_mapRange_comp _ map_homClass _).symm.trans z))).elim fun u e ↦ by
  ext1
  erw [← h o, ← congr(∑ i, (ρ i).app o ($(k.1.1 (((t (r i) _).congr (t _ _)).2 (congrArg _
    ((lerayHirsch_mapRange_comp D.b (map_extClass shortExact_nsmul_abCoker.2) u).trans e)))) _)), h]
  exact ((exact_triangle (shortExact_nsmul_abCoker (N := N).2) _).2.2 _).2 ⟨_, rfl⟩), s⟩,
    (@Pi.finite _ _ _ fun _ ↦ k.2).of_surjective (fun v ↦ ∑ i,
    (ρ i).app o (v i)) (o.Θ.comp_abCoker_surjective.forall.2 (⟨_, h o ·⟩))⟩

/-- Let `ComparedTheory.IsGood` hold for N, β_i be finitely many classes from ℤ[(P¹)^m]/ℤ[sp I] to
N, and T_i natural operations with d parameters q. If Σ T_i(w)∘β_i restricts at each section q'
to w times ∏_j (η(q_j) + η(q'_{σj})), then it holds for ℤ[(P¹)^m]/ℤ[sp I], sp =
`IdealFamily.topPoints`. -/
lemma isGood_of_integrate_params (β : ι → _) (k : D.IsGood N) (σ : _ → _) (T : ι → NaturalOp d _ N)
  (h : ∀ t q' w, pullbackAlong (I.atSection q') (∑ i, mapThenComp (restrictAlong t.g)
  ((T i).app t w) (β i)) = pullbackAlong (I.atSection _) (foldr d (fun j ↦ comp.flip (t.Θ.etaAt
  (freeAbSectionMap (projLinePow.component t.points j) + freeAbSectionMap (projLinePow.component q'
  (σ j)))).toTotalH) (pullbackAlong (t.g.whiskerLeft (abCoker.π (ℓ • 𝟙 _)))
  w))) : D.IsGood (relFreeAb I.topPoints) := by
  induction' d with d ih
  · exact D.isGood_of_retract T (fun i ↦
      ⟨_, by intros; apply mapThenComp_comp (map_restrictAlong_restrictAlong ..)⟩) (fun t x ↦
      (isBijective_relFreeAb_taut (I.topPoints.whisker t.g)).bijective_totalH.1 (((congrArg _
      ((map_sum ..).trans congr(∑ i, $((mapThenComp_comp (map_restrictAlong_restrictAlong t.g _ (β
     i))).trans (congrArg _ ((T i).naturality _ _ (.onElements _) ..)))))).congr
      (congrArg _ (mapThenComp_comp map_homClass))).2
     (h ⟨t.Θ.onElements, t.line_formula.onElements, _⟩ ⟨_, (·.2)⟩ _))) k
  refine ih (σ ·.succ) (T · |>.integrate) fun t r w ↦
    .trans ?_ (t.line_formula.integrate_mul_cupClass _
    (t.Θ.etaAt (freeAbSectionMap (projLinePow.component r (σ 0)))).toTotalH)
  erw [congr(∑ i, $(t.line_formula.integrate_naturality (φ := 𝟭 _) _
    (lerayHirsch_mapRange_comp _ rfl) _)), ← map_sum, t.line_formula.integrate_naturality (φ := 𝟭 _)
    _ (lerayHirsch_mapRange_comp _ rfl)]
  simp only [map_comp_assoc, map_restrictAlong_restrictAlong, map_homClass,
    TorsionCoeff.map_etaAt_onElements, foldr_succ, foldr_eq_finRange_foldr] at *
  conv_rhs => erw [← map_add, ← map_add, ← List.foldr_hom (TotalH.map _) (g₂ := fun _ ↦ comp.flip _)
    fun _ _ ↦ by erw [map_comp, TorsionCoeff.map_etaAt_onElements]; rfl, map_homClass_comp]
  exact congrArg _ (h t.consTautPoint ((elementsProj _).sectionsPrecomp r) _)

/-- Let I be a compatible family of ideals on points of (P¹)^m and U the locus where I is the unit
ideal. If some Leray–Hirsch map from N to `I.zerosCoeff` is surjective at ℤ[(P¹)^m]/ℤ[U], then
`ComparedTheory.IsGood` for D passes from N to ℤ[(P¹)^m]/ℤ[U].

Known result: Comparison of cohomology theories by duality: a diagonal kernel on products of P¹. -/
lemma isGood_topPoints_of_surjective {J d θ} (k : Surjective (@lerayHirsch _ _ _ _
  (restrictAlong (elementsProj _)) _ N (I.zerosCoeff (locConstAlong (elementsProj _))) J d θ
  (relFreeAb I.topPoints))) (a : D.IsGood N) :
  D.IsGood (relFreeAb I.topPoints) := let X := ringOf (𝟭 (TestOver A)) ⋙ projLinePow (Fin m)
  (((isBijective_relFreeAb_taut (I.topPoints.whisker (elementsProj X))).bijective_totalH.2.comp
    k).exists.1 (I.exists_move_kernel ((Theory.locallyConstant.onElements (X := X).onZeros
    I).onElements (X := _ ⋙ X)) (fun a m M ↦ (TestOver.exists_quotient _ m).elim fun _ ⟨π, k⟩ ↦
    ⟨.mk (obj := ⟨X.map π a.obj.val⟩) (X.map π a.val), ⟨⟨π, rfl⟩, rfl⟩, M.isPrime.radical ▸ k.1⟩)
      (fun r ↦ ⟨_, (funext
    fun j ↦ (r j).2 ·)⟩) (by aesop) (projLinePow.component ⟨_, (·.hom.map_val)⟩)
      (projLinePow.component ⟨_,
    (·.2)⟩) (pullbackAlong ((elementsProj _).whiskerLeft (abCoker.π _)) (.homClass ((elementsProj
    _).whiskerLeft I.constToZeros))))).elim fun β h ↦ D.isGood_of_integrate_params I (β.1.restrict
    β) a id (fun i ↦ ⟨fun t ↦ (comp _).comp (I.extendToZeros t.Θ t.points), fun t φ K _ b _ ↦ by
    apply (mapThenComp_comp (map_restrictAlong_restrictAlong _ φ (θ i).toTotalH)).trans (congrArg
      _ ((I.zerosEquiv K (φ.sectionsPrecomp t.points)).eq_symm_apply.2
      (((mapThenComp_comp map_homClass).congr (mapThenComp_comp map_homClass)).1
      congr(mapThenComp _ b $((I.zerosEquiv ..).1.4 _))) :))⟩) fun t q' w ↦ .trans (congrArg _ (by
    simp_rw [show lerayHirsch θ _ β = _ from (β.1.sum_coe_sort _).symm, map_sum,
      AddMonoidHom.finsetSum_apply]
    congr! 1
    exact (mapThenComp_comp (map_restrictAlong_restrictAlong (elementsProj X) (sectionLift _
      t.points) (β _))).symm)) ((comp_assoc_of_eq (map_homClass_comp.trans (congrArg _ ((congrArg
    _ comp_id).trans (map_restrictAlong_restrictAlong ..)))).symm _).trans (h _ (sectionLift
    (sectionLift _ t.points) q') _ (I.extendToZeros _ _ w) _ ((mapThenComp_comp map_homClass).trans
    ((congrArg _ (congr(comp $map_homClass _).trans ((I.zerosEquiv ..).1.4 _))).trans
    ((homClass_comp_homClass_comp ..).trans (by symm; apply homClass_comp_homClass_comp))))))
