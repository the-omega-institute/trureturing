import GRH.Lib.Cohomology.Hodge.Kunneth
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols) (known result; see Lib.Cohomology.Hodge.FixedPointFormula).

Part of: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles (known
result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Grothendieck symbols [dT/T]: definition, transformation law, multiplicativity, degree-one
form. -/

noncomputable section


open CategoryTheory Function MonoidalCategory TensorProduct Finset Abelian Ext RingHom TrivSqZeroExt
  Matrix exteriorPower Set Ideal Fin ULift witnessed HodgeTest Comparison H TotalH freeAb
set_option backward.isDefEq.respectTransparency false
variable {k} [Field k] {d V} (f : V ⟶ sqZeroExt ⋙ affineSpace k d)

/-- For f from V to d-tuples in A ⊕ M, the subfunctor of pairs (v, l), l ∈ A^d, with l · f̄(v) =
1, where f̄ is the A-component of f. -/
def jouanolouRel : Subfunctor (V ⊗ .mk (·.baseAlg) (·.1) ⋙ affineSpace k d) :=
  ⟨fun c ↦ {(v, l) | l.1 ⬝ᵥ fst ∘ (f.app c v).1 = 1}, fun φ _ h ↦ congr(_ ⬝ᵥ
  _ ∘ $(f.naturality_apply ..).1).trans (by simpa [dotProduct] using! congr(φ.1 $h))⟩

lemma exists_jouanolouRel_of_unimodular c v (h : v ∈ ((@unimodular k _ d).whisker _).obj c) : ∃ l,
  (v, l) ∈ (jouanolouRel (𝟙 _)).obj c :=
  «exists».2 (mem_span_range_iff_exists_fun.1 ((unimodular.map c.baseProj h).ge ⟨⟩))

variable {R} (ω : freeAb.obj V ⟶ hodgeCoeff) (h : R ≤ jouanolouRel f) {c : HodgeTest k}

instance : Module c.baseAlg (hodgeCoeff.obj c) := module' (M := ExteriorAlgebra ..)

/-- The map (v, l_1, …, l_d) ↦ det(l_1, …, l_d)·ω(v) from the free abelian group on points v
with d witnesses l_i ∈ A^d to ⋀_A M. -/
@[simp] def detCochain := desc (Y := witnessed R d) (fun c t ↦ det (t.1.2 · |>.1) • ω.app c
  (.of t.1.1)) fun _ _ _ _ ↦ congrArg up (.symm ((exteriorMap_smul ..).trans
  (congrArg₂ _ (map_det ..) congr($(ω.naturality_apply ..).1).symm)))

lemma sum_minor_eq_mul_det (t : Matrix _ _ c.baseAlg) f i (h : ∀ j, t j ⬝ᵥ f = 1) :
    ∑ j : Fin d.succ, (-1) ^ (j.1 + i.1) • (t.submatrix j.succAbove i.succAbove).det =
    f i * t.det := by simpa [det_succ_column' _ i, ← dotProduct.eq_1, dotProduct_comm f, h]
    using (open Calc in t.det_updateCol_sum i f)

/-- The map (v, l_1, …, l_d) ↦ det(l_i)·ω(v), on points with d witnesses l_i·f̄(v) = 1, kills
boundaries; this is the induced map on the cokernel of the boundary. -/
def detCocycle := abCoker.desc (α := boundary (jouanolouRel f) d) (detCochain ω) (hom_ext fun c ⟨⟨v,
  l⟩, t⟩ ↦ by simpa [boundary, sum_app_apply, -NatTrans.app_sum, ← smul_assoc,
  sum_smul] using! congr($(sum_minor_eq_mul_det (vecCons
  0 <| l · |>.1) (vecCons 0 _) 0 (by simpa)) • ω.app c (.of v)))

@[simp] lemma pi_comp_detCocycle : abCoker.π _ ≫ detCocycle f ω = detCochain ω := rfl

/-- The natural map from the free abelian group on (A⊕M)^d to ⋀_A M sending a tuple (a_i,m_i) to
m_1∧…∧m_d. -/
def volumeForm : freeAb.obj (sqZeroExt ⋙ affineSpace k d) ⟶ hodgeCoeff := desc (fun _ v ↦
  ⟨(ιMulti _ d (snd ∘ v.1)).1⟩) fun _ _ _ _ ↦ congrArg _ (exteriorMap_iotaMulti ..).symm

/-- The class [dT/T] ∈ Hdg^d(𝔸^d, 𝔸^d ∖ 0) of the cocycle det(l_1, …, l_d)·dT_1 ∧ … ∧ dT_d on
tuples of linear forms with l_j(T) = 1. -/
def symbolClass : HodgeH (_root_.relFreeAb (@unimodular k _ d)) d :=
  cocycleClass exists_jouanolouRel_of_unimodular (detCocycle _ volumeForm)

attribute [-simp] map_smul zsmul_eq_mul

/-- For c = (A, M) and f ∈ (A ⊕ M)^d: α sends the class of each σ: c → C modulo D(v) to that of
σ(f) modulo 𝔸^d∖0. -/
abbrev IsInducedByCoords (v : Fin d → c.baseAlg) (f : Fin d → TrivSqZeroExt c.baseAlg _) (α :
  _root_.relFreeAb (someUnitLocus v) ⟶ _) := ∀ C σ,
  α.app C (relFreeAb.mk _ σ) = relFreeAb.mk (unimodular.whisker _) ⟨sqZeroExt.map σ.1 ∘ f⟩

seal Finset.univ Finset.sum Finset.prod in
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
/-- Transformation law for Grothendieck symbols: let f = (f̄, ω), g = (ḡ, η) be d-tuples in the
square-zero extension, I = (f̄), f̄ = Mḡ, ω ≡ Nη and det N ≡ a·det M mod I, a ∈ k. Then
[ω/f̄] = a[η/ḡ] with supports in V(I). -/
lemma symbolClass_transformation {v : Fin d → c.baseAlg} {f g α β}
  (hα : IsInducedByCoords v f α) (hβ :
  IsInducedByCoords v g β) (hf : fst ∘ f = v) (M N : Matrix (Fin d) _ _) (a : k)
    (hM : v = M *ᵥ fst ∘ g)
  (hN : ∀ i j, (f i).snd j - ∑ l, N i l * (g l).snd j ∈ span (.range v)) (ha : N.det - algebraMap k
  _ a * M.det ∈ span (.range v)) : H.map _ α d symbolClass = a • H.map _ β d symbolClass := by
  let S : ⋀[c.baseAlg]^d _ →+ _ := (cocycleClass (U := someUnitLocus v) (hf ▸ fun _ _ ⟨i, h⟩ ↦
    ⟨⟨Pi.single i _⟩, (single_dotProduct ..).trans h.val_inv_mul⟩)).comp
    (.mk' (detCocycle (pointMap ⟨f⟩) <| ((homReprEquiv ..).trans
    .ulift).symm ·.1) fun _ _ ↦ (cancel_epi (abCoker.π _)).1 (hom_ext (by simp)))
  have T {g a} M (e : v = M *ᵥ fst ∘ g) {α} (h : IsInducedByCoords v g α) :
    a • H.map _ α d symbolClass = S ((algebraMap k _ a * M.det) • ιMulti _ d (snd ∘ g)) := by
    erw [smul_eq_push, ← pull_id_eq_push, ← map_pull_eq_pull_map rfl, H.map_id]
    refine pull_cocycleClass (R' := jouanolouRel (pointMap ⟨f⟩)) exists_jouanolouRel_of_unimodular _
      _ (pointMap _) ⟨fun C ↦ ↾fun x ↦ ⟨x.2.1 ᵥ* M.map x.1.1.1⟩, by intros; ext; congrm ⟨fun _ ↦
      $(.symm (map_vecMul ..))⟩⟩ (fun _ x ↦ (dotProduct_mulVec x.2.1 ..).symm.trans ∘ congr(_ ⬝ᵥ
      $(congr(_ ∘ $(hf.trans e)).trans (funext (map_mulVec _ _ _)))).symm.trans) ?_ h
    simp [volumeForm]; intros; erw [det_mul, ← map_det]
    exact congrArg up (.trans (by simp [exteriorMap_iotaMulti, mul_smul, ← smul_comm a]; rfl)
      congr(_ • $((add_zero _).trans (exteriorMap_smul ..))).symm)
  have K i (r : c.baseAlg) m := @T (update (inr ∘ m) i (1, r • m i)) 1 (updateCol 1 i v)
    (by ext; simp [mulVec, dotProduct, update, apply_ite]) 0 fun _ φ ↦ .symm (relFreeAb.mk_eq_zero
    (projSpace.span_eq_top_of_isUnit i (by simp [isUnit_iff_isUnit_fst, HodgeTest.sqZeroExt])))
  simp [H.map, ← cramer_apply, smul_smul, ↓comp_update, comp_def, mul_comm] at K
  rw [(one_smul ..).symm.trans (T 1 (by simp [hf]) hα), T M hM hβ, ← sub_eq_zero,
    ← map_sub, ← ((Pi.basisFun ..).exteriorPower d).sum_repr (_ - _)]
  simpa [basis_repr_apply, ιMulti_family] using sum_eq_zero fun s _ ↦
    (mem_span_range_iff_exists_fun.1 (show _ ∈ span (range v) by
    simp_rw [← Ideal.Quotient.eq] at *; simp [← ha, ← det_mul, map_det, Matrix.map,
      hN]; rfl)).elim fun t e ↦ congr(S ($e • _)).symm.trans (by simp [sum_smul, ← K])

variable (k d)

lemma symbolClass_one : ∃ ω : _ ⋙ freeAb.obj unimodular.toFunctor ⟶ hodgeCoeff, (∀ c v, ∃ w,
  (v.1.1 0).fst • w = (v.1.1 0).snd ∧ ω.app c (.of v) = ⟨.ι _ w⟩) ∧ @symbolClass k _ 1 =
  (relFreeAb.shortExact (unimodular.whisker _)).2.extClass.comp (.mk₀ ω) rfl :=
  (exists_map_extClass_comp (relFreeAb.shortExact _).2 shortExact_cokerBoundary.2 (detCocycle _
  volumeForm) (.mk₀ (𝟙 _)) _ (fromRel exists_jouanolouRel_of_unimodular) rfl).imp fun _ ↦
  .imp (fun a c ⟨⟨v⟩, u⟩ ↦ (exists_jouanolouRel_of_unimodular _ _ u).elim fun ⟨l⟩ h ↦ ⟨l 0 • _, by
  simpa [dotProduct, smul_smul, mul_comm] using! congr($h • (v 0).2), .symm (a c _ _ ⟨⟦.of ⟨(_, _),
  fun _ ↦ h⟩⟧, by with_unfolding_all congrm .of ⟨⟨_, $(funext nofun)⟩, _⟩, congrArg up (by
  simp [volumeForm]; rfl)⟩)⟩) (by simp_all [symbolClass, cocycleClass, push])

/-- The natural map 𝔸^d × 𝔸^1 → 𝔸^{d+1} appending a last coordinate. -/
@[simp] def affineSpace.snoc : affineSpace k d ⊗ affineSpace k 1 ⟶ affineSpace k d.succ :=
  ⟨fun _ ↦ ↾fun v ↦ ⟨Fin.snoc v.1.1 (v.2.1 0)⟩, by aesop_cat (add simp [affineSpace, comp_snoc])⟩

seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
/-- In characteristic 0: under 𝔸^d × 𝔸^1 → 𝔸^{d+1}, which
respects the complements of the origin, the class [dT/T] of
degree d + 1 pulls back to the external product of the classes [dT/T] of degrees d and 1. -/
lemma symbolClass_succ [CharZero k] : ∃ h, HodgeH.map (relFreeAb.prod ..)
  (_root_.cup exteriorAlg.mulPairing (@symbolClass k _ d) symbolClass (add_comm ..) :) =
  HodgeH.map (relFreeAb.map (affineSpace.snoc ..) h) symbolClass := by
  refine (symbolClass_one k).elim fun ω ⟨hω, e₁⟩ ↦ e₁ ▸ ⟨?h, by
  let G := (@unimodular k _ 1).whisker sqZeroExt
  let f := sqZeroExt.whiskerLeft (affineSpace.snoc k d)
  let Q := jouanolouRel f ⊓ ⟨({(x, l) | x.2 ∈ G.obj · ∨ l.1 (last d) = 0}), fun φ x ↦ .imp (G.map φ
    ·) (by simpa using! congrArg φ.1 ·)⟩
  have T {B : Ab} {c x} {a b : B} (e : x ∉ G.obj c → a = b) : a ⊗ₜ[ℤ] relFreeAb.mk G x =
    b ⊗ₜ relFreeAb.mk _ x := by_cases (by simp [relFreeAb.mk_eq_zero ·]) (e · ▸ rfl)
  refine (map_cocycleClass (R' := Q) (U' := .whisker (_ ⊔ _) _) exists_jouanolouRel_of_unimodular
    (fun c x a ↦ a.elim (exists_jouanolouRel_of_unimodular _ _ · |>.elim fun l a ↦ ⟨⟨snoc _ 0⟩,
    (sum_univ_castSucc _).trans (by simpa [f]), by simp⟩) fun _ ↦ (exists_jouanolouRel_of_unimodular
    _ _ (?h _ a)).imp (by tauto)) (abTensor.flip.obj (_root_.relFreeAb G)) ((-1) ^ d • 𝟙 _)
    (fun m ↦ desc (fun c ⟨⟨⟨v, x⟩, l⟩, t⟩ ↦ (if a : x ∈ G.obj c then 0 else .of ⟨(v,
    (⟨init <| l · |>.1⟩)), fun i ↦ by simpa [f, show (l i).1 _ = 0 from (t i).2.resolve_left a,
    jouanolouRel, dotProduct, sum_univ_castSucc] using! (t i).1⟩) ⊗ₜ relFreeAb.mk G x) fun _ _ φ _ ↦
    T (by have := G.map φ; split_ifs <;> tauto)) (by intros; exact T (by simp [·]; congrm ⟦.of ⟨⟨_,
    $(funext nofun)⟩, _⟩⟧)) (fun _ _ _ ↦ hom_ext fun _ _ ↦ T (by simp [·]; rfl))
    (detCocycle _ volumeForm)).elim fun y H ↦ (congrArg _ (DirectSum.of_injective
    _ ?_).symm).trans ((comp_assoc _ _ _ _ rfl (by simp)).symm.trans (congr($(H.2).comp _ rfl).trans
    ((exists_map_extClass_comp (shortExact_cokerBoundary (R := Q)).2 ((relFreeAb.shortExact
    G).2.map_of_exact (abTensor.obj _)) ((abTensor.obj _).map ω ≫ exteriorAlg.mulPairing) _
    (desc (fun c ⟨⟨⟨v, x⟩, l⟩, _⟩ ↦ ((-1) ^ d • (detCochain (R := ⊤) volumeForm).app c (.of ⟨(v,
    (⟨init <| l · |>.1⟩)), by simp⟩)) ⊗ₜ .of x) fun _ _ _ _ ↦ .symm congr($(((_ : ℤ) • detCochain
    _).naturality_apply ..) ⊗ₜ _).symm) _ (H.1.trans (hom_ext fun _ _ ↦ T (by simp [·])))).elim fun
    z h ↦ .trans (by exact h.2) ((pull_cocycleClass (R' :=
    Q) exists_jouanolouRel_of_unimodular _ (.id _) f {app _ := ↾(·.2)} (fun _ _ ↦
    (·.1)) (fun c ⟨_, t⟩ ↦ h.1 c _ _ ?_) (by tauto)).symm.trans congr($(id_pull _) _ _)))))
  erw [← comp_of, ← of_comp_homClass, ← cup_of, ← comp_of _ (.mk₀ ω), cup_comp_homClass_right,
    TotalH.cup]
  cases neg_one_pow_eq_or ℤ d <;> simpa [*, TotalH.comp_assoc, -Functor.flip_obj_obj, ← comp_of,
    TotalH.homClass, ← homClass_comp] using! congr((-1 :) ^ d • $(comp_assoc_of_eq
    (extClass_sign_comm (abTensor_shortExact (relFreeAb.shortExact G).2) (@symbolClass k _ d)) _))
  conv => enter [1, _, 1, 2, 2]; erw [sum_app_apply]
  simp
  erw [map_sum, sum_congr rfl fun _ _ ↦ map_zsmul ..]
  simp
  rw [show ∑ _, _ = _ by simpa [sum_smul, sum_tmul, pow_add, mul_zsmul]
    using! congr(($(sum_minor_eq_mul_det _ _ (last _) (t · |>.1)) • volumeForm.app c _) ⊗ₜ _)]
  refine if a : _ then (hω c ⟨_, a⟩).elim fun w e ↦ ⟨_ ⊗ₜ .of ⟨_, a⟩, rfl, congrArg up
    ?_⟩ else ⟨0, by
      simpa [det_eq_zero_of_column_eq_zero _ (t · |>.2.resolve_left a)] using map_zero _⟩
  simp [volumeForm, ExteriorAlgebra.ιMulti, ↓List.ofFn_succ', f, smul_smul, ← e.1,
    mul_comm]; erw [e.2]⟩
  rintro _ _ ⟨⟩ <;> apply eq_top_mono (span_mono _) ‹_› <;> simp <;> tauto
