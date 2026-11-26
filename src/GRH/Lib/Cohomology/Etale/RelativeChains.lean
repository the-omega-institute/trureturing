import GRH.Lib.Cohomology.Hodge.CupProduct
import GRH.Lib.Cohomology.Etale.Relations
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Relative cohomology of pairs of functors; locally zero sections, excision, transfer. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor

open CategoryTheory ShortComplex Function MonoidalCategory AddCommGrpCat QuotientAddGroup
  AddMonoidHom FreeAbelianGroup Fintype


variable {C} [Category C] {V V' V'' : C ⥤ Type 1} {F M N : AbFunctor C} (U : Subfunctor V)
  {U' : Subfunctor V'} {U'' : Subfunctor V''} {α : M ⟶ N}

lemma relFreeAb.shortExact : ∃ w, ShortExact ⟨freeAb.map U.ι, π U, w⟩ := by
  delta π relFreeAb freeAb; exact ⟨_, ⟨(exact_of_app fun _ ↦ (eq_zero_iff ·)).2⟩⟩

lemma relFreeAb.isCohomEquiv_iff_subsingleton : IsCohomEquiv F (freeAb.map U.ι) ↔ ∀ n,
  Subsingleton (H (relFreeAb U) F n) := _root_.isCohomEquiv_iff_subsingleton (shortExact U).2

variable {U} (v u) (h : U'' ≤ U'.preimage v) (h' : U' ≤ U.preimage u)

lemma relFreeAb.mk_eq_zero {A x} : x ∈ U A → mk U x = 0 := ((eq_zero_iff _).2 ⟨of ⟨x, ·⟩, rfl⟩)

instance : HasFlatValues (freeAb V) := ⟨fun _ ↦ .of_linearEquiv (basis _).1⟩

lemma relFreeAb.mem_of_mk_mem {A} (S : AddSubgroup (relFreeAb U A)) (h : ∀ y, mk U y ∈ S) :
    ∀ s, s ∈ S := Quot.ind (·.induction_on S.zero_mem h (fun _ ↦ neg_mem) fun _ _ ↦ add_mem)

instance : HasFlatValues (relFreeAb U) := ⟨fun _ ↦ (((map Subtype.val
  ).toIntLinearMap.exact_map_mkQ_range.split_tfae'.out 2 1 rfl rfl).1 ⟨mk_surjective, (lift (extend
  (↑) of 0)).toIntLinearMap, (basis _).ext (by simp [basis])⟩).2.elim (.of_retract · _)⟩

/-- For set-valued functors X, Y, the map ℤ[X × Y] → ℤ[X] ⊗ ℤ[Y] sending [(x, y)] to [x] ⊗ [y]. -/
def freeAb.prod X Y : freeAb (X ⊗ Y : C ⥤ _) ⟶ abTensor (freeAb X) (freeAb Y) :=
  desc (fun _ x ↦ of x.1 ⊗ₜ of x.2) (by tauto)

instance : IsIso (freeAb.prod V V') := (isoOfAppBijective _ fun _ ↦ congr(Bijective $(lift_ext
  ((basis _).1.trans ((basis _).tensorProduct (basis _)).1.symm).toAddMonoidHom _
  (by aesop (add simp basis)))).mp (LinearEquiv.bijective _)).isIso_hom

/-- Let u: V' → V, φ: ℤ[V'] → N and S ⊂ N(A) a subgroup containing φ[x] − φ[y] when u(x) = u(y)
and φ[x] when u(x) ∈ U(A). Then φ maps the kernel of ℤ[V'(A)] → ℤ[V(A)]/ℤ[U(A)] into S. -/
lemma relFreeAb.mem_of_map_eq_zero (φ : freeAb V' ⟶ N) {A} (S : AddSubgroup _) (h : ∀ x y, u A x =
  u A y → φ A (of x) - φ A (of y) ∈ S) (k : ∀ x, u A x ∈ U A → φ A (of x) ∈ S) t (e :
  (freeAb.map u ≫ π U) A t = 0) : φ A t ∈ S :=
  (eq_zero_iff _).1 ((lift_unique _ ((mk' S).comp _) (congrFun (FactorsThrough.extend_comp (const
  _ 0) (eq_iff_sub_mem.2 ∘ h · ·)).symm)).trans ((lift_comp ..).trans ((range_le_ker_iff ..).2
  (lift_ext _ _ (lift_apply_of _ ·.1 |>.trans (by simp [extend]; grind))) ((eq_zero_iff _).1 e))))

/-- The zero section of N: the subfunctor c ↦ {0} of the set-valued functor underlying N. -/
def zeroSection N : @Subfunctor C _ (N ⋙ forget Ab) :=
  ⟨fun _ ↦ {0}, fun _ ↦ OrderBot.bot_le (ker _)⟩

/-- The subgroup of locally zero elements of N(A): the s such that the maps A → B killing s form
a subfunctor of h_A that is dense for F. -/
def locallyZero (F N : AbFunctor C) A : AddSubgroup (N A) :=
  .ofSub {s | IsCohomDense F ((zeroSection N).preimage (pointMap s))} ⟨0, .of_top_le fun _ _ _ ↦
  (ker _).zero_mem⟩ fun _ h _ k ↦ (h.inf k).mono fun _ _ ↦ ((ker _).add_mem ·.1 (by aesop))

/-- If every section of N is locally zero for F (`locallyZero`), then Ext^n(N, F) = 0 for all n. -/
lemma cohomology_eq_zero_of_locallyZero {N} (h : ∀ A s, s ∈ locallyZero F N A) n (x : H N F n) :
  x = 0 := (LongExactSeq.contravariant (@kerComplex_shortExact _ _ (relFreeAb (zeroSection N)) _
  (abCoker.desc (N.whiskerLeft adj.counit) (freeAb.hom_ext fun _ ↦ ((add_zero _).trans
  ·.2))) fun _ ↦ (⟨⟦of ·⟧, add_zero _⟩)) F).f_injective_of_g_surjective (fun _ _ ↦
  (cohomology_eq_zero_of_locallyZero (fun _ _ ↦ by exact (relFreeAb.mem_of_mk_mem (locallyZero ..)
  (h _ · |>.mono fun _ _ ↦ (relFreeAb.mk_eq_zero ·)) _).mono fun _ _ ↦
  (Subtype.ext ·)) _ · ▸ ⟨0, map_zero _⟩)) (((relFreeAb.isCohomEquiv_iff_subsingleton
  (zeroSection N)).1 (IsCohomDense.isCohomEquiv (h · · |>.isCohomEquiv)) n).1 ..)

/-- If every section of the kernel and of the cokernel of α: M → N is killed by a sieve that is
dense for F (`locallyZero`), then α induces bijections on all Ext^n(−, F). -/
lemma LocalIso.isCohomEquiv (h : (∀ c s, α c s = 0 → s ∈ locallyZero F M c) ∧ ∀ c t,
  abCoker.π α c t ∈ locallyZero F _ c) : IsCohomEquiv F α := (isCohomEquiv_quotient_of_acyclic
  (@kerComplex_shortExact _ _ _ (kerComplex (abCoker.π α)).X₁ ⟨(ofHom <| α · |>.1.codRestrict
  _ ((eq_zero_iff _).2 ⟨·, rfl⟩)), fun _ _ f ↦ ext (congr(⟨$(α.2 f) ·, _⟩))⟩ fun
  _ y ↦ ((eq_zero_iff _).1 y.2).imp fun _ ↦ Subtype.ext) (cohomology_eq_zero_of_locallyZero fun _
  s ↦ (h.1 _ _ congr($(s.2).1)).mono fun _ _ ↦ (Subtype.ext ·))).comp_iff.2
  ((isCohomEquiv_iff_subsingleton (kerComplex_shortExact fun _ ↦ mk_surjective)).2
  (subsingleton_of_forall_eq 0 ∘' cohomology_eq_zero_of_locallyZero (Quot.ind ∘' h.2)))

/-- Transfer. If p'f_i = p for finitely many f_i, then ℤ[p] = lm, ∑ ℤ[f_i] = νm, ℤ[p']ν = |ι|·l
for some m, l, ν; l is an equivalence when the image of p, and the pairs in V' ×_V V' whose
tuples (f_i w) agree up to order, are dense. -/
lemma exists_transfer_map {ι} [Fintype ι] {f : ι → (V' ⟶ V'')} {p : _ ⟶ V} {p'} (h : ∀ i, f i ≫ p' =
  p) : let P : Subfunctor (cech p 1) := ⟨({x | ∃ e : ι ≃ ι, ∀ i, f i · (x.1 1) = f (e i) _ (x.1
  0)}), by delta cech; aesop⟩; ∃ Q m l ν, m ≫ l = freeAb.map p ∧ m ≫ ν = ∑ i, freeAb.map (f i) ∧
    ν ≫ freeAb.map p' = card ι • l ∧ ∀ F, IsCohomDense F (.range p) → IsCohomDense F P →
    IsCohomEquiv F (N' := Q) l := by
  intro P
  exact let d j := freeAb.map (P.ι ≫ cech.proj p 1 j); ⟨_, abCoker.π (d 0 - d 1),
      abCoker.desc (freeAb.map p) (freeAb.hom_ext fun _ ↦ (sub_eq_zero.2 congr(of $(·.1.2 ..)))),
      abCoker.desc _ (freeAb.hom_ext fun _ ⟨_, e, h⟩ ↦ (sub_mem_ker_iff _).2
      (sum_app_apply.trans (sum_app_apply.trans (sum_equiv e _ _ (congrArg of ∘' h))).symm)),
  rfl, rfl, (cancel_epi (abCoker.π _)).1 ((Preadditive.sum_comp _ _ (freeAb.map p')).trans (by
  simp [← freeAb.map_comp, h]; rfl)), fun _ k o ↦
    LocalIso.isCohomEquiv ⟨fun _ ↦ Quot.ind (relFreeAb.mem_of_map_eq_zero (U := ⊥) p (abCoker.π _)
  (locallyZero ..) (fun x y _ ↦ o.of_preimage_le (pointMap ⟨![x, y], by simp_all⟩) fun _ _ ↦
      ((eq_zero_iff _).2 ⟨of ⟨_, ·⟩, rfl⟩)) (by simp) · <| congrArg _ ·), fun _ ↦
      (·.induction_on (zero_mem _) (fun _ ↦ k.of_preimage_le (pointMap _)
  fun _ _ ⟨x, e⟩ ↦ (eq_zero_iff _).2 ⟨⟦of x⟧, congr(of $e)⟩) (fun _ ↦ neg_mem) fun _ _ ↦ add_mem)⟩⟩

namespace relFreeAb

/-- For u:V'→V carrying U' into U, the induced morphism Z[V']/Z[U']→Z[V]/Z[U]. -/
def map : relFreeAb U' ⟶ relFreeAb U :=
  abCoker.desc (freeAb.map u ≫ π U) (freeAb.hom_ext (mk_eq_zero (U := U) <| h' · ·.2))

lemma π_map : π _ ≫ map u h' = freeAb.map u ≫ π U := rfl

@[simp] lemma map_comp : map v h ≫ map u h' = map (v ≫ u) (by tauto) := hom_ext

/-- For a monomorphism u: V' → V and a subfunctor U ⊂ V, the natural maps form a short exact
sequence 0 → ℤ[V']/ℤ[u⁻¹U] → ℤ[V]/ℤ[U] → ℤ[V]/ℤ[u(V') ∪ U] → 0 of functors to abelian
groups. -/
lemma shortExact_triple U [Mono u] : ∃ w, ShortExact ⟨map u le_rfl,
  map (𝟙 V) (U := .range u ⊔ U) le_sup_right, w⟩ := shortExact_of_app (fun A ↦ .of_ker _ (Quot.ind
  (mem_of_map_eq_zero u _ ⊥ (by simp [(injective_of_mono (u A)).eq_iff]) fun _ ↦ (mk_eq_zero ·))))
  (fun _ ↦ exact_of_comp_of_mem_range (ext (mem_of_mk_mem (ker _) (mk_eq_zero <| .inl ⟨·, rfl⟩)))
  (Quot.ind (mem_of_map_eq_zero _ (π U) _ (by bound) fun _ ↦ Or.rec (.imp' (mk _) (by bound)) (⟨0,
  mk_eq_zero · |>.symm⟩)))) fun _ ↦ mem_of_mk_mem (range _) (⟨⟦of ·⟧, rfl⟩)

lemma isCohomEquiv_of_le {U' U} (h : U' ≤ U) (h' : IsCohomDense F (U'.preimage U.ι)) :
  IsCohomEquiv F (map (𝟙 V) h) := by
  convert isCohomEquiv_quotient_of_acyclic (shortExact_triple ..).2
    ((isCohomEquiv_iff_subsingleton _).1 h'.isCohomEquiv · |>.1 · 0) <;> congr <;> simp_all

/-- Excision: if u: V' → V is a monomorphism and u(V') ∪ U is dense in V for the coefficient F,
then ℤ[V']/ℤ[u⁻¹U] → ℤ[V]/ℤ[U] induces bijections on Ext^n(·, F) for all n. -/
lemma excision (h : IsCohomDense F (.range u ⊔ U)) [m : Mono u] (e : U' = U.preimage u) :
    IsCohomEquiv F (map u e.le) := by grind [_root_.isCohomEquiv_iff_subsingleton
  (shortExact_triple ..).2, isCohomEquiv_iff_subsingleton, h.isCohomEquiv]
