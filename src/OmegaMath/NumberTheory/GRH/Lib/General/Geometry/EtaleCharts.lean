import OmegaMath.NumberTheory.GRH.Lib.Cohomology.Etale.GluingWithSupports
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic geometry (textbook or folklore).

This file: Charts with étale coordinates on functors: lifting criterion, shrinking, products,
intersections, atlases. -/

noncomputable section


open CategoryTheory MonoidalCategory CartesianMonoidalCategory Algebra TensorProduct EtaleChart
  CommAlgCat MvPolynomial Ideal IsLocalization.Away KaehlerDifferential Set Functor Fin Quotient
  AlgHom FormallyUnramified
variable {k} [CommRing k] {X Y : CommAlg k ⥤ Type 1} {A B R : CommAlg k} {d n} (x : Fin d → R) (a :
  EtaleChart d X) (b : EtaleChart n Y) (u : Y ⟶ X) [Mono u]

instance [IsSepFunctor X] [IsSepFunctor Y] : IsSepFunctor (X ⊗ Y) := ⟨fun _ _ _ ↦ ⟨_, fun _ _ ↦ by
  erw [Prod.ext_iff, sup_le_iff]; repeat erw [(IsSepFunctor.exists_ideal ..).choose_spec]⟩⟩

/-- The localisation map A → A[1/g] of k-algebras. -/
abbrev CommAlg.toAway (g : A) := ofHom (IsScalarTower.toAlgHom k A (Localization.Away g))

lemma CommAlg.exists_toAway_comp_iff g (φ : A ⟶ B) : (∃ χ, toAway g ≫ χ = φ) ↔ IsUnit (φ g) :=
  ⟨fun ⟨χ, e⟩ ↦ e ▸ (algebraMap_isUnit g).map χ.1, (⟨ofHom <| liftAlgHom _ ·, by aesop⟩)⟩

lemma EtaleChart.point_mem_locus : a.point ∈ a.locus _ := ⟨_, X.map_id_apply ..⟩

/-- Let a be a chart of a functor X on algebras over a commutative ring k. A subfunctor V of X that
is contained in the image of a and open in that image is open in X. -/
lemma EtaleChart.isOpenSub_of_le_locus {V} (h : V ≤ a.locus) (o : IsOpenSub (V.preimage
  a.locus.ι)) : IsOpenSub V := le_antisymm (a := fieldLocus V.1) (o.fieldLocus_le · (a :=
  ⟨·, a.isOpenSub.fieldLocus_le _ (by tauto)⟩) ·) (V.rec (by tauto)) ▸ isOpenSub_fieldLocus fun
  A x ↦ ⟨span {f | ∀ B ψ, IsUnit (ψ f) → X.map ψ x ∈ V B}, fun _ φ k ↦ let := k.toField
  by simpa [span_le, not_subset] using
    ⟨fun e ↦ have ⟨f, H, E⟩ := a.isOpenSub.exists_basicOpen φ x k (h _ e)
    ((A.exists_toAway_comp_iff ..).2 H.isUnit).rec fun | χ, rfl => (o.exists_basicOpen χ ⟨_, E _ (A.toAway f) (algebraMap_isUnit _)⟩
                 k (by aesop) |>.imp' ((f * ·.1) ∘ sec f) (by simp [← A.exists_toAway_comp_iff f, ← sec_spec]; aesop)), by aesop⟩⟩

/-- The ring homomorphism k[X_i] → R sending X_i to x_i. -/
abbrev polyEval := (aeval (R := k) x).1

/-- The ring of a chart a as an algebra over the polynomial ring k[X_1, …, X_d], with X_i sent
to the i-th coordinate of a. -/
abbrev EtaleChart.polyAlgebra := (polyEval a.coordinate).toAlgebra

attribute [local instance] EtaleChart.polyAlgebra

instance : Smooth k a.R := @.comp k _ _ _ _ _ _ _ _ _ {} a.etale.instSmooth

variable {x} [IsNoetherianRing k]

/-- Infinitesimal criterion: for k Noetherian, R of finite type and finitely many x_i ∈ R,
k[X_i] → R, X_i ↦ x_i, is étale iff each ζ: R → A lifts uniquely along square-zero
extensions B → A of k-algebras once lifts of the ζ(x_i) are prescribed. -/
lemma etale_polyEval_iff [FiniteType k R] : (polyEval x).Etale ↔ ∀ ⦃A B⦄ (π : B ⟶ A),
  IsSquareZero π → ∀ ζ (b : _ → B),
  (∀ i, π (b i) = ζ (x i)) → ∃! s, s ≫ π = ζ ∧ ∀ i, s (x i) = b i := have E := aeval_X x
  ⟨fun v A B π ⟨l, h⟩ ζ b hb ↦ by
  algebraize [polyEval x, polyEval b, polyEval (π ∘ b)]
  have e := FormallySmooth.liftOfSurjective_apply ⟨_, (funext hb ▸ comp_aeval_apply _ ζ.1 :)⟩
    ⟨_, comp_aeval_apply _ _⟩ l ⟨2, h⟩
  exact ⟨ofHom (.restrictScalars ..), ⟨hom_ext (ext e), (by erw [← E ·, AlgHom.commutes, aeval_X])⟩,
    fun t ⟨p, q⟩ ↦ congr(ofHom ⟨$(ext' _ ⟨2, h⟩ ⟨_, (funext q ▸ comp_aeval_apply _ _ :)⟩ _
    (e · ▸ congr($p _))), _⟩)⟩, fun h ↦ let := (polyEval x).toAlgebra
    ⟨.iff_comp_bijective.2 fun _ _ j I i ↦ .of_existsUnique _ fun ζ ↦ by
  algebraize [j.2.comp C]
  exact (h (ofHom (mkₐ ..)) ⟨exists_rep, I.mk_ker ▸ i⟩ (ofHom (.restrictScalars ..)) _
    (E · ▸ (ζ.2 _).symm)).elim fun s ⟨c, _⟩ H ↦ ⟨⟨_, AlgHom.congr_fun (by aesop : s.1.comp (aeval x)
    = algHom ..)⟩, congr(⟨$c.1, _⟩), fun t _ ↦ congr(⟨$(H (ofHom (.restrictScalars ..)) ⟨by
    bound, (E · ▸ t.2 _)⟩).1, _⟩)⟩, .of_finiteType.1 (.of_restrictScalars_finiteType k ..)⟩⟩

lemma EtaleChart.lift_unique {π : B ⟶ A} (h : IsSquareZero π) {s t} (e : s ≫ π = t ≫ π) (H : ∀ i,
  s (a.coordinate i) = t (a.coordinate i)) :
  s = t := (etale_polyEval_iff.1 a.etale _ h _ _ (by simp)).unique ⟨e, H⟩ (by simp)

/-- For a chart a and φ from its ring to a finite-type algebra R, the chart on R with
transported point and coordinates, provided Spec R embeds as an open subfunctor. -/
def EtaleChart.restrict [FiniteType k R] {φ y} (e : X.map φ a.point = y) i h :=
  mk R y (φ ∘ _) (etale_polyEval_iff.2
  fun _ _ _ S _ _ l ↦ have ⟨s, hs, H⟩ := etale_polyEval_iff.1 a.etale _ S (_ ≫ _) _ l
  by obtain ⟨⟨⟩, ⟨t⟩, ht⟩ := e,
       h.mem_of_isSquareZero _ S _ ⟨_, e ▸ X.map_comp_apply .. ▸ hs.1 ▸ map_comp_apply ..⟩
     cases a.eq_comp_of_map_point_eq _ ht.symm
     use t; simp_rw [← (i _).eq_iff, ← map_comp_apply, (injective ..).eq_iff]; bound) i h

/-- For a chart a of X and an element g of its ring R, the chart on R[1/g] with the images of
the point and coordinates of a. -/
def EtaleChart.away g := a.restrict (φ := CommAlg.toAway g) rfl (fun _ _ _ e ↦ by
  ext; congrm $(a.eq_comp_of_map_point_eq _ ((map_comp_apply ..).trans e)) _) (a.isOpenSub_of_le_locus
  (fun | _, _, ⟨_, rfl⟩ => a.locus.2 _ ⟨_, rfl⟩) fun | _, ⟨_, _, rfl⟩ => ⟨span {_}, fun _ φ ↦
      ULift.exists.trans (by simpa [← (injective ..).eq_iff] using! CommAlg.exists_toAway_comp_iff g (_ ≫ φ))⟩)

lemma EtaleChart.mem_locus_away g φ : X.map φ a.point ∈ (a.away g).locus B ↔ IsUnit (φ g) := by
  simp [← CommAlg.exists_toAway_comp_iff, ← (injective ..).eq_iff]; bound

/-- Charts can be shrunk: if U ⊂ X is open, charts of dimension d cover the points of X in
fields, and x ∈ U(A) with A a field, then x lies in a chart of dimension d contained in U. -/
lemma IsOpenSub.exists_chart_le {U x} (o : IsOpenSub U) (l : IsField A) [IsChartCovered d X] (m :
  x ∈ U A) : ∃ a : EtaleChart d X, x ∈ a.locus A ∧ a.point ∈ U _ := (IsChartCovered.exists_chart _ l
  x).rec fun _ ⟨_, e⟩ ↦ (o.exists_basicOpen _ _ l (e ▸ m)).imp' _ fun f ⟨h, H⟩ ↦ ⟨e ▸
  (mem_locus_away ..).2 ((l.3 h).rec .of_mul_eq_one), H _ (CommAlg.toAway f) (algebraMap_isUnit f)⟩

/-- For commutative k-algebras A and B, the k-algebra map A → A ⊗_k B, a ↦ a ⊗ 1, as a morphism
in `CommAlg` k. -/
abbrev tensorInl : A ⟶ of k (A ⊗[k] B) := ofHom includeLeft

/-- For commutative k-algebras A and B, the k-algebra map B → A ⊗_k B, b ↦ 1 ⊗ b, as a morphism
in `CommAlg` k. -/
abbrev tensorInr : B ⟶ of k (A ⊗[k] B) := ofHom includeRight

omit [IsNoetherianRing k] in
lemma existsUnique_tensor_desc (φ : A ⟶ R) (ψ : B ⟶ R) : ∃! χ, tensorInl ≫ χ = φ ∧ tensorInr ≫ χ =
  ψ := ⟨ofHom (productMap φ.1 ψ.1), by aesop⟩

omit [IsNoetherianRing k] in
lemma range_pointMap_prod : .range (pointMap (X.map tensorInl a.point, Y.map tensorInr b.point)) =
  a.locus.preimage (fst ..) ⊓ b.locus.preimage (snd ..) :=
  le_antisymm (fun | _, _, ⟨_, rfl⟩ => ⟨a.locus.2 _ ⟨_, rfl⟩, b.locus.2 _ ⟨_, rfl⟩⟩)
  (by rintro _ ⟨⟩ ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩; exact (existsUnique_tensor_desc ‹_› ‹_›).imp' .up (by aesop))

/-- For charts a of X and b of Y, the chart of X×Y on the tensor product of their rings, with
coordinates x_i⊗1 and 1⊗y_j. -/
def EtaleChart.prod := mk _ _
  (append (a.coordinate · ⊗ₜ 1) (1 ⊗ₜ b.coordinate ·)) (have := Smooth.comp k a.R (a.R ⊗[k] b.R)
  etale_polyEval_iff.2 fun _ _ π e ζ _ h ↦ by
    simp_all [forall_fin_add]
    obtain ⟨⟨s, _⟩, t, _⟩ := etale_polyEval_iff.1 a.etale π e (tensorInl ≫ ζ) _ h.1,
      etale_polyEval_iff.1 b.etale π e (tensorInr ≫ ζ) _ h.2
    obtain ⟨χ, ⟨⟨⟩, ⟨⟩⟩, _⟩ := existsUnique_tensor_desc s t
    use χ, ⟨(existsUnique_tensor_desc ..).unique ?_ ⟨rfl, rfl⟩, ?_⟩ <;> bound) (fun _ _ _ e ↦
  (existsUnique_tensor_desc ..).unique (by simpa [← (injective ..).eq_iff] using! Prod.mk.inj e)
  ⟨rfl, rfl⟩) (range_pointMap_prod a _ ▸ (a.isOpenSub.preimage _).inf (b.isOpenSub.preimage _))

instance HasAtlas.isChartCovered [h : HasAtlas d X] : IsChartCovered d X :=
  ⟨by choose _ _ _ _ using h.2; tauto⟩

instance IsChartCovered.prod [IsChartCovered d X] [IsChartCovered n Y] :
  IsChartCovered (d + n) (X ⊗ Y) := ⟨fun _ k _ ↦ ⟨.prod .., (range_pointMap_prod ..).ge _
  ⟨(exists_chart _ k _).choose_spec, (exists_chart _ k _).choose_spec⟩⟩⟩

lemma EtaleChart.exists_locus_eq_inf [IsSepFunctor X] (b : EtaleChart n X) : ∃ c : EtaleChart n X,
  c.locus = a.locus ⊓ b.locus := (IsSepFunctor.exists_ideal (a.prod b).R ..).rec fun J
  h ↦ have e {B} χ := ((X ⊗ X).map_comp_apply ..).trans (congr(
    (X ⊗ X).map (Y := B) χ ($((h _ (ofHom (mkₐ k J))).2 mk_ker.ge), _)))
  suffices _ = _ from ⟨b.restrict (map_comp_apply ..) (fun _ _ _ H ↦ hom_ext
    (algHom_ext _ congr($(injective _ _ ((e _).trans ((Prod.ext H H).trans (e _).symm))).1)))
    (this.symm.subst (a.isOpenSub.inf b.isOpenSub)), this⟩
  by ext B x; exact .trans ⟨(·.choose_spec ▸ ⟨_, e _⟩), fun ⟨_, H⟩ ↦ ⟨⟨ofHom (liftₐ J _ ((h ..).1 (H
    ▸ mem_diagonal x)))⟩, X.map_comp_apply .. ▸ congr($H.2)⟩⟩ congr((x,
    x) ∈ $(range_pointMap_prod ..).1 _)

omit [IsNoetherianRing k] in
lemma EtaleChart.nonempty_basis_kaehler :
  Nonempty (Module.Basis (Fin d) a.R Ω[a.R⁄k]) := have := a.etale.1
  ⟨(isBaseChange_of_formallyEtale ..).basis (mvPolynomialBasis ..)⟩

/-- For a chart a with ring R there are finitely many pairs (s_j, t_j) in R such that points p,
q of the chart agree in X exactly when ∑ q(s_j)p(t_j) is a unit and p, q have equal
coordinates. -/
lemma EtaleChart.exists_eq_iff_coordinate_eq : ∃ e, ∀ C (χ : a.R ⊗ a.R ⟶ C),
  X.map χ (a.prod a).point.1 = X.map χ (a.prod a).point.2 ↔
  IsUnit (χ e) ∧ ∀ i, χ (a.coordinate i ⊗ₜ 1 - 1 ⊗ₜ a.coordinate i) = 0 := have := a.etale.toAlgebra
  (elem (MvPolynomial (Fin d) k) _).exists_finset.rec fun T e ↦ ⟨∑ j ∈ T, j.1 ⊗ₜ j.2, fun C χ ↦ by
    have ⟨⟨⟨p, q⟩, _⟩, h⟩ := liftEquiv.surjective χ.hom
    algebraize [polyEval (p ∘ a.coordinate)]; simp [← h, prod, ← map_comp_apply, -Functor.map_comp,
      (injective ..).eq_iff, CommAlgCat.hom_ext_iff]
    use (· ▸ by simpa [lmul_elem] using congr(IsUnit (p (lmul' _ $e)))), fun ⟨u, E⟩ ↦
      ext fun s ↦ u.mul_right_cancel (by simpa [e] using (congr(productMap ⟨_, comp_aeval_apply
      _ _⟩ ⟨_, (funext E ▸ comp_aeval_apply _ q :)⟩ $(one_tmul_mul_elem s))).symm)⟩

omit [IsNoetherianRing k] in
lemma EtaleChart.locus_comap {y} (h : u _ y = a.point) : .range (pointMap y) =
  a.locus.preimage u := by ext; simp [← h, (injective_of_mono _).eq_iff, ← pointMap_comp]

/-- For u: Y → X injective on points and a chart a of X whose point is u(y), the chart of Y with
the same ring and coordinates and the point y. -/
def EtaleChart.comap y h := mk _ y _ a.etale (fun _ _ _ e ↦ a.injective _ (by
  simpa [h] using congr(u _ $e))) (a.locus_comap u h ▸ a.isOpenSub.preimage _)

/-- Let u: Y → X be a monomorphism, with open image, of functors on algebras over a noetherian
ring k. If charts of dimension d cover the field-valued points of X (`IsChartCovered`), the
same holds for Y. -/
lemma IsChartCovered.comap [h : IsChartCovered d X] (o : IsOpenSub (.range u)) :
  IsChartCovered d Y := ⟨fun _ ↦ (o.exists_chart_le · ⟨·, rfl⟩ |>.rec fun a ⟨m, _, h⟩ ↦
  ⟨a.comap _ _ h, (locus_comap _ u h).ge _ m⟩)⟩

/-- V is locally everything in X, and ℤ[V] lies in every closed class (`IsClosedClass`)
containing ℤ[h_R] for all charts Spec R of X whose étale coordinates are units. -/
def IsCharting (V : Subfunctor X) := IsLocallyEverything (forget₂ ..) V ∧ ∀ P, IsClosedClass P →
  (∀ {d} (b : EtaleChart d X), (∀ j,
  IsUnit (b.coordinate j)) → P (freeAb (reprBy b.R))) → P (freeAb V.toFunctor)

/-- If X has an atlas of dimension d, there is a subfunctor V of X satisfying `IsCharting`. -/
lemma HasAtlas.exists_isCharting : HasAtlas d X → ∃ V, @IsCharting k _ X V
  := fun ⟨_, a, ha⟩ ↦ let x i j := (a i.1).coordinate j + ite (j ∈ i.2) 1 0
  let u i := away {a _ with coordinate := x i, etale := etale_polyEval_iff.2 fun _ _ π h _ _ _ ↦ by
                              simpa [x, eq_sub_iff_add_eq] using (etale_polyEval_iff.1
                                (EtaleChart.etale _) π h _ (_ - _) (by aesop))} (∏ j, x i j)
  ⟨_, isLocallyEverything_of_open_cover (Θ := 𝟭 _) (ha · · · |>.rec fun i ⟨⟨φ⟩, l⟩ ↦
    ⟨_, isOpenSub _, l ▸ (mem_locus_away ..).2 (by simp; let := IsField.toField ‹_›; aesop),
    le_iSup (locus ∘ u) (i, φ.hom ∘ (a i).coordinate ⁻¹' {0})⟩), fun _ p h ↦ p.freeAb_iSup (locus ''
    {b | ∃ i, b.locus ≤ (u i).locus}) (fun | _, ⟨b, ⟨_, e⟩, rfl⟩ => ((e _ b.point_mem_locus).rec
    fun ⟨φ⟩ l ↦ ⟨(p.iff_of_isIso (freeAb.map (Subfunctor.toRange _))).1 (h (EtaleChart.restrict _ l
    b.injective b.isOpenSub) (by simpa using! (CommAlg.exists_toAway_comp_iff ..).1 ⟨φ, rfl⟩)),
    fun _ ⟨c, _⟩ ↦ by grind [b.exists_locus_eq_inf c, inf_le_left]⟩)) (⟨_, ⟨·, le_rfl⟩, rfl⟩)⟩
