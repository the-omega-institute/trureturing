import GRH.Lib.Cohomology.Etale.BijectiveComparisons
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols) (known result; see Lib.Cohomology.Hodge.FixedPointFormula).

This file: Tensor product of functors, total Ext with Yoneda composition, cup product and
naturality. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor

noncomputable section


open CategoryTheory Abelian Ext TensorProduct Functor DirectSum Function H LongExactSeq
variable {C C'} [Category C] [Category C'] {M N N' F F' G G' : AbFunctor C} {a b e n A} [Category A]
  (Φ Ψ : AbFunctor C ⥤ AbFunctor C') [IsExactFunctor Φ] [IsExactFunctor Ψ] {f :
  N ⟶ F} {R} [Ring R] [CoeffAction R F] {S : ShortComplex (AbFunctor C)} (h : S.ShortExact)

@[ext high] lemma addCommGrp_tensor_hom_ext {A B X : Ab} {f g : .of (A ⊗[ℤ] B) ⟶ X} (h : ∀ a b,
  f (a ⊗ₜ b) =
  g (a ⊗ₜ b)) : f = g := AddCommGrpCat.hom_ext (AddMonoidHom.toIntLinearMap_injective (ext' h))

/-- For homomorphisms f: A → A' and g: B → B' of abelian groups, the homomorphism f ⊗ g: A ⊗ B →
A' ⊗ B' of tensor products over ℤ. -/
abbrev abTensorMap {A B A' B' : Ab} (f : A ⟶ A') (g : B ⟶ B') :=
  AddCommGrpCat.ofHom (map f.hom.toIntLinearMap g.hom.toIntLinearMap).toAddMonoidHom

/-- The pointwise tensor product over ℤ of two functors from C to abelian groups, as a
bifunctor. -/
def abTensor : AbFunctor C ⥤ AbFunctor C ⥤ AbFunctor C :=
  curryObj ⟨fun p ↦ .mk _ fun f ↦ abTensorMap (p.1.map f) (p.2.map f),
  fun f ↦ .mk fun c ↦ abTensorMap (f.1 c) (f.2 c), by intros; ext; rfl, by intros; ext; rfl⟩

lemma abTensor_hom_ext {f g : abTensor F G ⟶ G'} (h : ∀ c a b, f c (a ⊗ₜ b) = g c (a ⊗ₜ b)
    := by tauto) : f = g := NatTrans.ext (funext (addCommGrp_tensor_hom_ext <| h ·))

/-- Every value F(c) of the functor F from C to abelian groups is a flat ℤ-module. -/
class HasFlatValues (F : AbFunctor C) where flat c : Module.Flat ℤ (F c)

instance (φ) [HasFlatValues F] : @HasFlatValues C' _ (φ ⋙ F) := ⟨HasFlatValues.flat ∘' φ⟩

instance : (abTensor F).Additive := ⟨abTensor_hom_ext fun _ _ _ ↦ tmul_add ..⟩

instance : (abTensor.flip F).Additive := ⟨abTensor_hom_ext fun _ _ _ ↦ add_tmul ..⟩

instance [HasFlatValues F] : IsExactFunctor (abTensor F) := (((abTensor F).exact_tfae.out 2 4 :).1
  fun _ e ↦ (exact_of_app (HasFlatValues.flat · |>.lTensor_exact _
  (exact_of_shortComplex_exact (e.map ((evaluation ..) _))))).2).rec fun _ _ ↦ ⟨⟩

instance [HasFlatValues F] : IsExactFunctor (abTensor.flip F) := (((abTensor.flip
  F).exact_tfae.out 2 4 :).1 fun _ e ↦ (exact_of_app (HasFlatValues.flat · |>.rTensor_exact _
  (exact_of_shortComplex_exact (e.map ((evaluation ..) _))))).2).rec fun _ _ ↦ ⟨⟩

attribute [local simp] mapExactFunctor_mapExactFunctor Comparison.pull H.map H.push
  Ext.comp_assoc

/-- The sum x+y of two classes x, y in Ext^a(N,F). -/
@[reducible] def H.add (x y : H N F a) := x + y

instance addCommGroupH : AddCommGroup (H N F a) := { Ext.instAddCommGroup with add := .add }

/-- The total Ext group, the direct sum of the Ext^n(N,F) over all n ≥ 0. -/
abbrev TotalH N F := DirectSum ℕ (@H C _ N F)

/-- The biadditive map from total Ext(M,N) and total Ext(N,F) to total Ext(M,F) extending the
Yoneda composition of homogeneous classes. -/
@[irreducible] def TotalH.comp := (@exists_eq (TotalH M N →+ TotalH N F →+ TotalH ..) (toAddMonoid
  fun _ ↦ (toAddMonoid fun _ ↦ ((bilinearComp (h := rfl) ..).compr₂ (of ..)).flip).flip)).choose

@[local simp] lemma TotalH.comp_of x y h :
    comp (of (H M N) a x) (of (H N F) b y) = .of _ n (x.comp y h) := h ▸ by simp [comp]

/-- A class x in Ext^n(N,F), as the element of the total group ⊕_m Ext^m(N,F) concentrated in
degree n. -/
abbrev CategoryTheory.Abelian.Ext.toTotalH (x : H N F n) : TotalH N F := of _ n x

namespace TotalH

/-- For an exact functor Φ, the additive map from total Ext(N,F) to total Ext(ΦN,ΦF) obtained by
applying Φ in each degree. -/
@[irreducible, local simp] def map :=
  (@exists_eq (TotalH N F →+ TotalH ..) (DirectSum.map (Φ.mapExtAddHom N F))).choose

lemma map_map Θ [@IsExactFunctor _ A _ _ Θ] (x : TotalH N F) : map Θ (map Φ x) =
  map (Φ ⋙ Θ) x := by aesop

/-- For an exact functor Φ and u in total Ext(ΦF,K), the additive map x ↦ Φx·u (Yoneda product)
from total Ext(N,F) to total Ext(ΦN,K). -/
def mapThenComp {K} (u : TotalH (Φ F) K) := (comp.flip u).comp (map (N := N) Φ)

variable {Φ Ψ} {x : TotalH M N} (r : R) (y : TotalH N F)

lemma comp_assoc y (z : TotalH F G) : comp (comp x y) z = comp x (comp y z) := by
  repeat induction ‹TotalH ..› using DirectSum.induction_on <;> try simp_all [add_assoc]

/-- A morphism f: N → F as a degree-zero element of total Ext(N,F). -/
abbrev homClass (f : N ⟶ F) : TotalH N F := of _ 0 (mk₀ f)

/-- For f: N → F, the additive map from total Ext(F,G) to total Ext(N,G) given by precomposition
with f. -/
abbrev pullbackAlong (f : N ⟶ F) : TotalH F G →+ TotalH N G := comp (homClass f)

@[simp] lemma map_of x : map Φ (of (H N F) a x) = .of _ a (x.mapExactFunctor Φ) := by simp

lemma map_homClass : map Φ (homClass f) = homClass (Φ.map f) := by simp

lemma map_comp : map Φ (comp x y) = comp (map Φ x) (map Φ y) := by
  apply x.induction_on .. <;> apply y.induction_on .. <;> simp_all

/-- For an exact functor Φ, a morphism f: G → M and x in total Ext(M,N), the image under Φ of f^*x
is (Φf)^*(Φx). -/
lemma map_homClass_comp {f : G ⟶ M} : map Φ (pullbackAlong f x) =
  pullbackAlong (Φ.map f) (map Φ x) := by simp [↓map_comp]

lemma homClass_comp g : homClass (f ≫ g) = comp (F := G) (homClass f) (homClass g) := by simp

lemma map_extClass : map Φ h.extClass.toTotalH = (h.map_of_exact Φ).extClass.toTotalH := by aesop

lemma homClass_comp_of x : pullbackAlong f (of _ n x) = of _ n (.map G f n x) := by simp

lemma of_comp_homClass x : comp (of _ n x) (homClass f) = of _ n (push M f n x) := by simp

@[simp] lemma comp_id : comp x (homClass (𝟙 N)) = x := by apply x.induction_on .. <;> simp_all

lemma comp_homClass_eq : pullbackAlong f = DirectSum.map (H.map G f) := by aesop

lemma id_comp : pullbackAlong (𝟙 M) x = x := by ext; simp [comp_homClass_eq]

lemma map_id : map (𝟭 _) x = x := by ext; simpa using! mapExactFunctor_restrictAlong_id _

lemma naturality (η : Φ ⟶ Ψ) x : comp (map Φ x) (homClass (η F)) = pullbackAlong (η N)
  (map Ψ x) := by apply x.induction_on .. <;> simp_all; solve_by_elim [mapExactFunctor_naturality]

lemma smul_eq_comp : r • y = comp y (homClass (End.asHom (CoeffAction.act r))) := by
  apply y.induction_on .. <;> simp_all [← of_smul]; tauto

lemma comp_smul : comp x (r • y) = r • comp x y := by simp [smul_eq_comp, comp_assoc]

variable {y}

lemma comp_assoc_of_eq {z} (e : comp x y = z) u : comp x (comp y u) =
  comp (F := G) z u := by rw [← e, comp_assoc]

/-- Pulling a total Ext class back along g and then along f is pulling it back along the
composite of f followed by g. -/
lemma homClass_comp_homClass_comp g (u : TotalH G G') : pullbackAlong f (pullbackAlong g u) =
  pullbackAlong (f ≫ g) u := by simp [comp_assoc_of_eq]

variable (Φ) in
/-- `map_comp`, reassociated -/
lemma map_comp_assoc {K} (u : TotalH _ K) : TotalH.comp (TotalH.map Φ (TotalH.comp x y)) u =
    TotalH.comp (TotalH.map Φ x) (TotalH.comp (TotalH.map Φ y) u) := by simp [↓TotalH.map_comp,
  comp_assoc_of_eq]

lemma mapThenComp_comp {K z} {u : TotalH _ K} (e : map Φ x = z) : mapThenComp Φ u (comp x y) =
  comp z (mapThenComp Φ u y) := e ▸ map_comp_assoc ..

lemma comp_assoc_of_sq {z w} (h : comp x y = comp (N := N') z w) (u : TotalH F G) :
    comp x (comp y u) = comp z (comp w u) := by simp [comp_assoc_of_eq, h]

attribute [-instance] addCommGroupH in
lemma exact_precomp {ξ : H M N e} {ζ : H G M b} (h : ∀ {n} {y : H M F n}, (∀ m e, ζ.comp (c :=
  m) y e = 0) → y = 0 ∨ ∃ a e x, ξ.comp (b := a) x e = y) (w : ζ.comp ξ rfl = 0 := by simp) :
  Exact (comp (F := F) ξ.toTotalH) (comp ζ.toTotalH) := .of_comp_of_mem_range
  (by aesop (add simp comp_assoc_of_eq)) fun y hy ↦ y.sum_support_of ▸ (comp _).range.sum_mem fun n
  _ ↦ (@h n (y n) fun m _ ↦ .trans (by apply y.induction_on .. <;> aesop (add simp of_apply))
  (congr($hy m) :)).elim (by aesop) (by simp_all [← comp_of, eq_comm])

/-- Long exact Ext sequence in the first variable: for a short exact sequence 0 → X₁ → X₂ → X₃ →
0, the triangle of total Ext groups Ext(X₃,F) → Ext(X₂,F) → Ext(X₁,F) → Ext(X₃,F), closed by
the extension class, is exact at each vertex. -/
lemma exact_triangle F : Exact (pullbackAlong (G := F) S.g) (pullbackAlong S.f) ∧
  Exact (pullbackAlong (G := F) S.f) (comp h.extClass.toTotalH) ∧
  Exact (comp (F := F) h.extClass.toTotalH) (pullbackAlong S.g) := let L := contravariant h F
  ⟨exact_precomp (.inr ⟨_, _, (L.exact_f_g ..).1 <| · ..⟩),
    exact_precomp (.inr ⟨_, _, (L.exact_g_delta ..).1 <| · ..⟩), exact_precomp @(Nat.rec (.inl <|
    (map_eq_zero_iff _ L.7).1 <| · ..) fun _ _ ↦ (.inr ⟨_, _, (L.exact_delta_f ..).1 <| · ..⟩))⟩

/-- The Yoneda isomorphism from G(c) to the total Ext(ℤ[h_c], G), which is concentrated in
degree 0; here h_c = Hom(c, −). -/
def sectionEquiv G (c : C) : G c ≃+ TotalH (freeAb (reprBy c)) G :=
  (homReprEquiv ..).symm.trans ((@addEquiv₀ (AbFunctor C)
  ..).symm.trans (.ofBijective _ ⟨of_injective 0, (⟨· 0, by ext ⟨⟩ <;> subsingleton⟩)⟩))

end TotalH

lemma IsCohomEquiv.bijective_totalH (h : IsCohomEquiv G f) : Bijective (TotalH.pullbackAlong (G :=
  G) f) := TotalH.comp_homClass_eq (f := f) ▸ (congrAddEquiv (.ofBijective _ <| h ·)).bijective

variable [HasFlatValues M] [HasFlatValues G] (x : TotalH M F) (y : TotalH N G) [HasFlatValues G']

/-- For x in total Ext(M,F), y in total Ext(N,G), with M, G of flat values, the Yoneda composite
of M ⊗ y and x ⊗ G in total Ext(M ⊗ N, F ⊗ G). -/
def TotalH.cup := (y.map (abTensor M)).comp (F := abTensor F G) (x.map (abTensor.flip G))

lemma TotalH.cup_comp_homClass_left β : cup (comp x (homClass (F := F') β)) y =
  comp (cup x y) (homClass (abTensor.map β G)) := by simp [cup, map_comp, comp_assoc_of_eq]

lemma TotalH.cup_comp_homClass_right γ : cup x (comp y (homClass (F := G') γ)) =
  comp (cup x y) (homClass ((abTensor F).map γ)) := by
  erw [cup, map_comp_assoc, ← comp_assoc_of_eq rfl, naturality (abTensor.flip.map _)]; simp

variable {K} (μ : abTensor F G ⟶ K) (x : H M F a) (y : H N G b)

/-- For x in Ext^a(M,F), y in Ext^b(N,G), M and G of flat values, the product in Ext^{a+b}(M ⊗
N, K): their external product pushed along μ: F ⊗ G → K. -/
def cup {n} h :=
  push _ μ n ((y.mapExactFunctor (abTensor M)).comp (x.mapExactFunctor (abTensor.flip G)) h)

lemma TotalH.cup_of h : comp (cup (.of _ a x) (.of _ b y)) (homClass μ) =
  .of _ n (_root_.cup μ x y h) := by simp [cup, _root_.cup, h]

/-- The external product is natural in both spaces: for α: M' → M, β: N' → N and γ = (α ⊗ β)∘γ',
with M, M' flat, γ^*(x × y) = γ'^*(α^*x × β^*y). -/
lemma cup_map {M'} [HasFlatValues M'] e α β {L} {γ γ' : L ⟶ _} (h : γ' ≫ (abTensor.map α).app _ ≫
    (abTensor.obj M).map β = γ) : (cup μ x y e).map _ γ n =
  .map _ γ' n (cup μ (.map (N' := M') _ α a x) (.map (N' := N') _ β b y) e) := have :=
    (congr($(mapExactFunctor_naturality (abTensor.map α) y).precomp · e ·))
  by simp_all [cup]

variable {N N' : AbFunctor A} {Θ : C ⥤ A} {Θ'} {F' : AbFunctor C'} {c : Comparison F F'} {η :
  Θ' ⟶ c.φ ⋙ Θ}

/-- Let y be the pull-back of x along c = (ψ, β) and A, and φ an endofunctor of C'. If σ: ψ → ψφ
has βφ∘Fσ = s∘β and Aφ∘α = Nσ∘A, then α^*(y restricted along φ) = s_*y in total Ext(N',
F'φ). -/
lemma TotalH.pull_twist {N N' φ x y} {A : N' ⟶ _} {s : F' ⟶ φ ⋙ F'} (h : y = c.pull A n x) (σ : _ ⟶
    φ ⋙ c.φ) α (e : whiskerRight σ F ≫ φ.whiskerLeft c.coeffHom = c.coeffHom ≫ s) (w :
  α ≫ φ.whiskerLeft A = A ≫ whiskerRight σ N) : pullbackAlong α (map (restrictAlong φ) y.toTotalH) =
  comp y.toTotalH (homClass s) := by
  simpa [h, w, ← e, map] using! congr(toTotalH ($(Comparison.pull_whiskerRight σ ..) x)).symm

/-- Let c = (φ,β) compare F with F' and η: Θ' → Θ∘φ, with Θ, Θ' functors to A. For ξ in
Ext^a(N',N) on A and x in Ext^b(N∘Θ,F), the pull-back by c, η of the Yoneda composite
(ξ∘Θ)·x equals (ξ∘Θ')·(pull-back of x). -/
lemma Comparison.pull_comp_restrictAlong (ξ : H _ N a) x h : TotalH.comp
  (ξ.mapExactFunctor (restrictAlong Θ')).toTotalH (c.pull (whiskerRight η N) b x).toTotalH =
  (c.pull (whiskerRight η N') n ((ξ.mapExactFunctor (restrictAlong Θ)).comp x h)).toTotalH := by
  simpa [h] using! congr(toTotalH
    ($(mapExactFunctor_naturality ((whiskeringLeft ..).map η) ξ).comp _ h))

/-- The external product is natural in the site: if a comparison (φ,β) from F to F' carries the
pairing μ on F to μ' on F', its pull-back along η: Θ' → Θ∘φ sends x × y to the product of
the pull-backs (F, F', N flat). -/
lemma Comparison.pull_cup [HasFlatValues F] [HasFlatValues F'] [HasFlatValues N] {μ μ'} (hμ :
  (abTensor.map c.coeffHom).app _ ≫ (abTensor.obj _).map c.coeffHom ≫ μ' = c.φ.whiskerLeft μ ≫
  c.coeffHom) (x : H (Θ ⋙ N) F a) (y : H (Θ ⋙ N') F b) h : c.pull (whiskerRight η ((abTensor.obj
  N).obj N')) n (cup μ x y h :) = cup μ' (c.pull (whiskerRight η _) a x) (c.pull (whiskerRight η _)
  b y) h := have := (congr($(mapExactFunctor_naturality (abTensor.flip.map c.coeffHom)
    (x.mapExactFunctor (restrictAlong _))).comp (mk₀ (abTensor.map c.coeffHom _ ≫ μ')) rfl))
  .symm (((cup_map (h := rfl) ..).trans (map_id _)).symm.trans (by
  simp_all [cup]; congr 2 <;> solve_by_elim [abTensor_hom_ext]))
