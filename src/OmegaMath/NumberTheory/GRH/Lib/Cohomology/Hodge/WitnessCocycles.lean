import OmegaMath.NumberTheory.GRH.Lib.Cohomology.Etale.Functoriality
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols) (known result; see Lib.Cohomology.Hodge.FixedPointFormula).

Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas). -/

noncomputable section

section

open CategoryTheory NatTrans Function FreeAbelianGroup AddCommGrpCat ShortComplex QuotientAddGroup
variable {C} [Category C] {F M N : C ⥤ Ab} {Y : C ⥤ Type 1} (A : C) (α : M ⟶ N) (U : Subfunctor Y)

/-- For maps s_A: Y(A) → F(A) natural in A, the morphism Z[Y] → F sending [y] to s_A(y). -/
def freeAb.desc (s : ∀ A, _ → F A) (h : ∀ A B f y, s B (Y.map f y) = F.map f (s A y)) :
    freeAb Y ⟶ F := ⟨(ofHom <| lift <| s ·), by delta freeAb free; aesop⟩

@[simp] lemma freeAb.desc_of s h A y : @desc C _ F Y s h A (of y) = s A y := add_zero _

lemma freeAb.hom_ext {z z' : freeAb Y ⟶ F} (h : ∀ A y, z A (of y) = z' A (of y) := by tauto) :
    z = z' := by ext; apply_rules [lift_ext]

@[simp] lemma freeAb.map_of {E} (u : E ⟶ Y) A y : freeAb.map u A (of y) = of (u A y) := rfl

/-- The universal property of Z[Y]: the bijection between maps Z[Y] → F of functors to abelian
groups and maps Y → F of functors to sets. -/
abbrev freeAb.homEquiv := (adj.whiskerRight C).homEquiv

/-- The Yoneda isomorphism of abelian groups Hom(Z[h_A],F) ≅ F(A). -/
def homReprEquiv F : (freeAb (reprBy A) ⟶ F) ≃+ F A :=
  ⟨(freeAb.homEquiv ..).trans uliftCoyonedaEquiv, by tauto⟩

instance : Projective (freeAb (reprBy A)) := ⟨fun _ _ _ ↦ ((homReprEquiv ..).exists_congr fun _ ↦
  (homReprEquiv ..).apply_eq_iff_eq.symm).2 ((range_eq_top_of_epi _).ge ⟨⟩)⟩

lemma sum_app_apply {ι A x} [Fintype ι] {g : ι → (N ⟶ F)} : (∑ i, g i) A x = ∑ i, g i A x :=
  by simp [← homAddEquiv_apply]

/-- The cokernel of a map α: M → N of functors to abelian groups, formed objectwise: A ↦
N(A)/α(M(A)). -/
def abCoker : C ⥤ Ab := .mk (fun A ↦ .of (_ ⧸ (α A).hom.range))
  fun f ↦ ofHom (map _ _ (N.map f).hom (by simp [LE.le, ← naturality_apply]))

/-- The quotient map N → coker α, sending an element of N(A) to its class modulo α(M(A)). -/
def abCoker.π : N ⟶ abCoker α where app _ := ofHom (mk' _)

instance : Epi (abCoker.π α) := ⟨fun _ _ h ↦ by ext _ ⟨⟩; congrm $h _ _⟩

/-- For a subfunctor U of a set-valued functor V, the functor to abelian groups ℤ[V]/ℤ[U]; its
Ext groups are the relative cohomology of (V, U). -/
def relFreeAb := abCoker (freeAb.map U.ι)

/-- For a subfunctor U⊂V, the quotient morphism Z[V]→Z[V]/Z[U]. -/
def relFreeAb.π : freeAb Y ⟶ relFreeAb U := abCoker.π _

/-- For x∈V(A), the class of the generator [x] in Z[V(A)]/Z[U(A)]. -/
abbrev relFreeAb.mk {A} x := π U A (.of x)

variable {U α} {g : N ⟶ F}

lemma exact_of_app (h : ∀ A, Exact (α A) (g A)) : ∃ w, Exact ⟨α, g, w⟩ :=
  ⟨by ext; simp [h ..], by simpa [(⟨NatIso.isIso_of_isIso_app⟩ :
  JointlyReflectIsomorphisms (evaluation ..)).exact_iff, ab_exact_iff_function_exact]⟩

/-- A three-term complex of functors C → Ab is short exact if, at every object A, the first map
is injective, the sequence is exact in the middle, and the second map is surjective. -/
lemma shortExact_of_app (i : ∀ A, Injective (α A)) (e : ∀ A, Exact (α A) (g A)) (s : ∀ A, Surjective
    (g A)) : ∃ w, ShortExact ⟨α, g, w⟩ := ⟨_, .mk' (exact_of_app e).2 (by simpa [mono_iff_mono_app,
  AddCommGrpCat.mono_iff_injective]) (by simpa [epi_iff_epi_app, AddCommGrpCat.epi_iff_surjective])⟩

/-- For f:N→F with f∘α=0, the induced morphism coker α→F through which f factors. -/
def abCoker.desc (f : N ⟶ F) (h : α ≫ f = 0) : abCoker α ⟶ F := ⟨fun A ↦ ofHom (lift _ (f A).hom
  (by simp [LE.le, ← comp_app_apply, h])), by delta abCoker; aesop⟩

lemma relFreeAb.hom_ext {f g : _ ⟶ F} (h : ∀ A x, f A (mk U x) = g A (mk U x) := by tauto) :
    f = g := (cancel_epi (abCoker.π _)).1 freeAb.hom_ext

end

attribute [-simp] zsmul_eq_mul Even.neg_pow map_smul

open CategoryTheory MonoidalCategory Abelian.Ext FreeAbelianGroup QuotientAddGroup Fin ShortComplex
  abCoker H freeAb
variable {C} [Category C] {m n} {V L : C ⥤ _} (R : Subfunctor (V ⊗ L))

set_option backward.isDefEq.respectTransparency false

/-- For R ⊂ V × L, the functor of points with m witnesses: tuples (x, l_1, …, l_m) with every
(x, l_i) in R. -/
def witnessed (m : ℕ) : C ⥤ Type _ := .mk ({t : _ × (Fin m → _) // ∀ i, (t.1, t.2 i) ∈ R ·})
  fun f ↦ ↾fun t ↦ ⟨(V.map f t.1.1, _), (R.map f <| t.2 ·)⟩

namespace witnessed

/-- For g: Fin m → Fin n, the natural map (x, l) ↦ (x, l∘g) from points with n witnesses to
points with m witnesses. -/
def reindexWitness (g : Fin m → Fin n) :
  witnessed R n ⟶ witnessed R m where app _ := ↾(⟨(_, _ ∘ g), ·.2 ∘' g⟩)

/-- The boundary map from the free abelian group on points with m + 1 witnesses to that on
points with m: the alternating sum of omissions of one witness. -/
def boundary m := ∑ j, (-1) ^ j.1 • freeAb.map (reindexWitness R (@succAbove m j))

/-- The map induced by the boundary, from chains with m + 1 witnesses modulo boundaries to
chains with m witnesses. -/
def cokerBoundary m := desc (α :=
  boundary ..) (boundary R m) (m.casesOn (by simpa [boundary, add_neg_eq_zero] using freeAb.hom_ext)
  (AlgebraicTopology.AlternatingFaceMapComplex.d_squared (.mk _ (reindexWitness R ·.1) ⋙ freeAb)))

/-- The natural isomorphism from the functor of points with zero witnesses for R to V that
forgets the empty tuple of witnesses. -/
def noWitness : witnessed R 0 ≅ V := NatIso.ofComponents fun _ ↦ Equiv.toIso
  (.trans (.subtypeUnivEquiv nofun) (.prodUnique ..))

variable {R}

lemma proj_boundary_of_eq_zero {A t} : (∃ l, (t.1.1, l) ∈ R A) → π (boundary R 0) A (of t) = 0 :=
  fun ⟨_, h⟩ ↦ (eq_zero_iff _).2 ⟨of ⟨(_, _), fun _ ↦ h⟩, by simp [boundary, reindexWitness,
  Subsingleton.elim _ t.1.2]⟩

/-- Write C_m for the functor of free abelian groups on points with m witnesses for R, and ∂ for
the alternating sum of omissions. Then 0 → C_{m+1}/∂C_{m+2} → C_m → C_m/∂C_{m+1} → 0, with
maps ∂ and the projection, is exact. -/
lemma shortExact_cokerBoundary : ∃ w, ShortExact ⟨cokerBoundary R m, π (boundary ..), w⟩ :=
  shortExact_of_app (fun A ↦
  let c m := lift fun t : witnessed R m A ↦ ∑ᶠ h : ∃ l, (t.1.1, l) ∈ _, @of ((witnessed ..) A) ⟨(_,
    cons _ _), cases h.choose_spec t.2⟩; Function.HasLeftInverse.injective ⟨(⟦c m ·⟧), Quot.ind
    (congr($(lift_ext ((mk' _).comp ((c m).comp _)) (mk' _) fun t ↦ by
  erw [eq_iff_sub_mem, AddMonoidHom.comp_apply, sum_app_apply]
  use -c _ (of t)
  simp [c, (⟨_, t.2 0⟩ : ∃ l, (_, l) ∈ R A), boundary, sum_app_apply, -NatTrans.app_sum,
    reindexWitness]
  simp [pow_succ, sum_univ_succ]; rfl) ·))⟩)
    (fun _ _ ↦ (eq_zero_iff _).trans (.symm exists_mk)) fun _ ↦ mk_surjective

variable {U : Subfunctor V} (hU : ∀ A, ∀ x ∈ U A, ∃ l, (x, l) ∈ R _) {F : AbFunctor C} {C'}
  [Category C'] {F' : AbFunctor C'} {V' L' : C' ⥤ _} {R' : Subfunctor (V' ⊗ L')} {U'} (hU')

/-- If every point of U ⊂ V has a witness, the map x ↦ [x] from ℤ[V]/ℤ[U] to chains with no
witness modulo boundaries. -/
def fromRel : relFreeAb U ⟶ abCoker (boundary R 0) :=
  desc (freeAb.map (noWitness R).2 ≫ π _) (hom_ext (proj_boundary_of_eq_zero <| hU · _ ·.2))

/-- The additive map sending a cocycle, a map to F from chains with n witnesses modulo
boundaries, to its class in Ext^n(ℤ[V]/ℤ[U], F). -/
def cocycleClass : (abCoker (boundary R n) ⟶ F) →+ H (relFreeAb U) F n := .mk' (push _ · n
  (n.rec (mk₀ (fromRel hU)) fun _ ↦ (·.comp shortExact_cokerBoundary.2.extClass rfl)))
  (by simp [H.push, mk₀_add])

attribute [local simp] cocycleClass H.map H.push

/-- Let γ: S₂ → T₂, y: S₃ → T₃ be compatible maps between short exact sequences S, T, and β: T₁
→ F. Some z: S₁ → F has z(s) = β(t) whenever t and s have matching images in T₂, and
y^*β_*[T] = z_*[S] in Ext¹(S₃, F). -/
lemma exists_map_extClass_comp {S T} (h : ShortExact S) (k : ShortExact T) (β :
  T.X₁ ⟶ F) {N} x γ y (e : S.g ≫ y =
  γ ≫ T.g) : ∃ z : _ ⟶ F, (∀ A s w, (∃ t, T.f A t = γ A (S.f A s) ∧ β A t = w) → w = z A s) ∧
  (push N y n x).comp (k.extClass.comp (mk₀ β) rfl) rfl = push _ z _ (x.comp h.extClass rfl) := by
  cases k; have ⟨z, e'⟩ := Exact.lift' ‹_› (S.f ≫ γ) (by simp [← e])
  use z ≫ β, fun _ _ _ ⟨_, a, b⟩ ↦ b ▸ congrArg _
    (injective_of_mono ((forget Ab).map _) (a ▸ congr($e' _ _).symm))
  simp [← comp_assoc_of_third_deg_zero, ← h.extClass_naturality _ ⟨z, γ, y, e', e.symm⟩]

lemma map_cocycleClass Φ [IsExactFunctor Φ] (β : Φ F ⟶ F') {α} (q : ∀ _, _ ⟶ Φ (freeAb _)) (h₀ :
  ∀ A x, (α ≫ Φ.map (fromRel hU)) A (relFreeAb.mk U' x) = (q 0 ≫ Φ.map (π _)) A
  (of ((noWitness _).2 A x))) (h : ∀ m n g, freeAb.map (reindexWitness R' g) ≫ q m =
  q n ≫ Φ.map (freeAb.map (reindexWitness R g))) y : ∃ y', π _ ≫ y' = q n ≫ Φ.map (π _ ≫ y) ≫ β ∧
  .map _ α n (push _ β n ((cocycleClass hU y).mapExactFunctor Φ)) = cocycleClass hU' y' :=
  have h m := (by simp [boundary, Preadditive.sum_comp, Preadditive.comp_sum, h] :
    boundary .. ≫ q m = q _ ≫ Φ.map (boundary ..)).trans (_ ≫= Φ.4 (π _) (cokerBoundary ..))
  let k m :=
    abCoker.desc (q m ≫ Φ.map (π _)) (by simp [reassoc_of% h, ← Φ.4, shortExact_cokerBoundary.1])
  ⟨k n ≫ Φ.map y ≫ β, by aesop, by simpa using congrArg (push ..) (n.rec (by simpa using (congrArg
    mk₀ relFreeAb.hom_ext)) fun n _ ↦ by simp_all [← comp_assoc (h₁₂ :=
          n.zero_add), shortExact_cokerBoundary.2.extClass_naturality
    (shortExact_cokerBoundary.2.map_of_exact Φ) ⟨k _, _, k _, (cancel_epi (π _)).1 (h _).symm,
    rfl⟩] : .map _ α n ((cocycleClass hU (𝟙 _)).mapExactFunctor Φ) = cocycleClass hU' (k n))⟩

lemma pull_cocycleClass (c : Comparison F F') (u : _ ⟶ _ ⋙ V) (v : _ ⟶ _ ⋙ L) (h : ∀ A, ∀ x ∈ R' A,
  (u A x.1, v A x) ∈ R _) {y : _ ⟶ F} {y'} (e : ∀ A t, c.coeffHom A ((π _ ≫ y) _ (of ⟨(u A t.1.1,
  _), h A _ ∘' t.2⟩)) = (π _ ≫ y') A (of t)) {α} (hα : ∀ A x, α A (relFreeAb.mk U' x) = relFreeAb.mk
  U (u A x)) : c.pull α n (cocycleClass hU y) = cocycleClass hU' y' := have ⟨_, a, b⟩ :=
    (map_cocycleClass hU hU' (restrictAlong _) c.coeffHom (fun _ ↦ freeAbMap ⟨fun A ↦ ↾fun t ↦ ⟨(u A
    t.1.1, _), h A _ ∘' t.2⟩, by intros; ext; congrm ⟨($(u.2 _) _, fun _ ↦ $(v.2 _) (_, _)), _⟩⟩)
    (hα · · |> congrArg _ |>.trans congr(⟦of ⟨⟨_, $(funext nofun)⟩, _⟩⟧)) (fun _ _ _ ↦ hom_ext) y)
  (cancel_epi _).1 (a.trans hom_ext) ▸ b
