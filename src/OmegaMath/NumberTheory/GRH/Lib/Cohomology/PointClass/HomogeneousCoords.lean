import OmegaMath.NumberTheory.GRH.Lib.General.Geometry.ProperAtlas
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles
(known result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Homogeneous Noether normalisation and Galois closure of the cone over a variety.
Homogeneous coordinates of points under a projective embedding; global functions constant on
components. -/

open Fin MvPolynomial Finset Function Finite IsScalarTower FaithfulSMul Algebra Ideal RingHom

namespace CutsOutLocus

variable {k L ι A B C : Type} [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A] {u : A}
  [CommRing B] [Algebra k B] [CommRing C] [Algebra k C] {g : ι → B} {v : ι → A} {d} (Λ : Fin (d
  + 1) → homogeneousSubmodule ι k 1) {F : MvPolynomial ι k} (φ : A →ₐ[k] C) (ψ : A →ₐ[k] L)

variable (k g v) in def IsHomogSolution := ∀ ⦃n F⦄, @IsHomogeneous _ k _ F n → F.aeval g = 0 →
  F.aeval v = 0

/-- For polynomials Λ_0,…,Λ_d over k and a family v of elements of a k-algebra, the tuple of
values Λ_j(v). -/
noncomputable abbrev evalForms v j := ((Λ j).1.aeval v : A)

@[grind =>] lemma aeval_smul_of_isHomogeneous {n} : F.IsHomogeneous n → aeval (u • v) F =
  u ^ n * aeval v F := (eval₂_mul_of_isHomogeneous · ..)

lemma IsHomogSolution.of_ker {D} [CommRing D] [Algebra k D] (ψ : A →ₐ[k] D) : (∀ r, φ r = 0 →
  ψ r = 0) → IsHomogSolution k g (φ ∘ v) →
  IsHomogSolution k g (ψ ∘ v) := by simp [IsHomogSolution, comp_def, ← comp_aeval_apply]; tauto

lemma IsHomogSolution.map : IsHomogSolution k g v → IsHomogSolution k g (φ ∘ v) :=
  of_ker 1 φ (by simp)

lemma IsHomogSolution.smul (u : C) : IsHomogSolution k g v → IsHomogSolution k g (u • φ ∘ v) :=
  (by grind [IsHomogSolution]) ∘ map φ

@[simp] lemma evalForms_map v : evalForms Λ (φ ∘ v) =
  φ ∘ evalForms Λ v := by simp [comp_aeval_apply, comp_def]

@[simp] lemma evalForms_smul : evalForms Λ (u • v) = u • evalForms Λ v := by simp [funext_iff,
  aeval_smul_of_isHomogeneous (Λ _).2]

lemma IsHomogSolution.aeval_eq_zero_of_transcendental [Algebra B L] [IsScalarTower k B L] {t :
  L} (T : Transcendental B t) (h : IsHomogSolution k g v)
  (e : aeval (t • algebraMap B L ∘ g) F = 0) : aeval v F = 0 := by
  rw [← F.sum_homogeneousComponent, map_sum] at *
  refine sum_eq_zero fun n m ↦ h (homogeneousComponent_mem ..) ?_
  simp_rw [aeval_smul_of_isHomogeneous (homogeneousComponent_mem ..), aeval_algebraMap_apply,
    ← commutes, ← Polynomial.aeval_monomial, ← map_sum] at e
  simpa [Polynomial.coeff_monomial, m] using congr($(transcendental_iff.1 T _ e).coeff n)

lemma IsHomogSolution.refl : IsHomogSolution k v v := by tauto

lemma isIntegralElem_of_valuationSubring {f : A →+* L} {x} (h : ∀ V : ValuationSubring L,
  (∀ a, f a ∈ V) → x ∈ V) : f.IsIntegralElem x := let := f.toAlgebra
  (integralClosure ..).toSubring.eq_iInf_of_isIntegrallyClosedIn.ge
    (by simpa using (h · fun _ ↦ · isIntegral_algebraMap))

/-- Λ is a Noether normalisation of g: linear forms Λ_0, …, Λ_d, the Λ_j(g) without non-zero
homogeneous relation, and field-valued solutions v of the homogeneous equations of g
integral over any algebra image containing Λ(v). -/
def IsNoetherNormalization (g : ι → L) := IsHomogSolution k (evalForms Λ g) (@X k _ _) ∧
  ∀ {K R : Type} [Field K] [Algebra k K] [CommRing R] [Algebra k R] (φ : R →ₐ[k] K) p v,
  IsHomogSolution k g v → evalForms Λ v = φ ∘ p → ∀ i, φ.IsIntegralElem (v i)

attribute [local instance 10] FractionRing.liftAlgebra ker_isPrime

lemma exists_algHom_comp_eq_of_integral [IsAlgClosed L] (hf : φ.IsIntegral) (h : ker φ ≤ ker ψ) :
  ∃ χ, .comp χ φ = ψ := by
  algebraize [φ.1, (kerLiftAlg ψ).1]
  choose q _ _ e using exists_ideal_over_prime_of_isIntegral _ ⊥ h
  have := LiesOver.mk e.symm
  let φ := @IsAlgClosed.lift L _ _ _ _ _ (C ⧸ q) _ _ _ _ (to_isTorsionFree ..)
    (Module.isTorsionFree_iff_algebraMap_injective.2 (kerLiftAlg_injective ψ)) _
  use .comp (φ.restrictScalars k) (toAlgHom ..), AlgHom.ext (φ.2 ⟦·⟧)

variable {Λ} {g : ι → L} [CharZero k] [Finite ι]

open IsIntegralClosure FiniteGaloisIntermediateField in /--
Finitely many elements of an algebraically closed field, integral over a noetherian normal domain
`A` of characteristic zero, lie in a finite `A`-algebra `B` whose ring of invariants is `A`. -/

lemma exists_galois_hull [IsDomain A] [IsNoetherianRing A] [CharZero A] [IsIntegrallyClosed A]
    [IsAlgClosed L] [Algebra A L] [FaithfulSMul A L] (I : ∀ i, IsIntegral A (g i)) :
    ∃ᵉ (B : CommAlgCat.{0} A) (_ : Fintype Gal(B/A)) (j : B →ₐ[A] L) (x), IsInvariant A B Gal(B/A) ∧
  (algebraMap A B).Finite ∧ Injective j ∧ j ∘ x = g := let K := FractionRing A
  let N := (adjoin (K := algebraicClosure K L) K (.range (⟨_, I · |>.tower_top⟩))).1
  let B := integralClosure A N
  have := isFractionRing_of_finite_extension A K N B
  ⟨.of .., .ofEquiv _ (galRestrict A K N B).1, ⟨_, by tauto⟩, (⟨⟨_, subset_adjoin K _
    ⟨·, rfl⟩⟩, .of_map (algebraMap_injective N L) (I _)⟩), isInvariant_of_isGalois' A K N B,
    finite_algebraMap.2 (finite A K N B), algebraMap_injective .., rfl⟩

/-- Noether normalisation: for a non-zero finite tuple g in a field L over k of characteristic
0, there are d and Λ_0, …, Λ_d with Λ_0(g) ≠ 0 satisfying `CutsOutLocus.IsNoetherNormalization` for
u·g, for every unit u of L. -/
lemma exists_isNoetherNormalization (h : g ≠ 0) : ∃ d Λ, evalForms Λ g 0 ≠ 0 ∧ ∀ u : Lˣ,
  IsNoetherNormalization (k := k) (d := d) Λ (u • g) := by
  have ⟨n, Λ, h₂⟩ : ∃ᵉ (n) (Λ : _ → homogeneousSubmodule ι k 1), ∀ {K} [Field K] [Algebra k K] v,
    IsHomogSolution k g v → (∀ j, (Λ j).1.aeval v = (0 : K)) → v = 0 := ⟨_, (⟨_,
    isHomogeneous_X _ <| (equivFin ι).2 ·⟩), by simp [(equivFin ι).forall_congr_left, funext_iff]⟩
  induction' n with n I
  cases h (h₂ g .refl nofun)
  obtain ⟨m, f, c, h, z⟩ | H := (em' (IsHomogSolution k (evalForms Λ g) (@X k _ _))).imp_left
    (by simpa [IsHomogSolution] using ·)
  choose a _ using not_forall.1 (funext.mt (mul_ne_zero z (X_ne_zero 0)))
  refine I (fun i ↦ Λ i.succ - a i.succ • a⁻¹ 0 • Λ 0) fun x w H ↦ h₂ x w ?_
  specialize w (c.aeval _ (Λ · |>.2)) ((aeval_bind₁ ..).trans h)
  erw [aeval_bind₁, (funext ?_ : (Λ · |>.1.aeval x) =
    (a⁻¹ 0 • evalForms Λ x 0) • algebraMap k _ ∘ a), aeval_smul_of_isHomogeneous c,
    aeval_algebraMap_apply] at w <;> simp_all [forall_fin_succ, algebraMap_eq_smul_one]
  use n, Λ, by simpa using H (isHomogeneous_X ..), fun u ↦ ⟨fun _ _ c ↦ H c ∘ by simp [
    u.smul_def, aeval_smul_of_isHomogeneous c], fun φ p v w e i ↦
    isIntegralElem_of_valuationSubring fun V W ↦ ?_⟩
  choose j x hx using @exists_max _ _ _ ⟨i⟩ _ (V.valuation ∘ v)
  algebraize [(φ.1.codRestrict V W).comp (algebraMap k _)]
  let S := AlgHom.mk V.subtype φ.2
  refine hx i ▸ mul_mem (x i).2 (V.mem_of_valuation_le_one _ (not_lt.1 fun t ↦ ?_))
  have E := (eq_inv_smul_iff₀ (ne_zero_of_map t.ne_zero)).2 ((mul_comm _ (S ∘ x)).trans (funext hx))
  have F {y} := (IsLocalRing.residue_eq_zero_iff y).trans (V.valuation_lt_one_iff y)
  simpa [t.ne_zero] using congr(V.valuation ($E j)).ge.trans_lt (F.1 (congrFun (h₂ _ (.of_ker
    S (toAlgHom ..) (by aesop) (by grind [IsHomogSolution, Units.smul_def])) fun l ↦ by
    erw [← comp_aeval_apply, F, ← congr(V.valuation ($(evalForms_map Λ S x) l))]
    simpa [*, inv_mul_lt_one₀ t.pos] using (V.valuation_le_one ⟨_, W _⟩).trans_lt t) j))

/-- Galois closure: a Noether normalisation Λ of g yields a finite group G, finite injective f:
k[X] → B and solutions b_σ of the homogeneous equations of g with Λ(b_σ) = f(X), such that
geometric points φ, ψ with ψf(X) = uφf(X) have ψ(b_σ) = uφ(b_{τσ}) for some τ. -/
lemma IsNoetherNormalization.exists_galois_closure (h : IsNoetherNormalization Λ g) :
  ∃ (G : GrpCat.{0}) (B : CommAlgCat k) (_ : Fintype G)
  (f : MvPolynomial _ k →ₐ[k] B) (b : G → _), (∀ σ, IsHomogSolution k g (b σ) ∧ evalForms Λ (b σ) =
  f ∘ X) ∧ f.1.Finite ∧ Injective f ∧ ∀ {K : Type} [Field K] [IsAlgClosed K] [Algebra k K] (φ ψ
  : B →ₐ[k] K) (u : K), u • φ ∘ f ∘ X = ψ ∘ f ∘ X → ∃ τ, ∀ σ, ψ ∘ b σ = u • φ ∘ b (τ * σ) := by
  let Ω := AlgebraicClosure (RatFunc L)
  let φ := toAlgHom k L Ω
  let A := MvPolynomial (Fin d.succ) k
  have ⟨t, ht⟩ := PSigma.mk _ ((transcendental_algebraMap_iff
    (algebraMap_injective (RatFunc L) Ω)).2 RatFunc.transcendental_X)
  have := not_exists.1 ht .X
  algebraize [(aeval (R := k) (evalForms Λ (t • φ ∘ g))).1]
  have := (faithfulSMul_iff_algebraMap_injective A Ω).2 (algebraicIndependent_iff.2 fun _ ↦
    by simpa using! h.1.aeval_eq_zero_of_transcendental ht)
  choose B _ J x Γ Z hj e using exists_galois_hull (h.2 (aeval _) X _ (.smul φ t .refl) (by aesop))
  algebraize [(algebraMap A B).comp C]
  let j := J.restrictScalars k
  have c := congr($(funext J.2) ∘ X).trans (funext (aeval_X _))
  let b (σ : Gal(B/A)) := σ.toAlgHom.restrictScalars k ∘ x
  have hb σ : IsHomogSolution k g (b σ) := .of_ker j _ (by aesop) (e ▸ .smul φ t .refl)
  have y σ : evalForms Λ (b σ) = toAlgHom k A B ∘ X := (evalForms_map ..).trans
    (hj.comp_left (c ▸ e ▸ evalForms_map Λ j x) ▸ funext (σ.4 <| X ·))
  have e : t • toAlgHom k (integralClosure L Ω) Ω ∘ (fun (σ, i) ↦ ⟨_, h.2 φ (evalForms Λ g) _ ((hb
    σ).smul j t⁻¹) (by erw [evalForms_smul, evalForms_map, y, c]; simp_all) i⟩) = j ∘ ↿b := by aesop
  refine ⟨.of _, .of .., ‹_›, _, b, (⟨hb ·, y _⟩), Z, .of_comp (funext J.2 ▸ algebraMap_injective
    ..), fun φ ψ u E ↦ (exists_algHom_comp_eq_of_integral (aeval ↿b) _ (.tower_top (bind₁ (rename
    (.mk 1) <| Λ ·)).1 _ ((ringHom_ext (by aesop)
    (by simpa [aeval_rename] using! congrFun (y 1))).symm.subst Z.to_isIntegral)) fun _ m ↦ (((e ▸
    IsHomogSolution.refl.smul _ t).of_ker j 1 (by aesop)).smul φ u).aeval_eq_zero_of_transcendental
    ht.integralClosure (by erw [e, ← comp_aeval_apply, m, map_zero])).elim fun χ H ↦ ?_⟩
  have H σ : u • φ ∘ b σ = χ ∘ b σ := by ext; simpa using! congr($H (X (σ, _))).symm
  refine .imp (by aesop) (Subspace.exists_eq_top_of_iUnion_eq_univ
    (p := fun τ ↦ (ψ.equalizer (χ.comp (τ.restrictScalars k))).toSubmodule) ?_)
  ext a
  have ⟨P, (e : P.map _ = _)⟩ := Γ.charpoly_mem_lifts (b := a)
  have := congr(P.eval₂ $((algHom_ext (congrFun (E.symm.trans (by
    simpa [y] using! congrArg (evalForms Λ) (H 1)))) : ψ.comp _ =
    χ.comp (toAlgHom ..))).1 (ψ a) = 0)
  repeat erw [← P.eval₂_map, e, Polynomial.eval₂_finsetProd, prod_eq_zero_iff] at this
  simpa using this.le ⟨1, by simp⟩

end CutsOutLocus

open CategoryTheory AlgebraicGeometry CutsOutLocus CommAlgCat ProjSpace Over Category
variable {k ι F} [Field k] {R} [Algebra R.1 k] {Y : Over (Spec R)} [Finite ι] (L : LineBundle _ ι)
  {A B : CommAlg k} (x x' : PointsIn Y A) (v : ι → A) [Field F] [Algebra k F] [hL :
  Fact (L.IsProjEmbedding Y.hom)]

/-- The vector v in A^ι is a vector of homogeneous coordinates, for L, of the A-point x of Y,
and some coordinate v_i is a unit. -/
abbrev IsUnimodCoords := L.IsHomogCoords x.1.left v ∧ ∃ i, IsUnit (v i)

omit [Finite ι] in
lemma IsUnimodCoords.exists_chart_coords (hK :
  IsField A) {d} [IsChartCovered d (algPointsOf k R Y)] : ∃ᵉ (c : EtaleChart d _)
  (κ) (w), .map κ c.point = x ∧ IsUnimodCoords L c.point w := let := hK.toField
  ((isOpenSub_of_landsIn (·.1.1) (by tauto) ⟨_, by tauto⟩ fun _ _ ↦
    .rfl).exists_chart_le hK (L.exists_landsIn
    _).choose_spec).imp fun a ⟨⟨_, E⟩, I⟩ ↦ ⟨_, _, E, hL.1.1.2 I, _, L.isUnit_transition I I⟩

variable {L x x' v} {ξ : PointsIn Y (of k F)} {g i} (hξ : IsUnimodCoords L ξ g)

omit [Finite ι] [Fact (L.IsProjEmbedding Y.hom)] in
lemma IsUnimodCoords.exists_unit_smul_eq {w} : IsUnimodCoords L x v → IsUnimodCoords L x w → ∃ u :
  Aˣ, u • v = w | ⟨h, i, u⟩, ⟨H, _⟩ => ⟨(
  u.ringInverse.mul ((H i).1.1 ((h i).1.2 u))).unit, by ext; simp; grind [h i, H i]⟩

section

omit [Finite ι]

lemma IsUnimodCoords.map_unit_smul (h : IsUnimodCoords L x v) (φ : A ⟶ B) (u : Bˣ) :
  IsUnimodCoords L (x.map φ) (u • φ ∘ v) :=
  ⟨(h.1.map hL.1.1 h.2.choose_spec _).smul u.isUnit, h.2.imp (by simp_all [IsUnit.map])⟩

lemma IsUnimodCoords.comp (h : IsUnimodCoords L x v) (φ : A ⟶ B) :
  IsUnimodCoords L (x.map φ) (φ ∘ v) := by simpa using h.map_unit_smul φ 1

lemma IsUnimodCoords.ext (h : IsUnimodCoords L x v) (H : IsUnimodCoords L x' v) : x =
  x' := congr(⟨$(OverMorphism.ext
  (hL.1.eq_of_isHomogCoords (by erw [w, w]) h.1 H.1 (by grind [LineBundle.IsHomogCoords])))⟩)

end

include hξ

lemma IsUnimodCoords.exists_descend_of_injective (φ : A ⟶ _) (I : Injective φ) (e : g i • φ ∘ v =
  g) : ∃ x, IsUnimodCoords L x v ∧ ξ = x.map φ := by
  have hi := isUnit_of_mul_isUnit_left (e ▸ hξ).2.choose_spec
  have hv := (map_eq_one_iff _ I).1 (hi.mul_eq_left.1 congr($e i)) ▸ isUnit_one
  obtain ⟨⟨j, _, a, rfl⟩, t, b, ht⟩ := hL.1.exists_isClosedImmersion,
    exists_isHomogCoords (specAlg k R A).1.hom hv
  obtain ⟨x, rfl⟩ := (exists_ideal_le_ker_iff_factors j t).elim fun _ H ↦ by simpa using ((H.2
    (.id _)).1 (.trans ((H.2 φ.1.1).2 ⟨_, isProjEmbedding_projSpace.eq_of_isHomogCoords
    (by erw [assoc, a, assoc, b, w, ((specAlg ..).map φ).1.w]) hξ.1
    (e ▸ (ht.map (isLinearSystem_hyperplaneBundle.pull _) hv _).smul hi)⟩) (by aesop_cat)))
  exact ⟨⟨homMk x⟩, by tauto, hξ.ext (e ▸ map_unit_smul (by tauto) _ hi.unit)⟩

lemma IsUnimodCoords.exists_universal_chart (hv : IsHomogSolution k g v) (h : v i ≠ 0) : ∃ D y,
  ∃ (j : D ⟶ of k F) (G : D → MvPolynomial ι k), (Injective j ∧ ξ = .map j y) ∧ ∀ {C w},
  IsHomogSolution k g w → IsUnit (w i) → ∃ φ :
  D ⟶ C, (∀ d, Associated (aeval w (G d)) (φ d)) ∧ IsUnimodCoords L (y.map φ) w := by
  have h := Ne.isUnit (by simpa [h] using hv (isHomogeneous_X _ i))
  choose G hG E using (exists_homogenization (isHomogeneous_X k i) · .refl)
  choose φ a b using fun {C : CommAlg k} {w} (u : IsUnit (w i)) ↦
    (⟨aeval (u.unit⁻¹.1 • w), by simp [← mul_assoc, funext_iff],
    (by simp [← E ·, aeval_smul_of_isHomogeneous (hG _), associated_unit_mul_right,
    IsUnit.pow])⟩ : ∃ φ : _ →ₐ[k] C, w i • φ ∘ X = w ∧ ∀ P, Associated ((G P).aeval w) (φ P))
  obtain ⟨y, H, e⟩ := hξ.exists_descend_of_injective (ofHom _) (kerLiftAlg_injective (φ h)) (v :=
    (⟦X ·⟧)) (a h)
  exact ⟨_, y, _, _, ⟨kerLiftAlg_injective _, e⟩, fun w u ↦ ⟨ofHom (Quotient.liftₐ _ _ (by
    simpa [(b u _).eq_zero_iff, (b h _).eq_zero_iff] using w <| hG ·)),
    (congrArg _ ·.out_eq |>.subst (b u _)), (a u).subst (H.map_unit_smul _ u.unit)⟩⟩

lemma IsUnimodCoords.exists_function_const [IsAlgClosed k] (f : _ ⟶ affineSpace k 1) : ∃ c,
  ∀ {A} [Nontrivial A.1] {x v}, IsUnimodCoords L x v → IsHomogSolution k g v → (f A x).1 0 =
  algebraMap k A c := have := hξ.2.nonempty
  (IsAIC.mem_range_of_isIntegralElem (isIntegralElem_of_valuationSubring (x :=
    (f _ ξ).1 0) fun V hV ↦ by
    choose i w hw using Finite.exists_max (V.valuation ∘ g)
    obtain ⟨y, -, rfl⟩ := hξ.exists_descend_of_injective (ofHom (Subalgebra.val ⟨_, hV⟩)) (by simp)
      (.trans (mul_comm ..) (funext hw))
    simpa using! Subtype.prop _)).imp fun c e ↦ fun h@⟨_, _, u⟩ hv ↦ by
                          choose _ y j _ I φ _ H using hξ.exists_universal_chart hv u.ne_zero
                          simp_all [h.ext (H ..)]
                          exact (I.1 ((j.1.2 c).trans e) ▸ (φ _ u).1.2 c :)

lemma IsUnimodCoords.exists_mem_open_of_isUnit {V} (hV : IsOpenSub V) (hx : ξ ∈ V _) : ∃ b,
  aeval (R := k) g b ≠ 0 ∧ ∀ {C w}, IsHomogSolution k g w → IsUnit (aeval w b) → ∃ z ∈ V C,
  IsUnimodCoords L z w := hξ.2.elim fun i hi ↦ by
  choose _ z _ G _ _ _ H using hξ.exists_universal_chart .refl hi.ne_zero
  have ⟨b, _, _⟩ := hV.exists_basicOpen _ z (Field.toIsField _) ((H .refl hi).ext hξ ▸ hx)
  use G b * X i; simp_all [← isUnit_iff_ne_zero]; grind [Associated.isUnit_iff]
