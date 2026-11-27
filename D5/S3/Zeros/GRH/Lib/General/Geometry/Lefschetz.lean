/- GID: D5/S3/Zeros/GRH/Lib/General/Geometry/Lefschetz
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Geometry/Lefschetz
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Geometry.Lefschetz. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Geometry/Lefschetz.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.Deformation.DrinfeldLifting
import D5.S3.Zeros.GRH.Lib.General.Geometry.SmoothnessCriterion
import D5.S3.Zeros.GRH.Lib.Shimura.TraceFormula.MarkedEqDefinite
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of algebraic geometry (textbook or folklore).

Part of: Transfer of eigensystems between inner forms of a unitary group differing at a real place
(known result; see Lib.Shimura.Transfer.PELDataExistence).

This file: Reduced closures of points; free finite group actions are étale; Galois covers
generically smooth. Lefschetz local terms of Hecke correspondences rewritten as a sum over marked
pairs. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits RingHom Over Set Scheme IsArtinianRing Pi pullback
  CommRingCat Ideal Quotient Algebra TensorProduct Function Finset Module Spec OverMorphism
  FormallyUnramified LocallyQuasiFinite IsOpenImmersion IsLocalization IsIntegralClosure Fint
variable {S} {b : Spec ⟨ℂ⟩ ⟶ S} {J A : Type} [Finite J] {Z : J → _} (F : ∀ j, A → (Over.mk b ⟶ Z j))

/-- A reduced closed subscheme W of the product over S of the Z_j, with complex points over b
lifting the tuples (F j a)_j and dense in W: their reduced closure. -/
structure ReducedClosure where
  W : _
  incl : W ⟶ ∏ᶜ Z
  point _a : _ ⟶ W
  point_incl a : point a ≫ incl = lift (F · a)
  isClosedImmersion : IsClosedImmersion incl.left
  isSeparatingFamily : IsSeparatingFamily (point · |>.left)

attribute [instance] ReducedClosure.isClosedImmersion

variable {F} (C : ReducedClosure F) {J' Z' F'} [Finite J'] {C' : @ReducedClosure S b J' A _ Z' F'}

instance : IsReduced C.W.left := C.isSeparatingFamily.1

/-- The morphism from the closed subscheme W to the factor Z_j: the inclusion into the product
followed by the j-th projection. -/
def ReducedClosure.proj j := C.incl ≫ Pi.π Z j

@[simp] lemma ReducedClosure.point_comp_proj a j : C.point a ≫ C.proj j =
  F j a := by simp [proj, reassoc_of% point_incl]

instance : Nonempty (ReducedClosure F) := (exists_reduced_closure _).elim fun _ ⟨i, _, c, h, r⟩ ↦
  ⟨.mk (i ≫ _), homMk i, fun a ↦ homMk _ (by simp [reassoc_of% h]), (ext <| h ·), c, r⟩

lemma ReducedClosure.hom_ext {T} {f g : T ⟶ _} (h : ∀ j, f ≫ C.proj j = g ≫ C.proj j) : f = g :=
  (mono_of_mono_left _).1 _ _ (Pi.hom_ext _ _ h)

lemma ReducedClosure.exists_lift (σ : A → _) (f : ∀ _, _ ⟶ _) (h : ∀ a j, C'.point a ≫ f j =
  F j (σ a)) : ∃ g, (∀ j, g ≫ C.proj j = f j) ∧ ∀ a, C'.point a ≫ g = C.point (σ a) :=
  have ⟨g, e⟩ := exists_lift_of_dense_preimage _ (lift f).1 (C'.isSeparatingFamily.2.mono
    (forall_mem_range.2 fun a ↦ ⟨_, congr($((C.4 (σ a)).trans (by aesop : _ = _ ≫ _)).1 _)⟩))
  have G j : homMk g (by simpa using e =≫ hom _) ≫ _ = _ := lift_comp_π f _ ▸ ext (e =≫ _)
  ⟨_, G, fun _ ↦ C.hom_ext (by simp [*])⟩

variable {R : CommRingCat} {W Z : Over (Spec R)} [IsProper W.hom] [IsSeparated Z.hom]
  {c : W ⟶ Z} {Δ : FiniteGrp} {s : Δ →* End W}

attribute [local instance 10] Quotient.field rightAlgebra finitePresentation_of_projective
  IsFinite.of_isProper_of_locallyQuasiFinite finite_of_free

/-- Chase–Harrison–Rosenberg. Let B be a finite A-algebra containing A, and G a finite group
acting on B with ring of invariants A and simply transitively on the A-algebra maps B → k,
for every field k over A. Then B is étale over A. -/
lemma etale_of_simply_transitive {A B G} [CommRing A] [CommRing.{0} B] [Algebra A B] [Module.Finite
  A B] [Group G] [Finite G] (I : Injective (algebraMap A B)) (σ : G →* (B →ₐ[A] B)ᵐᵒᵖ) (H :
  ∀ k [Field.{0} k] [Algebra A k] (x y : B →ₐ[A] k), ∃! g, ∀ b, x ((σ g).unop b) = y b)
  (V : ∀ s, (∀ g, (σ g).unop s = s) → ∃ a, algebraMap A B a = s) : Etale A B := by
  let t := (∑ g, (σ g).unop.toLinearMap).codRestrictOfInjective (Algebra.linearMap ..) (id I)
    fun s ↦ id (V _ fun g ↦ by simpa using Equiv.sum_comp (.mulRight g) (σ · |>.unop s))
  choose u E using exists_forall_sub_mem_ideal (I := fun g ↦ ker (productMap (σ g).unop (.id ..)))
    (fun _ _ ↦ isCoprime_iff_sup_eq.2 ∘ Not.imp_symm (exists_le_maximal _ · |>.elim fun m ⟨_, _⟩ ↦
    by apply (H _ (.comp (mkₐ _ m) includeRight) (.comp (mkₐ ..) includeLeft)).unique <;>
      simp_all [Ideal.Quotient.eq, ↓sup_le_iff, IsConcreteLE.le_iff])) (Pi.single 1 1)
  obtain ⟨_, y, x, ⟨⟩⟩ := exists_sum_tmul_eq u
  have K z : ∑ i, t (z * y i) • x i = z := by simp_all [Algebra.smul_def, t, sum_mul, sum_comm,
    ← linearMap_apply, mul_assoc, ← mul_sum]
  have J s := congr(∑ i, x i ⊗ₜ[A] $(K (s * y i)))
  simp [↓tmul_sum, ↓← smul_tmul, sum_comm, ← sum_tmul, mul_right_comm, K] at J
  rcases iff_exists_tensorProduct.2 ⟨_, fun s ↦ (sub_mul ..).trans (congr(_ * $(J 1) -
    _).trans (by simp [mul_sum, J])), by simpa using E 1⟩, Projective.of_split
    (.pi (t.comp ∘ .mulRight A ∘ y)) (Fintype.linearCombination _ x) (by bound)
  exact .of_formallyUnramified_of_flat

/-- Let R be a countable domain, with a map to ℂ, whose maps to fields of characteristic 0 are
injective; W proper, Z separated over R; c: W → Z onto and Δ-invariant, Δ finite. If Δ is
simply transitive on the non-empty fibres of c on complex points, then also on k-points for
every field k of characteristic 0 (`IsGaloisCovering`). -/
lemma isGaloisCovering_of_complex_points [Countable R] [Algebra R ℂ] (hR :
  ∀ k [Field.{0} k] [CharZero k] (f : R →+* k),
  Injective f) (b : ∀ g, (s g).asHom ≫ c = c) (hc : AlgebraicGeometry.Surjective c.left)
    (o : ∀ y z :
  specOver R ℂ ⟶ W, y ≫ c = z ≫ c → ∃! g, y ≫ (s g).asHom = z) : IsGaloisCovering c s := ⟨b, hc, by
    intros
    obtain ⟨x, ⟨⟩, ⟨⟩⟩ := lift' _ _ ‹_›
    obtain ⟨z, φ, ⟨⟩, _⟩ := exists_countable_residue_point (fst .. ≫ hom W) x
    set j := fromSpecResidueField _ z
    choose ψ f using exists_ringHom_complex_extend (@hR _ _ φ.charZero (Spec.preimage (j ≫ fst .. ≫
      hom W)).hom) (hR _ (algebraMap ..)) (by simp [Cardinal.aleph0_le_continuum.trans'])
    specialize o (homMk (specMap ψ ≫ j ≫ fst ..) ?_) (homMk (specMap ψ ≫ j ≫ snd ..) ?_) <;>
    simp_all [OverMorphism.ext_iff, cancel_epi, ← f, ← c.w, condition_assoc, -w]⟩

/-- Let W → Z be a Galois cover (`IsGaloisCovering`) over a domain R, W proper and reduced, Z
separated and smooth of relative dimension d. Then W ×_R k is smooth of relative dimension d
for every field k ⊇ R of characteristic 0. -/
lemma IsGaloisCovering.smoothOfRelativeDimension_baseChange [IsDomain R]
    (G : IsGaloisCovering c s) d
  [IsReduced W.left] [SmoothOfRelativeDimension d Z.hom] k [Field k] [CharZero k] [Algebra R k]
  [FaithfulSMul R k] : SmoothOfRelativeDimension d (snd W.hom (specMap (algebraMap R k))) := by
  let ι : Spec ⟨functionField _⟩ ⟶ Spec R := fromSpecStalk ..
  obtain ⟨⟨ψ, e⟩, b, hc, o⟩ := (⟨IsFractionRing.lift (FaithfulSMul.algebraMap_injective R k), (_ ≫=
    fromSpecStalk_eq ..).trans (map_comp .. ▸ congr(specMap $(lift_comp _)))⟩ : ∃ ψ, specMap ψ ≫ ι =
    specMap (algebraMap R k)), G
  let π := fst Z.hom ι
  let q := snd c.1 π
  have C {k} [Field k] y := (charZero_iff (@preimage _ ⟨k⟩ (y ≫ snd Z.hom ι)).1.injective).1
    ψ.charZero
  have O {X p} (q : X ⟶ _) (h : p ≫ c.1 = q ≫ π) w v (e : q v = q w) : ∃ g,
    (s g).asHom.1 (p w) = p v :=
    by obtain ⟨t, ⟨⟩, ⟨⟩⟩ := Pullback.exists_preimage_pullback _ _ e
       exact fromSpecResidueField_apply t _ ▸ (@o _ _ (C (fromSpecResidueField _ t ≫ fst .. ≫ q))
    (_ ≫ _ ≫ p) (_ ≫ _ ≫ p) (by grind [condition])).exists.imp fun _ ↦ (congrArg (· default) ·)
  have et {P} [CommRing P] [IsDomain P] [IsIntegrallyClosed P] {A B : CommRingCat} {_ : Algebra P A}
    (_ : Etale P A) {_ : Algebra A B} (_ : Module.Finite A B) [IsReduced B] {p u} [Mono p]
    (hp : IsPullback p (specOver A B).hom c.1 (u ≫ π)) : Etale A B := ?_
  rcases @isReduced_of_isReduced_stalk _ (⟨(fst c.1 π).stalkMap_surjective · |>.forall.2 (by simp
    [IsNilpotent.map_iff, stalkMap_injective_of_flat])⟩),
    of_finite_preimage_singleton q (q.surjective.forall.2
    (((finite_range _).preimage (fst _ π).injective.injOn).subset <| O _ condition ·))
  refine e ▸ c.w ▸ (smoothOfRelativeDimension_isStableUnderBaseChange d).1
    (.of_right' (.of_hasPullback ..) (.paste_vert (.of_hasPullback ..) (.of_hasPullback ..)))
    (d.zero_add ▸ smoothOfRelativeDimension_comp (hf := ⟨fun x ↦ ?_⟩) ..)
  choose U _ V h hx e hs using (inferInstance : SmoothOfRelativeDimension d (snd _ ι)).1 (q x)
  obtain ⟨⟨⟩, r⟩ := U.eq_bot_or_top.resolve_left (·.le (e hx)), h.preimage q
  exact ⟨_, h, _, r, hx, _, etale_iff_isStandardSmoothOfRelativeDimension_zero.1 (et
    hs.exists_etale_mvPolynomial.choose_spec.2 (q.app_eq_appLE ▸ q.finite_app _ h) ((isPullback _ _
    _ _ (h.SpecMap_appLE_fromSpec q r _).symm (by simp)).flip.paste_horiz (.of_hasPullback ..)))⟩
  have L k [CommRing k] [Algebra A k] y hy : ∃ χ : B →ₐ[A] k, specMap χ ≫ p = y :=
    (specOver.map_bijective.2
    (homMk _ (hp.lift_snd y _ hy))).imp fun _ e ↦ by simpa using! congr($e.1 ≫ p)
  choose a h0 using fun g ↦ L B (p ≫ (s g).asHom.1) (by simp [← comp_left, b, hp.w])
  let F := FractionRing P
  let N := A ⊗[P] F
  obtain ⟨h1, hm⟩ := h0 1, (h0 <| · * ·), fun {k} [Field k] [Algebra A k] ↦
    C ((specOver A k).hom ≫ u), Etale.of_equiv (commRight P F A)
  obtain H := fun {k} [Field k] [Algebra A k] (x y : B →ₐ[A] k) ↦ o k (specMap x ≫ p) (specMap y ≫
    p) (by simp [hp.w, ← Spec.map_comp_assoc, ← ofHom_comp]), isReduced_of_field F N, of_finite F N
  simp [← h0, ← reassoc_of% h0, ← Spec.map_comp_assoc, cancel_mono, cancel_mono_id, Spec.map_inj,
    -Spec.map_comp, ConcreteCategory.hom_ext_iff] at h1 hm H
  let Ω (m : MaximalSpectrum N) := AlgebraicClosure (_ ⧸ m.1)
  have inj := ((equivPi _).injective_comp _).2 (.piMap (Ω · |> algebraMap _ |>.injective))
  let χ := AlgHom.pi fun m ↦ (L (Ω m) _ (exists_point_over _ (hc.1 _)).choose_spec).choose
  have hA := χ.comp_algebraMap ▸ @id (Injective (algebraMap ..)) (inj.comp
    (includeLeft_injective (S := P) (IsFractionRing.injective ..)))
  refine etale_of_simply_transitive (.of_comp (f := χ) hA) ⟨⟨(⟨a ·⟩), congr(⟨$(AlgHom.ext h1)⟩)⟩,
    (congr(⟨$(AlgHom.ext <| hm · ·)⟩))⟩ @H fun s hb ↦ ?_
  obtain ⟨v, hv : algebraMap _ _ v = _⟩ := (reindex_equiv (equivPi _)).2.1.1 ((range_piMap _).ge
    fun m _ ↦ (InfiniteGalois.mem_bot_iff_fixed _).2 fun σ ↦ (H
    ((σ.restrictScalars A).toAlgHom.comp (.comp (evalAlgHom _ _ m) χ)) _).exists.elim (hb · ▸ · _))
  obtain ⟨x, ⟨⟩⟩ := toIntegralClosure_bijective_of_smooth (B := F).2.comp (includeLeft_surjective A
    A (isIntegral_iff.1 ·.2 |>.imp (by bound))) ⟨v, .tower_bot inj (hv ▸ .map χ (.of_finite ..))⟩
  use x, sub_eq_zero.1 (nilpotent_iff_mem_prime.2 fun q i ↦ (exists_ideal_over_prime_of_isIntegral
    (q.under A) (ker χ) (comap_bot_le_of_injective _ hA)).elim fun Q ⟨hQ, j, e⟩ ↦ (O (_ ≫ u) hp.w
    ⟨Q, j⟩ ⟨q, i⟩ congr(u ⟨$e.symm, _⟩)).elim fun g e ↦ congr($(p.injective (congr($(h0 g) _
    ).trans e)).1).le (hQ (by erw [map_sub, hb]; simpa))).eq_zero

open NumberField Matrix Polynomial LinearMap Nat ModuliPoint QuotientAddGroup
variable {E} [Field E] [CMBase E] {d₀ n} [Fintype n] [HasQuadSubfield d₀ E] {𝔑 : 𝓞 E} {ν} {R :
  _} (X : Model n d₀ 𝔑 ν R) [Nonempty n]

/-- If b is supported on regular elements, finitely many marked pairs contribute and, for all
α ∈ O_E^ν, the b-weighted z^h-coefficients of the local terms `localTerm` at 2α sum to 0. -/
def IsNullHecke ν h (b : heckeAlgebra n ℂ 𝔑) := IsRegularHecke b → ∀ α : Fin ν → _, (countTerm True
  b 1).support.Finite ∧ ∑ᶠ x, countTerm True b (localTerm (2 * α) · · |>.coeff h) x = 0

/-- θ occurs in weight h: for every linear combination p of words with p(θ) = 1,
`IsNullHecke` fails in weight h for some b·p(τ), b in the Hecke algebra. -/
def OccursInWeight a ν (θ : SafePlace 𝔑 → ℕ → ℂ) h := ∀ s (c : List _ → ℂ), ∑ L ∈ s,
  c L * (L.map ↿θ).prod = 1 →
  ¬∀ b : heckeAlgebra (Fin a) .., IsNullHecke ν h (b * ∑ L ∈ s, c L • (L.map tauHecke).prod)

attribute [local simp] mul_assoc ratConj_eigenReflection isLevelIso_iff map_smul'
  Matrix.map_sub prod_ne_zero_iff
  eval_prod eval_multiset_prod charpoly_map det_one_sub_smul_eq_prod_roots Nat.card_pi

/-- Let 𝔑 be neat and b in the Hecke algebra, with function f on cosets. If on all deep levels i
of the model the combinations ∑ f(q)[m_α ∘ u_{i,q}] satisfy `IsNullFamily` in weight h
for all α, then `IsNullHecke` holds for b in weight h. -/
lemma Model.isNullHecke_of_isNullFamily (hN : IsNeat n 𝔑) {b : heckeAlgebra _ ℂ 𝔑} {h}
  (hF : ∀ᶠ i in .atTop, ∀ α, IsNullFamily (X.leg i ⟦·.out⟧ ≫ X.m α) (heckeCosetFn b) X.d h) :
  IsNullHecke ν h b := fun hr α ↦ let f := heckeCosetFn b
  have o (c : f.support) := heckeAlgebra.mem_GUPlus_of_ne_zero (by aesop : f c.1.out ≠ 0)
  (hF.and (.all (X.eventually_translate ∅ <| o ·))).exists.elim fun i ⟨hF, ok⟩ ↦ by
  let B (z : GL n E) j := 1 - (2 * α j).val • z.1
  let L x z j := (frameLattice x).comap (realVecAction (B z j)).toAddMonoidHom
  let Q x z j := _ ⧸ (frameLattice x).addSubgroupOf (L x z j)
  have hd {x z} (h : f (γ z x) ≠ 0) j : frameLattice x ≤ L x z j ∧ (B z j).det ≠ 0 ∧
    Nat.card (Q x z j) = ∏ σ : E →+* ℂ, σ (B z j).det := ?_
  let Fx p (t : _ × _) := f (γ t.1 (x p)) ≠ 0 ∧ p.reflection = eigenReflection True t.1 t.2 ∧ ∀ j,
    p.P j ∈ L p.x t.1 j
  choose q hq using X.point_surjective i
  obtain ⟨hF, g⟩ := hF _ _, X.covering i
  extract_lets S at hF
  have ra c {p} z : (act p ⟨_, o c⟩ (2 * α)).IsLevelIso (levelGU _ 𝔑) z p ↔ γ z p.x = c.1 ∧ ratConj
    z p.reflection = p.reflection ∧ ∀ j, p.P j ∈ L p.x z j := by simp +zetaDelta [act,
                      sub_mem_comm_iff, Quotient.mk_eq_iff_out.trans QuotientGroup.leftRel_apply]
  have e c y := by simpa only [*, ← point_leg] using
    (X.point_eq_iff i _ (q y)).trans (exists_congr (ra c))
  choose! r hs un using fun s (h : s ∈ S) ↦ (((e ..).1 h.symm).elim fun z ⟨e, H⟩ ↦
    ((isReflection_eigenReflection (hr (e ▸ (f.3 _).1 s.1.2))).2 _ (ModuliPoint.isReflection _)
    H.1).elim fun μ U ↦ ⟨(z, μ), by grind, fun t a ↦ by grind
    [mul_inv_eq_one.1 (hN.2 (isSignedFrame _) (by simpa [← a.2, QuotientGroup.eq] using e)
    (by simpa [a.1.2] using H.1))]⟩ : ∃! t, Fx (q s.2.1) t ∧ γ t.1 (q s.2.1).x = s.1.1)
  let cl := Quotient.mk (MulAction.orbitRel (GL n E) (MarkedTriple (levelGU n 𝔑) n))
  have fix {p q z t} (hz : p.IsLevelIso _ z q) (h : Fx p t) : Fx q (z * t.1 * z⁻¹, t.2) :=
    have k := heckeAlgebra.heckeCosetFn_conj hz.mem_level ▸ by simpa using h.1
    ⟨k, by simp [← hz.reflection_eq, h.2], fun j ↦ (add_mem_cancel_left
      ((hd k _).1 (hz.sub_mem_lattice j))).1 (by simpa +zetaDelta [-sub_mulVec, mul_sub,
      sub_mul] using realVecAction_mem_frameLattice hz.mem_level.2.1.isIntMatrix (h.2.2 j))⟩
  have H {p q s t} (h : Fx p t) (hs : Fx q s) : cl (p.x, t) = cl (q.x, s) ↔ ∃ w,
    q.IsLevelIso (levelGU _ 𝔑) w {p with P j := realVecAction w (q.P j)} ∧ (w * s.1 * w⁻¹, s.2) =
    t := Quotient.eq.trans (exists_congr fun w ↦ Prod.ext_iff.trans (.symm (and_congr_left fun e ↦
    .trans (by simp [hs.2, h.2, ← e]) (QuotientGroup.eq.symm.trans comm))))
  have hc {p z δ} (e : X.point i p ≫ _ = z) := g.1 δ ▸ (reassoc_of% e) _
  have bij p {t} (h : Fx p t) : {s ∈ S | cl ((q s.2.1).x, r s) = cl (p.x, t)}.BijOn (·.2.1) (.range
    fun u : (∀ j, Q p.x t.1 j) × _ ↦
      X.point i {p with P j := (u.1 j).out} ≫ (X.deck i u.2).asHom) :=
    ⟨fun s ⟨m, a⟩ ↦ ((H h (hs s m).1).1 a.symm).elim fun w ⟨R, e⟩ ↦ let u j : Q .. := ⟦⟨_, (e ▸ fix
    R (hs s m).1).2.2 j⟩⟧; (g.3 ℂ _ _ congr($((hq _ ▸ (X.point_eq_iff i _ {p with P j :=
      (u j).out}).2 ⟨w, R.mem_level, R.reflection_eq, (eq_iff_sub_mem.1 <| u
      · |>.out_eq.symm :)⟩ :).symm).1)).exists.imp' (u, ·) fun _ _ ↦ by ext; tauto,
          fun ⟨c, ⟨y⟩⟩ a ⟨c', ⟨_⟩⟩ b E ↦ by
    cases E
    obtain ⟨w, R, e⟩ := (H (hs _ b.1).1 (hs _ a.1).1).1 (b.2.trans a.2.symm)
    cases hN.2 (isSignedFrame _) R.mem_level R.reflection_eq
    congr 1
    exact Subtype.ext ((hs _ a.1).2.symm.trans (.trans (by simp [← e]) (hs _ b.1).2)),
      fun y ⟨P, E⟩ ↦
    ((point_eq_iff ..).1 (hc (hq y ▸ E :))).elim fun w R ↦ have a := fix R ⟨h.1, by simp [h.2]⟩
    have m := ((e ⟨_, (f.3 _).2 a.1⟩ y).2 ⟨_, rfl, by simp [a.2], a.2.2⟩).symm
    ⟨⟨_, ⟨y⟩⟩, ⟨m,
      un ⟨_, ⟨y⟩⟩ m _ ⟨a, rfl⟩ ▸ (H a h).2 ⟨w, ⟨R.mem_level, R.reflection_eq, by simp⟩, rfl⟩⟩, rfl⟩⟩
  have hP {p t} (h : Fx p t) : (localTerm (2 * α) t.1.1.charpoly t.2).eval 1 = Nat.card (∀ j, Q p.x
    t.1 j) := by simp [hd h.1, B, lieRoots, apply_ite, RingHom.map_det, localTerm,
    (numberedRoots ..).injective]
  obtain ⟨fS, sum⟩ := hF _ (hs · · |>.elim fun h k ↦ ⟨hq _ ▸ X.tangent i _ _ _ _ _ (ok _).1 (hr h.1)
    h.2.1 ((ra ..).2 ⟨k, by simp [h.2]⟩), by simp [hP h, hd h.1]⟩)
  have sup {w} : (countTerm _ b w).support ⊆ _ := fun c hc ↦ ((ite_ne_right_iff.1 hc).imp_right
    left_ne_zero_of_mul).elim fun h₂ h₃ ↦
    ((bij ⟨_, _, 0, h₂, (isReflection_eigenReflection (hr h₃)).1 _⟩ ⟨h₃, by
    simp⟩).surjOn ⟨(0, 1), rfl⟩).imp fun _ ↦ (·.1.imp_right (·.trans (by simp; exact c.out_eq)))
  use (fS.image _).subset sup, Set.indicator_eq_self.2 sup ▸ (finsum_mem_def ..).symm.trans
    (finsum_image_eq_zero_of_fibers fS _ sum (hs · · |>.elim fun a k ↦ by
    rw [countTerm_mk, ite_eq_left (a.2.1 ▸ isSignedFrame _), k, card_congr (bij _ a).equiv,
      Nat.card_range_of_injective, card_prod, cast_mul, hP a, div_div]
    rintro ⟨u⟩ ⟨v⟩ e
    cases (((point_eq_iff ..).1 ((hc e).trans (hc rfl).symm)).elim fun w R ↦
      funext (Quotient.out_equiv_out
      |>.1 <| by simpa [leftRel_apply, neg_add_eq_sub, hN.2 (isSignedFrame _) R.mem_level
                   R.reflection_eq] using! R.sub_mem_lattice ·) : v = u)
    simpa using (g.3 ℂ _ _ congr($(hc e).1)).unique congr($e.1) rfl))
  let F := (realVecAction (B z j)).restrictScalars ℂ
  let G := 1 + -2 • ((realVecAction ((α j).1 • z.1)).restrictScalars ℤ).restrict fun _ ↦
    realVecAction_mem_frameLattice (by
    simpa using! mul_mem (coe_mem_Ô _) <| (heckeAlgebra.mem_GUPlus_of_ne_zero h).2 · ·)
  have hG y : F y.1 = G y := by simp +zetaDelta [mul_smul, map_ofNat]; rfl
  have hf := let c := Module.finBasis ..; show (F.restrictScalars ℝ).det = (G.toMatrix c c).det by
    simp [det_apply', hG, ← det_toMatrix (c.ofZLatticeBasis ℝ), toMatrix_apply].trans_ne (by
    rw [Int.cast_ne_zero, map_add, toMatrix_one, map_smul, det_one_add_smul]; omega)
  obtain ⟨le, dL⟩ := (hG ⟨·, ·⟩ ▸ (G _).2), show F.det = _ by erw [det_restrictScalars,
    det_toLin', ← cmEmbedding.map_det, det_pi (LinearMap.mul ℂ ℂ <| Φ · _)]
  exact ⟨le, (hf <| by simp [det_restrictScalars, dL, ·]), (relIndex_comap_lattice le
    (equivOfDetNeZero _ hf).injective).trans (by simp [dL, prod_embeddings_eq_prod_pairs])⟩
