/- GID: D5/S3/Zeros/GRH/Lib/Shimura/ThetaModuli/UniversalFamily
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/ThetaModuli/UniversalFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.ThetaModuli.UniversalFamily. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/ThetaModuli/UniversalFamily.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.IntegralModel.UniversalPoints
import D5.S3.Zeros.GRH.Lib.Shimura.GoodReduction.ArcReduction
import D5.S3.Zeros.GRH.Lib.Shimura.Deformation.TangentBound
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Moduli of abelian varieties by theta values (theta-null embedding, universal
family). Here the base is the closure of theta values at level points of PEL tori rather than being
cut out by quartic relations, the theta group is odd, and residue characteristic 2 is allowed.
Flatness comes from constant Hilbert ranks, and the group law and action come from an r-fold Riemann
theta relation. Source: D. Mumford, On the equations defining abelian varieties II, Invent. Math. 3
(1967) 75-135, section 6; theta groups in part I, Invent. Math. 1 (1966).

Part of: Integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation (known
result; see Lib.Shimura.IntegralModel.ModelExistence).

This file: Analytic families immerse, finitely many meet every point; covers have only the expected
points. Universal theta family over a smooth projective base, uniformised by balls. -/
seal Finset.univ Finset.sum Finset.prod

open ThetaObject Set AlgebraicGeometry Cardinal CategoryTheory Classical Filter IsLocalRing
  NumberField ModuliPoint Submodule LocallyOfFiniteType Over TorusModel
variable {E} [Field E] [CMBase E] {D : PEL E} {R ν} [NeZero ν] {U :
  UniversalFamily D R} {J} [Finite J] {γ : J → _} (C : U.GraphClosure γ ν) {f : AnalyticFamily D}

/-- Balls immerse. Let objects x_b of X be modelled with the period maps of the analytic family
f. If b lies in f.U and the uniformisation (b', z) ↦ ψ(b', z) is holomorphic at every (b,
z), then b' ↦ x_b' is a holomorphic immersion at b. -/
lemma AnalyticFamily.holomorphic_immersive {Z τ} {X : ThetaFamily D Z τ} {x : _ →
  ThetaObject X _} (m : ∀ b, (x b).TorusModel (f.torus b).toPeriodMap) {b}
  (h₀ : b ∈ f.U) : let ψ q := atGeneric (m _).uniformisation.expMap q.2 ≫ (x q.1).toFamily.left
  (∀ z, HolomorphicAt ψ (b, z)) → IsHolImmersionAt x b := by
  intro ψ H
  use by simpa [ψ] using ((H 0).comp (g := (·, _)) (by fun_prop)).comp_hom (hom _), fun v hv ↦
    f.eq_zero_of_linear _ h₀ _ fun _ ↦ sub_eq_zero.1
    (((m _).uniformisation.immersive_of_isPullback (x _).isGroupBaseChange.1 0).2 _ ((isJet_comp_iff
    (by fun_prop) (H _)).2 (isFirstOrderConst_iff.2 fun U r k ↦ ?_)))
  obtain ⟨d, a, L, c⟩ := f.analyticAt _ h₀,
    (H 0 (PointFn.isRegularOn_ofSection r) k).imp_right (·.fderiv.neg.differentiableAt)
  set i : _ →L[ℂ] BallBase D.Index × BallFibre E D.Index := .inr ..
  have R w : fderiv ℂ (PointFn.ofSection r _ <| ψ ·) (b, 0)
      (i (fderiv ℂ (f.torus · |>.Q ((f.torus b).Q.symm w)) b v)) = L (i w) (v, 0) := by
    induction eq_top_iff'.1 (m b).uniformisation.3.2.1 w using span_induction
    any_goals simp (disch := fun_prop) [fderiv_fun_add, fderiv_fun_const_smul, *]
    by_contra
    apply (tendsto_natCast_atTop_cobounded.eventually (tendsto_inv₀_cobounded' (((c.hasLineDerivAt
      _).clm_apply ((hasFDerivAt_id _).hasLineDerivAt _)).neg.eventually_ne
      (by simpa [add_neg_eq_zero])))).frequently
    filter_upwards [tendsto_const_nhds.prodMk_nhds (tendsto_inv_atTop_nhds_zero_nat
      (𝕜 := ℂ).zero_smul_const _) a, eventually_ne_atTop 0] with n u hn
    simpa [i] using isFirstOrderConst_iff.1 ((H _).isFirstOrderConst_of_nsmul X.relative_dim hn
      ((isJet_comp_iff (.prodMk (hasFDerivAt_id _)
      ((d ((f.torus b).Q.symm _)).differentiableAt.hasFDerivAt.const_smul (_ : ℂ)))
      ((H _).comp_hom _)).1 (cast (by simp_all [← (x _).isGroupBaseChange.nsmul_id_comp,
      ← comp_left_assoc, ← map_nsmul, (Uniformisation.eq_zero_iff ..).1, ← Nat.cast_smul_eq_nsmul ℂ,
      (f.torus _).Q.eq_symm_apply, TorusModel.lattice_eq, ψ, mem_classLattice,
      ← (x _).isGroupBaseChange.pullSection_comp]) (hv.comp_hom (X.η 0).1)))) U r u
  simp [*]

/-- For 𝔪 ≠ 0 there are finitely many analytic families f_k of theta tori such that every point
is isomorphic at level K(𝔪) to a point of some f_k lying over the domain of f_k. -/
lemma ModuliPoint.exists_finite_reps D ν {𝔪} (h : 𝔪 ≠ 0) : ∃ (κ : Type) (f : κ → AnalyticFamily D),
  Finite κ ∧ ∀ a : ModuliPoint E _ ν, ∃ k, ∃ p ∈ (f k).U.1 ×ˢ .univ, ∃ z,
  a.IsLevelIso (levelGU _ 𝔪) z ((f k).ballPoint 0 p) := let φ := _ ∘ x
  (axiomOfChoice (exists_ball_family <| rangeSplitting φ ·)).elim fun f H ↦
    ⟨_, f, (finite_isSignedFrame_classes
    (isOpen_congruenceGL_span h)).subset fun _ ⟨a, e⟩ ↦ ⟨_, ⟨_, a.isSignedFrame⟩, e⟩, fun a ↦
    have ⟨_, ⟨z, rfl⟩, _, h, e⟩ := DoubleCoset.eq.1 (apply_rangeSplitting φ ⟨_, a, rfl⟩).symm
    ⟨_, ((H _).2.2.1 ⟨_, _, realVecAction z ∘ a.P, a.isSignedFrame.mul z h.1, a.isReflection.conj _⟩
      e.symm).imp fun _ ↦ .imp_right (⟨z, · ▸ by simpa [isLevelIso_iff, mul_assoc]⟩)⟩⟩

attribute [local simp] act ratConj

/-- For an analytic family f of theta tori, the map sending p = (b, periods) to the complex
point, with its 𝔪-torsion, of the Kuga–Sato variety (fibre power of the universal abelian
scheme) is a holomorphic immersion at every p with b in the domain of f. -/
lemma UniversalFamily.isHolImmersionAt_datumPoint {P : Fin ν → _} {𝔪} p (hp : p.1 ∈ f.U) :
  IsHolImmersionAt (f.ballPoint P · |> U.datumPoint 𝔪 |>.left) p := by
  obtain ⟨I, _⟩ := f.holomorphic_immersive (U.model ⟨f, ·⟩) hp (U.holomorphic f _ hp),
    (f.analyticAt _ hp · |>.contDiffAt.fst'')
  simp_rw [← IsPt.eq_datumPoint (a := f.ballPoint ..) ⟨U.model (f, _), rfl⟩]
  refine (fun H ↦ ⟨H, fun (_, _) hv ↦ ?_⟩) (HasGermAt.of_jointly_mono ((Over.map U.base.hom).map <|
    Limits.Pi.π _ ·) (fun e ↦ OverMorphism.ext
    (fibrePower_ext_iff.2 ⟨by simpa using congr($(e ofNonempty).1 ≫ U.family.A.hom), (congr($(e
    ·).1))⟩)) (by rintro ⟨⟩ <;> simp <;> apply (U.holomorphic f _ hp _).comp (g :=
    (Prod.fst ·, _)) (ContDiffAt.analyticAt _) <;> (try simp) <;> fun_prop) (by simp; rfl))
  cases I.2 _ ((isJet_comp_iff hasFDerivAt_fst I.1).1
    (by simpa using hv.comp_hom (U.family.fibrePower _).hom))
  simpa [funext_iff] using fun i ↦ (Uniformisation.immersive_of_isPullback _
    (ThetaObject.isGroupBaseChange _).1 _).elim fun h k ↦ k _
    ((isJet_comp_iff ((hasFDerivAt_apply i p.2).add_const _) h).1 (by simpa [π] using
    ((isJet_comp_iff (hasFDerivAt_prodMk_right p.1 p.2) H).2 hv).comp_hom (U.family.proj (.inr i))))

/-- For an analytic family f and vectors P, the map sending p to the complex point of the cover
C attached to the point of f with parameter p relative to P is holomorphic at every p over
the domain of f. -/
lemma UniversalFamily.GraphClosure.holomorphicAt_point P p (hp : p.1 ∈ f.U) :
  HolomorphicAt (f.ballPoint P · |> C.point |>.left) p := .of_jointly_mono _ C.hom_ext
  fun j ↦ by simpa [↓← comp_left, ↓C.point_comp_proj] using!
  (isHolImmersionAt_datumPoint (f := f.heckeTranslate _) p hp).1

/-- Every point z of the cover W is the image of the closed point under some α: Spec V → W, V a
valuation subring of ℂ, with a point b such that: whenever a morphism u sends the complex
point of b to that of a with its 𝔪-torsion, u∘α is the V-point of a (`ThetaFamily.IsPointOf`). -/
lemma UniversalFamily.GraphClosure.exists_arc z : ∃ᵉ (V : ValuationSubring ℂ) (α) (b) (ρ :
  C.W.left.residueField z →+* _), specMap ρ ≫ C.W.left.fromSpecResidueField z =
  specMap (residue V) ≫ α ∧ ∀ {𝔪 u} {a : ModuliPoint E _ ν}, C.point b ≫ u = U.datumPoint 𝔪 a →
  U.family.IsPointOf 𝔪 a (α ≫ u.1) := C.exists_level_point_eq.elim fun m M ↦ by
  obtain ⟨_, _, f, _, H⟩ := U.isDedekindDomain, exists_finite_reps D ν (by simp : m.1 ≠ 0)
  choose b _ G using fun i ↦ exists_generic_member (hom _) ((f i).U.2.prod (by simp))
    ((f i).2.prod isConnected_univ) (C.holomorphicAt_point 0 · ·.1)
  obtain ⟨i, V, α, l, rfl⟩ := @_root_.exists_arc _ _ (isLocallyNoetherian (hom _)) _ _
    (C.isSeparatingFamily.2.induction_on · (by simp) (H · |>.elim fun c ⟨q, h, _, r⟩ ↦ M r
    ▸ (G c q h).mem_closed (by simp) (subset_closure (mem_range_self c)))) z
  exact (comap_closedPoint (residue _)).rec ⟨_, α, _, _, (Scheme.SpecToEquivOfField ..).3 (specMap
    _ ≫ α), fun h ↦ .of_generic (((reassoc_of% l) _).trans congr($h.1) ▸ isPointOf_datumPoint)⟩

/-- Let W be the closure `UniversalFamily.GraphClosure` for a finite family γ, with ν ≥ 1. If a
morphism c from W sends each point [a] to `UniversalFamily.datumPoint` of a for 𝔪 = 1, every complex
point of W over R is some [a]. -/
lemma UniversalFamily.GraphClosure.point_surjective {c} (hc : ∀ a, C.point a ≫ c =
  U.datumPoint 1 a) : C.point.Surjective := fun t ↦ by
  have ⟨z, φ, hφ, _⟩ := exists_countable_residue_point (hom _) t.1
  have ⟨V, α, b, j, hα, H⟩ := C.exists_arc z
  obtain ⟨⟨φ, rfl⟩, e, ho⟩ := exists_ringHom_complex_extend j.injective φ.injective
    (mk_quotient_le.trans (mk_set_le _)), H (hc _)
  have hφ := reassoc_of% (by simp_all [specMap] : specMap (φ.comp (residue _)) ≫ α = t.1)
  choose x p using fun {y} ↦ exists_isPullbackAlong (X := U.family) (specMap (φ.comp (residue V))) y
  choose f w using fun {y} ↦ FullStructure.exists_pullback (@p y)
  have ⟨g, ℓ, d, Y, m, v, s₂⟩ := exists_torusModel (f e.fullStructure) (by simp [baseHom, ← p, hφ,
    reassoc_of% (by simp [← c.w, reassoc_of% ho] : ‹ThetaObject ..› ≫ hom _ = α ≫ hom _)]; tauto)
  choose P G using (@id m.π.Surjective (m.uniformisation.surjective.comp Y.Q.surjective) <|
    p.isGroupBaseChange.pullSection <| e.π ·)
  use ⟨_, _, P ∘ b.P, ⟨_, Y.isSignedFrameFor⟩, s₂⟩, C.hom_ext fun i ↦ (γ i).2.2.1.elim fun _ q ↦ ?_
  obtain ⟨⟨_ | _, rfl⟩, f', h⟩ := q.2.exists_intCast_eq (γ i).2.2,
    H (C.point_comp_proj _ i) <;> simp [↓Int.cast_pos] at q
  obtain ⟨o, χ, _, _, l, _⟩ := exists_isogeny 1 (by simp) e f' (by simp) (γ i).2.2.2 (by simpa)
  obtain ⟨⟨ψ, a, _, K⟩, g₀, ℓ₀, d, Y', m', u, s⟩ :=
    p.isGroupBaseChange.exists_hom_baseChange p.isGroupBaseChange (𝟙 _) χ,
    exists_torusModel (f f'.fullStructure) (by simp [p.baseHom_eq_comp, o, ← m.baseHom_eq])
  exact (exists_matrix_of_hom m m' ψ q.1.ne' (by simpa [p.lineBundle_eq_pull] using!
    (congr((ThetaObject.lineBundle _).picClass.pull $(a (𝟙 _)).1).trans congr(($l).pull _)))).elim
    fun z ⟨F, _, _⟩ ↦ (C.point_comp_proj ..).trans (OverMorphism.ext ((isPointOf_datumPoint.eq_iff
    (b := ⟨_, _, (realVecAction z <| P <| b.P ·), ⟨_, Y'.isSignedFrameFor⟩, s⟩) ⟨m', by
    rw [comp_left, ← hφ, h]; simp [fibrePower_ext_iff, ← p.comp_toFamily, ↓← F,
      IsGroupBaseChange.pullSection_comp_assoc, *]⟩).2 ⟨z, by erw [isLevelIso_iff, ← mul_assoc,
    ← (Units.ext (funext₂ fun a b ↦ sub_eq_zero.1 (eq_zero_of_forall_mul_integral
    fun x ↦ by simpa [mul_comm, mul_sub] using torsionClass_eq_iff.1 (m'.fullStructure.injective
    (.trans (by simp [*]) (torsionPoint_comp _ _ F (Pi.single b x))) :
    torsionClass (x • (γ i).2.1.2.col b) = _) a)) : _⁻¹ = _ * g)]; simpa⟩))

open And LineBundle PeriodMap ProjSpace Ideal.IsPrime

/-- Let D be PEL data and R ⊂ E a localisation of O_E whose maximal ideals lie over primes good
for D (`PEL.IsGoodAt`). Then a universal theta family `UniversalFamily` exists: its base is
projective and smooth over R, with dense, holomorphically modelled complex objects.

Known result: Moduli of abelian varieties by theta values (theta-null embedding, universal
family). -/
lemma nonempty_universalFamily {E} [Field E] [CMBase E] {D M} {R :
  Subalgebra _ E} [IsLocalization M R] (hM : M ≤ nonZeroDivisors (𝓞 E)) (hR : ∀ m, m.IsMaximal →
  D.IsGoodAt (.comap (algebraMap _ R) m)) : Nonempty (UniversalFamily D R) := by
  obtain ⟨_, _, ι, f, _, rep⟩ :=
    @Fintype.ofFinite D.levelTorsion (finite_torsionBy ⟨_, by simp [D.level_ne_zero]⟩),
    IsLocalization.isDedekindDomain _ hM R, ModuliPoint.exists_finite_reps D 0 D.level_ne_zero
  choose t k ht using fun (ω : D.levelTorsion) (a : AnalyticFamily D × _) ↦
    exists_isHomogCoords (v := ((a.1.torus a.2).thetaCoord · ((a.1.torus a.2).torsionLift ω)))
    (specOver R ℂ).hom (Function.ne_iff.1 (thetaCoord_vector_ne_zero _ _)).choose_spec.isUnit
  have Z {B} (y : B → _) :=
    Set.univ_nonempty.imp fun (C : ReducedClosure (Over.homMk (V := Over.mk _) _ <|
    k · <| y ·)) _ ↦ let c ω := ((hyperplaneBundle _).pull Limits.prod.fst).pull (C.proj ω).1
    have := HasProjEmbedding.pi C.incl (h := fun _ ↦ ⟨isProjEmbedding_projSpace⟩)
    have A : (LineBundle.pi c).IsProjEmbedding _ ∧ ∀ a ω, (c ω).IsHomogCoords (C.point a).1 _ :=
      ⟨isProjEmbedding_pi _ (fun _ ↦ isProjEmbedding_projSpace) C.hom_ext, by
      intros; rw [IsHomogCoords.pull_iff, ← Over.comp_left, C.point_comp_proj]; apply ht⟩
    have := LocallyOfFiniteType.isLocallyNoetherian C.W.hom
    intro A fun {ι} (j : ι → B) [Finite ι] hd ↦ have H z := ((Ideal.exists_le_maximal _ (C.W.hom
      z).2.1).elim fun m h ↦ (C.W.hom.isClosedMap.specializingMap ((PrimeSpectrum.le_iff_specializes
      _ ⟨m, h.1.isPrime⟩).1 h.2)).elim fun w k ↦ Exists₃.imp (fun _ O a ↦ imp_right fun e ↦
      intro (e.symm.subst k.1) (congr(D.IsGoodAt ($(Spec.map_preimage (a ≫ C.W.hom ≫ (specOver (𝓞 E)
      R).hom)) (closedPoint _)).1).mpr (hR _ (by erw [e, k.2]; tauto)))) (exists_arc _ hd w))
      intro H ((forall_and.1 (H · |>.elim fun i ⟨v, α, h, l, d⟩ ↦ by
    -- the closed point of an arc through the point of x
    let x := (y (j i)).1.torus (y (j i)).2
    obtain ⟨hx, hc, G⟩ := h ▸ A.2 _, ?hc,
      x.hasGoodReduction_and_val_card_eq_one (by simpa [← h] using ?o (j i)) d
    choose i hi using (c · |>.exists_landsIn α)
    have n ω := ((hx ..).1.1 ((hi ω).comp _)).ne_zero
    have e ω j : Subtype.val _ = _ := ((hc ω).1 ..).1 _ _ (hi ω) ▸ (hx ..).2 j (n ω).isUnit
    have R ω := funext ((hc ω).1 _ · |>.1 _ α (hi ω)) ▸ (hc ω).2 ((hi ω).comp (specMap (residue _)))
    choose m hm using fun z ↦ Finite.exists_max (v <| x.thetaCoord · z)
    rw [← comap_closedPoint (residue _)] at l; refine ⟨⟨_, _, inferInstance, _, by exact l,
      _, x.isCutOutAt_reduction residue_surjective G.1 (q := fun z j ↦ ⟨_, by simp; bound⟩) (fun z ↦
      ⟨_, fun _ ↦ rfl, m z, by simpa using (x.thetaCoord_vector_ne_zero z <| by
      simpa [·, funext_iff] using hm z)⟩) (fun a ↦ ⟨_, by simpa using! e a, i a, by simp [*]⟩) R⟩, (
      G.elim x.exists_peak · |>.imp fun o H u _ w ↦
      l.mem_open (LineBundle.opens ..).2 (landsIn_iff_mem.1 ((R ..).1.2 ?_)))⟩
    have L i := by simpa [thetaShift, valuation_multiplier_mul_bicharacter]
      using congr(v ($(x.thetaShift_thetaCoord (frameTorsionClass_ratLift u.1) i) 0))
    simpa [v.mem_maximalIdeal_iff, e, le_mul_inv_iff₀, n, ← L, zero_lt_iff] using!
      H _ w (u + _))).elim ((IsUnit.mul_iff.1 (by_contra (exists_max_ideal_of_mem_nonunits · |>.elim
        fun m ⟨e, k⟩ ↦ (hR m e).elim fun n ⟨_, _, _, _, a, c, _⟩ ↦ notMem_of_isCoprime_of_mem c
      a (by simpa using add_mem ((mem_or_mem' k).resolve_right n.2) a)))).elim
        (exists_thetaFamily_of_points j
      hd (IsPreimmersion.of_isLocalization M).instMonoScheme ?o ?hc A.1 A.2)))
  have ⟨C, ⟨emb@⟨_, _, _⟩, hx⟩, K⟩ := Z id
  have hs {f} ⦃b⦄ n :
    HolomorphicAt (C.point ⟨f, ·⟩ |>.1) b := have ⟨_, h, k⟩ := f.exists_analytic_thetaCoord n
    .of_isHomogCoords emb (fun _ ↦ Finset.analyticAt_fun_prod _ fun ω _ ↦ (h ..).comp₂ analyticAt_id
               (f.analyticAt _ n (toRealVectors (ratLift f.frame _)))) (k.mono fun _ h ↦ .pi (w :=
      (·)) (hx _ · |>.smul h))
  choose b hb G using fun i ↦ exists_generic_member C.W.hom (f i).U.2 (f i).2 hs
  -- the generic points of the finitely many balls are dense
  choose A X m hm using K (fun i ↦ (f i,
    b i)) (C.isSeparatingFamily.2.induction_on · isClosed_closure fun x ↦ by
    choose i a ha z r using rep (x.1.ballPoint 0 (x.2, 0))
    choose _ _ m _ using
      (Z ![x, (f i, a.1)]).choose_spec.2 id (ReducedClosure.isSeparatingFamily _).2
    simpa [(C.hom_ext fun ω ↦ by simpa using (Over.OverMorphism.ext (((ThetaFamily.IsPointOf.eq_iff
      (𝔪 := 1) ⟨m 0, rfl⟩ ⟨m 1, rfl⟩).2 ⟨z, levelGU_inf_one.ge r.mem_level, r.reflection_eq,
      r.sub_mem_lattice⟩ ▸ pointOf_hom :).symm.trans pointOf_hom) =≫ ReducedClosure.proj _ ω) :
      C.point x = C.point _)] using closure_mono (by simp) (G _ _ ha.1).mem_closure)
  choose i O a ha l gd using A
  refine ⟨‹_›, _, X, ⟨emb⟩, ?_, _, m, ?l, C.isSeparatingFamily.2⟩
  -- smoothness
  choose U h h' using fun z ↦
    smooth_of_immersion _ ((f _).holomorphic_immersive (m ⟨_, ·⟩) (hb _) (?l _ _ (hb _)))
    (ha z) (fun _ ↦ Over.w _) (FaithfulSMul.algebraMap_injective ..) (((f _).U.2.eventually_mem
    (hb _)).mono (G _)) fun _ τ h₁ h₂ ↦ ((m _).exists_model_over_arc (ha _)).elim fun m _ ↦
    tangent_bound h₁ (by simp [← RingHom.comap_ker, ker_residue, baseHom]; apply gd) m.fullStructure
    (m.isRigid_pullback (residue _) rfl) rfl (by simp [baseHom, reassoc_of% h₂, RingHom.comp_assoc])
  exact HasRingHomProperty.instIsZariskiLocalAtSource.of_iSup_eq_top U (top_unique fun z _ ↦
    le_iSup U z ((l z).mem_open (U z).2 (h z ⟨⟩))) h'
  -- the uniformisations are holomorphic in families
  exact fun f b h z ↦ match f.exists_analytic_thetaCoord h, (hs h).exists_isHomogCoords emb.1 with
    | ⟨_, u, v⟩, ⟨_, k, r⟩ => .of_isHomogCoords (X.embeds.mul emb) (hb := by simp; rfl) (fun _ ↦
      (u ..).mul ((k _).comp analyticAt_fst)) (((r.and v).prod_inl_nhds _).mono fun w h ↦ .mul
    (by simpa [hm] using! ((m _).hasThetaCoords.4 _).smul h.2) (by simpa [IsHomogCoords] using h.1))
  all_goals simp [c, (isLinearSystem_hyperplaneBundle.pull _).pull] <;> tauto
