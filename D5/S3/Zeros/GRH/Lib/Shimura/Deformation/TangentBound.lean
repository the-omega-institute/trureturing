/- GID: D5/S3/Zeros/GRH/Lib/Shimura/Deformation/TangentBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/Deformation/TangentBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.Deformation.TangentBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/Deformation/TangentBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation.LiftedIsogenies
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Deformations of the PEL object have at most n-1 parameters. Only the upper bound
for first-order deformations is proved here, at every good place. The proof works on the finite
group scheme of w-torsion with Drinfeld's lifting lemma, without p-divisible groups or crystals.
Source: N. Katz, Serre–Tate local moduli, LNM 868 (1981), §1 (Drinfeld's lemma); J. Lubin, J. Tate,
Formal moduli for one-parameter formal Lie groups, Bull. SMF 94 (1966); M. Harris, R. Taylor, The
Geometry and Cohomology of Some Simple Shimura Varieties (2001), III.4.1. -/

noncomputable section


open CategoryTheory AlgebraicGeometry TrivSqZeroExt ThetaObject Obj IsGroupBaseChange CommRingCat
  DualNumber Module Dual Spec Over OverMorphism RingHom Algebra
variable {E k M} [Field E] [CMBase E] {D : PEL E} [Field k] {Z σ} [AddCommGroup M] [Module k M] {X :
  ThetaFamily D Z σ} {x₀ : ThetaObject X _} {x} (hp : IsPullbackAlong (sqZeroReduction k (M →ₗ[k]
  k)) x₀ x) ⦃C : Type⦄ {C'} [CommRing C] [Algebra k C] [CommRing C'] [Algebra k C'] (φ : C →ₐ[k] C')

instance : CommRing (TrivSqZeroExt C (M →ₗ[k] C)) := inferInstance

instance : IsLocalRing (TrivSqZeroExt k (M →ₗ[k] k)) :=
  .of_nonunits_add (by simp_all [isUnit_iff_isUnit_fst])

attribute [-simp] smul_eq_zero
attribute [local simp ←] Spec.map_comp map_comp_assoc ofHom_comp AlgHom.comp_toRingHom smul_smul
  map_smul
attribute [local simp↓] map_inj lift_def algebraMap_eq_inl'

/-- For a k-algebra map φ: C → C', the ring homomorphism C ⊕ Hom_k(M,C) → C' ⊕ Hom_k(M,C') of
trivial square-zero extensions given by φ and composition with φ. -/
@[simps] def sqZeroMap : TrivSqZeroExt C (M →ₗ[k] C) →+* TrivSqZeroExt C' (M →ₗ[k] C') := by
  refine' {toFun x := inl (φ x.fst) + inr (φ ∘ₗ x.snd), ..} <;> aesop

variable (C) in
def toSqZeroSpec : map (sqZeroReduction k (M →ₗ[k] k)) (specOver k C) ⟶ .mk (specMap
  (sqZeroMap (ofId k C))) := homMk (sqZeroReduction ..)

lemma exists_point_lift [IsLocalRing C] y : ∃ Z, toSqZeroSpec C ≫ Z =
  hp.isGroupBaseChange.pointEquiv y :=
  let ⟨_, _, i, L⟩ := exists_isEtaleChart _ x.smoothOfRelativeDimension
  (L _ (inl ∘ _) (landsIn_iff_mem.2 i) ((Over.w _).trans (toSqZeroSpec C).w.symm) rfl).imp fun _ ↦
    (ext ·.1.1)

/-- For a k-algebra map φ: C → C', the induced morphism Spec(C' ⊕ Hom_k(M,C')) → Spec(C ⊕
Hom_k(M,C)) over Spec(k ⊕ M*), M* the dual of M. -/
def sqZeroSpecMap : Over.mk (specMap (sqZeroMap (ofId k C'))) ⟶ .mk
  (specMap (sqZeroMap (M := M) (ofId k C))) := homMk (specMap (sqZeroMap φ))

lemma sqZeroSpecMap_point_lift {y Z} (e : toSqZeroSpec C ≫ Z = hp.isGroupBaseChange.pointEquiv y) :
  toSqZeroSpec _ ≫ sqZeroSpecMap φ ≫ Z = hp.isGroupBaseChange.pointEquiv (specOver.map φ ≫ y) := by
  simp [pointEquiv_apply] at *; ext; simp [← e, toSqZeroSpec, sqZeroSpecMap,
    specOver.map]; congr 2; aesop

lemma isInfinitesimal_of_comp_eq_zero (Z : _ ⟶ x.groupScheme) : toSqZeroSpec C ≫ Z = 0 →
  IsInfinitesimal (ofHom (fstHom C ..).1) Z := by
  simp [IsInfinitesimal, ↓eq_zero_iff_factors_zero_section]; tauto

include hp in
/-- Known result: Deformations of the PEL object have at most n-1 parameters. -/
lemma tangent_bound [IsAlgClosed k] (hw : D.IsGoodAt (ker x₀.baseHom)) {V : ValuationSubring ℂ} {w}
  (e : FullStructure w) (hr : x₀.IsRigid) {χ : V →+* k} (h₀ : x₀.IsPullbackAlong (specMap χ) w)
  (hρ : x.baseHom = (algebraMap ..).comp x₀.baseHom) (h : ∀ l, specMap (map (eval k M l)).1 ≫ x =
  specMap (algebraMap ..) ≫ x₀ → l = 0) : finrank k M ≤ Fintype.card D.Index - 1 := by
  obtain ⟨_, ⟨-, c, hc, hc0, t, ht, H⟩, b, hb, ⟨_, _, co⟩, hN⟩ := isGoodAt_ker_spec hw
  choose ω L Q A F P using by simpa [hρ] using x.exists_tangent_log (b := b) (by simp [*])
  choose Y J using exists_point_lift hp
  choose N hL using fun {C} [CommRing C] [Algebra k C] [IsLocalRing C] (y : placeTorsion x₀ C) ↦
    have N := isInfinitesimal_of_comp_eq_zero (c • Y y.1) (y.rec (by simp_all))
    have hL Z (e : toSqZeroSpec C ≫ Z = hp.isGroupBaseChange.pointEquiv
      y := by simp [J]) := have n := isInfinitesimal_of_comp_eq_zero (Z - Y y.1) (by
        simp [*]); by simpa [← smul_add, L n, hc] using (A (n.smul c) N).symm
    And.intro N @hL
  refine finrank_le_of_placeTorsion hw h₀ e (fun _ ↦ ⟨⟨(snd <| ω <| c • Y ·.1), fun y
    z ↦ by simp [↓hL (y + z) (Y y + Y z), A (N y) (N z)]⟩, fun a y ↦ by simp [↓hL (a • y) (a • Y y),
    smul_comm c, L (N y)]⟩) (fun φ y ↦ by simp [hL (placeTorsionMap φ y) _ (sqZeroSpecMap_point_lift
    hp φ (J _)), ← ModuleObj.comp_smul, P (N y) (sqZeroSpecMap φ) rfl]) (fun y u ↦ by simp [hc, (hL
    y (Y y - sqZeroSpecMap (.comp (ofId ..) (fstHom ..)) ≫ Y y.1) (by simp [sqZeroSpecMap_point_lift
    hp, ← specOver.map_comp_assoc, *])).trans (@L _ _ (ofHom (sqZeroMap (fstHom ..))) ⟨(⟨sqZeroMap
    (ofId ..) ·, by ext <;> simp⟩), by simp +contextual [TrivSqZeroExt.ext_iff, DFunLike.ext_iff]⟩ _
    _ (by simp [IsInfinitesimal, OverMorphism.ext_iff, sqZeroSpecMap]; congr; ext <;> simp) c)])
    fun l hl ↦ ?_
  let m := specMap (map (eval k M l)).1
  obtain ⟨⟨z, hz⟩, z₀, hz'⟩ := x.exists_isPullbackAlong m,
    x₀.exists_isPullbackAlong (specMap (algebraMap _ k[ε]))
  obtain ⟨o, hq, hq₀⟩ := by simpa [hρ, ← comp_assoc] using hz.baseHom_eq_comp,
    (by simpa [m, ← hz, IsPullbackAlong] using! hp : IsPullbackAlong (sqZeroReduction ..) x₀ z),
    (by simp [← hz', IsPullbackAlong] : IsPullbackAlong (sqZeroReduction ..) x₀ z₀)
  choose G _ u K using drinfeld_lift hq₀ hq fun _ _ ↦ (·.ringChar_smul_and_smul_eq_zero.2 o hb hc)
  choose f _ g using exists_lift_of_kills_ker (hq' := hq₀) (c • 𝟙 _) (by simp) hc0 _ _ _ u fun C ↦
    fun y hy _ ↦ by
    algebraize [(algebraMap _ C).comp (inlHom k k)]
    let χ := (liftEquivOfComm (A := C) ⟨(ε : k[ε]) • .applyₗ' (R := k) C l, by simp [smul_smul]⟩).1
    let d : (map m) (specOver ..) ⟶ .mk (specMap (sqZeroMap (ofId ..))) :=
      homMk (specMap χ) (homEquiv.injective
      (by ext; simp [m, χ, TrivSqZeroExt.map, smul_def, algebraMap_toAlgebra, mul_comm]))
    let v : specOver k C ⟶ _ := homMk (V := (Over.map _).obj (specOver k[ε] C)) (𝟙 (Spec _))
      (by simp) ≫ hz'.isGroupBaseChange.pointEquiv y
    obtain ⟨⟨_, ψ, _, -, _, e, U⟩, hy⟩ := exists_isSqZeroExt_mod_eps (specOver k[ε] C).hom,
      show c • v = 0 by simpa [map_smul] using congr(_ ≫ hz'.isGroupBaseChange.pointEquiv $hy)
    obtain ⟨a, n⟩ := show ofHom χ ≫ ψ = ofHom (fstHom C ..).1 ≫ ψ by ext; simp [χ, smul_def, e,
      -map_mul], isInfinitesimal_of_comp_eq_zero (c • Y v) (by simp [*])
    refine (K _ (hz.isGroupBaseChange.pointEquiv.symm (d ≫ Y v)) y fun _ _ s ↦ (U s.w).rec fun s'
      g ↦ by ext; simpa [← g, hp.comp_toFamily, hz'.comp_toFamily, ← hz.comp_toFamily, d, v,
      toSqZeroSpec, a, pointEquiv] using (s' ≫= map ψ ≫= congr($(J v).1 ≫ x.toFamily.1))
      ).trans (hz.isGroupBaseChange.pointEquiv.injective ?_)
    simpa using Q (n.precomp d rfl _ a) (by simpa [↓P n d rfl, by simpa [smul_comm c, L n,
      ((sub_mem_ker_iff _).1 ht)] using (congr(snd $(hL ⟨t • v, by simpa using ((Ideal.torsionOf _
           _ v).span_singleton_le_iff_mem.2 hy <| H ⟨·, ·, mul_comm ..⟩)⟩ (t • Y v)) l).symm.trans
           (@hl _ _ _ _ (.trans k[ε] C) _)), χ] using F n)
  choose μ _ g using exists_lift_of_kills_ker f g (by simpa [·, hb] using congr(x₀.baseHom $co)) hq₀
    ((star D.β - b) • 𝟙 _) 1 (by simp) fun _ ↦ fun y h K ↦ by simpa [add_smul, K,
    (hr.eq_zero_of_pairing_eq_zero hz' ((D.β - b) • (star D.β - b) • y) 1 (𝟙 _) (by simp [smul_comm
    _ (D.β - _), AgreeModEps.ringChar_smul_and_smul_eq_zero hq₀, *,
    isLinear_and_pairing_eq_of_reduction f g]) fun _ t w ↦ by
    simpa [h, Pic.pairing.eq_1 _ 0, by simpa using (z₀.pairing_pow_smul_adjoint b 1 · w)] using
      ((isLinear_and_pairing_eq_of_reduction f g).2.2 hz' (t ≫ y) w).symm)] using congr($co • (star
    D.β - b) • y).symm
  choose μ _ g using exists_lift_of_kills_ker μ g (by simp) hq (𝟙 _) 1 (by simp) (by simp)
  obtain ⟨_, -, N⟩ := isLinear_and_pairing_eq_of_reduction _ g
  refine h l (hz ▸ hz' ▸ (hr.eq_of_hom hz' (o ▸ hz'.baseHom_eq_comp) μ (by simp [N hz']) fun l ↦
    eq_of_sub_eq_zero ((Ideal.torsionOf_eq_top_iff ..).1 (eq_top_mono (sup_le (by simp [smul_sub,
    ← IsLinear.smul_comp, (Subtype.ext l.2 : D.𝔑 • l = 0)]) ?_) hN))).1.symm)
  have K := AgreeModEps.ringChar_smul_and_smul_eq_zero hq (y := z₀.levelPoints l ≫ μ - z.levelPoints
    l) fun _ _ t ↦ by simp [hq.levelPoints_eq_pullSection, ← hq₀.levelPoints_eq_pullSection,
    g, OverMorphism.ext_iff, by simpa using t.w, ← hq.isGroupBaseChange.pullSection_comp,
    ← hq₀.isGroupBaseChange.pullSection_comp_assoc, ← comp_left _ _ _ hq₀.schemeMap]
  simpa [mul_comm (ker _), smul_comm (ringChar k), Ideal.span_insert, Ideal.sup_mul,
    Ideal.span_singleton_mul_le_iff, Nat.cast_smul_eq_nsmul, K] using (@K.2 _ o _ · hb)
