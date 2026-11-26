/- GID: D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/ModelAlongArc
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/Uniformisation/ModelAlongArc
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.Uniformisation.ModelAlongArc. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/Uniformisation/ModelAlongArc.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation.AppellHumbert
import D5.S3.Zeros.GRH.Lib.Shimura.ThetaNormality.RiemannRelation
import D5.S3.Zeros.GRH.Lib.Shimura.Extension.ArcExtension
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number
(known result; see Lib.Shimura.Uniformisation.AppellHumbert).

This file: Linear maps to the torsion module come from finite-adelic matrices. Objects modelled on
theta tori: uniformisation, torsion points, Weil pairing, multiplier. Isogenies of modelled PEL
abelian varieties correspond to rational matrices. Analytic families of period maps; theta
coordinates vary holomorphically after scaling. Uniformisation of the generic fibre extends over a
valuation ring by properness. -/

open Set Matrix NumberField CategoryTheory Complex LinearMap Submodule LineBundle AlgebraicGeometry
  Polynomial AddChar IsIntegrallyClosed Category Function ValuativeArc
variable {E n} [Field E] [NumberField E] [Fintype n] (φ : (n → E) →ₗ[𝓞 E] AdelicTorsion E n)

lemma exists_matrix_torsionClass_eq : ∃ h, ∀ y, torsionClass (h *ᵥ frameCoords 1 y) = φ y := by
  choose r hr using
    (_root_.id <| Quot.exists_rep <| φ <| Pi.single · · : ∀ _ _, ∃ y, torsionClass y = _)
  choose a _ h using fun j ↦ ((isCompact_pi_infinite fun _ ↦ isCompact_Ô).vadd
    (r j 1)).inter_iInter_nonempty _ (fun x ↦ (isOpen_preimage_torsionClass
    {torsionClass (r j x)}ᶜ).isClosed_compl.preimage_of_continuous (f := (x • ·))) fun u ↦ by
    choose m b e using IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) u _root_.id
    use m.1 • r j m.1⁻¹, ⟨_, torsionClass_eq_iff.1 ?_, add_sub_cancel ..⟩, mem_biInter fun x h ↦ ?_
    repeat (try erw [mem_preimage, smul_comm, ← smul_assoc, ← e _ h]); simp; simp_all
      [← map_smul, ← Pi.single_smul, Algebra.smul_def, ← division_def]
  use aᵀ; simp_all [mulVec_eq_sum, frameCoords, transpose_transpose a, ← map_sum φ,
    Finset.univ_sum_single]

variable {E : _} [Field E] [CMBase E] {D : PEL E} {Z τ} {X :
  ThetaFamily D Z τ} {O} [CommRing O] [ValuativeArc O] (y
  : ThetaObject X (Spec ⟨O⟩)) {g ℓ V} [FinComplexSpace V] (Y : PeriodMap D g ℓ V)

/-- A model of y on (g, ℓ): a polarised period map and an O_E-linear uniformisation with the
period lattice as kernel, giving theta coordinates and the level points; O_E → ℂ is Φ_{v₀}. -/
structure ThetaObject.TorusModel where
  baseHom_eq c : algebraMap O ℂ (y.baseHom c) = Φ v₀ c.val
  uniformisation : Uniformisation y.groupScheme V
  (χ θ) hasThetaCoords :
    HasThetaCoords uniformisation.L (atGeneric uniformisation.expMap) y.lineBundle Y.B χ θ
  equivariant (c : 𝓞 E) w : uniformisation.expMap (Y.Q (cmEmbedding c.val • w)) =
    c • uniformisation.expMap (Y.Q w)
  level_eq l : y.levelPoints l = uniformisation.expMap (Y.torsionLift l)
  lattice_eq : uniformisation.L = Y.periodLattice

/-- Let A/ℂ be abelian of dimension d, embedded by N obeying the parallelogram law. A dense
homomorphism V → A(ℂ) killing the lattice of Y, with the theta functions of Y as
coordinates, is a uniformisation with exactly that kernel, and d = n[E⁺:ℚ]. -/
lemma PeriodMap.exists_uniformisation_of_dense {A N} [IsAbelianScheme A] d (h :
  SmoothOfRelativeDimension d A.hom) (hN : IsProjEmbedding N A.hom) (w :
  N.picClass.ParallelogramLaw) (e : V →+ ComplexPoint A) (hd : IsSeparatingFamily (atGeneric e))
  (hl : ∀ z, N.IsHomogCoords (e z).left (Y.thetaCoord · z)) (hL : ∀ l ∈ Y.periodLattice, e l = 0) :
  ∃ u : Uniformisation A V, HasThetaCoords u.L (atGeneric u.expMap) N Y.B Y.multiplier
  (flip Y.thetaCoord) ∧ u.expMap = e ∧ u.L = Y.periodLattice ∧ d = abelianDim E D.Index := by
  obtain ⟨⟨u⟩, o⟩ := hN.nonempty_uniformisation h,
    HasThetaCoords.mk hN.1 Y.isAppellHumbert_periodLattice Y.thetaCoord_mem_thetaSpace hl
  obtain ⟨⟨B', _, _, h', hp'⟩, ⟨F, hF⟩, T, U, C, -⟩ := u.appell_humbert hN w,
    u.universal e (o.holomorphicAt hN 0), exists_theta_evaluation o
  have P {M χ θ} (t : HasThetaCoords (ι := D.T) _ (atGeneric _) M B' χ θ) :
    HasThetaCoords Y.periodLattice _ M .. := t.pull _ (f := 𝟙 _) (congr($(hF ·).1))
  have ⟨ρ, _⟩ :=
    (P h').riemannForm_eq_of_isFrame o (picClass_eq_iff.1 rfl).choose_spec (o.holomorphicAt hN)
  have key b (hb : ∀ l ∈ Y.periodLattice, B'.riemannPhase (F l) b = 1) l (hl' : l ∈ u.L) :
      B'.riemannPhase l b = 1 := (fun M (t : HasThetaCoords _ _ M ..) ↦ by
    choose σ v using fun a ↦ Y.isAppellHumbert_periodLattice.thetaSpace_le_of_thetaShift_mem
      (Y.thetaCoord_mem_thetaSpace 0) (Y.thetaCoord_ne_zero _) T.range (Y.dualLattice_periodLattice
      ▸ fun _ ⟨_, a, j⟩ ↦ j ▸ Y.thetaShift_thetaCoord (s := ⟨_, a⟩) rfl 0 ▸ smul_mem _ _ ⟨_, C _⟩)
      ((P t).2.of_riemannForm_eq Y.isAppellHumbert_periodLattice ρ (by aesop) ((P t).3 a))
    simp [U] at v
    have r q : PointFn.IsRegularOn _ ((N.mul M.inv).opens q) := ((σ q.2).2.1.1 _).mono inf_le_left
    have ⟨G, hG, H⟩ := h'.exists_theta_of_isSection t ⟨r, fun p q _ _ a b ↦
      hd.pointFn_ext ((r p).mono (by order)) (.mul (regular ..) (r q))
      (by simp +contextual [hl .., *, (P t).4 .., field]) _ _ (by simp_all)⟩ (h'.holomorphicAt hN)
    have H0 z : G (F z) ≠ 0 := (hl z).ne_zero.elim fun i k ↦ ((P t).4 z).ne_zero.elim fun a m h ↦
      m (by simpa [*] using H _ a _ (((P h').4 ..).1.1 ((hl ..).1.2 k.isUnit)).ne_zero)
    simpa [F.map_zero ▸ H0 0, h'.2.ne_zero hl', field, eq_comm, one_smul ℂ l ▸
      (h'.2.add t.2.neg).apply_smul_of_nonpos hG l (by simp) 1] using
      hG.2 _ hl' 0) _ (h'.pull_translate (u.atGeneric_add b))
  let G := LinearEquiv.ofBijective F.1 (.of_comp_left (f :=
    (B'.riemannForm ∘ₗ F.1.restrictScalars ℝ).flip) (BilinForm.toDual _
    (ρ ▸ Y.isPosRiemann.nondegenerate :).flip).bijective (ker_eq_bot.1 (bot_unique
    (hp'.nondegenerate.flip.ker_eq_bot ▸ le_ker_iff_comp_subtype_eq_zero.2 (flip_inj (ext_on u.3.2.1
    (eq_zero_of_exp_eq_one _ fun ⟨b, h⟩ ↦ key b (by simp_all [LinearMap.ext_iff]) · ·)))))))
  exact ⟨⟨e, Y.periodLattice, funext hF ▸ u.surjective.comp G.surjective,
    (⟨hL ·, fun h ↦ Y.isPosRiemann.isDualFamily.5 _ fun y ↦ ρ ▸ key _ (by simpa [← ρ] using!
    ((Y.isPosRiemann.isDualFamily.1 y).2 · · 0)) (F _) (by simp [*])⟩), (⟨o.holomorphicAt hN ·,
    fun _ h ↦ G.ker.le ((u.immersive _).2 _ ((isJet_comp_iff F.hasFDerivAt (u.immersive _).1).1
    (by aesop)))⟩), (u.universal · · |>.imp' (G.symm.toContinuousLinearEquiv ∘L ·) fun _ ↦ (· · ▸
    hF _ ▸ congrArg _ (G.4 _)))⟩, o, by simp [← Y.isPeriodMap.finrank_eq_abelianDim, G.finrank_eq]⟩

namespace ThetaObject.TorusModel

variable {y Y} (m : y.TorusModel Y)

/-- The map π of a model m, from (E ⊗ ℝ)ⁿ to the sections of A over O: the period map Q followed
by the uniformisation. -/
noncomputable def π w := m.uniformisation.expMap (Y.Q w)

/-- Let O be a valuation ring with fraction field ℂ and φ : O → ℂ a ring homomorphism. For some
unit ε of Ẑ, every value ψ_f(t) lies in O and φ sends it to ψ_f(εt). -/
lemma exists_unit_on_roots_of_unity (φ : O →+* ℂ) : ∃ ε : (Ô ℚ)ˣ, ∀ t, ∃ c, algebraMap O ℂ c =
  ψf E t ∧ φ c = ψf E (t * finAdeleIncl ℚ E ε) := by
  choose! ζ J using fun (z : ℂ) h ↦ isIntegral_iff (R := O).1
    ((IsPrimitiveRoot.orderOf z).isIntegral (orderOf_pos_iff.2 h)).tower_top
  refine .elim ((isCompact_Ô.prod isCompact_Ô).inter_iInter_nonempty (fun t ↦ {p | φ (ζ (ψf E t)) =
    ψf _ (t * finAdeleIncl _ _ p.1) ∧ (ψf E (t * finAdeleIncl _ _ (p.1 * p.2))).1 = ψf _ t})
    (fun _ ↦ by apply_rules [IsClosed.and, isClosed_eq, Continuous.subtype_val] <;> fun_prop)
    fun U ↦ ?_) fun _ ⟨⟨a, c⟩, H⟩ ↦ ⟨.mkOfMulEqOne ⟨_, a⟩ ⟨_, c⟩ (Subtype.ext (adeleMap_injective
    (algebraMap _ E) (eq_of_ψf (by aesop)))), (⟨_, J _ <| isOfFinOrder_ψf ·, by aesop⟩)⟩
  choose N hN _ using exists_forall_mul_mem_Ô (U.restrict id)
  obtain ⟨P, _, I⟩ := isPrimitiveRoot_exp N hN, NeZero.mk hN, IsFractionRing.injective O ℂ
  have Q := (J _ (P.isOfFinOrder hN) ▸ P).of_map_of_injective I
  have P' := isRoot_cyclotomic_iff.1 (map_cyclotomic _ φ ▸ (Q.isRoot_cyclotomic hN.pos).map)
  obtain ⟨⟨k, _⟩, l, _⟩ := P.eq_pow_of_pow_eq_one P'.1, P'.eq_pow_of_pow_eq_one P.1
  refine ⟨(k, l), by simp, mem_biInter fun t _ ↦ (Q.eq_pow_of_pow_eq_one (ξ := ζ (ψf E t)) (I
    (by simp_all [isOfFinOrder_ψf, ← Circle.coe_pow, ← map_nsmul_eq_pow, ψf_of_mem]))).elim ?_⟩
  simp [-nsmul_eq_mul, ← nsmul_eq_mul', map_nsmul_eq_pow]
  grind [isOfFinOrder_ψf, P.isOfFinOrder, pow_right_comm]

/-- The full structure of a model: the class of g⁻¹a in (𝔸_f / Ô)ⁿ, for a in Eⁿ, is sent to the
torsion section π(a). -/
noncomputable def fullStructure :
  y.FullStructure := have K := by simpa [← m.lattice_eq] using @Y.sub_mem_periodLattice_iff
  by refine ⟨⟨⟨(m.uniformisation.expMap <| Y.periodPoint <| ratLift g ·), ?_⟩, ?_⟩, fun _ ↦ ?_,
    m.level_eq, fun ι ↦ Y.isFrameFor.elim fun a F ↦ (exists_unit_on_roots_of_unity ι).imp' (a * ·)
    fun ε H k s t _ _ ↦ (H _).imp fun _ h ↦ ⟨by simpa [mul_right_comm]
    using h.2, fun _ _ ↦ (lift_commutator_iff_weil_pairing _ m.hasThetaCoords · · |>.2 (by
    simpa [*, mul_add, map_add_eq_mul, (ψf_unit_eq_one _).2, (D.mem_T _).1,
      Y.riemannForm_eq, -nsmul_eq_mul, ← frameTorsionClass_apply, show ∀ ξ a b,
      xiForm ξ (frameCoords g a) (k • b) = k * xiForm ξ s t + xiForm ξ (k • s) (b - t) +
    xiForm ξ (frameCoords g a - s) (k • b) by simp [star_trivial, xiForm, -nsmul_eq_mul]; grind,
      Circle.ext_iff] using (fourierChar_polarisationForm F (ratLift g (torsionClass s))
      (k • ratLift g (torsionClass t))).symm))⟩⟩ <;>
    simp [← equivariant, ← toRealVectors_smul, K, ← map_add, map_add (frameTorsionClass g)]

/-- For a model m of y on (g, ℓ) and z in Eⁿ, the full level structure `m.fullStructure` sends the
torsion class of g⁻¹z to the uniformised section at Q(Φ(z)), Q the period map, Φ the CM-type
embedding. -/
lemma torsionPoint_frameTorsionClass z : m.fullStructure.torsionPoint (frameTorsionClass g z) =
  m.uniformisation.expMap (Y.periodPoint
  z) := by simpa [← m.lattice_eq] using! Y.sub_mem_periodLattice_iff.2 (frameTorsionClass_ratLift _)

/-- In a model with lattice L, every b in the dual lattice L^∨ has |T|·b in L, and translation
by the section of b has a lift to N that preserves the O-span of the coordinates. -/
lemma exists_isTranslationLift_of_dualLattice : ∀ b ∈ Y.B.dualLattice (L := m.uniformisation.L),
  Nat.card D.T • b ∈ m.uniformisation.L ∧ ∃ Φ, IsTranslationLift _ (m.uniformisation.expMap b) Φ ∧
  span O (range (coordSection y.isProjEmbedding.1)) ∈ Φ.invtSubmodule := m.lattice_eq ▸
  Y.dualLattice_periodLattice ▸ fun b H@⟨w, a, h⟩ ↦ ⟨Y.card_nsmul_mem_periodLattice H,
  (y.obj_isThetaStructure.theta_law 1 ⟨_, a⟩).imp fun _ k ↦
  ⟨h ▸ by simpa [← torsionPoint_frameTorsionClass, m.level_eq] using! k.1, span_le.2 (by aesop)⟩⟩

/-- On the lattice of a model the multiplier is χ(l) = exp(πi·e(βl, l)), where e is the Riemann
form of B. -/
lemma multiplier_eq_canonicalMultiplier l (h : l ∈ m.uniformisation.L) : m.χ l =
  canonicalMultiplier Y.B (Y.intAction D.β) l := by
  have P c := m.hasThetaCoords.pull _ (e' := atGeneric m.uniformisation.expMap) (f :=
    (c • 𝟙 y.groupScheme).1) (by simp [PeriodMap.intAction, equivariant, atGeneric,
    ← Over.comp_left]) (m.lattice_eq ▸ Y.intAction_mem_periodLattice c)
  simpa [add_comm _ l, m.hasThetaCoords.2.semicharacter, m.hasThetaCoords.2.ne_zero, field,
    (m.lattice_eq ▸ Y.intAction_mem_periodLattice _) l h, h] using! (((m.hasThetaCoords.mul
    m.hasThetaCoords).mul (P _)).riemannForm_eq_of_isFrame (P (D.β + 1)) (picClass_eq_iff.1 (by
    simpa [Pic.pairing, add_smul, eq_sub_iff_add_eq] using!
      y.hasClassLaws.2 0 (𝟙 _))).choose_spec).2.1 l h

variable {V : _} {V'} [FinComplexSpace V] [FinComplexSpace V'] {D : PEL E} {g : _} {g'} {ℓ :
  _} {ℓ'} {Z τ : _} {X : ThetaFamily D Z τ} {O : _} [CommRing O] [ValuativeArc O] {x x' :
  ThetaObject X (Spec ⟨O⟩)} {Y : PeriodMap D g ℓ V} {Y' : PeriodMap D g' ℓ' V'}
  (z : GL D.Index E) (hz : ratConj z ℓ = ℓ') (m : x.TorusModel Y) (m' : x'.TorusModel Y')

attribute [local simp] PeriodMap.intAction riemannForm_pullForm polarisationForm star_mulVec
  dotProduct_mulVec π ext_iff₂

/-- Let x, x' be modelled on frames g, g' by π, π'. If ψ: x → x' satisfies ψπ = π'z for z in
GL_n(E), then on the torsion points given by the models ψ acts by the adelic matrix g'⁻¹zg. -/
lemma torsionPoint_comp {z ψ} (h : ∀ w, m.π w ≫ ψ = m'.π (realVecAction z.1 w)) y :
  m.fullStructure.torsionPoint (torsionClass y) ≫ ψ = m'.fullStructure.torsionPoint (torsionClass
  ((g'⁻¹ * toFinGL z * g).1 *ᵥ y)) :=
  denseRange_frameCoords (g := g).induction_on y ⟨IsLocallyConstant.comp₂
  isOpen_preimage_torsionClass (.comp_continuous isOpen_preimage_torsionClass (by fun_prop))
  (m.fullStructure.torsionPoint · ≫ ψ = m'.fullStructure.torsionPoint ·) Not⟩ (by
  simpa [← torsionPoint_frameTorsionClass, frameTorsionClass_apply, frameCoords, LinearMap.compLeft,
    comp_def, RingHom.map_mulVec] using h <| toRealVectors ·)

/-- Let π, π' model x, x' on (g, ℓ), (g', ℓ') over an arc. An O_E-linear ψ: x → x' with ψ*[N'] =
μ[N], μ ≠ 0, comes from z in GL_n(E): ψπ = π'z, zℓz⁻¹ = ℓ', z multiplying the Riemann form
by μ. -/
lemma exists_matrix_of_hom ψ [hψ : IsLinear ψ] {μ : ℕ} (hμ : μ ≠ 0) (H : x'.lineBundle.picClass.pull
    ψ.left = μ • x.lineBundle.picClass) : ∃ z : GL D.Index E,
  (∀ w, m.π w ≫ ψ = m'.π (realVecAction z w)) ∧ (∀ y w, μ * polarisationForm D
  Y.β y w = polarisationForm D (z.1ᴴ * Y'.β * z) y w) ∧ ratConj z ℓ = ℓ' := by
  have ⟨F, hF⟩ := m'.uniformisation.universal ((IsAddMonHom.addMonoidHom ψ _).comp _)
    ((m.uniformisation.immersive 0).1.comp_hom _)
  have R := (m.hasThetaCoords.pow μ).riemannForm_eq_of_isFrame (m'.hasThetaCoords.pull _
    (congr(_ ≫ $(hF ·).1)) (by simp_all)) (picClass_eq_iff.1 (by aesop)).choose_spec
  choose f _ v using fun y ↦ (exists_nsmul_adelicTorsion_eq_zero
    (frameTorsionClass g y)).choose_spec |> (Y'.nsmul_mem_latticeOver ·.1 (S := ⊥)
    (u := F (Y.Q (toRealVectors y))) |>.1 (by simp [← m'.lattice_eq,
    ← torsionPoint_frameTorsionClass, ← nsmul_comp, ← map_nsmul m.fullStructure.torsionPoint, *]))
  have L c : F ∘L Y.intAction c = Y'.intAction c ∘L F :=
    m'.uniformisation.linear_ext (by simp [equivariant, *])
  simp [DFunLike.ext_iff, reindex_equiv Y.Q, ← Y'.Q.eq_symm_apply] at L v hF
  have ⟨z, h⟩ : ∃ z, ∀ w, F (Y.Q w) = Y'.Q (realVecAction z w) :=
    ⟨toMatrix' (.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E (by use! f <;> simp [*,
    ← toRealVectors_injective.eq_iff])), denseRange_toRealVectors.eq⟩
  obtain ⟨z, rfl⟩ := z.mulVec_injective_iff_isUnit.1 fun a b k ↦
    toRealVectors_injective (Y.Q.injective (sub_eq_zero.1
    ((R.1 ▸ (Y.isPosRiemann.nsmul hμ).nondegenerate (L := Y.periodLattice)).1 _ (by simp [*]))))
  use z, ?_, ?_, Y.isPeriodMap.ratConj_eq Y'.isPeriodMap F h <;> simp_all [↓← Y.riemannForm_eq,
    Y'.riemannForm_eq, ↓map_conjTranspose_mul_mul]

include hz

/-- For models π, π' of x, x' on (g, ℓ), (g', ℓ'): if zℓz⁻¹ = ℓ' and k = g'⁻¹zg is integral, kᴴk
∈ μẐ^×, then an O_E-linear isogeny ψ has ψ*[N'] = μ[N], ψπ = π'z, acts by k on torsion;
structure maps agree. -/
lemma exists_isogeny {k} {μ : ℕ} (hk : g'⁻¹ * toFinGL z * g = k) (hi : ∀ i j, k i j ∈ Ô E) (hμ :
  IsScalarFrame k⁻¹ μ) : x'.baseHom = x.baseHom ∧ ∃ ψ, IsIsogeny ψ ∧ IsLinear ψ ∧
  x'.lineBundle.picClass.pull ψ.left = μ • x.lineBundle.picClass ∧
  (∀ y, m.fullStructure.torsionPoint (torsionClass y) ≫ ψ = m'.fullStructure.torsionPoint
  (torsionClass (k *ᵥ y))) ∧ ∀ w, m.π w ≫ ψ = m'.π (realVecAction z w) := by
  obtain ⟨_, S, rfl⟩ := (z.map _).mul_inv_eq_iff_eq_mul.1 hz, Y.Q.surjective, hk
  let F : V →L[ℂ] V' := {Y.Q.arrowCongr Y'.Q (realVecAction z.1).toContinuousLinearMap with
    map_smul' a := by simp_all [↓S.forall, ← Y'.Q.symm.injective.eq_iff, smul_re_im a,
      ← PeriodMap.isPeriodMap _ _, funext_iff]}
  -- L: F maps the lattice into the lattice; R: F multiplies the Riemann form by μ
  have ⟨ψ, a, G, c⟩ := (fun L R ↦ have P := m'.hasThetaCoords.pull F (fun _ ↦ .symm (comp_id _)) L
    exists_hom_of_hasThetaCoords (s' := m'.uniformisation.expMap.comp F) _ m.hasThetaCoords
      (by simp_all) x.obj_isThetaStructure.4 (by grind [exists_isTranslationLift_of_dualLattice])
      x'.isProjEmbedding x.isProjEmbedding x.hasClassLaws.1 x'.hasClassLaws.1 ⟨P.1,
      m.hasThetaCoords.2.nsmul μ, (P.2.of_riemannForm_eq (m.hasThetaCoords.2.nsmul μ) R
      (by simp_all [multiplier_eq_canonicalMultiplier, canonicalMultiplier, mul_left_comm, S.forall,
      F, ← Complex.exp_nat_mul, ← mulVec_smul]) <| P.3 ·), (F · |> m'.hasThetaCoords.4
    |>.smul (by simp))⟩) (by simpa [lattice_eq, F, frameLattice, mem_classLattice] using
    (realVecAction_mem_frameLattice hi (P := ·))) (by simp [F, S.forall, PeriodMap.riemannForm_eq,
    ← map_conjTranspose_mul_mul, vecMul_smul, Matrix.map_smul', Finset.mul_sum,
    Y.isSignedFrameFor.conj_eq_smul Y'.isSignedFrameFor hμ]; grind)
  use RingHom.ext (IsFractionRing.injective O ℂ <| m.baseHom_eq · ▸ m'.baseHom_eq _), ψ,
    finite_flat_of_quasiFinite _ (locallyQuasiFinite_of_pull_picClass x.isProjEmbedding (by aesop)
    c) ((isSeparatingFamily_atGeneric m'.uniformisation.surjective).2.surjective _
    (atGeneric m.π ∘ realVecAction z⁻¹ ∘ Y'.Q.symm) ?_), ⟨fun c ↦ (isSeparatingFamily_atGeneric
    (m.uniformisation.surjective.comp S)).hom_ext ?_⟩, c, m.torsionPoint_comp m' ?_ <;>
    simp [← assoc (m.uniformisation.expMap _), ← equivariant, atGeneric, ← Over.comp_left, F, *]

end ThetaObject.TorusModel

/-- A family of theta tori with fixed frame g over a domain U in ℂ^(n−1): periods analytic, with
differential injective modulo ℂ-linear maps; β and B(Q·, ·) constant; Re B positive
definite. -/
structure AnalyticFamily (D : PEL E) where
  U : TopologicalSpace.Opens (BallBase D.Index)
  isConnected : _root_.IsConnected U.1
  (frame) reflection : _ → _
  torus b : ThetaTorus D frame (reflection b) (BallFibre E D.Index)
  analyticAt : ∀ b₀ ∈ U, ∀ w, AnalyticAt ℂ (torus · |>.Q w) b₀
  eq_zero_of_linear : ∀ b ∈ U, ∀ v, let d y := fderiv ℂ (torus · |>.Q ((torus b).Q.symm y)) b v
    (∀ y, d (Complex.I • y) = Complex.I • d y) → v = 0
  form_const b' b : (torus b).β = (torus b').β ∧ ∀ w, (torus b).B ((torus b).Q w) =
    (torus b').B ((torus b').Q w)
  re_pos b : ∀ u ≠ 0, 0 < ((torus b).B u u).re

attribute [local fun_prop] ContinuousLinearMap.analyticAt analyticAt_fst analyticAt_snd

/-- For an analytic family f of theta tori and b₀ in its domain, some scalar function c(b),
non-zero near b₀, makes each theta coordinate c(b)·θ_t(b, z) jointly analytic in (b, z) at
every point (b₀, z). -/
lemma AnalyticFamily.exists_analytic_thetaCoord (f : AnalyticFamily D) {b₀} (h₀ : b₀ ∈ f.U) : ∃ c :
  _ → ℂ, (∀ z t, AnalyticAt ℂ (fun p ↦ (c p.1 • ((f.torus p.1).thetaCoord · p.2)) t) (b₀, z)) ∧ ∀ᶠ
  b in nhds b₀, IsUnit (c b) := by
  let Q b := (f.torus b₀).Q.symm.trans (f.torus b).Q
  choose _ _ S _ w hz using
    (f.torus · |>.isAppellHumbert_latticeOver_lagrangian.poincareSeries_spec <| f.re_pos _)
  choose c hc using fun b ↦ ((PeriodMap.exists_thetaSpace_lagrangian_le_span _).2.2 ⟨_,
    S b (Q b (w b₀))⟩).imp fun _ ↦ congrArg (·.1)
  have a w (z : BallFibre E D.Index) := (f.analyticAt (_, z).1 h₀ w).comp analyticAt_fst
  have hφ z := (((f.torus b₀).isAppellHumbert_latticeOver_lagrangian.summable_and_analyticAt_tsum
    (T := (Q ·)) ((f.U.2.eventually_mem h₀).mono (by solve_by_elim [Q, analyticAt]))
    (by simp_all [Q, re_pos]) _).2.comp (x := (_, z)) (f := fun p ↦ (p.1, (f.torus b₀).B (w b₀), p.2
    - Q _ (w b₀), p.2)) (by simp [Q]; fun_prop)).congr (.of_forall fun p ↦ (tsum_congr (by simp [Q,
    IsAppellHumbert.poincareTerm, f.form_const b₀, canonicalMultiplier, PeriodMap.intAction,
    PeriodMap.riemannForm_eq, mem_classLattice])).trans ((((Q p.1).subtypeEquiv (by simp [Q,
    mem_classLattice, ContinuousLinearEquiv.eq_symm_apply])).tsum_eq _).trans congr($(hc p.1)
    p.2).symm))
  use c, fun _ _ ↦ ?_, ((hφ _).curry_left.continuousAt.eventually_ne
    (by simpa [hc, Q] using hz _)).mono (by aesop)
  simp [PeriodMap.thetaCoord, normalizedShift, PeriodMap.torsionLift, thetaShift, f.form_const b₀,
    canonicalMultiplier, PeriodMap.intAction, PeriodMap.riemannForm_eq, mul_left_comm (c _)]
  refine .mul ?_ (.mul ?_ ((hφ _).comp₂ analyticAt_fst (.add ?_ (a ..)))) <;> fun_prop

/-- Let y be an object over a valuation ring O with fraction field ℂ and x its generic fibre. A
model of x on (g, ℓ) gives a model of y on (g, ℓ) whose sections π'(w) restrict to π(w) at
the generic point.

Known result: Homomorphisms and line bundles of abelian schemes extend from the generic fibre. -/
lemma ThetaObject.TorusModel.exists_model_over_arc {E V} [Field E] [CMBase E] [FinComplexSpace V]
  {D : PEL E} {g ℓ Z τ O} {X : ThetaFamily D Z τ} [CommRing O] [ValuativeArc O] {y x : ThetaObject X
  _} {Y : PeriodMap D g ℓ V} (m : x.TorusModel Y) (h : x.IsPullbackAlong (@genericPt O _ _) y) :
  ∃ m' : y.TorusModel Y, ∀ w, genericPt ≫ (m'.π w).left = (m.π w).left ≫ h.schemeMap.left := by
  let j := LinearEquiv.ofBijective h.isGroupBaseChange.pullSection
    (h.isGroupBaseChange.pointEquiv.symm.bijective.comp bijective_restrict_genericPt)
  have E w : atGeneric (j.symm ∘ m.uniformisation.expMap) w = _ :=
    h.isGroupBaseChange.pullSection_comp _ ▸ congr($(j.4 _).1 ≫ _)
  refine ⟨⟨((@genericPt_eq O .. ▸ h).baseHom_eq_comp ▸ m.baseHom_eq :),
    ⟨.comp j.symm m.uniformisation.expMap, _, by simpa using m.uniformisation.surjective, ?_,
    _root_.funext E ▸ m.uniformisation.immersive_of_isPullback h.isGroupBaseChange.1, fun γ k ↦
    (k.exists_isHomogCoords y.isProjEmbedding.1).elim fun _ ⟨a, b⟩ ↦
    (m.uniformisation.universal (.comp j γ) (.of_isHomogCoords x.isProjEmbedding a (b.mono fun _ c ↦
    h.lineBundle_eq_pull ▸ .pull_iff.2 (h.isGroupBaseChange.pullSection_comp _ ▸ c)))).imp ?_⟩, _,
    _, by simpa [_root_.funext E] using {h.lineBundle_eq_pull ▸ m.hasThetaCoords with
    isLinearSystem := y.isProjEmbedding.1}, ?_, (j.eq_symm_apply.2 <| h.levelPoints_eq_pullSection
    _ ▸ m.level_eq ·), m.lattice_eq⟩, E ∘' _⟩ <;> simp_all [equivariant]
