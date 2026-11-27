/- GID: D5/S3/Zeros/GRH/Lib/General/Measure/Place
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Measure/Place
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Measure.Place. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Measure/Place.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Measure.HaarModulus
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Bruhat.EichlerMaps
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of measure and integration (textbook or folklore).

This file: Leray measures on hermitian quadrics disintegrate volume, uniquely, over an axiomatised
place (`Place`). -/


/-- A choice of an element τ with τ + τ̄ = 1 in a commutative ring with involution. -/
class TraceOne A [CommRing A] [StarRing A] where (τ : A) (tau_add_star : τ + star τ = 1)

instance {A} [Field A] [CharZero A] [StarRing A] : TraceOne A := ⟨2⁻¹, by norm_num⟩

open Matrix MeasureTheory Measure ENNReal Sum Ring Units Function Set TraceOne
variable (A : Type) [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A]

/-- A place: a locally compact Polish commutative ring with involution and Haar measure, with τ
+ τ̄ = 1, a skew unit δ, a Haar measure ν on skew elements, a modulus md, a unitary
character ψ and a Plancherel constant c. -/
class Place extends IsTopologicalRing A, ContinuousStar A, LocallyCompactSpace A, PolishSpace A,
    BorelSpace A, (@volume A _).IsAddHaarMeasure, TraceOne A where
  (skewUnit : Aˣ) (skewMeasure : Measure (skewAdjoint A)) (md : A →* ℝ≥0∞) (ψ : AddChar A ℂ) (c)
  [haar : IsAddHaarMeasure skewMeasure] (continuous_psi : Continuous ψ) (measurable_md :
    Measurable md) star_skewUnit : star skewUnit.1 = -skewUnit
  measurePreserving_split :
    MeasurePreserving (fun p ↦ τ * skewUnit⁻¹ * p.1 + p.2) (skewMeasure.prod skewMeasure)
  md_star_and_neg x : md (star x) = md x ∧ md (-x) = md x
  map_mulVec_volume (n : Type) [Fintype n] (M : Matrix n n A) : IsUnit M.det →
    volume.map (M *ᵥ ·) = (md M.det)⁻¹ • volume
  ae_isUnit : ∀ᵐ t : A, IsUnit t
  exists_locallyIntegrable_bound : ∃ g : A → ℝ, LocallyIntegrable g ∧ ∀ u : Aˣ,
    (md u)⁻¹ ≤ ‖g u‖ₑ ^ 2
  norm_psi x : ‖ψ x‖ = 1
  exists_plancherel_kernel : ∃ G : A → ℝ, Continuous G ∧ Integrable G ∧ 0 ≤ G ∧ G 0 = 1 ∧
    ∫⁻ z, ‖∫ v, G v * ψ (star v * z)‖ₑ ≤ c

section

variable {A} [IsTopologicalRing A] [ContinuousStar A] [PolishSpace A]

/-- The skew element x − x̄ attached to x. -/
abbrev skewPart (x : A) : skewAdjoint A := ⟨x - star x, by simp [skewAdjoint]⟩

instance isClosed_skewAdjoint : IsClosed (skewAdjoint A : Set A) :=
  isClosed_eq (by fun_prop) continuous_neg

instance : PolishSpace (skewAdjoint A) := isClosed_skewAdjoint.polishSpace

instance [LocallyCompactSpace A] : LocallyCompactSpace (skewAdjoint A) :=
  isClosed_skewAdjoint.locallyCompactSpace

end

variable {A} [P : Place A] {ι : Type} [Fintype ι] (u : Aˣ) (T : Matrix ι ι A) (b : skewAdjoint A)
  (μ : Measure (ι → A)) {Z κ} [MeasurableSpace Z] {ζ : Measure Z} [Fintype κ]

lemma measurableEmbedding_units_val : MeasurableEmbedding (@val A _) :=
  continuous_val.measurableEmbedding val_injective

@[fun_prop] lemma measurable_inverse : Measurable (@inverse A _) :=
  measurableEmbedding_units_val.measurable_extend continuous_coe_inv.measurable (by simp)

lemma lintegral_eq_mul_lintegral_map {f c g} (h : ζ.map f = c⁻¹ • ζ) (n : c ≠ 0 ∧ c ≠ ∞) :
    lintegral ζ g = c * lintegral (ζ.map f) g := by simp [*, ENNReal.mul_inv_cancel_left]

lemma lintegral_congr_of_ae_imp {p : Z → _} {f g} (h : ∀ᵐ x ∂ζ, p x) (k : ∀ x, p x → f x = g x) :
    lintegral ζ f = lintegral ζ g := lintegral_congr_ae (h.mono k)

lemma lintegral_le_of_ae_imp {p : Z → _} {f g} (h : ∀ᵐ x ∂ζ, p x) (k : ∀ x, p x → f x ≤ g x) :
    lintegral ζ f ≤ lintegral ζ g := lintegral_mono_ae (h.mono k)

omit [MeasureSpace A] [Place A] in
/-- Let F ≥ 0 be jointly continuous in a skew element x of A and y in Z, vanishing for y outside
a compact set k, and ζ finite on compact sets. Then x ↦ ∫ F(x, y) dζ(y) is finite and
continuous. -/
lemma continuous_lintegral_and_lt_top [TopologicalSpace Z] [T2Space Z] [BorelSpace Z]
  [IsFiniteMeasureOnCompacts ζ] {k} {F : skewAdjoint A → Z → NNReal} (h : IsCompact k) (c :
  Continuous ↿F) (s : ∀ x y, F x y ≠ 0 → y ∈ k) : Continuous (∫⁻ y, F · y ∂ζ) ∧ ∀ x, ∫⁻ y, F x y ∂ζ
  < ∞ := by simpa [fun x ↦ lintegral_coe_eq_integral (μ := ζ) (F x) (HasCompactSupport.integrable
  (.intro h (mod_cast by grind)))] using! continuous_ofReal.comp (continuousOn_univ.1
  (continuousOn_integral_of_compact_support h (by fun_prop) (mod_cast by grind)))

/-- For a place A and finite index sets ι, κ, joining two vectors is a volume-preserving map
from A^ι × A^κ to A^(ι ⊔ κ). -/
lemma measurePreserving_sumElim : MeasurePreserving fun p : (ι → A) × (κ → A) ↦ p.1 ⊕ᵥ p.2 :=
  volume_measurePreserving_sumPiEquivProdPi_symm fun _ ↦ A

@[fun_prop] lemma measurable_sumElim_pair : Measurable fun p : (ι → A) × (κ → A) ↦ p.1 ⊕ᵥ p.2 :=
  measurePreserving_sumElim.1

lemma measurePreserving_pair_sumElim : MeasurePreserving fun r :
  A × A × (ι → A) ↦ ![r.1, r.2.1] ⊕ᵥ r.2.2 := (measurePreserving_sumElim.comp
  ((volume_preserving_finTwoArrow A).symm.prod (.id _))).comp volume_preserving_prodAssoc.symm

/-- The Gram matrix of a hyperbolic plane plus the form T: block diagonal with blocks (0 1; 1 0)
and T. -/
abbrev planeSumGram := fromBlocks !![0, 1; 1, 0] 0 0 T

instance : BorelSpace (U T) := inferInstance

namespace Place

attribute [instance] haar

instance : SigmaFinite P.skewMeasure := inferInstance

attribute [simp] norm_psi md_star_and_neg

attribute [fun_prop] continuous_psi measurable_md

attribute [simp, grind! .] tau_add_star

attribute [local grind! .] inverse_mul_cancel star_form inv_mul

/-- Flat chart of the quadric h(v, v) = Γ := δ⁻¹b in a hyperbolic plane e, e' plus T: (t, w,
a) ↦ (t̄⁻¹τ(Γ − h(w, w)) + ta)e + te' + w, a skew. -/
noncomputable def flatChart : (A × (ι → A)) × skewAdjoint A → Fin 2 ⊕ ι → A
  | ((t, w), a) => ![(star t)⁻¹ʳ * τ * (skewUnit⁻¹.1 * b - star w ⬝ᵥ T *ᵥ w) + t * a, t] ⊕ᵥ w

/-- The measure δ_Γ on the quadric h(v, v) = Γ: the image of dt dw dν(a) under the flat chart
`Place.flatChart`. -/
noncomputable abbrev quadricMeasure := (volume.prod skewMeasure).map (flatChart T b)

/-- The measures l_β (β skew) disintegrate μ along h(x, x) = x*Jx: finite on compact sets,
weakly continuous in β, ∫ f(h(x, x), x) dμ = ∬ f(δ⁻¹β, x) dl_β dν(β) for measurable f ≥ 0. -/
structure IsDisintegration J (l : skewAdjoint A → Measure (ι → A)) where
  continuousOn_lintegral {f : _ → NNReal} : Continuous f → HasCompactSupport f →
    Continuous (∫⁻ x, f x ∂l ·) ∧ ∀ b, ∫⁻ x, f x ∂l b < ∞
  lintegral_eq f : Measurable f → ∫⁻ x, f (star x ⬝ᵥ J *ᵥ x, x) ∂μ = ∫⁻ b, ∫⁻ x,
    f (skewUnit⁻¹.1 * b, x) ∂l b ∂skewMeasure

lemma measurePreserving_mulVec (h : star T.det * T.det = 1) : MeasurePreserving (T *ᵥ ·) :=
  ⟨by fun_prop, by simp [map_mulVec_volume, by
                        simpa [toReal_eq_one_iff] using congr((√(md $h).toReal, IsUnit $h))]⟩

variable {T b μ}

@[simp] lemma md_inv : P.md ↑u⁻¹ = (P.md u)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left (u.map _).4

@[simp] lemma md_ne_zero_and_ne_top : P.md u ≠ 0 ∧ P.md u ≠ ∞ := isUnit_iff.1 ⟨u.map _, rfl⟩

lemma map_mul_volume : volume.map (u.1 * ·) = (P.md u)⁻¹ • volume := by
  have e := volume_preserving_funUnique (Fin 1) A
  simpa using!
    ((e.smul_measure _).comp (.comp ⟨by fun_prop, map_mulVec_volume _ !![↑u] (by simp)⟩ e.symm)).2

@[simp] lemma star_skewUnit_inv : star skewUnit⁻¹.1 = -P.skewUnit⁻¹.1 :=
  congrArg inv (ext star_skewUnit : star skewUnit = -_)

/-- For a unit u with ū = u, the image of the Haar measure ν on the skew elements under
multiplication by u (written as the skew projection of τuβ) is md(u)^{−1/2} ν. -/
lemma map_skewMeasure_mul_unit (h : star u.1 = u) : skewMeasure.map (skewPart <| P.τ * u * ·.1) =
  (P.md u ^ (2⁻¹ : ℝ))⁻¹ • skewMeasure := by
  ext; apply rpow_left_injective two_ne_zero; simp [↓mul_pow, ← inv_rpow, ↓← rpow_mul_natCast, sq,
    ← prod_prod]; refine congr($((measurePreserving_split.1.measurableEmbedding fun a b e ↦ by grind
    [by simpa using (star_inj.2 e)]).map_injective
    ((measurePreserving_split.smul_measure (_ : ℝ≥0∞)).2.trans ?_).symm) _)
  simp (disch := with_unfolding_all fun_prop) [map_prod_map, ↓← map_mul_volume,
    ← measurePreserving_split.2, Measure.map_map, comp_def]; grind

@[fun_prop] lemma measurable_flatChart : Measurable fun p : _ × _ ↦ flatChart T p.1 p.2 := by
  fun_prop [flatChart]

/-- For Γ in A with Γ̄ = Γ, the skew element δΓ, where δ is the skew unit of the place. -/
@[simps] def skewUnitMul (Γ : A) (e : star Γ =
  Γ := by apply IsHermitian.apply IsHermUnit.conjTranspose_eq) : skewAdjoint A :=
  ⟨P.skewUnit * Γ, by simp [skewAdjoint, star_skewUnit, e]⟩

lemma form_flatChart (hT : Tᴴ = T) {p} (h : IsUnit p.1.1) :
  star (flatChart T b p) ⬝ᵥ planeSumGram T *ᵥ flatChart T b p =
  skewUnit⁻¹.1 * b := by simp [flatChart, fromBlocks_mulVec, star_sumElim, inverse_star]; grind

/-- Let S be a set of skew elements and u a unit with u(τδ⁻¹β + β') in C for all β, β' in S − S.
If vol(C)/md(u) ≤ x², then ν(S) ≤ x. -/
lemma skewMeasure_le_of_sub_mem {S C x} (h : ∀ p ∈ S ×ˢ S, ∀ q ∈ S ×ˢ S, u * (P.τ * skewUnit⁻¹.1 *
  (p - q).1.1 + (p - q).2.1) ∈ C) (e : (P.md u)⁻¹ * volume C ≤ x ^ 2) : skewMeasure S ≤ x := by
  grw [← ENNReal.pow_le_pow_left_iff, ← ((MeasurePreserving.comp ⟨by fun_prop, map_mul_volume u⟩
    measurePreserving_split).measure_preimage_le C).trans e, sq, ← prod_prod,
    measure_le_of_sub_mem] <;> tauto

lemma IsDisintegration.finite_on_compacts {l} (h : IsDisintegration μ T l) b :
  IsFiniteMeasureOnCompacts (l b) := ⟨fun _ k ↦
  have ⟨_, ⟨⟨_, c⟩, s⟩, o, _⟩ := rieszContentAux_image_nonempty 0 ⟨_, k⟩
  (meas_le_lintegral₀ (by fun_prop) (mod_cast o)).trans_lt ((h.1 c s).2 b)⟩

/-- Two disintegrations l, l' of the same measure μ along the form with matrix T agree at every
skew element b. -/
lemma IsDisintegration.unique {l l'} (h : IsDisintegration μ T l) (k : IsDisintegration μ T l') :
  l b = l' b := have := h.finite_on_compacts; have :=
      k.finite_on_compacts; ext_of_integral_eq_on_compactlySupported_nnreal fun f ↦ by
      obtain ⟨⟨c, -⟩, d, -⟩ := h.1 f.1.2 f.2, k.1 f.1.2 f.2
      repeat erw [← f.toBoundedContinuousFunction.toReal_lintegral_coe_eq_integral]
      exact congr(($(eq_of_ae_eq (ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite c.measurable
        d.measurable (by rintro _ ⟨s, m, rfl⟩ -; simpa (disch := fun_prop) [↓lintegral_mul_const,
        ← lintegral_indicator (measurable_subtype_coe m), indicator] using (fun m ↦ (h.2 (fun (x, y)
        ↦ f y * s.indicator 1 (skewUnit.1 * x)) m ▸ k.2 _ m :)) (by fun_prop))) c d) b).toReal)

lemma IsDisintegration.map {l M} {J : Matrix κ κ A} {L : Matrix ι κ A} (h :
  IsDisintegration μ T l) (hJ : Mᴴ * J * M = T)
  (hL : L * M = 1) : IsDisintegration (μ.map (M *ᵥ ·)) J fun Γ ↦ (l Γ).map (M *ᵥ ·) := by
  have e := LeftInverse.isClosedEmbedding (mulVec_mulVec · L M |>.trans (by simp [*]))
    (by fun_prop) (by fun_prop)
  constructor <;> intros <;> simp [e.measurableEmbedding.lintegral_map, star_mulVec_dotProduct,
    ← Matrix.mul_assoc, -Subtype.forall, *]
  exacts [h.1 (by fun_prop) (.comp_isClosedEmbedding ‹_› e), h.2 (_ ∘ Prod.map id _) (by fun_prop)]

/-- For T hermitian, the flat chart measures δ_Γ form a disintegration of the volume along h(v,
v), for the form made of a hyperbolic pair and T. -/
lemma isDisintegration_quadricMeasure (hT : Tᴴ = T) :
  IsDisintegration volume (planeSumGram T) (quadricMeasure T) := by
  obtain ⟨⟨g, i, e⟩, u : ∀ᵐ p : A × (ι → A), _⟩ := P.exists_locallyIntegrable_bound,
    quasiMeasurePreserving_fst.ae ae_isUnit
  constructor <;> intro f c <;> simp (disch := fun_prop) [lintegral_map, lintegral_prod]
  intro s
  have ⟨r, d⟩ := ENNReal.exists_nat_gt (P.lt_top_of_isCompact (((s.prod s).prod
    (s.prod s)).image_auto fun (x, y) ↦ ((P.τ * skewUnit⁻¹.1) • (x - y).1 + (x - y).2) (inl 0))).ne
  refine have B Γ := u.mono fun p h ↦ ?_; have N := ((lintegral_const_mul' ↑(iSup f) _
    coe_ne_top).trans_lt (mul_lt_top coe_lt_top ((lintegral_indicator_le ..).trans_lt
    (((i.integrableOn_isCompact (s.image_auto (· (inl 1)))).mul_prod ((locallyIntegrable_const
    √r).integrableOn_isCompact (s.image_auto (· ∘ inr)))).mono_measure (prod_restrict
        ..).ge).2))); ⟨.of_at fun _ ↦ tendsto_lintegral_filter_of_dominated_convergence _
        (.of_forall (by fun_prop)) (.of_forall B) N.ne (u.mono fun p h ↦
        (continuous_lintegral_and_lt_top (s.image_auto (skewPart <| star τ * p.1⁻¹ʳ * · (inl 0)))
    (c.comp (continuous_pi (by simp; continuity))) fun _ _ n ↦ ⟨_, subset_closure n, by
    simp [skewPart, flatChart, inverse_star]; grind⟩).1.tendsto _), fun _ _ ↦ N.trans_le'
    (lintegral_mono_ae (B _))⟩
  grw [← setLIntegral_eq_of_support_subset (s := (flatChart T Γ ⟨p, ·⟩) ⁻¹' tsupport f) fun _ h ↦
    subset_closure (by tauto), le_ciSup (s.isCompact_range c).bddAbove, setLIntegral_const]
  exact mul_right_mono (le_indicator_apply (fun _ ↦ skewMeasure_le_of_sub_mem h.unit (fun _ h _ k ↦
    .intro ((_, _), _, _) ⟨⟨h, k⟩, by simp; ring⟩) ((mul_le_mul' (e _) d.le).trans (by
    simp [← enorm_pow, mul_pow]))) fun n ↦ (skewMeasure.mono_null (by aesop) skewMeasure.empty).le)
  erw [lintegral_lintegral_swap, ← measurePreserving_pair_sumElim.lintegral_comp,
    lintegral_prod_symm, lintegral_congr_of_ae_imp u] <;> try fun_prop
  rintro ⟨_, w⟩ ⟨t, rfl⟩
  erw [← lintegral_sub_right_eq_self _ (star t⁻¹ * τ * star w ⬝ᵥ T *ᵥ w),
    lintegral_eq_mul_lintegral_map (map_mul_volume t), lintegral_map,
    ← measurePreserving_split.lintegral_comp, lintegral_prod, lintegral_eq_mul_lintegral_map
    (map_skewMeasure_mul_unit (t⁻¹ * star t⁻¹) (star_mul_star ..)), lintegral_map] <;> first
    | fun_prop | simp [← sq, ← rpow_natCast_mul, ENNReal.mul_inv_cancel_left]
  congr! 5
  grind [form_flatChart, flatChart, inverse_unit]
