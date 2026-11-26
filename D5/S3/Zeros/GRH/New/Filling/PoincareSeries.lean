/- GID: D5/S3/Zeros/GRH/New/Filling/PoincareSeries
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/PoincareSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.PoincareSeries. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/PoincareSeries.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.DiscreteSeries.BesselExistence
import D5.S3.Zeros.GRH.New.Filling.AmplitudeSums
import D5.S3.Zeros.GRH.New.Seesaw.GradingsOfY
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: dictionaries between two encodings of the same objects.

Also holds known results stated on this proof's data: Poincaré series along a Bessel subgroup,
unfolding; unipotent strong approximation (known result; see Lib.Adelic.Poincare.BesselSubgroup).

This file: Poincaré series from cut-off Bessel function: convergence, being a form, unfolding, inner
products. -/

noncomputable section

open MeasureTheory Matrix Complex Subgroup Finset PiLp

namespace Filling

variable {E 𝔰 ε} [Field E] [CMType E] [p : Frame 𝔰 ε] (S : Filling E 𝔰) (V :
  Space E _ ε)

/-- V fits S: the Bessel systems have types (l v, kw v), `typeKernel` l is an idempotent
kernel, Y is
standardly indexed, η is central in U(X₀)(𝔸_f), and x_f = idele × η × lattice basis ×
integral matrix ≡ 1 at the chosen places. -/
structure Fits (l kw : _ → _) (Y : Grading V S.N _ _) (η : Gf E 𝔰.κ) where
  isBessel v : IsBessel (S.besselSys v) (l v) (kw v)
  index_eq : Y.indexEquiv = 𝔰.besselIndexEquiv
  isIdempotentKernel : IsIdempotentKernel (typeKernel l ε)
  point_eq : ∃ k, (∀ i (w : S.chosenPlaces i), intGL.map (reduceAt w) k = 1) ∧
    ∃ u : (𝔸f E)ˣ, V.xFin = u • (toBesselH _ ↑S.N η).1 * S.latBasis * k.1
  central a : Commute η a

/-- The principal level at the chosen places above g, as an open subgroup of the finite adelic
unitary group in orthonormal local bases. -/
def stdPrincipalLevel : OpenSubgroup (Gf E 𝔰.BesselIndex) :=
  ⟨levelOf (·.2 : Sigma (S.chosenPlaces ·) → _) ⊥, isOpen_levelOf⟩

namespace Fits

variable {S V l kw Y η} (X : S.Fits V l kw Y η) (a a' : S.Classes × S.BesselCoord)
  (φ : EuclideanSpace ℂ (S.Classes × S.BesselCoord)) (g : _root_.G E ε)
attribute [local simp] mul_assoc termPosition Set.subset_def map_splitGram_ratMiddle

include X in lemma J_eq_ratGram : V.J = S.ratGram := by simp [Y.2, X.index_eq, ← ext_iff,
  gradedGram, Shape.besselIndexEquiv, splitGram, middleGram, Fin.rev]; lia

/-- The isomorphism from the rational points of the unitary group of S onto the discrete
subgroup Γ of V, given by `Space.ratEmbed`. -/
def ratEquiv : S.G E ≃* V.Γ :=
  .trans (.subgroupCongr (X.J_eq_ratGram ▸ rfl)) (V.ratEmbed.ofInjective V.ratEmbed_injective)

/-- The isomorphism, given by the point of V, from the standard adelic group of signs ε onto the
adelic points of the unitary group of S. -/
def adelicEquiv : _root_.G E ε ≃* S.G (𝔸 E) :=
  V.toRatCoords.trans (.subgroupCongr (by simp [X.J_eq_ratGram]))

lemma adelicEquiv_ratEquiv γ : X.adelicEquiv (X.ratEquiv γ) =
  S.ratToAdelic γ := by erw [V.toRatCoords.trans_apply, V.toRatCoords.apply_symm_apply]; rfl

/-- The homeomorphism from G_∞ onto ∏_v G₁, g_v ↦ d_v⁻¹x_v g_v p⁻¹, with x the point of V, d_v =
`Filling.basisScaleGL` v and p the fixed frame `Frame`. -/
def realHomeo := Homeomorph.piCongrRight fun v ↦ frameEquiv.symm.toHomeomorph.trans
  (.mulLeft ⟨_ * .map (evalInf v) V.x * _, gram_mul_of_gram_eq
  (gram_mul_of_gram_eq (gram_inv_of_gram_eq (S.gram_basisScaleGL v)) (by simpa [X.J_eq_ratGram,
  stdForm] using! congr((map $V.gram_point (evalInf v))))) (gram_inv_of_gram_eq p.gram_eq)⟩)

lemma realHomeo_mul g' : X.realHomeo (g * g').1 =
  S.adelicToInf (X.adelicEquiv g) * X.realHomeo g'.1 := by
  ext : 2; show _ * (_ * _) = _ * (_ * (_ * _))
  simp [adelicToInf, adelicEquiv, U.map, U.conj, Space.toRatCoords]; rfl

/-- The isomorphism g ↦ η⁻¹(x_f g x_f⁻¹)η from the standard finite adelic unitary group onto
that of S, written in the lattice basis; x_f is the finite point of V. -/
def finiteEquiv : Gf E 𝔰.BesselIndex ≃* S.GFin := (U.conj _ (by simpa [X.J_eq_ratGram] using
  V.gram_xFin)).trans (S.toLatBasis.trans (MulAut.conj (S.inclHFin η)⁻¹))

lemma finiteEquiv_eq_adelicToFin : X.finiteEquiv g.2 =
  (S.inclHFin η)⁻¹ * S.adelicToFin (X.adelicEquiv g) * S.inclHFin η := by
  simp [finiteEquiv, adelicToFin]; ext : 2; use V.ratCoordMatrixFin_snd _

lemma reduction_finiteEquiv_iff k s : (∃ h, S.reduction ⟨X.finiteEquiv k, h⟩ = s) ↔ ∃ h,
  Kf.reduceFamily _ ⟨k, h⟩ = Sigma.uncurry s := by
  have ⟨l, a, u, e⟩ := X.point_eq
  have e : (X.finiteEquiv k).1 =
    l * k * l⁻¹ := by simp [finiteEquiv, inclHFin, Filling.toLatBasis, U.conj, e, Units.ext_iff]
  simp_rw [funext_iff, Sigma.forall]; congr! 1; exact (e ▸ le_normalizer l.2 _).symm
  congr! 1; congr!
  exact congr(intGL.map _ $((Subtype.ext e : _ = l * ⟨_, _⟩ * _))).trans (by simp [a]; rfl)

lemma mem_stdPrincipalLevel_iff {k} : k ∈ S.stdPrincipalLevel ↔ X.finiteEquiv k ∈
  S.principalLevel := mem_levelOf.trans (by simp [principalLevel, reduction_finiteEquiv_iff])

/-- For a = (c, i), the function of adelic g equal to β_c(g_∞) W_i(g_∞) if f⁻¹(h_c⁻¹η) g_f lies
in the level `Filling.stdPrincipalLevel`, and 0 otherwise; f = `Filling.Fits.finiteEquiv`. -/
def cutBessel := if X.finiteEquiv.symm ((S.h a.1)⁻¹ * S.inclHFin η) * g.2 ∈ S.stdPrincipalLevel then
  (S.classCutoff a.1 (X.realHomeo g.1)).toReal • S.besselFn (X.realHomeo g.1) a.2 else 0

lemma cutBessel_ratEquiv_mul γ : X.cutBessel a
  (X.ratEquiv γ * g) = let y := S.ratToInf γ * X.realHomeo g.1; if (S.h a.1)⁻¹ * (S.ratToFin γ *
    (S.inclHFin η * X.finiteEquiv g.2)) ∈ S.principalLevel then (S.classCutoff a.1 y).toReal •
    S.besselFn y a.2 else 0 := by simp [cutBessel, X.mem_stdPrincipalLevel_iff,
  finiteEquiv_eq_adelicToFin, ↓realHomeo_mul, adelicEquiv_ratEquiv, ratToFin, ratToInf]

/-- The Poincaré series of φ over a subgroup Δ (by default Γ): g ↦ ∑_a φ_a ∑_{γ∈Δ}
`Filling.Fits.cutBessel` a (γg), a running over pairs (class, coordinate). -/
@[local simp] def poincare (Δ := V.Γ) g := ∑ a, φ a * ∑' γ : Δ, X.cutBessel a (γ * g)

variable {X} [S.IsAdmissible]

@[fun_prop] lemma measurable_cutBessel [StablyUnram E] : Measurable (X.cutBessel a) :=
  .indicator (by fun_prop) S.stdPrincipalLevel.2.preimage_of_continuous.measurableSet

/-- For a = (c, i) and adelic y, the sum over u ∈ 𝖴_c(g) of the cut-off function of a at uy
equals W_i(y_∞) if h_c⁻¹ η f(y_f) ∈ K(g), and 0 otherwise; f = `Filling.Fits.finiteEquiv`. -/
lemma tsum_cutBessel_classUnip [StablyUnram E] : ∑' u : S.classUnip a.1,
  X.cutBessel a (X.ratEquiv u * g) = if (S.h a.1)⁻¹ * (S.inclHFin η * X.finiteEquiv g.2)
  ∈ S.principalLevel then S.besselFn (X.realHomeo g.1) a.2 else 0 := by
  convert tsum_toReal_smul_of_tsum_eq_one (S.tsum_classCutoff_eq_one _ (X.realHomeo g.1)) _ with u
  simp [cutBessel_ratEquiv_mul, besselFn_mul_of_mem_classUnip,
    ← S.principalLevel.mul_mem_cancel_left u.2.2 (y := _ * (_ * X.finiteEquiv _))]

/-- The sum over γ ∈ Γ of |`cutBessel` a (γg)| is bounded uniformly in g.

Known result: Poincaré series along a Bessel subgroup, unfolding; unipotent strong
approximation. -/
lemma tsum_cutBessel_le [StablyUnram E] :
    ∃ M : NNReal, ∀ g, ∑' γ : V.Γ, ‖X.cutBessel a (γ * g)‖ₑ ≤ M :=
  ((amplitudeAbs_lt_top_and_cut_le .univ a.1 1).1 _).1.imp fun _ h g ↦ by
  choose! δ d using
    @id (∃ γ, (S.h a.1)⁻¹ * (S.ratToFin γ * (S.inclHFin η * X.finiteEquiv g.2)) ∈ S.principalLevel)
  grw [← h (S.ratToInf δ * X.realHomeo g.1), ← ((Equiv.divLeft δ).symm.trans X.ratEquiv.1).tsum_eq,
    ← tsum_subtype_eq_of_support_subset]; gcongr; all_goals simp [cutBessel_ratEquiv_mul, -map_mul,
    besselFn]
  split; grw [← real_smul, enorm_toReal_smul_le]; simp [enorm]; grw [nnnorm_apply_le]; simp
  use fun _ _ e _ _ ↦ (mul_mem (d ⟨_, e⟩) (inv_mem e)).imp (by simp)

/-- Unfolding, under `Filling.IsAdmissible`: for a form y on V and a subgroup Δ ≤ Γ, y times the
Poincaré series of φ over Δ is integrable on Δ∖G, with integral ∑_a φ_a ∫_G
y·`Filling.Fits.cutBessel` a.

Known result: Poincaré series along a Bessel subgroup, unfolding; unipotent strong approximation. -/
lemma integral_poincare [StablyUnram E]
    {Δ q y} (h : Δ ≤ V.Γ) (k : V.IsForm q y) : let F := y * X.poincare φ Δ
  Integrable F Δ.qms ∧ integral Δ.qms F = ∑ a, φ a * ∫ g, y g * X.cutBessel a g :=
  have {a} := inf_eq_right.2 h ▸ integral_quotMeasure_tsum (Γ :=
    _ ⊓ Δ) (k.isBoundedMeasurable.integrable_mul_comp (c := X.cutBessel a)
    ⟨by fun_prop, (lintegral_orbitMeasure_lintegral (by fun_prop)).ge.trans_lt
    (IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal V.quotMeasure (by
    simp_rw [lintegral_count]; apply tsum_cutBessel_le))⟩ id)
  by simp_all [Pi.mul_def, mul_comm (y _), sum_mul, integral_finsetSum, integrable_finsetSum,
    Integrable.const_mul, tsum_mul_right, k.rat_mul, @h _]

/-- The Poincaré series φ ↦ `Filling.Fits.poincare` φ as a linear map into the forms on V of type
`typeKernel` l fixed by the level `Filling.stdPrincipalLevel`. -/
def poincareMap [StablyUnram E] :
    {Q : _ →ₗ[ℂ] levelSpace (V.formRep (typeKernel l ε)) S.stdPrincipalLevel // ∀ φ,
  (Q φ).1.1 = X.poincare φ} := by
  choose _ h using X.tsum_cutBessel_le
  choose y e using fun a ↦ let o := (cosetProdEquiv (S.classUnip a.1)).trans X.ratEquiv.1
    have e g := (o.tsum_eq (X.cutBessel a <| · * g)).symm.trans
      (o.summable_iff.2 (.of_enorm ((h a g).trans_lt (by simp)).ne)).tsum_prod
    (V.exists_form_eq_tsum (ι := Quotient _) X.3 S.stdPrincipalLevel (by fun_prop)
      (by simp_all [cutBessel, ← mul_assoc, mul_mem_cancel_right]) e (by simp) (h a · |>.trans' (by
      grw [← o.tsum_eq, ENNReal.tsum_prod', enorm_tsum_le_tsum_enorm]; rfl))).imp fun _ h g ↦
      (e g).trans (.symm (congr($h g).trans (tsum_congr fun _ ↦ by
      simp [o, tsum_cutBessel_classUnip, realConv, besselFn]
      rw [← funext (X.1 · |>.3 ..), ← integral_fintype_prod_volume_eq_prod]
      split <;> simp [realHomeo]; rfl)))
  use (basisFun ..).constr ℂ y; intro; ext
  simp [e]; erw [Submodule.coe_sum]; simp; rfl

/-- Unfolding. Under `Filling.IsAdmissible`, for coordinate columns a = (c, i), a' = (c', i') and k
in K₀ with reduction s, the Petersson product ⟨k𝒫a', 𝒫a⟩ is the volume of
`Filling.stdPrincipalLevel` times entry (i, i') of the amplitude sum over all rational terms over
(c, s, c'). -/
lemma petersson_poincare [StablyUnram E] {k s} (hs : Kf.reduceFamily _ k = Sigma.uncurry s) :
  inner ℂ (V.formRep _ k (X.poincareMap.1 (.single a' 1)).1) (X.poincareMap.1 (.single a 1)) =
  volume.real S.stdPrincipalLevel.carrier * S.amplitudeSum .univ a.1 s a'.1 (a.2, a'.2) :=
  ((X.poincareMap.2 _).symm ▸
  (integral_poincare _ le_rfl ((X.poincareMap.1 _).1.2.comp_mul_right k).conj).2 :).trans (by
  erw [tsum_integral_apply (by fun_prop)
    (by grw [enorm_toReal_smul_le]; use ((amplitudeAbs_lt_top_and_cut_le ..).1 _).2)]
  simp [X.poincareMap.2, ← ((Equiv.inv _).trans X.ratEquiv.1).tsum_eq, conj_tsum,
    cutBessel_ratEquiv_mul, -map_inv]
  rw [mul_comm, ← integral_indicator_one S.stdPrincipalLevel.2.measurableSet,
    ← integral_complex_ofReal, ← integral_mul_left_eq_self _
    (X.finiteEquiv.symm ((S.h a.1)⁻¹ * S.inclHFin η)), ← ((volume_preserving_pi
    fun _ ↦ measurePreserving_frameEquiv.comp (measurePreserving_mul_left ..)).symm
    X.realHomeo.symm.toMeasurableEquiv).integral_comp', ← integral_prod_mul]
  congr with g; simp [cutBessel, Set.indicator, X.mem_stdPrincipalLevel_iff,
    ← tsum_mul_right]; split <;> simp
  obtain ⟨⟨m, _⟩, n, _⟩ := ‹_›, (X.reduction_finiteEquiv_iff ..).2 ⟨_, hs⟩
  rw [← tsum_subtype_eq_of_support_subset]; congr with γ
  rw [ite_eq_left (.imp' (·⁻¹ * m * ⟨_, n⟩) (by simp_all) γ.2.2)]; simp [besselKernel]; ring
  simp; intros; refine .imp' (m * ⟨_, n⟩ * ·⁻¹) ?_ ‹_ ∈ S.principalLevel›; simp_all)
