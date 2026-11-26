import GRH.Lib.DiscreteSeries.Haar.LogDerivative
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Haar measure of U(J) in Cayley coordinates, volume of U(n), polynomial volume growth
(known result; see Lib.DiscreteSeries.Haar.RegularRepL2).

This file: Cayley chart density gives Haar measure on U(J); area inequality; invariance under
isometries. -/

noncomputable section


open Matrix MeasureTheory Measure Set IsHermInvolution Norms.L2Operator ComplexOrder Fintype Haar
  MatMul

section

variable {n} [Fintype.{0} n] (J J' : Matrix n n ℂ) [IsHermInvolution J] (y : Matrix n n ℝ)

/-- The matrix 1 − ½J⁻¹Y, where Y is the skew-hermitian matrix `skewOfReal` y attached to the real
matrix y; the denominator in Cayley's chart. -/
def cayleyDenom := 1 - (2⁻¹ : ℂ) • (J⁻¹ * skewOfReal y)

attribute [local simp] det_ne_zero inv_smul cayleyDenom Function.comp_def logDerivU InjOn mul_assoc
  subset_def ENNReal.mul_lt_top_iff isUnit_iff_isUnit_det

/-- The Cayley chart: the element of U(J) with matrix (1+X)(1−X)⁻¹, X = ½J⁻¹Y, Y = `skewOfReal` y
skew-hermitian; it is −1 when 1−X is singular. -/
@[simps! -isSimp coe_val] def cayleyChart : U J :=
  U.of isUnit ((2 : ℂ) • (cayleyDenom J y)⁻¹ - 1) <| (cayleyDenom J
  y).nonsing_inv_cancel_or_zero.elim (fun ⟨_, e⟩ ↦ have e := congr((cayleyDenom J y)⁻¹ᴴ * J * $e)
  by have := congr($eᴴ); simp [isHermitian.eq, two_smul] at *; grind) (by aesop)

/-- For J and a real matrix y, the real number (|det J|·|det(1−½J⁻¹S)|²)^(−n), S the
skew-hermitian matrix with coordinates y. -/
abbrev cayleyDensity := ((‖J.det‖ * ‖(cayleyDenom J y).det‖ ^ 2) ^ card n)⁻¹

/-- The number 2π^k r^{k−1}/(k−1)!; for k ≥ 1 the sphere of radius ρ in ℂ^k has area ρ times its
value at r = ρ². -/
@[simp] abbrev sphereDensity k (r : ℝ) := 2 * .pi ^ k / (k - 1).factorial * r ^ (k - 1)

/-- The volume ∏_{i<j} 2π^(i+1)/i! of the compact unitary group U(j). -/
def volU j := ∏ i ∈ .range j, sphereDensity (i + 1) 1

/-- The image under Cayley's chart of Lebesgue measure with density `cayleyDensity` divided by vol
U(n), on the y with det(`cayleyDenom` J y) ≠ 0; for hermitian involutions J, the compact dual
Haar measure. -/
def haarU := ((volume.withDensity (.ofReal <| cayleyDensity J · / volU (card n))).comap (↑)).map
    ({y | (cayleyDenom J y).det ≠ 0}.domRestrict (cayleyChart J))

instance measureSpaceU : MeasureSpace (U J) := ⟨haarU J⟩

@[simp] lemma volU_pos j : 0 < volU j := by delta volU; positivity

@[simp] lemma det_cayleyDenom_one_ne_zero : (cayleyDenom 1 y).det ≠ 0 :=
  IsAccretive.det_ne_zero (by norm_num [IsAccretive, PosDef.ofNat])

section

variable {J J' y} (g : U J) [IsHermInvolution J'] (a b : GL n ℂ) (ε : ℝˣ) (φ : U J ≃ U J')
  (hb : b.1ᴴ * ε • J * b = J' := by aesop) (hφ : ∀ g, (φ g).1 = a * g * b := by simp) {V}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (e : V ≃ₗ[ℝ] Matrix n n ℝ)

@[fun_prop] lemma measurable_cayleyChart : Measurable (cayleyChart J) := by
  simp [measurable_comap_iff, Matrix.inv_def, val_cayleyChart_coe]; fun_prop

omit [IsHermInvolution J] in
@[fun_prop] lemma continuous_cayleyDenom : Continuous (cayleyDenom J) := by fun_prop [cayleyDenom]

/-- Let J be a hermitian involution and S(y) the skew-hermitian matrix with coordinates y. Where
det(1−½J⁻¹S(y)) ≠ 0, the Cayley chart is differentiable and Jg⁻¹dg takes the value X*S(v)X
on a direction v, X = (1−½J⁻¹S(y))⁻¹. -/
lemma logDerivU_cayleyChart (h : (cayleyDenom J y).det ≠ 0) : DifferentiableAtU (cayleyChart J) y ∧
    ∀ v, logDerivU (cayleyChart J) y v =
  (cayleyDenom J y)⁻¹ᴴ * skewOfReal v * (cayleyDenom J y)⁻¹ := by
  have d :=
    ((hasFDerivAt_ringInverse (IsUnit.unit (by simpa))).comp y (((skewOfReal.toContinuousLinearMap
    ).hasFDerivAt.const_mul ((2⁻¹ : ℂ) • J⁻¹)).const_sub 1)).fun_const_smul (2 : ℂ)
  simp [← nonsing_inv_eq_ringInverse,
    ← (inv_smul_eq_iff₀ _).2 (add_eq_of_eq_sub (val_cayleyChart_coe ..))] at *
  simp [d.fderiv, d.differentiableAt, ← mul_assoc, -Matrix.mul_assoc, mem_U.1]; grind

/-- For g in U(J), the real n×n matrix of coordinates of the complex matrix 2J(1−2(g+1)⁻¹). -/
def cayleyChartInv := skewCoords ((2 : ℂ) • (J * (1 - (2 : ℂ) • (g.1.1 + 1)⁻¹)))

lemma cayleyChart_injOn : {y | (cayleyDenom J y).det ≠ 0}.InjOn (cayleyChart J) :=
  .of_comp (g := cayleyChartInv) (by simp_all [cayleyChartInv, val_cayleyChart_coe])

lemma cayleyChart_cayleyChartInv (h : IsUnit (g.1.1 + 1)) :
  (cayleyDenom J (cayleyChartInv g)).det ≠ 0 ∧ cayleyChart J (cayleyChartInv g) = g := by
  obtain _ := h.mul_val_inv, U.gram_invariant g h.unit.2 h.unit.2; erw [Subtype.ext_iff,
    Units.ext_iff, val_cayleyChart_coe, cayleyDenom,
    skewOfReal_skewCoords]; aesop; simp_all [isHermitian.eq, two_smul, ← eq_sub_iff_add_eq]; grind

lemma measurableEmbedding_cayleyChart : MeasurableEmbedding ({y | (cayleyDenom J
  y).det ≠ 0}.domRestrict (cayleyChart J)) := by apply_rules [Measurable.measurableEmbedding,
  MeasurableSet.standardBorel, cayleyChart_injOn.injective] <;> measurability

/-- For a hermitian involution J of size n and any f: U(J) → [0,∞], the integral of f against
`haarU` equals the integral of (`cayleyDensity` divided by vol U(n)) times f∘`cayleyChart`
over the real matrices y with det(`cayleyDenom` J y) ≠ 0.

Known result: Haar measure of U(J) in Cayley coordinates, volume of U(n), polynomial volume
growth. -/
lemma lintegral_eq_cayleyChart f : lintegral volume f = ∫⁻ y in {y | (cayleyDenom J y).det ≠ 0},
  .ofReal (cayleyDensity J
  y / volU (card n)) * f (cayleyChart J y) := by erw [measurableEmbedding_cayleyChart.lintegral_map,
  ← setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable, ← lintegral_subtype_comap] <;>
  measurability

include hb in
lemma cayleyChart_jacobian {y p L} (hy : HasFDerivAt y L p) {Φ : V → U J'} (h : (cayleyDenom J
  (y p)).det ≠ 0) (E : ∀ᶠ q in nhds p, (Φ q).1.1 = a * cayleyChart J (y q) * b := by simp [*]) :
  DifferentiableAtU Φ p ∧ |(e.symm ∘ₗ skewCoords ∘ₗ logDerivU Φ p).det| =
  |(e.symm ∘ₗ L.1).det| * cayleyDensity J (y p) := by
  obtain ⟨⟨d, l⟩, ⟨⟩⟩ := logDerivU_cayleyChart h,
    hb, by simpa using congr(√‖det $(‹IsHermInvolution J'›.2)‖ ^ card n)
  have D := (((d.hasFDerivAt.comp p hy).const_mul _).mul_const' _).congr_of_eventuallyEq E
  use ⟨_, D⟩; rw [(_ : logDerivU .. = _ ∘ₗ skewOfReal ∘ₗ (ε • L).1),
    abs_det_skew_congruence _ (_ * _)]; rotate_right
  ext1; simpa [D.fderiv, ↓← U.form_mul_inv_eq, E.self_of_nhds] using congr(ε • _ * $(l _) * b)
  simp_all [mul_pow, cayleyDensity, pow_mul, pow_two, LinearMap.comp_smul, e.finrank_eq,
    Module.finrank_matrix, ε.smul_def]; grind

/-- For a hermitian involution J and Y the skew-hermitian matrix with coordinates y, if
det(1−½J⁻¹Y) ≠ 0 then Cayley's chart is differentiable at y, and the form Jg⁻¹dg in real
coordinates has absolute determinant (|det J|·|det(1−½J⁻¹Y)|²)^(−n) there. -/
lemma abs_det_logDerivU_cayleyChart (h : (cayleyDenom J y).det ≠ 0) : DifferentiableAtU
  (cayleyChart J) y ∧ |(skewCoords ∘ₗ logDerivU (cayleyChart J) y).det| = cayleyDensity J
  y := by simpa using cayleyChart_jacobian 1 1 1 (by simp) (.refl ..) (hasFDerivAt_id y) h

/-- Let J be a hermitian involution, Φ: V → U(J) injective and differentiable on a measurable A,
with Jacobian w for Jg⁻¹dg in measure preserving coordinates e. For almost every real t and
all f ≥ 0, ∫_A (w(p)/vol U(n)) f(e^{it}Φ(p)) dp ≤ ∫ f d`haarU`. -/
lemma Haar.lintegral_chart_rotate_le [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
    [(@volume V _).IsAddHaarMeasure] (he : MeasurePreserving e) {A} {Φ : V → U J} (hA :
  MeasurableSet A) (hi : A.InjOn Φ) {w : V → ℝ} (hΦ : ∀ p ∈ A, DifferentiableAtU Φ p ∧ |(e.symm ∘ₗ
  skewCoords ∘ₗ logDerivU Φ p).det| = w p) : ∀ᵐ t, ∀ f, ∫⁻ p in A, .ofReal (w p / volU (card n)) * f
  (circleScalar t * Φ p) ≤ lintegral volume f := .mono ((((volume.restrict A).map Φ).ae_ae_comm (by
  measurability)).1 (.of_forall fun x ↦ (((-x.1.1⁻¹).finite_spectrum.countable.preimage_circleMap 0
  one_ne_zero).ae_notMem _).mono fun t h ↦ show IsUnit ((circleScalar t * x :).1.1 + 1) by
  simpa [Algebra.smul_def, circleScalar, circleMap] using (of_not_not h).mul x.1.isUnit)) fun t h
  f ↦ by
  have ⟨O, o, m, h⟩ :=
    ((ae_restrict_mem hA).and (ae_of_ae_map ((isClosedEmbedding_U.continuousOn_iff.2
    (hΦ · · |>.1.continuousAt.continuousWithinAt)).aemeasurable hA) h)).exists_measurable_mem
  have k p u := cayleyChart_cayleyChartInv _ (h p u).2
  have D p u :
    HasFDerivAt (cayleyChartInv <| circleScalar t * Φ ·) _ p := have := (hΦ p (h p u).1).1
    (skewCoords.toContinuousLinearMap.differentiableAt.comp p (by
                    simp [nonsing_inv_eq_ringInverse]; fun_prop (disch := aesop))).hasFDerivAt
  grw [lintegral_eq_cayleyChart, ← he.setLIntegral_comp_preimage_emb (he.1.measurableEmbedding
    e.injective), restrict_mono_ae (s := A) (ae_imp_of_ae_restrict o), setLIntegral_congr_fun m,
    ← lintegral_image_eq_lintegral_abs_det_fderiv_mul _ m (D · · |> (e.symm.toContinuousLinearEquiv
    ).hasFDerivAt.comp _ |>.hasFDerivWithinAt) (.of_comp (g := cayleyChart J ∘ e) (by aesop))]
  gcongr; aesop
  simp +contextual [*, mul_div_assoc, cayleyChart_cayleyChartInv, EqOn,
    (hΦ ..).2 ▸ cayleyChart_jacobian (circleScalar t : U J)⁻¹ 1 1 _ e (D ..) (k ..).1
    (.mono ((((hΦ ..).1.const_mul _).add_const _).continuousAt (h ..).2.unit.nhds) _)]; tauto

include hb hφ

lemma lintegral_comp_le_haarU f : lintegral volume f ≥ ∫⁻ g, f (φ g) := by
  have ⟨t, h, k⟩ := ((lintegral_chart_rotate_le (.refl ..) (.id _) (by measurability)
    (φ.injective.comp_injOn cayleyChart_injOn) (cayleyChart_jacobian a b ε hb _ <|
    hasFDerivAt_id ·)).and ((quasiMeasurePreserving_neg _).ae (lintegral_chart_rotate_le 1 (.id _)
    (by measurability) cayleyChart_injOn (@abs_det_logDerivU_cayleyChart _ _ J' _)))).exists
  simp_all [lintegral_eq_cayleyChart]; convert! (h (f <| _ * ·)).trans (k f)
  ext; simp [circleScalar, Complex.exp_neg]

/-- Let J, J' be hermitian involutions, a, b invertible, ε real nonzero, bᴴ(εJ)b = J'. A bijection
φ: U(J) → U(J') given by g ↦ agb carries the measure `haarU` of U(J) to that of U(J'). -/
lemma measurePreserving_haarU : MeasurePreserving φ := have c := .subtype_mk (by measurability)
  ⟨c, ext_of_lintegral _ fun f h ↦
    lintegral_map h c ▸ (lintegral_comp_le_haarU a b ε φ hb hφ f).antisymm (by
                  simpa using lintegral_comp_le_haarU a⁻¹ b⁻¹ ε⁻¹ φ.symm
                    (gram_inv_of_gram_eq (by aesop)) (by simp_all [↓reindex_equiv φ]) (f ∘ φ))⟩

end

instance : (@volume (U J) _).IsHaarMeasure := by
  have : SigmaFinite (haarU J) := by apply_rules [(measurePreserving_subtype_coe
    _).sigmaFinite, measurableEmbedding_cayleyChart.sigmaFinite_map]; measurability
  have := exists_subset_measure_lt_top .univ (by
    rw [← lintegral_one, @lintegral_eq_cayleyChart _ _ J, setLIntegral_pos_iff, inter_eq_right.2]
    apply continuous_cayleyDenom.matrix_det.isOpen_support.measure_pos _ ⟨0,
      _⟩; repeat measurability)
  have : (haarU J).IsMulLeftInvariant := ⟨(measurePreserving_haarU · 1 1 (.mulLeft _) |>.2)⟩
  rw [haarMeasure_unique volume Classical.ofNonempty] at *; apply IsHaarMeasure.smul <;> aesop
