/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/SectorBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/Character/SectorBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.Character.SectorBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/Character/SectorBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Character.KTypeMultiplicity
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Discrete series character on the compact Cartan by orbital integrals; formal degree
(known result; see Lib.DiscreteSeries.Character.FormalDegree).

This file: Haar measure of U(p,q) as the measure of its open orbit on flags. Weyl's dimension
formula for U(n), as the mean square of the highest coefficient. Lower bound for products of
principal minors of conjugated positive diagonal matrices. -/
seal Finset.univ Finset.sum Finset.prod

open Matrix MeasureTheory Complex ComplexOrder Norms.L2Operator LinearMap Finset U
variable {n} [Fintype n] {o : n → ℤ} (ho : o.Injective) (ε : n → _) {b c}

/-- The set of matrices gb with g in U(diag ε) and b invertible and upper triangular for the
order o. -/
def openOrbit o := {y | ∃ g : USign ε, ∃ b, IsBorelMatrix o b ∧ y = g.1.1 * b}

include ho

lemma IsBorelMatrix.unitary_eq_of_mul_eq {g g' : USign ε} (hb : IsBorelMatrix o b) (hc :
  IsBorelMatrix o c) : g * b = g' * c ∧ (∀ i, 0 < c i i / b i i) → g = g' := by
  obtain ⟨t, rfl⟩ := mul_left_surjective g' g; simp [mul_assoc]; rintro rfl p
  cases (by simpa [hb.2] using hc.mul hb.inv :).exists_eq_diagonal_exp ho; ext : 2
  simpa [funext_iff, hb.diag_ne_zero, *] using (eq_coe_norm_of_nonneg <| p · |>.le)

/-- For o injective, b invertible and upper triangular for o with positive diagonal, J = diag ε,
J' = diag ε': the real map y ↦ co(J·lo(bJ'·sk(y)·b⁻¹)), lo = `lowerLiePart` ε 1 o,
co = `skewCoords`, sk = `skewOfReal`, has |det| = ∏
b_ii^{2r_i}, r_i = #{j : o_j < o_i} − #{j : o_i < o_j}. -/
lemma abs_det_lowerLiePart (h : IsBorelMatrix o b) (p : ∀ i, 0 < b i i) ε' :
  |(skewCoords ∘ₗ mulLeft ℝ (signMatrix ε) ∘ₗ lowerLiePart ε 1 o ∘ₗ mulLeftRight ℝ (b,
  b⁻¹) ∘ₗ mulLeft ℝ (signMatrix ε') ∘ₗ skewOfReal).det| = ‖diagChar (twoRho o ⊤) b‖ ^ 2 := by
  let := LinearOrder.lift' (fun (i, j) ↦ [|o i - o j|, o i, o j]) (by aesop_cat)
  choose d u e using (RCLike.pos_iff_exists_ofReal.1 <| p ·); let x i j := ε i * ε' i * d i / d j
  rw [← det_toMatrix (stdBasis ..)]; show ‖(?T : Matrix (n × n) _ ℝ).det‖ = _
  have z i j (y : Matrix n n ℂ) (H : ∀ k l, o i - o j < o k - o l → y k l = 0) : (b * y * b⁻¹) i j =
      b i i * y i j / b j j := by simp [entrywise, sum_mul, ← sum_product']; rw [sum_eq_single
    (j, i)] <;> grind [h.inv, h.inv_apply_diag, IsBorelMatrix, BlockTriangular]
  have E p q (H : q ≤ p) : ?T p q = ite (p = q) (ite (o p.1 < o p.2) (x p.2 p.1) (x p.1 p.2)) 0 :=
    by simp [toMatrix_apply, stdBasis, lowerLiePart, skewCoords, signMatrix]; split_ifs <;>
    (try lia) <;> (repeat rw [z]) <;> simp [skewOfReal, ← e, ite_apply] <;> grind [ofReal_zero,
    H.imp_right List.head_le_of_lt, abs_unit_intCast (α := ℝ) (ε p.1)]
  rw [det_of_isUpperTriangular fun _ ↦ by grind]; simp [E, ← e, x, sq, diagChar, twoRho, u,
    ne_of_gt, zpow_sub₀, ← prod_const, prod_filter, apply_ite norm, ← prod_div_distrib,
    Fintype.prod_prod_type]; nth_rw 2 [prod_comm]; simp_rw [← prod_mul_distrib]; rcongr; grind

/-- For o injective, B the o-upper-triangular group, G_ε = U(diag ε): G_ε' ∩ G_εB is open in
G_ε'. If real f satisfies f(yb) = |b^{2ρ}|²f(y) (y invertible, b ∈ B, 2ρ = `twoRho` of o),
then ∫ f⁺ over G_ε' ∩ G_εB is at most that over G_ε ∩ G_ε'B. -/
lemma isOpen_openOrbit_and_lintegral_le ε' : IsOpen {g : USign ε' | ↑g ∈ openOrbit ε o} ∧ ∀ f,
  (∀ (y : GL n ℂ) b, IsBorelMatrix o b → f (y * b) = ‖diagChar (twoRho o ⊤) b‖ ^ 2 * f y) → ∫⁻ g :
  USign ε', (openOrbit ε o).indicator (.ofReal ∘ f)
  g ≤ ∫⁻ g : USign ε, (openOrbit ε' o).indicator (.ofReal ∘ f) g := by
  have ⟨ψ, ⟨d, z⟩, H⟩ := exists_borel_chart 1 o (lowerLiePart ε 1 o) hasStrictFDerivAt_exp_zero
    (by simp [lowerLiePart, signMatrix]; grind)
  choose! Φ B P Q e i using (fun _ ⟨g, b, h, e⟩ ↦ let t := diagTorus ε fun i ↦ ⟨‖b i i‖ / b i i, by
    simp [Submonoid.unitSphere, h.diag_ne_zero ho]⟩; ⟨g * t⁻¹, t * b, .mul ⟨by simp [t, diagTorus],
    by simp⟩ h, by simp [t, diagTorus, h.diag_ne_zero ho], by simp [e, mul_assoc,
              h.2]⟩ : ∀ y ∈ openOrbit ε o, ∃ g : USign ε, ∃ b, IsBorelMatrix o b ∧
    (∀ i, 0 < b i i) ∧ g * b = y ∧ y * b⁻¹ = g)
  have E y h := have u := P y h; let A := ContinuousLinearMap.mulLeftRight ℝ _ (Φ y).1.1⁻¹ (B y)⁻¹
      have a : A y = 1 := (by simp_all [A, mul_assoc]); (Filter.eventually_and.1
        (((A.cont.tendsto' _ _ a).eventually (.and (.mp (by simp) H) (d.continuousAt.const_add 1
        (IsAccretive.setOf_mem_nhds (by simp [z, PosDef.one.isAccretive]))))).mono fun x ⟨⟨p, _, q⟩,
        k⟩ ↦ have r : x = (Φ y * expU ⟨_, lowerLiePart_mem_unitaryLie ..⟩).1.1 * _ :=
          (by simpa [mul_assoc, A, u.2] using congr(Φ y * $q * B y))
        (fun m ↦ And.intro m congr($((P x m).unitary_eq_of_mul_eq ho ε (p.mul u) ⟨(e x m).trans r,
          fun i ↦ by simpa [↓p.mul_apply_diag ho u, Q, h, m, lowerLiePart, lt_def, ← two_mul,
          signMatrix, mul_right_comm, ← Int.cast_mul] using
          k.diag_pos⟩).1.1)) ⟨_, _, p.mul u, r⟩)).imp_right (((a ▸ HasFDerivAt.comp 1 (by
      simpa [z] using hasFDerivAt_exp_zero) ((lowerLiePart ..).hasFDerivAt.comp _ d)).comp _
        A.hasFDerivAt).const_mul _).congr_of_eventuallyEq
  refine (fun O ↦ ⟨O, fun F hB ↦ have S := measurable_cayleyChart O.measurableSet; ?_⟩)
    (.preimage_of_continuous (isOpen_iff_mem_nhds.2 (E · · |>.1)))
  have ⟨t, h⟩ := (Haar.lintegral_chart_rotate_le (.refl ..) (.id _) (Φ :=
    (Φ <| cayleyChart (signMatrix ε') ·)) (S.inter (by measurability)) (fun _ ⟨p, u⟩ _ ⟨q, v⟩ _ ↦
    cayleyChart_injOn u v ((P _ p).inv.unitary_eq_of_mul_eq ho ε' (P _
    q).inv (by simp_all [IsBorelMatrix.inv_apply_diag ho]))) fun y ⟨p,
    q⟩ ↦ have ⟨c, j⟩ := abs_det_logDerivU_cayleyChart q; .imp_right (.trans · ((abs_mul ..).trans
      (congrArg₂ _ (abs_det_lowerLiePart ho ε (P _ p) (Q _ p) ε') j))) ?_).exists
  grw [lintegral_eq_cayleyChart, ← lintegral_mul_left_eq_self _ (circleScalar t)⁻¹, ← h,
    ← setLIntegral_indicator S]
  gcongr; exact Set.le_indicator_apply (fun p ↦ by simp_all [(openOrbit ε' o).indicator_of_mem ⟨_,
    _, (P _ p).inv, (i _ p).symm⟩, mul_left_comm, e _ p ▸ hB .., mul_assoc, ← mul_div]) (by aesop)
  have D := (E _ p).2.comp y c.hasFDerivAt
  use ⟨_, D⟩; erw [← map_mul, logDerivU, D.fderiv]; congr 2 with
  simp [conjTranspose_logDerivU c, ← congr($(i _ p)⁻¹), (P _ p).2, inv_mat]
  simp [logDerivU, ← mul_assoc, mem_U.1]

/-- Let o be injective, F continuous on GL_n(ℂ) with F(yb) = |∏ b_ii^{r_i}|²F(y) for o-triangular b,
r_i = #{j : o_j<o_i} − #{j : o_i<o_j}. Then F is integrable on G = U(diag ε), and ∫_G F is ∫_{U(n)}
F minus the part outside `openOrbit ε o`. -/
lemma integral_haar_eq_integral_openOrbit {F : _ → ℂ} (hB : ∀ (y : GL n ℂ) b, IsBorelMatrix o b →
  F (y * b) = ‖diagChar (twoRho o ⊤)
  b‖ ^ 2 * F y) (c : Continuous (F · : GL n ℂ → ℂ)) : Integrable (F · : USign ε → ℂ) ∧ ∫ g :
  USign ε, F g = (∫ k : USign 1, F k.1.1) - ∫ k in {k : USign 1 | k.1.1 ∈ openOrbit ε o}ᶜ, F k := by
  have ⟨S, L⟩ := (isOpen_openOrbit_and_lintegral_le ho ε 1).imp_left (·.measurableSet)
  have K := integrable_of_compactSpace (X := USign 1) (ν := volume) (c.comp' continuous_subtype_val)
  have E f h := (((isOpen_openOrbit_and_lintegral_le ho ..).2 f h).antisymm (L f h)).trans
    (lintegral_indicator S _)
  simp [fun g : USign ε ↦ (exists_orthonormal_mul o ⟨_, g.1.4⟩).elim (b := ↑g ∈ openOrbit 1 o)
    (⟨⟨g * ·, by simp_all [U]⟩, _, .inv ⟨·.1, by simp⟩, by simp⟩)] at E
  refine (fun i ↦ ⟨i, (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun φ ↦ ?_⟩)
    ⟨c.comp_aestronglyMeasurable (by fun_prop), by simpa [E (‖F ·‖) (by aesop), ← ofReal_norm,
    HasFiniteIntegral] using K.restrict.2⟩; simp [← φ.integral_comp_comm, φ.integrable_comp,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part, K.restrict, setIntegral_compl, *]
  erw [E (φ ∘ F), E (-φ ∘ F)] <;> simp_all [← ofReal_pow, ← real_smul]

omit ho

open Nat Orbital AddCircle HCParam

/-- Weyl's dimension formula for U(n): for a parameter l = 2λ and Λ = λ−ρ, (∏_{i<n} i!) /
∫_{U(n)} |m_Λ(k)|² dk = ∏_{λ_j<λ_i} (λ_i−λ_j), for Haar measure of mass one. -/
lemma weyl_dimension_formula {n} [Fintype n] {l : @HCParam n 1} {h} (hg : l.HasGap h) :
  l.lowestKType.kTypeNormSq⁻¹ = weylDimensionPoly l := by
  have L (a : HCParam 1) := tendsto_finsetProd ⊤ fun i _ ↦ tendsto_finsetProd {j | l j < l i} fun j
    _ ↦ ((hasDerivAt_fourier 1 (a i) 0).sub (hasDerivAt_fourier 1 (a j) 0)).tendsto_slope_zero
  have E (t : ℝ) := ((weyl_character_kTypeChar hg.1 hg.isKDominant_lowestKType).2 (@toCircle 1 t ^
    l.lowerCount Eq ·)).trans (by rw [torusEval_alternant, ← det_transpose]; simp [weyl_denominator
    hg.1, torusEval_alternant, transpose, zpow_comm] :
    _ = Orbital.torusEval (@toCircle 1 t ^ (l.lowestKType + l.lowerCount Eq) ·) (l.rootProd Eq))
  simp [rootProd, Orbital.torusEval, toCircle_zsmul, ← mul_sub] at E L
  obtain ⟨t, k, e, he⟩ := tendsto_nhds_unique (((L _).mul (by fun_prop : ContinuousWithinAt ..)
    ).congr ((mul_assoc ..).trans <| congrArg _ <| E ·)) (L _), fun a ↦ congr(($(two_mul_lowestKType
    hg a) : ℂ) + $(card_lt_add_card_gt_add_one hg.1 a)), exists_equiv_fin_lt_iff hg.1
  simp [kTypeChar, diagTorus, prod_eq_zero_iff, mul_assoc, lowerCount, twoRho] at t k
  rw [weylDimensionPoly, eq_div_iff (by positivity), ← ofReal_inj, mul_comm]; push_cast
  convert t <;> try grind
  simp_rw [← map_univ_equiv e, filter_map, prod_map, prod_range, ← descFactorial_self,
    descFactorial_eq_prod_range, ← prod_range_natCast_sub]
  simp [he, filter_gt_eq_Iio, ← Iio_eq_range, ← Fin.map_valEmbedding_Iio]

variable {n : _} [Fintype n] (h : ℕ) (u : GL n ℂ) (l f : n → ℤ)

/-- The matrix u*·diag(2^{f_i})·u, for u in GL_n(ℂ) and an integer vector f. -/
@[simp] noncomputable abbrev twoPowDiagConj := u.1ᴴ * diagonal ((2 : ℂ) ^ f ·) * u

attribute [local simp] zpow_nonneg prod_eq_zero_iff PosSemidef.conjTranspose_mul_mul_same

/-- Let u be unitary, l, f integer vectors, m an integer, f_a+|m| ≤ f_c whenever l_c < l_a, and
h ≤ |l_i−l_j|, h natural. Then (|u_ij|² 2^m)^h·|m_l(D)| ≤ |m_l(u*Du)|, where D =
diag(2^{f_a}). -/
lemma le_norm_weightMinors_twoPowDiagConj i j m (hu : uᴴ = u.1⁻¹) (k : ∀ a c, l c < l a →
  f a + |m| ≤ f c) (H : h ≤ |l i - l j|) : ‖weightMinors l (twoPowDiagConj 1 f)‖ *
  (‖u i j‖ ^ 2 * 2 ^ m) ^ h ≤ ‖weightMinors l (twoPowDiagConj u f)‖ := by
  have P {f g p} [DecidablePred p] (h : f ≤
    g) : ‖principalMinor (twoPowDiagConj u f) p‖ ≤ ‖principalMinor (twoPowDiagConj u g) p‖ :=
    norm_det_le_norm_det_of_posSemidef (.submatrix (by simp) _) (.submatrix (M :=
    twoPowDiagConj u g - twoPowDiagConj u f) (by simp [← sub_mul, ← mul_sub, h _]) _)
  have V f : (twoPowDiagConj u f)⁻¹ = twoPowDiagConj u (-f) :=
    inv_eq_left_inv (by simp [mul_assoc, hu, ← mul_assoc (diagonal _)])
  wlog H : l j ≤ l i generalizing l f; convert V f ▸ this (-l) _
  simp +contextual [↓← weightMinors_neg, add_comm, k]; grind
  obtain ⟨⟨a, A⟩, b, B⟩ := @Finite.exists_min _ _ _ ⟨i⟩ _ l, Finite.exists_le l
  rw [show h = #(Ioc (l a) b ∩ Ioc (l i - h) (l i)) by simp [Ioc_inter_Ioc]; grind, ← prod_const]
  simp [weightMinors_eq_det_zpow_mul_prod _ (l a) b, ↓← prod_ite_mem, ← prod_mul_distrib, *,
    mul_zpow, field, -mul_ite]
  gcongr with t; have ⟨c, _⟩ := exists_min_image {k | l k < t} f ⟨a, by grind⟩
  let q k := t ∈ Ioc (l i - h) (l i) ∧ k = j; have := (k · c)
  grw [(?_ : ite .. ≤ ‖principalMinor (twoPowDiagConj 1 (f c)) q‖ * ‖principalMinor (twoPowDiagConj
    u (f ⊓ f c))⁻¹ q‖), jacobi_complementary_minor (by simp), norm_div, fischer_inequality (r :=
    (¬q ·)) (by simp) (fun i ↦ l i < t ∧ ¬q i) (t ≤ l ·), P inf_le_right, P inf_le_left]
  simp [principalMinor_eq_det, ← diagonal_one, ← smul_eq_mul_diagonal, hu, ← diagonal_smul, field,
    sub_ite, ← prod_mul_distrib, apply_ite norm]
  rw [mul_comm, prod_congr rfl]; any_goals grind
  nth_grw 3 [← re_le_norm]; split <;> simp [↓V, q, ‹_›, principalMinor.eq_1, diagonal, mul_apply,
    default, toSquareBlockProp, mul_right_comm _ _⁻¹, conj_mul', ↓re_eq_norm.2, sq]
  grw [← single_le_sum (by bound) (mem_univ i)]; simp [field, mul_assoc, ← zpow_add₀]
  gcongr <;> grind
