import OmegaMath.NumberTheory.GRH.New.RealPlace.LocalTheorem
import OmegaMath.NumberTheory.GRH.New.Filling.StandardLevel
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Phase sums are sharply dominated by local Bessel kernels (see New.Filling.Moments).

This file: Finite Bessel function; shell, frequency and bottom-value bounds for its forms. Top
kernel of finite system: local constancy, positivity, packet energy bound, transform. -/

noncomputable section

open Finset Subgroup ENNReal InnerProductSpace Level Matrix MeasureTheory IntegralPlace Place
  QuotientGroup SemilocalField Set Size MeasureTheory.Measure Measure ComplexOrder Function Filter

attribute [local simp] div_eq_top mul_eq_top mul_mem indicator Units.smul_def weylRatio intVectors
  le_of_lt mul_assoc mul_pow genIndex_pos prod_mem

variable {A ι} {𝔰 : Shape} [SemilocalField A] [StarRing A] [P :
  IntegralPlace A] [Fintype ι] {m} {T : 𝔰.Form A}
  [IsHermUnit T.splitGram] {F : Level ι T (m + 1)} {x y u k : T.G} {g : Aˣ} {u' : T.G} {g' : Aˣ}

/-- The function χ_g equal to ψ(σ(u)/g) on uK(g), for a chosen u in 𝖴, and to 0 off 𝖴K(g); σ(u)
sums the entries at the simple roots, 𝖴 = `besselU`, K(g) = `unitaryLevel` R g. -/
def IntegralPlace.phase g z := if h : ∃ u ∈ T.besselU,
  u⁻¹ * z ∈ unitaryLevel R g _ then P.ψ (g⁻¹.1 * simpleRootSum h.choose) else 0

section

omit [IsHermUnit T.splitGram]

lemma IntegralPlace.exists_besselU_of_phase_ne_zero : phase g y ≠ 0 → ∃ u ∈ besselU,
  u⁻¹ * y ∈ unitaryLevel R g _ := Not.imp_symm (dite_eq_right ·)

lemma IntegralPlace.norm_phase_le_one : ‖phase g y‖ ≤ 1 := by fun_cases phase <;> simp

lemma IntegralPlace.phase_eq (hu : u ∈ besselU) (e : u⁻¹ * y ∈ unitaryLevel R g _) : phase g y =
  P.ψ (g⁻¹.1 * simpleRootSum u) := by
  rw [phase, dite_eq_left ⟨u, hu, e⟩]; generalize_proofs k; have := k.choose_spec
  rw [← mul_one (P.ψ _), ← (self_dual _).2 (inv_mul_simpleRootSum_mem (div_mem this.2 e)) 1
    (one_mem _), one_mul, ← P.ψ.map_add_eq_mul, ← mul_add, ← simpleRootSum_mul] <;> simp [*]

lemma IntegralPlace.phase_besselS_mul (hx : x ∈ besselS) (hu : u ∈ besselU) (f :
  u⁻¹ * x ∈ unitaryLevel R g _) : phase g (x * y) = ψ (g⁻¹ * simpleRootSum u) * phase g y := by
  fun_cases phase g y <;> rename_i H
  · rw [phase_eq (mul_mem ((besselS_le_normalizer_besselU hx _).1 H.choose_spec.1) hu) (by
      simpa using mul_mem f H.choose_spec.2), ← P.ψ.map_add_eq_mul]
    grind -ac [simpleRootSum_mul, mul_mem, inv_mem, inv_mul_cancel_left,
      mem_unitriGroup_of_mem_besselU]
  rw [phase, mul_zero, dite_eq_right fun ⟨v, hv, q⟩ ↦ H ⟨_,
    (besselS_le_normalizer_besselU (inv_mem hx)
    _).1 (mul_mem hv (inv_mem hu)), by simpa using mul_mem (inv_mem f) q⟩]

lemma IntegralPlace.phase_mul_of_mem_unitaryLevel (hk : k ∈ unitaryLevel R g _) : phase g (y * k) =
  phase g y := by simp [phase, ← mul_assoc, mul_mem_cancel_right hk]

lemma IntegralPlace.phase_besselU_mul (hu : u ∈ besselU) : phase g (u * y) = ψ (g⁻¹ * simpleRootSum
  u) * phase g y := phase_besselS_mul (mem_unitriGroup_of_mem_besselU hu) hu (by simp)

@[fun_prop] lemma IntegralPlace.continuous_phase : Continuous (phase (T := T) g) :=
    (isLocallyConstant_of_eventually_mul (.mono (unitaryLevel_open_compact.1.mem_nhds (one_mem _))
  fun _ k _ ↦ phase_mul_of_mem_unitaryLevel k)).continuous

lemma IntegralPlace.unitaryLevel_le_unitaryLevel_one : unitaryLevel R g T.splitGram ≤
  unitaryLevel R 1 _ := fun _ ↦ (unitaryLevel_one.ge ·.1)

end

/-- The type of subgroups Z of the unitary group with K(g) ≤ Z ≤ K, where K(g) is the principal
congruence subgroup of F and K the integral unitary group. -/
abbrev Level.IntermediateGroup (F : Level ι T (m + 1)) := ↥(Icc F.congGroup (unitaryLevel R 1 _))

/-- The product over the floors l < ϱ of the volumes `Level.floorModulus` l; used as the mass of 𝖴 ∩
K(g) in the unipotent group. -/
abbrev Level.unipotentMass (F : Level ι T (m + 1)) := ∏ l ∈ .range 𝔰.ϱ, F.floorModulus l

variable (F) in
/-- The number ϰ(Z) = ∫|∫_Z χ_g(yxy⁻¹)dy|²dx, both integrals for the measure `Level.groupMeasure`,
with χ_g = `IntegralPlace.phase`. -/
def Level.floorZeroForm (Z : Subgroup T.G) := ∫⁻ x, ‖∫ y in Z,
  phase F.g (y * x * y⁻¹) ∂F.groupMeasure‖ₑ ^ 2 ∂F.groupMeasure

/-- The set of cosets K(g)a, a in Z, of the level group K(g) in the group Z containing it. -/
def Level.IntermediateGroup.Cosets (Z : F.IntermediateGroup) :=
  Quotient (rightRel (F.congGroup.subgroupOf Z))

instance (Z : F.IntermediateGroup) : Fintype Z.Cosets := @fintypeQuotientRightRel _ _ _
  (fintypeOfIndexNeZero (unitaryLevel_open_compact.2.relIndex_ne_zero unitaryLevel_open_compact.1 <|
  relIndex_eq_zero_of_le_right Z.2.2 ·))

/-- The number 𝖬(Z)·𝖬(K(g))/v² in [0, ∞], with 𝖬 the measure `Level.groupMeasure` and v the product
`Level.unipotentMass` of the floor volumes. -/
def Level.IntermediateGroup.massRatio (Z : F.IntermediateGroup) :=
  F.groupMeasure Z * F.groupMeasure F.congGroup / F.unipotentMass ^ 2

/-- The finite Bessel vector W(y): its coordinate at the coset K(g)a in Z is χ_g(ya⁻¹), with a
the chosen representative and χ_g the function `IntegralPlace.phase`. -/
def Level.IntermediateGroup.besselVector (Z : F.IntermediateGroup) (y : T.G) :
  EuclideanSpace ℂ Z.Cosets := .toLp 2 fun c ↦ phase F.g (y * c.out.1⁻¹)

@[simp] lemma Level.unipotentMass_ne_zero_and_ne_top : F.unipotentMass ≠ 0 ∧
  F.unipotentMass ≠ ∞ := by simp [unipotentMass, floorModulus, prod_eq_zero_iff, prod_ne_top]

lemma Level.exists_of_inner_besselVector_ne_zero (Z : F.IntermediateGroup) (e : ⟪Z.besselVector x,
  Z.besselVector y⟫_ℂ ≠ 0) : ∃ u ∈ besselU, ∃ v ∈ besselU, u * x ∈ unitaryLevel R 1 _ ∧
  (u * x)⁻¹ * (v * y) ∈ F.congGroup := have ⟨c, _, f⟩ := exists_ne_zero_of_sum_ne_zero e
  have ⟨⟨v, q, f⟩, u, p, g⟩ := (mul_ne_zero_iff.1 f).imp exists_besselU_of_phase_ne_zero
    (exists_besselU_of_phase_ne_zero ∘ star_ne_zero.1)
  ⟨_, inv_mem p, _,
    inv_mem q, by simpa using mul_mem (unitaryLevel_le_unitaryLevel_one g) (Z.2.2 c.out.2),
    by simpa using unitaryLevel_one_le_normalizer (Z.2.2 c.out⁻¹.2) (mul_mem (inv_mem g) f)⟩

lemma Level.IntermediateGroup.isOpen (Z : F.IntermediateGroup) : Z.1.IsOpen :=
  isOpen_mono Z.2.1 unitaryLevel_open_compact.1

variable (Z : F.IntermediateGroup) [h : IsStdLevel F] {j K : ℕ} (r t) {p q : ℕ → Aˣ} {ξ : Aˣ} {Γ :
  Gauge F} (hj : j ≤ 𝔰.ϱ) (hr : r + 10 ^ 8 * 𝔰.n ^ 4 ≤ 𝔰.k) (ht : t + 10 ^ 10 * 𝔰.n ^ 4 ≤ 𝔰.k)

lemma Level.IntermediateGroup.exists_coset {F : Level ι T (m + 1)} (Z : F.IntermediateGroup) (a :
  y ∈ Z.1) : ∃ d, ∀ c : Z.Cosets, y * c.out.1⁻¹ ∈
  F.congGroup ↔ c = d := ⟨⟦⟨y, a⟩⟧, fun _ ↦ .symm (.trans Quotient.eq_mk_iff_out rightRel_apply)⟩

lemma IntegralPlace.inv_md_eq_sqrt_genIndex_sq (u : Aˣ) : (P.md u)⁻¹ =
  .ofReal √(_root_.genIndex u.1) ^ 2 := by simp [md_eq_inv_genIndex, ← ofReal_pow]

namespace IntegralPlace.IsStdLevel

lemma groupMeasure_ne_top {S} (e : S ≤ unitaryLevel R 1 T.splitGram) : F.groupMeasure S ≠ ∞ :=
  (measure_lt_top_mono e (isHaarMeasure_groupMeasure.1.1 unitaryLevel_open_compact.2)).ne

lemma massRatio_ne_zero_and_ne_top : Z.massRatio ≠ 0 ∧ Z.massRatio ≠ ∞ := by
  simp [IntermediateGroup.massRatio, groupMeasure_ne_top, Z.2.2, unitaryLevel_le_unitaryLevel_one,
    Z.isOpen, unitaryLevel_open_compact, IsOpen.measure_ne_zero]

lemma floorZeroForm_on_congGroup : ∫⁻ x in F.congGroup, ‖∫ y in Z, phase F.g (y * x * y⁻¹)
  ∂F.groupMeasure‖ₑ ^ 2 ∂F.groupMeasure = F.groupMeasure Z ^ 2 * F.groupMeasure F.congGroup := by
  rw [setLIntegral_congr_fun measurableSet_unitaryLevel fun x e ↦ by rw [setIntegral_congr_fun
                            Z.isOpen.measurableSet fun y a ↦
    phase_eq (one_mem _) (by simpa using unitaryLevel_one_le_normalizer (Z.2.2 a) e)]]
  simp [Measure.real, ← ofReal_norm, groupMeasure_ne_top Z.2.2]

lemma isCut_besselVector : F.IsCut Z.besselVector :=
  ⟨⟨⟨by fun_prop [IntermediateGroup.besselVector], _, fun x ↦ by
    grw [EuclideanSpace.norm_eq, IntermediateGroup.besselVector, norm_phase_le_one]⟩, by simp_all
  [IntermediateGroup.besselVector, phase_besselU_mul, PiLp.ext_iff]⟩, fun e ↦
  (exists_of_inner_besselVector_ne_zero Z (inner_self_ne_zero.2 e)).imp (by simp_all [h.box_eq])⟩

/-- For a standard level and K(g) ≤ Z ≤ K: fl·⟨W_Z(y), W_Z(yx)⟩ = ∫_𝖴 1_Z(uy)·χ_g(uyx(uy)⁻¹)du,
where fl = ∏_{l<ϱ} fl_l and du is the convolution of the measures `Place.heisenbergMeasure`. -/
lemma unipotentMass_mul_inner_besselVector y x : F.unipotentMass.toReal * ⟪Z.besselVector y,
  Z.besselVector (y * x)⟫_ℂ = ∫ u, indicator Z
  (fun z ↦ phase F.g (z * x * z⁻¹)) (u * y) ∂ascConv heisenbergMeasure (𝔰.ϱ + 2) := by
  have A c := by simpa only [mconv_dirac_one] using
    h.unfold_besselU (θ := dirac 1) (c := c) h.integral_data.2.2
  rw [integral_congr_ae (g := fun u ↦ ∑ c : Z.Cosets,
    {u | u * (y * c.out.1⁻¹) ∈ F.congGroup}.indicator (fun _ ↦ Z.besselVector (y * x) c * star
    (Z.besselVector y c)) u) (ae_ascConv_mem_unipotentBelow.mono fun u hu ↦ ?_), integral_finsetSum
    _ fun c _ ↦ (integrableOn_const ((A _).trans_ne (by simp [-dirac_apply]))).integrable_indicator
    (measurable_mul_const _ measurableSet_unitaryLevel), PiLp.inner_apply, mul_sum]
  · congr! with c; by_cases e : Z.besselVector y c = 0; simp [e]
    erw [integral_indicator_const _ (measurable_mul_const _ measurableSet_unitaryLevel),
      Measure.real, A, dirac_apply_of_mem
      (by exact (exists_besselU_of_phase_ne_zero e).imp' (·⁻¹) (by simp)), mul_one]; rfl
  by_cases! a : u * y ∉ Z.1
  · exact (ite_eq_right a).trans (Fintype.sum_eq_zero _ fun c ↦ ite_eq_right fun b ↦ a
      (by simpa using mul_mem (Z.2.1 b) c.out.2)).symm
  obtain ⟨⟨d, e⟩, i⟩ := Z.exists_coset a, inv_mem (unipotentBelow_le_besselU hu)
  have := (phase_besselU_mul (y :=
    u * y * x * (u * y)⁻¹ * _) i).trans congr(_ * $(phase_mul_of_mem_unitaryLevel ((e d).2 rfl)))
  simp at e this
  simp [IntermediateGroup.besselVector, phase_eq i ((e d).2 rfl), mul_left_comm (ψ _),
    Complex.mul_conj', *]

/-- For a standard level at a finite place and K(g) ≤ Z ≤ K, the quantity `Level.pairingNorm` of the
pair (W_Z, W_Z), times the product of the floor volumes fl_l over l < ϱ, is at most
`Level.IntermediateGroup.massRatio` Z. -/
lemma pairingNorm_mul_le_massRatio : F.pairingNorm Z.besselVector Z.besselVector * F.unipotentMass ≤
  Z.massRatio := by
  have β x y := congr(‖$(unipotentMass_mul_inner_besselVector Z x (x⁻¹ * y))‖ₑ).trans_le
    ((enorm_integral_le_lintegral_enorm _).trans ((lintegral_indicator_one_le {u | u * x ∈
    Z.1}).trans' (lintegral_mono_ae (by simp_all [apply_ite, ← ofReal_norm, norm_phase_le_one]))))
  simp [← ofReal_norm, mul_comm F.unipotentMass, -toReal_prod] at β
  grw [IntermediateGroup.massRatio, ENNReal.le_div_iff_mul_le (by simp) (by simp), groupMeasure,
    stackMeasure_zero_eq, mconv_apply_eq_lintegral Z.isOpen.measurableSet, ← stackMeasure_zero_eq,
    Level.pairingNorm, upperMeasure, tsub_zero, mul_right_comm, mul_assoc,
    lintegral_mul_const_le, ← lintegral_mul_const' _ _
    (groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one), lintegral_mono fun x ↦ ?_]
  refine if a : Z.besselVector x = 0 then by simp [a] else
    ((isCut_besselVector Z).exists_mul_mem_box a).elim fun u b ↦ ?_
  erw [← measure_preimage_mul_right F.groupMeasure (u * x)⁻¹, groupMeasure, stackMeasure_zero_eq,
    h.unfold_besselU h.integral_data.2.2]
  grw [lintegral_mul_const_le, ← mul_assoc, ← lintegral_indicator_const_le,
    lintegral_mono fun y ↦ le_indicator_apply (fun _ ↦ ?_) fun n ↦ ?_]
  · grw [← mul_assoc, ← mul_pow, ← ofReal_norm, β, pow_le_of_le_one bot_le _ two_ne_zero]; rfl
    grw [Z.2.2, ← mconv_dirac_one (ascConv ..), h.unfold_besselU (by simp),
      prob_le_one]; simp [floorModulus]
  rw [by_contra fun e ↦ (exists_of_inner_besselVector_ne_zero Z e).elim fun v ⟨c, w, d, _, e⟩ ↦
    n ⟨_, mul_mem (div_mem b.1 c) d, by simpa [div_eq_mul_inv]
    using unitaryLevel_one_le_normalizer (h.box_eq.2.1.le b.2) e⟩]; simp

lemma enorm_integral_phase_eq_upperPairing : ‖∫ y in Z, phase F.g (y * x * y⁻¹) ∂F.groupMeasure‖ₑ =
  ‖F.upperPairing 0 (translatePairing Z.besselVector Z.besselVector 1) 1 x‖ₑ * F.unipotentMass := by
  have I := (integrableOn_of_bounded (h.groupMeasure_ne_top Z.2.2) (by fun_prop) (.of_forall fun z ↦
    norm_phase_le_one (g := F.g) (y := z * x * z⁻¹))).integrable_indicator Z.isOpen.measurableSet
  rw [← integral_indicator Z.isOpen.measurableSet, groupMeasure, stackMeasure_zero_eq] at *
  simp [↓(integral_mconv I).trans (integral_integral_swap (I.comp_measurable measurable_mul)),
    ↓← unipotentMass_mul_inner_besselVector Z, upperPairing, mul_comm, ← ofReal_norm, -toReal_prod]

/-- For a standard level at a finite place with integers R: if the non-units of R have volume at
most 1/B for some B ≥ 2, then the group of integral unitary elements has measure M at least
2^(−(ϱ+1)). -/
lemma inv_two_pow_le_groupMeasure {B} (hB : 2 ≤ B ∧ volume (P.R \ P.intUnits) ≤ B⁻¹) : 2⁻¹ ^ 𝔰.n ≤
  F.groupMeasure (unitaryLevel R 1 T.splitGram) := by
  grw [← h.box_eq.2.1, ← h.le_stackMeasure_boxSet _ _ (zero_add _), ← one_sub_inv_two, hB.1, ← hB.2,
    ← @volume_O A, le_measure_sdiff, sdiff_sdiff_le]

/-- For a standard level F, if the finite Bessel vector at x is not orthogonal to that at some
z, then for all a, y the set `Level.floorValues` a x y contains a unit c of A lying in R and
has volume at most md(c). -/
lemma exists_unit_mem_floorValues a {z} y (e : ⟪Z.besselVector x, Z.besselVector z⟫_ℂ ≠ 0) : ∃ c :
    Aˣ, c.1 ∈ R ∧ ↑c ∈ F.floorValues a x y ∧ volume (F.floorValues a x y) ≤ P.md c := by
  let X := fromRows x⁻¹.1.1 (F.g⁻¹.1 • (x⁻¹.1.1 - (x * y)⁻¹.1.1)); let i : 𝔰.BesselIndex := eStar a
  obtain ⟨⟨u, hu, -, -, hx, -⟩, b, t, I, L, l, k⟩ := exists_of_inner_besselVector_ne_zero Z e,
    valPair.exists_isPrimitiveMatrix_mul (X := X) ⟨fromCols x.1 0, by simp [X]⟩ FI.level
  have z c (l : c < a) : b.1.col i (eStar c) = 0 := t (by simp [FI.level, i]; omega)
  have r w (z : ∀ c < a, w (eStar c) = 0) : (b⁻¹.1 *ᵥ w) i = _ :=
    Fintype.sum_eq_single i fun x n ↦ by
    by_cases l : FI.level x < FI.level i; simp [blockTriangular_inv_of_blockTriangular t l]
    obtain c | c | c := x <;> simp [FI.level, i] at l n <;> first | omega | rw [z, mul_zero]; omega
  let c := Units.mkOfMulEqOne _ _ ((r _ z).symm.trans (congr($b.inv_mul i i).trans (by simp)))
  use c⁻¹, (unitriGroup_mulVec_dual (mem_unitriGroup_of_mem_besselU hu) a.2 z).subst
    (by simpa using! (hx.1.isIntMatrix.mul (N := x⁻¹.1.1 * b.1) (I <| .inl ·) i i)), ⟨_,
    ⟨by simpa [h.box_eq, X, sub_mul, -mul_assoc] using! (I · i), z⟩, rfl⟩, md_inv c ▸
    volume_setOf_mul_mem c ▸ measure_mono fun _ ⟨w, ⟨j, n⟩, e⟩ ↦ e ▸ (r w n).subst (motive := (·
    ∈ R)) (by simpa [← inv_eq_left_inv ((L.mul_assoc ..).trans k)] using (l.mulVec (v := X *ᵥ
    w) (by simpa [h.box_eq, X] using j) i))

/-- For a standard level, K(g) ≤ Z ≤ K and any gauge Γ: if ⟨W_Z(x), W_Z(y)⟩ ≠ 0, there are u, v
in 𝖴 with ux, vy in the box and (vy − ux)/g of size 2. -/
lemma exists_close_of_inner_ne_zero (e : ⟪Z.besselVector x, Z.besselVector y⟫_ℂ ≠ 0) :
  ∃ u ∈ besselU, ∃ v ∈ besselU, u * x ∈ F.boxSet ∧ v * y ∈ F.boxSet ∧ Γ.HasMatSize 2
  (F.g⁻¹.1 • ((v * y).1.1 - (u * x).1.1)) :=
  h.box_eq.2.1 ▸ (exists_of_inner_besselVector_ne_zero Z e).imp fun u ⟨a, v, b, k, l⟩ ↦ ⟨a, v, b,
  k, by simpa using mul_mem k (unitaryLevel_le_unitaryLevel_one l), fun i j ↦ mem_ofSize_mono (by
    simpa [mul_sub] using Γ.hasVecSize_ball (h.box_eq.2.2.2.1.ge (k.1.isIntMatrix.mul l.2 · j)) i)⟩

/-- If `Level.formMajorant` j p q of W_Z is not identically 0, j ≤ ϱ, then in some gauge of depth α:
`Size.IsHead` holds for p, q; 1/g (if j ≠ 0) and 1/p_i − 1/q_i (i < j) have size 1; Λ^E ≤
(2/md g)^K·Λf(p)Λf(q) whenever 4E ≤ K (`finHeadWeight` K j). -/
lemma exists_gauge_depth_of_ne_zero (hj : j ≤ 𝔰.ϱ) K p q (e : ∃ x, F.formMajorant j p q
  Z.besselVector Z.besselVector x ≠ 0) : ∃ α a b, let Γ := (h.gauge α a b); (Γ.IsHead j p ∧ Γ.IsHead
    j q ∧ (j ≠ 0 → ↑F.g⁻¹ ∈ Γ.ofSize 1)) ∧ (∀ i < j, (p i)⁻¹.1 - (q i)⁻¹.1 ∈ Γ.ofSize 1) ∧ ∀ E, 4 *
    E ≤ K → Γ.Λ ^ E ≤ (2 / P.md F.g) ^ K * .ofReal (finHeadWeight K j p * finHeadWeight K j q) := by
  obtain ⟨g, c, x, y, ⟨σ, hσ, a⟩, τ, hτ, b⟩ := h.integral_data.2.2.1, isCut_besselVector Z,
    e.imp fun _ e ↦ (exists_ne_zero_of_ae ae_stackMeasure_mem e).imp fun _ k ↦
    (mul_ne_zero_iff.1 k.2).imp exists_ne_zero_of_pivotModulus exists_ne_zero_of_pivotModulus
  have H p y a b : ∃ β : Aˣ, ((β.1 ∈ R ∧ ∀ l ≤ j, (β / ∏ a ∈ .range l, p a).1 ∈ R) ∧ ∀ i < j,
      (β / p i).1 ∈ R) ∧ finHeadWeight K j p = √(_root_.genIndex β.1) ^ K := have H :=
      (minors_mem_ofSize (p := p) h.gauge.hasMatSize_box hj ((c.isNear_of_ne_zero
      b).of_floorGroup_mul hτ) ((c.isNear_of_ne_zero a).of_floorGroup_mul (g := y) hσ).choose_spec)
    ⟨∏ l ∈ .range (j + 1), ∏ a ∈ .range l, p a, suffices _ from ⟨this, fun i l ↦ by
        simpa [prod_range_succ, div_eq_mul_inv, -Units.coe_prod] using mul_mem (this.2 _ l) (H
        i l.le)⟩; by simp_all [← prod_erase_eq_div], by clear * - H; induction j <;> simp_all
      [finHeadWeight, prod_range_succ _ (_ + 1), prod_range_succ (M := ℝ), ← Units.coe_prod]⟩
  refine (H p y ?_ ?_).elim fun β ⟨u, _⟩ ↦ (H q (y * x) ?_ ?_).elim fun γ ⟨v, _⟩ ↦
    ⟨F.g * star (β * γ) * β * γ, ?_, by simp [star_g]; ring, ?_, ?_, fun E _ ↦ ?_⟩
  iterate 4 intro; simp_all [← (weylElem_mul_left_comm hτ).2]
  all_goals simp [IsHead, *, div_eq_mul_inv, ENNReal.mul_inv, inv_md_eq_sqrt_genIndex_sq, mul_sub]
  iterate 3 simp_all (maxDischargeDepth := 9) [↓mul_mem, mul_left_comm β.1, mul_left_comm F.g.1,
    isAdelic.1.1, div_eq_mul_inv, ↓sub_mem]
  ring_nf; gcongr <;> first | lia | simp [one_le_genIndex, *]

/-- Let n = ϱ+1, j ≤ ϱ, t + 10⁸n⁴ ≤ |κ|, K(g) ≤ Z ≤ K, p, q heads for the depth-α gauge, 1/g of size
1 if j ≠ 0. If f ≤ `Level.formMajorant` and, when e < 1, f² ≤ e^(2s)·`Gauge.selfNormProduct` on
positions, s = `Level.volumeExponent`, then κ_j(p,q)∫f dM ≤
min(1,e)^t·`Level.IntermediateGroup.massRatio`·Λ^(10⁹n⁴). -/
lemma lintegral_shells_le (hj : j ≤ 𝔰.ϱ) (hr : t + 10 ^ 8 * 𝔰.n ^ 4 ≤ 𝔰.k) {α a sα} (hΓ : Γ =
  gauge α a sα) (H : Γ.IsHead j p ∧ Γ.IsHead j q ∧ (j ≠ 0 → ↑F.g⁻¹ ∈ Γ.ofSize 1)) {f : _ →
  _} {e} (hf : ∀ {x}, f x ≤ F.formMajorant j
  p q Z.besselVector Z.besselVector x) (he : e < 1 → ∀ x ∈ F.positions, f x ^ 2 ≤ (e ^
  F.volumeExponent) ^ 2 * Γ.selfNormProduct j p q Z.besselVector Z.besselVector x) : F.headDensity j
  p q * ∫⁻ x, f x ∂F.groupMeasure ≤ min 1 e ^ t * Z.massRatio * Γ.Λ ^ (10 ^ 9 * 𝔰.n ^ 4) := by
  obtain ⟨hk, _, _, ζ, V⟩ := isCut_besselVector Z, h.zeta_rank, F.card_eq,
    le_two_of_pow_le_ofReal h.zeta_rank.1, by
    simpa [volume_O] using h.gauge.floorMassLe_one ⟨j, by lia⟩ h.gauge.hasFibreBound_floorQuadric
  let D (x : T.G) := (Option.elim · 1 (F.g⁻¹.1 • (x.1.1 - 1)).uncurry)
  grw [← setLIntegral_eq_of_support_subset fun x hx ↦ ?_, ← withDensity_apply',
    ← setLIntegral_const F.positions, lintegral_le_idealZeta_mul ζ (V := min 1 e ^ t * Z.massRatio *
    Γ.Λ ^ (9 * 10 ^ 8 * 𝔰.n ^ 4) * 2 ^ (10 ^ 5 * 𝔰.n ^ 2)) ({x ∈ F.positions | {ε | ∀ i,
    ε * D x i ∈ R} = R.subtype '' ·}) (.of_forall fun x y ↦ ?_), ζ, Γ.two_le_and_pairs_le.1]
  rotate_left
  obtain ⟨c, -, -, -, E⟩ :=
    inv_surjective.exists.1 (exists_content (p := D x) (i := none) isUnit_one)
  have hc := mul_one c.1 ▸ (E c).2 (by simp) none
  obtain ⟨z, I, i, b, l⟩ := isAdelic.1.1 hc, exists_ideal_cardQuot_eq c hc
  use I, i, ⟨y, b ▸ ext E⟩
  let ⟨σ, eσ⟩ : ∃ σ, σ ^ (400 * 𝔰.n ^ 2) = P.md c * Γ.Λ ^ ((10 * 𝔰.n + 1) * (99 * 𝔰.n)) :=
    ⟨_, rpow_inv_natCast_pow (by lia) _⟩
  let Γ' := h.gauge (star c * c) (mul_mem z hc)
  grw +useKAbstract [l, b, ← md_inv, Γ'.md_le 1 _ (by simp [Γ', z]), pow_le_pow_right₀
    (by simp) (by lia : m ≤ 50000 * 𝔰.n ^ 2), withDensity_apply', Γ.lintegral_positions_le Γ'
    hk hk.1 hj H.2.1 (e := min (min σ 1) e ^ F.volumeExponent * Γ.Λ ^ (9999 * 𝔰.n)) (sq _).ge
    (fun x k ↦ ⟨k.1, fun _ _ ↦ by simpa [Γ'] using! mul_mem z (k.2.ge (by simp) (some (_, _)))⟩)
    fun x hx ↦ ?_, min_assoc, pow_le_pow_right_of_le_one' (by simp) (by lia : 400 * 𝔰.n ^ 2 *
    (200000 * 𝔰.n ^ 2) + t ≤ F.volumeExponent), pow_add, pow_le_pow_left' inf_le_right t,
    inf_le_left, pow_mul σ, eσ, ← pairingNorm_mul_le_massRatio Z,
    ← (md_ne_zero_and_ne_top (star c * c)).elim (@ENNReal.mul_div_cancel _ 2)]
  simp [Γ', data_mem]; rotate_left
  rw [min_def_lt']; split
  grw [he (by order) x hx.1, ← Γ.one_le_Lambda]; simp
  grw [hf, Γ.formMajorant_sq_le (σ := min σ 1 ^ 2) hk hk.1 hj H.1 hx.1 V (by bound)
    hk.isNear_of_ne_zero fun o _ z N N' ↦ ?_, Γ.two_le_and_pairs_le.1]
  rotate_left
  simp [sq] at o; by_contra! n
  choose d hd E V using (exists_unit_mem_floorValues Z · x z); let C := ∏ i with j ≤ i.1, d i
  have ⟨hC, u⟩ : C.1 ∈ R ∧ ∀ i, j ≤ i.1 → (C / d i).1 ∈ R := by simp_all [C, ← prod_erase_eq_div]
  have w := mul_mem (pow_mem a (10 * 𝔰.n + 1)) (isAdelic.1.1 hC)
  let Γ' := h.gauge (α ^ _ * star C * C) (mul_mem w hC)
  have K := hx.2.le (Option.rec (Γ'.zero_one_mem_ofSize _).2
    (Prod.rec (Γ'.hasMatSize_sub_one_of_floorValues Γ hj H.1 H.2.1 (fun a c m ↦
    by simpa +arith [Γ', mul_left_comm] using mul_mem hC (mul_mem (isAdelic.1.1 hC)
    (hΓ ▸ Γ.mul_mem_ofSize (H.2.2 a) m :))) (exists_close_of_inner_ne_zero Z z) N N' fun i l ↦
    ⟨_, E i, by simpa [Γ'] using! mul_mem w (u i l)⟩)))
  apply ((md_ne_zero_and_ne_top (C ^ (99 * 𝔰.n * 2))).elim ENNReal.mul_lt_mul_left o).not_ge
  simp [C]
  grw [← V, ← n, min_eq_left o.le, prod_const, ← pow_mul, ← pow_mul, ← pow_succ',
    ← pow_le_pow_right_of_le_one' o.le (by grw [card_finset_fin_le]; lia : _ ≤ 400 * 𝔰.n ^ 2), eσ,
    ← Γ.md_le _ (c⁻¹ * (star C * C) ^ _) (by simpa [hΓ, ← pow_mul, mul_left_comm] using K),
    ← map_mul]
  simp [C, pow_mul, sq]; simp_all
  obtain ⟨y, -, a⟩ := exists_ne_zero_of_ae ae_stackMeasure_mem (ne_bot_of_le_ne_bot hx hf)
  obtain ⟨σ, -, a⟩ := exists_ne_zero_of_pivotModulus (left_ne_zero_of_mul a)
  obtain ⟨u, _, v, _, -, k⟩ := exists_of_inner_besselVector_ne_zero Z a
  exact h.box_eq.2.2.2.2 ▸ ⟨_, ⟨σ * y, v⁻¹ * u, by bound, rfl⟩, _, k, by simp⟩
  all_goals ring_nf; clear * - m; gcongr <;> simp

include hj hr in
lemma lintegral_formMajorant_ne_top : ∫⁻ x,
  F.formMajorant j p q Z.besselVector Z.besselVector x ∂F.groupMeasure ≠ ∞ := fun e ↦ by
  obtain ⟨_, _, _, H, -⟩ := exists_gauge_depth_of_ne_zero Z hj 0 p q (by by_contra; simp_all)
  simpa [e, headDensity, prod_eq_zero_iff, massRatio_ne_zero_and_ne_top] using
    lintegral_shells_le Z r hj hr rfl H le_rfl (e := 1) (by simp)

include ht

/-- Standard level, `Level.IntermediateGroup` Z, j ≤ ϱ, n = ϱ+1, t + 10¹⁰n⁴ ≤ |κ|, K ≥ 10¹⁰n⁴. For ω
= ψ(ξ·(`Shape.Form.frameGram` x)_{j+1,j+1}), or j ≥ 1, ω = 1,
ξ = (1/p_j − 1/q_j)/g (indices from 1): |`Level.floorForm`|
≤ `Level.IntermediateGroup.massRatio`·[R:ξR]^(t/2)·vol(R ∩ ξ⁻¹R)⁶·(2/md g)^K·Λf(p)Λf(q), Λf =
`finHeadWeight`. -/
lemma enorm_floorForm_le {ω} (hK : 10 ^ 10 * 𝔰.n ^ 4 ≤ K)
    (H : (ω = fun x ↦ P.ψ (ξ * (T.frameGram x.1.1).diag ⟨j, by lia⟩)) ∨ ∃ i, j = i + 1 ∧ ω = 1 ∧ ξ =
    F.g⁻¹ * ((p i)⁻¹.1 - (q i)⁻¹.1)) : ‖F.floorForm j p q Z.besselVector ω‖ₑ ≤
  Z.massRatio * (.ofReal √(_root_.genIndex ξ.1) ^ t * (denomIndex R ξ.1 : ℝ≥0∞)⁻¹ ^ 6 *
  (2 / P.md F.g) ^ K * .ofReal (finHeadWeight K j p * finHeadWeight K j q)) := by
  obtain ⟨C, n | ⟨α, a, _, D, L, E⟩⟩ := isCut_besselVector Z,
    not_or_of_imp (exists_gauge_depth_of_ne_zero Z hj K p q)
    <;> have hf {x} : formModulus j p q _ x ω ≤ _ := C.formModulus_le_formMajorant (by bound)
  grw [Level.enorm_floorForm_le]; simp_all
  set Γ := h.gauge α a _
  let β := α ^ (200 * 𝔰.n ^ 2)
  obtain ⟨η, w, u, v, e, i, d⟩ : ∃ η w : Aˣ, w.1 ∈ R ∧ ξ * w.1 ∈ R ∧
    (∀ x ∈ F.positions, formModulus j p q Z.besselVector x ω ^ 2 ≤ (P.c / P.md η) ^ Fintype.card ι *
    Γ.selfNormProduct j p q Z.besselVector Z.besselVector x) ∧ ξ * η⁻¹.1 ∈ R ∧
    min 1 (.ofReal √(_root_.genIndex η.1)) ^ 2 ≤ P.md w * md β⁻¹.1 := by
    obtain ⟨i, hi, rfl, e⟩ | rfl := H.symm
    exact ⟨ξ, β, pow_mem a _, e ▸ mul_comm β.1 _ ▸ mem_ofSize_mono
      (Γ.mul_mem_ofSize (D.2.2 (by omega)) (L i hi.ge)), fun _ ↦
      (Γ.formModulus_sq_le_of_heads C hj D.1 · hi e), by simp [ENNReal.mul_inv_cancel]; bound⟩
    obtain ⟨_, e, _, ⟨x, hx, _⟩, he, _, _, _⟩ := ξ.mul_inv, by simpa using valPair ξ.1 β
    let η : Aˣ := ⟨ξ + (e - x * e) * β, ξ⁻¹.1 * x, by grind, by grind⟩
    use η, η⁻¹ * β, by simp [η]; grind, by simp [η, β, pow_mem, hx, a], fun z hz ↦
      Γ.formModulus_sq_le_of_char C hj D.1 hz fun z m ↦ by simp [η, add_mul, P.ψ.map_add_eq_mul,
      (self_dual (β * z)).2 m _ (sub_mem he (mul_mem hx he))], by
      simpa [η], by grw [min_le_right, ← inv_md_eq_sqrt_genIndex_sq, ← map_mul]; simp
  grw +useKAbstract [Level.enorm_floorForm_le, lintegral_shells_le Z (t + 12) hj (by lia) (.refl Γ)
    D hf fun l x hx ↦ by grw [e x hx, data_mem.2.2.2.1, one_div, inv_md_eq_sqrt_genIndex_sq,
    pow_right_comm, pow_le_pow_right_of_le_one' l.le (tsub_le_self : F.volumeExponent ≤ _)],
    mul_assoc (_ * _), ← E (2 * 10 ^ 9 * 𝔰.n ^ 4) (by omega), pow_add, pow_mul _ 2 6, d,
    min_le_right, le_mul_of_one_le_left (genIndex_pos η).le (one_le_genIndex i (by
    simp)), ← map_mul, η.inv_mul_cancel_right, Γ.md_le _ β⁻¹ (β.3 ▸ R.one_mem), denomIndex,
    ← measure_inter_eq_inv_relIndex_add isCompact_O (isOpen_O.preimage (continuous_const_mul _)) _
    volume_O, ← md_le_volume (u := w) (by simp_all [← mul_assoc])]
  ring_nf; gcongr <;> simp

/-- The bottom value: for a standard level, a group Z between K(g) and the integral group, and t
+ 10¹⁰(ϱ+1)⁴ ≤ |κ|, ϰ(Z) ≤ M(Z)·M(K(g))·(M(Z) + vol(R∖R^×)^(t+1)·2^(−ϱ−1)), with ϰ =
`Level.floorZeroForm`. -/
lemma floorZeroForm_le_main_term : F.floorZeroForm Z ≤ F.groupMeasure Z * F.groupMeasure
  F.congGroup * (F.groupMeasure Z + volume (P.R \ P.intUnits) ^ (t + 1) * 2⁻¹ ^ 𝔰.n) := by
  let Γ := h.gauge; have H : Γ.IsHead 0 1 := by simp [IsHead, Γ]
  have k := Γ.isPairingKernel_self (isCut_besselVector Z) 0; let e :=
    min (volume (P.R \ P.intUnits)) 2⁻¹
  have h_meas : MeasurableSet (SetLike.coe F.congGroup) := measurableSet_unitaryLevel
  grw [floorZeroForm, ← lintegral_add_compl _ h_meas,
    floorZeroForm_on_congGroup, (enorm_integral_phase_eq_upperPairing Z).le,
    k.enorm_upperPairing_le, (mul_pow ..).le]
  with_unfolding_all grw +useKAbstract [lintegral_mul_const' _ _ (by simp), ← lintegral_indicator
    h_meas.compl, (one_mul (lintegral ..)).ge.trans
    (lintegral_shells_le Z (t + 1 + (𝔰.n + 10 ^ 9 * 𝔰.n ^ 4)) bot_le (by lia) (.refl Γ) ⟨H,
    H, by simp⟩ (indicator_apply_le ?_) fun _ x hx ↦ ?_), inf_le_right, IntermediateGroup.massRatio,
    mul_right_comm (e ^ _), mul_assoc, ENNReal.div_mul_cancel (by simp)
    (by simp), pow_add e, pow_le_pow_left' inf_le_left, pow_le_pow_left' inf_le_right]
  simp [Γ, pow_add, ← mul_pow, ENNReal.inv_mul_cancel]; ring_nf; rfl
  simp [formMajorant, descConv, sq]
  by_cases n : x ∈ F.congGroup; simp_all
  have M {y} : F.IsNear 0 y := ⟨y⁻¹, by simp [h.box_eq]⟩
  have C := Γ.pivotModulus_sq_le_of_capped (g := 1) (ε := e) k hx fun _ _ a ↦ by_contra fun b ↦
    n (h.integral_data.1.mem_unitaryLevel h.integral_data.2.2.1 (by simpa [Γ] using!
    (Γ.hasMatSize_sub_one_of_floorValues Γ bot_le H H (by simp) (exists_close_of_inner_ne_zero Z
    (by simp_all)) M M fun i l ↦ (exists_unit_mem_floorValues Z i x a).imp fun u k ↦
    ⟨k.2.1, by_contra fun m ↦ b ⟨i, l, k.2.2.trans (le_min (md_le_volume fun r a ↦
    ⟨mul_mem k.1 a, fun ⟨_, v, b, e⟩ ↦ m (by simp [Γ]; grind [mul_mem a b, Units.mul_inv])⟩)
    ((exists_ideal_cardQuot_eq u k.1).elim fun I ⟨a, b, e⟩ ↦ by simpa [le_inv_iff_le_inv, ← e,
    Nat.two_le_iff, a] using (m <| by simpa [·, Γ] using congr(1 ∈ $b))))⟩⟩)))
  simp_all [descConv, Gauge.selfNormProduct, Level.selfNorm, floorWeight, ← pow_mul Γ.Λ]
  grw [C, (by lia : 10000 * _ ≤ 1500000 * 𝔰.n ^ 3)] <;> ring_nf <;> simp

end IntegralPlace.IsStdLevel

variable {A ι j : _} {𝔰 : Shape} [SemilocalField A] [StarRing A] {m : _} {T : 𝔰.Form A} (L :
  Set A) [P : IntegralPlace A] [IsHermUnit T.splitGram] [Fintype ι] {F : Level ι T (m + 1)} (Z :
  F.IntermediateGroup) (p q : _) [Fintype j] (R : Matrix j j ℂ) (ω : j → ℕ → Aˣ) (e)

/-- The tensor 𝒥(p, l) = κ_ϱ(p, 1) ∫ W(y) ⊗ W(l w_p⁻¹ y)^* d𝖬(y), with κ_ϱ = `Level.headDensity` ϱ
and w_p the Weyl element of length ϱ. -/
def Level.correlation l := (F.headDensity 𝔰.ϱ p 1).toReal • besselCorrelation F.groupMeasure
  Z.besselVector (weylElem 𝔰.ϱ p * l⁻¹)

/-- The integral of ⟨𝒥(p, l), 𝒥(q, l)⟩, 𝒥 = `Level.correlation`, over the l in U(X₀ ⊕ Az) with h(z,
l⁻¹z) ∈ p_ϱ + L. -/
def Level.topKernel := ∫ l in {l | T.frameGram ↑l⁻¹ 𝔰.top 𝔰.top - p 𝔰.ϱ ∈ L}, ⟪correlation Z p l,
  correlation Z q l⟫_ℂ ∂F.stackMeasure 𝔰.ϱ 2

/-- The infimum, over l in U(X₀ ⊕ Az) with l⁻¹z = e, of ∫_H ∑_x (Re v*Rv)⁺ dh, v_p = 𝒥(ω_p, hl)_x;
infinite if no such l exists. 𝒥 = `Level.correlation`; ω_p are sequences of units and R is a
matrix, both indexed by p. -/
def Level.energy := ⨅ (l) (_ : l ∈ GT 𝔰.ϱ ∧ orbitPoint 𝔰.top l = e), ∫⁻ h, ∑ x,
  let v p := correlation Z (ω p) (h * l) x; .ofReal (star v ⬝ᵥ R *ᵥ v).re ∂F.measureH

variable {L R e} [h : P.IsStdLevel F]

namespace IntegralPlace.IsStdLevel

attribute [local simp] mul_assoc

/-- For a standard level and sequences p, q of units, there is one gauge in which, for all r
near p or near q, the inverses of the products r_0⋯r_{l−1}, l ≤ ϱ, have size 1. -/
lemma exists_gauge_isHead : ∃ Γ : Gauge F, ∀ j, ∀ᶠ r in nhds (![p, q] j), Γ.IsHead 𝔰.ϱ r := match
    (dense_of_ae P.ae_isUnit).inter_nhds_nonempty (Eventually.all fun j ↦ ((finite_le_nat
  𝔰.ϱ).eventually_all.2 fun i _ ↦ isOpen_O.preimage_of_continuous (f := fun (z, r) ↦ (star z * z) ^
  1 * (∏ i ∈ range i, r i)⁻¹.1).eventually_mem (x := (0, ![p, q] j)) (by simp)).curry_nhds) with
    | ⟨_, ⟨α, rfl⟩, e⟩ => ⟨gauge (star α * α) (by simpa using (e 0).self_of_nhds 0), e⟩

/-- Local constancy, uniform in l. For a standard level, all (p', l') near (p, 1) with l' in U(V_ϱ)
satisfy 𝒥(p', ll') = 𝒥(p, l) for every l in U(V_ϱ), 𝒥 = `Level.correlation` Z. -/
lemma eventually_correlation_eq : ∀ᶠ z in nhds (p, 1), z.2 ∈ GT 𝔰.ϱ → ∀ l ∈ GT 𝔰.ϱ,
    correlation Z z.1 (l * z.2) = correlation Z p l := (h.exists_gauge_isHead p 1).elim fun Γ e ↦ by
  filter_upwards [Γ.isCompact_hasMatSize.eventually_forall_of_forall_eventually (P := fun z y ↦
    y⁻¹ * weylElem 𝔰.ϱ p * z.2 * (weylElem 𝔰.ϱ z.1)⁻¹ * y ∈ F.congGroup) fun y _ ↦
    unitaryLevel_open_compact.1.preimage_of_continuous.mem_nhds (by simp), continuousAt_fst
    ((e 0).and ((range 𝔰.ϱ).eventually_all.2 fun j _ ↦ (continuousAt_apply j p).const_mul (p
    j)⁻¹ ((O.isOpen_units isOpen_O).mem_nhds (by simp))))] with z b ⟨s, d⟩ n l hl
  delta correlation besselCorrelation headDensity; congr! 5 with j n _ y
  · simpa [← map_mul] using congr(P.md (p j) * $((md_le_one (_ * _) (d j n).1).antisymm
      (ENNReal.inv_le_one.1 (P.md_inv _ ▸ md_le_one _ (d j n).2))))
  refine if o : Z.besselVector y = 0 then ?_ else congr(_ * star ($(by_contra fun t ↦
    t (PiLp.ext fun c ↦ .trans ?_ (phase_mul_of_mem_unitaryLevel (unitaryLevel_one_le_normalizer
    (Z.2.2 c.out.2) (b y ((Ne.ne_or_ne 0 t).rec (Γ.hasMatSize_of_ne_zero (isCut_besselVector Z)
    s ?_ o) (Γ.hasMatSize_of_ne_zero (isCut_besselVector Z) (e 0).self_of_nhds ?_ o)))))))
    _)) <;> simp [mul_mem, ↓o, IntermediateGroup.besselVector, *]

/-- Standard level, units open, inversion continuous at 1; l_θ ∈ U(V_ϱ), l_θ⁻¹z = e, pairs (K(g)l_θ,
n_θ) distinct, θ in a nonempty finite set. On H ∩ K(g)-orbits of points near e,
`Level.energy` ≥ μ_H(K(g)) ∑_θ (Re v_θ*Rv_θ)⁺, v_θ(p) = `Level.correlation`(ω_p, l_θ)_{n_θ}. -/
lemma eventually_sum_packets_le_energy (hi : IsOpen {x : A | IsUnit x}) (hc :
  ContinuousAt Ring.inverse (1 : A)) {i} [Fintype i] {l : i → _} (o : i) (hl : ∀ θ, l θ ∈ GT 𝔰.ϱ ∧
  orbitPoint 𝔰.top (l θ) = e) {n : i → _} (hn : ∀ θ θ', l θ * (l θ')⁻¹ ∈ F.congGroup → n θ = n θ' →
  θ = θ') : let v θ p := correlation Z (ω p) (l θ) (n θ)
  ∀ᶠ x in nhds e, ∀ k ∈ besselH ⊓ F.congGroup, ∀ y, k *ᵥ y = x →
            F.measureH F.congGroup * ∑ θ, .ofReal (star (v θ) ⬝ᵥ R *ᵥ v θ).re ≤ energy Z R ω y := by
  have hH k (e : k ∈ besselH ⊓ F.congGroup) x : Z.besselVector (k * x) = Z.besselVector x := by
    simp [IntermediateGroup.besselVector, simpleRootSum_eq_zero_of_mem_besselH,
      phase_besselS_mul (mem_unitriGroup_of_mem_floorGroup e.1) (one_mem _) (by simpa using e.2)]
  obtain ⟨⟨u, hu⟩, he, f, rfl⟩ := h.exists_isotropic, orbitPoint_eq_iff.1 (hl o).2, hl o
  simp_rw [energy, le_iInf_iff, mul_sum, ← (hasSum_fintype _).tsum_eq]
  filter_upwards [((isClosedEmbedding_unitary_coe.continuousAt_iff (f := fun x ↦ (l o)⁻¹ *
    U.of IsHermUnit.isUnit _ (exists_eichler_orbitPoint_eq hu).fst * l o)).2 (by
    have := congr($he _).trans (Pi.single_eq_same ..) ▸ hc; simp [comp_def, -besselFrame_last]
    fun_prop)).trans_eq (by congr with; simp [he]) (Eventually.all fun p ↦
    (eventually_correlation_eq Z (ω p)).curry_nhds.self_of_nhds), (hi.preimage_of_continuous (f :=
    (mulVec (l o) · (𝔰.besselFrame 𝔰.top)))).mem_nhds (by simp [he])] with _ r t a ha y rfl z s
  obtain ⟨g, ⟨m, q⟩, hz, rfl⟩ := floorGroup_anti 𝔰.ϱ.le_succ ha.1,
    (exists_eichler_orbitPoint_eq (e := l o *ᵥ a.1.1 *ᵥ y) hu).2, s
  have m := mul_mem (mul_mem (inv_mem f) (m fun i
    k ↦ by simpa [orbitPoint, -besselFrame_last, ← mul_assoc] using! (floorGroup_apply_besselFrame
    (mul_mem (mul_mem f g) (inv_mem hz)) (one_mem _) i).trans (ite_eq_left k))) f
  have b θ := unitriGroup_inf_floorGroup_last.le (inv_mul_mem_of_orbitPoint_eq (inv_mem hz)
    (inv_mem (mul_mem (mul_mem (hl θ).1 m) g)) (.symm (orbitPoint_eq_iff.2
    (by push_cast [-coe_units_inv, ← mulVec_mulVec, inv_inv, orbitPoint_eq_iff.1 (q (by
      simp_rw [orbitPoint, U.form_mulVec_mulVec]) t)]; exact orbitPoint_eq_iff.1 (hl θ).2))))
  rw [tsum_congr fun θ ↦ by rw [mul_comm, ← lintegral_indicator_const measurableSet_unitaryLevel,
    ← F.measureH_spec.2.1 _ (b θ), lintegral_mconv_dirac],
    ← lintegral_tsum (by fun_prop (disch := exact measurableSet_unitaryLevel))]
  refine lintegral_le_of_ae_imp F.measureH_spec.1 fun k g' ↦ (_root_.tsum_subtype ..).ge.trans
    ((tsum_congr fun ⟨θ, t⟩ ↦ ?_).trans_le (tsum_comp_le_tsum_of_injective (fun a b ↦
    Subtype.ext ∘ hn _ _ (by simpa using mul_mem (inv_mem a.2) b.2)) _))
  simp_rw [← r _ m _ (hl θ).1, correlation, besselCorrelation]
  conv_lhs => simp +singlePass [← integral_mul_left_eq_self _ a]
  simp [weylElem_mul_left_comm, *, ← hH _ ⟨mul_mem g' (b θ), t⟩ (l θ * _)]

/-- Unfolding: for a standard level with W = `Level.IntermediateGroup.besselVector` Z and
φ(x) = ψ(ξh(z, xz)), l ↦ φ(l⁻¹)⟨𝒥(p, l), 𝒥(q, l)⟩ is integrable for `Level.stackMeasure` ϱ 2,
𝒥 = `Level.correlation` Z, with integral `Level.floorForm` ϱ p q W φ. -/
lemma floorForm_top_eq_integral ξ : let φ x := P.ψ (ξ * T.frameGram x.1 𝔰.top 𝔰.top)
  let f l := φ l⁻¹ * ⟪correlation Z p l, correlation Z q l⟫_ℂ; Integrable f (F.stackMeasure 𝔰.ϱ 2) ∧
  F.floorForm 𝔰.ϱ p q Z.besselVector φ = ∫ l, f l ∂F.stackMeasure 𝔰.ϱ 2 :=
  (h.exists_gauge_isHead p q).rec fun Γ k ↦ by
  intro ω; have c := isCut_besselVector Z; set W := Z.besselVector
  obtain ⟨hW, _, ⟨e, n, b⟩, u, v⟩ := (by fun_prop [IntermediateGroup.besselVector] : Continuous W),
    (by fun_prop [frameGram] : Measurable ω),
    (Γ.isPairingKernel_self c 0).exists_lintegral_le 𝔰.ϱ, by simpa using (k · |>.self_of_nhds)
  have := hW.measurable
  have E : ProbabilityTheory.IdentDistrib (fun (l, x, y) ↦ ω l⁻¹ * (⟪W x, W y⟫_ℂ * ⟪W
    ((weylElem 𝔰.ϱ q * l⁻¹)⁻¹ * y), W ((weylElem 𝔰.ϱ p * l⁻¹)⁻¹ * x)⟫_ℂ)) (fun (k, τ, h, σ, x, y) ↦
    let z := k * τ * (weylElem 𝔰.ϱ p)⁻¹ * y; ω (σ * τ⁻¹) * ⟪W (h * σ * y), W (h * σ * y * x)⟫_ℂ *
      ⟪W (weylRatio 𝔰.ϱ p q * z * x), W z⟫_ℂ) ((F.stackMeasure 𝔰.ϱ 2).prod
    (F.groupMeasure.prod F.groupMeasure)) (F.measureH.prod ((F.floorMeasure 𝔰.ϱ).prod
    (F.measureH.prod ((F.floorMeasure 𝔰.ϱ).prod (F.groupMeasure.prod (F.stackMeasure 0 𝔰.ϱ)))))) :=
    ⟨by fun_prop, by fun_prop, ext_of_lintegral _ fun φ hφ ↦ by
    rw [← (measurePreserving_prod_mul_swap ..).2, congrArg F.groupMeasure.prod
      ((descConv_add _ 2 0).trans (by simp!; rfl))]
    simp (disch := with_unfolding_all fun_prop) only [mconv, lintegral_map,
      lintegral_prod_symm', ↓lintegral_prod (μ := F.groupMeasure), ← floorMeasure_top]
    congr! 6 with x _ y σ hσ h hh
    rw [← stackMeasure_mconv_dirac rfl (inv_mem (mul_mem (unitriGroup_inf_floorGroup_last.ge hh).2
      hσ)), lintegral_mconv_dirac, stackMeasure_top,
      lintegral_mconv_symm (by fun_prop), ← floorMeasure_top]
    congr! 2 with τ hτ k hk
    simp [weylRatio, ω, ↓← (frameGram_diag_mul (unitriGroup_inf_floorGroup_last.ge hh) _).1.trans
      (frameGram_diag_mul (unitriGroup_inf_floorGroup_last.ge (inv_mem hk))
      (σ * τ⁻¹)).2, *, ← (weylElem_mul_left_comm _).2, floorGroup_anti 𝔰.ϱ.le_succ _]⟩
  have J : Integrable _ _ := ⟨E.1.aestronglyMeasurable, (lintegral_prod_symm _ E.1.enorm).trans_lt
    ((setLIntegral_eq_of_support_subset fun y z ↦ by
    have ⟨l, h, n⟩ := exists_ne_zero_of_ae ae_stackMeasure_mem z
    use Γ.hasMatSize_of_ne_zero c u (inv_mem h) ?_ ?_, Γ.hasMatSize_of_ne_zero c v
      (inv_mem h) ?_ ?_ <;> contrapose! n <;> simp [↓n]).ge.trans_lt ((lintegral_mono fun _ ↦ by
    simpa [ω, descConv, n.ne, ← ofReal_norm, lintegral_const_mul'] using mul_le_mul_right (b ..)
      _).trans_lt ((Γ.isCompact_hasMatSize.prod Γ.isCompact_hasMatSize).integrableOn fun (x,
    y) ↦ ⟪W x, W y⟫_ℂ * e.toReal).2))⟩
  refine (fun H ↦ ⟨(J.integral_prod_left.const_mul _).congr H, integral_congr_ae H ▸
    ((integral_const_mul ..).trans (congrArg _ ?_)).symm⟩) (ae_stackMeasure_mem.mono fun l h ↦ ?_)
  · simp [Γ.inner_besselCorrelation c, *, W, correlation, headDensity, mul_rpow_of_nonneg,
      mul_pow]; ring
  rw [← integral_prod _ J, E.integral_eq, E.integrable_iff] at *
  iterate 4 rw [integral_prod_symm _ J]; replace J := J.integral_prod_right
  simp [← integral_conj, formIntegrand, formIntegrandOne, upperPairing, descConv,
    mul_left_comm (ω _)]

/-- Standard level, L open, R positive semidefinite, ω_p(ϱ) = t for all p. Then Q = ∑ R_pq
`Level.topKernel`(ω_p, ω_q) is real, nonnegative, and at least the integral of `Level.energy` over
h(z, e) − t ∈ L for `HyperbolicBasis.floorQuadric` at z. -/
lemma lintegral_energy_le_topKernel (o : IsOpen L) (hR : R.PosSemidef) {t} (ht : ∀ p, ω p 𝔰.ϱ = t) :
    let Q := ∑ p, ∑ q, R p q * topKernel L Z (ω p) (ω q)
    0 ≤ Q ∧ ∫⁻ e, {e | (T.splitGram *ᵥ e) (𝔰.besselFrame 𝔰.top) - t ∈ L}.indicator (energy Z R ω) e
      ∂F.floorQuadric 𝔰.top ≤ .ofReal Q.re := by
  obtain ⟨_, r, _⟩ := (isCut_besselVector Z).stronglyMeasurable, hR.dotProduct_mulVec_nonneg, by
    simpa using (floorForm_top_eq_integral Z · · 0 |>.1.restrict (s := ·))
  have e (v : j → EuclideanSpace ℂ (Z.Cosets × Z.Cosets)) : ∑ p, ∑ q, R p q * ⟪v p, v q⟫_ℂ = ∑ x,
    star (v · x) ⬝ᵥ R *ᵥ (v · x) := by simp [inner, entrywise, mul_sum,
    @Finset.sum_comm _ _ (_ × _), mul_comm]
  have p {l} := (e l).trans_ge (sum_nonneg fun _ _ ↦ r _)
  simp (disch := fun_prop) only [topKernel, ht, ← integral_const_mul, ← integral_finsetSum]
  grw (transparency := default) [and_iff_right (integral_nonneg fun _ ↦ p), ← RCLike.re_to_complex,
    ← integral_re, ofReal_integral_eq_lintegral_ofReal (.re ?_) (.of_forall fun _ ↦ p.1),
    ← (measurePreserving_orbitPoint ..).2, lintegral_map_le, ← lintegral_indicator_le,
    stackMeasure_top, lintegral_mconv_symm (.indicator ?_ (o.preimage_of_continuous
    ?_).measurableSet)] <;> try fun_prop [frameGram, correlation, besselCorrelation]
  refine lintegral_le_of_ae_imp ae_floorMeasure_mem fun x a ↦ indicator_apply_le' (fun k ↦
    iInf₂_le_of_le x ⟨a, rfl⟩ (lintegral_le_of_ae_imp F.measureH_spec.1 fun y s ↦ ?_)) (by simp)
  rw [indicator_of_mem
    (by rw [Set.mem_preimage, ← (frameGram_diag_mul (unitriGroup_inf_floorGroup_last.ge s)
    _).2]; simpa [orbitPoint, -besselFrame_last] using! k), e]
  simp [ofReal_sum_of_nonneg fun _ _ ↦ (r _).1]

/-- For a standard level, an intermediate group Z and an open additive subgroup L of A, the kernel
`Level.topKernel` L Z is jointly continuous in the two sequences of units. -/
lemma continuous_topKernel (L : OpenAddSubgroup A) : Continuous (topKernel L Z).uncurry :=
  .of_at fun x ↦ tendsto_const_nhds.congr' (by
  have A p := (Continuous.prodMk_left 1).continuousAt (eventually_correlation_eq Z p)
  filter_upwards [prod_mem_nhds (A _) (A _), (L.2.preimage_of_continuous (f :=
    ((x.1 𝔰.ϱ).1 - ·.1 𝔰.ϱ))).mem_nhds (by simp)] with _ a (d : _ ∈ L)
  simpa [uncurry, topKernel, ← add_mem_cancel_right (y := _ - _) d] using
    integral_congr_ae (ae_restrict_of_ae (ae_stackMeasure_mem.mono (by simp_all))))
