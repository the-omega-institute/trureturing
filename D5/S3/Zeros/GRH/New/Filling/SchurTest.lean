/- GID: D5/S3/Zeros/GRH/New/Filling/SchurTest
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/SchurTest
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.SchurTest. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/SchurTest.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.AmplitudeSums
import D5.S3.Zeros.GRH.New.RealPlace.VolumeKernel
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Energy of terms of the second moment; splitting; passage to cut Bessel functions. Size
function of a class of terms; open-cell mass fits under it. -/

open Subgroup ComplexOrder ENNReal Finset MeasureTheory Real

namespace Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {V : Type _} {S : Filling E 𝔰}
  [NormedAddCommGroup V] (A : S.Classes → S.GRes → S.Classes → V) (Ω : Set _) (T : Set ↥(S.G E))
  (Ω' : Set _)

/-- The energy over Ω of a family A of vectors in a normed group: ν⁻² (ν = `Filling.unipCovolume`)
times the sum of ‖A(c, s,
c')‖² over classes c, c' and s ∈ Ω. -/
noncomputable def energy := ∑ c, ∑ c', ∑ s with s ∈ Ω, ‖A c s c'‖ ^ 2 / S.unipCovolume ^ 2

/-- The sum, over c, c', s ∈ Ω and links Λ ∈ R, of the squared norms of the blocks over (c,s,c')
of the elements of T with link Λ. -/
noncomputable def linkEnergy [Side] (R : Set _) := ∑' (c) (c') (s : Ω') (Λ :
  R), ‖S.amplitudeSum (T ∩ link ⁻¹' {Λ.1}) c s.1 c'‖ₑ ^ 2

variable [StablyUnram E] [S.IsAdmissible] (U : Set ↥(S.G E)) {ε : ℝ}
  {A B : S.Classes → S.GRes → S.Classes → V} {Ω : Set _}

lemma amplitudeSum_split [Side] : S.amplitudeSum T = S.amplitudeSum (T ∩ Uᶜ) + S.amplitudeSum
  (T ∩ U) := funext₃ fun _ _ _ ↦ (tsum_congr_set_coe _ (by grind)).trans
  ((summable_amplitude ..).tsum_union_disjoint (by grind) (summable_amplitude ..))

omit [StablyUnram E] [S.IsAdmissible] in
lemma energy_add_le (hε : 0 < ε) : energy (A + B) Ω ≤
  (1 + ε) * energy A Ω + (1 + ε⁻¹) * energy B Ω := by
  simp [energy, mul_sum, ← sum_add_distrib]
  gcongr; grw [norm_add_le, add_sq, two_mul_le_add_mul_sq hε]; grind

/-- Under `Filling.IsAdmissible`, for any set U of rational terms and any Ω, the family A_U − A♭_U,
the difference of the amplitude sums for the Bessel functions and for their cuts, has energy
over Ω at most b⁻³⁰d₁, d₁ = `Filling.besselEnergy`. -/
lemma energy_sub_cut_le : energy (S.amplitudeSum U - S.amplitudeSum (σ := .cut) U) Ω ≤
  (S.b ^ 30)⁻¹ * S.besselEnergy := by
  simp [energy, amplitudeSum, summable_amplitude, ← Summable.tsum_sub, ← Finset.sum_div,
    @sum_comm S.GRes, ← toReal_enorm]
  obtain ⟨⟨r, k⟩⟩ := S.ϱ_le_k.dest, S.one_le_b, S.k_le_f, S.unipCovolume_pos
  grw [besselEnergy, columnDim, ← le_mul_of_one_le_right' NeZero.one_le, filter_subset,
    sum_sq_le_sq_sum_of_nonneg, ← Nat.card_pos.succ_le, (toReal_sum _).ge,
    toReal_le_of_le_ofReal _ ∘ (amplitudeAbs_lt_top_and_cut_le U ..).2.trans']
  any_goals simp [field, unipCovolume_pos, le_of_lt]
  grw [Fintype.card_eq_nat_card, Nat.card_pi, Nat.card_pi.le, card_GL_le _]
  simp [card_resField_eq_levelPrime, S.card_chosenPlaces, ← mul_pow, -Nat.cast_mul]
  grw [g_le_b_pow, ← one_le_two]; simp [← pow_mul, ← pow_add, ← k]; gcongr; lia
  simp [amplitude, ← integral_sub, ← smul_sub, -toReal_mul, fun [Side] c s d γ ↦
    integrable_toReal_smul (by fun_prop) (by fun_prop)
    ((ENNReal.le_tsum γ).trans_lt ((amplitudeAbs_lt_top_and_cut_le U c s).1 d).2)]
  grw [enorm_tsum_le_tsum_enorm, enorm_integral_le_lintegral_enorm, enorm_toReal_smul_le]

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰) (c : S.Classes)
  (γ : ↥(S.G E)) (c' : S.Classes) (γ' : ↥(S.G E))

/-- The number τ²·√(D/(M·g^(2min(ϱ,j)kf)·x^(k+1))), with M = `Filling.countWeight` 0, k = |κ|, f the
number of infinite places, and D = 𝖽 for j > ϱ, else τ^(13−32j)𝖽₁. -/
noncomputable def classSize (j : Fin (𝔰.ϱ + 2)) x := S.tailScale ^ 2 * √(ite (𝔰.ϱ < j) S.mainEnergy
  (S.tailScale ^ 13 / (S.tailScale ^ 32) ^ j.1 * S.besselEnergy) /
  (S.countWeight 0 * S.g ^ (2 * min 𝔰.ϱ j * 𝔰.k * numInfPlaces E) * x ^ (𝔰.k + 1)))

/-- Let γ be near with x = ∏_v|𝗀_v(γ)| ≥ 1, and let a be the top-level class size
`Filling.classSize` at x. Then b^(−k³f) ≤ a, and the product over infinite places of the open-cell
masses `cellMass` at γ is at most (νa/2)². -/
lemma IsNear.le_classSize_and_cellMass_le {S : Filling E 𝔰} {γ} [ok : S.IsAdmissible] (n :
  S.IsNear γ) (N : 1 ≤ S.termDiscNorm γ) : (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ ≤ S.classSize ⊤
  (S.termDiscNorm γ) ∧ ∏ v, cellMass (S.ratToInf γ v) (S.besselSys v).deg S.boxSize (Fintype.card
  (S.besselSys v).I) ≤ (S.unipCovolume * S.classSize ⊤ (S.termDiscNorm γ) / 2) ^ 2 := by
  apply S.of_size_bounds; intros
  obtain ⟨⟨_, e⟩, b, m, Q, q, h, t, K⟩ := S.ϱ_le.dest, S.one_le_b, ok.packetConst_mul_mass_le,
    S.N_le, S.size_le, S.pow_le_k, ‹2 ≤ S.tailScale›,
    univ.one_le_prod₀ fun v _ ↦ S.one_le_abs_kappa v, Nonempty.intro 𝔰.k₀,
    S.besselDegree_pos, mass_pos E 𝔰.r, rootDiscr_pos E, 𝔰.openCellConst_pos
  rw [classSize, termDiscNorm, frameScaleProd, ite_eq_left, min_eq_left] at *; constructor
  grw [countWeight, ← ok.besselEnergy_le, besselEnergy, columnDim, g_le_b_pow, ← S.N_prime.one_le,
    ← t, ← one_le_two, one_pow, ← t, ← one_le_two, fun v ↦ ((n.norm_map_leadingMinor_le ⊤ v).trans'
    (by simp [↓← Complex.real_le_real, ↓← map_termDisc_eq_norm, frameDisc,
    RCLike.mul_conj]; bound) : ‖Φ v (S.termDisc γ)‖ ≤
    _), one_mul, ← @NeZero.one_le (Fintype.card S.BesselCoord), ← le_sqrt_of_sq_le]
  simp [field, ← pow_mul, ← pow_add]; gcongr; exact h.dest.choose_spec ▸ by lia
  simp_rw [cellMass, mainEnergy, besselDegree, gramDiscReal_realFrameGram_ratToInf, frameScaleSq,
    ← pow_abs_two_mul (kappa ..), add_comm 𝔰.k, pow_add] at *
  grw [packetConst, unipOrder, siegelConst, ← two_le_pi, tsub_le_self, Nat.factorial_le_pow, ← b,
    ← S.N_prime.one_le, abs_kappa_le, tsub_le_self, tsub_le_self] at m; set g := S.g
  simp (disch := positivity) only [volÔ_eq, abs_discr_eq_rootDiscr_pow, prod_pow_eq_pow_sum _ _ |_|,
    boxSize, columnDim, tailScale, Finset.prod_div_distrib, prod_const, prod_mul_distrib, card_univ,
    prod_pow, Fintype.card_pi, Fintype.card_fin, ← Real.log_le_log_iff, log_mul, log_div,
    Real.log_pow, Real.log_inv, Real.log_rpow, log_sqrt, Real.log_one, push_cast] at *; rify at *
  linear_combination (norm := rw [← neg_nonneg, ← e]) m + 3 * t + ↑(numInfPlaces E) *
    (((𝔰.k + 𝔰.ϱ + 0.5) * q + Real.log S.b * h) / 1000 + 𝔰.ϱ ^ 7 * Q)
  clear * - b N K; ring_nf; positivity
  repeat simp [one_le_pow₀, b]

/-- For a class c, the function equal to the cutoff β_c on the set `Filling.boxedPoints` and zero
outside it. -/
noncomputable def boxCutoff := S.boxedPoints.indicator (S.classCutoff c)

/-- The weight β⁰_c(γ⁻¹y)·∏_v (Δ(y_v)/Δ((γ⁻¹y)_v))^(k+ϱ+1) of Schur's test, with β⁰ the boxed
cutoff `Filling.boxCutoff`, Δ = `frameVolume` and k = |κ|. -/
noncomputable def schurWeight y := S.boxCutoff c ((S.ratToInf γ)⁻¹ * y) * ∏ v, .ofReal
    ((frameVolume (y v) / frameVolume (((S.ratToInf γ)⁻¹ * y) v)) ^ (𝔰.k + 𝔰.n))

attribute [local instance] Side.cut

/-- The integral over y of β⁰_c(y)·∏_v‖W_v(y_v)‖² times the weight `Filling.schurWeight` at (y,
γ⁻¹y), with β⁰ the truncated cutoff `Filling.boxCutoff`; used in Schur's test. -/
noncomputable def schurIntegral := ∫⁻ y,
  S.boxCutoff c y * (∏ v, ‖(S.besselSys v).W .cut (y v)‖ₑ ^ 2) * S.schurWeight c' γ' y

variable [StablyUnram E] {S : Filling E 𝔰} {c c' : S.Classes} {γ : ↥(S.G E)} {X : Type _}
  [MeasurableSpace X]

omit [StablyUnram E] in
lemma inCut_of_besselKernel_ne_zero {y} (h : S.besselKernel γ y ≠ 0) v : InCut (y v) S.b ∧
  InCut (((S.ratToInf γ)⁻¹ * y) v)
  S.b := by simp_all [← enorm_pos, enorm_besselKernel, (S.besselSys v).tail.inCut_of_ne_zero]

@[fun_prop] lemma measurable_boxCutoff [S.IsAdmissible] :
  Measurable (S.boxCutoff c) := by delta boxCutoff boxedPoints frameBox; measurability

@[fun_prop] lemma measurable_schurWeight [S.IsAdmissible] :
  Measurable (S.schurWeight c γ) := by fun_prop [schurWeight]

lemma amplitudeAbs_sq_le [S.IsAdmissible] : S.amplitudeAbs c c' γ ^ 2 ≤
  S.schurIntegral c c' γ * S.schurIntegral c' c γ⁻¹ := by
  rw [mul_comm, schurIntegral, ← lintegral_mul_left_eq_self _ (S.ratToInf γ⁻¹)]
  apply sq_lintegral_le <;> try fun_prop
  by_contra! ⟨_, n⟩; cases by simpa using n.ne_zero
  simp_all [boxCutoff, classCutoff, boxedPoints, ↓inCut_of_besselKernel_ne_zero ‹_›,
    (isBoxPartition_epsilon c).2, ↓(isBoxPartition_epsilon c').2, enorm_besselKernel, schurWeight,
    sq]; ac_nf at n
  simp [← mul_assoc, ← prod_mul_distrib, ← ofReal_mul, ← mul_pow, field,
    frameVolume_pos, le_of_lt, ne_of_gt] at n

/-- Averaging: let s map (X, m) measurably to 𝖴⁰_∞, B ⊆ X with m(B) ≥ 1, F ≥ 0 be measurable and
left 𝖴⁰_c(g)-invariant, ∫_B F(u·s(x)·y)dm ≤ C for u ∈ 𝖴⁰_∞, y ∈ `Filling.boxedPoints`. Then
∫β⁰_c∏_v‖W_v‖²F ≤ C·ν·#`Filling.BesselCoord`, for W_v cut, β⁰ = `Filling.boxCutoff`. -/
lemma lintegral_boxCutoff_le_of_average [S.IsAdmissible] c (m : Measure X) [SFinite m] {s : X → _ →
  _} (ms : Measurable s) (hs : ∀ x v, s x v ∈ besselU0) {F} (mF : Measurable F) (hF :
  ∀ u ∈ S.classUnip₀ c, ∀ y, F (S.ratToInf u * y) = F y) B (hm : 1 ≤ m
  B) {C} (h : ∀ u, (∀ v, u v ∈ besselU0) → ∀ y ∈ S.boxedPoints, ∫⁻ x in B, F (u * s x * y) ∂m ≤
  C) : ∫⁻ y, S.boxCutoff c y * (∏ v, ‖(S.besselSys v).W .cut (y v)‖ₑ ^ 2) * F y ≤
  C * (.ofReal S.unipCovolume * Fintype.card S.BesselCoord) := by
  cases (S.exists_cutoff_classUnip _).choose_spec
  grw [Fintype.card_pi, Nat.cast_prod, ← (S.besselSys _).tail.lintegral_sq_cut_le,
    ← lintegral_classCutoff_mul_prod _ _ c]
  simp (disch := fun_prop) [lintegral_prod, ↓← lintegral_const_mul,
    ← (measurePreserving_pi_orbitMeasure 𝔰.besselHaar₀).lintegral_comp]
  gcongr 1; by_cases x ∈ S.boxedPoints
  any_goals simp +contextual [← ofReal_norm, norm_smul, ((S.besselSys _).tail.isBesselFunction _).2,
    boxCutoff, classCutoff, mul_mem_boxedPoints_iff, *, (isBoxPartition_epsilon c).2, mem_sup_left,
    Subgroup.mem_inf.1 (_ : besselU0).2, ← mul_assoc, mul_right_comm _ _ (F _)]
  set p := Exists.choose _
  have e t := ((Equiv.inv _).tsum_eq _).trans congr(∑' k : (S.classUnip₀ c).subgroupOf (S.classUnip
    c), $(lintegral_mul_left_eq_self (μ := .pi fun _ ↦ 𝔰.besselHaar₀) (fun u ↦ (p * F) (((u *
    t) · |>.1) * x) * p (S.ratToInf k * (u · |>.1) * x)) (⟨_, ratToInf_mem_besselU0 k⁻¹.2.2 ·⟩)))
  simp (disch := first | fun_prop | simp [← mem_subgroupOf]) [mul_assoc, ← Pi.mul_def
    (S.ratToInf _), *, ← lintegral_tsum, ↓lintegral_mul_const, -lintegral_const_mul] at e ⊢
  grw [← mul_one (lintegral ..), hm, ← setLIntegral_const, funext fun x ↦
    (lintegral_mul_right_eq_self _ (⟨_, hs x ·⟩)).symm.trans (e _).symm, lintegral_lintegral_swap]
  gcongr; rw [lintegral_mul_const]; bound
  repeat fun_prop
