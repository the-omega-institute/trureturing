/- GID: D5/S3/Zeros/GRH/New/RealPlace/FloorKernels
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/RealPlace/FloorKernels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.RealPlace.FloorKernels. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/RealPlace/FloorKernels.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.CuspKernel.CircleMean
import D5.S3.Zeros.GRH.New.RealPlace.FlatCharts
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Tower method: pairings of kernels bounded floor by floor (see
New.RealPlace.LocalTheorem).

This file: Laws of floor kernels; pairing on one floor is integral of next floor's pairings. -/

namespace Level

open MeasureTheory Measure ProbabilityTheory Set
attribute [-simp] Subtype.forall
attribute [local simp] ite_eq_right mul_assoc
variable {R ι} {𝔰 : Shape} [CommRing R] [StarRing R] [TopologicalSpace R] [MeasureSpace R] [Place R]
  [Fintype ι] {m j l K} {T : 𝔰.Form R} [IsHermUnit T.splitGram] {F :
  Level ι T m} {x g y s k d} (hk : F.IsPairingKernel j k d)

lemma exists_ne_zero_of_pivotModulus (h : F.pivotModulus l k g y ≠ 0) : ∃ x ∈ GT l,
  k (x * g) (x * y) ≠ 0 := (exists_ne_zero_of_ae ae_floorMeasure_mem h).elim fun σ
  h ↦ by grind [exists_ne_zero_of_ae (ae_descConv_mem ae_floorMeasure_mem) (ne_bot_of_le_ne_bot h.2
  (enorm_integral_le_lintegral_enorm _)), mul_mem, =_ mul_assoc, enorm_zero]

lemma lintegral_upperPairing_sq_le (hl : l ≤ 𝔰.ϱ) : ∫⁻ σ, ‖F.upperPairing (l + 1) k (σ * g)
  (σ * (g * x))‖ₑ ^ 2 ∂F.floorMeasure l ≤ F.weightedSquareSum k x l g
  / F.floorWeight l g x := by rw [weightedSquareSum]; simp_all [← lintegral_const_mul',
  ENNReal.le_div_iff_mul_le, mul_comm, lintegral_mono_fn', weightedSquare]

namespace IsPairingKernel

include hk

@[fun_prop] lemma stronglyMeasurable_upperPairing : StronglyMeasurable ↿(F.upperPairing l k) :=
  .integral_prod_right (hk.rec (by fun_prop))

lemma mono (h : j ≤ l) : F.IsPairingKernel l k d :=
  {hk with conj_eq_self := (hk.conj_eq_self · <| floorGroup_anti h ·)}

lemma integrable_upperMeasure l g y : Integrable (fun x ↦ k (x * g) (x * y)) (F.upperMeasure l) :=
  (hk.exists_lintegral_le l).elim fun _ ⟨a, b⟩ ↦
  ⟨⟨_, hk.rec (by fun_prop), .rfl⟩, (b ..).trans_lt a⟩

lemma upperPairing_eq_integral_succ :
  Integrable (fun σ ↦ F.upperPairing (l + 1) k (σ * g) (σ * y)) (F.floorMeasure l) ∧
  F.upperPairing l k g y = ∫ σ, F.upperPairing (l + 1) k (σ * g) (σ * y) ∂F.floorMeasure l := by
  have I := hk.integrable_upperMeasure l g y
  simp [upperPairing, upperMeasure_eq_succ_mconv, ← mul_assoc] at *
  have J := I.comp_measurable measurable_mul
  use J.integral_prod_right, integral_mconv I ▸ integral_integral_swap J

lemma enorm_upperPairing_le : ‖F.upperPairing l k g y‖ₑ ≤ F.pivotModulus l k g y :=
  hk.upperPairing_eq_integral_succ.2 ▸ enorm_integral_le_lintegral_enorm _

lemma upperPairing_invariant (hl : j ≤ l) (hs : s ∈ unitriGroup l ⊓ GT j) :
  F.upperPairing l k (s * g) (s * y) = F.upperPairing l k g y := by
  induction' e : 𝔰.ϱ + 2 - l generalizing l s g y
  have := @hk.law 𝔰.n s s; simp_all [upperPairing, descConv, unipotentBelow_eq_besselU,
    hk.conj_eq_self, unitriGroup_top_eq_besselU.le (unitriGroup_anti (by lia) hs.1)]
  repeat rw [hk.upperPairing_eq_integral_succ.2]
  apply IdentDistrib.integral_eq ⟨_, _, ext_of_lintegral _ fun _ _ ↦ by rw [lintegral_map, eq_comm,
    lintegral_map, ← lintegral_floorMeasure_mul_right (floorGroup_anti hl) _ hs] <;> first
    | fun_prop | grind [mul_assoc]⟩ <;> fun_prop

@[fun_prop] lemma measurable_weightedSquareSum : Measurable ↿(F.weightedSquareSum k · l ·) := by
  fun_induction F.weightedSquareSum k 1 l 1 <;> unfold weightedSquareSum <;> simp_all <;> fun_prop

lemma weightedSquare_invariant_support : (unitriGroup (j + 1)).FixesLeft (F.weightedSquare j k x) ∧
  ∀ g, ¬F.IsNear (j + 1) g → F.weightedSquare j k x g = 0 :=
  ⟨fun s h ↦ (exists_floorGroup_mul_unipotentBelow (unitriGroup_anti le_self_add h)).elim fun _ ⟨_,
  _, b, _⟩ ↦ by simp_all [weightedSquare,
  hk.upperPairing_invariant, mul_mem_cancel_right, unipotentBelow_le_unitriGroup b, hk.law,
  ← ofReal_norm], by simp; grind [isNear_of_upperPairing_ne_zero]⟩

lemma weightedSquareSum_invariant_support x : (unitriGroup j).FixesLeft
  (F.weightedSquareSum k x j) ∧ ∀ g, ¬F.IsNear j g → F.weightedSquareSum k x j g = 0 := by
  fun_induction F.weightedSquareSum k x j 1 <;> simp <;> unfold weightedSquareSum <;> simp_all
  use fun s h g ↦ .trans (by simp) (lintegral_floorMeasure_mul_right le_top
    (by simp_all [hk.weightedSquare_invariant_support, hk.mono]) ⟨h, ⟨⟩⟩)
  grind [exists_ne_zero_of_ae F.ae_floorMeasure_mem, hk.weightedSquare_invariant_support.2, mono,
    add_zero, IsNear.of_floorGroup_mul]

/-- Cauchy–Schwarz on floor l, for a kernel k (`Level.IsPairingKernel`). If |k_{l+1}(σg, σy)|² ≤
u(σg)v(σ) on H_l, with u, v measurable and u of mass ≤ K on near points (`Level.FloorMassLe`),
then (∫|k_{l+1}(σg, σy)| dθ_l)² ≤ K ∫ v dθ_l. -/
lemma pivotModulus_sq_le {u v} (hK : F.FloorMassLe l K u) (h :
  ∀ σ ∈ GT l, ‖F.upperPairing (l + 1) k (σ * g) (σ * y)‖ₑ ^ 2 ≤ u (σ
  * g) * v σ := by exact fun _ _ ↦ (one_mul _).ge) (hu : Measurable u := by fun_prop) (hv :
  Measurable v := by fun_prop) : F.pivotModulus l k g y ^ 2 ≤ K * ∫⁻ σ, v σ ∂F.floorMeasure l := by
  nth_grw 1 [pivotModulus, ← lintegral_floorMeasure_congr rfl eqOn_indicator,
    ← setLIntegral_eq_of_support_subset, sq_lintegral_le, hK g, restrict_le_self]
  repeat first | fun_prop | simp [indicator, subset_def]; grind [isNear_of_upperPairing_ne_zero,
    zero_le]

lemma selfNorm_eq_add_succ (hl : l ≤ 𝔰.ϱ) : F.selfNorm l k x = ∫⁻ g, F.weightedSquare l k x
  g ∂descConv F.floorMeasure 0 (l + 1) + F.selfNorm (l + 1) k x := by erw [← lintegral_add_left,
  descConv_succ, lintegral_mconv_symm] <;> first | fun_prop | grind [weightedSquareSum, selfNorm]

lemma selfNorm_le_selfNorm_zero (hl : l ≤ 𝔰.n) : F.selfNorm l k x ≤ F.selfNorm 0 k x := by
  induction' l with l <;> grind [selfNorm_eq_add_succ (l := l), le_add_self]
