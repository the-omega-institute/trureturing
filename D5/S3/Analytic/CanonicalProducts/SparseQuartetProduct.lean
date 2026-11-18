/- GID: D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct
   generality: G
   mirror-B: D5/B/S3/Analytic/CanonicalProducts/SparseQuartetProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse reciprocal-mass quartet products have actual convergence and fast-ratio rigidity. -/

import D5.S3.Analytic.CanonicalProducts.SummableLinearProduct
import D5.S3.Analytic.Entire.ZeroExponentialTypeRigidity
import D5.S3.Analytic.Asymptotics.PositiveSubexponentialRatio
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped BigOperators Topology
open D5.S3.Analytic.CanonicalProducts.SummableLinearProduct
open D5.S3.Analytic.Asymptotics.PositiveSubexponentialRatio

namespace D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct

noncomputable def C (β γ : ℝ) (z : ℂ) : ℂ :=
  (((z - (β : ℂ)) ^ 2 + (γ : ℂ) ^ 2) *
    ((z - ((1 - β : ℝ) : ℂ)) ^ 2 + (γ : ℂ) ^ 2)) /
  (((β : ℂ) ^ 2 + (γ : ℂ) ^ 2) *
    (((1 - β : ℝ) : ℂ) ^ 2 + (γ : ℂ) ^ 2))

def X (β γ : ℝ) : ℝ := γ ^ 2 + β * (1 - β)
def Y (β γ : ℝ) : ℝ := γ * (2 * β - 1)
def Q (β γ : ℝ) : ℝ := X β γ ^ 2 + Y β γ ^ 2

noncomputable def realFactor (β γ x : ℝ) : ℝ :=
  ((x * (x - 1) + X β γ) ^ 2 + Y β γ ^ 2) / Q β γ

noncomputable def root (β γ : ℝ) (q : Fin 4) : ℂ :=
  ![(β : ℂ) + (γ : ℂ) * Complex.I, (β : ℂ) - (γ : ℂ) * Complex.I,
    ((1 - β : ℝ) : ℂ) + (γ : ℂ) * Complex.I,
    ((1 - β : ℝ) : ℂ) - (γ : ℂ) * Complex.I] q

abbrev Slot {I : Type*} (m : I → ℕ) := Σ i : I, Fin (m i) × Fin 4

noncomputable def coefficient {I : Type*} (β γ : I → ℝ) (m : I → ℕ)
    (k : Slot m) : ℂ := -(root (β k.1) (γ k.1) k.2.2)⁻¹

noncomputable def actualProduct {I : Type*} (β γ : I → ℝ) (m : I → ℕ)
    (z : ℂ) : ℂ := ∏' i : I, C (β i) (γ i) z ^ m i

noncomputable def realProduct {I : Type*} (β γ : I → ℝ) (m : I → ℕ)
    (x : ℝ) : ℝ := ∏' i : I, realFactor (β i) (γ i) x ^ m i

structure Data (I : Type*) where
  β : I → ℝ
  γ : I → ℝ
  m : I → ℕ
  beta_pos : ∀ i, 0 < β i
  beta_lt_one : ∀ i, β i < 1
  gamma_pos : ∀ i, 0 < γ i
  reciprocal_summable : Summable (fun i => (m i : ℝ) / γ i)

noncomputable def Data.product {I : Type*} (S : Data I) : ℂ → ℂ :=
  actualProduct S.β S.γ S.m

noncomputable def Data.realProduct {I : Type*} (S : Data I) : ℝ → ℝ :=
  _root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.realProduct S.β S.γ S.m

noncomputable def difference {I J : Type*} (S : Data I) (T : Data J) (b : ℂ)
    (z : ℂ) : ℂ := Complex.exp b * S.product z - T.product z

private lemma X_positive {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < γ) : 0 < X β γ := by
  dsimp [X]
  exact add_pos (sq_pos_of_pos hγ) (mul_pos hβ0 (sub_pos.mpr hβ1))

private lemma Q_positive {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < γ) : 0 < Q β γ := by
  dsimp [Q]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (X_positive hβ0 hβ1 hγ))
    (sq_nonneg _)

-- The identity is polynomial, and imposes no distinct-root condition.
private lemma C_eq_t (β γ : ℝ) (z : ℂ) :
    C β γ z = ((z * (z - 1) + (X β γ : ℂ)) ^ 2 + (Y β γ : ℂ) ^ 2) /
      (Q β γ : ℂ) := by
  unfold C Q X Y
  push_cast
  congr 1 <;> ring

private lemma C_real_axis (β γ x : ℝ) :
    C β γ (x : ℂ) = (realFactor β γ x : ℂ) := by
  rw [C_eq_t]
  simp only [realFactor, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]

private lemma C_reflection (β γ : ℝ) (z : ℂ) : C β γ (1 - z) = C β γ z := by
  have ht : (1 - z) * (1 - z - 1) = z * (z - 1) := by ring
  simp only [C_eq_t, ht]

-- Necessary real-factor algebra extracted from the accepted finite proof;
-- none of that source's Laplace/integral/rounded-stage baseline is used.
private lemma realFactor_expansion {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < γ) (x : ℝ) :
    realFactor β γ x =
      1 + (x * (x - 1)) * (2 * X β γ + x * (x - 1)) / Q β γ := by
  have hQ := Q_positive hβ0 hβ1 hγ
  unfold realFactor
  field_simp [hQ.ne']
  dsimp [Q]
  ring

private lemma realFactor_ge_one {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < γ) {x : ℝ} (hx : 1 ≤ x) : 1 ≤ realFactor β γ x := by
  have ht : 0 ≤ x * (x - 1) := mul_nonneg (by linarith) (by linarith)
  have hX := X_positive hβ0 hβ1 hγ
  have hQ := Q_positive hβ0 hβ1 hγ
  rw [realFactor_expansion hβ0 hβ1 hγ]
  exact le_add_of_nonneg_right
    (div_nonneg (mul_nonneg ht (by linarith)) hQ.le)

private lemma gamma_le_norm_root (β : ℝ) {γ : ℝ} (hγ : 0 < γ) (q : Fin 4) :
    γ ≤ ‖root β γ q‖ := by
  have him : |(root β γ q).im| = γ := by
    fin_cases q <;> simp [root, abs_of_pos hγ]
  calc
    γ = |(root β γ q).im| := him.symm
    _ ≤ ‖root β γ q‖ := Complex.abs_im_le_norm _

private lemma coefficient_bound {I : Type*} (S : Data I) (k : Slot S.m) :
    ‖coefficient S.β S.γ S.m k‖ ≤ 1 / S.γ k.1 := by
  rw [coefficient, norm_neg, norm_inv, ← one_div]
  exact one_div_le_one_div_of_le (S.gamma_pos k.1)
    (gamma_le_norm_root (S.β k.1) (S.gamma_pos k.1) k.2.2)

theorem coefficient_norm_budget {I : Type*} (S : Data I) :
    Summable (fun k : Slot S.m => ‖coefficient S.β S.γ S.m k‖) ∧
    (∑' k : Slot S.m, ‖coefficient S.β S.γ S.m k‖) ≤
      4 * ∑' i : I, (S.m i : ℝ) / S.γ i := by
  classical
  let major : Slot S.m → ℝ := fun k => 1 / S.γ k.1
  have hfiber (i : I) :
      (∑' t : Fin (S.m i) × Fin 4, major ⟨i, t⟩) =
        4 * ((S.m i : ℝ) / S.γ i) := by
    simp [major, tsum_fintype, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul]
    <;> ring
  have hmajor : Summable major := by
    apply (summable_sigma_of_nonneg (f := major) (fun k =>
      one_div_nonneg.mpr (S.gamma_pos k.1).le)).2
    refine ⟨fun i => (hasSum_fintype _).summable, ?_⟩
    simpa only [hfiber] using S.reciprocal_summable.mul_left 4
  have hcoef : Summable (fun k : Slot S.m => ‖coefficient S.β S.γ S.m k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (coefficient_bound S) hmajor
  refine ⟨hcoef, ?_⟩
  calc
    (∑' k : Slot S.m, ‖coefficient S.β S.γ S.m k‖) ≤ ∑' k, major k :=
      hcoef.tsum_le_tsum (coefficient_bound S) hmajor
    _ = ∑' i : I, ∑' t : Fin (S.m i) × Fin 4, major ⟨i, t⟩ :=
      Summable.tsum_sigma' (fun i => (hasSum_fintype _).summable) hmajor
    _ = ∑' i : I, 4 * ((S.m i : ℝ) / S.γ i) := tsum_congr hfiber
    _ = 4 * ∑' i : I, (S.m i : ℝ) / S.γ i :=
      S.reciprocal_summable.tsum_mul_left 4

private lemma linear_pair (u : ℝ) {γ : ℝ} (hγ : 0 < γ) (z : ℂ) :
    (1 + z * -((u : ℂ) + (γ : ℂ) * Complex.I)⁻¹) *
      (1 + z * -((u : ℂ) - (γ : ℂ) * Complex.I)⁻¹) =
      ((z - (u : ℂ)) ^ 2 + (γ : ℂ) ^ 2) /
        ((u : ℂ) ^ 2 + (γ : ℂ) ^ 2) := by
  let rp : ℂ := (u : ℂ) + (γ : ℂ) * Complex.I
  let rm : ℂ := (u : ℂ) - (γ : ℂ) * Complex.I
  have hp : rp ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    have : γ = 0 := by simpa [rp] using hi
    exact hγ.ne' this
  have hm : rm ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    have : -γ = 0 := by simpa [rm] using hi
    linarith
  have hden : rp * rm = (u : ℂ) ^ 2 + (γ : ℂ) ^ 2 := by
    apply Complex.ext <;> simp [rp, rm, pow_two, Complex.mul_re, Complex.mul_im] <;> ring
  have hnum : (rp - z) * (rm - z) = (z - (u : ℂ)) ^ 2 + (γ : ℂ) ^ 2 := by
    apply Complex.ext <;> simp [rp, rm, pow_two, Complex.mul_re, Complex.mul_im] <;> ring
  change (1 + z * -rp⁻¹) * (1 + z * -rm⁻¹) = _
  calc
    _ = ((rp - z) / rp) * ((rm - z) / rm) := by
      congr 1 <;> field_simp [hp, hm] <;> ring
    _ = ((rp - z) * (rm - z)) / (rp * rm) := div_mul_div_comm _ _ _ _
    _ = _ := by rw [hnum, hden]

private lemma four_linear_factors (β : ℝ) {γ : ℝ} (hγ : 0 < γ) (z : ℂ) :
    (∏ q : Fin 4, (1 + z * -(root β γ q)⁻¹)) = C β γ z := by
  let L : ℝ → ℂ := fun u =>
    (1 + z * -((u : ℂ) + (γ : ℂ) * Complex.I)⁻¹) *
      (1 + z * -((u : ℂ) - (γ : ℂ) * Complex.I)⁻¹)
  have hfour : (∏ q : Fin 4, (1 + z * -(root β γ q)⁻¹)) = L β * L (1 - β) := by
    dsimp [L]
    simp [root, Fin.prod_univ_succ] <;> ring
  rw [hfour]
  dsimp only [L]
  rw [linear_pair β hγ z, linear_pair (1 - β) hγ z, div_mul_div_comm]
  rfl

private lemma fiber_product {I : Type*} (S : Data I) (i : I) (z : ℂ) :
    (∏ t : Fin (S.m i) × Fin 4,
      (1 + z * coefficient S.β S.γ S.m ⟨i, t⟩)) =
        C (S.β i) (S.γ i) z ^ S.m i := by
  rw [Fintype.prod_prod_type]
  simp only [coefficient, four_linear_factors (S.β i) (S.gamma_pos i) z,
    Fin.prod_const]

theorem actual_product_hasProd {I : Type*} (S : Data I) (z : ℂ) :
    HasProd (fun i : I => C (S.β i) (S.γ i) z ^ S.m i)
      (∏' k : Slot S.m, (1 + z * coefficient S.β S.γ S.m k)) := by
  have hlinear := (entire_zero_type_of_summable_norm
    (coefficient S.β S.γ S.m) (coefficient_norm_budget S).1).1 z
  -- HasProd.sigma is valid in ℂ as a regular topological commutative monoid;
  -- it requires no nonvanishing, so evaluation at actual roots is covered.
  apply hlinear.hasProd.sigma
  intro i
  simpa only [fiber_product S i z] using
    (hasProd_fintype (fun t : Fin (S.m i) × Fin 4 =>
      (1 + z * coefficient S.β S.γ S.m ⟨i, t⟩)))

private lemma actual_eq_linear {I : Type*} (S : Data I) (z : ℂ) :
    S.product z = ∏' k : Slot S.m, (1 + z * coefficient S.β S.γ S.m k) :=
  (actual_product_hasProd S z).tprod_eq

theorem actual_product_analytic {I : Type*} (S : Data I) :
    (∀ z : ℂ, Multipliable (fun i : I => C (S.β i) (S.γ i) z ^ S.m i)) ∧
    Differentiable ℂ S.product ∧
    S.product 0 = 1 ∧ S.product 1 = 1 ∧
    (∀ z : ℂ, S.product (1 - z) = S.product z) ∧
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 1 ≤ A ∧
      ∀ z : ℂ, ‖S.product z‖ ≤ A * Real.exp (ε * ‖z‖) := by
  have hgeneric := entire_zero_type_of_summable_norm
    (coefficient S.β S.γ S.m) (coefficient_norm_budget S).1
  have hfun : S.product =
      (fun z : ℂ => ∏' k : Slot S.m, (1 + z * coefficient S.β S.γ S.m k)) :=
    funext (actual_eq_linear S)
  have hzero : S.product 0 = 1 := by
    simp [actual_eq_linear S]
  have hreflect (z : ℂ) : S.product (1 - z) = S.product z := by
    unfold Data.product actualProduct
    apply tprod_congr
    intro i
    rw [C_reflection]
  refine ⟨fun z => (actual_product_hasProd S z).multipliable, ?_, hzero,
    ?_, hreflect, ?_⟩
  · rw [hfun]
    exact hgeneric.2.1
  · simpa using (hreflect 0).trans hzero
  · intro ε hε
    obtain ⟨A, hA, hg⟩ := hgeneric.2.2 ε hε
    exact ⟨A, hA, fun z => by rw [actual_eq_linear S z]; exact hg z⟩

private lemma real_hasProd {I : Type*} (S : Data I) (x : ℝ) :
    HasProd (fun i : I => realFactor (S.β i) (S.γ i) x ^ S.m i)
      (S.product (x : ℂ)).re := by
  classical
  have hP : HasProd (fun i : I => C (S.β i) (S.γ i) (x : ℂ) ^ S.m i)
      (S.product (x : ℂ)) := (actual_product_hasProd S (x : ℂ)).multipliable.hasProd
  have hfinite (F : Finset I) :
      (∏ i ∈ F, C (S.β i) (S.γ i) (x : ℂ) ^ S.m i) =
        ((∏ i ∈ F, realFactor (S.β i) (S.γ i) x ^ S.m i : ℝ) : ℂ) := by
    change (∏ i ∈ F, C (S.β i) (S.γ i) (x : ℂ) ^ S.m i) =
      Complex.ofRealHom (∏ i ∈ F, realFactor (S.β i) (S.γ i) x ^ S.m i)
    rw [map_prod Complex.ofRealHom]
    apply Finset.prod_congr rfl
    intro i _
    change C (S.β i) (S.γ i) (x : ℂ) ^ S.m i =
      ((realFactor (S.β i) (S.γ i) x ^ S.m i : ℝ) : ℂ)
    rw [C_real_axis, Complex.ofReal_pow]
  have ht := (Complex.continuous_re.tendsto (S.product (x : ℂ))).comp hP
  change Tendsto (fun F : Finset I =>
    ∏ i ∈ F, realFactor (S.β i) (S.γ i) x ^ S.m i) atTop
    (𝓝 (S.product (x : ℂ)).re)
  simpa only [Function.comp_def, hfinite, Complex.ofReal_re,
    SummationFilter.unconditional_filter] using ht

private lemma product_eq_real {I : Type*} (S : Data I) (x : ℝ) :
    S.product (x : ℂ) = (S.realProduct x : ℂ) := by
  have hr := (real_hasProd S x).multipliable.hasProd
  have hc := hr.map Complex.ofRealHom Complex.continuous_ofReal
  have hp := (actual_product_hasProd S (x : ℂ)).multipliable.hasProd
  have heq : (fun i : I => Complex.ofRealHom
      (realFactor (S.β i) (S.γ i) x ^ S.m i)) =
      (fun i : I => C (S.β i) (S.γ i) (x : ℂ) ^ S.m i) := by
    funext i
    change ((realFactor (S.β i) (S.γ i) x ^ S.m i : ℝ) : ℂ) =
      C (S.β i) (S.γ i) (x : ℂ) ^ S.m i
    rw [C_real_axis, Complex.ofReal_pow]
  change HasProd (fun i : I => Complex.ofRealHom
    (realFactor (S.β i) (S.γ i) x ^ S.m i)) (S.realProduct x : ℂ) at hc
  rw [heq] at hc
  exact hp.unique hc

private lemma real_product_ge_one {I : Type*} (S : Data I) {x : ℝ}
    (hx : 1 ≤ x) : 1 ≤ S.realProduct x := by
  classical
  have hr : HasProd (fun i : I => realFactor (S.β i) (S.γ i) x ^ S.m i)
      (S.realProduct x) := (real_hasProd S x).multipliable.hasProd
  apply ge_of_tendsto hr
  exact Eventually.of_forall fun F : Finset I =>
    Finset.one_le_prod₀ fun i _ =>
      one_le_pow₀ (realFactor_ge_one (S.beta_pos i) (S.beta_lt_one i) (S.gamma_pos i) hx)

private lemma log_real_product_sublinear {I : Type*} (S : Data I) :
    Tendsto (fun x : ℝ => Real.log (S.realProduct x) / x) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact hl.trans_le (div_nonneg (Real.log_nonneg (real_product_ge_one S hx))
      (by linarith))
  · intro u hu
    obtain ⟨A, hA, hg⟩ := (actual_product_analytic S).2.2.2.2.2 (u / 2) (by linarith)
    have hApos : 0 < A := zero_lt_one.trans_le hA
    have hconst : Tendsto (fun x : ℝ => Real.log A / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hsmall : ∀ᶠ x : ℝ in atTop, Real.log A / x < u / 2 :=
      hconst.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < u / 2))
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hs hx
    have hxpos : 0 < x := by linarith
    have hp : 0 < S.realProduct x := zero_lt_one.trans_le (real_product_ge_one S hx)
    have hbound : S.realProduct x ≤ A * Real.exp ((u / 2) * x) := by
      have hh := hg (x : ℂ)
      rw [product_eq_real S x, Complex.norm_of_nonneg hp.le,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos] at hh
      exact hh
    have hlog : Real.log (S.realProduct x) ≤ Real.log A + (u / 2) * x := by
      have hh := Real.log_le_log hp hbound
      rwa [Real.log_mul hApos.ne' (Real.exp_ne_zero _), Real.log_exp] at hh
    calc
      Real.log (S.realProduct x) / x ≤ (Real.log A + (u / 2) * x) / x :=
        div_le_div_of_nonneg_right hlog hxpos.le
      _ = Real.log A / x + u / 2 := by field_simp [hxpos.ne'] <;> ring
      _ < u := by linarith

theorem actual_product_real {I : Type*} (S : Data I) :
    (∀ x : ℝ, Multipliable (fun i : I => realFactor (S.β i) (S.γ i) x ^ S.m i)) ∧
    (∀ x : ℝ, S.product (x : ℂ) = (S.realProduct x : ℂ)) ∧
    (∀ x : ℝ, 1 ≤ x → 1 ≤ S.realProduct x) ∧
    Tendsto (fun x : ℝ => Real.log (S.realProduct x) / x) atTop (𝓝 0) := by
  exact ⟨fun x => (real_hasProd S x).multipliable, product_eq_real S,
    fun _ hx => real_product_ge_one S hx, log_real_product_sublinear S⟩

theorem difference_analytic {I J : Type*} (S : Data I) (T : Data J) (b : ℂ) :
    Differentiable ℂ (difference S T b) ∧
    (∀ z : ℂ, difference S T b (1 - z) = difference S T b z) ∧
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 1 ≤ A ∧
      ∀ z : ℂ, ‖difference S T b z‖ ≤ A * Real.exp (ε * ‖z‖) := by
  have hS := actual_product_analytic S
  have hT := actual_product_analytic T
  refine ⟨(hS.2.1.const_mul (Complex.exp b)).sub hT.2.1, ?_, ?_⟩
  · intro z
    simp only [difference, hS.2.2.2.2.1 z, hT.2.2.2.2.1 z]
  · intro ε hε
    obtain ⟨A, hA, hAz⟩ := hS.2.2.2.2.2 ε hε
    obtain ⟨B, hB, hBz⟩ := hT.2.2.2.2.2 ε hε
    refine ⟨‖Complex.exp b‖ * A + B, ?_, ?_⟩
    · exact hB.trans (le_add_of_nonneg_left (mul_nonneg (norm_nonneg _) (by linarith)))
    · intro z
      calc
        ‖difference S T b z‖ ≤ ‖Complex.exp b‖ * ‖S.product z‖ + ‖T.product z‖ := by
          simpa only [difference, norm_mul] using
            norm_sub_le (Complex.exp b * S.product z) (T.product z)
        _ ≤ ‖Complex.exp b‖ * (A * Real.exp (ε * ‖z‖)) +
            B * Real.exp (ε * ‖z‖) :=
          add_le_add (mul_le_mul_of_nonneg_left (hAz z) (norm_nonneg _)) (hBz z)
        _ = (‖Complex.exp b‖ * A + B) * Real.exp (ε * ‖z‖) := by ring

theorem reflected_difference_zero {I J : Type*} (S : Data I) (T : Data J)
    (b : ℂ)
    (hlim : Tendsto (fun x : ℝ => difference S T b (x : ℂ)) atTop (𝓝 0)) :
    difference S T b = 0 := by
  obtain ⟨hd, hr, hg⟩ := difference_analytic S T b
  apply D5.S3.Analytic.Entire.eq_zero_of_zero_exponential_type_of_reflection_of_tendsto_zero
    hd ?_ hr hlim
  intro ε hε
  obtain ⟨A, _, hA⟩ := hg ε hε
  exact ⟨A, hA⟩

private lemma exp_decay {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (-c * x)) atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp
    (tendsto_const_nhds.neg_mul_atTop (by linarith : -c < 0) tendsto_id)

theorem fast_ratio_rigidity {I J : Type*} (S : Data I) (T : Data J)
    (a b : ℂ) (Cerr c : ℝ) (hCerr : 0 ≤ Cerr) (hc : 0 < c)
    (herror : ∀ᶠ x : ℝ in atTop,
      ‖Complex.exp (a * (x : ℂ) + b) * S.product (x : ℂ) / T.product (x : ℂ) - 1‖ ≤
        Cerr * Real.exp (-c * x)) :
    a = 0 ∧ Complex.exp b = 1 ∧ S.product = T.product := by
  let R : ℝ → ℂ := fun x =>
    Complex.exp (a * (x : ℂ) + b) * S.product (x : ℂ) / T.product (x : ℂ)
  have herr0 : Tendsto (fun x : ℝ => R x - 1) atTop (𝓝 0) := by
    apply squeeze_zero_norm' herror
    simpa only [mul_zero] using (exp_decay hc).const_mul Cerr
  have hR : Tendsto R atTop (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using herr0.add_const (1 : ℂ)
  have hS := actual_product_real S
  have hT := actual_product_real T
  have hp : ∀ᶠ x : ℝ in atTop, 0 < S.realProduct x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact zero_lt_one.trans_le (hS.2.2.1 x hx)
  have hq : ∀ᶠ x : ℝ in atTop, 0 < T.realProduct x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact zero_lt_one.trans_le (hT.2.2.1 x hx)
  have ha : a = 0 := by
    apply linear_exponent_eq_zero a b S.realProduct T.realProduct hp hq
      hS.2.2.2 hT.2.2.2
    simpa only [R, hS.2.1, hT.2.1] using hR
  obtain ⟨A, hA, hAz⟩ := (actual_product_analytic T).2.2.2.2.2 (c / 2) (half_pos hc)
  have hDlim : Tendsto (fun x : ℝ => difference S T b (x : ℂ)) atTop (𝓝 0) := by
    have hdecay : Tendsto (fun x : ℝ =>
        (A * Cerr) * Real.exp (-(c / 2) * x)) atTop (𝓝 0) := by
      simpa only [mul_zero] using (exp_decay (half_pos hc)).const_mul (A * Cerr)
    apply squeeze_zero_norm' ?_ hdecay
    filter_upwards [herror, eventually_ge_atTop (1 : ℝ)] with x hxerr hx
    have hxpos : 0 < x := by linarith
    have hqpos : 0 < T.realProduct x := zero_lt_one.trans_le (hT.2.2.1 x hx)
    have hqne : T.product (x : ℂ) ≠ 0 := by
      rw [hT.2.1 x]
      exact Complex.ofReal_ne_zero.mpr hqpos.ne'
    have hid : difference S T b (x : ℂ) = T.product (x : ℂ) * (R x - 1) := by
      dsimp only [difference, R]
      rw [ha, zero_mul, zero_add]
      field_simp [hqne] <;> ring
    have hgrowth : ‖T.product (x : ℂ)‖ ≤ A * Real.exp ((c / 2) * x) := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos] using hAz (x : ℂ)
    calc
      ‖difference S T b (x : ℂ)‖ = ‖T.product (x : ℂ)‖ * ‖R x - 1‖ := by
        rw [hid, norm_mul]
      _ ≤ (A * Real.exp ((c / 2) * x)) * (Cerr * Real.exp (-c * x)) :=
        mul_le_mul hgrowth hxerr (norm_nonneg _)
          (mul_nonneg (by linarith : 0 ≤ A) (Real.exp_pos _).le)
      _ = (A * Cerr) * Real.exp (-(c / 2) * x) := by
        calc
          _ = (A * Cerr) * (Real.exp ((c / 2) * x) * Real.exp (-c * x)) := by ring
          _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring
  have hDzero := reflected_difference_zero S T b hDlim
  have hzero := congrFun hDzero 0
  have hSzero := (actual_product_analytic S).2.2.1
  have hTzero := (actual_product_analytic T).2.2.1
  have heb : Complex.exp b = 1 := by
    simpa only [difference, hSzero, hTzero, mul_one, Pi.zero_apply, sub_eq_zero] using hzero
  refine ⟨ha, heb, ?_⟩
  funext z
  have hz := congrFun hDzero z
  simpa only [difference, heb, one_mul, Pi.zero_apply, sub_eq_zero] using hz

end D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct
