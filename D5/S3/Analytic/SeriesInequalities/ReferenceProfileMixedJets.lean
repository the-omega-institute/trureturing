/- GID: D5/S3/Analytic/SeriesInequalities/ReferenceProfileMixedJets
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/ReferenceProfileMixedJets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform mixed derivative scales for compact inverse-scale reference profiles. -/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Tactic

noncomputable section
open Filter Function Set
open scoped Topology ContDiff NNReal ENNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets

/-- The reference function. Its scale-zero value is only a totalization. -/
def reference (φ : ℝ → ℝ) (η a b x q : ℝ) : ℝ :=
  1 / 2 + η * φ ((a + b * q) / x)

/-- First take `ell` derivatives in `q`, then `m` in the positive scale `x`. -/
def xqJet (φ : ℝ → ℝ) (η a b : ℝ) (m ell : ℕ) (x q : ℝ) : ℝ :=
  iteratedDeriv m (fun z => iteratedDeriv ell
    (fun u => reference φ η a b z u - 1 / 2) q) x

/-- First take `m` scale derivatives, then `ell` derivatives in `q`. -/
def qxJet (φ : ℝ → ℝ) (η a b : ℝ) (m ell : ℕ) (x q : ℝ) : ℝ :=
  iteratedDeriv ell (fun u => iteratedDeriv m
    (fun z => reference φ η a b z u - 1 / 2) x) q

/-- The same mixed jet of the full reference, including its constant term. -/
def fullQxJet (φ : ℝ → ℝ) (η a b : ℝ) (m ell : ℕ) (x q : ℝ) : ℝ :=
  iteratedDeriv ell (fun u => iteratedDeriv m
    (fun z => reference φ η a b z u) x) q

private lemma fullQxJet_eq (φ : ℝ → ℝ) (η a b : ℝ) (m ell : ℕ) (x q : ℝ) :
    fullQxJet φ η a b m ell x q =
      qxJet φ η a b m ell x q + if m = 0 ∧ ell = 0 then 1 / 2 else 0 := by
  cases m with
  | zero =>
    cases ell with
    | zero => simp [fullQxJet, qxJet, reference]; ring
    | succ ell =>
      simp [fullQxJet, qxJet, reference, iteratedDeriv_const_add (Nat.succ_pos ell)]
  | succ m =>
    simp [fullQxJet, qxJet, reference, iteratedDeriv_const_add (Nat.succ_pos m)]

private def profile (φ : ℝ → ℝ) (k : ℕ) : ℕ → ℝ → ℝ
  | 0 => φ
  | m + 1 => fun t => -((k + m : ℕ) : ℝ) * profile φ k m t -
      t * deriv (profile φ k m) t

private lemma profile_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (k m : ℕ) :
    ContDiff ℝ ∞ (profile φ k m) := by
  induction m with
  | zero => exact hφ
  | succ m ih =>
    exact (contDiff_const.mul ih).sub
      (contDiff_id.mul (contDiff_infty_iff_deriv.mp ih).2)

private lemma profile_compact {φ : ℝ → ℝ} (hφ : HasCompactSupport φ) (k m : ℕ) :
    HasCompactSupport (profile φ k m) := by
  induction m with
  | zero => exact hφ
  | succ m ih =>
    exact ih.mul_left.sub ih.deriv.mul_left

private lemma iterated_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (ell : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv ell φ) := by
  rw [iteratedDeriv_eq_iterate]
  exact hφ.iterate_deriv ell

private lemma iterated_compact {φ : ℝ → ℝ} (hφ : HasCompactSupport φ) (ell : ℕ) :
    HasCompactSupport (iteratedDeriv ell φ) := by
  induction ell with
  | zero => exact hφ
  | succ ell ih => simpa only [iteratedDeriv_succ] using ih.deriv

private lemma scaled_hasDerivAt {f : ℝ → ℝ} {x y : ℝ} (hx : x ≠ 0)
    (hf : DifferentiableAt ℝ f (y / x)) (k : ℤ) :
    HasDerivAt (fun z => z ^ k * f (y / z))
      (x ^ (k - 1) * ((k : ℝ) * f (y / x) - y / x * deriv f (y / x))) x := by
  have hi := (hasDerivAt_id x).inv hx
  have hc := hf.hasDerivAt.comp x (hi.const_mul y)
  have hp := (hasDerivAt_zpow k x (Or.inl hx)).mul hc
  have hk : x ^ k = x ^ (k - 1) * x := by
    calc
      x ^ k = x ^ ((k - 1) + 1) := by congr 1; omega
      _ = x ^ (k - 1) * x := by rw [zpow_add₀ hx, zpow_one]
  convert! hp using 1
  rw [hk]
  dsimp
  field_simp
  ring

private lemma scaled_iterated {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (k m : ℕ) (y : ℝ) {x : ℝ} (hx : x ≠ 0) :
    iteratedDeriv m (fun z => z ^ (-(k : ℤ)) * φ (y / z)) x =
      x ^ (-((k + m : ℕ) : ℤ)) * profile φ k m (y / x) := by
  induction m generalizing x with
  | zero => simp [profile]
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have heq : (fun z => iteratedDeriv m
        (fun u => u ^ (-(k : ℤ)) * φ (y / u)) z) =ᶠ[𝓝 x]
        (fun z => z ^ (-((k + m : ℕ) : ℤ)) * profile φ k m (y / z)) := by
      filter_upwards [eventually_ne_nhds hx] with z hz
      exact ih hz
    rw [heq.deriv_eq]
    have hd := scaled_hasDerivAt hx
      ((profile_smooth hφ k m).differentiable (by simp) (y / x))
      (-((k + m : ℕ) : ℤ))
    rw [hd.deriv]
    have he : -((k + m : ℕ) : ℤ) - 1 = -((k + (m + 1) : ℕ) : ℤ) := by omega
    rw [he]
    simp [profile]


private lemma affine_iterated {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (ell : ℕ) (a b x q : ℝ) :
    iteratedDeriv ell (fun u => φ ((a + b * u) / x)) q =
      b ^ ell * x ^ (-(ell : ℤ)) * iteratedDeriv ell φ ((a + b * q) / x) := by
  have heq : (fun u => φ ((a + b * u) / x)) =
      (fun u => (fun t => φ (a / x + t)) ((b / x) * u)) := by
    ext u
    congr 1
    ring
  have hs : ContDiff ℝ ell (fun t => φ (a / x + t)) :=
    (hφ.comp (contDiff_const.add contDiff_id)).of_le
      (by exact_mod_cast (le_top : (ell : ℕ∞) ≤ ⊤))
  rw [heq, iteratedDeriv_comp_const_mul (f := fun t => φ (a / x + t)) hs (b / x),
    iteratedDeriv_comp_const_add]
  simp only [zpow_neg, zpow_natCast, div_pow]
  have ht : a / x + (b / x) * q = (a + b * q) / x := by ring
  rw [ht]
  ring

private lemma xq_formula {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a b : ℝ) (m ell : ℕ) {x : ℝ} (hx : x ≠ 0) (q : ℝ) :
    xqJet φ η a b m ell x q =
      η * b ^ ell * x ^ (-((ell + m : ℕ) : ℤ)) *
        profile (iteratedDeriv ell φ) ell m ((a + b * q) / x) := by
  have heq : (fun z => iteratedDeriv ell
      (fun u => reference φ η a b z u - 1 / 2) q) =
      (fun z => (η * b ^ ell) * (z ^ (-(ell : ℤ)) *
        iteratedDeriv ell φ ((a + b * q) / z))) := by
    ext z
    simp only [reference, add_sub_cancel_left, iteratedDeriv_const_mul_field,
      affine_iterated hφ]
    ring
  unfold xqJet
  rw [heq, iteratedDeriv_const_mul_field,
    scaled_iterated (iterated_smooth hφ ell) ell m _ hx]
  ring

private lemma qx_formula {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a b : ℝ) (m ell : ℕ) {x : ℝ} (hx : x ≠ 0) (q : ℝ) :
    qxJet φ η a b m ell x q =
      η * b ^ ell * x ^ (-((m + ell : ℕ) : ℤ)) *
        iteratedDeriv ell (profile φ 0 m) ((a + b * q) / x) := by
  have heq : (fun u => iteratedDeriv m
      (fun z => reference φ η a b z u - 1 / 2) x) =
      (fun u => (η * x ^ (-(m : ℤ))) * profile φ 0 m ((a + b * u) / x)) := by
    ext u
    have hs := scaled_iterated hφ 0 m (a + b * u) hx
    simp only [Nat.cast_zero, neg_zero, zpow_zero, one_mul, zero_add] at hs
    simp only [reference, add_sub_cancel_left, iteratedDeriv_const_mul_field, hs]
    ring
  unfold qxJet
  rw [heq, iteratedDeriv_const_mul_field, affine_iterated (profile_smooth hφ 0 m)]
  have hp : x ^ (-(m : ℤ)) * x ^ (-(ell : ℤ)) = x ^ (-((m + ell : ℕ) : ℤ)) := by
    rw [← zpow_add₀ hx]
    congr 1
    push_cast
    ring
  calc
    _ = η * b ^ ell * (x ^ (-(m : ℤ)) * x ^ (-(ell : ℤ))) *
        iteratedDeriv ell (profile φ 0 m) ((a + b * q) / x) := by ring
    _ = _ := by rw [hp]


private lemma positive_bound {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ A : ℝ, 0 < A ∧ ∀ t, |f t| ≤ A := by
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hf
  refine ⟨max A 0 + 1, by positivity, fun t => ?_⟩
  have h := hA t
  rw [Real.norm_eq_abs] at h
  exact h.trans (by linarith [le_max_left A 0])

private lemma compact_holder {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v, |f u - f v| ≤ C * |u - v| ^ α := by
  obtain ⟨A, hA, hbA⟩ := positive_bound hf.continuous hc
  obtain ⟨B, hB, hbB⟩ := positive_bound
    (contDiff_infty_iff_deriv.mp hf).2.continuous hc.deriv
  let A' : ℝ≥0 := ⟨2 * A, by positivity⟩
  let B' : ℝ≥0 := ⟨B, hB.le⟩
  have hzero : HolderWith A' 0 f := by
    intro u v
    simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one, edist_dist]
    apply ENNReal.ofReal_le_coe.mpr
    change |f u - f v| ≤ 2 * A
    have htri := norm_sub_le (f u) (f v)
    simp only [Real.norm_eq_abs] at htri
    exact htri.trans (by linarith [hbA u, hbA v])
  have hone : HolderWith B' 1 f := by
    apply LipschitzWith.holderWith
    apply lipschitzWith_of_nnnorm_deriv_le (hf.differentiable (by simp))
    intro t
    change ‖deriv f t‖ ≤ B
    simpa only [Real.norm_eq_abs] using hbB t
  have hall := hzero.of_le_of_le hone (t := (⟨α, hα⟩ : ℝ≥0)) (by exact hα) (by exact hα1)
  refine ⟨max (2 * A) B, lt_max_of_lt_left (by positivity), fun u v => ?_⟩
  convert! hall.dist_le u v using 1

private lemma scaled_bound {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (c a b : ℝ) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 < x → ∀ q : ℝ,
      |c * x ^ (-(p : ℤ)) * f ((a + b * q) / x)| ≤ K * x ^ (-(p : ℝ)) := by
  obtain ⟨A, hA, hb⟩ := positive_bound hf hc
  refine ⟨|c| * A + 1, by positivity, fun x hx q => ?_⟩
  have hz : 0 < x ^ (-(p : ℤ)) := zpow_pos hx _
  rw [abs_mul, abs_mul, abs_of_pos hz]
  rw [show x ^ (-(p : ℝ)) = x ^ (-(p : ℤ)) by
    rw [← Real.rpow_intCast]; simp]
  nlinarith [mul_le_mul_of_nonneg_left (hb ((a + b * q) / x))
    (mul_nonneg (abs_nonneg c) hz.le)]

/-- Every mixed order has the same inverse scale in both derivative orders.
The constant is independent of the positive scale and of the evaluation point. -/
private theorem mixed_derivative_scale {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (η a b : ℝ) (m ell : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 < x → ∀ q : ℝ,
      |xqJet φ η a b m ell x q| ≤ K * x ^ (-((m + ell : ℕ) : ℝ)) ∧
      |qxJet φ η a b m ell x q| ≤ K * x ^ (-((m + ell : ℕ) : ℝ)) := by
  obtain ⟨A, hA, hbA⟩ := scaled_bound
    (profile_smooth (iterated_smooth hφ ell) ell m).continuous
    (profile_compact (iterated_compact hc ell) ell m) (η * b ^ ell) a b (ell + m)
  obtain ⟨B, hB, hbB⟩ := scaled_bound
    (iterated_smooth (profile_smooth hφ 0 m) ell).continuous
    (iterated_compact (profile_compact hc 0 m) ell) (η * b ^ ell) a b (m + ell)
  refine ⟨A + B, by positivity, fun x hx q => ?_⟩
  constructor
  · rw [xq_formula hφ η a b m ell hx.ne' q]
    have h := hbA x hx q
    rw [Nat.add_comm ell m] at h ⊢
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hx.le _))
  · rw [qx_formula hφ η a b m ell hx.ne' q]
    exact (hbB x hx q).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hx.le _))

private lemma scaled_holder {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (c a b : ℝ) (p : ℕ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 < x → ∀ q q' : ℝ,
      |c * x ^ (-(p : ℤ)) * f ((a + b * q) / x) -
        c * x ^ (-(p : ℤ)) * f ((a + b * q') / x)| ≤
      K * x ^ (-(p : ℝ) - α) * |q - q'| ^ α := by
  obtain ⟨C, hC, hb⟩ := compact_holder hf hc hα.le hα1
  refine ⟨|c| * C * |b| ^ α + 1, by positivity, fun x hx q q' => ?_⟩
  have hdiff : |(a + b * q) / x - (a + b * q') / x| = |b| / x * |q - q'| := by
    rw [← sub_div, show a + b * q - (a + b * q') = b * (q - q') by ring,
      abs_div, abs_mul, abs_of_pos hx]
    ring
  have hbase := hb ((a + b * q) / x) ((a + b * q') / x)
  rw [hdiff, Real.mul_rpow (by positivity) (abs_nonneg _),
    Real.div_rpow (abs_nonneg _) hx.le] at hbase
  have hscale : x ^ (-(p : ℤ)) / x ^ α = x ^ (-(p : ℝ) - α) := by
    rw [← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast, Real.rpow_sub hx]
  have hpos : 0 ≤ |c| * x ^ (-(p : ℤ)) := by positivity
  have h := mul_le_mul_of_nonneg_left hbase hpos
  rw [← mul_sub, abs_mul, abs_mul, abs_of_pos (zpow_pos hx _)]
  calc
    _ ≤ (|c| * x ^ (-(p : ℤ))) *
        (C * (|b| ^ α / x ^ α * |q - q'| ^ α)) := h
    _ = (|c| * C * |b| ^ α) * x ^ (-(p : ℝ) - α) * |q - q'| ^ α := by
      rw [← hscale]
      ring
    _ ≤ _ := by gcongr; linarith


private lemma centered_holder_scale {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (η a b : ℝ) (m r : ℕ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      (∀ ell ≤ r, ∀ q : ℝ,
        |qxJet φ η a b m ell x q| ≤ K * x ^ (-((m + r : ℕ) : ℝ) - α)) ∧
      (∀ q q' : ℝ, |qxJet φ η a b m r x q - qxJet φ η a b m r x q'| ≤
        K * x ^ (-((m + r : ℕ) : ℝ) - α) * |q - q'| ^ α) := by
  classical
  obtain ⟨C, hC, hbC⟩ := scaled_holder
    (iterated_smooth (profile_smooth hφ 0 m) r)
    (iterated_compact (profile_compact hc 0 m) r) (η * b ^ r) a b (m + r) hα hα1
  choose A hA hbA using fun ell => mixed_derivative_scale hφ hc η a b m ell
  let T : ℝ := ∑ ell ∈ Finset.range (r + 1), A ell
  have hT : 0 ≤ T := Finset.sum_nonneg fun ell _ => (hA ell).le
  refine ⟨T + C, by positivity, fun x hx hx1 => ⟨?_, ?_⟩⟩
  · intro ell hell q
    have hAT : A ell ≤ T := Finset.single_le_sum
      (fun i _ => (hA i).le) (Finset.mem_range.mpr (by omega : ell < r + 1))
    have hpow : x ^ (-((m + ell : ℕ) : ℝ)) ≤ x ^ (-((m + r : ℕ) : ℝ) - α) := by
      apply Real.rpow_le_rpow_of_exponent_ge hx hx1
      have he : (ell : ℝ) ≤ r := by exact_mod_cast hell
      push_cast
      linarith
    exact ((hbA ell x hx q).2).trans
      (mul_le_mul (by linarith : A ell ≤ T + C) hpow
        (Real.rpow_nonneg hx.le _) (by positivity))
  · intro q q'
    rw [qx_formula hφ η a b m r hx.ne' q, qx_formula hφ η a b m r hx.ne' q']
    exact (hbC x hx q q').trans (by
      gcongr
      linarith)

private lemma full_holder_scale {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (η a b : ℝ) (m r : ℕ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      (∀ ell ≤ r, ∀ q : ℝ,
        |fullQxJet φ η a b m ell x q| ≤ K * x ^ (-((m + r : ℕ) : ℝ) - α)) ∧
      (∀ q q' : ℝ, |fullQxJet φ η a b m r x q - fullQxJet φ η a b m r x q'| ≤
        K * x ^ (-((m + r : ℕ) : ℝ) - α) * |q - q'| ^ α) := by
  obtain ⟨K, hK, hb⟩ := centered_holder_scale hφ hc η a b m r hα hα1
  refine ⟨K + 1, by positivity, fun x hx hx1 => ⟨?_, ?_⟩⟩
  · intro ell hell q
    rw [fullQxJet_eq]
    have hp : 1 ≤ x ^ (-((m + r : ℕ) : ℝ) - α) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx hx1 (by
        have : (0 : ℝ) ≤ (m + r : ℕ) := Nat.cast_nonneg _
        linarith)
    have hconst : |(if m = 0 ∧ ell = 0 then 1 / 2 else 0 : ℝ)| ≤ 1 := by
      split <;> norm_num
    have ht := abs_add_le (qxJet φ η a b m ell x q)
      (if m = 0 ∧ ell = 0 then 1 / 2 else 0)
    nlinarith [(hb x hx hx1).1 ell hell q]
  · intro q q'
    simp only [fullQxJet_eq, add_sub_add_right_eq_sub]
    exact ((hb x hx hx1).2 q q').trans (by gcongr; linarith)

/-- Positive-side power profile, extended by zero. -/
def cutoff (χ : ℝ → ℝ) (β t : ℝ) : ℝ :=
  if 0 < t then χ t * t ^ β else 0

private lemma cutoff_eq_mul {χ : ℝ → ℝ} (hs : tsupport χ ⊆ Ioi 0) (β : ℝ) :
    cutoff χ β = fun t => χ t * t ^ β := by
  ext t
  by_cases ht : 0 < t
  · simp [cutoff, ht]
  · have hz : χ t = 0 := by
      by_contra hn
      exact ht (hs (subset_closure hn))
    simp [cutoff, ht, hz]

private lemma cutoff_smooth {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ Ioi 0) (β : ℝ) : ContDiff ℝ ∞ (cutoff χ β) := by
  rw [cutoff_eq_mul hs β]
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    have hz : (0 : ℝ) ∉ tsupport χ := fun h => lt_irrefl (0 : ℝ) (hs h)
    have he := notMem_tsupport_iff_eventuallyEq.mp hz
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with t ht
    simp [ht]
  · exact hχ.contDiffAt.mul (Real.contDiffAt_rpow_const_of_ne ht)

private lemma cutoff_compact {χ : ℝ → ℝ} (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioi 0) (β : ℝ) : HasCompactSupport (cutoff χ β) := by
  rw [cutoff_eq_mul hs β]
  exact hc.mul_right

private lemma ring_scale {s c x p : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hxs : s / c ≤ x) (hp : 0 ≤ p) :
    x ^ (-p) ≤ c ^ p * s ^ (-p) := by
  calc
    x ^ (-p) ≤ (s / c) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos (div_pos hs hc) hxs (by linarith)
    _ = c ^ p * s ^ (-p) := by
      rw [Real.div_rpow hs.le hc.le, Real.rpow_neg hc.le p, div_inv_eq_mul]
      ring

/-- The cutoff reference has uniform bounds for every mixed order on every
proportional ring. Its scale derivatives have the full `C^(r+alpha)` bound:
all derivatives through order `r`, and the `alpha`-Hölder bound of the top
jet, use one constant independent of the ring, scale and evaluation points.
No differentiability or continuity at scale zero is asserted. -/
theorem cutoff_reference_mixed_scales {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ioi 0)
    (β η a b c : ℝ) (hc : 0 < c) :
    (∀ m ell : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ s x : ℝ, 0 < s → 0 < x → s / c ≤ x →
      ∀ q : ℝ,
        |xqJet (cutoff χ β) η a b m ell x q| ≤ K * s ^ (-((m + ell : ℕ) : ℝ)) ∧
        |qxJet (cutoff χ β) η a b m ell x q| ≤ K * s ^ (-((m + ell : ℕ) : ℝ))) ∧
    (∀ (m r : ℕ) (α : ℝ), 0 < α → α ≤ 1 → ∃ K : ℝ, 0 < K ∧
      ∀ s x : ℝ, 0 < s → 0 < x → x ≤ 1 → s / c ≤ x →
        (∀ ell ≤ r, ∀ q : ℝ,
          |fullQxJet (cutoff χ β) η a b m ell x q| ≤
            K * s ^ (-((m + r : ℕ) : ℝ) - α)) ∧
        (∀ q q' : ℝ,
          |fullQxJet (cutoff χ β) η a b m r x q - fullQxJet (cutoff χ β) η a b m r x q'| ≤
            K * s ^ (-((m + r : ℕ) : ℝ) - α) * |q - q'| ^ α)) := by
  have hφ := cutoff_smooth hχ hsχ β
  have hcφ := cutoff_compact hcχ hsχ β
  constructor
  · intro m ell
    obtain ⟨K, hK, hb⟩ := mixed_derivative_scale hφ hcφ η a b m ell
    refine ⟨K * c ^ ((m + ell : ℕ) : ℝ), by positivity, fun s x hs hx hxs q => ?_⟩
    have hr := ring_scale hs hc hxs (show (0 : ℝ) ≤ (m + ell : ℕ) by positivity)
    have h := mul_le_mul_of_nonneg_left hr hK.le
    rw [← mul_assoc] at h
    exact ⟨((hb x hx q).1).trans h, ((hb x hx q).2).trans h⟩
  · intro m r α hα hα1
    obtain ⟨K, hK, hb⟩ := full_holder_scale hφ hcφ η a b m r hα hα1
    refine ⟨K * c ^ (((m + r : ℕ) : ℝ) + α), by positivity,
      fun s x hs hx hx1 hxs => ?_⟩
    have hr := ring_scale hs hc hxs (show (0 : ℝ) ≤ ((m + r : ℕ) : ℝ) + α by positivity)
    rw [neg_add, ← sub_eq_add_neg] at hr
    have h : K * x ^ (-((m + r : ℕ) : ℝ) - α) ≤
        (K * c ^ (((m + r : ℕ) : ℝ) + α)) * s ^ (-((m + r : ℕ) : ℝ) - α) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hr hK.le
    constructor
    · intro ell hell q
      exact ((hb x hx hx1).1 ell hell q).trans h
    · intro q q'
      exact ((hb x hx hx1).2 q q').trans
        (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (abs_nonneg _) _))

end D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets
