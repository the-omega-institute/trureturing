/- GID: D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.claim; result=D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.result; claim=D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.claim
   digest: A connected real interval has a degree-four Fekete polynomial whose unit lemniscate is not area-minimal. -/

/- result: proof_shape: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (#15369; Refuted)
   Direct frozen dependencies: none (pinned Mathlib only).
   All helper proofs have proof_shape: bind-only and live consumers below.
   Public helper escape registration is not supplied; the linked issue is #15369. -/

import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators ENNReal
open Set

namespace D5.S3.Analytic.Lemniscates.FeketeLemniscateAreaRefutation

def vandermonde {n : ℕ} (a : Fin n → ℂ) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖a i - a j‖

def IsFeketeTuple (K : Set ℂ) {n : ℕ} (a : Fin n → ℂ) : Prop :=
  (∀ i, a i ∈ K) ∧ ∀ b : Fin n → ℂ, (∀ i, b i ∈ K) → vandermonde b ≤ vandermonde a

def InP (K : Set ℂ) (n : ℕ) (p : Polynomial ℂ) : Prop :=
  p.Monic ∧ p.natDegree = n ∧ ∀ z : ℂ, p.IsRoot z → z ∈ K

def lemniscateArea (p : Polynomial ℂ) : ℝ≥0∞ :=
  MeasureTheory.volume {z : ℂ | ‖p.eval z‖ < 1}

def claim : Prop :=
  ∀ (K : Set ℂ) (n : ℕ), 1 ≤ n → ∀ a : Fin n → ℂ,
    IsConnected K → IsCompact K → IsFeketeTuple K a →
    ∀ p : Polynomial ℂ, InP K n p →
      lemniscateArea (∏ i : Fin n, (Polynomial.X - Polynomial.C (a i))) ≤ lemniscateArea p

private lemma real_vandermonde (x : Fin 4 → ℝ) :
    vandermonde (fun i => (x i : ℂ)) = |∏ i : Fin 4, ∏ j ∈ Finset.Ioi i, (x i - x j)| := by
  simp [vandermonde, ← Complex.ofReal_sub, Complex.norm_real, Finset.abs_prod]

private lemma real_vandermonde_perm (x : Fin 4 → ℝ) (σ : Equiv.Perm (Fin 4)) :
    vandermonde (fun i => (x (σ i) : ℂ)) = vandermonde (fun i => (x i : ℂ)) := by
  rw [real_vandermonde, real_vandermonde,
    σ.prod_Ioi_comp_eq_sign_mul_prod (f := fun i j => x i - x j) (fun i j => by ring), abs_mul]
  rcases Int.units_eq_one_or σ.sign with h | h <;> simp [h]

private lemma real_vandermonde_sorted (x : Fin 4 → ℝ) (hx : Monotone x) :
    vandermonde (fun i => (x i : ℂ)) =
      (x 1 - x 0) * (x 2 - x 0) * (x 3 - x 0) *
      (x 2 - x 1) * (x 3 - x 1) * (x 3 - x 2) := by
  have h01 := hx (show (0 : Fin 4) ≤ 1 by decide)
  have h02 := hx (show (0 : Fin 4) ≤ 2 by decide)
  have h03 := hx (show (0 : Fin 4) ≤ 3 by decide)
  have h12 := hx (show (1 : Fin 4) ≤ 2 by decide)
  have h13 := hx (show (1 : Fin 4) ≤ 3 by decide)
  have h23 := hx (show (2 : Fin 4) ≤ 3 by decide)
  have e0 : Finset.Ioi (0 : Fin 4) = {1, 2, 3} := by decide
  have e1 : Finset.Ioi (1 : Fin 4) = {2, 3} := by decide
  have e2 : Finset.Ioi (2 : Fin 4) = {3} := by decide
  have e3 : Finset.Ioi (3 : Fin 4) = ∅ := by decide
  simp [vandermonde, Fin.prod_univ_four, e0, e1, e2, e3, Finset.prod_insert,
    ← Complex.ofReal_sub, Complex.norm_real, abs_of_nonpos (sub_nonpos.mpr h01),
    abs_of_nonpos (sub_nonpos.mpr h02), abs_of_nonpos (sub_nonpos.mpr h03),
    abs_of_nonpos (sub_nonpos.mpr h12), abs_of_nonpos (sub_nonpos.mpr h13),
    abs_of_nonpos (sub_nonpos.mpr h23)]
  ring_nf
  simp

private lemma centered_product_bound (R y z : ℝ) (hR : 0 ≤ R)
    (hy : -R ≤ y ∧ y ≤ R) (hz : -R ≤ z ∧ z ≤ R) (hyz : y ≤ z) :
    2 * R * (R^2-y^2) * (R^2-z^2) * (z-y) ≤
      4 * R * ((z-y)/2) * (R^2-((z-y)/2)^2)^2 := by
  let d := (z-y)/2
  let s := (y+z)/2
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hs : -R ≤ s ∧ s ≤ R := by dsimp [s]; constructor <;> linarith [hy.1,hy.2,hz.1,hz.2]
  have hs2 : s^2 ≤ R^2 := by nlinarith [mul_nonneg (by linarith [hs.1] : 0 ≤ R+s) (by linarith [hs.2] : 0 ≤ R-s)]
  have hcoef : 0 ≤ 2*R^2+2*d^2-s^2 := by nlinarith [sq_nonneg R,sq_nonneg d]
  have hp : (R^2-y^2)*(R^2-z^2) ≤ (R^2-d^2)^2 := by
    have he : (R^2-d^2)^2 - (R^2-y^2)*(R^2-z^2) =
        s^2*(2*R^2+2*d^2-s^2) := by dsimp [s,d]; ring
    nlinarith only [he,mul_nonneg (sq_nonneg s) hcoef]
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg (by positivity : 0 ≤ 4*R) hd)
  dsimp [d] at hm
  nlinarith only [hm]

private lemma one_variable_maximum (R u d : ℝ) (hR : 0 < R) (hu : 0 < u)
    (hsq : 5*u^2=R^2) (hd : 0 ≤ d) (hdR : d ≤ R) :
    d*(R^2-d^2)^2 ≤ u*(R^2-u^2)^2 := by
  have ht : 0 ≤ R^2-d^2 := by nlinarith
  have hid : 256*R^10 - 3125*d^2*(R^2-d^2)^4 =
      (5*d^2-R^2)^2 * (125*(R^2-d^2)^3 + 75*R^2*(R^2-d^2)^2 +
        40*R^4*(R^2-d^2) + 16*R^6) := by ring
  have hpoly : 0 ≤ (125*(R^2-d^2)^3 + 75*R^2*(R^2-d^2)^2 +
        40*R^4*(R^2-d^2) + 16*R^6) := by positivity
  have hbound : 3125*d^2*(R^2-d^2)^4 ≤ 256*R^10 := by
    nlinarith only [hid,mul_nonneg (sq_nonneg (5*d^2-R^2)) hpoly]
  have huval : 3125*u^2*(R^2-u^2)^4 = 256*R^10 := by
    calc
      _ = 3125*u^2*(4*u^2)^4 := by congr 2; nlinarith only [hsq]
      _ = 256*(5*u^2)^5 := by ring
      _ = 256*(R^2)^5 := by rw [hsq]
      _ = _ := by ring
  have hh : (d*(R^2-d^2)^2)^2 ≤ (u*(R^2-u^2)^2)^2 := by
    nlinarith only [hbound,huval]
  nlinarith only [hh,show 0 ≤ d*(R^2-d^2)^2 by positivity,
    show 0 ≤ u*(R^2-u^2)^2 by positivity]

private lemma sorted_interval_maximum (R u : ℝ) (hR : 0 < R) (hu : 0 < u)
    (hsq : 5*u^2=R^2) (x : Fin 4 → ℝ) (hx : Monotone x)
    (hmem : ∀ i, x i ∈ Icc (-R) R) :
    vandermonde (fun i => (x i : ℂ)) ≤ 4*R*u*(R^2-u^2)^2 := by
  have h01 := hx (show (0 : Fin 4) ≤ 1 by decide)
  have h02 := hx (show (0 : Fin 4) ≤ 2 by decide)
  have h03 := hx (show (0 : Fin 4) ≤ 3 by decide)
  have h12 := hx (show (1 : Fin 4) ≤ 2 by decide)
  have h13 := hx (show (1 : Fin 4) ≤ 3 by decide)
  have h23 := hx (show (2 : Fin 4) ≤ 3 by decide)
  have ha : 0 ≤ x 1+R := by linarith [(hmem 1).1]
  have hb : 0 ≤ x 2+R := by linarith [(hmem 2).1]
  have hc : 0 ≤ x 2-x 1 := sub_nonneg.mpr h12
  have he : 0 ≤ R-x 1 := by linarith [(hmem 1).2]
  have hf : 0 ≤ R-x 2 := by linarith [(hmem 2).2]
  rw [real_vandermonde_sorted x hx]
  calc
    _ ≤ (x 1+R)*(x 2+R)*(2*R)*(x 2-x 1)*(R-x 1)*(R-x 2) := by
      gcongr <;> first | positivity | linarith [(hmem 0).1,(hmem 0).2,(hmem 1).1,(hmem 1).2,
        (hmem 2).1,(hmem 2).2,(hmem 3).1,(hmem 3).2]
    _ = 2*R*(R^2-(x 1)^2)*(R^2-(x 2)^2)*(x 2-x 1) := by ring
    _ ≤ 4*R*((x 2-x 1)/2)*(R^2-((x 2-x 1)/2)^2)^2 :=
      centered_product_bound R (x 1) (x 2) hR.le (hmem 1) (hmem 2) h12
    _ ≤ 4*R*u*(R^2-u^2)^2 := by
      have hh := one_variable_maximum R u ((x 2-x 1)/2) hR hu hsq
        (by linarith) (by linarith [(hmem 1).1,(hmem 2).2])
      have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 4*R)
      nlinarith only [hm]

private lemma optimal_vandermonde (R u : ℝ) (hR : 0 < R) (hu : 0 < u)
    (hsq : 5*u^2=R^2) :
    vandermonde (fun i => ((![-R,-u,u,R] : Fin 4 → ℝ) i : ℂ)) =
      4*R*u*(R^2-u^2)^2 := by
  have huR : u ≤ R := by nlinarith [sq_nonneg u]
  have hm : Monotone (![-R,-u,u,R] : Fin 4 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> linarith
  rw [real_vandermonde_sorted _ hm]
  simp
  ring

/-- Four-point Fekete tuples on a real interval. -/
theorem isFeketeTuple_interval_four (R u : ℝ) (hR : 0 < R) (hu : 0 < u)
    (hsq : 5*u^2=R^2) :
    IsFeketeTuple (Complex.ofReal '' Icc (-R) R)
      (fun i => ((![-R,-u,u,R] : Fin 4 → ℝ) i : ℂ)) := by
  have huR : u ≤ R := by nlinarith [sq_nonneg u]
  constructor
  · intro i
    refine ⟨(![-R,-u,u,R] : Fin 4 → ℝ) i, ?_, rfl⟩
    fin_cases i <;> simp <;> first | constructor <;> linarith | linarith
  · intro b hb
    have hb' : ∀ i, ∃ x : ℝ, x ∈ Icc (-R) R ∧ (x : ℂ) = b i := hb
    choose x hx hbx using hb'
    have hbeq : b = fun i => (x i : ℂ) := by ext i; exact (hbx i).symm
    rw [hbeq, optimal_vandermonde R u hR hu hsq,
      ← real_vandermonde_perm x (Tuple.sort x)]
    exact sorted_interval_maximum R u hR hu hsq (x ∘ Tuple.sort x)
      (Tuple.monotone_sort x) (fun i => hx (Tuple.sort x i))

private def rootPolynomial {n : ℕ} (c : Fin n → ℂ) : Polynomial ℂ :=
  ∏ i, (Polynomial.X - Polynomial.C (c i))

private theorem eval_norm {n : ℕ} (c : Fin n → ℂ) (z : ℂ) :
    ‖(rootPolynomial c).eval z‖ = ∏ i, ‖z - c i‖ := by
  simp [rootPolynomial, Polynomial.eval_prod, norm_prod]

theorem ball_subset_lemniscate {n : ℕ} (c : Fin n → ℂ) (k : Fin n) {r : ℝ}
    (hr : 0 < r) (h : r * ∏ j ∈ Finset.univ.erase k, (‖c k - c j‖ + r) < 1) :
    Metric.ball (c k) r ⊆ {z | ‖(∏ i, (Polynomial.X - Polynomial.C (c i))).eval z‖ < 1} := by
  classical
  intro z hz
  have hz' : ‖z - c k‖ < r := by simpa [dist_eq_norm] using hz
  change ‖(rootPolynomial c).eval z‖ < 1
  rw [eval_norm, ← Finset.mul_prod_erase Finset.univ (fun i => ‖z - c i‖) (Finset.mem_univ k)]
  have hp : (∏ j ∈ Finset.univ.erase k, ‖z - c j‖) ≤
      ∏ j ∈ Finset.univ.erase k, (‖c k - c j‖ + r) := by
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro j hj
    calc
      ‖z - c j‖ ≤ ‖z - c k‖ + ‖c k - c j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖c k - c j‖ + r := by linarith
  exact lt_of_le_of_lt (mul_le_mul (le_of_lt hz') hp (Finset.prod_nonneg
    (fun _ _ => norm_nonneg _)) (le_of_lt hr)) h

/-- A finite separated root family admits a covering by discs certified by three distance regimes. -/
theorem lemniscate_subset_balls {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (r : Fin n → ℝ)
    (e t : ℝ) (_he : 0 < e) (ht : 0 < t)
    (sep : ∀ i j, i ≠ j → 2 * t ≤ ‖c i - c j‖)
    (near : ∀ k, 1 ≤ r k * ∏ j ∈ Finset.univ.erase k, (‖c k - c j‖ - e))
    (near_pos : ∀ i j, i ≠ j → e ≤ ‖c i - c j‖)
    (middle : 1 ≤ e * t ^ (n - 1)) (far : 1 ≤ t ^ n) :
    {z | ‖(∏ i, (Polynomial.X - Polynomial.C (c i))).eval z‖ < 1} ⊆
      ⋃ i, Metric.ball (c i) (r i) := by
  classical
  intro z hz
  change ‖(rootPolynomial c).eval z‖ < 1 at hz
  by_contra hout
  have hr : ∀ i, r i ≤ ‖z - c i‖ := by
    simpa only [mem_iUnion, Metric.mem_ball, dist_eq_norm, not_exists, not_lt] using hout
  obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ (fun i => ‖z - c i‖)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hk' : ∀ i, ‖z - c k‖ ≤ ‖z - c i‖ := fun i => hk i (Finset.mem_univ i)
  have triangle : ∀ j, ‖c k - c j‖ ≤ ‖z - c k‖ + ‖z - c j‖ := by
    intro j
    simpa [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub (c k) z (c j)
  have hprod : 1 ≤ ∏ i, ‖z - c i‖ := by
    by_cases hd : ‖z - c k‖ < e
    · calc
        1 ≤ r k * ∏ j ∈ Finset.univ.erase k, (‖c k - c j‖ - e) := near k
        _ ≤ ‖z - c k‖ * ∏ j ∈ Finset.univ.erase k, ‖z - c j‖ := by
          apply mul_le_mul (hr k)
          · apply Finset.prod_le_prod₀
            · intro j hj
              exact sub_nonneg.mpr (near_pos k j (Ne.symm (Finset.mem_erase.mp hj).1))
            · intro j hj
              linarith [triangle j]
          · exact Finset.prod_nonneg fun j hj =>
              sub_nonneg.mpr (near_pos k j (Ne.symm (Finset.mem_erase.mp hj).1))
          · exact norm_nonneg _
        _ = ∏ i, ‖z - c i‖ := Finset.mul_prod_erase Finset.univ (fun i => ‖z - c i‖) (Finset.mem_univ k)
    · by_cases hdt : ‖z - c k‖ < t
      · have hj : ∀ j ∈ Finset.univ.erase k, t ≤ ‖z - c j‖ := by
          intro j hmem
          linarith [triangle j, sep k j (Ne.symm (Finset.mem_erase.mp hmem).1)]
        calc
          1 ≤ e * t ^ (n - 1) := middle
          _ = e * ∏ j ∈ Finset.univ.erase k, t := by simp
          _ ≤ ‖z - c k‖ * ∏ j ∈ Finset.univ.erase k, ‖z - c j‖ :=
            mul_le_mul (le_of_not_gt hd)
              (Finset.prod_le_prod₀ (fun _ _ => le_of_lt ht) hj)
              (by positivity) (norm_nonneg _)
          _ = ∏ i, ‖z - c i‖ := Finset.mul_prod_erase Finset.univ (fun i => ‖z - c i‖) (Finset.mem_univ k)
      · calc
          1 ≤ t ^ n := far
          _ = ∏ i : Fin n, t := by simp
          _ ≤ ∏ i, ‖z - c i‖ := Finset.prod_le_prod₀ (fun _ _ => le_of_lt ht)
              (fun j _ => (le_of_not_gt hdt).trans (hk' j))
  exact (not_le_of_gt (by simpa [eval_norm] using hz)) hprod

private def u : ℝ := Real.sqrt 80
private def a : Fin 4 → ℂ := fun i => ((![-20, -u, u, 20] : Fin 4 → ℝ) i : ℂ)
private def b : Fin 4 → ℂ := fun i => ((![-20, -10, 10, 20] : Fin 4 → ℝ) i : ℂ)
private def innerRadius : Fin 4 → ℝ := ![97/1250000, 217/1250000, 217/1250000, 97/1250000]
private def outerRadius : Fin 4 → ℝ := ![53/625000, 849/5000000, 849/5000000, 53/625000]
private def K : Set ℂ := Complex.ofReal '' Set.Icc (-20) 20

private theorem u_bounds : (8944 / 1000 : ℝ) ≤ u ∧ u ≤ 8945 / 1000 ∧ u ^ 2 = 80 := by
  have hp : 0 ≤ u := Real.sqrt_nonneg _
  have hs : u ^ 2 = 80 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, hs⟩ <;> nlinarith

private theorem b_dist (i j : Fin 4) :
    ‖b i - b j‖ = |(![-20, -10, 10, 20] : Fin 4 → ℝ) i -
      (![-20, -10, 10, 20] : Fin 4 → ℝ) j| := by
  simp only [b, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

private theorem competitor_cover :
    {z | ‖(rootPolynomial b).eval z‖ < 1} ⊆ ⋃ i, Metric.ball (b i) (outerRadius i) := by
  apply lemniscate_subset_balls (by norm_num : 0 < 4) b outerRadius (1/10) 5
    (by norm_num) (by norm_num)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [b_dist] <;> norm_num
  · intro k
    fin_cases k <;> simp [outerRadius, b_dist, show (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} from by decide,
    show (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} from by decide,
    show (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} from by decide,
    show (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} from by decide, Finset.prod_insert] <;> norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [b_dist] <;> norm_num
  · norm_num
  · norm_num

private theorem a_dist (i j : Fin 4) :
    ‖a i - a j‖ = |(![-20, -u, u, 20] : Fin 4 → ℝ) i -
      (![-20, -u, u, 20] : Fin 4 → ℝ) j| := by
  simp only [a, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

private theorem a_dist_upper (i j : Fin 4) :
    ‖a i - a j‖ ≤ |(![-20, -8944/1000, 8944/1000, 20] : Fin 4 → ℝ) i -
      (![-20, -8944/1000, 8944/1000, 20] : Fin 4 → ℝ) j| + 1/500 := by
  have h := u_bounds
  rw [a_dist]
  fin_cases i <;> fin_cases j <;> norm_num <;> rw [abs_le] <;> constructor <;> linarith [h.1, h.2.1]

private theorem inner_cert (k : Fin 4) :
    innerRadius k * ∏ j ∈ Finset.univ.erase k, (‖a k - a j‖ + innerRadius k) < 1 := by
  have hr : 0 ≤ innerRadius k := by fin_cases k <;> norm_num [innerRadius]
  have hp := Finset.prod_le_prod₀ (s := Finset.univ.erase k)
    (f := fun j => ‖a k - a j‖ + innerRadius k)
    (g := fun j => |(![-20, -8944/1000, 8944/1000, 20] : Fin 4 → ℝ) k -
      (![-20, -8944/1000, 8944/1000, 20] : Fin 4 → ℝ) j| + 1/500 + innerRadius k)
    (fun j _ => add_nonneg (norm_nonneg _) hr)
    (fun j _ => by linarith [a_dist_upper k j])
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hp hr)
  fin_cases k <;> simp [innerRadius,
    show (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} from by decide,
    show (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} from by decide,
    show (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} from by decide,
    show (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} from by decide, Finset.prod_insert] <;> norm_num

private theorem inner_disjoint : Pairwise (fun i j =>
    Disjoint (Metric.ball (a i) (innerRadius i)) (Metric.ball (a j) (innerRadius j))) := by
  intro i j hij
  apply Metric.ball_disjoint_ball
  rw [dist_eq_norm, a_dist]
  have h := u_bounds
  fin_cases i <;> fin_cases j <;> simp_all [innerRadius] <;>
    rw [le_abs] <;> first | left; linarith [h.1, h.2.1] | right; linarith [h.1, h.2.1]

private theorem complex_ball_volume (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    MeasureTheory.volume (Metric.ball c r) = ENNReal.ofReal (r ^ 2 * Real.pi) := by
  rw [Complex.volume_ball, ENNReal.ofReal_mul (sq_nonneg r), ENNReal.ofReal_pow hr,
    ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

private theorem fekete_area_lower :
    ENNReal.ofReal ((7231744 / 100000000000000 : ℝ) * Real.pi) ≤
      lemniscateArea (rootPolynomial a) := by
  have hsub : (⋃ i, Metric.ball (a i) (innerRadius i)) ⊆
      {z | ‖(rootPolynomial a).eval z‖ < 1} := by
    refine iUnion_subset fun i => ?_
    exact ball_subset_lemniscate a i (by fin_cases i <;> norm_num [innerRadius]) (inner_cert i)
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 4)))
      (fun i => Metric.ball (a i) (innerRadius i)) := fun i _ j _ hij => inner_disjoint hij
  have hm := MeasureTheory.measure_biUnion_finset (μ := MeasureTheory.volume) hd
    (fun i _ => measurableSet_ball)
  simp only [Finset.mem_univ, iUnion_true] at hm
  have hv : (∑ i, MeasureTheory.volume (Metric.ball (a i) (innerRadius i))) =
      ENNReal.ofReal ((7231744 / 100000000000000 : ℝ) * Real.pi) := by
    have hri : ∀ i, 0 ≤ innerRadius i := by intro i; fin_cases i <;> norm_num [innerRadius]
    simp_rw [complex_ball_volume _ (hri _)]
    rw [Fin.sum_univ_four]
    simp only [innerRadius, Matrix.cons_val]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [← hv, ← hm]
  exact MeasureTheory.measure_mono hsub

private theorem competitor_area_upper : lemniscateArea (rootPolynomial b) ≤
    ENNReal.ofReal ((7204616 / 100000000000000 : ℝ) * Real.pi) := by
  have h := (MeasureTheory.measure_mono competitor_cover).trans
    (MeasureTheory.measure_iUnion_fintype_le MeasureTheory.volume
      (fun i => Metric.ball (b i) (outerRadius i)))
  have hv : (∑ i, MeasureTheory.volume (Metric.ball (b i) (outerRadius i))) =
      ENNReal.ofReal ((7204616 / 100000000000000 : ℝ) * Real.pi) := by
    have hri : ∀ i, 0 ≤ outerRadius i := by intro i; fin_cases i <;> norm_num [outerRadius]
    simp_rw [complex_ball_volume _ (hri _)]
    rw [Fin.sum_univ_four]
    simp only [outerRadius, Matrix.cons_val]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  exact h.trans_eq hv

private theorem competitor_inP : InP K 4 (rootPolynomial b) := by
  constructor
  · exact Polynomial.monic_prod_X_sub_C b _
  constructor
  · rw [rootPolynomial, Polynomial.natDegree_prod_of_monic _ _
      (fun i _ => Polynomial.monic_X_sub_C (b i))]
    simp
  · intro z hz
    obtain ⟨i, _, hi⟩ := (Polynomial.isRoot_prod _ _ z).mp hz
    have hz' : z = b i := sub_eq_zero.mp (by simpa using hi)
    rw [hz']
    refine ⟨(![-20, -10, 10, 20] : Fin 4 → ℝ) i, ?_, rfl⟩
    fin_cases i <;> norm_num

private theorem fekete_tuple : IsFeketeTuple K a := by
  dsimp [K, a, u]
  apply isFeketeTuple_interval_four 20 (Real.sqrt 80) (by norm_num)
    (Real.sqrt_pos.mpr (by norm_num))
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 80 by norm_num)]

theorem result : ¬ claim := by
  intro h
  have hconn : IsConnected K := (isConnected_Icc (by norm_num : (-20 : ℝ) ≤ 20)).image
    Complex.ofReal Complex.continuous_ofReal.continuousOn
  have hcompact : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hclaimed := h K 4 (by norm_num) a hconn hcompact fekete_tuple
    (rootPolynomial b) competitor_inP
  have hgap : ENNReal.ofReal ((7204616 / 100000000000000 : ℝ) * Real.pi) <
      ENNReal.ofReal ((7231744 / 100000000000000 : ℝ) * Real.pi) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    nlinarith [Real.pi_pos]
  exact (not_le_of_gt (competitor_area_upper.trans_lt (hgap.trans_le fekete_area_lower)))
    hclaimed

end D5.S3.Analytic.Lemniscates.FeketeLemniscateAreaRefutation
