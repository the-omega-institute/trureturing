/- GID: D5/S3/Entropy/PoissonBinomial/EntropyDirectionBounds
   generality: G
   mirror-B: D5/B/S3/Entropy/PoissonBinomial/EntropyDirectionBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic divided differences and finite three-point entropy directions. -/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import D5.S3.Quantum.Schatten.PowerMajorization

/-! Estimates for real logarithms and finite mixtures; no probability infrastructure is required. -/

namespace D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds

open scoped BigOperators

private lemma log_numerator_nonneg {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ 1 - x ^ 2 + 2 * (x * Real.log x) := by
  let f : ℝ → ℝ := fun y => 1 - y ^ 2 + 2 * (y * Real.log y)
  have hd (y : ℝ) (hy : 0 < y) :
      HasDerivAt f (2 * (1 - y + Real.log y)) y := by
    convert ((hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_id y).pow 2)).add
      ((Real.hasDerivAt_mul_log hy.ne').const_mul 2) using 1
    · ext z
      simp [f]
    · dsimp
      ring
  have hm : AntitoneOn f (Set.Icc x 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x 1)
    · intro y hy
      exact (hd y (hx.trans_le hy.1)).continuousAt.continuousWithinAt
    · intro y hy
      have hy' : y ∈ Set.Ioo x 1 := by simpa only [interior_Icc] using hy
      exact (hd y (hx.trans hy'.1)).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Set.Ioo x 1 := by simpa only [interior_Icc] using hy
      have hp : 0 < y := hx.trans hy'.1
      have hl := Real.log_le_sub_one_of_pos hp
      linarith
  have hh := hm ⟨le_rfl, hx1⟩ ⟨hx1, le_rfl⟩ hx1
  simpa [f] using hh

private lemma log_ratio_monotone :
    MonotoneOn (fun x : ℝ => Real.log x * (1 + x) / (1 - x)) (Set.Ioo 0 1) := by
  have hd (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
      HasDerivAt (fun y : ℝ => Real.log y * (1 + y) / (1 - y))
        ((1 - x ^ 2 + 2 * (x * Real.log x)) / (x * (1 - x) ^ 2)) x := by
    convert (((Real.hasDerivAt_log hx.1.ne').mul
      ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x))).div
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) (by linarith [hx.2] : 1 - x ≠ 0))
      using 1
    · ext y
      rfl
    · dsimp
      field_simp [hx.1.ne']
      ring
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 1)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (by simpa using hx)).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hx
    exact div_nonneg (log_numerator_nonneg hx'.1 hx'.2.le)
      (mul_nonneg hx'.1.le (sq_nonneg _))

/-- The secant slope of `log` dominates the fixed-product logarithmic slope.
This is the non-strict estimate used in the entropy gradient comparison. -/
theorem log_divided_difference_lower {A B : ℝ} (hB : 0 < B) (hBA : B < A)
    (hA : A < 1) :
    -Real.log (A * B) / (1 - A * B) ≤ (Real.log A - Real.log B) / (A - B) := by
  have hAp : 0 < A := hB.trans hBA
  have hB1 : B < 1 := hBA.trans hA
  have hab : A * B < 1 := lt_trans (mul_lt_mul_of_pos_right hA hB) (by simpa using hB1)
  have hh := log_ratio_monotone ⟨hB, hB1⟩ ⟨hAp, hA⟩ hBA.le
  rw [div_le_div_iff₀ (by linarith : 0 < 1 - B) (by linarith : 0 < 1 - A)] at hh
  rw [Real.log_mul hAp.ne' hB.ne']
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - A * B) (sub_pos.mpr hBA)).2
  nlinarith [hh]

/-- The fixed-product slope strictly exceeds the negative logarithm of the product. -/
theorem neg_log_product_lt_div {A B : ℝ} (hB : 0 < B) (hBA : B < A)
    (hA : A < 1) :
    -Real.log (A * B) < -Real.log (A * B) / (1 - A * B) := by
  have hAp : 0 < A := hB.trans hBA
  have hp : 0 < A * B := mul_pos hAp hB
  have hp1 : A * B < 1 := lt_trans (mul_lt_mul_of_pos_right hA hB) (by simpa using hBA.trans hA)
  have hl : 0 < -Real.log (A * B) := neg_pos.mpr (Real.log_neg hp hp1)
  apply (lt_div_iff₀ (by linarith : 0 < 1 - A * B)).2
  nlinarith [mul_pos hl hp]

section FiniteMixtures

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

private noncomputable def pushMass (r : ι → ℝ) (a : ι → κ) (k : κ) : ℝ :=
  ∑ j, if k = a j then r j else 0

omit [Fintype κ] in
private lemma le_pushMass (r : ι → ℝ) (hr : ∀ j, 0 ≤ r j) (a : ι → κ) (j : ι) :
    r j ≤ pushMass r a (a j) := by
  classical
  simpa only [pushMass, ite_eq_left] using
    (Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) =>
      show 0 ≤ (if a j = a i then r i else 0) from ite_nonneg (hr i) le_rfl)
      (Finset.mem_univ j))

private lemma sum_pushMass_mul (r : ι → ℝ) (a : ι → κ) (f : κ → ℝ) :
    ∑ k, pushMass r a k * f k = ∑ j, r j * f (a j) := by
  classical
  simp only [pushMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  ext j
  simp

private lemma sum_pushMass (r : ι → ℝ) (a : ι → κ) :
    ∑ k, pushMass r a k = ∑ j, r j := by
  simpa using sum_pushMass_mul r a (fun _ => 1)

private noncomputable def mixMass (r : ι → ℝ) (a b c : ι → κ)
    (v0 v1 v2 t : ℝ) (k : κ) : ℝ :=
  (v0 + t) * pushMass r a k + (v1 - 2 * t) * pushMass r b k +
    (v2 + t) * pushMass r c k

omit [Fintype κ] in
private lemma mixMass_nonneg (r : ι → ℝ) (hr : ∀ j, 0 ≤ r j) (a b c : ι → κ)
    (v0 v1 v2 : ℝ) (h0 : 0 ≤ v0) (h1 : 0 ≤ v1) (h2 : 0 ≤ v2) (k : κ) :
    0 ≤ mixMass r a b c v0 v1 v2 0 k := by
  simp only [mixMass, add_zero, mul_zero, sub_zero]
  exact add_nonneg (add_nonneg
    (mul_nonneg h0 (Finset.sum_nonneg fun j _ => ite_nonneg (hr j) le_rfl))
    (mul_nonneg h1 (Finset.sum_nonneg fun j _ => ite_nonneg (hr j) le_rfl)))
    (mul_nonneg h2 (Finset.sum_nonneg fun j _ => ite_nonneg (hr j) le_rfl))

omit [Fintype κ] in
private lemma mixMass_lower (r : ι → ℝ) (hr : ∀ j, 0 ≤ r j) (a b c : ι → κ)
    (v0 v1 v2 : ℝ) (h0 : 0 ≤ v0) (h1 : 0 ≤ v1) (h2 : 0 ≤ v2) (j : ι) :
    v0 * r j ≤ mixMass r a b c v0 v1 v2 0 (a j) ∧
    v1 * r j ≤ mixMass r a b c v0 v1 v2 0 (b j) ∧
    v2 * r j ≤ mixMass r a b c v0 v1 v2 0 (c j) := by
  have ha := mul_le_mul_of_nonneg_left (le_pushMass r hr a j) h0
  have hb := mul_le_mul_of_nonneg_left (le_pushMass r hr b j) h1
  have hc := mul_le_mul_of_nonneg_left (le_pushMass r hr c j) h2
  have hn (k : κ) := (⟨mul_nonneg h0 (Finset.sum_nonneg fun j _ => ite_nonneg (hr j) le_rfl),
    mul_nonneg h1 (Finset.sum_nonneg fun j _ => ite_nonneg (hr j) le_rfl),
    mul_nonneg h2 (Finset.sum_nonneg fun j _ => ite_nonneg (hr j) le_rfl)⟩ :
    0 ≤ v0 * pushMass r a k ∧ 0 ≤ v1 * pushMass r b k ∧ 0 ≤ v2 * pushMass r c k)
  simp only [mixMass, add_zero, mul_zero, sub_zero]
  exact ⟨by linarith [(hn (a j)).2.1, (hn (a j)).2.2],
    by linarith [(hn (b j)).1, (hn (b j)).2.2],
    by linarith [(hn (c j)).1, (hn (c j)).2.1]⟩

private lemma mixMass_sum (r : ι → ℝ) (hr : ∑ j, r j = 1) (a b c : ι → κ)
    (v0 v1 v2 : ℝ) (hv : v0 + v1 + v2 = 1) :
    ∑ k, mixMass r a b c v0 v1 v2 0 k = 1 := by
  simp only [mixMass, add_zero, mul_zero, sub_zero, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_pushMass, hr, mul_one, hv]

private lemma weighted_log_lower {r q v : ℝ} (hr : 0 ≤ r) (hv : 0 < v)
    (hq : v * r ≤ q) : r * (Real.log v + Real.log r) ≤ r * Real.log q := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  have hp : 0 < v * r := mul_pos hv hr
  have hl := Real.log_le_log hp hq
  rw [Real.log_mul hv.ne' hr.ne'] at hl
  exact mul_le_mul_of_nonneg_left hl hr.le

omit [DecidableEq κ] in
private lemma finite_direction_bound (r : ι → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hs : ∑ j, r j = 1) (Q : κ → ℝ) (hQ : ∀ k, 0 ≤ Q k) (hQs : ∑ k, Q k = 1)
    (a b c : ι → κ) (hb : Function.Injective b)
    (v0 v1 v2 : ℝ) (h0 : 0 < v0) (h1 : 0 < v1) (h2 : 0 < v2)
    (hlo : ∀ j, v0 * r j ≤ Q (a j) ∧ v1 * r j ≤ Q (b j) ∧ v2 * r j ≤ Q (c j)) :
    (∑ j, r j * (2 * Real.log (Q (b j)) - Real.log (Q (a j)) - Real.log (Q (c j))))
      ≤ -Real.log (v0 * v2) := by
  classical
  have hsub : ∑ j, Q (b j) ≤ 1 := by
    calc
      ∑ j, Q (b j) = ∑ k ∈ Finset.univ.image b, Q k :=
        (Finset.sum_image (fun i _ j _ hij => hb hij)).symm
      _ ≤ ∑ k, Q k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => hQ k)
      _ = 1 := hQs
  have hterm (j : ι) :
      r j * (Real.log (Q (b j)) - Real.log (r j)) ≤ Q (b j) - r j := by
    rcases (hr j).eq_or_lt with hz | hp
    · simp [← hz, hQ]
    have hqp : 0 < Q (b j) := (mul_pos h1 hp).trans_le (hlo j).2.1
    simpa only [Real.log_div hqp.ne' hp.ne'] using (sub_ge_mul_log_div hp hqp)
  have hmid : (∑ j, r j * (Real.log (Q (b j)) - Real.log (r j))) ≤ 0 := by
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
    rw [Finset.sum_sub_distrib, hs] at hh
    linarith
  have hterm' (j : ι) :
      r j * (2 * Real.log (Q (b j)) - Real.log (Q (a j)) - Real.log (Q (c j))) ≤
        2 * (r j * (Real.log (Q (b j)) - Real.log (r j))) -
          r j * (Real.log v0 + Real.log v2) := by
    have ha := weighted_log_lower (hr j) h0 (hlo j).1
    have hc := weighted_log_lower (hr j) h2 (hlo j).2.2
    nlinarith
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm' j)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hs, one_mul] at hh
  rw [Real.log_mul h0.ne' h2.ne']
  linarith

private lemma mixMass_entropy_hasDerivAt (r : ι → ℝ) (hr : ∀ j, 0 ≤ r j)
    (a b c : ι → κ) (v0 v1 v2 : ℝ) (h0 : 0 < v0) (h1 : 0 < v1) (h2 : 0 < v2) :
    HasDerivAt (fun t => ∑ k, Real.negMulLog (mixMass r a b c v0 v1 v2 t k))
      (∑ j, r j * (2 * Real.log (mixMass r a b c v0 v1 v2 0 (b j)) -
        Real.log (mixMass r a b c v0 v1 v2 0 (a j)) -
        Real.log (mixMass r a b c v0 v1 v2 0 (c j)))) 0 := by
  classical
  let Q := mixMass r a b c v0 v1 v2 0
  let D := fun k => pushMass r a k - 2 * pushMass r b k + pushMass r c k
  have hd (k : κ) : HasDerivAt (fun t => mixMass r a b c v0 v1 v2 t k) (D k) 0 := by
    have he : (fun t => mixMass r a b c v0 v1 v2 t k) = fun t => Q k + t * D k := by
      ext t
      dsimp [Q, D, mixMass]
      ring
    have hh : HasDerivAt (fun t : ℝ => Q k + t * D k) (D k) 0 := by
      convert! (((hasDerivAt_id (0 : ℝ)).mul_const (D k)).const_add (Q k)) using 1 <;>
        simp only [one_mul, id_eq]
    exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => congrFun he t))
  have heach (k : κ) :
      HasDerivAt (fun t => Real.negMulLog (mixMass r a b c v0 v1 v2 t k))
        ((-Real.log (Q k) - 1) * D k) 0 := by
    by_cases hz : Q k = 0
    · have hpa : 0 ≤ pushMass r a k :=
        Finset.sum_nonneg fun j _ => ite_nonneg (hr j) le_rfl
      have hpb : 0 ≤ pushMass r b k :=
        Finset.sum_nonneg fun j _ => ite_nonneg (hr j) le_rfl
      have hpc : 0 ≤ pushMass r c k :=
        Finset.sum_nonneg fun j _ => ite_nonneg (hr j) le_rfl
      have heq : v0 * pushMass r a k + v1 * pushMass r b k +
          v2 * pushMass r c k = 0 := by simpa [Q, mixMass] using hz
      have hza : pushMass r a k = 0 := by
        nlinarith [mul_nonneg h1.le hpb, mul_nonneg h2.le hpc]
      have hzb : pushMass r b k = 0 := by
        nlinarith [mul_nonneg h0.le hpa, mul_nonneg h2.le hpc]
      have hzc : pushMass r c k = 0 := by
        nlinarith [mul_nonneg h0.le hpa, mul_nonneg h1.le hpb]
      have he : (fun t => Real.negMulLog (mixMass r a b c v0 v1 v2 t k)) =
          fun _ => (0 : ℝ) := by
        ext t
        simp [mixMass, hza, hzb, hzc]
      rw [he]
      simpa [D, hza, hzb, hzc] using hasDerivAt_const 0 (0 : ℝ)
    · exact (Real.hasDerivAt_negMulLog hz).comp 0 (hd k)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => heach k)
  have he : (∑ k, (-Real.log (Q k) - 1) * D k) =
      ∑ j, r j * (2 * Real.log (Q (b j)) - Real.log (Q (a j)) - Real.log (Q (c j))) := by
    calc
      _ = (∑ k, pushMass r a k * (-Real.log (Q k) - 1)) -
          2 * (∑ k, pushMass r b k * (-Real.log (Q k) - 1)) +
          ∑ k, pushMass r c k * (-Real.log (Q k) - 1) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        dsimp [D]
        ring
      _ = _ := by
        rw [sum_pushMass_mul, sum_pushMass_mul, sum_pushMass_mul]
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [he] at hsum
  exact hsum

end FiniteMixtures

/-- Three-point convolution of a finite mass vector, extended by zero outside its indices.
The output has indices `0, …, n+1`; the three summands shift `r` by zero, one, and two. -/
noncomputable def threePointMass {n : ℕ} (r : Fin n → ℝ) (v0 v1 v2 t : ℝ)
    (k : Fin (n + 2)) : ℝ :=
  (v0 + t) * (∑ j, if k = j.castAdd 2 then r j else 0) +
    (v1 - 2 * t) * (∑ j, if k = (j.castAdd 1).succ then r j else 0) +
    (v2 + t) * (∑ j, if k = j.succ.succ then r j else 0)

/-- Entropy derivative of the three-point convolution along `(1,-2,1)`, together with
its upper bound. Zero masses of `r` and zero output masses are allowed. The explicit
sum is suitable for chaining with a parameterized pair of Bernoulli coordinates. -/
theorem three_point_entropy_direction_bound {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : ∑ j, r j = 1)
    (v0 v1 v2 : ℝ) (h0 : 0 < v0) (h1 : 0 < v1) (h2 : 0 < v2)
    (hv : v0 + v1 + v2 = 1) :
    let Q := threePointMass r v0 v1 v2 0
    let d := ∑ j, r j * (2 * Real.log (Q ((j.castAdd 1).succ)) -
      Real.log (Q (j.castAdd 2)) - Real.log (Q j.succ.succ))
    HasDerivAt (fun t => ∑ k, Real.negMulLog (threePointMass r v0 v1 v2 t k)) d 0 ∧
      d ≤ -Real.log (v0 * v2) := by
  change HasDerivAt _ _ _ ∧ _
  constructor
  · exact mixMass_entropy_hasDerivAt r hr (fun j => j.castAdd 2)
      (fun j => (j.castAdd 1).succ) (fun j => j.succ.succ) v0 v1 v2 h0 h1 h2
  · have hb : Function.Injective (fun j : Fin n => (j.castAdd 1).succ) :=
      (Fin.succ_injective (n + 1)).comp (Fin.castAdd_injective n 1)
    exact finite_direction_bound r hr hs _
      (mixMass_nonneg r hr _ _ _ v0 v1 v2 h0.le h1.le h2.le)
      (mixMass_sum r hs _ _ _ v0 v1 v2 hv) _ _ _ hb v0 v1 v2 h0 h1 h2
      (mixMass_lower r hr _ _ _ v0 v1 v2 h0.le h1.le h2.le)

end D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds
