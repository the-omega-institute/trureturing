/- GID: D5/S3/Divergence/JensenShannonBallMajorizationRefutation
   generality: I
   mirror-B: D5/B/S3/Divergence/JensenShannonBallMajorizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Divergence/JensenShannonBallMajorizationRefutation.claim; result=D5/S3/Divergence/JensenShannonBallMajorizationRefutation.result; claim=D5/S3/Divergence/JensenShannonBallMajorizationRefutation.claim
   digest: A three-point Jensen--Shannon ball has no majorization-minimizer. -/

import D5.S3.TotalVariation.CycleSingleCutMinimax
import D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing

/-!
For natural logarithms, a Jensen--Shannon sublevel set need not have a point majorized by
all its members. The square-root metric has the same balls after rescaling the radius.
Majorization uses descending partial sums, including equality of the total sums.
-/

set_option linter.style.longLine false

noncomputable section
open scoped BigOperators
open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
open D5.S3.TotalVariation.CycleSingleCutMinimax

namespace D5.S3.Divergence.JensenShannonBallMajorizationRefutation

/-- Jensen--Shannon divergence with natural logarithms and the `0 log 0 = 0` convention.
If just one coordinate is zero its weighted logarithm vanishes; if both are zero both
summands vanish, since real division and the real logarithm are totalized at zero. -/
def jensenShannon {d : ℕ} (p q : Fin d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, (p i * Real.log (2 * p i / (p i + q i)) +
    q i * Real.log (2 * q i / (p i + q i)))

/-- Equation (3.1), restricted to its majorization-minimum clause.
In Eq. (2.3), `moreMixed r q` is `r ≺ q`: the descending partial sums of `r` are at most
those of `q`, and their total sums agree. -/
def IsMajorizationMinimizer {d : ℕ} (B : Set (Fin d → ℝ)) (r : Fin d → ℝ) : Prop :=
  r ∈ B ∧ ∀ q ∈ B, moreMixed r q

/-- The Jensen--Shannon clause of Question 1, with a positive divergence threshold. -/
def claim : Prop :=
  ∀ (d : ℕ) (p : Fin d → ℝ), Probability p → ∀ t : ℝ, 0 < t →
    ∃ r, IsMajorizationMinimizer {q | Probability q ∧ jensenShannon p q ≤ t} r

private def term (c x : ℝ) : ℝ :=
  (c * Real.log (2 * c / (c + x)) + x * Real.log (2 * x / (c + x))) / 2

private lemma support_gap {c x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    term c x - term c y - Real.log (2 * y / (c + y)) / 2 * (x - y) =
      -(c * Real.log ((c + x) / (c + y)) +
        x * Real.log (y * (c + x) / (x * (c + y)))) / 2 := by
  have hcx : c + x ≠ 0 := ne_of_gt (add_pos hc hx)
  have hcy : c + y ≠ 0 := ne_of_gt (add_pos hc hy)
  have first : Real.log (2 * c / (c + x)) - Real.log (2 * c / (c + y)) =
      -Real.log ((c + x) / (c + y)) := by
    rw [Real.log_div (by positivity) hcx, Real.log_div (by positivity) hcy,
      Real.log_div hcx hcy]
    ring
  have second : Real.log (2 * x / (c + x)) - Real.log (2 * y / (c + y)) =
      -Real.log (y * (c + x) / (x * (c + y))) := by
    rw [Real.log_div (by positivity) hcx, Real.log_div (by positivity) hcy,
      Real.log_div (mul_ne_zero hy.ne.symm hcx) (mul_ne_zero hx.ne.symm hcy),
      Real.log_mul two_ne_zero hx.ne.symm, Real.log_mul two_ne_zero hy.ne.symm,
      Real.log_mul hy.ne.symm hcx, Real.log_mul hx.ne.symm hcy]
    ring
  dsimp only [term]
  linear_combination c / 2 * first + x / 2 * second

private lemma supporting_line_pos {c x y : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hy : 0 < y) :
    term c y + Real.log (2 * y / (c + y)) / 2 * (x - y) ≤ term c x ∧
    (term c x = term c y + Real.log (2 * y / (c + y)) / 2 * (x - y) → x = y) := by
  have hu : 0 < (c + x) / (c + y) := div_pos (add_pos hc hx) (add_pos hc hy)
  have hv : 0 < y * (c + x) / (x * (c + y)) := by positivity
  have boundc := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hu) hc.le
  have boundx := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hv) hx.le
  have cancel : c * ((c + x) / (c + y) - 1) +
      x * (y * (c + x) / (x * (c + y)) - 1) = 0 := by
    field_simp
    ring
  have gap := support_gap hc hx hy
  constructor
  · linarith
  · intro heq
    by_contra hne
    have hu_ne : (c + x) / (c + y) ≠ 1 := by
      intro h
      have ratio_eq := (div_eq_one_iff_eq (ne_of_gt (add_pos hc hy))).mp h
      exact hne (by linarith)
    have strictc := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos hu hu_ne) hc
    linarith

private lemma supporting_line {c x y : ℝ} (hc : 0 < c) (hx : 0 ≤ x)
    (hy : 0 < y) :
    term c y + Real.log (2 * y / (c + y)) / 2 * (x - y) ≤ term c x ∧
    (term c x = term c y + Real.log (2 * y / (c + y)) / 2 * (x - y) → x = y) := by
  rcases hx.eq_or_lt with hzero | hpos
  · subst x
    have ratio : 2 * c / (c + 0) = 2 := by field_simp; ring
    have logc : Real.log (2 * c / (c + y)) =
        Real.log 2 - Real.log ((c + y) / c) := by
      rw [Real.log_div (by positivity) (ne_of_gt (add_pos hc hy)),
        Real.log_mul two_ne_zero hc.ne.symm,
        Real.log_div (ne_of_gt (add_pos hc hy)) hc.ne.symm]
      ring
    have gap : term c 0 - term c y - Real.log (2 * y / (c + y)) / 2 * (0 - y) =
        c / 2 * Real.log ((c + y) / c) := by
      unfold term
      rw [ratio, logc]
      ring
    have positive : 0 < c / 2 * Real.log ((c + y) / c) :=
      mul_pos (by positivity) (Real.log_pos ((one_lt_div hc).mpr (by linarith)))
    constructor
    · linarith
    · intro heq
      linarith
  · exact supporting_line_pos hc hpos hy

private def p : Fin 3 → ℝ := ![2/3, 4/15, 1/15]
private def a : Fin 3 → ℝ := ![1/2, 2/5, 1/10]
private def b : Fin 3 → ℝ := ![8/15, 1/3, 2/15]

private lemma probability_data : Probability p ∧ Probability a ∧ Probability b := by
  rw [Probability.eq_1, Probability.eq_1, Probability.eq_1]
  rw [p.eq_1, a.eq_1, b.eq_1]
  norm_num [p.eq_1, a.eq_1, b.eq_1, Fin.sum_univ_succ, Fin.forall_fin_succ]

private lemma js_three (q : Fin 3 → ℝ) :
    jensenShannon p q = term (2/3) (q 0) + term (4/15) (q 1) + term (1/15) (q 2) := by
  rw [jensenShannon.eq_1, term.eq_1, term.eq_1, term.eq_1]
  norm_num [Fin.sum_univ_succ, p.eq_1]
  ring

private lemma term_nonneg_eq {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    0 ≤ term c x ∧ (term c x = 0 → x = c) := by
  have ratio : 2 * c / (c + c) = 1 := by field_simp; ring
  have hs := supporting_line hc hx hc
  simpa only [term, ratio, Real.log_one, mul_zero, add_zero, zero_div, zero_mul,
    zero_add] using hs

private lemma radius_pos : 0 < jensenShannon p a := by
  have h0 := term_nonneg_eq (c := (2/3:ℝ)) (x := (1/2:ℝ)) (by norm_num) (by norm_num)
  have h1 := term_nonneg_eq (c := (4/15:ℝ)) (x := (2/5:ℝ)) (by norm_num) (by norm_num)
  have h2 := term_nonneg_eq (c := (1/15:ℝ)) (x := (1/10:ℝ)) (by norm_num) (by norm_num)
  have strict : 0 < term (2/3) (1/2) := by
    rcases h0.1.eq_or_lt with heq | hlt
    · have equal_masses := h0.2 heq.symm
      norm_num at equal_masses
    · exact hlt
  rw [js_three]
  change 0 < term (2/3) (1/2) + term (4/15) (2/5) + term (1/15) (1/10)
  linarith [h1.1, h2.1]

private lemma descending_data :
    desc a = [(1/2:ℝ), 2/5, 1/10] ∧ desc b = [(8/15:ℝ), 1/3, 2/15] := by
  constructor
  · rw [desc.eq_1]
    change ([(1/2:ℝ), 2/5, 1/10].mergeSort (fun x y => decide (y ≤ x))) = _
    exact List.mergeSort_of_pairwise (by norm_num)
  · rw [desc.eq_1]
    change ([(8/15:ℝ), 1/3, 2/15].mergeSort (fun x y => decide (y ≤ x))) = _
    exact List.mergeSort_of_pairwise (by norm_num)

private lemma majorized_bounds {r : Fin 3 → ℝ} (h : moreMixed r a) :
    ∀ i, 1/10 ≤ r i ∧ r i ≤ 1/2 := by
  have h1 := h.1 1 (by decide)
  have h2 := h.1 2 (by decide)
  have h3 := h.2
  have length : (desc r).length = 3 := by
    rw [desc.eq_1, List.length_mergeSort, List.length_ofFn]
  obtain ⟨u, v, w, sorted_eq⟩ := List.length_eq_three.mp length
  have ordered : (desc r).Pairwise (fun x y : ℝ => y ≤ x) := by
    rw [desc.eq_1]
    exact List.pairwise_mergeSort' (fun x y : ℝ => y ≤ x) (List.ofFn r)
  rw [sorted_eq] at ordered
  norm_num at ordered
  rw [prefixSum.eq_1] at h1
  norm_num [prefixSum.eq_1, sorted_eq, descending_data.1] at h1 h2 h3
  intro i
  have membership : r i ∈ desc r := by
    rw [desc.eq_1, List.mem_mergeSort]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  rw [sorted_eq] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with heq | heq | heq <;> rw [heq] <;> constructor <;> linarith

private lemma unique_candidate {r : Fin 3 → ℝ} (hr : Probability r)
    (hm : moreMixed r a) (hball : jensenShannon p r ≤ jensenShannon p a) : r = a := by
  have bounds := majorized_bounds hm
  have h0 := supporting_line (c := (2/3:ℝ)) (x := r 0) (y := (1/2:ℝ))
    (by norm_num) (le_trans (by norm_num : (0:ℝ) ≤ 1/10) (bounds 0).1) (by norm_num)
  have h1 := supporting_line (c := (4/15:ℝ)) (x := r 1) (y := (2/5:ℝ))
    (by norm_num) (le_trans (by norm_num : (0:ℝ) ≤ 1/10) (bounds 1).1) (by norm_num)
  have h2 := supporting_line (c := (1/15:ℝ)) (x := r 2) (y := (1/10:ℝ))
    (by norm_num) (le_trans (by norm_num : (0:ℝ) ≤ 1/10) (bounds 2).1) (by norm_num)
  norm_num at h0 h1 h2
  have total : r 0 + r 1 + r 2 = 1 := by
    simpa [Probability, Fin.sum_univ_succ, add_assoc] using hr.2
  have logdiff : Real.log (6/7:ℝ) - Real.log (6/5:ℝ) = Real.log (5/7:ℝ) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    congr 1
    norm_num
  have tangent : 0 ≤ Real.log (6/7:ℝ) / 2 * (r 0 - 1/2) +
      Real.log (6/5:ℝ) / 2 * (r 1 - 2/5) +
      Real.log (6/5:ℝ) / 2 * (r 2 - 1/10) := by
    have sign := mul_nonneg_of_nonpos_of_nonpos
      (Real.log_neg (by norm_num : (0:ℝ) < 5/7) (by norm_num)).le
      (sub_nonpos.mpr (bounds 0).2)
    have tangent_eq : Real.log (6/7:ℝ) / 2 * (r 0 - 1/2) +
        Real.log (6/5:ℝ) / 2 * (r 1 - 2/5) +
        Real.log (6/5:ℝ) / 2 * (r 2 - 1/10) =
        Real.log (5/7:ℝ) / 2 * (r 0 - 1/2) := by
      linear_combination Real.log (6/5:ℝ) / 2 * total + (r 0 - 1/2) / 2 * logdiff
    rw [tangent_eq]
    linarith
  rw [js_three, js_three] at hball
  change term (2/3) (r 0) + term (4/15) (r 1) + term (1/15) (r 2) ≤
    term (2/3) (1/2) + term (4/15) (2/5) + term (1/15) (1/10) at hball
  have equal0 : term (2/3) (r 0) = term (2/3) (1/2) +
      Real.log (6/7:ℝ) / 2 * (r 0 - 1/2) := by linarith [h0.1, h1.1, h2.1]
  have equal1 : term (4/15) (r 1) = term (4/15) (2/5) +
      Real.log (6/5:ℝ) / 2 * (r 1 - 2/5) := by linarith [h0.1, h1.1, h2.1]
  have equal2 : term (1/15) (r 2) = term (1/15) (1/10) +
      Real.log (6/5:ℝ) / 2 * (r 2 - 1/10) := by linarith [h0.1, h1.1, h2.1]
  funext i
  fin_cases i
  · exact h0.2 equal0
  · exact h1.2 equal1
  · exact h2.2 equal2

private lemma ball_log_identity :
    60 * (jensenShannon p b - jensenShannon p a) =
      Real.log ((4:ℝ) * 5^55 * 7^35 / 3^144) := by
  have l6 : Real.log (6:ℝ) = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
    norm_num
  have l8 : Real.log (8:ℝ) = 3 * Real.log 2 := by
    convert Real.log_pow (2:ℝ) 3 using 1 <;> norm_num
  have l9 : Real.log (9:ℝ) = 2 * Real.log 3 := by
    convert Real.log_pow (3:ℝ) 2 using 1 <;> norm_num
  have l87 : Real.log (8/7:ℝ) = 3 * Real.log 2 - Real.log 7 := by
    rw [Real.log_div (by norm_num) (by norm_num), l8]
  have l45 : Real.log (4/5:ℝ) = 2 * Real.log 2 - Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_four_eq]
  have l67 : Real.log (6/7:ℝ) = Real.log 2 + Real.log 3 - Real.log 7 := by
    rw [Real.log_div (by norm_num) (by norm_num), l6]
  have l65 : Real.log (6/5:ℝ) = Real.log 2 + Real.log 3 - Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num), l6]
  have l109 : Real.log (10/9:ℝ) = Real.log 2 + Real.log 5 - 2 * Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_ten_eq, l9]
  have l89 : Real.log (8/9:ℝ) = 3 * Real.log 2 - 2 * Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), l8, l9]
  have l23 : Real.log (2/3:ℝ) = Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have l43 : Real.log (4/3:ℝ) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_four_eq]
  have ja : jensenShannon p a = (11/6:ℝ) * Real.log 2 + Real.log 3 / 2 -
      (5/12:ℝ) * Real.log 5 - (7/12:ℝ) * Real.log 7 := by
    rw [js_three]
    change term (2/3) (1/2) + term (4/15) (2/5) + term (1/15) (1/10) = _
    norm_num [term]
    rw [l87, l67, l45, l65]
    ring
  have jb : jensenShannon p b = (28/15:ℝ) * Real.log 2 - (19/10:ℝ) * Real.log 3 +
      Real.log 5 / 2 := by
    rw [js_three]
    change term (2/3) (8/15) + term (4/15) (1/3) + term (1/15) (2/15) = _
    norm_num [term]
    rw [l109, l89, l23, l43]
    ring
  have numerator : Real.log ((4:ℝ) * 5^55 * 7^35) =
      2 * Real.log 2 + 55 * Real.log 5 + 35 * Real.log 7 := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_four_eq, Real.log_pow, Real.log_pow]
    norm_num
  have quotient : Real.log ((4:ℝ) * 5^55 * 7^35 / 3^144) =
      2 * Real.log 2 + 55 * Real.log 5 + 35 * Real.log 7 - 144 * Real.log 3 := by
    rw [Real.log_div (by positivity) (by positivity), numerator, Real.log_pow]
    norm_num
  rw [ja, jb, quotient]
  ring

private lemma second_in_ball : jensenShannon p b < jensenShannon p a := by
  have certificate : (4:ℕ) * 5^55 * 7^35 < 3^144 := by norm_num
  have real_certificate : (4:ℝ) * 5^55 * 7^35 < 3^144 := by exact_mod_cast certificate
  have negative : Real.log ((4:ℝ) * 5^55 * 7^35 / 3^144) < 0 :=
    Real.log_neg (by positivity) ((div_lt_one (by positivity)).mpr real_certificate)
  linarith [ball_log_identity]

private lemma not_majorizes : ¬ moreMixed a b := by
  intro h
  have h2 := h.1 2 (by decide)
  rw [prefixSum.eq_1] at h2
  norm_num [prefixSum.eq_1, descending_data.1, descending_data.2] at h2

/-- The Jensen--Shannon ball at `p = (2/3,4/15,1/15)` with threshold `J(p,a)`
has no majorization-minimizer, where `a = (1/2,2/5,1/10)`. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨r, hr, hmin⟩ := h 3 p probability_data.1 (jensenShannon p a) radius_pos
  have forced : r = a := unique_candidate hr.1
    (hmin a ⟨probability_data.2.1, le_rfl⟩) hr.2
  subst r
  exact not_majorizes (hmin b ⟨probability_data.2.2, second_in_ball.le⟩)

end D5.S3.Divergence.JensenShannonBallMajorizationRefutation
