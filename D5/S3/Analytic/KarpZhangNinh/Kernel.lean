/- GID: D5/S3/Analytic/KarpZhangNinh/Kernel
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangNinh/Kernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Pochhammer, mathlib/module/Mathlib.Topology.Algebra.Polynomial]
   utility: none
   digest: Paired rising-factorial kernels have at most one negative-to-positive sign change. -/

import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

/-!
admission_basis: escape-witness
The sign propagation for paired Pochhammer products is the content step.
Per-declaration proof_shape and consumers:
* a: definition; consumers: raw, paired_relation, a_zero, a_continuous, Result.delta.
* raw: definition; consumers: paired, paired_relation, Result.delta.
* paired: definition; consumers: paired_relation, paired_sign, Result.tail_nonneg_pos.
* pairPoch: definition; consumers: paired_sign_step, paired_relation, paired_sign.
* a_zero: bind-only; escape_witness: none; consumers: a_continuous, paired_sign,
  Result.tail_nonneg_pos.
* a_continuous: bind-only; escape_witness: none; consumers: Result.tail_nonneg.
* strict_four_product: content; escape_witness: strict_four_product;
  consumers: pair_step_lengths.
* ordered_lengths: content; escape_witness: ordered_lengths;
  consumers: pair_step_lengths.
* four_numbers_step: bind-only; escape_witness: none; consumers: pair_step_lengths.
* pair_step_lengths: content; escape_witness: strict_four_product;
  consumers: paired_sign_step.
* paired_sign_step: content; escape_witness: ordered_lengths;
  consumers: paired_sign.
* paired_relation: bind-only; escape_witness: none; consumers: paired_sign.
* paired_sign: content; escape_witness: paired_sign_step;
  consumers: Result.tail_nonneg_pos.
The strict four-product comparison and ordered-length invariant remain on
both sign proofs' mathematical dependency paths. Direct frozen D5 dependencies: none.
All identities and inequalities quantify over arbitrary lengths and real parameters.
No finite computation, checker, numerical reduction or certified instance occurs.
-/

noncomputable section
open Polynomial Finset

namespace D5.S3.Analytic.KarpZhangNinh.Kernel

/-- The coefficient of positive degree, with zero constant coefficient. -/
def a (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then 0 else (ascPochhammer ℝ (3 * n)).eval t / ((3 * n - 1).factorial : ℝ)

/-- An unpaired Turán coefficient kernel. -/
def raw (μ α β : ℝ) (m k : ℕ) : ℝ :=
  a k (μ + α) * a (m - k) (μ + β) - a k μ * a (m - k) (μ + α + β)

/-- The reflected kernel, counting the middle term once. -/
def paired (μ α β : ℝ) (m k : ℕ) : ℝ :=
  if 2 * k = m then raw μ α β m k else raw μ α β m k + raw μ α β m (m - k)

/-- A paired difference before division by factorials. -/
def pairPoch (a b c : ℝ) (N k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval (a+b) * (ascPochhammer ℝ (N-k)).eval (a+c) +
  (ascPochhammer ℝ k).eval (a+c) * (ascPochhammer ℝ (N-k)).eval (a+b) -
  (ascPochhammer ℝ k).eval a * (ascPochhammer ℝ (N-k)).eval (a+b+c) -
  (ascPochhammer ℝ k).eval (a+b+c) * (ascPochhammer ℝ (N-k)).eval a

@[simp] theorem a_zero (t : ℝ) : a 0 t = 0 := by simp [a]

/-- Each coefficient is polynomial in its parameter, including degree zero. -/
lemma a_continuous (n : ℕ) : Continuous (a n) := by
  by_cases hn : n = 0
  · simp only [hn, a_zero]
    exact continuous_const
  · change Continuous (fun t : ℝ => if n = 0 then 0 else
      (ascPochhammer ℝ (3*n)).eval t / ((3*n-1).factorial:ℝ))
    simp only [if_neg hn]
    exact (ascPochhammer ℝ (3*n)).continuous.div_const _

private theorem strict_four_product (n : ℕ) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hn : 0 < n) :
    (ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval (a+b+c) <
      (ascPochhammer ℝ n).eval (a+b) * (ascPochhammer ℝ n).eval (a+c) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp only [ascPochhammer_succ_eval, ascPochhammer_zero, eval_one,
        Nat.cast_zero, add_zero, one_mul]; nlinarith [mul_pos hb hc]
    | succ n =>
      have hip := ih (by omega)
      rw [ascPochhammer_succ_eval (n+1) a,
        ascPochhammer_succ_eval (n+1) (a+b+c),
        ascPochhammer_succ_eval (n+1) (a+b), ascPochhammer_succ_eval (n+1) (a+c)]
      have hh : (a+((n+1:ℕ):ℝ))*(a+b+c+(n+1:ℕ)) <
          (a+b+(n+1:ℕ))*(a+c+(n+1:ℕ)) := by nlinarith [mul_pos hb hc]
      have hbase : 0 < (ascPochhammer ℝ (n+1)).eval a *
          (ascPochhammer ℝ (n+1)).eval (a+b+c) :=
        mul_pos (ascPochhammer_pos _ _ ha) (ascPochhammer_pos _ _ (by linarith))
      have htop : 0 < (a+b+((n+1:ℕ):ℝ))*(a+c+(n+1:ℕ)) := by positivity
      have h := (mul_lt_mul_of_pos_left hh hbase).trans
        (mul_lt_mul_of_pos_right hip htop)
      convert h using 1 <;> ring

private theorem ordered_lengths {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d)
    {k l : ℕ} (hkl : k ≤ l) :
    (ascPochhammer ℝ k).eval (a+d) * (ascPochhammer ℝ l).eval a ≤
      (ascPochhammer ℝ k).eval a * (ascPochhammer ℝ l).eval (a+d) := by
  have hm : Monotone (fun n => (ascPochhammer ℝ n).eval (a+d) /
      (ascPochhammer ℝ n).eval a) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    have hp := ascPochhammer_pos n a ha
    have hq := ascPochhammer_pos n (a+d) (by linarith)
    apply (div_le_div_iff₀ hp (mul_pos hp (by positivity))).2
    nlinarith [mul_nonneg (mul_nonneg hq.le hp.le) hd]
  have h := (div_le_div_iff₀ (ascPochhammer_pos k a ha)
    (ascPochhammer_pos l a ha)).mp (hm hkl)
  nlinarith

private theorem four_numbers_step {U V R Q x b c C : ℝ}
    (hU : 0 < U) (hV : 0 < V) (hR : 0 < R) (hQ : 0 < Q)
    (hUV : V ≤ U) (hprod : U*V < R*Q) (hsum : R+Q ≤ U+V)
    (hx : 0 < x) (hb : 0 < b) (hc : 0 < c) (hC : x+b+c < C) :
    0 < (C/x-1)*U + (C/(x+b+c)-1)*V -
      (C/(x+b)-1)*R - (C/(x+c)-1)*Q := by
  have hUR : R < U := by
    by_contra h
    have hh : 0 ≤ (R-U)*(R-V) := mul_nonneg (by linarith) (by linarith)
    have hsum' := mul_le_mul_of_nonneg_left hsum hR.le
    nlinarith
  have hUQ : Q < U := by
    by_contra h
    have hh : 0 ≤ (Q-U)*(Q-V) := mul_nonneg (by linarith) (by linarith)
    have hsum' := mul_le_mul_of_nonneg_left hsum hQ.le
    nlinarith
  let D := U+V-R-Q
  let B := U/x+V/(x+b+c)-R/(x+b)-Q/(x+c)
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hrec : 0 < 1/x+1/(x+b+c)-1/(x+b)-1/(x+c) := by
    have he : 1/x+1/(x+b+c)-1/(x+b)-1/(x+c) =
        b*c*(2*x+b+c)/(x*(x+b)*(x+c)*(x+b+c)) := by
      field_simp [ne_of_gt hx, ne_of_gt (show 0 < x+b by positivity),
        ne_of_gt (show 0 < x+c by positivity), ne_of_gt (show 0 < x+b+c by positivity)]
      <;> ring
    rw [he]
    positivity
  have hxb : 0 ≤ 1/(x+b)-1/(x+b+c) := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hxc : 0 ≤ 1/(x+c)-1/(x+b+c) := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))
  have he : B-D/(x+b+c) =
      (U-R)*(1/(x+b)-1/(x+b+c)) +
      (U-Q)*(1/(x+c)-1/(x+b+c)) +
      U*(1/x+1/(x+b+c)-1/(x+b)-1/(x+c)) := by
    dsimp [B, D]
    ring
  have hBD : D/(x+b+c) < B := by
    have h1 := mul_nonneg (sub_nonneg.mpr hUR.le) hxb
    have h2 := mul_nonneg (sub_nonneg.mpr hUQ.le) hxc
    have h3 := mul_pos hU hrec
    linarith
  have hCpos : 0 < C := by linarith
  have hCB := mul_lt_mul_of_pos_left hBD hCpos
  have hden : (x+b+c) ≠ 0 := by positivity
  have hDD : D = (x+b+c)*(D/(x+b+c)) := by field_simp
  have hquot : 0 ≤ D/(x+b+c) := div_nonneg hD (by positivity)
  have hCD := mul_le_mul_of_nonneg_right hC.le hquot
  have heq : (C/x-1)*U + (C/(x+b+c)-1)*V -
      (C/(x+b)-1)*R - (C/(x+c)-1)*Q = C*B-D := by
    dsimp [B, D]
    ring
  rw [heq]
  linarith

private theorem pair_step_lengths {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (n l : ℕ) (hnl : n+1 ≤ l)
    (hsum :
      (ascPochhammer ℝ (n+1)).eval (a+b) * (ascPochhammer ℝ l).eval (a+c) +
      (ascPochhammer ℝ (n+1)).eval (a+c) * (ascPochhammer ℝ l).eval (a+b) ≤
      (ascPochhammer ℝ (n+1)).eval a * (ascPochhammer ℝ l).eval (a+b+c) +
      (ascPochhammer ℝ (n+1)).eval (a+b+c) * (ascPochhammer ℝ l).eval a) :
    (ascPochhammer ℝ n).eval (a+b) * (ascPochhammer ℝ (l+1)).eval (a+c) +
      (ascPochhammer ℝ n).eval (a+c) * (ascPochhammer ℝ (l+1)).eval (a+b) <
      (ascPochhammer ℝ n).eval a * (ascPochhammer ℝ (l+1)).eval (a+b+c) +
      (ascPochhammer ℝ n).eval (a+b+c) * (ascPochhammer ℝ (l+1)).eval a := by
  let U := (ascPochhammer ℝ (n+1)).eval a * (ascPochhammer ℝ l).eval (a+b+c)
  let V := (ascPochhammer ℝ (n+1)).eval (a+b+c) * (ascPochhammer ℝ l).eval a
  let R := (ascPochhammer ℝ (n+1)).eval (a+b) * (ascPochhammer ℝ l).eval (a+c)
  let Q := (ascPochhammer ℝ (n+1)).eval (a+c) * (ascPochhammer ℝ l).eval (a+b)
  have hU : 0 < U := by dsimp [U]; apply mul_pos <;> apply ascPochhammer_pos <;> linarith
  have hV : 0 < V := by dsimp [V]; apply mul_pos <;> apply ascPochhammer_pos <;> linarith
  have hR : 0 < R := by dsimp [R]; apply mul_pos <;> apply ascPochhammer_pos <;> linarith
  have hQ : 0 < Q := by dsimp [Q]; apply mul_pos <;> apply ascPochhammer_pos <;> linarith
  have hUV : V ≤ U := by
    simpa [U, V, add_assoc] using ordered_lengths ha (show 0 ≤ b+c by linarith) hnl
  have hprod : U*V < R*Q := by
    have hk := strict_four_product (n+1) ha hb hc (by omega)
    have hl := strict_four_product l ha hb hc (by omega)
    have hp : 0 < (ascPochhammer ℝ (n+1)).eval a *
        (ascPochhammer ℝ (n+1)).eval (a+b+c) :=
      mul_pos (ascPochhammer_pos _ _ ha) (ascPochhammer_pos _ _ (by linarith))
    have hq : 0 < (ascPochhammer ℝ l).eval (a+b) *
        (ascPochhammer ℝ l).eval (a+c) :=
      mul_pos (ascPochhammer_pos _ _ (by linarith)) (ascPochhammer_pos _ _ (by linarith))
    have hh := (mul_lt_mul_of_pos_left hl hp).trans
      (mul_lt_mul_of_pos_right hk hq)
    convert hh using 1 <;> dsimp [U, V, R, Q] <;> ring
  let x := a+(n:ℝ)
  let C := 2*a+n+l+b+c
  have hx : 0 < x := by dsimp [x]; positivity
  have hC : x+b+c < C := by dsimp [x, C]; have : 0 ≤ (l:ℝ) := Nat.cast_nonneg l; linarith
  have h := four_numbers_step hU hV hR hQ hUV hprod hsum hx hb hc hC
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hxb : x+b ≠ 0 := by positivity
  have hxc : x+c ≠ 0 := by positivity
  have hxbc : x+b+c ≠ 0 := by positivity
  have hEq : (C/x-1)*U + (C/(x+b+c)-1)*V -
      (C/(x+b)-1)*R - (C/(x+c)-1)*Q =
      ((ascPochhammer ℝ n).eval a * (ascPochhammer ℝ (l+1)).eval (a+b+c) +
      (ascPochhammer ℝ n).eval (a+b+c) * (ascPochhammer ℝ (l+1)).eval a) -
      ((ascPochhammer ℝ n).eval (a+b) * (ascPochhammer ℝ (l+1)).eval (a+c) +
      (ascPochhammer ℝ n).eval (a+c) * (ascPochhammer ℝ (l+1)).eval (a+b)) := by
    dsimp [U, V, R, Q]
    simp only [ascPochhammer_succ_eval]
    dsimp [x, C] at *
    field_simp [hx0, hxb, hxc, hxbc]
    <;> ring
  rw [hEq] at h
  linarith

/-- A nonpositive pair forces strict negativity at the preceding index. -/
theorem paired_sign_step {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) {N k : ℕ} (hk : 1 ≤ k) (hkN : 2*k ≤ N)
    (h : pairPoch a b c N k ≤ 0) : pairPoch a b c N (k-1) < 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hl : n+1 ≤ N-(n+1) := by omega
  have hi := pair_step_lengths ha hb hc n (N-(n+1)) hl (by
    dsimp [pairPoch] at h
    linarith)
  have he : N-n = N-(n+1)+1 := by omega
  simp only [pairPoch, Nat.succ_sub_one, he]
  linarith

private theorem paired_relation (μ α β : ℝ) (m k : ℕ)
    (hk : 1 ≤ k) (hkm : 2*k ≤ m) :
    paired μ α β m k *
      (((3*k-1).factorial:ℝ)*((3*(m-k)-1).factorial:ℝ)*
      (if 2*k=m then 2 else 1)) = pairPoch μ α β (3*m) (3*k) := by
  have hk0 : k ≠ 0 := by omega
  have hmk0 : m-k ≠ 0 := by omega
  have hidx : 3*m-3*k = 3*(m-k) := by omega
  have hidx' : m-(m-k) = k := by omega
  have hf : ((3*k-1).factorial:ℝ) ≠ 0 := by positivity
  have hg : ((3*(m-k)-1).factorial:ℝ) ≠ 0 := by positivity
  unfold paired raw a pairPoch
  simp only [if_neg hk0, if_neg hmk0, hidx, hidx']
  split_ifs with h
  · have he : m-k = k := by omega
    simp only [he] at *
    field_simp [hf, hg]
    <;> ring
  · field_simp [hf, hg]
    <;> ring

/-- No positive paired kernel can precede a negative one. -/
theorem paired_sign {μ α β : ℝ} (hμ : 0 < μ) (hα : 0 < α) (hβ : 0 < β)
    (m : ℕ) :
    ∀ i ≤ m/2, ∀ j ≤ m/2, i < j → 0 < paired μ α β m i →
      0 ≤ paired μ α β m j := by
  intro i hi j hj hij hpos
  have hi0 : 1 ≤ i := by
    by_contra h
    have he : i = 0 := by omega
    simp [he, paired, raw] at hpos
  have hj0 : 1 ≤ j := by omega
  have heI := paired_relation μ α β m i hi0 (by omega)
  have heJ := paired_relation μ α β m j hj0 (by omega)
  have hI : 0 < pairPoch μ α β (3*m) (3*i) := by
    rw [← heI]
    apply mul_pos hpos
    split_ifs <;> positivity
  by_contra hn
  have hJ : pairPoch μ α β (3*m) (3*j) ≤ 0 := by
    rw [← heJ]
    apply mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hn)
    split_ifs <;> positivity
  have hback : ∀ d, 3*i+d ≤ 3*j →
      pairPoch μ α β (3*m) (3*i+d) ≤ 0 →
      pairPoch μ α β (3*m) (3*i) ≤ 0 := by
    intro d
    induction d with
    | zero => intro _ h; simpa only [Nat.add_zero] using h
    | succ d ih =>
      intro hd h
      apply ih (by omega)
      have hstep := paired_sign_step hμ hα hβ (by omega : 1 ≤ 3*i+(d+1))
        (by omega : 2*(3*i+(d+1)) ≤ 3*m) h
      simpa only [show 3*i+(d+1)-1=3*i+d by omega] using hstep.le
  exact (not_le_of_gt hI) (hback (3*j-3*i) (by omega)
    (by simpa only [show 3*i+(3*j-3*i)=3*j by omega] using hJ))

end D5.S3.Analytic.KarpZhangNinh.Kernel
