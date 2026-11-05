/- GID: D5/S3/Analytic/KarpZhangNinh/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangNinh/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Coefficientwise log-concavity for the triple rising-factorial series. -/

import D5.S3.Analytic.KarpZhangNinh.Beta
import D5.S3.Analytic.KarpZhangGamma.Result
import D5.S3.Analytic.SeriesInequalities.KarpQuadraticTruncations

/-!
admission_basis: open-problem-resolution (#21124; Proved)
Judgment form: the source claim keeps the full sequence predicate, all natural
degrees, and all nonnegative real parameters. The beta module hosts consumed bind-only
trisection balancing helpers and the content-bearing symmetric beta lifting.
Finite pairing, one-sign-change weighting and the Abel decomposition are
reused from their existing owners.
Utility none: all declarations are uniform polynomial identities and inequalities,
not bounded computations, checkers, numerical reductions or certified instances.
-/

noncomputable section
open Polynomial Finset

namespace D5.S3.Analytic.KarpZhangNinh.Result.Kernel

/-- The coefficient of positive degree, with zero constant coefficient. -/
/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Result.Kernel.a_continuous; D5.S3.Analytic.KarpZhangNinh.Result.Kernel.paired_sign; D5.S3.Analytic.KarpZhangNinh.Result.Kernel.raw; D5.S3.Analytic.KarpZhangNinh.Result.Z; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Kernel.paired_relation; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Z_symm; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.full_tail_nonneg; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.lift_normalization; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.normalization_term; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.tail_nonneg;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def a (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then 0 else (ascPochhammer ℝ (3 * n)).eval t / ((3 * n - 1).factorial : ℝ)

/-- An unpaired Turán coefficient kernel. -/
/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Result.Kernel.paired; D5.S3.Analytic.KarpZhangNinh.Result.Kernel.paired_sign; D5.S3.Analytic.KarpZhangNinh.Result.delta; D5.S3.Analytic.KarpZhangNinh.Result.result; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Kernel.paired_relation; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.full_tail_nonneg; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.tail_nonneg; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.tail_nonneg_pos;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def raw (μ α β : ℝ) (m k : ℕ) : ℝ :=
  a k (μ + α) * a (m - k) (μ + β) - a k μ * a (m - k) (μ + α + β)

/-- The reflected kernel, counting the middle term once. -/
/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Result.Kernel.paired_sign; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Kernel.paired_relation; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.tail_nonneg_pos;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def paired (μ α β : ℝ) (m k : ℕ) : ℝ :=
  if 2 * k = m then raw μ α β m k else raw μ α β m k + raw μ α β m (m - k)

/-- A paired difference before division by factorials. -/
/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Result.Kernel.paired_sign; D5.S3.Analytic.KarpZhangNinh.Result.Kernel.paired_sign_step; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Kernel.paired_relation;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def pairPoch (a b c : ℝ) (N k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval (a+b) * (ascPochhammer ℝ (N-k)).eval (a+c) +
  (ascPochhammer ℝ k).eval (a+c) * (ascPochhammer ℝ (N-k)).eval (a+b) -
  (ascPochhammer ℝ k).eval a * (ascPochhammer ℝ (N-k)).eval (a+b+c) -
  (ascPochhammer ℝ k).eval (a+b+c) * (ascPochhammer ℝ (N-k)).eval a

/-- Each coefficient is polynomial in its parameter, including degree zero. -/
/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.tail_nonneg;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
lemma a_continuous (n : ℕ) : Continuous (a n) := by
  by_cases hn : n = 0
  · subst n
    change Continuous (fun _ : ℝ => (0 : ℝ))
    exact continuous_const
  · change Continuous (fun t : ℝ => if n = 0 then 0 else
      (ascPochhammer ℝ (3*n)).eval t / ((3*n-1).factorial:ℝ))
    simp only [if_neg hn]
    exact (ascPochhammer ℝ (3*n)).continuous.div_const _

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Kernel.pair_step_lengths;
direct_frozen_dependencies: D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.pochhammer_turan_nonneg (D5.S3.Analytic.SeriesInequalities.KarpQuadraticTruncations.pochhammer_turan_nonneg) statement_id=sha256:9b9547e6ee28fad6d1a405777a4a27ec734321727ef590923b24a36c509a1439;
stacked_dependencies: none. -/
private theorem strict_four_product (n : ℕ) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hn : 0 < n) :
    (ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval (a+b+c) <
      (ascPochhammer ℝ n).eval (a+b) * (ascPochhammer ℝ n).eval (a+c) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval,
    ascPochhammer_succ_eval, ascPochhammer_succ_eval]
  have hfactor : (a + n) * (a + b + c + n) < (a + b + n) * (a + c + n) := by
    nlinarith [mul_pos hb hc]
  have hleft := ascPochhammer_pos n a ha
  have hright := ascPochhammer_pos n (a+b+c) (by linarith)
  have hle := sub_nonneg.mp
    (D5.S3.Analytic.SeriesInequalities.KarpQuadraticTruncations.pochhammer_turan_nonneg
      n a b c ha hb.le hc.le)
  calc
    _ = ((ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval (a+b+c)) *
        ((a+n) * (a+b+c+n)) := mul_mul_mul_comm _ _ _ _
    _ < ((ascPochhammer ℝ n).eval (a+b) * (ascPochhammer ℝ n).eval (a+c)) *
        ((a+b+n) * (a+c+n)) :=
      mul_lt_mul_of_le_of_lt_of_pos_of_nonneg hle hfactor
        (mul_pos hleft hright) (by positivity)
    _ = _ := (mul_mul_mul_comm _ _ _ _).symm

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Kernel.pair_step_lengths;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private theorem ordered_lengths {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d)
    {k l : ℕ} (hkl : k ≤ l) :
    (ascPochhammer ℝ k).eval (a+d) * (ascPochhammer ℝ l).eval a ≤
      (ascPochhammer ℝ k).eval a * (ascPochhammer ℝ l).eval (a+d) := by
  have hsplit (t : ℝ) : (ascPochhammer ℝ l).eval t =
      (ascPochhammer ℝ k).eval t * (ascPochhammer ℝ (l-k)).eval (t+k) := by
    have h := congrArg (fun p : ℝ[X] => p.eval t) (ascPochhammer_mul ℝ k (l-k))
    simpa only [Nat.add_sub_of_le hkl, eval_mul, eval_comp, eval_add, eval_X,
      eval_natCast] using h.symm
  rw [hsplit a, hsplit (a+d)]
  have ht : (ascPochhammer ℝ (l-k)).eval (a+k) ≤
      (ascPochhammer ℝ (l-k)).eval (a+d+k) := by
    have h := monotoneOn_descPochhammer_eval (S := ℝ) (l-k)
      (a := a+k+((l-k : ℕ) : ℝ)-1) (b := a+d+k+((l-k : ℕ) : ℝ)-1)
      (by simp only [Set.mem_Ici]; have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
      (by simp only [Set.mem_Ici]; have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) (by linarith)
    simpa only [descPochhammer_eval_eq_ascPochhammer,
      show a + k + ((l-k : ℕ) : ℝ) - 1 - ((l-k : ℕ) : ℝ) + 1 = a+k by ring,
      show a + d + k + ((l-k : ℕ) : ℝ) - 1 - ((l-k : ℕ) : ℝ) + 1 = a+d+k by ring] using h
  have hp0 := mul_nonneg (ascPochhammer_pos k (a+d) (by linarith)).le
    (ascPochhammer_pos k a ha).le
  convert mul_le_mul_of_nonneg_left ht hp0 using 1 <;> ring

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Kernel.pair_step_lengths;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
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

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Result.Kernel.paired_sign_step;
direct_frozen_dependencies: D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.pochhammer_turan_nonneg (D5.S3.Analytic.SeriesInequalities.KarpQuadraticTruncations.pochhammer_turan_nonneg) statement_id=sha256:9b9547e6ee28fad6d1a405777a4a27ec734321727ef590923b24a36c509a1439;
stacked_dependencies: none. -/
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
/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Result.Kernel.paired_sign;
direct_frozen_dependencies: D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.pochhammer_turan_nonneg (D5.S3.Analytic.SeriesInequalities.KarpQuadraticTruncations.pochhammer_turan_nonneg) statement_id=sha256:9b9547e6ee28fad6d1a405777a4a27ec734321727ef590923b24a36c509a1439;
stacked_dependencies: none. -/
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

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Result.Kernel.paired_sign;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
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
/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.tail_nonneg_pos;
direct_frozen_dependencies: D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.pochhammer_turan_nonneg (D5.S3.Analytic.SeriesInequalities.KarpQuadraticTruncations.pochhammer_turan_nonneg) statement_id=sha256:9b9547e6ee28fad6d1a405777a4a27ec734321727ef590923b24a36c509a1439;
stacked_dependencies: none. -/
theorem paired_sign {μ α β : ℝ} (hμ : 0 < μ) (hα : 0 < α) (hβ : 0 < β)
    (m : ℕ) :
    ∀ i ≤ m/2, ∀ j ≤ m/2, i < j → 0 < paired μ α β m i →
      0 ≤ paired μ α β m j := by
  intro i hi j hj hij hpos
  have hi0 : 1 ≤ i := by
    by_contra h
    have he : i = 0 := Nat.eq_zero_of_not_pos h
    simp [he, paired, raw, a] at hpos
  have hj0 : 1 ≤ j := Nat.one_le_of_lt hij
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
  have hback : pairPoch μ α β (3*m) (3*i) ≤ 0 := by
    apply Nat.decreasingInduction' (n := 3*j) (m := 3*i)
      (P := fun k => pairPoch μ α β (3*m) k ≤ 0) ?_ (by omega) hJ
    intro k hk hki hkSign
    have hs := paired_sign_step hμ hα hβ (by omega : 1 ≤ k+1)
      (by omega : 2*(k+1) ≤ 3*m) hkSign
    simpa only [Nat.add_sub_cancel] using hs.le
  exact (not_le_of_gt hI) hback

end D5.S3.Analytic.KarpZhangNinh.Result.Kernel


noncomputable section
open Finset
open scoped Topology
namespace D5.S3.Analytic.KarpZhangNinh.Result
open Kernel

/-- The finite Cauchy coefficient; the zero endpoints vanish. -/
/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Result.claim; D5.S3.Analytic.KarpZhangNinh.Result.result;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def delta (f : ℕ → ℝ) (μ α β : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ range (m+1), f k * f (m-k) * raw μ α β m k

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.central_tail_of_sign; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.tail_nonneg_pos; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.tail_pair;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private def pair (K : ℕ → ℝ) (m k : ℕ) : ℝ :=
  if 2*k<m then K k + K (m-k) else K k

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.central_tail_of_sign;
direct_frozen_dependencies: D5/S3/Analytic/KarpZhangGamma/Result.pair_sum (D5.S3.Analytic.KarpZhangGamma.Result.pair_sum) statement_id=sha256:8b8de24a133e92ce41bfd64f52ec4220d8e69256816912f55e8a2fc7e91f1326; D5/S3/Analytic/KarpZhangReciprocal/Result.tail_sum (D5.S3.Analytic.KarpZhangReciprocal.Result.tail_sum) statement_id=sha256:47b3c03268296e64f4b0bf24d2c278d331ce0da2c2acf1874e481088ac6793fd;
stacked_dependencies: none. -/
private theorem tail_pair (K : ℕ → ℝ) (m q : ℕ) (hq : 2*q≤m) :
    (∑ i ∈ range (m-q-q+1), K (q+i)) =
      ∑ k ∈ range (m/2+1), pair K m k * (if q≤k then 1 else 0) := by
  rw [← KarpZhangReciprocal.Result.tail_sum K m q hq,
    KarpZhangGamma.Result.pair_sum]
  apply sum_congr rfl
  intro k hk
  have hkm : 2*k≤m := by have := mem_range.mp hk; omega
  have hmk : m-(m-k)=k := by omega
  simp only [pair, hmk]
  by_cases hqk : q≤k
  · have hqr : q≤m-k := by omega
    simp only [hqk, hqr, and_self, ite_true, mul_one]
  · simp [hqk]

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.tail_nonneg_pos;
direct_frozen_dependencies: D5/S3/Analytic/KarpZhangGamma/Result.pair_sum (D5.S3.Analytic.KarpZhangGamma.Result.pair_sum) statement_id=sha256:8b8de24a133e92ce41bfd64f52ec4220d8e69256816912f55e8a2fc7e91f1326; D5/S3/Analytic/KarpZhangGamma/Weighting.weighted_sum_nonneg (D5.S3.Analytic.KarpZhangGamma.Weighting.weighted_sum_nonneg) statement_id=sha256:21a3c16ca411f5688e6d008390c044d80ff0f7c00cd4bb0f2640224c3f40eca6; D5/S3/Analytic/KarpZhangReciprocal/Result.tail_sum (D5.S3.Analytic.KarpZhangReciprocal.Result.tail_sum) statement_id=sha256:47b3c03268296e64f4b0bf24d2c278d331ce0da2c2acf1874e481088ac6793fd;
stacked_dependencies: none. -/
private theorem central_tail_of_sign (K : ℕ → ℝ) (m q : ℕ) (hq : 2*q≤m)
    (hsign : ∀ i≤m/2, ∀ j≤m/2, i<j → 0<pair K m i → 0≤pair K m j)
    (htotal : 0≤∑ k ∈ range (m+1), K k) :
    0≤∑ i ∈ range (m-q-q+1), K (q+i) := by
  rw [tail_pair K m q hq]
  apply KarpZhangGamma.Weighting.weighted_sum_nonneg (pair K m)
    (fun k => if q≤k then 1 else 0) (m/2) hsign
  · simpa only [pair] using (KarpZhangGamma.Result.pair_sum K m) ▸ htotal
  · intro i hi; split_ifs <;> norm_num
  · intro i hi j hj hij
    split_ifs <;> norm_num <;> omega


/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Z_monotoneOn; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Z_symm; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.full_tail_nonneg; _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.lift_normalization;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
def Z (m : ℕ) (u v : ℝ) : ℝ :=
  ∑ k ∈ range (m+1), a k u * a (m-k) v

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.normalization_term;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private theorem factorial_product (n : ℕ) (hn : 0<n) :
    (n.factorial:ℝ) = n * ((n-1).factorial:ℝ) := by
  exact_mod_cast (Nat.mul_factorial_pred (Nat.ne_of_gt hn)).symm

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.lift_normalization;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private theorem normalization_term (m k : ℕ) (hk : k≤m) (u v : ℝ) :
    Homogeneous.coeff (3*m) (3*k) * (ascPochhammer ℝ (3*k)).eval u *
      (ascPochhammer ℝ (3*m-3*k)).eval v =
      ((3*m).factorial:ℝ) * (a k u * a (m-k) v) := by
  by_cases hk0 : k=0
  · subst k
    simp [Homogeneous.coeff,a]
  by_cases hkm : k=m
  · subst k
    simp [Homogeneous.coeff,a]
  have hsub : 3*m-3*k=3*(m-k) := (Nat.mul_sub_left_distrib 3 m k).symm
  have hfac := congrArg (fun n:ℕ => (n:ℝ))
    (Nat.choose_mul_factorial_mul_factorial (by omega : 3*k≤3*m))
  simp only [Nat.cast_mul] at hfac
  have hkpos : 0<3*k := by omega
  have hlpos : 0<3*(m-k) := by omega
  rw [hsub] at hfac ⊢
  rw [factorial_product _ hkpos, factorial_product _ hlpos] at hfac
  simp only [Homogeneous.coeff, Nat.mul_mod_right, ite_true, Kernel.a, if_neg hk0,
    if_neg (by omega : m-k ≠ 0)]
  rw [← hfac]
  have hfk : (((3*k-1).factorial:ℕ):ℝ) ≠ 0 := by positivity
  have hfl : (((3*(m-k)-1).factorial:ℕ):ℝ) ≠ 0 := by positivity
  field_simp [hfk,hfl]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hk]
  ring

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.Z_monotoneOn;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private theorem lift_normalization (m : ℕ) (u v : ℝ) :
    Beta.lift (Homogeneous.coeff (3*m)) (3*m) u v = ((3*m).factorial:ℝ) * Z m u v := by
  unfold Beta.lift Z
  rw [mul_sum]
  calc
    _ = ∑ k ∈ (range (3*m+1)).filter (fun k => k%3=0),
        Homogeneous.coeff (3*m) k * (ascPochhammer ℝ k).eval u *
          (ascPochhammer ℝ (3*m-k)).eval v := by
      symm
      apply sum_subset (filter_subset _ _)
      intro k hk hk'
      have hn : ¬ k%3=0 := by simpa only [mem_filter, hk, true_and] using hk'
      simp [Homogeneous.coeff, hn]
    _ = _ := by
      apply sum_bij (fun k _ => k/3)
      · intro k hk
        simp only [mem_filter, mem_range] at hk ⊢
        omega
      · intro k hk l hl hkl
        simp only [mem_filter, mem_range] at hk hl
        omega
      · intro k hk
        have hkm := mem_range.mp hk
        refine ⟨3*k, ?_, ?_⟩
        · simp only [mem_filter, mem_range]
          omega
        · omega
      · intro k hk
        simp only [mem_filter, mem_range] at hk
        have he : k=3*(k/3) := by omega
        rw [he]
        simpa using normalization_term m (k/3) (by omega) u v



/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.full_tail_nonneg;
direct_frozen_dependencies: none;
stacked_dependencies: none. -/
private theorem Z_symm (m : ℕ) (u v : ℝ) : Z m u v = Z m v u := by
  unfold Z
  rw [← sum_range_reflect (fun k => a k u * a (m-k) v) (m+1)]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_range.mp hk
  rw [show m+1-1-k=m-k by omega, show m-(m-k)=k by omega]
  exact mul_comm _ _

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.full_tail_nonneg;
direct_frozen_dependencies: D5/S3/Analytic/IncompleteBeta/Comparison.betaMean (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean) statement_id=sha256:52c1879a896c372f1717b74579f07258b6c1526a22f27baddf0c9a2d6d9c8d4d; D5/S3/Analytic/IncompleteBeta/Comparison.betaMean_strictAntiOn (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean_strictAntiOn) statement_id=sha256:8e5cc3dcb0b903667c4ed8ac30429217f113e1e1e09d26451dfd2b0252bacacc; D5/S3/Analytic/KummerRatio/BetaIntegral.gamma_pochhammer (D5.S3.Analytic.KummerRatio.BetaIntegral.gamma_pochhammer) statement_id=sha256:1059688f4875284d841121819603b9b49cf825aab8e4de735ff76c3e200ab797; D5/S3/Analytic/KummerRatio/BetaIntegral.integral_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.integral_beta) statement_id=sha256:fcc3a54a2a2111346d704d8d357ee41b6843e3310e722bd37de37805d8db9a45; D5/S3/Analytic/KummerRatio/BetaIntegral.intervalIntegrable_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.intervalIntegrable_beta) statement_id=sha256:e5a0a5542de6599ee2c9cccab09e8ca6fa72a102e012c68c1531e2633f1e2986;
stacked_dependencies: none. -/
private theorem Z_monotoneOn (m : ℕ) (hm : 2≤m) {S : ℝ} (hS : 0≤S) :
    MonotoneOn (fun s => Z m s (S-s)) (Set.Icc 0 (S/2)) := by
  have H := Beta.lift_monotoneOn (Homogeneous.coeff (3*m)) (3*m)
    (fun k hk => Homogeneous.coeff_symm (3*m) k (by omega) hk)
    (show MonotoneOn (fun t => Beta.polynomial (Homogeneous.coeff (3*m)) (3*m) t (1-t))
      (Set.Ioc 0 (1/2)) from (Homogeneous.strictMonoOn_slice m hm).monotoneOn) hS
  intro x hx y hy hxy
  have he := H hx hy hxy
  change Beta.lift (Homogeneous.coeff (3*m)) (3*m) x (S-x) ≤
    Beta.lift (Homogeneous.coeff (3*m)) (3*m) y (S-y) at he
  rw [lift_normalization, lift_normalization] at he
  exact (mul_le_mul_iff_right₀ (by positivity : (0:ℝ)<((3*m).factorial:ℝ))).mp he

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.tail_nonneg_pos;
direct_frozen_dependencies: D5/S3/Analytic/IncompleteBeta/Comparison.betaMean (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean) statement_id=sha256:52c1879a896c372f1717b74579f07258b6c1526a22f27baddf0c9a2d6d9c8d4d; D5/S3/Analytic/IncompleteBeta/Comparison.betaMean_strictAntiOn (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean_strictAntiOn) statement_id=sha256:8e5cc3dcb0b903667c4ed8ac30429217f113e1e1e09d26451dfd2b0252bacacc; D5/S3/Analytic/KummerRatio/BetaIntegral.gamma_pochhammer (D5.S3.Analytic.KummerRatio.BetaIntegral.gamma_pochhammer) statement_id=sha256:1059688f4875284d841121819603b9b49cf825aab8e4de735ff76c3e200ab797; D5/S3/Analytic/KummerRatio/BetaIntegral.integral_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.integral_beta) statement_id=sha256:fcc3a54a2a2111346d704d8d357ee41b6843e3310e722bd37de37805d8db9a45; D5/S3/Analytic/KummerRatio/BetaIntegral.intervalIntegrable_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.intervalIntegrable_beta) statement_id=sha256:e5a0a5542de6599ee2c9cccab09e8ca6fa72a102e012c68c1531e2633f1e2986;
stacked_dependencies: none. -/
private theorem full_tail_nonneg (m : ℕ) {μ α β : ℝ}
    (hμ : 0≤μ) (hα : 0≤α) (hβ : 0≤β) :
    0≤∑ k ∈ range (m+1), raw μ α β m k := by
  by_cases hm : 2≤m
  · have heq : (∑ k ∈ range (m+1), raw μ α β m k) =
        Z m (μ+α) (μ+β) - Z m μ (μ+α+β) := by
      simp only [raw,Z,sum_sub_distrib]
    rw [heq]
    let S := 2*μ+α+β
    let s := min (μ+α) (μ+β)
    have hS : 0≤S := by dsimp [S]; linarith
    have hμs : μ≤s := le_min (by linarith) (by linarith)
    have hs : s≤S/2 := by
      dsimp [s,S]
      linarith [min_le_left (μ+α) (μ+β), min_le_right (μ+α) (μ+β)]
    have H := Z_monotoneOn m hm hS
      (show μ ∈ Set.Icc 0 (S/2) from ⟨hμ, hμs.trans hs⟩)
      (show s ∈ Set.Icc 0 (S/2) from ⟨hμ.trans hμs,hs⟩) hμs
    change Z m μ (S-μ) ≤ Z m s (S-s) at H
    have hleft : S-μ=μ+α+β := by dsimp [S]; ring
    rw [hleft] at H
    have hright : Z m s (S-s) = Z m (μ+α) (μ+β) := by
      by_cases hab : α≤β
      · have he : s=μ+α := min_eq_left (by linarith)
        rw [he, show S-(μ+α)=μ+β by dsimp [S]; ring]
      · have he : s=μ+β := min_eq_right (by linarith)
        rw [he, show S-(μ+β)=μ+α by dsimp [S]; ring, Z_symm]
    exact sub_nonneg.mpr (hright ▸ H)
  · have hm' : m=0 ∨ m=1 := by omega
    rcases hm' with rfl | rfl <;> simp [raw, a, sum_range_succ]

/- proof_shape: bind-only; escape_witness: none;
consumers: _private.D5.S3.Analytic.KarpZhangNinh.Result.0.D5.S3.Analytic.KarpZhangNinh.Result.tail_nonneg;
direct_frozen_dependencies: D5/S3/Analytic/IncompleteBeta/Comparison.betaMean (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean) statement_id=sha256:52c1879a896c372f1717b74579f07258b6c1526a22f27baddf0c9a2d6d9c8d4d; D5/S3/Analytic/IncompleteBeta/Comparison.betaMean_strictAntiOn (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean_strictAntiOn) statement_id=sha256:8e5cc3dcb0b903667c4ed8ac30429217f113e1e1e09d26451dfd2b0252bacacc; D5/S3/Analytic/KarpZhangGamma/Result.pair_sum (D5.S3.Analytic.KarpZhangGamma.Result.pair_sum) statement_id=sha256:8b8de24a133e92ce41bfd64f52ec4220d8e69256816912f55e8a2fc7e91f1326; D5/S3/Analytic/KarpZhangGamma/Weighting.weighted_sum_nonneg (D5.S3.Analytic.KarpZhangGamma.Weighting.weighted_sum_nonneg) statement_id=sha256:21a3c16ca411f5688e6d008390c044d80ff0f7c00cd4bb0f2640224c3f40eca6; D5/S3/Analytic/KarpZhangReciprocal/Result.tail_sum (D5.S3.Analytic.KarpZhangReciprocal.Result.tail_sum) statement_id=sha256:47b3c03268296e64f4b0bf24d2c278d331ce0da2c2acf1874e481088ac6793fd; D5/S3/Analytic/KummerRatio/BetaIntegral.gamma_pochhammer (D5.S3.Analytic.KummerRatio.BetaIntegral.gamma_pochhammer) statement_id=sha256:1059688f4875284d841121819603b9b49cf825aab8e4de735ff76c3e200ab797; D5/S3/Analytic/KummerRatio/BetaIntegral.integral_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.integral_beta) statement_id=sha256:fcc3a54a2a2111346d704d8d357ee41b6843e3310e722bd37de37805d8db9a45; D5/S3/Analytic/KummerRatio/BetaIntegral.intervalIntegrable_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.intervalIntegrable_beta) statement_id=sha256:e5a0a5542de6599ee2c9cccab09e8ca6fa72a102e012c68c1531e2633f1e2986; D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.pochhammer_turan_nonneg (D5.S3.Analytic.SeriesInequalities.KarpQuadraticTruncations.pochhammer_turan_nonneg) statement_id=sha256:9b9547e6ee28fad6d1a405777a4a27ec734321727ef590923b24a36c509a1439;
stacked_dependencies: none. -/
private theorem tail_nonneg_pos (m q : ℕ) (hq : 2*q≤m) {μ α β : ℝ}
    (hμ : 0<μ) (hα : 0<α) (hβ : 0<β) :
    0≤∑ i ∈ range (m-q-q+1), raw μ α β m (q+i) := by
  apply central_tail_of_sign (raw μ α β m) m q hq
  · have he (k : ℕ) (hk : k≤m/2) : pair (raw μ α β m) m k = paired μ α β m k := by
      unfold pair paired
      have hh : 2*k≤m := by omega
      split_ifs <;> (first | rfl | omega)
    intro i hi j hj hij hpi
    rw [he i hi] at hpi
    rw [he j hj]
    exact paired_sign hμ hα hβ m i hi j hj hij hpi
  · exact full_tail_nonneg m hμ.le hα.le hβ.le

/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Result.result;
direct_frozen_dependencies: D5/S3/Analytic/IncompleteBeta/Comparison.betaMean (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean) statement_id=sha256:52c1879a896c372f1717b74579f07258b6c1526a22f27baddf0c9a2d6d9c8d4d; D5/S3/Analytic/IncompleteBeta/Comparison.betaMean_strictAntiOn (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean_strictAntiOn) statement_id=sha256:8e5cc3dcb0b903667c4ed8ac30429217f113e1e1e09d26451dfd2b0252bacacc; D5/S3/Analytic/KarpZhangGamma/Result.pair_sum (D5.S3.Analytic.KarpZhangGamma.Result.pair_sum) statement_id=sha256:8b8de24a133e92ce41bfd64f52ec4220d8e69256816912f55e8a2fc7e91f1326; D5/S3/Analytic/KarpZhangGamma/Weighting.weighted_sum_nonneg (D5.S3.Analytic.KarpZhangGamma.Weighting.weighted_sum_nonneg) statement_id=sha256:21a3c16ca411f5688e6d008390c044d80ff0f7c00cd4bb0f2640224c3f40eca6; D5/S3/Analytic/KarpZhangReciprocal/Result.tail_sum (D5.S3.Analytic.KarpZhangReciprocal.Result.tail_sum) statement_id=sha256:47b3c03268296e64f4b0bf24d2c278d331ce0da2c2acf1874e481088ac6793fd; D5/S3/Analytic/KummerRatio/BetaIntegral.gamma_pochhammer (D5.S3.Analytic.KummerRatio.BetaIntegral.gamma_pochhammer) statement_id=sha256:1059688f4875284d841121819603b9b49cf825aab8e4de735ff76c3e200ab797; D5/S3/Analytic/KummerRatio/BetaIntegral.integral_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.integral_beta) statement_id=sha256:fcc3a54a2a2111346d704d8d357ee41b6843e3310e722bd37de37805d8db9a45; D5/S3/Analytic/KummerRatio/BetaIntegral.intervalIntegrable_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.intervalIntegrable_beta) statement_id=sha256:e5a0a5542de6599ee2c9cccab09e8ca6fa72a102e012c68c1531e2633f1e2986; D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.pochhammer_turan_nonneg (D5.S3.Analytic.SeriesInequalities.KarpQuadraticTruncations.pochhammer_turan_nonneg) statement_id=sha256:9b9547e6ee28fad6d1a405777a4a27ec734321727ef590923b24a36c509a1439;
stacked_dependencies: none. -/
private theorem tail_nonneg (m q : ℕ) (hq : 2*q≤m) {μ α β : ℝ}
    (hμ : 0≤μ) (hα : 0≤α) (hβ : 0≤β) :
    0≤∑ i ∈ range (m-q-q+1), raw μ α β m (q+i) := by
  have hc : Continuous (fun e : ℝ =>
      ∑ i ∈ range (m-q-q+1), raw (μ+e) (α+e) (β+e) m (q+i)) := by
    apply continuous_finsetSum
    intro i hi
    have hmc : Continuous (fun e : ℝ => μ+e) := continuous_const.add continuous_id
    have hac : Continuous (fun e : ℝ => α+e) := continuous_const.add continuous_id
    have hbc : Continuous (fun e : ℝ => β+e) := continuous_const.add continuous_id
    exact (((a_continuous _).comp (hmc.add hac)).mul
      ((a_continuous _).comp (hmc.add hbc))).sub
        (((a_continuous _).comp hmc).mul
          ((a_continuous _).comp ((hmc.add hac).add hbc)))
  have ht := hc.continuousAt.tendsto.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from inf_le_left)
  apply ge_of_tendsto (by simpa only [add_zero] using ht)
  filter_upwards [self_mem_nhdsWithin] with e he
  change 0 < e at he
  exact tail_nonneg_pos m q hq (add_pos_of_nonneg_of_pos hμ he)
    (add_pos_of_nonneg_of_pos hα he) (add_pos_of_nonneg_of_pos hβ he)

/-- The exact universal coefficient inequality of Conjecture 3.8. -/
/- proof_shape: bind-only; escape_witness: none;
consumers: D5.S3.Analytic.KarpZhangNinh.Result.result;
direct_frozen_dependencies: D5/S3/Analytic/KarpZhangReciprocal/Result.IsLogConcave (D5.S3.Analytic.KarpZhangReciprocal.Result.IsLogConcave) statement_id=sha256:b42cbcf21ac638e1b04c3104e1ecca467dd7f5283382d61727edd4354b0c30a0;
stacked_dependencies: none. -/
def claim : Prop :=
  ∀ (f : ℕ → ℝ) (μ α β : ℝ) (m : ℕ),
    KarpZhangReciprocal.Result.IsLogConcave f → 0≤μ → 0≤α → 0≤β →
      0≤delta f μ α β m

/-- The triple-Pochhammer coefficient assertion for every admissible sequence. -/
/- proof_shape: bind-only; escape_witness: none;
consumers: external Conjecture 3.8 settlement;
direct_frozen_dependencies: D5/S3/Analytic/IncompleteBeta/Comparison.betaMean (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean) statement_id=sha256:52c1879a896c372f1717b74579f07258b6c1526a22f27baddf0c9a2d6d9c8d4d; D5/S3/Analytic/IncompleteBeta/Comparison.betaMean_strictAntiOn (D5.S3.Analytic.IncompleteBeta.Comparison.betaMean_strictAntiOn) statement_id=sha256:8e5cc3dcb0b903667c4ed8ac30429217f113e1e1e09d26451dfd2b0252bacacc; D5/S3/Analytic/KarpZhangGamma/Result.pair_sum (D5.S3.Analytic.KarpZhangGamma.Result.pair_sum) statement_id=sha256:8b8de24a133e92ce41bfd64f52ec4220d8e69256816912f55e8a2fc7e91f1326; D5/S3/Analytic/KarpZhangGamma/Weighting.weighted_sum_nonneg (D5.S3.Analytic.KarpZhangGamma.Weighting.weighted_sum_nonneg) statement_id=sha256:21a3c16ca411f5688e6d008390c044d80ff0f7c00cd4bb0f2640224c3f40eca6; D5/S3/Analytic/KarpZhangReciprocal/Result.IsLogConcave (D5.S3.Analytic.KarpZhangReciprocal.Result.IsLogConcave) statement_id=sha256:b42cbcf21ac638e1b04c3104e1ecca467dd7f5283382d61727edd4354b0c30a0; D5/S3/Analytic/KarpZhangReciprocal/Result.abel_layers (D5.S3.Analytic.KarpZhangReciprocal.Result.abel_layers) statement_id=sha256:1f4c98d526cdc81a6201b601b53c9ae3d7f1341af0d6daaf3cd848ef99f7e763; D5/S3/Analytic/KarpZhangReciprocal/Result.balanced_step (D5.S3.Analytic.KarpZhangReciprocal.Result.balanced_step) statement_id=sha256:140a2a4910e9527641f28cb4c26ce135410f92b1634e3f35f50ae0c8d6efd5f6; D5/S3/Analytic/KarpZhangReciprocal/Result.increment (D5.S3.Analytic.KarpZhangReciprocal.Result.increment) statement_id=sha256:1207b96dae6c500c52707f41fe79b5e5058f4c0aa52be6412607471cb02c05b8; D5/S3/Analytic/KarpZhangReciprocal/Result.tail_sum (D5.S3.Analytic.KarpZhangReciprocal.Result.tail_sum) statement_id=sha256:47b3c03268296e64f4b0bf24d2c278d331ce0da2c2acf1874e481088ac6793fd; D5/S3/Analytic/KummerRatio/BetaIntegral.gamma_pochhammer (D5.S3.Analytic.KummerRatio.BetaIntegral.gamma_pochhammer) statement_id=sha256:1059688f4875284d841121819603b9b49cf825aab8e4de735ff76c3e200ab797; D5/S3/Analytic/KummerRatio/BetaIntegral.integral_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.integral_beta) statement_id=sha256:fcc3a54a2a2111346d704d8d357ee41b6843e3310e722bd37de37805d8db9a45; D5/S3/Analytic/KummerRatio/BetaIntegral.intervalIntegrable_beta (D5.S3.Analytic.KummerRatio.BetaIntegral.intervalIntegrable_beta) statement_id=sha256:e5a0a5542de6599ee2c9cccab09e8ca6fa72a102e012c68c1531e2633f1e2986; D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.pochhammer_turan_nonneg (D5.S3.Analytic.SeriesInequalities.KarpQuadraticTruncations.pochhammer_turan_nonneg) statement_id=sha256:9b9547e6ee28fad6d1a405777a4a27ec734321727ef590923b24a36c509a1439;
stacked_dependencies: none. -/
theorem result : claim := by
  intro f μ α β m hf hμ hα hβ
  rw [delta, KarpZhangReciprocal.Result.abel_layers]
  apply sum_nonneg
  intro q hq
  have hqm : q≤m/2 := Nat.le_of_lt_succ (mem_range.mp hq)
  apply mul_nonneg
  · unfold KarpZhangReciprocal.Result.increment
    split_ifs with hz
    · exact mul_nonneg (hf.1 _) (hf.1 _)
    · have H := KarpZhangReciprocal.Result.balanced_step hf m (q-1) (by omega)
      rw [show q-1+1=q by omega] at H
      exact sub_nonneg.mpr H
  · exact tail_nonneg m q (by omega) hμ hα hβ

end D5.S3.Analytic.KarpZhangNinh.Result
