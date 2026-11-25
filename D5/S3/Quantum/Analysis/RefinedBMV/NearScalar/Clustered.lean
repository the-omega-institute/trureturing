/- GID: D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/Clustered
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proof component of the four-copy refined BMV comparison near a scalar. -/

import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.PowerReorder
import D5.S3.Quantum.Analysis.RefinedBMV43
import Batteries.Tactic.OpenPrivate

/-! Bounds and cyclic word forms for two commutators and two copies of B. -/

open Matrix
open scoped Matrix Matrix.Norms.Frobenius BigOperators

namespace D5.S3.Quantum.Analysis.RefinedBMVNearScalarClustered

open D5.S3.Quantum.Analysis.RefinedBMVNearScalarCommutator (trace_product_bound)
open D5.S3.Quantum.Analysis.RefinedBMVNearScalarPowerReorder
  (power_commutator three_commutator_power_word_bound)
open private frobenius_mul_pow_le from D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.WordControl
open private trace_move_bound from D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.PowerReorder

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "opNorm" =>
  fun A : Matrix n n ℂ => ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A‖

private theorem trace_move_right_bound (H B Q : Matrix n n ℂ) (k : ℕ)
    (A E : ℝ)
    (hA : |(H ^ k * B * Q).trace.re| ≤ A)
    (hE : ∀ j < k, |(H ^ j * (H * B - B * H) * H ^ (k - 1 - j) * Q).trace.re| ≤ E) :
    |(B * H ^ k * Q).trace.re| ≤ A + (k : ℝ) * E := by
  classical
  have he : B * H ^ k = H ^ k * B -
      ∑ j ∈ Finset.range k, H ^ j * (H * B - B * H) * H ^ (k - 1 - j) := by
    rw [← power_commutator H B k]
    abel
  rw [he, Matrix.sub_mul, Matrix.sum_mul, Matrix.trace_sub, Matrix.trace_sum,
    Complex.sub_re, Complex.re_sum]
  calc
    _ ≤ |(H ^ k * B * Q).trace.re| +
        |∑ j ∈ Finset.range k, (H ^ j * (H * B - B * H) * H ^ (k - 1 - j) * Q).trace.re| := by
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans (by rw [abs_neg])
    _ ≤ A + ∑ j ∈ Finset.range k, E :=
      add_le_add hA ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun j hj => hE j (Finset.mem_range.mp hj)))
    _ = _ := by simp

omit [DecidableEq n] in
private theorem group_rotated_product (X A₁ A₂ A₃ B₁ B₂ B₃ : Matrix n n ℂ) :
    X * (A₁ * A₂ * A₃ * B₁ * B₂ * B₃) = (X * A₁ * A₂ * A₃) * (B₁ * B₂) * B₃ := by
  simp only [Matrix.mul_assoc]

set_option maxHeartbeats 1000000 in
theorem clustered_two_commutator_power_word_bound (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.IsHermitian) (a b c d : ℕ) :
    let C := H * B - B * H
    |(C * H ^ a * C * H ^ b * B * H ^ c * B * H ^ d).trace.re| ≤
      (1 + 2 * (d : ℝ) + (b : ℝ) * (2 + 4 * (d : ℝ))) *
        opNorm H ^ (a + b + c + d) * ‖B * C‖ ^ 2 := by
  classical
  let C : Matrix n n ℂ := H * B - B * H
  let M : ℝ := opNorm H
  let K : ℝ := ‖B * C‖
  let T : ℝ := M ^ (a + b + c + d) * K ^ 2
  have hC : Cᴴ = -C := by
    dsimp only [C]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hH.eq, hB.eq, neg_sub]
  have hBC : ‖C * B‖ = K := by
    calc
      ‖C * B‖ = ‖(C * B)ᴴ‖ := (Matrix.frobenius_norm_conjTranspose (C * B)).symm
      _ = K := by rw [Matrix.conjTranspose_mul, hC, hB.eq, mul_neg, norm_neg]
  have hthree (p q s t : ℕ) (hs : p + q + s + t + 1 = a + b + c + d) :
      |(C * H ^ p * B * H ^ q * C * H ^ s * C * H ^ t).trace.re| ≤
        (2 + 4 * (p : ℝ)) * T := by
    calc
      _ ≤ (2 + 4 * (p : ℝ)) * M ^ (p + q + s + t + 1) * K ^ 2 :=
        three_commutator_power_word_bound H B hH hB p q s t
      _ = _ := by rw [hs]; dsimp only [T]; ring
  let P : Matrix n n ℂ := B * H ^ d * C * H ^ a * C
  let Q : Matrix n n ℂ := C * H ^ a * C * B * H ^ (b + c)
  change |(C * H ^ a * C * H ^ b * B * H ^ c * B * H ^ d).trace.re| ≤
    (1 + 2 * (d : ℝ) + (b : ℝ) * (2 + 4 * (d : ℝ))) *
      M ^ (a + b + c + d) * K ^ 2
  rw [mul_assoc (1 + 2 * (d : ℝ) + (b : ℝ) * (2 + 4 * (d : ℝ)))]
  change _ ≤ (1 + 2 * (d : ℝ) + (b : ℝ) * (2 + 4 * (d : ℝ))) * T
  have hrotate :
      (C * H ^ a * C * H ^ b * B * H ^ c * B * H ^ d).trace =
        (P * (H ^ b * B) * H ^ c).trace := by
    let X : Matrix n n ℂ := C * H ^ a * C * H ^ b * B * H ^ c
    let Y : Matrix n n ℂ := B * H ^ d
    have hsplit : C * H ^ a * C * H ^ b * B * H ^ c * B * H ^ d = X * Y :=
      Matrix.mul_assoc X B (H ^ d)
    have hgroup : Y * X = P * (H ^ b * B) * H ^ c :=
      group_rotated_product Y C (H ^ a) C (H ^ b) B (H ^ c)
    rw [hsplit, Matrix.trace_mul_comm X Y, hgroup]
  rw [hrotate]
  have hbase : |(H ^ d * B * Q).trace.re| ≤ T := by
    let X : Matrix n n ℂ := B * C * H ^ a
    let Y : Matrix n n ℂ := C * B * H ^ (b + c)
    let Z : Matrix n n ℂ := C * B * H ^ (b + c + d)
    let Hd : Matrix n n ℂ := H ^ d
    let XY : Matrix n n ℂ := X * Y
    have hsplit : H ^ d * B * Q = Hd * XY := by
      simp only [Hd, XY, X, Y, Q, Matrix.mul_assoc]
    have hgroup : XY * Hd = X * Z := by
      simp only [XY, Hd, Y, Z, pow_add H (b + c) d, Matrix.mul_assoc]
    have htrace : (H ^ d * B * Q).trace = (X * Z).trace := by
      rw [hsplit, Matrix.trace_mul_comm Hd XY, hgroup]
    rw [htrace]
    have hX : ‖X‖ ≤ K * M ^ a := frobenius_mul_pow_le (B * C) H a
    have hZ : ‖Z‖ ≤ K * M ^ (b + c + d) := by
      calc
        ‖Z‖ ≤ ‖C * B‖ * M ^ (b + c + d) := frobenius_mul_pow_le (C * B) H (b + c + d)
        _ = K * M ^ (b + c + d) := by rw [hBC]
    calc
      |(X * Z).trace.re| ≤ ‖(X * Z).trace‖ := Complex.abs_re_le_norm (X * Z).trace
      _ ≤ ‖X‖ * ‖Z‖ := trace_product_bound X Z
      _ ≤ (K * M ^ a) * (K * M ^ (b + c + d)) :=
        mul_le_mul hX hZ (norm_nonneg Z) (by positivity)
      _ = T := by dsimp only [T]; simp only [pow_add]; ring
  have herrRight (j : ℕ) (hj : j < d) :
      |(H ^ j * C * H ^ (d - 1 - j) * Q).trace.re| ≤ 2 * T := by
    let r : ℕ := d - 1 - j
    let X : Matrix n n ℂ := H ^ j * C * H ^ r * C * H ^ a
    let Y : Matrix n n ℂ := C * B * H ^ (b + c)
    let W : Matrix n n ℂ := C * H ^ (0 : ℕ) * B * H ^ (b + c + j) * C * H ^ r * C * H ^ a
    have hsplit : H ^ j * C * H ^ r * Q = X * Y := by
      simp only [X, Y, Q, Matrix.mul_assoc]
    have hgroup : Y * X = W := by
      simp only [X, Y, W, pow_add H (b + c) j, pow_zero, mul_one, Matrix.mul_assoc]
    have htrace : (H ^ j * C * H ^ r * Q).trace = W.trace := by
      rw [hsplit, Matrix.trace_mul_comm X Y, hgroup]
    have hsum : 0 + (b + c + j) + r + a + 1 = a + b + c + d := by
      dsimp only [r]
      omega
    change |(H ^ j * C * H ^ r * Q).trace.re| ≤ 2 * T
    rw [htrace]
    simpa only [Nat.cast_zero, mul_zero, add_zero] using hthree 0 (b + c + j) r a hsum
  have hadj : |(P * (B * H ^ b) * H ^ c).trace.re| ≤ (1 + 2 * (d : ℝ)) * T := by
    have he : P * (B * H ^ b) * H ^ c = B * H ^ d * Q := by
      simp only [P, Q, pow_add H b c, Matrix.mul_assoc]
    rw [he]
    calc
      |(B * H ^ d * Q).trace.re| ≤ T + (d : ℝ) * (2 * T) :=
        trace_move_right_bound H B Q d T (2 * T) hbase herrRight
      _ = (1 + 2 * (d : ℝ)) * T := by ring
  have herrLeft (j : ℕ) (hj : j < b) :
      |(P * (H ^ j * C * H ^ (b - 1 - j)) * H ^ c).trace.re| ≤
        (2 + 4 * (d : ℝ)) * T := by
    let r : ℕ := b - 1 - j
    let X : Matrix n n ℂ := B * H ^ d * C
    let Y : Matrix n n ℂ := H ^ a * C * H ^ j * C * H ^ (r + c)
    let W : Matrix n n ℂ := C * H ^ d * B * H ^ (r + c) * C * H ^ j * C * H ^ a
    have hsplit : P * (H ^ j * C * H ^ r) * H ^ c = X * Y := by
      simp only [P, X, Y, pow_add H r c, Matrix.mul_assoc]
    have htrace : (P * (H ^ j * C * H ^ r) * H ^ c).trace = (Y * X).trace := by
      rw [hsplit, Matrix.trace_mul_comm X Y]
    have hstar : (Y * X)ᴴ = -W := by
      simp only [X, Y, W, Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hH.eq, hB.eq,
        hC, Matrix.mul_assoc, neg_mul, mul_neg, neg_neg]
    have hre : (Y * X).trace.re = -(W.trace.re) := by
      calc
        (Y * X).trace.re = (star (Y * X).trace).re := rfl
        _ = ((Y * X)ᴴ).trace.re :=
          congrArg Complex.re (Matrix.trace_conjTranspose (Y * X)).symm
        _ = -(W.trace.re) := by rw [hstar, Matrix.trace_neg, Complex.neg_re]
    have hsum : d + (r + c) + j + a + 1 = a + b + c + d := by
      dsimp only [r]
      omega
    change |(P * (H ^ j * C * H ^ r) * H ^ c).trace.re| ≤ (2 + 4 * (d : ℝ)) * T
    rw [htrace, hre, abs_neg]
    exact hthree d (r + c) j a hsum
  calc
    |(P * (H ^ b * B) * H ^ c).trace.re| ≤
        (1 + 2 * (d : ℝ)) * T + (b : ℝ) * ((2 + 4 * (d : ℝ)) * T) :=
      trace_move_bound H B P (H ^ c) b ((1 + 2 * (d : ℝ)) * T) ((2 + 4 * (d : ℝ)) * T)
        hadj herrLeft
    _ = (1 + 2 * (d : ℝ) + (b : ℝ) * (2 + 4 * (d : ℝ))) * T := by ring

open RefinedBMV (evalWord)
open private evalWord_block43 from D5.S3.Quantum.Analysis.RefinedBMV43

private theorem all_true_of_count_false_zero (w : List Bool) (hw : w.count false = 0) :
    w = List.replicate w.length true := by
  apply List.eq_replicate_length.mpr
  intro letter h
  cases letter
  · exact (List.count_eq_zero.mp hw h).elim
  · rfl

private theorem split_at_first_false (w : List Bool) (hw : 0 < w.count false) :
    ∃ a v, w = List.replicate a true ++ false :: v ∧ v.count false + 1 = w.count false := by
  induction w with
  | nil => simp at hw
  | cons letter w ih =>
      cases letter
      · exact ⟨0, w, rfl, List.count_cons_self.symm⟩
      · have hcount : (true :: w).count false = w.count false :=
          List.count_cons_of_ne (Ne.symm Bool.false_ne_true)
        rw [hcount] at hw
        obtain ⟨a, v, hv, hc⟩ := ih hw
        exact ⟨a + 1, v, by rw [List.replicate_succ, List.cons_append, ← hv], hc.trans hcount.symm⟩

private theorem one_false_decomposition (w : List Bool) (hw : w.count false = 1) :
    ∃ a b, w = List.replicate a true ++ false :: List.replicate b true := by
  obtain ⟨a, v, hv, hc⟩ := split_at_first_false w (by omega)
  exact ⟨a, v.length, hv.trans (congrArg (fun z => List.replicate a true ++ false :: z)
    (all_true_of_count_false_zero v (by omega)))⟩

private theorem two_false_decomposition (w : List Bool) (hw : w.count false = 2) :
    ∃ a b c, w = List.replicate a true ++
      false :: (List.replicate b true ++ false :: List.replicate c true) := by
  obtain ⟨a, v, hv, hc⟩ := split_at_first_false w (by omega)
  obtain ⟨b, c, htail⟩ := one_false_decomposition v (by omega)
  exact ⟨a, b, c, hv.trans (congrArg (fun z => List.replicate a true ++ false :: z) htail)⟩

/-- With two ordinary B letters in total, either each segment contributes
one B or both come from the same segment. Rotate at a commutator in the
latter case so that the segment with both B letters comes second. -/
theorem two_boolean_segments_trace_patterns (H B C : Matrix n n ℂ) (u v : List Bool)
    (hB : (u ++ v).count false = 2) :
    ∃ a b c d : ℕ, a + b + c + d = (u ++ v).count true ∧
      ((C * evalWord H B u * C * evalWord H B v).trace =
          (C * H ^ a * B * H ^ b * C * H ^ c * B * H ^ d).trace ∨
        (C * evalWord H B u * C * evalWord H B v).trace =
          (C * H ^ a * C * H ^ b * B * H ^ c * B * H ^ d).trace) := by
  have eval_run (k : ℕ) : evalWord H B (List.replicate k true) = H ^ k := by
    simpa only [List.append_nil, evalWord, mul_one] using evalWord_block43 H B k []
  have hcluster (x y : List Bool) (hx : x.count false = 0) (hy : y.count false = 2) :
      ∃ a b c d : ℕ, a + b + c + d = (x ++ y).count true ∧
        (C * evalWord H B x * C * evalWord H B y).trace =
          (C * H ^ a * C * H ^ b * B * H ^ c * B * H ^ d).trace := by
    obtain ⟨b, c, d, hword⟩ := two_false_decomposition y hy
    refine ⟨x.length, b, c, d, ?_, ?_⟩
    · conv_rhs => rw [List.count_append, all_true_of_count_false_zero x hx, hword]
      simp only [List.count_append, List.count_replicate_self,
        List.count_cons_of_ne Bool.false_ne_true]
      omega
    · conv_lhs => rw [all_true_of_count_false_zero x hx, hword]
      simp only [evalWord_block43, evalWord, eval_run, Matrix.mul_assoc]
  rw [List.count_append] at hB
  by_cases hu : u.count false = 0
  · obtain ⟨a, b, c, d, hc, ht⟩ := hcluster u v hu (by omega)
    exact ⟨a, b, c, d, hc, Or.inr ht⟩
  by_cases hv : v.count false = 0
  · obtain ⟨a, b, c, d, hc, ht⟩ := hcluster v u hv (by omega)
    refine ⟨a, b, c, d, ?_, Or.inr ?_⟩
    · simpa only [List.count_append, Nat.add_comm (v.count true)] using hc
    · let X : Matrix n n ℂ := C * evalWord H B u
      let Y : Matrix n n ℂ := C * evalWord H B v
      have hsplit : C * evalWord H B u * C * evalWord H B v = X * Y :=
        Matrix.mul_assoc X C (evalWord H B v)
      have hgroup : C * evalWord H B v * C * evalWord H B u = Y * X :=
        Matrix.mul_assoc Y C (evalWord H B u)
      rw [hsplit, Matrix.trace_mul_comm X Y, ← hgroup]
      exact ht
  obtain ⟨a, b, hu'⟩ := one_false_decomposition u (by omega)
  obtain ⟨c, d, hv'⟩ := one_false_decomposition v (by omega)
  refine ⟨a, b, c, d, ?_, Or.inl ?_⟩
  · rw [hu', hv']
    simp only [List.count_append, List.count_replicate_self,
      List.count_cons_of_ne Bool.false_ne_true]
    omega
  · rw [hu', hv']
    simp only [evalWord_block43, evalWord, eval_run, Matrix.mul_assoc]

end D5.S3.Quantum.Analysis.RefinedBMVNearScalarClustered
