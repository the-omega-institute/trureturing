/- GID: D5/S3/Fourier/Concentration/CyclicPrefixFourthMoment
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CyclicPrefixFourthMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact fourth moment of a cyclic prefix with a correction for wrapped differences. -/

import D5.S3.Fourier.Concentration.CyclicFejerBand
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum

/-! Exact fourth moment of a prefix character sum on a finite cyclic group. -/

open Finset

noncomputable section

namespace D5.S3.Fourier.Concentration.CyclicPrefixFourthMoment

open CyclicFejerBand

variable {q : ℕ} [NeZero q]

private theorem card_prefixPairs_eq_add (N : ℕ) (hN : N ≤ q) (r : ZMod q) :
    (prefixPairs q N r).card = (N - r.val) + (N - (q - r.val)) := by
  classical
  let d := r.val
  have hd : d < q := ZMod.val_lt r
  have hcast : (d : ZMod q) = r := ZMod.natCast_zmod_val r
  let P := (range (N - d)).map
    ⟨fun j => (j + d, j), fun _ _ h => congrArg Prod.snd h⟩
  let Q := (range (N - (q - d))).map
    ⟨fun j => (j, j + (q - d)), fun _ _ h => congrArg Prod.fst h⟩
  have hP (a b : ℕ) : (a,b) ∈ P ↔ a = b + d ∧ b < N - d := by
    constructor
    · intro h
      obtain ⟨j,hj,he⟩ := mem_map.mp h
      change (j+d,j) = (a,b) at he
      cases he
      exact ⟨rfl,mem_range.mp hj⟩
    · rintro ⟨rfl,h⟩
      exact mem_map.mpr ⟨b,mem_range.mpr h,rfl⟩
  have hQ (a b : ℕ) : (a,b) ∈ Q ↔ b = a + (q - d) ∧ a < N - (q - d) := by
    constructor
    · intro h
      obtain ⟨j,hj,he⟩ := mem_map.mp h
      change (j,j+(q-d)) = (a,b) at he
      cases he
      exact ⟨rfl,mem_range.mp hj⟩
    · rintro ⟨rfl,h⟩
      exact mem_map.mpr ⟨a,mem_range.mpr h,rfl⟩
  have hneg : -((q - d : ℕ) : ZMod q) = r := by
    rw [Nat.cast_sub hd.le, ZMod.natCast_self, zero_sub, neg_neg, hcast]
  have hdis : Disjoint P Q := by
    rw [Finset.disjoint_left]
    rintro ⟨a,b⟩ ha hb
    have hpa := (hP a b).mp ha
    have hqb := (hQ a b).mp hb
    omega
  have hunion : prefixPairs q N r = P ∪ Q := by
    ext p
    rcases p with ⟨i,j⟩
    simp only [prefixPairs, mem_filter, mem_product, mem_range, mem_union, hP, hQ]
    constructor
    · rintro ⟨⟨hi,hj⟩,hc⟩
      by_cases hji : j ≤ i
      · rw [← Nat.cast_sub hji] at hc
        have hr : i - j = d := by
          simpa only [d, ZMod.val_natCast_of_lt (show i - j < q by omega)] using
            congrArg (ZMod.val (n := q)) hc
        exact Or.inl ⟨by omega,by omega⟩
      · have hij : i ≤ j := by omega
        have he : ((i : ZMod q) - j) = ((q - (j - i) : ℕ) : ZMod q) := by
          rw [Nat.cast_sub (show j - i ≤ q by omega), ZMod.natCast_self, zero_sub, Nat.cast_sub hij]
          abel
        rw [he] at hc
        have hr : q - (j - i) = d := by
          simpa only [d, ZMod.val_natCast_of_lt (show q - (j - i) < q by omega)] using
            congrArg (ZMod.val (n := q)) hc
        exact Or.inr ⟨by omega,by omega⟩
    · rintro (⟨rfl,hj⟩ | ⟨rfl,hi⟩)
      · refine ⟨⟨by omega,by omega⟩,?_⟩
        rw [Nat.cast_add, add_sub_cancel_left, hcast]
      · refine ⟨⟨by omega,by omega⟩,?_⟩
        rw [Nat.cast_add]
        have he : ((i : ZMod q) - ((i : ZMod q) + ((q - d : ℕ) : ZMod q))) =
            -((q - d : ℕ) : ZMod q) := by abel
        exact he.trans hneg
  rw [hunion, card_union_of_disjoint hdis]
  simp [P,Q,d]

private theorem spectral_prefix_pair_count (N : ℕ) (k : ZMod q) :
    ZMod.dft (fun r : ZMod q => (((prefixPairs q N r).card : ℕ) : ℂ)) k =
      (‖prefixCharacter q N k‖ ^ 2 : ℝ) := by
  have hB : prefixCharacter q N k * prefixCharacter q N (-k) =
      ((‖prefixCharacter q N k‖ ^ 2 : ℝ) : ℂ) := by
    rw [prefixCharacter_neg, mul_comm, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have hchar := pair_char_factor N (-k)
  rw [neg_neg] at hchar
  rw [← hB, mul_comm, ← hchar, ZMod.dft_apply]
  apply Complex.ext
  · simpa only [Complex.re_sum, smul_eq_mul, mul_comm _ ((prefixPairs q N _).card : ℂ),
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul,
      sub_zero, mul_neg] using
      (sum_prefixPairs (q := q) N (fun r => (ZMod.stdAddChar (-(r * k))).re))
  · simpa only [Complex.im_sum, smul_eq_mul, mul_comm _ ((prefixPairs q N _).card : ℂ),
      Complex.mul_im, Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul,
      add_zero, zero_add, mul_neg] using
      (sum_prefixPairs (q := q) N (fun r => (ZMod.stdAddChar (-(r * k))).im))

private theorem fourth_moment_pair_energy (q N : ℕ) [NeZero q] (hN : N ≤ q) :
    ∑ k : ZMod q, ‖prefixCharacter q N k‖ ^ 4 =
      (q : ℝ) * ∑ r : ZMod q,
        ((((N - r.val) + (N - (q - r.val)) : ℕ)) : ℝ) ^ 2 := by
  let C (r : ZMod q) : ℝ := (prefixPairs q N r).card
  have h := fourier_pair_sum N (fun r : ZMod q => (C r : ℂ))
  have hsum : (∑ i ∈ range N, ∑ j ∈ range N, (C ((i : ZMod q) - j) : ℂ)) =
      ((∑ r : ZMod q, C r ^ 2 : ℝ) : ℂ) := by
    have hC := congrArg Complex.ofReal (sum_prefixPairs N C).symm
    simpa only [Complex.ofReal_sum, C, pow_two] using hC
  rw [hsum] at h
  have hb (k : ZMod q) : prefixCharacter q N k * prefixCharacter q N (-k) =
      ((‖prefixCharacter q N k‖ ^ 2 : ℝ) : ℂ) := by
    rw [prefixCharacter_neg, mul_comm, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have hterms (k : ZMod q) :
      prefixCharacter q N k * prefixCharacter q N (-k) *
        ZMod.dft (fun r : ZMod q => (C r : ℂ)) k =
      ((‖prefixCharacter q N k‖ ^ 4 : ℝ) : ℂ) := by
    rw [hb]
    simp only [C, Complex.ofReal_natCast, spectral_prefix_pair_count, ← Complex.ofReal_mul]
    push_cast
    ring
  simp_rw [hterms] at h
  have hreal := congrArg Complex.re h
  simp only [Complex.re_sum, Complex.ofReal_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, Complex.ofReal_im, zero_mul, sub_zero] at hreal
  rw [← hreal]
  congr 1
  apply sum_congr rfl
  intro r _
  simp [C, card_prefixPairs_eq_add N hN]

private theorem sum_linear_rank (n : ℕ) :
    (∑ j ∈ range n, ((j : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  cases n with
  | zero => simp
  | succ n =>
    have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.sum_range_add_choose n 1)
    simp only [Nat.cast_sum, Nat.choose_one_right] at h
    change (∑ j ∈ range (n + 1), (↑(j + 1) : ℝ)) = ↑((n + 1 + 1).choose 2) at h
    rw [Nat.cast_choose_two] at h
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] at h ⊢
    rw [h]
    ring

theorem sum_square_rank (n : ℕ) :
    (∑ j ∈ range n, ((j : ℝ) + 1) ^ 2) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  cases n with
  | zero => simp
  | succ n =>
    have hs := congrArg (fun a : ℕ => (a : ℝ)) (Nat.sum_range_add_choose n 2)
    push_cast only [Nat.cast_sum] at hs
    have hchoose : (((n + 2 + 1).choose 3 : ℕ) : ℝ) =
        ((n : ℝ) + 3) * ((n : ℝ) + 2) * ((n : ℝ) + 1) / 6 := by
      have h := congrArg (fun a : ℕ => (a : ℝ))
        (Nat.descFactorial_eq_factorial_mul_choose (n + 2 + 1) 3)
      rw [show (n + 2 + 1).descFactorial 3 =
        (n + 2 + 1 - 2) * (n + 2 + 1).descFactorial 2 from Nat.descFactorial_succ _ 2,
        show n + 2 + 1 - 2 = n + 1 by omega] at h
      simp only [Nat.cast_mul, Nat.cast_descFactorial_two, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat] at h
      norm_num [Nat.factorial] at h
      linear_combination -h / 6
    calc
      _ = ∑ j ∈ range (n + 1), (2 * (((j + 2).choose 2 : ℕ) : ℝ) - ((j : ℝ) + 1)) := by
        apply sum_congr rfl
        intro j _
        rw [Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat]
        ring
      _ = _ := by
        rw [sum_sub_distrib, ← mul_sum, hs, hchoose, sum_linear_rank, Nat.cast_succ]
        ring

private theorem sum_opposite_rank (m : ℕ) :
    (∑ j ∈ range m, ((j : ℝ) + 1) * ((m : ℝ) - (j : ℝ))) =
      (m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 2) / 6 := by
  calc
    _ = (∑ j ∈ range m, (((m : ℝ) + 1) * ((j : ℝ) + 1) - ((j : ℝ) + 1) ^ 2)) := by
      exact sum_congr rfl fun j _ => by ring
    _ = _ := by
      rw [sum_sub_distrib, ← mul_sum, sum_square_rank, sum_linear_rank]
      ring

private theorem sum_forward_count_sq (N q : ℕ) (hNq : N ≤ q) :
    (∑ r ∈ range q, ((N - r : ℕ) : ℝ) ^ 2) =
      (N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6 := by
  rw [← sum_square_rank]
  calc
    _ = ∑ r ∈ range N, ((N - r : ℕ) : ℝ) ^ 2 := by
      symm
      apply sum_subset (fun _ hr => mem_range.mpr ((mem_range.mp hr).trans_le hNq))
      intro r _ hr
      simp [Nat.sub_eq_zero_of_le (by simpa using hr : N ≤ r)]
    _ = _ := by
      rw [← sum_range_reflect]
      apply sum_congr rfl
      intro r hr
      have h : N - (N - 1 - r) = r + 1 := by
        have hr' := mem_range.mp hr
        omega
      rw [h, Nat.cast_add, Nat.cast_one]

private theorem sum_wrapped_count_sq (N q : ℕ) (hNq : N ≤ q) :
    (∑ r ∈ range q, ((N - (q - r) : ℕ) : ℝ) ^ 2) =
      ((N - 1 : ℕ) : ℝ) * (((N - 1 : ℕ) : ℝ) + 1) *
        (2 * ((N - 1 : ℕ) : ℝ) + 1) / 6 := by
  rw [← sum_square_rank]
  calc
    _ = ∑ r ∈ Ico (q - N + 1) q, ((N - (q - r) : ℕ) : ℝ) ^ 2 := by
      symm
      apply sum_subset (fun r hr => mem_range.mpr (mem_Ico.mp hr).2)
      intro r hr hr'
      have hr₀ := mem_range.mp hr
      have hz : N - (q - r) = 0 := by
        simp only [mem_Ico, hr₀, and_true, not_le] at hr'
        omega
      simp [hz]
    _ = _ := by
      rw [sum_Ico_eq_sum_range]
      have ht : q - (q - N + 1) = N - 1 := by omega
      rw [ht]
      apply sum_congr rfl
      intro j hj
      have hj' := mem_range.mp hj
      have he : N - (q - (q - N + 1 + j)) = j + 1 := by omega
      rw [he, Nat.cast_add, Nat.cast_one]

private theorem sum_forward_mul_wrapped_count (N q : ℕ) (hNq : N ≤ q) :
    let m := 2 * N - q - 1
    (∑ r ∈ range q, ((N - r : ℕ) : ℝ) * ((N - (q - r) : ℕ) : ℝ)) =
      (m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 2) / 6 := by
  dsimp only
  rw [← sum_opposite_rank]
  calc
    _ = ∑ r ∈ Ico (q - N + 1) N, ((N - r : ℕ) : ℝ) * ((N - (q - r) : ℕ) : ℝ) := by
      symm
      apply sum_subset (fun r hr => mem_range.mpr ((mem_Ico.mp hr).2.trans_le hNq))
      intro r hr hr'
      have hr₀ := mem_range.mp hr
      by_cases hrN : r < N
      · have hz : N - (q - r) = 0 := by
          simp only [mem_Ico, hrN, and_true, not_le] at hr'
          omega
        simp [hz]
      · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hrN)]
    _ = _ := by
      rw [sum_Ico_eq_sum_range]
      have ht : N - (q - N + 1) = 2 * N - q - 1 := by omega
      rw [ht]
      apply sum_congr rfl
      intro j hj
      have hj' := mem_range.mp hj
      have hother : N - (q - (q - N + 1 + j)) = j + 1 := by omega
      have hone : N - (q - N + 1 + j) = (2 * N - q - 1) - j := by omega
      rw [hother, hone, Nat.cast_add, Nat.cast_one,
        Nat.cast_sub (Nat.le_of_lt hj')]
      ring

private theorem prefix_pair_energy (N q : ℕ) (hNq : N ≤ q) :
    let m := 2 * N - q - 1
    3 * (∑ r ∈ range q, (((N - r : ℕ) : ℝ) + ((N - (q - r) : ℕ) : ℝ)) ^ 2) =
      (N : ℝ) * (2 * (N : ℝ) ^ 2 + 1) + (m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
  dsimp only
  by_cases hN : 1 ≤ N
  swap
  · have : N = 0 := by omega
    subst N
    simp
  have hsum :
      (∑ r ∈ range q, (((N - r : ℕ) : ℝ) + ((N - (q - r) : ℕ) : ℝ)) ^ 2) =
        (∑ r ∈ range q, ((N - r : ℕ) : ℝ) ^ 2) +
        (∑ r ∈ range q, ((N - (q - r) : ℕ) : ℝ) ^ 2) +
        2 * ∑ r ∈ range q, ((N - r : ℕ) : ℝ) * ((N - (q - r) : ℕ) : ℝ) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun r _ => by ring
  rw [hsum, sum_forward_count_sq N q hNq, sum_wrapped_count_sq N q hNq,
    sum_forward_mul_wrapped_count N q hNq]
  rw [Nat.cast_sub hN, Nat.cast_one]
  ring

private theorem sum_zmod_val (q : ℕ) [NeZero q] (f : ℕ → ℝ) :
    (∑ r : ZMod q, f r.val) = ∑ r ∈ range q, f r := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
      change (∑ i : Fin (q + 1), f i.val) = _
      exact Fin.sum_univ_eq_sum_range f (q + 1)

/-- Exact fourth moment of the prefix character sum. The cubic correction counts
the residues with both a forward and a wrapped difference. -/
theorem sum_prefixCharacter_norm_four (q N : ℕ) [NeZero q] (hNq : N ≤ q) :
    let fourthPower := fun z : ℂ => ‖z‖ ^ 4
    let m := 2 * N - q - 1
    3 * (∑ k : ZMod q, fourthPower (prefixCharacter q N k)) =
      (q : ℝ) * ((N : ℝ) * (2 * (N : ℝ) ^ 2 + 1) +
        (m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  dsimp only
  rw [fourth_moment_pair_energy q N hNq]
  rw [show (∑ r : ZMod q, (((N - r.val + (N - (q - r.val)) : ℕ)) : ℝ) ^ 2) =
      ∑ r ∈ range q, (((N - r + (N - (q - r)) : ℕ)) : ℝ) ^ 2 from
        sum_zmod_val q (fun r => (((N - r + (N - (q - r)) : ℕ)) : ℝ) ^ 2)]
  rw [mul_left_comm (3 : ℝ)]
  congr 1
  simpa only [Nat.cast_add] using prefix_pair_energy N q hNq

end D5.S3.Fourier.Concentration.CyclicPrefixFourthMoment
