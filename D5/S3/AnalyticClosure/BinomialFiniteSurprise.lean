/- GID: D5/S3/AnalyticClosure/BinomialFiniteSurprise
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/BinomialFiniteSurprise
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite binomial mode, surprise envelopes, partitions and all natural moments. -/

import D5.S3.AnalyticClosure.BinomialLocalGaussian
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
open Real Finset
open scoped BigOperators
open D5.S3.AnalyticClosure.BinomialLocalGaussian
namespace D5.S3.AnalyticClosure.BinomialFiniteSurprise

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
-- The distance inductions and shell injection require repeated real and natural arithmetic.
/-- Uniform finite binomial surprise estimates, including the original floor mode,
all natural escort moments, variance and the centered fourth moment. The finite
ratio bounds feed the distance shells and clipped plateau used in the moments. -/
theorem result :
    let U : ℝ := 4 * exp (1/8) / (1-exp (-(1/8)))
    let D : ℝ := exp (-768) / 2
    let c : ℝ := min (3/128) D
    let C : ℝ := 32+U
    let K : ℕ → ℝ := fun k => (U/D) * (2*((k:ℝ)+1))^k
    0 < c ∧ 0 < C ∧ (∀ k, 0 < K k) ∧
    ∀ (N : ℕ) (p : ℝ), p ∈ Set.Icc (1/4 : ℝ) (3/4 : ℝ) →
      let q : Fin (N+1) → ℝ := fun n => binomialMass p N n.val
      let M : ℝ := Finset.univ.sup' Finset.univ_nonempty q
      let S : Fin (N+1) → ℝ := fun n => -log (q n / M)
      let Z : ℝ → ℝ := fun β => ∑ n, exp (-β * S n)
      let E : ℝ → ℕ → ℝ := fun β k => (∑ n, (S n)^k * exp (-β*S n)) / Z β
      let w : ℝ → Fin (N+1) → ℝ := fun β n => exp (-β*S n) / Z β
      let μ : ℝ → ℝ := fun β => ∑ n, w β n * S n
      let V : ℝ → ℝ := fun β => ∑ n, w β n * (S n-μ β)^2
      let H : ℝ → ℝ := fun β => ∑ n, w β n * |S n-μ β|^4
      (∑ n, q n) = 1 ∧
      (∀ n, 0 < q n ∧ q n ≤ M ∧ 0 ≤ S n) ∧
      0 < M ∧ M ≤ 1 ∧
      (∀ β : ℝ, 0 < Z β ∧ E β 0 = 1 ∧ (∀ n, 0 ≤ w β n) ∧ (∑ n, w β n) = 1) ∧
      (1 ≤ N →
        let m : ℕ := ⌊((N:ℝ)+1)*p⌋₊
        let δ : ℝ := ((N:ℝ)+1)*p-(m:ℝ)
        let z : Fin (N+1) → ℝ := fun n => ((n.val:ℝ)-(N:ℝ)*p) / sqrt ((N:ℝ)*p*(1-p))
        m ≤ N ∧ M = binomialMass p N m ∧ |(m:ℝ)-(N:ℝ)*p| ≤ 1 ∧
        (δ = 0 → 1 ≤ m ∧ binomialMass p N (m-1) = M) ∧
        ∀ n,
          let t : ℝ := |(n.val:ℝ)-(m:ℝ)|
          t*(t-1)/(2*(N:ℝ)) ≤ S n ∧
          (3/128 : ℝ)*(z n)^2-1/2 ≤ S n ∧ S n ≤ 32*(1+(z n)^2) ∧
          c*(z n)^2-C ≤ S n ∧ S n ≤ C*(1+(z n)^2)) ∧
      Z (1/2) ≤ U*sqrt ((N:ℝ)+1) ∧
      (∀ β : ℝ, 1/2 ≤ β → Z β ≤ Z (1/2)) ∧
      (∀ α : ℝ, α ∈ Set.Icc (1:ℝ) 2 →
        D*sqrt ((N:ℝ)+1) ≤ Z α ∧ Z α ≤ U*sqrt ((N:ℝ)+1) ∧
        c*sqrt ((N:ℝ)+1) ≤ Z α ∧ Z α ≤ C*sqrt ((N:ℝ)+1) ∧
        (∀ k : ℕ, 0 ≤ E α k ∧ E α k ≤ K k) ∧
        0 ≤ V α ∧ V α ≤ E α 2 ∧ E α 2 ≤ K 2 ∧
        0 ≤ H α ∧ H α ≤ 16*E α 4 ∧ 16*E α 4 ≤ 16*K 4) ∧
      (N = 0 →
        (∀ n, n.val = 0 ∧ q n = 1 ∧ S n = 0) ∧ M = 1 ∧
        ∀ β : ℝ, Z β = 1 ∧ ∀ k : ℕ, 1 ≤ k → E β k = 0) := by
  classical
  let U : ℝ := 4*exp (1/8)/(1-exp (-(1/8)))
  let D : ℝ := exp (-768)/2
  let c : ℝ := min (3/128) D
  let C : ℝ := 32+U
  let K : ℕ → ℝ := fun k => (U/D)*(2*((k:ℝ)+1))^k
  have hden0 : 0 < 1-exp (-(1/8:ℝ)) := by
    have hh := exp_lt_one_iff.mpr (by norm_num : -(1/8:ℝ) < 0)
    linarith
  have hU0 : 0 < U := by dsimp [U]; positivity
  have hU1 : 1 ≤ U := by
    dsimp [U]
    apply (le_div_iff₀ hden0).2
    have hh := exp_le_exp.mpr (by norm_num : (0:ℝ) ≤ 1/8)
    rw [exp_zero] at hh
    nlinarith [exp_pos (-(1/8:ℝ))]
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hD1 : D ≤ 1 := by
    have hh := exp_le_one_iff.mpr (by norm_num : (-768:ℝ) ≤ 0)
    dsimp [D]; linarith
  have hc0 : 0 < c := lt_min (by norm_num) hD0
  have hC0 : 0 < C := by dsimp [C]; linarith
  have hK0 (k : ℕ) : 0 < K k := by dsimp [K]; positivity
  refine ⟨hc0, hC0, hK0, ?_⟩
  intro N p hp
  have hp0 : 0 < p := by linarith [hp.1]
  have hp1 : 0 < 1-p := by linarith [hp.2]
  let Q : ℕ → ℝ := binomialMass p N
  let q : Fin (N+1) → ℝ := fun n => Q n.val
  let M : ℝ := univ.sup' univ_nonempty q
  let S : ℕ → ℝ := fun n => log M - log (Q n)
  have hQ (i : ℕ) (hi : i ≤ N) : 0 < Q i := by
    dsimp [Q, binomialMass]
    exact mul_pos (mul_pos (by exact_mod_cast Nat.choose_pos hi) (pow_pos hp0 _))
      (pow_pos hp1 _)
  have hsum : ∑ n : Fin (N+1), q n = 1 := by
    rw [Fin.sum_univ_eq_sum_range]
    have h := (add_pow p (1-p) N).symm
    simpa [q, Q, binomialMass, mul_comm, mul_left_comm, mul_assoc] using h
  have hqM (n : Fin (N+1)) : q n ≤ M := le_sup' q (mem_univ n)
  have hM0 : 0 < M := lt_of_lt_of_le (hQ 0 (Nat.zero_le _)) (hqM ⟨0, by omega⟩)
  have hM1 : M ≤ 1 := by
    apply sup'_le
    intro n _
    rw [← hsum]
    exact single_le_sum (fun i _ => (hQ i.val (by omega)).le) (mem_univ n)
  have hS0 (i : ℕ) (hi : i ≤ N) : 0 ≤ S i := by
    have hle : Q i ≤ M := hqM ⟨i, by omega⟩
    dsimp [S]
    exact sub_nonneg.mpr (log_le_log (hQ i hi) hle)
  have hS (n : Fin (N+1)) : S n.val = -log (q n / M) := by
    rw [log_div (hQ n.val (by omega)).ne' hM0.ne']
    dsimp [S]; ring
  have hrec (i : ℕ) (hi : i < N) :
      ((i:ℝ)+1)*(1-p)*Q (i+1) = ((N:ℝ)-i)*p*Q i := by
    have h := Nat.choose_succ_right_eq N i
    have hc : (N.choose (i+1):ℝ)*((i:ℝ)+1) = (N.choose i:ℝ)*((N:ℝ)-i) := by
      have hcast : (N.choose (i+1):ℝ)*((i:ℝ)+1) = (N.choose i:ℝ)*(N-i:ℕ) := by exact_mod_cast h
      simpa [Nat.cast_sub hi.le] using hcast
    have he : N-i = (N-(i+1))+1 := by omega
    dsimp [Q, binomialMass]
    rw [he, pow_succ, pow_succ]
    linear_combination (p^i*(1-p)^(N-(i+1))*p*(1-p)) * hc
  have hstep (i : ℕ) (hi : i < N) :
      Q (i+1) / Q i = ((N:ℝ)-i)*p / (((i:ℝ)+1)*(1-p)) := by
    apply (div_eq_div_iff (hQ i hi.le).ne' (by positivity)).2
    nlinarith [hrec i hi]
  have hlogstep (i : ℕ) (hi : i < N) :
      S (i+1)-S i = log ((((i:ℝ)+1)*(1-p)) / (((N:ℝ)-i)*p)) := by
    have hA : 0 < ((N:ℝ)-i)*p := mul_pos (by exact sub_pos.mpr (by exact_mod_cast hi)) hp0
    have hB : 0 < ((i:ℝ)+1)*(1-p) := by positivity
    have h := congrArg log (hstep i hi)
    rw [log_div (hQ (i+1) (by omega)).ne' (hQ i hi.le).ne',
      log_div hA.ne' hB.ne'] at h
    rw [log_div hB.ne' hA.ne']
    dsimp [S]
    linarith
  let m : ℕ := ⌊((N:ℝ)+1)*p⌋₊
  have hNp0 : 0 ≤ ((N:ℝ)+1)*p := by positivity
  have hmle : (m:ℝ) ≤ ((N:ℝ)+1)*p := Nat.floor_le hNp0
  have hmlt : ((N:ℝ)+1)*p < (m:ℝ)+1 := Nat.lt_floor_add_one _
  have hmN : m ≤ N := by
    have : ((N:ℝ)+1)*p < (N:ℝ)+1 := by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
    have : (m:ℝ) < (N:ℝ)+1 := hmle.trans_lt this
    have : m < N+1 := by exact_mod_cast this
    omega
  have hmode : ∀ i : ℕ, i ≤ N → Q i ≤ Q m := by
    have hleft : MonotoneOn Q (Set.Icc 0 m) := by
      apply monotoneOn_of_le_add_one Set.ordConnected_Icc
      intro i _ hi his
      have hin : i < N := by simp only [Set.mem_Icc] at hi his; omega
      have hic : (i:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast his.2
      have hdiff : ((i:ℝ)+1)*(1-p) ≤ ((N:ℝ)-i)*p := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hdiff (hQ i hin.le).le
      have hbase := hrec i hin
      exact (mul_le_mul_iff_right₀ (show 0 < ((i:ℝ)+1)*(1-p) by positivity)).mp
        (by nlinarith)
    have hright : AntitoneOn Q (Set.Icc m N) := by
      apply antitoneOn_of_add_one_le Set.ordConnected_Icc
      intro i _ hi his
      have hin : i < N := by simp only [Set.mem_Icc] at hi his; omega
      have hic : (m:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi.1
      have hdiff : ((N:ℝ)-i)*p ≤ ((i:ℝ)+1)*(1-p) := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hdiff (hQ i hin.le).le
      have hbase := hrec i hin
      exact (mul_le_mul_iff_right₀ (show 0 < ((i:ℝ)+1)*(1-p) by positivity)).mp
        (by nlinarith)
    intro i hi
    by_cases him : i ≤ m
    · exact hleft ⟨by omega, him⟩ ⟨by omega, le_rfl⟩ him
    · exact hright ⟨le_rfl, hmN⟩ ⟨by omega, hi⟩ (by omega)
  have hMm : M = Q m := le_antisymm
    (sup'_le _ _ (fun i _ => hmode i.val (by omega))) (hqM ⟨m, by omega⟩)
  have hSm : S m = 0 := by simp [S, hMm]
  have hmd : |(m:ℝ)-(N:ℝ)*p| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hp.1, hp.2]
  have htie (hδ : ((N:ℝ)+1)*p-(m:ℝ) = 0) :
      1 ≤ m ∧ Q (m-1) = M := by
    have hm0 : 1 ≤ m := by
      by_contra h
      have hmz : m = 0 := by omega
      simp only [hmz, Nat.cast_zero, sub_zero] at hδ
      have : 0 < ((N:ℝ)+1)*p := by positivity
      linarith
    refine ⟨hm0, ?_⟩
    have hi : m-1 < N := by omega
    have h := hrec (m-1) hi
    have hc : ((m-1:ℕ):ℝ) = (m:ℝ)-1 := by rw [Nat.cast_sub hm0]; norm_num
    rw [show m-1+1=m by omega, hc] at h
    rw [hMm]
    have he : ((N:ℝ)-(m-1))*p = ((m-1)+1)*(1-p) := by nlinarith
    rw [he] at h
    have hmR : (0:ℝ) < m := by exact_mod_cast hm0
    exact ((mul_left_cancel₀ (by nlinarith : ((m:ℝ)-1+1)*(1-p) ≠ 0)) h).symm
  have hN (hN1 : 1 ≤ N) :
      ∀ n : ℕ, n ≤ N → |(n:ℝ)-(m:ℝ)| *(|(n:ℝ)-(m:ℝ)| -1)/(2*(N:ℝ)) ≤ S n := by
    have hN0 : (0:ℝ) < N := by exact_mod_cast hN1
    have hscalar (A B r : ℝ) (hA : 0 < A) (hB : 0 < B)
        (hAN : A ≤ N) (hr : 0 ≤ r) (hgap : r ≤ A-B) :
        r/(N:ℝ) ≤ log (A/B) := by
      have hlog := one_sub_inv_le_log_of_pos (div_pos hA hB)
      have hf : r/(N:ℝ) ≤ (A-B)/A := by
        apply (div_le_div_iff₀ hN0 hA).2
        nlinarith
      have he : 1-(A/B)⁻¹ = (A-B)/A := by field_simp
      rw [he] at hlog
      exact hf.trans hlog
    have hright (t : ℕ) (ht : m+t ≤ N) :
        (t:ℝ)*((t:ℝ)-1)/(2*(N:ℝ)) ≤ S (m+t) := by
      induction t with
      | zero => simp [hSm]
      | succ t ih =>
        have htn : m+t < N := by omega
        have hi := ih (by omega)
        have hl := hlogstep (m+t) htn
        have hc : ((m+t:ℕ):ℝ) = (m:ℝ)+t := by push_cast; rfl
        have hA : 0 < (((m+t:ℕ):ℝ)+1)*(1-p) := by positivity
        have hB : 0 < ((N:ℝ)-((m+t:ℕ):ℝ))*p := by
          have : ((m+t:ℕ):ℝ) < N := by exact_mod_cast htn
          exact mul_pos (by linarith) hp0
        have hab : (((m+t:ℕ):ℝ)+1)*(1-p) ≤ N := by
          have : ((m+t:ℕ):ℝ)+1 ≤ N := by exact_mod_cast ht
          have := mul_le_mul_of_nonneg_left (show 1-p ≤ 1 by linarith)
            (by positivity : 0 ≤ ((m+t:ℕ):ℝ)+1)
          nlinarith
        have hgap : (t:ℝ) ≤ (((m+t:ℕ):ℝ)+1)*(1-p)-((N:ℝ)-((m+t:ℕ):ℝ))*p := by
          rw [hc]; nlinarith
        have hh := hscalar _ _ (t:ℝ) hA hB hab (by positivity) hgap
        rw [← hl] at hh
        have he : (m+Nat.succ t) = m+t+1 := by omega
        rw [he]; push_cast
        have heq : ((t:ℝ)+1)*((t:ℝ)+1-1)/(2*(N:ℝ)) =
            (t:ℝ)*((t:ℝ)-1)/(2*(N:ℝ)) + (t:ℝ)/(N:ℝ) := by field_simp; ring
        rw [heq]; linarith
    have hleft (t : ℕ) (ht : t ≤ m) :
        (t:ℝ)*((t:ℝ)-1)/(2*(N:ℝ)) ≤ S (m-t) := by
      induction t with
      | zero => simp [hSm]
      | succ t ih =>
        have hi := ih (by omega)
        let i := m-(t+1)
        have hin : i < N := by dsimp [i]; omega
        have hie : i+1=m-t := by dsimp [i]; omega
        have hic : (i:ℝ) = (m:ℝ)-(t:ℝ)-1 := by
          dsimp [i]; rw [Nat.cast_sub ht]; push_cast; ring
        have hA : 0 < ((N:ℝ)-i)*p := by
          have : (i:ℝ) < N := by exact_mod_cast hin
          exact mul_pos (by linarith) hp0
        have hB : 0 < ((i:ℝ)+1)*(1-p) := by positivity
        have hab : ((N:ℝ)-i)*p ≤ N := by
          have hi0 : (0:ℝ) ≤ i := by positivity
          nlinarith [hp.2, (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
        have hgap : (t:ℝ) ≤ ((N:ℝ)-i)*p-((i:ℝ)+1)*(1-p) := by
          rw [hic]; nlinarith
        have hh := hscalar _ _ (t:ℝ) hA hB hab (by positivity) hgap
        have hl := hlogstep i hin
        rw [log_div hB.ne' hA.ne'] at hl
        rw [log_div hA.ne' hB.ne'] at hh
        rw [hie] at hl
        have heq : ((t:ℝ)+1)*((t:ℝ)+1-1)/(2*(N:ℝ)) =
            (t:ℝ)*((t:ℝ)-1)/(2*(N:ℝ)) + (t:ℝ)/(N:ℝ) := by field_simp; ring
        push_cast
        change ((t:ℝ)+1)*((t:ℝ)+1-1)/(2*(N:ℝ)) ≤ S i
        rw [heq]; linarith
    intro n hn
    by_cases hmn : m ≤ n
    · have hh := hright (n-m) (by omega)
      rw [Nat.add_sub_of_le hmn, Nat.cast_sub hmn] at hh
      rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmn))]
      exact hh
    · have hnm : n ≤ m := by omega
      have hh := hleft (m-n) (by omega)
      rw [Nat.sub_sub_self hnm, Nat.cast_sub hnm] at hh
      rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hnm))]
      convert hh using 1; ring
  have hpvar : 3/16 ≤ p*(1-p) ∧ p*(1-p) ≤ 1/4 := by
    have hl := mul_nonneg (show 0 ≤ p-1/4 by linarith [hp.1]) (show 0 ≤ 3/4-p by linarith [hp.2])
    have hu := sq_nonneg (p-1/2)
    constructor <;> nlinarith
  have hglobal (n : ℕ) (hn : n ≤ N) : S n ≤ 2*(N:ℝ) := by
    have hmass : (1/4:ℝ)^N ≤ Q n := by
      have hc : (1:ℝ) ≤ N.choose n := by exact_mod_cast Nat.choose_pos hn
      calc
        (1/4:ℝ)^N = 1*(1/4:ℝ)^n*(1/4:ℝ)^(N-n) := by
          rw [one_mul, ← pow_add, Nat.add_sub_of_le hn]
        _ ≤ Q n := by dsimp [Q, binomialMass]; gcongr <;> linarith [hp.1, hp.2]
    have hlogq := log_le_log (pow_pos (by norm_num : (0:ℝ)<1/4) N) hmass
    have hlogM := log_nonpos hM0.le hM1
    have hlog4 : log (4:ℝ) < 2 := by
      have h := log_two_lt_d9
      have he : log (4:ℝ) = 2*log 2 := by
        convert log_pow (2:ℝ) 2 using 1 <;> norm_num
      rw [he]; linarith
    rw [log_pow, log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0), log_one] at hlogq
    dsimp [S]
    nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hcentral (hN8 : 8 ≤ N) : ∀ n : ℕ, n ≤ N →
      (N:ℝ)/8 ≤ n → (n:ℝ) ≤ 7*(N:ℝ)/8 →
      S n ≤ 16*|(n:ℝ)-(m:ℝ)| *(|(n:ℝ)-(m:ℝ)| +1)/(N:ℝ) := by
    have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN8R : (8:ℝ) ≤ N := by exact_mod_cast hN8
    have hmlo : (N:ℝ)/8 ≤ m := by nlinarith [hp.1]
    have hmhi : (m:ℝ) ≤ 7*(N:ℝ)/8 := by nlinarith [hp.2]
    have hscalar (A B s : ℝ) (hA : 0 < A) (hB : 0 < B)
        (hBN : (N:ℝ)/32 ≤ B) (hs : 0 ≤ s) (hgap : A-B ≤ s) :
        log (A/B) ≤ 32*s/(N:ℝ) := by
      have hlog := log_le_sub_one_of_pos (div_pos hA hB)
      have hf : (A-B)/B ≤ 32*s/(N:ℝ) := by
        apply (div_le_div_iff₀ hB hN0).2
        nlinarith
      have he : A/B-1 = (A-B)/B := by field_simp
      rw [he] at hlog
      exact hlog.trans hf
    have hright (t : ℕ) (ht : m+t ≤ N) (hthi : ((m+t:ℕ):ℝ) ≤ 7*(N:ℝ)/8) :
        S (m+t) ≤ 16*(t:ℝ)*((t:ℝ)+1)/(N:ℝ) := by
      induction t with
      | zero => simp [hSm]
      | succ t ih =>
        have hin : m+t < N := by omega
        have htR : ((m+(t+1):ℕ):ℝ) = (m:ℝ)+t+1 := by push_cast; ring
        have hi := ih (by omega) (by push_cast at hthi ⊢; linarith)
        have hl := hlogstep (m+t) hin
        have hic : ((m+t:ℕ):ℝ) = (m:ℝ)+t := by push_cast; rfl
        have hA : 0 < (((m+t:ℕ):ℝ)+1)*(1-p) := by positivity
        have hB : 0 < ((N:ℝ)-((m+t:ℕ):ℝ))*p := by
          exact mul_pos (sub_pos.mpr (by exact_mod_cast hin)) hp0
        have hBN : (N:ℝ)/32 ≤ ((N:ℝ)-((m+t:ℕ):ℝ))*p := by
          have hihi : ((m+t:ℕ):ℝ) ≤ 7*(N:ℝ)/8 := by push_cast at hthi ⊢; linarith
          have hh := mul_nonneg (show 0 ≤ (N:ℝ)-(m+t) by linarith)
            (show 0 ≤ p-1/4 by linarith [hp.1])
          nlinarith
        have hgap : (((m+t:ℕ):ℝ)+1)*(1-p)-((N:ℝ)-((m+t:ℕ):ℝ))*p ≤ (t:ℝ)+1 := by
          rw [hic]; nlinarith
        have hh := hscalar _ _ ((t:ℝ)+1) hA hB hBN (by positivity) hgap
        rw [← hl] at hh
        have he : m+Nat.succ t = m+t+1 := by omega
        rw [he]; push_cast
        have heq : 16*((t:ℝ)+1)*((t:ℝ)+1+1)/(N:ℝ) =
            16*(t:ℝ)*((t:ℝ)+1)/(N:ℝ) + 32*((t:ℝ)+1)/(N:ℝ) := by ring
        rw [heq]; linarith
    have hleft (t : ℕ) (ht : t ≤ m) (htlo : (N:ℝ)/8 ≤ ((m-t:ℕ):ℝ)) :
        S (m-t) ≤ 16*(t:ℝ)*((t:ℝ)+1)/(N:ℝ) := by
      induction t with
      | zero => simp [hSm]
      | succ t ih =>
        have hi := ih (by omega) (by
          rw [Nat.cast_sub (by omega : t ≤ m)]
          rw [Nat.cast_sub ht] at htlo
          push_cast at htlo
          linarith)
        let i := m-(t+1)
        have hin : i < N := by dsimp [i]; omega
        have hie : i+1=m-t := by dsimp [i]; omega
        have hic : (i:ℝ) = (m:ℝ)-(t:ℝ)-1 := by
          dsimp [i]; rw [Nat.cast_sub ht]; push_cast; ring
        have hA : 0 < ((N:ℝ)-i)*p := mul_pos (sub_pos.mpr (by exact_mod_cast hin)) hp0
        have hB : 0 < ((i:ℝ)+1)*(1-p) := by positivity
        have hBN : (N:ℝ)/32 ≤ ((i:ℝ)+1)*(1-p) := by
          have hilo : (N:ℝ)/8 ≤ i := htlo
          have hh := mul_nonneg (show 0 ≤ (i:ℝ)+1 by positivity)
            (show 0 ≤ 1-p-1/4 by linarith [hp.2])
          nlinarith
        have hgap : ((N:ℝ)-i)*p-((i:ℝ)+1)*(1-p) ≤ (t:ℝ)+1 := by
          rw [hic]; nlinarith
        have hh := hscalar _ _ ((t:ℝ)+1) hA hB hBN (by positivity) hgap
        have hl := hlogstep i hin
        rw [log_div hB.ne' hA.ne'] at hl
        rw [log_div hA.ne' hB.ne'] at hh
        rw [hie] at hl
        have heq : 16*((t:ℝ)+1)*((t:ℝ)+1+1)/(N:ℝ) =
            16*(t:ℝ)*((t:ℝ)+1)/(N:ℝ) + 32*((t:ℝ)+1)/(N:ℝ) := by ring
        push_cast
        change S i ≤ 16*((t:ℝ)+1)*((t:ℝ)+1+1)/(N:ℝ)
        rw [heq]; linarith
    intro n hn hnlo hnhi
    by_cases hmn : m ≤ n
    · have hh := hright (n-m) (by omega) (by simpa [Nat.add_sub_of_le hmn] using hnhi)
      rw [Nat.add_sub_of_le hmn, Nat.cast_sub hmn] at hh
      rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmn))]
      exact hh
    · have hnm : n ≤ m := by omega
      have hh := hleft (m-n) (by omega) (by simpa [Nat.sub_sub_self hnm] using hnlo)
      rw [Nat.sub_sub_self hnm, Nat.cast_sub hnm] at hh
      rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hnm))]
      convert hh using 1; ring
  have henvelope (hN1 : 1 ≤ N) : ∀ n : ℕ, n ≤ N →
      let z : ℝ := ((n:ℝ)-(N:ℝ)*p)/sqrt ((N:ℝ)*p*(1-p))
      (3/128:ℝ)*z^2-1/2 ≤ S n ∧ S n ≤ 32*(1+z^2) := by
    intro n hn z
    have hN0 : (0:ℝ) < N := by exact_mod_cast hN1
    have hN1R : (1:ℝ) ≤ N := by exact_mod_cast hN1
    let t : ℝ := |(n:ℝ)-(m:ℝ)|
    let d : ℝ := |(n:ℝ)-(N:ℝ)*p|
    let v : ℝ := (N:ℝ)*p*(1-p)
    have hv0 : 0 < v := by dsimp [v]; positivity
    have hvlo : (3/16:ℝ)*(N:ℝ) ≤ v := by dsimp [v]; nlinarith [hpvar.1]
    have hvhi : v ≤ (N:ℝ)/4 := by dsimp [v]; nlinarith [hpvar.2]
    have hz : z^2*v = d^2 := by
      dsimp [z, d, v]
      rw [div_pow, sq_sqrt (by positivity), sq_abs]
      field_simp
    have hd0 : 0 ≤ d := abs_nonneg _
    have ht0 : 0 ≤ t := abs_nonneg _
    have hdt : d ≤ t+1 := by
      have h := abs_add_le ((n:ℝ)-(m:ℝ)) ((m:ℝ)-(N:ℝ)*p)
      have he : (n:ℝ)-(m:ℝ)+((m:ℝ)-(N:ℝ)*p) = (n:ℝ)-(N:ℝ)*p := by ring
      rw [he] at h
      exact h.trans (by dsimp [t]; linarith)
    have htd : t ≤ d+1 := by
      have h := abs_add_le ((n:ℝ)-(N:ℝ)*p) ((N:ℝ)*p-(m:ℝ))
      have he : (n:ℝ)-(N:ℝ)*p+((N:ℝ)*p-(m:ℝ)) = (n:ℝ)-(m:ℝ) := by ring
      rw [he, abs_sub_comm ((N:ℝ)*p) (m:ℝ)] at h
      exact h.trans (by dsimp [d]; linarith)
    constructor
    · have hlow := (div_le_iff₀ (by positivity : 0 < 2*(N:ℝ))).mp (hN hN1 n hn)
      change t*(t-1) ≤ S n*(2*(N:ℝ)) at hlow
      have hd2 : d^2 ≤ 2*t^2+2 := by nlinarith [sq_nonneg (t-1)]
      have hvz := mul_nonneg (sub_nonneg.mpr hvlo) (sq_nonneg z)
      have hNextra := mul_nonneg (show 0 ≤ (N:ℝ)-1 by linarith) (by norm_num : (0:ℝ) ≤ 1/2)
      have hscaled : (N:ℝ)*((3/128:ℝ)*z^2-1/2) ≤ (N:ℝ)*S n := by
        nlinarith [sq_nonneg (t-1)]
      exact (mul_le_mul_iff_right₀ hN0).mp hscaled
    · by_cases hN8 : 8 ≤ N
      · by_cases hc : (N:ℝ)/8 ≤ n ∧ (n:ℝ) ≤ 7*(N:ℝ)/8
        · have hupper := (le_div_iff₀ hN0).mp (hcentral hN8 n hn hc.1 hc.2)
          change S n*(N:ℝ) ≤ 16*t*(t+1) at hupper
          have htbound : t*(t+1) ≤ 4*d^2+5 := by nlinarith [sq_nonneg (d-1/2)]
          have hvz := mul_nonneg (sub_nonneg.mpr hvhi) (sq_nonneg z)
          have hN8R : (8:ℝ) ≤ N := by exact_mod_cast hN8
          have hs : (N:ℝ)*S n ≤ (N:ℝ)*(32*(1+z^2)) := by nlinarith [sq_nonneg z]
          exact (mul_le_mul_iff_right₀ hN0).mp hs
        · have hdlo : (N:ℝ)/8 ≤ d := by
            dsimp [d]
            rw [abs_le] at hmd
            by_cases hnlo : (n:ℝ) < (N:ℝ)/8
            · rw [abs_of_nonpos (by nlinarith [hp.1])]; nlinarith [hp.1]
            · have hnhi : 7*(N:ℝ)/8 < n := by
                push Not at hc
                exact hc (by linarith)
              rw [abs_of_nonneg (by nlinarith [hp.2])]; nlinarith [hp.2]
          have hvz := mul_nonneg (sub_nonneg.mpr hvhi) (sq_nonneg z)
          have hzlo : (N:ℝ)/16 ≤ z^2 := by nlinarith
          nlinarith [hglobal n hn, sq_nonneg z]
      · have hN7 : (N:ℝ) ≤ 7 := by exact_mod_cast (show N ≤ 7 by omega)
        nlinarith [hglobal n hn, sq_nonneg z]
  let Z : ℝ → ℝ := fun β => ∑ n : Fin (N+1), exp (-β*S n.val)
  have hshell (hN1 : 1 ≤ N) :
      Z (1/2) ≤ (4*exp (1/8)/(1-exp (-(1/8)))) * sqrt ((N:ℝ)+1) := by
    have hN0 : (0:ℝ) < N := by exact_mod_cast hN1
    have hN1R : (1:ℝ) ≤ N := by exact_mod_cast hN1
    let L : ℕ := ⌈sqrt (N:ℝ)⌉₊
    have hsqrt1 : (1:ℝ) ≤ sqrt (N:ℝ) := by
      exact (le_sqrt (by norm_num) (by positivity)).2 (by simpa using hN1R)
    have hLlo : sqrt (N:ℝ) ≤ (L:ℝ) := Nat.le_ceil _
    have hL1 : 1 ≤ L := by exact_mod_cast hsqrt1.trans hLlo
    have hL0 : 0 < L := by omega
    have hLhi : (L:ℝ) ≤ 2*sqrt (N:ℝ) := by
      have hh := Nat.ceil_lt_add_one (sqrt_nonneg (N:ℝ))
      change (L:ℝ) < sqrt (N:ℝ)+1 at hh
      linarith
    have hLsq : (N:ℝ) ≤ (L:ℝ)^2 := by
      nlinarith [sq_sqrt (Nat.cast_nonneg N : (0:ℝ) ≤ N), sqrt_nonneg (N:ℝ)]
    let T : Fin (N+1) → ℕ := fun n => (n.val-m)+(m-n.val)
    have hT (n : Fin (N+1)) : (T n:ℝ) = |(n.val:ℝ)-(m:ℝ)| := by
      dsimp [T]
      by_cases hm : m ≤ n.val
      · rw [Nat.sub_eq_zero_of_le hm, Nat.cast_add, Nat.cast_sub hm, Nat.cast_zero, add_zero,
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hm))]
      · have hn : n.val ≤ m := by omega
        rw [Nat.sub_eq_zero_of_le hn, Nat.cast_add, Nat.cast_sub hn, Nat.cast_zero, zero_add,
          abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hn))]
        ring
    have hTN (n : Fin (N+1)) : T n ≤ N := by dsimp [T]; have := n.isLt; omega
    let R : ℕ := N/L
    let shell : ℕ → Finset (Fin (N+1)) := fun r => univ.filter (fun n => T n/L=r)
    have hcard (r : ℕ) : (shell r).card ≤ 2*L := by
      let f : Fin (N+1) → ℕ := fun n => if m ≤ n.val then T n % L else L + T n % L
      have hmaps : Set.MapsTo f (shell r) (range (2*L)) := by
        intro n hn
        have ht : T n % L < L := Nat.mod_lt _ hL0
        simp only [Finset.mem_coe, mem_range]
        dsimp [f]; split_ifs <;> omega
      have hinj : Set.InjOn f (shell r) := by
        intro a ha b hb hab
        have haR : T a / L = r := (mem_filter.mp ha).2
        have hbR : T b / L = r := (mem_filter.mp hb).2
        have haM := Nat.mod_lt (T a) hL0
        have hbM := Nat.mod_lt (T b) hL0
        have haD := Nat.mod_add_div (T a) L
        have hbD := Nat.mod_add_div (T b) L
        rw [haR] at haD
        rw [hbR] at hbD
        dsimp [f] at hab
        apply Fin.ext
        by_cases haSide : m ≤ a.val
        · by_cases hbSide : m ≤ b.val
          · simp only [if_pos haSide, if_pos hbSide] at hab
            have htd : T a = T b := by omega
            dsimp [T] at htd
            omega
          · simp only [if_pos haSide, if_neg hbSide] at hab
            omega
        · by_cases hbSide : m ≤ b.val
          · simp only [if_neg haSide, if_pos hbSide] at hab
            omega
          · simp only [if_neg haSide, if_neg hbSide] at hab
            have htd : T a = T b := by omega
            dsimp [T] at htd
            omega
      have hh := card_le_card_of_injOn f hmaps hinj
      simpa only [card_range] using hh
    let ρ : ℝ := exp (-(1/8))
    have hρ0 : 0 < ρ := exp_pos _
    have hρ1 : ρ < 1 := by dsimp [ρ]; exact exp_lt_one_iff.mpr (by norm_num)
    have hden : 0 < 1-ρ := by linarith
    have hweight (r : ℕ) (n : Fin (N+1)) (hn : n ∈ shell r) :
        exp (-(1/2)*S n.val) ≤ exp (1/8)*ρ^r := by
      have hr : T n/L=r := (mem_filter.mp hn).2
      have hdist : r*L ≤ T n := by rw [← hr]; exact Nat.div_mul_le_self _ _
      have hdistR : (r:ℝ)*(L:ℝ) ≤ (T n:ℝ) := by exact_mod_cast hdist
      have hd2 : (r:ℝ)^2*(N:ℝ) ≤ (T n:ℝ)^2 := by
        have hl2 := mul_le_mul_of_nonneg_left hLsq (sq_nonneg (r:ℝ))
        have hsq : ((r:ℝ)*(L:ℝ))^2 ≤ (T n:ℝ)^2 := by
          exact pow_le_pow_left₀ (by positivity) hdistR 2
        nlinarith
      have hr2 : (r:ℝ) ≤ (r:ℝ)^2 := by
        simpa only [pow_two] using
          (show (r:ℝ) ≤ (r:ℝ)*(r:ℝ) by exact_mod_cast Nat.le_mul_self r)
      have hl := (div_le_iff₀ (by positivity : 0 < 2*(N:ℝ))).mp (hN hN1 n.val (by omega))
      rw [← hT n] at hl
      have hexp : -(1/2)*S n.val ≤ 1/8-(r:ℝ)/8 := by
        have hh : (N:ℝ)*(-(1/2)*S n.val) ≤ (N:ℝ)*(1/8-(r:ℝ)/8) := by
          nlinarith [sq_nonneg ((T n:ℝ)-1), mul_nonneg (sub_nonneg.mpr hr2) hN0.le]
        exact (mul_le_mul_iff_right₀ hN0).mp hh
      calc
        exp (-(1/2)*S n.val) ≤ exp (1/8-(r:ℝ)/8) := exp_le_exp.mpr hexp
        _ = exp (1/8)*ρ^r := by
          rw [show (1/8:ℝ)-(r:ℝ)/8 = 1/8+(r:ℝ)*(-(1/8)) by ring, exp_add, exp_nat_mul]
    have hmaps : ∀ n ∈ (univ : Finset (Fin (N+1))), T n/L ∈ range (R+1) := by
      intro n _
      apply mem_range.mpr
      have hh : T n/L ≤ N/L := Nat.div_le_div_right (hTN n)
      change T n/L ≤ R at hh
      omega
    have hgeo : ∑ r ∈ range (R+1), ρ^r ≤ 1/(1-ρ) := by
      rw [geom_sum_eq (ne_of_lt hρ1)]
      have he : (ρ^(R+1)-1)/(ρ-1) = (1-ρ^(R+1))/(1-ρ) := by
        field_simp [hden.ne', sub_ne_zero.mpr (ne_of_lt hρ1)]; ring
      rw [he]
      exact (div_le_div_iff_of_pos_right hden).mpr (by nlinarith [pow_nonneg hρ0.le (R+1)])
    calc
      Z (1/2) = ∑ r ∈ range (R+1), ∑ n ∈ shell r, exp (-(1/2)*S n.val) :=
        (sum_fiberwise_of_maps_to hmaps _).symm
      _ ≤ ∑ r ∈ range (R+1), (2*(L:ℝ))*(exp (1/8)*ρ^r) := by
        apply sum_le_sum
        intro r hr
        calc
          (∑ n ∈ shell r, exp (-(1/2)*S n.val)) ≤ (shell r).card • (exp (1/8)*ρ^r) :=
            sum_le_card_nsmul _ _ _ (fun n hn => hweight r n hn)
          _ ≤ (2*(L:ℝ))*(exp (1/8)*ρ^r) := by
            rw [nsmul_eq_mul]
            apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard r)
            positivity
      _ = 2*(L:ℝ)*exp (1/8)*(∑ r ∈ range (R+1), ρ^r) := by rw [mul_sum]; congr 1; ext r; ring
      _ ≤ 2*(L:ℝ)*exp (1/8)*(1/(1-ρ)) := by gcongr
      _ ≤ (4*exp (1/8)/(1-ρ))*sqrt (N:ℝ) := by
        have hh := mul_le_mul_of_nonneg_right hLhi (exp_pos (1/8)).le
        rw [mul_one_div, div_mul_eq_mul_div]
        apply (div_le_div_iff_of_pos_right hden).mpr
        nlinarith
      _ ≤ (4*exp (1/8)/(1-ρ))*sqrt ((N:ℝ)+1) := by gcongr; norm_num
  have hplateau (hN1 : 1 ≤ N) (α : ℝ) (hα : α ∈ Set.Icc (1:ℝ) 2) :
      (exp (-768)/2)*sqrt ((N:ℝ)+1) ≤ Z α := by
    have hN0 : (0:ℝ) < N := by exact_mod_cast hN1
    have hN1R : (1:ℝ) ≤ N := by exact_mod_cast hN1
    let B : ℝ := sqrt ((N:ℝ)+1)
    let ell : ℕ := ⌊B⌋₊
    have hB1 : 1 ≤ B := by
      dsimp [B]
      exact (le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
    have hell1 : 1 ≤ ell := by
      have hh : 0 < ell := Nat.floor_pos.mpr hB1
      omega
    have hellB : (ell:ℝ) ≤ B := Nat.floor_le (by linarith)
    have hBlt : B < (ell:ℝ)+1 := Nat.lt_floor_add_one _
    have hellR : (1:ℝ) ≤ ell := by exact_mod_cast hell1
    have hellhalf : B/2 ≤ ell := by linarith
    have hBN : B ≤ (N:ℝ)+1 := by
      dsimp [B]
      apply (sqrt_le_left (by positivity)).2
      nlinarith
    have hellN : ell ≤ N+1 := by
      exact_mod_cast hellB.trans hBN
    let a : ℕ := min m (N+1-ell)
    let P : Finset ℕ := Ico a (a+ell)
    have haN : a+ell ≤ N+1 := by dsimp [a]; omega
    have ham : a ≤ m := min_le_left _ _
    have hma : m < a+ell := by dsimp [a]; omega
    have hPsub : P ⊆ range (N+1) := by
      intro n hn
      have hh := mem_Ico.mp hn
      exact mem_range.mpr (by omega)
    have hPS (n : ℕ) (hn : n ∈ P) : S n ≤ 384 := by
      have hnP := mem_Ico.mp hn
      have hnN : n ≤ N := by omega
      have ht : |(n:ℝ)-(m:ℝ)| ≤ (ell:ℝ)-1 := by
        apply abs_le.mpr
        have han : (a:ℝ) ≤ n := by exact_mod_cast hnP.1
        have hna : (n:ℝ)+1 ≤ (a:ℝ)+ell := by exact_mod_cast hnP.2
        have hamR : (a:ℝ) ≤ m := by exact_mod_cast ham
        have hmaR : (m:ℝ)+1 ≤ (a:ℝ)+ell := by exact_mod_cast hma
        constructor <;> linarith
      have hd : |(n:ℝ)-(N:ℝ)*p| ≤ (ell:ℝ) := by
        have hh := abs_add_le ((n:ℝ)-(m:ℝ)) ((m:ℝ)-(N:ℝ)*p)
        have he : (n:ℝ)-(m:ℝ)+((m:ℝ)-(N:ℝ)*p) = (n:ℝ)-(N:ℝ)*p := by ring
        rw [he] at hh
        linarith
      let z : ℝ := ((n:ℝ)-(N:ℝ)*p)/sqrt ((N:ℝ)*p*(1-p))
      have hz : z^2*((N:ℝ)*p*(1-p)) = |(n:ℝ)-(N:ℝ)*p|^2 := by
        dsimp [z]
        rw [div_pow, sq_sqrt (by positivity), sq_abs]
        field_simp
      have hvlo : (3/16:ℝ)*(N:ℝ) ≤ (N:ℝ)*p*(1-p) := by nlinarith [hpvar.1]
      have hBsq : B^2 = (N:ℝ)+1 := sq_sqrt (by positivity)
      have hd2 : |(n:ℝ)-(N:ℝ)*p|^2 ≤ (N:ℝ)+1 := by
        nlinarith [abs_nonneg ((n:ℝ)-(N:ℝ)*p), show 0 ≤ B by linarith]
      have hz2 : z^2 ≤ 32/3 := by
        have hh := mul_nonneg (sub_nonneg.mpr hvlo) (sq_nonneg z)
        have hscaled : (N:ℝ)*z^2 ≤ (N:ℝ)*(32/3) := by nlinarith
        exact (mul_le_mul_iff_right₀ hN0).mp hscaled
      have hh := (henvelope hN1 n hnN).2
      change S n ≤ 32*(1+z^2) at hh
      linarith
    have hw (n : ℕ) (hn : n ∈ P) : exp (-768) ≤ exp (-α*S n) := by
      apply exp_le_exp.mpr
      have hs := hS0 n (by have := mem_range.mp (hPsub hn); omega)
      have hu := hPS n hn
      nlinarith [hα.1, hα.2]
    calc
      (exp (-768)/2)*sqrt ((N:ℝ)+1) ≤ (ell:ℝ)*exp (-768) := by
        dsimp [B] at hellhalf
        nlinarith [exp_pos (-768)]
      _ = ∑ n ∈ P, exp (-768) := by simp [P, mul_comm]
      _ ≤ ∑ n ∈ P, exp (-α*S n) := sum_le_sum hw
      _ ≤ ∑ n ∈ range (N+1), exp (-α*S n) :=
        sum_le_sum_of_subset_of_nonneg hPsub (fun n _ _ => (exp_pos _).le)
      _ = Z α := (Fin.sum_univ_eq_sum_range (fun n => exp (-α*S n)) (N+1)).symm
  have hZpos (β : ℝ) : 0 < Z β := by
    apply sum_pos
    · intro n _; exact exp_pos _
    · exact univ_nonempty
  have hZmono (β : ℝ) (hβ : 1/2 ≤ β) : Z β ≤ Z (1/2) := by
    apply sum_le_sum
    intro n _
    apply exp_le_exp.mpr
    nlinarith [hS0 n.val (by omega)]
  have hzero (hN0 : N=0) :
      (∀ n : Fin (N+1), n.val=0 ∧ q n=1 ∧ S n.val=0) ∧ M=1 ∧
      (∀ β : ℝ, Z β=1) := by
    have hn0 (n : Fin (N+1)) : n.val=0 := by have := n.isLt; omega
    have hq0 (n : Fin (N+1)) : q n=1 := by simp [q, Q, binomialMass, hN0, hn0 n]
    have hMz : M=1 := by
      apply le_antisymm hM1
      have hh := hqM ⟨0, by omega⟩
      rwa [hq0] at hh
    have hSz (n : Fin (N+1)) : S n.val=0 := by
      dsimp [S]; change log M - log (q n) = 0
      rw [hMz, hq0, log_one, sub_self]
    refine ⟨fun n => ⟨hn0 n, hq0 n, hSz n⟩, hMz, ?_⟩
    intro β
    dsimp [Z]
    simp only [hSz, mul_zero, exp_zero]
    simp [hN0]
  have hpoly (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
      x^k*exp (-x/2) ≤ (2*((k:ℝ)+1))^k := by
    by_cases hk : k=0
    · subst k
      simpa using (exp_le_one_iff.mpr (show -x/2 ≤ 0 by linarith))
    have hk0 : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    let y : ℝ := x/(2*(k:ℝ))
    have hy0 : 0 ≤ y := by dsimp [y]; positivity
    have hyexp : y ≤ exp y := by linarith [add_one_le_exp y]
    have hye : y*exp (-y) ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_right hyexp (exp_pos (-y)).le
      rw [← exp_add, add_neg_cancel, exp_zero] at hh
      exact hh
    have he : x^k*exp (-x/2) = (2*(k:ℝ))^k*(y*exp (-y))^k := by
      have hxy : 2*(k:ℝ)*y=x := by dsimp [y]; field_simp
      have hek : exp (-y)^k = exp (-x/2) := by
        rw [← exp_nat_mul]
        congr 1
        dsimp [y]
        field_simp
      calc
        x^k*exp (-x/2) = (2*(k:ℝ)*y)^k*exp (-y)^k := by rw [hxy, hek]
        _ = (2*(k:ℝ))^k*(y*exp (-y))^k := by simp only [mul_pow]; ring
    calc
      x^k*exp (-x/2) = (2*(k:ℝ))^k*(y*exp (-y))^k := he
      _ ≤ (2*(k:ℝ))^k*1 := by
        gcongr
        simpa using pow_le_pow_left₀ (mul_nonneg hy0 (exp_pos _).le) hye k
      _ ≤ (2*((k:ℝ)+1))^k := by rw [mul_one]; gcongr; linarith
  have hpolyα (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (α : ℝ) (hα : 1 ≤ α) :
      x^k*exp (-α*x) ≤ (2*((k:ℝ)+1))^k*exp (-(1/2)*x) := by
    calc
      x^k*exp (-α*x) = (x^k*exp (-x/2))*exp (-(α-1/2)*x) := by
        rw [mul_assoc, ← exp_add]
        congr 1
        congr 1
        ring
      _ ≤ (2*((k:ℝ)+1))^k*exp (-(α-1/2)*x) := by
        exact mul_le_mul_of_nonneg_right (hpoly x hx k) (exp_pos _).le
      _ ≤ (2*((k:ℝ)+1))^k*exp (-(1/2)*x) := by gcongr; nlinarith
  have hZu : Z (1/2) ≤ U*sqrt ((N:ℝ)+1) := by
    by_cases hNz : N=0
    · rw [(hzero hNz).2.2, hNz]
      simpa using hU1
    · exact hshell (by omega)
  have hZl (α : ℝ) (hα : α ∈ Set.Icc (1:ℝ) 2) : D*sqrt ((N:ℝ)+1) ≤ Z α := by
    by_cases hNz : N=0
    · rw [(hzero hNz).2.2, hNz]
      simpa using hD1
    · exact hplateau (by omega) α hα
  let E : ℝ → ℕ → ℝ := fun β k => (∑ n : Fin (N+1), (S n.val)^k*exp (-β*S n.val))/Z β
  let w : ℝ → Fin (N+1) → ℝ := fun β n => exp (-β*S n.val)/Z β
  let μ : ℝ → ℝ := fun β => ∑ n, w β n*S n.val
  let V : ℝ → ℝ := fun β => ∑ n, w β n*(S n.val-μ β)^2
  let H : ℝ → ℝ := fun β => ∑ n, w β n*|S n.val-μ β|^4
  have hE0 (β : ℝ) : E β 0=1 := by
    dsimp [E]
    simp only [pow_zero, one_mul]
    exact div_self (hZpos β).ne'
  have hw0 (β : ℝ) (n : Fin (N+1)) : 0 ≤ w β n := (div_pos (exp_pos _) (hZpos β)).le
  have hw1 (β : ℝ) : ∑ n, w β n=1 := by dsimp [w]; rw [← sum_div]; exact div_self (hZpos β).ne'
  have hEw (β : ℝ) (k : ℕ) : E β k = ∑ n, w β n*(S n.val)^k := by
    dsimp [E, w]
    rw [sum_div]
    apply sum_congr rfl
    intro n _
    ring
  have hEk (α : ℝ) (hα : α ∈ Set.Icc (1:ℝ) 2) (k : ℕ) : 0 ≤ E α k ∧ E α k ≤ K k := by
    have hnum0 : 0 ≤ ∑ n : Fin (N+1), (S n.val)^k*exp (-α*S n.val) :=
      sum_nonneg (fun n _ => mul_nonneg (pow_nonneg (hS0 n.val (by omega)) _) (exp_pos _).le)
    refine ⟨div_nonneg hnum0 (hZpos α).le, ?_⟩
    have hnumb : (∑ n : Fin (N+1), (S n.val)^k*exp (-α*S n.val)) ≤ (2*((k:ℝ)+1))^k*Z (1/2) := by
      calc
        _ ≤ ∑ n : Fin (N+1), (2*((k:ℝ)+1))^k*exp (-(1/2)*S n.val) :=
          sum_le_sum (fun n _ => hpolyα (S n.val) (hS0 n.val (by omega)) k α hα.1)
        _ = _ := by rw [mul_sum]
    have hu := mul_le_mul_of_nonneg_left hZu (by positivity : 0 ≤ (2*((k:ℝ)+1))^k)
    have hl := mul_le_mul_of_nonneg_left (hZl α hα) (show 0 ≤ (U/D)*(2*((k:ℝ)+1))^k by positivity)
    have he : ((U/D)*(2*((k:ℝ)+1))^k)*(D*sqrt ((N:ℝ)+1)) =
        (2*((k:ℝ)+1))^k*(U*sqrt ((N:ℝ)+1)) := by field_simp
    rw [he] at hl
    exact (div_le_iff₀ (hZpos α)).2 ((hnumb.trans hu).trans hl)
  have hV (β : ℝ) : 0 ≤ V β ∧ V β ≤ E β 2 := by
    have hv0 : 0 ≤ V β := sum_nonneg (fun n _ => mul_nonneg (hw0 β n) (sq_nonneg _))
    have he : V β = E β 2-(μ β)^2 := by
      dsimp [V]
      simp_rw [show ∀ n : Fin (N+1), w β n*(S n.val-μ β)^2 =
          w β n*(S n.val)^2 - (2*μ β)*(w β n*S n.val) + (μ β)^2*w β n by intro n; ring]
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hw1 β, ← hEw β 2]
      change E β 2-2*μ β*μ β+(μ β)^2*1 = E β 2-(μ β)^2
      ring
    refine ⟨hv0, ?_⟩
    rw [he]
    nlinarith [sq_nonneg (μ β)]
  have hH (β : ℝ) : 0 ≤ H β ∧ H β ≤ 16*E β 4 := by
    have hh0 : 0 ≤ H β := sum_nonneg (fun n _ => mul_nonneg (hw0 β n) (pow_nonneg (abs_nonneg _) _))
    have hj : (μ β)^4 ≤ E β 4 := by
      have hh := (convexOn_pow (𝕜 := ℝ) 4).map_sum_le (t := univ)
        (fun n _ => hw0 β n) (hw1 β) (fun n _ => hS0 n.val (by omega))
      simpa only [smul_eq_mul, ← hEw β 4] using hh
    have hpoint (n : Fin (N+1)) : |S n.val-μ β|^4 ≤ 8*((S n.val)^4+(μ β)^4) := by
      rw [show |S n.val-μ β|^4 = (S n.val-μ β)^4 by exact (even_two.mul_left 2).pow_abs _]
      have hh := (show Even 4 by decide).add_pow_le (a := S n.val) (b := -μ β)
      norm_num at hh
      simpa only [sub_eq_add_neg] using hh
    have hbound : H β ≤ 8*(E β 4+(μ β)^4) := by
      calc
        H β ≤ ∑ n, w β n*(8*((S n.val)^4+(μ β)^4)) :=
          sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left (hpoint n) (hw0 β n))
        _ = 8*(E β 4+(μ β)^4) := by
          simp_rw [mul_add,
            show ∀ n : Fin (N+1), w β n*(8*(S n.val)^4) =
              8*(w β n*(S n.val)^4) by intro n; ring,
            show ∀ n : Fin (N+1), w β n*(8*(μ β)^4) = (8*(μ β)^4)*w β n by intro n; ring]
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, hw1 β, ← hEw β 4]
          ring
    exact ⟨hh0, by linarith⟩
  have hfinish :
      (∑ n, q n) = 1 ∧
      (∀ n, 0 < q n ∧ q n ≤ M ∧ 0 ≤ S n.val) ∧
      0 < M ∧ M ≤ 1 ∧
      (∀ β : ℝ, 0 < Z β ∧ E β 0 = 1 ∧ (∀ n, 0 ≤ w β n) ∧ (∑ n, w β n) = 1) ∧
      (1 ≤ N →
        m ≤ N ∧ M = binomialMass p N m ∧ |(m:ℝ)-(N:ℝ)*p| ≤ 1 ∧
        (((N:ℝ)+1)*p-(m:ℝ) = 0 → 1 ≤ m ∧ binomialMass p N (m-1) = M) ∧
        ∀ n : Fin (N+1),
          let t : ℝ := |(n.val:ℝ)-(m:ℝ)|
          let z : ℝ := ((n.val:ℝ)-(N:ℝ)*p)/sqrt ((N:ℝ)*p*(1-p))
          t*(t-1)/(2*(N:ℝ)) ≤ S n.val ∧
          (3/128 : ℝ)*z^2-1/2 ≤ S n.val ∧ S n.val ≤ 32*(1+z^2) ∧
          c*z^2-C ≤ S n.val ∧ S n.val ≤ C*(1+z^2)) ∧
      Z (1/2) ≤ U*sqrt ((N:ℝ)+1) ∧
      (∀ β : ℝ, 1/2 ≤ β → Z β ≤ Z (1/2)) ∧
      (∀ α : ℝ, α ∈ Set.Icc (1:ℝ) 2 →
        D*sqrt ((N:ℝ)+1) ≤ Z α ∧ Z α ≤ U*sqrt ((N:ℝ)+1) ∧
        c*sqrt ((N:ℝ)+1) ≤ Z α ∧ Z α ≤ C*sqrt ((N:ℝ)+1) ∧
        (∀ k : ℕ, 0 ≤ E α k ∧ E α k ≤ K k) ∧
        0 ≤ V α ∧ V α ≤ E α 2 ∧ E α 2 ≤ K 2 ∧
        0 ≤ H α ∧ H α ≤ 16*E α 4 ∧ 16*E α 4 ≤ 16*K 4) ∧
      (N = 0 →
        (∀ n, n.val = 0 ∧ q n = 1 ∧ S n.val = 0) ∧ M = 1 ∧
        ∀ β : ℝ, Z β = 1 ∧ ∀ k : ℕ, 1 ≤ k → E β k = 0) := by
    refine ⟨hsum, fun n => ⟨hQ n.val (by omega), hqM n, hS0 n.val (by omega)⟩,
      hM0, hM1, fun β => ⟨hZpos β, hE0 β, hw0 β, hw1 β⟩, ?_, hZu, hZmono, ?_, ?_⟩
    · intro hN1
      refine ⟨hmN, hMm, hmd, htie, ?_⟩
      intro n t z
      have hn : n.val ≤ N := by omega
      have he := henvelope hN1 n.val hn
      change (3/128:ℝ)*z^2-1/2 ≤ S n.val ∧ S n.val ≤ 32*(1+z^2) at he
      refine ⟨hN hN1 n.val hn, he.1, he.2, ?_, ?_⟩
      · have hc : c ≤ (3/128:ℝ) := min_le_left _ _
        have hC : (1/2:ℝ) ≤ C := by dsimp [C]; linarith
        have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg z)
        linarith
      · have hC : (32:ℝ) ≤ C := by dsimp [C]; linarith
        exact he.2.trans (mul_le_mul_of_nonneg_right hC (by positivity))
    · intro α hα
      have hu := (hZmono α (by linarith [hα.1])).trans hZu
      have hl := hZl α hα
      have hc : c ≤ D := min_le_right _ _
      have hC : U ≤ C := by dsimp [C]; linarith
      refine ⟨hl, hu, (mul_le_mul_of_nonneg_right hc (sqrt_nonneg _)).trans hl,
        hu.trans (mul_le_mul_of_nonneg_right hC (sqrt_nonneg _)), hEk α hα,
        (hV α).1, (hV α).2, (hEk α hα 2).2,
        (hH α).1, (hH α).2, ?_⟩
      exact mul_le_mul_of_nonneg_left (hEk α hα 4).2 (by norm_num)
    · intro hNz
      refine ⟨(hzero hNz).1, (hzero hNz).2.1, ?_⟩
      intro β
      refine ⟨(hzero hNz).2.2 β, ?_⟩
      intro k hk
      have hk0 : k ≠ 0 := by omega
      dsimp [E]
      have hsz (n : Fin (N+1)) : S n.val=0 := ((hzero hNz).1 n).2.2
      simp only [hsz, zero_pow hk0, zero_mul, sum_const_zero, zero_div]
  simpa only [E, w, μ, V, H, Z, hS] using hfinish

end D5.S3.AnalyticClosure.BinomialFiniteSurprise
