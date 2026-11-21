/- GID: D5/S3/CharacterSums/SplittingProgressionMangoldtSupply
   generality: I
   mirror-B: D5/B/S3/CharacterSums/SplittingProgressionMangoldtSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: In long splitting progressions the two clipped Mangoldt tests fail on a vanishing fraction of integer candidates, uniformly in the first denominator and the starting index. -/

import D5.S3.CharacterSums.DyadicMangoldtPrimeSupply
import D5.S3.CharacterSums.AffineJacobiCorrelation

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Finset Real Filter
open ArithmeticFunction hiding log
open D5.S3.CharacterSums.DyadicMangoldtPrimeSupply
open D5.S3.CharacterSums.AffineJacobiCorrelation

namespace D5.S3.CharacterSums.SplittingProgressionMangoldtSupply

/-- The diagonal and off-diagonal estimates apply to signed weights, in particular
after twisting the coefficients by the first selected prime. -/
private lemma signed_moment (P : Finset ℕ) (a : ℕ → ℝ) (K : ℕ → ℕ → ℝ) (L : ℕ)
    (diag : ∀ p ∈ P, (∑ i ∈ range L, K p i * K p i) ≤ L)
    (off : ∀ p ∈ P, ∀ r ∈ P, p ≠ r → |∑ i ∈ range L, K p i * K r i| ≤ (p:ℝ)*r) :
    (∑ i ∈ range L, (∑ p ∈ P, a p * K p i)^2) ≤
      L*(∑ p ∈ P, (a p)^2) + (∑ p ∈ P, (p:ℝ)*|a p|)^2 := by
  classical
  let C (p r : ℕ) := ∑ i ∈ range L, K p i * K r i
  have row (i : ℕ) :
      (∑ p ∈ P, a p * K p i)^2 =
        ∑ p ∈ P, ∑ r ∈ P, a p * a r * (K p i * K r i) := by
    simp only [sq,sum_mul,mul_sum]
    apply sum_congr rfl; intro p _
    apply sum_congr rfl; intro r _; ring
  have exchange :
      (∑ i ∈ range L, ∑ p ∈ P, ∑ r ∈ P, a p*a r*(K p i*K r i)) =
      ∑ p ∈ P, ∑ r ∈ P, a p*a r*C p r := by
    rw [sum_comm]; apply sum_congr rfl; intro p _
    rw [sum_comm]; apply sum_congr rfl; intro r _; simp [C,mul_sum]
  have term (p : ℕ) (hp : p ∈ P) (r : ℕ) (hr : r ∈ P) :
      a p*a r*C p r ≤ (if p=r then L*(a p)^2 else 0) + ((p:ℝ)*|a p|)*((r:ℝ)*|a r|) := by
    by_cases h : p=r
    · subst r; simp only [ite_true]
      have h := mul_le_mul_of_nonneg_left (diag p hp) (sq_nonneg (a p))
      change (a p)^2 * C p p ≤ _ at h
      nlinarith only [h,sq_nonneg ((p:ℝ)*|a p|)]
    · simp only [ite_eq_right h,zero_add]
      calc
        _ ≤ |a p*a r*C p r| := le_abs_self _
        _ = |a p| *|a r| *|C p r| := by rw [abs_mul,abs_mul]
        _ ≤ |a p| *|a r| *((p:ℝ)*r) := mul_le_mul_of_nonneg_left (off p hp r hr h) (by positivity)
        _ = _ := by ring
  rw [sum_congr rfl (fun i _ => row i),exchange]
  refine (sum_le_sum (fun p hp => sum_le_sum (fun r hr => term p hp r hr))).trans_eq ?_
  simp only [sum_add_distrib]
  congr 1
  · rw [mul_sum]; apply sum_congr rfl; intro p hp; simp [hp]
  · simp_rw [← mul_sum]; rw [← sum_mul,sq]


private theorem affine_prime_moment (b m A L : ℕ) (hb : b%4=3) (hm : 4 ∣ m)
    (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ m.Coprime p) :
    (∑ i ∈ range L, (∑ p ∈ P, a p * (jacobiSym (p:ℤ) (b+m*(A+i)):ℝ))^2) ≤
      L*(∑ p ∈ P, (a p)^2) + (∑ p ∈ P, (p:ℝ)*|a p|)^2 := by
  let K (p i : ℕ) := (jacobiSym (p:ℤ) (b+m*(A+i)):ℝ)
  have re (p r : ℕ) : (∑ i ∈ range L, K p i*K r i) = (corr b m p r A L:ℝ) := by
    unfold D5.S3.CharacterSums.AffineJacobiCorrelation.corr; push_cast; rfl
  apply signed_moment P a K L
  · intro p _
    rw [re]
    exact_mod_cast (affine_jacobi_correlation b m p p A L).1.2
  · intro p hp r hr hne
    obtain ⟨hp',hp2,hmp⟩ := hP p hp
    obtain ⟨hr',hr2,hmr⟩ := hP r hr
    have h := ((affine_jacobi_correlation b m p r A L).2
      hb hm hp' hr' hp2 hr2 hne hmp hmr).2
    have hpr : 0 < p*r := Nat.mul_pos hp'.pos hr'.pos
    have hrem : L % (p*r) ≤ p*r := (Nat.mod_lt _ hpr).le
    have hle : |corr b m p r A L| ≤ (p*r:ℕ) := h.trans (by exact_mod_cast hrem)
    rw [re]; exact_mod_cast hle

private theorem damped_signed_prime_bound {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : 1 ≤ N)
    (b m A L : ℕ) (hb : b%4 = 3) (hm : 4 ∣ m) (v : ℕ → ℝ) (hv : ∀ p, |v p| ≤ 1) :
    let P := (Icc 1 N).filter (fun p => Nat.Prime p ∧ p ≠ 2 ∧ m.Coprime p)
    let a := fun p : ℕ => log p * min 1 (x/p)
    (∑ i ∈ range L, (∑ p ∈ P, (a p*v p)*(jacobiSym (p:ℤ) (b+m*(A+i)):ℝ))^2) ≤
      L*((log N)^2*x*(1+log N)) + ((N:ℝ)^2*log N)^2 := by
  intro P a
  have hP (p : ℕ) (hp : p ∈ P) := (mem_filter.1 hp).2
  have ha (p : ℕ) (hp : p ∈ P) : 0 ≤ a p := by
    have h1 := (hP p hp).1.one_le
    exact mul_nonneg (log_nonneg (by exact_mod_cast h1))
      (le_min zero_le_one (div_nonneg hx p.cast_nonneg))
  have hcoeff (p : ℕ) (hp : p ∈ P) : |a p*v p| ≤ a p := by
    rw [abs_mul,abs_of_nonneg (ha p hp)]
    exact mul_le_of_le_one_right (ha p hp) (hv p)
  have bound := affine_prime_moment b m A L hb hm P (fun p => a p*v p) hP
  obtain ⟨hd,ho⟩ := coefficient_bounds x hx N hN P (filter_subset _ _)
  apply bound.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ L.cast_nonneg
    apply le_trans _ hd
    apply sum_le_sum
    intro p hp
    have h := (sq_le_sq₀ (abs_nonneg _) (ha p hp)).2 (hcoeff p hp)
    simpa only [sq_abs] using h
  · have hle : (∑ p ∈ P, (p:ℝ)*|a p*v p|) ≤ (N:ℝ)^2*log N := by
      apply le_trans _ ho
      exact sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hcoeff p hp) p.cast_nonneg)
    apply (sq_le_sq₀ _ _).2 hle
    · exact sum_nonneg (fun p _ => mul_nonneg p.cast_nonneg (abs_nonneg _))
    · exact mul_nonneg (sq_nonneg _) (log_nonneg (by exact_mod_cast hN))

/-- Uniform discarded mass for any bounded real multiplier and any modulus whose
prime factors up to the cutoff are at most the real threshold y. -/
theorem clipped_coprime_prime_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x y : ℝ) (N m d : ℕ) (v : ℕ → ℝ), 0 < x →
      (∀ n, |v n| ≤ 1) → (∀ p : ℕ, p.Prime → p ∣ m → (p:ℝ) ≤ y ∨ N < p) →
      |(∑ n ∈ Finset.Icc 1 N, vonMangoldt n * min 1 (x/n) * v n * (jacobiSym (n:ℤ) d : ℝ)) -
        ∑ p ∈ (Finset.Icc 1 N).filter (fun p => p.Prime ∧ p ≠ 2 ∧ p.Coprime m),
          Real.log p * min 1 (x/p) * v p * (jacobiSym (p:ℤ) d : ℝ)| ≤
          K*Real.sqrt x+Real.log 2+Chebyshev.theta y := by
  classical
  obtain ⟨K,hK,hpow⟩ := clipped_prime_powers
  refine ⟨K,hK,?_⟩
  intro x y N m d v hx hv hfactor
  let S := Finset.Icc 1 N
  let c := fun n : ℕ => vonMangoldt n * min 1 (x/n)
  let f := fun n : ℕ => c n * v n * (jacobiSym (n:ℤ) d : ℝ)
  have hc (n : ℕ) : 0 ≤ c n := mul_nonneg vonMangoldt_nonneg
    (le_min zero_le_one (div_nonneg hx.le (Nat.cast_nonneg n)))
  have hf (n : ℕ) : |f n| ≤ c n := by
    dsimp only [f]; rw [abs_mul,abs_mul,abs_of_nonneg (hc n)]
    have hχ : |(jacobiSym (n:ℤ) d : ℝ)| ≤ 1 := by
      rcases jacobiSym.trichotomy (n:ℤ) d with h|h|h <;> rw [h] <;> norm_num
    exact (mul_le_of_le_one_right (mul_nonneg (hc n) (abs_nonneg _)) hχ).trans
      (mul_le_of_le_one_right (hc n) (hv n))
  have hprime (p : ℕ) (hp : p.Prime) : c p ≤ Real.log p := by
    dsimp [c]; rw [vonMangoldt_apply_prime hp]
    exact mul_le_of_le_one_right (Real.log_nonneg (by exact_mod_cast hp.one_le)) (min_le_left _ _)
  let P := S.filter (fun p => p.Prime ∧ p ≠ 2 ∧ p.Coprime m)
  let B := S.filter (fun p => p.Prime ∧ p ≠ 2 ∧ ¬p.Coprime m)
  have eqp : ∑ p ∈ P, f p = ∑ p ∈ P, Real.log p*min 1 (x/p)*v p*(jacobiSym (p:ℤ) d:ℝ) := by
    apply Finset.sum_congr rfl
    intro p hp; simp [f,c,vonMangoldt_apply_prime (Finset.mem_filter.1 hp).2.1]
  have splitSum : (∑ n ∈ S, f n) - ∑ p ∈ P, f p =
      ((∑ n ∈ S.filter (fun n => ¬n.Prime), f n) + ∑ n ∈ S.filter (fun n => n=2), f n) +
      ∑ p ∈ B, f p := by
    dsimp only [P,B]
    simp only [Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases ht : n=2
    · subst n; simp [Nat.prime_two]
    · by_cases hp : n.Prime <;> by_cases hm : n.Coprime m <;> simp_all
      rw [ite_eq_left hm, sub_self]
  change |(∑ n ∈ S, f n) - ∑ p ∈ P, _| ≤ _
  rw [← eqp,splitSum]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · have hS : S = Ioc 0 N := by ext n; simp [S,Nat.lt_iff_add_one_le]
    rw [hS]; exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (fun n _ => hf n)).trans (hpow x hx N))
  · rw [Finset.sum_filter]; by_cases h2 : 2 ∈ S
    · simpa [h2] using (hf 2).trans (hprime 2 Nat.prime_two)
    · simp [h2,Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]
  · rw [Chebyshev.theta_eq_sum_Icc]
    have hsub : B ⊆ (Finset.Icc 0 ⌊y⌋₊).filter Nat.Prime := by
      intro p hp
      obtain ⟨hs,hp,_,hm⟩ := Finset.mem_filter.1 hp
      have hd : p ∣ m := by simpa [hp.coprime_iff_not_dvd] using hm
      have hpy : (p:ℝ) ≤ y := (hfactor p hp hd).resolve_right (not_lt.mpr (Finset.mem_Icc.1 hs).2)
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega,Nat.le_floor hpy⟩,hp⟩
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum (fun p hp => (hf p).trans (hprime p (Finset.mem_filter.1 hp).2.1))).trans
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
      Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.1 hp).2.one_le))

/-- A clipped quadratic Mangoldt sum with an extra bounded multiplier on the original index. -/
def twistedBy (x : ℝ) (N d : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, vonMangoldt n * min 1 (x/n) * v n * (jacobiSym (n:ℤ) d:ℝ)

/-- At any starting index the same second-moment bound holds for every bounded multiplier. -/
private theorem progression_moment {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ b m A L : ℕ, b%4=3 → 4 ∣ m →
      (∀ p : ℕ, p.Prime → p ∣ m → (p:ℝ) ≤ x^(ε/5) ∨ cutoff x < p) →
      exp (x^(ε/5)/2) ≤ 2*(L:ℝ) → ∀ v : ℕ → ℝ, (∀ n, |v n| ≤ 1) →
      (∑ i ∈ range L, (twistedBy x (cutoff x) (b+m*(A+i)) v)^2) ≤ L*x*x^ε := by
  obtain ⟨K,hK,herr⟩ := clipped_coprime_prime_error
  let C := K + log 2 + log 4
  have h2 : 0 ≤ log 2 := log_nonneg (by norm_num)
  have h4 : 0 ≤ log 4 := log_nonneg (by norm_num)
  have hC : 0 ≤ C := add_nonneg (add_nonneg hK h2) h4
  filter_upwards [window_moment_scale (show 0 < ε/2 by linarith) (2*C^2)] with x hscale
  obtain ⟨hx,hN,hscale⟩ := hscale
  intro b m A L hb hm hfac hL v hv
  let N := cutoff x
  let d (i : ℕ) := b+m*(A+i)
  let P := (Icc 1 N).filter (fun p => Nat.Prime p ∧ p ≠ 2 ∧ m.Coprime p)
  let g (i : ℕ) : ℝ := ∑ p ∈ P, (log p*min 1 (x/p)*v p)*(jacobiSym (p:ℤ) (d i):ℝ)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  let E := x^(1/2+ε/4)
  have hroot : sqrt x ≤ E := by
    rw [sqrt_eq_rpow]; exact rpow_le_rpow_of_exponent_le hx (by linarith)
  have hy : x^(ε/5) ≤ E := rpow_le_rpow_of_exponent_le hx (by linarith)
  have hE : 1 ≤ E := one_le_rpow hx (by linarith)
  have htheta : Chebyshev.theta (x^(ε/5)) ≤ log 4 * E :=
    (Chebyshev.theta_le_log4_mul_x (rpow_nonneg hx0.le _)).trans
      (mul_le_mul_of_nonneg_left hy h4)
  have error (i : ℕ) : |twistedBy x N (d i) v - g i| ≤ C*E := by
    have h := herr x (x^(ε/5)) N m (d i) v hx0 hv hfac
    have heq : (Icc 1 N).filter (fun p => Nat.Prime p ∧ p ≠ 2 ∧ p.Coprime m) = P := by
      ext p; simp [P,Nat.coprime_comm]
    rw [heq] at h
    change |twistedBy x N (d i) v - g i| ≤ _ at h
    apply h.trans
    dsimp only [C]
    linarith only [htheta,mul_le_mul_of_nonneg_left hroot hK,mul_le_mul_of_nonneg_left hE h2]
  have hEsq : E^2 = x*x^(ε/2) := by
    dsimp only [E]
    rw [← rpow_mul_natCast hx0.le,show (1/2+ε/4)*(2:ℕ) = 1+ε/2 by push_cast; ring,rpow_add hx0,rpow_one]
  have oneRow (i : ℕ) :
      (twistedBy x N (d i) v)^2 ≤ 2*(g i)^2 + 2*C^2*(x*x^(ε/2)) := by
    have he := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (zero_le_one.trans hE))).2 (error i)
    rw [sq_abs,mul_pow,hEsq] at he
    nlinarith only [he,sq_nonneg (twistedBy x N (d i) v-2*g i)]
  have hp := damped_signed_prime_bound hx0.le hN b m A L hb hm v hv
  change (∑ i ∈ range L, (g i)^2) ≤ _ at hp
  have hsum := sum_le_sum (s:=range L) (fun i _ => oneRow i)
  rw [sum_add_distrib,← mul_sum] at hsum
  simp only [sum_const,card_range,nsmul_eq_mul] at hsum
  apply hsum.trans
  have hlength : exp (x^((ε/2)/5)/2) ≤ 2*(L:ℝ) := by
    apply le_trans _ hL
    apply exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (rpow_le_rpow_of_exponent_le hx (by linarith)) (by norm_num)
  specialize hscale L hlength
  change 2*((L:ℝ)*((log N)^2*x*(1+log N)) + 8*((N:ℝ)^2*log N)^2) + (2*C^2)*L*x ≤ _ at hscale
  have hslack : 1 ≤ x^(ε/2) := one_le_rpow hx (by linarith)
  have hs := mul_le_mul_of_nonneg_right hscale (zero_le_one.trans hslack)
  have hbase : 0 ≤ (L:ℝ)*((log N)^2*x*(1+log N)) + 8*((N:ℝ)^2*log N)^2 := by
    have hn : 0 ≤ log N := log_nonneg (by exact_mod_cast hN)
    positivity
  have hgrow := mul_le_mul_of_nonneg_left hslack hbase
  have hxpow : x^ε = x^(ε/2)*x^(ε/2) := by rw [← rpow_add hx0]; congr 1; ring
  rw [hxpow]
  nlinarith only [hs, hp, hgrow, sq_nonneg ((N:ℝ)^2*log N)]

/-- The union bound costs one second moment per multiplier. -/
private theorem two_bad_counts (L : ℕ) (f g : ℕ → ℝ) {t M : ℝ} (ht : 0 < t)
    (hf : (∑ i ∈ range L, (f i)^2) ≤ M) (hg : (∑ i ∈ range L, (g i)^2) ≤ M) :
    (((range L).filter (fun i => t < |f i| ∨ t < |g i|)).card:ℝ) * t^2 ≤ 2*M := by
  classical
  let S := (range L).filter (fun i => t < |f i| ∨ t < |g i|)
  calc
    _ = ∑ _i ∈ S, t^2 := by simp [S]
    _ ≤ ∑ i ∈ S, ((f i)^2+(g i)^2) := by
      apply sum_le_sum; intro i hi
      rcases (mem_filter.1 hi).2 with h | h
      · have h' := (sq_le_sq₀ ht.le (abs_nonneg _)).2 h.le
        rw [sq_abs] at h'; linarith only [h',sq_nonneg (g i)]
      · have h' := (sq_le_sq₀ ht.le (abs_nonneg _)).2 h.le
        rw [sq_abs] at h'; linarith only [h',sq_nonneg (f i)]
    _ ≤ ∑ i ∈ range L, ((f i)^2+(g i)^2) := sum_le_sum_of_subset_of_nonneg
        (filter_subset _ _) (fun i _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ _ := by rw [sum_add_distrib]; linarith

/-- Indices failing either of the second-prime tests in the prescribed splitting class. -/
def failures (x ε : ℝ) (q b m A L : ℕ) : Finset ℕ :=
  let d (i : ℕ) := b+m*(A+i)
  let N := cutoff x
  let t := x^(1/2+ε)/2
  (range L).filter (fun i =>
    t < |twistedBy x N (d i) (fun _ => 1)| ∨
    t < |twistedBy x N (d i) (fun n => (jacobiSym (n:ℤ) q:ℝ))|)

/-- With x fixed in both tests, the exceptional fraction tends to zero uniformly in
the chosen first prime, the starting index and the admissible progression. -/
theorem simultaneous_splitting_progression (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ q b m A L : ℕ, b%4=3 → 4 ∣ m →
      (∀ p : ℕ, p.Prime → p ∣ m → (p:ℝ) ≤ x^(ε/5) ∨ cutoff x < p) →
      exp (x^(ε/5)/2) ≤ 2*(L:ℝ) →
      ((failures x ε q b m A L).card:ℝ) ≤ 8*L/x^ε := by
  filter_upwards [eventually_gt_atTop (0:ℝ),progression_moment hε] with x hx hxmom
  intro q b m A L hb hm hdiv hL
  let d (i : ℕ) := b+m*(A+i)
  let F (i : ℕ) := twistedBy x (cutoff x) (d i) (fun _ => 1)
  let G (i : ℕ) := twistedBy x (cutoff x) (d i) (fun n => (jacobiSym (n:ℤ) q:ℝ))
  have hχ (n : ℕ) : |(jacobiSym (n:ℤ) q : ℝ)| ≤ 1 := by
    rcases jacobiSym.trichotomy (n:ℤ) q with h|h|h <;> rw [h] <;> norm_num
  have h := two_bad_counts L F G (show 0 < x^(1/2+ε)/2 by positivity)
    (hxmom b m A L hb hm hdiv hL (fun _ => 1) (by simp))
    (hxmom b m A L hb hm hdiv hL _ hχ)
  change ((failures x ε q b m A L).card:ℝ)*(x^(1/2+ε)/2)^2 ≤ 2*(L*x*x^ε) at h
  have ht : (x^(1/2+ε)/2)^2 = x*(x^ε)^2/4 := by
    rw [div_pow,← rpow_mul_natCast hx.le,show (1/2+ε)*(2:ℕ) = 1+ε*2 by push_cast;ring,
      rpow_add hx,rpow_one,rpow_mul hx.le]; norm_num
  have hpos := rpow_pos_of_pos hx ε
  rw [ht] at h
  apply (le_div_iff₀ hpos).2
  apply (mul_le_mul_iff_left₀ (mul_pos hx hpos)).mp
  linarith only [h]

end D5.S3.CharacterSums.SplittingProgressionMangoldtSupply
