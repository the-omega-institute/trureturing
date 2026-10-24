/- GID: D5/S3/Analytic/KarpZhangNinh/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangNinh/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Coefficientwise log-concavity for the triple rising-factorial series. -/

import D5.S3.Analytic.KarpZhangNinh.Kernel
import D5.S3.Analytic.KarpZhangNinh.Homogeneous
import D5.S3.Analytic.KarpZhangNinh.Beta
import D5.S3.Analytic.KarpZhangGamma.Result

/-!
admission_basis: open-problem-resolution (#21124; Proved)
Judgment form: the source claim keeps the full sequence predicate, all natural
degrees, and all nonnegative real parameters. Supporting content is the
trisection balancing inequality, the general symmetric beta lifting, and
backward propagation of the paired kernel sign. Finite pairing, one-sign-change
weighting and the Abel decomposition are reused from their existing owners.
Utility none: all declarations are uniform polynomial identities and inequalities,
not bounded computations, checkers, numerical reductions or certified instances.
-/

noncomputable section
open Finset
open scoped Topology
namespace D5.S3.Analytic.KarpZhangNinh.Result
open Kernel

/-- The finite Cauchy coefficient; the zero endpoints vanish. -/
/- proof_shape: bind-only definition; consumer: result. -/
def delta (f : ℕ → ℝ) (μ α β : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ range (m+1), f k * f (m-k) * raw μ α β m k

/- proof_shape: bind-only definition; consumer: tail_pair, central_tail_of_sign, tail_nonneg_pos. -/
private def pair (K : ℕ → ℝ) (m k : ℕ) : ℝ :=
  if 2*k<m then K k + K (m-k) else K k

/- proof_shape: bind-only; consumer: central_tail_of_sign. -/
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

/- proof_shape: bind-only; consumer: tail_nonneg_pos. -/
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


/- proof_shape: bind-only definition; consumer: lift_normalization, Z_symm, full_tail_nonneg. -/
def Z (m : ℕ) (u v : ℝ) : ℝ :=
  ∑ k ∈ range (m+1), a k u * a (m-k) v

/- proof_shape: bind-only; consumer: normalization_term. -/
private theorem factorial_product (n : ℕ) (hn : 0<n) :
    (n.factorial:ℝ) = n * ((n-1).factorial:ℝ) := by
  exact_mod_cast (Nat.mul_factorial_pred (Nat.ne_of_gt hn)).symm

/- proof_shape: content; escape_witness: normalization_term (factorial computation);
consumer: lift_normalization. -/
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
  have hsub : 3*m-3*k=3*(m-k) := by omega
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

/- proof_shape: content; escape_witness: normalization_term; consumer: Z_monotoneOn. -/
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



/- proof_shape: bind-only; consumer: full_tail_nonneg. -/
private theorem Z_symm (m : ℕ) (u v : ℝ) : Z m u v = Z m v u := by
  unfold Z
  rw [← sum_range_reflect (fun k => a k u * a (m-k) v) (m+1)]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_range.mp hk
  rw [show m+1-1-k=m-k by omega, show m-(m-k)=k by omega]
  exact mul_comm _ _

/- proof_shape: bind-only; consumer: full_tail_nonneg. -/
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
  exact (mul_le_mul_left (by positivity : (0:ℝ)<((3*m).factorial:ℝ))).mp he

/- proof_shape: content; escape_witness: Homogeneous.strictMonoOn_slice;
consumer: tail_nonneg_pos. -/
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
    rcases hm' with rfl | rfl <;> simp [raw, sum_range_succ]

/- proof_shape: bind-only; consumer: tail_nonneg. -/
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

/- proof_shape: content; escape_witness: tail_nonneg_pos and the polynomial limit;
consumer: result. -/
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
  exact tail_nonneg_pos m q hq (by linarith) (by linarith) (by linarith)

/-- The exact universal coefficient inequality of Conjecture 3.8. -/
/- proof_shape: bind-only definition; consumer: result. -/
def claim : Prop :=
  ∀ (f : ℕ → ℝ) (μ α β : ℝ) (m : ℕ),
    KarpZhangReciprocal.Result.IsLogConcave f → 0≤μ → 0≤α → 0≤β →
      0≤delta f μ α β m

/-- The triple-Pochhammer coefficient assertion for every admissible sequence. -/
/- proof_shape: content; escape_witness: full_tail_nonneg;
admission_basis: open-problem-resolution; consumer: external conjecture 3.8 settlement (#21124). -/
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
