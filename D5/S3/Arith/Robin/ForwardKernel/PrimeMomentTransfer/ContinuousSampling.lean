/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous cells transfer integer interval moments to real sampling with endpoint and product bounds. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.ArithmeticTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FiniteProductMomentBounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic
open scoped BigOperators
open Set MeasureTheory
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private lemma psi_nat_shift (n la lb : ℕ) (hle : la ≤ lb) :
    Chebyshev.psi ((n + lb : ℕ) : ℝ) - Chebyshev.psi ((n + la : ℕ) : ℝ) =
      ∑ d ∈ Finset.Ioc la lb, ArithmeticFunction.vonMangoldt (n+d) := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  have hi (r : ℕ) :
      (∑ i ∈ Finset.Icc 0 r, ArithmeticFunction.vonMangoldt i) =
      ∑ i ∈ Finset.Ioc 0 r, ArithmeticFunction.vonMangoldt i := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (f := ArithmeticFunction.vonMangoldt)
      (a := 0) (b := r) (by omega)]
    simp
  have hsum :
      (∑ i ∈ Finset.Ioc 0 (n + la), ArithmeticFunction.vonMangoldt i) +
        ∑ i ∈ Finset.Ioc (n + la) (n + lb), ArithmeticFunction.vonMangoldt i =
      ∑ i ∈ Finset.Ioc 0 (n + lb), ArithmeticFunction.vonMangoldt i :=
    Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.add_le_add_left hle n)
  have hshift :
      (∑ d ∈ Finset.Ioc la lb, ArithmeticFunction.vonMangoldt (n+d)) =
        ∑ i ∈ Finset.Ioc (n + la) (n + lb), ArithmeticFunction.vonMangoldt i := by
    have h := Finset.sum_Ico_add (f := ArithmeticFunction.vonMangoldt) (la+1) (lb+1) n
    have hleft : Finset.Ico (la+1) (lb+1) = Finset.Ioc la lb := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    have hright : Finset.Ico (la+1+n) (lb+1+n) = Finset.Ioc (n+la) (n+lb) := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    rw [hleft, hright] at h
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  rw [hi (n+lb), hi (n+la)]
  rw [← hsum, hshift]
  ring

private lemma vm_le_log_of_le {m : ℕ} {X : ℝ} (hm : 1 ≤ m) (hM : (m : ℝ) ≤ X) :
    ArithmeticFunction.vonMangoldt m ≤ Real.log X := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le hm0 hM
  exact ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.strictMonoOn_log.monotoneOn hm0 hX0 hM)

private lemma psi_nat_succ_le {m : ℕ} {X : ℝ} (hm : 1 ≤ m) (hM : (m+1 : ℕ) ≤ X) :
    Chebyshev.psi ((m+1 : ℕ) : ℝ) - Chebyshev.psi (m : ℝ) ≤ Real.log X := by
  have hs := psi_nat_shift 0 m (m+1) (by omega)
  rw [show (0 + (m+1) : ℕ) = m+1 by omega, show (0+m : ℕ) = m by omega] at hs
  rw [hs]
  simp [Finset.sum_Ioc_succ_top (by omega)]
  exact vm_le_log_of_le (by omega) (by exact_mod_cast hM)

private lemma floor_shift_cases {x A : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (hA : 0 ≤ A) :
    ⌊x + A⌋₊ = ⌊A⌋₊ ∨ ⌊x + A⌋₊ = ⌊A⌋₊ + 1 := by
  by_cases h : x + A < (⌊A⌋₊ : ℝ) + 1
  · left
    apply (Nat.floor_eq_iff (by positivity)).2
    constructor
    · exact (Nat.floor_le hA).trans (by linarith)
    · exact h
  · right
    apply (Nat.floor_eq_iff (by positivity)).2
    constructor
    · push_cast; exact le_of_not_gt h
    · have hAf : A < (⌊A⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one A
      push_cast; linarith

lemma floor_shift_cases_add_nat {n : ℕ} {x A : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (hA : 0 ≤ A) :
    ⌊(n : ℝ) + x + A⌋₊ = n + ⌊A⌋₊ ∨ ⌊(n : ℝ) + x + A⌋₊ = n + ⌊A⌋₊ + 1 := by
  rw [show (n : ℝ) + x + A = (x+A) + n by ring, Nat.floor_add_natCast (by positivity)]
  exact floor_shift_cases hx hx1 hA |>.imp (fun h => by rw [h]; omega) (fun h => by rw [h]; omega)

lemma psi_endpoint_discrepancy {m m' p q : ℕ} {L : ℝ}
    (hmm : m ≤ m') (hp : p = m ∨ p = m+1) (hq : q = m' ∨ q = m'+1)
    (hpL : (p : ℝ) ≤ 4*L) (hqL : (q : ℝ) ≤ 4*L) (hm1 : 1 ≤ m)
    (hmm1 : 1 ≤ m') (hL : 1 ≤ L) :
    |(Chebyshev.psi q - Chebyshev.psi p) -
      (Chebyshev.psi m' - Chebyshev.psi m)| ≤ 2 * Real.log (4*L) := by
  have hstep (r : ℕ) (hr : 1 ≤ r) (hrL : (r+1 : ℕ) ≤ 4*L) :
      |Chebyshev.psi ((r+1 : ℕ) : ℝ) - Chebyshev.psi (r : ℝ)| ≤ Real.log (4*L) := by
    have hs := psi_nat_succ_le hr hrL
    have hnon : 0 ≤ Chebyshev.psi ((r+1 : ℕ) : ℝ) - Chebyshev.psi (r : ℝ) :=
      sub_nonneg.mpr (Chebyshev.psi_mono (by exact_mod_cast (Nat.le_succ r)))
    rw [abs_of_nonneg hnon]
    exact hs
  have hlog : 0 ≤ Real.log (4*L) := Real.log_nonneg (by nlinarith [hL])
  have hp' : |Chebyshev.psi p - Chebyshev.psi m| ≤ Real.log (4*L) := by
    rcases hp with rfl | rfl
    · simp [hlog]
    · exact hstep m hm1 (by linarith [hpL])
  have hq' : |Chebyshev.psi q - Chebyshev.psi m'| ≤ Real.log (4*L) := by
    rcases hq with rfl | rfl
    · simp [hlog]
    · exact hstep m' hmm1 (by linarith [hqL])
  calc
    _ = |(Chebyshev.psi q - Chebyshev.psi m') -
        (Chebyshev.psi p - Chebyshev.psi m)| := by ring_nf
    _ ≤ |Chebyshev.psi q - Chebyshev.psi m'| +
        |Chebyshev.psi p - Chebyshev.psi m| := by
      simpa [abs_neg, abs_sub_comm] using (abs_sub_le (Chebyshev.psi q - Chebyshev.psi m')
        0 (Chebyshev.psi p - Chebyshev.psi m))
    _ ≤ 2 * Real.log (4*L) := by linarith [hq', hp']

lemma S_eq_psi_shift (H a b : ℝ) (n : ℕ) (ha : 0 ≤ a) (hab : a ≤ b) (hH : 0 ≤ H) :
    S H a b n =
      (Chebyshev.psi ((n + ⌊b*H⌋₊ : ℕ) : ℝ) - Chebyshev.psi ((n + ⌊a*H⌋₊ : ℕ) : ℝ)) -
        ((⌊b*H⌋₊ : ℝ) - ⌊a*H⌋₊) := by
  have hle : ⌊a*H⌋₊ ≤ ⌊b*H⌋₊ := Nat.floor_mono (mul_le_mul_of_nonneg_right hab hH)
  change (∑ d ∈ Finset.Ioc ⌊a*H⌋₊ ⌊b*H⌋₊,
      (ArithmeticFunction.vonMangoldt (n+d)-1)) = _
  rw [Finset.sum_sub_distrib, psi_nat_shift n _ _ hle]
  simp [Nat.card_Ioc, Nat.cast_sub hle, smul_eq_mul]


/-- The continuous and left-cell integer increments differ only by the two endpoint
lattice crossings and the centering discrepancy. -/
theorem sampling_pointwise {N H M x a b : ℝ}
    (hN : 2 ≤ N) (hH : 1 ≤ H) (ha : 0 ≤ a) (hab : a ≤ b) (hbM : b ≤ M)
    (hMH : M * H ≤ N) (hx : x ∈ Icc N (2 * N)) :
    |Delta H a b x - S H a b ⌊x⌋₊| ≤ 2 * Real.log (4 * N) + 2 := by
  let n : ℕ := ⌊x⌋₊
  let t : ℝ := x - n
  have hxN : N ≤ x := hx.1
  have hx2N : x ≤ 2 * N := hx.2
  have hn : 1 ≤ n := by
    apply Nat.le_floor
    have h : (1 : ℝ) ≤ x := by linarith [hxN]
    exact_mod_cast h
  have hnt : (n : ℝ) ≤ x := Nat.floor_le (by linarith [hxN])
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith [Nat.lt_floor_add_one x]
  have hH0 : 0 ≤ H := by linarith
  have haH : 0 ≤ a * H := mul_nonneg ha hH0
  have hb0 : 0 ≤ b := le_trans ha hab
  have hbH : 0 ≤ b * H := mul_nonneg hb0 hH0
  have hbaH : a * H ≤ b * H := mul_le_mul_of_nonneg_right hab hH0
  have hMH' : b * H ≤ N :=
    (mul_le_mul_of_nonneg_right hbM hH0).trans hMH
  have hxa : x + a * H ≤ 3 * N := by nlinarith
  have hxb : x + b * H ≤ 3 * N := by nlinarith
  let la : ℕ := ⌊a * H⌋₊
  let lb : ℕ := ⌊b * H⌋₊
  let p : ℕ := ⌊x + a * H⌋₊
  let q : ℕ := ⌊x + b * H⌋₊
  have hla : (la : ℝ) ≤ a * H := Nat.floor_le haH
  have hlb : (lb : ℝ) ≤ b * H := Nat.floor_le hbH
  have hlab : la ≤ lb := Nat.floor_mono hbaH
  have hp : p = n + la ∨ p = n + la + 1 := by
    dsimp [p, n, t]
    rw [show x + a * H = (n : ℝ) + (x - (n : ℝ)) + a * H by ring]
    exact floor_shift_cases_add_nat ht0 ht1 haH
  have hq : q = n + lb ∨ q = n + lb + 1 := by
    dsimp [q, n, t]
    rw [show x + b * H = (n : ℝ) + (x - (n : ℝ)) + b * H by ring]
    exact floor_shift_cases_add_nat ht0 ht1 hbH
  have hpL : (p : ℝ) ≤ 4 * N := by
    dsimp [p]
    exact (Nat.floor_le (by linarith [hxN])).trans (by linarith)
  have hqL : (q : ℝ) ≤ 4 * N := by
    dsimp [q]
    exact (Nat.floor_le (by linarith [hxN])).trans (by linarith)
  have hm1 : 1 ≤ n + la := by omega
  have hm'1 : 1 ≤ n + lb := by omega
  have hpsi := psi_endpoint_discrepancy (m := n + la) (m' := n + lb)
    (Nat.add_le_add_left hlab n) hp hq hpL hqL hm1 hm'1 (by linarith [hN])
  have hS := S_eq_psi_shift H a b n ha hab hH0
  dsimp [Delta]
  rw [Chebyshev.psi_eq_psi_coe_floor (x + b * H),
    Chebyshev.psi_eq_psi_coe_floor (x + a * H)]
  norm_num [Nat.cast_add] at hS
  rw [hS]
  have hmain :
      |(Chebyshev.psi ⌊x + b * H⌋₊ - Chebyshev.psi ⌊x + a * H⌋₊) -
        (Chebyshev.psi (n + lb) - Chebyshev.psi (n + la))| ≤
        2 * Real.log (4 * N) := by
    simpa [p, q, la, lb, Nat.cast_add] using hpsi
  have hcount : |((lb : ℝ) - la) - (b - a) * H| ≤ 1 := by
    have hfloora : a * H < (la : ℝ) + 1 := Nat.lt_floor_add_one _
    have hfloorb : b * H < (lb : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [abs_le]
    constructor <;> linarith
  have hlog : 0 ≤ Real.log (4 * N) := Real.log_nonneg (by nlinarith)
  have heq :
      (Chebyshev.psi ⌊x + b * H⌋₊ - Chebyshev.psi ⌊x + a * H⌋₊ -
          (b - a) * H) -
        (Chebyshev.psi (n + lb) - Chebyshev.psi (n + la) -
          ((lb : ℝ) - la)) =
      (Chebyshev.psi ⌊x + b * H⌋₊ - Chebyshev.psi ⌊x + a * H⌋₊ -
          (Chebyshev.psi (n + lb) - Chebyshev.psi (n + la))) +
        (((lb : ℝ) - la) - (b - a) * H) := by ring
  rw [heq]
  calc
    _ ≤ 2 * Real.log (4 * N) + 1 := (abs_add_le _ _).trans (add_le_add hmain hcount)
    _ ≤ 2 * Real.log (4 * N) + 2 := by linarith


end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
