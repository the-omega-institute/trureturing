/- GID: D5/S3/Combinatorics/Circle/SparseNecklaceRounding/Arithmetic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/SparseNecklaceRounding/Arithmetic
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Sparse cyclic gap cuts, low-bit winding and literal centered chain coordinates. -/
import D5.S3.Combinatorics.Circle.PhysicalJointRepetition.Repetition
import Batteries.Tactic.OpenPrivate

/-! Sparse cyclic cuts and their original physical coordinates. -/
set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.SparseNecklaceRounding
open SourceWidth PeriodicShorteningArithmetic
open scoped BigOperators
open private base_fresh_value
  from D5.S3.Combinatorics.Circle.PhysicalJointRepetition.Repetition

/-- The integer with one bit at each successive gap prefix. The final gap
determines the period but introduces no further one-bit. -/
def bits : List ℕ → ℤ
  | [] => 0
  | a :: l => 1 + (2 : ℤ) ^ a * bits l

/-- A cut rotates the suffix to the low end; no minimal-period quotient is taken. -/
def cutHead (l r : List ℕ) : ℤ := bits (r ++ l)

/-- These are exactly the low bits already carried across the period. -/
def cutCharge (r : List ℕ) : ℤ := bits r

private theorem bits_append (l r : List ℕ) :
    bits (l ++ r) = bits l + (2 : ℤ) ^ l.sum * bits r := by
  induction l with
  | nil => simp [bits]
  | cons a l ih =>
    simp only [List.cons_append, bits, List.sum_cons, ih, pow_add]
    ring

private theorem bits_nonneg (l : List ℕ) : 0 ≤ bits l := by
  induction l with
  | nil => simp [bits]
  | cons a l ih => dsimp [bits]; positivity

private theorem bits_pos {l : List ℕ} (hl : l ≠ []) : 0 < bits l := by
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons a l => dsimp [bits]; have := bits_nonneg l; positivity

private theorem sparse_pow_bound (l : List ℕ) (hl : ∀ a ∈ l, 2 ≤ a) :
    3 * bits l + 1 ≤ (2 : ℤ) ^ l.sum := by
  revert hl
  induction l with
  | nil => intro _; simp [bits]
  | cons a l ih =>
    intro hl
    have ha : 2 ≤ a := hl a (by simp)
    have ht := ih (fun b hb => hl b (by simp [hb]))
    have hfour : (4 : ℤ) ≤ 2 ^ a := by
      calc
        (4 : ℤ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha
    have hm := mul_le_mul_of_nonneg_left ht (show (0 : ℤ) ≤ 2 ^ a by positivity)
    simp only [bits, List.sum_cons, pow_add]
    nlinarith

private theorem bits_odd {l : List ℕ} (hl : l ≠ [])
    (hg : ∀ a ∈ l, 2 ≤ a) : bits l % 2 = 1 := by
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons a l =>
    have ha : 0 < a := by have := hg a (by simp); omega
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
    simp [bits, pow_succ, Int.add_emod, Int.mul_emod]

private theorem cut_winding (l r : List ℕ) :
    (2 : ℤ) ^ r.sum * bits (l ++ r) =
      cutHead l r + modulus (l.sum + r.sum) * cutCharge r := by
  rw [bits_append]
  simp only [cutHead, cutCharge, bits_append, modulus, pow_add]
  ring

private theorem cut_step (l r : List ℕ) (a : ℕ) :
    (2 : ℤ) ^ a * cutHead (l ++ [a]) r =
      modulus (l.sum + a + r.sum) + cutHead l (a :: r) := by
  simp only [cutHead, bits_append, bits, List.sum_cons, List.sum_nil,
    mul_zero, add_zero, modulus, pow_add]
  ring

private theorem charge_step (r : List ℕ) (a : ℕ) :
    cutCharge (a :: r) = (2 : ℤ) ^ a * cutCharge r + 1 := by
  simp [cutCharge, bits, add_comm]

private theorem cut_low_bits {l r : List ℕ} (hl : l ≠ []) :
    0 ≤ cutCharge r ∧ cutCharge r < cutHead l r := by
  have hb := bits_pos hl
  have hr := bits_nonneg r
  have hp : (0 : ℤ) < 2 ^ r.sum := by positivity
  simp only [cutCharge, cutHead, bits_append]
  constructor
  · exact hr
  · nlinarith

private theorem modulus_next (k : ℕ) : modulus (k + 1) = 2 * modulus k + 1 := by
  simp only [modulus, pow_succ]
  ring

private theorem centered_pair_of_charge (k e : ℕ) (hk : 2 ≤ k) (i : Fin k)
    (f c : ℤ)
    (hw : (2 : ℤ) ^ i.val * e = f + modulus k * c)
    (hf : -(modulus k / 2) ≤ f ∧ f ≤ modulus k / 2)
    (hg : -modulus k ≤ 2 * f - c ∧ 2 * f - c ≤ modulus k) :
    actualSource k e i = f ∧
      actualSource (k + 1) (2 * e) i.castSucc = 2 * f - c := by
  obtain ⟨hN, ho⟩ := TwoRunSource.modulus_positive_odd k (by omega)
  obtain ⟨hQ, hqo⟩ := TwoRunSource.modulus_positive_odd (k + 1) (by omega)
  have hhalf : modulus (k + 1) / 2 = modulus k := by
    rw [modulus_next]
    omega
  constructor
  · apply centered_unique hN ho (centered_bounds hN ho _) hf
    rw [centered_mod, hw]
    simp [Int.add_emod, Int.mul_emod]
  · have he : (2 : ℤ) ^ i.val * (2 * e : ℕ) =
        (2 * f - c) + modulus (k + 1) * c := by
      push_cast
      rw [modulus_next]
      nlinarith [hw]
    apply centered_unique hQ hqo (centered_bounds hQ hqo _) (by simpa [hhalf] using hg)
    rw [centered_mod, Fin.val_castSucc, he]
    simp [Int.add_emod, Int.mul_emod]

/-- The split is a cut of the actual binary necklace. Moving the last gap of
the left part across the seam gives the next head and next winding. Every
positive label and the terminal retain their original index. -/
theorem native_chain_coordinates (l r : List ℕ) (a : ℕ)
    (hg : ∀ b ∈ (l ++ [a]) ++ r, 2 ≤ b) :
    let k := l.sum + a + r.sum
    let e := (bits ((l ++ [a]) ++ r)).toNat
    let N := modulus k
    let h := cutHead (l ++ [a]) r
    let h' := cutHead l (a :: r)
    let z := cutCharge r
    let z' := cutCharge (a :: r)
    let n := (N - h') / 2
    let tau := (z' + 1) / 2
    2 ≤ k ∧ 0 < (e : ℤ) ∧ 3 * (e : ℤ) ≤ N ∧
    0 < h ∧ 3 * h ≤ N ∧ 0 < h' ∧ 3 * h' ≤ N ∧
    h % 2 = 1 ∧ h' % 2 = 1 ∧
    0 ≤ z ∧ z < h ∧ 0 < z' ∧ z' ≤ h' ∧ z' % 2 = 1 ∧
    (2 : ℤ) ^ a * h = N + h' ∧ z' = (2 : ℤ) ^ a * z + 1 ∧
    (2 : ℤ) ^ r.sum * e = h + N * z ∧
    2 * n = N - h' ∧ 2 * tau = z' + 1 ∧
    N ≤ 3 * n ∧ n ≤ N / 2 ∧ 1 ≤ tau ∧ tau ≤ h' ∧
    ((2 : ℤ) ^ (a - 1) - 1) * h = n + h' - h ∧
    ((2 : ℤ) ^ (a - 1) - 1) * z + tau = z' - z ∧
    0 < n + h' - (e : ℤ) ∧ 2 * n + z' ≤ N ∧
    actualSource (k + 1) (2 * e) (Fin.last k) = (e : ℤ) ∧
    (∀ t : ℕ, t ≤ a - 2 → ∃ hi : r.sum + t < k,
      let i : Fin k := ⟨r.sum + t, hi⟩
      let mass := (2 : ℤ) ^ t * h
      let charge := (2 : ℤ) ^ t * z
      0 < mass ∧ 3 * mass ≤ N ∧ 0 ≤ charge ∧ charge < mass ∧
      actualSource k e i = mass ∧
      actualSource (k + 1) (2 * e) i.castSucc = 2 * mass - charge) ∧
    (∃ hi : r.sum + a - 1 < k,
      let i : Fin k := ⟨r.sum + a - 1, hi⟩
      actualSource k e i = -n ∧
      actualSource (k + 1) (2 * e) i.castSucc = -2 * n - tau ∧
      0 < n ∧ 0 < 2 * n + tau ∧ 2 * n + tau ≤ N) := by
  dsimp only
  let k := l.sum + a + r.sum
  let N := modulus k
  let h := cutHead (l ++ [a]) r
  let h' := cutHead l (a :: r)
  let z := cutCharge r
  let z' := cutCharge (a :: r)
  let n := (N - h') / 2
  let tau := (z' + 1) / 2
  let e := (bits ((l ++ [a]) ++ r)).toNat
  have ha : 2 ≤ a := hg a (by simp)
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hsum : ((l ++ [a]) ++ r).sum = k := by simp [k, add_assoc]
  have hrmem : ∀ b ∈ r ++ (l ++ [a]), 2 ≤ b := by
    intro b hb
    exact hg b (by simpa [List.mem_append, or_assoc, or_comm, or_left_comm] using hb)
  have hnmem : ∀ b ∈ (a :: r) ++ l, 2 ≤ b := by
    intro b hb
    exact hg b (by simpa [List.mem_append, or_assoc, or_comm, or_left_comm] using hb)
  have hshead : (r ++ (l ++ [a])).sum = k := by simp [k]; omega
  have hsnext : ((a :: r) ++ l).sum = k := by simp [k]; omega
  have he : (e : ℤ) = bits ((l ++ [a]) ++ r) := Int.toNat_of_nonneg (bits_nonneg _)
  have hepos : 0 < (e : ℤ) := by rw [he]; exact bits_pos (by simp)
  have heb : 3 * (e : ℤ) ≤ N := by
    have hb := sparse_pow_bound ((l ++ [a]) ++ r) hg
    rw [hsum] at hb
    dsimp [N, modulus]
    linarith [he]
  have hhpos : 0 < h := bits_pos (by simp [h, cutHead])
  have hhnext : 0 < h' := bits_pos (by simp [h', cutHead])
  have hhb : 3 * h ≤ N := by
    have hb := sparse_pow_bound (r ++ (l ++ [a])) hrmem
    rw [hshead] at hb
    dsimp [h, cutHead, N, modulus] at *
    linarith
  have hhnb : 3 * h' ≤ N := by
    have hb := sparse_pow_bound ((a :: r) ++ l) hnmem
    rw [hsnext] at hb
    dsimp [h', cutHead, N, modulus] at *
    linarith
  have hho : h % 2 = 1 := bits_odd (by simp) hrmem
  have hhno : h' % 2 = 1 := bits_odd (by simp) hnmem
  have hz := cut_low_bits (l := l ++ [a]) (r := r) (by simp)
  have hzs : z' = (2 : ℤ) ^ a * z + 1 := charge_step r a
  have hz0 : 0 ≤ z := hz.1
  have hzh : z < h := hz.2
  have hzp : 0 < z' := by rw [hzs]; positivity
  have hzle : z' ≤ h' := by
    have := bits_nonneg l
    have hp : (0 : ℤ) ≤ 2 ^ (a :: r).sum := by positivity
    change bits (a :: r) ≤ bits ((a :: r) ++ l)
    rw [bits_append]
    exact le_add_of_nonneg_right (mul_nonneg hp (bits_nonneg l))
  have hzo : z' % 2 = 1 := bits_odd (by simp) (by
    intro b hb; exact hnmem b (List.mem_append_left l hb))
  have hstep : (2 : ℤ) ^ a * h = N + h' := cut_step l r a
  have hw : (2 : ℤ) ^ r.sum * e = h + N * z := by
    rw [he]
    simpa [k, List.sum_append, List.sum_cons, List.sum_nil] using cut_winding (l ++ [a]) r
  obtain ⟨hN, hNo⟩ := TwoRunSource.modulus_positive_odd k (by omega)
  have hn : 2 * n = N - h' := by dsimp [n, N] at *; omega
  have ht : 2 * tau = z' + 1 := by dsimp [tau]; omega
  have hnb : N ≤ 3 * n ∧ n ≤ N / 2 := by omega
  have htb : 1 ≤ tau ∧ tau ≤ h' := by omega
  have hpow : (2 : ℤ) ^ a = 2 * (2 : ℤ) ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
    ring
  have hstep' := hstep
  rw [hpow] at hstep'
  have hzs' := hzs
  rw [hpow] at hzs'
  have hv : (2 : ℤ) ^ (a - 1) * h = N - n := by nlinarith [hstep', hn]
  have hq : (2 : ℤ) ^ (a - 1) * z + 1 = tau := by nlinarith [hzs', ht]
  have hP : ((2 : ℤ) ^ (a - 1) - 1) * h = n + h' - h := by nlinarith [hv,hn]
  have hC : ((2 : ℤ) ^ (a - 1) - 1) * z + tau = z' - z := by nlinarith [hq,ht]
  have hdir : 0 < n + h' - (e : ℤ) := by omega
  have hpeak : 2 * n + z' ≤ N := by omega
  have hfresh : actualSource (k + 1) (2 * e) (Fin.last k) = (e : ℤ) := by
    apply base_fresh_value k e hk
    have hp : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
      ring
    have hhalf : (e : ℤ) ≤ (2 : ℤ) ^ (k - 1) - 1 := by
      dsimp [N, modulus] at heb
      omega
    have hNat : e + 1 ≤ 2 ^ (k - 1) := by
      exact_mod_cast (show (e : ℤ) + 1 ≤ (2 : ℤ) ^ (k - 1) by linarith [hhalf])
    omega
  refine ⟨hk, hepos, heb, hhpos, hhb, hhnext, hhnb, hho, hhno,
    hz0, hzh, hzp, hzle, hzo, hstep, hzs, hw, hn, ht,
    hnb.1, hnb.2, htb.1, htb.2, hP, hC, hdir, hpeak, hfresh, ?_, ?_⟩
  · intro t htt
    have hit : r.sum + t < k := by dsimp [k]; omega
    refine ⟨hit, ?_⟩
    let mass := (2 : ℤ) ^ t * h
    let charge := (2 : ℤ) ^ t * z
    have hm : 0 < mass := by dsimp [mass]; positivity
    have hc : 0 ≤ charge ∧ charge < mass := by
      dsimp [charge, mass]
      exact ⟨mul_nonneg (by positivity) hz0,
        mul_lt_mul_of_pos_left hzh (by positivity)⟩
    have htp : (4 : ℤ) * 2 ^ t ≤ 2 ^ a := by
      have hm := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show t + 2 ≤ a by omega)
      simpa [pow_add, mul_comm] using hm
    have hmass : 3 * mass ≤ N := by
      have hp := mul_le_mul_of_nonneg_right htp (le_of_lt hhpos)
      dsimp [mass]
      nlinarith [hstep, hhnb]
    have heq : (2 : ℤ) ^ (r.sum + t) * e = mass + N * charge := by
      calc
        _ = (2 : ℤ) ^ t * ((2 : ℤ) ^ r.sum * e) := by rw [pow_add]; ring
        _ = (2 : ℤ) ^ t * (h + N * z) := by rw [hw]
        _ = mass + N * charge := by dsimp [mass,charge]; ring
    have hp := centered_pair_of_charge k e hk ⟨r.sum + t, hit⟩ mass charge heq
      (by have := Int.emod_nonneg N (by omega : (2 : ℤ) ≠ 0); omega)
      (by omega)
    exact ⟨hm, hmass, hc.1, hc.2, hp.1, hp.2⟩
  · have hit : r.sum + a - 1 < k := by dsimp [k]; omega
    refine ⟨hit, ?_⟩
    have heq : (2 : ℤ) ^ (r.sum + a - 1) * e = -n + N * tau := by
      have hq' : (2 : ℤ) ^ (a - 1) * z = tau - 1 := by linarith
      calc
        _ = (2 : ℤ) ^ (a - 1) * ((2 : ℤ) ^ r.sum * e) := by
          rw [show r.sum + a - 1 = r.sum + (a - 1) by omega, pow_add]
          ring
        _ = (2 : ℤ) ^ (a - 1) * (h + N * z) := by rw [hw]
        _ = (2 : ℤ) ^ (a - 1) * h + N * ((2 : ℤ) ^ (a - 1) * z) := by ring
        _ = -n + N * tau := by rw [hv,hq']; ring
    have hnpos : 0 < n := by omega
    have hgmag : 0 < 2 * n + tau ∧ 2 * n + tau ≤ N := by omega
    have hp := centered_pair_of_charge k e hk ⟨r.sum + a - 1, hit⟩ (-n) tau heq
      (by omega) (by omega)
    exact ⟨hp.1, by convert hp.2 using 1 <;> ring, hnpos, hgmag.1, hgmag.2⟩

end D5.S3.Combinatorics.Circle.SparseNecklaceRounding
