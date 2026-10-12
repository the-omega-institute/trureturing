/- GID: D5/S1/Recurrence/KimberlingArrayFirstOccurrence
   generality: I
   mirror-B: D5/B/S1/Recurrence/KimberlingArrayFirstOccurrence
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Golden row occurrence counts first attain v at Lucas index four v minus five. -/

import D5.S1.Recurrence.KimberlingArrayRowPairs
import D5.S1.Recurrence.GoldenPartition

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

noncomputable section
namespace D5.S1.Recurrence.KimberlingArray
open Real D5.S0.Carrier D5.S1.Scale
local notation "φ" => goldenRatio

noncomputable def a (N : ℕ) : ℕ := by
  classical exact ((Finset.Icc 1 N).filter (fun i => N ∈ row i)).card

def claim : Prop := ∀ v : ℕ, 2 ≤ v →
  a (lucas (4 * v - 5)) = v ∧
    ∀ N, 1 ≤ N → N < lucas (4 * v - 5) → a N ≠ v

private theorem golden_pow_irrational (i : ℕ) (hi : 1 ≤ i) : Irrational (goldenRatio ^ i) := by
  cases i with
  | zero => omega
  | succ n =>
      rw [← goldenRatio_mul_fib_succ_add_fib n]
      exact (goldenRatio_irrational.mul_natCast (by simp)).add_natCast _

private theorem row_values (i N : ℕ) (hi : 1 ≤ i) (hmem : N ∈ row i) :
    ∃ k : ℕ, 1 ≤ k ∧ (N : ℝ) < (k : ℝ) * goldenRatio ^ i ∧
      (k : ℝ) * goldenRatio ^ i < N + 1 := by
  obtain ⟨k, hk, hN⟩ := hmem
  refine ⟨k, hk, ?_, ?_⟩
  · rw [hN]
    have hirr := (golden_pow_irrational i hi).natCast_mul (show k ≠ 0 by omega)
    exact lt_of_le_of_ne (Nat.floor_le (by positivity)) (hirr.ne_nat _).symm
  · rw [hN]
    exact Nat.lt_floor_add_one _

private theorem golden_pow_ge_index (i : ℕ) : (i : ℝ) ≤ goldenRatio ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
      cases i with
      | zero => simpa using one_lt_goldenRatio.le
      | succ n =>
          have hpow := goldenRatio_pow_sub_goldenRatio_pow n
          have hone : (1 : ℝ) ≤ goldenRatio ^ n := one_le_pow₀ one_lt_goldenRatio.le
          simp only [Nat.cast_add, Nat.cast_one] at ih ⊢
          linarith

private theorem row_index_le (i N : ℕ) (hmem : N ∈ row i) : i ≤ N := by
  obtain ⟨k, hk, hN⟩ := hmem
  rw [hN]
  apply Nat.le_floor
  have hkp : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact (golden_pow_ge_index i).trans (le_mul_of_one_le_left (by positivity) hkp)

private theorem rows_consecutive_disjoint (i : ℕ) (hi : 1 ≤ i) (N : ℕ)
    (h1 : N ∈ row i) (h2 : N ∈ row (i + 1)) : False := by
  obtain ⟨k, hk, hxlo, hxhi⟩ := row_values i N hi h1
  obtain ⟨l, hl, hylo, hyhi⟩ := row_values (i + 1) N (by omega) h2
  let A : ℝ := (Nat.fib (i + 1) : ℝ) * (goldenRatio ^ i)⁻¹
  let B : ℝ := (Nat.fib i : ℝ) * (goldenRatio ^ (i + 1))⁻¹
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (by exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < i + 1))
      (inv_pos.mpr (pow_pos goldenRatio_pos _))
  have hB : 0 < B := by
    dsimp [B]
    exact mul_pos (by exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < i))
      (inv_pos.mpr (pow_pos goldenRatio_pos _))
  have hpart : A + B = 1 := by
    simpa only [A, B, zpow_neg, zpow_natCast] using
      D5.S1.Recurrence.GoldenPartition.fibonacci_golden_partition i
  have hsum : (k : ℝ) * goldenRatio ^ i * A +
      (l : ℝ) * goldenRatio ^ (i + 1) * B =
      (Nat.fib (i + 1) : ℝ) * k + (Nat.fib i : ℝ) * l := by
    dsimp [A, B]
    field_simp [goldenRatio_ne_zero]
  have hN : (N : ℝ) * A + N * B = N := by
    calc _ = N * (A + B) := by ring
      _ = N := by rw [hpart, mul_one]
  have hNp : ((N : ℝ) + 1) * A + (N + 1) * B = N + 1 := by
    calc _ = (N + 1) * (A + B) := by ring
      _ = N + 1 := by rw [hpart, mul_one]
  have hlow := add_lt_add (mul_lt_mul_of_pos_right hxlo hA)
    (mul_lt_mul_of_pos_right hylo hB)
  have hupp := add_lt_add (mul_lt_mul_of_pos_right hxhi hA)
    (mul_lt_mul_of_pos_right hyhi hB)
  rw [hN, hsum] at hlow
  rw [hNp, hsum] at hupp
  have hlow' : N < Nat.fib (i + 1) * k + Nat.fib i * l := by exact_mod_cast hlow
  have hupp' : Nat.fib (i + 1) * k + Nat.fib i * l < N + 1 := by exact_mod_cast hupp
  omega

theorem lucas_zero : lucas 0 = 2 := by
  rfl

theorem lucas_succ (n : ℕ) : lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  unfold lucas
  rw [D5.S1.Scale.golden_lucas_succ_eq_fib_add_fib]
  norm_cast

theorem lucas_real (n : ℕ) : (lucas n : ℝ) = goldenRatio ^ n + goldenConj ^ n := by
  cases n with
  | zero => norm_num [lucas_zero]
  | succ n =>
    rw [lucas_succ]
    push_cast
    have hφ := goldenRatio_mul_fib_succ_add_fib n
    have hψ := goldenConj_mul_fib_succ_add_fib n
    rw [← hφ, ← hψ, Nat.fib_add_two]
    push_cast
    nlinarith [goldenRatio_add_goldenConj]

theorem lucas_pos (n : ℕ) : 0 < lucas n := by
  cases n with
  | zero => norm_num [lucas_zero]
  | succ n =>
    rw [lucas_succ]
    have hf : 0 < Nat.fib (n+2) := Nat.fib_pos.2 (by omega)
    omega

theorem lucas_recur (n : ℕ) : lucas (n+2) = lucas (n+1) + lucas n := by
  cases n with
  | zero => norm_num [lucas_succ, lucas_zero, Nat.fib_add_two]
  | succ n =>
    simp only [lucas_succ]
    simp only [Nat.fib_add_two]
    omega

theorem lucas_strict (n : ℕ) (hn : 1 ≤ n) : lucas n < lucas (n+1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.add_comm 1 k]
  rw [show k + 1 + 1 = k+2 by omega, lucas_recur]
  have := lucas_pos k
  omega

theorem lucas_mono {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) : lucas n ≤ lucas m := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => exact ih.trans (lucas_strict m (by omega)).le


theorem lucas_odd_real {n : ℕ} (hn : Odd n) :
    (lucas n : ℝ) = goldenRatio ^ n - (goldenRatio ^ n)⁻¹ := by
  rw [lucas_real, ← inv_pow, inv_goldenRatio, hn.neg_pow]
  ring

theorem lucas_even_real {n : ℕ} (hn : Even n) :
    (lucas n : ℝ) = goldenRatio ^ n + (goldenRatio ^ n)⁻¹ := by
  rw [lucas_real, ← inv_pow, inv_goldenRatio, hn.neg_pow]

theorem inv_one_add_inv_cube_lt_one : goldenRatio⁻¹ + (goldenRatio ^ 3)⁻¹ < 1 := by
  have hs := goldenRatio_sq
  have hb : goldenRatio < (5 : ℝ)/3 := by
    nlinarith [one_lt_goldenRatio, sq_nonneg (goldenRatio - 5/3)]
  have hi : goldenRatio⁻¹ = goldenRatio - 1 := by
    rw [inv_goldenRatio]
    linarith [goldenRatio_add_goldenConj]
  rw [← inv_pow, hi]
  have hcube : (goldenRatio - 1)^3 = 2*goldenRatio - 3 := by
    have hmul := congrArg (fun x : ℝ => x * goldenRatio) hs
    nlinarith [hs, hmul]
  rw [hcube]
  linarith

theorem lucas_mem_own_row {m : ℕ} (hm : Odd m) (hmp : 1 ≤ m) : lucas m ∈ row m := by
  refine ⟨1, by omega, ?_⟩
  simp only [Nat.cast_one, one_mul]
  symm
  apply Nat.floor_eq_iff (by positivity) |>.2
  rw [lucas_odd_real hm]
  have hp : 1 < goldenRatio ^ m := one_lt_pow₀ one_lt_goldenRatio (by omega)
  have hi : 0 < (goldenRatio ^ m)⁻¹ := by positivity
  have hil : (goldenRatio ^ m)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  constructor <;> linarith

theorem lucas_mem_lower_odd_row {m i : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (hi : Odd i) (hi1 : 1 ≤ i) (him : 2 * i < m) : lucas m ∈ row i := by
  have hid : i ≤ m := by omega
  have hd : Even (m - i) := by
    obtain ⟨a, ha⟩ := hm
    obtain ⟨b, hb⟩ := hi
    exact ⟨a-b, by omega⟩
  have hφ := goldenRatio_pos
  have hp : 0 < goldenRatio ^ i := by positivity
  have hpD : 0 < goldenRatio ^ (m-i) := by positivity
  have hpM : 0 < goldenRatio ^ m := by positivity
  have hiM : 0 < (goldenRatio ^ m)⁻¹ := by positivity
  have hD : goldenRatio ^ i * goldenRatio ≤ goldenRatio ^ (m-i) := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ one_lt_goldenRatio.le (by omega)
  have hratio : (goldenRatio ^ (m-i))⁻¹ * goldenRatio ^ i ≤ goldenRatio⁻¹ := by
    apply (mul_le_mul_iff_of_pos_right hpD).mp
    have hiφ : goldenRatio⁻¹ * (goldenRatio ^ i * goldenRatio) = goldenRatio ^ i := by
      field_simp
    calc
      (goldenRatio ^ (m-i))⁻¹ * goldenRatio ^ i * goldenRatio ^ (m-i) = goldenRatio ^ i := by
        field_simp
      _ = goldenRatio⁻¹ * (goldenRatio ^ i * goldenRatio) := hiφ.symm
      _ ≤ goldenRatio⁻¹ * goldenRatio ^ (m-i) := mul_le_mul_of_nonneg_left hD (by positivity)
  have hinv : (goldenRatio ^ m)⁻¹ ≤ (goldenRatio ^ 3)⁻¹ := by
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_lt_goldenRatio.le hm3)
  have hsum : (goldenRatio ^ (m-i))⁻¹ * goldenRatio ^ i + (goldenRatio ^ m)⁻¹ < 1 := by
    linarith [inv_one_add_inv_cube_lt_one]
  refine ⟨lucas (m-i), lucas_pos (m-i), ?_⟩
  symm
  apply Nat.floor_eq_iff (by positivity) |>.2
  rw [lucas_even_real hd, lucas_odd_real hm]
  have hprod : goldenRatio ^ (m-i) * goldenRatio ^ i = goldenRatio ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hid]
  rw [add_mul, hprod]
  constructor
  · have : 0 < (goldenRatio ^ (m-i))⁻¹ * goldenRatio ^ i := by positivity
    linarith
  · linarith

private theorem conj_embedding_pow (n : ℕ) :
    embedding (conj (phi ^ n)) = goldenConj ^ n := by
  change embedding (conjEquiv (phi ^ n)) = _
  rw [map_pow, map_pow]
  congr 1
  change embedding (conj phi) = _
  rw [conj_phi, map_sub, map_one, embedding_phi]
  linarith [goldenRatio_add_goldenConj]

/-- Any two positive rows have their first common value above the odd Lucas threshold. -/
theorem pair_lower_bound (i j N : ℕ) (hi : 1 ≤ i) (hij : i < j)
    (h1 : N ∈ row i) (h2 : N ∈ row j) : lucas (2*i+1) ≤ N := by
  by_contra hbad
  have hNL : N + 1 ≤ lucas (2*i+1) := by omega
  have hj : 1 ≤ j := by omega
  obtain ⟨k, hk, hxlo, hxhi⟩ := row_values i N hi h1
  obtain ⟨l, hl, hylo, hyhi⟩ := row_values j N hj h2
  let d := j-i
  have hd : 2 ≤ d := by
    by_contra hd
    have he : j = i+1 := by omega
    subst j
    exact rows_consecutive_disjoint i hi N h1 h2
  have hji : j = i+d := by omega
  let P := φ ^ i
  let D := φ ^ d
  let T := φ ^ (i+1)
  have hP : 0 < P := by positivity
  have hD : 0 < D := by positivity
  have hT : 0 < T := by positivity
  have hTP : T = P*φ := pow_succ _ _
  have hNreal : (N : ℝ)+1 ≤ lucas (2*i+1) := by exact_mod_cast hNL
  have hLreal : (lucas (2*i+1) : ℝ) < φ^(2*i+1) := by
    rw [lucas_odd_real (by exact ⟨i, by omega⟩)]
    have : 0 < (φ^(2*i+1))⁻¹ := by positivity
    linarith
  have hbig : φ^(2*i+1) = P*T := by
    dsimp [P,T]
    rw [← pow_add]
    congr 1; omega
  have hkT : (k : ℝ) < T := by
    apply (mul_lt_mul_iff_of_pos_right hP).mp
    nlinarith only [hbig, hxhi.trans_le hNreal |>.trans hLreal]
  have hlD : (l : ℝ)*D < T := by
    have hy : (l : ℝ)*φ^j = (l : ℝ)*D*P := by rw [hji,pow_add]; dsimp [P,D]; ring
    rw [hy] at hyhi
    apply (mul_lt_mul_iff_of_pos_right hP).mp
    nlinarith only [hbig, hyhi.trans_le hNreal |>.trans hLreal]
  let z : GoldenInt := (k : GoldenInt) - (l : GoldenInt)*phi^d
  have he : embedding z = (k : ℝ)-(l : ℝ)*D := by
    dsimp only [z,D]
    rw [map_sub,map_mul,map_pow,embedding_phi]
    simp
  have hec : embedding (conj z) = (k : ℝ)-(l : ℝ)*goldenConj^d := by
    change embedding (conjEquiv ((k : GoldenInt)-(l : GoldenInt)*phi^d)) = _
    rw [map_sub,map_mul,map_sub,map_mul]
    change embedding (conj (k : GoldenInt)) -
      embedding (conj (l : GoldenInt)) * embedding (conj (phi ^ d)) = _
    rw [conj_embedding_pow]
    simp [conj]
  have hb : z.b = -(l : ℤ)*(Nat.fib d : ℤ) := by
    simp [z,sub_eq_add_neg,golden_phi_pow_b_eq_fib_index]
  have hbn : z.b < 0 := by
    rw [hb]
    have hf : (0 : ℤ) < Nat.fib d := by exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < d)
    have hlz : (0 : ℤ) < l := by omega
    nlinarith
  have hz0 : z ≠ 0 := by intro hh; simp [hh] at hbn
  have he0 : embedding z ≠ 0 := fun hh => hz0 ((embedding_eq_zero_iff z).mp hh)
  have hec0 : embedding (conj z) ≠ 0 := by
    intro hh
    have := congrArg conj ((embedding_eq_zero_iff (conj z)).mp hh)
    simp only [conj_involutive, conj_zero] at this
    exact hz0 this
  have hsmall : |embedding z| < P⁻¹ := by
    apply (mul_lt_mul_iff_of_pos_right hP).mp
    rw [inv_mul_cancel₀ (ne_of_gt hP),← abs_of_pos hP,← abs_mul]
    rw [he]
    have hy : (l : ℝ)*φ^j = (l : ℝ)*D*P := by rw [hji,pow_add]; dsimp [P,D]; ring
    rw [hy] at hylo hyhi
    apply abs_lt.mpr
    constructor <;> dsimp only [P] at * <;> nlinarith only [hxlo,hxhi,hylo,hyhi]
  have hψ : goldenConj = -φ⁻¹ := by rw [inv_goldenRatio]; ring
  have habsψ : |goldenConj^d| = D⁻¹ := by
    rw [hψ,abs_pow,abs_neg,abs_of_pos (by positivity),inv_pow]
  have hc : |embedding (conj z)| ≤ (k : ℝ)+(l : ℝ)*D⁻¹ := by
    rw [hec]
    calc
      _ ≤ |(k : ℝ)| + |(l : ℝ)*goldenConj^d| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg (Nat.cast_nonneg _),abs_mul,
          abs_of_nonneg (Nat.cast_nonneg _),habsψ]
  have hlbound : (l : ℝ)*D⁻¹ < T*(D⁻¹)^2 := by
    have hh := mul_lt_mul_of_pos_right hlD (show 0 < (D⁻¹)^2 by positivity)
    have hcancel : (l : ℝ)*D*(D⁻¹)^2 = (l : ℝ)*D⁻¹ := by field_simp
    rwa [hcancel] at hh
  have hcT : |embedding (conj z)| < T*(1+(D⁻¹)^2) := by nlinarith only [hc, hkT, hlbound]
  have hD2 : φ^2 ≤ D := pow_le_pow_right₀ one_lt_goldenRatio.le hd
  have hDinv : D⁻¹ ≤ (φ^2)⁻¹ := inv_anti₀ (by positivity) hD2
  have hDinv2 : (D⁻¹)^2 ≤ (φ^4)⁻¹ := by
    have h := sq_le_sq₀ (show 0 ≤ D⁻¹ by positivity) (show 0 ≤ (φ^2)⁻¹ by positivity) |>.mpr hDinv
    calc
      _ ≤ ((φ^2)⁻¹)^2 := h
      _ = (φ^4)⁻¹ := by rw [← inv_pow,← pow_mul,inv_pow]
  have hφbound : φ*(1+(φ^4)⁻¹) < 2 := by
    have hφ : φ = 1+φ⁻¹ := by rw [inv_goldenRatio]; linarith [goldenRatio_add_goldenConj]
    have hh : φ*(φ^4)⁻¹ = (φ^3)⁻¹ := by rw [show (4 : ℕ)=3+1 by omega,pow_succ]; field_simp
    rw [mul_add,mul_one,hh]
    nth_rw 1 [hφ]
    linarith [inv_one_add_inv_cube_lt_one]
  have hnsmall : |(norm z : ℝ)| < 2 := by
    rw [← abs_embedding_mul_abs_conj]
    calc
      _ < P⁻¹*(T*(1+(D⁻¹)^2)) :=
        mul_lt_mul hsmall hcT.le (abs_pos.mpr hec0) (by positivity)
      _ = φ*(1+(D⁻¹)^2) := by rw [hTP]; field_simp
      _ ≤ φ*(1+(φ^4)⁻¹) := by nlinarith only [hDinv2, goldenRatio_pos]
      _ < 2 := hφbound
  have hn0 : norm z ≠ 0 := by
    intro hh
    have := embedding_mul_conj z
    rw [hh,Int.cast_zero] at this
    exact (mul_ne_zero he0 hec0) this
  have hn : norm z = 1 ∨ norm z = -1 := by
    have hh : -(2 : ℤ) < norm z ∧ norm z < 2 := by exact_mod_cast (abs_lt.mp hnsmall)
    omega
  obtain ⟨r, hir, hz, hur⟩ := golden_small_unit z i hn hbn hsmall
  have hcoef : l*Nat.fib d = Nat.fib r := by
    have hh := congrArg GoldenInt.b hz
    simp only [hb,conj_b,golden_phi_pow_b_eq_fib_index] at hh
    exact_mod_cast (by linarith only [hh] : (l : ℤ)*(Nat.fib d : ℤ) = Nat.fib r)
  have hdr : d ≤ r := by
    by_contra hh
    have hf := (Nat.fib_lt_fib (by omega : 2 ≤ r)).mpr (show r < d by omega)
    have hg : Nat.fib d ≤ l*Nat.fib d := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hkconj : (k : ℝ) = φ^r+(l : ℝ)*goldenConj^d := by
    have hh := congrArg (fun w => embedding (conj w)) hz
    rw [conj_involutive,map_pow,embedding_phi,hec] at hh
    linarith
  have hr : r = i+1 := by
    by_contra hh
    have hir2 : i+2 ≤ r := by omega
    have hpow : T*φ ≤ φ^r := by
      dsimp [T]
      rw [← pow_succ]
      exact pow_le_pow_right₀ one_lt_goldenRatio.le hir2
    have hkc : φ^r ≤ (k : ℝ)+(l : ℝ)*D⁻¹ := by
      have hh := le_abs_self (-((l : ℝ)*goldenConj^d))
      rw [abs_neg,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),habsψ] at hh
      linarith only [hh, hkconj]
    have hInv : (φ^4)⁻¹ < φ-1 := by
      calc
        _ < φ⁻¹ := inv_strictAnti₀ (by positivity)
          (by simpa using pow_lt_pow_right₀ one_lt_goldenRatio (show 1 < (4 : ℕ) by omega))
        _ = φ-1 := by rw [inv_goldenRatio]; linarith [goldenRatio_add_goldenConj]
    have htotal : (k : ℝ)+(l : ℝ)*D⁻¹ < T*φ := by
      nlinarith only [hkT, hlbound, hDinv2,
        mul_le_mul_of_nonneg_left hDinv2 hT.le, mul_lt_mul_of_pos_left hInv hT]
    linarith only [htotal,hpow,hkc]
  have hjr : j = r+d-1 := by omega
  rcases (Nat.even_or_odd d) with hde | hdo
  · have hdp : goldenConj^d = D⁻¹ := by rw [hψ,hde.neg_pow,inv_pow]
    have hR : (φ^r)⁻¹ ≤ D⁻¹ := inv_anti₀ (by positivity)
      (pow_le_pow_right₀ one_lt_goldenRatio.le hdr)
    have hpsi : goldenConj^r ≤ (φ^r)⁻¹ := by
      calc
        _ ≤ |goldenConj^r| := le_abs_self _
        _ = _ := by rw [hψ,abs_pow,abs_neg,abs_of_pos (by positivity),inv_pow]
    have hlR : goldenConj^r ≤ (l : ℝ)*D⁻¹ := by
      have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
      nlinarith only [hpsi,hR,mul_le_mul_of_nonneg_right hl1 (show 0 ≤ D⁻¹ by positivity)]
    have huψ : (k : ℝ)-(l : ℝ)*D = goldenConj^r := by
      rw [← he,hz,conj_embedding_pow]
    rw [hdp] at hkconj
    have hyge : φ^r ≤ (l : ℝ)*D := by linarith only [hkconj,huψ,hlR]
    have hy : φ^(2*i+1) ≤ (l : ℝ)*φ^j := by
      have hh : φ^r*P = φ^(2*i+1) := by dsimp only [P]; rw [← pow_add,hr]; congr 1; omega
      rw [← hh,hji,pow_add]
      dsimp only [P,D] at hyge ⊢
      nlinarith only [mul_le_mul_of_nonneg_right hyge (pow_pos goldenRatio_pos i).le]
    linarith only [hy,hyhi,hNreal,hLreal]
  · have hpar : (-1 : ℝ)^j = (-1 : ℝ)^r := by
      have he : Even (d-1) := by obtain ⟨t,ht⟩ := hdo; exact ⟨t,by omega⟩
      rw [show j=r+(d-1) by omega,pow_add,he.neg_one_pow,mul_one]
    let ε := (l : ℝ)*(φ^j)⁻¹
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hεφ : ε < φ⁻¹ := by
      have hjpow : φ^j = P*D := by rw [hji,pow_add]
      have hmul : ε*(P*D^2) = (l : ℝ)*D := by dsimp only [ε]; rw [hjpow]; field_simp
      have hp : 0 < P*D^2 := by positivity
      apply (mul_lt_mul_iff_of_pos_right hp).mp
      rw [hmul]
      have htarget : T ≤ φ⁻¹*(P*D^2) := by
        have hh : φ^2 ≤ D^2 := by
          have hD1 : φ ≤ D := by
            simpa using pow_le_pow_right₀ one_lt_goldenRatio.le (by omega : 1 ≤ d)
          nlinarith only [hD1,goldenRatio_pos,hD]
        rw [hTP]
        have heq : φ⁻¹*(P*φ^2)=P*φ := by field_simp
        rw [← heq]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hP.le) (by positivity)
      exact hlD.trans_le htarget
    let H : ℕ := l*lucas j
    have hyH : (l : ℝ)*φ^j = (H : ℝ)-(-1 : ℝ)^r*ε := by
      have hψj : goldenConj^j = (-1 : ℝ)^r*(φ^j)⁻¹ := by rw [hψ,neg_pow,inv_pow,hpar]
      have hh := lucas_real j
      rw [hψj] at hh
      dsimp [H,ε]
      push_cast
      nlinarith only [hh]
    have huP : embedding z*P = (-1 : ℝ)^r*φ⁻¹ := by
      have hcancel : (φ^r)⁻¹*P = φ⁻¹ := by
        rw [hr]
        dsimp only [P]
        rw [pow_succ, mul_inv_rev]
        simp only [mul_assoc, inv_mul_cancel₀ (pow_ne_zero i goldenRatio_ne_zero), mul_one]
      rw [hur, mul_assoc, hcancel]
    have hxH : (k : ℝ)*P = (H : ℝ)+(-1 : ℝ)^r*(φ⁻¹-ε) := by
      have hy : (l : ℝ)*φ^j = (l : ℝ)*D*P := by rw [hji,pow_add]; dsimp [P,D]; ring
      rw [he] at huP
      rw [hy] at hyH
      nlinarith only [huP,hyH]
    have hδ : 0 < φ⁻¹-ε := by linarith
    rcases neg_one_pow_eq_or ℝ r with hs | hs
    · rw [hs] at hxH hyH
      dsimp only [P] at hxH
      have hHN : N < H := by
        exact_mod_cast (by linarith only [hxH,hyH,hxlo,hylo,hδ,hε] : (N : ℝ) < H)
      have hNH : H < N+1 := by
        exact_mod_cast (by linarith only [hxH,hyH,hxhi,hyhi,hδ,hε] : (H : ℝ) < N+1)
      omega
    · rw [hs] at hxH hyH
      dsimp only [P] at hxH
      have hHN : N < H := by
        exact_mod_cast (by linarith only [hxH,hyH,hxlo,hylo,hδ,hε] : (N : ℝ) < H)
      have hNH : H < N+1 := by
        exact_mod_cast (by linarith only [hxH,hyH,hxhi,hyhi,hδ,hε] : (H : ℝ) < N+1)
      omega

/-- At least v occurrences force the Lucas threshold for v. -/
theorem occurrence_lower_bound (N v : ℕ) (hv : 2 ≤ v) (ha : v ≤ a N) :
    lucas (4*v-5) ≤ N := by
  classical
  let s := (Finset.Icc 1 N).filter (fun i => N ∈ row i)
  have hs : v ≤ s.card := ha
  let f : Fin v ↪o ℕ := s.orderEmbOfCardLe hs
  have hm (t : Fin v) : 1 ≤ f t ∧ N ∈ row (f t) := by
    have hh := s.orderEmbOfCardLe_mem hs t
    exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1).1,
      (Finset.mem_filter.mp hh).2⟩
  have hrank : ∀ n (hn : n < v), 2*n+1 ≤ f ⟨n,hn⟩ := by
    intro n
    induction n with
    | zero => intro hn; simpa using (hm ⟨0,hn⟩).1
    | succ n ih =>
      intro hn
      have hn' : n < v := by omega
      have hh := ih hn'
      have hlt : f ⟨n,hn'⟩ < f ⟨n+1,hn⟩ := f.strictMono (by exact Nat.lt_succ_self n)
      have hgap : f ⟨n,hn'⟩ + 2 ≤ f ⟨n+1,hn⟩ := by
        by_contra hgap
        have he : f ⟨n+1,hn⟩ = f ⟨n,hn'⟩+1 := by omega
        have hh2 := (hm ⟨n+1,hn⟩).2
        rw [he] at hh2
        exact rows_consecutive_disjoint _ (hm ⟨n,hn'⟩).1 _ (hm ⟨n,hn'⟩).2 hh2
      omega
  let t : Fin v := ⟨v-2,by omega⟩
  let u : Fin v := ⟨v-1,by omega⟩
  have htu : f t < f u := f.strictMono (by change v-2 < v-1; omega)
  have ht : 2*(v-2)+1 ≤ f t := hrank _ _
  have hb := pair_lower_bound (f t) (f u) N (hm t).1 htu (hm t).2 (hm u).2
  exact (lucas_mono (by omega : 1 ≤ 4*v-5) (by omega : 4*v-5 ≤ 2*f t+1)).trans hb

/-- The odd rows below half the index, together with the index itself, attain v occurrences. -/
theorem lucas_attainment (v : ℕ) (hv : 2 ≤ v) : a (lucas (4*v-5)) = v := by
  classical
  let m := 4*v-5
  have hm3 : 3 ≤ m := by omega
  have hm : Odd m := ⟨2*v-3,by omega⟩
  let s := (Finset.range (v-1)).image (fun t => 2*t+1)
  have hsm : m ∉ s := by
    intro hh
    obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hh
    have ht' := Finset.mem_range.mp ht
    omega
  have hcard : (insert m s).card = v := by
    rw [Finset.card_insert_of_notMem hsm]
    have hinj : Function.Injective (fun t : ℕ => 2*t+1) := by
      intro x y hxy
      change 2*x+1=2*y+1 at hxy
      omega
    dsimp only [s]
    rw [Finset.card_image_of_injective _ hinj,Finset.card_range]
    omega
  have hsub : insert m s ⊆ (Finset.Icc 1 (lucas m)).filter (fun i => lucas m ∈ row i) := by
    intro i hi
    have hmem : lucas m ∈ row i := by
      rcases Finset.mem_insert.mp hi with he | hs
      · rw [he]
        exact lucas_mem_own_row hm (by omega)
      · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
        have ht' := Finset.mem_range.mp ht
        apply lucas_mem_lower_odd_row hm hm3
        · exact ⟨t,rfl⟩
        · omega
        · omega
    have hi1 : 1 ≤ i := by
      rcases Finset.mem_insert.mp hi with he | hs
      · omega
      · obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hs
        omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi1,row_index_le i _ hmem⟩,hmem⟩
  have hlow : v ≤ a (lucas m) := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hhigh : a (lucas m) ≤ v := by
    by_contra hh
    have hnext := occurrence_lower_bound (lucas m) (v+1) (by omega) (by omega)
    have hstrict : lucas m < lucas (4*(v+1)-5) := by
      have hstep := lucas_strict m (by omega)
      have hmono := lucas_mono (by omega : 1 ≤ m+1)
        (by omega : m+1 ≤ 4*(v+1)-5)
      exact hstep.trans_le hmono
    omega
  exact Nat.le_antisymm hhigh hlow

/-- The first value occurring in v rows is the Lucas number with index four v minus five. -/
theorem result : claim := by
  intro v hv
  refine ⟨lucas_attainment v hv, ?_⟩
  intro N hN hlt heq
  have hbound := occurrence_lower_bound N v hv (by omega)
  omega



end D5.S1.Recurrence.KimberlingArray
