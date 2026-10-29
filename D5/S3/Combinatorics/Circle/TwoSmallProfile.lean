/- GID: D5/S3/Combinatorics/Circle/TwoSmallProfile
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/TwoSmallProfile
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Two physical small gaps close the alternating doubling profile. -/
module
public import D5.S3.Combinatorics.Circle.ExpandingSourcePath

/-! # Alternating profiles and two-gap period closure -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.TwoSmallProfile
open SourceWidth ExpandingSourcePath

/-- The sign accumulated across a physical arc of LARGE labels. -/
def paritySign (n : ℕ) : ℤ := if n % 2 = 0 then 1 else -1

@[simp] theorem paritySign_zero : paritySign 0 = 1 := rfl

@[simp] theorem paritySign_succ (n : ℕ) : paritySign (n + 1) = -paritySign n := by
  unfold paritySign
  split_ifs <;> omega

@[simp] theorem paritySign_sq (n : ℕ) : paritySign n * paritySign n = 1 := by
  unfold paritySign
  split_ifs <;> norm_num

theorem paritySign_pow (n : ℕ) : paritySign n * (2 : ℤ) ^ n = (-2 : ℤ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [paritySign_succ, pow_succ, pow_succ, ← ih]; ring

/-- A SMALL departure followed by a free number of LARGE steps, with its
actual endpoint and every signed arc value retained. -/
theorem large_gap_profile (Q N : ℤ) (hQ : 2 ≤ Q) (hN : N = 4 * Q - 1)
    (w : ℕ → ℤ) (ell : ℕ)
    (hb : ∀ j ≤ ell + 1, -(2 * Q - 1) ≤ w j ∧ w j ≤ 2 * Q - 1)
    (hs : 0 < w 0 ∧ w 0 < Q)
    (hstep : ∀ j ≤ ell, w (j + 1) = doubleStep N (w j))
    (hlarge : ∀ j, 1 ≤ j → j ≤ ell → Q ≤ |w j|) :
    ∀ j ≤ ell, 0 < paritySign j * w (j + 1) ∧
      3 * w (j + 1) = paritySign j * N + (2 : ℤ) ^ j * (6 * w 0 - N) := by
  intro j hj
  induction j with
  | zero =>
    have ht := hstep 0 (by omega)
    have h1 : ¬N < 4 * w 0 := by omega
    have h2 : ¬4 * w 0 < -N := by omega
    rw [doubleStep, ite_eq_right h1, ite_eq_right h2] at ht
    simp only [paritySign_zero, one_mul, pow_zero]
    constructor <;> omega
  | succ j ih =>
    obtain ⟨hsgn, heq⟩ := ih (by omega)
    obtain ⟨hlo, hhi⟩ := hb (j + 1) (by omega)
    have hL := hlarge (j + 1) (by omega) (by omega)
    have ht := hstep (j + 1) (by omega)
    rw [paritySign_succ, pow_succ]
    by_cases hp : j % 2 = 0
    · have he : paritySign j = 1 := by simp [paritySign, hp]
      rw [he] at hsgn heq ⊢
      simp only [one_mul] at hsgn heq
      rw [abs_of_pos hsgn] at hL
      rw [doubleStep, ite_eq_left (by omega : N < 4 * w (j + 1))] at ht
      constructor <;> nlinarith
    · have he : paritySign j = -1 := by simp [paritySign, hp]
      rw [he] at hsgn heq ⊢
      have hn : w (j + 1) < 0 := by omega
      rw [abs_of_neg hn] at hL
      rw [doubleStep, ite_eq_right (by omega : ¬N < 4 * w (j + 1)),
        ite_eq_left (by omega : 4 * w (j + 1) < -N)] at ht
      constructor <;> nlinarith

/-- The magnitude equation at the endpoint of the same actual arc. -/
theorem large_gap_endpoint (Q N : ℤ) (hQ : 2 ≤ Q) (hN : N = 4 * Q - 1)
    (w : ℕ → ℤ) (ell : ℕ)
    (hb : ∀ j ≤ ell + 1, -(2 * Q - 1) ≤ w j ∧ w j ≤ 2 * Q - 1)
    (hs : 0 < w 0 ∧ w 0 < Q)
    (hstep : ∀ j ≤ ell, w (j + 1) = doubleStep N (w j))
    (hlarge : ∀ j, 1 ≤ j → j ≤ ell → Q ≤ |w j|) :
    0 < paritySign ell * w (ell + 1) ∧
      3 * (paritySign ell * w (ell + 1)) =
        N + (-2 : ℤ) ^ ell * (6 * w 0 - N) := by
  obtain ⟨hp, he⟩ := large_gap_profile Q N hQ hN w ell hb hs hstep hlarge ell (le_refl _)
  refine ⟨hp, ?_⟩
  calc
    3 * (paritySign ell * w (ell + 1)) = paritySign ell * (3 * w (ell + 1)) := by ring
    _ = N + (-2 : ℤ) ^ ell * (6 * w 0 - N) := by
      rw [he, mul_add, ← mul_assoc, paritySign_sq, one_mul,
        ← mul_assoc, paritySign_pow]

/-- Closing both physical gaps fixes both SMALL magnitudes. -/
theorem closing_classifier (Q N C s r A B : ℤ) (hN0 : 0 < N)
    (hN : N = 4 * Q - 1) (hC : C = 2 * Q - 1) (hAB : A * B = Q)
    (hfirst : 3 * r = N + A * (6 * s - N))
    (hsecond : 3 * s = N + B * (6 * r - N)) :
    3 * s = C - B ∧ 3 * r = C - A := by
  have hs : N * (3 * s - (C - B)) = 0 := by
    linear_combination -2 * B * hfirst - hsecond -
      (12 * s - 2 * N) * hAB + 3 * s * hN - N * hC
  have hr : N * (3 * r - (C - A)) = 0 := by
    linear_combination -2 * A * hsecond - hfirst -
      (12 * r - 2 * N) * hAB + 3 * r * hN - N * hC
  have hn : N ≠ 0 := ne_of_gt hN0
  exact ⟨by rcases mul_eq_zero.mp hs with h | h <;> omega,
    by rcases mul_eq_zero.mp hr with h | h <;> omega⟩


/-- The period closes only with gaps of the same parity, and fixes both
magnitudes. The two signed arc formulas are part of the conclusion. -/
theorem cyclic_two_gap_classifier (ell m : ℕ) (Q N C : ℤ)
    (hQ : 2 ≤ Q) (hpow : Q = (2 : ℤ) ^ (ell + m))
    (hN : N = 4 * Q - 1) (hC : C = 2 * Q - 1)
    (w : ℕ → ℤ)
    (hb : ∀ j ≤ ell + m + 2, -C ≤ w j ∧ w j ≤ C)
    (hs : 0 < w 0 ∧ w 0 < Q)
    (hsmall : |w (ell + 1)| < Q)
    (hlarge : ∀ j, 0 < j → j < ell + m + 2 → j ≠ ell + 1 → Q ≤ |w j|)
    (hstep : ∀ j < ell + m + 2, w (j + 1) = doubleStep N (w j))
    (hclose : w (ell + m + 2) = w 0) :
    let r := paritySign ell * w (ell + 1)
    0 < r ∧ ell % 2 = m % 2 ∧
      3 * w 0 = C - (-2 : ℤ) ^ m ∧ 3 * r = C - (-2 : ℤ) ^ ell ∧
      (∀ j ≤ ell, 3 * w (j + 1) =
        paritySign j * N + (2 : ℤ) ^ j * (6 * w 0 - N)) ∧
      (∀ j ≤ m, 3 * (paritySign ell * w (ell + 1 + (j + 1))) =
        paritySign j * N + (2 : ℤ) ^ j * (6 * r - N)) := by
  let r := paritySign ell * w (ell + 1)
  have hg1 := large_gap_profile Q N hQ hN w ell
    (fun j hj => by simpa [← hC] using hb j (by omega)) hs
    (fun j hj => hstep j (by omega))
    (fun j hj he => hlarge j (by omega) (by omega) (by omega))
  obtain ⟨hr, he1⟩ := large_gap_endpoint Q N hQ hN w ell
    (fun j hj => by simpa [← hC] using hb j (by omega)) hs
    (fun j hj => hstep j (by omega))
    (fun j hj he => hlarge j (by omega) (by omega) (by omega))
  change 0 < r at hr
  let v := fun j => paritySign ell * w (ell + 1 + j)
  have hv0 : v 0 = r := by simp [v, r]
  have hvb : ∀ j ≤ m + 1, -(2 * Q - 1) ≤ v j ∧ v j ≤ 2 * Q - 1 := by
    intro j hj
    have hh := hb (ell + 1 + j) (by omega)
    dsimp [v]
    unfold paritySign
    split_ifs <;> simp only [one_mul, neg_one_mul] <;> omega
  have hsmallbounds := abs_lt.mp hsmall
  have hvs : 0 < v 0 ∧ v 0 < Q := by
    rw [hv0]
    refine ⟨hr, ?_⟩
    dsimp [r]
    unfold paritySign
    split_ifs <;> simp only [one_mul, neg_one_mul] <;> omega
  have hvstep : ∀ j ≤ m, v (j + 1) = doubleStep N (v j) := by
    intro j hj
    have ht := hstep (ell + 1 + j) (by omega)
    dsimp [v]
    rw [show ell + 1 + (j + 1) = (ell + 1 + j) + 1 by omega, ht]
    unfold paritySign
    split_ifs <;> simp only [one_mul, neg_one_mul]
    exact (doubleStep_neg (by omega : 0 ≤ N)).symm
  have hvlarge : ∀ j, 1 ≤ j → j ≤ m → Q ≤ |v j| := by
    intro j hj he
    have ht := hlarge (ell + 1 + j) (by omega) (by omega) (by omega)
    dsimp [v]
    unfold paritySign
    split_ifs <;> simpa only [one_mul, neg_one_mul, abs_neg] using ht
  have hg2 := large_gap_profile Q N hQ hN v m hvb hvs hvstep hvlarge
  obtain ⟨hlast, he2⟩ := large_gap_endpoint Q N hQ hN v m hvb hvs hvstep hvlarge
  have hpar : ell % 2 = m % 2 := by
    have he : ell + 1 + (m + 1) = ell + m + 2 := by omega
    dsimp [v] at hlast
    rw [he, hclose] at hlast
    unfold paritySign at hlast
    split_ifs at hlast <;> simp only [one_mul, neg_one_mul, neg_neg] at hlast <;> omega
  have hsign : paritySign m = paritySign ell := by simp [paritySign, hpar]
  have he2' : 3 * w 0 = N + (-2 : ℤ) ^ m * (6 * r - N) := by
    have he : paritySign m * v (m + 1) = w 0 := by
      dsimp [v]
      rw [show ell + 1 + (m + 1) = ell + m + 2 by omega, hclose, hsign,
        ← mul_assoc, paritySign_sq, one_mul]
    rw [he, hv0] at he2
    exact he2
  have hAB : (-2 : ℤ) ^ ell * (-2 : ℤ) ^ m = Q := by
    rw [← paritySign_pow, ← paritySign_pow, hsign]
    calc
      (paritySign ell * (2 : ℤ) ^ ell) * (paritySign ell * (2 : ℤ) ^ m) =
        (paritySign ell * paritySign ell) * ((2 : ℤ) ^ ell * (2 : ℤ) ^ m) := by ring
      _ = Q := by rw [paritySign_sq, one_mul, ← pow_add, ← hpow]
  obtain ⟨hc1, hc2⟩ := closing_classifier Q N C (w 0) r
    ((-2 : ℤ) ^ ell) ((-2 : ℤ) ^ m) (by omega) hN hC hAB he1 he2'
  exact ⟨hr, hpar, hc1, hc2, fun j hj => (hg1 j hj).2,
    fun j hj => by simpa only [v, hv0] using (hg2 j hj).2⟩


end D5.S3.Combinatorics.Circle.TwoSmallProfile
