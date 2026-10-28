/- GID: D5/S3/Combinatorics/Circle/TwoSmallProfile
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/TwoSmallProfile
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Two physical small gaps close the alternating doubling profile. -/
module
public import D5.S3.Combinatorics.Circle.ExpandingSourcePath

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
    rw [doubleStep, if_neg h1, if_neg h2] at ht
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
      rw [doubleStep, if_pos (by omega : N < 4 * w (j + 1))] at ht
      constructor <;> nlinarith
    · have he : paritySign j = -1 := by simp [paritySign, hp]
      rw [he] at hsgn heq ⊢
      have hn : w (j + 1) < 0 := by omega
      rw [abs_of_neg hn] at hL
      rw [doubleStep, if_neg (by omega : ¬N < 4 * w (j + 1)),
        if_pos (by omega : 4 * w (j + 1) < -N)] at ht
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

end D5.S3.Combinatorics.Circle.TwoSmallProfile
