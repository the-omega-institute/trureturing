/- GID: D5/S3/Quantum/Matrix/PentagonQuarticTrace
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/PentagonQuarticTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.PosDef]
   utility: none
   digest: A sharp quartic trace certificate for Hermitian pentagon-supported matrices. -/

module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Tactic

/-! Exact quartic trace squares for arbitrary Hermitian matrices supported on a five-cycle. -/

set_option autoImplicit false

@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
namespace D5.S3.Quantum.Matrix.PentagonQuarticTrace

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Mat (n : Type*) := _root_.Matrix n n ℂ

/-- The real part of the ordinary, unnormalized trace. -/
def reTrace (B : Mat n) : ℝ := B.trace.re

/-- The squared Hilbert--Schmidt norm, including empty matrix spaces. -/
def hsSq (B : Mat n) : ℝ := reTrace (Bᴴ * B)

/-- The quadratic Hermitian remainder with the two cyclic neighbours. -/
def remainder (A : Fin 5 → Mat n) (i : Fin 5) : Mat n :=
  A i ^ 2 - (1 / 2 : ℝ) •
    (A i * (A (i + 4) + A (i + 1)) + (A (i + 4) + A (i + 1)) * A i)

/-- The ordered commutator along one cyclic edge. -/
def commutator (A : Fin 5 → Mat n) (i : Fin 5) : Mat n :=
  A i * A (i + 1) - A (i + 1) * A i

private lemma tr_add (B D : Mat n) : reTrace (B + D) = reTrace B + reTrace D := by
  simp [reTrace]
private lemma tr_sub (B D : Mat n) : reTrace (B - D) = reTrace B - reTrace D := by
  simp [reTrace]
private lemma tr_smul (c : ℝ) (B : Mat n) : reTrace (c • B) = c * reTrace B := by
  simp [reTrace, Complex.real_smul]
private lemma tr_zero : reTrace (0 : Mat n) = 0 := by simp [reTrace]
private lemma tr_comm (B D : Mat n) : reTrace (B * D) = reTrace (D * B) := by
  exact congrArg Complex.re (Matrix.trace_mul_comm B D)

private def word (a b c d : Mat n) : ℝ := reTrace (a * (b * (c * d)))

private lemma word_eq (a b c d : Mat n) :
    word a b c d = reTrace (a * (b * (c * d))) := rfl

private lemma word_rot (a b c d : Mat n) : word a b c d = word b c d a := by
  unfold word
  rw [tr_comm a, Matrix.mul_assoc, Matrix.mul_assoc]
private lemma word_rot2 (a b c d : Mat n) : word a b c d = word c d a b := by
  rw [word_rot a b c d, word_rot b c d a]
private lemma word_rot3 (a b c d : Mat n) : word a b c d = word d a b c := by
  rw [word_rot2 a b c d, word_rot c d a b]
private lemma word_zero1 (a b c d : Mat n) (h : a * b = 0) : word a b c d = 0 := by
  simp only [word, ← Matrix.mul_assoc, h, zero_mul, tr_zero]
private lemma word_zero2 (a b c d : Mat n) (h : b * c = 0) : word a b c d = 0 := by
  rw [word_rot]; exact word_zero1 _ _ _ _ h
private lemma word_zero3 (a b c d : Mat n) (h : c * d = 0) : word a b c d = 0 := by
  rw [word_rot2]; exact word_zero1 _ _ _ _ h
private lemma word_zero4 (a b c d : Mat n) (h : d * a = 0) : word a b c d = 0 := by
  rw [word_rot3]; exact word_zero1 _ _ _ _ h

private lemma reverse_zero (a b : Mat n) (ha : a.IsHermitian) (hb : b.IsHermitian)
    (h : a * b = 0) : b * a = 0 := by
  simpa only [Matrix.conjTranspose_mul, ha.eq, hb.eq, Matrix.conjTranspose_zero] using
    congrArg Matrix.conjTranspose h

private lemma hs_nonneg (B : Mat n) : 0 ≤ hsSq B := by
  exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self B).trace_nonneg).1


private def pairing (B D : Mat n) : ℝ := reTrace (Bᴴ * D)

private lemma pairing_comm (B D : Mat n) : pairing B D = pairing D B := by
  have h := congrArg Complex.re (Matrix.trace_conjTranspose (Bᴴ * D))
  simpa [pairing, reTrace, Matrix.conjTranspose_mul] using h.symm
private lemma pairing_add_left (B D E : Mat n) :
    pairing (B + D) E = pairing B E + pairing D E := by
  simp [pairing, Matrix.add_mul, tr_add]
private lemma pairing_add_right (B D E : Mat n) :
    pairing B (D + E) = pairing B D + pairing B E := by
  simp [pairing, Matrix.mul_add, tr_add]
private lemma pairing_sub_left (B D E : Mat n) :
    pairing (B - D) E = pairing B E - pairing D E := by
  simp [pairing, Matrix.sub_mul, tr_sub]
private lemma pairing_sub_right (B D E : Mat n) :
    pairing B (D - E) = pairing B D - pairing B E := by
  simp [pairing, Matrix.mul_sub, tr_sub]
private lemma pairing_smul_left (r : ℝ) (B D : Mat n) :
    pairing (r • B) D = r * pairing B D := by
  simp [pairing, Matrix.smul_mul, tr_smul]
private lemma pairing_smul_right (r : ℝ) (B D : Mat n) :
    pairing B (r • D) = r * pairing B D := by
  simp [pairing, Matrix.mul_smul, tr_smul]

private lemma sum_five {E : Type*} [AddCommMonoid E] (f : Fin 5 → E) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  have h : (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} := by decide
  rw [h]
  simp [add_assoc]

private lemma cyclic_remainder_squares (R : Fin 5 → Mat n) :
    (∑ i, hsSq (R i - R (i + 1))) +
      (1/2 : ℝ) * ∑ i, hsSq (R i - (2 : ℝ) • R (i + 1) + (2 : ℝ) • R (i + 2) - R (i + 3)) =
    7 * (∑ i, pairing (R i) (R i)) - 10 * (∑ i, pairing (R i) (R (i + 1))) +
      3 * ∑ i, pairing (R i) (R (i + 2)) := by
  change (∑ i, pairing (R i - R (i + 1)) (R i - R (i + 1))) +
      (1/2 : ℝ) * ∑ i, pairing (R i - (2 : ℝ) • R (i + 1) + (2 : ℝ) • R (i + 2) - R (i + 3))
        (R i - (2 : ℝ) • R (i + 1) + (2 : ℝ) • R (i + 2) - R (i + 3)) = _
  simp only [sum_five, Fin.reduceAdd,
    pairing_add_left, pairing_add_right, pairing_sub_left, pairing_sub_right,
    pairing_smul_left, pairing_smul_right, pairing_comm]
  ring

private lemma cyclic_commutator_squares (C : Fin 5 → Mat n) :
    (3/4 : ℝ) * (∑ i, hsSq (C i)) +
      (5/8 : ℝ) * (∑ i, hsSq (C i - C (i + 1))) =
    2 * (∑ i, pairing (C i) (C i)) - (5/4 : ℝ) * ∑ i, pairing (C i) (C (i + 1)) := by
  change (3/4 : ℝ) * (∑ i, pairing (C i) (C i)) +
      (5/8 : ℝ) * (∑ i, pairing (C i - C (i + 1)) (C i - C (i + 1))) = _
  simp only [sum_five, Fin.reduceAdd,
    pairing_sub_left, pairing_sub_right, pairing_comm]
  ring

private def totalFourth (A : Fin 5 → Mat n) : ℝ := ∑ i, word (A i) (A i) (A i) (A i)
private def edge31 (A : Fin 5 → Mat n) : ℝ :=
  ∑ i, (word (A i) (A i) (A i) (A (i + 1)) + word (A i) (A (i + 1)) (A (i + 1)) (A (i + 1)))
private def edge22 (A : Fin 5 → Mat n) : ℝ := ∑ i, word (A i) (A i) (A (i + 1)) (A (i + 1))
private def alternating (A : Fin 5 → Mat n) : ℝ := ∑ i, word (A i) (A (i + 1)) (A i) (A (i + 1))
private def starTrace (A : Fin 5 → Mat n) : ℝ := ∑ i, word (A (i + 4)) (A i) (A (i + 1)) (A i)

private lemma zero_products (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    A 0 * A 2 = 0 ∧ A 2 * A 0 = 0 ∧ A 1 * A 3 = 0 ∧ A 3 * A 1 = 0 ∧
    A 2 * A 4 = 0 ∧ A 4 * A 2 = 0 ∧ A 3 * A 0 = 0 ∧ A 0 * A 3 = 0 ∧
    A 4 * A 1 = 0 ∧ A 1 * A 4 = 0 := by
  have h02 : A 0 * A 2 = 0 := hz 0
  have h13 : A 1 * A 3 = 0 := hz 1
  have h24 : A 2 * A 4 = 0 := hz 2
  have h30 : A 3 * A 0 = 0 := hz 3
  have h41 : A 4 * A 1 = 0 := hz 4
  exact ⟨h02, reverse_zero _ _ (hA 0) (hA 2) h02,
    h13, reverse_zero _ _ (hA 1) (hA 3) h13,
    h24, reverse_zero _ _ (hA 2) (hA 4) h24,
    h30, reverse_zero _ _ (hA 3) (hA 0) h30,
    h41, reverse_zero _ _ (hA 4) (hA 1) h41⟩

-- Each use expands one bounded quadratic aggregate, deletes forbidden cyclic
-- words, and collects the remaining real trace classes. Matrix entries stay opaque.
local macro "normalize_pentagon" A:ident hA:ident hz:ident : tactic =>
  `(tactic| (
    obtain ⟨h02, h20, h13, h31, h24, h42, h30, h03, h41, h14⟩ := zero_products $A $hA $hz
    have hstar : ∀ i, (($A) i)ᴴ = ($A) i := fun i => (($hA) i).eq
    simp only [totalFourth, edge31, edge22, alternating, starTrace, sum_five,
      Fin.reduceAdd, pairing, remainder, commutator, pow_two]
    try simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, star_trivial, hstar]
    simp only [mul_add, add_mul, sub_mul, mul_sub, smul_mul_assoc,
      mul_smul_comm, smul_smul, Matrix.mul_assoc, tr_add, tr_sub, tr_smul]
    simp only [← word_eq]
    simp only [word_zero1, word_zero2, word_zero3, word_zero4,
      h02, h20, h13, h31, h24, h42, h30, h03, h41, h14,
      word_rot, word_rot2, word_rot3]
    ring))

private lemma remainder_self (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    (∑ i, pairing (remainder A i) (remainder A i)) =
      totalFourth A - 2 * edge31 A + edge22 A + alternating A + starTrace A := by
  normalize_pentagon A hA hz

private lemma remainder_neighbour (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    (∑ i, pairing (remainder A i) (remainder A (i + 1))) =
      -edge31 A + (3/2 : ℝ) * edge22 A + (1/2 : ℝ) * alternating A + starTrace A := by
  normalize_pentagon A hA hz

private lemma remainder_distance_two (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    (∑ i, pairing (remainder A i) (remainder A (i + 2))) = (1/2 : ℝ) * starTrace A := by
  normalize_pentagon A hA hz

private lemma commutator_self (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    (∑ i, pairing (commutator A i) (commutator A i)) =
      2 * edge22 A - 2 * alternating A := by
  normalize_pentagon A hA hz

private lemma commutator_neighbour (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    (∑ i, pairing (commutator A i) (commutator A (i + 1))) = 2 * starTrace A := by
  normalize_pentagon A hA hz

private lemma power_four (B : Mat n) : B ^ 4 = B * (B * (B * B)) := by
  noncomm_ring

private lemma sum_fourth (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    reTrace ((∑ i, A i)^4) =
      totalFourth A + 4 * edge31 A + 4 * edge22 A + 2 * alternating A + 4 * starTrace A := by
  rw [power_four]
  normalize_pentagon A hA hz

private lemma totalFourth_eq (A : Fin 5 → Mat n) :
    totalFourth A = ∑ i, reTrace (A i ^ 4) := by
  simp only [totalFourth, power_four, word]

/-- The exact four-family sum of Hilbert--Schmidt squares. The only support
condition is the ordered distance-two zero product; Hermiticity supplies its reverse. -/
theorem pentagon_quartic_sos (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    8 * (∑ i, reTrace (A i ^ 4)) - reTrace ((∑ i, A i)^4) =
      (∑ i, hsSq (remainder A i - remainder A (i + 1))) +
      (1/2 : ℝ) * (∑ i, hsSq (remainder A i - (2 : ℝ) • remainder A (i + 1) +
        (2 : ℝ) • remainder A (i + 2) - remainder A (i + 3))) +
      (3/4 : ℝ) * (∑ i, hsSq (commutator A i)) +
      (5/8 : ℝ) * (∑ i, hsSq (commutator A i - commutator A (i + 1))) := by
  have hr := cyclic_remainder_squares (remainder A)
  have hc := cyclic_commutator_squares (commutator A)
  rw [remainder_self A hA hz, remainder_neighbour A hA hz,
    remainder_distance_two A hA hz] at hr
  rw [commutator_self A hA hz, commutator_neighbour A hA hz] at hc
  rw [sum_fourth A hA hz, ← totalFourth_eq]
  linarith

/-- The sharp dimension-independent quartic bound for arbitrary complex Hermitian
pentagon-supported matrices. No positivity, invertibility or rank bound is assumed. -/
theorem pentagon_quartic_trace_le (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    reTrace ((∑ i, A i)^4) ≤ 8 * ∑ i, reTrace (A i ^ 4) := by
  have h := pentagon_quartic_sos A hA hz
  have h0 : 0 ≤ ∑ i, hsSq (remainder A i - remainder A (i + 1)) :=
    Finset.sum_nonneg (fun _ _ => hs_nonneg _)
  have h1 : 0 ≤ ∑ i, hsSq (remainder A i - (2 : ℝ) • remainder A (i + 1) +
      (2 : ℝ) • remainder A (i + 2) - remainder A (i + 3)) :=
    Finset.sum_nonneg (fun _ _ => hs_nonneg _)
  have h2 : 0 ≤ ∑ i, hsSq (commutator A i) :=
    Finset.sum_nonneg (fun _ _ => hs_nonneg _)
  have h3 : 0 ≤ ∑ i, hsSq (commutator A i - commutator A (i + 1)) :=
    Finset.sum_nonneg (fun _ _ => hs_nonneg _)
  linarith

private def sharpTuple (i : Fin 5) : Mat (Fin 1) :=
  if i = 0 ∨ i = 1 then 1 else 0

private lemma sharp_facts :
    (∀ i, (sharpTuple i).IsHermitian) ∧
    (∀ i, sharpTuple i * sharpTuple (i + 2) = 0) ∧
    (∑ i, reTrace (sharpTuple i ^ 4)) = 2 ∧
    reTrace ((∑ i, sharpTuple i)^4) = 16 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [sharpTuple]
  · intro i; fin_cases i <;> norm_num [sharpTuple]
  · rw [sum_five]
    norm_num [sharpTuple, reTrace, Matrix.trace]
  · rw [sum_five]
    norm_num [sharpTuple, reTrace, Matrix.trace]
    rfl

/-- Every smaller coefficient fails already for two equal adjacent scalar matrices. -/
theorem constant_eight_sharp (c : ℝ) (hc : c < 8) :
    ∃ A : Fin 5 → Mat (Fin 1), (∀ i, (A i).IsHermitian) ∧
      (∀ i, A i * A (i + 2) = 0) ∧
      c * (∑ i, reTrace (A i ^ 4)) < reTrace ((∑ i, A i)^4) := by
  obtain ⟨hA, hz, hT, hS⟩ := sharp_facts
  refine ⟨sharpTuple, hA, hz, ?_⟩
  rw [hT, hS]
  linarith

end D5.S3.Quantum.Matrix.PentagonQuarticTrace
