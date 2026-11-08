/- GID: D5/S3/Quantum/Matrix/PentagonQuinticTrace
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/PentagonQuinticTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.PosDef]
   utility: none
   digest: A sharp fifth-moment certificate for complex PSD matrices with pentagon support. -/

module

public import D5.S3.Quantum.Matrix.PentagonQuarticTrace

/-! Seven rational weighted squares for the fifth moment of a PSD pentagon. -/

set_option autoImplicit false

@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Matrix.PentagonQuarticTrace (Mat reTrace)
namespace D5.S3.Quantum.Matrix.PentagonQuinticTrace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The four even quadratic operators, in the certificate's fixed order. -/
def even (A : Fin 5 → Mat n) (i : Fin 5) : Fin 4 → Mat n :=
  ![(A (i + 4) * A (i + 3)) + (A (i + 1) * A (i + 2)), (A (i + 4)^2 - A (i + 4) * A i) + (A (i + 1)^2 - A (i + 1) * A i),
    (A (i + 4)^2 - A i * A (i + 4)) + (A (i + 1)^2 - A i * A (i + 1)), A i^2 - A (i + 4)^2 - A (i + 1)^2]

/-- The three odd quadratic operators; their product order is significant. -/
def odd (A : Fin 5 → Mat n) (i : Fin 5) : Fin 3 → Mat n :=
  ![(A (i + 4) * A (i + 3)) - (A (i + 1) * A (i + 2)), (A (i + 4)^2 - A (i + 4) * A i) - (A (i + 1)^2 - A (i + 1) * A i), (A (i + 4)^2 - A i * A (i + 4)) - (A (i + 1)^2 - A i * A (i + 1))]

/-- The seven explicit quadratics from the rational LDL factorization. -/
def square (A : Fin 5 → Mat n) (i : Fin 5) : Fin 7 → Mat n :=
  ![even A i 0 - even A i 1 + (7/8 : ℝ) • even A i 2 + (3/2 : ℝ) • even A i 3,
    even A i 1 + (1/6 : ℝ) • even A i 2 + (7/6 : ℝ) • even A i 3,
    even A i 2 + (316/325 : ℝ) • even A i 3, even A i 3,
    odd A i 0 - (1/3 : ℝ) • odd A i 1 + (1/6 : ℝ) • odd A i 2,
    odd A i 1 - (1/2 : ℝ) • odd A i 2, odd A i 2]

/-- The positive rational weights in the same order as `square`. -/
def weight : Fin 7 → ℝ := ![2, 3, 325/96, 4181/1300, 3, 2/3, 1/4]

/-- The actual PSD-weighted trace square, with no square root or inverse. -/
def weightedSquare (a B : Mat n) : ℝ := reTrace (Bᴴ * a * B)

private def pairing (a B C : Mat n) : ℝ := reTrace (Bᴴ * a * C)

private lemma tr_add (B C : Mat n) : reTrace (B+C) = reTrace B + reTrace C := by simp [reTrace]
private lemma tr_sub (B C : Mat n) : reTrace (B-C) = reTrace B - reTrace C := by simp [reTrace]
private lemma tr_smul (r : ℝ) (B : Mat n) : reTrace (r • B) = r * reTrace B := by
  simp [reTrace, Complex.real_smul]
private lemma tr_zero : reTrace (0 : Mat n) = 0 := by simp [reTrace]
private lemma tr_comm (B C : Mat n) : reTrace (B*C) = reTrace (C*B) :=
  congrArg Complex.re (Matrix.trace_mul_comm B C)

private lemma pairing_comm (a B C : Mat n) (ha : a.IsHermitian) :
    pairing a B C = pairing a C B := by
  have h := congrArg Complex.re (Matrix.trace_conjTranspose (Bᴴ * a * C))
  simpa [pairing, reTrace, Matrix.conjTranspose_mul, ha.eq, Matrix.mul_assoc] using h.symm
private lemma pairing_add_left (a B C D : Mat n) :
    pairing a (B+C) D = pairing a B D + pairing a C D := by
  simp [pairing, add_mul, tr_add]
private lemma pairing_add_right (a B C D : Mat n) :
    pairing a B (C+D) = pairing a B C + pairing a B D := by
  simp [pairing, mul_add, tr_add]
private lemma pairing_sub_left (a B C D : Mat n) :
    pairing a (B-C) D = pairing a B D - pairing a C D := by
  simp [pairing, sub_mul, tr_sub]
private lemma pairing_sub_right (a B C D : Mat n) :
    pairing a B (C-D) = pairing a B C - pairing a B D := by
  simp [pairing, mul_sub, tr_sub]
private lemma pairing_smul_left (r : ℝ) (a B C : Mat n) :
    pairing a (r • B) C = r * pairing a B C := by
  simp [pairing, Matrix.smul_mul, tr_smul]
private lemma pairing_smul_right (r : ℝ) (a B C : Mat n) :
    pairing a B (r • C) = r * pairing a B C := by
  simp [pairing, Matrix.mul_smul, tr_smul]

private lemma sum_five {E : Type*} [AddCommMonoid E] (f : Fin 5 → E) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  have h : (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} := by decide
  rw [h]; simp [add_assoc]

private def word (a b c d e : Mat n) : ℝ := reTrace (a * (b * (c * (d * e))))
private lemma word_eq (a b c d e : Mat n) :
    word a b c d e = reTrace (a * (b * (c * (d * e)))) := rfl
private lemma word_rot (a b c d e : Mat n) : word a b c d e = word b c d e a := by
  unfold word; rw [tr_comm a]; simp only [Matrix.mul_assoc]
private lemma word_rot2 (a b c d e : Mat n) : word a b c d e = word c d e a b := by
  rw [word_rot a b c d e, word_rot b c d e a]
private lemma word_rot3 (a b c d e : Mat n) : word a b c d e = word d e a b c := by
  rw [word_rot2 a b c d e, word_rot c d e a b]
private lemma word_rot4 (a b c d e : Mat n) : word a b c d e = word e a b c d := by
  rw [word_rot3 a b c d e, word_rot d e a b c]

-- Adjoint reversal conjugates the complex trace; only its real part is equated.
private lemma word_reverse (A : Fin 5 → Mat n) (hA : ∀ i, (A i).IsHermitian)
    (a b c d e : Fin 5) : word (A a) (A b) (A c) (A d) (A e) =
      word (A e) (A d) (A c) (A b) (A a) := by
  have h := congrArg Complex.re (Matrix.trace_conjTranspose (A a * (A b * (A c * (A d * A e)))))
  have hs : ∀ i, (A i)ᴴ = A i := fun i => (hA i).eq
  simpa [word, reTrace, Matrix.conjTranspose_mul, hs, Matrix.mul_assoc] using h.symm

private lemma word_reverse1 (A : Fin 5 → Mat n) (hA : ∀ i, (A i).IsHermitian)
    (a b c d e : Fin 5) : word (A a) (A b) (A c) (A d) (A e) =
      word (A d) (A c) (A b) (A a) (A e) := by
  rw [word_reverse A hA a b c d e]
  exact word_rot _ _ _ _ _

private lemma word_reverse2 (A : Fin 5 → Mat n) (hA : ∀ i, (A i).IsHermitian)
    (a b c d e : Fin 5) : word (A a) (A b) (A c) (A d) (A e) =
      word (A c) (A b) (A a) (A e) (A d) := by
  rw [word_reverse A hA a b c d e]
  exact word_rot2 _ _ _ _ _

private lemma word_reverse3 (A : Fin 5 → Mat n) (hA : ∀ i, (A i).IsHermitian)
    (a b c d e : Fin 5) : word (A a) (A b) (A c) (A d) (A e) =
      word (A b) (A a) (A e) (A d) (A c) := by
  rw [word_reverse A hA a b c d e]
  exact word_rot3 _ _ _ _ _

private lemma word_reverse4 (A : Fin 5 → Mat n) (hA : ∀ i, (A i).IsHermitian)
    (a b c d e : Fin 5) : word (A a) (A b) (A c) (A d) (A e) =
      word (A a) (A e) (A d) (A c) (A b) := by
  rw [word_reverse A hA a b c d e]
  exact word_rot4 _ _ _ _ _

private lemma word_zero1 (a b c d e : Mat n) (h : a*b=0) : word a b c d e = 0 := by
  simp only [word, ← Matrix.mul_assoc, h, zero_mul, tr_zero]
private lemma word_zero2 (a b c d e : Mat n) (h : b*c=0) : word a b c d e = 0 := by
  rw [word_rot]; exact word_zero1 _ _ _ _ _ h
private lemma word_zero3 (a b c d e : Mat n) (h : c*d=0) : word a b c d e = 0 := by
  rw [word_rot2]; exact word_zero1 _ _ _ _ _ h
private lemma word_zero4 (a b c d e : Mat n) (h : d*e=0) : word a b c d e = 0 := by
  rw [word_rot3]; exact word_zero1 _ _ _ _ _ h
private lemma word_zero5 (a b c d e : Mat n) (h : e*a=0) : word a b c d e = 0 := by
  rw [word_rot4]; exact word_zero1 _ _ _ _ _ h

private lemma reverse_zero (a b : Mat n) (ha : a.IsHermitian) (hb : b.IsHermitian)
    (h : a*b=0) : b*a=0 := by
  simpa only [Matrix.conjTranspose_mul, ha.eq, hb.eq, Matrix.conjTranspose_zero] using
    congrArg Matrix.conjTranspose h
private lemma zero_products (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    A 0 * A 2=0 ∧ A 2 * A 0=0 ∧ A 1 * A 3=0 ∧ A 3 * A 1=0 ∧ A 2 * A 4=0 ∧ A 4 * A 2=0 ∧
    A 3 * A 0=0 ∧ A 0 * A 3=0 ∧ A 4 * A 1=0 ∧ A 1 * A 4=0 := by
  have h02 : A 0 * A 2=0 := hz 0
  have h13 : A 1 * A 3=0 := hz 1
  have h24 : A 2 * A 4=0 := hz 2
  have h30 : A 3 * A 0=0 := hz 3
  have h41 : A 4 * A 1=0 := hz 4
  exact ⟨h02, reverse_zero _ _ (hA 0) (hA 2) h02, h13, reverse_zero _ _ (hA 1) (hA 3) h13,
    h24, reverse_zero _ _ (hA 2) (hA 4) h24, h30, reverse_zero _ _ (hA 3) (hA 0) h30,
    h41, reverse_zero _ _ (hA 4) (hA 1) h41⟩

private def totalFifth (A : Fin 5 → Mat n) : ℝ := ∑ i, word (A i) (A i) (A i) (A i) (A i)
private def edge41 (A : Fin 5 → Mat n) : ℝ := ∑ i,
  (word (A i) (A i) (A i) (A i) (A (i + 1)) + word (A i) (A (i + 1)) (A (i + 1)) (A (i + 1)) (A (i + 1)))

private def edge32 (A : Fin 5 → Mat n) : ℝ := ∑ i,
  (word (A i) (A i) (A i) (A (i + 1)) (A (i + 1)) + word (A i) (A i) (A (i + 1)) (A (i + 1)) (A (i + 1)))

private def alternate (A : Fin 5 → Mat n) : ℝ := ∑ i,
  (word (A i) (A i) (A (i + 1)) (A i) (A (i + 1)) + word (A (i + 1)) (A (i + 1)) (A i) (A (i + 1)) (A i))

private def centre (A : Fin 5 → Mat n) : ℝ := ∑ i,
  word (A i) (A i) (A (i + 1)) (A i) (A (i + 4))
private def leaf (A : Fin 5 → Mat n) : ℝ := ∑ i,
  (word (A (i + 4)) (A (i + 4)) (A i) (A (i + 1)) (A i) +
  word (A (i + 1)) (A (i + 1)) (A i) (A (i + 4)) (A i))

private def cycle (A : Fin 5 → Mat n) : ℝ := word (A 0) (A 1) (A 2) (A 3) (A 4)

-- Each call expands one quadratic Gram entry, never matrix coordinates.
local macro "normalize_pentagon5" A:ident hA:ident hz:ident : tactic =>
  `(tactic| (
    obtain ⟨h02,h20,h13,h31,h24,h42,h30,h03,h41,h14⟩ := zero_products $A $hA $hz
    have hs : ∀ i, (($A) i)ᴴ = ($A) i := fun i => (($hA) i).eq
    simp only [totalFifth, edge41, edge32, alternate, centre, leaf, cycle, sum_five,
      even, odd,
      Matrix.cons_val,
      Fin.reduceAdd, pairing, pow_two]
    try simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hs]
    simp only [mul_add, add_mul, sub_mul, mul_sub, Matrix.mul_assoc, tr_add, tr_sub]
    try simp only [← word_eq]
    simp only [word_zero1,word_zero2,word_zero3,word_zero4,word_zero5,
      h02,h20,h13,h31,h24,h42,h30,h03,h41,h14,
      word_rot,word_rot2,word_rot3,word_rot4,word_reverse $A $hA,
      word_reverse1 $A $hA,word_reverse2 $A $hA,word_reverse3 $A $hA,word_reverse4 $A $hA]
    ring))

private def gramE (A : Fin 5 → Mat n) (j k : Fin 4) : ℝ :=
  ∑ i, pairing (A i) (even A i j) (even A i k)
private def gramO (A : Fin 5 → Mat n) (j k : Fin 3) : ℝ :=
  ∑ i, pairing (A i) (odd A i j) (odd A i k)

private lemma gram_e00 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramE A 0 0 = leaf A + 10 * cycle A := by
  unfold gramE
  normalize_pentagon5 A hA hz

private lemma gram_e01 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramE A 0 1 = 2 * centre A := by
  unfold gramE
  normalize_pentagon5 A hA hz

private lemma gram_e02 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramE A 0 2 = 2 * centre A - leaf A := by
  unfold gramE
  normalize_pentagon5 A hA hz

private lemma gram_e03 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramE A 0 3 = -2 * centre A := by
  unfold gramE
  normalize_pentagon5 A hA hz

private lemma gram_e11 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramE A 1 1 = edge41 A - alternate A + 2 * centre A - 2 * leaf A := by
  unfold gramE
  normalize_pentagon5 A hA hz

private lemma gram_e12 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramE A 1 2 = edge41 A - edge32 A + 2 * centre A - leaf A := by
  unfold gramE
  normalize_pentagon5 A hA hz

private lemma gram_e13 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramE A 1 3 = -2 * edge41 A + edge32 A + alternate A + leaf A := by
  unfold gramE
  normalize_pentagon5 A hA hz

private lemma gram_e22 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramE A 2 2 = edge41 A - edge32 A := by
  unfold gramE
  normalize_pentagon5 A hA hz

private lemma gram_e23 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramE A 2 3 = -2 * edge41 A + 2 * edge32 A := by
  unfold gramE
  normalize_pentagon5 A hA hz

private lemma gram_e33 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramE A 3 3 = totalFifth A + edge41 A - 2 * edge32 A := by
  unfold gramE
  normalize_pentagon5 A hA hz

private lemma gram_o00 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramO A 0 0 = leaf A - 10 * cycle A := by
  unfold gramO
  normalize_pentagon5 A hA hz

private lemma gram_o01 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramO A 0 1 = 2 * centre A := by
  unfold gramO
  normalize_pentagon5 A hA hz

private lemma gram_o02 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramO A 0 2 = 2 * centre A - leaf A := by
  unfold gramO
  normalize_pentagon5 A hA hz

private lemma gram_o11 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramO A 1 1 = edge41 A - alternate A - 2 * centre A + 2 * leaf A := by
  unfold gramO
  normalize_pentagon5 A hA hz

private lemma gram_o12 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramO A 1 2 = edge41 A - edge32 A - 2 * centre A + leaf A := by
  unfold gramO
  normalize_pentagon5 A hA hz

private lemma gram_o22 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    gramO A 2 2 = edge41 A - edge32 A := by
  unfold gramO
  normalize_pentagon5 A hA hz

private lemma power_five (B : Mat n) : B^5 = B * (B * (B * (B * B))) := by
  noncomm_ring

-- Fixing the first factor bounds each expansion to 5^4 ordered words.
-- The displayed survivors retain cyclic orientation; adjoint reversal is a separate proved rule.
private def row (A : Fin 5 → Mat n) (i : Fin 5) : ℝ :=
  reTrace (A i * ((∑ j, A j) * ((∑ j, A j) * ((∑ j, A j) * (∑ j, A j)))))

private def row0 (A : Fin 5 → Mat n) : ℝ :=
  word (A 0) (A 0) (A 0) (A 0) (A 0) +
  4 * word (A 0) (A 0) (A 0) (A 0) (A 1) +
  4 * word (A 0) (A 0) (A 0) (A 0) (A 4) +
  3 * word (A 0) (A 0) (A 0) (A 1) (A 1) +
  3 * word (A 0) (A 0) (A 0) (A 4) (A 4) +
  3 * word (A 0) (A 0) (A 1) (A 0) (A 1) +
  3 * word (A 0) (A 0) (A 1) (A 0) (A 4) +
  2 * word (A 0) (A 0) (A 1) (A 1) (A 1) +
  2 * word (A 0) (A 0) (A 1) (A 2) (A 1) +
  3 * word (A 0) (A 0) (A 4) (A 0) (A 1) +
  3 * word (A 0) (A 0) (A 4) (A 0) (A 4) +
  2 * word (A 0) (A 0) (A 4) (A 3) (A 4) +
  2 * word (A 0) (A 0) (A 4) (A 4) (A 4) +
  2 * word (A 0) (A 1) (A 0) (A 1) (A 1) +
  2 * word (A 0) (A 1) (A 0) (A 4) (A 4) +
  2 * word (A 0) (A 1) (A 1) (A 0) (A 4) +
  word (A 0) (A 1) (A 1) (A 1) (A 1) +
  word (A 0) (A 1) (A 1) (A 2) (A 1) +
  word (A 0) (A 1) (A 2) (A 1) (A 1) +
  word (A 0) (A 1) (A 2) (A 2) (A 1) +
  word (A 0) (A 1) (A 2) (A 3) (A 4) +
  2 * word (A 0) (A 4) (A 0) (A 4) (A 4) +
  word (A 0) (A 4) (A 3) (A 2) (A 1) +
  word (A 0) (A 4) (A 3) (A 3) (A 4) +
  word (A 0) (A 4) (A 3) (A 4) (A 4) +
  word (A 0) (A 4) (A 4) (A 3) (A 4) +
  word (A 0) (A 4) (A 4) (A 4) (A 4)

private lemma row_0 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    row A 0 = row0 A := by
  unfold row row0
  normalize_pentagon5 A hA hz

private def row1 (A : Fin 5 → Mat n) : ℝ :=
  word (A 0) (A 0) (A 0) (A 0) (A 1) +
  2 * word (A 0) (A 0) (A 0) (A 1) (A 1) +
  2 * word (A 0) (A 0) (A 1) (A 0) (A 1) +
  word (A 0) (A 0) (A 1) (A 0) (A 4) +
  3 * word (A 0) (A 0) (A 1) (A 1) (A 1) +
  2 * word (A 0) (A 0) (A 1) (A 2) (A 1) +
  word (A 0) (A 0) (A 4) (A 0) (A 1) +
  3 * word (A 0) (A 1) (A 0) (A 1) (A 1) +
  word (A 0) (A 1) (A 0) (A 4) (A 4) +
  2 * word (A 0) (A 1) (A 1) (A 0) (A 4) +
  4 * word (A 0) (A 1) (A 1) (A 1) (A 1) +
  3 * word (A 0) (A 1) (A 1) (A 2) (A 1) +
  3 * word (A 0) (A 1) (A 2) (A 1) (A 1) +
  2 * word (A 0) (A 1) (A 2) (A 2) (A 1) +
  word (A 0) (A 1) (A 2) (A 3) (A 4) +
  word (A 0) (A 4) (A 3) (A 2) (A 1) +
  word (A 1) (A 1) (A 1) (A 1) (A 1) +
  4 * word (A 1) (A 1) (A 1) (A 1) (A 2) +
  3 * word (A 1) (A 1) (A 1) (A 2) (A 2) +
  3 * word (A 1) (A 1) (A 2) (A 1) (A 2) +
  2 * word (A 1) (A 1) (A 2) (A 2) (A 2) +
  2 * word (A 1) (A 1) (A 2) (A 3) (A 2) +
  2 * word (A 1) (A 2) (A 1) (A 2) (A 2) +
  word (A 1) (A 2) (A 2) (A 2) (A 2) +
  word (A 1) (A 2) (A 2) (A 3) (A 2) +
  word (A 1) (A 2) (A 3) (A 2) (A 2) +
  word (A 1) (A 2) (A 3) (A 3) (A 2)

private lemma row_1 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    row A 1 = row1 A := by
  unfold row row1
  normalize_pentagon5 A hA hz

private def row2 (A : Fin 5 → Mat n) : ℝ :=
  word (A 0) (A 0) (A 1) (A 2) (A 1) +
  word (A 0) (A 1) (A 1) (A 2) (A 1) +
  word (A 0) (A 1) (A 2) (A 1) (A 1) +
  2 * word (A 0) (A 1) (A 2) (A 2) (A 1) +
  word (A 0) (A 1) (A 2) (A 3) (A 4) +
  word (A 0) (A 4) (A 3) (A 2) (A 1) +
  word (A 1) (A 1) (A 1) (A 1) (A 2) +
  2 * word (A 1) (A 1) (A 1) (A 2) (A 2) +
  2 * word (A 1) (A 1) (A 2) (A 1) (A 2) +
  3 * word (A 1) (A 1) (A 2) (A 2) (A 2) +
  2 * word (A 1) (A 1) (A 2) (A 3) (A 2) +
  3 * word (A 1) (A 2) (A 1) (A 2) (A 2) +
  4 * word (A 1) (A 2) (A 2) (A 2) (A 2) +
  3 * word (A 1) (A 2) (A 2) (A 3) (A 2) +
  3 * word (A 1) (A 2) (A 3) (A 2) (A 2) +
  2 * word (A 1) (A 2) (A 3) (A 3) (A 2) +
  word (A 2) (A 2) (A 2) (A 2) (A 2) +
  4 * word (A 2) (A 2) (A 2) (A 2) (A 3) +
  3 * word (A 2) (A 2) (A 2) (A 3) (A 3) +
  3 * word (A 2) (A 2) (A 3) (A 2) (A 3) +
  2 * word (A 2) (A 2) (A 3) (A 3) (A 3) +
  2 * word (A 2) (A 2) (A 3) (A 4) (A 3) +
  2 * word (A 2) (A 3) (A 2) (A 3) (A 3) +
  word (A 2) (A 3) (A 3) (A 3) (A 3) +
  word (A 2) (A 3) (A 3) (A 4) (A 3) +
  word (A 2) (A 3) (A 4) (A 3) (A 3) +
  word (A 2) (A 3) (A 4) (A 4) (A 3)

private lemma row_2 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    row A 2 = row2 A := by
  unfold row row2
  normalize_pentagon5 A hA hz

private def row3 (A : Fin 5 → Mat n) : ℝ :=
  word (A 0) (A 0) (A 4) (A 3) (A 4) +
  word (A 0) (A 1) (A 2) (A 3) (A 4) +
  word (A 0) (A 4) (A 3) (A 2) (A 1) +
  2 * word (A 0) (A 4) (A 3) (A 3) (A 4) +
  word (A 0) (A 4) (A 3) (A 4) (A 4) +
  word (A 0) (A 4) (A 4) (A 3) (A 4) +
  word (A 1) (A 1) (A 2) (A 3) (A 2) +
  word (A 1) (A 2) (A 2) (A 3) (A 2) +
  word (A 1) (A 2) (A 3) (A 2) (A 2) +
  2 * word (A 1) (A 2) (A 3) (A 3) (A 2) +
  word (A 2) (A 2) (A 2) (A 2) (A 3) +
  2 * word (A 2) (A 2) (A 2) (A 3) (A 3) +
  2 * word (A 2) (A 2) (A 3) (A 2) (A 3) +
  3 * word (A 2) (A 2) (A 3) (A 3) (A 3) +
  2 * word (A 2) (A 2) (A 3) (A 4) (A 3) +
  3 * word (A 2) (A 3) (A 2) (A 3) (A 3) +
  4 * word (A 2) (A 3) (A 3) (A 3) (A 3) +
  3 * word (A 2) (A 3) (A 3) (A 4) (A 3) +
  3 * word (A 2) (A 3) (A 4) (A 3) (A 3) +
  2 * word (A 2) (A 3) (A 4) (A 4) (A 3) +
  word (A 3) (A 3) (A 3) (A 3) (A 3) +
  4 * word (A 3) (A 3) (A 3) (A 3) (A 4) +
  3 * word (A 3) (A 3) (A 3) (A 4) (A 4) +
  3 * word (A 3) (A 3) (A 4) (A 3) (A 4) +
  2 * word (A 3) (A 3) (A 4) (A 4) (A 4) +
  2 * word (A 3) (A 4) (A 3) (A 4) (A 4) +
  word (A 3) (A 4) (A 4) (A 4) (A 4)

private lemma row_3 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    row A 3 = row3 A := by
  unfold row row3
  normalize_pentagon5 A hA hz

private def row4 (A : Fin 5 → Mat n) : ℝ :=
  word (A 0) (A 0) (A 0) (A 0) (A 4) +
  2 * word (A 0) (A 0) (A 0) (A 4) (A 4) +
  word (A 0) (A 0) (A 1) (A 0) (A 4) +
  word (A 0) (A 0) (A 4) (A 0) (A 1) +
  2 * word (A 0) (A 0) (A 4) (A 0) (A 4) +
  2 * word (A 0) (A 0) (A 4) (A 3) (A 4) +
  3 * word (A 0) (A 0) (A 4) (A 4) (A 4) +
  2 * word (A 0) (A 1) (A 0) (A 4) (A 4) +
  word (A 0) (A 1) (A 1) (A 0) (A 4) +
  word (A 0) (A 1) (A 2) (A 3) (A 4) +
  3 * word (A 0) (A 4) (A 0) (A 4) (A 4) +
  word (A 0) (A 4) (A 3) (A 2) (A 1) +
  2 * word (A 0) (A 4) (A 3) (A 3) (A 4) +
  3 * word (A 0) (A 4) (A 3) (A 4) (A 4) +
  3 * word (A 0) (A 4) (A 4) (A 3) (A 4) +
  4 * word (A 0) (A 4) (A 4) (A 4) (A 4) +
  word (A 2) (A 2) (A 3) (A 4) (A 3) +
  word (A 2) (A 3) (A 3) (A 4) (A 3) +
  word (A 2) (A 3) (A 4) (A 3) (A 3) +
  2 * word (A 2) (A 3) (A 4) (A 4) (A 3) +
  word (A 3) (A 3) (A 3) (A 3) (A 4) +
  2 * word (A 3) (A 3) (A 3) (A 4) (A 4) +
  2 * word (A 3) (A 3) (A 4) (A 3) (A 4) +
  3 * word (A 3) (A 3) (A 4) (A 4) (A 4) +
  3 * word (A 3) (A 4) (A 3) (A 4) (A 4) +
  4 * word (A 3) (A 4) (A 4) (A 4) (A 4) +
  word (A 4) (A 4) (A 4) (A 4) (A 4)

private lemma row_4 (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    row A 4 = row4 A := by
  unfold row row4
  normalize_pentagon5 A hA hz

private lemma sum_fifth (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    reTrace ((∑ i, A i)^5) = totalFifth A + 5 * edge41 A + 5 * edge32 A +
      5 * alternate A + 10 * centre A + 5 * leaf A + 10 * cycle A := by
  have split : reTrace ((∑ i, A i)^5) = ∑ i, row A i := by
    rw [power_five, Matrix.sum_mul, reTrace, Matrix.trace_sum, Complex.re_sum]
    rfl
  rw [split, sum_five, row_0 A hA hz, row_1 A hA hz, row_2 A hA hz,
    row_3 A hA hz, row_4 A hA hz]
  unfold row0 row1 row2 row3 row4
  normalize_pentagon5 A hA hz

private lemma totalFifth_eq (A : Fin 5 → Mat n) : totalFifth A = ∑ i, reTrace (A i^5) := by
  simp only [totalFifth, power_five, word]

private lemma sum_seven {E : Type*} [AddCommMonoid E] (f : Fin 7 → E) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  have h : (Finset.univ : Finset (Fin 7)) = {0,1,2,3,4,5,6} := by decide
  rw [h]; simp [add_assoc]

private lemma ldl_at (A : Fin 5 → Mat n) (hA : ∀ i, (A i).IsHermitian) (i : Fin 5) :
    (∑ k, weight k * weightedSquare (A i) (square A i k)) =
      2 * pairing (A i) (even A i 0) (even A i 0) +
      5 * pairing (A i) (even A i 1) (even A i 1) +
      5 * pairing (A i) (even A i 2) (even A i 2) +
      15 * pairing (A i) (even A i 3) (even A i 3) -
      4 * pairing (A i) (even A i 0) (even A i 1) +
      (7/2 : ℝ) * pairing (A i) (even A i 0) (even A i 2) +
      6 * pairing (A i) (even A i 0) (even A i 3) -
      (5/2 : ℝ) * pairing (A i) (even A i 1) (even A i 2) +
      pairing (A i) (even A i 1) (even A i 3) +
      13 * pairing (A i) (even A i 2) (even A i 3) +
      3 * pairing (A i) (odd A i 0) (odd A i 0) +
      pairing (A i) (odd A i 1) (odd A i 1) +
      (1/2 : ℝ) * pairing (A i) (odd A i 2) (odd A i 2) -
      2 * pairing (A i) (odd A i 0) (odd A i 1) +
      pairing (A i) (odd A i 0) (odd A i 2) -
      pairing (A i) (odd A i 1) (odd A i 2) := by
  change (∑ k, weight k * pairing (A i) (square A i k) (square A i k)) = _
  simp only [sum_seven, square, weight, Matrix.cons_val, pairing_add_left, pairing_add_right,
    pairing_sub_left, pairing_sub_right, pairing_smul_left, pairing_smul_right,
    pairing_comm (A i) _ _ (hA i)]
  ring

private lemma certificate_sum (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    (∑ i, ∑ k, weight k * weightedSquare (A i) (square A i k)) =
      15 * totalFifth A - 5 * edge41 A - 5 * edge32 A -
      5 * alternate A - 10 * centre A - 5 * leaf A - 10 * cycle A := by
  simp_rw [ldl_at A hA]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ]
  change 2 * gramE A 0 0 + 5 * gramE A 1 1 + 5 * gramE A 2 2 +
    15 * gramE A 3 3 - 4 * gramE A 0 1 + (7/2 : ℝ) * gramE A 0 2 +
    6 * gramE A 0 3 - (5/2 : ℝ) * gramE A 1 2 + gramE A 1 3 +
    13 * gramE A 2 3 + 3 * gramO A 0 0 + gramO A 1 1 +
    (1/2 : ℝ) * gramO A 2 2 - 2 * gramO A 0 1 + gramO A 0 2 - gramO A 1 2 = _
  rw [gram_e00 A hA hz, gram_e01 A hA hz, gram_e02 A hA hz, gram_e03 A hA hz,
    gram_e11 A hA hz, gram_e12 A hA hz, gram_e13 A hA hz, gram_e22 A hA hz,
    gram_e23 A hA hz, gram_e33 A hA hz, gram_o00 A hA hz, gram_o01 A hA hz,
    gram_o02 A hA hz, gram_o11 A hA hz, gram_o12 A hA hz, gram_o22 A hA hz]
  ring

/-- The exact seven-square identity. Hermiticity suffices for the identity;
positive semidefiniteness is essential for its nonnegative-square consequence. -/
theorem pentagon_quintic_sos (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).IsHermitian) (hz : ∀ i, A i * A (i + 2) = 0) :
    16 * (∑ i, reTrace (A i^5)) - reTrace ((∑ i, A i)^5) =
      ∑ i, ∑ k, weight k * weightedSquare (A i) (square A i k) := by
  rw [certificate_sum A hA hz, sum_fifth A hA hz, ← totalFifth_eq]
  ring

/-- The universal sharp fifth-moment inequality for finite complex PSD matrices
with distance-two zero products. Empty dimensions and singular matrices are included. -/
theorem pentagon_quintic_trace_le (A : Fin 5 → Mat n)
    (hA : ∀ i, (A i).PosSemidef) (hz : ∀ i, A i * A (i + 2) = 0) :
    reTrace ((∑ i, A i)^5) ≤ 16 * ∑ i, reTrace (A i^5) := by
  have h := pentagon_quintic_sos A (fun i => (hA i).isHermitian) hz
  have hn : 0 ≤ ∑ i, ∑ k, weight k * weightedSquare (A i) (square A i k) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg
    · fin_cases k <;> norm_num [weight]
    · exact (Complex.nonneg_iff.mp
        ((hA i).conjTranspose_mul_mul_same (square A i k)).trace_nonneg).1
  linarith

private def sharpTuple (i : Fin 5) : Mat (Fin 1) := if i=0 ∨ i=1 then 1 else 0
private lemma sharp_facts :
    (∀ i, (sharpTuple i).PosSemidef) ∧
    (∀ i, sharpTuple i * sharpTuple (i + 2) = 0) ∧
    (∑ i, reTrace (sharpTuple i^5)) = 2 ∧ reTrace ((∑ i, sharpTuple i)^5) = 32 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp only [sharpTuple, Fin.isValue, zero_ne_one,
      one_ne_zero, or_self, if_true, if_false] <;>
      first | exact Matrix.PosSemidef.one | exact Matrix.PosSemidef.zero
  · intro i; fin_cases i <;> norm_num [sharpTuple]
  · rw [sum_five]; norm_num [sharpTuple, reTrace, Matrix.trace]
  · rw [sum_five]; norm_num [sharpTuple, reTrace, Matrix.trace]; rfl

/-- Any coefficient below sixteen fails already for two equal adjacent scalar PSD matrices. -/
theorem constant_sixteen_sharp (c : ℝ) (hc : c<16) :
    ∃ A : Fin 5 → Mat (Fin 1), (∀ i, (A i).PosSemidef) ∧
      (∀ i, A i * A (i + 2) = 0) ∧
      c * (∑ i, reTrace (A i^5)) < reTrace ((∑ i, A i)^5) := by
  obtain ⟨hA,hz,hT,hS⟩ := sharp_facts
  refine ⟨sharpTuple,hA,hz,?_⟩
  rw [hT,hS]; linarith

end D5.S3.Quantum.Matrix.PentagonQuinticTrace
