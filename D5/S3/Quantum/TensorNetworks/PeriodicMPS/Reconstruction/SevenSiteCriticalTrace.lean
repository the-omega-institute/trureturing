/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalTrace
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalTrace
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteAmbiguity]
   utility: none
   digest: The aligned trace recurrence agrees with the literal word trace and yields the seven-site raw two-site marginal. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteAmbiguity
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Seven-site literal traces and raw Gram entries

The recurrence in the ordered basis (1,A,B,AB) computes the trace-one,
traceless chart. Its split contraction agrees with the actual two-site raw
marginal and bounds the degree and phase of the monomials.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

open Matrix
open UniformMPSExpectedDimensionRefutation (traceWord)

private structure Term where
  coeff : ℤ
  d : ℕ
  k : ℕ
  e : ℕ

private def Term.degree (m : Term) : ℕ := m.d + m.k + m.e
private def Term.phase (m : Term) : ℕ := m.k + 2 * m.e

private abbrev Terms := List Term

private def raiseD (c : ℤ) (s : Terms) : Terms :=
  s.map fun m => { m with coeff := c * m.coeff, d := m.d + 1 }

private def raiseK (s : Terms) : Terms :=
  s.map fun m => { m with k := m.k + 1 }

private def raiseE (s : Terms) : Terms :=
  s.map fun m => { m with coeff := -m.coeff, e := m.e + 1 }

private def scale (c : ℤ) (s : Terms) : Terms :=
  s.map fun m => { m with coeff := c * m.coeff }

private structure NormalForm where
  one : Terms
  a : Terms
  b : Terms
  ab : Terms

/-- Coefficient lists obtained by prepending letters to the word. -/
private def normalForm : List (Fin 2) → NormalForm
  | [] => ⟨[⟨1, 0, 0, 0⟩], [], [], []⟩
  | x :: xs =>
    let f := normalForm xs
    if x = 0 then
      ⟨raiseD (-1) f.a, f.one ++ f.a, raiseD (-1) f.ab, f.b ++ f.ab⟩
    else
      ⟨raiseK f.a ++ raiseE f.b ++ raiseE f.ab,
        scale (-1) (raiseE f.ab),
        f.one ++ f.a ++ raiseK f.ab, scale (-1) f.a⟩

private def traceTerms (word : List (Fin 2)) : Terms :=
  let f := normalForm word
  scale 2 f.one ++ f.a ++ raiseK f.ab

private def Term.eval {R : Type*} [CommRing R] (d k e : R) (m : Term) : R :=
  (m.coeff : R) * d ^ m.d * k ^ m.k * e ^ m.e

private def evalTerms {R : Type*} [CommRing R] (d k e : R) (s : Terms) : R :=
  (s.map (Term.eval d k e)).sum

/-- Literal trace polynomial of a word, with arguments in order (d,k,e). -/
def wordTrace {R : Type*} [CommRing R] (d k e : R) (word : List (Fin 2)) : R :=
  evalTerms d k e (traceTerms word)

section Literal

variable {R : Type*} [CommRing R]

private theorem evalTerms_append (d k e : R) (s t : Terms) :
    evalTerms d k e (s ++ t) = evalTerms d k e s + evalTerms d k e t := by
  simp [evalTerms]

private theorem evalTerms_raiseD (d k e : R) (c : ℤ) (s : Terms) :
    evalTerms d k e (raiseD c s) = (c : R) * d * evalTerms d k e s := by
  induction s with
  | nil => simp [evalTerms, raiseD]
  | cons m s ih =>
    simp only [evalTerms, raiseD, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [Term.eval, Int.cast_mul, pow_succ]
    ring

private theorem evalTerms_raiseK (d k e : R) (s : Terms) :
    evalTerms d k e (raiseK s) = k * evalTerms d k e s := by
  induction s with
  | nil => simp [evalTerms, raiseK]
  | cons m s ih =>
    simp only [evalTerms, raiseK, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [Term.eval, pow_succ]
    ring

private theorem evalTerms_raiseE (d k e : R) (s : Terms) :
    evalTerms d k e (raiseE s) = -e * evalTerms d k e s := by
  induction s with
  | nil => simp [evalTerms, raiseE]
  | cons m s ih =>
    simp only [evalTerms, raiseE, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [Term.eval, Int.cast_neg, pow_succ]
    ring

private theorem evalTerms_scale (d k e : R) (c : ℤ) (s : Terms) :
    evalTerms d k e (scale c s) = (c : R) * evalTerms d k e s := by
  induction s with
  | nil => simp [evalTerms, scale]
  | cons m s ih =>
    simp only [evalTerms, scale, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [Term.eval, Int.cast_mul]
    ring

private abbrev Bond (R : Type*) := Matrix (Fin 2) (Fin 2) R

private theorem square (A : Bond R) :
    A * A = A.trace • A - A.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, diag, det_fin_two] <;> ring

private theorem anticommutator (A B : Bond R) :
    B * A + A * B =
      A.trace • B + B.trace • A + ((A * B).trace - A.trace * B.trace) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, diag] <;> ring

private def realizes (A B : Bond R) (f : NormalForm) : Bond R :=
  let eval := evalTerms A.det (A * B).trace B.det
  eval f.one • 1 + eval f.a • A + eval f.b • B + eval f.ab • (A * B)

private theorem realizes_normalForm (A B : Bond R) (hA : A.trace = 1) (hB : B.trace = 0)
    (w : List (Fin 2)) :
    realizes A B (normalForm w) =
      (w.map fun i => if i = 0 then A else B).prod := by
  have hAA : A * A = A - A.det • 1 := by simpa [hA] using square A
  have hBB : B * B = -(B.det • 1) := by simpa [hB] using square B
  have hBA : B * A = B + (A * B).trace • 1 - A * B := by
    apply eq_sub_of_add_eq
    simpa [hA, hB] using anticommutator A B
  have hAAB : A * (A * B) = A * B - A.det • B := by
    rw [← mul_assoc, hAA, sub_mul, smul_mul_assoc, one_mul]
  have hBAB : B * (A * B) = -(B.det • 1) + (A * B).trace • B + B.det • A := by
    have habb : (A * B) * B = -(B.det • A) := by
      rw [mul_assoc, hBB, mul_neg, mul_smul_comm, mul_one]
    rw [← mul_assoc, hBA, sub_mul, add_mul, habb, hBB, smul_mul_assoc, one_mul]
    rw [sub_neg_eq_add]
  induction w with
  | nil => simp [normalForm, realizes, evalTerms, Term.eval]
  | cons x xs ih =>
    simp only [normalForm, List.map_cons, List.prod_cons, ← ih]
    by_cases hx : x = 0
    · simp only [ite_eq_left hx, realizes, evalTerms_append, evalTerms_raiseD,
        Int.cast_neg, Int.cast_one, neg_one_mul, mul_add, mul_smul_comm, mul_one, hAA, hAAB]
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    · simp only [ite_eq_right hx, realizes, evalTerms_append,
        evalTerms_raiseK, evalTerms_raiseE, evalTerms_scale, Int.cast_neg, Int.cast_one,
        mul_add, mul_smul_comm, mul_one, hBB, hBA, hBAB]
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
        smul_eq_mul]
      ring

/-- The recurrence gives the trace of the actual matrix product over any commutative ring. -/
theorem wordTrace_eq_matrixTrace (A B : Bond R) (hA : A.trace = 1) (hB : B.trace = 0)
    (w : List (Fin 2)) :
    wordTrace A.det (A * B).trace B.det w =
      ((w.map fun i => if i = 0 then A else B).prod).trace := by
  rw [← realizes_normalForm A B hA hB]
  simp [realizes, wordTrace, traceTerms, evalTerms_append, evalTerms_scale, evalTerms_raiseK,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, hA, hB, smul_eq_mul]
  ring

/-- On the trace-one, traceless chart the recurrence agrees with the library's
uniform periodic amplitude. -/
theorem wordTrace_eq_traceWord {n : ℕ} (A : Fin 2 → Bond ℂ)
    (hA : (A 0).trace = 1) (hB : (A 1).trace = 0) (w : Fin n → Fin 2) :
    wordTrace (A 0).det (A 0 * A 1).trace (A 1).det (List.ofFn w) = traceWord 2 2 n A w := by
  rw [wordTrace_eq_matrixTrace _ _ hA hB, traceWord, List.map_ofFn]
  have select (b : Fin 2) : (if b = 0 then A 0 else A 1) = A b := by
    have h : b = 0 ∨ b = 1 := by omega
    rcases h with rfl | rfl
    · rfl
    · exact ite_eq_right (by decide)
  simp only [Function.comp_def, select]

end Literal

/-- Number of occurrences of the second core in a word. -/
private def numB : List (Fin 2) → ℕ
  | [] => 0
  | x :: xs => x.val + numB xs

private def Fits (n b size phase : ℕ) (s : Terms) : Prop :=
  ∀ m ∈ s, 2 * m.degree + size ≤ n ∧ m.phase + phase = b

private theorem fits_append {n b size phase : ℕ} {s t : Terms}
    (hs : Fits n b size phase s) (ht : Fits n b size phase t) :
    Fits n b size phase (s ++ t) := by
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hs m hm
  · exact ht m hm

private theorem fits_map {n b size phase n' b' size' phase' : ℕ} {s : Terms}
    (hs : Fits n b size phase s) (f : Term → Term)
    (hf : ∀ m, 2 * m.degree + size ≤ n → m.phase + phase = b →
        2 * (f m).degree + size' ≤ n' ∧ (f m).phase + phase' = b') :
    Fits n' b' size' phase' (s.map f) := by
  intro m hm
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
  exact hf t (hs t ht).1 (hs t ht).2

private theorem fits_relax {n b size phase n' b' size' phase' : ℕ} {s : Terms}
    (hs : Fits n b size phase s)
    (hf : ∀ m : Term, 2 * m.degree + size ≤ n → m.phase + phase = b →
        2 * m.degree + size' ≤ n' ∧ m.phase + phase' = b') :
    Fits n' b' size' phase' s := by
  intro m hm
  exact hf m (hs m hm).1 (hs m hm).2

private theorem normalForm_fits (w : List (Fin 2)) :
    Fits w.length (numB w) 0 0 (normalForm w).one ∧
    Fits w.length (numB w) 1 0 (normalForm w).a ∧
    Fits w.length (numB w) 1 1 (normalForm w).b ∧
    Fits w.length (numB w) 2 1 (normalForm w).ab := by
  induction w with
  | nil =>
    simp [normalForm, Fits, numB, Term.degree, Term.phase]
  | cons x xs ih =>
    obtain ⟨h1, hA, hB, hAB⟩ := ih
    by_cases hx : x = 0
    · subst x
      simp only [normalForm, List.length_cons, numB, Fin.val_zero, zero_add]
      refine ⟨fits_map hA _ ?_, fits_append (fits_relax h1 ?_) (fits_relax hA ?_),
        fits_map hAB _ ?_, fits_append (fits_relax hB ?_) (fits_relax hAB ?_)⟩ <;>
        intro m hd hp <;> simp only [Term.degree, Term.phase] at * <;> omega
    · have hn : x.val = 1 := by omega
      simp only [normalForm, ite_eq_right hx, List.length_cons, numB, hn]
      simp only [scale, raiseE, List.map_map]
      refine ⟨fits_append (fits_append (fits_map hA _ ?_) (fits_map hB _ ?_))
          (fits_map hAB _ ?_), fits_map hAB _ ?_,
        fits_append (fits_append (fits_relax h1 ?_) (fits_relax hA ?_))
          (fits_map hAB _ ?_), fits_map hA _ ?_⟩ <;>
        intro m hd hp <;> simp only [Term.degree, Term.phase, Function.comp_apply] at * <;> omega

private theorem traceTerms_fits (w : List (Fin 2)) :
    Fits w.length (numB w) 0 0 (traceTerms w) := by
  obtain ⟨h1, hA, _, hAB⟩ := normalForm_fits w
  exact fits_append
    (fits_append (fits_map h1 _ (by intro m hd hp; exact ⟨hd, hp⟩))
      (fits_relax hA (by intro m hd hp; exact ⟨by omega, hp⟩)))
    (fits_map hAB _ (by intro m hd hp; simp only [Term.degree, Term.phase] at *; omega))

open scoped BigOperators

/-- The ordered two-site computational basis. -/
abbrev Pair := Fin 2 × Fin 2

private def joinedWord (p : Pair) (s : Fin 5 → Fin 2) : List (Fin 2) :=
  p.1 :: p.2 :: List.ofFn s

private theorem term_degree (p : Pair) (s : Fin 5 → Fin 2)
    {m : Term} (hm : m ∈ traceTerms (joinedWord p s)) : m.degree ≤ 3 := by
  have h := (traceTerms_fits _ m hm).1
  simp [joinedWord] at h
  omega

private def pairWeight (p : Pair) : ℕ := p.1.val + p.2.val

private theorem pairPhase (p : Pair) (s : Fin 5 → Fin 2) :
    numB (joinedWord p s) = pairWeight p + numB (List.ofFn s) := by
  rcases p with ⟨a,b⟩
  simp only [numB, joinedWord, pairWeight, Nat.add_assoc]

private theorem term_phase (p : Pair) (s : Fin 5 → Fin 2)
    {m : Term} (hm : m ∈ traceTerms (joinedWord p s)) :
    m.phase = pairWeight p + numB (List.ofFn s) := by
  simpa only [Nat.add_zero, pairPhase] using (traceTerms_fits _ m hm).2

/-- Forward and reverse coefficients of a complexified two-site raw Gram entry. -/
def rawGram {R : Type*} [CommRing R] (plus minus : Fin 3 → R) (p q : Pair) : R :=
  ∑ s : Fin 5 → Fin 2,
    wordTrace (plus 0) (plus 1) (plus 2) (joinedWord p s) *
    wordTrace (minus 0) (minus 1) (minus 2) (joinedWord q s)

/-- The three trace invariants in the aligned chart. -/
def alignedInvariants (A : Fin 2 → Bond ℂ) : Fin 3 → ℂ :=
  ![(A 0).det, (A 0 * A 1).trace, (A 1).det]

/-- The split-block contraction gives the literal ket times bra trace contraction. -/
theorem rawGram_eq_traceWord (A B : Fin 2 → Bond ℂ)
    (hA₀ : (A 0).trace = 1) (hA₁ : (A 1).trace = 0)
    (hB₀ : (B 0).trace = 1) (hB₁ : (B 1).trace = 0) (p q : Pair) :
    rawGram (alignedInvariants A) (alignedInvariants B) p q =
      ∑ s : Fin 5 → Fin 2,
        traceWord 2 2 7 A (Fin.cons p.1 (Fin.cons p.2 s)) *
        traceWord 2 2 7 B (Fin.cons q.1 (Fin.cons q.2 s)) := by
  unfold rawGram
  apply Finset.sum_congr rfl
  intro s _
  simp only [alignedInvariants, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  change wordTrace (A 0).det (A 0 * A 1).trace (A 1).det
      (List.ofFn (Fin.cons p.1 (Fin.cons p.2 s))) *
    wordTrace (B 0).det (B 0 * B 1).trace (B 1).det
      (List.ofFn (Fin.cons q.1 (Fin.cons q.2 s))) = _
  rw [wordTrace_eq_traceWord A hA₀ hA₁, wordTrace_eq_traceWord B hB₀ hB₁]

private theorem traceWord_map_star (A : Fin 2 → Bond ℂ) {n : ℕ} (w : Fin n → Fin 2) :
    traceWord 2 2 n (fun j => (A j).map (starRingEnd ℂ)) w =
      star (traceWord 2 2 n A w) := by
  let f : Bond ℂ →+* Bond ℂ := (starRingEnd ℂ).mapMatrix
  change ((List.ofFn fun i => f (A (w i))).prod).trace =
    starRingEnd ℂ ((List.ofFn fun i => A (w i)).prod).trace
  have h : (List.ofFn fun i => f (A (w i))) = (List.ofFn fun i => A (w i)).map f :=
    List.map_ofFn.symm
  rw [h, ← map_list_prod]
  exact (AddMonoidHom.map_trace (starRingEnd ℂ) _).symm

set_option maxHeartbeats 800000 in
/-- On actual cores the split recurrence gives the library's raw two-site marginal. -/
theorem rawGram_eq_rawTwo (A : Fin 2 → Bond ℂ)
    (hA₀ : (A 0).trace = 1) (hA₁ : (A 1).trace = 0) (p q : Pair) :
    rawGram (alignedInvariants A) (star ∘ alignedInvariants A) p q =
      PeriodicMPSTwoSiteAmbiguity.rawTwo A 3 p q := by
  let f : ℂ →+* ℂ := starRingEnd ℂ
  let B : Fin 2 → Bond ℂ := fun i => f.mapMatrix (A i)
  have hBtrace (i : Fin 2) : (B i).trace = f (A i).trace :=
    (AddMonoidHom.map_trace f.toAddMonoidHom _).symm
  have hB₀ : (B 0).trace = 1 := by simp [hBtrace, hA₀]
  have hB₁ : (B 1).trace = 0 := by simp [hBtrace, hA₁]
  have hAB : alignedInvariants B = star ∘ alignedInvariants A := by
    funext i
    fin_cases i
    · change (f.mapMatrix (A 0)).det = f (A 0).det
      exact (RingHom.map_det f _).symm
    · change (f.mapMatrix (A 0) * f.mapMatrix (A 1)).trace = f (A 0 * A 1).trace
      rw [← map_mul]
      exact (AddMonoidHom.map_trace f.toAddMonoidHom _).symm
    · change (f.mapMatrix (A 1)).det = f (A 1).det
      exact (RingHom.map_det f _).symm
  rw [← hAB, rawGram_eq_traceWord A B hA₀ hA₁ hB₀ hB₁]
  unfold PeriodicMPSTwoSiteAmbiguity.rawTwo
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    PeriodicMPSParentIntersection.twoFlattening]
  have prepend (a : Pair) (s : Fin 5 → Fin 2) :
      Fin.append ![a.1, a.2] s = Fin.cons a.1 (Fin.cons a.2 s) := by
    funext i
    fin_cases i <;> rfl
  simp only [prepend]
  apply Finset.sum_congr rfl
  intro s _
  exact congrArg (fun a : ℂ => traceWord 2 2 7 A (Fin.cons p.1 (Fin.cons p.2 s)) * a)
    (traceWord_map_star A (Fin.cons q.1 (Fin.cons q.2 s)))

end D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate
