/- GID: D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.claim; result=D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.result; claim=D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.claim
   digest: Word-trace domination fails to order Schatten norms at exponent three halves. -/

import D5.S3.Quantum.Schatten.Holder
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Observer.Hankel.WordHankelRealization

/-! A diagonal counterexample to word-trace control of fractional Schatten norms. -/

set_option linter.style.longLine false
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open D5.S3.Observer.Hankel.WordHankelRealization (wordProduct)
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Schatten.FractionalSchattenAlignmentRefutation

def claim : Prop :=
  ∀ (m : ℕ) (a₀ a₁ b₀ b₁ : Matrix (Fin m) (Fin m) ℂ),
    a₀.PosSemidef → a₁.PosSemidef → b₀.PosSemidef → b₁.PosSemidef →
    a₀.charpoly = b₀.charpoly → a₁.charpoly = b₁.charpoly →
    (∀ s : List Bool, (wordProduct (fun b : Bool => if b then a₁ else a₀) s).trace.im = 0 ∧
      ‖(wordProduct (fun b : Bool => if b then b₁ else b₀) s).trace‖ ≤
        (wordProduct (fun b : Bool => if b then a₁ else a₀) s).trace.re) →
    ∀ p : ℝ, 1 ≤ p → schattenNorm (b₀ + b₁) p ≤ schattenNorm (a₀ + a₁) p

private def a₀ : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![0, 1, 1, 2]
private def a₁ : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![1, 0, 1, 2]
private def b₁ : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![0, 1, 2, 1]

lemma word_diagonal {m : ℕ} (d₀ d₁ : Fin m → ℂ) (s : List Bool) :
    wordProduct (fun b : Bool => if b then diagonal d₁ else diagonal d₀) s =
      diagonal (fun k => d₀ k ^ s.count false * d₁ k ^ s.count true) := by
  induction s with
  | nil =>
    change (1 : Matrix (Fin m) (Fin m) ℂ) =
      diagonal (fun k => d₀ k ^ 0 * d₁ k ^ 0)
    simp [diagonal_one]
  | cons b s ih =>
    change (if b then diagonal d₁ else diagonal d₀) *
      wordProduct (fun b : Bool => if b then diagonal d₁ else diagonal d₀) s = _
    rw [ih]
    cases b <;>
      simp only [Bool.false_eq_true, reduceIte, diagonal_mul_diagonal] <;>
      congr 1 <;> funext k <;> simp [pow_succ] <;> ring

private lemma trace_forms (s : List Bool) :
    (wordProduct (fun b : Bool => if b then a₁ else a₀) s).trace =
      ((0 ^ s.count false + 0 ^ s.count true + 1 + 2 ^ (s.count false + s.count true) : ℕ) : ℂ) ∧
    (wordProduct (fun b : Bool => if b then b₁ else a₀) s).trace =
      ((0 ^ (s.count false + s.count true) + 1 + 2 ^ s.count false +
        2 ^ s.count true : ℕ) : ℂ) := by
  constructor <;>
    simp [a₀, a₁, b₁, word_diagonal, trace_diagonal, Fin.sum_univ_succ,
      -List.count_false_add_count_true, pow_add] <;> ring

private lemma nat_gap (m n : ℕ) :
    0 ^ (m + n) + 1 + 2 ^ m + 2 ^ n ≤ 0 ^ m + 0 ^ n + 1 + 2 ^ (m + n) := by
  cases m with
  | zero => simp
  | succ m =>
    cases n with
    | zero => simp
    | succ n =>
      have hm : 2 ≤ (2 : ℕ) ^ (m + 1) := le_self_pow₀ (by decide) (Nat.succ_ne_zero m)
      have hn : 2 ≤ (2 : ℕ) ^ (n + 1) := le_self_pow₀ (by decide) (Nat.succ_ne_zero n)
      simpa [pow_add, Nat.add_assoc, Nat.mul_assoc] using Nat.add_le_add_left (add_le_mul hm hn) 1

private lemma witness_psd : a₀.PosSemidef ∧ a₁.PosSemidef ∧ b₁.PosSemidef := by
  refine ⟨PosSemidef.diagonal ?_, PosSemidef.diagonal ?_, PosSemidef.diagonal ?_⟩ <;>
    intro k <;> fin_cases k <;> norm_num

private lemma witness_spectra : a₁.charpoly = b₁.charpoly := by
  simp only [a₁, b₁, charpoly_diagonal, Fin.prod_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one]
  ring

private lemma word_bounds (s : List Bool) :
    (wordProduct (fun b : Bool => if b then a₁ else a₀) s).trace.im = 0 ∧
      ‖(wordProduct (fun b : Bool => if b then b₁ else a₀) s).trace‖ ≤
        (wordProduct (fun b : Bool => if b then a₁ else a₀) s).trace.re := by
  obtain ⟨ha, hb⟩ := trace_forms s
  rw [ha, hb]
  constructor
  · exact Complex.natCast_im _
  · simpa only [Complex.norm_natCast, Complex.natCast_re] using
      (Nat.cast_le (α := ℝ)).mpr (nat_gap (s.count false) (s.count true))

lemma norm_diagonal {m : ℕ} (d : Fin m → ℝ) (hd : ∀ k, 0 ≤ d k) (p : ℝ) :
    schattenNorm (diagonal (fun k => (d k : ℂ))) p = (∑ k, d k ^ p) ^ (1 / p) := by
  have hg : (diagonal (fun k => (d k : ℂ))).conjTranspose *
      (diagonal (fun k => (d k : ℂ))).conjTranspose.conjTranspose =
      diagonal (fun k => ((d k ^ 2 : ℝ) : ℂ)) := by
    simp [diagonal_mul_diagonal, pow_two]
  unfold schattenNorm
  rw [← Matrix.IsHermitian.cfc_eq, hg,
    D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal,
    trace_diagonal]
  congr 1
  simp only [map_sum, RCLike.re_to_complex, Complex.ofReal_re]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Real.rpow_natCast, ← Real.rpow_mul (hd k)]
  congr 1
  ring

private lemma norm_reverse : schattenNorm (a₀ + a₁) (3 / 2) <
    schattenNorm (a₀ + b₁) (3 / 2) := by
  have ha : a₀ + a₁ = diagonal (fun k => ((![1, 1, 2, 4] : Fin 4 → ℝ) k : ℂ)) := by
    rw [a₀, a₁, diagonal_add]
    congr 1
    funext k
    fin_cases k <;> norm_num
  have hb : a₀ + b₁ = diagonal (fun k => ((![0, 2, 3, 3] : Fin 4 → ℝ) k : ℂ)) := by
    rw [a₀, b₁, diagonal_add]
    congr 1
    funext k
    fin_cases k <;> norm_num
  have hda : ∀ k, 0 ≤ (![1, 1, 2, 4] : Fin 4 → ℝ) k := by
    intro k
    fin_cases k <;> norm_num
  have hdb : ∀ k, 0 ≤ (![0, 2, 3, 3] : Fin 4 → ℝ) k := by
    intro k
    fin_cases k <;> norm_num
  rw [ha, hb, norm_diagonal _ hda, norm_diagonal _ hdb]
  apply Real.rpow_lt_rpow
    (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hda k) _) ?_ (by norm_num)
  have hfour : (4 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
    calc
      (4 : ℝ) ^ (3 / 2 : ℝ) = ((2 : ℝ) ^ 2) ^ (3 / 2 : ℝ) := by norm_num
      _ = (2 : ℝ) ^ ((2 : ℝ) * (3 / 2 : ℝ)) :=
        (Real.rpow_natCast_mul (by norm_num) 2 (3 / 2)).symm
      _ = 8 := by norm_num
  have hthree : (3 : ℝ) ^ (3 / 2 : ℝ) = 3 * Real.sqrt 3 := by
    rw [show (3 / 2 : ℝ) = 1 + (1 / 2) by norm_num,
      Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  norm_num [Fin.sum_univ_succ, hfour, hthree]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]

theorem result : ¬ claim := by
  intro h
  obtain ⟨h₀, h₁, h₂⟩ := witness_psd
  exact (not_le_of_gt norm_reverse)
    (h 4 a₀ a₁ a₀ b₁ h₀ h₁ h₀ h₂ rfl witness_spectra word_bounds (3 / 2) (by norm_num))

end D5.S3.Quantum.Schatten.FractionalSchattenAlignmentRefutation
