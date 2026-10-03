/- GID: D5/S3/Combinatorics/PartialTheta/PartialThetaHankel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PartialTheta/PartialThetaHankel
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integral coalescence completes Cigler's partial theta Hankel determinant conjecture. -/

import D5.S3.Combinatorics.PartialTheta.PartialThetaHankelCoalescence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PartialTheta.PartialThetaHankel

open Polynomial Finset
open PartialThetaHankelDefs

set_option maxHeartbeats 800000 in
theorem result : PartialThetaHankelDefs.claim := by
  classical
  intro m n
  obtain ⟨quotient, factorization, divided, division, cleared⟩ :=
    PartialThetaHankelQuotient.integral_quotient m n
  obtain ⟨monic, degree, at_zero⟩ :=
    PartialThetaHankelHighest.quotient_data m n quotient factorization
  refine ⟨(PartialThetaHankelVandermonde.unshifted n).2.1,
    quotient, factorization, monic, degree, ?_, at_zero⟩
  let evaluate : ℤ[X] →+* ℤ := Polynomial.evalRingHom 1
  let integer_divided : MvPolynomial (Fin (n + 1)) ℤ :=
    MvPolynomial.map evaluate divided
  let top : Fin m → Fin (m + (n + 1)) → ℤ :=
    fun row column => if m - (row : ℕ) ≤ column then 1 else 0
  have integer_division :
      (Matrix.of fun row column : Fin (m + (n + 1)) =>
        if before : (row : ℕ) < m then MvPolynomial.C (top ⟨row, before⟩ column)
        else MvPolynomial.X ⟨(row : ℕ) - m, by omega⟩ ^ (column : ℕ)).det =
          (∏ lower : Fin (n + 1), ∏ upper ∈ Ioi lower,
            (MvPolynomial.X upper - MvPolynomial.X lower)) * integer_divided := by
    have equation := congrArg (MvPolynomial.map evaluate) division
    erw [RingHom.map_det, map_mul] at equation
    simp only [map_prod, map_sub, MvPolynomial.map_X] at equation
    let reindex : Fin (m + (n + 1)) ≃ Fin (n + m + 1) := finCongr (by omega)
    rw [← Matrix.det_reindex_self reindex.symm] at equation
    convert equation using 2
    apply _root_.funext
    intro row
    apply _root_.funext
    intro column
    change (if before : (row : ℕ) < m then
      MvPolynomial.C (top ⟨row, before⟩ column)
      else MvPolynomial.X (⟨(row : ℕ) - m, by omega⟩ : Fin (n + 1)) ^ (column : ℕ)) =
        MvPolynomial.map evaluate
          (if before : (row : ℕ) < m then
            MvPolynomial.C (if (column : ℕ) < m - row then 0 else
              X ^ ((m - row + 1).choose 2 + (m - row) * (n + m + 1 - column)))
          else MvPolynomial.X (⟨(row : ℕ) - m, by omega⟩ : Fin (n + 1)) ^ (column : ℕ))
    by_cases before : (row : ℕ) < m
    · rw [dif_pos before, dif_pos before]
      erw [MvPolynomial.map_C]
      by_cases early : (column : ℕ) < m - row
      · simp [top, evaluate, early]
        omega
      · simp [top, evaluate, early]
        omega
    · rw [dif_neg before, dif_neg before]
      erw [map_pow, MvPolynomial.map_X]
  have coalesced : MvPolynomial.eval (fun _ => 1) integer_divided =
      (-1 : ℤ) ^ (m + 1).choose 2 := by
    rw [PartialThetaHankelCoalescence.coalescence m (n + 1) top integer_divided
      integer_division]
    convert PartialThetaHankelCoalescence.staircase_det m n using 2
    ext row column
    simp only [top, Matrix.of_apply]
    split_ifs <;> rfl
  have specialized :
      evaluate (MvPolynomial.eval₂ (RingHom.id ℤ[X])
        (fun index : Fin (n + 1) => X ^ (index : ℕ)) divided) =
          MvPolynomial.eval (fun _ => 1) integer_divided := by
    rw [MvPolynomial.hom_eval₂, MvPolynomial.eval_map]
    simp [evaluate]
  have evaluation := congrArg evaluate cleared
  simp only [map_mul, map_pow, map_neg, map_one] at evaluation
  rw [specialized, coalesced] at evaluation
  simp [evaluate, ← pow_add] at evaluation
  exact evaluation

end D5.S3.Combinatorics.PartialTheta.PartialThetaHankel
