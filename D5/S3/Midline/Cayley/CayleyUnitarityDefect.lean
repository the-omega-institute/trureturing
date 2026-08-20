/- GID: D5/S3/Midline/Cayley/CayleyUnitarityDefect
   generality: I
   mirror-B: D5/B/S3/Midline/Cayley/CayleyUnitarityDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compute the Cayley star-unitarity defect on every nontrivial-zero coordinate. -/

/- Library-search audit trail (2026-08-20):
   * Repository searches found the exhaustive `ZeroData` carrier, but no Cayley-defect theorem.
   * `SpectralDynamics.critical_line_characterizations` concerns a different multiplier.
   * Pinned Mathlib provides the exact norm identities `Complex.normSq_div`,
     `Complex.normSq_sub`, `Complex.normSq_eq_conj_mul_self`, and `Complex.sq_norm`.
   * Searches found finite matrix unitary lemmas, but no full countable diagonal specialization.
-/

import D5.S3.Weil.ZeroSum

namespace D5.S3.Midline.Cayley.CayleyUnitarityDefect

open D5.S3.Weil.ZeroSum
open scoped ComplexConjugate

/-- A diagonal operator on the countable coordinate space. -/
structure DiagonalOperator where
  coefficient : Nat -> Complex

@[ext]
theorem DiagonalOperator.ext {A B : DiagonalOperator}
    (h : forall n, A.coefficient n = B.coefficient n) : A = B := by
  cases A with
  | mk a =>
    cases B with
    | mk b =>
      congr
      funext n
      exact h n

instance : One DiagonalOperator :=
  ⟨⟨fun _ => 1⟩⟩

instance : Mul DiagonalOperator :=
  ⟨fun A B => ⟨fun n => A.coefficient n * B.coefficient n⟩⟩

instance : Sub DiagonalOperator :=
  ⟨fun A B => ⟨fun n => A.coefficient n - B.coefficient n⟩⟩

instance : Star DiagonalOperator :=
  ⟨fun A => ⟨fun n => star (A.coefficient n)⟩⟩

/-- Apply a diagonal operator to a coordinate vector. -/
def operatorAction (A : DiagonalOperator) (x : Nat -> Complex) : Nat -> Complex :=
  fun n => A.coefficient n * x n

/-- The coordinate basis vector at `n`. -/
def basisVector (n : Nat) : Nat -> Complex :=
  fun j => if j = n then 1 else 0

/-- The Cayley coefficient constructed from a complex spectral point. -/
noncomputable def cayleyCoefficient (rho : Complex) : Complex :=
  (rho - 1) / rho

/-- The Cayley operator constructed from every zero in the exhaustive source carrier. -/
noncomputable def cayleyOperator (Z : ZeroData) : DiagonalOperator :=
  ⟨fun n => cayleyCoefficient (Z.zero n)⟩

/-- The real star-unitarity defect of the `n`th Cayley coefficient. -/
noncomputable def defectScalar (Z : ZeroData) (n : Nat) : Real :=
  ‖cayleyCoefficient (Z.zero n)‖ ^ 2 - 1

/-- Every source zero lies on the midline. -/
def AllZerosOnMidline (Z : ZeroData) : Prop :=
  forall n, (Z.zero n).re = 1 / 2

/-- A diagonal operator has its coordinatewise star as a two-sided inverse. -/
def IsTwoSidedUnitary (A : DiagonalOperator) : Prop :=
  star A * A = 1 ∧ A * star A = 1

private theorem zero_ne_zero (Z : ZeroData) (n : Nat) : Z.zero n ≠ 0 := by
  intro hzero
  have hpositive := (Z.zero_isNontrivial n).2.1
  rw [hzero] at hpositive
  norm_num at hpositive

private theorem defect_scalar_formula (Z : ZeroData) (n : Nat) :
    defectScalar Z n =
      (1 - 2 * (Z.zero n).re) / Complex.normSq (Z.zero n) := by
  have hzero := zero_ne_zero Z n
  have hnormSq : Complex.normSq (Z.zero n) ≠ 0 :=
    mt Complex.normSq_eq_zero.mp hzero
  rw [defectScalar, Complex.sq_norm, cayleyCoefficient, Complex.normSq_div,
    Complex.normSq_sub]
  simp only [map_one, mul_one]
  field_simp [hnormSq]
  ring

private theorem coefficient_norm_one_iff_midline (Z : ZeroData) (n : Nat) :
    ‖cayleyCoefficient (Z.zero n)‖ = 1 ↔ (Z.zero n).re = 1 / 2 := by
  have hzero := zero_ne_zero Z n
  have hnormSq : Complex.normSq (Z.zero n) ≠ 0 :=
    mt Complex.normSq_eq_zero.mp hzero
  have hformula := defect_scalar_formula Z n
  constructor
  · intro hnorm
    have hdefect : defectScalar Z n = 0 := by
      simp [defectScalar, hnorm]
    rw [hdefect] at hformula
    have hnumerator : 1 - 2 * (Z.zero n).re = 0 :=
      (div_eq_zero_iff).mp hformula.symm |>.resolve_right hnormSq
    linarith
  · intro hmidline
    have hdefect : defectScalar Z n = 0 := by
      rw [hformula, hmidline]
      norm_num
    rw [defectScalar] at hdefect
    nlinarith [norm_nonneg (cayleyCoefficient (Z.zero n))]

private theorem star_mul_self_iff_norm_one (Z : ZeroData) :
    star (cayleyOperator Z) * cayleyOperator Z = 1 ↔
      forall n, ‖cayleyCoefficient (Z.zero n)‖ = 1 := by
  constructor
  · intro h n
    have hn := congrArg (fun A => A.coefficient n) h
    change conj (cayleyCoefficient (Z.zero n)) *
      cayleyCoefficient (Z.zero n) = 1 at hn
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq] at hn
    have hnReal : ‖cayleyCoefficient (Z.zero n)‖ ^ 2 = (1 : Real) := by
      exact_mod_cast hn
    nlinarith [norm_nonneg (cayleyCoefficient (Z.zero n))]
  · intro h
    ext n
    change conj (cayleyCoefficient (Z.zero n)) *
      cayleyCoefficient (Z.zero n) = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, h n]
    norm_num

private theorem norm_one_implies_two_sided (Z : ZeroData)
    (h : forall n, ‖cayleyCoefficient (Z.zero n)‖ = 1) :
    IsTwoSidedUnitary (cayleyOperator Z) := by
  constructor
  · exact (star_mul_self_iff_norm_one Z).2 h
  · ext n
    change cayleyCoefficient (Z.zero n) * star (cayleyCoefficient (Z.zero n)) = 1
    rw [mul_comm]
    have hn := congrArg (fun A => A.coefficient n) ((star_mul_self_iff_norm_one Z).2 h)
    exact hn

/-- The Cayley defect formula and all its global midline-unitarity characterizations. -/
theorem cayley_unitarity_defect_formula (Z : ZeroData) :
    (forall n,
      operatorAction (star (cayleyOperator Z) * cayleyOperator Z - 1) (basisVector n) =
          (fun j => (defectScalar Z n : Complex) * basisVector n j) ∧
        defectScalar Z n = ‖cayleyCoefficient (Z.zero n)‖ ^ 2 - 1 ∧
        defectScalar Z n =
          (1 - 2 * (Z.zero n).re) / Complex.normSq (Z.zero n)) ∧
      (AllZerosOnMidline Z ↔
        forall n, ‖cayleyCoefficient (Z.zero n)‖ = 1) ∧
      (AllZerosOnMidline Z ↔
        star (cayleyOperator Z) * cayleyOperator Z = 1) ∧
      (AllZerosOnMidline Z ↔ IsTwoSidedUnitary (cayleyOperator Z)) := by
  have hmidline :
      AllZerosOnMidline Z ↔ forall n, ‖cayleyCoefficient (Z.zero n)‖ = 1 := by
    simp only [AllZerosOnMidline]
    exact forall_congr' fun n => (coefficient_norm_one_iff_midline Z n).symm
  refine ⟨?_, hmidline, hmidline.trans (star_mul_self_iff_norm_one Z).symm, ?_⟩
  · intro n
    refine ⟨?_, rfl, defect_scalar_formula Z n⟩
    funext j
    by_cases hjn : j = n
    · subst j
      simp only [operatorAction, basisVector, if_pos, mul_one]
      change (conj (cayleyCoefficient (Z.zero n)) *
          cayleyCoefficient (Z.zero n) - 1) =
        (defectScalar Z n : Complex)
      rw [← Complex.normSq_eq_conj_mul_self, defectScalar, Complex.sq_norm]
      norm_cast
    · simp [operatorAction, basisVector, hjn]
  · constructor
    · intro h
      exact norm_one_implies_two_sided Z (hmidline.mp h)
    · intro h
      exact hmidline.mpr ((star_mul_self_iff_norm_one Z).mp h.1)

#print axioms cayley_unitarity_defect_formula

end D5.S3.Midline.Cayley.CayleyUnitarityDefect
