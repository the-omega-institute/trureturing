/- GID: D5/S3/Arith/CharacterSums/PascadiScalarCenters
   generality: G
   mirror-B: none(waiver:actual-all-scalar-center-comparison)
   mirror-E: none(waiver:actual-all-scalar-center-comparison)
   anchors: []
   utility: none
   digest: Scalar centers of the original word with literal interval multiplicities. -/

import D5.S3.Arith.CharacterSums.PascadiIntervalAutocorrelation
import D5.S3.Arith.CharacterSums.PascadiMinusRows
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! The original alternating word is realized in the finite special linear
group with its exact sign and integer interval multiplicities. -/

namespace D5.S3.Arith.CharacterSums.Original

open scoped BigOperators Matrix
open Matrix

noncomputable section

variable {c : ℕ} [NeZero c]

private abbrev ReturnGroup (c : ℕ) := Matrix.SpecialLinearGroup (Fin 2) (ZMod c)

private def upperSL (x : ZMod c) : ReturnGroup c :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

private def lowerSL (x : ZMod c) : ReturnGroup c :=
  ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two]⟩

private def upperIntegerHom (a : ZMod c) : Multiplicative ℤ →* ReturnGroup c where
  toFun n := upperSL (a * (Multiplicative.toAdd n : ℤ))
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperSL, Matrix.one_apply]
  map_mul' n m := by
    apply Subtype.ext
    change !![1, a * (Multiplicative.toAdd (n * m) : ℤ); 0, 1] =
      !![1, a * (Multiplicative.toAdd n : ℤ); 0, 1] *
        !![1, a * (Multiplicative.toAdd m : ℤ); 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add] <;> ring

private def lowerIntegerHom (a : ZMod c) : Multiplicative ℤ →* ReturnGroup c where
  toFun n := lowerSL (a * (Multiplicative.toAdd n : ℤ))
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerSL, Matrix.one_apply]
  map_mul' n m := by
    apply Subtype.ext
    change !![1, 0; a * (Multiplicative.toAdd (n * m) : ℤ), 1] =
      !![1, 0; a * (Multiplicative.toAdd n : ℤ), 1] *
        !![1, 0; a * (Multiplicative.toAdd m : ℤ), 1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add] <;> ring

private def groupReturnWord (a₁ a₂ : ZMod c) (h : ReturnRows) : ReturnGroup c :=
  upperIntegerHom a₁ (.ofAdd (h.1 0)) * lowerIntegerHom (-a₂) (.ofAdd (h.2 2)) *
    upperIntegerHom a₁ (.ofAdd (h.1 1)) * lowerIntegerHom (-a₂) (.ofAdd (h.2 0)) *
    upperIntegerHom a₁ (.ofAdd (h.1 2)) * lowerIntegerHom (-a₂) (.ofAdd (h.2 1))

private theorem step_pair_upper_lower (x y : ZMod c) :
    returnStep x * returnStep y =
      -((upperSL x : Matrix (Fin 2) (Fin 2) (ZMod c)) * (lowerSL (-y))) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [returnStep, upperSL, lowerSL, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The exact upper/lower realization, keeping the fixed alternating units and
the original even-row cyclic ordering. The overall sign is minus. -/
private theorem groupReturnWord_matrix (a₁ a₂ : ZMod c) (h : ReturnRows) :
    (groupReturnWord a₁ a₂ h : Matrix (Fin 2) (Fin 2) (ZMod c)) =
      -sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1) (h.2 0) (h.1 2) (h.2 1) := by
  have hword : sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1) (h.2 0) (h.1 2) (h.2 1) =
      (returnStep (a₁ * (h.1 0 : ZMod c)) * returnStep (a₂ * (h.2 2 : ZMod c))) *
        (returnStep (a₁ * (h.1 1 : ZMod c)) * returnStep (a₂ * (h.2 0 : ZMod c))) *
        (returnStep (a₁ * (h.1 2 : ZMod c)) * returnStep (a₂ * (h.2 1 : ZMod c))) := by
    simp only [sixReturnWord, mul_assoc]
  rw [hword, step_pair_upper_lower, step_pair_upper_lower, step_pair_upper_lower]
  simp only [neg_mul, mul_neg, neg_neg]
  simp only [groupReturnWord, Matrix.SpecialLinearGroup.coe_mul,
    upperIntegerHom, lowerIntegerHom, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd, neg_mul, mul_assoc]
  rfl

private def scalarSL (γ : ZMod c) (hγ : γ * γ = 1) : ReturnGroup c :=
  ⟨scalarReturn γ, by simpa [scalarReturn, Matrix.det_fin_two] using hγ⟩

private theorem scalarSL_central (γ : ZMod c) (hγ : γ * γ = 1) :
    scalarSL γ hγ ∈ Subgroup.center (ReturnGroup c) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) (ZMod c)) * scalarReturn γ =
    scalarReturn γ * (g : Matrix (Fin 2) (Fin 2) (ZMod c))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarReturn, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem groupReturnWord_scalar_iff (a₁ a₂ γ : ZMod c) (hγ : γ * γ = 1)
    (h : ReturnRows) :
    groupReturnWord a₁ a₂ h = scalarSL (-γ) (by simpa using hγ) ↔
      sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1) (h.2 0) (h.1 2) (h.2 1) =
        scalarReturn γ := by
  have hneg : scalarReturn (-γ) = -(scalarReturn γ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalarReturn]
  constructor
  · intro hh
    have he := congrArg (fun g : ReturnGroup c => (g : Matrix (Fin 2) (Fin 2) (ZMod c))) hh
    rw [groupReturnWord_matrix] at he
    change -sixReturnWord _ _ _ _ _ _ _ _ = scalarReturn (-γ) at he
    rw [hneg, neg_inj] at he
    exact he
  · intro hh
    apply Subtype.ext
    rw [groupReturnWord_matrix, hh]
    exact hneg.symm

/-- Original scalar returns, with six literal integer letters and their
separate row bounds, using the existing return word unchanged. -/
def scalarSolutions (c X Y : ℕ) (a₁ a₂ γ : ZMod c) : Finset ReturnRows :=
  (literalRowBox X Y).filter fun h =>
    sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1) (h.2 0) (h.1 2) (h.2 1) =
      scalarReturn γ

private abbrev PairTriple := (ℤ × ℤ) × ((ℤ × ℤ) × (ℤ × ℤ))

private def rowsToPairs (h : ReturnRows) : PairTriple :=
  ((h.1 0, h.2 2), ((h.1 1, h.2 0), (h.1 2, h.2 1)))

private def pairsToRows (t : PairTriple) : ReturnRows :=
  (![t.1.1, t.2.1.1, t.2.2.1], ![t.2.1.2, t.2.2.2, t.1.2])

private def pairsWord (u v : Multiplicative ℤ →* ReturnGroup c) (t : PairTriple) : ReturnGroup c :=
  u (.ofAdd t.1.1) * v (.ofAdd t.1.2) *
    u (.ofAdd t.2.1.1) * v (.ofAdd t.2.1.2) *
    u (.ofAdd t.2.2.1) * v (.ofAdd t.2.2.2)

private theorem interval_cube_rows (a₁ a₂ : ZMod c) (X Y : ℕ) :
    (integerIntervalMeasure (upperIntegerHom a₁) X *
        integerIntervalMeasure (lowerIntegerHom (-a₂)) Y) ^ 3 =
      ∑ h ∈ literalRowBox X Y, MonoidAlgebra.single (groupReturnWord a₁ a₂ h) (1 : ℝ) := by
  classical
  let u := upperIntegerHom a₁
  let v := lowerIntegerHom (-a₂)
  let E := symmetricIntegerInterval X ×ˢ symmetricIntegerInterval Y
  let L := E ×ˢ (E ×ˢ E)
  have hpairs : integerIntervalMeasure u X * integerIntervalMeasure v Y =
      ∑ ab ∈ E, MonoidAlgebra.single (u (.ofAdd ab.1) * v (.ofAdd ab.2)) (1 : ℝ) := by
    simp only [integerIntervalMeasure, Finset.sum_mul, Finset.mul_sum,
      MonoidAlgebra.single_mul_single, mul_one, E, Finset.sum_product]
    rw [Finset.sum_comm]
  have hcube : (integerIntervalMeasure u X * integerIntervalMeasure v Y) ^ 3 =
      ∑ t ∈ L, MonoidAlgebra.single (pairsWord u v t) (1 : ℝ) := by
    rw [hpairs, pow_succ', pow_two, Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum,
      MonoidAlgebra.single_mul_single, mul_one, L, Finset.sum_product, pairsWord, mul_assoc]
  have hrows : (∑ h ∈ literalRowBox X Y,
      MonoidAlgebra.single (groupReturnWord a₁ a₂ h) (1 : ℝ)) =
        ∑ t ∈ L, MonoidAlgebra.single (pairsWord u v t) (1 : ℝ) := by
    apply Finset.sum_nbij' rowsToPairs pairsToRows
    · intro h hh
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hh
      have hx' := Fintype.mem_piFinset.mp hx
      have hy' := Fintype.mem_piFinset.mp hy
      exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx' 0, hy' 2⟩,
        Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx' 1, hy' 0⟩,
          Finset.mem_product.mpr ⟨hx' 2, hy' 1⟩⟩⟩
    · intro t ht
      obtain ⟨ht₀, hrest⟩ := Finset.mem_product.mp ht
      obtain ⟨ht₁, ht₂⟩ := Finset.mem_product.mp hrest
      obtain ⟨hx₀, hy₂⟩ := Finset.mem_product.mp ht₀
      obtain ⟨hx₁, hy₀⟩ := Finset.mem_product.mp ht₁
      obtain ⟨hx₂, hy₁⟩ := Finset.mem_product.mp ht₂
      simp only [symmetricIntegerInterval, Finset.mem_Icc] at hx₀ hx₁ hx₂ hy₂ hy₀ hy₁
      apply Finset.mem_product.mpr
      constructor
      · apply Fintype.mem_piFinset.mpr
        intro i
        fin_cases i
        · exact Finset.mem_Icc.mpr hx₀
        · exact Finset.mem_Icc.mpr hx₁
        · exact Finset.mem_Icc.mpr hx₂
      · apply Fintype.mem_piFinset.mpr
        intro i
        fin_cases i
        · exact Finset.mem_Icc.mpr hy₀
        · exact Finset.mem_Icc.mpr hy₁
        · exact Finset.mem_Icc.mpr hy₂
    · intro h _
      apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
    · intro t _
      rfl
    · intro h _
      rfl
  exact hcube.trans hrows.symm

/-- The group-algebra coefficient equals the actual integer solution count,
including every wraparound multiplicity and the original even-row order. -/
private theorem scalar_coefficient_count (a₁ a₂ γ : ZMod c) (hγ : γ * γ = 1) (X Y : ℕ) :
    ((integerIntervalMeasure (upperIntegerHom a₁) X *
      integerIntervalMeasure (lowerIntegerHom (-a₂)) Y) ^ 3).coeff
        (scalarSL (-γ) (by simpa using hγ)) =
      ((scalarSolutions c X Y a₁ a₂ γ).card : ℝ) := by
  classical
  rw [interval_cube_rows]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp_rw [groupReturnWord_scalar_iff a₁ a₂ γ hγ]
  calc
    _ = ∑ _h ∈ scalarSolutions c X Y a₁ a₂ γ, (1 : ℝ) := by
      rw [scalarSolutions, Finset.sum_filter]
    _ = _ := by simp

/-- Every scalar center of the existing six-return word is bounded by the
minus-identity count in the doubled, separate integer intervals. -/
theorem scalarSolutions_card_le_minus_doubled (a₁ a₂ γ : ZMod c)
    (hγ : γ * γ = 1) (X Y : ℕ) :
    (scalarSolutions c X Y a₁ a₂ γ).card ≤
      64 * (minusSolutions c (2 * X) (2 * Y) a₁ a₂).card := by
  have hh := alternating_integer_interval_center_le
    (upperIntegerHom a₁) (lowerIntegerHom (-a₂)) X Y
    (scalarSL (-γ) (by simpa using hγ)) (scalarSL_central (-γ) (by simpa using hγ))
  rw [scalar_coefficient_count a₁ a₂ γ hγ X Y] at hh
  have hone : scalarSL (-(-1 : ZMod c)) (by simp) = (1 : ReturnGroup c) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalarSL, scalarReturn, Matrix.one_apply]
  have hminus := scalar_coefficient_count a₁ a₂ (-1) (by simp) (2 * X) (2 * Y)
  rw [hone] at hminus
  rw [hminus] at hh
  change ((scalarSolutions c X Y a₁ a₂ γ).card : ℝ) ≤
    64 * ((minusSolutions c (2 * X) (2 * Y) a₁ a₂).card : ℝ) at hh
  exact_mod_cast hh

/-- Actual original scalar returns for nonnegative real widths; floors only
enumerate the literal integer intervals and do not identify equal residues. -/
def scalarSolutionsReal (c : ℕ) (X Y : ℝ) (a₁ a₂ γ : ZMod c) : Finset ReturnRows :=
  scalarSolutions c ⌊X⌋₊ ⌊Y⌋₊ a₁ a₂ γ

private theorem integer_real_interval_iff (T : ℝ) (hT : 0 ≤ T) (n : ℤ) :
    (-(⌊T⌋₊ : ℤ) ≤ n ∧ n ≤ ⌊T⌋₊) ↔ |(n : ℝ)| ≤ T := by
  rw [Int.natCast_floor_eq_floor hT]
  constructor
  · intro hn
    have hu := Int.le_floor.mp hn.2
    have hl : ((-n : ℤ) : ℝ) ≤ T := Int.le_floor.mp (by omega)
    push_cast at hl
    exact abs_le.mpr ⟨by linarith, hu⟩
  · intro hn
    have hu := Int.le_floor.mpr (abs_le.mp hn).2
    have hl : -n ≤ ⌊T⌋ := Int.le_floor.mpr (by push_cast; linarith [(abs_le.mp hn).1])
    omega

/-- Membership is the existing six-return equation and the six literal,
separately bounded integer letters, even for nonintegral real widths. -/
theorem mem_scalarSolutionsReal (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (a₁ a₂ γ : ZMod c) (h : ReturnRows) :
    h ∈ scalarSolutionsReal c X Y a₁ a₂ γ ↔
      (∀ i, |(h.1 i : ℝ)| ≤ X) ∧ (∀ i, |(h.2 i : ℝ)| ≤ Y) ∧
        sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1) (h.2 0) (h.1 2) (h.2 1) =
          scalarReturn γ := by
  simp only [scalarSolutionsReal, scalarSolutions, literalRowBox, Finset.mem_filter,
    Finset.product_eq_sprod, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc,
    integer_real_interval_iff X hX, integer_real_interval_iff Y hY, and_assoc]

/-- The all-center comparison for the actual six-return word and arbitrary
nonnegative real widths, with the two widths doubled separately. -/
theorem scalarSolutionsReal_card_le_minus_doubled (a₁ a₂ γ : ZMod c)
    (hγ : γ * γ = 1) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (scalarSolutionsReal c X Y a₁ a₂ γ).card ≤
      64 * (minusSolutions c ⌊2 * X⌋₊ ⌊2 * Y⌋₊ a₁ a₂).card := by
  have hc := scalarSolutions_card_le_minus_doubled a₁ a₂ γ hγ ⌊X⌋₊ ⌊Y⌋₊
  have hsub : minusSolutions c (2 * ⌊X⌋₊) (2 * ⌊Y⌋₊) a₁ a₂ ⊆
      scalarSolutionsReal c (2 * X) (2 * Y) a₁ a₂ (-1) := by
    intro h hh
    obtain ⟨hbox, hword⟩ := Finset.mem_filter.mp hh
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hbox
    apply (mem_scalarSolutionsReal (2 * X) (2 * Y) (by positivity) (by positivity)
      a₁ a₂ (-1) h).mpr
    refine ⟨?_, ?_, hword⟩
    · intro i
      have hb := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hx i)
      have hab : |(h.1 i : ℝ)| ≤ (2 * ⌊X⌋₊ : ℕ) := by exact_mod_cast abs_le.mpr hb
      push_cast at hab
      nlinarith [Nat.floor_le hX]
    · intro i
      have hb := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hy i)
      have hab : |(h.2 i : ℝ)| ≤ (2 * ⌊Y⌋₊ : ℕ) := by exact_mod_cast abs_le.mpr hb
      push_cast at hab
      nlinarith [Nat.floor_le hY]
  have hh := Nat.mul_le_mul_left 64 (Finset.card_le_card hsub)
  exact hc.trans hh

end

end D5.S3.Arith.CharacterSums.Original
