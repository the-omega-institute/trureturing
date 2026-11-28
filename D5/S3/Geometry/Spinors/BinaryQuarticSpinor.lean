/- GID: D5/S3/Geometry/Spinors/BinaryQuarticSpinor
   generality: G
   mirror-B: none(waiver:covered-by-petrov-bel-robinson-superenergy4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric complex four-spinors and their binary quartic invariants. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Omega original.
Symmetric complex four-spinors and their binary quartic invariants. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.BinaryQuarticSpinor

open Matrix Polynomial
open scoped BigOperators

abbrev Spinor := Fin 2 → ℂ
abbrev Coefficients := Fin 5 → ℂ

def weylEntry (ψ : Coefficients) (a b c d : Fin 2) : ℂ :=
  ψ ⟨a.val + b.val + c.val + d.val, by omega⟩

def weylSpinorForm (ψ : Coefficients) (α β γ δ : Spinor) : ℂ :=
  ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
    weylEntry ψ a b c d * α a * β b * γ c * δ d

def entryIndex (i : Fin 4 → Fin 2) : Fin 5 :=
  ⟨∑ j, (i j).val, by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin 4) _ =>
      Nat.le_of_lt_succ (i j).isLt)
    simp at h
    omega⟩

theorem entryIndex_comp (σ : Equiv.Perm (Fin 4)) (i : Fin 4 → Fin 2) :
    entryIndex (i ∘ σ) = entryIndex i := by
  apply Fin.ext
  exact Equiv.sum_comp σ (fun j => (i j).val)

theorem sum_tuple_four {K : Type*} [AddCommMonoid K] (f : (Fin 4 → Fin 2) → K) :
    ∑ i, f i = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2, f ![a, b, c, d] := by
  have split (n : ℕ) (g : (Fin (n + 1) → Fin 2) → K) :
      ∑ i, g i = ∑ a : Fin 2, ∑ t : Fin n → Fin 2, g (Fin.cons a t) := by
    calc
      (∑ i, g i) = ∑ p : Fin 2 × (Fin n → Fin 2), g (Fin.cons p.1 p.2) :=
        ((Fin.consEquiv _).sum_comp g).symm
      _ = _ := Fintype.sum_prod_type _
  have empty (g : (Fin 0 → Fin 2) → K) : ∑ i, g i = g ![] :=
    Fintype.sum_unique g
  simp only [split 3, split 2, split 1, split 0, empty]
  rfl

def indexedForm (ψ : Coefficients) (s : Fin 4 → Spinor) : ℂ :=
  ∑ i : Fin 4 → Fin 2, ψ (entryIndex i) * ∏ j, s j (i j)

theorem indexedForm_eq (ψ : Coefficients) (s : Fin 4 → Spinor) :
    indexedForm ψ s = weylSpinorForm ψ (s 0) (s 1) (s 2) (s 3) := by
  rw [indexedForm, sum_tuple_four]
  simp only [weylSpinorForm, Fin.prod_univ_four]
  congr 1
  funext a
  congr 1
  funext b
  congr 1
  funext c
  congr 1
  funext d
  have h : entryIndex ![a, b, c, d] = ⟨a.val + b.val + c.val + d.val, by omega⟩ := by
    apply Fin.ext
    simp [entryIndex, Fin.sum_univ_succ]
    omega
  rw [h, weylEntry]
  simp
  ring

theorem weylSpinorForm_totally_symmetric (ψ : Coefficients) (s : Fin 4 → Spinor)
    (σ : Equiv.Perm (Fin 4)) :
    weylSpinorForm ψ (s (σ 0)) (s (σ 1)) (s (σ 2)) (s (σ 3)) =
      weylSpinorForm ψ (s 0) (s 1) (s 2) (s 3) := by
  change weylSpinorForm ψ ((s ∘ σ) 0) ((s ∘ σ) 1) ((s ∘ σ) 2) ((s ∘ σ) 3) = _
  rw [← indexedForm_eq ψ (s ∘ σ), ← indexedForm_eq]
  unfold indexedForm
  let e : (Fin 4 → Fin 2) ≃ (Fin 4 → Fin 2) :=
    { toFun := fun i => i ∘ σ
      invFun := fun i => i ∘ σ.symm
      left_inv := fun i => by funext j; simp
      right_inv := fun i => by funext j; simp }
  refine (e.sum_comp _).symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  change ψ (entryIndex (i ∘ σ)) * (∏ j, s (σ j) (i (σ j))) =
    ψ (entryIndex i) * ∏ j, s j (i j)
  rw [entryIndex_comp, Equiv.prod_comp σ (fun j => s j (i j))]

def petrovI (ψ : Coefficients) : ℂ :=
  ψ 0 * ψ 4 - 4 * ψ 1 * ψ 3 + 3 * ψ 2 ^ 2

def petrovJ (ψ : Coefficients) : ℂ :=
  ψ 0 * ψ 2 * ψ 4 + 2 * ψ 1 * ψ 2 * ψ 3 - ψ 2 ^ 3 - ψ 0 * ψ 3 ^ 2 - ψ 1 ^ 2 * ψ 4

def petrovDisc (ψ : Coefficients) : ℂ := petrovI ψ ^ 3 - 27 * petrovJ ψ ^ 2

/-- Pullback along the given matrix on each of the four spinor arguments, in components. -/
def sl2cAct (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Coefficients) : Coefficients :=
  let a := M 0 0
  let b := M 0 1
  let c := M 1 0
  let d := M 1 1
  ![ψ 0 * a^4 + 4 * ψ 1 * a^3*c + 6 * ψ 2 * a^2*c^2 + 4 * ψ 3 * a*c^3 + ψ 4*c^4,
    ψ 0 * a^3*b + ψ 1*(3*a^2*b*c+a^3*d) + ψ 2*(3*a*b*c^2+3*a^2*c*d) +
      ψ 3*(b*c^3+3*a*c^2*d) + ψ 4*c^3*d,
    ψ 0 * a^2*b^2 + ψ 1*(2*a*b^2*c + 2*a^2*b*d) + ψ 2*(b^2*c^2+4*a*b*c*d+a^2*d^2) +
      ψ 3*(2*b*c^2*d+2*a*c*d^2) + ψ 4*c^2*d^2,
    ψ 0 * a*b^3 + ψ 1*(b^3*c+3*a*b^2*d) + ψ 2*(3*b^2*c*d+3*a*b*d^2) +
      ψ 3*(3*b*c*d^2+a*d^3) + ψ 4*c*d^3,
    ψ 0 * b^4 + 4 * ψ 1 * b^3*d + 6 * ψ 2 * b^2*d^2 + 4 * ψ 3 * b*d^3 + ψ 4*d^4]

private theorem entry_sl2cAct (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Coefficients)
    (a b c d : Fin 2) :
    weylEntry (sl2cAct M ψ) a b c d =
      weylSpinorForm ψ (fun i => M i a) (fun i => M i b) (fun i => M i c) (fun i => M i d) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [weylEntry, weylSpinorForm, Fin.sum_univ_two] <;>
    norm_num [sl2cAct] <;> ring

theorem sl2cAct_form (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Coefficients)
    (s : Fin 4 → Spinor) :
    indexedForm (sl2cAct M ψ) s = indexedForm ψ (fun j => M *ᵥ s j) := by
  have coeff (i : Fin 4 → Fin 2) :
      sl2cAct M ψ (entryIndex i) = ∑ k : Fin 4 → Fin 2, ψ (entryIndex k) * ∏ j, M (k j) (i j) := by
    change _ = indexedForm ψ (fun j k => M k (i j))
    rw [indexedForm_eq, ← entry_sl2cAct]
    congr 1
    apply Fin.ext
    simp [entryIndex, Fin.sum_univ_succ]
    omega
  unfold indexedForm
  simp_rw [coeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [mul_assoc, ← Finset.prod_mul_distrib, ← Finset.mul_sum]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  simpa only [Fintype.piFinset_univ] using
    (Finset.sum_prod_piFinset (ι := Fin 4) (Finset.univ : Finset (Fin 2))
      (fun j i => M (k j) i * s j i))

theorem petrovI_det_weight (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Coefficients) :
    petrovI (sl2cAct M ψ) = M.det ^ 4 * petrovI ψ := by
  simp [petrovI, sl2cAct, Matrix.det_fin_two]
  ring

theorem petrovJ_det_weight (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Coefficients) :
    petrovJ (sl2cAct M ψ) = M.det ^ 6 * petrovJ ψ := by
  simp [petrovJ, sl2cAct, Matrix.det_fin_two]
  ring

theorem petrov_invariants_sl2c_invariant (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Coefficients)
    (hM : M.det = 1) :
    petrovI (sl2cAct M ψ) = petrovI ψ ∧ petrovJ (sl2cAct M ψ) = petrovJ ψ ∧
      petrovDisc (sl2cAct M ψ) = petrovDisc ψ := by
  simp [petrovDisc, petrovI_det_weight, petrovJ_det_weight, hM]

def psiD (c : ℂ) : Coefficients := ![0, 0, c, 0, 0]
def psiII (c d : ℂ) : Coefficients := ![0, 0, c, 0, d]
def psiIII (c : ℂ) : Coefficients := ![0, 0, 0, c, 0]
def psiN (c : ℂ) : Coefficients := ![0, 0, 0, 0, c]
def psiI (a b : ℂ) : Coefficients := ![a, 0, b, 0, a]

theorem petrov_typeD (c : ℂ) :
    petrovI (psiD c) = 3 * c ^ 2 ∧ petrovJ (psiD c) = -c ^ 3 ∧
      petrovDisc (psiD c) = 0 ∧ (c ≠ 0 → petrovI (psiD c) ≠ 0 ∧ petrovJ (psiD c) ≠ 0) := by
  simp [petrovI, petrovJ, petrovDisc, psiD]
  ring

theorem petrov_typeII (c d : ℂ) :
    petrovI (psiII c d) = 3 * c ^ 2 ∧ petrovJ (psiII c d) = -c ^ 3 ∧
      petrovDisc (psiII c d) = 0 := by
  simp [petrovI, petrovJ, petrovDisc, psiII]
  ring

theorem petrov_typeIII (c : ℂ) :
    petrovI (psiIII c) = 0 ∧ petrovJ (psiIII c) = 0 ∧ petrovDisc (psiIII c) = 0 := by
  simp [petrovI, petrovJ, petrovDisc, psiIII]

theorem petrov_typeN (c : ℂ) :
    petrovI (psiN c) = 0 ∧ petrovJ (psiN c) = 0 ∧ petrovDisc (psiN c) = 0 := by
  simp [petrovI, petrovJ, petrovDisc, psiN]

theorem petrov_typeI (a b : ℂ) :
    petrovDisc (psiI a b) = a ^ 2 * (a ^ 2 - 9 * b ^ 2) ^ 2 ∧
      (a ≠ 0 → a ≠ 3 * b → a ≠ -3 * b → petrovDisc (psiI a b) ≠ 0) := by
  have h : petrovDisc (psiI a b) = a ^ 2 * (a ^ 2 - 9 * b ^ 2) ^ 2 := by
    simp [petrovI, petrovJ, petrovDisc, psiI]
    ring
  refine ⟨h, fun ha hb hc => ?_⟩
  have hfactor : a ^ 2 - 9 * b ^ 2 = (a - 3 * b) * (a - (-3 * b)) := by ring
  rw [h, hfactor]
  exact mul_ne_zero (pow_ne_zero _ ha)
    (pow_ne_zero _ (mul_ne_zero (sub_ne_zero.mpr hb) (sub_ne_zero.mpr hc)))

def weylPolynomial (ψ : Coefficients) : ℂ[X] :=
  monomial 4 (ψ 0) + monomial 3 (4 * ψ 1) + monomial 2 (6 * ψ 2) +
    monomial 1 (4 * ψ 3) + C (ψ 4)

theorem weylPolynomial_eval (ψ : Coefficients) (z : ℂ) :
    (weylPolynomial ψ).eval z = weylSpinorForm ψ ![z, 1] ![z, 1] ![z, 1] ![z, 1] := by
  simp only [weylPolynomial, weylSpinorForm, weylEntry, Fin.sum_univ_two, eval_add,
    eval_monomial, eval_C]
  norm_num
  ring

theorem weylPolynomial_coeff (ψ : Coefficients) (n : ℕ) :
    (weylPolynomial ψ).coeff n =
      if n = 4 then ψ 0 else if n = 3 then 4 * ψ 1 else if n = 2 then 6 * ψ 2 else
        if n = 1 then 4 * ψ 3 else if n = 0 then ψ 4 else 0 := by
  by_cases h4 : n = 4
  · subst n
    norm_num [weylPolynomial, coeff_monomial]
  by_cases h3 : n = 3
  · subst n
    norm_num [weylPolynomial, coeff_monomial]
  by_cases h2 : n = 2
  · subst n
    norm_num [weylPolynomial, coeff_monomial]
  by_cases h1 : n = 1
  · subst n
    norm_num [weylPolynomial, coeff_monomial]
  by_cases h0 : n = 0
  · subst n
    norm_num [weylPolynomial, coeff_monomial]
  simp [weylPolynomial, coeff_monomial, coeff_C, h4, h3, h2, h1, h0, Ne.symm h4, Ne.symm h3,
    Ne.symm h2, Ne.symm h1]

private def translate (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, z; 0, 1]

private def invertChart : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

private theorem weylPolynomial_translate (ψ : Coefficients) (z : ℂ) :
    weylPolynomial (sl2cAct (translate z) ψ) = (weylPolynomial ψ).comp (X + C z) := by
  apply Polynomial.funext
  intro t
  simp [weylPolynomial, sl2cAct, translate]
  ring

theorem petrov_repeated_at_zero (ψ : Coefficients) (h4 : ψ 4 = 0) (h3 : ψ 3 = 0) :
    petrovDisc ψ = 0 := by
  simp [petrovDisc, petrovI, petrovJ, h4, h3]
  ring

theorem petrov_triple_at_zero (ψ : Coefficients) (h4 : ψ 4 = 0) (h3 : ψ 3 = 0)
    (h2 : ψ 2 = 0) :
    petrovI ψ = 0 ∧ petrovJ ψ = 0 := by
  simp [petrovI, petrovJ, h4, h3, h2]

/-- Divisibility in the finite chart, or vanishing through the same order in the chart at infinity. -/
def principalMultiplicityAtLeast (ψ : Coefficients) (r : Option ℂ) (n : ℕ) : Prop :=
  match r with
  | some z => (X - C z) ^ n ∣ weylPolynomial ψ
  | none => X ^ n ∣ weylPolynomial (sl2cAct invertChart ψ)

private theorem to_zero_chart (ψ : Coefficients) (r : Option ℂ) (n : ℕ) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℂ, M.det = 1 ∧
      (principalMultiplicityAtLeast ψ r n ↔ X ^ n ∣ weylPolynomial (sl2cAct M ψ)) := by
  cases r with
  | none => exact ⟨invertChart, by norm_num [Matrix.det_fin_two, invertChart], Iff.rfl⟩
  | some z =>
    refine ⟨translate z, by simp [Matrix.det_fin_two, translate], ?_⟩
    rw [principalMultiplicityAtLeast, weylPolynomial_translate, X_sub_C_pow_dvd_iff]

theorem petrov_repeated_pnd (ψ : Coefficients) (r : Option ℂ)
    (hr : principalMultiplicityAtLeast ψ r 2) : petrovDisc ψ = 0 := by
  obtain ⟨M, hM, hChart⟩ := to_zero_chart ψ r 2
  have h := X_pow_dvd_iff.mp (hChart.mp hr)
  have h4 := h 0 (by decide)
  have h3 := h 1 (by decide)
  rw [weylPolynomial_coeff] at h4 h3
  have ha : sl2cAct M ψ 4 = 0 := by simpa using h4
  have hb : sl2cAct M ψ 3 = 0 := by simpa using h3
  rw [← (petrov_invariants_sl2c_invariant M ψ hM).2.2]
  exact petrov_repeated_at_zero _ ha hb

theorem petrov_triple_pnd (ψ : Coefficients) (r : Option ℂ)
    (hr : principalMultiplicityAtLeast ψ r 3) : petrovI ψ = 0 ∧ petrovJ ψ = 0 := by
  obtain ⟨M, hM, hChart⟩ := to_zero_chart ψ r 3
  have h := X_pow_dvd_iff.mp (hChart.mp hr)
  have h4 := h 0 (by decide)
  have h3 := h 1 (by decide)
  have h2 := h 2 (by decide)
  rw [weylPolynomial_coeff] at h4 h3 h2
  have ha : sl2cAct M ψ 4 = 0 := by simpa using h4
  have hb : sl2cAct M ψ 3 = 0 := by simpa using h3
  have hc : sl2cAct M ψ 2 = 0 := by simpa using h2
  have hinv := petrov_invariants_sl2c_invariant M ψ hM
  rw [← hinv.1, ← hinv.2.1]
  exact petrov_triple_at_zero _ ha hb hc


/-- The canonical representatives in the finite chart and in the chart at infinity. -/
theorem petrov_canonical_chart_polynomials (c d : ℂ) :
    weylPolynomial (psiD c) = monomial 2 (6 * c) ∧
      weylPolynomial (sl2cAct invertChart (psiD c)) = monomial 2 (6 * c) ∧
    weylPolynomial (psiII c d) = monomial 2 (6 * c) + C d ∧
      weylPolynomial (sl2cAct invertChart (psiII c d)) = monomial 4 d + monomial 2 (6 * c) ∧
    weylPolynomial (psiIII c) = monomial 1 (4 * c) ∧
      weylPolynomial (sl2cAct invertChart (psiIII c)) = monomial 3 (-4 * c) ∧
    weylPolynomial (psiN c) = C c ∧
      weylPolynomial (sl2cAct invertChart (psiN c)) = monomial 4 c ∧
    weylPolynomial (0 : Coefficients) = 0 := by
  simp [weylPolynomial, sl2cAct, invertChart, psiD, psiII, psiIII, psiN, ← neg_mul]

/-- Multiplicity at a finite principal direction agrees with polynomial root multiplicity
for every nonzero binary quartic. -/
theorem principalMultiplicity_finite (ψ : Coefficients) (z : ℂ) (n : ℕ)
    (hψ : weylPolynomial ψ ≠ 0) :
    principalMultiplicityAtLeast ψ (some z) n ↔ n ≤ (weylPolynomial ψ).rootMultiplicity z :=
  (le_rootMultiplicity_iff hψ).symm

private theorem monomial_multiplicity_at_zero {c : ℂ} (hc : c ≠ 0) (n k : ℕ) :
    X ^ n ∣ monomial k c ↔ n ≤ k := by
  rw [X_pow_dvd_iff]
  constructor
  · intro h
    by_contra hn
    have hz := h k (by omega)
    exact hc (by simpa using hz)
  · intro h d hd
    exact by simp [coeff_monomial, show k ≠ d by omega]

theorem petrov_typeD_principal_multiplicities (c : ℂ) (hc : c ≠ 0) (n : ℕ) :
    (principalMultiplicityAtLeast (psiD c) (some 0) n ↔ n ≤ 2) ∧
    (principalMultiplicityAtLeast (psiD c) none n ↔ n ≤ 2) := by
  have hc' : 6 * c ≠ 0 := mul_ne_zero (by norm_num) hc
  simp [principalMultiplicityAtLeast, (petrov_canonical_chart_polynomials c 0).1,
    (petrov_canonical_chart_polynomials c 0).2.1, monomial_multiplicity_at_zero hc']

theorem petrov_typeII_principal_multiplicities (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0) :
    (principalMultiplicityAtLeast (psiII c d) none 2 ∧
      ¬ principalMultiplicityAtLeast (psiII c d) none 3) ∧
    ∃ z : ℂ, z ≠ -z ∧ ∀ w : ℂ,
      ((weylPolynomial (psiII c d)).eval w = 0 ↔ w = z ∨ w = -z) ∧
      ¬ principalMultiplicityAtLeast (psiII c d) (some w) 2 := by
  have hpoly := (petrov_canonical_chart_polynomials c d).2.2
  constructor
  · simp only [principalMultiplicityAtLeast, hpoly.2.1, X_pow_dvd_iff, coeff_add]
    constructor
    · intro k hk
      interval_cases k <;> norm_num [coeff_monomial]
    · intro h
      have hs := h 2 (by decide)
      norm_num [coeff_monomial, hc] at hs
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-d / (6 * c)) (by decide : 0 < 2)
    have h6 : 6 * c ≠ 0 := mul_ne_zero (by norm_num) hc
    have hz' : 6 * c * z ^ 2 = -d := by rw [hz, mul_div_cancel₀ _ h6]
    have hz0 : z ≠ 0 := by
      intro h
      apply hd
      simpa [h] using hz'.symm
    have hp : weylPolynomial (psiII c d) ≠ 0 := by
      intro h
      have hs := congrArg (fun p : ℂ[X] => p.coeff 2) h
      norm_num [hpoly.1, coeff_monomial, hc] at hs
    have roots (w : ℂ) : (weylPolynomial (psiII c d)).eval w = 0 ↔ w = z ∨ w = -z := by
      rw [← sq_eq_sq_iff_eq_or_eq_neg, hpoly.1]
      simp only [eval_add, eval_C, eval_monomial]
      have he : 6 * c * w ^ 2 + d = (6 * c) * (w ^ 2 - z ^ 2) := by
        linear_combination hz'
      rw [he, mul_eq_zero, or_iff_right h6, sub_eq_zero]
    refine ⟨z, fun h => hz0 (by linear_combination h / 2), fun w => ⟨roots w, fun hw => ?_⟩⟩
    have hm := (principalMultiplicity_finite (psiII c d) w 2 hp).mp hw
    obtain ⟨hr, hdr⟩ := (one_lt_rootMultiplicity_iff_isRoot hp).mp hm
    have h0 : w ≠ 0 := by
      rcases (roots w).mp hr with rfl | rfl
      · exact hz0
      · exact neg_ne_zero.mpr hz0
    change (derivative (weylPolynomial (psiII c d))).eval w = 0 at hdr
    norm_num [hpoly.1, derivative_monomial, hc, h0] at hdr

theorem petrov_typeIII_and_typeN_principal_multiplicities (c : ℂ) (hc : c ≠ 0) (n : ℕ) :
    (principalMultiplicityAtLeast (psiIII c) (some 0) n ↔ n ≤ 1) ∧
    (principalMultiplicityAtLeast (psiIII c) none n ↔ n ≤ 3) ∧
    (principalMultiplicityAtLeast (psiN c) none n ↔ n ≤ 4) := by
  have h := (petrov_canonical_chart_polynomials c 0).2.2.2.2
  simp [principalMultiplicityAtLeast, h.1, h.2.1, h.2.2.2.1,
    monomial_multiplicity_at_zero hc,
    monomial_multiplicity_at_zero (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hc)]

theorem petrov_typeI_has_no_repeated_direction (a b : ℂ)
    (ha : a ≠ 0) (hp : a ≠ 3 * b) (hm : a ≠ -3 * b) (r : Option ℂ) :
    ¬ principalMultiplicityAtLeast (psiI a b) r 2 := by
  intro h
  exact (petrov_typeI a b).2 ha hp hm (petrov_repeated_pnd _ r h)

theorem petrov_typeO (r : Option ℂ) (n : ℕ) :
    petrovI (0 : Coefficients) = 0 ∧ petrovJ (0 : Coefficients) = 0 ∧
      petrovDisc (0 : Coefficients) = 0 ∧ principalMultiplicityAtLeast 0 r n := by
  cases r <;> simp [petrovI, petrovJ, petrovDisc, principalMultiplicityAtLeast, weylPolynomial,
    sl2cAct]

end Omega.BinaryQuarticSpinor
