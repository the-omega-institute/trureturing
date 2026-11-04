/- GID: D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness
   generality: I
   mirror-B: D5/B/S3/HilbertOperators/ReversibleFourByFourNonuniqueness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.claim; result=D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.result; claim=D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.claim
   digest: Weighted anticommuting matrices refute unitary uniqueness of reversible algebras. -/

import Mathlib.Analysis.CStarAlgebra.Matrix

/-! The nonunital matrix-algebra reading of Blecher, arXiv:2509.17673v2,
Example 5.2 and its unitary-uniqueness conjecture; preregistration #24898. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false

noncomputable section
namespace D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness

open scoped Matrix.Norms.L2Operator

/-- Multiplicative closure of a complex matrix subspace; no unit is required. -/
def IsMatrixAlgebra (b : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ)) : Prop :=
  ∀ x ∈ b, ∀ y ∈ b, x * y ∈ b

/-- Two elements of the algebra fail to commute. -/
def IsNoncommutative (b : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ)) : Prop :=
  ∃ x ∈ b, ∃ y ∈ b, x * y ≠ y * x

/-- A completely isometric representation with reversed multiplication.
All block norms use the scoped `Matrix.instL2OpNormedAddCommGroup` instance. -/
def IsReversible (b : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ)) : Prop :=
  ∃ m : ℕ, 0 < m ∧
    ∃ ρ : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ,
      (∀ x ∈ b, ∀ y ∈ b, ρ (y * x) = ρ x * ρ y) ∧
      ∀ n (x : Fin n → Fin n → Matrix (Fin 4) (Fin 4) ℂ),
        (∀ i j, x i j ∈ b) →
        ‖Matrix.comp _ _ _ _ ℂ (fun i j => ρ (x i j))‖ = ‖Matrix.comp _ _ _ _ ℂ x‖

/-- The source CAR example, using zero-based indices for its matrix units. -/
def carAlgebra : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ) :=
  let u : Matrix (Fin 4) (Fin 4) ℂ := Matrix.single 0 2 1 + Matrix.single 1 3 1
  let v : Matrix (Fin 4) (Fin 4) ℂ := Matrix.single 0 1 1 - Matrix.single 2 3 1
  Submodule.span ℂ {u, v, u * v}

/-- Unitary conjugation identifies the two subspaces. -/
def UnitarilyEquivalent (b c : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ)) : Prop :=
  ∃ q : Matrix.unitaryGroup (Fin 4) ℂ,
    ∀ x, x ∈ b ↔ star (q : Matrix (Fin 4) (Fin 4) ℂ) * x * q ∈ c

/-- Blecher's unitary-uniqueness conjecture under the preregistered formal reading. -/
def claim : Prop :=
  ∀ b : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ),
    IsMatrixAlgebra b → IsNoncommutative b → IsReversible b →
      UnitarilyEquivalent b carAlgebra

private def form (t a b c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, t * b, t * a, c; 0, 0, 0, a; 0, 0, 0, -b; 0, 0, 0, 0]

private def witness : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ) :=
  Submodule.span ℂ {form 2 1 0 0, form 2 0 1 0, form 2 0 0 1}

private lemma form_linear (t a b c : ℂ) :
    a • form t 1 0 0 + b • form t 0 1 0 + c • form t 0 0 1 = form t a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;> (dsimp only [form]; simp [Matrix.add_apply, mul_comm])

private lemma witness_coordinates (x : Matrix (Fin 4) (Fin 4) ℂ) :
    x ∈ witness ↔ ∃ a b c : ℂ, form 2 a b c = x := by
  dsimp only [witness]
  simp only [Submodule.mem_span_triple, form_linear]

private lemma form_product (t a b c d e f : ℂ) :
    form t a b c * form t d e f = form t 0 0 (t * (b * d - a * e)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.mul_apply, Fin.sum_univ_succ]; dsimp only [form]; simp)
  ring

private lemma car_coordinates (x : Matrix (Fin 4) (Fin 4) ℂ) :
    x ∈ carAlgebra ↔ ∃ a b c : ℂ, form 1 a b c = x := by
  have hu : (Matrix.single 0 2 1 + Matrix.single 1 3 1 : Matrix (Fin 4) (Fin 4) ℂ) =
      form 1 1 0 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> (dsimp only [form]; simp)
  have hv : (Matrix.single 0 1 1 - Matrix.single 2 3 1 : Matrix (Fin 4) (Fin 4) ℂ) =
      form 1 0 1 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> (dsimp only [form]; simp)
  have hn : form 1 0 0 (-1) = -(form 1 0 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> (dsimp only [form]; simp)
  dsimp only [carAlgebra]
  simp only [hu, hv, form_product]
  norm_num only [mul_one, zero_mul, one_mul, zero_sub]
  rw [hn, Submodule.mem_span_triple]
  simp only [smul_neg, ← neg_smul, form_linear]
  constructor
  · rintro ⟨a, b, c, hc⟩
    exact ⟨a, b, -c, hc⟩
  · rintro ⟨a, b, c, hc⟩
    exact ⟨a, b, -c, by simpa only [neg_neg] using hc⟩

private lemma witness_algebra : IsMatrixAlgebra witness := by
  intro x hx y hy
  obtain ⟨a, b, c, rfl⟩ := (witness_coordinates x).mp hx
  obtain ⟨d, e, f, rfl⟩ := (witness_coordinates y).mp hy
  exact (witness_coordinates _).mpr ⟨0, 0, _, (form_product _ _ _ _ _ _ _).symm⟩

private lemma witness_anticommutes (x : Matrix (Fin 4) (Fin 4) ℂ) (hx : x ∈ witness)
    (y : Matrix (Fin 4) (Fin 4) ℂ) (hy : y ∈ witness) : x * y = -(y * x) := by
  obtain ⟨a, b, c, rfl⟩ := (witness_coordinates x).mp hx
  obtain ⟨d, e, f, rfl⟩ := (witness_coordinates y).mp hy
  rw [form_product, form_product]
  ext i j
  fin_cases i <;> fin_cases j <;> (dsimp only [form]; simp)
  ring

private lemma witness_noncommutative : IsNoncommutative witness := by
  refine ⟨form 2 1 0 0, (witness_coordinates _).mpr ⟨1, 0, 0, rfl⟩,
    form 2 0 1 0, (witness_coordinates _).mpr ⟨0, 1, 0, rfl⟩, ?_⟩
  intro h
  have he := congrArg (fun x : Matrix (Fin 4) (Fin 4) ℂ => x 0 3) h
  rw [form_product, form_product] at he
  dsimp only [form] at he
  norm_num at he

private lemma witness_reversible : IsReversible witness := by
  refine ⟨4, by decide, -LinearMap.id, ?_, ?_⟩
  · intro x hx y hy
    change -(y * x) = (-x) * (-y)
    rw [neg_mul_neg, witness_anticommutes x hx y hy]
  · intro n x hx
    change ‖Matrix.comp _ _ _ _ ℂ (fun i j => -(x i j))‖ = ‖Matrix.comp _ _ _ _ ℂ x‖
    exact norm_neg (Matrix.comp _ _ _ _ ℂ x)

private def delta (x : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  2 * Matrix.trace ((x * star x) ^ 2) - Matrix.trace (x * star x) ^ 2

private lemma delta_conjugate (q : Matrix.unitaryGroup (Fin 4) ℂ)
    (x : Matrix (Fin 4) (Fin 4) ℂ) : delta (Unitary.conjStarAlgAut ℂ _ (star q) x) = delta x := by
  dsimp only [delta]
  rw [← map_star, ← map_mul, ← map_pow]
  simp only [Unitary.conjStarAlgAut_star_apply]
  exact congrArg₂ (fun a b : ℂ => 2 * a - b ^ 2)
    (Matrix.trace_units_conj' (Unitary.toUnits q) ((x * star x) ^ 2))
    (Matrix.trace_units_conj' (Unitary.toUnits q) (x * star x))

private lemma car_delta (a b : ℂ) : delta (form 1 a b 0) = 0 := by
  dsimp only [delta]
  simp only [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.star_apply, Fin.sum_univ_succ]
  (dsimp only [form]; simp)
  ring

private lemma witness_delta : delta (form 2 1 0 0) = 9 := by
  dsimp only [delta]
  simp only [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.star_apply, Fin.sum_univ_succ]
  (dsimp only [form]; norm_num)

private lemma conjugate_product_line (q : Matrix.unitaryGroup (Fin 4) ℂ)
    (h : ∀ x ∈ witness, Unitary.conjStarAlgAut ℂ _ (star q) x ∈ carAlgebra) :
    ∃ t : ℂ, t ≠ 0 ∧ Unitary.conjStarAlgAut ℂ _ (star q) (form 2 0 0 1) = t • form 1 0 0 1 := by
  obtain ⟨a, b, c, hu⟩ := (car_coordinates _).mp
    (h _ ((witness_coordinates _).mpr ⟨1, 0, 0, rfl⟩))
  obtain ⟨d, e, f, hv⟩ := (car_coordinates _).mp
    (h _ ((witness_coordinates _).mpr ⟨0, 1, 0, rfl⟩))
  have hw : form 2 0 0 1 = (1 / 2 : ℂ) • (form 2 0 1 0 * form 2 1 0 0) := by
    rw [form_product]
    ext i j
    fin_cases i <;> fin_cases j <;> (dsimp only [form]; norm_num)
  have he : Unitary.conjStarAlgAut ℂ _ (star q) (form 2 0 0 1) =
      ((e * a - d * b) / 2) • form 1 0 0 1 := by
    rw [hw, map_smul, map_mul, ← hv, ← hu, form_product]
    ext i j
    fin_cases i <;> fin_cases j <;> (dsimp only [form]; simp)
    ring
  refine ⟨_, ?_, he⟩
  intro ht
  have hz : Unitary.conjStarAlgAut ℂ _ (star q) (form 2 0 0 1) = 0 := by rw [he, ht, zero_smul]
  have hwz : form 2 0 0 1 = 0 :=
    (Unitary.conjStarAlgAut ℂ _ (star q)).toRingEquiv.map_eq_zero_iff.mp hz
  have hh := congrArg (fun x : Matrix (Fin 4) (Fin 4) ℂ => x 0 3) hwz
  dsimp only [form] at hh
  norm_num at hh

private lemma conjugate_complement (q : Matrix.unitaryGroup (Fin 4) ℂ)
    (h : ∀ x ∈ witness, Unitary.conjStarAlgAut ℂ _ (star q) x ∈ carAlgebra) :
    ∃ a b : ℂ, Unitary.conjStarAlgAut ℂ _ (star q) (form 2 1 0 0) = form 1 a b 0 := by
  obtain ⟨t, ht, hw⟩ := conjugate_product_line q h
  obtain ⟨a, b, c, hu⟩ := (car_coordinates _).mp
    (h _ ((witness_coordinates _).mpr ⟨1, 0, 0, rfl⟩))
  have hz : Matrix.trace (star (Unitary.conjStarAlgAut ℂ _ (star q) (form 2 0 0 1)) *
      Unitary.conjStarAlgAut ℂ _ (star q) (form 2 1 0 0)) = 0 := by
    rw [← map_star, ← map_mul]
    simp only [Unitary.conjStarAlgAut_star_apply]
    calc
      _ = Matrix.trace (star (form 2 0 0 1) * form 2 1 0 0) :=
        Matrix.trace_units_conj' (Unitary.toUnits q) _
      _ = 0 := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply,
          Fin.sum_univ_succ]
        (dsimp only [form]; norm_num)
  rw [hw, ← hu] at hz
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply,
    Fin.sum_univ_succ] at hz
  dsimp only [form] at hz
  simp at hz
  have hc : c = 0 := hz.resolve_left ht
  exact ⟨a, b, by simpa only [hc] using hu.symm⟩

private lemma witness_not_equivalent : ¬ UnitarilyEquivalent witness carAlgebra := by
  rintro ⟨q, hq⟩
  have h : ∀ x ∈ witness, Unitary.conjStarAlgAut ℂ _ (star q) x ∈ carAlgebra := by
    intro x hx
    simpa only [Unitary.conjStarAlgAut_star_apply] using (hq x).mp hx
  obtain ⟨a, b, hab⟩ := conjugate_complement q h
  have hd := delta_conjugate q (form 2 1 0 0)
  rw [hab, car_delta, witness_delta] at hd
  norm_num at hd

/-- A second noncommutative reversible matrix algebra refutes unitary uniqueness. -/
theorem result : ¬ claim := by
  intro h
  exact witness_not_equivalent
    (h witness witness_algebra witness_noncommutative witness_reversible)

end D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness
