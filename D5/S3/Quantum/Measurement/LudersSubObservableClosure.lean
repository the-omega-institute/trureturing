/- GID: D5/S3/Quantum/Measurement/LudersSubObservableClosure
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/LudersSubObservableClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/LudersSubObservableClosure.claim; result=D5/S3/Quantum/Measurement/LudersSubObservableClosure.result; claim=D5/S3/Quantum/Measurement/LudersSubObservableClosure.claim
   digest: An unsharp two-outcome qubit Lüders instrument violates ambient Sob sum closure. -/

/- result
   proof_shape: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (#16759; Proved)
   Direct frozen dependencies: none.
   Private theorem classifications and consumers:
   k_psd: proof_shape: bind-only; consumers: double_subobservable, result.
   k_complete: proof_shape: bind-only; consumer: result.
   e_effect: proof_shape: bind-only; consumers: a_mem, double_subobservable.
   a_mem: proof_shape: bind-only; consumer: not_sob.
   double_subobservable: proof_shape: bind-only; consumer: not_sob.
   preimage_eq: proof_shape: bind-only; consumer: double_not_mem.
   double_quadratic_form: proof_shape: bind-only; consumer: double_not_effect.
   double_not_effect: proof_shape: bind-only; consumer: double_not_mem.
   double_not_mem: proof_shape: bind-only; consumer: not_sob.
   not_sob: proof_shape: bind-only; consumer: result.
   Each private theorem has escape_witness: none and Direct frozen dependencies: none.
   The public result is the designated refutation result (`basis=refutes`) and is
   exempt from four-slot escape registration (CLAUDE.md §3.9).
   The observable condition from #16759 is inlined as IsSubObservable Z together
   with sum Z = 1: the equivalent IsPOVM owner in
   ConcealmentKernelNecessityRefutation has generality I and is not duplicated.
   The proof uses only (S3), so it needs no observable correspondence lemma or import.
   FiniteKrausRepresentation is unfrozen; matrix positivity and cancellation use
   pinned Mathlib directly. -/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ComplexOrder
namespace D5.S3.Quantum.Measurement.LudersSubObservableClosure

variable {d n : ℕ}

def IsSubObservable (A : Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ x, (A x).PosSemidef) ∧ (1 - ∑ x, A x).PosSemidef

def IsEffect (a : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  a.PosSemidef ∧ (1 - a).PosSemidef

def IsSobEffectAlgebra (U : Set (Fin n → Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  (∀ A ∈ U, IsSubObservable A) ∧ ∃ Z ∈ U, (IsSubObservable Z ∧ ∑ x, Z x = 1) ∧
    (∀ A ∈ U, Z - A ∈ U) ∧
    ∀ A ∈ U, ∀ B ∈ U, IsSubObservable (A + B) → A + B ∈ U

def ludersImage (K : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    Set (Fin n → Matrix (Fin d) (Fin d) ℂ) :=
  {A | ∃ a, IsEffect a ∧ A = fun x => K x * a * K x}

def claim : Prop :=
  ∀ (d n : ℕ) (K : Fin n → Matrix (Fin d) (Fin d) ℂ),
    (∀ x, (K x).PosSemidef) → ∑ x, K x * K x = 1 →
    IsSobEffectAlgebra (ludersImage K)

private def K : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![Matrix.diagonal ![(4/5 : ℂ), (3/5 : ℂ)],
    Matrix.diagonal ![(3/5 : ℂ), (4/5 : ℂ)]]

private def E : Matrix (Fin 2) (Fin 2) ℂ := (1/400 : ℂ) • !![(151 : ℂ), 50; 50, 151]
private def A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := fun x => K x * E * K x

private theorem k_psd (x : Fin 2) : (K x).PosSemidef := by
  fin_cases x <;> dsimp [K] <;> apply Matrix.PosSemidef.diagonal <;>
    intro i <;> fin_cases i <;> norm_num [Complex.le_def]

private theorem k_complete : ∑ x, K x * K x = 1 := by
  rw [Fin.sum_univ_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

private theorem e_effect : IsEffect E := by
  have hp : (Matrix.vecMulVec ![(1 : ℂ), 1] (star ![(1 : ℂ), 1])).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star _
  have hm : (Matrix.vecMulVec ![(1 : ℂ), -1] (star ![(1 : ℂ), -1])).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star _
  constructor
  · have h := (hp.smul (show (0 : ℂ) ≤ 201/800 by norm_num [Complex.le_def])).add
      (hm.smul (show (0 : ℂ) ≤ 101/800 by norm_num [Complex.le_def]))
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [E, Matrix.vecMulVec, Pi.star_apply, RCLike.star_def]
  · have h := (hp.smul (show (0 : ℂ) ≤ 199/800 by norm_num [Complex.le_def])).add
      (hm.smul (show (0 : ℂ) ≤ 299/800 by norm_num [Complex.le_def]))
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [E, Matrix.vecMulVec, Pi.star_apply, RCLike.star_def]

private theorem a_mem : A ∈ ludersImage K := ⟨E, e_effect, rfl⟩

private theorem double_subobservable : IsSubObservable (A + A) := by
  constructor
  · intro x
    have h : (K x * E * K x).PosSemidef := by
      simpa only [(k_psd x).isHermitian.eq] using
        e_effect.1.conjTranspose_mul_mul_same (K x)
    exact h.add h
  · have hp : (Matrix.vecMulVec ![(1 : ℂ), 1] (star ![(1 : ℂ), 1])).PosSemidef :=
      Matrix.posSemidef_vecMulVec_self_star _
    have hm : (Matrix.vecMulVec ![(1 : ℂ), -1] (star ![(1 : ℂ), -1])).PosSemidef :=
      Matrix.posSemidef_vecMulVec_self_star _
    have h := (hp.smul (show (0 : ℂ) ≤ 1/400 by norm_num [Complex.le_def])).add
      (hm.smul (show (0 : ℂ) ≤ 97/400 by norm_num [Complex.le_def]))
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, K, E, Fin.sum_univ_two, Matrix.mul_apply, Matrix.diagonal,
        Matrix.vecMulVec, Pi.star_apply, RCLike.star_def]

private theorem preimage_eq (a : Matrix (Fin 2) (Fin 2) ℂ)
    (h : A + A = fun x => K x * a * K x) : a = E + E := by
  have hu : IsUnit (K 0) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    norm_num [K, Matrix.det_diagonal, Fin.prod_univ_two, isUnit_iff_ne_zero]
  have h0 := congrFun h 0
  change K 0 * E * K 0 + K 0 * E * K 0 = K 0 * a * K 0 at h0
  have he : K 0 * (E + E) * K 0 = K 0 * a * K 0 := by
    simpa only [Matrix.mul_add, Matrix.add_mul] using h0
  exact (hu.mul_left_cancel (hu.mul_right_cancel he)).symm

private theorem double_quadratic_form :
    dotProduct (star (![(1 : ℂ), 1])) (Matrix.mulVec (1 - (E + E)) ![(1 : ℂ), 1]) =
      (-1/100 : ℂ) := by
  norm_num [E, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
    Pi.star_apply, RCLike.star_def]

private theorem double_not_effect : ¬ IsEffect (E + E) := by
  intro h
  have hn := h.2.dotProduct_mulVec_nonneg (![(1 : ℂ), 1])
  rw [double_quadratic_form] at hn
  norm_num [Complex.le_def] at hn

private theorem double_not_mem : A + A ∉ ludersImage K := by
  rintro ⟨a, ha, h⟩
  have he := preimage_eq a h
  exact double_not_effect (he ▸ ha)

private theorem not_sob : ¬ IsSobEffectAlgebra (ludersImage K) := by
  rintro ⟨_, Z, _, _, _, hclosure⟩
  exact double_not_mem (hclosure A a_mem A a_mem double_subobservable)

theorem result : ¬ claim := by
  intro h
  exact not_sob (h 2 2 K k_psd k_complete)

end D5.S3.Quantum.Measurement.LudersSubObservableClosure
