/- GID: D5/S3/Quantum/Measurement/LudersSubObservableClosure
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/LudersSubObservableClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/LudersSubObservableClosure.claim; result=D5/S3/Quantum/Measurement/LudersSubObservableClosure.result; claim=D5/S3/Quantum/Measurement/LudersSubObservableClosure.claim
   digest: An unsharp two-outcome qubit Lüders instrument violates ambient Sob sum closure. -/

/- Per-declaration proof classification:
   effect_iff_owner: proof_shape: bind-only; escape_witness: none;
     consumers: a_mem, double_not_effect, double_not_mem, double_subobservable, e_effect;
     direct frozen dependencies: effect-owner.
   k_psd: proof_shape: bind-only; escape_witness: none;
     consumers: double_subobservable, result;
     direct frozen dependencies: none.
   k_complete: proof_shape: bind-only; escape_witness: none;
     consumers: result;
     direct frozen dependencies: none.
   e_effect: proof_shape: bind-only; escape_witness: none;
     consumers: a_mem, double_subobservable;
     direct frozen dependencies: effect-owner.
   a_mem: proof_shape: bind-only; escape_witness: none;
     consumers: not_sob;
     direct frozen dependencies: block-owner, effect-owner.
   double_subobservable: proof_shape: bind-only; escape_witness: none;
     consumers: not_sob;
     direct frozen dependencies: block-owner, effect-owner.
   preimage_eq: proof_shape: bind-only; escape_witness: none;
     consumers: double_not_mem;
     direct frozen dependencies: block-owner.
   double_quadratic_form: proof_shape: bind-only; escape_witness: none;
     consumers: double_not_effect;
     direct frozen dependencies: none.
   double_not_effect: proof_shape: bind-only; escape_witness: none;
     consumers: double_not_mem;
     direct frozen dependencies: effect-owner.
   double_not_mem: proof_shape: bind-only; escape_witness: none;
     consumers: not_sob;
     direct frozen dependencies: block-owner, effect-owner.
   not_sob: proof_shape: bind-only; escape_witness: none;
     consumers: result;
     direct frozen dependencies: block-owner, effect-owner.
   result: proof_shape: bind-only; escape_witness: none;
     admission_basis: open-problem-resolution (#16759; Proved);
     direct frozen dependencies: block-owner, effect-owner.
   Direct frozen dependency identities:
   effect-owner:
     GID: D5/S0/Diagonal/Lawvere/TypedEscapeNeedsPositivity
     declaration: D5.S0.Diagonal.Lawvere.TypedEscapeNeedsPositivity.IsEffect
     statement_id: sha256:5f32d535fdc03150ce20023e4cc4a396bcc2873b7a155c0db6acf48dd7fdb634
   block-owner:
     GID: D5/S3/Quantum/Bogoliubov/HardyBlockConservation
     declaration: D5.S3.Quantum.Bogoliubov.HardyBlockConservation.compressedBlock
     statement_id: sha256:2ac1332dea41c82e6801ecbf96346c6b514d05a0d9b6a632a6962d7efbaf156d
   The claim states the preregistered effect body literally in ludersImage, and
   the proofs use TypedEscapeNeedsPositivity.IsEffect under MatrixOrder.
   The family A uses HardyBlockConservation.compressedBlock (K x) E.
   The public result is the designated refutation result (`basis=refutes`) and
   is exempt from four-slot escape registration (CLAUDE.md §3.9).
   The observable condition is inlined as IsSubObservable Z and sum Z = 1;
   ConcealmentKernelNecessityRefutation.IsPOVM states that condition and has
   generality I; it is not on this module's dependency path.
   FiniteKrausRepresentation is unfrozen; matrix positivity and cancellation
   use pinned Mathlib directly. -/

import D5.S0.Diagonal.Lawvere.TypedEscapeNeedsPositivity
import D5.S3.Quantum.Bogoliubov.HardyBlockConservation
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Measurement.LudersSubObservableClosure

variable {d n : ℕ}

def IsSubObservable (A : Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ x, (A x).PosSemidef) ∧ (1 - ∑ x, A x).PosSemidef

def IsSobEffectAlgebra (U : Set (Fin n → Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  (∀ A ∈ U, IsSubObservable A) ∧ ∃ Z ∈ U, (IsSubObservable Z ∧ ∑ x, Z x = 1) ∧
    (∀ A ∈ U, Z - A ∈ U) ∧
    ∀ A ∈ U, ∀ B ∈ U, IsSubObservable (A + B) → A + B ∈ U

def ludersImage (K : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    Set (Fin n → Matrix (Fin d) (Fin d) ℂ) :=
  {A | ∃ a, (a.PosSemidef ∧ (1 - a).PosSemidef) ∧ A = fun x => K x * a * K x}

def claim : Prop :=
  ∀ (d n : ℕ) (K : Fin n → Matrix (Fin d) (Fin d) ℂ),
    (∀ x, (K x).PosSemidef) → ∑ x, K x * K x = 1 →
    IsSobEffectAlgebra (ludersImage K)

private def K : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![Matrix.diagonal ![(4/5 : ℂ), (3/5 : ℂ)],
    Matrix.diagonal ![(3/5 : ℂ), (4/5 : ℂ)]]

private def E : Matrix (Fin 2) (Fin 2) ℂ := (1/400 : ℂ) • !![(151 : ℂ), 50; 50, 151]
private def A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := fun x =>
  D5.S3.Quantum.Bogoliubov.HardyBlockConservation.compressedBlock (K x) E

private theorem effect_iff_owner (a : Matrix (Fin d) (Fin d) ℂ) :
    (a.PosSemidef ∧ (1 - a).PosSemidef) ↔
      D5.S0.Diagonal.Lawvere.TypedEscapeNeedsPositivity.IsEffect a := by
  unfold D5.S0.Diagonal.Lawvere.TypedEscapeNeedsPositivity.IsEffect
  rw [Matrix.nonneg_iff_posSemidef, Matrix.le_iff]

private theorem k_psd (x : Fin 2) : (K x).PosSemidef := by
  fin_cases x <;> dsimp [K] <;> apply Matrix.PosSemidef.diagonal <;>
    intro i <;> fin_cases i <;> norm_num [Complex.le_def]

private theorem k_complete : ∑ x, K x * K x = 1 := by
  rw [Fin.sum_univ_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

private theorem e_effect :
    D5.S0.Diagonal.Lawvere.TypedEscapeNeedsPositivity.IsEffect E := by
  apply (effect_iff_owner E).mp
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

private theorem a_mem : A ∈ ludersImage K := ⟨E, (effect_iff_owner E).mpr e_effect, rfl⟩

private theorem double_subobservable : IsSubObservable (A + A) := by
  constructor
  · intro x
    have h : (K x * E * K x).PosSemidef := by
      simpa only [(k_psd x).isHermitian.eq] using
        ((effect_iff_owner E).mpr e_effect).1.conjTranspose_mul_mul_same (K x)
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
      norm_num [A, D5.S3.Quantum.Bogoliubov.HardyBlockConservation.compressedBlock,
        K, E, Fin.sum_univ_two, Matrix.mul_apply, Matrix.diagonal,
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

private theorem double_not_effect :
    ¬ D5.S0.Diagonal.Lawvere.TypedEscapeNeedsPositivity.IsEffect (E + E) := by
  intro h
  have hn := ((effect_iff_owner (E + E)).mpr h).2.dotProduct_mulVec_nonneg (![(1 : ℂ), 1])
  rw [double_quadratic_form] at hn
  norm_num [Complex.le_def] at hn

private theorem double_not_mem : A + A ∉ ludersImage K := by
  rintro ⟨a, ha, h⟩
  have he := preimage_eq a h
  exact double_not_effect (he ▸ (effect_iff_owner a).mp ha)

private theorem not_sob : ¬ IsSobEffectAlgebra (ludersImage K) := by
  rintro ⟨_, Z, _, _, _, hclosure⟩
  exact double_not_mem (hclosure A a_mem A a_mem double_subobservable)

theorem result : ¬ claim := by
  intro h
  exact not_sob (h 2 2 K k_psd k_complete)

end D5.S3.Quantum.Measurement.LudersSubObservableClosure
