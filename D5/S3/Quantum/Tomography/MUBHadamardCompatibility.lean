/- GID: D5/S3/Quantum/Tomography/MUBHadamardCompatibility
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBHadamardCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Four MUBs in dimension six reduce to a gauge-retaining compatibility problem over exact complex-Hadamard atlases. -/

import D5.S3.Quantum.Tomography.MutuallyUnbiasedDiagonalPlanes
import Mathlib.Tactic.FinCases

/- Library-search audit trail (2026-09-03):
   * Repository exact hits `RankOneContext`, `overlap`, `incompatibility`,
     `centeredContextPlane`, `aggregated_rank_one_context_commutator`, and
     `mutually_unbiased_diagonal_planes` are reused below.
   * The public Lean audit accompanying arXiv:2608.18053 supplies an order-six
     complex-Hadamard predicate, the standard row/column monomial equivalence,
     and a paper-facing finite-corner classification theorem. This module does
     not import that repository or assume its classification. Instead it states
     the exact atlas contract that any independently verified classification
     must satisfy before it can be consumed by the MUB problem.
   * Pinned Mathlib and repository searches found no declaration stating the
     gauge-retaining atlas reduction or showing that independent Hadamard class
     representatives fail to preserve mutual-unbiasedness compatibility.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBHadamardCompatibility

open Matrix
open D5.S3.Observer.Conditioning
open D5.S3.Quantum.Tomography.OneStepProbabilityInnovation
open D5.S3.Quantum.Tomography.RankOneContextCommutator
open D5.S3.Quantum.Tomography.MutuallyUnbiasedDiagonalPlanes

/-- A square complex matrix on the finite coordinate carrier `n`. -/
abbrev ComplexSquare (n : Type*) := Matrix n n ℂ

/-- Every matrix entry has unit squared complex norm. -/
def EntrywiseUnit {m n : Type*} (A : Matrix m n ℂ) : Prop :=
  ∀ i j, Complex.normSq (A i j) = 1

/-- The unnormalized complex Hadamard condition in arbitrary finite order. -/
def IsComplexHadamard {n : Type*} [Fintype n] [DecidableEq n]
    (H : ComplexSquare n) : Prop :=
  EntrywiseUnit H ∧
    H * Hᴴ = (Fintype.card n : ℂ) • (1 : ComplexSquare n)

/-- Standard complex-Hadamard equivalence: permute rows and columns, then
multiply them by unit phases. -/
def HadamardEquivalent {n : Type*} (H K : ComplexSquare n) : Prop :=
  ∃ (σ τ : Equiv.Perm n) (r c : n → ℂ),
    (∀ i, Complex.normSq (r i) = 1) ∧
    (∀ j, Complex.normSq (c j) = 1) ∧
    ∀ i j, K i j = r i * H (σ i) (τ j) * c j

private theorem star_mul_self_of_normSq_one {z : ℂ}
    (hz : Complex.normSq z = 1) : star z * z = 1 := by
  simpa [Complex.star_def, Complex.normSq_eq_conj_mul_self] using
    congrArg (fun a : ℝ ↦ (a : ℂ)) hz

/-- Hadamard equivalence is reflexive. -/
theorem hadamardEquivalent_refl {n : Type*} (H : ComplexSquare n) :
    HadamardEquivalent H H := by
  refine ⟨Equiv.refl n, Equiv.refl n, (fun _ ↦ 1), (fun _ ↦ 1), ?_, ?_, ?_⟩
  · intro i
    simp
  · intro j
    simp
  · intro i j
    simp

/-- Hadamard equivalence is transitive. -/
theorem hadamardEquivalent_trans {n : Type*} {H K L : ComplexSquare n}
    (hHK : HadamardEquivalent H K) (hKL : HadamardEquivalent K L) :
    HadamardEquivalent H L := by
  rcases hHK with ⟨σ₁, τ₁, r₁, c₁, hr₁, hc₁, hHK⟩
  rcases hKL with ⟨σ₂, τ₂, r₂, c₂, hr₂, hc₂, hKL⟩
  refine ⟨σ₂.trans σ₁, τ₂.trans τ₁,
    (fun i ↦ r₂ i * r₁ (σ₂ i)),
    (fun j ↦ c₁ (τ₂ j) * c₂ j), ?_, ?_, ?_⟩
  · intro i
    simp [Complex.normSq_mul, hr₂ i, hr₁ (σ₂ i)]
  · intro j
    simp [Complex.normSq_mul, hc₁ (τ₂ j), hc₂ j]
  · intro i j
    rw [hKL, hHK]
    simp only [Equiv.trans_apply]
    ring

/-- Hadamard equivalence is symmetric. -/
theorem hadamardEquivalent_symm {n : Type*} {H K : ComplexSquare n}
    (hHK : HadamardEquivalent H K) : HadamardEquivalent K H := by
  rcases hHK with ⟨σ, τ, r, c, hr, hc, hHK⟩
  refine ⟨σ.symm, τ.symm,
    (fun i ↦ star (r (σ.symm i))),
    (fun j ↦ star (c (τ.symm j))), ?_, ?_, ?_⟩
  · intro i
    simpa [Complex.normSq_conj] using hr (σ.symm i)
  · intro j
    simpa [Complex.normSq_conj] using hc (τ.symm j)
  · intro i j
    have h := hHK (σ.symm i) (τ.symm j)
    simp only [Equiv.apply_symm_apply] at h ⊢
    have hri : star (r (σ.symm i)) * r (σ.symm i) = 1 :=
      star_mul_self_of_normSq_one (hr (σ.symm i))
    have hcj : c (τ.symm j) * star (c (τ.symm j)) = 1 := by
      simpa [mul_comm] using
        star_mul_self_of_normSq_one (hc (τ.symm j))
    rw [h]
    symm
    calc
      star (r (σ.symm i)) *
          (r (σ.symm i) * H i j * c (τ.symm j)) *
          star (c (τ.symm j)) =
        (star (r (σ.symm i)) * r (σ.symm i)) * H i j *
          (c (τ.symm j) * star (c (τ.symm j))) := by ring
      _ = H i j := by rw [hri, hcj]; simp

/-- The unnormalized transition between two Hadamard matrices is flat. For
order `d`, this says every entry of `Hᴴ K` has squared norm `d`. -/
def HadamardUnbiased {n : Type*} [Fintype n]
    (H K : ComplexSquare n) : Prop :=
  ∀ i j, Complex.normSq ((Hᴴ * K) i j) = (Fintype.card n : ℝ)

/-- Hadamard mutual unbiasedness is symmetric. -/
theorem hadamardUnbiased_symm {n : Type*} [Fintype n]
    {H K : ComplexSquare n} (hHK : HadamardUnbiased H K) :
    HadamardUnbiased K H := by
  intro i j
  rw [show Kᴴ * H = (Hᴴ * K)ᴴ by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]]
  simpa [Matrix.conjTranspose_apply, Complex.normSq_conj] using hHK j i

/-- The coordinate carrier used by the exact order-six Hadamard audit. -/
abbrev I6 := Fin 3 ⊕ Fin 3

/-- A complex square matrix of order six. -/
abbrev Mat6 := ComplexSquare I6

/-- After fixing the first of four MUBs to the coordinate basis, the remaining
three bases are represented by three order-six complex Hadamard matrices whose
pairwise transitions are also flat. -/
structure FourMUBHadamardWitness where
  matrix : Fin 3 → Mat6
  hadamard : ∀ r, IsComplexHadamard (matrix r)
  unbiased : ∀ r s, r ≠ s → HadamardUnbiased (matrix r) (matrix s)

/-- An exact atlas contains a representative, with an explicit standard
Hadamard-equivalence lift, for every complex Hadamard matrix and only for such
matrices. -/
def IsExactHadamardAtlas (atlas : Set Mat6) : Prop :=
  ∀ H, IsComplexHadamard H ↔
    ∃ A, A ∈ atlas ∧ HadamardEquivalent A H

/-- The compatibility problem that an exact single-matrix atlas must solve.
Each selected atlas representative is lifted separately into a common ambient
coordinate frame before pairwise unbiasedness is tested. -/
def HasLiftedFourMUBWitness (atlas : Set Mat6) : Prop :=
  ∃ H : Fin 3 → Mat6,
    (∀ r, ∃ A, A ∈ atlas ∧ HadamardEquivalent A (H r)) ∧
      ∀ r s, r ≠ s → HadamardUnbiased (H r) (H s)

/-- Any exact order-six Hadamard atlas reduces the four-MUB question precisely
to the gauge-retaining lifted compatibility problem over three atlas entries. -/
theorem nonempty_fourMUBHadamardWitness_iff_lifted_atlas
    (atlas : Set Mat6) (hAtlas : IsExactHadamardAtlas atlas) :
    Nonempty FourMUBHadamardWitness ↔ HasLiftedFourMUBWitness atlas := by
  constructor
  · rintro ⟨witness⟩
    refine ⟨witness.matrix, ?_, witness.unbiased⟩
    intro r
    exact (hAtlas (witness.matrix r)).mp (witness.hadamard r)
  · rintro ⟨matrix, hAtlasMembership, hUnbiased⟩
    refine ⟨{
      matrix := matrix
      hadamard := ?_
      unbiased := hUnbiased
    }⟩
    intro r
    exact (hAtlas (matrix r)).mpr (hAtlasMembership r)

/-- A certificate excluding every lifted atlas triple excludes the normalized
Hadamard form of four mutually unbiased bases. -/
theorem no_fourMUBHadamardWitness_of_no_lifted_atlas
    (atlas : Set Mat6) (hAtlas : IsExactHadamardAtlas atlas)
    (hExclude : ¬ HasLiftedFourMUBWitness atlas) :
    ¬ Nonempty FourMUBHadamardWitness := by
  intro hWitness
  exact hExclude
    ((nonempty_fourMUBHadamardWitness_iff_lifted_atlas atlas hAtlas).mp hWitness)

/-! ## Independent class representatives lose relative MUB geometry -/

private abbrev Mat2 := ComplexSquare (Fin 2)

private def fourierTwo : Mat2 :=
  !![1, 1;
     1, -1]

private def phasedFourierTwo : Mat2 :=
  !![1, 1;
     Complex.I, -Complex.I]

private def rowPhaseTwo : Fin 2 → ℂ :=
  ![1, Complex.I]

private theorem fourierTwo_isComplexHadamard :
    IsComplexHadamard fourierTwo := by
  refine ⟨?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [fourierTwo, Complex.normSq_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fourierTwo, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two]

private theorem phasedFourierTwo_isComplexHadamard :
    IsComplexHadamard phasedFourierTwo := by
  refine ⟨?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [phasedFourierTwo, Complex.normSq_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [phasedFourierTwo, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Complex.star_def] <;> ring

private theorem fourierTwo_equivalent_phasedFourierTwo :
    HadamardEquivalent fourierTwo phasedFourierTwo := by
  refine ⟨Equiv.refl (Fin 2), Equiv.refl (Fin 2), rowPhaseTwo,
    (fun _ ↦ 1), ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [rowPhaseTwo, Complex.normSq_apply]
  · intro j
    simp
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [rowPhaseTwo, fourierTwo, phasedFourierTwo]

private theorem fourierTwo_unbiased_phasedFourierTwo :
    HadamardUnbiased fourierTwo phasedFourierTwo := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fourierTwo, phasedFourierTwo, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.normSq_apply]

private theorem fourierTwo_not_unbiased_self :
    ¬ HadamardUnbiased fourierTwo fourierTwo := by
  intro h
  have h00 := h (0 : Fin 2) (0 : Fin 2)
  norm_num [fourierTwo, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, Complex.normSq_apply] at h00

/-- Standard Hadamard equivalence does not descend mutual-unbiasedness to
independently chosen equivalence classes. A row phase turns one copy of the
order-two Fourier matrix into an unbiased partner of another copy, while the
unphased pair is not unbiased. Consequently an order-six classification must
retain relative equivalence witnesses when testing MUB extension. -/
theorem independent_hadamard_equivalence_does_not_preserve_unbiasedness :
    ∃ H K K' : Mat2,
      IsComplexHadamard H ∧
      IsComplexHadamard K ∧
      IsComplexHadamard K' ∧
      HadamardEquivalent K K' ∧
      HadamardUnbiased H K' ∧
      ¬ HadamardUnbiased H K := by
  exact ⟨fourierTwo, fourierTwo, phasedFourierTwo,
    fourierTwo_isComplexHadamard,
    fourierTwo_isComplexHadamard,
    phasedFourierTwo_isComplexHadamard,
    fourierTwo_equivalent_phasedFourierTwo,
    fourierTwo_unbiased_phasedFourierTwo,
    fourierTwo_not_unbiased_self⟩

/-! ## Existing rank-one projector consequences in dimension six -/

/-- Four pairwise mutually unbiased rank-one contexts in dimension six. -/
def IsFourMUBContextFamily
    (context : Fin 4 → RankOneContext 6) : Prop :=
  ∀ l k, l ≠ k → ∀ j r,
    overlap (context l) (context k) j r = (6 : ℝ)⁻¹

/-- Every distinct pair in a four-MUB context family has maximal normalized
incompatibility. -/
theorem fourMUBContexts_have_maximal_incompatibility
    (context : Fin 4 → RankOneContext 6)
    (hMUB : IsFourMUBContextFamily context) :
    ∀ l k, l ≠ k →
      incompatibility (context l) (context k) = 1 := by
  intro l k hlk
  norm_num [incompatibility, hMUB l k hlk]

/-- Under the existing record-measurement interface, distinct members of a
four-MUB context family have orthogonal centered projector planes. -/
theorem fourMUBContexts_have_pairwise_orthogonal_planes
    (context : Fin 4 → RankOneContext 6)
    (hRecord : ∀ l, IsRecordMeasurement (context l).projector)
    (hMUB : IsFourMUBContextFamily context) :
    ∀ l k, l ≠ k →
      centeredContextPlane (context l) ⟂ centeredContextPlane (context k) := by
  intro l k hlk
  exact ((mutually_unbiased_diagonal_planes
    (d := 6) (by norm_num) (context l) (context k)
    (hRecord l) (hRecord k)).1).mp (hMUB l k hlk)

/-- Distinct members of a dimension-six four-MUB context family have aggregate
squared rank-one commutator norm exactly ten. -/
theorem fourMUBContexts_have_commutator_sum_ten
    (context : Fin 4 → RankOneContext 6)
    (hMUB : IsFourMUBContextFamily context)
    (l k : Fin 4) (hlk : l ≠ k) :
    ∑ j, ∑ r,
        hilbertSchmidtSquare
          ((context l).projector j * (context k).projector r -
            (context k).projector r * (context l).projector j) = 10 := by
  rw [aggregated_rank_one_context_commutator
    (d := 6) (by norm_num) (context l) (context k)]
  rw [fourMUBContexts_have_maximal_incompatibility context hMUB l k hlk]
  norm_num

#print axioms nonempty_fourMUBHadamardWitness_iff_lifted_atlas
#print axioms independent_hadamard_equivalence_does_not_preserve_unbiasedness
#print axioms fourMUBContexts_have_maximal_incompatibility
#print axioms fourMUBContexts_have_pairwise_orthogonal_planes
#print axioms fourMUBContexts_have_commutator_sum_ten

end D5.S3.Quantum.Tomography.MUBHadamardCompatibility
