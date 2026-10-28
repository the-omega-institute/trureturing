/- GID: D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.claim; result=D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.result; claim=D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.claim
   digest: A stable two-block matrix has an unstable asynchronous iteration with unit delays. -/

import D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs
import D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-! A stable two-block iteration becomes unstable when only remote entries are delayed. -/

noncomputable section

open Matrix
open D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs (Vtx)
open scoped ENNReal NNReal

namespace D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation

/-- The history state has the newest iterate in slot zero. -/
def asyncMatrix {ℓ : ℕ} {n : Fin ℓ → ℕ}
    (M : Matrix (Vtx n) (Vtx n) ℝ)
    (δ : Fin ℓ → Fin ℓ → ℕ) (k : ℕ) :
    Matrix (Fin (k + 1) × Vtx n) (Fin (k + 1) × Vtx n) ℝ :=
  fun rp sq =>
    if rp.1.val = 0 then
      if sq.1.val = δ sq.2.1 rp.2.1 then M rp.2 sq.2 else 0
    else if sq.1.val + 1 = rp.1.val ∧ sq.2 = rp.2 then 1 else 0

/-- The spectral radius is taken after extension of scalars to the complex numbers. -/
def radius {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : ℝ≥0∞ :=
  spectralRadius ℂ (M.map (algebraMap ℝ ℂ))

/-- Nonempty blocks, zero local delay, bounded positive remote delays, and a stable radius. -/
def Admissible (ℓ : ℕ) (n : Fin ℓ → ℕ) (k : ℕ)
    (M : Matrix (Vtx n) (Vtx n) ℝ)
    (δ : Fin ℓ → Fin ℓ → ℕ) (lambda : ℝ) : Prop :=
  (∀ i, 0 < n i) ∧ (∀ i, δ i i = 0) ∧
    (∀ i j, i ≠ j → 1 ≤ δ i j ∧ δ i j ≤ k) ∧
    0 < lambda ∧ lambda < 1 ∧ radius M = ENNReal.ofReal lambda

/-- The proposed power bound, uniformly over block arrays and admissible delays. -/
def Q1 : Prop :=
  ∀ (ℓ : ℕ) (n : Fin ℓ → ℕ) (k : ℕ)
    (M : Matrix (Vtx n) (Vtx n) ℝ)
    (δ : Fin ℓ → Fin ℓ → ℕ) (lambda : ℝ),
    Admissible ℓ n k M δ lambda →
      radius (asyncMatrix M δ k) ≤ ENNReal.ofReal (lambda ^ ((1 : ℝ) / (k + 1)))

/-- A uniformly subunit bound depending only on the original radius and maximum delay. -/
def Q2 : Prop :=
  ∃ f : ℝ → ℕ → ℝ,
    (∀ lambda k, 0 < lambda → lambda < 1 → 0 < f lambda k ∧ f lambda k < 1) ∧
    ∀ (ℓ : ℕ) (n : Fin ℓ → ℕ) (k : ℕ)
      (M : Matrix (Vtx n) (Vtx n) ℝ)
      (δ : Fin ℓ → Fin ℓ → ℕ) (lambda : ℝ),
      Admissible ℓ n k M δ lambda →
        radius (asyncMatrix M δ k) ≤ ENNReal.ofReal (f lambda k)

/-- At least one of the two proposed bounds for the price of asynchrony holds. -/
def claim : Prop := Q1 ∨ Q2

private def baseMatrix : Matrix (Vtx (fun _ : Fin 2 => 1)) (Vtx (fun _ : Fin 2 => 1)) ℝ :=
  fun p q => if p.1 = 0 then (if q.1 = 0 then 7 / 4 else 5 / 4)
    else (if q.1 = 0 then -5 / 4 else -3 / 4)

private def unstableVector : Fin 2 × Vtx (fun _ : Fin 2 => 1) → ℂ :=
  fun rp => if rp.1 = 0 then (if rp.2.1 = 0 then 10 else -5)
    else (if rp.2.1 = 0 then 8 else -4)

private theorem base_square_zero :
    (baseMatrix.map (algebraMap ℝ ℂ) -
      algebraMap ℂ (Matrix (Vtx (fun _ : Fin 2 => 1)) (Vtx (fun _ : Fin 2 => 1)) ℂ)
        (1 / 2)) ^ 2 = 0 := by
  delta baseMatrix Matrix.map
  apply Matrix.ext
  rintro ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [pow_two, Matrix.mul_apply, Fintype.sum_sigma, Fin.sum_univ_two, Fin.sum_univ_succ,
      Matrix.map_apply, Matrix.algebraMap_eq_diagonal,
      Matrix.diagonal_apply, Fintype.sum_unique]

private theorem base_spectrum :
    spectrum ℂ (baseMatrix.map (algebraMap ℝ ℂ)) = {(1 / 2 : ℂ)} := by
  let A := baseMatrix.map (algebraMap ℝ ℂ)
  have hsquare : (A - algebraMap ℂ _ (1 / 2)) ^ 2 = 0 := base_square_zero
  apply Set.Subset.antisymm
  · intro z hz
    have hshift : z - 1 / 2 ∈ spectrum ℂ (A - algebraMap ℂ _ (1 / 2)) := by
      have hh := (spectrum.add_mem_iff (a := A) (r := z - 1 / 2) (s := 1 / 2)).mp
        (by simpa only [sub_add_cancel] using hz)
      simpa only [neg_add_eq_sub] using hh
    have hpow := spectrum.pow_mem_pow _ 2 hshift
    rw [hsquare, spectrum.zero_eq] at hpow
    exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow))
  · rw [Set.singleton_subset_iff, spectrum.mem_iff]
    apply IsNilpotent.not_isUnit
    refine ⟨2, ?_⟩
    rw [← neg_sub A, neg_sq, hsquare]

private theorem base_radius : radius baseMatrix = ENNReal.ofReal (1 / 2) := by
  unfold radius
  rw [spectralRadius_eq_of_unital, base_spectrum]
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left]
  convert (ENNReal.ofReal_coe_nnreal (p := ‖(1 / 2 : ℂ)‖₊)).symm using 1
  norm_num [coe_nnnorm, norm_div]

private theorem witness_admissible :
    Admissible 2 (fun _ => 1) 1 baseMatrix ((⊤ : SimpleGraph (Fin 2)).adjMatrix ℕ)
      (1 / 2) := by
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, base_radius⟩
  · intro i
    norm_num
  · intro i
    simp
  · intro i j hij
    simp [SimpleGraph.adjMatrix, hij]

private theorem unstable_eigenvector :
    unstableVector ≠ 0 ∧
    (asyncMatrix baseMatrix ((⊤ : SimpleGraph (Fin 2)).adjMatrix ℕ) 1).map
        (algebraMap ℝ ℂ) *ᵥ unstableVector =
      (5 / 4 : ℂ) • unstableVector := by
  constructor
  · intro hzero
    have hh := congrFun hzero (0, ⟨0, 0⟩)
    change (10 : ℂ) = 0 at hh
    norm_num at hh
  · funext rp
    delta asyncMatrix baseMatrix unstableVector Matrix.map
    unfold Matrix.mulVec dotProduct
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    rcases rp with ⟨r, i, a⟩
    fin_cases r <;> fin_cases i <;> fin_cases a <;>
      norm_num [Fintype.sum_sigma, Fin.sum_univ_two, Fintype.sum_unique,
        Matrix.map_apply, smul_eq_mul, SimpleGraph.adjMatrix]

private theorem asynchronous_radius :
    ENNReal.ofReal (5 / 4) ≤
      radius (asyncMatrix baseMatrix ((⊤ : SimpleGraph (Fin 2)).adjMatrix ℕ) 1) := by
  obtain ⟨hv, he⟩ := unstable_eigenvector
  have hmem :=
    D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree.eigenpair_mem_spectrum
      _ (5 / 4) unstableVector hv he
  unfold radius
  rw [spectralRadius_eq_of_unital]
  have hnorm : (‖(5 / 4 : ℂ)‖₊ : ℝ≥0∞) = ENNReal.ofReal (5 / 4) := by
    convert (ENNReal.ofReal_coe_nnreal (p := ‖(5 / 4 : ℂ)‖₊)).symm using 1
    norm_num [coe_nnnorm, norm_div]
  rw [← hnorm]
  exact le_iSup₂ (f := fun z (_ : z ∈ spectrum ℂ
    ((asyncMatrix baseMatrix ((⊤ : SimpleGraph (Fin 2)).adjMatrix ℕ) 1).map
      (algebraMap ℝ ℂ))) => (‖z‖₊ : ℝ≥0∞))
    (5 / 4 : ℂ) hmem

private theorem not_q1 : ¬ Q1 := by
  intro h
  have hbound := h 2 (fun _ => 1) 1 baseMatrix ((⊤ : SimpleGraph (Fin 2)).adjMatrix ℕ) (1 / 2)
    witness_admissible
  have hroot : (1 / 2 : ℝ) ^ ((1 : ℝ) / (1 + 1)) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)
  rw [Nat.cast_one] at hbound
  have hbad := asynchronous_radius.trans
    (hbound.trans (ENNReal.ofReal_le_ofReal hroot))
  norm_num at hbad

private theorem not_q2 : ¬ Q2 := by
  rintro ⟨f, hf, hbound⟩
  have hrange := hf (1 / 2) 1 (by norm_num) (by norm_num)
  have hbad : (5 / 4 : ℝ) ≤ f (1 / 2) 1 :=
    (ENNReal.ofReal_le_ofReal_iff hrange.1.le).mp
      (asynchronous_radius.trans
        (hbound 2 (fun _ => 1) 1 baseMatrix ((⊤ : SimpleGraph (Fin 2)).adjMatrix ℕ) (1 / 2)
          witness_admissible))
  linarith [hrange.2]

/-- A matrix of radius one half with unit remote delays refutes both proposed bounds. -/
theorem result : ¬ claim := by
  intro h
  exact h.elim not_q1 not_q2

end D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation
