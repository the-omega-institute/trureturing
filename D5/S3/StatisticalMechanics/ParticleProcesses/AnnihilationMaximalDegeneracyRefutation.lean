/- GID: D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.claim; result=D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.result; claim=D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.claim
   digest: Ayyer–Mallick maximal degeneracy fails at length five and positive rates. -/

/-
proof_shape: result: bind-only
proof_shape: qkernel1: bind-only; consumer: realKernel1
proof_shape: qkernel2: bind-only; consumer: realKernel2
proof_shape: qGenMat_cast: bind-only; consumer: shifted_cast
proof_shape: shifted_cast: bind-only; consumers: realKernel1, realKernel2
proof_shape: realKernel1: bind-only; consumer: left_nullity
proof_shape: realKernel2: bind-only; consumer: left_nullity
proof_shape: vectors_independent: bind-only; consumer: left_nullity
proof_shape: left_nullity: bind-only; consumer: right_nullity
proof_shape: right_nullity: bind-only; consumer: result
escape_witness: none
admission_basis: open-problem-resolution (#16707; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
States use Fin L → Bool directly; true denotes a particle and index 0 is site 1.
The claim is the geometric-multiplicity clause after Eq. (79) of
Ayyer–Mallick, arXiv:0910.0693v2, p. 14. It quantifies over real eigenvalues;
the real eigenvalue -2 already refutes the source's unrestricted assertion.
The private rational generator permits exact kernel evaluation; its cast is
proved equal to the real generator. The two integer polynomials use prefix
products written locally, with no new name for an existing Walsh function.
-/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false

namespace D5.S3.StatisticalMechanics.ParticleProcesses.AnnihilationMaximalDegeneracyRefutation
open scoped BigOperators Matrix

def bulkMove {L : ℕ} (s : Fin L → Bool) (i j : Fin L) : Fin L → Bool :=
  Function.update (Function.update s i false) j (!s j)

def bulkCount (L : ℕ) (s t : Fin L → Bool) : ℕ :=
  ∑ i : Fin L, if h : i.val + 1 < L then
    if s i = true ∧ t = bulkMove s i ⟨i.val + 1, h⟩ then 1 else 0
    else 0

def leftCount (L : ℕ) (s t : Fin L → Bool) : ℕ :=
  if h : 0 < L then
    if t = Function.update s ⟨0, h⟩ (!s ⟨0, h⟩) then 1 else 0
    else 0

def rightCount (L : ℕ) (s t : Fin L → Bool) : ℕ :=
  if h : 0 < L then
    if s ⟨L - 1, by omega⟩ = true ∧
      t = Function.update s ⟨L - 1, by omega⟩ false then 1 else 0
    else 0

def offRate (L : ℕ) (α β : ℝ) (s t : Fin L → Bool) : ℝ :=
  (bulkCount L s t : ℝ) + α * leftCount L s t + β * rightCount L s t

def genMat (L : ℕ) (α β : ℝ) : Matrix (Fin L → Bool) (Fin L → Bool) ℝ :=
  fun t s => if t = s then -(∑ u : (Fin L → Bool), if u ≠ s then offRate L α β s u else 0)
    else offRate L α β s t

def claim : Prop := ∀ L : ℕ, 1 ≤ L → ∀ α β : ℝ, 0 < α → 0 < β →
  ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (genMat L α β - μ • 1))) ≤ 1


private def qGenMat (L : ℕ) (α β : ℚ) : Matrix (Fin L → Bool) (Fin L → Bool) ℚ :=
  fun t s => if t = s then
    -(∑ u : Fin L → Bool, if u ≠ s then
      (bulkCount L s u : ℚ) + α * leftCount L s u + β * rightCount L s u else 0)
    else (bulkCount L s t : ℚ) + α * leftCount L s t + β * rightCount L s t

private def v1 (s : Fin 5 → Bool) : ℤ :=
  let p := fun n : ℕ => ∏ i : Fin 5, if i.val < n then (if s i then (-1 : ℤ) else 1) else 1
  p 1 * p 2 - 3 * p 2 + 9 * p 1 - 5

private def v2 (s : Fin 5 → Bool) : ℤ :=
  let p := fun n : ℕ => ∏ i : Fin 5, if i.val < n then (if s i then (-1 : ℤ) else 1) else 1
  p 1 * p 4 - p 2 * p 3 - 3 * p 4 +
  9 * p 3 - 27 * p 2 + 81 * p 1 - 40

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact reduction sums the rational generator over all 32 Boolean configurations.
private theorem qkernel1 :
  (qGenMat 5 (1/3) (2/5) - (-2 : ℚ) • 1)ᵀ *ᵥ (fun s => (v1 s : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact reduction sums the rational generator over all 32 Boolean configurations.
private theorem qkernel2 :
  (qGenMat 5 (1/3) (2/5) - (-2 : ℚ) • 1)ᵀ *ᵥ (fun s => (v2 s : ℚ)) = 0 := by
  decide +kernel


private theorem qGenMat_cast (L : ℕ) (α β : ℚ) :
    (qGenMat L α β).map (Rat.castHom ℝ) = genMat L (α : ℝ) (β : ℝ) := by
  ext t s
  by_cases h : t = s <;>
    simp [Matrix.map_apply, qGenMat, genMat, offRate, h, apply_ite]

private theorem shifted_cast :
    ((qGenMat 5 (1/3) (2/5) - (-2 : ℚ) • 1)ᵀ).map (Rat.castHom ℝ) =
    (genMat 5 (1/3) (2/5) - (-2 : ℝ) • 1)ᵀ := by
  ext t s
  have h := congrFun (congrFun (qGenMat_cast 5 (1/3) (2/5)) s) t
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, map_sub, map_mul] at *
  norm_num at h ⊢
  rw [h]
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num

private theorem realKernel1 :
    (genMat 5 (1/3) (2/5) - (-2 : ℝ) • 1)ᵀ *ᵥ (fun s => (v1 s : ℝ)) = 0 := by
  funext s
  have h := congrArg (Rat.castHom ℝ) (congrFun qkernel1 s)
  have hv : (Rat.castHom ℝ) ∘ (fun s => (v1 s : ℚ)) = (fun s => (v1 s : ℝ)) := by
    funext t
    simp
  rw [RingHom.map_mulVec, shifted_cast, hv] at h
  simpa only [Pi.zero_apply, map_zero] using h

private theorem realKernel2 :
    (genMat 5 (1/3) (2/5) - (-2 : ℝ) • 1)ᵀ *ᵥ (fun s => (v2 s : ℝ)) = 0 := by
  funext s
  have h := congrArg (Rat.castHom ℝ) (congrFun qkernel2 s)
  have hv : (Rat.castHom ℝ) ∘ (fun s => (v2 s : ℚ)) = (fun s => (v2 s : ℝ)) := by
    funext t
    simp
  rw [RingHom.map_mulVec, shifted_cast, hv] at h
  simpa only [Pi.zero_apply, map_zero] using h

private theorem vectors_independent :
    LinearIndependent ℝ ![(fun s => (v1 s : ℝ)), (fun s => (v2 s : ℝ))] := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have h0 := congrFun h (fun _ => false)
    norm_num [v2, Fin.prod_univ_succ] at h0
  · intro a h
    have h0 := congrFun h (fun _ => false)
    have h1 := congrFun h (fun i : Fin 5 => decide (i.val = 3))
    norm_num [v1, v2, Fin.prod_univ_succ] at h0 h1
    linarith

private theorem left_nullity :
    2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (genMat 5 (1/3) (2/5) - (-2 : ℝ) • 1)ᵀ)) := by
  let K := LinearMap.ker (Matrix.toLin' (genMat 5 (1/3) (2/5) - (-2 : ℝ) • 1)ᵀ)
  have h1 : (fun s => (v1 s : ℝ)) ∈ K := by
    change Matrix.toLin' _ (fun s => (v1 s : ℝ)) = 0
    simpa only [Matrix.toLin'_apply] using realKernel1
  have h2 : (fun s => (v2 s : ℝ)) ∈ K := by
    change Matrix.toLin' _ (fun s => (v2 s : ℝ)) = 0
    simpa only [Matrix.toLin'_apply] using realKernel2
  let w : Fin 2 → K := ![⟨(fun s => (v1 s : ℝ)), h1⟩, ⟨(fun s => (v2 s : ℝ)), h2⟩]
  have hw : LinearIndependent ℝ w := by
    apply LinearIndependent.of_comp K.subtype
    have heq : K.subtype ∘ w = ![(fun s => (v1 s : ℝ)), (fun s => (v2 s : ℝ))] := by
      funext i
      fin_cases i <;> rfl
    rw [heq]
    exact vectors_independent
  simpa using hw.fintype_card_le_finrank

private theorem right_nullity :
    2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (genMat 5 (1/3) (2/5) - (-2 : ℝ) • 1))) := by
  let A := genMat 5 (1/3) (2/5) - (-2 : ℝ) • 1
  have ht := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' Aᵀ)
  have hf := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  have hr : Module.finrank ℝ (LinearMap.range (Matrix.toLin' Aᵀ)) =
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) := Matrix.rank_transpose A
  have hl := left_nullity
  change 2 ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toLin' Aᵀ)) at hl
  change 2 ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A))
  rw [hr] at ht
  have hn := Nat.add_left_cancel (ht.trans hf.symm)
  rw [← hn]
  exact hl

theorem result : ¬ claim := by
  intro hc
  have h := hc 5 (by omega) (1/3) (2/5) (by norm_num) (by norm_num) (-2)
  have htwo := right_nullity
  omega

end D5.S3.StatisticalMechanics.ParticleProcesses.AnnihilationMaximalDegeneracyRefutation
