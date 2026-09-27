/- GID: D5/S3/Quantum/Measurement/ContinuationEffectClosure
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ContinuationEffectClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The continuation effect spaces of finitely many Kraus branches close within d squared minus r steps to the least invariant space. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.ContinuationEffectClosure

open Matrix

variable {d : ℕ} {J : Type} {κ : J → Type} [∀ j, Fintype (κ j)]

/-- The dual `Φ_j^*(H) = ∑_k K_{jk}ᴴ H K_{jk}` of the branch `j` with Kraus operators `K_{jk}`, as a
real-linear map. -/
def branchDual (K : (j : J) → κ j → Matrix (Fin d) (Fin d) ℂ) (j : J) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ where
  toFun H := ∑ k, (K j k)ᴴ * H * K j k
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' r X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply]

/-- The continuation effect spaces `𝒵_{k+1} = span_ℝ(𝒵_k ∪ ⋃_j Φ_j^*(𝒵_k))` starting from `𝒵₀`. -/
noncomputable def continuationSpace (K : (j : J) → κ j → Matrix (Fin d) (Fin d) ℂ)
    (Z₀ : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ)) : ℕ → Submodule ℝ (Matrix (Fin d) (Fin d) ℂ)
  | 0 => Z₀
  | n + 1 => continuationSpace K Z₀ n ⊔ ⨆ j, (continuationSpace K Z₀ n).map (branchDual K j)

/-- **Finite closure of continuation effect spaces.** Let `𝒵₀` be a real space of Hermitian
`d × d` matrices of dimension `r`, and let `Φ_j^*` be the duals of finitely-generated Kraus branches.
The spaces `𝒵_k` are constant from `k = d² - r` on; `𝒵_{d²-r}` contains `𝒵₀` and is invariant under
every `Φ_j^*`; and it is contained in every real space containing `𝒵₀` and invariant under every
`Φ_j^*`. -/
theorem continuationSpace_closure (K : (j : J) → κ j → Matrix (Fin d) (Fin d) ℂ)
    (Z₀ : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ)) (hZ₀ : ∀ H ∈ Z₀, Hᴴ = H) :
    (∀ n, d ^ 2 - Module.finrank ℝ Z₀ ≤ n →
        continuationSpace K Z₀ n = continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀)) ∧
      Z₀ ≤ continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀) ∧
      (∀ j, ∀ H ∈ continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀),
        branchDual K j H ∈ continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀)) ∧
      ∀ W : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ), Z₀ ≤ W →
        (∀ j, ∀ H ∈ W, branchDual K j H ∈ W) →
          continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀) ≤ W := by
  classical
  let Z := continuationSpace K Z₀
  have hZ : ∀ n, Z (n + 1) = Z n ⊔ ⨆ j, (Z n).map (branchDual K j) := fun n => rfl
  have hstep : ∀ n, Z n ≤ Z (n + 1) := fun n => by rw [hZ]; exact le_sup_left
  have hmono : Monotone Z := monotone_nat_of_le_succ hstep
  -- one equality makes the space invariant and persists
  have hinv : ∀ n, Z (n + 1) = Z n → ∀ j, ∀ H ∈ Z n, branchDual K j H ∈ Z n := by
    intro n hn j H hH
    rw [← hn, hZ]
    exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem j ⟨H, hH, rfl⟩)
  have hprop : ∀ k, Z (k + 1) = Z k → ∀ m, Z (k + m) = Z k := by
    intro k hk m
    induction m with
    | zero => rfl
    | succ m ih => rw [← add_assoc, hZ, ih, ← hZ, hk]
  -- every continuation space consists of Hermitian matrices
  let Hm : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ) :=
    { carrier := {H | Hᴴ = H}
      add_mem' := fun {X Y} hX hY => by
        simp only [Set.mem_setOf_eq] at *; rw [conjTranspose_add, hX, hY]
      zero_mem' := conjTranspose_zero
      smul_mem' := fun r X hX => by
        simp only [Set.mem_setOf_eq] at *
        rw [conjTranspose_smul, hX]
        congr 1 }
  have hherm : ∀ n, Z n ≤ Hm := by
    intro n
    induction n with
    | zero => exact fun H hH => hZ₀ H hH
    | succ n ih =>
        rw [hZ]
        refine sup_le ih (iSup_le fun j => ?_)
        rintro _ ⟨H, hH, rfl⟩
        have hHh : Hᴴ = H := ih hH
        change (∑ k, (K j k)ᴴ * H * K j k)ᴴ = ∑ k, (K j k)ᴴ * H * K j k
        simp only [conjTranspose_sum, conjTranspose_mul, conjTranspose_conjTranspose, hHh,
          Matrix.mul_assoc]
  -- every continuation space lies in the Hermitian matrices, of real dimension `d²`
  have hdim : ∀ n, Module.finrank ℝ (Z n) ≤ d ^ 2 := by
    intro n
    have hle : Z n ≤ D5.S3.Quantum.Measurement.BasisMeasurementProjection.HermitianSpace d := by
      intro X hX
      change X ∈ selfAdjoint (Matrix (Fin d) (Fin d) ℂ)
      rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
      exact hherm n hX
    calc Module.finrank ℝ (Z n)
        ≤ Module.finrank ℝ (D5.S3.Quantum.Measurement.BasisMeasurementProjection.HermitianSpace d) :=
          Submodule.finrank_mono hle
      _ = d ^ 2 := D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition.hermitian_space_finrank d
  -- stabilization at `d² - r`
  set r := Module.finrank ℝ Z₀ with hr
  have hr_le : r ≤ d ^ 2 := hdim 0
  set N := d ^ 2 - r with hN
  have hstable : Z (N + 1) = Z N := by
    -- the ranks are monotone and bounded by `d²`, so some step among the first `d² - r` is flat
    obtain ⟨m, hm, hmeq⟩ :=
      D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate.bounded_monotone_has_equal_step
        (fun n => Module.finrank ℝ (Z n)) (d ^ 2)
        (fun a b hab => Submodule.finrank_mono (hmono hab)) hdim
    have hm' : m ≤ N := hm
    have hflat : Z (m + 1) = Z m :=
      (Submodule.eq_of_le_of_finrank_eq (hstep m) hmeq).symm
    have h1 := hprop m hflat (N + 1 - m)
    have h2 := hprop m hflat (N - m)
    rw [show m + (N + 1 - m) = N + 1 by omega] at h1
    rw [show m + (N - m) = N by omega] at h2
    rw [h1, h2]
  refine ⟨fun n hn => ?_, hmono (Nat.zero_le N), hinv N hstable, fun W hW hWinv => ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact hprop N hstable m
  · have hle : ∀ n, Z n ≤ W := by
      intro n
      induction n with
      | zero => exact hW
      | succ n ih =>
          rw [hZ]
          refine sup_le ih (iSup_le fun j => ?_)
          rintro _ ⟨H, hH, rfl⟩
          exact hWinv j H (ih hH)
    exact hle N

#print axioms continuationSpace_closure

end D5.S3.Quantum.Measurement.ContinuationEffectClosure
