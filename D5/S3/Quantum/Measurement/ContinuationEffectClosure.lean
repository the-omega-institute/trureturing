/- GID: D5/S3/Quantum/Measurement/ContinuationEffectClosure
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ContinuationEffectClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The continuation effect spaces of finitely many Kraus branches close within d squared minus r steps to the least invariant space. -/

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
  -- an injective real coordinate map on Hermitian matrices bounds the dimension by `d²`
  let φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] (Fin d × Fin d → ℝ) :=
    { toFun := fun X p => if p.1 ≤ p.2 then (X p.1 p.2).re else (X p.2 p.1).im
      map_add' := fun X Y => by
        funext p
        split_ifs <;> simp [*]
      map_smul' := fun r X => by
        funext p
        split_ifs <;> simp [*] }
  have hφ : ∀ X ∈ Hm, φ X = 0 → X = 0 := by
    intro X hXh h0
    have hsym : ∀ i j, X j i = star (X i j) := fun i j => by
      rw [← congrFun (congrFun (show Xᴴ = X from hXh) j) i, conjTranspose_apply]
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hre : (X i j).re = 0 := by
        have := congrFun h0 (i, j); simpa [φ, hij.le] using this
      have him : (X i j).im = 0 := by
        have := congrFun h0 (j, i); simpa [φ, not_le.mpr hij] using this
      exact Complex.ext hre him
    · have hre : (X i i).re = 0 := by
        have := congrFun h0 (i, i); simpa [φ] using this
      have him : (X i i).im = 0 := by
        have h := congrArg Complex.im (hsym i i)
        simp only [Complex.star_def, Complex.conj_im] at h
        linarith
      exact Complex.ext hre him
    · have hre : (X j i).re = 0 := by
        have := congrFun h0 (j, i); simpa [φ, hij.le] using this
      have him : (X j i).im = 0 := by
        have := congrFun h0 (i, j); simpa [φ, not_le.mpr hij] using this
      rw [hsym j i, show X j i = 0 from Complex.ext hre him, star_zero]
      rfl
  have hdim : ∀ n, Module.finrank ℝ (Z n) ≤ d ^ 2 := by
    intro n
    have hinj : Function.Injective (φ.comp (Z n).subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro X hX
      exact Subtype.ext (hφ X (hherm n X.2) hX)
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, sq] using this
  -- stabilization at `d² - r`
  set r := Module.finrank ℝ Z₀ with hr
  have hr_le : r ≤ d ^ 2 := hdim 0
  set N := d ^ 2 - r with hN
  have hstable : Z (N + 1) = Z N := by
    by_contra hne
    have hstrict : ∀ k, k ≤ N → Z (k + 1) ≠ Z k := by
      intro k hk hk'
      apply hne
      have h1 := hprop k hk' (N + 1 - k)
      have h2 := hprop k hk' (N - k)
      rw [show k + (N + 1 - k) = N + 1 by omega] at h1
      rw [show k + (N - k) = N by omega] at h2
      rw [h1, h2]
    have hgrow : ∀ k, k ≤ N + 1 → r + k ≤ Module.finrank ℝ (Z k) := by
      intro k hk
      induction k with
      | zero => exact le_of_eq (by rw [add_zero, hr]; rfl)
      | succ k ih =>
          have hlt : Z k < Z (k + 1) := lt_of_le_of_ne (hstep k) (hstrict k (by omega)).symm
          have := Submodule.finrank_lt_finrank_of_lt hlt
          have := ih (by omega)
          omega
    have := hgrow (N + 1) le_rfl
    have := hdim (N + 1)
    omega
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
