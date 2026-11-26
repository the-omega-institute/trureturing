/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NoncommutingClockSublevel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Wigner-free spectral sublevel projection, trial-energy rank lower bounds, and noncommuting positive operator sum bounds. -/

import D5.S3.Quantum.Analysis.TraceClass.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace D5.S3.Quantum.Analysis.NullConeGravity.NoncommutingClockSublevel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The closed spectral sublevel of a bounded self-adjoint operator, obtained as the kernel of
its shifted positive part. -/
def sublevelProjection (T : H →L[ℂ] H) (ℓ : ℝ) : H →L[ℂ] H :=
  (posPart (T - ℓ • (1 : H →L[ℂ] H))).ker.starProjection

private theorem positive_energy_strict {A : H →L[ℂ] H} (hA : 0 ≤ A) (x : H)
    (hx : A x ≠ 0) : 0 < (⟪x, A x⟫_ℂ).re := by
  let R := CFC.sqrt A
  have hR : IsSelfAdjoint R := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA
  have hrx : R x ≠ 0 := by
    intro hz
    apply hx
    rw [← hRR, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hz, map_zero]
  have hinner : ⟪x, A x⟫_ℂ = ⟪R x, R x⟫_ℂ := by
    rw [← hRR, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_left R (R x) x]
    rw [← ContinuousLinearMap.star_eq_adjoint, hR.star_eq]
  rw [hinner, inner_self_eq_norm_sq_to_K]
  norm_cast
  exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hrx)

/-- On the orthogonal complement of the sublevel, the energy is strictly above the threshold.
The projection reduces the operator, so the corresponding lower bound holds for all vectors,
and is strict whenever the complementary component is nonzero. -/
theorem sublevelProjection_energy_lower_bound (T : H →L[ℂ] H) (hT : 0 ≤ T)
    (ℓ : ℝ) (_hℓ : 0 < ℓ) :
    let K := (posPart (T - ℓ • (1 : H →L[ℂ] H))).ker
    let P := sublevelProjection T ℓ
    (∀ x ∈ K, T x ∈ K) ∧ (∀ x ∈ Kᗮ, T x ∈ Kᗮ) ∧
    (∀ x : H, ℓ * ‖(1 - P) x‖ ^ 2 ≤ (⟪x, T x⟫_ℂ).re) ∧
    (∀ x ∈ Kᗮ, x ≠ 0 → ℓ * ‖x‖ ^ 2 < (⟪x, T x⟫_ℂ).re) ∧
    (∀ x : H, (1 - P) x ≠ 0 → ℓ * ‖(1 - P) x‖ ^ 2 < (⟪x, T x⟫_ℂ).re) := by
  dsimp only
  let U : H →L[ℂ] H := T - ℓ • (1 : H →L[ℂ] H)
  let A := posPart U
  let B := negPart U
  let K := A.ker
  let P := K.starProjection
  let Q := Kᗮ.starProjection
  have hU : IsSelfAdjoint U := by
    change IsSelfAdjoint (T - ℓ • (1 : H →L[ℂ] H))
    exact (IsSelfAdjoint.of_nonneg hT).sub (by simp [IsSelfAdjoint, star_smul])
  have hA : 0 ≤ A := CFC.posPart_nonneg U
  have hB : 0 ≤ B := CFC.negPart_nonneg U
  have hAB : A * B = 0 := CFC.posPart_mul_negPart U
  have hBA : B * A = 0 := CFC.negPart_mul_posPart U
  have hdecomp : T = A - B + ℓ • (1 : H →L[ℂ] H) := by
    rw [CFC.posPart_sub_negPart U hU]
    simp [U]
  have hTpos := ContinuousLinearMap.nonneg_iff_isPositive.mp hT
  have hBpos := ContinuousLinearMap.nonneg_iff_isPositive.mp hB
  have hBmem : ∀ x : H, B x ∈ K := by
    intro x
    change A (B x) = 0
    have h := congrArg (fun f : H →L[ℂ] H => f x) hAB
    simpa [ContinuousLinearMap.mul_def] using h
  have hBzero : ∀ x ∈ Kᗮ, B x = 0 := by
    intro x hx
    have h := (K.mem_orthogonal x).mp hx (B (B x)) (hBmem (B x))
    rw [hBpos.inner_left_eq_inner_right] at h
    exact inner_self_eq_zero.mp h
  have hKinv : ∀ x ∈ K, T x ∈ K := by
    intro x hx
    change A x = 0 at hx
    change A (T x) = 0
    rw [hdecomp]
    simp [hx, show A (B x) = 0 from hBmem x]
  have hKperp : ∀ x ∈ Kᗮ, T x ∈ Kᗮ := by
    intro x hx
    apply (K.mem_orthogonal (T x)).mpr
    intro y hy
    rw [← hTpos.inner_left_eq_inner_right]
    exact (K.mem_orthogonal x).mp hx (T y) (hKinv y hy)
  have hstrict : ∀ x ∈ Kᗮ, x ≠ 0 → ℓ * ‖x‖ ^ 2 < (⟪x, T x⟫_ℂ).re := by
    intro x hx hn
    have hAx : A x ≠ 0 := by
      intro hzero
      have hmem : x ∈ K := hzero
      exact hn (inner_self_eq_zero.mp ((K.mem_orthogonal x).mp hx x hmem))
    have henergy := positive_energy_strict hA x hAx
    have heq : (⟪x, T x⟫_ℂ).re = (⟪x, A x⟫_ℂ).re + ℓ * ‖x‖ ^ 2 := by
      rw [hdecomp]
      simp [hBzero x hx, inner_add_right]
      change (⟪x, (ℓ : ℂ) • x⟫_ℂ).re = ℓ * ‖x‖ ^ 2
      rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
      simp [pow_two, Complex.mul_re]
    linarith
  have hQ : Q = 1 - P := K.starProjection_orthogonal'
  have hsplit : ∀ x : H, (⟪x, T x⟫_ℂ).re =
      (⟪P x, T (P x)⟫_ℂ).re + (⟪Q x, T (Q x)⟫_ℂ).re := by
    intro x
    have hp : P x ∈ K := K.starProjection_apply_mem x
    have hq : Q x ∈ Kᗮ := Kᗮ.starProjection_apply_mem x
    have h₁ : ⟪P x, T (Q x)⟫_ℂ = 0 := (K.mem_orthogonal _).mp (hKperp _ hq) _ hp
    have h₂ : ⟪Q x, T (P x)⟫_ℂ = 0 := by
      rw [← inner_conj_symm]
      simp [(K.mem_orthogonal _).mp hq _ (hKinv _ hp)]
    have hadd : P x + Q x = x := K.starProjection_add_starProjection_orthogonal x
    conv_lhs => rw [← hadd]
    simp [map_add, inner_add_left, inner_add_right, h₁, h₂, Complex.add_re]
  have hweak : ∀ x : H, ℓ * ‖Q x‖ ^ 2 ≤ (⟪x, T x⟫_ℂ).re := by
    intro x
    rw [hsplit]
    have hnn : 0 ≤ (⟪P x, T (P x)⟫_ℂ).re := hTpos.re_inner_nonneg_right (P x)
    by_cases hx : Q x = 0
    · simp [hx, hnn]
    · have h := hstrict (Q x) (Kᗮ.starProjection_apply_mem x) hx
      linarith
  have hstrict' : ∀ x : H, Q x ≠ 0 → ℓ * ‖Q x‖ ^ 2 < (⟪x, T x⟫_ℂ).re := by
    intro x hx
    rw [hsplit]
    have hnn : 0 ≤ (⟪P x, T (P x)⟫_ℂ).re := hTpos.re_inner_nonneg_right (P x)
    have h := hstrict (Q x) (Kᗮ.starProjection_apply_mem x) hx
    linarith
  change (∀ x ∈ K, T x ∈ K) ∧ (∀ x ∈ Kᗮ, T x ∈ Kᗮ) ∧
    (∀ x : H, ℓ * ‖(1 - P) x‖ ^ 2 ≤ (⟪x, T x⟫_ℂ).re) ∧
    (∀ x ∈ Kᗮ, x ≠ 0 → ℓ * ‖x‖ ^ 2 < (⟪x, T x⟫_ℂ).re) ∧
    (∀ x : H, (1 - P) x ≠ 0 → ℓ * ‖(1 - P) x‖ ^ 2 < (⟪x, T x⟫_ℂ).re)
  rw [← hQ]
  exact ⟨hKinv, hKperp, hweak, hstrict, hstrict'⟩

omit [CompleteSpace H] in
private theorem projection_mass_le_rank (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    [FiniteDimensional ℂ K] {k : ℕ} (u : Fin k → H) (hu : Orthonormal ℂ u) :
    (∑ j, ‖K.starProjection (u j)‖ ^ 2) ≤ (Module.finrank ℂ K : ℝ) := by
  let b := stdOrthonormalBasis ℂ K
  have hparseval : ∀ x : H, ‖K.starProjection x‖ ^ 2 =
      ∑ i, ‖⟪(b i : H), x⟫_ℂ‖ ^ 2 := by
    intro x
    rw [K.starProjection_apply]
    change ‖K.orthogonalProjectionOnto x‖ ^ 2 = _
    rw [← b.sum_sq_norm_inner_right]
    simp only [K.inner_orthogonalProjectionOnto_eq_of_mem_left]
  simp_rw [hparseval]
  rw [Finset.sum_comm]
  calc
    (∑ i, ∑ j, ‖⟪(b i : H), u j⟫_ℂ‖ ^ 2) ≤ ∑ _i : Fin (Module.finrank ℂ K), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := hu.sum_inner_products_le (s := Finset.univ) (b i : H)
      have hnorm : ‖(b i : H)‖ = 1 := b.orthonormal.1 i
      simp only [hnorm, one_pow] at h
      simpa only [← inner_conj_symm (b i : H), RCLike.norm_conj] using h
    _ = _ := by simp

/-- Trial energy controls the total sublevel projection mass and gives a strict lower bound on
energy when the sublevel rank is deficient. -/
theorem sublevel_rank_of_trial_energy {k : ℕ}
    (T : H →L[ℂ] H) (hT : 0 ≤ T) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (u : Fin k → H) (hu : Orthonormal ℂ u) :
    let P := sublevelProjection T ℓ
    let S := ∑ j, (inner ℂ (u j) (T (u j))).re
    (k : ℝ) - S / ℓ ≤ ∑ j, ‖P (u j)‖ ^ 2 ∧
    ∀ [FiniteDimensional ℂ P.range], Module.finrank ℂ P.range < k →
      ℓ * ((k : ℝ) - (Module.finrank ℂ P.range : ℝ)) < S := by
  classical
  let K := (posPart (T - ℓ • (1 : H →L[ℂ] H))).ker
  let P := sublevelProjection T ℓ
  let Q : H →L[ℂ] H := 1 - P
  let S := ∑ j, (inner ℂ (u j) (T (u j))).re
  have hP : P = K.starProjection := rfl
  have hQ : Q = Kᗮ.starProjection := (K.starProjection_orthogonal').symm
  obtain ⟨_, _, hweak, _, hstrict⟩ := sublevelProjection_energy_lower_bound T hT ℓ hℓ
  have hpyth : ∀ j, ‖P (u j)‖ ^ 2 + ‖Q (u j)‖ ^ 2 = 1 := by
    intro j
    have h := K.norm_sq_eq_add_norm_sq_starProjection (u j)
    rw [← hP, ← hQ, hu.1 j, one_pow] at h
    exact h.symm
  have hnormsum : (∑ j, ‖P (u j)‖ ^ 2) + (∑ j, ‖Q (u j)‖ ^ 2) = (k : ℝ) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hpyth]
    simp
  have hsum : ℓ * (∑ j, ‖Q (u j)‖ ^ 2) ≤ S := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hweak (u j)
  change (k : ℝ) - S / ℓ ≤ ∑ j, ‖P (u j)‖ ^ 2 ∧
    ∀ [FiniteDimensional ℂ P.range], Module.finrank ℂ P.range < k →
      ℓ * ((k : ℝ) - (Module.finrank ℂ P.range : ℝ)) < S
  constructor
  · have hdiv := (le_div_iff₀ hℓ).mpr (by simpa [mul_comm] using hsum)
    linarith
  · intro hfd hr
    have hrange : P.range = K := by rw [hP, Submodule.range_starProjection]
    have : FiniteDimensional ℂ K := hrange ▸ hfd
    have hmass := projection_mass_le_rank K u hu
    rw [← hP, ← hrange] at hmass
    have hrcast : (Module.finrank ℂ P.range : ℝ) < k := by exact_mod_cast hr
    obtain ⟨j, hj⟩ : ∃ j : Fin k, Q (u j) ≠ 0 := by
      by_contra! hzero
      have hqsum : ∑ j, ‖Q (u j)‖ ^ 2 = 0 := by simp [hzero]
      linarith
    have hsumstrict : ℓ * (∑ j, ‖Q (u j)‖ ^ 2) < S := by
      rw [Finset.mul_sum]
      exact Finset.sum_lt_sum (fun i _ => hweak (u i)) ⟨j, Finset.mem_univ _, hstrict (u j) hj⟩
    nlinarith [mul_le_mul_of_nonneg_left hmass hℓ.le]

/-- A trial family with average energy at most the threshold forces a nonzero sublevel.
A uniform Rayleigh bound on a trial subspace makes projection into the sublevel injective. -/
theorem sublevel_nonempty_and_rayleigh_rank {k : ℕ}
    (T : H →L[ℂ] H) (hT : 0 ≤ T) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    let P := sublevelProjection T ℓ
    (∀ (u : Fin k → H), Orthonormal ℂ u → 0 < k →
      (∑ j, (⟪u j, T (u j)⟫_ℂ).re) ≤ (k : ℝ) * ℓ → P.range ≠ ⊥) ∧
    (∀ W : Submodule ℂ H, (∀ v ∈ W, (⟪v, T v⟫_ℂ).re ≤ ℓ * ‖v‖ ^ 2) →
      Set.InjOn P W ∧ ∀ [FiniteDimensional ℂ P.range],
        FiniteDimensional ℂ W ∧ Module.finrank ℂ W ≤ Module.finrank ℂ P.range) := by
  classical
  let P := sublevelProjection T ℓ
  let K := (posPart (T - ℓ • (1 : H →L[ℂ] H))).ker
  have hP : P = K.starProjection := rfl
  change (∀ u : Fin k → H, Orthonormal ℂ u → 0 < k →
      (∑ j, (⟪u j, T (u j)⟫_ℂ).re) ≤ (k : ℝ) * ℓ → P.range ≠ ⊥) ∧
    (∀ W : Submodule ℂ H, (∀ v ∈ W, (⟪v, T v⟫_ℂ).re ≤ ℓ * ‖v‖ ^ 2) →
      Set.InjOn P W ∧ ∀ [FiniteDimensional ℂ P.range],
        FiniteDimensional ℂ W ∧ Module.finrank ℂ W ≤ Module.finrank ℂ P.range)
  constructor
  · intro u hu hk hS hbot
    have : FiniteDimensional ℂ P.range := hbot.symm ▸ inferInstanceAs (FiniteDimensional ℂ (⊥ : Submodule ℂ H))
    have hr : Module.finrank ℂ P.range = 0 := by rw [hbot, finrank_bot]
    have hlt : Module.finrank ℂ (sublevelProjection T ℓ).range < k := by
      change Module.finrank ℂ P.range < k
      omega
    have h := (sublevel_rank_of_trial_energy T hT hℓ u hu).2 hlt
    rw [hr] at h
    push_cast at h
    linarith
  · intro W hW
    have hstrict := (sublevelProjection_energy_lower_bound T hT ℓ hℓ).2.2.2.1
    have hinj : Set.InjOn P W := by
      intro x hx y hy heq
      have hzero : P (x - y) = 0 := by rw [map_sub, heq, sub_self]
      have hperp : x - y ∈ Kᗮ := by
        rw [← Submodule.ker_starProjection, ← hP]
        exact hzero
      by_contra hxy
      exact (not_lt_of_ge (hW (x - y) (W.sub_mem hx hy)))
        (hstrict (x - y) hperp (sub_ne_zero.mpr hxy))
    refine ⟨hinj, ?_⟩
    intro hfd
    let L : W →ₗ[ℂ] P.range := (P.toLinearMap.comp W.subtype).codRestrict P.range
      (fun x => ⟨x, rfl⟩)
    have hLin : Function.Injective L := by
      intro x y hxy
      apply Subtype.ext
      apply hinj x.property y.property
      exact congrArg (fun z : P.range => (z : H)) hxy
    exact ⟨FiniteDimensional.of_injective L hLin, LinearMap.finrank_le_finrank_of_injective hLin⟩

/-- Positive operator sums of the form A† E A admit the same trial-vector bounds, with each
quadratic form equal to the energy of the corresponding transformed vector. -/
theorem noncommuting_sum_sublevel_rank_bound {ι : Type*} {k : ℕ}
    (s : Finset ι) (A E : ι → H →L[ℂ] H) (hE : ∀ i ∈ s, 0 ≤ E i)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (u : Fin k → H) (hu : Orthonormal ℂ u) :
    let T := ∑ i ∈ s, (A i).adjoint ∘L E i ∘L A i
    let P := sublevelProjection T ℓ
    let S := ∑ j, ∑ i ∈ s, (⟪A i (u j), E i (A i (u j))⟫_ℂ).re
    (k : ℝ) - S / ℓ ≤ ∑ j, ‖P (u j)‖ ^ 2 ∧
    ∀ [FiniteDimensional ℂ P.range], Module.finrank ℂ P.range < k →
      ℓ * ((k : ℝ) - (Module.finrank ℂ P.range : ℝ)) < S := by
  dsimp only
  let T := ∑ i ∈ s, (A i).adjoint ∘L E i ∘L A i
  have hT : 0 ≤ T := Finset.sum_nonneg fun i hi =>
    ContinuousLinearMap.nonneg_iff_isPositive.mpr
      ((ContinuousLinearMap.nonneg_iff_isPositive.mp (hE i hi)).adjoint_conj (A i))
  have henergy : ∀ x : H, (⟪x, T x⟫_ℂ).re =
      ∑ i ∈ s, (⟪A i x, E i (A i x)⟫_ℂ).re := by
    intro x
    dsimp [T]
    simp [inner_sum, Complex.re_sum,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  have h := sublevel_rank_of_trial_energy T hT hℓ u hu
  dsimp only at h
  simp_rw [henergy] at h
  exact h

#print axioms sublevelProjection_energy_lower_bound
#print axioms sublevel_rank_of_trial_energy
#print axioms sublevel_nonempty_and_rayleigh_rank
#print axioms noncommuting_sum_sublevel_rank_bound

end D5.S3.Quantum.Analysis.NullConeGravity.NoncommutingClockSublevel
