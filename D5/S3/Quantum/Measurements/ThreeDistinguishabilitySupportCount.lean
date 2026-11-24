/- GID: D5/S3/Quantum/Measurements/ThreeDistinguishabilitySupportCount
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/ThreeDistinguishabilitySupportCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.weighted_isometry_of_inRegion; instance=D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.one_zero_feasible
   digest: Four dimensions force two rank-one members of any three orthogonal density supports. -/

import Mathlib.Analysis.Matrix.PosDef
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.States.Mixed.MState
import D5.S3.Quantum.PureState.PureStateHandshake

/-! Orthogonal supports give a joint rank bound and two rank-one witnesses in dimension four. -/

set_option autoImplicit false

open scoped BigOperators ComplexOrder Matrix InnerProductSpace

noncomputable section

namespace D5.S3.Quantum.Measurements.ThreeDistinguishabilitySupportCount

open Matrix
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

private theorem eigenvectors_orthogonal_of_mul_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A * B = 0)
    (i j : n) (hi : hA.eigenvalues i ≠ 0) (hj : hB.eigenvalues j ≠ 0) :
    inner ℂ (hA.eigenvectorBasis i) (hB.eigenvectorBasis j) = 0 := by
  let x : n → ℂ := ⇑(hA.eigenvectorBasis i)
  let y : n → ℂ := ⇑(hB.eigenvectorBasis j)
  have hx : A *ᵥ x = hA.eigenvalues i • x := hA.mulVec_eigenvectorBasis i
  have hy : B *ᵥ y = hB.eigenvalues j • y := hB.mulVec_eigenvectorBasis j
  have hAy : A *ᵥ y = 0 := by
    have hz : hB.eigenvalues j • (A *ᵥ y) = 0 := by
      rw [← Matrix.mulVec_smul, ← hy, Matrix.mulVec_mulVec, hAB, Matrix.zero_mulVec]
    exact (smul_eq_zero.mp hz).resolve_left hj
  have hz : hA.eigenvalues i • (star x ⬝ᵥ y) = 0 := by
    calc
      _ = star (A *ᵥ x) ⬝ᵥ y := by rw [hx, star_smul, star_trivial (hA.eigenvalues i), smul_dotProduct]
      _ = star x ⬝ᵥ (A *ᵥ y) := by
        rw [Matrix.star_mulVec, hA.eq, ← Matrix.dotProduct_mulVec]
      _ = 0 := by rw [hAy, dotProduct_zero]
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  exact (smul_eq_zero.mp hz).resolve_left hi

/-- All nonzero-eigenvalue vectors of pairwise annihilating Hermitian matrices fit
in one orthonormal family. -/
theorem sum_rank_le_of_orthogonal_supports
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (ρ : m → Matrix n n ℂ) (hHerm : ∀ i, (ρ i).IsHermitian)
    (hOrth : ∀ i j, i ≠ j → ρ i * ρ j = 0) :
    ∑ i, (ρ i).rank ≤ Fintype.card n := by
  classical
  let S (i : m) := {a : n // (hHerm i).eigenvalues a ≠ 0}
  let v : (Σ i, S i) → EuclideanSpace ℂ n :=
    fun a => (hHerm a.1).eigenvectorBasis a.2.val
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, a⟩ ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      by_cases hab : a.val = b.val
      · have hab' : a = b := Subtype.ext hab
        subst b
        simpa [v] using
          (orthonormal_iff_ite.mp (hHerm i).eigenvectorBasis.orthonormal a.val a.val)
      · have hne : (⟨i, a⟩ : Σ i, S i) ≠ ⟨i, b⟩ := by
          intro he
          exact hab (congrArg (fun t : Σ i, S i => t.2.val) he)
        simpa [v, hab, hne] using
          (orthonormal_iff_ite.mp (hHerm i).eigenvectorBasis.orthonormal a.val b.val)
    · have hne : (⟨i, a⟩ : Σ i, S i) ≠ ⟨j, b⟩ :=
        fun he => hij (congrArg Sigma.fst he)
      simpa [v, hne] using eigenvectors_orthogonal_of_mul_eq_zero
        (hHerm i) (hHerm j) (hOrth i j hij) a.val b.val a.property b.property
  calc
    ∑ i, (ρ i).rank = ∑ i, Fintype.card (S i) :=
      Finset.sum_congr rfl fun i _ => (hHerm i).rank_eq_card_non_zero_eigs
    _ = Fintype.card (Σ i, S i) := Fintype.card_sigma.symm
    _ ≤ _ := by simpa only [finrank_euclideanSpace] using hv.linearIndependent.fintype_card_le_finrank

private theorem rank_pos_of_trace_one {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (ht : A.trace = 1) : 0 < A.rank := by
  classical
  have hA0 : A ≠ 0 := by
    intro h
    simpa [h] using ht
  have hEigen : hA.eigenvalues ≠ 0 := fun h => hA0 (hA.eigenvalues_eq_zero_iff.mp h)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hEigen
  rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_pos_iff]
  exact ⟨⟨i, hi⟩⟩

/-- Relabel the three states so that the first two have rank one. -/
theorem exists_perm_rank_one_pair
    (ρ : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ)
    (hρ : ∀ j, (ρ j).PosSemidef ∧ (ρ j).trace = 1)
    (hOrth : ∀ i j, i ≠ j → ρ i * ρ j = 0) :
    ∃ σ : Equiv.Perm (Fin 3), (ρ (σ 0)).rank = 1 ∧ (ρ (σ 1)).rank = 1 := by
  have hpos (j : Fin 3) : 0 < (ρ j).rank := rank_pos_of_trace_one (hρ j).1.isHermitian (hρ j).2
  have hsum := sum_rank_le_of_orthogonal_supports ρ (fun j => (hρ j).1.isHermitian) hOrth
  simp only [Fin.sum_univ_three, Fintype.card_fin] at hsum
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  by_cases hzero : (ρ 0).rank = 1
  · by_cases hone : (ρ 1).rank = 1
    · exact ⟨Equiv.refl _, hzero, hone⟩
    · have htwo : (ρ 2).rank = 1 := by omega
      exact ⟨Equiv.swap 1 2, by simpa [Equiv.swap_apply_def] using hzero,
        by simpa [Equiv.swap_apply_def] using htwo⟩
  · have hone : (ρ 1).rank = 1 := by omega
    have htwo : (ρ 2).rank = 1 := by omega
    exact ⟨Equiv.swap 0 2, by simpa [Equiv.swap_apply_def] using htwo,
      by simpa [Equiv.swap_apply_def] using hone⟩

/-- Use the Physlib rank-one characterization with the repository's outer product. -/
theorem exists_rankOneDensity_of_rank_one
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (ht : A.trace = 1) (hr : A.rank = 1) :
    ∃ x : n → ℂ, A = rankOneDensity x := by
  let H : HermitianMat n ℂ := ⟨A, hA.isHermitian⟩
  have hH : H.trace = 1 := by
    rw [HermitianMat.trace_eq_re_trace]
    change A.trace.re = 1
    rw [ht, Complex.one_re]
  let state : MState n := ⟨H, HermitianMat.zero_le_iff.mpr hA, hH⟩
  have hRank : state.m.rank = 1 := hr
  obtain ⟨ψ, hψ⟩ := (MState.pure_iff_rank_eq_one state).mpr hRank
  refine ⟨⇑ψ, ?_⟩
  have he := congrArg MState.m hψ
  change A = (MState.pure ψ).m at he
  rw [he]
  ext i j
  change ψ i * ((ψ : Bra n) : n → ℂ) j = ψ i * star (ψ j)
  simp [Bra.eq_conj, Complex.star_def]

end D5.S3.Quantum.Measurements.ThreeDistinguishabilitySupportCount
