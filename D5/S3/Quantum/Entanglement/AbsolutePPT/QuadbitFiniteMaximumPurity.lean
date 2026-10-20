/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity
   mirror-E: none(waiver:structural-density-transfer)
   anchors: []
   utility: none
   digest: The actual four-by-n APPT maximum purity is (4n+8)/(4n+2)^2 for 7<=n<=13. -/

/-
The rank-one formula and attaining spectrum are due to
Ahiable–Kothakonda–Winter, arXiv:2608.03390v2.
One actual sorted spectrum supplies the literal K1, K2, L4 and purity.
The unrestricted length-52 endpoint is supplied internally, and the
rank-four dimension transfer fills the finite interval. This is a
necessary-constraint upper bound with actual physical attainment;
it asserts no PSD sufficiency, strict positivity, distinctness,
extension beyond n=13, classification of maximizers or priority.

proof_shape: endpoint52, finite_spectral_bound and attainer_data are
bind-only helpers consumed by physical_purity_upper_bound and
physical_finite7_maximum. Both public theorems are bind-only physical
compositions of the supplied length-52 concentration estimate,
rank-four dimension surgery and existing physical ray construction.
The maximum consumes the upper bound and the actual normalized
rank-one density to obtain a nonempty bounded purity set and its
attained real supremum. No separate escape witness or independent
new spectral estimate is claimed by this consumer module.
utility:none rationale: universal structural inference over arbitrary
complex density matrices, not a finite numerical certificate.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ContinuousSpectrumAssembly
import D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Entanglement.AbsolutePPT
open QutritPerturbationAttainment QutritSpectralReduction

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity
noncomputable section

/-- The maximum in the finite rank-one branch. -/
def purityValue (n : ℕ) : ℝ :=
  (((4 * n : ℕ) : ℝ) + 8) / (((4 * n : ℕ) : ℝ) + 2) ^ 2

/-- Purities of actual complex PSD trace-one APPT matrices on the product. -/
def physicalPurities (n : ℕ) : Set ℝ :=
  {p | ∃ rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ,
    (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧ (rho * rho).trace.re = p}

/-- The actual product basis vector index, with its nonempty dimension paid. -/
def basisZero (n : ℕ) (hn : 7 ≤ n) : Fin 4 × Fin n :=
  (0, ⟨0, by omega⟩)

/-- The actual normalized rank-one ray, rather than an abstract spectrum. -/
def attainingDensity (n : ℕ) (hn : 7 ≤ n) :
    Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ :=
  QuadbitQuintitMaximumPurity.normalizedRay (Pi.single (basisZero n hn) 1)

/- K2 is an unused extra hypothesis at the upper endpoint. The endpoint
is supplied here for every ordered length-52 tuple satisfying its hypotheses. -/
private theorem endpoint52 : SpectralBoundaryTransfer.RankFourSpectralBound 36 := by
  intro l ho hn ht h1 _h2 h4
  have hf : UniformRankFourNecessary.sumFirst 6 l =
      ∑ i : Fin 6, l ⟨i.val, by omega⟩ := by
    unfold UniformRankFourNecessary.sumFirst
    apply Finset.sum_congr rfl
    intro i _
    rw [dif_pos (show i.val < 36 + 16 by omega)]
  have hl : UniformRankFourNecessary.sumLast 10 l =
      ∑ i : Fin 10, l ⟨42 + i.val, by omega⟩ := by
    unfold UniformRankFourNecessary.sumLast
    apply Finset.sum_congr rfl
    intro i _
    rw [dif_pos (show 36 + 16 - 10 + i.val < 36 + 16 by omega)]
  rw [hf, hl] at h4
  have hK : K1 (SpectralBoundaryTransfer.boundaryValues (36 + 7) l) =
      (!![2*l 51, l 50-l 0, l 48-l 1;
        l 50-l 0, 2*l 49, l 47-l 2;
        l 48-l 1, l 47-l 2, 2*l 46] : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [K1, SpectralBoundaryTransfer.boundaryValues,
        SpectralBoundaryTransfer.boundaryIndex]
  rw [hK] at h1
  have hs := QuadbitUniformSpectralBound.actual_k1_l4_length52_purity_bound
    l ho hn ht h4 h1
  have hvalue : SpectralBoundaryTransfer.purityBound (36 + 16) =
      (5 / 243 : ℝ) := by
    norm_num [SpectralBoundaryTransfer.purityBound]
  rw [hvalue]
  exact hs

/- Reindex by substituting the dimension equality in the entire telescope.
This avoids identifying spectra belonging to different physical states. -/
private theorem finite_spectral_bound (N : ℕ) (hN : 24 ≤ N) (hN52 : N ≤ 52)
    (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i)
    (ht : ∑ i, l i = 1)
    (h1 : (K1 (QuadbitQuintitMaximumPurity.cornerBoundaryValues N (by omega) l)).PosSemidef)
    (h2 : (K2 (QuadbitQuintitMaximumPurity.cornerBoundaryValues N (by omega) l)).PosSemidef)
    (h4 : UniformRankFourNecessary.sumFirst 6 l ≤
      UniformRankFourNecessary.sumLast 10 l) :
    ∑ i, (l i) ^ 2 ≤ SpectralBoundaryTransfer.purityBound N := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, N = k + 16 := ⟨N - 16, by omega⟩
  subst N
  have hb : QuadbitQuintitMaximumPurity.cornerBoundaryValues (k + 16) (by omega) l =
      SpectralBoundaryTransfer.boundaryValues (k + 7) l := by
    funext q
    apply congrArg l
    apply Fin.ext
    dsimp only [QuadbitQuintitMaximumPurity.cornerBoundaryValues,
      SpectralBoundaryTransfer.boundaryValues, SpectralBoundaryTransfer.boundaryIndex]
    split_ifs <;> simp_all <;> omega
  rw [hb] at h1 h2
  exact SpectralBoundaryTransfer.rank_four_endpoint_interval
    36 (by omega) endpoint52 k (by omega) (by omega) l ho hn ht h1 h2 h4

/-- Upper bound for every actual 4-by-n APPT density in this branch.
Both qutrit pencils and L4 consume exactly the one returned APPT diagonal. -/
theorem physical_purity_upper_bound (n : ℕ) (hn : 7 ≤ n) (hn13 : n ≤ 13)
    (rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ)
    (hpos : rho.PosSemidef) (htrace : rho.trace = 1) (happt : APPT rho) :
    (rho * rho).trace.re ≤ purityValue n := by
  classical
  let e : (Fin 4 × Fin n) ≃ Fin (4 * n) := finProdFinEquiv
  obtain ⟨l, ho, hnonneg, hmass, hdiag, hpur⟩ :=
    QuadbitQuintitMaximumPurity.diagonal_spectral_reduction e rho hpos htrace happt
  obtain ⟨h1, h2⟩ := QuadbitQuintitMaximumPurity.diagonal_necessary_both
    (by omega : 3 ≤ 4) (by omega : 3 ≤ n) e l hdiag
  have hL4 := UniformRankFourNecessary.uniform_rank_four_necessary
    (by omega : 4 ≤ 4) (by omega : 4 ≤ n) e l hdiag
  have hs := finite_spectral_bound (4 * n) (by omega) (by omega)
    l ho hnonneg hmass h1 h2 hL4
  rw [hpur]
  simpa only [purityValue, SpectralBoundaryTransfer.purityBound] using hs

/- The existing physical ray theorem pays PSD, trace, APPT and the actual
trace-square identity. No LMI sufficiency inference occurs in attainment. -/
private theorem attainer_data (n : ℕ) (hn : 7 ≤ n) :
    attainingDensity n hn = diagonal (fun p : Fin 4 × Fin n =>
      if p = basisZero n hn then (3 / (((4*n : ℕ) : ℂ) + 2) : ℂ)
      else (1 / (((4*n : ℕ) : ℂ) + 2) : ℂ)) ∧
    (attainingDensity n hn).PosSemidef ∧ (attainingDensity n hn).trace = 1 ∧
    APPT (attainingDensity n hn) ∧
    (attainingDensity n hn * attainingDensity n hn).trace.re = purityValue n := by
  classical
  have hnpos : 0 < n := by omega
  letI : NeZero n := ⟨ne_of_gt hnpos⟩
  let v : Fin 4 × Fin n → ℂ := Pi.single (0, 0) 1
  have hv : star v ⬝ᵥ v = (1 : ℂ) := by
    simp [v, dotProduct, Pi.single_apply]
  have heq : attainingDensity n hn = QuadbitQuintitMaximumPurity.normalizedRay v := rfl
  obtain ⟨hd, ht, ha, hp⟩ := QuadbitQuintitMaximumPurity.normalized_ray v hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact QuadbitQuintitMaximumPurity.normalized_basis_diagonal (basisZero n hn)
  · rw [heq]
    exact hd
  · rw [heq]
    exact ht
  · rw [heq]
    exact ha
  · simpa only [heq, purityValue] using hp

/-- Actual attained maximum and real supremum, with no spectral
endpoint or PSD supplier left as a hypothesis. Scope is exactly 7 <= n <= 13. -/
theorem physical_finite7_maximum (n : ℕ) (hn : 7 ≤ n) (hn13 : n ≤ 13) :
    0 < (((4*n : ℕ) : ℝ) + 2) ∧
    (∀ rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ,
      rho.PosSemidef → rho.trace = 1 → APPT rho →
      (rho * rho).trace.re ≤ purityValue n) ∧
    (∃ rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ,
      rho = QuadbitQuintitMaximumPurity.normalizedRay
        (Pi.single (basisZero n hn) 1) ∧
      rho = diagonal (fun p : Fin 4 × Fin n =>
        if p = basisZero n hn then (3 / (((4*n : ℕ) : ℂ) + 2) : ℂ)
        else (1 / (((4*n : ℕ) : ℂ) + 2) : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
      (rho * rho).trace.re = purityValue n) ∧
    (physicalPurities n).Nonempty ∧ BddAbove (physicalPurities n) ∧
    sSup (physicalPurities n) = purityValue n := by
  classical
  obtain ⟨hdiag, hpos, htrace, happt, hpur⟩ := attainer_data n hn
  have hattain : purityValue n ∈ physicalPurities n :=
    ⟨attainingDensity n hn, ⟨hpos, htrace⟩, happt, hpur⟩
  have hnonempty : (physicalPurities n).Nonempty := ⟨purityValue n, hattain⟩
  have hupper : ∀ p ∈ physicalPurities n, p ≤ purityValue n := by
    rintro p ⟨rho, hdensity, ha, hp⟩
    rw [← hp]
    exact physical_purity_upper_bound n hn hn13 rho hdensity.1 hdensity.2 ha
  have hbounded : BddAbove (physicalPurities n) := ⟨purityValue n, hupper⟩
  refine ⟨by positivity, physical_purity_upper_bound n hn hn13, ?_,
    hnonempty, hbounded, ?_⟩
  · exact ⟨attainingDensity n hn, rfl, hdiag, ⟨hpos, htrace⟩, happt, hpur⟩
  · exact csSup_eq_of_forall_le_of_forall_lt_exists_gt hnonempty hupper
      (fun w hw => ⟨purityValue n, hattain, hw⟩)

#print axioms physical_purity_upper_bound
#print axioms physical_finite7_maximum

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity
