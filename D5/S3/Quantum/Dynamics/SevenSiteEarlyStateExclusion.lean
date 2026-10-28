/- GID: D5/S3/Quantum/Dynamics/SevenSiteEarlyStateExclusion
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/SevenSiteEarlyStateExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: No 7-site early state exclusion iff positive eigenvalues are multiples of the least. -/

/-
proof_shape:
  claim: definition (the conjecture of Section 4 of arXiv:2507.18767 in the conventions of
    issue #14487)
  result: content; escape_witness (form 1): the same-delivery intermediate proposition
    D5/S3/Quantum/Dynamics/SymmetricSpectrumEndAmplitude.symmetric_spectrum_reduction (spectrum
    (π/T) (0, ±a, ±b, ±c), first-site amplitude a positive multiple of the cosine sum
    amplitudeNumerator a b c at the time π τ / T, transfer at the times T/g) and the frozen
    D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator_zero_iff (a zero of the
    cosine sum in (0, π) iff a ≠ 1), both on the live path. The steps of result itself are:
    gcd(a, b, c) = 1 from the minimality of the transfer time T (a common divisor g > 1 would
    give transfer at the time T/g < T); the equivalence of the divisibility condition on the
    positive eigenvalues with a = 1 (they are π a / T < π b / T < π c / T, and a divides b and c
    with gcd(a, b, c) = 1 exactly when a = 1); and the translation of early state exclusion
    into a zero of the cosine sum in (0, π) by t = π τ / T.
admission_basis: open-problem-resolution (issue #14487; Proved). The source, Library note
  D5/L/GraphInvariants/escobar2025earlystateexclusion, proves the spectra
  {0, ±1, ±2m, ±(2m+1)} (its Theorem 3.2) and {0, ±(2m+1), ±(2m+2), ±(2m+3)} (its Theorem 3.4)
  and states the general case as a conjecture.
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianPropagator
  statement_id sha256:cda9b54324a60c3d19d82ae43fd312bec7fd42bc7d2748ad663e34115d863ceb.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian
  statement_id sha256:2a698170a16b6888380fcc8f26eb4e7fe06d99129518c7579da37d4ef440257a.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.HasPST
  statement_id sha256:757dd0796ec75540b7989b0cc8ff7b30e16f838075ebdaf9dafec9866abcd80e.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian_isHermitian
  statement_id sha256:9ef82c6c2002677d2d5ca2cbbbca0f264c96cd4b9b9c894ea79af8bb10c65c8a.
  D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator
  statement_id sha256:fae52ee8cd1ad5bddce5fa09f4e2e1443642529470a5c5478f4d7e16249f196c.
  D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator_zero_iff
  statement_id sha256:38ffaf347d1d914161094e5e315525838939c04f10068f275386945094f813fd.
Same-delivery dependency:
  D5/S3/Quantum/Dynamics/SymmetricSpectrumEndAmplitude.symmetric_spectrum_reduction.
utility: none; no declaration is a bounded enumeration, checker, numeric reduction or certified
instance: the claim quantifies over all seven-site paths with positive weights, all real
potentials and all transfer times.
-/

import D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
import D5.S3.Quantum.Dynamics.SymmetricSpectrumEndAmplitude
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.Field
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.SevenSiteEarlyStateExclusion

open Matrix Finset Complex
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
open D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros
open D5.S3.Quantum.Dynamics.SymmetricSpectrumEndAmplitude

/-- **The seven-site conjecture of Escobar, Garcia and Minenkova** (arXiv:2507.18767,
Section 4). Let `J` be the Hamiltonian of a path on seven sites with positive weights `r` and
real potentials `q` whose spectrum is closed under negation, and let `T > 0` be a time at which
`J` has perfect state transfer between its end sites, with no such transfer at any time in
`(0, T)`. Then the first-site amplitude `(exp (-i τ J))_{0,0}` has no zero `τ ∈ (0, T)` if and
only if every positive eigenvalue of `J` is an integer multiple of the smallest positive
eigenvalue. -/
def claim : Prop :=
  ∀ (r : Fin 6 → ℝ) (q : Fin 7 → ℝ) (T : ℝ), (∀ j, 0 < r j) →
    (∀ k, ∃ l, (pathHamiltonian_isHermitian r q).eigenvalues l =
      -(pathHamiltonian_isHermitian r q).eigenvalues k) →
    0 < T → HasPST (pathHamiltonian r q) T 0 (Fin.last 6) →
    (∀ t, 0 < t → t < T → ¬ HasPST (pathHamiltonian r q) t 0 (Fin.last 6)) →
    ((¬ ∃ τ, 0 < τ ∧ τ < T ∧ hamiltonianPropagator (pathHamiltonian r q) τ 0 0 = 0) ↔
      ∃ k₀, 0 < (pathHamiltonian_isHermitian r q).eigenvalues k₀ ∧
        (∀ k, 0 < (pathHamiltonian_isHermitian r q).eigenvalues k →
          (pathHamiltonian_isHermitian r q).eigenvalues k₀ ≤
            (pathHamiltonian_isHermitian r q).eigenvalues k) ∧
        ∀ k, 0 < (pathHamiltonian_isHermitian r q).eigenvalues k → ∃ n : ℤ,
          (pathHamiltonian_isHermitian r q).eigenvalues k =
            n * (pathHamiltonian_isHermitian r q).eigenvalues k₀)

/-- **The seven-site conjecture holds.** A seven-site chain with positive couplings, real
potentials and symmetric spectrum whose earliest perfect state transfer between its ends occurs
at the time `T` has spectrum `(π / T) (0, ±a, ±b, ±c)` with `a < b < c`, `a`, `c` odd, `b` even
and `gcd(a, b, c) = 1`; its first-site amplitude is a positive multiple of the cosine sum
`amplitudeNumerator a b c` at the time `π τ / T`, which has a zero in `(0, π)` if and only if
`a ≠ 1`, and `a = 1` says that every positive eigenvalue is an integer multiple of the smallest
one. -/
theorem result : claim := by
  intro r q T hr hsym hT hpst hmin
  obtain ⟨a, b, c, σ, κ, ha, hb, hc, ha0, hab, hbc, hκ, hS, hA, hG⟩ :=
    symmetric_spectrum_reduction r q hr hsym hT hpst
  have hu : 0 < Real.pi / T := div_pos Real.pi_pos hT
  have hAr : (0 : ℝ) < a := by exact_mod_cast ha0
  have hABr : (a : ℝ) < b := by exact_mod_cast hab
  have hBCr : (b : ℝ) < c := by exact_mod_cast hbc
  -- minimality of the transfer time
  have hgcd : Nat.gcd (Nat.gcd a b) c = 1 := by
    have hga : Nat.gcd (Nat.gcd a b) c ∣ a :=
      (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have hgb : Nat.gcd (Nat.gcd a b) c ∣ b :=
      (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have hgc : Nat.gcd (Nat.gcd a b) c ∣ c := Nat.gcd_dvd_right _ _
    have hg0 : 0 < Nat.gcd (Nat.gcd a b) c := Nat.pos_of_dvd_of_pos hga ha0
    by_contra hne
    have hg1 : 1 < Nat.gcd (Nat.gcd a b) c := by omega
    have hg0r : (0 : ℝ) < (Nat.gcd (Nat.gcd a b) c : ℝ) := by exact_mod_cast hg0
    have hg1r : (1 : ℝ) < (Nat.gcd (Nat.gcd a b) c : ℝ) := by exact_mod_cast hg1
    exact hmin _ (div_pos hT hg0r) (div_lt_self hT hg1r) (hG _ hga hgb hgc)
  -- early state exclusion is a zero of the cosine sum
  have hESE : (∃ τ, 0 < τ ∧ τ < T ∧ hamiltonianPropagator (pathHamiltonian r q) τ 0 0 = 0) ↔
      ∃ t : ℝ, 0 < t ∧ t < Real.pi ∧ amplitudeNumerator a b c t = 0 := by
    constructor
    · rintro ⟨τ, hτ0, hτT, hτ⟩
      refine ⟨Real.pi * τ / T, div_pos (mul_pos Real.pi_pos hτ0) hT, ?_, ?_⟩
      · rw [div_lt_iff₀ hT]
        exact mul_lt_mul_of_pos_left hτT Real.pi_pos
      · rw [hA τ] at hτ
        exact (mul_eq_zero.mp (Complex.ofReal_eq_zero.mp hτ)).resolve_left hκ.ne'
    · rintro ⟨t, ht0, htπ, ht⟩
      refine ⟨T * t / Real.pi, div_pos (mul_pos hT ht0) Real.pi_pos, ?_, ?_⟩
      · rw [div_lt_iff₀ Real.pi_pos]
        exact mul_lt_mul_of_pos_left htπ hT
      · have harg : Real.pi * (T * t / Real.pi) / T = t := by
          have hTne : T ≠ 0 := hT.ne'
          have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
          field
        rw [hA, harg, ht, mul_zero, Complex.ofReal_zero]
  -- the positive eigenvalues
  have e4 : (pathHamiltonian_isHermitian r q).eigenvalues (σ 4) = Real.pi / T * a := by
    simpa only [Matrix.cons_val] using hS 4
  have e5 : (pathHamiltonian_isHermitian r q).eigenvalues (σ 5) = Real.pi / T * b := by
    simpa only [Matrix.cons_val] using hS 5
  have e6 : (pathHamiltonian_isHermitian r q).eigenvalues (σ 6) = Real.pi / T * c := by
    simpa only [Matrix.cons_val] using hS 6
  have hua : 0 < Real.pi / T * a := mul_pos hu hAr
  have hub : Real.pi / T * (a : ℝ) < Real.pi / T * b := mul_lt_mul_of_pos_left hABr hu
  have huc : Real.pi / T * (b : ℝ) < Real.pi / T * c := mul_lt_mul_of_pos_left hBCr hu
  have hposev : ∀ k, 0 < (pathHamiltonian_isHermitian r q).eigenvalues k →
      (pathHamiltonian_isHermitian r q).eigenvalues k = Real.pi / T * a ∨
        (pathHamiltonian_isHermitian r q).eigenvalues k = Real.pi / T * b ∨
        (pathHamiltonian_isHermitian r q).eigenvalues k = Real.pi / T * c := by
    intro k hk
    obtain ⟨i, rfl⟩ := σ.surjective k
    have n0 : (pathHamiltonian_isHermitian r q).eigenvalues (σ 0) = Real.pi / T * -(c : ℝ) := by
      simpa only [Matrix.cons_val] using hS 0
    have n1 : (pathHamiltonian_isHermitian r q).eigenvalues (σ 1) = Real.pi / T * -(b : ℝ) := by
      simpa only [Matrix.cons_val] using hS 1
    have n2 : (pathHamiltonian_isHermitian r q).eigenvalues (σ 2) = Real.pi / T * -(a : ℝ) := by
      simpa only [Matrix.cons_val] using hS 2
    have n3 : (pathHamiltonian_isHermitian r q).eigenvalues (σ 3) = Real.pi / T * 0 := by
      simpa only [Matrix.cons_val] using hS 3
    fin_cases i
    · exfalso
      have h : 0 < Real.pi / T * -(c : ℝ) := by
        rw [← n0]
        exact hk
      rw [mul_neg] at h
      linarith
    · exfalso
      have h : 0 < Real.pi / T * -(b : ℝ) := by
        rw [← n1]
        exact hk
      rw [mul_neg] at h
      linarith
    · exfalso
      have h : 0 < Real.pi / T * -(a : ℝ) := by
        rw [← n2]
        exact hk
      rw [mul_neg] at h
      linarith
    · exfalso
      have h : 0 < Real.pi / T * (0 : ℝ) := by
        rw [← n3]
        exact hk
      rw [mul_zero] at h
      exact lt_irrefl _ h
    · exact Or.inl e4
    · exact Or.inr (Or.inl e5)
    · exact Or.inr (Or.inr e6)
  -- the divisibility condition is `a = 1`
  have hdiv : (∃ k₀, 0 < (pathHamiltonian_isHermitian r q).eigenvalues k₀ ∧
      (∀ k, 0 < (pathHamiltonian_isHermitian r q).eigenvalues k →
        (pathHamiltonian_isHermitian r q).eigenvalues k₀ ≤
          (pathHamiltonian_isHermitian r q).eigenvalues k) ∧
      ∀ k, 0 < (pathHamiltonian_isHermitian r q).eigenvalues k → ∃ n : ℤ,
        (pathHamiltonian_isHermitian r q).eigenvalues k =
          n * (pathHamiltonian_isHermitian r q).eigenvalues k₀) ↔ a = 1 := by
    constructor
    · rintro ⟨k₀, hk₀, hle, hmul⟩
      have h4 := hle (σ 4) (by rw [e4]; exact hua)
      rw [e4] at h4
      have hk₀a : (pathHamiltonian_isHermitian r q).eigenvalues k₀ = Real.pi / T * a := by
        rcases hposev k₀ hk₀ with h | h | h
        · exact h
        · rw [h] at h4
          exact absurd h4 (not_le.mpr hub)
        · rw [h] at h4
          exact absurd h4 (not_le.mpr (hub.trans huc))
      have hdvd : ∀ d : ℕ, (∃ n : ℤ, Real.pi / T * (d : ℝ) = n * (Real.pi / T * a)) → a ∣ d := by
        rintro d ⟨n, hn⟩
        have h1 : Real.pi / T * (d : ℝ) = Real.pi / T * ((n : ℝ) * a) := by
          rw [hn]
          ring
        have h2 : ((d : ℤ) : ℝ) = ((n * a : ℤ) : ℝ) := by
          push_cast
          exact mul_left_cancel₀ hu.ne' h1
        have h3 : (d : ℤ) = n * a := by exact_mod_cast h2
        exact Int.natCast_dvd_natCast.mp (Dvd.intro_left n h3.symm)
      have hab' : a ∣ b := hdvd b (by
        obtain ⟨n, hn⟩ := hmul (σ 5) (by rw [e5]; exact hua.trans hub)
        exact ⟨n, by rw [← e5, ← hk₀a]; exact hn⟩)
      have hac' : a ∣ c := hdvd c (by
        obtain ⟨n, hn⟩ := hmul (σ 6) (by rw [e6]; exact (hua.trans hub).trans huc)
        exact ⟨n, by rw [← e6, ← hk₀a]; exact hn⟩)
      have h1 : a ∣ Nat.gcd (Nat.gcd a b) c := Nat.dvd_gcd (Nat.dvd_gcd dvd_rfl hab') hac'
      rw [hgcd] at h1
      exact Nat.dvd_one.mp h1
    · intro ha1
      refine ⟨σ 4, by rw [e4]; exact hua, fun k hk => ?_, fun k hk => ?_⟩
      · rw [e4]
        rcases hposev k hk with h | h | h
        · exact h.ge
        · rw [h]
          exact hub.le
        · rw [h]
          exact (hub.trans huc).le
      · rw [e4, ha1]
        rcases hposev k hk with h | h | h
        · exact ⟨1, by rw [h, ha1]; push_cast; ring⟩
        · exact ⟨b, by rw [h]; push_cast; ring⟩
        · exact ⟨c, by rw [h]; push_cast; ring⟩
  exact (not_congr (hESE.trans (amplitudeNumerator_zero_iff a b c ha hb hc hab hbc hgcd))).trans
    (not_not.trans hdiv.symm)

end D5.S3.Quantum.Dynamics.SevenSiteEarlyStateExclusion
