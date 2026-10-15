/- GID: D5/S3/Quantum/Dynamics/SymmetricSpectrumEndAmplitude
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/SymmetricSpectrumEndAmplitude
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Seven-site transfer chains with symmetric spectrum have a cosine-sum end amplitude. -/

/-
proof_shape: symmetric_spectrum_end_amplitude: content; escape_witness: the public conclusion
itself (form 2), as a proof shape: it is not an instantiation of a frozen or Mathlib statement.
For a seven-site path with positive weights, real potentials, symmetric spectrum and transfer
between its ends at a real time T, the eigenvalues are 0, ±x, ±y, ±z with exp(iTx) = -1,
exp(iTy) = 1, exp(iTz) = -1, and the first-site amplitude is
P [1/(x²y²z²) + cos(τx)/(x²(y²-x²)(z²-x²)) + cos(τy)/(y²(y²-x²)(z²-y²))
+ cos(τz)/(z²(z²-x²)(z²-y²))], P the product of the weights. The formula is known (see
admission_basis); the live path derives it from the mirror symmetry of the increasing
enumeration of a symmetric simple spectrum, the signs of the seven nodal products, and the
weights and phases of D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pst_spectral_weights.
consumer: symmetric_spectrum_reduction.
proof_shape: symmetric_spectrum_reduction: content; escape_witness: the public conclusion itself
(form 2), as a proof shape: the spectrum is (π/T) (0, ±a, ±b, ±c) with a < b < c natural, a and c
odd, b even, the first-site amplitude is a positive multiple of the cosine sum
D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator a b c at the time π τ / T,
and every common divisor g of a, b, c gives transfer at the time T/g. These facts are known (see
admission_basis); the live path derives them from the phases by the integrality of T x/π,
T y/π, T z/π, a rescaling of the amplitude, and the equality of the spectral phases at the times
T/g and T. consumer: D5/S3/Quantum/Dynamics/SevenSiteEarlyStateExclusion.result.
Private helpers:
proof_shape: symmetric_spectrum_weights: content (as for symmetric_spectrum_end_amplitude:
spectrum, phases and first-site weights); consumer: symmetric_spectrum_end_amplitude.
proof_shape: exists_symmetric_enumeration: content (sorting and mirror symmetry of seven distinct
reals closed under negation); consumer: symmetric_spectrum_weights.
proof_shape: strictMono_rev_neg: content (uniqueness of the increasing enumeration of a finite
set); consumer: exists_symmetric_enumeration.
proof_shape: prod_erase_symmetric: bind-only (normalisation: evaluation of the seven nodal
products); consumer: symmetric_spectrum_weights.
proof_shape: sum_weight_exp_symmetric: bind-only (normalisation: the seven weighted phases are
paired into cosines by exp_neg_add_exp); consumer: symmetric_spectrum_end_amplitude.
proof_shape: exp_neg_add_exp: bind-only (Complex.two_cos); consumer: sum_weight_exp_symmetric.
proof_shape: spectral_exp_apply_self: bind-only (diagonal entry of
RationalWeightPathTransfer.spectral_exp); consumer: symmetric_spectrum_end_amplitude.
proof_shape: hasPST_of_phase_eq: bind-only (RationalWeightPathTransfer.spectral_exp at two
times); consumer: symmetric_spectrum_reduction.
proof_shape: exists_odd_nat, exists_even_nat: bind-only (a positive integer is a natural number);
consumer: symmetric_spectrum_reduction.
proof_shape: exp_div_eq: bind-only (Complex.exp_eq_exp_iff_exists_int); consumer:
symmetric_spectrum_reduction.
Private definitions nodal, nodalAbs (the seven nodal products and their absolute values);
consumer: prod_erase_symmetric, sum_weight_exp_symmetric, symmetric_spectrum_weights.
admission_basis: escape-witness for the proof shape (the declarations are not instantiations of
frozen or Mathlib statements); the mathematics is known. The amplitude formula is Eq. (2.1) of
arXiv:2507.18767 for the explicit seven-site matrix, and for every persymmetric Jacobi matrix
with symmetric spectrum of any order it is the Proposition 'Amplitude Formulas' of
arXiv:2606.04353 (Hochstadt's weights); with Kay's criterion, which makes every chain with
perfect state transfer persymmetric with odd spacing of the spectrum in units of π/T, it covers
every transferring chain. The reduction to integer spectra of alternating parity with gcd 1,
first transfer at π and time scaling by a common factor is stated in Section 3 of
arXiv:2606.04353. Library notes D5/L/GraphInvariants/escobar2025earlystateexclusion and
D5/L/GraphInvariants/escobar2026spectralfusion. What this module adds is the Lean derivation of
these facts for seven sites from the hypothesis of transfer at a time T and the symmetry of the
spectrum, through RationalWeightPathTransfer.pst_spectral_weights. The conjecture itself is
settled in D5/S3/Quantum/Dynamics/SevenSiteEarlyStateExclusion.
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianPropagator
  statement_id sha256:cda9b54324a60c3d19d82ae43fd312bec7fd42bc7d2748ad663e34115d863ceb.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian
  statement_id sha256:2a698170a16b6888380fcc8f26eb4e7fe06d99129518c7579da37d4ef440257a.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.HasPST
  statement_id sha256:757dd0796ec75540b7989b0cc8ff7b30e16f838075ebdaf9dafec9866abcd80e.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.hamiltonianPropagator_neg
  statement_id sha256:5965bdf5e9583b3548e15db5890602825b2142c2be7b5125a36b6586891c2045.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian_isHermitian
  statement_id sha256:9ef82c6c2002677d2d5ca2cbbbca0f264c96cd4b9b9c894ea79af8bb10c65c8a.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.spectral_exp
  statement_id sha256:6d70a85b3878e56c8305508bbcad20a585f5e754d4479bd5c7bbe65bab3ec540.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.exists_int_of_exp_eq_one
  statement_id sha256:c53ecfce15def8b3681bf73a34fabf6b7432c89fc5c24270f1511c455e6d025a.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.exists_int_of_exp_eq_neg_one
  statement_id sha256:e5f0dc0f4cfd995c3ce9f987e1ecd249b8d3fc701986c281115dfd87445d5034.
  D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator
  statement_id sha256:fae52ee8cd1ad5bddce5fa09f4e2e1443642529470a5c5478f4d7e16249f196c.
Same-delivery dependency:
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pst_spectral_weights,
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian_pow_apply_ends.
utility: none; no declaration is a bounded enumeration, checker, numeric reduction or certified
instance: every statement quantifies over all positive weights, all real potentials and all
transfer times of seven-site paths.
-/

import D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.Field
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.SymmetricSpectrumEndAmplitude

open Matrix Finset Complex
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
open D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros

section Spectral

variable {V : Type*} [Fintype V] [DecidableEq V] {H : Matrix V V ℂ} (hH : H.IsHermitian)

/-- The diagonal entries of the propagator `exp (s • H)` of a Hermitian matrix are the sums of
its spectral phases weighted by the squared moduli of the eigenvector entries. -/
private theorem spectral_exp_apply_self (s : ℂ) (a : V) :
    NormedSpace.exp (s • H) a a = ∑ k,
      (Complex.normSq ((hH.eigenvectorUnitary : Matrix V V ℂ) a k) : ℂ) *
        Complex.exp (s * hH.eigenvalues k) := by
  rw [spectral_exp hH, mul_apply]
  simp only [mul_diagonal, star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.mul_conj]
  ring

/-- Equal spectral phases at the times `s` and `t` carry perfect state transfer from the time
`t` to the time `s`. -/
private theorem hasPST_of_phase_eq {s t : ℝ} (a b : V)
    (hphase : ∀ k, Complex.exp ((s : ℂ) * I * hH.eigenvalues k) =
      Complex.exp ((t : ℂ) * I * hH.eigenvalues k))
    (hpst : HasPST H t a b) : HasPST H s a b := by
  unfold HasPST at hpst ⊢
  rw [hamiltonianPropagator_neg, spectral_exp hH] at hpst ⊢
  simp only [hphase]
  exact hpst

end Spectral

/-- A positive real number of the form `2 n + 1` with `n` an integer is an odd natural number. -/
private theorem exists_odd_nat {θ : ℝ} (hθ : 0 < θ) (h : ∃ n : ℤ, θ = 2 * n + 1) :
    ∃ a : ℕ, Odd a ∧ θ = a := by
  obtain ⟨n, hn⟩ := h
  have hn0 : 0 ≤ n := by
    by_contra hneg
    have h1 : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    linarith
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ 2 * n + 1)
  refine ⟨a, ⟨n.toNat, by omega⟩, ?_⟩
  rw [hn]
  exact_mod_cast ha

/-- A positive real number of the form `2 n` with `n` an integer is an even natural number. -/
private theorem exists_even_nat {θ : ℝ} (hθ : 0 < θ) (h : ∃ n : ℤ, θ = 2 * n) :
    ∃ b : ℕ, Even b ∧ θ = b := by
  obtain ⟨n, hn⟩ := h
  have hn0 : 0 ≤ n := by
    by_contra hneg
    have h1 : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    linarith
  obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ 2 * n)
  refine ⟨b, ⟨n.toNat, by omega⟩, ?_⟩
  rw [hn]
  exact_mod_cast hb

/-- For an odd `g` dividing the integer `n`, the phases `exp (i s (π / T) n)` at the times
`s = T / g` and `s = T` coincide. -/
private theorem exp_div_eq {T : ℝ} (hT : T ≠ 0) {g : ℕ} (hg : Odd g) {n : ℤ}
    (hn : (g : ℤ) ∣ n) :
    Complex.exp (((T / g : ℝ) : ℂ) * I * ((Real.pi / T * n : ℝ) : ℂ)) =
      Complex.exp ((T : ℂ) * I * ((Real.pi / T * n : ℝ) : ℂ)) := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨h, rfl⟩ := hg
  have hTc : (T : ℂ) ≠ 0 := ofReal_ne_zero.mpr hT
  have hgc : (2 * (h : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * h)
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-((h : ℤ) * m), ?_⟩
  push_cast
  field

/-- `exp (-i τ (-θ)) + exp (-i τ θ) = 2 cos (τ θ)`. -/
private theorem exp_neg_add_exp (τ θ : ℝ) :
    Complex.exp (((-τ : ℝ) : ℂ) * I * ((-θ : ℝ) : ℂ)) +
        Complex.exp (((-τ : ℝ) : ℂ) * I * (θ : ℂ)) =
      ((2 * Real.cos (τ * θ) : ℝ) : ℂ) := by
  have e1 : ((-τ : ℝ) : ℂ) * I * ((-θ : ℝ) : ℂ) = ((τ * θ : ℝ) : ℂ) * I := by
    push_cast
    ring
  have e2 : ((-τ : ℝ) : ℂ) * I * (θ : ℂ) = -((τ * θ : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [e1, e2, ← Complex.two_cos, ← Complex.ofReal_cos]
  norm_cast

/-- The increasing enumeration of finitely many reals closed under negation is odd under the
reversal of the indices. -/
private theorem strictMono_rev_neg {n : ℕ} {μ : Fin n → ℝ} (hμ : StrictMono μ)
    (hsym : ∀ i, ∃ j, μ j = -μ i) (i : Fin n) : μ i.rev = -μ i := by
  have hν : StrictMono fun i : Fin n => -μ i.rev := fun i j hij =>
    neg_lt_neg (hμ (Fin.rev_lt_rev.mpr hij))
  have hrange : Set.range (fun i : Fin n => -μ i.rev) = Set.range μ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hsym i.rev
      exact ⟨j, hj⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hsym i
      exact ⟨j.rev, by simp [hj]⟩
  have h : -μ i.rev = μ i := congrFun ((hν.range_inj hμ).mp hrange) i
  linarith

/-- The nodal products `∏_{j ≠ i} (μ i - μ j)` of the seven points
`μ = (-z, -y, -x, 0, x, y, z)`. -/
private def nodal (x y z : ℝ) : Fin 7 → ℝ :=
  ![2 * z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2),
    -(2 * y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)),
    2 * x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2),
    -(x ^ 2 * y ^ 2 * z ^ 2),
    2 * x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2),
    -(2 * y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)),
    2 * z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)]

/-- The absolute values of the nodal products of the seven points `(-z, -y, -x, 0, x, y, z)`
with `0 < x < y < z`. -/
private def nodalAbs (x y z : ℝ) : Fin 7 → ℝ :=
  ![2 * z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2),
    2 * y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2),
    2 * x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2),
    x ^ 2 * y ^ 2 * z ^ 2,
    2 * x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2),
    2 * y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2),
    2 * z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)]

/-- Evaluation of the nodal products of the seven points `(-z, -y, -x, 0, x, y, z)`. -/
private theorem prod_erase_symmetric (x y z : ℝ) (i : Fin 7) :
    ∏ j ∈ univ.erase i, (![-z, -y, -x, 0, x, y, z] i - ![-z, -y, -x, 0, x, y, z] j) =
      nodal x y z i := by
  rw [← Finset.filter_ne', Finset.prod_filter, Fin.prod_univ_seven]
  fin_cases i <;> simp [nodal] <;> ring

/-- Seven distinct reals closed under negation are, in increasing order,
`-z, -y, -x, 0, x, y, z` with `0 < x < y < z`. -/
private theorem exists_symmetric_enumeration (Λ : Fin 7 → ℝ) (hinj : Function.Injective Λ)
    (hsym : ∀ k, ∃ l, Λ l = -Λ k) :
    ∃ (σ : Equiv.Perm (Fin 7)) (x y z : ℝ), 0 < x ∧ x < y ∧ y < z ∧
      ∀ i, Λ (σ i) = ![-z, -y, -x, 0, x, y, z] i := by
  set σ := Tuple.sort Λ with hσ
  have hmono : StrictMono fun i => Λ (σ i) :=
    (Tuple.monotone_sort Λ).strictMono_of_injective (hinj.comp σ.injective)
  have hsym' : ∀ i, ∃ j, Λ (σ j) = -Λ (σ i) := by
    intro i
    obtain ⟨l, hl⟩ := hsym (σ i)
    exact ⟨σ.symm l, by rw [Equiv.apply_symm_apply]; exact hl⟩
  have hrev : ∀ i : Fin 7, Λ (σ i.rev) = -Λ (σ i) := fun i =>
    strictMono_rev_neg hmono hsym' i
  have h3 : Λ (σ 3) = 0 := by
    have h := hrev 3
    rw [show (3 : Fin 7).rev = 3 by decide] at h
    linarith
  have h2 : Λ (σ 2) = -Λ (σ 4) := by
    have h := hrev 4
    rwa [show (4 : Fin 7).rev = 2 by decide] at h
  have h1 : Λ (σ 1) = -Λ (σ 5) := by
    have h := hrev 5
    rwa [show (5 : Fin 7).rev = 1 by decide] at h
  have h0 : Λ (σ 0) = -Λ (σ 6) := by
    have h := hrev 6
    rwa [show (6 : Fin 7).rev = 0 by decide] at h
  have h34 : Λ (σ 3) < Λ (σ 4) := hmono (show (3 : Fin 7) < 4 by decide)
  have h45 : Λ (σ 4) < Λ (σ 5) := hmono (show (4 : Fin 7) < 5 by decide)
  have h56 : Λ (σ 5) < Λ (σ 6) := hmono (show (5 : Fin 7) < 6 by decide)
  refine ⟨σ, Λ (σ 4), Λ (σ 5), Λ (σ 6), by linarith, h45, h56, fun i => ?_⟩
  fin_cases i
  exacts [h0, h1, h2, h3, rfl, rfl, rfl]

/-- The weighted sum of the phases `exp (-i τ μ)` over the points
`μ = (-z, -y, -x, 0, x, y, z)`, with the weights `P / |∏_{j ≠ i} (μ i - μ j)|`, is a cosine
sum. -/
private theorem sum_weight_exp_symmetric (P x y z τ : ℝ) (w Λ : Fin 7 → ℝ)
    (hΛ : ∀ i, Λ i = ![-z, -y, -x, 0, x, y, z] i) (hw : ∀ i, w i = P / nodalAbs x y z i) :
    ∑ i, (w i : ℂ) * Complex.exp (((-τ : ℝ) : ℂ) * I * (Λ i : ℂ)) =
      ((P * (1 / (x ^ 2 * y ^ 2 * z ^ 2) +
        Real.cos (τ * x) / (x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2)) +
        Real.cos (τ * y) / (y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)) +
        Real.cos (τ * z) / (z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2))) : ℝ) : ℂ) := by
  have hc : ∀ θ : ℝ, Complex.exp (((-τ : ℝ) : ℂ) * I * ((-θ : ℝ) : ℂ)) =
      ((2 * Real.cos (τ * θ) : ℝ) : ℂ) - Complex.exp (((-τ : ℝ) : ℂ) * I * (θ : ℂ)) :=
    fun θ => eq_sub_of_add_eq (exp_neg_add_exp τ θ)
  have e0 : Λ 0 = -z := by simpa only [Matrix.cons_val] using hΛ 0
  have e1 : Λ 1 = -y := by simpa only [Matrix.cons_val] using hΛ 1
  have e2 : Λ 2 = -x := by simpa only [Matrix.cons_val] using hΛ 2
  have e3 : Λ 3 = 0 := by simpa only [Matrix.cons_val] using hΛ 3
  have e4 : Λ 4 = x := by simpa only [Matrix.cons_val] using hΛ 4
  have e5 : Λ 5 = y := by simpa only [Matrix.cons_val] using hΛ 5
  have e6 : Λ 6 = z := by simpa only [Matrix.cons_val] using hΛ 6
  have w0 : w 0 = P / (2 * z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)) := by
    simpa only [nodalAbs, Matrix.cons_val] using hw 0
  have w1 : w 1 = P / (2 * y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)) := by
    simpa only [nodalAbs, Matrix.cons_val] using hw 1
  have w2 : w 2 = P / (2 * x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2)) := by
    simpa only [nodalAbs, Matrix.cons_val] using hw 2
  have w3 : w 3 = P / (x ^ 2 * y ^ 2 * z ^ 2) := by
    simpa only [nodalAbs, Matrix.cons_val] using hw 3
  have w4 : w 4 = P / (2 * x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2)) := by
    simpa only [nodalAbs, Matrix.cons_val] using hw 4
  have w5 : w 5 = P / (2 * y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)) := by
    simpa only [nodalAbs, Matrix.cons_val] using hw 5
  have w6 : w 6 = P / (2 * z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)) := by
    simpa only [nodalAbs, Matrix.cons_val] using hw 6
  rw [Fin.sum_univ_seven, e0, e1, e2, e3, e4, e5, e6, w0, w1, w2, w3, w4, w5, w6, hc z, hc y,
    hc x, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  generalize z ^ 2 - x ^ 2 = F₁
  generalize z ^ 2 - y ^ 2 = F₂
  generalize y ^ 2 - x ^ 2 = F₃
  push_cast
  ring

section SevenSites

variable (r : Fin 6 → ℝ) (q : Fin 7 → ℝ)

/-- Spectrum, phases and first-site spectral weights of a seven-site path with positive weights,
symmetric spectrum and transfer between its ends at the time `T`. -/
private theorem symmetric_spectrum_weights (hr : ∀ j, 0 < r j)
    (hsym : ∀ k, ∃ l, (pathHamiltonian_isHermitian r q).eigenvalues l =
      -(pathHamiltonian_isHermitian r q).eigenvalues k)
    {T : ℝ} (hpst : HasPST (pathHamiltonian r q) T 0 (Fin.last 6)) :
    ∃ (σ : Equiv.Perm (Fin 7)) (x y z : ℝ), 0 < x ∧ x < y ∧ y < z ∧
      (∀ i, (pathHamiltonian_isHermitian r q).eigenvalues (σ i) =
        ![-z, -y, -x, 0, x, y, z] i) ∧
      Complex.exp ((T : ℂ) * I * x) = -1 ∧ Complex.exp ((T : ℂ) * I * y) = 1 ∧
      Complex.exp ((T : ℂ) * I * z) = -1 ∧
      ∀ i, Complex.normSq (((pathHamiltonian_isHermitian r q).eigenvectorUnitary :
          Matrix (Fin 7) (Fin 7) ℂ) 0 (σ i)) = (∏ t, r t) / nodalAbs x y z i := by
  set Λ := (pathHamiltonian_isHermitian r q).eigenvalues with hΛ
  set W : Matrix (Fin 7) (Fin 7) ℂ :=
    ↑(pathHamiltonian_isHermitian r q).eigenvectorUnitary with hW
  set P : ℝ := ∏ t, r t with hP
  have hPpos : 0 < P := Finset.prod_pos fun t _ => hr t
  set γ := NormedSpace.exp (((T : ℂ) * I) • pathHamiltonian r q) 0 (Fin.last 6) with hγ
  let ρ : Fin 7 → ℝ := fun k => P / ∏ l ∈ univ.erase k, (Λ k - Λ l)
  obtain ⟨hinj, -, -, habsρ, hsign⟩ :
      Function.Injective Λ ∧ (∀ k, W 0 k * starRingEnd ℂ (W (Fin.last 6) k) = (ρ k : ℂ)) ∧
        (∀ k, Complex.exp ((T : ℂ) * I * Λ k) * (ρ k : ℂ) =
          γ * (Complex.normSq (W 0 k) : ℂ)) ∧
        (∀ k, |ρ k| = Complex.normSq (W 0 k)) ∧
        ∀ k, Complex.exp ((T : ℂ) * I * Λ k) = if 0 < ρ k then γ else -γ :=
    pst_spectral_weights (pathHamiltonian_isHermitian r q) 0 (Fin.last 6) 6
      (Fintype.card_fin _) P hPpos.ne'
      (fun p hp => (pathHamiltonian_pow_apply_ends r q p hp).2) hpst
  obtain ⟨σ, x, y, z, hx, hxy, hyz, hσ⟩ := exists_symmetric_enumeration Λ hinj hsym
  have hy : 0 < y := hx.trans hxy
  have hz : 0 < z := hy.trans hyz
  have hyx : 0 < y ^ 2 - x ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hxy) (add_pos hx hy)]
  have hzx : 0 < z ^ 2 - x ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr (hxy.trans hyz)) (add_pos hx hz)]
  have hzy : 0 < z ^ 2 - y ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hyz) (add_pos hy hz)]
  have hd0 : 0 < 2 * z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2) :=
    mul_pos (mul_pos (mul_pos two_pos (pow_pos hz 2)) hzx) hzy
  have hd1 : 0 < 2 * y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2) :=
    mul_pos (mul_pos (mul_pos two_pos (pow_pos hy 2)) hyx) hzy
  have hd2 : 0 < 2 * x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2) :=
    mul_pos (mul_pos (mul_pos two_pos (pow_pos hx 2)) hyx) hzx
  have hd3 : 0 < x ^ 2 * y ^ 2 * z ^ 2 :=
    mul_pos (mul_pos (pow_pos hx 2) (pow_pos hy 2)) (pow_pos hz 2)
  have hD : ∀ i, ρ (σ i) = P / nodal x y z i := by
    intro i
    have h1 : ∏ l ∈ univ.erase (σ i), (Λ (σ i) - Λ l) =
        ∏ j ∈ univ.erase i, (![-z, -y, -x, 0, x, y, z] i - ![-z, -y, -x, 0, x, y, z] j) := by
      refine (Finset.prod_equiv σ (by simp) fun j _ => ?_).symm
      simp only [hσ]
    change P / ∏ l ∈ univ.erase (σ i), (Λ (σ i) - Λ l) = _
    rw [h1, prod_erase_symmetric]
  have e3 : Λ (σ 3) = 0 := by simpa only [Matrix.cons_val] using hσ 3
  have e4 : Λ (σ 4) = x := by simpa only [Matrix.cons_val] using hσ 4
  have e5 : Λ (σ 5) = y := by simpa only [Matrix.cons_val] using hσ 5
  have e6 : Λ (σ 6) = z := by simpa only [Matrix.cons_val] using hσ 6
  have hneg : ∀ d : ℝ, 0 < d → |P / -d| = P / d := fun d hd => by
    rw [div_neg, abs_neg, abs_of_pos (div_pos hPpos hd)]
  have n0 : nodal x y z 0 = 2 * z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2) := by
    simp only [nodal, Matrix.cons_val]
  have n1 : nodal x y z 1 = -(2 * y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)) := by
    simp only [nodal, Matrix.cons_val]
  have n2 : nodal x y z 2 = 2 * x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2) := by
    simp only [nodal, Matrix.cons_val]
  have n3 : nodal x y z 3 = -(x ^ 2 * y ^ 2 * z ^ 2) := by
    simp only [nodal, Matrix.cons_val]
  have n4 : nodal x y z 4 = 2 * x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2) := by
    simp only [nodal, Matrix.cons_val]
  have n5 : nodal x y z 5 = -(2 * y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)) := by
    simp only [nodal, Matrix.cons_val]
  have n6 : nodal x y z 6 = 2 * z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2) := by
    simp only [nodal, Matrix.cons_val]
  have a0 : nodalAbs x y z 0 = 2 * z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2) := by
    simp only [nodalAbs, Matrix.cons_val]
  have a1 : nodalAbs x y z 1 = 2 * y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2) := by
    simp only [nodalAbs, Matrix.cons_val]
  have a2 : nodalAbs x y z 2 = 2 * x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2) := by
    simp only [nodalAbs, Matrix.cons_val]
  have a3 : nodalAbs x y z 3 = x ^ 2 * y ^ 2 * z ^ 2 := by
    simp only [nodalAbs, Matrix.cons_val]
  have a4 : nodalAbs x y z 4 = 2 * x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2) := by
    simp only [nodalAbs, Matrix.cons_val]
  have a5 : nodalAbs x y z 5 = 2 * y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2) := by
    simp only [nodalAbs, Matrix.cons_val]
  have a6 : nodalAbs x y z 6 = 2 * z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2) := by
    simp only [nodalAbs, Matrix.cons_val]
  have hρ3 : ρ (σ 3) < 0 := by
    rw [hD 3, n3]
    exact div_neg_of_pos_of_neg hPpos (neg_neg_of_pos hd3)
  have hρ4 : 0 < ρ (σ 4) := by
    rw [hD 4, n4]
    exact div_pos hPpos hd2
  have hρ5 : ρ (σ 5) < 0 := by
    rw [hD 5, n5]
    exact div_neg_of_pos_of_neg hPpos (neg_neg_of_pos hd1)
  have hρ6 : 0 < ρ (σ 6) := by
    rw [hD 6, n6]
    exact div_pos hPpos hd0
  have hγ1 : γ = -1 := by
    have h := (hsign (σ 3)).trans (if_neg (not_lt.mpr hρ3.le))
    rw [e3, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
    linear_combination h
  have hEx : Complex.exp ((T : ℂ) * I * x) = -1 := by
    have h := (hsign (σ 4)).trans (if_pos hρ4)
    rw [e4, hγ1] at h
    exact h
  have hEy : Complex.exp ((T : ℂ) * I * y) = 1 := by
    have h := (hsign (σ 5)).trans (if_neg (not_lt.mpr hρ5.le))
    rw [e5, hγ1, neg_neg] at h
    exact h
  have hEz : Complex.exp ((T : ℂ) * I * z) = -1 := by
    have h := (hsign (σ 6)).trans (if_pos hρ6)
    rw [e6, hγ1] at h
    exact h
  have hw0 : |P / nodal x y z 0| = P / nodalAbs x y z 0 := by
    rw [n0, a0]
    exact abs_of_pos (div_pos hPpos hd0)
  have hw1 : |P / nodal x y z 1| = P / nodalAbs x y z 1 := by
    rw [n1, a1]
    exact hneg _ hd1
  have hw2 : |P / nodal x y z 2| = P / nodalAbs x y z 2 := by
    rw [n2, a2]
    exact abs_of_pos (div_pos hPpos hd2)
  have hw3 : |P / nodal x y z 3| = P / nodalAbs x y z 3 := by
    rw [n3, a3]
    exact hneg _ hd3
  have hw4 : |P / nodal x y z 4| = P / nodalAbs x y z 4 := by
    rw [n4, a4]
    exact abs_of_pos (div_pos hPpos hd2)
  have hw5 : |P / nodal x y z 5| = P / nodalAbs x y z 5 := by
    rw [n5, a5]
    exact hneg _ hd1
  have hw6 : |P / nodal x y z 6| = P / nodalAbs x y z 6 := by
    rw [n6, a6]
    exact abs_of_pos (div_pos hPpos hd0)
  refine ⟨σ, x, y, z, hx, hxy, hyz, hσ, hEx, hEy, hEz, fun i => ?_⟩
  rw [← habsρ (σ i), hD i]
  fin_cases i
  exacts [hw0, hw1, hw2, hw3, hw4, hw5, hw6]

/-- **First-site amplitude of a seven-site chain with symmetric spectrum.** Let a path on seven
sites with positive weights `r`, arbitrary real potentials and a spectrum closed under negation
have perfect state transfer between its ends at a real time `T`. Then its eigenvalues are, in
increasing order, `-z, -y, -x, 0, x, y, z` with `0 < x < y < z`, the phases are
`exp (i T x) = -1`, `exp (i T y) = 1`, `exp (i T z) = -1`, and with `P = ∏ r` the first-site
amplitude at every time `τ` is
`P (1/(x²y²z²) + cos(τx)/(x²(y²-x²)(z²-x²)) + cos(τy)/(y²(y²-x²)(z²-y²)) +
cos(τz)/(z²(z²-x²)(z²-y²)))`. -/
theorem symmetric_spectrum_end_amplitude (hr : ∀ j, 0 < r j)
    (hsym : ∀ k, ∃ l, (pathHamiltonian_isHermitian r q).eigenvalues l =
      -(pathHamiltonian_isHermitian r q).eigenvalues k)
    {T : ℝ} (hpst : HasPST (pathHamiltonian r q) T 0 (Fin.last 6)) :
    ∃ (σ : Equiv.Perm (Fin 7)) (x y z : ℝ), 0 < x ∧ x < y ∧ y < z ∧
      (∀ i, (pathHamiltonian_isHermitian r q).eigenvalues (σ i) =
        ![-z, -y, -x, 0, x, y, z] i) ∧
      Complex.exp ((T : ℂ) * I * x) = -1 ∧ Complex.exp ((T : ℂ) * I * y) = 1 ∧
      Complex.exp ((T : ℂ) * I * z) = -1 ∧
      ∀ τ : ℝ, hamiltonianPropagator (pathHamiltonian r q) τ 0 0 =
        (((∏ t, r t) * (1 / (x ^ 2 * y ^ 2 * z ^ 2) +
          Real.cos (τ * x) / (x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2)) +
          Real.cos (τ * y) / (y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)) +
          Real.cos (τ * z) / (z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2))) : ℝ) : ℂ) := by
  obtain ⟨σ, x, y, z, hx, hxy, hyz, hσ, hEx, hEy, hEz, hw⟩ :=
    symmetric_spectrum_weights r q hr hsym hpst
  refine ⟨σ, x, y, z, hx, hxy, hyz, hσ, hEx, hEy, hEz, fun τ => ?_⟩
  have hprop : hamiltonianPropagator (pathHamiltonian r q) τ =
      NormedSpace.exp ((((-τ : ℝ) : ℂ) * I) • pathHamiltonian r q) := by
    have h := hamiltonianPropagator_neg (pathHamiltonian r q) (-τ)
    rwa [neg_neg] at h
  rw [hprop, spectral_exp_apply_self (pathHamiltonian_isHermitian r q), ← Equiv.sum_comp σ]
  exact sum_weight_exp_symmetric (∏ t, r t) x y z τ _ _ hσ hw

/-- **Spectral reduction of a seven-site chain with symmetric spectrum.** Let a path on seven
sites with positive weights, arbitrary real potentials and a spectrum closed under negation have
perfect state transfer between its ends at a time `T > 0`. Then there are natural numbers
`0 < a < b < c`, with `a` and `c` odd and `b` even, such that the eigenvalues are
`(π / T) (-c, -b, -a, 0, a, b, c)`, the first-site amplitude at the time `τ` is a positive
constant times the cosine sum `amplitudeNumerator a b c t`, that is
`(b²-a²)(c²-a²)(c²-b²) + b²c²(c²-b²) cos(a t) + a²c²(c²-a²) cos(b t) + a²b²(b²-a²) cos(c t)`, at
`t = π τ / T`, and the chain has perfect state transfer between its ends at the time `T / g`
for every common divisor `g` of `a`, `b`, `c`. -/
theorem symmetric_spectrum_reduction (hr : ∀ j, 0 < r j)
    (hsym : ∀ k, ∃ l, (pathHamiltonian_isHermitian r q).eigenvalues l =
      -(pathHamiltonian_isHermitian r q).eigenvalues k)
    {T : ℝ} (hT : 0 < T) (hpst : HasPST (pathHamiltonian r q) T 0 (Fin.last 6)) :
    ∃ (a b c : ℕ) (σ : Equiv.Perm (Fin 7)) (κ : ℝ), Odd a ∧ Even b ∧ Odd c ∧ 0 < a ∧ a < b ∧
      b < c ∧ 0 < κ ∧
      (∀ i, (pathHamiltonian_isHermitian r q).eigenvalues (σ i) =
        Real.pi / T * ![-(c : ℝ), -(b : ℝ), -(a : ℝ), 0, (a : ℝ), (b : ℝ), (c : ℝ)] i) ∧
      (∀ τ : ℝ, hamiltonianPropagator (pathHamiltonian r q) τ 0 0 =
        ((κ * amplitudeNumerator a b c (Real.pi * τ / T) : ℝ) : ℂ)) ∧
      ∀ g : ℕ, g ∣ a → g ∣ b → g ∣ c →
        HasPST (pathHamiltonian r q) (T / g) 0 (Fin.last 6) := by
  obtain ⟨σ, x, y, z, hx, hxy, hyz, hσ, hEx, hEy, hEz, hamp⟩ :=
    symmetric_spectrum_end_amplitude r q hr hsym hpst
  have hy : 0 < y := hx.trans hxy
  have hz : 0 < z := hy.trans hyz
  have hTne : T ≠ 0 := hT.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hu : 0 < Real.pi / T := div_pos Real.pi_pos hT
  have hcast : ∀ s : ℝ,
      (Real.pi : ℂ) * I * ((T * s / Real.pi : ℝ) : ℂ) = (T : ℂ) * I * s := by
    intro s
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field
  have hpos : ∀ s : ℝ, 0 < s → 0 < T * s / Real.pi := fun s hs =>
    div_pos (mul_pos hT hs) Real.pi_pos
  obtain ⟨a, ha, hxa⟩ := exists_odd_nat (hpos x hx)
    (exists_int_of_exp_eq_neg_one (by rw [hcast]; exact hEx))
  obtain ⟨b, hb, hyb⟩ := exists_even_nat (hpos y hy)
    (exists_int_of_exp_eq_one (by rw [hcast]; exact hEy))
  obtain ⟨c, hc, hzc⟩ := exists_odd_nat (hpos z hz)
    (exists_int_of_exp_eq_neg_one (by rw [hcast]; exact hEz))
  have hx' : x = Real.pi / T * a := by
    rw [← hxa]
    field
  have hy' : y = Real.pi / T * b := by
    rw [← hyb]
    field
  have hz' : z = Real.pi / T * c := by
    rw [← hzc]
    field
  have hA : (0 : ℝ) < a := by
    have h : Real.pi / T * (0 : ℝ) < Real.pi / T * (a : ℝ) := by
      rw [mul_zero, ← hx']
      exact hx
    exact lt_of_mul_lt_mul_left h hu.le
  have hAB : (a : ℝ) < b := by
    have h : Real.pi / T * (a : ℝ) < Real.pi / T * (b : ℝ) := by
      rw [← hx', ← hy']
      exact hxy
    exact lt_of_mul_lt_mul_left h hu.le
  have hBC : (b : ℝ) < c := by
    have h : Real.pi / T * (b : ℝ) < Real.pi / T * (c : ℝ) := by
      rw [← hy', ← hz']
      exact hyz
    exact lt_of_mul_lt_mul_left h hu.le
  have hB : (0 : ℝ) < b := hA.trans hAB
  have hC : (0 : ℝ) < c := hB.trans hBC
  have hE1 : 0 < (b : ℝ) ^ 2 - (a : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hAB) (add_pos hA hB)]
  have hE2 : 0 < (c : ℝ) ^ 2 - (a : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr (hAB.trans hBC)) (add_pos hA hC)]
  have hE3 : 0 < (c : ℝ) ^ 2 - (b : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hBC) (add_pos hB hC)]
  have hP : 0 < ∏ t, r t := Finset.prod_pos fun t _ => hr t
  have hκ : 0 < (∏ t, r t) * (T / Real.pi) ^ 6 /
      ((a : ℝ) ^ 2 * (b : ℝ) ^ 2 * (c : ℝ) ^ 2 * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) *
        ((c : ℝ) ^ 2 - (a : ℝ) ^ 2) * ((c : ℝ) ^ 2 - (b : ℝ) ^ 2)) :=
    div_pos (mul_pos hP (pow_pos (div_pos hT Real.pi_pos) 6))
      (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (pow_pos hA 2) (pow_pos hB 2))
        (pow_pos hC 2)) hE1) hE2) hE3)
  have hS : ∀ i, (pathHamiltonian_isHermitian r q).eigenvalues (σ i) =
      Real.pi / T * ![-(c : ℝ), -(b : ℝ), -(a : ℝ), 0, (a : ℝ), (b : ℝ), (c : ℝ)] i := by
    have s0 : (pathHamiltonian_isHermitian r q).eigenvalues (σ 0) =
        Real.pi / T * ![-(c : ℝ), -(b : ℝ), -(a : ℝ), 0, (a : ℝ), (b : ℝ), (c : ℝ)] 0 := by
      rw [hσ 0]
      simp only [Matrix.cons_val]
      rw [hz']
      ring
    have s1 : (pathHamiltonian_isHermitian r q).eigenvalues (σ 1) =
        Real.pi / T * ![-(c : ℝ), -(b : ℝ), -(a : ℝ), 0, (a : ℝ), (b : ℝ), (c : ℝ)] 1 := by
      rw [hσ 1]
      simp only [Matrix.cons_val]
      rw [hy']
      ring
    have s2 : (pathHamiltonian_isHermitian r q).eigenvalues (σ 2) =
        Real.pi / T * ![-(c : ℝ), -(b : ℝ), -(a : ℝ), 0, (a : ℝ), (b : ℝ), (c : ℝ)] 2 := by
      rw [hσ 2]
      simp only [Matrix.cons_val]
      rw [hx']
      ring
    have s3 : (pathHamiltonian_isHermitian r q).eigenvalues (σ 3) =
        Real.pi / T * ![-(c : ℝ), -(b : ℝ), -(a : ℝ), 0, (a : ℝ), (b : ℝ), (c : ℝ)] 3 := by
      rw [hσ 3]
      simp only [Matrix.cons_val]
      rw [mul_zero]
    have s4 : (pathHamiltonian_isHermitian r q).eigenvalues (σ 4) =
        Real.pi / T * ![-(c : ℝ), -(b : ℝ), -(a : ℝ), 0, (a : ℝ), (b : ℝ), (c : ℝ)] 4 := by
      rw [hσ 4]
      simp only [Matrix.cons_val]
      exact hx'
    have s5 : (pathHamiltonian_isHermitian r q).eigenvalues (σ 5) =
        Real.pi / T * ![-(c : ℝ), -(b : ℝ), -(a : ℝ), 0, (a : ℝ), (b : ℝ), (c : ℝ)] 5 := by
      rw [hσ 5]
      simp only [Matrix.cons_val]
      exact hy'
    have s6 : (pathHamiltonian_isHermitian r q).eigenvalues (σ 6) =
        Real.pi / T * ![-(c : ℝ), -(b : ℝ), -(a : ℝ), 0, (a : ℝ), (b : ℝ), (c : ℝ)] 6 := by
      rw [hσ 6]
      simp only [Matrix.cons_val]
      exact hz'
    intro i
    fin_cases i
    exacts [s0, s1, s2, s3, s4, s5, s6]
  refine ⟨a, b, c, σ, _, ha, hb, hc, by exact_mod_cast hA, by exact_mod_cast hAB,
    by exact_mod_cast hBC, hκ, hS, fun τ => ?_, fun g hga hgb hgc => ?_⟩
  · rw [hamp τ]
    congr 1
    unfold amplitudeNumerator
    have cx : τ * x = (a : ℝ) * (Real.pi * τ / T) := by
      rw [hx']
      ring
    have cy : τ * y = (b : ℝ) * (Real.pi * τ / T) := by
      rw [hy']
      ring
    have cz : τ * z = (c : ℝ) * (Real.pi * τ / T) := by
      rw [hz']
      ring
    have hxyz : x ^ 2 * y ^ 2 * z ^ 2 =
        (Real.pi / T) ^ 6 * ((a : ℝ) ^ 2 * (b : ℝ) ^ 2 * (c : ℝ) ^ 2) := by
      rw [hx', hy', hz']
      ring
    have hdx : x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2) = (Real.pi / T) ^ 6 *
        ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) * ((c : ℝ) ^ 2 - (a : ℝ) ^ 2)) := by
      rw [hx', hy', hz']
      ring
    have hdy : y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2) = (Real.pi / T) ^ 6 *
        ((b : ℝ) ^ 2 * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) * ((c : ℝ) ^ 2 - (b : ℝ) ^ 2)) := by
      rw [hx', hy', hz']
      ring
    have hdz : z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2) = (Real.pi / T) ^ 6 *
        ((c : ℝ) ^ 2 * ((c : ℝ) ^ 2 - (a : ℝ) ^ 2) * ((c : ℝ) ^ 2 - (b : ℝ) ^ 2)) := by
      rw [hx', hy', hz']
      ring
    rw [cx, cy, cz, hxyz, hdx, hdy, hdz]
    have hAne : (a : ℝ) ≠ 0 := hA.ne'
    have hBne : (b : ℝ) ≠ 0 := hB.ne'
    have hCne : (c : ℝ) ≠ 0 := hC.ne'
    have hE1ne := hE1.ne'
    have hE2ne := hE2.ne'
    have hE3ne := hE3.ne'
    generalize (b : ℝ) ^ 2 - (a : ℝ) ^ 2 = E1 at hE1ne ⊢
    generalize (c : ℝ) ^ 2 - (a : ℝ) ^ 2 = E2 at hE2ne ⊢
    generalize (c : ℝ) ^ 2 - (b : ℝ) ^ 2 = E3 at hE3ne ⊢
    field
  · have hgodd : Odd g := ha.of_dvd_nat hga
    refine hasPST_of_phase_eq (pathHamiltonian_isHermitian r q) 0 (Fin.last 6) (fun k => ?_) hpst
    obtain ⟨i, rfl⟩ := σ.surjective k
    rw [hS i]
    obtain ⟨n, hn, hv⟩ : ∃ n : ℤ, (g : ℤ) ∣ n ∧
        ![-(c : ℝ), -(b : ℝ), -(a : ℝ), 0, (a : ℝ), (b : ℝ), (c : ℝ)] i = n := by
      have hga' : (g : ℤ) ∣ (a : ℤ) := Int.natCast_dvd_natCast.mpr hga
      have hgb' : (g : ℤ) ∣ (b : ℤ) := Int.natCast_dvd_natCast.mpr hgb
      have hgc' : (g : ℤ) ∣ (c : ℤ) := Int.natCast_dvd_natCast.mpr hgc
      fin_cases i
      · exact ⟨-(c : ℤ), (dvd_neg).mpr hgc', by simp⟩
      · exact ⟨-(b : ℤ), (dvd_neg).mpr hgb', by simp⟩
      · exact ⟨-(a : ℤ), (dvd_neg).mpr hga', by simp⟩
      · exact ⟨0, dvd_zero _, by simp⟩
      · exact ⟨(a : ℤ), hga', by simp⟩
      · exact ⟨(b : ℤ), hgb', by simp⟩
      · exact ⟨(c : ℤ), hgc', by simp⟩
    rw [hv]
    exact exp_div_eq hTne hgodd hn

end SevenSites

end D5.S3.Quantum.Dynamics.SymmetricSpectrumEndAmplitude
