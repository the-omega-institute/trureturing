/- GID: D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.claim; result=D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.result; claim=D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.claim
   digest: Fourier truncation, analytic deformations and the real-density isolation assertion. -/

import Mathlib
import D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationJacobian
import D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve

open scoped BigOperators Topology
open scoped Matrix.Norms.Elementwise
noncomputable section

namespace D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationRefutation

/-- The Fourier truncation F_{S,p} has rows S, all columns in ZMod p, and entries
w^(s j), where w = exp(2 pi i / p). -/
def partialFourier (p : ℕ) [NeZero p] (S : Finset (ZMod p)) : Matrix S (ZMod p) ℂ :=
  fun s j => Complex.exp (2 * Real.pi * Complex.I * ((s.1.val * j.val : ℕ) : ℂ) / p)

/-- A partial Hadamard matrix (source Definition 1.1) has unit-modulus entries
and pairwise orthogonal rows. -/
def IsPartialHadamard {m n : Type*} [Fintype n] (H : Matrix m n ℂ) : Prop :=
  (∀ i j, ‖H i j‖ = 1) ∧ ∀ i k, i ≠ k → ∑ j, H i j * star (H k j) = 0

/-- An analytic specialization of source Definition 1.3, with q = exp(i t).
Regularity is `ContDiff ℝ ⊤`, real analyticity (order ω) in the pinned Mathlib.
The global curve passes through H and is partial Hadamard near zero.
Analytic curves are smooth, so the existence of a nontrivial analytic deformation
also refutes the source's smooth isolation conjecture. -/
def IsDeformation {m n : Type*} [Fintype m] [Fintype n] (H : Matrix m n ℂ) (γ : ℝ → Matrix m n ℂ) : Prop :=
  ContDiff ℝ ⊤ γ ∧ γ 0 = H ∧ ∀ᶠ t in 𝓝 (0 : ℝ), IsPartialHadamard (γ t)

/-- Trivial deformation: entrywise multiplication of H by row and column phase factors
    at every parameter, near 0. It contains the source's f_ij(q) = H_ij q^{a_i+b_j}
    (take a_i(t) = t a_i, b_j(t) = t b_j); no regularity is imposed on the phases.
This generalizes the trivial class in source Definition 1.3. Source isolation
implies isolation here: analytic deformations are smooth and the trivial class
is enlarged. Consequently, the negation of `claim` refutes the source conjecture. -/
def IsTrivialDeformation {m n : Type*} (H : Matrix m n ℂ) (γ : ℝ → Matrix m n ℂ) : Prop :=
  ∃ (a : m → ℝ → ℝ) (b : n → ℝ → ℝ), ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i j,
    γ t i j = H i j * Complex.exp (Complex.I * ((a i t + b j t : ℝ) : ℂ))

/-- The analytic specialization of isolation following source Definition 1.3:
every analytic deformation of H is trivial. -/
def IsolatedPartialHadamard {m n : Type*} [Fintype m] [Fintype n] (H : Matrix m n ℂ) : Prop :=
  ∀ γ, IsDeformation H γ → IsTrivialDeformation H γ

/-- The analytic specialization of source Conjecture 1.14 on Fourier truncations. -/
def claim : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ p : ℕ, ∀ hp : p.Prime, ∀ S : Finset (ZMod p),
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (1 - ε) * (p : ℝ) ≤ (S.card : ℝ) → IsolatedPartialHadamard (partialFourier p S)

open BanicaTruncationJacobian BanicaLevelSetCurve

private theorem partial_fourier_eq_stdAddChar (p : ℕ) [NeZero p]
    (S : Finset (ZMod p)) (s : S) (j : ZMod p) :
    partialFourier p S s j = ZMod.stdAddChar (s.1 * j) := by
  have h := ZMod.stdAddChar_coe (N := p) ((s.1.val * j.val : ℕ) : ℤ)
  simpa only [partialFourier, Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
    ZMod.natCast_zmod_val] using h.symm

private theorem star_stdAddChar {p : ℕ} [NeZero p] (x : ZMod p) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  exact (AddChar.map_neg_eq_conj _ _).symm

/-- The prescribed Fourier entries have unit norm and distinct rows are orthogonal. -/
theorem partial_fourier_isPartialHadamard (p : ℕ) [NeZero p]
    (S : Finset (ZMod p)) : IsPartialHadamard (partialFourier p S) := by
  classical
  constructor
  · intro s j
    rw [partial_fourier_eq_stdAddChar, ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  · intro s t hst
    have hne : s.1 - t.1 ≠ 0 := sub_ne_zero.mpr (fun h => hst (Subtype.ext h))
    simp only [partial_fourier_eq_stdAddChar, star_stdAddChar]
    have hterm (j : ZMod p) :
        ZMod.stdAddChar (s.1 * j) * ZMod.stdAddChar (-(t.1 * j)) =
          ZMod.stdAddChar (j * (s.1 - t.1)) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    simp_rw [hterm]
    simpa [hne] using AddChar.sum_mulShift (s.1 - t.1) (ZMod.isPrimitive_stdAddChar p)

private theorem phase_residual_zero_of_partialHadamard
    {m n : Type*} [Fintype m] [Fintype n] [LinearOrder m]
    (H : Matrix m n ℂ) (hH : IsPartialHadamard H) : phaseResidual H 0 = 0 := by
  funext e
  simpa [phaseResidual] using hH.2 e.1.1 e.1.2 (ne_of_lt e.2)

private theorem phase_matrix_isPartialHadamard
    {m n : Type*} [Fintype m] [Fintype n] [LinearOrder m]
    (H : Matrix m n ℂ) (hH : IsPartialHadamard H)
    (θ : m → n → ℝ) (hθ : phaseResidual H θ = 0) :
    IsPartialHadamard (phaseMatrix H θ) := by
  classical
  have hentry (s t : m) (j : n) :
      phaseMatrix H θ s j * star (phaseMatrix H θ t j) =
        H s j * star (H t j) *
          Complex.exp (Complex.I * ((θ s j - θ t j : ℝ) : ℂ)) := by
    simp only [phaseMatrix, star_mul, Complex.star_def, ← Complex.exp_conj,
      map_mul, Complex.conj_I, Complex.conj_ofReal]
    have hexp : Complex.I * ((θ s j - θ t j : ℝ) : ℂ) =
        Complex.I * (θ s j : ℂ) + (-Complex.I) * (θ t j : ℂ) := by
      push_cast
      ring
    rw [hexp, Complex.exp_add]
    ring
  constructor
  · intro s j
    simp [phaseMatrix, norm_mul, hH.1 s j, Complex.norm_exp_I_mul_ofReal]
  · intro s t hst
    by_cases hlt : s < t
    · simp_rw [hentry]
      exact congrFun hθ ⟨(s, t), hlt⟩
    · have hlt' : t < s := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hst)
      have h := congrFun hθ ⟨(t, s), hlt'⟩
      have hz : ∑ j, phaseMatrix H θ t j * star (phaseMatrix H θ s j) = 0 := by
        simp_rw [hentry]
        exact h
      have hs := congrArg star hz
      simpa [star_sum, star_mul, mul_comm] using hs

/-- A regular phase level set with a tangent outside additive row-column phases
contains a deformation that is not trivial. -/
theorem not_isolated_of_regular_tangent
    {m n : Type*} [Fintype m] [Fintype n] [LinearOrder m]
    [Nonempty m] [Nonempty n]
    (H : Matrix m n ℂ) (hH : IsPartialHadamard H)
    (hsurj : Function.Surjective (phaseJacobian H))
    (v : m → n → ℝ) (hv : phaseJacobian H v = 0)
    (hout : v ∉ LinearMap.range (rowColumnMap (m := m) (n := n))) :
    ¬ IsolatedPartialHadamard H := by
  classical
  have hfderiv : fderiv ℝ (phaseResidual H) 0 = phaseJacobian H :=
    (phase_residual_hasFDerivAt_zero H).fderiv
  obtain ⟨c, κ, hκ, hcs, hc0, hcd, hclevel⟩ :=
    analytic_level_set_curve (phaseResidual H) (phase_residual_contDiff H)
      (phase_residual_zero_of_partialHadamard H hH)
      (by simpa only [hfderiv] using hsurj) v
      (by simpa only [hfderiv] using hv)
  let γ : ℝ → Matrix m n ℂ := fun t => phaseMatrix H (c t)
  have hγ : IsDeformation H γ := by
    refine ⟨?_, ?_, Filter.Eventually.of_forall (fun t =>
      phase_matrix_isPartialHadamard H hH (c t) (hclevel t))⟩
    · change ContDiff ℝ ⊤ (fun t => fun s j =>
        H s j * Complex.exp (Complex.I * (c t s j : ℂ)))
      apply contDiff_pi.2
      intro s
      apply contDiff_pi.2
      intro j
      have hcij : ContDiff ℝ ⊤ (fun t => c t s j) :=
        contDiff_pi.mp (contDiff_pi.mp hcs s) j
      exact contDiff_const.mul
        ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hcij)).cexp)
    · funext s j
      simp [γ, phaseMatrix, hc0]
  intro hisolated
  obtain ⟨a, b, hab⟩ := hisolated γ hγ
  let s₀ : m := Classical.choice inferInstance
  let j₀ : n := Classical.choice inferInstance
  have hdcoord (s : m) (j : n) : HasDerivAt (fun t => c t s j) (κ * v s j) 0 := by
    let ev : (m → n → ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj j : (n → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj s : (m → n → ℝ) →L[ℝ] (n → ℝ))
    simpa [ev, Function.comp_def] using ev.hasFDerivAt.comp_hasDerivAt 0 hcd
  have hdphase (s : m) (j : n) :
      HasDerivAt (fun t => Complex.exp (Complex.I * (c t s j : ℂ)))
        (Complex.I * ((κ * v s j : ℝ) : ℂ)) 0 := by
    simpa [hc0] using ((hdcoord s j).ofReal_comp.const_mul Complex.I).cexp
  have hcross (s : m) (j : n) :
      (fun t => Complex.exp (Complex.I * (c t s j : ℂ)) *
        Complex.exp (Complex.I * (c t s₀ j₀ : ℂ))) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => Complex.exp (Complex.I * (c t s j₀ : ℂ)) *
        Complex.exp (Complex.I * (c t s₀ j : ℂ))) := by
    filter_upwards [hab] with t ht
    have he (s : m) (j : n) : Complex.exp (Complex.I * (c t s j : ℂ)) =
        Complex.exp (Complex.I * ((a s t + b j t : ℝ) : ℂ)) := by
      have hnH : H s j ≠ 0 := by
        intro hz
        have hn := hH.1 s j
        simp [hz] at hn
      exact mul_left_cancel₀ hnH (ht s j)
    rw [he s j, he s₀ j₀, he s j₀, he s₀ j, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hscalar (s : m) (j : n) :
      κ * v s j + κ * v s₀ j₀ = κ * v s j₀ + κ * v s₀ j := by
    have hd := ((hdphase s j).mul (hdphase s₀ j₀)).unique
      (((hdphase s j₀).mul (hdphase s₀ j)).congr_of_eventuallyEq (hcross s j))
    simp only [hc0, Pi.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      mul_one, one_mul] at hd
    apply Complex.ofReal_injective
    apply mul_left_cancel₀ Complex.I_ne_zero
    push_cast
    simpa only [mul_add, Complex.ofReal_mul] using hd
  have hmem : κ • v ∈ LinearMap.range (rowColumnMap (m := m) (n := n)) := by
    refine ⟨(fun s => κ * v s j₀ - κ * v s₀ j₀, fun j => κ * v s₀ j), ?_⟩
    ext s j
    change κ * v s j₀ - κ * v s₀ j₀ + κ * v s₀ j = κ * v s j
    linarith [hscalar s j]
  apply hout
  have hh := (LinearMap.range (rowColumnMap (m := m) (n := n))).smul_mem κ⁻¹ hmem
  simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt hκ)] using hh

/-- Removing two rows from a prime Fourier matrix of order at least five leaves
an actual nontrivial analytic deformation. -/
theorem two_row_truncation_not_isolated {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (S : Finset (ZMod p)) (hcard : S.card = p - 2) :
    ¬ IsolatedPartialHadamard (partialFourier p S) := by
  classical
  letI : LinearOrder (ZMod p) := LinearOrder.lift' ZMod.val (ZMod.val_injective p)
  have hproper : S ≠ Finset.univ := by
    intro he
    have h := hcard
    rw [he, Finset.card_univ, ZMod.card] at h
    omega
  have hmatrix : partialFourier p S = fourierMatrix p S := by
    funext s j
    exact partial_fourier_eq_stdAddChar p S s j
  have hdim : 2 * Fintype.card (RowPairs S) + Fintype.card S +
      Fintype.card (ZMod p) < Fintype.card S * Fintype.card (ZMod p) := by
    rw [row_pairs_card_twice]
    have hcs : Fintype.card S = p - 2 := by simpa using hcard
    rw [hcs, ZMod.card]
    have ha : p - 2 + 2 = p := by omega
    have hb : p - 2 - 1 + 1 = p - 2 := by omega
    nlinarith
  have hsurj : Function.Surjective (phaseJacobian (partialFourier p S)) := by
    simpa only [hmatrix] using fourier_jacobian_surjective S hproper
  obtain ⟨v, hv, hout⟩ :=
    phase_jacobian_kernel_nontrivial (partialFourier p S) hsurj hdim
  haveI : Nonempty S := by
    apply Finset.Nonempty.to_subtype
    exact Finset.card_pos.mp (by omega)
  exact not_isolated_of_regular_tangent (partialFourier p S)
    (partial_fourier_isPartialHadamard p S) hsurj v hv hout

private theorem dense_two_row_truncation (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℕ, ∃ hp : p.Prime,
      haveI : NeZero p := ⟨hp.ne_zero⟩
      ∃ S : Finset (ZMod p), 5 ≤ p ∧ S.card = p - 2 ∧
        (1 - ε) * (p : ℝ) ≤ (S.card : ℝ) := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ε)
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (max 5 n)
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hp5 : 5 ≤ p := (le_max_left 5 n).trans hnp
  have hnle : n ≤ p := (le_max_right 5 n).trans hnp
  let S : Finset (ZMod p) := (Finset.univ.erase 0).erase 1
  have hcard : S.card = p - 2 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (by simp), Finset.card_erase_of_mem (by simp),
      Finset.card_univ, ZMod.card]
    omega
  have hcast : (S.card : ℝ) = (p : ℝ) - 2 := by
    rw [hcard, Nat.cast_sub (by omega)]
    norm_num
  have hpε : 2 < ε * (p : ℝ) := by
    have hnp' : (n : ℝ) ≤ p := by exact_mod_cast hnle
    have hdiv : 2 / ε < (p : ℝ) := lt_of_lt_of_le hn hnp'
    have := (div_lt_iff₀ hε).1 hdiv
    nlinarith
  refine ⟨p, hp, S, hp5, hcard, ?_⟩
  rw [hcast]
  nlinarith

/-- No positive real density margin forces isolation of all prime Fourier truncations. -/
theorem result : ¬ claim := by
  rintro ⟨ε, hε, hall⟩
  obtain ⟨p, hp, S, hp5, hcard, hbound⟩ := dense_two_row_truncation ε hε
  letI : Fact p.Prime := ⟨hp⟩
  exact two_row_truncation_not_isolated hp5 S hcard (hall p hp S hbound)

end D5.S3.Quantum.Tomography.Hadamard.BanicaTruncationRefutation
