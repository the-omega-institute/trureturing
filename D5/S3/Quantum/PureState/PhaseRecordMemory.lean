/- GID: D5/S3/Quantum/PureState/PhaseRecordMemory
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/PhaseRecordMemory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact memory threshold and finite CPTP decoding bounds for flat phase records. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.PureState.JointRecordTransport
import D5.S3.Quantum.Recovery.KrausCompletion
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite-memory penalty for flat orthogonal phase records

The diagonal optimality certificate is from `JointRecordDecoding`. Subtracting a common
lower bound from the amplitudes decomposes the strengthened slack into a residual diagonal
certificate and a positive diagonal matrix compressed to the complement of the phase row.
-/

namespace PhaseRecordMemory

noncomputable section

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open JointRecordDecoding
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Subentropy.GuessingProbability

variable {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]

/-- The diagonal dual before averaging over the uniform prior. -/
def phaseDual (t : ι → ℝ) : Matrix ι ι ℂ :=
  diagonal fun i => (((∑ l, t l) * t i : ℝ) : ℂ)

omit [DecidableEq ι] in
private theorem phaseBasis_scale_sq :
    ((Real.sqrt (Fintype.card ι))⁻¹ : ℝ) ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by positivity)]

omit [DecidableEq ι] in
private theorem phaseEffect_entry (u : ι → ι → ℂ) (j i l : ι) :
    phaseEffect u j i l = (↑((Fintype.card ι : ℝ)⁻¹) : ℂ) * u j i * star (u j l) := by
  simp only [phaseEffect, rankOneDensity, vecMulVec_apply, Pi.star_apply, phaseBasis,
    star_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← phaseBasis_scale_sq (ι := ι), Complex.ofReal_pow]
  ring

omit [DecidableEq ι] in
private theorem phaseBasis_norm_entry (u : ι → ι → ℂ) (j i : ι)
    (hu : ‖u j i‖ = 1) : star (phaseBasis u j i) * phaseBasis u j i =
      (↑((Fintype.card ι : ℝ)⁻¹) : ℂ) := by
  have h := phaseEffect_entry u j i i
  have hunit : star (u j i) * u j i = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hu]
    norm_num
  change phaseBasis u j i * star (phaseBasis u j i) = _ at h
  rw [mul_comm (phaseBasis u j i), mul_assoc, mul_comm (u j i), hunit, mul_one] at h
  exact h

omit [DecidableEq ι] in
theorem phaseBasis_norm [Nonempty ι] (u : ι → ι → ℂ) (j : ι)
    (hu : ∀ i, ‖u j i‖ = 1) : star (phaseBasis u j) ⬝ᵥ phaseBasis u j = 1 := by
  simp only [dotProduct, Pi.star_apply, phaseBasis_norm_entry u j _ (hu _),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card ι : ℂ) ≠ 0)

private theorem phaseEffect_diagonal_mul [Nonempty ι] (u : ι → ι → ℂ) (j : ι)
    (hu : ∀ i, ‖u j i‖ = 1) (r : ι → ℝ) :
    phaseEffect u j * diagonal (fun i => (r i : ℂ)) * phaseEffect u j =
      (↑((Fintype.card ι : ℝ)⁻¹ * ∑ i, r i) : ℂ) • phaseEffect u j := by
  rw [phaseEffect, (pure_state_handshake _ (phaseBasis_norm u j hu) _).2.1]
  congr 1
  simp only [dotProduct, Pi.star_apply, mulVec_diagonal, Complex.ofReal_mul, Complex.ofReal_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_left_comm, phaseBasis_norm_entry u j i (hu i),
    Complex.ofReal_inv, Complex.ofReal_natCast, mul_comm]

/-- The unscaled phase dual slack dominates `S m` times the complementary projection.
Here `m` may be any nonnegative lower bound for the amplitudes. -/
theorem phaseDual_gap [Nonempty ι] (u : ι → ι → ℂ) (t : ι → ℝ) (m : ℝ)
    (hm : 0 ≤ m) (hmt : ∀ i, m ≤ t i) (j : ι) (hu : ∀ i, ‖u j i‖ = 1) :
    (phaseDual t - rankOneDensity (phaseVector u t j) -
      (↑((∑ i, t i) * m) : ℂ) • (1 - phaseEffect u j)).PosSemidef := by
  let r : ι → ℝ := fun i => t i - m
  let A : Matrix ι ι ℂ := diagonal fun i => (r i : ℂ)
  let P := phaseEffect u j
  let Q := 1 - P
  have hr (i : ι) : 0 ≤ r i := sub_nonneg.mpr (hmt i)
  have hA : A.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr
    (fun i => by simpa [Complex.nonneg_iff] using hr i)
  have hQ : Qᴴ = Q := (Matrix.isHermitian_one.sub (phaseEffect_posSemidef u j).isHermitian)
  have hsum : (∑ i, t i) = (∑ i, r i) + (Fintype.card ι : ℝ) * m := by
    simp [r, Finset.sum_sub_distrib, nsmul_eq_mul]
  have hcompress : Q * A * Q =
      A - P * A - A * P + (↑((Fintype.card ι : ℝ)⁻¹ * ∑ i, r i) : ℂ) • P := by
    dsimp only [Q]
    rw [sub_mul, one_mul, sub_mul, mul_sub, mul_one, mul_sub, mul_one,
      phaseEffect_diagonal_mul u j hu r]
    abel
  have hdecomp : phaseDual t - rankOneDensity (phaseVector u t j) -
      (↑((∑ i, t i) * m) : ℂ) • Q =
      (phaseDual r - rankOneDensity (phaseVector u r j)) +
        (↑((Fintype.card ι : ℝ) * m) : ℂ) • (Q * A * Q) := by
    rw [hcompress]
    ext i l
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      phaseDual, rankOneDensity, vecMulVec_apply, Pi.star_apply, phaseVector,
      star_mul, Complex.star_def, Complex.conj_ofReal, mul_diagonal, diagonal_mul, A, Q, P,
      phaseEffect_entry, hsum, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_inv,
      Complex.ofReal_natCast, Matrix.diagonal_apply, Matrix.one_apply]
    have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have ht (i : ι) : (t i : ℂ) = (r i : ℂ) + (m : ℂ) := by simp [r]
    rw [ht i, ht l]
    by_cases hil : i = l
    · subst l
      simp only [ite_true]
      field_simp
      ring
    · simp only [ite_eq_right hil]
      field_simp
      ring
  rw [hdecomp]
  refine (diagonal_sub_rankOne_posSemidef r hr (u j) hu).add ?_
  apply Matrix.PosSemidef.smul
  · simpa only [hQ] using hA.conjTranspose_mul_mul_same Q
  · exact Complex.nonneg_iff.mpr ⟨mul_nonneg (by positivity) hm, rfl⟩

/-- Matrix coordinates of the canonical CPTP encoder. -/
def channelMatrix (Φ : QuantumChannel ι μ) : MatrixMap ι μ ℂ :=
  (CStarMatrix.ofMatrixₗ.symm (R := ℂ)).toLinearMap.comp
    (Φ.toCompletelyPositiveMap.toLinearMap.comp (CStarMatrix.ofMatrixₗ (R := ℂ)).toLinearMap)

/-- The Heisenberg pullback under a canonical CPTP encoder, using the adjoint Kraus operators. -/
def pullEffect (Φ : QuantumChannel ι μ) : MatrixMap μ ι ℂ :=
  let K := (krausRepresentation Φ.toCompletelyPositiveMap).1
  MatrixMap.of_kraus (fun r => (K r)ᴴ) (fun r => (K r)ᴴ)

theorem pullEffect_trace (Φ : QuantumChannel ι μ) (A : Matrix ι ι ℂ) (D : Matrix μ μ ℂ) :
    trace (pullEffect Φ D * A) = trace (D * channelMatrix Φ A) := by
  let K := krausRepresentation Φ.toCompletelyPositiveMap
  have hA : channelMatrix Φ A = ∑ r, K.1 r * A * (K.1 r)ᴴ := K.2 A
  rw [hA]
  simp only [pullEffect, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, conjTranspose_conjTranspose, Matrix.sum_mul, Matrix.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  change trace ((K.1 r)ᴴ * D * K.1 r * A) = trace (D * (K.1 r * A * (K.1 r)ᴴ))
  rw [Matrix.mul_assoc ((K.1 r)ᴴ * D), ← Matrix.mul_assoc D (K.1 r * A),
    Matrix.trace_mul_cycle D (K.1 r * A)]

theorem pullEffect_posSemidef (Φ : QuantumChannel ι μ) {D : Matrix μ μ ℂ}
    (hD : D.PosSemidef) : (pullEffect Φ D).PosSemidef := by
  simp only [pullEffect, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, conjTranspose_conjTranspose]
  exact Matrix.posSemidef_sum _ fun _ _ => hD.conjTranspose_mul_mul_same _

theorem pullEffect_one (Φ : QuantumChannel ι μ) : pullEffect Φ 1 = 1 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro A
  rw [pullEffect_trace, one_mul, one_mul]
  exact Φ.trace_preserving (CStarMatrix.ofMatrix A)

theorem sum_pullEffect {X : Type*} [Fintype X] (Φ : QuantumChannel ι μ)
    (D : X → Matrix μ μ ℂ) (hsum : ∑ j, D j = 1) :
    ∑ j, pullEffect Φ (D j) = 1 := by
  rw [← map_sum, hsum, pullEffect_one]

private theorem density_le_one (ρ : DensityState μ) :
    CStarMatrix.ofMatrix.symm ρ.1 ≤ 1 := by
  let A := CStarMatrix.ofMatrix.symm ρ.1
  have hA : A.PosSemidef := density_posSemidef ρ
  let e := hA.isHermitian.eigenvalues
  have hsum : ∑ i, e i = 1 := by
    have h := hA.isHermitian.trace_eq_sum_eigenvalues (𝕜 := ℂ)
    change ρ.1.trace = ∑ i, (e i : ℂ) at h
    simpa only [ρ.trace_eq_one, Complex.re_sum, Complex.ofReal_re, Complex.one_re] using
      (congrArg Complex.re h).symm
  have he (i : μ) : e i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  let U := hA.isHermitian.eigenvectorUnitary
  let B : Matrix μ μ ℂ := diagonal fun i => (e i : ℂ)
  have hB : B ≤ 1 := by
    apply Matrix.le_iff.mpr
    have hid : 1 - B = diagonal (fun i => ((1 - e i : ℝ) : ℂ)) := by
      change 1 - diagonal (fun i => (e i : ℂ)) = _
      rw [← diagonal_one, diagonal_sub]
      congr 1
      funext i
      simp
    rw [hid, Matrix.posSemidef_diagonal_iff]
    intro i
    exact Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr (he i), rfl⟩
  have hspectral : A = Unitary.conjStarAlgAut ℂ _ U B := hA.isHermitian.spectral_theorem
  change A ≤ 1
  apply Matrix.le_iff.mpr
  rw [hspectral, ← map_one (Unitary.conjStarAlgAut ℂ _ U), ← map_sub]
  exact (map_nonneg (Unitary.conjStarAlgAut ℂ _ U) (Matrix.le_iff.mp hB).nonneg).posSemidef

private theorem trace_pair_le_trace (D : Matrix μ μ ℂ) (hD : D.PosSemidef) (ρ : DensityState μ) :
    (trace (D * CStarMatrix.ofMatrix.symm ρ.1)).re ≤ (trace D).re := by
  have h := RHLinalg.trace_mul_nonneg_of_posSemidef hD (Matrix.le_iff.mp (density_le_one ρ))
  change 0 ≤ (trace (D * (1 - CStarMatrix.ofMatrix.symm ρ.1))).re at h
  simpa only [mul_sub, mul_one, trace_sub, Complex.sub_re, sub_nonneg] using h

private theorem sum_pair {X : Type*} [Fintype X] (E : X → Matrix ι ι ℂ)
    (hsE : ∑ j, E j = 1) (A : Matrix ι ι ℂ) :
    (∑ j, (trace (E j * A)).re) = (trace A).re := by
  rw [← Complex.re_sum, ← trace_sum, ← Matrix.sum_mul, hsE, one_mul]

private theorem sum_trace {X : Type*} [Fintype X] (D : X → Matrix μ μ ℂ)
    (hsD : ∑ j, D j = 1) : (∑ j, (trace (D j)).re) = Fintype.card μ := by
  rw [← Complex.re_sum, ← trace_sum, hsD, trace_one]
  simp

/-- The normalized phase ensemble in the existing guessing-probability representation. -/
def phaseState (u : ι → ι → ℂ) (t : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1) (ht : ∑ i, t i ^ 2 = 1) (j : ι) : DensityState ι :=
  pureState (phaseVector u t j) (phaseVector_norm u t hu ht j)

/-- Uniform guessing through a genuine finite CPTP encoder obeys both dimension bounds.
The comparison uses the scalar value of the full-carrier diagonal dual. For a nonnegative
profile, take `m` to be its finite minimum for the strongest bound of this form when `M ≤ N`. -/
theorem phase_success_le [Nonempty ι] (u : ι → ι → ℂ) (t : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1) (ht : ∑ i, t i ^ 2 = 1)
    (m : ℝ) (hm : 0 ≤ m) (hmt : ∀ i, m ≤ t i)
    (Φ : QuantumChannel ι μ) (D : ι → Matrix μ μ ℂ)
    (hD : ∀ j, (D j).PosSemidef) (hsD : ∑ j, D j = 1) :
    successProbability (uniformPrior ι) (fun j => Φ.mapState (phaseState u t hu ht j)) D ≤
      min ((Fintype.card μ : ℝ) / Fintype.card ι)
        ((Fintype.card ι : ℝ)⁻¹ * (∑ i, t i) ^ 2 -
          (1 - (Fintype.card μ : ℝ) / Fintype.card ι) * ((∑ i, t i) * m)) := by
  let E := fun j => pullEffect Φ (D j)
  have hsE : ∑ j, E j = 1 := sum_pullEffect Φ D hsD
  let ψ := fun j => Φ.mapState (phaseState u t hu ht j)
  let w := fun j => Φ.mapState (pureState (phaseBasis u j) (phaseBasis_norm u j (hu j)))
  let g := successProbability (uniformPrior ι) ψ D
  let k := (∑ i, t i) * m
  have hk : 0 ≤ k := mul_nonneg (Finset.sum_nonneg fun i _ => hm.trans (hmt i)) hm
  have hp (j : ι) :
      trace (E j * rankOneDensity (phaseVector u t j)) =
        trace (D j * CStarMatrix.ofMatrix.symm (ψ j).1) :=
    pullEffect_trace Φ _ _
  have hw (j : ι) : trace (E j * phaseEffect u j) =
        trace (D j * CStarMatrix.ofMatrix.symm (w j).1) :=
    pullEffect_trace Φ _ _
  have hmem (ρ : ι → DensityState μ) :
      ∑ j, (trace (D j * CStarMatrix.ofMatrix.symm (ρ j).1)).re ≤ Fintype.card μ := by
    rw [← sum_trace D hsD]
    exact Finset.sum_le_sum fun j _ => trace_pair_le_trace (D j) (hD j) (ρ j)
  have hpoint (j : ι) :
      k * ((trace (E j)).re - (trace (D j * CStarMatrix.ofMatrix.symm (w j).1)).re) ≤
        (trace (E j * phaseDual t)).re -
          (trace (D j * CStarMatrix.ofMatrix.symm (ψ j).1)).re := by
    have h := RHLinalg.trace_mul_nonneg_of_posSemidef (pullEffect_posSemidef Φ (hD j))
      (phaseDual_gap u t m hm hmt j (hu j))
    change 0 ≤ (trace (E j * _)).re at h
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, trace_sub, trace_smul,
      Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hp, hw, ← show k = (∑ i, t i) * m from rfl] at h
    linarith
  have htrace : (trace (phaseDual t)).re = (∑ i, t i) ^ 2 := by
    simp [phaseDual, ← Finset.mul_sum, pow_two]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun j _ => hpoint j)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_pair E hsE, htrace] at hsum
  have hsumE : (∑ j, (trace (E j)).re) = Fintype.card ι := sum_trace E hsE
  rw [hsumE] at hsum
  have hgap := (mul_le_mul_of_nonneg_left (sub_le_sub_left (hmem w)
    (Fintype.card ι : ℝ)) hk).trans hsum
  change g ≤ _
  have hg : g = (Fintype.card ι : ℝ)⁻¹ *
      ∑ j, (trace (D j * CStarMatrix.ofMatrix.symm (ψ j).1)).re := by
    simp only [g, successProbability, uniformPrior, Finset.mul_sum]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have hnin : 0 ≤ (Fintype.card ι : ℝ)⁻¹ := by positivity
  apply le_min
  · rw [hg, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hmem ψ) hnin
  · rw [hg, div_eq_inv_mul]
    have h := mul_le_mul_of_nonneg_left hgap hnin
    have hc : (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) - Fintype.card μ) =
        1 - (Fintype.card ι : ℝ)⁻¹ * Fintype.card μ := by
      rw [mul_sub, inv_mul_cancel₀ hn]
    rw [mul_left_comm _ k, hc, mul_sub] at h
    change _ ≤ _ - _ * k
    linarith

/-- An isometry gives a single-Kraus trace-preserving channel. -/
theorem isometryChannel (V : Matrix μ ι ℂ) (hV : Vᴴ * V = 1) :
    ∃ Φ : QuantumChannel ι μ, ∀ A, channelMatrix Φ A = V * A * Vᴴ := by
  obtain ⟨Φ, hΦ⟩ := finite_kraus_quantum_channel (fun _ : Unit => V) (by simpa using hV)
  refine ⟨Φ, fun A => ?_⟩
  change CStarMatrix.ofMatrix.symm
    (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix A)) = _
  simpa using hΦ A

/-- An isometric inclusion induces a genuine CPTP memory channel. -/
theorem exists_isometryChannel (h : Fintype.card ι ≤ Fintype.card μ) :
    ∃ (V : Matrix μ ι ℂ) (Φ : QuantumChannel ι μ),
      Vᴴ * V = 1 ∧ ∀ A, channelMatrix Φ A = V * A * Vᴴ := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le h
  let V : Matrix μ ι ℂ := Matrix.of fun a i => if a = e i then 1 else 0
  have hV : Vᴴ * V = 1 := by
    ext i j
    simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, apply_ite,
      star_one, star_zero]
    rw [Finset.sum_eq_single (e i)]
    · simp [Matrix.one_apply, e.injective.eq_iff]
    · intro a _ ha
      simp [ha]
    · simp
  obtain ⟨Φ, hΦ⟩ := isometryChannel V hV
  exact ⟨V, Φ, hV, hΦ⟩

/-- Positive flat phase profiles retain the full-carrier optimum through a finite memory
exactly when the memory has at least the carrier dimension. -/
theorem phase_optimum_attainable_iff [Nonempty ι] (u : ι → ι → ℂ) (t : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0)
    (ht : ∑ i, t i ^ 2 = 1) (htpos : ∀ i, 0 < t i) :
    (∃ Φ : QuantumChannel ι μ,
      pGuess (uniformPrior ι) (phaseState u t hu ht) ∈
        successProbabilitySet (uniformPrior ι) (fun j => Φ.mapState (phaseState u t hu ht j))) ↔
      Fintype.card ι ≤ Fintype.card μ := by
  have hopt := isGreatest_phase u t hu horth (fun i => (htpos i).le) ht
  change IsGreatest (successProbabilitySet (uniformPrior ι) (phaseState u t hu ht))
    ((Fintype.card ι : ℝ)⁻¹ * (∑ i, t i) ^ 2) at hopt
  rw [pGuess, hopt.csSup_eq]
  constructor
  · rintro ⟨Φ, D, hD, hsD, hsuccess⟩
    obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ t Finset.univ_nonempty
    have h := (phase_success_le u t hu ht (t i) (htpos i).le
      (fun j => hi j (Finset.mem_univ j)) Φ D hD hsD).trans (min_le_right _ _)
    rw [← hsuccess] at h
    by_contra! hdim
    have hratio : (Fintype.card μ : ℝ) / Fintype.card ι < 1 :=
      (div_lt_one (by positivity)).mpr (by exact_mod_cast hdim)
    have hS : 0 < ∑ j, t j := Finset.sum_pos (fun j _ => htpos j) Finset.univ_nonempty
    linarith [mul_pos (sub_pos.mpr hratio) (mul_pos hS (htpos i))]
  · intro hdim
    obtain ⟨V, Φ, hV, hΦ⟩ := exists_isometryChannel hdim
    refine ⟨Φ, ?_⟩
    rw [success_set_partialIsometry (uniformPrior ι) (phaseState u t hu ht)
      (fun j => Φ.mapState (phaseState u t hu ht j)) V (by rw [hV, Matrix.mul_one])
      (fun _ => by rw [hV, one_mul]) (fun j => hΦ _)]
    exact hopt.1

section IsometricTransport

variable {A : Type*} [Fintype A] [DecidableEq A]

open D5.S3.Quantum.Recovery.KrausCompletion

/-- Compression to an isometric subspace, with a trace-preserving reset on its complement. -/
theorem isometryLeftInverse [Nonempty ι] (V : Matrix A ι ℂ) (hV : Vᴴ * V = 1) :
    ∃ Ψ : QuantumChannel A ι, ∀ R : Matrix ι ι ℂ,
      channelMatrix Ψ (V * R * Vᴴ) = R := by
  let P := V * Vᴴ
  have hP : Pᴴ = P := by simp [P, conjTranspose_mul]
  have hPP : P * P = P := by
    simp only [P, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
  have hPV : P * V = V := by
    dsimp only [P]
    rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  obtain ⟨Ψ, hΨ⟩ := complete_quantum_channel (fun _ : Unit => Vᴴ) P
    (Classical.choice ‹Nonempty ι›) hP hPP (by simp [P])
  refine ⟨Ψ, fun R => ?_⟩
  have hzero : (1 - P) * (V * R * Vᴴ) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hPV,
      sub_self, Matrix.zero_mul, Matrix.zero_mul]
  change CStarMatrix.ofMatrix.symm
    (Ψ.toCompletelyPositiveMap (CStarMatrix.ofMatrix (V * R * Vᴴ))) = R
  rw [hΨ, hzero, trace_zero, zero_smul, add_zero]
  simp only [Fintype.sum_unique, conjTranspose_conjTranspose]
  calc
    Vᴴ * (V * R * Vᴴ) * V = (Vᴴ * V) * R * (Vᴴ * V) := by
      simp only [Matrix.mul_assoc]
    _ = R := by simp [hV]

/-- Equality in matrix coordinates determines the channel output state. -/
theorem state_eq_of_channelMatrix (Φ : QuantumChannel ι A) (ρ : DensityState ι)
    (σ : DensityState A)
    (h : channelMatrix Φ (CStarMatrix.ofMatrix.symm ρ.1) = CStarMatrix.ofMatrix.symm σ.1) :
    Φ.mapState ρ = σ := by
  apply Subtype.ext
  exact CStarMatrix.ofMatrix.symm.injective h

/-- Transport along an isometry preserves attainable success values through a CPTP memory. -/
theorem isometric_memory_attainment {X : Type*} [Fintype X] [Nonempty X] [Nonempty ι]
    (p : X → ℝ) (ρ : X → DensityState ι) (σ : X → DensityState A) (V : Matrix A ι ℂ)
    (hV : Vᴴ * V = 1) (hstate : ∀ j, CStarMatrix.ofMatrix.symm (σ j).1 =
      V * CStarMatrix.ofMatrix.symm (ρ j).1 * Vᴴ) (g : ℝ) :
    (∃ Φ : QuantumChannel A μ, g ∈ successProbabilitySet p (fun j => Φ.mapState (σ j))) ↔
      ∃ Φ : QuantumChannel ι μ, g ∈ successProbabilitySet p (fun j => Φ.mapState (ρ j)) := by
  constructor
  · rintro ⟨Φ, hΦ⟩
    obtain ⟨Ω, hΩ⟩ := isometryChannel V hV
    have hmap (j : X) : Ω.mapState (ρ j) = σ j :=
      state_eq_of_channelMatrix Ω _ _ ((hΩ _).trans (hstate j).symm)
    exact ⟨Φ.comp Ω, by simpa only [QuantumChannel.comp_mapState, hmap] using hΦ⟩
  · rintro ⟨Φ, hΦ⟩
    obtain ⟨Ω, hΩ⟩ := isometryLeftInverse V hV
    have hmap (j : X) : Ω.mapState (σ j) = ρ j := by
      apply state_eq_of_channelMatrix
      rw [hstate j, hΩ]
    exact ⟨Φ.comp Ω, by simpa only [QuantumChannel.comp_mapState, hmap] using hΦ⟩

end IsometricTransport

omit [Fintype μ] in
private theorem rankOne_single (a : μ) :
    rankOneDensity (Pi.single a (1 : ℂ)) = Matrix.single a a 1 := by
  ext i j
  by_cases hi : a = i <;> by_cases hj : a = j <;>
    simp [rankOneDensity, Matrix.single, vecMulVec_apply, Pi.single_apply, hi, hj, Ne.symm]
  all_goals
    by_cases h : i = j
    · simp only [ite_eq_left h, ite_eq_left h.symm]
    · simp only [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- Uniform orthonormal phase records attain the dimension bound by retaining one
label per memory basis state. The complement reset makes the encoder trace preserving. -/
theorem orthogonal_phase_success_attains_dimension [Nonempty ι] [Nonempty μ]
    (u : ι → ι → ℂ) (hu : ∀ j i, ‖u j i‖ = 1)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0)
    (hdim : Fintype.card μ ≤ Fintype.card ι) :
    ∃ Φ : QuantumChannel ι μ,
      ((Fintype.card μ : ℝ) / Fintype.card ι) ∈ successProbabilitySet (uniformPrior ι)
        (fun j => Φ.mapState (pureState (phaseBasis u j) (phaseBasis_norm u j (hu j)))) := by
  obtain ⟨e : μ ↪ ι⟩ := Function.Embedding.nonempty_of_card_le hdim
  let W : Matrix ι ι ℂ := Matrix.of fun a j => phaseBasis u j a
  have hW : W * Wᴴ = 1 := by
    ext a b
    have h := congrArg (fun M : Matrix ι ι ℂ => M a b) (sum_phaseEffect u horth)
    simpa only [W, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.sum_apply, phaseEffect, rankOneDensity, vecMulVec_apply, Pi.star_apply] using h
  have hW' : Wᴴ * W = 1 := mul_eq_one_symm hW
  let V : Matrix ι μ ℂ := W.submatrix id e
  have hV : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id, hW',
      submatrix_one_embedding]
  obtain ⟨Φ, hΦ⟩ := isometryLeftInverse V hV
  let ρ := fun j => Φ.mapState (pureState (phaseBasis u j) (phaseBasis_norm u j (hu j)))
  let D : ι → Matrix μ μ ℂ := fun j =>
    ∑ a, if e a = j then Matrix.single a a 1 else 0
  have hD (j : ι) : (D j).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro a _
    split_ifs
    · rw [← rankOne_single]
      exact Matrix.posSemidef_vecMulVec_self_star _
    · exact Matrix.PosSemidef.zero
  have hsD : ∑ j, D j = 1 := by
    dsimp only [D]
    rw [Finset.sum_comm]
    simp [Matrix.sum_single_one]
  have hDself (a : μ) : D (e a) = Matrix.single a a 1 := by
    simp [D, e.injective.eq_iff]
  have hρself (a : μ) : CStarMatrix.ofMatrix.symm (ρ (e a)).1 = Matrix.single a a 1 := by
    change channelMatrix Φ (rankOneDensity (phaseBasis u (e a))) = _
    have hcol : V *ᵥ Pi.single a 1 = phaseBasis u (e a) := by
      rw [Matrix.mulVec_single_one]
      rfl
    have hshift : V * Matrix.single a a (1 : ℂ) * Vᴴ = rankOneDensity (phaseBasis u (e a)) := by
      rw [← rankOne_single, ← hcol]
      simp only [rankOneDensity, mul_vecMulVec, vecMulVec_mul, ← star_mulVec]
    rw [← hshift, hΦ]
  refine ⟨Φ, D, hD, hsD, ?_⟩
  unfold successProbability uniformPrior
  rw [← Finset.mul_sum, div_eq_inv_mul]
  congr 1
  symm
  apply le_antisymm
  · rw [← sum_trace D hsD]
    exact Finset.sum_le_sum fun j _ => trace_pair_le_trace (D j) (hD j) (ρ j)
  · let f := fun j => (trace (D j * CStarMatrix.ofMatrix.symm (ρ j).1)).re
    have ha (a : μ) : f (e a) = 1 := by
      dsimp only [f]
      rw [hDself, hρself, Matrix.single_mul_single_same, mul_one, trace_single_eq_same]
      norm_num
    have hsum : (∑ j ∈ Finset.univ.map e, f j) = Fintype.card μ := by
      rw [Finset.sum_map]
      simp [ha]
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => RHLinalg.trace_mul_nonneg_of_posSemidef (hD j) (density_posSemidef (ρ j)))

end

end PhaseRecordMemory
