/- GID: D5/S3/Quantum/Decoherence/FiniteShiftedRecordChannel
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/FiniteShiftedRecordChannel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Concrete finite shifted records realize the coefficient coherence channel. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Decoherence.EnvironmentMarginalChannel
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Int.Interval

/- Source: QUANTUM-REALITY, finite coherence realization (definition74.1 and
   theorem74.1). Source inspection and echo preceded the ordered D5, pinned
   Mathlib and upstream searches. The arbitrary-record marginal and Kraus
   CP/TP proofs are reused through their canonical owners.
   This proves one finite isometric realization only. It does not assert
   conservation for a specified Hamiltonian, spatial locality, zero operation
   cost, or universality over reference devices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Decoherence.FiniteShiftedRecordChannel

private theorem label_bound {ι : Type*} [Fintype ι] (q : ι → ℤ) (i : ι) :
    -(↑(∑ j, (q j).natAbs) : ℤ) ≤ q i ∧ q i ≤ (↑(∑ j, (q j).natAbs) : ℤ) := by
  classical
  have hi : (q i).natAbs ≤ ∑ j, (q j).natAbs :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (q j).natAbs) (Finset.mem_univ i)
  have hup := Int.le_natAbs (a := q i)
  have hlo := Int.le_natAbs (a := -q i)
  simp only [Int.natAbs_neg] at hlo
  omega

private theorem coordinate_interval (N Q : ℕ) :
    Set.range (fun a : Fin (N + 2 * Q + 1) => (a.val : ℤ) - (Q : ℤ)) =
      (↑(Finset.Icc (-(Q : ℤ)) ((N : ℤ) + (Q : ℤ))) : Set ℤ) ∧
    Function.Injective (fun a : Fin (N + 2 * Q + 1) => (a.val : ℤ) - (Q : ℤ)) := by
  constructor
  · ext m
    simp only [Set.mem_range, Finset.mem_coe, Finset.mem_Icc]
    constructor
    · rintro ⟨a, rfl⟩
      have := a.isLt
      omega
    · intro hm
      refine ⟨⟨(m + (Q : ℤ)).toNat, ?_⟩, ?_⟩
      · omega
      · dsimp only
        omega
  · intro a b h
    dsimp only at h
    apply Fin.ext
    omega

private theorem shifted_sum_reindex
    {ι A : Type*} [Fintype ι] [AddCommMonoid A]
    (N : ℕ) (q : ι → ℤ) (i : ι) (f : ℤ → A)
    (hf : ∀ n : ℤ, n < 0 ∨ (N : ℤ) < n → f n = 0) :
    let Q : ℕ := ∑ j : ι, (q j).natAbs
    (∑ a : Fin (N + 2 * Q + 1), f ((a.val : ℤ) - (Q : ℤ) + q i)) =
      ∑ n ∈ Finset.Icc (0 : ℤ) (N : ℤ), f n := by
  classical
  dsimp only
  let Q : ℕ := ∑ j : ι, (q j).natAbs
  have hq := label_bound q i
  change -(Q : ℤ) ≤ q i ∧ q i ≤ (Q : ℤ) at hq
  refine Finset.sum_bij_ne_zero (fun a _ _ => (a.val : ℤ) - (Q : ℤ) + q i)
    ?_ ?_ ?_ (fun _ _ _ => rfl)
  · intro a ha hn
    apply Finset.mem_Icc.mpr
    by_contra! h
    exact hn (hf _ (by omega))
  · intro a ha hna b hb hnb hab
    apply Fin.ext
    omega
  · intro n hn hfn
    have hn' := Finset.mem_Icc.mp hn
    let a : Fin (N + 2 * Q + 1) := ⟨(n + (Q : ℤ) - q i).toNat, by omega⟩
    have heq : (a.val : ℤ) - (Q : ℤ) + q i = n := by
      dsimp [a]
      omega
    refine ⟨a, Finset.mem_univ a, ?_, heq⟩
    change f ((a.val : ℤ) - (Q : ℤ) + q i) ≠ 0
    rwa [heq]

private theorem coherenceKernel_eq_tsum
    (N : ℕ) (c : ℤ → ℂ)
    (hsupport : ∀ n : ℤ, n < 0 ∨ (N : ℤ) < n → c n = 0) (ell : ℤ) :
    (∑ n ∈ Finset.Icc (0 : ℤ) (N : ℤ), c (n + ell) * star (c n)) =
      ∑' n : ℤ, c (n + ell) * star (c n) := by
  symm
  apply tsum_eq_sum
  intro n hn
  have hc : c n = 0 := hsupport n (by simpa only [Finset.mem_Icc, not_and_or,
    not_le] using hn)
  simp [hc]

/-- Zero-extended normalized coefficients give concrete records on a derived
finite integer interval, with the source's signed conjugate overlap. -/
theorem shifted_coefficient_records
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (c : ℤ → ℂ) (q : ι → ℤ)
    (hsupport : ∀ n : ℤ, n < 0 ∨ (N : ℤ) < n → c n = 0)
    (hnorm : (∑ n ∈ Finset.Icc (0 : ℤ) (N : ℤ), ‖c n‖ ^ 2) = (1 : ℝ)) :
    let Q : ℕ := ∑ i : ι, (q i).natAbs
    let L : ℕ := N + 2 * Q + 1
    let D : Finset ℤ := Finset.Icc (-(Q : ℤ)) ((N : ℤ) + (Q : ℤ))
    let coord : Fin L → ℤ := fun a => (a.val : ℤ) - (Q : ℤ)
    let record : ι → Fin L → ℂ := fun i a => c (coord a + q i)
    let gamma : ℤ → ℂ := fun ell =>
      ∑ n ∈ Finset.Icc (0 : ℤ) (N : ℤ), c (n + ell) * star (c n)
    Set.range coord = (↑D : Set ℤ) ∧
    Function.Injective coord ∧
    (∀ i m, c (m + q i) ≠ 0 → m ∈ D) ∧
    (∀ i, (∑ a : Fin L, ‖record i a‖ ^ 2) = (1 : ℝ)) ∧
    (∀ i j, (∑ a : Fin L, star (record j a) * record i a) =
      gamma (q i - q j)) := by
  dsimp only
  refine ⟨(coordinate_interval N _).1, (coordinate_interval N _).2, ?_, ?_, ?_⟩
  · intro i m hm
    have hq := label_bound q i
    have hc : 0 ≤ m + q i ∧ m + q i ≤ (N : ℤ) := by
      by_contra! h
      exact hm (hsupport _ (by omega))
    apply Finset.mem_Icc.mpr
    omega
  · intro i
    rw [shifted_sum_reindex N q i (fun n => ‖c n‖ ^ 2) (by
      intro n hn
      simp [hsupport n hn])]
    exact hnorm
  · intro i j
    have h := shifted_sum_reindex N q j
      (fun n => c (n + (q i - q j)) * star (c n)) (by
        intro n hn
        simp [hsupport n hn])
    dsimp only at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro a ha
    have harg : (a.val : ℤ) - (↑(∑ x : ι, (q x).natAbs) : ℤ) + q j +
        (q i - q j) = (a.val : ℤ) - (↑(∑ x : ι, (q x).natAbs) : ℤ) + q i := by ring
    rw [harg, mul_comm]

private theorem recording_isometry
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε]
    (record : ι → ε → ℂ) (hnorm : ∀ i, ∑ a, ‖record i a‖ ^ 2 = (1 : ℝ)) :
    let V : Matrix (ι × ε) ι ℂ :=
      fun p j => if j = p.1 then record p.1 p.2 else 0
    V.conjTranspose * V = 1 := by
  classical
  dsimp only
  ext i j
  change (∑ p : ι × ε, star (if i = p.1 then record p.1 p.2 else 0) *
    (if j = p.1 then record p.1 p.2 else 0)) = if i = j then 1 else 0
  by_cases hij : i = j
  · subst j
    simp [Fintype.sum_prod_type,
      apply_ite, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
    exact_mod_cast hnorm i
  · simp [Fintype.sum_prod_type, apply_ite, hij]

private theorem marginal_entry
    {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (record : ι → Fin L → ℂ) (rho : Matrix ι ι ℂ) (i j : ι) :
    let V : Matrix (ι × Fin L) ι ℂ :=
      fun p j => if j = p.1 then record p.1 p.2 else 0
    (∑ a, (V * rho * V.conjTranspose) (i, a) (j, a)) =
      (∑ a, star (record j a) * record i a) * rho i j := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let ep : (Fin (Fintype.card ι) × Fin L) ≃ (ι × Fin L) :=
    Equiv.prodCongr e (Equiv.refl _)
  let V : Matrix (ι × Fin L) ι ℂ :=
    fun p j => if j = p.1 then record p.1 p.2 else 0
  have hV : V.submatrix ep e =
      (fun p j => if j = p.1 then record (e p.1) p.2 else 0) := by
    ext ⟨p, a⟩ j
    change (if e j = e p then record (e p) a else 0) =
      if j = p then record (e p) a else 0
    simp only [Equiv.apply_eq_iff_eq]
  have htransport :
      V.submatrix ep e * rho.submatrix e e * (V.submatrix ep e).conjTranspose =
        (V * rho * V.conjTranspose).submatrix ep ep := by
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
  have h :=
    (D5.S3.Quantum.Decoherence.EnvironmentMarginalChannel.environment_marginal_channel
      (fun p a => record (e p) a) (rho.submatrix e e)).2.2 (e.symm i) (e.symm j)
  dsimp only at h
  rw [← hV, htransport] at h
  simpa [ep, Matrix.submatrix_apply,
    D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality.recordGram, mul_comm] using h

private theorem diagonal_kraus_complete
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε]
    (record : ι → ε → ℂ) (hnorm : ∀ i, ∑ a, ‖record i a‖ ^ 2 = (1 : ℝ)) :
    ∑ a, (Matrix.diagonal (fun i => record i a)).conjTranspose *
      Matrix.diagonal (fun i => record i a) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.sum_apply, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    exact_mod_cast hnorm i
  · simp [Matrix.sum_apply, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      hij]

private theorem diagonal_kraus_entry
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε]
    (record : ι → ε → ℂ) (rho : Matrix ι ι ℂ) (i j : ι) :
    (∑ a, Matrix.diagonal (fun i => record i a) * rho *
      (Matrix.diagonal (fun i => record i a)).conjTranspose) i j =
        (∑ a, star (record j a) * record i a) * rho i j := by
  simp only [Matrix.sum_apply, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Pi.star_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- The concrete controlled recording and its actual environment partial trace
realize the coefficient coherence multiplier as a canonical quantum channel. -/
theorem finite_shifted_record_channel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (c : ℤ → ℂ) (q : ι → ℤ)
    (hsupport : ∀ n : ℤ, n < 0 ∨ (N : ℤ) < n → c n = 0)
    (hnorm : (∑ n ∈ Finset.Icc (0 : ℤ) (N : ℤ), ‖c n‖ ^ 2) = (1 : ℝ)) :
    let Q : ℕ := ∑ i : ι, (q i).natAbs
    let L : ℕ := N + 2 * Q + 1
    let D : Finset ℤ := Finset.Icc (-(Q : ℤ)) ((N : ℤ) + (Q : ℤ))
    let coord : Fin L → ℤ := fun a => (a.val : ℤ) - (Q : ℤ)
    let record : ι → Fin L → ℂ := fun i a => c (coord a + q i)
    let gamma : ℤ → ℂ := fun ell =>
      ∑ n ∈ Finset.Icc (0 : ℤ) (N : ℤ), c (n + ell) * star (c n)
    let V : Matrix (ι × Fin L) ι ℂ :=
      fun p j => if j = p.1 then record p.1 p.2 else 0
    let partialTrace : Matrix (ι × Fin L) (ι × Fin L) ℂ → Matrix ι ι ℂ :=
      fun joint i j => ∑ a : Fin L, joint (i, a) (j, a)
    let Lambda : Matrix ι ι ℂ → Matrix ι ι ℂ :=
      fun rho => partialTrace (V * rho * V.conjTranspose)
    (Set.range coord = (↑D : Set ℤ) ∧
    Function.Injective coord ∧
    (∀ i m, c (m + q i) ≠ 0 → m ∈ D) ∧
    (∀ i, (∑ a : Fin L, ‖record i a‖ ^ 2) = (1 : ℝ)) ∧
    (∀ i j, (∑ a : Fin L, star (record j a) * record i a) =
      gamma (q i - q j))) ∧
    (∀ ell : ℤ, gamma ell = ∑' n : ℤ, c (n + ell) * star (c n)) ∧
    V.conjTranspose * V = 1 ∧
    (∃ channel : D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel ι ι,
      ∀ rho : Matrix ι ι ℂ,
        CStarMatrix.ofMatrix.symm
          (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) = Lambda rho) ∧
    (∀ (rho : Matrix ι ι ℂ) i j,
      Lambda rho i j = gamma (q i - q j) * rho i j) ∧
    (∀ rho : Matrix ι ι ℂ, Matrix.trace (Lambda rho) = Matrix.trace rho) := by
  let Q : ℕ := ∑ i : ι, (q i).natAbs
  let record : ι → Fin (N + 2 * Q + 1) → ℂ :=
    fun i a => c ((a.val : ℤ) - (Q : ℤ) + q i)
  let V : Matrix (ι × Fin (N + 2 * Q + 1)) ι ℂ :=
    fun p j => if j = p.1 then record p.1 p.2 else 0
  have hr := shifted_coefficient_records N c q hsupport hnorm
  dsimp only at hr ⊢
  obtain ⟨channel, hchannel⟩ :=
    D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel
      (fun a => Matrix.diagonal (fun i => record i a))
      (diagonal_kraus_complete record hr.2.2.2.1)
  have hactual (rho : Matrix ι ι ℂ) :
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) =
      (fun i j => ∑ a, (V * rho * V.conjTranspose) (i, a) (j, a)) := by
    rw [hchannel]
    ext i j
    exact (diagonal_kraus_entry record rho i j).trans (marginal_entry record rho i j).symm
  refine ⟨hr, fun ell => coherenceKernel_eq_tsum N c hsupport ell,
    recording_isometry record hr.2.2.2.1, ⟨channel, hactual⟩, ?_, ?_⟩
  · intro rho i j
    exact (marginal_entry record rho i j).trans
      (congrArg (fun z => z * rho i j) (hr.2.2.2.2 i j))
  · intro rho
    rw [← hactual rho]
    exact channel.trace_preserving (CStarMatrix.ofMatrix rho)

#print axioms shifted_coefficient_records
#print axioms finite_shifted_record_channel

end D5.S3.Quantum.Decoherence.FiniteShiftedRecordChannel
