/- GID: D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every positive Gibbs weight vector admits a stochastic matrix with simple spectrum. -/

import D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer
import D5.S3.Quantum.Algebra.ZeitlinSixJ.Inverse
import D5.S3.StatisticalMechanics.ThermalProcessSelfDualFactorizationRefutation

/-! A birth–death chain preserving positive weights is similar to an irreducible real
Jacobi matrix. -/

namespace D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum

open _root_.Matrix Finset
open D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer (Near)
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence
open D5.S3.StatisticalMechanics.ThermalProcessSelfDualFactorizationRefutation (thermalProcesses)

/-- Every complex eigenvalue has algebraic multiplicity one. -/
def HasSimpleEigenvalues {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ((P.map (algebraMap ℝ ℂ)).charpoly.roots).Nodup

/-- A simple-spectrum Gibbs-stochastic matrix exists for every positive Gibbs vector. -/
def claim : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℝ), (∀ i, 0 < d i) →
    ∃ P : Matrix (Fin n) (Fin n) ℝ, P ∈ thermalProcesses d ∧ HasSimpleEigenvalues P

private noncomputable def weights {n : ℕ} (d : Fin n → ℝ) : Fin n → ℝ :=
  fun i => d i / ∑ j, d j

private noncomputable def transition {n : ℕ} (g : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i j =>
  if i = j then 1 - ∑ k, if Near k j then g k / 2 else 0
  else if Near i j then g i / 2 else 0

private noncomputable def symmetrization {n : ℕ} (g : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => (Real.sqrt (g i))⁻¹) * transition g * diagonal (fun i => Real.sqrt (g i))

private lemma weights_positive {m : ℕ} (d : Fin (m + 1) → ℝ) (hd : ∀ i, 0 < d i) :
    ∀ i, 0 < weights d i := by
  have hs : 0 < ∑ j, d j := sum_pos (fun j _ => hd j) univ_nonempty
  intro i
  exact div_pos (hd i) hs

private lemma weights_sum {m : ℕ} (d : Fin (m + 1) → ℝ) (hd : ∀ i, 0 < d i) :
    ∑ i, weights d i = 1 := by
  have hs : 0 < ∑ j, d j := sum_pos (fun j _ => hd j) univ_nonempty
  unfold weights
  rw [← sum_div, div_self hs.ne']

private lemma transition_columns {n : ℕ} (g : Fin n → ℝ) (j : Fin n) :
    ∑ i, transition g i j = 1 := by
  classical
  have hj : ¬ Near j j := by unfold Near; omega
  have entry (i : Fin n) : transition g i j =
      (if i = j then 1 - ∑ k, if Near k j then g k / 2 else 0 else 0) +
      (if Near i j then g i / 2 else 0) := by
    by_cases h : i = j
    · subst i
      simp only [transition, ite_eq_right hj, add_zero]
    · simp only [transition, ite_eq_right h, zero_add]
  simp_rw [entry]
  rw [sum_add_distrib]
  simp

private lemma transition_stochastic {n : ℕ} (g : Fin n → ℝ)
    (hg : ∀ i, 0 ≤ g i) (hsum : ∑ i, g i ≤ 1) :
    transition g ∈ Matrix.colStochastic ℝ (Fin n) := by
  classical
  rw [Matrix.mem_colStochastic_iff_sum]
  refine ⟨?_, transition_columns g⟩
  intro i j
  by_cases h : i = j
  · subst i
    have hb : (∑ k, if Near k j then g k / 2 else 0) ≤ (∑ k, g k) / 2 := by
      rw [sum_div]
      apply sum_le_sum
      intro k _
      split_ifs
      · exact le_rfl
      · exact div_nonneg (hg k) (by norm_num)
    rw [transition, ite_eq_left rfl]
    linarith
  · rw [transition, ite_eq_right h]
    split_ifs
    · exact div_nonneg (hg i) (by norm_num)
    · exact le_rfl

private lemma transition_stationary {n : ℕ} (g : Fin n → ℝ) :
    transition g *ᵥ g = g := by
  classical
  have balance (i j : Fin n) : transition g i j * g j = transition g j i * g i := by
    by_cases h : i = j
    · subst i; rfl
    · have ha : Near i j ↔ Near j i := by unfold Near; exact or_comm
      by_cases hij : Near i j
      · simp only [transition, ite_eq_right h, ite_eq_right (Ne.symm h),
          ite_eq_left hij, ite_eq_left (ha.mp hij)]
        ring
      · simp only [transition, ite_eq_right h, ite_eq_right (Ne.symm h), ite_eq_right hij,
          ite_eq_right (fun hji => hij (ha.mpr hji)), zero_mul]
  ext i
  change (∑ j, transition g i j * g j) = g i
  simp_rw [balance i]
  rw [← sum_mul, transition_columns, one_mul]

private lemma transition_preserves_weights {m : ℕ} (d : Fin (m + 1) → ℝ)
    (hd : ∀ i, 0 < d i) : transition (weights d) *ᵥ d = d := by
  have hs : (∑ j, d j) ≠ 0 := ne_of_gt (sum_pos (fun j _ => hd j) univ_nonempty)
  have hdg : d = (∑ j, d j) • weights d := by
    funext i
    dsimp [weights]
    exact (mul_div_cancel₀ (d i) hs).symm
  calc
    transition (weights d) *ᵥ d = transition (weights d) *ᵥ ((∑ j, d j) • weights d) :=
      congrArg (fun v => transition (weights d) *ᵥ v) hdg
    _ = (∑ j, d j) • weights d := by rw [mulVec_smul, transition_stationary]
    _ = d := hdg.symm

private lemma symmetrization_charpoly {n : ℕ} (g : Fin n → ℝ) (hg : ∀ i, 0 < g i) :
    (transition g).charpoly = (symmetrization g).charpoly := by
  have hcancel : diagonal (fun i => Real.sqrt (g i)) *
      diagonal (fun i => (Real.sqrt (g i))⁻¹) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (hg i)).ne'
  delta symmetrization
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hcancel, one_mul]

private lemma symmetrization_jacobi {m : ℕ} (g : Fin (m + 1) → ℝ)
    (hg : ∀ i, 0 < g i) :
    ∃ a e : Fin (m + 1) → ℝ,
      (∀ t : Fin m, e t.castSucc ≠ 0) ∧ symmetrization g = jacobiMatrix m a e := by
  classical
  let next (i : Fin (m + 1)) : Fin (m + 1) :=
    ⟨min (i.val + 1) m, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  let e (i : Fin (m + 1)) : ℝ := Real.sqrt (g i) * Real.sqrt (g (next i)) / 2
  have hnext {i j : Fin (m + 1)} (h : i.val + 1 = j.val) : next i = j := by
    apply Fin.ext
    dsimp [next]
    omega
  have hroot (i : Fin (m + 1)) : Real.sqrt (g i) ≠ 0 := (Real.sqrt_pos.mpr (hg i)).ne'
  have hscale (i : Fin (m + 1)) : (Real.sqrt (g i))⁻¹ * g i = Real.sqrt (g i) := by
    simpa only [div_eq_inv_mul] using (Real.div_sqrt (x := g i))
  refine ⟨fun i => transition g i i, e, ?_, ?_⟩
  · intro t
    dsimp [e]
    exact (div_pos (mul_pos (Real.sqrt_pos.mpr (hg _))
      (Real.sqrt_pos.mpr (hg _))) (by norm_num)).ne'
  · ext i j
    delta symmetrization
    simp only [mul_diagonal, diagonal_mul, jacobiMatrix, Matrix.add_apply,
      transpose_apply, upperBand]
    by_cases hij : i = j
    · subst j
      have h : ¬ i.val + 1 = i.val := by omega
      simp only [diagonal_apply_eq, ite_eq_right h, add_zero]
      calc
        (Real.sqrt (g i))⁻¹ * transition g i i * Real.sqrt (g i) =
            transition g i i * ((Real.sqrt (g i))⁻¹ * Real.sqrt (g i)) := by ring
        _ = transition g i i := by rw [inv_mul_cancel₀ (hroot i), mul_one]
    · rw [diagonal_apply_ne _ hij, zero_add]
      by_cases hu : i.val + 1 = j.val
      · have hl : ¬ j.val + 1 = i.val := by omega
        have ha : Near i j := Or.inl hu
        rw [ite_eq_left hu, ite_eq_right hl, add_zero, transition, ite_eq_right hij, ite_eq_left ha]
        dsimp [e]
        rw [hnext hu]
        calc
          (Real.sqrt (g i))⁻¹ * (g i / 2) * Real.sqrt (g j) =
              ((Real.sqrt (g i))⁻¹ * g i) * Real.sqrt (g j) / 2 := by ring
          _ = Real.sqrt (g i) * Real.sqrt (g j) / 2 := by rw [hscale]
      · by_cases hl : j.val + 1 = i.val
        · have ha : Near i j := Or.inr hl
          rw [ite_eq_right hu, ite_eq_left hl, zero_add, transition,
            ite_eq_right hij, ite_eq_left ha]
          dsimp [e]
          rw [hnext hl]
          calc
            (Real.sqrt (g i))⁻¹ * (g i / 2) * Real.sqrt (g j) =
                ((Real.sqrt (g i))⁻¹ * g i) * Real.sqrt (g j) / 2 := by ring
            _ = Real.sqrt (g j) * Real.sqrt (g i) / 2 := by rw [hscale]; ring
        · have ha : ¬ Near i j := by unfold Near; exact not_or.mpr ⟨hu, hl⟩
          rw [ite_eq_right hu, ite_eq_right hl, transition, ite_eq_right hij, ite_eq_right ha]
          ring

private lemma jacobi_eigenvector_zero (m : ℕ) (a e : Fin (m + 1) → ℝ)
    (he : ∀ t : Fin m, e t.castSucc ≠ 0) (v : Fin (m + 1) → ℝ) (mu : ℝ)
    (hv : jacobiMatrix m a e *ᵥ v = mu • v) (hz : v (Fin.last m) = 0) : v = 0 := by
  have hX : jacobiMatrix m a e * vecMulVec v v =
      vecMulVec v v * diagonal (fun _ => mu) := by
    rw [mul_vecMulVec, hv]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_diagonal]
    ring
  have hzero :=
    D5.S3.Quantum.Algebra.ZeitlinSixJ.Inverse.symmetric_jacobi_intertwiner_unique
      m a e (fun _ => mu) (vecMulVec v v) 0 he hX (by simp)
      (transpose_vecMulVec v v) (by simp) (by simp [vecMulVec_apply, hz])
  exact (vecMulVec_eq_zero.mp hzero).elim id id

lemma jacobi_simple (m : ℕ) (a e : Fin (m + 1) → ℝ)
    (he : ∀ t : Fin m, e t.castSucc ≠ 0) :
    HasSimpleEigenvalues (jacobiMatrix m a e) := by
  classical
  have hJ : (jacobiMatrix m a e).IsHermitian := by
    simpa only [jacobiMatrix, add_assoc, conjTranspose_eq_transpose_of_trivial] using
      (isHermitian_diagonal a).add (isHermitian_add_transpose_self (upperBand m e))
  have endpoint (i : Fin (m + 1)) : hJ.eigenvectorBasis i (Fin.last m) ≠ 0 := by
    intro hi
    have hv := jacobi_eigenvector_zero m a e he _ _ (hJ.mulVec_eigenvectorBasis i) hi
    apply hJ.eigenvectorBasis.orthonormal.ne_zero i
    apply PiLp.ext
    intro k
    exact congrFun hv k
  have hinj : Function.Injective hJ.eigenvalues := by
    intro i j hij
    by_contra hne
    let x := hJ.eigenvectorBasis i
    let y := hJ.eigenvectorBasis j
    let c := y (Fin.last m)
    let b := x (Fin.last m)
    have hv : jacobiMatrix m a e *ᵥ (c • ⇑x - b • ⇑y) =
        hJ.eigenvalues j • (c • ⇑x - b • ⇑y) := by
      rw [mulVec_sub, mulVec_smul, mulVec_smul,
        hJ.mulVec_eigenvectorBasis i, hJ.mulVec_eigenvectorBasis j, hij]
      ext k
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hz : (c • ⇑x - b • ⇑y) (Fin.last m) = 0 := by
      dsimp [c, b]
      ring
    have hzero := jacobi_eigenvector_zero m a e he _ _ hv hz
    have hzero' : c • x - b • y = 0 := by
      apply PiLp.ext
      intro k
      exact congrFun hzero k
    have hc := congrArg (fun z => hJ.eigenvectorBasis.toBasis.repr z i) hzero'
    have hc0 : c = 0 := by
      simpa [x, y, Module.Basis.repr_self, hne, Ne.symm hne] using hc
    exact endpoint j hc0
  unfold HasSimpleEigenvalues
  rw [Matrix.charpoly_map,
    hJ.splits_charpoly.roots_map_of_injective (algebraMap ℝ ℂ).injective]
  apply Multiset.Nodup.map (algebraMap ℝ ℂ).injective
  rw [hJ.roots_charpoly_eq_eigenvalues]
  exact Multiset.Nodup.map hinj Finset.univ.nodup

private lemma empty_case (d : Fin 0 → ℝ) :
    ∃ P : Matrix (Fin 0) (Fin 0) ℝ, P ∈ thermalProcesses d ∧ HasSimpleEigenvalues P := by
  refine ⟨1, ⟨(Matrix.colStochastic ℝ (Fin 0)).one_mem, ?_⟩, ?_⟩
  · exact one_mulVec d
  · unfold HasSimpleEigenvalues
    rw [Matrix.charpoly_isEmpty, Polynomial.roots_one]
    exact Multiset.nodup_zero

theorem result : claim := by
  intro n d hd
  cases n with
  | zero => exact empty_case d
  | succ m =>
    have hg := weights_positive d hd
    obtain ⟨a, e, he, hS⟩ := symmetrization_jacobi (weights d) hg
    refine ⟨transition (weights d), ⟨?_, transition_preserves_weights d hd⟩, ?_⟩
    · exact transition_stochastic (weights d) (fun i => (hg i).le) (weights_sum d hd).le
    · unfold HasSimpleEigenvalues at *
      rw [Matrix.charpoly_map, symmetrization_charpoly (weights d) hg, hS,
        ← Matrix.charpoly_map]
      exact jacobi_simple m a e he

end D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum
