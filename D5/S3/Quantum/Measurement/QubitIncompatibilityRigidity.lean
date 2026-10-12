/- GID: D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/QubitIncompatibilityRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Restricted-state compatibility determines incompatible unbiased qubit pairs. -/

import D5.S3.Quantum.Measurement.FourQubitParentConstruction
import D5.S3.Arith.Lattices.Klartag.State.PaddingMap
noncomputable section
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Foundation
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open scoped ComplexOrder MatrixOrder CStarAlgebra
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityRigidity
def effect (v : EuclideanSpace ℝ (Fin 3)) (s : Fin 2) : QubitMatrix :=
  (1 / 2 : ℂ) • ((1 : QubitMatrix) + (if s = 0 then (1 : ℂ) else -1) •
    D5.S3.Quantum.Measurement.FourQubitParentConstruction.B v)
def marginal (G : Fin 2 × Fin 2 → QubitMatrix) (i s : Fin 2) : QubitMatrix :=
  if i = 0 then ∑ t : Fin 2, G (s, t) else ∑ t : Fin 2, G (t, s)
def SCompatible (S : Set (FiniteStateChannel.DensityState (Fin 2)))
    (a : Fin 2 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ G : Fin 2 × Fin 2 → QubitMatrix, IsPOVM G ∧ ∀ ρ ∈ S, ∀ i s : Fin 2,
    bornProbability (CStarMatrix.ofMatrix.symm ρ.1) (marginal G i s) =
      bornProbability (CStarMatrix.ofMatrix.symm ρ.1) (effect (a i) s)
def Incompatible (a : Fin 2 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ¬ SCompatible (Set.univ : Set (FiniteStateChannel.DensityState (Fin 2))) a
def SignedPermutation (a b : Fin 2 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ (π : Equiv.Perm (Fin 2)) (ε : Fin 2 → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ i, b i = ε i • a (π i)
def claim : Prop :=
  ∀ a b : Fin 2 → EuclideanSpace ℝ (Fin 3),
    (∀ i, ‖a i‖ ≤ 1) →
    (∀ i, ‖b i‖ ≤ 1) →
    Incompatible a →
    Incompatible b →
    ((∀ S : Set (FiniteStateChannel.DensityState (Fin 2)), SCompatible S a ↔ SCompatible S b) ↔
      SignedPermutation a b)


open scoped InnerProductSpace
private abbrev B (t : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : QubitMatrix :=
  (1 / 2 : ℂ) • D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB t v

open D5.S3.Quantum.Measurement.FourQubitParentConstruction
  (scalarB_hermitian half_scalarB_posSemidef_iff
    hermitian_decomposition half_scalarB_double half_scalarB_complement trace_B_mul)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (bloch)

private lemma B_hermitian (t : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : (B t v).IsHermitian :=
  (scalarB_hermitian t v).smul (by simp [IsSelfAdjoint])

private lemma B_trace (t : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : Matrix.trace (B t v) = (t : ℂ) := by
  have he : B t v =
      D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix t v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
        D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula,
        D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix] <;> ring
  rw [he]
  exact D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix_trace t v

private lemma B_psd (t : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : (B t v).PosSemidef ↔ ‖v‖ ≤ t :=
  half_scalarB_posSemidef_iff t v

private lemma B_rep (M : QubitMatrix) (h : M.IsHermitian) :
    M = B (Matrix.trace M).re (bloch M) := by
  have he := hermitian_decomposition M h
  rw [← half_scalarB_double] at he
  simpa [B, mul_div_cancel₀] using he

private lemma B_born (s t : ℝ) (w v : EuclideanSpace ℝ (Fin 3)) :
    bornProbability (B s w) (B t v) = ((s * t + ⟪w, v⟫_ℝ) / 2 : ℝ) := by
  simp only [B, bornProbability,
    D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, add_mul, mul_add,
    Matrix.trace_add, Matrix.one_mul, Matrix.mul_one, trace_B_mul]
  simp [D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula,
    Matrix.trace, Fin.sum_univ_two]
  ring

private lemma effect_B (v : EuclideanSpace ℝ (Fin 3)) (s : Fin 2) :
    effect v s = B 1 ((if s = 0 then (1 : ℝ) else -1) • v) := by
  rw [effect]
  fin_cases s <;> simp [B, D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB]

private def state (r : EuclideanSpace ℝ (Fin 3)) (h : ‖r‖ ≤ 1) :
    FiniteStateChannel.DensityState (Fin 2) :=
  ⟨CStarMatrix.ofMatrix (B 1 r),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv ((B_psd 1 r).mpr h).nonneg, B_trace 1 r⟩

private lemma tomography (M N : QubitMatrix) (hM : M.IsHermitian)
    (hN : N.IsHermitian)
    (h : ∀ ρ : FiniteStateChannel.DensityState (Fin 2),
      bornProbability (CStarMatrix.ofMatrix.symm ρ.1) M =
        bornProbability (CStarMatrix.ofMatrix.symm ρ.1) N) : M = N := by
  have h0 := h (state 0 (by simp))
  dsimp only [state] at h0
  simp only [Equiv.symm_apply_apply] at h0
  rw [B_rep M hM, B_rep N hN, B_born, B_born] at h0
  have ht : (Matrix.trace M).re = (Matrix.trace N).re := by
    have hr := congrArg Complex.re h0
    simp only [Complex.ofReal_re, inner_zero_left, add_zero, one_mul] at hr
    linarith
  have hv : bloch M = bloch N := by
    ext i
    have he := h (state (EuclideanSpace.single i 1) (by simp))
    dsimp only [state] at he
    simp only [Equiv.symm_apply_apply] at he
    rw [B_rep M hM, B_rep N hN, B_born, B_born] at he
    have he' := congrArg Complex.re he
    simp [ht, PiLp.inner_apply] at he'
    linarith
  rw [B_rep M hM, B_rep N hN, ht, hv]

private lemma B_sub (s t : ℝ) (v w : EuclideanSpace ℝ (Fin 3)) :
    B (s - t) (v - w) = B s v - B t w := by
  have h : D5.S3.Quantum.Measurement.FourQubitParentConstruction.B (v - w) =
      D5.S3.Quantum.Measurement.FourQubitParentConstruction.B v -
        D5.S3.Quantum.Measurement.FourQubitParentConstruction.B w := by
    simp [sub_eq_add_neg]
  simp only [B, D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
    h, Complex.ofReal_sub, sub_smul, smul_add, smul_sub]
  abel

private lemma B_complement (t : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : B (2 - t) (-v) = 1 - B t v :=
  half_scalarB_complement t v


private lemma marginal_psd {G : Fin 2 × Fin 2 → QubitMatrix} (hG : IsPOVM G)
    (i s : Fin 2) : (marginal G i s).PosSemidef := by
  fin_cases i
  · simpa [marginal, Fin.sum_univ_two] using (hG.1 (s, 0)).add (hG.1 (s, 1))
  · simpa [marginal, Fin.sum_univ_two] using (hG.1 (0, s)).add (hG.1 (1, s))

private lemma marginal_sum {G : Fin 2 × Fin 2 → QubitMatrix} (hG : IsPOVM G)
    (i : Fin 2) : marginal G i 0 + marginal G i 1 = 1 := by
  fin_cases i <;> simpa [marginal, Fintype.sum_prod_type, Fin.sum_univ_two, add_assoc, add_comm,
    add_left_comm]
    using hG.2

private def Joint (a b : EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ G : Fin 2 × Fin 2 → QubitMatrix, IsPOVM G ∧
    marginal G 0 0 = B 1 a ∧ marginal G 1 0 = B 1 b

private lemma joint_margins {a b : EuclideanSpace ℝ (Fin 3)} {G : Fin 2 × Fin 2 → QubitMatrix}
    (hG : IsPOVM G) (hm : marginal G 0 0 = B 1 a ∧ marginal G 1 0 = B 1 b) :
    ∀ i s, marginal G i s = effect (![a, b] i) s := by
  intro i s
  fin_cases i <;> fin_cases s
  · simpa [effect_B] using hm.1
  · have hc := marginal_sum hG 0
    rw [hm.1] at hc
    have he := (eq_sub_of_add_eq' hc).trans (B_complement 1 a).symm
    norm_num at he
    simpa [effect_B] using he
  · simpa [effect_B] using hm.2
  · have hc := marginal_sum hG 1
    rw [hm.2] at hc
    have he := (eq_sub_of_add_eq' hc).trans (B_complement 1 b).symm
    norm_num at he
    simpa [effect_B] using he


private lemma compatible_univ (a : Fin 2 → EuclideanSpace ℝ (Fin 3)) :
    SCompatible Set.univ a ↔ Joint (a 0) (a 1) := by
  constructor
  · rintro ⟨G, hG, h⟩
    refine ⟨G, hG, ?_, ?_⟩ <;>
      have hm := marginal_psd hG
    · have he := tomography _ _ (hm 0 0).isHermitian
        (by rw [effect_B]; exact B_hermitian _ _) (fun ρ => h ρ (Set.mem_univ ρ) 0 0)
      simpa [effect_B] using he
    · have he := tomography _ _ (hm 1 0).isHermitian
        (by rw [effect_B]; exact B_hermitian _ _) (fun ρ => h ρ (Set.mem_univ ρ) 1 0)
      simpa [effect_B] using he
  · rintro ⟨G, hG, hm⟩
    refine ⟨G, hG, fun ρ _ i s => ?_⟩
    have he := joint_margins hG hm i s
    have ha : ![a 0, a 1] = a := by ext j; fin_cases j <;> rfl
    rw [ha] at he
    rw [he]

private lemma joint_criterion (a b : EuclideanSpace ℝ (Fin 3)) :
    Joint a b ↔ ‖a + b‖ + ‖a - b‖ ≤ 2 := by
  constructor
  · rintro ⟨G, hG, hA, hB⟩
    let γ := (Matrix.trace (G (0, 0))).re
    let g := bloch (G (0, 0))
    have h00 : G (0, 0) = B γ g := B_rep _ (hG.1 (0, 0)).isHermitian
    have h01 : G (0, 1) = B (1 - γ) (a - g) := by
      rw [B_sub, ← h00]
      exact eq_sub_of_add_eq' (by simpa [marginal, Fin.sum_univ_two] using hA)
    have h10 : G (1, 0) = B (1 - γ) (b - g) := by
      rw [B_sub, ← h00]
      exact eq_sub_of_add_eq' (by simpa [marginal, Fin.sum_univ_two] using hB)
    have h11 : G (1, 1) = B γ (g - a - b) := by
      have hc := marginal_sum hG 0
      rw [hA, show marginal G 0 1 = G (1, 0) + G (1, 1) by
        simp [marginal, Fin.sum_univ_two], h10] at hc
      have he : G (1, 1) = B 1 (-a) - B (1 - γ) (b - g) := by
        rw [show B 1 (-a) = 1 - B 1 a by
          simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using B_complement 1 a]
        exact eq_sub_of_add_eq' (eq_sub_of_add_eq' hc)
      rw [he, ← B_sub]
      congr 1
      · ring
      · module
    have hp := (B_psd γ g).mp (h00 ▸ hG.1 (0, 0))
    have hq := (B_psd γ (g - a - b)).mp (h11 ▸ hG.1 (1, 1))
    have hr := (B_psd (1 - γ) (a - g)).mp (h01 ▸ hG.1 (0, 1))
    have hs := (B_psd (1 - γ) (b - g)).mp (h10 ▸ hG.1 (1, 0))
    have hx := norm_sub_le g (g - a - b)
    have hy := norm_sub_le (a - g) (b - g)
    rw [show g - (g - a - b) = a + b by module] at hx
    rw [show (a - g) - (b - g) = a - b by module] at hy
    linarith
  · intro h
    let k := ‖a + b‖
    let G : Fin 2 × Fin 2 → QubitMatrix := fun q =>
      if q.1 = 0 then
        if q.2 = 0 then B (k / 2) ((1 / 2 : ℝ) • (a + b))
        else B ((2 - k) / 2) ((1 / 2 : ℝ) • (a - b))
      else if q.2 = 0 then B ((2 - k) / 2) (-((1 / 2 : ℝ) • (a - b)))
      else B (k / 2) (-((1 / 2 : ℝ) • (a + b)))
    refine ⟨G, ⟨?_, ?_⟩, ?_, ?_⟩
    · rintro ⟨s, t⟩
      fin_cases s <;> fin_cases t <;>
        norm_num only [G, Fin.ext_iff, Fin.val_zero, Fin.val_mk] <;>
        simp only [ite_true, ite_false] <;> rw [B_psd] <;>
        norm_num only [norm_neg, norm_smul, Real.norm_eq_abs] <;>
        dsimp only [k] <;> linarith
    all_goals
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [G, marginal, Fintype.sum_prod_type, Fin.sum_univ_two, B,
          D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
          D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula] <;> ring

private def K (a b : EuclideanSpace ℝ (Fin 3)) : ℝ := 1 - ‖a‖ ^ 2 - ‖b‖ ^ 2 + ⟪a, b⟫_ℝ ^ 2

private lemma criterion_K (a b : EuclideanSpace ℝ (Fin 3)) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a + b‖ + ‖a - b‖ ≤ 2 ↔ 0 ≤ K a b := by
  have hp := norm_nonneg (a + b)
  have hq := norm_nonneg (a - b)
  have hprod : 0 ≤ ‖a + b‖ * ‖a - b‖ := mul_nonneg hp hq
  have hA : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
  have hB : ‖b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg b]
  have hs := norm_add_sq_real a b
  have ht := norm_sub_sq_real a b
  have hi : (‖a + b‖ * ‖a - b‖) ^ 2 =
      (‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2 - 4 * ⟪a, b⟫_ℝ ^ 2 := by rw [mul_pow, hs, ht]; ring
  dsimp only [K]
  constructor
  · intro h
    have hbound : ‖a + b‖ * ‖a - b‖ ≤ 2 - ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
      nlinarith [sq_nonneg (2 - (‖a + b‖ + ‖a - b‖))]
    nlinarith [mul_self_le_mul_self hprod hbound]
  · intro h
    have hbound : ‖a + b‖ * ‖a - b‖ ≤ 2 - ‖a‖ ^ 2 - ‖b‖ ^ 2 := by nlinarith
    nlinarith [sq_nonneg (‖a + b‖ + ‖a - b‖ - 2)]

private def project (n v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) := v - ⟪n, v⟫_ℝ • n

private lemma project_add (n v w : EuclideanSpace ℝ (Fin 3)) :
    project n (v + w) = project n v + project n w := by
  simp only [project.eq_1, inner_add_right]
  module

private lemma project_sub (n v w : EuclideanSpace ℝ (Fin 3)) :
    project n (v - w) = project n v - project n w := by
  simp only [project, inner_sub_right]
  module

private lemma project_orth (n v : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) :
    ⟪n, project n v⟫_ℝ = 0 := by
  simp [project, inner_sub_right, inner_smul_right, hn]

private lemma project_inner (n v w : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) :
    ⟪project n v, project n w⟫_ℝ = ⟪v, w⟫_ℝ - ⟪n, v⟫_ℝ * ⟪n, w⟫_ℝ := by
  simp only [project, inner_sub_left, inner_sub_right, real_inner_smul_left,
    inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow, mul_one,
    real_inner_comm n v]
  ring

private lemma project_sq (n v : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) :
    ‖project n v‖ ^ 2 = ‖v‖ ^ 2 - ⟪n, v⟫_ℝ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, project_inner n v v hn, real_inner_self_eq_norm_sq]
  ring

private lemma project_norm (n v : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) :
    ‖project n v‖ ≤ ‖v‖ := by
  have he : project n v = (ℝ ∙ n)ᗮ.starProjection v := by
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_unit_singleton ℝ hn]
    rfl
  rw [he]
  exact Submodule.norm_starProjection_apply_le _ _

private lemma plane_separation (n u v : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1)
    (h : ∀ r : EuclideanSpace ℝ (Fin 3), ‖r‖ ≤ 1 → ⟪n, r⟫_ℝ = 0 → ⟪r, u⟫_ℝ = ⟪r, v⟫_ℝ) :
    project n u = project n v := by
  ext i
  have hi := h (project n (EuclideanSpace.single i 1))
    ((project_norm _ _ hn).trans (by simp)) (project_orth _ _ hn)
  simp only [project, inner_sub_left, real_inner_smul_left,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul] at hi
  simpa [project, mul_comm] using hi

private def central (n : EuclideanSpace ℝ (Fin 3)) :
    Set (FiniteStateChannel.DensityState (Fin 2)) :=
  {ρ | ∃ (r : EuclideanSpace ℝ (Fin 3)) (h : ‖r‖ ≤ 1), ⟪n, r⟫_ℝ = 0 ∧ ρ = state r h}

private def quartic (a b n : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  K a b + ⟪n, a⟫_ℝ ^ 2 + ⟪n, b⟫_ℝ ^ 2 -
    2 * ⟪a, b⟫_ℝ * ⟪n, a⟫_ℝ * ⟪n, b⟫_ℝ + ⟪n, a⟫_ℝ ^ 2 * ⟪n, b⟫_ℝ ^ 2

private lemma quartic_identity (a b n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) :
    K (project n a) (project n b) = quartic a b n := by
  simp only [K.eq_1, quartic.eq_1, project_sq n a hn, project_sq n b hn, project_inner n a b hn]
  ring

private lemma central_criterion (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1)
    (a : Fin 2 → EuclideanSpace ℝ (Fin 3)) :
    SCompatible (central n) a ↔
      ‖project n (a 0) + project n (a 1)‖ + ‖project n (a 0) - project n (a 1)‖ ≤ 2 := by
  constructor
  · rintro ⟨G, hG, h⟩
    let u : Fin 2 → EuclideanSpace ℝ (Fin 3) := fun i => bloch (marginal G i 0)
    have he (i : Fin 2) (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ ≤ 1) (hnr : ⟪n, r⟫_ℝ = 0) :
        (Matrix.trace (marginal G i 0)).re + ⟪r, u i⟫_ℝ = 1 + ⟪r, a i⟫_ℝ := by
      have hz := h (state r hr) ⟨r, hr, hnr, rfl⟩ i 0
      dsimp only [state] at hz
      simp only [Equiv.symm_apply_apply] at hz
      rw [B_rep _ (marginal_psd hG i 0).isHermitian, effect_B] at hz
      simp only [ite_true, one_smul] at hz
      rw [B_born, B_born] at hz
      have hz' := congrArg Complex.re hz
      simp only [Complex.ofReal_re, one_mul] at hz'
      dsimp only [u]
      linarith
    have ht (i : Fin 2) : (Matrix.trace (marginal G i 0)).re = 1 := by
      simpa using he i 0 (by simp) (by simp)
    have hm (i : Fin 2) : marginal G i 0 = B 1 (u i) := by
      rw [B_rep _ (marginal_psd hG i 0).isHermitian, ht]
    have hp (i : Fin 2) : project n (u i) = project n (a i) := by
      apply plane_separation n (u i) (a i) hn
      intro r hr hnr
      have hi := he i r hr hnr
      rw [ht] at hi
      linarith
    have hj := (joint_criterion (u 0) (u 1)).mp ⟨G, hG, hm 0, hm 1⟩
    have h1 := project_norm n (u 0 + u 1) hn
    have h2 := project_norm n (u 0 - u 1) hn
    rw [project_add, hp 0, hp 1] at h1
    rw [project_sub, hp 0, hp 1] at h2
    linarith
  · intro h
    obtain ⟨G, hG, hm⟩ := (compatible_univ (fun i => project n (a i))).mpr
      ((joint_criterion _ _).mpr h)
    refine ⟨G, hG, fun ρ hρ i s => ?_⟩
    obtain ⟨r, hr, hnr, rfl⟩ := hρ
    rw [hm _ (Set.mem_univ _) i s]
    dsimp only [state]
    simp only [Equiv.symm_apply_apply]
    rw [effect_B, effect_B, B_born, B_born]
    fin_cases s <;>
      simp [project, inner_smul_right, inner_sub_right, real_inner_comm n r, hnr]

private lemma central_quartic (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1)
    (a : Fin 2 → EuclideanSpace ℝ (Fin 3))
    (ha : ∀ i, ‖a i‖ ≤ 1) : SCompatible (central n) a ↔ 0 ≤ quartic (a 0) (a 1) n := by
  rw [central_criterion n hn a,
    criterion_K _ _ ((project_norm n (a 0) hn).trans (ha 0))
      ((project_norm n (a 1) hn).trans (ha 1)), quartic_identity _ _ _ hn]

private lemma incompatible_parameters (a : Fin 2 → EuclideanSpace ℝ (Fin 3)) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hi : Incompatible a) : K (a 0) (a 1) < 0 ∧
      0 < ‖a 0‖ ^ 2 * ‖a 1‖ ^ 2 - ⟪a 0, a 1⟫_ℝ ^ 2 := by
  change ¬ SCompatible Set.univ a at hi
  rw [compatible_univ, joint_criterion, criterion_K _ _ (ha 0) (ha 1)] at hi
  have hk := lt_of_not_ge hi
  have hA : ‖a 0‖ ^ 2 ≤ 1 := by nlinarith [ha 0, norm_nonneg (a 0)]
  have hB : ‖a 1‖ ^ 2 ≤ 1 := by nlinarith [ha 1, norm_nonneg (a 1)]
  refine ⟨hk, ?_⟩
  dsimp only [K] at hk
  nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]

private abbrev cross (a b : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp a) (WithLp.ofLp b))
private lemma cross_geometry (a b : EuclideanSpace ℝ (Fin 3)) :
    ⟪a, cross a b⟫_ℝ = 0 ∧ ⟪b, cross a b⟫_ℝ = 0 ∧
      ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2 := by
  have hd (v w : EuclideanSpace ℝ (Fin 3)) : ⟪v, w⟫_ℝ = WithLp.ofLp v ⬝ᵥ WithLp.ofLp w := by
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [← real_inner_self_eq_norm_sq]
  simp only [hd, cross]
  rw [dot_self_cross, dot_cross_self, cross_dot_cross]
  simp only [← hd, real_inner_self_eq_norm_sq, real_inner_comm b a, pow_two]
  trivial
private lemma gram_complete (a b r : EuclideanSpace ℝ (Fin 3)) :
    (‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2) * ‖r‖ ^ 2 =
      ‖b‖ ^ 2 * ⟪r, a⟫_ℝ ^ 2 - 2 * ⟪a, b⟫_ℝ * ⟪r, a⟫_ℝ * ⟪r, b⟫_ℝ +
      ‖a‖ ^ 2 * ⟪r, b⟫_ℝ ^ 2 + ⟪r, cross a b⟫_ℝ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, Fin.sum_univ_succ,
    cross, cross_apply]
  ring
private lemma normal_exists (a b : EuclideanSpace ℝ (Fin 3))
    (hD : 0 < ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2) :
    ∃ m : EuclideanSpace ℝ (Fin 3), ‖m‖ = 1 ∧ ⟪m, a⟫_ℝ = 0 ∧ ⟪m, b⟫_ℝ = 0 ∧
      ∀ r : EuclideanSpace ℝ (Fin 3), (‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2) *
        (‖r‖ ^ 2 - ⟪r, m⟫_ℝ ^ 2) =
        ‖b‖ ^ 2 * ⟪r, a⟫_ℝ ^ 2 - 2 * ⟪a, b⟫_ℝ * ⟪r, a⟫_ℝ * ⟪r, b⟫_ℝ +
        ‖a‖ ^ 2 * ⟪r, b⟫_ℝ ^ 2 := by
  obtain ⟨ha, hb, hc⟩ := cross_geometry a b
  have hn : ‖cross a b‖ ≠ 0 := by intro h; rw [h] at hc; nlinarith
  refine ⟨‖cross a b‖⁻¹ • cross a b, ?_, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  · rw [real_inner_smul_left, real_inner_comm, ha, mul_zero]
  · rw [real_inner_smul_left, real_inner_comm, hb, mul_zero]
  · intro r
    simp only [inner_smul_right]
    have hg := gram_complete a b r
    rw [← hc]
    field_simp
    nlinarith [hg]
private lemma radial_root (k M L : ℝ) (hk : k < 0) (hM : 0 < M) (hL : 0 ≤ L)
    (h1 : 0 ≤ k + M + L) :
    ∃ R : ℝ, 0 < R ∧ R ≤ 1 ∧ k + M * R + L * R ^ 2 = 0 ∧
      ∀ z : ℝ, 0 ≤ z → (0 ≤ k + M * z + L * z ^ 2 ↔ R ≤ z) := by
  let s := Real.sqrt (M ^ 2 - 4 * L * k)
  have hs : s ^ 2 = M ^ 2 - 4 * L * k := Real.sq_sqrt (by nlinarith)
  have hd : 0 < M + s := by dsimp [s]; positivity
  let R := -2 * k / (M + s)
  have hR : 0 < R := div_pos (by linarith) hd
  have he : k + M * R + L * R ^ 2 = 0 := by
    dsimp [R]
    field_simp
    linear_combination k * hs
  have ht (z : ℝ) (hz : 0 ≤ z) : 0 ≤ k + M * z + L * z ^ 2 ↔ R ≤ z := by
    have hp : 0 < M + L * (z + R) := by positivity
    have hf : k + M * z + L * z ^ 2 = (z - R) * (M + L * (z + R)) := by
      linear_combination he
    rw [hf, mul_nonneg_iff_of_pos_right hp, sub_nonneg]
  exact ⟨R, hR, (ht 1 (by norm_num)).mp (by simpa using h1), he, ht⟩
private def radialM (a b e : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ⟪e, a⟫_ℝ ^ 2 + ⟪e, b⟫_ℝ ^ 2 - 2 * ⟪a, b⟫_ℝ * ⟪e, a⟫_ℝ * ⟪e, b⟫_ℝ
private def radialL (a b e : EuclideanSpace ℝ (Fin 3)) : ℝ := ⟪e, a⟫_ℝ ^ 2 * ⟪e, b⟫_ℝ ^ 2
private lemma meridian_formula (a b m e : EuclideanSpace ℝ (Fin 3)) (hma : ⟪m, a⟫_ℝ = 0)
    (hmb : ⟪m, b⟫_ℝ = 0) (u v : ℝ) :
    quartic a b (u • m + v • e) = K a b + v ^ 2 * radialM a b e +
      v ^ 4 * radialL a b e := by
  simp only [quartic, radialM.eq_1, radialL.eq_1, inner_add_left, real_inner_smul_left, hma, hmb]
  ring
private lemma meridian_positive (a b e : EuclideanSpace ℝ (Fin 3)) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hE : ‖b‖ ^ 2 * ⟪e, a⟫_ℝ ^ 2 - 2 * ⟪a, b⟫_ℝ * ⟪e, a⟫_ℝ * ⟪e, b⟫_ℝ +
      ‖a‖ ^ 2 * ⟪e, b⟫_ℝ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2)
    (hD : 0 < ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2) :
    0 < radialM a b e ∧ 0 ≤ quartic a b e := by
  dsimp only [radialM]
  have hA : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
  have hB : ‖b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg b]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sq_nonneg ⟪e, b⟫_ℝ),
      mul_nonneg (sub_nonneg.mpr hB) (sq_nonneg ⟪e, a⟫_ℝ)]
  · have hp := mul_nonneg (by nlinarith : 0 ≤ 1 - ‖a‖ ^ 2 + ⟪e, a⟫_ℝ ^ 2)
      (by nlinarith : 0 ≤ 1 - ‖b‖ ^ 2 + ⟪e, b⟫_ℝ ^ 2)
    dsimp only [quartic, K]
    nlinarith [hE]
private def cap (m p : EuclideanSpace ℝ (Fin 3)) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  t • p + Real.sqrt (1 - ‖t • p‖ ^ 2) • m
private lemma boundary_transfer (a b c d m p : EuclideanSpace ℝ (Fin 3)) (hm : ‖m‖ = 1)
    (hp : ‖p‖ ≤ 1) (hpm : ⟪p, m⟫_ℝ = 0)
    (hma : ⟪m, a⟫_ℝ = 0) (hmb : ⟪m, b⟫_ℝ = 0) (hk : K a b < 0)
    (heq : ∀ n : EuclideanSpace ℝ (Fin 3), ‖n‖ = 1 → (0 ≤ quartic a b n ↔ 0 ≤ quartic c d n))
    (hz : quartic a b (cap m p 1) = 0) : quartic c d (cap m p 1) = 0 := by
  have hu (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ‖cap m p t‖ = 1 := by
    refine D5.S3.Arith.Lattices.Klartag.norm_padUnit ?_ hm ?_
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg p)).trans (by simpa using hp)
    · simp [real_inner_smul_left, hpm]
  have hf (t : ℝ) : quartic a b (cap m p t) =
      K a b + t ^ 2 * radialM a b p + t ^ 4 * radialL a b p := by
    rw [cap, add_comm, meridian_formula a b m p hma hmb]
  have hn (t : ℝ) (ht : t ∈ Set.Ioo 0 1) : quartic c d (cap m p t) ≤ 0 := by
    have ht2 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have hneg := mul_neg_of_pos_of_neg ht2 hk
    have hL : 0 ≤ radialL a b p := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hq : quartic a b (cap m p t) < 0 := by
      rw [hf] at hz ⊢
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg t) ht2.le) hL]
    exact (lt_of_not_ge (fun h => hq.not_ge ((heq _ (hu t ⟨ht.1.le, ht.2.le⟩)).mpr h))).le
  have hg : Continuous (fun t => quartic c d (cap m p t)) := by
    unfold quartic cap
    fun_prop
  have hl := le_on_closure hn hg.continuousOn continuousOn_const
    (show (1 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) by
      rw [closure_Ioo zero_ne_one]; exact ⟨zero_le_one, le_rfl⟩)
  exact le_antisymm hl ((heq _ (hu 1 ⟨zero_le_one, le_rfl⟩)).mp (by rw [hz]))
private lemma coplanarity (a b : Fin 2 → EuclideanSpace ℝ (Fin 3)) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hb : ∀ i, ‖b i‖ ≤ 1) (hia : Incompatible a) (hib : Incompatible b)
    (heq : ∀ n : EuclideanSpace ℝ (Fin 3), ‖n‖ = 1 →
      (0 ≤ quartic (a 0) (a 1) n ↔ 0 ≤ quartic (b 0) (b 1) n)) :
    ∃ m : EuclideanSpace ℝ (Fin 3), ‖m‖ = 1 ∧ (∀ i, ⟪m, a i⟫_ℝ = 0) ∧ (∀ i, ⟪m, b i⟫_ℝ = 0) := by
  obtain ⟨hka, hDa⟩ := incompatible_parameters a ha hia
  obtain ⟨_, hDb⟩ := incompatible_parameters b hb hib
  obtain ⟨m, hm, hma, hma', hGa⟩ := normal_exists (a 0) (a 1) hDa
  obtain ⟨m', hm', hmb, hmb', hGb⟩ := normal_exists (b 0) (b 1) hDb
  refine ⟨m, hm, (by intro i; fin_cases i <;> assumption), ?_⟩
  let t := ⟪m, m'⟫_ℝ
  by_cases hp : project m m' = 0
  · have hd : m' = t • m := by dsimp [project, t] at hp ⊢; exact sub_eq_zero.mp hp
    have ht : t ≠ 0 := by intro ht; simp only [ht, zero_smul] at hd; rw [hd] at hm'; simp at hm'
    intro i
    have hi : ⟪m', b i⟫_ℝ = 0 := by fin_cases i <;> assumption
    rw [hd, real_inner_smul_left] at hi
    exact (mul_eq_zero.mp hi).resolve_left ht
  exfalso
  let s := ‖project m m'‖
  have hs : 0 < s := norm_pos_iff.mpr hp
  let e := s⁻¹ • project m m'
  have he : ‖e‖ = 1 := by dsimp [e, s]; exact norm_smul_inv_norm hp
  have hme : ⟪m, e⟫_ℝ = 0 := by simp [e, inner_smul_right, project_orth m m' hm]
  have hem : ⟪e, m⟫_ℝ = 0 := (real_inner_comm m e).trans hme
  have hd : m' = t • m + s • e := by
    simp only [e, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    dsimp only [project, t]
    module
  have hc : t ^ 2 + s ^ 2 = 1 := by have h := project_sq m m' hm; rw [hm'] at h; nlinarith
  let e' := s • m - t • e
  have he' : ‖e'‖ = 1 := by
    have h := norm_sub_sq_real (s • m) (t • e)
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hm, he,
      real_inner_smul_left, inner_smul_right, hme] at h
    dsimp only [e']; nlinarith [norm_nonneg (s • m - t • e)]
  have hme' : ⟪m', e'⟫_ℝ = 0 := by
    rw [hd]; simp [e', inner_add_left, inner_sub_right, real_inner_smul_left,
      inner_smul_right, hm, he, hme, hem]; ring
  have hEa := hGa e
  have hEb := hGb e'
  rw [he, hem] at hEa
  rw [he', real_inner_comm m' e', hme'] at hEb
  norm_num only [one_pow, zero_pow, sub_zero, mul_one] at hEa hEb
  obtain ⟨hMa, hFa⟩ := meridian_positive (a 0) (a 1) e (ha 0) (ha 1) hEa.symm hDa
  obtain ⟨hMb, hFb⟩ := meridian_positive (b 0) (b 1) e' (hb 0) (hb 1) hEb.symm hDb
  have hLa : 0 ≤ radialL (a 0) (a 1) e := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hLb : 0 ≤ radialL (b 0) (b 1) e' := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h1 : 0 ≤ K (a 0) (a 1) + radialM (a 0) (a 1) e + radialL (a 0) (a 1) e := by
    convert hFa using 1; dsimp only [quartic, radialM, radialL]; ring
  obtain ⟨R, hR, hR1, hroot, hthreshold⟩ :=
    radial_root _ _ _ hka hMa hLa h1
  have hRt : R ≤ t ^ 2 := by
    apply (hthreshold (t ^ 2) (sq_nonneg t)).mp
    have h := (heq e' he').mpr hFb
    dsimp only [e'] at h
    rw [sub_eq_add_neg, ← neg_smul, meridian_formula _ _ m e hma hma'] at h
    convert h using 1; ring
  have hRlt : R < 1 := by nlinarith only [hc, hRt, sq_pos_of_pos hs]
  let q := Real.sqrt (1 - R)
  let r := Real.sqrt R
  have hq : 0 < q := Real.sqrt_pos.mpr (by linarith)
  have hr : 0 < r := Real.sqrt_pos.mpr hR
  have hr2 : r ^ 2 = R := Real.sq_sqrt hR.le
  have hz (v : ℝ) (hv : v ^ 2 = R) : quartic (b 0) (b 1) (q • m + v • e) = 0 := by
    have hpv : ‖v • e‖ ≤ 1 := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs]
      nlinarith only [hv, hR1, sq_abs v, abs_nonneg v]
    have hc : cap m (v • e) 1 = q • m + v • e := by
      simp only [cap, one_smul, norm_smul, Real.norm_eq_abs, sq_abs, he, mul_one, hv]
      exact add_comm _ _
    rw [← hc]
    apply boundary_transfer (a 0) (a 1) (b 0) (b 1) m (v • e) hm hpv
      (by simp [real_inner_smul_left, hem]) hma hma' hka heq
    rw [hc, meridian_formula _ _ m e hma hma']
    rw [show v ^ 4 = (v ^ 2) ^ 2 by ring, hv]
    nlinarith only [hroot]
  have hrot (u v : ℝ) : u • m + v • e =
      (u * t + v * s) • m' + (u * s - v * t) • e' := by
    rw [hd]; ext i
    simp [e', PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply]
    linear_combination -(u * m i + v * e i) * hc
  have hzp := hz r hr2
  have hzn := hz (-r) (by simpa using hr2)
  rw [hrot, meridian_formula _ _ m' e' hmb hmb'] at hzp hzn
  have hdif : ((q * s - r * t) ^ 2 - (q * s - -r * t) ^ 2) *
      (radialM (b 0) (b 1) e' + radialL (b 0) (b 1) e' *
        ((q * s - r * t) ^ 2 + (q * s - -r * t) ^ 2)) = 0 := by
    linear_combination hzp - hzn
  have hpos : 0 < radialM (b 0) (b 1) e' + radialL (b 0) (b 1) e' *
      ((q * s - r * t) ^ 2 + (q * s - -r * t) ^ 2) := by positivity
  have heqz := (mul_eq_zero.mp hdif).resolve_right hpos.ne'
  have ht0 : (q * s * r) * t = 0 := by nlinarith only [heqz]
  have ht : t = 0 := (mul_eq_zero.mp ht0).resolve_left (mul_pos (mul_pos hq hs) hr).ne'
  rw [ht] at hRt
  nlinarith only [hRt, hR]
private def curve (k c x y : ℝ) : ℝ := x ^ 2 * y ^ 2 + x ^ 2 + y ^ 2 - 2 * c * x * y + k
private lemma feasible_zero (a b m : EuclideanSpace ℝ (Fin 3)) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hma : ⟪m, a⟫_ℝ = 0) (hmb : ⟪m, b⟫_ℝ = 0)
    (hD : 0 < ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2) (x y : ℝ)
    (hz : curve (K a b) ⟪a, b⟫_ℝ x y = 0) :
    ∃ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ≤ 1 ∧ ⟪p, m⟫_ℝ = 0 ∧ ⟪p, a⟫_ℝ = x ∧ ⟪p, b⟫_ℝ = y := by
  let D := ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2
  let p := D⁻¹ • ((‖b‖ ^ 2 * x - ⟪a, b⟫_ℝ * y) • a +
    (‖a‖ ^ 2 * y - ⟪a, b⟫_ℝ * x) • b)
  have hxy : ⟪p, a⟫_ℝ = x ∧ ⟪p, b⟫_ℝ = y := by
    constructor <;> dsimp only [p, D] <;>
      simp only [real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq,
        real_inner_comm a b] <;> field_simp [hD.ne'] <;> ring
  obtain ⟨hac, hbc, _⟩ := cross_geometry a b
  have hpc : ⟪p, cross a b⟫_ℝ = 0 := by
    simp only [p, inner_add_left, real_inner_smul_left, hac, hbc, mul_zero, add_zero]
  have hn := gram_complete a b p
  simp only [hxy.1, hxy.2, hpc, zero_pow (by decide : 2 ≠ 0), add_zero] at hn
  have hA : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
  have hB : ‖b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg b]
  have hprod := mul_nonneg (by nlinarith : 0 ≤ 1 - ‖a‖ ^ 2 + x ^ 2)
    (by nlinarith : 0 ≤ 1 - ‖b‖ ^ 2 + y ^ 2)
  have hsq : ‖p‖ ^ 2 ≤ 1 := by
    apply (mul_le_mul_iff_right₀ hD).mp
    dsimp only [curve, K] at hz
    nlinarith [hn, hprod]
  refine ⟨p, (by nlinarith [norm_nonneg p]), ?_, hxy⟩
  simp only [p, inner_add_left, real_inner_smul_left,
    real_inner_comm m a, real_inner_comm m b, hma, hmb, mul_zero, add_zero]
private lemma common_boundary_zero (a b c d m : EuclideanSpace ℝ (Fin 3)) (hm : ‖m‖ = 1)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hma : ⟪m, a⟫_ℝ = 0) (hmb : ⟪m, b⟫_ℝ = 0)
    (hk : K a b < 0) (hD : 0 < ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2)
    (heq : ∀ n : EuclideanSpace ℝ (Fin 3), ‖n‖ = 1 → (0 ≤ quartic a b n ↔ 0 ≤ quartic c d n))
    (x y : ℝ) (hz : curve (K a b) ⟪a, b⟫_ℝ x y = 0) :
    ∃ n : EuclideanSpace ℝ (Fin 3), ⟪n, a⟫_ℝ = x ∧ ⟪n, b⟫_ℝ = y ∧ quartic c d n = 0 := by
  obtain ⟨p, hp, hpm, hpa, hpb⟩ := feasible_zero a b m ha hb hma hmb hD x y hz
  have hxy : ⟪cap m p 1, a⟫_ℝ = x ∧ ⟪cap m p 1, b⟫_ℝ = y := by
    simp [cap, inner_add_left, real_inner_smul_left, hma, hmb, hpa, hpb]
  have hzero : quartic a b (cap m p 1) = 0 := by
    dsimp only [quartic]; rw [hxy.1, hxy.2]
    dsimp only [curve] at hz; linarith only [hz]
  exact ⟨cap m p 1, hxy.1, hxy.2,
    boundary_transfer a b c d m p hm hp hpm hma hmb hk heq hzero⟩
private def delta (a b : EuclideanSpace ℝ (Fin 3)) (x : ℝ) : ℝ :=
  -x ^ 4 + (‖a‖ ^ 2 + ‖b‖ ^ 2 - 2) * x ^ 2 - K a b
private def branch (a b : EuclideanSpace ℝ (Fin 3)) (x s : ℝ) : ℝ :=
  (⟪a, b⟫_ℝ * x + s * Real.sqrt (delta a b x)) / (1 + x ^ 2)
private lemma boundary_branches (a b : EuclideanSpace ℝ (Fin 3)) (hk : K a b < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Set.Ioo 0 ε, 0 < delta a b x ∧
      curve (K a b) ⟪a, b⟫_ℝ x (branch a b x 1) = 0 ∧
      curve (K a b) ⟪a, b⟫_ℝ x (branch a b x (-1)) = 0 := by
  have hc : Continuous (delta a b) := by
    change Continuous (fun x => delta a b x)
    simp only [delta.eq_1]; fun_prop
  have hp : 0 < delta a b 0 := by simpa [delta] using neg_pos.mpr hk
  obtain ⟨l, ε, ⟨hl, hε⟩, hI⟩ :=
    (continuousAt_const.eventually_lt hc.continuousAt hp).exists_Ioo_subset
  refine ⟨ε, hε, fun x hx => ?_⟩
  have hd : 0 < delta a b x := hI ⟨hl.trans hx.1, hx.2⟩
  have hs := Real.sq_sqrt hd.le
  have hH : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
  have hz (s : ℝ) (hs : s ^ 2 = delta a b x) :
      curve (K a b) ⟪a, b⟫_ℝ x ((⟪a, b⟫_ℝ * x + s) / (1 + x ^ 2)) = 0 := by
    unfold curve K; field_simp
    dsimp only [delta, K] at hs
    linear_combination (1 + x ^ 2) * hs
  have hs' : (-Real.sqrt (delta a b x)) ^ 2 = delta a b x := by simpa using hs
  exact ⟨hd, (by simpa [branch.eq_1] using hz _ hs),
    (by simpa [branch.eq_1] using hz _ hs')⟩
open Polynomial
private lemma two_root_elimination (a b : EuclideanSpace ℝ (Fin 3)) (hk : K a b < 0)
    (u v w z d l : ℝ)
    (hg : ∀ x y, curve (K a b) ⟪a, b⟫_ℝ x y = 0 →
      curve l d (u * x + v * y) (w * x + z * y) = 0) : u * w = 0 := by
  let H : ℝ[X] := 1 + X ^ 2
  let D : ℝ[X] := -X ^ 4 + C (‖a‖ ^ 2 + ‖b‖ ^ 2 - 2) * X ^ 2 - C (K a b)
  let P : ℝ[X] := X * (C u * H + C (v * ⟪a, b⟫_ℝ))
  let Q : ℝ[X] := X * (C w * H + C (z * ⟪a, b⟫_ℝ))
  let R := P * Q + C (v * z) * D
  let T := P * C z + Q * C v
  let N := R ^ 2 + T ^ 2 * D + H ^ 2 *
    (P ^ 2 + Q ^ 2 + C (v ^ 2 + z ^ 2) * D - C (2 * d) * R + C l * H ^ 2)
  obtain ⟨ε, hε, hbr⟩ := boundary_branches a b hk
  have hN : N = 0 := by
    apply eq_zero_of_infinite_isRoot
    apply (Set.Ioo_infinite hε).mono
    intro x hx
    obtain ⟨hd, hp, hn⟩ := hbr x hx
    have hp := hg x _ hp
    have hn := hg x _ hn
    have hs := Real.sq_sqrt hd.le
    have hH : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
    dsimp only [curve, branch] at hp hn
    field_simp at hp hn
    change N.eval x = 0
    simp only [N, R, T, P, Q, H, D, eval_add, eval_mul, eval_pow, eval_sub,
      eval_neg, eval_C, eval_X, eval_one]
    change Real.sqrt (delta a b x) ^ 2 =
      -x ^ 4 + (‖a‖ ^ 2 + ‖b‖ ^ 2 - 2) * x ^ 2 - K a b at hs
    linear_combination (1 / 2 : ℝ) * hp + (1 / 2 : ℝ) * hn -
      ((v * z) ^ 2 * (Real.sqrt (delta a b x) ^ 2 +
        (-x ^ 4 + (‖a‖ ^ 2 + ‖b‖ ^ 2 - 2) * x ^ 2 - K a b)) +
        (x * (u * (1 + x ^ 2) + v * ⟪a, b⟫_ℝ) * z +
          x * (w * (1 + x ^ 2) + z * ⟪a, b⟫_ℝ) * v) ^ 2 +
        2 * x ^ 2 * (u * (1 + x ^ 2) + v * ⟪a, b⟫_ℝ) *
          (w * (1 + x ^ 2) + z * ⟪a, b⟫_ℝ) * v * z +
        (1 + x ^ 2) ^ 2 * (v ^ 2 + z ^ 2 - 2 * d * v * z)) * hs
  have hc : N.coeff 12 = (u * w) ^ 2 := by
    dsimp [N, R, T, P, Q, H, D]
    compute_degree!
  rw [hN, coeff_zero] at hc
  nlinarith only [hc]
private lemma quadratic_residue (a b : EuclideanSpace ℝ (Fin 3)) (hk : K a b < 0) (U V W : ℝ)
    (hg : ∀ x y, curve (K a b) ⟪a, b⟫_ℝ x y = 0 → U * x ^ 2 + V * y ^ 2 + W = 0) :
    U = 0 ∧ V = 0 := by
  let J : ℝ[X] := C U * X ^ 6 + C (2 * U + W - V) * X ^ 4 +
    C (U + 2 * W + V * (2 * ⟪a, b⟫_ℝ ^ 2 - 1 - K a b)) * X ^ 2 + C (W - V * K a b)
  obtain ⟨ε, hε, hbr⟩ := boundary_branches a b hk
  have hJ : J = 0 := by
    apply eq_zero_of_infinite_isRoot
    apply (Set.Ioo_infinite hε).mono
    intro x hx
    obtain ⟨hd, hp, hn⟩ := hbr x hx
    have hp := hg x _ hp
    have hn := hg x _ hn
    have hs := Real.sq_sqrt hd.le
    change Real.sqrt (delta a b x) ^ 2 =
      -x ^ 4 + (‖a‖ ^ 2 + ‖b‖ ^ 2 - 2) * x ^ 2 - K a b at hs
    have hH : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
    dsimp only [branch] at hp hn
    field_simp at hp hn
    change J.eval x = 0
    simp only [J, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    dsimp only [K] at hp hn hs ⊢
    linear_combination (1 / 2 : ℝ) * hp + (1 / 2 : ℝ) * hn - V * hs
  have h6 := congrArg (fun p : ℝ[X] => p.coeff 6) hJ
  have h4 := congrArg (fun p : ℝ[X] => p.coeff 4) hJ
  have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) hJ
  simp only [J, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_zero] at h6 h4 h0
  norm_num at h6 h4 h0
  have hv : V * (1 - K a b) = 0 := by linarith only [h6, h4, h0]
  have hV := (mul_eq_zero.mp hv).resolve_right (by linarith : 1 - K a b ≠ 0)
  exact ⟨h6, hV⟩
private lemma scale_signs (a b : EuclideanSpace ℝ (Fin 3)) (hk : K a b < 0) (p q : ℝ)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hg : ∀ x y, curve (K a b) ⟪a, b⟫_ℝ x y = 0 →
      curve (K (p • a) (q • b)) ⟪p • a, q • b⟫_ℝ (p * x) (q * y) = 0) :
    (p = 1 ∨ p = -1) ∧ (q = 1 ∨ q = -1) := by
  obtain ⟨hU, hV⟩ := quadratic_residue a b hk (p ^ 2 * (1 - q ^ 2))
    (q ^ 2 * (1 - p ^ 2)) (K (p • a) (q • b) - p ^ 2 * q ^ 2 * K a b) (by
      intro x y hz
      have hg := hg x y hz
      dsimp only [curve] at hg hz ⊢
      simp only [real_inner_smul_left, inner_smul_right] at hg
      linear_combination hg - p ^ 2 * q ^ 2 * hz)
  constructor <;> apply sq_eq_one_iff.mp
  · have h := (mul_eq_zero.mp hV).resolve_left (pow_ne_zero 2 hq); linarith
  · have h := (mul_eq_zero.mp hU).resolve_left (pow_ne_zero 2 hp); linarith
private lemma plane_coordinates (a b m c : EuclideanSpace ℝ (Fin 3)) (hm : ‖m‖ = 1)
    (hma : ⟪m, a⟫_ℝ = 0) (hmb : ⟪m, b⟫_ℝ = 0) (hmc : ⟪m, c⟫_ℝ = 0)
    (hD : 0 < ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2) : ∃ u v : ℝ, c = u • a + v • b := by
  let D := ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2
  let u := (‖b‖ ^ 2 * ⟪c, a⟫_ℝ - ⟪a, b⟫_ℝ * ⟪c, b⟫_ℝ) / D
  let v := (‖a‖ ^ 2 * ⟪c, b⟫_ℝ - ⟪a, b⟫_ℝ * ⟪c, a⟫_ℝ) / D
  let r := c - (u • a + v • b)
  have hD' : D ≠ 0 := by dsimp [D]; linarith
  have hDexp : ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2 ≠ 0 := by linarith
  have hDexp2 : ‖b‖ ^ 2 * ‖a‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2 ≠ 0 := by nlinarith
  have hr : ⟪r, a⟫_ℝ = 0 ∧ ⟪r, b⟫_ℝ = 0 := by
    constructor <;> dsimp only [r, u, v, D] <;>
      simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, real_inner_comm a b] <;> field_simp [hDexp, hDexp2] <;> ring
  have hrm : ⟪r, m⟫_ℝ = 0 := by
    simp [r, inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_comm m a,
      real_inner_comm m b, real_inner_comm m c, hma, hmb, hmc]
  have hgm := gram_complete a b m
  simp only [hm, hma, hmb] at hgm
  obtain ⟨_, _, hc⟩ := cross_geometry a b
  have hproj := project_sq m (cross a b) hm
  have hinner : ⟪m, cross a b⟫_ℝ ^ 2 = D := by
    nlinarith only [hgm, hm]
  have hnorm : ‖cross a b‖ ^ 2 = D := by
    simpa [D] using hc
  have hpc : project m (cross a b) = 0 := by
    have hz : ‖project m (cross a b)‖ ^ 2 = 0 := by
      nlinarith only [hproj, hinner, hnorm]
    have hz' : ‖project m (cross a b)‖ = 0 := by
      nlinarith [norm_nonneg (project m (cross a b))]
    exact norm_eq_zero.mp hz'
  have hrc : ⟪r, cross a b⟫_ℝ = 0 := by
    rw [show cross a b = ⟪m, cross a b⟫_ℝ • m from sub_eq_zero.mp hpc]
    simp [inner_smul_right, hrm]
  have hgr := gram_complete a b r
  rw [hr.1, hr.2, hrc] at hgr
  have hrnorm : ‖r‖ ^ 2 = 0 := by
    have hnormeq := real_inner_self_eq_norm_sq r
    nlinarith [hgr, hD, hnormeq]
  have hz' : ‖r‖ = 0 := by nlinarith [hrnorm, norm_nonneg r]
  have hz : r = 0 := norm_eq_zero.mp hz'
  exact ⟨u, v, sub_eq_zero.mp hz⟩
private lemma incompatible_nonzero (a : Fin 2 → EuclideanSpace ℝ (Fin 3)) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hi : Incompatible a) (i : Fin 2) : a i ≠ 0 := by
  intro hzero
  have hD := (incompatible_parameters a ha hi).2
  fin_cases i
  · change a 0 = 0 at hzero
    simp [hzero] at hD
  · change a 1 = 0 at hzero
    simp [hzero] at hD
private lemma effect_neg (v : EuclideanSpace ℝ (Fin 3)) (s : Fin 2) :
    effect (-v) s = effect v (if s = 0 then 1 else 0) := by
  fin_cases s <;> simp [effect, neg_smul]
private def flip (s : Fin 2) : Fin 2 := if s = 0 then 1 else 0
private lemma compat_flip_first_mp (S : Set (FiniteStateChannel.DensityState (Fin 2)))
    (a : Fin 2 → EuclideanSpace ℝ (Fin 3)) :
    SCompatible S a → SCompatible S (fun i => if i = 0 then -a i else a i) := by
  rintro ⟨G, hG, h⟩
  rw [IsPOVM] at hG
  refine ⟨(fun q => G (flip q.1, q.2)), ?_, ?_⟩
  · constructor
    · intro q; exact hG.1 (flip q.1, q.2)
    · simpa [Fintype.sum_prod_type, flip.eq_1, Fin.sum_univ_two, add_comm,
        add_left_comm, add_assoc]
        using hG.2
  · intro ρ hρ i s; fin_cases i <;> fin_cases s
    · simpa [marginal.eq_1, flip.eq_1, effect_neg] using h ρ hρ 0 1
    · simpa [marginal, flip, effect_neg, add_comm, add_left_comm, add_assoc] using h ρ hρ 0 0
    · simpa [marginal, flip, effect_neg, add_comm, add_left_comm, add_assoc] using h ρ hρ 1 0
    · simpa [marginal, flip, effect_neg, add_comm, add_left_comm, add_assoc] using h ρ hρ 1 1
private lemma compat_flip_first (S : Set (FiniteStateChannel.DensityState (Fin 2)))
    (a : Fin 2 → EuclideanSpace ℝ (Fin 3)) :
    SCompatible S a ↔ SCompatible S (fun i => if i = 0 then -a i else a i) := by
  constructor
  · exact compat_flip_first_mp S a
  · intro h
    have h' := compat_flip_first_mp S (fun i => if i = 0 then -a i else a i) h
    convert h' using 1
    funext i; fin_cases i <;> simp
private lemma compat_flip_second_mp (S : Set (FiniteStateChannel.DensityState (Fin 2)))
    (a : Fin 2 → EuclideanSpace ℝ (Fin 3)) :
    SCompatible S a → SCompatible S (fun i => if i = 1 then -a i else a i) := by
  rintro ⟨G, hG, h⟩
  refine ⟨(fun q => G (q.1, flip q.2)), ?_, ?_⟩
  · constructor
    · intro q; exact hG.1 (q.1, flip q.2)
    · simpa [IsPOVM, Fintype.sum_prod_type, flip, Fin.sum_univ_two, add_comm,
        add_left_comm, add_assoc] using hG.2
  · intro ρ hρ i s; fin_cases i <;> fin_cases s
    · simpa [marginal, flip, effect_neg, add_comm, add_left_comm, add_assoc] using h ρ hρ 0 0
    · simpa [marginal, flip, effect_neg, add_comm, add_left_comm, add_assoc] using h ρ hρ 0 1
    · simpa [marginal, flip, effect_neg, add_comm, add_left_comm, add_assoc] using h ρ hρ 1 1
    · simpa [marginal, flip, effect_neg] using h ρ hρ 1 0
private lemma compat_flip_second (S : Set (FiniteStateChannel.DensityState (Fin 2)))
    (a : Fin 2 → EuclideanSpace ℝ (Fin 3)) :
    SCompatible S a ↔ SCompatible S (fun i => if i = 1 then -a i else a i) := by
  constructor
  · exact compat_flip_second_mp S a
  · intro h
    have h' := compat_flip_second_mp S (fun i => if i = 1 then -a i else a i) h
    convert h' using 1
    funext i; fin_cases i <;> simp
private lemma compat_exchange_mp (S : Set (FiniteStateChannel.DensityState (Fin 2)))
    (a : Fin 2 → EuclideanSpace ℝ (Fin 3)) :
    SCompatible S a → SCompatible S (fun i => a (if i = 0 then 1 else 0)) := by
  rintro ⟨G, hG, h⟩
  refine ⟨(fun q => G (q.2, q.1)), ?_, ?_⟩
  · constructor
    · intro q; exact hG.1 (q.2, q.1)
    · simpa [Fintype.sum_prod_type, Fin.sum_univ_two, add_comm, add_left_comm, add_assoc]
        using hG.2
  · intro ρ hρ i s; fin_cases i <;> fin_cases s
    · simpa [marginal] using h ρ hρ 1 0
    · simpa [marginal] using h ρ hρ 1 1
    · simpa [marginal] using h ρ hρ 0 0
    · simpa [marginal] using h ρ hρ 0 1
private lemma compat_exchange (S : Set (FiniteStateChannel.DensityState (Fin 2)))
    (a : Fin 2 → EuclideanSpace ℝ (Fin 3)) :
    SCompatible S a ↔ SCompatible S (fun i => a (if i = 0 then 1 else 0)) := by
  constructor
  · exact compat_exchange_mp S a
  · intro h
    have h' := compat_exchange_mp S (fun i => a (if i = 0 then 1 else 0)) h
    convert h' using 1
    funext i; fin_cases i <;> simp
private lemma compat_signs (S : Set (FiniteStateChannel.DensityState (Fin 2)))
    (a : Fin 2 → EuclideanSpace ℝ (Fin 3)) (ε : Fin 2 → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    SCompatible S a ↔ SCompatible S (fun i => ε i • a i) := by
  rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1 | h1
  · convert (Iff.rfl : SCompatible S a ↔ SCompatible S a) using 2
    funext i; fin_cases i <;> simp [h0, h1]
  · convert compat_flip_second S a using 2
    funext i; fin_cases i <;> simp [h0, h1]
  · convert compat_flip_first S a using 2
    funext i; fin_cases i <;> simp [h0, h1]
  · convert (compat_flip_first S a).trans
      (compat_flip_second S (fun i => if i = 0 then -a i else a i)) using 2
    funext i; fin_cases i <;> simp [h0, h1]
theorem result : claim := by
  intro a b ha hb hia hib
  constructor
  · intro hS
    have heq (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) :
        0 ≤ quartic (a 0) (a 1) n ↔ 0 ≤ quartic (b 0) (b 1) n := by
      rw [← central_quartic n hn a ha, ← central_quartic n hn b hb]
      exact hS (central n)
    obtain ⟨m, hm, hma, hmb⟩ := coplanarity a b ha hb hia hib heq
    obtain ⟨hk, hD⟩ := incompatible_parameters a ha hia
    obtain ⟨u, v, hc⟩ := plane_coordinates (a 0) (a 1) m (b 0) hm (hma 0) (hma 1) (hmb 0) hD
    obtain ⟨w, z, hd⟩ := plane_coordinates (a 0) (a 1) m (b 1) hm (hma 0) (hma 1) (hmb 1) hD
    have hg (x y : ℝ) (hz : curve (K (a 0) (a 1)) ⟪a 0, a 1⟫_ℝ x y = 0) :
        curve (K (b 0) (b 1)) ⟪b 0, b 1⟫_ℝ (u*x+v*y) (w*x+z*y) = 0 := by
      obtain ⟨n, hx, hy, hn⟩ := common_boundary_zero (a 0) (a 1) (b 0) (b 1) m hm
        (ha 0) (ha 1) (hma 0) (hma 1) hk hD heq x y hz
      have hx' : ⟪n, b 0⟫_ℝ = u*x+v*y := by
        rw [hc]; simp [inner_add_right, inner_smul_right, hx, hy]
      have hy' : ⟪n, b 1⟫_ℝ = w*x+z*y := by
        rw [hd]; simp [inner_add_right, inner_smul_right, hx, hy]
      dsimp only [quartic] at hn
      rw [hx', hy'] at hn
      dsimp only [curve]; linear_combination hn
    have hK : K (a 1) (a 0) = K (a 0) (a 1) := by
      unfold K; rw [real_inner_comm (a 0) (a 1)]; ring
    have hswap (x y : ℝ) : curve (K (a 1) (a 0)) ⟪a 1, a 0⟫_ℝ x y =
        curve (K (a 0) (a 1)) ⟪a 0, a 1⟫_ℝ y x := by
      unfold curve; rw [hK, real_inner_comm (a 0) (a 1)]; ring
    have huw := two_root_elimination (a 0) (a 1) hk u v w z ⟪b 0, b 1⟫_ℝ (K (b 0) (b 1)) hg
    have hvz := two_root_elimination (a 1) (a 0) (hK ▸ hk) v u z w
      ⟪b 0, b 1⟫_ℝ (K (b 0) (b 1)) (by
        intro x y hz
        simpa [mul_comm, add_comm] using hg y x ((hswap x y) ▸ hz))
    have hb0 := incompatible_nonzero b hb hib 0
    have hb1 := incompatible_nonzero b hb hib 1
    by_cases hu : u = 0
    · have hv : v ≠ 0 := by intro hv; apply hb0; simp [hc, hu, hv]
      have hz : z = 0 := (mul_eq_zero.mp hvz).resolve_left hv
      have hw : w ≠ 0 := by intro hw; apply hb1; simp [hd, hw, hz]
      have hc' : b 0 = v • a 1 := by simpa [hu] using hc
      have hd' : b 1 = w • a 0 := by simpa [hz] using hd
      obtain ⟨hv1, hw1⟩ := scale_signs (a 1) (a 0) (hK ▸ hk) v w hv hw (by
        intro x y hz'
        have h := hg y x ((hswap x y) ▸ hz')
        simpa [hu, hz, ← hc', ← hd'] using h)
      refine ⟨Equiv.swap 0 1, (fun i => if i = 0 then v else w), ?_, ?_⟩
      · intro i; fin_cases i <;> simp [hv1, hw1]
      · intro i; fin_cases i <;> simpa using (by assumption)
    · have hw : w = 0 := (mul_eq_zero.mp huw).resolve_left hu
      have hz : z ≠ 0 := by intro hz; apply hb1; simp [hd, hw, hz]
      have hv : v = 0 := (mul_eq_zero.mp hvz).resolve_right hz
      have hc' : b 0 = u • a 0 := by simpa [hv] using hc
      have hd' : b 1 = z • a 1 := by simpa [hw] using hd
      obtain ⟨hu1, hz1⟩ := scale_signs (a 0) (a 1) hk u z hu hz (by
        intro x y hz'
        have h := hg x y hz'
        simpa [hw, hv, ← hc', ← hd'] using h)
      refine ⟨Equiv.refl _, (fun i => if i = 0 then u else z), ?_, ?_⟩
      · intro i; fin_cases i <;> simp [hu1, hz1]
      · intro i; fin_cases i <;> simpa using (by assumption)
  · rintro ⟨π, ε, hε, hb'⟩ S
    have hbfun : b = (fun i => ε i • a (π i)) := funext hb'
    rw [hbfun]
    apply Iff.trans ?_ (compat_signs S (fun i => a (π i)) ε hε)
    have hne : π 1 ≠ π 0 := fun h => (by norm_num : (1 : Fin 2) ≠ 0) (π.injective h)
    have hcases (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hcases (π 0) with hp | hp
    · have hp' : π 1 = 1 := (hcases (π 1)).resolve_left (by intro h; apply hne; rw [h, hp])
      convert (Iff.rfl : SCompatible S a ↔ SCompatible S a) using 2
      funext i; fin_cases i <;> simp [hp, hp']
    · have hp' : π 1 = 0 := (hcases (π 1)).resolve_right (by intro h; apply hne; rw [h, hp])
      convert compat_exchange S a using 2
      funext i; fin_cases i <;> simp [hp, hp']
end D5.S3.Quantum.Measurement.QubitIncompatibilityRigidity
