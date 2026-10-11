/- GID: D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/QubitIncompatibilityRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Restricted-state compatibility determines incompatible unbiased qubit pairs. -/

import D5.S3.Quantum.FiniteDimensional
import D5.S3.Quantum.Measurement.FourQubitParentConstruction
noncomputable section
open D5.S3.Quantum.FiniteDimensional
open scoped ComplexOrder
namespace D5.S3.Quantum.ToriiTakakuraImamuraRigidity
abbrev V := EuclideanSpace ℝ (Fin 3)
abbrev Density := {ρ : QubitMatrix // ρ.PosSemidef ∧ Matrix.trace ρ = 1}
def pauliY : QubitMatrix := !![0, -Complex.I; Complex.I, 0]
def pauli (v : V) : QubitMatrix := (v 0 : ℂ) • qubitX + (v 1 : ℂ) • pauliY + (v 2 : ℂ) • qubitZ
def effect (v : V) (s : Fin 2) : QubitMatrix :=
  (1 / 2 : ℂ) • ((1 : QubitMatrix) + (if s = 0 then (1 : ℂ) else -1) • pauli v)
def IsPOVM (G : Fin 2 × Fin 2 → QubitMatrix) : Prop :=
  (∀ q, (G q).PosSemidef) ∧ (∑ s : Fin 2, ∑ t : Fin 2, G (s, t)) = 1
def marginal (G : Fin 2 × Fin 2 → QubitMatrix) (i s : Fin 2) : QubitMatrix :=
  if i = 0 then ∑ t : Fin 2, G (s, t) else ∑ t : Fin 2, G (t, s)
def SCompatible (S : Set Density) (a : Fin 2 → V) : Prop :=
  ∃ G : Fin 2 × Fin 2 → QubitMatrix, IsPOVM G ∧ ∀ ρ ∈ S, ∀ i s : Fin 2,
    bornProbability ρ.1 (marginal G i s) = bornProbability ρ.1 (effect (a i) s)
def Incompatible (a : Fin 2 → V) : Prop := ¬ SCompatible Set.univ a
def SignedPermutation (a b : Fin 2 → V) : Prop :=
  ∃ (π : Equiv.Perm (Fin 2)) (ε : Fin 2 → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ i, b i = ε i • a (π i)
def claim : Prop :=
  ∀ a b : Fin 2 → V,
    (∀ i, ‖a i‖ ≤ 1) →
    (∀ i, ‖b i‖ ≤ 1) →
    Incompatible a →
    Incompatible b →
    ((∀ S : Set Density, SCompatible S a ↔ SCompatible S b) ↔
      SignedPermutation a b)


open scoped InnerProductSpace
private abbrev B (t : ℝ) (v : V) : QubitMatrix :=
  (1 / 2 : ℂ) • D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB t v

private lemma pauli_eq (v : V) :
    pauli v = D5.S3.Quantum.Measurement.FourQubitParentConstruction.B v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, pauliY, qubitX, qubitZ,
      D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula] <;> ring

private lemma B_formula (t : ℝ) (v : V) :
    B t v = D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix t v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B, D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
      D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula,
      D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix] <;> ring

open D5.S3.Quantum.Measurement.FourQubitParentConstruction
  (scalarB_hermitian scalarB_det half_scalarB_posSemidef_iff
    hermitian_decomposition half_scalarB_double trace_B_mul)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (bloch blochMatrix)

private lemma B_hermitian (t : ℝ) (v : V) : (B t v).IsHermitian :=
  (scalarB_hermitian t v).smul (by simp [IsSelfAdjoint])

private lemma B_trace (t : ℝ) (v : V) : Matrix.trace (B t v) = (t : ℂ) := by
  rw [B_formula]
  simp [blochMatrix, Matrix.trace, Fin.sum_univ_two]
  ring

private lemma B_det (t : ℝ) (v : V) :
    Matrix.det (B t v) = ((t ^ 2 - ‖v‖ ^ 2) / 4 : ℝ) := by
  simp [B, scalarB_det, Complex.ofReal_div]
  ring

private lemma B_psd (t : ℝ) (v : V) : (B t v).PosSemidef ↔ ‖v‖ ≤ t :=
  half_scalarB_posSemidef_iff t v

private lemma B_rep (M : QubitMatrix) (h : M.IsHermitian) :
    M = B (Matrix.trace M).re (bloch M) := by
  have he := hermitian_decomposition M h
  rw [← half_scalarB_double] at he
  simpa [B, mul_div_cancel₀] using he

private lemma B_born (s t : ℝ) (w v : V) :
    bornProbability (B s w) (B t v) = ((s * t + ⟪w, v⟫_ℝ) / 2 : ℝ) := by
  simp only [B, bornProbability,
    D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, add_mul, mul_add,
    Matrix.trace_add, Matrix.one_mul, Matrix.mul_one, trace_B_mul]
  simp [D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula,
    Matrix.trace, Fin.sum_univ_two]
  ring

private lemma effect_B (v : V) (s : Fin 2) :
    effect v s = B 1 ((if s = 0 then (1 : ℝ) else -1) • v) := by
  rw [effect, pauli_eq]
  fin_cases s <;> simp [B, D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB]

private def state (r : V) (h : ‖r‖ ≤ 1) : Density :=
  ⟨B 1 r, (B_psd 1 r).mpr h, B_trace 1 r⟩

private lemma tomography (M N : QubitMatrix) (hM : M.IsHermitian)
    (hN : N.IsHermitian)
    (h : ∀ ρ : Density, bornProbability ρ.1 M = bornProbability ρ.1 N) : M = N := by
  have h0 := h (state 0 (by simp))
  dsimp only [state] at h0
  rw [B_rep M hM, B_rep N hN, B_born, B_born] at h0
  have ht : (Matrix.trace M).re = (Matrix.trace N).re := by
    have hr := congrArg Complex.re h0
    simp only [Complex.ofReal_re, inner_zero_left, add_zero, one_mul] at hr
    linarith
  have hv : bloch M = bloch N := by
    ext i
    have he := h (state (EuclideanSpace.single i 1) (by simp))
    dsimp only [state] at he
    rw [B_rep M hM, B_rep N hN, B_born, B_born] at he
    have he' := congrArg Complex.re he
    simp [ht, PiLp.inner_apply] at he'
    linarith
  rw [B_rep M hM, B_rep N hN, ht, hv]

private lemma B_sub (s t : ℝ) (v w : V) : B (s - t) (v - w) = B s v - B t w := by
  rw [B_formula, B_formula, B_formula]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blochMatrix] <;> ring

private lemma B_complement (t : ℝ) (v : V) : B (2 - t) (-v) = 1 - B t v := by
  rw [B_formula, B_formula]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blochMatrix] <;> ring

private lemma marginal_psd {G : Fin 2 × Fin 2 → QubitMatrix} (hG : IsPOVM G)
    (i s : Fin 2) : (marginal G i s).PosSemidef := by
  fin_cases i
  · simpa [marginal, Fin.sum_univ_two] using (hG.1 (s, 0)).add (hG.1 (s, 1))
  · simpa [marginal, Fin.sum_univ_two] using (hG.1 (0, s)).add (hG.1 (1, s))

private lemma marginal_sum {G : Fin 2 × Fin 2 → QubitMatrix} (hG : IsPOVM G)
    (i : Fin 2) : marginal G i 0 + marginal G i 1 = 1 := by
  fin_cases i <;> simpa [marginal, Fin.sum_univ_two, add_assoc, add_comm, add_left_comm]
    using hG.2

private def Joint (a b : V) : Prop :=
  ∃ G : Fin 2 × Fin 2 → QubitMatrix, IsPOVM G ∧
    marginal G 0 0 = B 1 a ∧ marginal G 1 0 = B 1 b

private lemma joint_margins {a b : V} {G : Fin 2 × Fin 2 → QubitMatrix}
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


private lemma compatible_univ (a : Fin 2 → V) :
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

private lemma joint_criterion (a b : V) : Joint a b ↔ ‖a + b‖ + ‖a - b‖ ≤ 2 := by
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
        simp [G, marginal, Fin.sum_univ_two, B,
          D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
          D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula] <;> ring

private def K (a b : V) : ℝ := 1 - ‖a‖ ^ 2 - ‖b‖ ^ 2 + ⟪a, b⟫_ℝ ^ 2

private lemma criterion_K (a b : V) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
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

private def project (n v : V) : V := v - ⟪n, v⟫_ℝ • n

private lemma project_add (n v w : V) : project n (v + w) = project n v + project n w := by
  simp only [project, inner_add_right]
  module

private lemma project_sub (n v w : V) : project n (v - w) = project n v - project n w := by
  simp only [project, inner_sub_right]
  module

private lemma project_orth (n v : V) (hn : ‖n‖ = 1) : ⟪n, project n v⟫_ℝ = 0 := by
  simp [project, inner_sub_right, inner_smul_right, hn]

private lemma project_inner (n v w : V) (hn : ‖n‖ = 1) :
    ⟪project n v, project n w⟫_ℝ = ⟪v, w⟫_ℝ - ⟪n, v⟫_ℝ * ⟪n, w⟫_ℝ := by
  simp only [project, inner_sub_left, inner_sub_right, real_inner_smul_left,
    inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow, mul_one,
    real_inner_comm n v]
  ring

private lemma project_sq (n v : V) (hn : ‖n‖ = 1) :
    ‖project n v‖ ^ 2 = ‖v‖ ^ 2 - ⟪n, v⟫_ℝ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, project_inner n v v hn, real_inner_self_eq_norm_sq]
  ring

private lemma project_norm (n v : V) (hn : ‖n‖ = 1) : ‖project n v‖ ≤ ‖v‖ := by
  nlinarith [project_sq n v hn, norm_nonneg (project n v), norm_nonneg v,
    sq_nonneg ⟪n, v⟫_ℝ]

private lemma plane_separation (n u v : V) (hn : ‖n‖ = 1)
    (h : ∀ r : V, ‖r‖ ≤ 1 → ⟪n, r⟫_ℝ = 0 → ⟪r, u⟫_ℝ = ⟪r, v⟫_ℝ) :
    project n u = project n v := by
  ext i
  have hi := h (project n (EuclideanSpace.single i 1))
    ((project_norm _ _ hn).trans (by simp)) (project_orth _ _ hn)
  simp only [project, inner_sub_left, real_inner_smul_left,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul] at hi
  simpa [project, mul_comm] using hi

private def central (n : V) : Set Density :=
  {ρ | ∃ (r : V) (h : ‖r‖ ≤ 1), ⟪n, r⟫_ℝ = 0 ∧ ρ = state r h}

private def quartic (a b n : V) : ℝ :=
  K a b + ⟪n, a⟫_ℝ ^ 2 + ⟪n, b⟫_ℝ ^ 2 -
    2 * ⟪a, b⟫_ℝ * ⟪n, a⟫_ℝ * ⟪n, b⟫_ℝ + ⟪n, a⟫_ℝ ^ 2 * ⟪n, b⟫_ℝ ^ 2

private lemma quartic_identity (a b n : V) (hn : ‖n‖ = 1) :
    K (project n a) (project n b) = quartic a b n := by
  simp only [K, quartic, project_sq n a hn, project_sq n b hn, project_inner n a b hn]
  ring

end D5.S3.Quantum.ToriiTakakuraImamuraRigidity
