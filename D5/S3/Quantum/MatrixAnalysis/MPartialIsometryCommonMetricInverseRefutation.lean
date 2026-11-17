/- GID: D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.claim; result=D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.result; claim=D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.claim
   digest: The prescribed inverse of a 2-partial isometry need not admit a common inner product. -/

/-
admission_basis: open-problem-resolution (#27062; Refuted).
Direct frozen dependencies: none (all imports are pinned Mathlib).
result: proof_shape: bind-only; escape_witness: none; consumer: external Question 6.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
beta, IsMPartialIsometry, candidateInverse, penroseIn, claim:
  proof_shape: bind-only (source definitions); escape_witness: none; consumer: result.
v, op, familyA, familyB, familyT:
  proof_shape: bind-only (parameterized counterexample data); escape_witness: none;
  consumers: adj_zero, family_partial, family_parameters, family_refutes, result.
op_zero, op_one: proof_shape: bind-only; escape_witness: none;
  consumers: family_partial, inverse_zero, q_apply, p_basis.
adj_zero, adj_one: proof_shape: bind-only; escape_witness: none;
  consumers: family_partial, inverse_zero, inverse_one.
family_partial: proof_shape: bind-only; escape_witness: none; consumer: family_refutes.
incompatible_core: proof_shape: bind-only; escape_witness: none; consumer: family_obstruction.
inverse_zero: proof_shape: bind-only; escape_witness: none; consumers: q_apply, p_basis.
inverse_one: proof_shape: bind-only; escape_witness: none; consumer: q_apply.
q_apply, p_basis: proof_shape: bind-only; escape_witness: none; consumer: family_obstruction.
family_obstruction, family_parameters: proof_shape: bind-only; escape_witness: none;
  consumer: family_refutes.
family_refutes: proof_shape: bind-only; escape_witness: none; consumer: result.
The claim retains the original adjoints and all four Penrose equations for one
independent positive definite Core. The finite-dimensional installed-inner-product
predicate FiniteMoorePenroseInverse.IsMoorePenroseInverse has a narrower domain.
The counterexample uses Mathlib rankOne and EuclideanSpace.single directly.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! A fixed generalized inverse of a 2-partial isometry with no common inner product. -/

namespace D5.S3.Quantum.MatrixAnalysis.MPartialIsometryCommonMetricInverseRefutation

open scoped BigOperators

/-- The operator definition preceding equation (2.1), page 2. Only m ≥ 1 is used. -/
noncomputable def beta {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (m : ℕ) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ k ∈ Finset.range (m + 1),
    (((-1 : ℂ) ^ (m - k)) * (Nat.choose m k : ℂ)) •
      ((ContinuousLinearMap.adjoint T) ^ k * T ^ k)

/-- Section 2: T is an m-partial isometry if T beta_m(T) = 0. -/
noncomputable def IsMPartialIsometry {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (m : ℕ) (T : H →L[ℂ] H) : Prop :=
  1 ≤ m ∧ T * beta m T = 0

/-- Question 6: the stars remain those of the original Hilbert space. -/
noncomputable def candidateInverse {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (2 : ℂ) • ContinuousLinearMap.adjoint T -
    (ContinuousLinearMap.adjoint T) ^ 2 * T

/-- Penrose's equations in one arbitrary positive definite inner product.
The finite-dimensional D5 IsMoorePenroseInverse owner does not cover this
unrestricted Hilbert-space domain or an independently chosen inner product.
The Core is used only as a form; no second norm instance is installed. -/
def penroseIn {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (g : InnerProductSpace.Core ℂ H) (T S : H →L[ℂ] H) : Prop :=
  T * S * T = T ∧ S * T * S = S ∧
    (∀ x y : H, g.inner ((T * S) x) y = g.inner x ((T * S) y)) ∧
    (∀ x y : H, g.inner ((S * T) x) y = g.inner x ((S * T) y))

/-- The affirmative assertion asked in Question 6, not its expected negation. -/
def claim : Prop :=
  ∀ (H : Type) [_originalNorm : NormedAddCommGroup H]
    [_originalInner : InnerProductSpace ℂ H] [_originalComplete : CompleteSpace H],
    ∀ T : H →L[ℂ] H, IsMPartialIsometry 2 T →
      ∃ g : InnerProductSpace.Core ℂ H, penroseIn g T (candidateInverse T)

open InnerProductSpace
private noncomputable def v (a b : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  (a : ℂ) • (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) +
    (b : ℂ) • (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))
private noncomputable def op (a b : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  rankOne ℂ (v a b) (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
private lemma op_zero (a b : ℝ) (x : EuclideanSpace ℂ (Fin 2)) : (op a b x) 0 = (a : ℂ) * x 0 := by
  simp [op, v, EuclideanSpace.inner_single_left]
private lemma op_one (a b : ℝ) (x : EuclideanSpace ℂ (Fin 2)) : (op a b x) 1 = (b : ℂ) * x 0 := by
  simp [op, v, EuclideanSpace.inner_single_left]
private lemma adj_zero (a b : ℝ) (x : EuclideanSpace ℂ (Fin 2)) :
    (ContinuousLinearMap.adjoint (op a b) x) 0 = (a : ℂ) * x 0 + (b : ℂ) * x 1 := by
  rw [show ContinuousLinearMap.adjoint (op a b) = rankOne ℂ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) (v a b) from adjoint_rankOne _ _]
  change inner ℂ (v a b) x * (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) 0 = _
  rw [show (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) 0 = 1 from
      PiLp.single_eq_same 2 (β := fun _ : Fin 2 => ℂ) (0 : Fin 2) (1 : ℂ), mul_one, v,
    inner_add_left, inner_smul_left, inner_smul_left]
  simp [EuclideanSpace.inner_single_left]
private lemma adj_one (a b : ℝ) (x : EuclideanSpace ℂ (Fin 2)) :
    (ContinuousLinearMap.adjoint (op a b) x) 1 = 0 := by
  simp [op]
private lemma family_partial (a b r : ℝ) (hs : a ^ 2 + b ^ 2 = r) (ht : a ^ 2 * r = 2 * r - 1) :
    IsMPartialIsometry 2 (op a b) := by
  constructor
  · norm_num
  have hsC : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = (r : ℂ) := by exact_mod_cast hs
  have htC : (a : ℂ) ^ 2 * (r : ℂ) = 2 * (r : ℂ) - 1 := by exact_mod_cast ht
  ext x i
  fin_cases i <;>
    simp [beta, Finset.sum_range_succ, pow_succ, mul_apply_eq_comp,
      op_zero, op_one, adj_zero, adj_one]
  · linear_combination (a : ℂ) * x 0 * htC + ((a : ℂ) ^ 3 - 2 * (a : ℂ)) * x 0 * hsC
  · linear_combination (b : ℂ) * x 0 * htC + ((a : ℂ) ^ 2 - 2) * (b : ℂ) * x 0 * hsC
private lemma incompatible_core (g : InnerProductSpace.Core ℂ (EuclideanSpace ℂ (Fin 2)))
    (P Q : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) (α c d δ : ℝ) (hc : 0 < c) (hd : d ≤ 0)
    (hQ0 : Q (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) = (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))) (hQ1 : Q (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) = 0)
    (hP0 : P (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) = (α : ℂ) • (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) + (d : ℂ) • (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)))
    (hP1 : P (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) = (c : ℂ) • (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) + (δ : ℂ) • (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)))
    (hP : ∀ x y, g.inner (P x) y = g.inner x (P y))
    (hQ : ∀ x y, g.inner (Q x) y = g.inner x (Q y)) : False := by
  let : InnerProductSpace.Core ℂ (EuclideanSpace ℂ (Fin 2)) := g
  have h01 : g.inner (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) = 0 := by
    have hh := hQ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))
    rw [hQ0, hQ1] at hh
    simpa only [InnerProductSpace.Core.inner_zero_right] using hh
  have hh := hP (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))
  rw [hP0, hP1] at hh
  simp only [InnerProductSpace.Core.inner_add_left,
    InnerProductSpace.Core.inner_add_right, InnerProductSpace.Core.inner_smul_left,
    InnerProductSpace.Core.inner_smul_right, h01,
    Complex.conj_ofReal, mul_zero, zero_add, add_zero] at hh
  have heq := congrArg Complex.re hh
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at heq
  have hp : 0 ≤ (g.inner (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))).re := g.re_inner_nonneg (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
  have hq : 0 ≤ (g.inner (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))).re := g.re_inner_nonneg (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))
  have hdq : d * (g.inner (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))).re ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hd hq
  have hp0 : (g.inner (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))).re = 0 := by nlinarith
  have hz : g.inner (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) = 0 := by
    apply Complex.ext
    · exact hp0
    · simpa using (InnerProductSpace.Core.inner_self_im (𝕜 := ℂ) (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)))
  have he := g.definite (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) hz
  have he0 := congrArg (fun x : EuclideanSpace ℂ (Fin 2) => x 0) he
  simp at he0
private lemma inverse_zero (a b r : ℝ) (hs : a ^ 2 + b ^ 2 = r) (x : EuclideanSpace ℂ (Fin 2)) :
    (candidateInverse (op a b) x) 0 = (a : ℂ) * (2 - (r : ℂ)) * x 0 + 2 * (b : ℂ) * x 1 := by
  have hsC : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = (r : ℂ) := by exact_mod_cast hs
  simp [candidateInverse, pow_two, mul_apply_eq_comp, op_zero, op_one, adj_zero, adj_one]
  linear_combination - (a : ℂ) * x 0 * hsC
private lemma inverse_one (a b : ℝ) (x : EuclideanSpace ℂ (Fin 2)) :
    (candidateInverse (op a b) x) 1 = 0 := by
  simp [candidateInverse, pow_two, mul_apply_eq_comp, adj_one]
private lemma q_apply (a b r : ℝ) (hs : a ^ 2 + b ^ 2 = r) (ht : a ^ 2 * r = 2 * r - 1) (x : EuclideanSpace ℂ (Fin 2)) :
    (candidateInverse (op a b) * op a b) x = x 0 • (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) := by
  have hsC : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = (r : ℂ) := by exact_mod_cast hs
  have htC : (a : ℂ) ^ 2 * (r : ℂ) = 2 * (r : ℂ) - 1 := by exact_mod_cast ht
  ext i
  fin_cases i
  · simp [mul_apply_eq_comp, inverse_zero a b r hs, op_zero, op_one]
    linear_combination 2 * x 0 * hsC - x 0 * htC
  · simp [mul_apply_eq_comp, inverse_one]
private lemma p_basis (a b r : ℝ) (hs : a ^ 2 + b ^ 2 = r) :
    (op a b * candidateInverse (op a b)) (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) =
      ((a ^ 2 * (2 - r) : ℝ) : ℂ) • (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) + ((a * b * (2 - r) : ℝ) : ℂ) • (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) ∧
    (op a b * candidateInverse (op a b)) (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) =
      ((2 * a * b : ℝ) : ℂ) • (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) + ((2 * b ^ 2 : ℝ) : ℂ) • (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [mul_apply_eq_comp, op_zero, op_one, inverse_zero a b r hs] <;> ring
private lemma family_obstruction (a b r : ℝ) (hr : 2 ≤ r) (ha : 0 < a) (hb : 0 < b)
    (hs : a ^ 2 + b ^ 2 = r) (ht : a ^ 2 * r = 2 * r - 1) (g : InnerProductSpace.Core ℂ (EuclideanSpace ℂ (Fin 2))) :
    ¬ penroseIn g (op a b) (candidateInverse (op a b)) := by
  intro h
  have hQ0 : (candidateInverse (op a b) * op a b) (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) = (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) := by
    rw [q_apply a b r hs ht]; simp
  have hQ1 : (candidateInverse (op a b) * op a b) (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) = 0 := by
    rw [q_apply a b r hs ht]; simp
  have hpos : 0 < 2 * a * b := by positivity
  have hneg : a * b * (2 - r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (mul_pos ha hb)) (by linarith)
  exact incompatible_core g _ _ _ _ _ _ hpos hneg hQ0 hQ1
    (p_basis a b r hs).1 (p_basis a b r hs).2 h.2.2.1 h.2.2.2

private noncomputable def familyA (r : ℝ) : ℝ := Real.sqrt (2 - 1/r)
private noncomputable def familyB (r : ℝ) : ℝ := (r - 1)/Real.sqrt r
private noncomputable def familyT (r : ℝ) : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) := op (familyA r) (familyB r)
private lemma family_parameters (r : ℝ) (hr : 2 ≤ r) :
    0 < familyA r ∧ 0 < familyB r ∧
    (familyA r) ^ 2 + (familyB r) ^ 2 = r ∧ (familyA r) ^ 2 * r = 2 * r - 1 := by
  have hr0 : 0 < r := by linarith
  have harg : 0 < 2 - 1/r := by
    have hh : 1/r < 2 := (div_lt_iff₀ hr0).mpr (by linarith)
    linarith
  have hasq : (familyA r) ^ 2 = 2 - 1/r := Real.sq_sqrt (le_of_lt harg)
  have hbsq : (familyB r) ^ 2 = (r - 1) ^ 2/r := by
    unfold familyB
    rw [div_pow, Real.sq_sqrt (le_of_lt hr0)]
  refine ⟨Real.sqrt_pos.mpr harg, div_pos (by linarith) (Real.sqrt_pos.mpr hr0), ?_, ?_⟩
  · rw [hasq,hbsq]
    field_simp [ne_of_gt hr0]
    ring
  · rw [hasq]
    field_simp [ne_of_gt hr0]
private lemma family_refutes (r : ℝ) (hr : 2 ≤ r) :
    IsMPartialIsometry 2 (familyT r) ∧
      ∀ g : InnerProductSpace.Core ℂ (EuclideanSpace ℂ (Fin 2)), ¬ penroseIn g (familyT r) (candidateInverse (familyT r)) := by
  obtain ⟨ha,hb,hs,ht⟩ := family_parameters r hr
  exact ⟨family_partial _ _ _ hs ht, fun g => family_obstruction _ _ _ hr ha hb hs ht g⟩
theorem result : ¬ claim := by
  intro h
  obtain ⟨g,hg⟩ := h (EuclideanSpace ℂ (Fin 2)) (familyT 25) (family_refutes 25 (by norm_num)).1
  exact (family_refutes 25 (by norm_num)).2 g hg
end D5.S3.Quantum.MatrixAnalysis.MPartialIsometryCommonMetricInverseRefutation
