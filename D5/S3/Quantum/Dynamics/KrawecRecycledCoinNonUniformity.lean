/- GID: D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.claim; result=D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.result; claim=D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.claim
   digest: Nonuniformity of the recycled-coin walk at a nonexceptional memory parameter. -/

/-
proof_shape (same-delivery helpers inlined):
Definitions and abbreviations below record binding/organization, not independent proof claims.
Compiler-generated support and equations are included with their live consumers.
  angle: bind-only; consumer: coinFlip.
  angle._proof_1: bind-only; consumer: B.
  angle._proof_2: bind-only; consumer: angle.
  coinFlip: bind-only; consumer: U.
  shift: bind-only; consumer: U.
  swap: bind-only; consumer: U.
  U: bind-only; consumer: p.
  initial: bind-only; consumer: b.
  p: bind-only; consumer: avg.
  avg: bind-only; consumer: claim.
  exceptional: bind-only; consumer: claim.
  exceptional._proof_1: bind-only; consumer: a.
  exceptional._proof_2: bind-only; consumer: kappa.
  exceptional._proof_3: bind-only; consumer: exceptional.
  unitCoin: bind-only; consumer: claim.
  claim: bind-only; consumer: result.
  claim._proof_1: bind-only; consumer: claim.
  a: bind-only; consumer: B.
  kappa: bind-only; consumer: c.
  c: bind-only; consumer: B.
  theta: bind-only; consumer: s.
  s: bind-only; consumer: B.
  phiStar: bind-only; consumer: M_step.
  a_facts: bind-only; consumer: c_bounds.
  kappa_facts: bind-only; consumer: c_bounds.
  c_bounds: bind-only; consumer: theta_facts.
  theta_facts: bind-only; consumer: sin_sq.
  phi_facts: bind-only; consumer: mode_step.
  phi_nonexceptional: bind-only; consumer: result.
  phi_nonexceptional._simp_1_1: bind-only; consumer: phi_nonexceptional.
  phi_nonexceptional._simp_1_2: bind-only; consumer: phi_nonexceptional.
  scalar_resonance: bind-only; consumer: resonance.
  sin_sq: bind-only; consumer: eigenvectors.
  scalar_reductions: bind-only; consumer: coin_overlap.
  z: bind-only; consumer: w.
  z._proof_1: bind-only; consumer: E.
  chi_norm: bind-only; consumer: z_norm.
  z_exp: bind-only; consumer: z_re.
  z_norm: bind-only; consumer: z_unit.
  z_re: bind-only; consumer: z_conj.
  z_conj: bind-only; consumer: z_poly.
  z_unit: bind-only; consumer: z_poly.
  z_poly: bind-only; consumer: resonance.
  z_ne_zero: bind-only; consumer: X_pairings.
  z_ne_one: bind-only; consumer: chi_sum.
  chi_sum: bind-only; consumer: X_pairings.
  chi_neg_one: bind-only; consumer: character_mode.
  lam: bind-only; consumer: v.
  resonance: bind-only; consumer: X_fixed.
  B: bind-only; consumer: B_apply.
  B_apply: bind-only; consumer: mode_step.
  B_apply._simp_1_1: bind-only; consumer: B_apply.
  B_apply._simp_1_2: bind-only; consumer: B_apply.
  mode_step: bind-only; consumer: trivial_mode.
  character_mode: bind-only; consumer: global_eigenvectors.
  trivial_mode: bind-only; consumer: global_eigenvectors.
  v: bind-only; consumer: f.
  w: bind-only; consumer: g.
  eigenvectors: bind-only; consumer: global_eigenvectors.
  eigenvectors._simp_1_1: bind-only; consumer: eigenvectors.
  eigenvectors._simp_1_2: bind-only; consumer: eigenvectors.
  coin_overlap: bind-only; consumer: X_pairings.
  Index: bind-only; consumer: E.
  H: bind-only; consumer: M.
  K: bind-only; consumer: E.
  coin_inner: bind-only; consumer: walk_inner.
  walk_inner: bind-only; consumer: walkIso._proof_1.
  walkLin: bind-only; consumer: walkIso.
  walkLin._proof_1: bind-only; consumer: walkLin.
  walkLin._proof_2: bind-only; consumer: walkLin.
  walkIso: bind-only; consumer: F_outer.
  walkIso._proof_1: bind-only; consumer: walkIso.
  walkEquiv: bind-only; consumer: M.
  walkEquiv._proof_1: bind-only; consumer: walkEquiv.
  M: bind-only; consumer: M_step.
  M._proof_1: bind-only; consumer: M.
  M._proof_2: bind-only; consumer: M.
  M._proof_3: bind-only; consumer: M.
  M_unitary: bind-only; consumer: F_identity.
  M_step: bind-only; consumer: F_outer.
  flat: bind-only; consumer: P.
  mat: bind-only; consumer: baseline.
  hs_inner: bind-only; consumer: identity_inner.
  conjugateLin: bind-only; consumer: F.
  conjugateLin._proof_1: bind-only; consumer: conjugateLin.
  conjugateLin._proof_2: bind-only; consumer: conjugateLin.
  F: bind-only; consumer: E.
  F._proof_1: bind-only; consumer: F.
  E: bind-only; consumer: Q.
  Q: bind-only; consumer: QF.
  Q._proof_1: bind-only; consumer: Q.
  QF: bind-only; consumer: avg_limit.
  identity: bind-only; consumer: Y.
  P: bind-only; consumer: P_sum.
  outer: bind-only; consumer: X.
  F_identity: bind-only; consumer: baseline.
  identity_inner: bind-only; consumer: baseline.
  F_outer: bind-only; consumer: X_fixed.
  P_inner: bind-only; consumer: X_pairings.
  f: bind-only; consumer: X.
  g: bind-only; consumer: X.
  X: bind-only; consumer: X_fixed.
  X.eq_1: bind-only; consumer: X_fixed.
  Y: bind-only; consumer: baseline.
  Y._proof_1: bind-only; consumer: Y.
  Y.eq_1: bind-only; consumer: baseline.
  global_eigenvectors: bind-only; consumer: X_fixed.
  X_fixed: bind-only; consumer: strict_surplus.
  X_pairings: bind-only; consumer: strict_surplus.
  baseline: bind-only; consumer: strict_surplus.
  projection_pairing: bind-only; consumer: limit_sum.
  strict_surplus: bind-only; consumer: witness12.
  strict_surplus._simp_1_2: bind-only; consumer: strict_surplus.
  basisCoin: bind-only; consumer: b.
  b: bind-only; consumer: P_sum.
  basis_unit: bind-only; consumer: result.
  P_sum: bind-only; consumer: limit_sum.
  walk_iterate: bind-only; consumer: probability_norm.
  probability_norm: bind-only; consumer: density_probability.
  density_iterate: bind-only; consumer: density_probability.
  density_probability: bind-only; consumer: avg_observable.
  avg_observable: bind-only; consumer: avg_limit._simp_1_1.
  limit: bind-only; consumer: avg_limit.
  avg_limit: bind-only; consumer: witness12.
  avg_limit._simp_1_1: bind-only; consumer: avg_limit.
  limit_sum: bind-only; consumer: witness12.
  witness12: bind-only; consumer: result.
  result: bind-only; consumer: none (designated settlement result).
escape_witness: none under the normalization criterion of CLAUDE.md §3.2.
admission_basis: open-problem-resolution (#15747; Refuted)

Public reuse:
  chi: the public D5/S3/Fourier/FinitePoisson.character at momentum 2 on ZMod 12;
    used directly, with no local character definition.
  Import closure adds one frozen D5 owner and 115 pinned-Mathlib modules.
Representation overlaps (Index = ZMod 12 × (Fin 2 × Fin 2)):
  flat: D5/S3/Quantum/Dynamics/OrderedThreePulseTrace.lean:54, frobMap;
    local binding, unavailable for public reuse.
  flat: D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.lean:132, vec;
    private definition on Fin d, a different index type.
  flat: D5/S3/Quantum/Matrix/CartesianVariance.lean:83, vectorize;
    public definition on Fin n, a different index type.
  hs_inner, identity_inner:
    D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.lean:135, inner_vec;
    private theorem on Fin d, a different index type; identity_inner is its identity case.
  hs_inner, identity_inner: matrix_inner_eq_trace_conjTranspose_mul at
    D5/S3/Observer/Linear/PrimeTimeGramianEnergyIdentity.lean:102,
    D5/S3/QuantumBounds/Designs/MixedStateRobertson.lean:60,
    D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.lean:61,
    D5/S3/Quantum/Tomography/FutureProbabilityResidualCorrelation.lean:62,
    D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes.lean:86,
    D5/S3/Quantum/Measurement/BasisMeasurementProjection.lean:161;
    private theorems on Fin indices with a matrix inner-product structure.
  hs_inner, identity_inner:
    D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.lean:347, hsInner;
    public structure on Fin d matrices, a different index type and representation.
  hs_inner, identity_inner: D5/S3/Quantum/Matrix/CartesianVariance.lean:327, matrix_pairing;
    public theorem on Fin n vectorization, a different index type.
  hs_inner, identity_inner:
    D5/S3/Quantum/Measurements/CompleteContextPurityIdentities.lean:78, hMatrixInner;
    local binding on Fin (n + 1) matrices, unavailable for public reuse.
  F_outer, density_iterate:
    D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.lean:859, density_mulVec;
    local binding, unavailable for public reuse; its diagonal rank-one form and iteration
    use the same Matrix multiplication identities and semiconjugacy principle.
No public exact match at Index was found in the D5 and pinned-Mathlib searches.
The private helpers retain their proof paths to result.
-/

import D5.S3.Fourier.FinitePoisson
import D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section
open scoped BigOperators Topology Matrix
open D5.S3.Fourier
namespace D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity


def angle (φ : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then Real.pi / 4 else Real.pi * (1 + φ) / 4

def coinFlip {d : ℕ} (φ : ℝ) (ψ : ZMod d → Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  fun n c => ∑ b : Fin 2, (D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness.X3
    (angle φ c.1) c.2 b : ℂ) * ψ n (c.1, b)

def shift {d : ℕ} (ψ : ZMod d → Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  fun n c => ψ (n + (if c.2 = 0 then 1 else -1)) c

def swap {d : ℕ} (ψ : ZMod d → Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  fun n c => ψ n (c.2, c.1)

def U {d : ℕ} (φ : ℝ) (ψ : ZMod d → Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  swap (shift (coinFlip φ ψ))

def initial {d : ℕ} (α : Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  fun n c => if n = 0 then α c else 0

def p {d : ℕ} (φ : ℝ) (α : Fin 2 × Fin 2 → ℂ)
    (n : ZMod d) (t : ℕ) : ℝ :=
  ∑ c : Fin 2 × Fin 2, Complex.normSq
    (((U φ)^[t]) (initial (d := d) α) n c)

def avg {d : ℕ} (φ : ℝ) (α : Fin 2 × Fin 2 → ℂ)
    (n : ZMod d) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, p φ α n (t + 1)) / (T : ℝ)

def exceptional (d : ℕ) : Set ℝ :=
  if 12 ∣ d then {0, 1, 2, 4, 5, 6} else {0, 2, 4, 6}

def unitCoin (α : Fin 2 × Fin 2 → ℂ) : Prop :=
  (∑ c : Fin 2 × Fin 2, Complex.normSq (α c)) = 1

def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    ∀ φ : ℝ, φ ∈ Set.Ico 0 8 → φ ∉ exceptional d →
      ∀ α : Fin 2 × Fin 2 → ℂ, unitCoin α →
        ∀ n : ZMod d,
          Filter.Tendsto (avg φ α n) Filter.atTop
            (nhds (1 / (d : ℝ)))

private def a : ℝ := Real.sqrt 2 / 2
private def kappa : ℝ := (Real.sqrt 5 - 1) / 2
private def c : ℝ := a * kappa
private def theta : ℝ := Real.arccos c
private def s : ℝ := Real.sin theta
private def phiStar : ℝ :=
  4 * Real.arccos ((Real.sqrt 2 / 2) * ((Real.sqrt 5 - 1) / 2)) / Real.pi - 1

private theorem a_facts : 2 * a ^ 2 = 1 ∧ 0 < a ∧ a < 1 := by
  unfold a
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hpos := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
  constructor
  · nlinarith only [hsq]
  constructor <;> nlinarith only [hsq, hpos]

private theorem kappa_facts : 0 < kappa ∧ kappa < 1 ∧ kappa ^ 2 + kappa = 1 := by
  have hk : kappa = -Real.goldenConj := by unfold kappa Real.goldenConj; ring
  rw [hk]
  refine ⟨neg_pos.mpr Real.goldenConj_neg, ?_, ?_⟩
  · linarith only [Real.neg_one_lt_goldenConj]
  · nlinarith only [Real.goldenConj_sq]

private theorem c_bounds : 0 < c ∧ c < a := by
  unfold c
  exact ⟨mul_pos a_facts.2.1 kappa_facts.1,
    mul_lt_of_lt_one_right a_facts.2.1 kappa_facts.2.1⟩

private theorem theta_facts : Real.pi / 4 < theta ∧ theta < Real.pi / 2 ∧
    Real.cos theta = c := by
  have ha : Real.arccos a = Real.pi / 4 := by
    unfold a
    rw [← Real.cos_pi_div_four]
    exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hc1 : c ≤ 1 := le_trans c_bounds.2.le a_facts.2.2.le
  have hlo := Real.arccos_lt_arccos (by linarith [c_bounds.1]) c_bounds.2 a_facts.2.2.le
  have hhi := Real.arccos_lt_arccos (by norm_num : (-1 : ℝ) ≤ 0) c_bounds.1 hc1
  rw [ha] at hlo
  rw [Real.arccos_zero] at hhi
  exact ⟨hlo, hhi, Real.cos_arccos (by linarith [c_bounds.1]) hc1⟩

private theorem phi_facts : 0 < phiStar ∧ phiStar < 1 ∧
    Real.pi * (1 + phiStar) / 4 = theta := by
  change 0 < 4 * theta / Real.pi - 1 ∧ 4 * theta / Real.pi - 1 < 1 ∧
    Real.pi * (1 + (4 * theta / Real.pi - 1)) / 4 = theta
  have hlo : 1 < 4 * theta / Real.pi :=
    (lt_div_iff₀ Real.pi_pos).mpr (by linarith [theta_facts.1])
  have hhi : 4 * theta / Real.pi < 2 :=
    (div_lt_iff₀ Real.pi_pos).mpr (by linarith [theta_facts.2.1])
  refine ⟨by linarith only [hlo], by linarith only [hhi], ?_⟩
  field_simp [ne_of_gt Real.pi_pos]
  ring

private theorem phi_nonexceptional : phiStar ∉ exceptional 12 := by
  unfold exceptional
  rw [if_pos (dvd_refl 12)]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  intro h
  rcases h with h | h | h | h | h | h <;> linarith [phi_facts.1, phi_facts.2.1]

private theorem scalar_resonance : c ^ 2 + a * c = 1 / 2 := by
  calc
    c ^ 2 + a * c = a ^ 2 * (kappa ^ 2 + kappa) := by unfold c; ring
    _ = 1 / 2 := by rw [kappa_facts.2.2]; nlinarith only [a_facts.1]

private theorem sin_sq : s ^ 2 + c ^ 2 = 1 := by
  have h := Real.sin_sq_add_cos_sq theta
  rw [theta_facts.2.2] at h
  exact h

private theorem scalar_reductions : c * (a + c) = a ^ 2 ∧ kappa * s ^ 2 = a ^ 2 := by
  constructor
  · nlinarith only [scalar_resonance, a_facts.1]
  · have hkc : kappa * c ^ 2 = kappa - a ^ 2 := by
      unfold c
      linear_combination a ^ 2 * (kappa - 1) * kappa_facts.2.2 + kappa * a_facts.1
    linear_combination kappa * sin_sq - hkc

private def z : ℂ := FinitePoisson.character (2 : ZMod 12) 1

private theorem chi_norm (n : ZMod 12) : ‖FinitePoisson.character (2 : ZMod 12) n‖ = 1 := by
  unfold FinitePoisson.character
  rw [AddChar.mulShift_apply, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

private theorem z_exp : z = Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
  change ZMod.stdAddChar (2 : ZMod 12) = _
  have h := ZMod.stdAddChar_coe (N := 12) (2 : ℤ)
  change ZMod.stdAddChar (2 : ZMod 12) =
    Complex.exp (2 * Real.pi * Complex.I * 2 / 12) at h
  rw [h]
  congr 1
  push_cast
  ring

private theorem z_norm : ‖z‖ = 1 := chi_norm 1

private theorem z_re : z.re = 1 / 2 := by
  rw [z_exp, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]

private theorem z_conj : starRingEnd ℂ z = 1 - z := by
  apply Complex.ext
  · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
    linarith only [z_re]
  · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im]
    ring

private theorem z_unit : z * starRingEnd ℂ z = 1 := by
  rw [Complex.mul_conj', z_norm]
  norm_num

private theorem z_poly : z ^ 2 - z + 1 = 0 := by
  have h := z_unit
  rw [z_conj] at h
  linear_combination -h

private theorem z_ne_zero : z ≠ 0 := by
  intro h
  have hn := z_norm
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

private theorem z_ne_one : z ≠ 1 := by
  intro h
  have hr := z_re
  rw [h, Complex.one_re] at hr
  norm_num at hr

private theorem chi_sum : ∑ n : ZMod 12, FinitePoisson.character (2 : ZMod 12) n = 0 :=
  AddChar.sum_eq_zero_of_ne_one (AddChar.ne_one_iff.mpr ⟨1, z_ne_one⟩)

private theorem chi_neg_one : FinitePoisson.character (2 : ZMod 12) (-1) = starRingEnd ℂ z := by
  rw [(FinitePoisson.character (2 : ZMod 12)).map_neg_eq_inv]
  exact Complex.inv_eq_conj z_norm

private def lam : ℂ := ((a : ℂ) + (c : ℂ)) * z - (c : ℂ)

private theorem resonance : lam * starRingEnd ℂ lam = 1 ∧
    lam ^ 2 + ((c : ℂ) - (a : ℂ)) * lam + 1 = 0 ∧
    lam * ((c : ℂ) + (a : ℂ) * z) = z - 1 := by
  have ha : 2 * (a : ℂ) ^ 2 = 1 := by exact_mod_cast a_facts.1
  have hc := congrArg Complex.ofReal scalar_resonance
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hc
  constructor
  · unfold lam
    simp only [map_sub, map_mul, map_add, Complex.conj_ofReal, z_conj]
    linear_combination -((a : ℂ) + (c : ℂ)) ^ 2 * z_poly + (1 / 2 : ℂ) * ha + hc
  constructor
  · unfold lam
    linear_combination ((a : ℂ) + (c : ℂ)) ^ 2 * z_poly - (1 / 2 : ℂ) * ha - hc
  · unfold lam
    linear_combination (a : ℂ) * ((a : ℂ) + (c : ℂ)) * z_poly +
      ((z - 1) / 2) * ha + (z - 1) * hc

private def B (q : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j => if i.1 = 0 then
    if i.2 = 0 then if j.1 = 0 then (a : ℂ) * q else 0
    else if j.1 = 0 then 0 else if j.2 = 0 then (c : ℂ) * q else (s : ℂ) * q
  else if i.2 = 0 then
    if j.1 = 0 then
      if j.2 = 0 then (a : ℂ) * starRingEnd ℂ q else -(a : ℂ) * starRingEnd ℂ q
    else 0
  else if j.1 = 0 then 0
  else if j.2 = 0 then (s : ℂ) * starRingEnd ℂ q else -(c : ℂ) * starRingEnd ℂ q

private theorem B_apply (q : ℂ) (u : Fin 2 × Fin 2 → ℂ) (i : Fin 2 × Fin 2) :
    (B q *ᵥ u) i =
      if i.1 = 0 then
        if i.2 = 0 then (a : ℂ) * q * (u (0, 0) + u (0, 1))
        else q * ((c : ℂ) * u (1, 0) + (s : ℂ) * u (1, 1))
      else if i.2 = 0 then (a : ℂ) * starRingEnd ℂ q * (u (0, 0) - u (0, 1))
      else starRingEnd ℂ q * ((s : ℂ) * u (1, 0) - (c : ℂ) * u (1, 1)) := by
  rcases i with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  all_goals
    unfold Matrix.mulVec dotProduct
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two]
    dsimp only [B]
    simp only [Fin.ext_iff, Fin.val_zero, one_ne_zero, ite_true, ite_false]
    ring

private theorem mode_step (η : AddChar (ZMod 12) ℂ)
    (hη : η (-1) = starRingEnd ℂ (η 1)) (u : Fin 2 × Fin 2 → ℂ) :
    U phiStar (fun n i => η n * u i) = fun n i => η n * (B (η 1) *ᵥ u) i := by
  funext n i
  rcases i with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  all_goals
    rw [B_apply]
    unfold U swap shift coinFlip
    rw [Fin.sum_univ_two]
  · change (Real.cos (Real.pi / 4) : ℂ) * (η (n + 1) * u (0, 0)) +
      (Real.sin (Real.pi / 4) : ℂ) * (η (n + 1) * u (0, 1)) =
        η n * ((a : ℂ) * η 1 * (u (0, 0) + u (0, 1)))
    rw [show Real.cos (Real.pi / 4) = a from Real.cos_pi_div_four,
      show Real.sin (Real.pi / 4) = a from Real.sin_pi_div_four, η.map_add_eq_mul]
    ring
  · change (Real.cos (Real.pi * (1 + phiStar) / 4) : ℂ) * (η (n + 1) * u (1, 0)) +
      (Real.sin (Real.pi * (1 + phiStar) / 4) : ℂ) * (η (n + 1) * u (1, 1)) =
        η n * (η 1 * ((c : ℂ) * u (1, 0) + (s : ℂ) * u (1, 1)))
    rw [phi_facts.2.2, theta_facts.2.2, show Real.sin theta = s from rfl,
      η.map_add_eq_mul]
    ring
  · change (Real.sin (Real.pi / 4) : ℂ) * (η (n + -1) * u (0, 0)) +
      ((-Real.cos (Real.pi / 4) : ℝ) : ℂ) * (η (n + -1) * u (0, 1)) =
        η n * ((a : ℂ) * starRingEnd ℂ (η 1) * (u (0, 0) - u (0, 1)))
    rw [show Real.sin (Real.pi / 4) = a from Real.sin_pi_div_four,
      show Real.cos (Real.pi / 4) = a from Real.cos_pi_div_four,
      Complex.ofReal_neg, η.map_add_eq_mul, hη]
    ring
  · change (Real.sin (Real.pi * (1 + phiStar) / 4) : ℂ) * (η (n + -1) * u (1, 0)) +
      ((-Real.cos (Real.pi * (1 + phiStar) / 4) : ℝ) : ℂ) * (η (n + -1) * u (1, 1)) =
        η n * (starRingEnd ℂ (η 1) * ((s : ℂ) * u (1, 0) - (c : ℂ) * u (1, 1)))
    rw [phi_facts.2.2, theta_facts.2.2, show Real.sin theta = s from rfl,
      Complex.ofReal_neg, η.map_add_eq_mul, hη]
    ring

private theorem character_mode (u : Fin 2 × Fin 2 → ℂ) :
    U phiStar (fun n i => FinitePoisson.character (2 : ZMod 12) n * u i) =
      fun n i => FinitePoisson.character (2 : ZMod 12) n * (B z *ᵥ u) i :=
  mode_step (FinitePoisson.character (2 : ZMod 12)) chi_neg_one u

private theorem trivial_mode (u : Fin 2 × Fin 2 → ℂ) :
    U (d := 12) phiStar (fun _ i => u i) = fun _ i => (B 1 *ᵥ u) i := by
  simpa only [AddChar.one_apply, one_mul] using
    mode_step (1 : AddChar (ZMod 12) ℂ) (by simp only [AddChar.one_apply, map_one]) u


private def v (i : Fin 2 × Fin 2) : ℂ :=
  if i.1 = 0 then if i.2 = 0 then a else lam - a
  else if i.2 = 0 then -lam - c else -s

private def w (i : Fin 2 × Fin 2) : ℂ :=
  if i.1 = 0 then if i.2 = 0 then a else (c : ℂ) * z
  else if i.2 = 0 then -c else (kappa : ℂ) * s * z

private theorem eigenvectors : B 1 *ᵥ v = lam • v ∧ B z *ᵥ w = lam • w := by
  have ha : 2 * (a : ℂ) ^ 2 = 1 := by exact_mod_cast a_facts.1
  have hs : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast sin_sq
  have hc : (c : ℂ) * ((a : ℂ) + c) = (a : ℂ) ^ 2 := by
    exact_mod_cast scalar_reductions.1
  have hk : (kappa : ℂ) * (s : ℂ) ^ 2 = (a : ℂ) ^ 2 := by
    exact_mod_cast scalar_reductions.2
  have hca : (c : ℂ) = (a : ℂ) * kappa := by unfold c; push_cast; rfl
  have hr := resonance.2.2
  unfold lam at hr
  constructor
  · ext ⟨i, j⟩
    rw [B_apply]
    fin_cases i <;> fin_cases j
    all_goals
      unfold v
      simp only [Pi.smul_apply, smul_eq_mul, Fin.ext_iff, Fin.val_zero,
        one_ne_zero, ite_true, ite_false, map_one, mul_one, one_mul]
    · ring
    · linear_combination -resonance.2.1 - hs
    · linear_combination resonance.2.1 + ha
    · ring
  · ext ⟨i, j⟩
    rw [B_apply]
    fin_cases i <;> fin_cases j
    all_goals
      unfold w
      simp only [Pi.smul_apply, smul_eq_mul, Fin.ext_iff, Fin.val_zero,
        one_ne_zero, ite_true, ite_false, z_conj]
      unfold lam
    · linear_combination (a : ℂ) * (c : ℂ) * z_poly
    · linear_combination z ^ 2 * hk - z ^ 2 * hc
    · linear_combination hr - (a : ℂ) ^ 2 * z_poly - (z - 1) * ha
    · rw [hca]
      linear_combination -(a : ℂ) * (kappa : ℂ) * (s : ℂ) * z_poly

private theorem coin_overlap :
    (∑ i : Fin 2 × Fin 2, starRingEnd ℂ (v i) * w i) =
      (3 / 2 : ℂ) * starRingEnd ℂ z := by
  have ha : 2 * (a : ℂ) ^ 2 = 1 := by exact_mod_cast a_facts.1
  have hc : (c : ℂ) * ((a : ℂ) + c) = (a : ℂ) ^ 2 := by
    exact_mod_cast scalar_reductions.1
  have hk : (kappa : ℂ) * (s : ℂ) ^ 2 = (a : ℂ) ^ 2 := by
    exact_mod_cast scalar_reductions.2
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  change starRingEnd ℂ (a : ℂ) * a +
    starRingEnd ℂ (lam - a) * ((c : ℂ) * z) +
    (starRingEnd ℂ (-lam - c) * (-c) +
    starRingEnd ℂ (-s : ℂ) * ((kappa : ℂ) * s * z)) = _
  simp only [map_sub, map_neg, Complex.conj_ofReal]
  unfold lam
  simp only [map_sub, map_mul, map_add, Complex.conj_ofReal, z_conj]
  linear_combination -(c : ℂ) * ((a : ℂ) + c) * z_poly +
    (2 - 2 * z) * hc - z * hk + (3 / 2 : ℂ) * (1 - z) * ha

private abbrev Index := ZMod 12 × (Fin 2 × Fin 2)
private abbrev H := EuclideanSpace ℂ Index
private abbrev K := EuclideanSpace ℂ (Index × Index)

private theorem coin_inner (θ : ℝ) (x y : Fin 2 → ℂ) :
    (∑ i : Fin 2,
      starRingEnd ℂ (∑ j : Fin 2,
        (D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness.X3 θ i j : ℂ) * x j) *
      (∑ j : Fin 2,
        (D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness.X3 θ i j : ℂ) * y j)) =
      ∑ i : Fin 2, starRingEnd ℂ (x i) * y i := by
  have h : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  simp only [Fin.sum_univ_two]
  change starRingEnd ℂ ((Real.cos θ : ℂ) * x 0 + (Real.sin θ : ℂ) * x 1) *
      ((Real.cos θ : ℂ) * y 0 + (Real.sin θ : ℂ) * y 1) +
    starRingEnd ℂ ((Real.sin θ : ℂ) * x 0 + ((-Real.cos θ : ℝ) : ℂ) * x 1) *
      ((Real.sin θ : ℂ) * y 0 + ((-Real.cos θ : ℝ) : ℂ) * y 1) = _
  simp only [Complex.ofReal_neg, map_add, map_neg, map_mul, Complex.conj_ofReal]
  linear_combination (starRingEnd ℂ (x 0) * y 0 + starRingEnd ℂ (x 1) * y 1) * h

private theorem walk_inner (x y : ZMod 12 → Fin 2 × Fin 2 → ℂ) :
    (∑ n, ∑ i, starRingEnd ℂ (U phiStar x n i) * U phiStar y n i) =
      ∑ n, ∑ i, starRingEnd ℂ (x n i) * y n i := by
  calc
    _ = ∑ i : Fin 2 × Fin 2, ∑ n : ZMod 12,
        starRingEnd ℂ (coinFlip phiStar x
          (n + (if i.1 = 0 then 1 else -1)) (i.2, i.1)) *
        coinFlip phiStar y (n + (if i.1 = 0 then 1 else -1)) (i.2, i.1) := by
      rw [Finset.sum_comm]; rfl
    _ = ∑ i : Fin 2 × Fin 2, ∑ n : ZMod 12,
        starRingEnd ℂ (coinFlip phiStar x n (i.2, i.1)) *
        coinFlip phiStar y n (i.2, i.1) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp (Equiv.addRight (if i.1 = 0 then (1 : ZMod 12) else -1))
        (fun n => starRingEnd ℂ (coinFlip phiStar x n (i.2, i.1)) *
          coinFlip phiStar y n (i.2, i.1))
    _ = ∑ n : ZMod 12, ∑ i : Fin 2 × Fin 2,
        starRingEnd ℂ (coinFlip phiStar x n i) * coinFlip phiStar y n i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n _
      exact (Equiv.prodComm (Fin 2) (Fin 2)).sum_comp
        (fun i => starRingEnd ℂ (coinFlip phiStar x n i) * coinFlip phiStar y n i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      exact coin_inner (angle phiStar i) (fun j => x n (i, j)) (fun j => y n (i, j))

private def walkLin : H →ₗ[ℂ] H where
  toFun x := WithLp.toLp 2 (fun i => U phiStar (fun n j => x (n, j)) i.1 i.2)
  map_add' x y := by
    ext ⟨n, i, j⟩
    change U phiStar (fun n j => x (n, j) + y (n, j)) n (i, j) =
      U phiStar (fun n j => x (n, j)) n (i, j) + U phiStar (fun n j => y (n, j)) n (i, j)
    unfold U swap shift coinFlip
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    ext ⟨n, i, j⟩
    change U phiStar (fun n j => r * x (n, j)) n (i, j) =
      r * U phiStar (fun n j => x (n, j)) n (i, j)
    unfold U swap shift coinFlip
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring

private def walkIso : H →ₗᵢ[ℂ] H := walkLin.isometryOfInner (by
  intro x y
  unfold walkLin
  simp only [PiLp.inner_apply, RCLike.inner_apply', LinearMap.coe_mk,
    AddHom.coe_mk, Fintype.sum_prod_type]
  simpa only [Fintype.sum_prod_type] using walk_inner (fun n j => x (n, j)) (fun n j => y (n, j)))

private def walkEquiv : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective walkIso
    (LinearMap.surjective_of_injective walkIso.injective)

private def M : Matrix Index Index ℂ :=
  walkEquiv.toLinearEquiv.toLinearMap.toMatrix
    (EuclideanSpace.basisFun Index ℂ).toBasis (EuclideanSpace.basisFun Index ℂ).toBasis

private theorem M_unitary : Mᴴ * M = 1 ∧ M * Mᴴ = 1 := by
  exact walkEquiv.toMatrix_mem_unitaryGroup
    (EuclideanSpace.basisFun Index ℂ) (EuclideanSpace.basisFun Index ℂ)

private theorem M_step (x : H) :
    M *ᵥ (fun i => x i) = fun i => U phiStar (fun n j => x (n, j)) i.1 i.2 := by
  exact walkEquiv.toLinearEquiv.toLinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun Index ℂ).toBasis
    (EuclideanSpace.basisFun Index ℂ).toBasis x

private def flat (A : Matrix Index Index ℂ) : K :=
  WithLp.toLp 2 (fun i => A i.1 i.2)
private def mat (A : K) : Matrix Index Index ℂ := fun i j => A (i, j)

private theorem hs_inner (A B : K) : inner ℂ A B = ((mat A)ᴴ * mat B).trace := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  change (∑ i : Index, ∑ j : Index, B (i, j) * starRingEnd ℂ (A (i, j))) =
    ∑ i : Index, ∑ j : Index, starRingEnd ℂ (A (j, i)) * B (j, i)
  rw [Finset.sum_comm]
  simp only [mul_comm]

private def conjugateLin : K →ₗ[ℂ] K where
  toFun A := flat (M * mat A * Mᴴ)
  map_add' A B := by
    change flat (M * (mat A + mat B) * Mᴴ) = flat (M * mat A * Mᴴ) + flat (M * mat B * Mᴴ)
    rw [Matrix.mul_add, Matrix.add_mul]
    rfl
  map_smul' r A := by
    change flat (M * (r • mat A) * Mᴴ) = r • flat (M * mat A * Mᴴ)
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl

private def F : K →ₗᵢ[ℂ] K := conjugateLin.isometryOfInner (by
  intro A B
  rw [hs_inner, hs_inner]
  change ((M * mat A * Mᴴ)ᴴ * (M * mat B * Mᴴ)).trace = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Mᴴ M, M_unitary.1, Matrix.one_mul]
  rw [Matrix.trace_mul_comm M]
  simp only [Matrix.mul_assoc, M_unitary.1, Matrix.mul_one])

private def E : Submodule ℂ K := F.toContinuousLinearMap.eqLocus 1
private def Q : K →L[ℂ] K := E.starProjection

private theorem QF (A : K) : Q (F A) = Q A := by
  apply E.eq_starProjection_of_mem_of_inner_eq_zero (E.starProjection_apply_mem A)
  intro Z hZ
  have hz : F Z = Z := hZ
  have hi : inner ℂ (F A) Z = inner ℂ A Z := by
    calc
      _ = inner ℂ (F A) (F Z) := congrArg (inner ℂ (F A)) hz.symm
      _ = _ := F.inner_map_map A Z
  rw [inner_sub_left, hi]
  have h := E.starProjection_inner_eq_zero A Z hZ
  rw [inner_sub_left] at h
  exact h

private def identity : K := flat 1
private def P : K := flat (Matrix.diagonal (fun i : Index => if i.1 = 0 then 1 else 0))
private def outer (x y : H) : K :=
  flat (Matrix.vecMulVec (fun i => x i) (fun i => starRingEnd ℂ (y i)))

private theorem F_identity : F identity = identity := by
  change flat (M * 1 * Mᴴ) = flat 1
  rw [Matrix.mul_one, M_unitary.2]

private theorem identity_inner (A : K) : inner ℂ identity A = (mat A).trace := by
  rw [hs_inner]
  change ((1 : Matrix Index Index ℂ)ᴴ * mat A).trace = _
  rw [Matrix.conjTranspose_one, Matrix.one_mul]

private theorem F_outer (x y : H) : F (outer x y) = outer (walkIso x) (walkIso y) := by
  change flat (M * Matrix.vecMulVec (fun i => x i) (fun i => starRingEnd ℂ (y i)) * Mᴴ) = _
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  have hy : (fun i => starRingEnd ℂ (y i)) ᵥ* Mᴴ =
      fun j => starRingEnd ℂ ((M *ᵥ (fun i => y i)) j) := by
    funext j
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      map_sum, map_mul, starRingEnd_apply]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hy, M_step x, M_step y]
  rfl

private theorem P_inner (A : K) :
    inner ℂ P A = ∑ j : Fin 2 × Fin 2, A ((0, j), (0, j)) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  change (∑ i : Index, ∑ j : Index,
    A (i, j) * starRingEnd ℂ (Matrix.diagonal
      (fun k : Index => if k.1 = 0 then (1 : ℂ) else 0) i j)) = _
  simp only [Matrix.diagonal_apply, apply_ite, map_zero, map_one, mul_one,
    mul_zero, Fintype.sum_ite_eq]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fintype.sum_ite_eq']

private def f : H := WithLp.toLp 2 (fun i => v i.2)
private def g : H := WithLp.toLp 2 (fun i => FinitePoisson.character (2 : ZMod 12) i.1 * w i.2)
private def X : K := outer f g
private def Y : K := (1 / 12 : ℂ) • identity

private theorem global_eigenvectors : walkIso f = lam • f ∧ walkIso g = lam • g := by
  constructor
  · ext ⟨n, j⟩
    change U phiStar (fun _ i => v i) n j = lam * v j
    rw [trivial_mode, eigenvectors.1]
    rfl
  · ext ⟨n, j⟩
    change U phiStar (fun n i => FinitePoisson.character (2 : ZMod 12) n * w i) n j =
      lam * (FinitePoisson.character (2 : ZMod 12) n * w j)
    rw [character_mode, eigenvectors.2]
    change FinitePoisson.character (2 : ZMod 12) n * (lam * w j) = _
    ring

private theorem X_fixed : F X = X := by
  rw [X, F_outer, global_eigenvectors.1, global_eigenvectors.2]
  ext ⟨i, j⟩
  change (lam * f i) * starRingEnd ℂ (lam * g j) = f i * starRingEnd ℂ (g j)
  rw [map_mul]
  calc
    _ = (lam * starRingEnd ℂ lam) * (f i * starRingEnd ℂ (g j)) := by ring
    _ = _ := by rw [resonance.1, one_mul]

private theorem X_pairings : inner ℂ X identity = 0 ∧ inner ℂ X P ≠ 0 := by
  constructor
  · have htr : (mat X).trace = 0 := by
      change (∑ i : Index, v i.2 *
        starRingEnd ℂ (FinitePoisson.character (2 : ZMod 12) i.1 * w i.2)) = 0
      rw [Fintype.sum_prod_type]
      simp only [map_mul]
      calc
        _ = (∑ n : ZMod 12, starRingEnd ℂ (FinitePoisson.character (2 : ZMod 12) n)) *
            (∑ j : Fin 2 × Fin 2, v j * starRingEnd ℂ (w j)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro n _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 0 := by rw [← map_sum, chi_sum, map_zero, zero_mul]
    rw [← inner_conj_symm, identity_inner, htr, map_zero]
  · rw [← inner_conj_symm, P_inner]
    change starRingEnd ℂ (∑ j, v j *
      starRingEnd ℂ (FinitePoisson.character (2 : ZMod 12) 0 * w j)) ≠ 0
    simp only [AddChar.map_zero_eq_one, one_mul, map_sum, map_mul, Complex.conj_conj]
    rw [coin_overlap]
    exact mul_ne_zero (by norm_num) ((map_ne_zero (starRingEnd ℂ)).mpr z_ne_zero)

private theorem baseline : F Y = Y ∧ inner ℂ Y P = 1 / 3 ∧ ‖Y‖ ^ 2 = 1 / 3 := by
  have hp : (mat P).trace = 4 := by
    change (Matrix.diagonal (fun i : Index => if i.1 = 0 then (1 : ℂ) else 0)).trace = 4
    rw [Matrix.trace_diagonal, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Fintype.sum_ite_eq', Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num
  have hi : inner ℂ identity identity = 48 := by
    rw [identity_inner]
    change (1 : Matrix Index Index ℂ).trace = 48
    rw [Matrix.trace_one]
    norm_num only [Fintype.card_prod, ZMod.card, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩
  · change F ((1 / 12 : ℂ) • identity) = (1 / 12 : ℂ) • identity
    rw [map_smul, F_identity]
  · rw [Y, inner_smul_left, identity_inner, hp]
    norm_num [map_ofNat]
  · rw [@norm_sq_eq_re_inner ℂ, Y, inner_smul_left, inner_smul_right, hi]
    norm_num

private theorem projection_pairing (Z A : K) (hZ : F Z = Z) :
    inner ℂ Z (Q A) = inner ℂ Z A := by
  have hz : Z ∈ E := hZ
  change inner ℂ Z (E.starProjection A) = inner ℂ Z A
  rw [← E.inner_starProjection_left_eq_right, E.starProjection_eq_self_iff.mpr hz]

private theorem strict_surplus : 1 / 3 < ‖Q P‖ ^ 2 := by
  have hne : Q P - Y ≠ 0 := by
    intro h
    have he : Q P = Y := sub_eq_zero.mp h
    have hxp := projection_pairing X P X_fixed
    rw [he, Y, inner_smul_right, X_pairings.1, mul_zero] at hxp
    exact X_pairings.2 hxp.symm
  have horth : inner ℂ Y (Q P - Y) = 0 := by
    rw [inner_sub_right, projection_pairing Y P baseline.1, baseline.2.1]
    have hy : inner ℂ Y Y = (1 / 3 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, baseline.2.2]
      norm_num
    rw [hy, sub_self]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero Y (Q P - Y) horth
  rw [add_sub_cancel] at hp
  simp only [← pow_two] at hp
  rw [baseline.2.2] at hp
  have hpos : 0 < ‖Q P - Y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  linarith only [hp, hpos]

private def basisCoin (j i : Fin 2 × Fin 2) : ℂ := if i = j then 1 else 0
private def b (j : Fin 2 × Fin 2) : H :=
  WithLp.toLp 2 (fun i => initial (basisCoin j) i.1 i.2)

private theorem basis_unit (j : Fin 2 × Fin 2) : unitCoin (basisCoin j) := by
  unfold unitCoin basisCoin
  simp only [apply_ite, Complex.normSq_one, Complex.normSq_zero, Fintype.sum_ite_eq']

private theorem P_sum : P = ∑ j : Fin 2 × Fin 2, outer (b j) (b j) := by
  ext ⟨⟨n, i⟩, ⟨m, j⟩⟩
  change Matrix.diagonal (fun k : Index => if k.1 = 0 then (1 : ℂ) else 0) (n, i) (m, j) =
    ∑ k : Fin 2 × Fin 2,
      (if n = 0 then basisCoin k i else 0) * starRingEnd ℂ (if m = 0 then basisCoin k j else 0)
  rw [Matrix.diagonal_apply]
  by_cases hn : n = 0 <;> by_cases hm : m = 0
  · subst n; subst m
    simp only [Prod.mk.injEq, true_and, ite_true]
    change (if i = j then (1 : ℂ) else 0) =
      ∑ k : Fin 2 × Fin 2, (if i = k then (1 : ℂ) else 0) *
        starRingEnd ℂ (if j = k then 1 else 0)
    simp only [apply_ite, map_one, map_zero, mul_one, mul_zero, Fintype.sum_ite_eq]
    split_ifs <;> rfl
  · have hnm : (n, i) ≠ (m, j) := by intro h; exact hm ((congrArg Prod.fst h).symm.trans hn)
    simp only [hnm, ite_false, hm, map_zero, mul_zero, Finset.sum_const_zero]
  · have hnm : (n, i) ≠ (m, j) := by intro h; exact hn ((congrArg Prod.fst h).trans hm)
    simp only [hnm, ite_false, hn, zero_mul, Finset.sum_const_zero]
  · by_cases hnm : (n, i) = (m, j) <;>
      simp only [hnm, hn, hm, ite_true, ite_false, zero_mul, Finset.sum_const_zero]

private theorem walk_iterate (α : Fin 2 × Fin 2 → ℂ) (t : ℕ) :
    ((walkIso : H → H)^[t]) (WithLp.toLp 2 (fun i => initial α i.1 i.2)) =
      WithLp.toLp 2 (fun i => ((U phiStar)^[t]) (initial α) i.1 i.2) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    rfl

private theorem probability_norm (α : Fin 2 × Fin 2 → ℂ) (n : ZMod 12) (t : ℕ) :
    p phiStar α n t = ‖WithLp.toLp 2 (fun j : Fin 2 × Fin 2 =>
      ((walkIso : H → H)^[t]) (WithLp.toLp 2 (fun i => initial α i.1 i.2)) (n, j))‖ ^ 2 := by
  rw [walk_iterate, PiLp.norm_sq_eq_of_L2]
  unfold p
  simp only [Complex.normSq_eq_norm_sq]

private theorem density_iterate (x : H) (t : ℕ) :
    ((F : K → K)^[t]) (outer x x) =
      outer (((walkIso : H → H)^[t]) x) (((walkIso : H → H)^[t]) x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, F_outer, Function.iterate_succ_apply']

private theorem density_probability (j : Fin 2 × Fin 2) (t : ℕ) :
    (inner ℂ P (((F : K → K)^[t]) (outer (b j) (b j)))).re =
      p phiStar (basisCoin j) (0 : ZMod 12) t := by
  rw [density_iterate, P_inner, probability_norm, PiLp.norm_sq_eq_of_L2]
  change (∑ i : Fin 2 × Fin 2,
    (((walkIso : H → H)^[t]) (b j)) (0, i) *
      starRingEnd ℂ ((((walkIso : H → H)^[t]) (b j)) (0, i))).re =
    ∑ i : Fin 2 × Fin 2, ‖(((walkIso : H → H)^[t]) (b j)) (0, i)‖ ^ 2
  simp only [Complex.mul_conj, Complex.re_sum, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private theorem avg_observable (j : Fin 2 × Fin 2) (T : ℕ) :
    avg phiStar (basisCoin j) (0 : ZMod 12) T =
      (inner ℂ P (birkhoffAverage ℂ F id T (F (outer (b j) (b j))))).re := by
  unfold avg birkhoffAverage birkhoffSum
  rw [inner_smul_right, inner_sum]
  have hinv : (T : ℂ)⁻¹ = (((T : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [hinv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_sum, id_eq]
  rw [div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [← Function.iterate_succ_apply, density_probability]

private def limit (j : Fin 2 × Fin 2) : ℝ :=
  (inner ℂ P (Q (outer (b j) (b j)))).re

private theorem avg_limit (j : Fin 2 × Fin 2) :
    Filter.Tendsto (avg phiStar (basisCoin j) (0 : ZMod 12)) Filter.atTop (nhds (limit j)) := by
  have hf : ‖F.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro A
    change ‖F A‖ ≤ 1 * ‖A‖
    rw [F.norm_map, one_mul]
  have hmean := F.toContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection hf
    (F (outer (b j) (b j)))
  change Filter.Tendsto (fun T => birkhoffAverage ℂ F id T (F (outer (b j) (b j))))
    Filter.atTop (nhds (Q (F (outer (b j) (b j))))) at hmean
  rw [QF] at hmean
  have hobs : Continuous (fun A : K => (inner ℂ P A).re) :=
    Complex.continuous_re.comp (continuous_const.inner continuous_id)
  have h := (hobs.tendsto _).comp hmean
  change Filter.Tendsto (fun T =>
    (inner ℂ P (birkhoffAverage ℂ F id T (F (outer (b j) (b j))))).re)
    Filter.atTop (nhds (limit j)) at h
  simpa only [← avg_observable] using h

private theorem limit_sum : ∑ j : Fin 2 × Fin 2, limit j = ‖Q P‖ ^ 2 := by
  unfold limit
  rw [← Complex.re_sum, ← inner_sum, ← map_sum, ← P_sum]
  have h := projection_pairing (Q P) P (E.starProjection_apply_mem P)
  have hi : inner ℂ P (Q P) = inner ℂ (Q P) (Q P) := by
    calc
      _ = inner ℂ (Q P) P := (E.inner_starProjection_left_eq_right P P).symm
      _ = _ := h.symm
  rw [hi]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (Q P)).symm

private theorem witness12 : phiStar ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∃ (j : Fin 2 × Fin 2) (L : ℝ), 1 / (12 : ℝ) < L ∧
      Filter.Tendsto (avg (d := 12) phiStar (fun i => if i = j then 1 else 0) 0)
        Filter.atTop (nhds L) := by
  refine ⟨⟨phi_facts.1, phi_facts.2.1⟩, ?_⟩
  have hex : ∃ j : Fin 2 × Fin 2, 1 / (12 : ℝ) < limit j := by
    by_contra h
    push Not at h
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)
    rw [limit_sum] at hs
    norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul] at hs
    linarith only [strict_surplus, hs]
  obtain ⟨j, hj⟩ := hex
  exact ⟨j, limit j, hj, avg_limit j⟩

theorem result : ¬ claim := by
  intro h
  obtain ⟨hφ, j, L, hL, ht⟩ := witness12
  have hu := h 12 (by norm_num) phiStar ⟨hφ.1.le, by linarith only [hφ.2]⟩
    phi_nonexceptional (basisCoin j) (basis_unit j) 0
  have he := tendsto_nhds_unique ht hu
  exact (ne_of_gt hL) he

end D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity
