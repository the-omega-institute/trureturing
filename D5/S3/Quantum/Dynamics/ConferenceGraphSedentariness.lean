/- GID: D5/S3/Quantum/Dynamics/ConferenceGraphSedentariness
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/ConferenceGraphSedentariness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Conference walks have sharp square-order floors and nonsquare vanishing infima. -/

import D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
import D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation
import D5.S3.Fourier.PositiveFourierApproximationRefutation
import D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality

/-! Sharp return probabilities for strongly regular conference graphs. -/

noncomputable section

namespace D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness

open Matrix Complex Real Set Filter
open scoped BigOperators Topology
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow (hamiltonianPropagator)
open D5.S3.Quantum.Dynamics.RationalWeightPathTransfer (hamiltonianPropagator_neg)

/-- The pointwise sharp classification and the absence of a uniform family floor. -/
def claim : Prop :=
  (∀ (m : ℕ), 1 ≤ m → ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m → ∀ u : V,
    (IsSquare (4 * m + 1) →
      (∀ t : ℝ, 1 / (4 * (m : ℝ) + 1) ^ 2 ≤
        ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2) ∧
      (∃ t : ℝ, 0 < t ∧ ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2 =
        1 / (4 * (m : ℝ) + 1) ^ 2)) ∧
    (¬ IsSquare (4 * m + 1) →
      (∀ t : ℝ, 0 ≤ ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2) ∧
      ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧
        ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2 < ε)) ∧
  ∀ c : ℝ, 0 < c → ∃ N : ℕ, ∀ (m : ℕ), 1 ≤ m → N ≤ 4 * m + 1 →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m → ∀ u : V,
    ∃ t : ℝ, 0 < t ∧ ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2 < c

private lemma conference_identity {m : ℕ} (hm : 1 ≤ m)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m) :
    G.adjMatrix ℂ * G.adjMatrix ℂ =
      (m : ℂ) • (1 : Matrix V V ℂ) - G.adjMatrix ℂ +
        (m : ℂ) • Matrix.of (fun _ _ => (1 : ℂ)) := by
  have hcomp := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one ℂ
  rw [G.compl_adjMatrix_eq_adjMatrix_compl ℂ] at hcomp
  simp only [Pi.one_def] at hcomp
  have hc : Gᶜ.adjMatrix ℂ = Matrix.of (fun _ _ => (1 : ℂ)) - 1 - G.adjMatrix ℂ := by
    rw [← hcomp]
    abel
  rw [← pow_two, hG.matrix_eq, hc, ← Nat.cast_smul_eq_nsmul ℂ,
    ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [Nat.cast_sub hm]
  push_cast
  module

private lemma conference_projectors {m : ℕ} (hm : 1 ≤ m)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m) :
    let n : ℂ := 4 * (m : ℂ) + 1
    let r : ℂ := (Real.sqrt (4 * (m : ℝ) + 1) : ℝ)
    let θ : ℂ := (-1 + r) / 2
    let τ : ℂ := (-1 - r) / 2
    let P : Matrix V V ℂ := n⁻¹ • Matrix.of (fun _ _ => (1 : ℂ))
    let Q := 1 - P
    let B := G.adjMatrix ℂ - (2 * (m : ℂ)) • P
    let E := r⁻¹ • (B - τ • Q)
    let F := r⁻¹ • (θ • Q - B)
    P * P = P ∧ E * E = E ∧ F * F = F ∧
      P * E = 0 ∧ E * P = 0 ∧ P * F = 0 ∧ F * P = 0 ∧ E * F = 0 ∧ F * E = 0 ∧
      P + E + F = 1 ∧ G.adjMatrix ℂ = (2 * (m : ℂ)) • P + θ • E + τ • F ∧
      ∀ u : V, P u u = 1 / n ∧ E u u = 2 * (m : ℂ) / n ∧
        F u u = 2 * (m : ℂ) / n := by
  let n : ℂ := 4 * (m : ℂ) + 1
  let r : ℂ := (Real.sqrt (4 * (m : ℝ) + 1) : ℝ)
  let θ : ℂ := (-1 + r) / 2
  let τ : ℂ := (-1 - r) / 2
  let J : Matrix V V ℂ := Matrix.of (fun _ _ => 1)
  let A := G.adjMatrix ℂ
  let P := n⁻¹ • J
  let Q := 1 - P
  let B := A - (2 * (m : ℂ)) • P
  let E := r⁻¹ • (B - τ • Q)
  let F := r⁻¹ • (θ • Q - B)
  change P * P = P ∧ E * E = E ∧ F * F = F ∧
    P * E = 0 ∧ E * P = 0 ∧ P * F = 0 ∧ F * P = 0 ∧ E * F = 0 ∧ F * E = 0 ∧
    P + E + F = 1 ∧ A = (2 * (m : ℂ)) • P + θ • E + τ • F ∧
    ∀ u : V, P u u = 1 / n ∧ E u u = 2 * (m : ℂ) / n ∧ F u u = 2 * (m : ℂ) / n
  have hn : n ≠ 0 := by
    have hn' : (4 * (m : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
    dsimp only [n]
    exact_mod_cast hn'
  have hr : r ≠ 0 := by
    have hr' : Real.sqrt (4 * (m : ℝ) + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    dsimp only [r]
    exact_mod_cast hr'
  have hrr : r * r = n := by
    dsimp only [r, n]
    exact_mod_cast Real.mul_self_sqrt (by positivity : 0 ≤ 4 * (m : ℝ) + 1)
  have hsum : θ + τ = -1 := by dsimp [θ, τ]; ring
  have hdiff : θ - τ = r := by dsimp [θ, τ]; ring
  have hprod : θ * τ = -(m : ℂ) := by
    dsimp [θ, τ]
    dsimp [n] at hrr
    linear_combination -hrr / 4
  have hAJ : A * J = (2 * (m : ℂ)) • J := by
    ext i j
    have h := G.adjMatrix_mulVec_const_apply_of_regular (α := ℂ) (a := 1) (v := i)
      hG.regular
    change (G.adjMatrix ℂ *ᵥ Function.const V (1 : ℂ)) i = (2 * (m : ℂ)) * 1
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  have hJA : J * A = (2 * (m : ℂ)) • J := by
    have h := congrArg Matrix.transpose hAJ
    have hJT : Jᵀ = J := Matrix.transpose_replicateCol (fun _ : V => (1 : ℂ))
    have hAT : Aᵀ = A := G.transpose_adjMatrix
    rw [Matrix.transpose_mul, Matrix.transpose_smul, hJT, hAT] at h
    exact h
  have hPP : P * P = P := by
    have hp := D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.P_sq
      (Fintype.card V) (by rw [hG.card]; omega)
    have he := congrArg (Matrix.reindexAlgEquiv ℝ ℂ (Fintype.equivFin V).symm) hp
    change (n⁻¹ • Matrix.of (fun _ _ : V => (1 : ℂ))) *
      (n⁻¹ • Matrix.of (fun _ _ : V => (1 : ℂ))) =
        n⁻¹ • Matrix.of (fun _ _ : V => (1 : ℂ))
    simpa [map_mul, map_smul, Matrix.reindex_apply, Matrix.submatrix,
      RCLike.real_smul_eq_coe_smul (K := ℂ), hG.card, n, Pi.smul_def, smul_eq_mul] using he
  have hAP : A * P = (2 * (m : ℂ)) • P := by
    dsimp [P]
    rw [Matrix.mul_smul, hAJ]
    module
  have hPA : P * A = (2 * (m : ℂ)) • P := by
    dsimp [P]
    rw [Matrix.smul_mul, hJA]
    module
  have hJP : J = n • P := by
    dsimp [P]
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hAA : A * A = (m : ℂ) • (1 : Matrix V V ℂ) - A + (m * n) • P := by
    have h := conference_identity hm G hG
    change A * A = (m : ℂ) • (1 : Matrix V V ℂ) - A + (m : ℂ) • J at h
    rw [hJP, smul_smul] at h
    exact h
  have hBP : B * P = 0 := by
    dsimp [B]
    rw [sub_mul, Matrix.smul_mul, hAP, hPP, sub_self]
  have hPB : P * B = 0 := by
    dsimp [B]
    rw [mul_sub, Matrix.mul_smul, hPA, hPP, sub_self]
  have hQQ : Q * Q = Q := IsIdempotentElem.one_sub hPP
  have hBQ : B * Q = B := by dsimp [Q]; rw [mul_sub, mul_one, hBP, sub_zero]
  have hQB : Q * B = B := by dsimp [Q]; rw [sub_mul, one_mul, hPB, sub_zero]
  have hBB : B * B = (m : ℂ) • Q - B := by
    dsimp [B, Q]
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, hAA, hAP, hPA, hPP, smul_smul]
    dsimp [n]
    module
  have hQE : Q * E = E := by
    dsimp [E]
    rw [Matrix.mul_smul, mul_sub, Matrix.mul_smul, hQB, hQQ]
  have hQF : Q * F = F := by
    dsimp [F]
    rw [Matrix.mul_smul, mul_sub, Matrix.mul_smul, hQB, hQQ]
  have hBE : B * E = θ • E := by
    calc
      B * E = r⁻¹ • ((m : ℂ) • Q - B - τ • B) := by
        dsimp only [E]
        rw [Matrix.mul_smul, mul_sub, Matrix.mul_smul, hBQ, hBB]
      _ = r⁻¹ • ((-1 - τ) • B + (m : ℂ) • Q) := by module
      _ = r⁻¹ • (θ • B - (θ * τ) • Q) := by
        rw [show -1 - τ = θ by linear_combination -hsum, hprod]
        module
      _ = θ • E := by dsimp only [E]; module
  have hBF : B * F = τ • F := by
    calc
      B * F = r⁻¹ • (θ • B - ((m : ℂ) • Q - B)) := by
        dsimp only [F]
        rw [Matrix.mul_smul, mul_sub, Matrix.mul_smul, hBQ, hBB]
      _ = r⁻¹ • ((θ + 1) • B - (m : ℂ) • Q) := by module
      _ = r⁻¹ • ((-τ) • B + (θ * τ) • Q) := by
        rw [show θ + 1 = -τ by linear_combination hsum, hprod]
        module
      _ = τ • F := by dsimp only [F]; module
  have hEE : E * E = E := by
    calc
      E * E = r⁻¹ • ((θ - τ) • E) := by
        conv_lhs => lhs; dsimp only [E]
        rw [Matrix.smul_mul, sub_mul, Matrix.smul_mul, hBE, hQE, sub_smul]
      _ = E := by rw [hdiff, smul_smul, inv_mul_cancel₀ hr, one_smul]
  have hFF : F * F = F := by
    calc
      F * F = r⁻¹ • ((θ - τ) • F) := by
        conv_lhs => lhs; dsimp only [F]
        rw [Matrix.smul_mul, sub_mul, Matrix.smul_mul, hQF, hBF, sub_smul]
      _ = F := by rw [hdiff, smul_smul, inv_mul_cancel₀ hr, one_smul]
  have hEF : E * F = 0 := by
    conv_lhs => lhs; dsimp only [E]
    rw [Matrix.smul_mul, sub_mul, Matrix.smul_mul, hBF, hQF, sub_self, smul_zero]
  have hFE : F * E = 0 := by
    conv_lhs => lhs; dsimp only [F]
    rw [Matrix.smul_mul, sub_mul, Matrix.smul_mul, hQE, hBE, sub_self, smul_zero]
  have hPQ : P * Q = 0 := IsIdempotentElem.mul_one_sub_self hPP
  have hQP : Q * P = 0 := IsIdempotentElem.one_sub_mul_self hPP
  have hPE : P * E = 0 := by
    dsimp [E]
    rw [Matrix.mul_smul, mul_sub, Matrix.mul_smul, hPB, hPQ, smul_zero, sub_self, smul_zero]
  have hEP : E * P = 0 := by
    dsimp [E]
    rw [Matrix.smul_mul, sub_mul, Matrix.smul_mul, hBP, hQP, smul_zero, sub_self, smul_zero]
  have hPF : P * F = 0 := by
    dsimp [F]
    rw [Matrix.mul_smul, mul_sub, Matrix.mul_smul, hPB, hPQ, smul_zero, sub_self, smul_zero]
  have hFP : F * P = 0 := by
    dsimp [F]
    rw [Matrix.smul_mul, sub_mul, Matrix.smul_mul, hBP, hQP, smul_zero, sub_self, smul_zero]
  have hEFsum : E + F = Q := by
    calc
      E + F = r⁻¹ • ((θ - τ) • Q) := by dsimp [E, F]; module
      _ = Q := by rw [hdiff, smul_smul, inv_mul_cancel₀ hr, one_smul]
  have hBsum : θ • E + τ • F = B := by
    calc
      θ • E + τ • F = r⁻¹ • ((θ - τ) • B) := by dsimp [E, F]; module
      _ = B := by rw [hdiff, smul_smul, inv_mul_cancel₀ hr, one_smul]
  refine ⟨hPP, hEE, hFF, hPE, hEP, hPF, hFP, hEF, hFE, ?_, ?_, ?_⟩
  · rw [add_assoc, hEFsum]
    dsimp [Q]
    module
  · rw [add_assoc, hBsum]
    dsimp [B]
    module
  · intro u
    have hPu : P u u = n⁻¹ := by simp [P, J]
    refine ⟨by simpa only [one_div] using hPu, ?_, ?_⟩
    · simp only [E, B, A, Q, Matrix.smul_apply, Matrix.sub_apply,
        SimpleGraph.adjMatrix_apply, SimpleGraph.irrefl, ite_false, Matrix.one_apply_eq,
        hPu, smul_eq_mul]
      field_simp
      dsimp [τ, n]
      ring
    · simp only [F, B, A, Q, Matrix.smul_apply, Matrix.sub_apply,
        SimpleGraph.adjMatrix_apply, SimpleGraph.irrefl, ite_false, Matrix.one_apply_eq,
        hPu, smul_eq_mul]
      field_simp
      dsimp [θ, n]
      ring

private lemma three_projector_exp {V : Type} [Fintype V] [DecidableEq V]
    (P E F : Matrix V V ℂ) (a b c : ℂ)
    (hPP : P * P = P) (hEE : E * E = E) (hFF : F * F = F)
    (hPE : P * E = 0) (hEP : E * P = 0) (hPF : P * F = 0) (hFP : F * P = 0)
    (hEF : E * F = 0) (hFE : F * E = 0) (hsum : P + E + F = 1) :
    NormedSpace.exp (a • P + b • E + c • F) =
      Complex.exp a • P + Complex.exp b • E + Complex.exp c • F := by
  have hcomm : Commute (a • P) (b • E) := by
    exact ((show Commute P E from hPE.trans hEP.symm).smul_left a).smul_right b
  have hcomm' : Commute (a • P + b • E) (c • F) := by
    exact (((show Commute P F from hPF.trans hFP.symm).smul_left a).smul_right c).add_left
      (((show Commute E F from hEF.trans hFE.symm).smul_left b).smul_right c)
  rw [Matrix.exp_add_of_commute _ _ hcomm', Matrix.exp_add_of_commute _ _ hcomm]
  rw [D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation.expIdempotent P hPP,
    D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation.expIdempotent E hEE,
    D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation.expIdempotent F hFF]
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
    hPE, hPF, hEF, smul_zero, add_zero]
  rw [← hsum]
  simp only [Complex.exp_eq_exp_ℂ]
  module

private lemma conference_walk {m : ℕ} (hm : 1 ≤ m)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m) (u : V) (t : ℝ) :
    let n : ℂ := 4 * (m : ℂ) + 1
    let r : ℂ := (Real.sqrt (4 * (m : ℝ) + 1) : ℝ)
    hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u =
      Complex.exp ((t : ℂ) * I * (2 * (m : ℂ))) / n +
        (Complex.exp ((t : ℂ) * I * ((-1 + r) / 2)) +
          Complex.exp ((t : ℂ) * I * ((-1 - r) / 2))) * (2 * (m : ℂ) / n) := by
  obtain ⟨hPP, hEE, hFF, hPE, hEP, hPF, hFP, hEF, hFE, hsum, hA, hd⟩ :=
    conference_projectors hm G hG
  rw [hamiltonianPropagator_neg, hA]
  simp only [smul_add]
  rw [smul_smul ((t : ℂ) * I) (2 * (m : ℂ)) _,
    smul_smul ((t : ℂ) * I) ((-1 + (Real.sqrt (4 * (m : ℝ) + 1) : ℂ)) / 2) _,
    smul_smul ((t : ℂ) * I) ((-1 - (Real.sqrt (4 * (m : ℝ) + 1) : ℂ)) / 2) _]
  rw [three_projector_exp _ _ _ _ _ _ hPP hEE hFF hPE hEP hPF hFP hEF hFE hsum]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, (hd u).1,
    (hd u).2.1, (hd u).2.2]
  ring

private lemma return_formula {m : ℕ} (hm : 1 ≤ m)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m) (u : V) (t : ℝ) :
    ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2 =
      ‖Complex.exp (((4 * (m : ℝ) + 1) * t / 2 : ℝ) * I) +
        ((4 * (m : ℝ)) * Real.cos (Real.sqrt (4 * (m : ℝ) + 1) * t / 2) : ℝ)‖ ^ 2 /
          (4 * (m : ℝ) + 1) ^ 2 := by
  let r : ℝ := Real.sqrt (4 * (m : ℝ) + 1)
  have he0 : Complex.exp ((t : ℂ) * I * (2 * (m : ℂ))) =
      Complex.exp ((-t / 2 : ℝ) * I) *
        Complex.exp (((4 * (m : ℝ) + 1) * t / 2 : ℝ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have heθ : (t : ℂ) * I * ((-1 + (r : ℂ)) / 2) =
      ((-t / 2 : ℝ) : ℂ) * I + ((r * t / 2 : ℝ) : ℂ) * I := by
    push_cast
    ring
  have heτ : (t : ℂ) * I * ((-1 - (r : ℂ)) / 2) =
      ((-t / 2 : ℝ) : ℂ) * I + -((r * t / 2 : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hesum : Complex.exp ((t : ℂ) * I * ((-1 + (r : ℂ)) / 2)) +
      Complex.exp ((t : ℂ) * I * ((-1 - (r : ℂ)) / 2)) =
      Complex.exp ((-t / 2 : ℝ) * I) * (2 * (Real.cos (r * t / 2) : ℂ)) := by
    rw [heθ, heτ, Complex.exp_add, Complex.exp_add, ← mul_add,
      ← Complex.two_cos, ← Complex.ofReal_cos]
  have hv : hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u =
      Complex.exp ((-t / 2 : ℝ) * I) *
        (Complex.exp (((4 * (m : ℝ) + 1) * t / 2 : ℝ) * I) +
          (4 * (m : ℝ) * Real.cos (r * t / 2) : ℝ)) /
            ((4 * (m : ℝ) + 1 : ℝ) : ℂ) := by
    rw [conference_walk hm G hG u t, he0, hesum]
    push_cast
    ring
  rw [hv]
  simp only [norm_div, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, div_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rfl

private lemma odd_cos_bound (q : ℕ) (hq : Odd q) (x : ℝ) :
    |Real.cos ((q : ℝ) * x)| ≤ (q : ℝ) * |Real.cos x| := by
  obtain ⟨k, hk⟩ := hq
  have h := D5.S3.Fourier.PositiveFourierApproximationRefutation.abs_sin_nat_mul_le
    q (x + Real.pi / 2)
  have heq : (q : ℝ) * (x + Real.pi / 2) =
      ((q : ℝ) * x + Real.pi / 2) + (k : ℝ) * Real.pi := by
    rw [hk]
    push_cast
    ring
  rw [heq, Real.sin_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, Real.sin_add_pi_div_two, Real.sin_add_pi_div_two] at h
  exact h

private lemma square_lower {m : ℕ} (hm : 1 ≤ m) (hs : IsSquare (4 * m + 1)) (t : ℝ) :
    1 ≤ ‖Complex.exp (((4 * (m : ℝ) + 1) * t / 2 : ℝ) * I) +
      ((4 * (m : ℝ)) * Real.cos (Real.sqrt (4 * (m : ℝ) + 1) * t / 2) : ℝ)‖ ^ 2 := by
  obtain ⟨q, hq⟩ := hs
  have hq' : 4 * (m : ℝ) + 1 = (q : ℝ) ^ 2 := by
    exact_mod_cast (show 4 * m + 1 = q ^ 2 by simpa only [pow_two] using hq)
  have hq0 : 3 ≤ q := by nlinarith
  have hodd : Odd q := by
    apply Nat.Odd.of_mul_left
    rw [← hq]
    exact ⟨2 * m, by omega⟩
  have hroot : Real.sqrt (4 * (m : ℝ) + 1) = (q : ℝ) := by
    rw [hq', Real.sqrt_sq (Nat.cast_nonneg _)]
  let x : ℝ := (q : ℝ) * t / 2
  have hx : (4 * (m : ℝ) + 1) * t / 2 = (q : ℝ) * x := by dsimp [x]; rw [hq']; ring
  rw [hroot, hx]
  change 1 ≤ ‖Complex.exp (((q : ℝ) * x : ℝ) * I) +
    (4 * (m : ℝ) * Real.cos x : ℝ)‖ ^ 2
  rw [Complex.sq_norm, Complex.normSq_add, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I,
    Complex.exp_ofReal_mul_I]
  suffices 1 ≤ 1 + (4 * (m : ℝ) * Real.cos x) * (4 * (m : ℝ) * Real.cos x) +
      2 * (Real.cos ((q : ℝ) * x) * (4 * (m : ℝ) * Real.cos x)) by
    simpa [-Complex.ofReal_cos, -Complex.ofReal_sin] using this
  have hbound := odd_cos_bound q hodd x
  have hprod : |Real.cos x * Real.cos ((q : ℝ) * x)| ≤
      (q : ℝ) * Real.cos x ^ 2 := by
    rw [abs_mul]
    calc
      |Real.cos x| * |Real.cos ((q : ℝ) * x)| ≤
          |Real.cos x| * ((q : ℝ) * |Real.cos x|) :=
        mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
      _ = (q : ℝ) * Real.cos x ^ 2 := by rw [mul_left_comm, ← sq, sq_abs]
  have hcross := (abs_le.mp hprod).1
  have hcoef : 0 ≤ 4 * (m : ℝ) - 2 * (q : ℝ) := by
    have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq0
    nlinarith
  have hnonneg := mul_nonneg (mul_nonneg (by positivity : 0 ≤ 4 * (m : ℝ)) hcoef)
    (sq_nonneg (Real.cos x))
  nlinarith

private lemma floor_attainment {m : ℕ} (hm : 1 ≤ m)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m) (u : V) :
    ∃ t : ℝ, 0 < t ∧ ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2 =
      1 / (4 * (m : ℝ) + 1) ^ 2 := by
  have hr : 0 < Real.sqrt (4 * (m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨Real.pi / Real.sqrt (4 * (m : ℝ) + 1), div_pos Real.pi_pos hr, ?_⟩
  rw [return_formula hm G hG]
  rw [show Real.sqrt (4 * (m : ℝ) + 1) *
      (Real.pi / Real.sqrt (4 * (m : ℝ) + 1)) / 2 = Real.pi / 2 by
    field_simp]
  simp only [Real.cos_pi_div_two, mul_zero, Complex.ofReal_zero, add_zero,
    Complex.norm_exp_ofReal_mul_I, one_pow]

private lemma nonsquare_small {m : ℕ} (hm : 1 ≤ m) (hs : ¬ IsSquare (4 * m + 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧
      ‖Complex.exp (((4 * (m : ℝ) + 1) * t / 2 : ℝ) * I) +
        ((4 * (m : ℝ)) * Real.cos (Real.sqrt (4 * (m : ℝ) + 1) * t / 2) : ℝ)‖ ^ 2 /
          (4 * (m : ℝ) + 1) ^ 2 < ε := by
  let n : ℝ := 4 * (m : ℝ) + 1
  let r := Real.sqrt n
  have hn : 0 < n := by dsimp [n]; positivity
  have hr : 0 < r := Real.sqrt_pos.mpr hn
  have hrr : r * r = n := Real.mul_self_sqrt hn.le
  have ha : 0 < 4 * (m : ℝ) := by positivity
  have ha1 : 1 ≤ 4 * (m : ℝ) := by exact_mod_cast (show 1 ≤ 4 * m by omega)
  have hi : Irrational r := by
    simpa only [r, n, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      (irrational_sqrt_natCast_iff.mpr hs)
  have hi' : Irrational ((2 * Real.pi / r) / (2 * Real.pi)) := by
    convert hi.inv using 1
    field_simp
  have hdZ : DenseRange (fun j : ℤ => j • ((2 * Real.pi / r : ℝ) : Real.Angle)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr hi'
  let f : Real.Angle → ℝ := fun z => (1 + 4 * (m : ℝ) * z.cos) ^ 2 / n ^ 2
  have hf : Continuous f := by
    exact ((continuous_const.add
      (continuous_const.mul Real.Angle.continuous_cos)).pow 2).div_const _
  have hz : f ((Real.arccos (-1 / (4 * (m : ℝ))) : ℝ) : Real.Angle) = 0 := by
    dsimp only [f]
    rw [Real.Angle.cos_coe, Real.cos_arccos]
    · field_simp
      ring
    · exact (le_div_iff₀ ha).mpr (by nlinarith)
    · exact (div_le_iff₀ ha).mpr (by nlinarith)
  have hzero : f 0 = 1 := by
    dsimp only [f]
    rw [Real.Angle.cos_zero]
    field_simp
    dsimp [n]
    ring
  obtain ⟨j, hj⟩ := hdZ.exists_mem_open (isOpen_Iio.preimage hf)
    ⟨((Real.arccos (-1 / (4 * (m : ℝ))) : ℝ) : Real.Angle), by
      change f _ < min ε 1
      rw [hz]
      exact lt_min hε zero_lt_one⟩
  change f (j • ((2 * Real.pi / r : ℝ) : Real.Angle)) < min ε 1 at hj
  have hj0 : j ≠ 0 := by
    intro hj0
    subst j
    rw [zero_zsmul, hzero] at hj
    exact (lt_irrefl 1) (lt_of_lt_of_le hj (min_le_right _ _))
  have hjp : (0 : ℝ) < (j.natAbs : ℝ) := Nat.cast_pos.mpr (Int.natAbs_pos.mpr hj0)
  refine ⟨4 * Real.pi * (j.natAbs : ℝ) / n, div_pos (by positivity) hn, ?_⟩
  change ‖Complex.exp ((n * (4 * Real.pi * (j.natAbs : ℝ) / n) / 2 : ℝ) * I) +
      (4 * (m : ℝ) * Real.cos (r * (4 * Real.pi * (j.natAbs : ℝ) / n) / 2) : ℝ)‖ ^ 2 /
        n ^ 2 < ε
  have hphase : n * (4 * Real.pi * (j.natAbs : ℝ) / n) / 2 =
      (j.natAbs : ℝ) * (2 * Real.pi) := by
    field_simp
    ring
  have hangle : r * (4 * Real.pi * (j.natAbs : ℝ) / n) / 2 =
      (j.natAbs : ℝ) * (2 * Real.pi / r) := by
    rw [← hrr]
    field_simp
    ring
  rw [hphase, hangle]
  have he : Complex.exp (((j.natAbs : ℝ) * (2 * Real.pi) : ℝ) * I) = 1 := by
    push_cast
    rw [mul_assoc]
    exact Complex.exp_nat_mul_two_pi_mul_I j.natAbs
  rw [he, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  have hcos : Real.cos ((j.natAbs : ℝ) * (2 * Real.pi / r)) =
      Real.cos ((j : ℝ) * (2 * Real.pi / r)) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    calc
      Real.cos (|(j : ℝ)| * (2 * Real.pi / r)) =
          Real.cos |(j : ℝ) * (2 * Real.pi / r)| := by
        rw [abs_mul, abs_of_nonneg (div_nonneg (by positivity) hr.le)]
      _ = Real.cos ((j : ℝ) * (2 * Real.pi / r)) := Real.cos_abs _
  rw [hcos]
  have hj' := lt_of_lt_of_le hj (min_le_left _ _)
  dsimp only [f] at hj'
  rw [← Real.Angle.coe_zsmul, Real.Angle.cos_coe, zsmul_eq_mul] at hj'
  exact hj'

private lemma family_small (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ (m : ℕ), 1 ≤ m → N ≤ 4 * m + 1 →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m → ∀ u : V,
      ∃ t : ℝ, 0 < t ∧ ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2 < c := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (1 / c))
  refine ⟨N, ?_⟩
  intro m hm hnm V _ _ G _ hG u
  obtain ⟨t, ht, hp⟩ := floor_attainment hm G hG u
  refine ⟨t, ht, ?_⟩
  rw [hp]
  have hn : (N : ℝ) ≤ 4 * (m : ℝ) + 1 := by exact_mod_cast hnm
  have hn1 : 1 < 4 * (m : ℝ) + 1 := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hN) hn
  have hnc : 1 / c < 4 * (m : ℝ) + 1 :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) hn
  apply (div_lt_iff₀ (by positivity : 0 < (4 * (m : ℝ) + 1) ^ 2)).mpr
  have hmul : 1 < (4 * (m : ℝ) + 1) * c := (div_lt_iff₀ hc).mp hnc
  nlinarith

/-- Godsil's conference-graph question has a sharp square-order classification. -/
theorem result : claim := by
  constructor
  · intro m hm V _ _ G _ hG u
    constructor
    · intro hs
      refine ⟨?_, floor_attainment hm G hG u⟩
      intro t
      rw [return_formula hm G hG u t]
      exact (div_le_div_iff_of_pos_right (by positivity)).mpr (square_lower hm hs t)
    · intro hs
      refine ⟨fun t => sq_nonneg _, ?_⟩
      intro ε hε
      obtain ⟨t, ht, hp⟩ := nonsquare_small hm hs ε hε
      exact ⟨t, ht, by rwa [return_formula hm G hG u t]⟩
  · exact family_small

end D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness
