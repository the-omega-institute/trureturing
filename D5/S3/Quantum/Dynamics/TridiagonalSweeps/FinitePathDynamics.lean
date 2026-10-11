/- GID: D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted Dirichlet rigidity, boundary observability, and matrix power decay. -/

/-
harmonic_dirichlet_zero: proof_shape: content; escape_witness: the conclusion itself,
  proved by weighted slope propagation, telescoping, and finite-path induction.
boundary_zero_observability: proof_shape: content; escape_witness: the conclusion
  itself, proved by the two-coordinate zero recurrence along the full finite path.
extend_interior: proof_shape: bind-only; consumer: harmonic_dirichlet_zero.
extend_last: proof_shape: bind-only; consumer: harmonic_dirichlet_zero.
powers_tendsto_zero_of_spectralRadius_lt_one: proof_shape: bind-only;
  consumer: complex_matrix_powers_tendsto_zero.
complex_matrix_powers_tendsto_zero: proof_shape: bind-only;
  consumer: real_mulVec_powers_tendsto_zero.
real_mulVec_powers_tendsto_zero: proof_shape: bind-only;
  consumer: D5.S3.Quantum.Dynamics.TridiagonalSweeps.TokenDampedSweepContraction.result.
admission_basis: escape-witness (harmonic_dirichlet_zero; boundary_zero_observability).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14784
Direct frozen dependencies: none (pinned Mathlib only).
The statements hold for arbitrary finite paths; utility is none.
-/

import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed

open Matrix Filter Topology
namespace D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics

def zeroExtend {m : ℕ} (z : Fin m → ℂ) : Fin (m + 2) → ℂ :=
  Fin.cases 0 (Fin.snoc z 0)

lemma extend_interior {m : ℕ} (z : Fin m → ℂ) (i : Fin m) :
    zeroExtend z i.castSucc.succ = z i := by simp [zeroExtend]

lemma extend_last {m : ℕ} (z : Fin m → ℂ) :
    zeroExtend z (Fin.last (m + 1)) = 0 := by
  change (Fin.snoc z 0 : Fin (m + 1) → ℂ) (Fin.last m) = 0
  simp

private lemma sum_succ_sub_castSucc (n : ℕ) (f : Fin (n + 1) → ℂ) :
    (∑ j : Fin n, (f j.succ - f j.castSucc)) = f (Fin.last n) - f 0 := by
  have h1 := Fin.sum_univ_succ f
  have h2 := Fin.sum_univ_castSucc f
  rw [Finset.sum_sub_distrib]
  linear_combination h2 - h1

private noncomputable def edgeSlope {m : ℕ} (v : Fin (m + 1) → ℝ) (z : Fin m → ℂ)
    (j : Fin (m + 1)) : ℂ := (zeroExtend z j.succ - zeroExtend z j.castSucc) / (v j : ℂ)

theorem harmonic_dirichlet_zero {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (z : Fin m → ℂ) (hfix : ∀ i : Fin m, (z i - zeroExtend z i.castSucc.castSucc) / (v i.castSucc : ℂ) =
      (zeroExtend z i.succ.succ - z i) / (v i.succ : ℂ)) : z = 0 := by
  have hs : ∀ j : Fin (m + 1), edgeSlope v z j = edgeSlope v z 0 := by
    intro j
    induction j using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have h := hfix i
      have heq : i.succ.castSucc = i.castSucc.succ := by ext; rfl
      have hh : edgeSlope v z i.castSucc = edgeSlope v z i.succ := by
        simpa only [edgeSlope, heq, extend_interior] using h
      rw [← hh, ih]
  have hd : ∀ j : Fin (m + 1), zeroExtend z j.succ - zeroExtend z j.castSucc =
      (v j : ℂ) * edgeSlope v z 0 := by
    intro j
    rw [← hs j]
    unfold edgeSlope
    field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt (hv j))]
  have htotal : (∑ j : Fin (m + 1), (zeroExtend z j.succ - zeroExtend z j.castSucc)) = 0 := by
    rw [sum_succ_sub_castSucc, extend_last]
    simp [zeroExtend]
  simp_rw [hd] at htotal
  rw [← Finset.sum_mul] at htotal
  have hsumPos : 0 < ∑ j : Fin (m + 1), v j :=
    Finset.sum_pos (fun j _ => hv j) Finset.univ_nonempty
  have hsumNe : (∑ j : Fin (m + 1), (v j : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_sum]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hsumPos)
  have hc : edgeSlope v z 0 = 0 := (mul_eq_zero.mp htotal).resolve_left hsumNe
  have he : ∀ j : Fin (m + 1), zeroExtend z j.succ = zeroExtend z j.castSucc := by
    intro j
    have h := hd j
    rw [hc, mul_zero] at h
    exact sub_eq_zero.mp h
  have hall : ∀ j : Fin (m + 2), zeroExtend z j = 0 := by
    intro j
    induction j using Fin.induction with
    | zero => simp [zeroExtend]
    | succ i ih => rw [he i]; exact ih
  funext i
  simpa only [extend_interior, Pi.zero_apply] using hall i.castSucc.succ


theorem boundary_zero_observability {m : ℕ} (hm : 1 ≤ m) (z : Fin m → ℂ)
    (hz : z ⟨0, by omega⟩ = 0)
    (hprop : ∀ i : Fin m, z i = 0 → zeroExtend z i.castSucc.castSucc = 0 →
      zeroExtend z i.succ.succ = 0) : z = 0 := by
  cases m with
  | zero => omega
  | succ n =>
    have hp : ∀ i : Fin (n + 1), z i = 0 ∧ zeroExtend z i.castSucc.castSucc = 0 := by
      intro i
      induction i using Fin.induction with
      | zero =>
        constructor
        · exact hz
        · simp [zeroExtend]
      | succ j ih =>
        have hr := hprop j.castSucc ih.1 ih.2
        have heR : j.castSucc.succ.succ = j.succ.castSucc.succ := by ext; rfl
        rw [heR, extend_interior] at hr
        constructor
        · exact hr
        · have heL : j.succ.castSucc.castSucc = j.castSucc.castSucc.succ := by ext; rfl
          rw [heL, extend_interior]
          exact ih.1
    funext i
    exact (hp i).1

private lemma powers_tendsto_zero_of_spectralRadius_lt_one
    {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (a : R) (h : spectralRadius ℂ a < 1) :
    Tendsto (fun k : ℕ => a ^ k) atTop (nhds 0) := by
  obtain ⟨r, hr, hr1⟩ := exists_between h
  have hb : ∀ᶠ k : ℕ in atTop, ‖a ^ k‖ₑ ≤ r ^ k := by
    have ht := (spectrum.gelfand_formula a).eventually (gt_mem_nhds hr)
    filter_upwards [ht, eventually_gt_atTop (0 : ℕ)] with k hk hk0
    have he : (1 / (k : ℝ)) * (k : ℝ) = 1 := by
      field_simp
    have hh := ENNReal.rpow_le_rpow hk.le (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    rw [← ENNReal.rpow_mul, he, ENNReal.rpow_one, ENNReal.rpow_natCast] at hh
    exact hh
  apply tendsto_zero_iff_enorm_tendsto_zero.mpr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1)
    (Eventually.of_forall fun k => bot_le) hb

private lemma complex_matrix_powers_tendsto_zero {m : ℕ} (hm : 1 ≤ m)
    (N : Matrix (Fin m) (Fin m) ℂ)
    (hN : ∀ c ∈ spectrum ℂ N, ‖c‖ < 1) :
    Tendsto (fun k : ℕ => N ^ k) atTop (nhds 0) := by
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  letI := Matrix.linftyOpNormedRing (n := Fin m) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := Fin m) (R := ℂ) (α := ℂ)
  apply powers_tendsto_zero_of_spectralRadius_lt_one
  apply spectrum.spectralRadius_lt_of_forall_lt
  intro c hc
  exact_mod_cast hN c hc

theorem real_mulVec_powers_tendsto_zero {m : ℕ} (hm : 1 ≤ m)
    (N : Matrix (Fin m) (Fin m) ℝ)
    (hN : ∀ c ∈ spectrum ℂ (N.map (algebraMap ℝ ℂ)), ‖c‖ < 1)
    (u : Fin m → ℝ) :
    Tendsto (fun k : ℕ => (N ^ k).mulVec u) atTop (nhds 0) := by
  have ht := complex_matrix_powers_tendsto_zero hm (N.map (algebraMap ℝ ℂ)) hN
  have hc : Tendsto (fun k : ℕ => ((N.map (algebraMap ℝ ℂ)) ^ k).mulVec
      (fun i => (u i : ℂ))) atTop (nhds 0) := by
    have hcont : Continuous (fun C : Matrix (Fin m) (Fin m) ℂ =>
        C.mulVec (fun i => (u i : ℂ))) := by
      apply continuous_pi
      intro i
      unfold Matrix.mulVec dotProduct
      fun_prop
    convert hcont.continuousAt.tendsto.comp ht using 1 <;> simp [Function.comp_def]
  have hr := (show Continuous (fun z : Fin m → ℂ => fun i => (z i).re) by
    apply continuous_pi; intro i; fun_prop).continuousAt.tendsto.comp hc
  have hmap : ∀ k : ℕ, (N.map (algebraMap ℝ ℂ)) ^ k =
      (N ^ k).map (algebraMap ℝ ℂ) := by
    intro k
    induction k with
    | zero => simp [Matrix.map_one]
    | succ k ih =>
      rw [pow_succ, pow_succ, ih, Matrix.map_mul]
  have he : (fun k : ℕ => fun i =>
      (((N.map (algebraMap ℝ ℂ)) ^ k).mulVec (fun i => (u i : ℂ)) i).re) =
      fun k : ℕ => (N ^ k).mulVec u := by
    funext k i
    rw [hmap k]
    have hx := (algebraMap ℝ ℂ).map_mulVec (N ^ k) u i
    change (↑((N ^ k).mulVec u i) : ℂ) = _ at hx
    simp only [Function.comp_def, Complex.coe_algebraMap] at hx
    simpa only [Complex.coe_algebraMap, Complex.ofReal_re] using congrArg Complex.re hx.symm
  convert hr using 1
  · simpa only [Function.comp_def] using he.symm


#print axioms extend_interior
#print axioms extend_last
#print axioms harmonic_dirichlet_zero
#print axioms boundary_zero_observability
#print axioms real_mulVec_powers_tendsto_zero
end D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics
