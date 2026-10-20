/- GID: D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/NMLWMeasuredFidelitySeparation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Three qubit states have measured average pairwise fidelity above the Uhlmann average. -/

/-
result:
  proof_shape: bind-only (consumed analytic estimates and the existing two-by-two identity)
  escape_witness: none
  admission_basis: open-problem-resolution (#19068; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19175
Reused analytic owners include TraceNorm.transitionMass_sq,
ActualPureQubitCostInfimum.norm_bloch_le_trace_of_posSemidef and
EntropyProductionCoherenceDeletionIdentity.cfc_diagonal.
The real infimum ranges over the single dependent sum of all finite POVMs.
The three matrices are I/2, (I + Z/2)/2 and (I + X/2)/2.
All private theorem helpers are consumed bind-only steps; none supplies an escape witness.
The measurement action is the literal diagonal trace expression, used without a second channel name.
Declarations (each proof_shape: bind-only; escape_witness: none):
  uhlmann; consumers: FU, FM, uhlmann_diagonal, povm_pair_sum_bound, uhlmann_sq_formula, qubit_fidelity_squares, FU_witness_lt, FM_witness_ge
  FU; consumers: claim, FU_witness_lt
  FM; consumers: claim, FM_witness_ge
  claim; consumers: result
  qubitR; consumers: qubit_states_psd, qubit_states_trace, witnessStates, effect_probabilities, effect_probabilities_nonneg, classicalCost, povm_pair_sum_bound, qubit_root_determinants, qubit_fidelity_squares, FU_witness_lt, FM_witness_ge
  qubitA; consumers: qubit_states_psd, qubit_states_trace, witnessStates, effect_probabilities, effect_probabilities_nonneg, classicalCost, povm_pair_sum_bound, qubit_root_determinants, qubit_fidelity_squares, FU_witness_lt, FM_witness_ge
  qubitB; consumers: qubit_states_psd, qubit_states_trace, witnessStates, effect_probabilities, effect_probabilities_nonneg, classicalCost, povm_pair_sum_bound, qubit_root_determinants, qubit_fidelity_squares, FU_witness_lt, FM_witness_ge
  qubit_states_psd; consumers: witnessStates, effect_probabilities_nonneg, qubit_root_determinants, qubit_fidelity_squares
  qubit_states_trace; consumers: witnessStates
  witnessStates; consumers: FU_witness_lt, FM_witness_ge, result
  effect_coordinates; consumers: effect_lower_bound
  effect_probabilities; consumers: effect_lower_bound, povm_pair_sum_bound
  effect_probabilities_nonneg; consumers: povm_pair_sum_bound
  povm_coordinates; consumers: povm_pair_sum_bound
  sum_pairs_three; consumers: FU_witness_lt, FM_witness_ge
  polynomial_certificate; consumers: disc_inequality
  disc_inequality; consumers: scalar_effect_bound
  scalar_effect_bound; consumers: effect_lower_bound
  sqrt_diagonal; consumers: uhlmann_diagonal
  uhlmann_diagonal; consumers: povm_pair_sum_bound
  classicalCost; consumers: effect_lower_bound, povm_pair_sum_bound
  effect_lower_bound; consumers: povm_pair_sum_bound
  povm_pair_sum_bound; consumers: FM_witness_ge
  traceNorm_sq_two; consumers: uhlmann_sq_formula
  gram_root_trace; consumers: uhlmann_sq_formula
  uhlmann_sq_formula; consumers: qubit_fidelity_squares
  qubit_root_determinants; consumers: qubit_fidelity_squares
  qubit_fidelity_squares; consumers: FU_witness_lt
  FU_witness_lt; consumers: result
  povm_index_nonempty; consumers: FM_witness_ge
  FM_witness_ge; consumers: result
  result; consumers: settling result
-/

import D5.S3.Quantum.Schatten.TraceNorm
import D5.S3.Quantum.Information.ActualPureQubitGeometry
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.QuantumStates.GNSZeroPropagation

/-! Binding conventions for T. Nuradha, H. K. Mishra, F. Leditzky and M. M. Wilde, "Multivariate fidelities",
arXiv:2404.16101v3 (J. Phys. A 58 (2025) 165304), Eq. (5.13), Definition 5.40 and Remark 5.45. -/

noncomputable section
namespace D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation

open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open scoped ComplexOrder MatrixOrder

/-- Proposition 3.1: the Uhlmann fidelity `F(ρ, σ) := ‖√ρ √σ‖₁`. -/
def uhlmann {n : Type*} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) : ℝ :=
  D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm (CFC.sqrt ρ * CFC.sqrt σ)

/-- Eq. (5.13): the average pairwise Uhlmann fidelity `F_U(ρ_1, …, ρ_r) = (2/(r(r−1))) Σ_{i<j} F(ρ_i, ρ_j)`. -/
def FU {d r : ℕ} (ρ : Fin r → DensityState (Fin d)) : ℝ :=
  2 / (r * (r - 1)) * ∑ i, ∑ j ∈ Finset.Ioi i,
    uhlmann (CStarMatrix.ofMatrix.symm (ρ i).val) (CStarMatrix.ofMatrix.symm (ρ j).val)

/-- Definition 5.40: the measured average pairwise fidelity
`F_M(ρ_1, …, ρ_r) := (2/(r(r−1))) inf_{(Λ_x)_x} Σ_{i<j} F(Λ(ρ_i), Λ(ρ_j))`, the infimum over all finite POVMs
`(Λ_x)_{x ∈ Fin m}` of every size `m`, taken as one infimum over the pairs `(m, Λ)`. -/
def FM {d r : ℕ} (ρ : Fin r → DensityState (Fin d)) : ℝ :=
  2 / (r * (r - 1)) * ⨅ Λ : (Σ m : ℕ, {Λ : Fin m → Matrix (Fin d) (Fin d) ℂ // IsPOVM Λ}),
    ∑ i, ∑ j ∈ Finset.Ioi i,
      uhlmann (Matrix.diagonal (fun x => Matrix.trace (Λ.2.val x * CStarMatrix.ofMatrix.symm (ρ i).val)))
        (Matrix.diagonal (fun x => Matrix.trace (Λ.2.val x * CStarMatrix.ofMatrix.symm (ρ j).val)))

/-- Remark 5.45: "it is interesting to determine whether there exists a tuple of states for which
`F_M(ρ_1, …, ρ_r) > F_U(ρ_1, …, ρ_r)` — we leave this as an open question." The affirmative answer. -/
def claim : Prop :=
  ∃ (d r : ℕ) (ρ : Fin r → DensityState (Fin d)), FU ρ < FM ρ

end D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation


namespace D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
set_option maxHeartbeats 600000

private def qubitR : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun _ => 1/2)
private def qubitA : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![3/4,1/4]
private def qubitB : Matrix (Fin 2) (Fin 2) ℂ := !![1/2,1/4;1/4,1/2]


private theorem qubit_states_psd : qubitR.PosSemidef ∧ qubitA.PosSemidef ∧ qubitB.PosSemidef := by
  refine ⟨?_, ?_, ?_⟩
  · exact Matrix.PosSemidef.diagonal (fun _ => by norm_num [Complex.nonneg_iff,Complex.div_re,Complex.div_im])
  · apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.nonneg_iff,Complex.div_re,Complex.div_im]
  · have hJ : (Matrix.of (fun _ _ : Fin 2 => (1 : ℂ))).PosSemidef := by
      simpa [Matrix.vecMulVec] using
        (Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin 2 => (1 : ℂ)))
    have hI : (((1/4 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).PosSemidef :=
      Matrix.PosSemidef.one.smul (by norm_num [Complex.nonneg_iff,Complex.div_re,Complex.div_im])
    have hh := hI.add (hJ.smul (show (0 : ℂ) ≤ 1/4 by norm_num [Complex.nonneg_iff,Complex.div_re,Complex.div_im]))
    convert hh using 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [qubitB, Matrix.vecMulVec]

private theorem qubit_states_trace : Matrix.trace qubitR=1 ∧ Matrix.trace qubitA=1 ∧ Matrix.trace qubitB=1 := by
  norm_num [qubitR,qubitA,qubitB,Matrix.trace,Fin.sum_univ_two]

private def witnessStates : Fin 3 → DensityState (Fin 2) := ![
  (densityBridge qubitR qubit_states_psd.1 qubit_states_trace.1).val,
  (densityBridge qubitA qubit_states_psd.2.1 qubit_states_trace.2.1).val,
  (densityBridge qubitB qubit_states_psd.2.2 qubit_states_trace.2.2).val]

private theorem effect_coordinates (E : Matrix (Fin 2) (Fin 2) ℂ) (hE : E.PosSemidef) :
    0 ≤ ((Matrix.trace E).re/2) ∧ ((bloch E 2/2))^2+((bloch E 0/2))^2 ≤ (((Matrix.trace E).re/2))^2 := by
  have hn := norm_bloch_le_trace_of_posSemidef E hE
  have ha : 0 ≤ (Matrix.trace E).re := (Complex.nonneg_iff.mp hE.trace_nonneg).1
  have hs : ‖bloch E‖^2 ≤ (Matrix.trace E).re^2 := (sq_le_sq₀ (norm_nonneg _) ha).2 hn
  rw [EuclideanSpace.real_norm_sq_eq] at hs
  simp only [Fin.sum_univ_three] at hs
  constructor
  · exact div_nonneg ha (by norm_num)
  · dsimp
    nlinarith only [hs, sq_nonneg (bloch E 1)]

private theorem effect_probabilities (E : Matrix (Fin 2) (Fin 2) ℂ) (hE : E.PosSemidef) :
    Matrix.trace (E*qubitR) = (((Matrix.trace E).re/2) : ℂ) ∧
    Matrix.trace (E*qubitA) = ((((Matrix.trace E).re/2)+(bloch E 2/2)/2 : ℝ) : ℂ) ∧
    Matrix.trace (E*qubitB) = ((((Matrix.trace E).re/2)+(bloch E 0/2)/2 : ℝ) : ℂ) := by
  have he := (bloch_geometry_of_isHermitian E hE.isHermitian).1
  refine ⟨?_, ?_, ?_⟩
  all_goals
    conv_lhs => rw [he]
    simp [qubitR,qubitA,qubitB,blochMatrix,Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,
      Fin.sum_univ_two] <;> push_cast <;> ring

private theorem effect_probabilities_nonneg (E : Matrix (Fin 2) (Fin 2) ℂ) (hE : E.PosSemidef) :
    0 ≤ (Matrix.trace (E*qubitR)).re ∧
    0 ≤ (Matrix.trace (E*qubitA)).re ∧
    0 ≤ (Matrix.trace (E*qubitB)).re := by
  exact ⟨(Complex.nonneg_iff.mp (hE.trace_mul_nonneg qubit_states_psd.1)).1,
    (Complex.nonneg_iff.mp (hE.trace_mul_nonneg qubit_states_psd.2.1)).1,
    (Complex.nonneg_iff.mp (hE.trace_mul_nonneg qubit_states_psd.2.2)).1⟩

private theorem povm_coordinates {m : ℕ} (Λ : Fin m → Matrix (Fin 2) (Fin 2) ℂ) (hΛ : IsPOVM Λ) :
    (∑ x, ((Matrix.trace (Λ x)).re/2))=1 ∧ (∑ x, (bloch (Λ x) 2/2))=0 ∧ (∑ x, (bloch (Λ x) 0/2))=0 := by
  have ht := congrArg (fun E : Matrix (Fin 2) (Fin 2) ℂ => (Matrix.trace E).re) hΛ.2
  simp [Matrix.trace_sum, Complex.re_sum] at ht
  have hr : (∑ x, bloch (Λ x))=0 := by
    change (∑ x, blochLinear (Λ x))=0
    rw [← map_sum, hΛ.2]
    ext i
    fin_cases i <;> norm_num [blochLinear,bloch]
  have hz := congrArg (fun r : EuclideanSpace ℝ (Fin 3) => r 2) hr
  have hx := congrArg (fun r : EuclideanSpace ℝ (Fin 3) => r 0) hr
  simp at hz hx
  refine ⟨?_, ?_, ?_⟩
  · simpa [Finset.sum_div] using congrArg (fun a : ℝ => a/2) ht
  · simpa [Finset.sum_div] using congrArg (fun a : ℝ => a/2) hz
  · simpa [Finset.sum_div] using congrArg (fun a : ℝ => a/2) hx

private theorem sum_pairs_three (f : Fin 3 → Fin 3 → ℝ) :
    (∑ i, ∑ j ∈ Finset.Ioi i, f i j) = f 0 1+f 0 2+f 1 2 := by
  have h0 : Finset.Ioi (0 : Fin 3)={1,2} := Finset.val_inj.mp rfl
  have h1 : Finset.Ioi (1 : Fin 3)={2} := Finset.val_eq_singleton_iff.mp rfl
  have h2 : Finset.Ioi (2 : Fin 3)=∅ := Finset.val_eq_zero.mp rfl
  simp [Fin.sum_univ_three,h0,h1,h2]

end D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation


namespace D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation

set_option maxHeartbeats 800000

private theorem polynomial_certificate (v q : ℝ)
    (hv : -(3/5 : ℝ) ≤ v) (hv1 : v ≤ 1) (hq : 0 ≤ q)
    (hd : (16 + 24*v + 4*v^2 + 2*q)*q ≤ 1 + 8*v^3 + 2*v^4) :
    0 ≤ 6 - 6*v + 25*v^2 - 78*q := by
  have hv0 : -1 ≤ v := by linarith
  have hv2 : v^2 ≤ 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-v) (by linarith : 0 ≤ 1+v)]
  have hv3 : v^3 ≤ v^2 := by nlinarith [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hv1)]
  have hv4 : v^4 ≤ v^2 := by nlinarith [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hv2)]
  have hk : 0 ≤ 6 - 6*v + 25*v^2 := by nlinarith [sq_nonneg (5*v-1)]
  have hP : 0 ≤ 18 + 48*v + 280*v^2 - 48*v^3 - 56*v^4 := by
    nlinarith [sq_nonneg (8*v+3), sq_nonneg v]
  have hC : 0 < 16 + 24*v + 4*v^2 + 2*q := by nlinarith [sq_nonneg v]
  have hprod : 0 ≤ (16 + 24*v + 4*v^2 + 2*q) * (6 - 6*v + 25*v^2 - 78*q) := by
    nlinarith only [hd, hP, mul_nonneg hq hk]
  exact nonneg_of_mul_nonneg_right hprod hC

private theorem disc_inequality (u w : ℝ) (hdisc : u^2 + w^2 ≤ 1) :
    (1/2 : ℝ) * (Real.sqrt (1+u/2) + Real.sqrt (1+w/2) +
      Real.sqrt ((1+u/2)*(1+w/2))) ≥ 36/25 + (53/200)*(u+w) := by
  have hu : -1 ≤ u ∧ u ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (u+1), sq_nonneg (u-1), sq_nonneg w]
  have hw : -1 ≤ w ∧ w ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (w+1), sq_nonneg (w-1), sq_nonneg u]
  let s := Real.sqrt (1+u/2)
  let t := Real.sqrt (1+w/2)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hs2 : s^2 = 1+u/2 := Real.sq_sqrt (by linarith)
  have ht2 : t^2 = 1+w/2 := Real.sq_sqrt (by linarith)
  have hslo : (7/10 : ℝ) ≤ s := by
    by_contra! h
    nlinarith [mul_nonneg hs (le_of_lt (show 0 < 7/10-s by linarith))]
  have htlo : (7/10 : ℝ) ≤ t := by
    by_contra! h
    nlinarith [mul_nonneg ht (le_of_lt (show 0 < 7/10-t by linarith))]
  have hshi : s ≤ 5/4 := by nlinarith [sq_nonneg (s-5/4)]
  have hthi : t ≤ 5/4 := by nlinarith [sq_nonneg (t-5/4)]
  let v := (s-1)+(t-1)
  let q := (s-1)^2+(t-1)^2
  have hv : -(3/5 : ℝ) ≤ v := by dsimp [v]; linarith
  have hv1 : v ≤ 1 := by dsimp [v]; linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hu' : u = 2*s^2-2 := by linarith
  have hw' : w = 2*t^2-2 := by linarith
  have hd : (16+24*v+4*v^2+2*q)*q ≤ 1+8*v^3+2*v^4 := by
    dsimp [v,q]
    rw [hu',hw'] at hdisc
    nlinarith only [hdisc]
  have hc := polynomial_certificate v q hv hv1 hq hd
  have hst : Real.sqrt ((1+u/2)*(1+w/2)) = s*t := by
    rw [Real.sqrt_mul (by linarith : 0 ≤ 1+u/2)]
  rw [hst]
  change 36/25+(53/200)*(u+w) ≤ (1/2 : ℝ)*(s+t+s*t)
  dsimp [v,q] at hc
  nlinarith only [hc,hs2,ht2]

end D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation

namespace D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation

private theorem scalar_effect_bound (a b c : ℝ) (ha : 0 ≤ a)
    (hbc : b^2+c^2 ≤ a^2) :
    (72/25 : ℝ)*a + (53/100)*(b+c) ≤
      Real.sqrt (a*(a+b/2)) + Real.sqrt (a*(a+c/2)) +
        Real.sqrt ((a+b/2)*(a+c/2)) := by
  by_cases haz : a=0
  · subst a
    have hb : b=0 := by nlinarith [sq_nonneg c]
    have hc : c=0 := by nlinarith [sq_nonneg b]
    subst b; subst c
    norm_num
  · have hap : 0<a := lt_of_le_of_ne ha (Ne.symm haz)
    have hd : (b/a)^2+(c/a)^2 ≤ 1 := by
      have hh : (b^2+c^2)/a^2 ≤ 1 := (div_le_one (sq_pos_of_pos hap)).2 hbc
      simpa only [div_pow, add_div] using hh
    have hh := mul_le_mul_of_nonneg_left (disc_inequality (b/a) (c/a) hd)
      (show 0 ≤ 2*a by positivity)
    have hs (x : ℝ) : Real.sqrt (a*(a+x/2)) = a*Real.sqrt (1+(x/a)/2) := by
      have he : a*(a+x/2) = a^2*(1+(x/a)/2) := by field_simp [haz] <;> ring
      rw [he, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
    have hst : Real.sqrt ((a+b/2)*(a+c/2)) =
        a*Real.sqrt ((1+(b/a)/2)*(1+(c/a)/2)) := by
      have he : (a+b/2)*(a+c/2) = a^2*((1+(b/a)/2)*(1+(c/a)/2)) := by
        field_simp [haz] <;> ring
      rw [he, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
    have hlin : 2*a*(36/25+(53/200)*(b/a+c/a)) =
        (72/25 : ℝ)*a+(53/100)*(b+c) := by field_simp [haz] <;> ring
    rw [hs b, hs c, hst]
    nlinarith only [hh,hlin]

end D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation


namespace D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_of_posSemidef)

set_option maxHeartbeats 600000

private theorem sqrt_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (p : n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    CFC.sqrt (Matrix.diagonal (fun i => (p i : ℂ))) =
      Matrix.diagonal (fun i => (Real.sqrt (p i) : ℂ)) := by
  have hP : (Matrix.diagonal (fun i => (p i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr (hp i))
  rw [CFC.sqrt_eq_real_sqrt _ hP.nonneg, cfcₙ_eq_cfc]
  exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
    Real.sqrt p

private theorem uhlmann_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (p q : n → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    uhlmann (Matrix.diagonal (fun i => (p i : ℂ)))
      (Matrix.diagonal (fun i => (q i : ℂ))) = ∑ i, Real.sqrt (p i * q i) := by
  rw [uhlmann, sqrt_diagonal p hp, sqrt_diagonal q hq, Matrix.diagonal_mul_diagonal]
  have hD : (Matrix.diagonal (fun i =>
      (Real.sqrt (p i) : ℂ) * (Real.sqrt (q i) : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact mul_nonneg (Complex.zero_le_real.mpr (Real.sqrt_nonneg _))
      (Complex.zero_le_real.mpr (Real.sqrt_nonneg _))
  have hh := congrArg Complex.re (traceNorm_of_posSemidef hD)
  simpa [Matrix.trace_diagonal, map_sum, ← Complex.ofReal_mul, ← Real.sqrt_mul (hp _)] using hh

end D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation

namespace D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (bloch)
open scoped ComplexOrder MatrixOrder

private def classicalCost (E : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Real.sqrt ((Matrix.trace (E*qubitR)).re*(Matrix.trace (E*qubitA)).re) +
  Real.sqrt ((Matrix.trace (E*qubitR)).re*(Matrix.trace (E*qubitB)).re) +
  Real.sqrt ((Matrix.trace (E*qubitA)).re*(Matrix.trace (E*qubitB)).re)

private theorem effect_lower_bound (E : Matrix (Fin 2) (Fin 2) ℂ) (hE : E.PosSemidef) :
    (72/25 : ℝ)*((Matrix.trace E).re/2)+(53/100)*((bloch E 2/2)+(bloch E 0/2)) ≤ classicalCost E := by
  obtain ⟨hR,hA,hB⟩ := effect_probabilities E hE
  have hc := effect_coordinates E hE
  simpa [classicalCost,hR,hA,hB] using
    scalar_effect_bound (((Matrix.trace E).re/2)) ((bloch E 2/2)) ((bloch E 0/2)) hc.1 hc.2

private theorem povm_pair_sum_bound {m : ℕ}
    (Λ : Fin m → Matrix (Fin 2) (Fin 2) ℂ) (hΛ : IsPOVM Λ) :
    (72/25 : ℝ) ≤
      uhlmann ((Matrix.diagonal (fun x => Matrix.trace (Λ x * qubitR)))) ((Matrix.diagonal (fun x => Matrix.trace (Λ x * qubitA)))) +
      uhlmann ((Matrix.diagonal (fun x => Matrix.trace (Λ x * qubitR)))) ((Matrix.diagonal (fun x => Matrix.trace (Λ x * qubitB)))) +
      uhlmann ((Matrix.diagonal (fun x => Matrix.trace (Λ x * qubitA)))) ((Matrix.diagonal (fun x => Matrix.trace (Λ x * qubitB)))) := by
  let pR : Fin m → ℝ := fun x => (Matrix.trace (Λ x*qubitR)).re
  let pA : Fin m → ℝ := fun x => (Matrix.trace (Λ x*qubitA)).re
  let pB : Fin m → ℝ := fun x => (Matrix.trace (Λ x*qubitB)).re
  have hR : (Matrix.diagonal (fun x => Matrix.trace (Λ x * qubitR))) = Matrix.diagonal (fun x => (pR x : ℂ)) := by
    congr 1
    funext x
    dsimp [pR]
    rw [(effect_probabilities (Λ x) (hΛ.1 x)).1]
    simp
  have hA : (Matrix.diagonal (fun x => Matrix.trace (Λ x * qubitA))) = Matrix.diagonal (fun x => (pA x : ℂ)) := by
    congr 1
    funext x
    dsimp [pA]
    rw [(effect_probabilities (Λ x) (hΛ.1 x)).2.1]
    simp
  have hB : (Matrix.diagonal (fun x => Matrix.trace (Λ x * qubitB))) = Matrix.diagonal (fun x => (pB x : ℂ)) := by
    congr 1
    funext x
    dsimp [pB]
    rw [(effect_probabilities (Λ x) (hΛ.1 x)).2.2]
    simp
  have hpR : ∀ x, 0 ≤ pR x := fun x => (effect_probabilities_nonneg (Λ x) (hΛ.1 x)).1
  have hpA : ∀ x, 0 ≤ pA x := fun x => (effect_probabilities_nonneg (Λ x) (hΛ.1 x)).2.1
  have hpB : ∀ x, 0 ≤ pB x := fun x => (effect_probabilities_nonneg (Λ x) (hΛ.1 x)).2.2
  rw [hR,hA,hB,uhlmann_diagonal pR pA hpR hpA,
    uhlmann_diagonal pR pB hpR hpB,uhlmann_diagonal pA pB hpA hpB]
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => effect_lower_bound (Λ x) (hΛ.1 x))
  have hcoords := povm_coordinates Λ hΛ
  have hbase : (∑ x, ((72/25 : ℝ)*((Matrix.trace (Λ x)).re/2)+(53/100)*((bloch (Λ x) 2/2)+(bloch (Λ x) 0/2))))=72/25 := by
    rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,
      Finset.sum_add_distrib,hcoords.1,hcoords.2.1,hcoords.2.2]
    ring
  rw [hbase] at hsum
  simpa [classicalCost,Finset.sum_add_distrib,pR,pA,pB] using hsum

end D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation

namespace D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation
open Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
private theorem traceNorm_sq_two (T : Matrix (Fin 2) (Fin 2) ℂ) :
    traceNorm T ^ 2 = (Tᴴ*T).trace.re + 2*‖T.det‖ := by
  have h : (CFC.sqrt (Tᴴ*T)).trace.re ^ 2 =
      (Tᴴ*T).trace.re + 2*‖T.det‖ := by
    exact D5.S3.Quantum.Schatten.TraceNorm.transitionMass_sq T
  change (CFC.sqrt (Tᴴ*T)).trace.re ^ 2 = _
  exact h

end D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation

namespace D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation
open Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)

private theorem gram_root_trace (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Matrix.trace ((CFC.sqrt A*CFC.sqrt B)ᴴ*(CFC.sqrt A*CFC.sqrt B)) =
      Matrix.trace (A*B) := by
  have hsA := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have owner : D5.S3.QuantumStates.GNSZeroPropagation.stateFunctional B
      ((CFC.sqrt A)ᴴ * CFC.sqrt A) =
      Matrix.trace ((CFC.sqrt A*CFC.sqrt B)ᴴ*(CFC.sqrt A*CFC.sqrt B)) := by
    exact D5.S3.QuantumStates.GNSZeroPropagation.cross_trace_factorization
      B (CFC.sqrt A) (CFC.sqrt A) hB
  rw [D5.S3.QuantumStates.GNSZeroPropagation.stateFunctional, hsA,
    CFC.sqrt_mul_sqrt_self A hA.nonneg] at owner
  exact owner.symm.trans (Matrix.trace_mul_comm B A)

private theorem uhlmann_sq_formula (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    uhlmann A B^2 = (Matrix.trace (A*B)).re +
      2*‖(CFC.sqrt A).det‖*‖(CFC.sqrt B).det‖ := by
  rw [uhlmann,traceNorm_sq_two,gram_root_trace A B hA hB,Matrix.det_mul,norm_mul]
  ring

private theorem qubit_root_determinants :
    (CFC.sqrt qubitR).det=(1/2 : ℂ) ∧
    (CFC.sqrt qubitA).det=((Real.sqrt 3/4 : ℝ) : ℂ) ∧
    (CFC.sqrt qubitB).det=((Real.sqrt 3/4 : ℝ) : ℂ) := by
  have hR : qubitR.det=(1/4 : ℂ) := by norm_num [qubitR,Matrix.det_fin_two]
  have hA : qubitA.det=(3/16 : ℂ) := by norm_num [qubitA,Matrix.det_fin_two]
  have hB : qubitB.det=(3/16 : ℂ) := by norm_num [qubitB,Matrix.det_fin_two]
  refine ⟨?_, ?_, ?_⟩
  · rw [qubit_states_psd.1.det_sqrt,hR,
      RCLike.sqrt_of_nonneg (show (0 : ℂ) ≤ 1/4 by norm_num [Complex.nonneg_iff,Complex.div_re,Complex.div_im])]
    norm_num [Real.sqrt_div]
  · rw [qubit_states_psd.2.1.det_sqrt,hA,
      RCLike.sqrt_of_nonneg (show (0 : ℂ) ≤ 3/16 by norm_num [Complex.nonneg_iff,Complex.div_re,Complex.div_im])]
    norm_num [Real.sqrt_div]
  · rw [qubit_states_psd.2.2.det_sqrt,hB,
      RCLike.sqrt_of_nonneg (show (0 : ℂ) ≤ 3/16 by norm_num [Complex.nonneg_iff,Complex.div_re,Complex.div_im])]
    norm_num [Real.sqrt_div]

private theorem qubit_fidelity_squares :
    uhlmann qubitR qubitA^2=1/2+Real.sqrt 3/4 ∧
    uhlmann qubitR qubitB^2=1/2+Real.sqrt 3/4 ∧
    uhlmann qubitA qubitB^2=(7/8 : ℝ) := by
  have hR : ‖(CFC.sqrt qubitR).det‖=(1/2 : ℝ) := by
    rw [qubit_root_determinants.1]
    norm_num
  have hA : ‖(CFC.sqrt qubitA).det‖=Real.sqrt 3/4 := by
    rw [qubit_root_determinants.2.1]
    norm_num [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_nonneg (Real.sqrt_nonneg 3)]
  have hB : ‖(CFC.sqrt qubitB).det‖=Real.sqrt 3/4 := by
    rw [qubit_root_determinants.2.2]
    norm_num [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_nonneg (Real.sqrt_nonneg 3)]
  have htRA : (Matrix.trace (qubitR*qubitA)).re=1/2 := by
    norm_num [qubitR,qubitA,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two]
  have htRB : (Matrix.trace (qubitR*qubitB)).re=1/2 := by
    norm_num [qubitR,qubitB,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two]
  have htAB : (Matrix.trace (qubitA*qubitB)).re=1/2 := by
    norm_num [qubitA,qubitB,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two]
  have hRA := uhlmann_sq_formula qubitR qubitA qubit_states_psd.1 qubit_states_psd.2.1
  have hRB := uhlmann_sq_formula qubitR qubitB qubit_states_psd.1 qubit_states_psd.2.2
  have hAB := uhlmann_sq_formula qubitA qubitB qubit_states_psd.2.1 qubit_states_psd.2.2
  rw [htRA,hR,hA] at hRA
  rw [htRB,hR,hB] at hRB
  rw [htAB,hA,hB] at hAB
  refine ⟨by nlinarith only [hRA],by nlinarith only [hRB],?_⟩
  nlinarith only [hAB,Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

private theorem FU_witness_lt : FU witnessStates < (24/25 : ℝ) := by
  have hk : Real.sqrt 3 < 7/4 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),Real.sqrt_nonneg 3]
  have hRA : uhlmann qubitR qubitA < (97/100 : ℝ) := by
    have h := qubit_fidelity_squares.1
    have hn := D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_nonneg
      (CFC.sqrt qubitR*CFC.sqrt qubitA)
    change 0 ≤ uhlmann qubitR qubitA at hn
    nlinarith
  have hRB : uhlmann qubitR qubitB < (97/100 : ℝ) := by
    have h := qubit_fidelity_squares.2.1
    have hn := D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_nonneg
      (CFC.sqrt qubitR*CFC.sqrt qubitB)
    change 0 ≤ uhlmann qubitR qubitB at hn
    nlinarith
  have hAB : uhlmann qubitA qubitB < (94/100 : ℝ) := by
    have h := qubit_fidelity_squares.2.2
    have hn := D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_nonneg
      (CFC.sqrt qubitA*CFC.sqrt qubitB)
    change 0 ≤ uhlmann qubitA qubitB at hn
    nlinarith
  unfold FU
  rw [sum_pairs_three]
  change (2 : ℝ)/(3*(3-1))*(uhlmann qubitR qubitA+uhlmann qubitR qubitB+
    uhlmann qubitA qubitB)<24/25
  have hcoeff : (2 : ℝ)/(3*(3-1))=1/3 := by norm_num
  rw [hcoeff]
  linarith

end D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation

namespace D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)

open scoped ComplexOrder MatrixOrder

private theorem povm_index_nonempty : Nonempty (Σ m : ℕ, {Λ : Fin m → Matrix (Fin 2) (Fin 2) ℂ // IsPOVM Λ}) := by
  refine ⟨⟨1, ⟨fun _ => 1, ?_⟩⟩⟩
  exact ⟨fun _ => Matrix.PosSemidef.one, by simp⟩

private theorem FM_witness_ge : (24/25 : ℝ) ≤ FM witnessStates := by
  haveI := povm_index_nonempty
  have hl : (72/25 : ℝ) ≤
      ⨅ P : (Σ m : ℕ, {Λ : Fin m → Matrix (Fin 2) (Fin 2) ℂ // IsPOVM Λ}),
        (uhlmann ((Matrix.diagonal (fun x => Matrix.trace (P.2.val x * qubitR)))) ((Matrix.diagonal (fun x => Matrix.trace (P.2.val x * qubitA)))) +
         uhlmann ((Matrix.diagonal (fun x => Matrix.trace (P.2.val x * qubitR)))) ((Matrix.diagonal (fun x => Matrix.trace (P.2.val x * qubitB)))) +
         uhlmann ((Matrix.diagonal (fun x => Matrix.trace (P.2.val x * qubitA)))) ((Matrix.diagonal (fun x => Matrix.trace (P.2.val x * qubitB))))) := by
    apply le_ciInf
    intro P
    exact povm_pair_sum_bound P.2.val P.2.property
  have hp (P : (Σ m : ℕ, {Λ : Fin m → Matrix (Fin 2) (Fin 2) ℂ // IsPOVM Λ})) :
      (∑ i : Fin 3, ∑ j ∈ Finset.Ioi i,
        uhlmann (Matrix.diagonal (fun x => Matrix.trace (P.2.val x * CStarMatrix.ofMatrix.symm (witnessStates i).val)))
          (Matrix.diagonal (fun x => Matrix.trace (P.2.val x * CStarMatrix.ofMatrix.symm (witnessStates j).val)))) =
        uhlmann ((Matrix.diagonal (fun x => Matrix.trace (P.2.val x * qubitR)))) ((Matrix.diagonal (fun x => Matrix.trace (P.2.val x * qubitA)))) +
        uhlmann ((Matrix.diagonal (fun x => Matrix.trace (P.2.val x * qubitR)))) ((Matrix.diagonal (fun x => Matrix.trace (P.2.val x * qubitB)))) +
        uhlmann ((Matrix.diagonal (fun x => Matrix.trace (P.2.val x * qubitA)))) ((Matrix.diagonal (fun x => Matrix.trace (P.2.val x * qubitB)))) := by
    rw [sum_pairs_three]
    rfl
  unfold FM
  simp_rw [hp]
  norm_num only [Nat.cast_ofNat]
  linarith

theorem result : D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.claim := by
  exact ⟨2, 3, witnessStates, FU_witness_lt.trans_le FM_witness_ge⟩

end D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation
