/- GID: D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hidden-matching cloning has mean marginal fidelity at most one half plus 1/n. -/

/-
admission_basis: open-problem-resolution (#24701; Proved)
escape_witness: none
The settling result and its consumed helpers use finite-sum/parity rewriting,
existing estimates, and normalization; no declaration claims independent content.
Definitions describe the source objects and the auxiliary finite matrix certificate.
The public phi keeps the preregistered power of −1. The proofs use complexSign
and identify the two forms at phi_outer_entry via complex_sign_val.
Direct frozen dependencies are declaration identities at base 3476ce98dd3c4326181683b37fc2ddad3e33a743.
The publicized selectors retain their base private declaration identities until canonical re-pin.
  F2: D5/S3/Quantum/Entanglement/UniversalReplacementCapacityGrowth.pure_trace
    statement_id: sha256:10a7dafe6e7a6b1cf2bcce71b142fca1562280cfd40a3330284db5fc95180878
  F3: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap
    statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
  F4: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
    statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
  F5: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus._proof_1
    statement_id: sha256:5dc7bcde8ce2ae710c058683e5324d31e0ca70317f167566967eee1cf3b23bbb
  F6: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus._proof_2
    statement_id: sha256:9b70ce4858eb731b17facafe93b167007eb9ca6533c641dc770fc553d31ddaa1
  F7: D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel
    statement_id: sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05
  F8: D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap
    statement_id: sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc
  F9: D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.trace_preserving
    statement_id: sha256:f7348a8905d2b54384d2e26b2c769f3d8eae0d734f588b9c2c8b8cc3892faf15
  F10: D5/S3/Quantum/Information/HedgingMajorityThreshold.trace_retained
    statement_id: sha256:db986ec7f4f4d0976fd1f41480c2c93228a7b154675ebf6ad636fb227b538d39
  F11: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft
    statement_id: sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d
  F12: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight
    statement_id: sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
  F13: D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.choi_tensor_pair
    statement_id: sha256:380687bfe14a0a9a1c783ea8cf9072cd406a6247d9a1896729abf2bf0d2f6603
  F14: D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.inputFirstChoi
    statement_id: sha256:7620ae518a39944b6825fd260cd713177187b28856493804968f5ddc77f33bd0
  F15: D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.matrixAction
    statement_id: sha256:83ac791e170c8f29d6ff3fedd7eb6d261e6a7ec791b03ef14422460da17cc9dc
  F16: D5/S3/Weil/ProjectiveRayleigh/ScaledComplexQuadraticRowBound.norm_complex_quadratic_le_scaled_rows
    statement_id: sha256:0546d1b31c5831f1ec46dc0ae54d7592aac449e3f961a4ea5c4b83a26803cd2a
  F17: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.SignQuotient.complexSign
  F18: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.sign_square
  F19: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.SignQuotient.complexSign_add
  F20: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.sign_one
  F21: D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.complex_sign_val
  F22: Matrix.trace_submatrix
  F23: D5/S3/Quantum/FixedPointProjection.Choi.fromBipartitePairing
  F24: D5/S3/Quantum/FixedPointProjection.Marginal.traceLocalLeft
  F25: D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg
  F26: D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg_univ
proof_shape: sign_sq: bind-only; consumers: moment_two, moment_four
  Direct frozen dependencies: F17, F18
proof_shape: sign_flip: bind-only; consumers: moment_two, moment_four
  Direct frozen dependencies: F17, F19, F20
proof_shape: sum_flip_zero: bind-only; consumers: moment_two, moment_four
  Direct frozen dependencies: none
proof_shape: moment_two: bind-only; consumers: moment_four
  Direct frozen dependencies: F17, F18, F19, F20
proof_shape: momentEntry: bind-only; consumers: moment_four, momentEntry_eq, momentEntry_nonneg, momentEntry_symm, L, L_nonneg, L_symm, L_row, performance_eq_L
  Direct frozen dependencies: none
proof_shape: moment_four: bind-only; consumers: performance_eq_L
  Direct frozen dependencies: F17, F18, F19, F20
proof_shape: momentEntry_eq: bind-only; consumers: momentEntry_nonneg, momentEntry_symm
  Direct frozen dependencies: none
proof_shape: momentEntry_nonneg: bind-only; consumers: L_nonneg
  Direct frozen dependencies: none
proof_shape: momentEntry_symm: bind-only; consumers: L_symm
  Direct frozen dependencies: none
proof_shape: L: bind-only; consumers: L_nonneg, L_symm, L_row, weight_row_bound, L_quadratic_bound, performance_eq_L, trace_L_outer, trace_L_gram_bound, result
  Direct frozen dependencies: none
proof_shape: weight: bind-only; consumers: weight_pos, weight_diag_sum, weight_diag_sum', weight_row_bound, L_quadratic_bound
  Direct frozen dependencies: none
proof_shape: L_nonneg: bind-only; consumers: L_quadratic_bound
  Direct frozen dependencies: none
proof_shape: L_symm: bind-only; consumers: L_quadratic_bound
  Direct frozen dependencies: none
proof_shape: weight_pos: bind-only; consumers: L_quadratic_bound
  Direct frozen dependencies: none
proof_shape: L_row: bind-only; consumers: weight_row_bound
  Direct frozen dependencies: none
proof_shape: weight_diag_sum: bind-only; consumers: weight_diag_sum', weight_row_bound
  Direct frozen dependencies: none
proof_shape: weight_diag_sum': bind-only; consumers: weight_row_bound
  Direct frozen dependencies: none
proof_shape: weight_row_bound: bind-only; consumers: L_quadratic_bound
  Direct frozen dependencies: none
proof_shape: L_quadratic_bound: bind-only; consumers: trace_L_gram_bound
  Direct frozen dependencies: F16
proof_shape: phi: bind-only; consumers: rho, meanFidelity, phi_outer_entry, perf_pair, meanFidelity_pair
  Direct frozen dependencies: none
proof_shape: rho: bind-only; consumers: eta, tau, perf, rho_entry, perf_pair, perf_entry
  Direct frozen dependencies: none
proof_shape: eta: bind-only; consumers: meanFidelity, perf_pair, meanFidelity_pair
  Direct frozen dependencies: F12, F8, F7
proof_shape: tau: bind-only; consumers: meanFidelity, perf_pair, meanFidelity_pair
  Direct frozen dependencies: F8, F11, F7
proof_shape: meanFidelity: bind-only; consumers: claim, meanFidelity_pair, result
  Direct frozen dependencies: F12, F8, F11, F7
proof_shape: claim: bind-only; consumers: result
  Direct frozen dependencies: F12, F8, F11, F7
proof_shape: choi_trace: bind-only; consumers: result
  Direct frozen dependencies: F9, F8, F15, F3, F7, F14, F23
proof_shape: choi_reindex: bind-only; consumers: choi_gram, perf_pair
  Direct frozen dependencies: F8, F15, F7, F14
proof_shape: choi_gram: bind-only; consumers: result
  Direct frozen dependencies: F4, F5, F6, F8, F15, F3, F7, F14
proof_shape: choi_tensor_pair: bind-only; consumers: perf_pair
  Direct frozen dependencies: F13, F3, F22
proof_shape: trace_right_pair: bind-only; consumers: perf_pair
  Direct frozen dependencies: F12, F24
proof_shape: trace_left_pair: bind-only; consumers: perf_pair
  Direct frozen dependencies: F11, F10
proof_shape: perf: bind-only; consumers: performance, perf_pair, perf_entry, performance_eq_L, meanFidelity_pair
  Direct frozen dependencies: none
proof_shape: performance: bind-only; consumers: performance_eq_L, meanFidelity_pair, result
  Direct frozen dependencies: F25
proof_shape: phi_outer_entry: bind-only; consumers: rho_entry
  Direct frozen dependencies: F17, F21
proof_shape: rho_entry: bind-only; consumers: perf_entry
  Direct frozen dependencies: F17, F21
proof_shape: perf_pair: bind-only; consumers: meanFidelity_pair
  Direct frozen dependencies: F12, F8, F15, F13, F3, F11, F7, F14, F10, F22, F24
proof_shape: perf_entry: bind-only; consumers: performance_eq_L
  Direct frozen dependencies: F17, F21
proof_shape: performance_eq_L: bind-only; consumers: result
  Direct frozen dependencies: F17, F18, F19, F20, F21, F25, F26
proof_shape: meanFidelity_pair: bind-only; consumers: result
  Direct frozen dependencies: F12, F8, F15, F13, F3, F11, F7, F14, F10, F22, F24, F25, F26
proof_shape: trace_outer_re: bind-only; consumers: trace_L_gram_bound
  Direct frozen dependencies: F2
proof_shape: trace_L_outer: bind-only; consumers: trace_L_gram_bound
  Direct frozen dependencies: none
proof_shape: trace_L_gram_bound: bind-only; consumers: result
  Direct frozen dependencies: F2, F16
proof_shape: result: bind-only; consumers: settling result
  Direct frozen dependencies: F4, F12, F5, F9, F6, F8, F15, F2, F13, F3, F11, F7, F14, F10, F16,
    F17, F18, F19, F20, F21, F22, F23, F24, F25, F26
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/31047
-/

import D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue
import D5.S3.Quantum.FixedPointProjection
import D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation
import D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
import D5.S3.Quantum.Information.HedgingMajorityThreshold
import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix.Positivity
import D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth
import D5.S3.Weil.ProjectiveRayleigh.ScaledComplexQuadraticRowBound
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Foundation.FiniteKrausChannel

/-! The channel fidelity bound for the uniform binary-sign ensemble. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient (complexSign complexSign_add)
open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (complex_sign_val)

open scoped BigOperators
namespace D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound
noncomputable section

private theorem sign_sq (s : Fin 2) :
    complexSign (s.val : ZMod 2) * complexSign (s.val : ZMod 2) = 1 :=
  D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_square (s.val : ZMod 2)

private theorem sign_flip {n : ℕ} (i j : Fin n) (x : Fin n → Fin 2) :
    complexSign (((Equiv.piCongrRight
      (fun k => if k = i then finRotate 2 else Equiv.refl _)) x j).val : ZMod 2) =
      (if j = i then -1 else 1) * complexSign ((x j).val : ZMod 2) := by
  by_cases h : j = i
  · subst j
    have hcast : ((finRotate 2 (x i)).val : ZMod 2) = ((x i).val : ZMod 2) + 1 := by
      simp only [finRotate_apply, Fin.val_add, Fin.val_one, ZMod.natCast_mod,
        Nat.cast_add, Nat.cast_one]
    have hs : complexSign ((finRotate 2 (x i)).val : ZMod 2) =
        -complexSign ((x i).val : ZMod 2) := calc
      _ = complexSign (((x i).val : ZMod 2) + 1) := congrArg complexSign hcast
      _ = -complexSign ((x i).val : ZMod 2) := by
        rw [complexSign_add, D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_one,
          mul_neg_one]
    simpa [Equiv.piCongrRight] using hs
  · simp [Equiv.piCongrRight, h]

private theorem sum_flip_zero {n : ℕ} (i : Fin n) (f : (Fin n → Fin 2) → ℂ)
    (hf : ∀ x, f ((Equiv.piCongrRight (fun j => if j = i then finRotate 2 else Equiv.refl _)) x) = -f x) : ∑ x, f x = 0 := by
  let e := Equiv.piCongrRight (fun j : Fin n => if j = i then finRotate 2 else Equiv.refl _)
  refine Finset.sum_ninvolution e (fun x => by rw [hf x, add_neg_cancel]) ?_
    (fun _ => Finset.mem_univ _) ?_
  · intro x hfx hfix
    apply hfx
    have hx := hf x
    change f (e x) = -f x at hx
    rw [hfix] at hx
    exact CharZero.eq_neg_self_iff.mp hx
  · intro x
    funext j
    by_cases h : j = i
    · simp only [e, Equiv.piCongrRight_apply, Pi.map_apply, if_pos h, finRotate_apply]
      rw [add_assoc, show (1 : Fin 2) + 1 = 0 by decide, add_zero]
    · simp only [e, Equiv.piCongrRight_apply, Pi.map_apply, if_neg h, Equiv.refl_apply]

private theorem moment_two {n : ℕ} (a b : Fin n) :
    (∑ x : Fin n → Fin 2, complexSign ((x a).val : ZMod 2) * complexSign ((x b).val : ZMod 2)) =
      (2 : ℂ)^n * (if a = b then 1 else 0) := by
  by_cases h : a = b
  · subst b
    simp [sign_sq]
  · simp only [if_neg h, mul_zero]
    apply sum_flip_zero a
    intro x
    rw [sign_flip a a x, sign_flip a b x]
    simp [Ne.symm h]

private def momentEntry {ι : Type*} [DecidableEq ι] (a b c d : ι) : ℝ :=
  (if a = b ∧ c = d then 1 else 0) +
  (if a = c ∧ b = d then 1 else 0) +
  (if a = d ∧ b = c then 1 else 0) -
  2 * (if a = b ∧ b = c ∧ c = d then 1 else 0)

private theorem moment_four {n : ℕ} (a b c d : Fin n) :
    (∑ x : Fin n → Fin 2, complexSign ((x a).val : ZMod 2) * complexSign ((x b).val : ZMod 2) *
      complexSign ((x c).val : ZMod 2) * complexSign ((x d).val : ZMod 2)) =
      (2 : ℂ)^n * (momentEntry a b c d : ℂ) := by
  by_cases hab : a = b
  · subst b
    simp_rw [sign_sq, one_mul]
    rw [moment_two]
    by_cases hcd : c = d <;> by_cases hac : a = c <;>
      simp_all [momentEntry] <;> norm_num
  · by_cases hac : a = c
    · subst c
      have hp (x : Fin n → Fin 2) :
          complexSign ((x a).val : ZMod 2) * complexSign ((x b).val : ZMod 2) *
            complexSign ((x a).val : ZMod 2) * complexSign ((x d).val : ZMod 2) =
            complexSign ((x b).val : ZMod 2) * complexSign ((x d).val : ZMod 2) := by
        calc
          _ = (complexSign ((x a).val : ZMod 2) * complexSign ((x a).val : ZMod 2)) * (
            complexSign ((x b).val : ZMod 2) * complexSign ((x d).val : ZMod 2)) := by ring
          _ = _ := by rw [sign_sq, one_mul]
      simp_rw [hp]
      rw [moment_two]
      by_cases hbd : b = d <;> simp_all [momentEntry, eq_comm]
    · by_cases had : a = d
      · subst d
        have hp (x : Fin n → Fin 2) :
            complexSign ((x a).val : ZMod 2) * complexSign ((x b).val : ZMod 2) *
              complexSign ((x c).val : ZMod 2) * complexSign ((x a).val : ZMod 2) =
              complexSign ((x b).val : ZMod 2) * complexSign ((x c).val : ZMod 2) := by
          calc
            _ = (complexSign ((x a).val : ZMod 2) * complexSign ((x a).val : ZMod 2)) * (
              complexSign ((x b).val : ZMod 2) * complexSign ((x c).val : ZMod 2)) := by ring
            _ = _ := by rw [sign_sq, one_mul]
        simp_rw [hp]
        rw [moment_two]
        by_cases hbc : b = c <;> simp_all [momentEntry, eq_comm]
      · have hz : (∑ x : Fin n → Fin 2,
            complexSign ((x a).val : ZMod 2) * complexSign ((x b).val : ZMod 2) *
              complexSign ((x c).val : ZMod 2) * complexSign ((x d).val : ZMod 2)) = 0 := by
          apply sum_flip_zero a
          intro x
          rw [sign_flip a a x, sign_flip a b x, sign_flip a c x, sign_flip a d x]
          simp [Ne.symm hab, Ne.symm hac, Ne.symm had]
        simp [hz, momentEntry, hab, hac, had]

end
end D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound


open scoped BigOperators
namespace D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound
noncomputable section


private theorem momentEntry_eq {ι : Type*} [DecidableEq ι] (a b c d : ι) :
    momentEntry a b c d =
      if (a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c) then 1 else 0 := by
  by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases had : a = d <;>
    by_cases hbc : b = c <;> by_cases hbd : b = d <;> by_cases hcd : c = d <;>
    simp_all [momentEntry] <;> norm_num

private theorem momentEntry_nonneg {ι : Type*} [DecidableEq ι] (a b c d : ι) :
    0 ≤ momentEntry a b c d := by
  rw [momentEntry_eq]
  split_ifs <;> norm_num

private theorem momentEntry_symm {ι : Type*} [DecidableEq ι] (a b c d : ι) :
    momentEntry a b c d = momentEntry c d a b := by
  simp only [momentEntry_eq]
  have h : ((a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ↔
      ((c = d ∧ a = b) ∨ (c = a ∧ d = b) ∨ (c = b ∧ d = a)) := by
    constructor <;> rintro (h | h | h) <;> simp_all [eq_comm]
  simp only [h]


private def L (n : ℕ) (p q : (Fin n × Fin n × Fin n)) : ℝ :=
  (if p.2.2 = q.2.2 then momentEntry p.1 p.2.1 q.1 q.2.1 else 0) +
  (if p.2.1 = q.2.1 then momentEntry p.1 p.2.2 q.1 q.2.2 else 0)

private def weight (n : ℕ) (p : (Fin n × Fin n × Fin n)) : ℝ :=
  if p.2.1 = p.2.2 then (if p.1 = p.2.1 then 2 * ((n : ℝ) - 1) else 2) else n

private theorem L_nonneg (n : ℕ) (p q : (Fin n × Fin n × Fin n)) : 0 ≤ L n p q := by
  have h₁ := momentEntry_nonneg p.1 p.2.1 q.1 q.2.1
  have h₂ := momentEntry_nonneg p.1 p.2.2 q.1 q.2.2
  unfold L
  split_ifs <;> linarith

private theorem L_symm (n : ℕ) (p q : (Fin n × Fin n × Fin n)) : L n p q = L n q p := by
  unfold L
  rw [momentEntry_symm p.1 p.2.1 q.1 q.2.1,
    momentEntry_symm p.1 p.2.2 q.1 q.2.2]
  simp only [eq_comm]

private theorem weight_pos (n : ℕ) (hn : 2 ≤ n) (p : (Fin n × Fin n × Fin n)) : 0 < weight n p := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold weight
  split_ifs <;> linarith

/-- Explicit action of the fourth-moment operator on any tensor coefficient array. -/
private theorem L_row (n : ℕ) (f : (Fin n × Fin n × Fin n) → ℝ) (a b c : Fin n) :
    (∑ q, L n (a,b,c) q * f q) =
      2 * f (a,b,c) + f (b,a,c) + f (c,b,a) +
      (if a = b then ∑ i, f (i,i,c) else 0) +
      (if a = c then ∑ i, f (i,b,i) else 0) -
      2 * (if a = b then f (a,b,c) else 0) -
      2 * (if a = c then f (a,b,c) else 0) := by
  simp only [L, Fintype.sum_prod_type, add_mul, Finset.sum_add_distrib,
    ite_mul, zero_mul]
  simp only [momentEntry, sub_mul, add_mul, ite_mul, zero_mul, one_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq]
  split_ifs <;> simp_all [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_ite_irrel, Finset.sum_const_zero] <;> ring

private theorem weight_diag_sum (n : ℕ) (c : Fin n) :
    (∑ i, weight n (i,i,c)) = (n : ℝ)^2 + n - 2 := by
  have hp (i : Fin n) : weight n (i,i,c) =
      (n : ℝ) + (if i = c then (n : ℝ) - 2 else 0) := by
    by_cases h : i = c <;> simp [weight, h] <;> ring
  simp_rw [hp]
  simp [Finset.sum_add_distrib]
  ring

private theorem weight_diag_sum' (n : ℕ) (b : Fin n) :
    (∑ i, weight n (i,b,i)) = (n : ℝ)^2 + n - 2 := by
  rw [← weight_diag_sum n b]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i = b <;> simp_all [weight, eq_comm]


private theorem weight_row_bound (n : ℕ) (hn : 2 ≤ n) (p : (Fin n × Fin n × Fin n)) :
    (∑ q, L n p q * weight n q) ≤ ((n : ℝ) + 2) * weight n p := by
  rcases p with ⟨a,b,c⟩
  rw [L_row, weight_diag_sum, weight_diag_sum']
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 2) := mul_nonneg (by positivity) (by linarith)
  by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases hbc : b = c <;>
    simp_all [weight, eq_comm] <;> nlinarith

end
end D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound


open scoped BigOperators ComplexConjugate
namespace D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound
noncomputable section


/-- The dimension-uniform quadratic-form ceiling of the parity operator. -/
private theorem L_quadratic_bound (n : ℕ) (hn : 2 ≤ n) (z : (Fin n × Fin n × Fin n) → ℂ) :
    (∑ p, ∑ q, star (z p) * z q * (L n p q : ℂ)).re ≤
      ((n : ℝ) + 2) * ∑ p, ‖z p‖ ^ 2 := by
  have hnL (p q : (Fin n × Fin n × Fin n)) : ‖(L n p q : ℂ)‖ = L n p q := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (L_nonneg n p q)]
  have h := D5.S3.Weil.ProjectiveRayleigh.ScaledComplexQuadraticRowBound.norm_complex_quadratic_le_scaled_rows
    (fun p => star (z p)) (fun p q => (L n p q : ℂ)) (fun _ => 1)
    (weight n) ((n : ℝ) + 2) (weight_pos n hn)
    (by intro p q; rw [hnL, hnL, L_symm])
    (by intro p; simp only [hnL, mul_one]; exact weight_row_bound n hn p)
  simpa only [starRingEnd_apply, star_star, one_mul, norm_star] using
    (Complex.re_le_norm _).trans h


end
end D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound


namespace D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound

open scoped BigOperators
open Matrix
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction inputFirstChoi)
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation

noncomputable section

/-- Equation (4): |φ_x⟩ = n^(-1/2) ∑ᵢ (-1)^(xᵢ) |i⟩. -/
def phi (n : ℕ) (x : (Fin n → Fin 2)) : Fin n → ℂ :=
  fun i => (Real.sqrt (n : ℝ) : ℂ)⁻¹ * (-1 : ℂ) ^ (x i).val

/-- The explicit pure input |φ_x⟩⟨φ_x|, using Mathlib's outer product. -/
def rho (n : ℕ) (x : (Fin n → Fin 2)) : CStarMatrix (Fin n) (Fin n) ℂ :=
  CStarMatrix.ofMatrix (Matrix.vecMulVec (phi n x) (star (phi n x)))

/-- Equation (11): η_x = Tr_Z Ψ(|φ_x⟩⟨φ_x|), with output order Y × Z. -/
def eta (n : ℕ) (Ψ : QuantumChannel (Fin n) (Fin n × Fin n)) (x : (Fin n → Fin 2)) :
    Matrix (Fin n) (Fin n) ℂ :=
  partialTraceRight (CStarMatrix.ofMatrix.symm (Ψ.toCompletelyPositiveMap (rho n x)))

/-- Equation (11): τ_x = Tr_Y Ψ(|φ_x⟩⟨φ_x|). -/
def tau (n : ℕ) (Ψ : QuantumChannel (Fin n) (Fin n × Fin n)) (x : (Fin n → Fin 2)) :
    Matrix (Fin n) (Fin n) ℂ :=
  partialTraceLeft (CStarMatrix.ofMatrix.symm (Ψ.toCompletelyPositiveMap (rho n x)))

/-- Equation (11): the uniform average of the two marginal pure-state fidelities.
Real parts merely express the order on the real scalar fidelity. -/
def meanFidelity (n : ℕ) (Ψ : QuantumChannel (Fin n) (Fin n × Fin n)) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : (Fin n → Fin 2),
    (((star (phi n x) ⬝ᵥ ((eta n Ψ x) *ᵥ phi n x)).re +
      (star (phi n x) ⬝ᵥ ((tau n Ψ x) *ᵥ phi n x)).re) / 2)

/-- Equation (21) and its conjecture, on the source's positive even-dimensional domain. -/
def claim : Prop :=
  ∀ (n : ℕ), 2 ≤ n → Even n →
    ∀ (Ψ : QuantumChannel (Fin n) (Fin n × Fin n)),
      meanFidelity n Ψ ≤ (1 : ℝ) / 2 + 1 / (n : ℝ)

end

end D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound

namespace D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open scoped BigOperators Matrix CStarAlgebra ComplexOrder MatrixOrder Kronecker
open Matrix
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction inputFirstChoi)
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
noncomputable section

private theorem choi_trace (n : ℕ) (Ψ : QuantumChannel (Fin n) (Fin n × Fin n)) :
    Matrix.trace ((inputFirstChoi (matrixAction Ψ.toCompletelyPositiveMap))) = n := by
  let N := matrixAction Ψ.toCompletelyPositiveMap
  let J := inputFirstChoi N
  have hswap : J.submatrix Prod.swap Prod.swap = MatrixMap.choi_matrix N := rfl
  have h := D5.S3.Quantum.FixedPointProjection.Choi.fromBipartitePairing J
    (1 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
  change trace (MatrixMap.of_choi_matrix (J.submatrix Prod.swap Prod.swap) 1 * 1) =
    trace (((1 : Matrix (Fin n) (Fin n) ℂ)ᵀ ⊗ₖ
      (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)) * J) at h
  rw [hswap, MatrixMap.choi_map_inv, mul_one, Matrix.transpose_one,
    Matrix.one_kronecker_one, one_mul] at h
  calc
    _ = trace (N 1) := h.symm
    _ = trace (1 : Matrix (Fin n) (Fin n) ℂ) :=
      Ψ.trace_preserving (CStarMatrix.ofMatrix 1)
    _ = _ := by simp

/-- Input-first order is the explicit swap of the canonical output-first Choi owner. -/
private theorem choi_reindex (n : ℕ) (Ψ : QuantumChannel (Fin n) (Fin n × Fin n)) :
    (inputFirstChoi (matrixAction Ψ.toCompletelyPositiveMap)) =
      (D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.choi_matrix
        ((matrixAction Ψ.toCompletelyPositiveMap))).submatrix Prod.swap Prod.swap := rfl

/-- The source-order Choi matrix has the existing finite Kraus Gram decomposition. -/
private theorem choi_gram (n : ℕ) (Ψ : QuantumChannel (Fin n) (Fin n × Fin n)) :
    ∃ z : ((Fin n × Fin n) × Fin n) → (Fin n × Fin n × Fin n) → ℂ,
      (inputFirstChoi (matrixAction Ψ.toCompletelyPositiveMap)) = ∑ r, Matrix.vecMulVec (z r) (star (z r)) := by
  let K := D5.S3.Quantum.Foundation.FiniteKrausChannel.krausRepresentation Ψ.toCompletelyPositiveMap
  have hmap : (matrixAction Ψ.toCompletelyPositiveMap) = MatrixMap.of_kraus K.val K.val := by
    apply LinearMap.ext
    intro M
    change CStarMatrix.ofMatrix.symm
      (Ψ.toCompletelyPositiveMap (CStarMatrix.ofMatrix M)) = _
    simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk] using K.property M
  have hJ := MatrixMap.choi_of_kraus K.val
  rw [← hmap] at hJ
  refine ⟨(fun r p => K.val r p.2 p.1), ?_⟩
  rw [choi_reindex, hJ]
  ext p q
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.vecMulVec,
    Pi.star_apply, Prod.swap, Matrix.of_apply]


end
end D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound


namespace D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound
open Matrix
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction inputFirstChoi)
open scoped BigOperators Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
noncomputable section

/-- Transport of the finite-coordinate Choi pairing to an arbitrary finite output. -/
private theorem choi_tensor_pair {a : ℕ} {B : Type*} [Fintype B]
    [DecidableEq B] (N : MatrixMap (Fin a) B ℂ)
    (Q : Matrix B B ℂ) (P : Matrix (Fin a) (Fin a) ℂ) :
    trace (MatrixMap.choi_matrix N * (Q ⊗ₖ P)) = trace (Q * N Pᵀ) := by
  let b := Fintype.equivFin B
  let N' : MatrixMap (Fin a) (Fin (Fintype.card B)) ℂ :=
    (Matrix.reindexLinearEquiv ℂ ℂ b b).toLinearMap.comp N
  let e := b.prodCongr (Equiv.refl (Fin a))
  have hJ : MatrixMap.choi_matrix N' =
      (MatrixMap.choi_matrix N).submatrix e.symm e.symm := rfl
  have hQ : Matrix.reindex b b Q ⊗ₖ P =
      (Q ⊗ₖ P).submatrix e.symm e.symm := rfl
  have h := D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue.choi_tensor_pair
    N' (Matrix.reindex b b Q) P
  have hleft : trace (MatrixMap.choi_matrix N' * (Matrix.reindex b b Q ⊗ₖ P)) =
      trace (MatrixMap.choi_matrix N * (Q ⊗ₖ P)) := by
    rw [hJ, hQ, Matrix.submatrix_mul_equiv]
    exact Matrix.trace_submatrix (MatrixMap.choi_matrix N * (Q ⊗ₖ P)) e.symm
  have hright : trace (Matrix.reindex b b Q * N' Pᵀ) = trace (Q * N Pᵀ) := by
    change trace (Q.submatrix b.symm b.symm * (N Pᵀ).submatrix b.symm b.symm) = _
    rw [Matrix.submatrix_mul_equiv]
    exact Matrix.trace_submatrix (Q * N Pᵀ) b.symm
  exact hleft.symm.trans (h.trans hright)


private theorem trace_right_pair {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (P : Matrix A A ℂ)
    (O : Matrix (A × B) (A × B) ℂ) :
    trace ((P ⊗ₖ (1 : Matrix B B ℂ)) * O) = trace (P * partialTraceRight O) :=
  D5.S3.Quantum.FixedPointProjection.Marginal.traceLocalLeft O P


private theorem trace_left_pair {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (P : Matrix B B ℂ)
    (O : Matrix (A × B) (A × B) ℂ) :
    trace (((1 : Matrix A A ℂ) ⊗ₖ P) * O) = trace (P * partialTraceLeft O)  := by
  exact D5.S3.Quantum.Information.HedgingMajorityThreshold.trace_retained O P

end
end D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound


namespace D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound
open Matrix
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction inputFirstChoi)
open scoped BigOperators Kronecker ComplexConjugate
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging (avg avg_univ)
noncomputable section

private def perf (n : ℕ) (x : (Fin n → Fin 2)) : Matrix ((Fin n × Fin n × Fin n)) ((Fin n × Fin n × Fin n)) ℂ :=
  (((CStarMatrix.ofMatrix.symm (rho n x) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) +
      ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm (rho n x))) ⊗ₖ
      (CStarMatrix.ofMatrix.symm (rho n x))ᵀ).submatrix Prod.swap Prod.swap

private def performance (n : ℕ) : Matrix ((Fin n × Fin n × Fin n)) ((Fin n × Fin n × Fin n)) ℂ :=
  (2 : ℂ)⁻¹ • avg n Finset.univ (perf n) (fun _ => 0)

private theorem phi_outer_entry (n : ℕ) (x : (Fin n → Fin 2)) (i j : Fin n) :
    phi n x i * star (phi n x j) = (n : ℂ)⁻¹ * complexSign ((x i).val : ZMod 2) * complexSign ((x j).val : ZMod 2) := by
  have hs : (Real.sqrt (n : ℝ) : ℂ)^2 = (n : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hden : (Real.sqrt (n : ℝ) : ℂ)⁻¹ * (Real.sqrt (n : ℝ) : ℂ)⁻¹ = (n : ℂ)⁻¹ := by
    rw [← mul_inv, ← sq, hs]
  simp only [phi, star_mul, star_inv₀, star_pow, star_neg, star_one,
    Complex.star_def, Complex.conj_ofReal, complex_sign_val,
    ZMod.val_natCast_of_lt (x i).isLt, ZMod.val_natCast_of_lt (x j).isLt]
  calc
    _ = ((Real.sqrt (n : ℝ) : ℂ)⁻¹ * (Real.sqrt (n : ℝ) : ℂ)⁻¹) *
        ((-1 : ℂ) ^ (x i).val * (-1 : ℂ) ^ (x j).val) := by ring
    _ = _ := by rw [hden]; ring

private theorem rho_entry (n : ℕ) (x : (Fin n → Fin 2)) (i j : Fin n) :
    CStarMatrix.ofMatrix.symm (rho n x) i j =
      (n : ℂ)⁻¹ * complexSign ((x i).val : ZMod 2) * complexSign ((x j).val : ZMod 2) :=
  phi_outer_entry n x i j

private theorem perf_pair (n : ℕ) (Ψ : QuantumChannel (Fin n) (Fin n × Fin n)) (x : (Fin n → Fin 2)) :
    trace ((inputFirstChoi (matrixAction Ψ.toCompletelyPositiveMap)) * perf n x) =
      (star (phi n x) ⬝ᵥ ((eta n Ψ x) *ᵥ phi n x)) +
      (star (phi n x) ⬝ᵥ ((tau n Ψ x) *ᵥ phi n x)) := by
  let R := CStarMatrix.ofMatrix.symm (rho n x)
  let V : Matrix ((Fin n × Fin n) × Fin n) ((Fin n × Fin n) × Fin n) ℂ :=
    ((R ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) + (1 ⊗ₖ R)) ⊗ₖ Rᵀ
  have hr : trace ((inputFirstChoi (matrixAction Ψ.toCompletelyPositiveMap)) * perf n x) =
      trace (MatrixMap.choi_matrix ((matrixAction Ψ.toCompletelyPositiveMap)) *
        (((R ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) + (1 ⊗ₖ R)) ⊗ₖ Rᵀ)) := by
    rw [choi_reindex]
    change trace ((MatrixMap.choi_matrix ((matrixAction Ψ.toCompletelyPositiveMap))).submatrix
      (Equiv.prodComm (Fin n) (Fin n × Fin n)) (Equiv.prodComm (Fin n) (Fin n × Fin n)) *
      ((((R ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) + (1 ⊗ₖ R)) ⊗ₖ Rᵀ).submatrix
      (Equiv.prodComm (Fin n) (Fin n × Fin n)) (Equiv.prodComm (Fin n) (Fin n × Fin n)))) = _
    rw [Matrix.submatrix_mul_equiv]
    exact Matrix.trace_submatrix
      (MatrixMap.choi_matrix (matrixAction Ψ.toCompletelyPositiveMap) * V)
      (Equiv.prodComm (Fin n) (Fin n × Fin n))
  rw [hr, choi_tensor_pair, Matrix.transpose_transpose, Matrix.add_mul, trace_add,
    trace_right_pair, trace_left_pair]
  change trace (Matrix.vecMulVec (phi n x) (star (phi n x)) * eta n Ψ x) +
    trace (Matrix.vecMulVec (phi n x) (star (phi n x)) * tau n Ψ x) = _
  congr 1 <;> rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec, dotProduct_comm]

/-- Exact entry of the unaveraged source performance operator. -/
private theorem perf_entry (n : ℕ) (x : (Fin n → Fin 2)) (p q : (Fin n × Fin n × Fin n)) :
    perf n x p q = ((n : ℂ)⁻¹)^2 *
      ((if p.2.2 = q.2.2 then
          complexSign ((x p.1).val : ZMod 2) * complexSign ((x p.2.1).val : ZMod 2) *
            complexSign ((x q.1).val : ZMod 2) * complexSign ((x q.2.1).val : ZMod 2) else 0) +
       (if p.2.1 = q.2.1 then
          complexSign ((x p.1).val : ZMod 2) * complexSign ((x p.2.2).val : ZMod 2) *
            complexSign ((x q.1).val : ZMod 2) * complexSign ((x q.2.2).val : ZMod 2) else 0)) := by
  simp only [perf, Matrix.submatrix_apply, Prod.swap, kroneckerMap_apply,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply, rho_entry n]
  split_ifs <;> ring

/-- The fourth moment gives the literal performance operator, including its normalization. -/
private theorem performance_eq_L (n : ℕ) (hn : 2 ≤ n) :
    performance n = (1 / (2 * (n : ℂ)^2)) • (Matrix.of (fun p q => (L n p q : ℂ))) := by
  have hpow : (2 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [performance, avg_univ, smul_smul, mul_comm (2 : ℂ)⁻¹, ← div_eq_mul_inv]
  ext p q
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
    perf_entry n, ← Finset.mul_sum, Finset.sum_add_distrib]
  by_cases hy : p.2.1 = q.2.1 <;> by_cases hz : p.2.2 = q.2.2 <;>
    simp only [hy, hz, if_true, if_false, Finset.sum_const_zero, add_zero, zero_add,
      moment_four]
  all_goals
    simp only [L, hy, hz, if_true, if_false, Complex.ofReal_add, Complex.ofReal_zero]
    field_simp [hpow, hn0]
    <;> ring

/-- The scalar in the source objective is the trace pairing with the averaged operator. -/
private theorem meanFidelity_pair (n : ℕ) (Ψ : QuantumChannel (Fin n) (Fin n × Fin n)) :
    meanFidelity n Ψ = (trace ((inputFirstChoi (matrixAction Ψ.toCompletelyPositiveMap)) * performance n)).re := by
  have hc : ((2 : ℂ)^n)⁻¹ / 2 = ((((2 : ℝ)^n)⁻¹ / 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_pow,
      Complex.ofReal_ofNat]
  rw [performance, avg_univ, smul_smul, mul_comm (2 : ℂ)⁻¹, ← div_eq_mul_inv]
  simp only [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum,
    Matrix.trace_sum, perf_pair, hc, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum, Complex.add_re]
  unfold meanFidelity
  rw [← Finset.sum_div]
  ring



end
end D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound


open scoped BigOperators ComplexConjugate
open Matrix
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction inputFirstChoi)
namespace D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound
noncomputable section

private theorem trace_outer_re {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    (Matrix.trace (Matrix.vecMulVec z (star z))).re = ∑ p, ‖z p‖ ^ 2 := by
  have h := D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth.pure_trace
    (WithLp.toLp 2 z)
  rw [h]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  exact EuclideanSpace.norm_sq_eq (WithLp.toLp 2 z)


private theorem trace_L_outer (n : ℕ) (z : (Fin n × Fin n × Fin n) → ℂ) :
    Matrix.trace ((Matrix.of (fun p q => (L n p q : ℂ))) * Matrix.vecMulVec z (star z)) =
      ∑ p, ∑ q, star (z p) * z q * (L n p q : ℂ) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm,
    Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simp only [Matrix.of_apply, Pi.star_apply]
  ring

private theorem trace_L_gram_bound (n : ℕ) (hn : 2 ≤ n) {κ : Type*} [Fintype κ]
    (z : κ → (Fin n × Fin n × Fin n) → ℂ) :
    (Matrix.trace ((Matrix.of (fun p q => (L n p q : ℂ))) *
      (∑ r, Matrix.vecMulVec (z r) (star (z r))))).re ≤
      ((n : ℝ) + 2) * (Matrix.trace (∑ r, Matrix.vecMulVec (z r) (star (z r)))).re := by
  simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, trace_L_outer,
    trace_outer_re, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  simpa only [Complex.re_sum, Finset.mul_sum] using L_quadratic_bound n hn (z r)

end
end D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound


namespace D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound
open Matrix
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction inputFirstChoi)
open scoped BigOperators
open D5.S3.Quantum.Foundation.FiniteStateChannel
noncomputable section

theorem result : claim := by
  intro n hn _ Ψ
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨z, hz⟩ := choi_gram n Ψ
  have hbound := trace_L_gram_bound n hn z
  rw [← hz, choi_trace] at hbound
  simp only [Complex.natCast_re] at hbound
  have hmean := meanFidelity_pair n Ψ
  rw [performance_eq_L n hn] at hmean
  have hc : (1 / (2 * (n : ℂ)^2)) = ((1 / (2 * (n : ℝ)^2) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_natCast]
  rw [Matrix.mul_smul, Matrix.trace_smul, hc] at hmean
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hmean
  rw [hmean, Matrix.trace_mul_comm]
  calc
    _ ≤ (1 / (2 * (n : ℝ)^2)) * (((n : ℝ) + 2) * n) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (1 : ℝ) / 2 + 1 / (n : ℝ) := by
      field_simp [ne_of_gt hnR]
      <;> ring

end
end D5.S3.Quantum.QuantumChannels.AmiriArrazolaHiddenMatchingCloningBound
