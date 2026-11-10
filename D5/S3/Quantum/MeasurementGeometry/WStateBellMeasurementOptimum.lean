/- GID: D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum
   generality: I
   mirror-B: D5/B/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The W-state Bell-measurement frame and index optimum is exactly sqrt(13)/3. -/
/-
admission_basis: open-problem-resolution (#23251; Proved)
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25122
result proof_shape: bind-only
Direct frozen dependencies (same-delivery helpers inlined):
D5/S3/Quantum/Contextuality/EightVertexQutritBound (compiled constant D5.S3.Quantum.Contextuality.EightVertexQutritBound.Realizes._proof_1):
  sha256:b7d506e17ed248b9523a9db95568405c027b182d594f4180ef5ade440d07b258
D5/S3/Quantum/Contextuality/EightVertexQutritBound.E:
  sha256:60688c9ca1d746ce17e099202d56cbf844a4dadb6d4484cd5daef5e0813fc7d3
D5/S3/Quantum/Contextuality/EightVertexQutritBound.bessel_pair:
  sha256:f07d305bf115e783cc0f62d281f6747d4b7f47a510cf0df48dac9e25a81ed60a
D5/S3/Quantum/Contextuality/EightVertexQutritBound.overlapSq:
  sha256:1520d7149275cee8045e5e2f84c9558526db444662ebad54034c45ff63b496e5
D5/S3/Quantum/Contextuality/EightVertexQutritBound.parseval_three:
  sha256:fa69829d7d83235cd394cd6d66dc2e02e833ce56fb8ac358560f0a1abda336fd
D5/S3/Quantum/FiniteDimensional.QubitMatrix:
  sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30
D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.cauchy_three:
  sha256:c105125352709404742ec643116a0ab267c68d87d18634f5013f425cbb2cd7a4
D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.match_1:
  sha256:e76372c22089380d9c838b17e3bd4a5afcc4cccecafd9a1ab034fe8a313aa852
D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauli1:
  sha256:d7da465fbbea589e6d0262a731cd4238e23bfe7c4ec5e0962a2e35730cad8539
The central Pauli sums and W ket are inlined in tau; pauli1 supplies the Pauli matrices.
The natural-index expression is kept in tau and related to Fin.predAbove by index_correspondence.
The source optimization includes identity indices and repeated index pairs.
Declarations (all proof_shape: bind-only; escape_witness: none):
index_correspondence: consumers=tau_zero_left,tau_nonzero,tau_zero_right
tau: consumers=tau_zero_left,claim,tau_std_13,attainment,upper_bound,pair_upper_bound,squared_optimum,tau_nonzero,tau_identity,ncSquaredSet,tau_unit_bound,tau_std_33,tau_identity_bound,tau_zero_right
lambda: consumers=claim,attainment,upper_bound,pair_upper_bound,squared_optimum,lambda_le_normSq_add,ncSquaredSet,lambda_same,orthogonal_equality
ncSquaredSet: consumers=result,upper_bound,squared_optimum
claim: consumers=result
dot3_cs: consumers=bil_cs,lambda_le_normSq_add,lambda_bdd
lambda_le_normSq_add: consumers=pair_upper_bound,orthogonal_equality
density_formula: consumers=tau_zero_left,tau_nonzero,tau_identity,tau_zero_right
triple: consumers=triple_symm,tau_std_13,quadratic_identity,pair_upper_bound,tau_nonzero,tau_unit_bound,tau_std_33,triple_unit_bound,triple_pair_distinct,triple_pair_sameLeft
tau_nonzero: consumers=tau_std_13,pair_upper_bound,tau_unit_bound,tau_std_33
quadratic_identity: consumers=triple_unit_bound,triple_pair_distinct,triple_pair_sameLeft
singleVec: consumers=tau_zero_left,singleVec_bound,tau_identity_bound,tau_zero_right
identityVec: consumers=tau_identity,tau_identity_bound
tau_identity: consumers=tau_identity_bound
tau_zero_left: consumers=tau_identity_bound
tau_zero_right: consumers=tau_identity_bound
diag3: consumers=bil_symm,bil_cs,bil,bil_col,bil_row,diag_norm,bil_formula
bil: consumers=bil_symm,bil_cs,projection_trace,bil_col,bil_row,bil_total,bil_formula,triple_unit_bound,triple_pair_distinct,triple_pair_sameLeft
frame_unit: consumers=bil_col,bil_row,tau_unit_bound,tau_identity_bound,triple_pair_distinct,triple_pair_sameLeft
frame_parseval: consumers=bil_col,bil_row,frame_z
coord_le: consumers=triple_unit_bound,triple_pair_sameLeft
frame_z: consumers=bil_total,triple_pair_distinct,triple_pair_sameLeft
diag_norm: consumers=bil_cs,bil_col,bil_row
bil_formula: consumers=triple_unit_bound
bil_symm: consumers=bil_row
bil_cs: consumers=triple_unit_bound,triple_pair_distinct
triple_unit_bound: consumers=tau_unit_bound
sum_three: consumers=projection_trace,pair_le_sum,triple_pair_distinct
third_index: consumers=pair_le_sum,triple_pair_distinct
pair_le_sum: consumers=triple_pair_sameLeft
bil_row: consumers=projection_trace,bil_total,triple_pair_sameLeft
bil_col: consumers=projection_trace
bil_total: consumers=projection_trace
projection_trace: consumers=triple_pair_distinct
triple_pair_distinct: consumers=pair_upper_bound
triple_pair_sameLeft: consumers=pair_upper_bound
triple_symm: consumers=pair_upper_bound
lambda_same: consumers=pair_upper_bound
singleVec_bound: consumers=tau_identity_bound
tau_identity_bound: consumers=pair_upper_bound,tau_unit_bound
tau_unit_bound: consumers=pair_upper_bound
frameIndex_injective: consumers=pair_upper_bound
pair_upper_bound: consumers=upper_bound,squared_optimum
upper_bound: consumers=squared_optimum
lambda_bdd: consumers=orthogonal_equality
orthogonal_equality: consumers=attainment
tau_std_33: consumers=attainment
tau_std_13: consumers=attainment
attainment: consumers=squared_optimum
squared_optimum: consumers=result
result: settling result
-/

import D5.S3.Quantum.Contextuality.EightVertexQutritBound
import D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction
import D5.S3.Quantum.FiniteDimensional
import D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight

namespace D5.S3.Quantum.MeasurementGeometry.WStateBellMeasurementOptimum
open scoped ComplexConjugate
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight (pauli1)
set_option maxHeartbeats 1200000

private lemma index_correspondence (μ : Fin 4) :
    (if _h : μ = 0 then (0 : Fin 3) else ⟨μ.val - 1, by omega⟩) =
      (0 : Fin 3).predAbove μ := by
  exact (Fin.predAbove_zero (i := μ)).symm

noncomputable def tau (e f : Fin 3 → EuclideanSpace ℝ (Fin 3)) (μ ν : Fin 4) :
    Fin 3 → ℝ := fun k =>
  let w : ((Fin 2 × Fin 2) × Fin 2) → ℂ := fun i =>
    if i = ((0, 0), 1) ∨ i = ((0, 1), 0) ∨ i = ((1, 0), 0) then
      1 / Complex.sqrt 3 else 0
  (Matrix.trace (Matrix.vecMulVec w (star w) *
      Matrix.kronecker (Matrix.kronecker (if μ = 0 then 1 else
          ∑ k : Fin 3,
            ((e (if h : μ = 0 then 0 else ⟨μ.val - 1, by omega⟩) k : ℝ) : ℂ) •
              pauli1 (Fin.succ k))
        (pauli1 (Fin.succ k))) (if ν = 0 then 1 else
          ∑ k : Fin 3,
            ((f (if h : ν = 0 then 0 else ⟨ν.val - 1, by omega⟩) k : ℝ) : ℂ) •
              pauli1 (Fin.succ k)))).re

noncomputable def lambda (u v : (Fin 3 → ℝ)) : ℝ :=
  sSup {q : ℝ | ∃ n n' : (Fin 3 → ℝ),
    (∑ coord : Fin 3, (n coord)^2) = 1 ∧ (∑ coord : Fin 3, (n' coord)^2) = 1 ∧
    (∑ i : Fin 3, n i * n' i) = 0 ∧
    q = (∑ i : Fin 3, u i * n i) ^ 2 + (∑ i : Fin 3, v i * n' i) ^ 2}

private noncomputable def ncSquaredSet : Set ℝ := {q : ℝ |
  ∃ e f : (Fin 3 → EuclideanSpace ℝ (Fin 3)), Orthonormal ℝ e ∧ Orthonormal ℝ f ∧
    ∃ μ ν μ' ν' : Fin 4,
      q = lambda (tau e f μ ν) (tau e f μ' ν')}

noncomputable def claim : Prop :=
  Real.sqrt (sSup {q : ℝ |
    ∃ e f : Fin 3 → EuclideanSpace ℝ (Fin 3),
      Orthonormal ℝ e ∧ Orthonormal ℝ f ∧
      ∃ μ ν μ' ν' : Fin 4,
        q = lambda (tau e f μ ν) (tau e f μ' ν')}) =
    Real.sqrt 13 / 3

private lemma dot3_cs (a b : Fin 3 → ℝ) :
    (dotProduct a b)^2 ≤ (∑ coord : Fin 3, (a coord)^2) *
      (∑ coord : Fin 3, (b coord)^2) := by
  have h := D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.Pinching.cauchy_three (a 0) (a 1) (a 2) (b 0) (b 1) (b 2)
  simpa [dotProduct, Fin.sum_univ_three, pow_two] using h

private lemma lambda_le_normSq_add (u v : (Fin 3 → ℝ)) : lambda u v ≤ (∑ coord : Fin 3, (u coord)^2) + (∑ coord : Fin 3, (v coord)^2) := by
  let n0 : (Fin 3 → ℝ) := ![1, 0, 0]
  let n1 : (Fin 3 → ℝ) := ![0, 1, 0]
  have hn0 : (∑ coord : Fin 3, (n0 coord)^2) = 1 := by simp [n0, Fin.sum_univ_three]
  have hn1 : (∑ coord : Fin 3, (n1 coord)^2) = 1 := by simp [n1, Fin.sum_univ_three]
  have hno : (∑ i : Fin 3, n0 i * n1 i) = 0 := by simp [n0, n1, Fin.sum_univ_three]
  have hnon : {q : ℝ | ∃ n n' : (Fin 3 → ℝ),
      (∑ coord : Fin 3, (n coord)^2) = 1 ∧ (∑ coord : Fin 3, (n' coord)^2) = 1 ∧
      (∑ i : Fin 3, n i * n' i) = 0 ∧
      q = (∑ i : Fin 3, u i * n i) ^ 2 + (∑ i : Fin 3, v i * n' i) ^ 2}.Nonempty := by
    exact ⟨u 0 ^ 2 + v 1 ^ 2, n0, n1, hn0, hn1, hno, by simp [n0, n1, Fin.sum_univ_three]⟩
  apply csSup_le hnon
  rintro q ⟨n, n', hn, hn', _, rfl⟩
  have hcu := dot3_cs u n
  have hcv := dot3_cs v n'
  rw [hn] at hcu
  rw [hn'] at hcv
  simpa only [dotProduct, mul_one] using add_le_add hcu hcv

private lemma density_formula (i j : ((Fin 2 × Fin 2) × Fin 2)) :
    (Matrix.vecMulVec (fun i : ((Fin 2 × Fin 2) × Fin 2) => if i = ((0, 0), 1) ∨ i = ((0, 1), 0) ∨ i = ((1, 0), 0) then (1 / Complex.sqrt 3 : ℂ) else 0) (star (fun i : ((Fin 2 × Fin 2) × Fin 2) => if i = ((0, 0), 1) ∨ i = ((0, 1), 0) ∨ i = ((1, 0), 0) then (1 / Complex.sqrt 3 : ℂ) else 0))) i j = if
      (i = ((0, 0), 1) ∨ i = ((0, 1), 0) ∨ i = ((1, 0), 0)) ∧
      (j = ((0, 0), 1) ∨ j = ((0, 1), 0) ∨ j = ((1, 0), 0))
    then (1 / 3 : ℂ) else 0 := by
  have hsqrt : Complex.sqrt (3 : ℂ) = (Real.sqrt 3 : ℂ) := by
    have h := Complex.sqrt_of_nonneg (a := (3 : ℂ)) (RCLike.ofReal_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 3))
    simpa using h
  have h3 : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  have h3c : (Real.sqrt 3 : ℂ)^2 = 3 := by exact_mod_cast h3
  have hprod : (1 / Complex.sqrt 3) * star (1 / Complex.sqrt 3) = (1/3:ℂ) := by
    rw [hsqrt]
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, h3, h3c, ← pow_two]
  simp only [Matrix.vecMulVec_apply, Pi.star_apply]
  split_ifs <;> simp_all

private noncomputable def triple (a c : (Fin 3 → ℝ)) : (Fin 3 → ℝ) :=
  ![2 * (a 0 * c 2 + a 2 * c 0) / 3,
    2 * (a 1 * c 2 + a 2 * c 1) / 3,
    (2 * (a 0 * c 0 + a 1 * c 1) - 3 * a 2 * c 2) / 3]

private lemma tau_nonzero (e f : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (μ ν : Fin 4) (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    tau e f μ ν = triple (e (((0 : Fin 3).predAbove μ))) (f (((0 : Fin 3).predAbove ν))) := by
  funext k
  simp only [tau, Matrix.trace, Matrix.diag, Matrix.mul_apply, density_formula,
    index_correspondence]
  fin_cases k <;>
    norm_num [hμ, hν,
      pauli1, qubitX, qubitZ, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.kronecker, Matrix.kroneckerMap, triple] <;> ring

private lemma quadratic_identity (a c : (Fin 3 → ℝ)) (ha : (∑ coord : Fin 3, (a coord)^2) = 1) (hc : (∑ coord : Fin 3, (c coord)^2) = 1) :
    9 * (∑ coord : Fin 3, ((triple a c) coord)^2) =
      (2 * a 0 * c 0 + 2 * a 1 * c 1 - a 2 * c 2)^2 +
      4 * (a 2)^2 + 4 * (c 2)^2 := by
  simp [Fin.sum_univ_three, triple] at ha hc ⊢
  linear_combination 4 * (c 2)^2 * ha + 4 * (a 2)^2 * hc

private noncomputable def singleVec (a : Fin 3 → ℝ) : Fin 3 → ℝ :=
  Matrix.mulVec (Matrix.diagonal ![(2 : ℝ)/3, 2/3, -1/3]) a

private noncomputable def identityVec : (Fin 3 → ℝ) := ![0,0,1/3]

private lemma tau_identity (e f : (Fin 3 → EuclideanSpace ℝ (Fin 3))) : tau e f 0 0 = identityVec := by
  funext k
  simp only [tau, Matrix.trace, Matrix.diag, Matrix.mul_apply, density_formula]
  fin_cases k <;>
    norm_num [
      pauli1, qubitX, qubitZ, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.kronecker, Matrix.kroneckerMap, identityVec]

private lemma tau_zero_left (e f : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (ν : Fin 4) (hν : ν ≠ 0) :
    tau e f 0 ν = singleVec (f (((0 : Fin 3).predAbove ν))) := by
  funext k
  simp only [tau, Matrix.trace, Matrix.diag, Matrix.mul_apply, density_formula,
    index_correspondence]
  fin_cases k <;>
    norm_num [ hν,
      pauli1, qubitX, qubitZ, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.kronecker, Matrix.kroneckerMap, singleVec, Matrix.mulVec_diagonal] <;> ring

private lemma tau_zero_right (e f : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (μ : Fin 4) (hμ : μ ≠ 0) :
    tau e f μ 0 = singleVec (e (((0 : Fin 3).predAbove μ))) := by
  funext k
  simp only [tau, Matrix.trace, Matrix.diag, Matrix.mul_apply, density_formula,
    index_correspondence]
  fin_cases k <;>
    norm_num [ hμ,
      pauli1, qubitX, qubitZ, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.kronecker, Matrix.kroneckerMap, singleVec, Matrix.mulVec_diagonal] <;> ring

private def diag3 (a : Fin 3 → ℝ) : Fin 3 → ℝ :=
  Matrix.mulVec (Matrix.diagonal ![2, 2, -1]) a

private def bil (a c : (Fin 3 → ℝ)) : ℝ := dotProduct a (diag3 c)

private lemma frame_unit (e : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (he : Orthonormal ℝ e) (i : Fin 3) :
    (∑ coord : Fin 3, ((e i) coord)^2) = 1 := by
  have h := congrArg (fun x : ℝ => x^2) (he.1 i)
  simpa [EuclideanSpace.real_norm_sq_eq] using h

private lemma frame_parseval (e : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (he : Orthonormal ℝ e) (x : (Fin 3 → ℝ)) :
    ∑ i, (dotProduct (e i) x)^2 = (∑ coord : Fin 3, (x coord)^2) := by
  have hv : (![e 0, e 1, e 2] : Fin 3 → EuclideanSpace ℝ (Fin 3)) = e := by
    funext i
    fin_cases i <;> rfl
  have ho : Orthonormal ℝ ![e 0, e 1, e 2] := by rwa [hv]
  have h := D5.S3.Quantum.Contextuality.EightVertexQutritBound.parseval_three ho (WithLp.toLp 2 x)
  simpa [D5.S3.Quantum.Contextuality.EightVertexQutritBound.overlapSq,
    EuclideanSpace.inner_toLp_toLp, EuclideanSpace.real_norm_sq_eq,
    PiLp.inner_apply, Real.inner_apply, dotProduct, Fin.sum_univ_three, mul_comm] using h

private lemma coord_le (x : (Fin 3 → ℝ)) (k : Fin 3) : (x k)^2 ≤ (∑ coord : Fin 3, (x coord)^2) := by
  exact Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ k)

private lemma frame_z (e : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (he : Orthonormal ℝ e) :
    ∑ i, (e i 2)^2 = 1 := by
  have h := frame_parseval e he ![0,0,1]
  simpa [dotProduct, Fin.sum_univ_three] using h

private lemma diag_norm (a : (Fin 3 → ℝ)) :
    (∑ coord : Fin 3, ((diag3 a) coord)^2) = 4 * (∑ coord : Fin 3, (a coord)^2) - 3 * (a 2)^2 := by
  simp [diag3, Matrix.mulVec_diagonal, Fin.sum_univ_three]
  ring

private lemma bil_formula (a c : Fin 3 → ℝ) :
    bil a c = 2*a 0*c 0 + 2*a 1*c 1 - a 2*c 2 := by
  simp [bil, dotProduct, diag3, Matrix.mulVec_diagonal, Fin.sum_univ_three]
  ring

private lemma bil_symm (a c : (Fin 3 → ℝ)) : bil a c = bil c a := by
  simp [bil, dotProduct, diag3, Matrix.mulVec_diagonal, Fin.sum_univ_three]
  ring

private lemma bil_cs (a c : (Fin 3 → ℝ)) (ha : (∑ coord : Fin 3, (a coord)^2) = 1) (hc : (∑ coord : Fin 3, (c coord)^2) = 1) :
    (bil a c)^2 ≤ 4 - 3 * (c 2)^2 := by
  have h := dot3_cs a (diag3 c)
  simpa [bil, diag_norm, ha, hc] using h

private lemma triple_unit_bound (a c : (Fin 3 → ℝ)) (ha : (∑ coord : Fin 3, (a coord)^2) = 1) (hc : (∑ coord : Fin 3, (c coord)^2) = 1) :
    (∑ coord : Fin 3, ((triple a c) coord)^2) ≤ 1 := by
  have h := quadratic_identity a c ha hc
  have hb := bil_cs a c ha hc
  have haz := coord_le a 2
  have hcz := coord_le c 2
  rw [bil_formula] at hb
  nlinarith

private lemma sum_three (x : Fin 3 → ℝ) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ r, x r = x i + x j + x k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [Fin.sum_univ_three] <;> ring

private lemma third_index (i j : Fin 3) : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  exact ⟨k, hki.symm, hkj.symm⟩

private lemma pair_le_sum (x : Fin 3 → ℝ) (i j : Fin 3) (hij : i ≠ j) :
    (x i)^2 + (x j)^2 ≤ ∑ r, (x r)^2 := by
  obtain ⟨k, hik, hjk⟩ := third_index i j
  rw [sum_three (fun r => (x r)^2) i j k hij hik hjk]
  nlinarith [sq_nonneg (x k)]

private lemma bil_row (e f : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (i : Fin 3) : ∑ j, (bil (e i) (f j))^2 = 4 - 3 * (e i 2)^2 := by
  simp_rw [bil_symm (e i)]
  simpa [bil, diag_norm, frame_unit e he i] using frame_parseval f hf (diag3 (e i))

private lemma bil_col (e f : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (j : Fin 3) : ∑ i, (bil (e i) (f j))^2 = 4 - 3 * (f j 2)^2 := by
  simpa [bil, diag_norm, frame_unit f hf j] using frame_parseval e he (diag3 (f j))

private lemma bil_total (e f : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f) :
    ∑ i, ∑ j, (bil (e i) (f j))^2 = 9 := by
  simp_rw [bil_row e f he hf]
  norm_num [Finset.sum_sub_distrib, ← Finset.mul_sum, frame_z e he]

private lemma projection_trace (e f : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (i i' j j' k l : Fin 3) (hii : i ≠ i') (hik : i ≠ k) (hi'k : i' ≠ k)
    (hjj : j ≠ j') (hjl : j ≠ l) (hj'l : j' ≠ l) :
    (bil (e i) (f j))^2 + (bil (e i') (f j'))^2 ≤
      1 + 3 * (e k 2)^2 + 3 * (f l 2)^2 + (bil (e k) (f l))^2 := by
  have hr := bil_row e f he hf k
  have hc := bil_col e f he hf l
  have ht := bil_total e f he hf
  rw [sum_three _ j j' l hjj hjl hj'l] at hr
  rw [sum_three _ i i' k hii hik hi'k] at hc ht
  simp_rw [sum_three _ j j' l hjj hjl hj'l] at ht
  nlinarith only [hr, hc, ht, sq_nonneg (bil (e i) (f j')),
    sq_nonneg (bil (e i') (f j))]

private lemma triple_pair_distinct (e f : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (i i' j j' : Fin 3) (hii : i ≠ i') (hjj : j ≠ j') :
    (∑ coord : Fin 3, ((triple (e i) (f j)) coord)^2) + (∑ coord : Fin 3, ((triple (e i') (f j')) coord)^2) ≤ 13/9 := by
  obtain ⟨k, hik, hi'k⟩ := third_index i i'
  obtain ⟨l, hjl, hj'l⟩ := third_index j j'
  have hp := projection_trace e f he hf i i' j j' k l hii hik hi'k hjj hjl hj'l
  have h1 := quadratic_identity (e i) (f j) (frame_unit e he i) (frame_unit f hf j)
  have h2 := quadratic_identity (e i') (f j') (frame_unit e he i') (frame_unit f hf j')
  have hz1 := frame_z e he
  have hz2 := frame_z f hf
  rw [sum_three _ i i' k hii hik hi'k] at hz1
  rw [sum_three _ j j' l hjj hjl hj'l] at hz2
  have hb := bil_cs (e k) (f l) (frame_unit e he k) (frame_unit f hf l)
  simp_rw [← bil_formula] at h1 h2
  nlinarith only [hp, h1, h2, hz1, hz2, hb, sq_nonneg (e k 2), sq_nonneg (f l 2)]

private lemma triple_pair_sameLeft (e f : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (i j j' : Fin 3) (hjj : j ≠ j') :
    (∑ coord : Fin 3, ((triple (e i) (f j)) coord)^2) + (∑ coord : Fin 3, ((triple (e i) (f j')) coord)^2) ≤ 13/9 := by
  have hp := pair_le_sum (fun j => bil (e i) (f j)) j j' hjj
  rw [bil_row e f he hf] at hp
  have hz := pair_le_sum (fun j => f j 2) j j' hjj
  rw [frame_z f hf] at hz
  have h1 := quadratic_identity (e i) (f j) (frame_unit e he i) (frame_unit f hf j)
  have h2 := quadratic_identity (e i) (f j') (frame_unit e he i) (frame_unit f hf j')
  have hez := coord_le (e i) 2
  rw [frame_unit e he i] at hez
  simp_rw [← bil_formula] at h1 h2
  nlinarith only [hp, hz, h1, h2, hez]

private lemma triple_symm (a c : (Fin 3 → ℝ)) : triple a c = triple c a := by
  funext k; fin_cases k <;> simp [triple] <;> ring

private lemma lambda_same (u : (Fin 3 → ℝ)) : lambda u u ≤ (∑ coord : Fin 3, (u coord)^2) := by
  let n0 : (Fin 3 → ℝ) := ![1,0,0]
  let n1 : (Fin 3 → ℝ) := ![0,1,0]
  have hnon : {q : ℝ | ∃ n n' : (Fin 3 → ℝ),
      (∑ coord : Fin 3, (n coord)^2) = 1 ∧ (∑ coord : Fin 3, (n' coord)^2) = 1 ∧
      (∑ i : Fin 3, n i * n' i) = 0 ∧
      q = (∑ i : Fin 3, u i * n i)^2 + (∑ i : Fin 3, u i * n' i)^2}.Nonempty := by
    refine ⟨u 0^2 + u 1^2, n0, n1, ?_, ?_, ?_, ?_⟩ <;>
      simp [n0, n1, Fin.sum_univ_three]
  apply csSup_le hnon
  rintro q ⟨n,n',hn,hn',horth,rfl⟩
  have hnE : ‖(WithLp.toLp 2 n : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    have hnorm : ‖(WithLp.toLp 2 n : EuclideanSpace ℝ (Fin 3))‖^2 = 1 := by
      simpa [EuclideanSpace.real_norm_sq_eq] using hn
    nlinarith [norm_nonneg (WithLp.toLp 2 n : EuclideanSpace ℝ (Fin 3))]
  have hn'E : ‖(WithLp.toLp 2 n' : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    have hnorm : ‖(WithLp.toLp 2 n' : EuclideanSpace ℝ (Fin 3))‖^2 = 1 := by
      simpa [EuclideanSpace.real_norm_sq_eq] using hn'
    nlinarith [norm_nonneg (WithLp.toLp 2 n' : EuclideanSpace ℝ (Fin 3))]
  have hoE : inner ℝ (WithLp.toLp 2 n : EuclideanSpace ℝ (Fin 3)) (WithLp.toLp 2 n') = 0 := by
    simpa [EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm] using horth
  have h := D5.S3.Quantum.Contextuality.EightVertexQutritBound.bessel_pair hnE hn'E hoE (WithLp.toLp 2 u)
  simpa [D5.S3.Quantum.Contextuality.EightVertexQutritBound.overlapSq,
    EuclideanSpace.inner_toLp_toLp, EuclideanSpace.real_norm_sq_eq,
    dotProduct, Real.norm_eq_abs, sq_abs, mul_comm] using h

private lemma singleVec_bound (a : (Fin 3 → ℝ)) (ha : (∑ coord : Fin 3, (a coord)^2) = 1) :
    (∑ coord : Fin 3, ((singleVec a) coord)^2) ≤ 4/9 := by
  simp [singleVec, Matrix.mulVec_diagonal, Fin.sum_univ_three] at ha ⊢
  nlinarith [sq_nonneg (a 2)]

private lemma tau_identity_bound (e f : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (μ ν : Fin 4) (h : μ = 0 ∨ ν = 0) : (∑ coord : Fin 3, ((tau e f μ ν) coord)^2) ≤ 4/9 := by
  by_cases hμ : μ = 0
  · subst μ
    by_cases hν : ν = 0
    · subst ν
      rw [tau_identity]
      norm_num [identityVec, Fin.sum_univ_three]
    · rw [tau_zero_left e f ν hν]
      exact singleVec_bound _ (frame_unit f hf _)
  · have hν : ν = 0 := h.resolve_left hμ
    subst ν
    rw [tau_zero_right e f μ hμ]
    exact singleVec_bound _ (frame_unit e he _)

private lemma tau_unit_bound (e f : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (μ ν : Fin 4) : (∑ coord : Fin 3, ((tau e f μ ν) coord)^2) ≤ 1 := by
  by_cases h : μ = 0 ∨ ν = 0
  · have h1 := tau_identity_bound e f he hf μ ν h
    linarith
  · push Not at h
    rw [tau_nonzero e f μ ν h.1 h.2]
    exact triple_unit_bound _ _ (frame_unit e he _) (frame_unit f hf _)

private lemma frameIndex_injective (μ μ' : Fin 4) (hμ : μ ≠ 0) (hμ' : μ' ≠ 0)
    (h : ((0 : Fin 3).predAbove μ) = ((0 : Fin 3).predAbove μ')) : μ = μ' := by
  have hv := congrArg Fin.succ h
  simpa only [Fin.succ_predAbove_zero hμ, Fin.succ_predAbove_zero hμ'] using hv

private lemma pair_upper_bound (e f : (Fin 3 → EuclideanSpace ℝ (Fin 3))) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (μ ν μ' ν' : Fin 4) :
    lambda (tau e f μ ν) (tau e f μ' ν') ≤ 13/9 := by
  have hl := lambda_le_normSq_add (tau e f μ ν) (tau e f μ' ν')
  by_cases h : μ = 0 ∨ ν = 0
  · have h1 := tau_identity_bound e f he hf μ ν h
    have h2 := tau_unit_bound e f he hf μ' ν'
    linarith
  by_cases h' : μ' = 0 ∨ ν' = 0
  · have h1 := tau_unit_bound e f he hf μ ν
    have h2 := tau_identity_bound e f he hf μ' ν' h'
    linarith
  push Not at h h'
  by_cases hμ : μ = μ'
  · by_cases hν : ν = ν'
    · subst μ'; subst ν'
      exact (lambda_same _).trans ((tau_unit_bound e f he hf μ ν).trans (by norm_num))
    · have hjj : ((0 : Fin 3).predAbove ν) ≠ ((0 : Fin 3).predAbove ν') :=
        fun hx => hν (frameIndex_injective ν ν' h.2 h'.2 hx)
      have hp := triple_pair_sameLeft e f he hf (((0 : Fin 3).predAbove μ)) (((0 : Fin 3).predAbove ν)) (((0 : Fin 3).predAbove ν')) hjj
      rw [tau_nonzero e f μ ν h.1 h.2, tau_nonzero e f μ' ν' h'.1 h'.2, ← hμ] at hl ⊢
      exact hl.trans hp
  · have hii : ((0 : Fin 3).predAbove μ) ≠ ((0 : Fin 3).predAbove μ') :=
      fun hx => hμ (frameIndex_injective μ μ' h.1 h'.1 hx)
    by_cases hν : ν = ν'
    · have hp := triple_pair_sameLeft f e hf he (((0 : Fin 3).predAbove ν)) (((0 : Fin 3).predAbove μ)) (((0 : Fin 3).predAbove μ')) hii
      rw [tau_nonzero e f μ ν h.1 h.2, tau_nonzero e f μ' ν' h'.1 h'.2, ← hν] at hl ⊢
      rw [triple_symm (f (((0 : Fin 3).predAbove ν))) (e (((0 : Fin 3).predAbove μ))),
          triple_symm (f (((0 : Fin 3).predAbove ν))) (e (((0 : Fin 3).predAbove μ')))] at hp
      exact hl.trans hp
    · have hjj : ((0 : Fin 3).predAbove ν) ≠ ((0 : Fin 3).predAbove ν') :=
        fun hx => hν (frameIndex_injective ν ν' h.2 h'.2 hx)
      have hp := triple_pair_distinct e f he hf (((0 : Fin 3).predAbove μ)) (((0 : Fin 3).predAbove μ'))
        (((0 : Fin 3).predAbove ν)) (((0 : Fin 3).predAbove ν')) hii hjj
      rw [tau_nonzero e f μ ν h.1 h.2, tau_nonzero e f μ' ν' h'.1 h'.2] at hl ⊢
      exact hl.trans hp

private lemma upper_bound : (sSup ncSquaredSet) ≤ 13/9 := by
  have hs : Orthonormal ℝ (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) := EuclideanSpace.orthonormal_single
  apply csSup_le
  · exact ⟨lambda (tau (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) 3 3) (tau (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) 1 3),
      (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)), (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)), hs,hs,3,3,1,3,rfl⟩
  · rintro q ⟨e,f,he,hf,μ,ν,μ',ν',rfl⟩
    exact pair_upper_bound e f he hf μ ν μ' ν'

private lemma lambda_bdd (u v : (Fin 3 → ℝ)) :
    BddAbove {q : ℝ | ∃ n n' : (Fin 3 → ℝ),
      (∑ coord : Fin 3, (n coord)^2) = 1 ∧ (∑ coord : Fin 3, (n' coord)^2) = 1 ∧
      (∑ i : Fin 3, n i * n' i) = 0 ∧
      q = (∑ i : Fin 3, u i * n i)^2 + (∑ i : Fin 3, v i * n' i)^2} := by
  refine ⟨(∑ coord : Fin 3, (u coord)^2) + (∑ coord : Fin 3, (v coord)^2), ?_⟩
  rintro q ⟨n,n',hn,hn',_,rfl⟩
  have h1 := dot3_cs u n
  have h2 := dot3_cs v n'
  rw [hn] at h1
  rw [hn'] at h2
  simpa only [dotProduct, mul_one] using add_le_add h1 h2

private lemma orthogonal_equality (u v : (Fin 3 → ℝ)) (r s : ℝ)
    (hr : r ≠ 0) (hs : s ≠ 0) (hrsq : r^2 = (∑ coord : Fin 3, (u coord)^2)) (hssq : s^2 = (∑ coord : Fin 3, (v coord)^2))
    (ho : dotProduct u v = 0) : lambda u v = (∑ coord : Fin 3, (u coord)^2) + (∑ coord : Fin 3, (v coord)^2) := by
  apply le_antisymm (lambda_le_normSq_add u v)
  let n : (Fin 3 → ℝ) := fun k => u k / r
  let n' : (Fin 3 → ℝ) := fun k => v k / s
  have hn : (∑ coord : Fin 3, (n coord)^2) = 1 := by
    dsimp [n]
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    change (∑ coord : Fin 3, (u coord)^2) / r^2 = 1
    rw [← hrsq]
    exact div_self (pow_ne_zero 2 hr)
  have hn' : (∑ coord : Fin 3, (n' coord)^2) = 1 := by
    dsimp [n']
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    change (∑ coord : Fin 3, (v coord)^2) / s^2 = 1
    rw [← hssq]
    exact div_self (pow_ne_zero 2 hs)
  have hno : (∑ k, n k * n' k) = 0 := by
    dsimp [n,n']
    simp_rw [div_mul_div_comm]
    rw [← Finset.sum_div]
    change dotProduct u v / (r*s) = 0
    rw [ho, zero_div]
  have hu : (∑ k, u k * n k) = r := by
    dsimp [n]
    simp_rw [← mul_div_assoc, ← pow_two]
    rw [← Finset.sum_div]
    change (∑ coord : Fin 3, (u coord)^2) / r = r
    rw [← hrsq]
    field_simp
  have hv : (∑ k, v k * n' k) = s := by
    dsimp [n']
    simp_rw [← mul_div_assoc, ← pow_two]
    rw [← Finset.sum_div]
    change (∑ coord : Fin 3, (v coord)^2) / s = s
    rw [← hssq]
    field_simp
  apply le_csSup (lambda_bdd _ _)
  exact ⟨n,n',hn,hn',hno,by rw [hu,hv,hrsq,hssq]⟩

private lemma tau_std_33 : tau (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) 3 3 = fun k : Fin 3 => if k = 2 then -1 else 0 := by
  rw [tau_nonzero _ _ _ _ (by decide) (by decide)]
  funext k
  fin_cases k <;> norm_num [triple, EuclideanSpace.single, Pi.single_apply, Fin.predAbove_zero]

private lemma tau_std_13 : tau (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) 1 3 = fun k : Fin 3 => if k = 0 then (2/3 : ℝ) else 0 := by
  rw [tau_nonzero _ _ _ _ (by decide) (by decide)]
  funext k
  fin_cases k <;> norm_num [triple, EuclideanSpace.single, Pi.single_apply, Fin.predAbove_zero]

private lemma attainment : lambda (tau (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) 3 3)
    (tau (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) 1 3) = 13/9 := by
  rw [tau_std_33, tau_std_13]
  have h := orthogonal_equality
    (fun k : Fin 3 => if k = 2 then -1 else 0)
    (fun k : Fin 3 => if k = 0 then (2/3:ℝ) else 0) 1 (2/3)
    (by norm_num) (by norm_num)
    (by norm_num [Fin.sum_univ_three])
    (by norm_num [Fin.sum_univ_three])
    (by norm_num [dotProduct, Fin.sum_univ_three])
  norm_num [Fin.sum_univ_three] at h
  exact h

private lemma squared_optimum : sSup ncSquaredSet = 13/9 := by
  have hs : Orthonormal ℝ (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) := EuclideanSpace.orthonormal_single
  have hm : (13/9:ℝ) ∈ ncSquaredSet := by
    exact ⟨(fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)), (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)), hs,hs,3,3,1,3,attainment.symm⟩
  have hb : ∀ q ∈ ncSquaredSet, q ≤ (13/9:ℝ) := by
    rintro q ⟨e,f,he,hf,μ,ν,μ',ν',rfl⟩
    exact pair_upper_bound e f he hf μ ν μ' ν'
  exact le_antisymm upper_bound (le_csSup ⟨_,hb⟩ hm)

theorem result : claim := by
  change Real.sqrt (sSup ncSquaredSet) = Real.sqrt 13 / 3
  rw [squared_optimum, Real.sqrt_div] <;> norm_num

end D5.S3.Quantum.MeasurementGeometry.WStateBellMeasurementOptimum
