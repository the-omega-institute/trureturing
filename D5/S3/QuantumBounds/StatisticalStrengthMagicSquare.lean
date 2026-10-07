/- GID: D5/S3/QuantumBounds/StatisticalStrengthMagicSquare
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/StatisticalStrengthMagicSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.result; premises=D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.comparison,D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.magic_valid,D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.magic_block_losing,D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.magic_joint,D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.source_chsh_born,D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.pstar_is_local
   digest: Two-singlet joint measurements exceed twice every CHSH setting strength. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#13919; Proved)
Direct frozen dependencies (declaration statement_id):
  D5/S3/Quantum/FiniteDimensional.qubitX:
    sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
  D5/S3/Quantum/FiniteDimensional.qubitZ:
    sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix:
    sha256:7f853eaeda888a9eccbab5fe25474fc62b519a3229013530986887de25cb28d7
  D5/S3/DivergenceSupport/LogSumInequality.log_sum_inequality:
    sha256:d22ae5efabb89e4a9f1ab5c0a7412668cdbeb6a8793620d128104f71218c1669
  D5/S3/Divergence/ClassicalDPI.klDivergence:
    sha256:5439abc1162340dc8a960e26ac9ec0e06ba733ba3a848aa4ce21aefc7592d01e
  D5/S3/Entropy/Forgetting/CapacityMonotone.pushforward:
    sha256:cad2df6e983d5d173955b5b13a616de5ba6ba0334e17112c93d7f2ed629ffbca
Auxiliary proof_shape: bind-only for every consumed statement below.
  literal_singlets_are_rational: consumer=two_singlets_normalized, born_converted
  two_singlets_normalized: consumer=quantum_total_of_valid
  spectral_projection: consumer=projector_star
  projector_star: consumer=pvm_of_involutions
  projector_orthogonal: consumer=pvm_of_involutions
  projector_total: consumer=pvm_of_involutions
  born_converted: consumer=magic_block_losing
  projector_trace: consumer=pvm_of_involutions
  pvm_of_involutions: consumer=magic_valid
  observable_facts: consumer=magic_valid
  singlet_unitary: consumer=convert_pvm
  convert_pvm: consumer=magic_valid
  magic_valid: consumer=quantum_total, result
  quantum_total_of_valid: consumer=quantum_total
  Classical.parity_obstruction: consumer=Classical.not_all_win
  Classical.row_sum: consumer=Classical.not_all_win
  Classical.col_sum: consumer=Classical.not_all_win
  Classical.not_all_win: consumer=Classical.score_le_eight
  Classical.score_le_eight: consumer=local_block_win_le_eight
  localBehavior_total: consumer=magic_local_lower
  local_expected_payoff: consumer=local_block_win_le_eight
  local_block_win_le_eight: consumer=magic_local_lower
  CoarseGrain.log_sum_data_processing: consumer=CoarseGrain.three_bin_bound
  CoarseGrain.push_absolute_continuity: consumer=CoarseGrain.three_bin_bound
  CoarseGrain.three_bin_bound: consumer=magic_local_lower
  uniform_joint: consumer=outside_push, local_win_push, quantum_push
  outside_push: consumer=quantum_push, magic_local_lower
  local_win_push: consumer=magic_local_lower
  Comparison.log_enclosure: consumer=Comparison.log_nine_eighths_lower, Comparison.positive_log_upper, Comparison.negative_log_upper
  Comparison.log_nine_eighths_lower: consumer=Comparison.magic_lower_above
  Comparison.sqrt_two_bounds: consumer=Comparison.positive_log_upper, Comparison.negative_log_upper, Comparison.twice_chsh_upper, chsh_context_divergence
  Comparison.positive_log_upper: consumer=Comparison.twice_chsh_upper
  Comparison.negative_log_upper: consumer=Comparison.twice_chsh_upper
  Comparison.twice_chsh_upper: consumer=Comparison.comparison
  Comparison.magic_lower_above: consumer=Comparison.comparison
  Comparison.comparison: consumer=result
  pstar_is_local: consumer=chsh_all_setting_strength_upper
  source_chsh_born: consumer=chsh_table
  chsh_table: consumer=chsh_context_divergence
  chsh_context_divergence: consumer=pstar_every_law
  pstar_positive: consumer=pstar_joint_support
  pstar_joint_support: consumer=pstar_every_law
  scale_kl_term: consumer=pstar_every_law
  pstar_every_law: consumer=chsh_all_setting_strength_upper
  chsh_all_setting_strength_upper: consumer=chsh_correlated_upper
  chsh_correlated_upper: consumer=result
  magic_block_losing: consumer=quantum_push
  quantum_total: consumer=quantum_push
  quantum_push: consumer=magic_local_lower
  magic_local_lower: consumer=magic_uniform_lower
  magic_uniform_lower: consumer=result
  magic_joint: consumer=result
Utility: numeric-reduction. The fulfilled logarithmic enclosures feed
comparison; the all-local-theory and all-CHSH-setting-law estimates feed
result. Projector and losing-outcome certificates supply the hypotheses
of those estimates on the literal state; they are not terminal instances.
Registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import D5.S3.DivergenceSupport.LogSumInequality
import D5.S3.Entropy.Forgetting.CapacityMonotone

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
noncomputable section
open Classical
open scoped BigOperators Kronecker ComplexOrder
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Entropy.Forgetting.CapacityMonotone
namespace D5.S3.QuantumBounds.StatisticalStrengthMagicSquare

def uniform (n : ℕ) [NeZero n] : stdSimplex NNReal (Fin n) :=
  ⟨fun _ => (n : NNReal)⁻¹, (by intro i; positivity), (by simp [NeZero.ne n])⟩

def D {α : Type*} [Fintype α] (q p : α → NNReal) : EReal :=
  if ∀ z, p z = 0 → q z = 0 then
    ((∑ z, (q z : ℝ) * Real.log ((q z : ℝ) / (p z : ℝ)) / Real.log 2 : ℝ) : EReal)
  else ⊤

def localBehavior {s o : ℕ} (μ : (stdSimplex NNReal ((Fin s → Fin o) × (Fin s → Fin o)))) : (Fin s → Fin s → Fin o → Fin o → NNReal) := fun x y a b =>
  ∑ t, if t.1 x = a ∧ t.2 y = b then μ t else 0

def productLaw {s : ℕ} (α β : (stdSimplex NNReal (Fin s))) : (stdSimplex NNReal (Fin s × Fin s)) :=
  ⟨fun xy => α xy.1 * β xy.2, (by intro xy; positivity), by
    calc
      (∑ xy : Fin s × Fin s, α.val xy.1 * β.val xy.2) =
          ∑ x, α.val x * ∑ y, β.val y := by
        simp only [Fintype.sum_prod_type, Finset.mul_sum]
      _ = 1 := by rw [β.property.2]; simpa using α.property.2⟩

def uniformLaw (s : ℕ) [NeZero s] : (stdSimplex NNReal (Fin s × Fin s)) := productLaw (uniform s) (uniform s)

def joint {s o : ℕ} (σ : (stdSimplex NNReal (Fin s × Fin s))) (q : (Fin s → Fin s → Fin o → Fin o → NNReal)) :
    ((Fin s × Fin s) × (Fin o × Fin o)) → (NNReal) :=
  fun z => σ z.1 * q z.1.1 z.1.2 z.2.1 z.2.2

def strengthAt {s o : ℕ} (q : (Fin s → Fin s → Fin o → Fin o → NNReal)) (σ : (stdSimplex NNReal (Fin s × Fin s))) : EReal :=
  ⨅ μ : (stdSimplex NNReal ((Fin s → Fin o) × (Fin s → Fin o))), D (joint σ q) (joint σ (localBehavior μ))

def S_uni {s o : ℕ} [NeZero s] (q : (Fin s → Fin s → Fin o → Fin o → NNReal)) : EReal := strengthAt q (uniformLaw s)
def S {s o : ℕ} (q : (Fin s → Fin s → Fin o → Fin o → NNReal)) : EReal :=
  ⨆ α : (stdSimplex NNReal (Fin s)), ⨆ β : (stdSimplex NNReal (Fin s)), strengthAt q (productLaw α β)
def S_cor {s o : ℕ} (q : (Fin s → Fin s → Fin o → Fin o → NNReal)) : EReal := ⨆ σ : (stdSimplex NNReal (Fin s × Fin s)), strengthAt q σ

def singletCoefficient (a b : (Fin 2)) : ℂ :=
  if a = 0 ∧ b = 1 then (Real.sqrt 2 : ℂ)⁻¹
  else if a = 1 ∧ b = 0 then -(Real.sqrt 2 : ℂ)⁻¹ else 0

def twoSinglets : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) → ℂ := fun z =>
  singletCoefficient z.1.1 z.2.1 * singletCoefficient z.1.2 z.2.2

def IsPVM {n : Type*} [Fintype n] [DecidableEq n] (P : Fin 4 → Matrix n n ℂ) : Prop :=
  (∀ a, P a ≠ 0 ∧ star (P a) = P a ∧ P a * P a = P a) ∧
  (∀ a b, a ≠ b → P a * P b = 0) ∧ ∑ a, P a = 1

structure Experiment where
  alice : Fin 4 → Fin 4 → (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
  bob : Fin 4 → Fin 4 → (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)

def Valid (e : Experiment) : Prop := (∀ x, IsPVM (e.alice x)) ∧ ∀ y, IsPVM (e.bob y)
def ProductOperator (P : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) : Prop := ∃ A B : (Matrix (Fin 2) (Fin 2) ℂ), P = A ⊗ₖ B

def JointMeasurement (e : Experiment) : Prop :=
  (∃ x a, ¬ ProductOperator (e.alice x a)) ∨ ∃ y b, ¬ ProductOperator (e.bob y b)

def born (e : Experiment) (x y a b : Fin 4) : ℂ :=
  dotProduct (star twoSinglets) ((e.alice x a ⊗ₖ e.bob y b).mulVec twoSinglets)
def quantum (e : Experiment) : (Fin 4 → Fin 4 → Fin 4 → Fin 4 → NNReal) := fun x y a b =>
  Real.toNNReal (born e x y a b).re

private def square : Fin 3 → Fin 3 → (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := ![
  ![qubitZ ⊗ₖ (1 : (Matrix (Fin 2) (Fin 2) ℂ)), (1 : (Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ qubitZ, qubitZ ⊗ₖ qubitZ],
  ![(1 : (Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ qubitX, qubitX ⊗ₖ (1 : (Matrix (Fin 2) (Fin 2) ℂ)), qubitX ⊗ₖ qubitX],
  ![qubitZ ⊗ₖ qubitX, qubitX ⊗ₖ qubitZ, pauliMatrix .Y ⊗ₖ pauliMatrix .Y]]

private def projector {n : Type*} [Fintype n] [DecidableEq n] (A B : (Matrix n n ℂ)) (a : Fin 4) : (Matrix n n ℂ) :=
  (1 / 4 : ℂ) • ((1 + (if a.val / 2 = 0 then 1 else -1 : ℂ) • A) *
    (1 + (if a.val % 2 = 0 then 1 else -1 : ℂ) • B))

private def aliceObservable (x : Fin 4) (i : (Fin 2)) : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  if hx : x.val < 3 then square ⟨x.val,hx⟩ ⟨i.val,by omega⟩
  else if i = 0 then pauliMatrix .Y ⊗ₖ (1 : (Matrix (Fin 2) (Fin 2) ℂ)) else (1 : (Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ pauliMatrix .Y

private def bobObservable (y : Fin 4) (i : (Fin 2)) : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  if hy : y.val < 3 then square ⟨i.val,by omega⟩ ⟨y.val,hy⟩
  else if i = 0 then pauliMatrix .Y ⊗ₖ (1 : (Matrix (Fin 2) (Fin 2) ℂ)) else (1 : (Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ pauliMatrix .Y

private def convertBob (P : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  (((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)) ⊗ₖ ((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ))) * P.transpose * star (((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)) ⊗ₖ ((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)))

private def magicSquare : Experiment where
  alice := fun x a => projector (aliceObservable x 0) (aliceObservable x 1) a
  bob := fun y b => convertBob (projector (bobObservable y 0) (bobObservable y 1) b)

private def chshWin (x y a b : Fin 2) : Prop :=
  if x = 1 ∧ y = 1 then a ≠ b else a = b

def chshAlice (x a : Fin 2) : (Matrix (Fin 2) (Fin 2) ℂ) :=
  (1/2 : ℂ) • (1 + (if a = 0 then 1 else -1 : ℂ) • (if x = 0 then qubitZ else qubitX))
def chshBob (y b : Fin 2) : (Matrix (Fin 2) (Fin 2) ℂ) :=
  (1/2 : ℂ) • (1 + (if b = 0 then 1 else -1 : ℂ) •
    (-(Real.sqrt 2 : ℂ)⁻¹ • (if y = 0 then qubitZ + qubitX else qubitZ - qubitX)))
def chshBorn (x y a b : Fin 2) : ℂ :=
  dotProduct (star (fun z : Fin 2 × Fin 2 => singletCoefficient z.1 z.2)) ((chshAlice x a ⊗ₖ chshBob y b).mulVec (fun z : Fin 2 × Fin 2 => singletCoefficient z.1 z.2))

def chsh : Fin 2 → Fin 2 → Fin 2 → Fin 2 → NNReal := fun x y a b =>
  Real.toNNReal (chshBorn x y a b).re

private def chshPstar : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → NNReal) := fun x y a b =>
  if chshWin x y a b then 3/8 else 1/8

private def c : ℝ := 2 * (((2 + Real.sqrt 2) / 8) * Real.log ((2 + Real.sqrt 2) / 3) +
  ((2 - Real.sqrt 2) / 8) * Real.log (2 - Real.sqrt 2)) / Real.log 2

def claim : Prop := ∃ e : Experiment, Valid e ∧ JointMeasurement e ∧
  S_uni (quantum e) > 2 * S_cor chsh

private def rationalSinglets : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) → ℂ := fun z =>
  if z.1.1 ≠ z.2.1 ∧ z.1.2 ≠ z.2.2 then
    (if z.1.1 = z.1.2 then 1/2 else -1/2) else 0

private theorem literal_singlets_are_rational : twoSinglets = rationalSinglets := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    norm_num
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  funext ⟨⟨a1,a2⟩,⟨b1,b2⟩⟩
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
    norm_num [twoSinglets, rationalSinglets, singletCoefficient]
  all_goals field_simp [hn]
  all_goals first | linear_combination hs | linear_combination -hs

private theorem two_singlets_normalized : dotProduct (star twoSinglets) twoSinglets = 1 := by
  rw [literal_singlets_are_rational]
  norm_num [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, rationalSinglets, map_ofNat, map_natCast]

private theorem spectral_projection {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hstar : star A = A) (hsq : A*A=1) :
    IsStarProjection ((1/2 : ℂ) • (1+A)) := by
  constructor
  · change ((1/2 : ℂ) • (1+A)) * ((1/2 : ℂ) • (1+A)) = _
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    have hid : (1+A)*(1+A) = (2 : ℂ) • (1+A) := by
      simp only [mul_add, add_mul, one_mul, mul_one, hsq]
      module
    rw [hid, smul_smul]
    norm_num
  · change star ((1/2 : ℂ) • (1+A)) = _
    simp [star_smul, hstar]

private theorem projector_star {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : star A=A ∧ A*A=1) (hB : star B=B ∧ B*B=1)
    (hcomm : Commute A B) (a : Fin 4) :
    IsStarProjection (projector A B a) := by
  have hp (s t : ℂ) (hs : s=1 ∨ s= -1) (ht : t=1 ∨ t= -1) :
      IsStarProjection ((1/4 : ℂ) • ((1+s•A)*(1+t•B))) := by
    have hsa : star (s•A)=s•A := by rcases hs with rfl|rfl <;> simp [hA.1]
    have hsb : star (t•B)=t•B := by rcases ht with rfl|rfl <;> simp [hB.1]
    have hsqA : (s•A)*(s•A)=1 := by
      rcases hs with rfl|rfl <;> simp [hA.2]
    have hsqB : (t•B)*(t•B)=1 := by
      rcases ht with rfl|rfl <;> simp [hB.2]
    have hc : Commute ((1/2 : ℂ) • (1+s•A)) ((1/2 : ℂ) • (1+t•B)) :=
      ((Commute.one_left _).add_left
        ((Commute.one_right _).add_right ((hcomm.smul_left s).smul_right t))).smul_left _ |>.smul_right _
    have h := (spectral_projection (s•A) hsa hsqA).mul
      (spectral_projection (t•B) hsb hsqB) hc
    simpa only [smul_mul_assoc,mul_smul_comm,smul_smul,
      show (1/2 : ℂ)*(1/2)=1/4 by norm_num] using h
  unfold projector
  apply hp <;> split_ifs <;> simp

private theorem projector_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A*A=1) (hB : B*B=1)
    (hcomm : Commute A B) (a b : Fin 4) (hab : a ≠ b) :
    projector A B a * projector A B b = 0 := by
  have hc (s t : ℂ) : Commute (1+s•B) (1+t•A) :=
    (Commute.one_left _).add_left
      ((Commute.one_right _).add_right ((hcomm.symm.smul_left s).smul_right t))
  unfold projector
  rw [smul_mul_assoc,mul_smul_comm,smul_smul]
  have hrearrange (s t u v : ℂ) :
      ((1+s•A)*(1+t•B))*((1+u•A)*(1+v•B)) =
        ((1+s•A)*(1+u•A))*((1+t•B)*(1+v•B)) := by
    rw [mul_assoc, ← mul_assoc (1+t•B), (hc t u).eq, mul_assoc (1+u•A),
      ← mul_assoc]
  rw [hrearrange]
  have hzeroA : (1+A)*(1-A)=0 ∧ (1-A)*(1+A)=0 := by
    constructor <;> noncomm_ring [hA]
  have hzeroB : (1+B)*(1-B)=0 ∧ (1-B)*(1+B)=0 := by
    constructor <;> noncomm_ring [hB]
  fin_cases a <;> fin_cases b <;> try contradiction
  all_goals norm_num [← sub_eq_add_neg,hzeroA.1,hzeroA.2,hzeroB.1,hzeroB.2]

private theorem projector_total {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) : ∑ a, projector A B a = 1 := by
  norm_num [projector,Fin.sum_univ_succ]
  simp only [mul_add,add_mul,one_mul,mul_one,neg_mul,mul_neg]
  module

private theorem born_converted
    (A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    dotProduct (star twoSinglets) ((A ⊗ₖ convertBob B).mulVec twoSinglets) =
      (1/4 : ℂ) * Matrix.trace (A*B) := by
  rw [literal_singlets_are_rational]
  norm_num [rationalSinglets,dotProduct,Matrix.mulVec,convertBob,ModularGroup.S,Matrix.map_apply,Int.castRingHom,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.kronecker_apply,
    Matrix.trace,Matrix.diag,Fintype.sum_prod_type,Fin.sum_univ_two,map_ofNat,map_natCast]
  ring

private theorem projector_trace {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : Matrix.trace A=0) (hB : Matrix.trace B=0)
    (hAB : Matrix.trace (A*B)=0) (a : Fin 4) :
    Matrix.trace (projector A B a) = (Fintype.card n : ℂ)/4 := by
  unfold projector
  simp only [Matrix.trace_smul, mul_add, add_mul, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, Matrix.trace_add, hA, hB, hAB,
    Matrix.trace_smul, smul_zero, add_zero, Matrix.trace_one]
  simp [smul_eq_mul]
  ring

private theorem pvm_of_involutions {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (A B : Matrix n n ℂ)
    (hA : star A=A ∧ A*A=1) (hB : star B=B ∧ B*B=1)
    (hcomm : Commute A B) (htrA : Matrix.trace A=0)
    (htrB : Matrix.trace B=0) (htrAB : Matrix.trace (A*B)=0) :
    IsPVM (projector A B) := by
  refine ⟨fun a => ⟨?_, (projector_star A B hA hB hcomm a).isSelfAdjoint.star_eq,
    (projector_star A B hA hB hcomm a).isIdempotentElem.eq⟩,
    projector_orthogonal A B hA.2 hB.2 hcomm, projector_total A B⟩
  intro hz
  have h := projector_trace A B htrA htrB htrAB a
  rw [hz,Matrix.trace_zero] at h
  have hc : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (div_ne_zero hc (by norm_num)) h.symm

private theorem observable_facts (obs : Fin 4 → Fin 2 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hobs : obs=aliceObservable ∨ obs=bobObservable) (x : Fin 4) :
    (star (obs x 0)=obs x 0 ∧ (obs x 0)*(obs x 0)=1) ∧
    (star (obs x 1)=obs x 1 ∧ (obs x 1)*(obs x 1)=1) ∧
    Commute (obs x 0) (obs x 1) ∧ Matrix.trace (obs x 0)=0 ∧
    Matrix.trace (obs x 1)=0 ∧ Matrix.trace ((obs x 0)*(obs x 1))=0 := by
  rcases hobs with rfl | rfl
  all_goals fin_cases x <;> repeat' apply And.intro
  all_goals first | apply Matrix.ext; intro ⟨i,j⟩ ⟨k,l⟩
                  | skip
  all_goals first
    | fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
    | skip
  all_goals norm_num only [aliceObservable, bobObservable, ↓reduceDIte, ↓reduceIte]
  all_goals dsimp only [square, pauliMatrix, qubitX, qubitZ, Matrix.of_apply]
  all_goals norm_num only [
    Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.kronecker_apply,
    Matrix.trace,Matrix.diag,Fintype.sum_prod_type,Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.one_apply, Matrix.star_eq_conjTranspose, Commute, SemiconjBy,
    Matrix.smul_apply, smul_eq_mul, Prod.mk.injEq, and_true, true_and,
    Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
    Complex.I_re, Complex.I_im, star_zero, star_one, star_neg,
    Complex.star_def, Complex.conj_I, Complex.I_mul_I,
    zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero,
    neg_mul, mul_neg, neg_neg]

private theorem singlet_unitary :
    star (((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)) ⊗ₖ ((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ))) * (((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)) ⊗ₖ ((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ))) = 1 ∧
    (((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)) ⊗ₖ ((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ))) * star (((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)) ⊗ₖ ((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ))) = 1 := by
  constructor <;> ext ⟨i,j⟩ ⟨k,l⟩
  all_goals fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [ModularGroup.S,Matrix.map_apply,Int.castRingHom,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.kronecker_apply,Fintype.sum_prod_type,Fin.sum_univ_two]

private theorem convert_pvm (P : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hP : IsPVM P) : IsPVM (fun a => convertBob (P a)) := by
  have hmult (A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      convertBob A * convertBob B = convertBob (B*A) := by
    simp only [convertBob,Matrix.transpose_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (star _) _ _,singlet_unitary.1,one_mul]
  have hstar (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      star (convertBob A) = convertBob (star A) := by
    simp only [convertBob,star_mul,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,Matrix.conjTranspose_conjTranspose,mul_assoc]
  refine ⟨fun a => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro hz
    change convertBob (P a)=0 at hz
    have hrecover := congrArg (fun M => (star (((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)) ⊗ₖ ((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ))))*M*(((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)) ⊗ₖ ((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)))) hz
    simp only [convertBob,mul_assoc] at hrecover
    rw [← mul_assoc (star _) _ _,singlet_unitary.1,one_mul] at hrecover
    simp only [mul_one,mul_zero,zero_mul] at hrecover
    exact (hP.1 a).1 (by simpa using congrArg Matrix.transpose hrecover)
  · rw [hstar,(hP.1 a).2.1]
  · rw [hmult,(hP.1 a).2.2]
  · intro a b hab
    rw [hmult,hP.2.1 b a (Ne.symm hab)]
    simp [convertBob]
  · simp only [convertBob,← Finset.mul_sum,← Finset.sum_mul,← Matrix.transpose_sum,
      hP.2.2,Matrix.transpose_one,mul_one,singlet_unitary.2]

private theorem magic_valid : Valid magicSquare := by
  constructor
  · intro x
    rcases observable_facts aliceObservable (Or.inl rfl) x with ⟨hA,hB,hcomm,htrA,htrB,htrAB⟩
    exact pvm_of_involutions _ _ hA hB hcomm htrA htrB htrAB
  · intro y
    rcases observable_facts bobObservable (Or.inr rfl) y with ⟨hA,hB,hcomm,htrA,htrB,htrAB⟩
    exact convert_pvm _ (pvm_of_involutions _ _ hA hB hcomm htrA htrB htrAB)

private theorem quantum_total_of_valid (e : Experiment) (he : Valid e) (x y : Fin 4) :
    ∑ a, ∑ b, (quantum e x y a b : ℝ) = 1 := by
  have hpos (a b : Fin 4) : 0 ≤ (born e x y a b).re := by
    have hstar : star (e.alice x a ⊗ₖ e.bob y b) = e.alice x a ⊗ₖ e.bob y b := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
      change star (e.alice x a) ⊗ₖ star (e.bob y b) = _
      rw [((he.1 x).1 a).2.1, ((he.2 y).1 b).2.1]
    have hsq : (e.alice x a ⊗ₖ e.bob y b)*(e.alice x a ⊗ₖ e.bob y b) =
        e.alice x a ⊗ₖ e.bob y b := by
      rw [← Matrix.mul_kronecker_mul,(he.1 x).1 a |>.2.2,(he.2 y).1 b |>.2.2]
    have hp := Matrix.posSemidef_conjTranspose_mul_self (e.alice x a ⊗ₖ e.bob y b)
    rw [← Matrix.star_eq_conjTranspose,hstar,hsq] at hp
    exact (RCLike.nonneg_iff.mp (hp.dotProduct_mulVec_nonneg twoSinglets)).1
  have hsum : ∑ a, ∑ b, (e.alice x a ⊗ₖ e.bob y b) = 1 := by
    calc
      _ = (∑ a, e.alice x a) ⊗ₖ (∑ b, e.bob y b) := by
        ext i j
        simp only [Matrix.sum_apply,Matrix.kroneckerMap_apply,Finset.sum_mul,Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = 1 := by rw [(he.1 x).2.2,(he.2 y).2.2,Matrix.one_kronecker_one]
  have hborn : ∑ a, ∑ b, born e x y a b = 1 := by
    simp only [born,← dotProduct_sum,← Matrix.sum_mulVec]
    rw [hsum,Matrix.one_mulVec,two_singlets_normalized]
  simp only [quantum,Real.coe_toNNReal _ (hpos _ _)]
  simpa only [Complex.re_sum,Complex.one_re] using congrArg Complex.re hborn

namespace Classical

private def first (a : Fin 4) : ZMod 2 := ((a.val / 2 : ℕ) : ZMod 2)

private def second (a : Fin 4) : ZMod 2 := ((a.val % 2 : ℕ) : ZMod 2)

private def rowOut (a : Fin 4) : Fin 3 → ZMod 2 := ![first a, second a, first a + second a]
private def parity (y : Fin 3) : ZMod 2 := if y = 2 then 1 else 0

private def colOut (y : Fin 3) (b : Fin 4) : Fin 3 → ZMod 2 :=
  ![first b, second b, first b + second b + parity y]

@[reducible]
private def wins (x y : Fin 3) (a b : Fin 4) : Prop := rowOut a y = colOut y b x

private theorem parity_obstruction {m n : ℕ} (A B : Fin m → Fin n → ZMod 2)
    (hA : ∑ i, ∑ j, A i j = 0) (hB : ∑ j, ∑ i, B i j = 1) :
    ¬ ∀ i j, A i j = B i j := by
  intro h
  have ht : (0 : ZMod 2) = 1 := calc
    0 = ∑ i, ∑ j, A i j := hA.symm
    _ = ∑ i, ∑ j, B i j := by simp_rw [h]
    _ = ∑ j, ∑ i, B i j := Finset.sum_comm
    _ = 1 := hB
  exact zero_ne_one ht

private theorem row_sum (a : Fin 4) : ∑ y, rowOut a y = 0 := by
  fin_cases a <;> norm_num [rowOut, first, second, Fin.sum_univ_succ] <;> decide

private theorem col_sum (y : Fin 3) (b : Fin 4) : ∑ x, colOut y b x = parity y := by
  fin_cases y <;> fin_cases b <;> norm_num [colOut, first, second, parity, Fin.sum_univ_succ] <;> decide

private theorem not_all_win (A B : Fin 3 → Fin 4) : ¬ ∀ x y, wins x y (A x) (B y) := by
  apply parity_obstruction (fun x y => rowOut (A x) y) (fun x y => colOut y (B y) x)
  · simp_rw [row_sum]
    simp
  · simp_rw [col_sum]
    norm_num [parity, Fin.sum_univ_succ]

private def score (A B : Fin 3 → Fin 4) : ℕ :=
  ∑ x, ∑ y, if wins x y (A x) (B y) then 1 else 0

private theorem score_le_eight (A B : Fin 3 → Fin 4) : score A B ≤ 8 := by
  have h := not_all_win A B
  push Not at h
  obtain ⟨x,y,hxy⟩ := h
  have hrow (i : Fin 3) : (∑ j, if wins i j (A i) (B j) then 1 else 0) ≤
      if i = x then 2 else 3 := by
    by_cases hi : i = x
    · subst i
      have hpoint (j : Fin 3) : (if wins x j (A x) (B j) then 1 else 0 : ℕ) ≤
          if j = y then 0 else 1 := by
        by_cases hj : j = y
        · subst j; simp [hxy]
        · simp [hj]; split_ifs <;> omega
      calc
        _ ≤ ∑ j, if j = y then 0 else 1 := Finset.sum_le_sum (fun j _ => hpoint j)
        _ = 2 := by fin_cases y <;> norm_num [Fin.sum_univ_succ] <;> decide
        _ = if x = x then 2 else 3 := by simp
    · simp only [hi, ↓reduceIte]
      calc
        _ ≤ ∑ _ : Fin 3, 1 := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
        _ = 3 := by norm_num
  calc
    score A B ≤ ∑ i, if i = x then 2 else 3 := Finset.sum_le_sum (fun i _ => hrow i)
    _ = 8 := by fin_cases x <;> norm_num [Fin.sum_univ_succ] <;> decide

end Classical

private theorem localBehavior_total {s o : ℕ} (μ : (stdSimplex NNReal ((Fin s → Fin o) × (Fin s → Fin o)))) (x y : Fin s) :
    ∑ a, ∑ b, localBehavior μ x y a b = 1 := by
  unfold localBehavior
  calc
    (∑ a, ∑ b, ∑ t : ((Fin s → Fin o) × (Fin s → Fin o)), if t.1 x = a ∧ t.2 y = b then μ t else 0) =
        ∑ a, ∑ t : ((Fin s → Fin o) × (Fin s → Fin o)), ∑ b, if t.1 x = a ∧ t.2 y = b then μ t else 0 := by
      apply Finset.sum_congr rfl; intro a _; exact Finset.sum_comm
    _ = ∑ t : ((Fin s → Fin o) × (Fin s → Fin o)), ∑ a, ∑ b, if t.1 x = a ∧ t.2 y = b then μ t else 0 := Finset.sum_comm
    _ = 1 := by simpa [ite_and] using μ.property.2

private theorem local_expected_payoff {s o : ℕ} (μ : (stdSimplex NNReal ((Fin s → Fin o) × (Fin s → Fin o)))) (x y : Fin s)
    (g : Fin o → Fin o → ℝ) :
    ∑ a, ∑ b, (localBehavior μ x y a b : ℝ) * g a b =
      ∑ t : ((Fin s → Fin o) × (Fin s → Fin o)), (μ t : ℝ) * g (t.1 x) (t.2 y) := by
  have hcoe (P : Prop) [Decidable P] (v : NNReal) :
      ((if P then v else 0 : NNReal) : ℝ) = if P then (v : ℝ) else 0 := by
    split_ifs <;> rfl
  simp only [localBehavior, NNReal.coe_sum, hcoe, Finset.sum_mul]
  calc
    (∑ a, ∑ b, ∑ t : ((Fin s → Fin o) × (Fin s → Fin o)),
        (if t.1 x = a ∧ t.2 y = b then (μ t : ℝ) else 0) * g a b) =
        ∑ a, ∑ t : ((Fin s → Fin o) × (Fin s → Fin o)), ∑ b,
        (if t.1 x = a ∧ t.2 y = b then (μ t : ℝ) else 0) * g a b := by
      apply Finset.sum_congr rfl; intro a _; exact Finset.sum_comm
    _ = ∑ t : ((Fin s → Fin o) × (Fin s → Fin o)), ∑ a, ∑ b,
        (if t.1 x = a ∧ t.2 y = b then (μ t : ℝ) else 0) * g a b := Finset.sum_comm
    _ = _ := by simp [ite_and, ite_mul]

private def blockWin (μ : (stdSimplex NNReal ((Fin 4 → Fin 4) × (Fin 4 → Fin 4)))) : ℝ :=
  ∑ x : Fin 3, ∑ y : Fin 3, ∑ a, ∑ b,
    (localBehavior μ (Fin.castSucc x) (Fin.castSucc y) a b : ℝ) *
      if D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.Classical.wins x y a b then 1 else 0

private theorem local_block_win_le_eight (μ : (stdSimplex NNReal ((Fin 4 → Fin 4) × (Fin 4 → Fin 4)))) : blockWin μ ≤ 8 := by
  have hweight : ∑ t, (μ t : ℝ) = 1 := by exact_mod_cast μ.property.2
  unfold blockWin
  simp_rw [local_expected_payoff]
  calc
    (∑ x : Fin 3, ∑ y : Fin 3, ∑ t : ((Fin 4 → Fin 4) × (Fin 4 → Fin 4)),
      (μ t : ℝ) * if D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.Classical.wins x y (t.1 (Fin.castSucc x)) (t.2 (Fin.castSucc y)) then 1 else 0) =
        ∑ x : Fin 3, ∑ t : ((Fin 4 → Fin 4) × (Fin 4 → Fin 4)), ∑ y : Fin 3,
      (μ t : ℝ) * if D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.Classical.wins x y (t.1 (Fin.castSucc x)) (t.2 (Fin.castSucc y)) then 1 else 0 := by
      apply Finset.sum_congr rfl; intro x _; exact Finset.sum_comm
    _ = ∑ t : ((Fin 4 → Fin 4) × (Fin 4 → Fin 4)), ∑ x : Fin 3, ∑ y : Fin 3,
      (μ t : ℝ) * if D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.Classical.wins x y (t.1 (Fin.castSucc x)) (t.2 (Fin.castSucc y)) then 1 else 0 := Finset.sum_comm
    _ = ∑ t : ((Fin 4 → Fin 4) × (Fin 4 → Fin 4)), (μ t : ℝ) *
        (D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.Classical.score (t.1 ∘ Fin.castSucc) (t.2 ∘ Fin.castSucc) : ℝ) := by
      apply Finset.sum_congr rfl; intro t _
      simp only [D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.Classical.score, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        Function.comp_apply, Finset.mul_sum]
    _ ≤ ∑ t : ((Fin 4 → Fin 4) × (Fin 4 → Fin 4)), (μ t : ℝ) * 8 := by
      apply Finset.sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
      exact_mod_cast D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.Classical.score_le_eight (t.1 ∘ Fin.castSucc) (t.2 ∘ Fin.castSucc)
    _ = 8 := by rw [← Finset.sum_mul, hweight]; norm_num

namespace CoarseGrain
open D5.S3.DivergenceSupport.LogSumInequality

private theorem log_sum_data_processing {α β : Type*} [Fintype α] [Fintype β]
    (q p : α → ℝ) (f : α → β) (hq : ∀ z, 0 ≤ q z) (hp : ∀ z, 0 ≤ p z)
    (hac : ∀ z, p z = 0 → q z = 0) : klDivergence (pushforward f q) (pushforward f p) ≤ klDivergence q p := by
  classical
  have hfiber (y : β) := log_sum_inequality
    (fun z => if f z = y then q z else 0)
    (fun z => if f z = y then p z else 0)
    (fun z => by split_ifs; exact hq z; exact le_refl 0)
    (fun z => by split_ifs; exact hp z; exact le_refl 0)
    (fun z hz => by split_ifs at hz ⊢ with h <;> simp_all [hac z])
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hfiber y)
  change klDivergence (pushforward f q) (pushforward f p) ≤ _ at hsum
  calc
    _ ≤ ∑ y : β, ∑ z, (if f z = y then q z else 0) *
        Real.log ((if f z = y then q z else 0) / (if f z = y then p z else 0)) := hsum
    _ = ∑ z, ∑ y : β, if f z = y then q z * Real.log (q z / p z) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : f z = y <;> simp [h]
    _ = klDivergence q p := by simp [klDivergence]

private theorem push_absolute_continuity {α β : Type*} [Fintype α]
    (q p : α → ℝ) (f : α → β) (hp : ∀ z, 0 ≤ p z)
    (hac : ∀ z, p z = 0 → q z = 0) (y : β) (hy : pushforward f p y = 0) :
    pushforward f q y = 0 := by
  classical
  unfold pushforward at *
  apply Finset.sum_eq_zero
  intro z hz
  by_cases h : f z = y
  · have hnonneg (w : α) (_ : w ∈ Finset.univ) : 0 ≤ (if f w = y then p w else 0) := by
      split_ifs; exact hp w; exact le_refl 0
    have heq := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hy z hz
    simp only [h, ↓reduceIte] at heq ⊢
    exact hac z heq
  · simp [h]

private theorem three_bin_bound {α : Type*} [Fintype α]
    (q p : α → ℝ) (f : α → Fin 3)
    (hq : ∀ z, 0 ≤ q z) (hp : ∀ z, 0 ≤ p z)
    (hac : ∀ z, p z = 0 → q z = 0)
    (hQ : pushforward f q = ![7/16,9/16,0])
    (hP0 : pushforward f p 0 = 7/16) (hP1 : pushforward f p 1 ≤ 1/2) :
    (9/16)*Real.log (9/8)/Real.log 2 ≤ klDivergence q p / Real.log 2 := by
  have hQ1 : pushforward f q 1 = 9/16 := by rw [hQ]; rfl
  have hP1nn : 0 ≤ pushforward f p 1 := Finset.sum_nonneg (fun z _ => by split_ifs; exact hp z; exact le_refl 0)
  have hP1ne : pushforward f p 1 ≠ 0 := by
    intro hz
    have hzero := push_absolute_continuity q p f hp hac 1 hz
    rw [hQ1] at hzero
    norm_num at hzero
  have hP1pos : 0 < pushforward f p 1 := lt_of_le_of_ne hP1nn (Ne.symm hP1ne)
  have hratio : (9/8 : ℝ) ≤ (9/16)/pushforward f p 1 := by
    apply (le_div_iff₀ hP1pos).2
    linarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ)<9/8) hratio
  have hdpi := log_sum_data_processing q p f hq hp hac
  have hsimp : klDivergence (pushforward f q) (pushforward f p) = (9/16)*Real.log ((9/16)/pushforward f p 1) := by
    simp [klDivergence, Fin.sum_univ_succ, hQ, hP0]
  rw [hsimp] at hdpi
  apply (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1:ℝ)<2))).2
  linarith

end CoarseGrain

private def coarse (z : ((Fin 4 × Fin 4) × (Fin 4 × Fin 4))) : Fin 3 :=
  if hx : z.1.1.val < 3 then
    if hy : z.1.2.val < 3 then
      if D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.Classical.wins ⟨z.1.1.val,hx⟩ ⟨z.1.2.val,hy⟩ z.2.1 z.2.2 then 1 else 2
    else 0
  else 0

private theorem uniform_joint (q : (Fin 4 → Fin 4 → Fin 4 → Fin 4 → NNReal)) (x y a b : Fin 4) :
    (joint (uniformLaw 4) q ((x,y),(a,b)) : ℝ) = (1/16) * (q x y a b : ℝ) := by
  change (((4 : NNReal)⁻¹ * (4 : NNReal)⁻¹ * q x y a b : NNReal) : ℝ) = _
  norm_num

private theorem outside_push (q : (Fin 4 → Fin 4 → Fin 4 → Fin 4 → NNReal))
    (htotal : ∀ x y, ∑ a, ∑ b, (q x y a b : ℝ) = 1) :
    pushforward coarse (fun z => (joint (uniformLaw 4) q z : ℝ)) 0 = 7/16 := by
  have hinner (x y : Fin 4) :
      (∑ a, ∑ b, if coarse ((x,y),(a,b)) = 0 then
        (joint (uniformLaw 4) q ((x,y),(a,b)) : ℝ) else 0) =
      if x.val = 3 ∨ y.val = 3 then 1/16 else 0 := by
    fin_cases x <;> fin_cases y <;>
      simp [coarse, uniform_joint, ← Finset.mul_sum, htotal,
        apply_ite (fun i : Fin 3 => i = 0)]
  simp only [pushforward, Fintype.sum_prod_type]
  simp_rw [hinner]
  norm_num [Fin.sum_univ_succ]

private theorem local_win_push (μ : (stdSimplex NNReal ((Fin 4 → Fin 4) × (Fin 4 → Fin 4)))) :
    pushforward coarse (fun z => (joint (uniformLaw 4) (localBehavior μ) z : ℝ)) 1 =
      (1/16) * blockWin μ := by
  have hinner (x y : Fin 4) :
      (∑ a, ∑ b, if coarse ((x,y),(a,b)) = 1 then
        (joint (uniformLaw 4) (localBehavior μ) ((x,y),(a,b)) : ℝ) else 0) =
      if hx : x.val < 3 then if hy : y.val < 3 then
        (1/16) * (∑ a, ∑ b, (localBehavior μ x y a b : ℝ) *
          if D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.Classical.wins ⟨x.val,hx⟩ ⟨y.val,hy⟩ a b then 1 else 0)
      else 0 else 0 := by
    by_cases hx : x.val < 3 <;> by_cases hy : y.val < 3
    · simp only [hx,hy,↓reduceDIte]
      simp only [coarse, hx, hy, ↓reduceDIte, uniform_joint, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> norm_num [Fin.ext_iff] at *
    all_goals simp [coarse,hx,hy]
  simp only [pushforward, Fintype.sum_prod_type]
  simp_rw [hinner]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, show ¬ (3:ℕ) < 3 by omega, ↓reduceDIte,
    Finset.sum_const_zero, add_zero]
  unfold blockWin
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, x.isLt, ↓reduceDIte, Fin.val_last,
    show ¬ (3:ℕ) < 3 by omega, add_zero]
  simp only [show ∀ y : Fin 3, y.val < 3 from Fin.isLt, ↓reduceDIte]
  simp only [Finset.mul_sum, Fin.castSucc]

namespace Comparison

private theorem log_enclosure {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, x ^ (2*i+1)/(2*i+1)) ≤
      Real.log ((1+x)/(1-x)) ∧
    Real.log ((1+x)/(1-x)) ≤
      2 * ((∑ i ∈ Finset.range n, x ^ (2*i+1)/(2*i+1)) + x^(2*n+1)/(1-x^2)) := by
  constructor
  · linarith [Real.sum_range_le_log_div hx0 hx1 n]
  · linarith [Real.log_div_le_sum_range_add hx0 hx1 n]

private theorem log_nine_eighths_lower : (1177/10000 : ℝ) ≤ Real.log (9/8) := by
  have h := (log_enclosure (x := 1/17) (by norm_num) (by norm_num) 2).1
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

-- Certified rational endpoints around sqrt 2; the loose margins suffice for the comparison.
private theorem sqrt_two_bounds : (14142/10000 : ℝ) ≤ Real.sqrt 2 ∧
    Real.sqrt 2 ≤ 14143/10000 := by
  constructor
  · apply (Real.le_sqrt (by norm_num) (by norm_num)).2
    norm_num
  · apply (Real.sqrt_le_iff).2
    norm_num

private theorem positive_log_upper : Real.log ((2+Real.sqrt 2)/3) ≤ (1294/10000 : ℝ) := by
  have hx : (2+Real.sqrt 2)/3 ≤ (34143/30000 : ℝ) := by linarith [sqrt_two_bounds.2]
  have hmono := Real.log_le_log (by positivity : (0 : ℝ) < (2+Real.sqrt 2)/3) hx
  have hb := (log_enclosure (x := (4143/64143 : ℝ)) (by norm_num) (by norm_num) 4).2
  norm_num [Finset.sum_range_succ] at hb
  have hrat : Real.log (34143/30000 : ℝ) ≤ 1294/10000 := by linarith
  exact hmono.trans hrat

private theorem negative_log_upper : Real.log (2-Real.sqrt 2) ≤ (-5347/10000 : ℝ) := by
  have hpos : 0 < 2-Real.sqrt 2 := by linarith [sqrt_two_bounds.2]
  have hx : 2-Real.sqrt 2 ≤ (2929/5000 : ℝ) := by linarith [sqrt_two_bounds.1]
  have hmono := Real.log_le_log hpos hx
  have hb := (log_enclosure (x := (2071/7929 : ℝ)) (by norm_num) (by norm_num) 5).1
  norm_num [Finset.sum_range_succ] at hb
  have heq : Real.log (5000/2929 : ℝ) = - Real.log (2929/5000 : ℝ) := by
    rw [show (5000/2929 : ℝ) = (2929/5000)⁻¹ by norm_num, Real.log_inv]
  rw [heq] at hb
  have hrat : Real.log (2929/5000 : ℝ) ≤ -5347/10000 := by linarith
  exact hmono.trans hrat

private theorem twice_chsh_upper : 2 * c < (93/1000 : ℝ) := by
  have hs := sqrt_two_bounds
  have hl2 : (693/1000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hp : 0 ≤ (2+Real.sqrt 2)/8 := by positivity
  have hn : 0 ≤ (2-Real.sqrt 2)/8 := by linarith
  have hup := mul_le_mul_of_nonneg_left positive_log_upper hp
  have hdown := mul_le_mul_of_nonneg_left negative_log_upper hn
  unfold c
  rw [← mul_div_assoc, div_lt_iff₀ (by linarith : 0 < Real.log 2)]
  nlinarith

private theorem magic_lower_above : (95/1000 : ℝ) < (9/16)*Real.log (9/8)/Real.log 2 := by
  have hlo := log_nine_eighths_lower
  have hi : Real.log 2 < (694/1000 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (lt_div_iff₀ hp).2
  nlinarith

private theorem comparison : 2*c < (9/16)*Real.log (9/8)/Real.log 2 := by
  linarith [twice_chsh_upper, magic_lower_above]
end Comparison

private def chshHidden : Fin 8 → ((Fin 2 → Fin 2) × (Fin 2 → Fin 2)) := ![
  (![0,0],![0,0]), (![0,0],![0,1]),
  (![0,1],![0,0]), (![0,1],![1,0]),
  (![1,0],![0,1]), (![1,0],![1,1]),
  (![1,1],![1,0]), (![1,1],![1,1])]

private def pstarTheory : stdSimplex NNReal ((Fin 2 → Fin 2) × (Fin 2 → Fin 2)) :=
  ⟨fun t => ∑ h : Fin 8, if chshHidden h = t then 1/8 else 0,
    (by intro t; positivity), by rw [Finset.sum_comm]; simp⟩

private theorem pstar_is_local : localBehavior pstarTheory = chshPstar := by
  funext x y a b
  unfold localBehavior pstarTheory
  change (∑ t, if t.1 x = a ∧ t.2 y = b then
    ∑ h : Fin 8, if chshHidden h = t then (1/8 : NNReal) else 0 else 0) = _
  have hrearrange : (∑ t : ((Fin 2 → Fin 2) × (Fin 2 → Fin 2)), if t.1 x = a ∧ t.2 y = b then
      ∑ h : Fin 8, if chshHidden h = t then (1/8 : NNReal) else 0 else 0) =
      ∑ h : Fin 8, if (chshHidden h).1 x = a ∧ (chshHidden h).2 y = b then 1/8 else 0 := by
    have hdist (t : ((Fin 2 → Fin 2) × (Fin 2 → Fin 2))) : (if t.1 x = a ∧ t.2 y = b then
        ∑ h : Fin 8, if chshHidden h = t then (1/8 : NNReal) else 0 else 0) =
        ∑ h : Fin 8, if t.1 x = a ∧ t.2 y = b then
          if chshHidden h = t then (1/8 : NNReal) else 0 else 0 := by
      by_cases ht : t.1 x = a ∧ t.2 y = b <;> simp [ht]
    simp_rw [hdist]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    rw [show (fun t : ((Fin 2 → Fin 2) × (Fin 2 → Fin 2)) => if t.1 x = a ∧ t.2 y = b then
        if chshHidden h = t then (1/8 : NNReal) else 0 else 0) =
        (fun t => if chshHidden h = t then
          if t.1 x = a ∧ t.2 y = b then (1/8 : NNReal) else 0 else 0) by
      funext t; split_ifs <;> rfl]
    simp
  rw [hrearrange]
  fin_cases x <;> fin_cases y <;> fin_cases a <;> fin_cases b <;>
    norm_num [chshHidden, chshPstar, chshWin, Fin.sum_univ_succ]

private theorem source_chsh_born (x y a b : Fin 2) :
    chshBorn x y a b =
      if chshWin x y a b then ((2 + Real.sqrt 2)/8 : ℝ) else ((2 - Real.sqrt 2)/8 : ℝ) := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    norm_num
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  fin_cases x <;> fin_cases y <;> fin_cases a <;> fin_cases b <;>
    norm_num [chshBorn, singletCoefficient, chshAlice, chshBob, qubitX, qubitZ,
      chshWin, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker_apply, D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_sub, star_inv₀]
  all_goals field_simp [hn]
  all_goals ring_nf
  all_goals have hs3 : (Real.sqrt 2 : ℂ)^3 = 2*(Real.sqrt 2 : ℂ) := by rw [pow_succ, hs]
  all_goals have hs4 : (Real.sqrt 2 : ℂ)^4 = 4 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hs]; norm_num
  all_goals simp only [hs3,hs4]
  all_goals ring

private theorem chsh_table (x y a b : Fin 2) :
    chsh x y a b = Real.toNNReal
      (if chshWin x y a b then (2+Real.sqrt 2)/8 else (2-Real.sqrt 2)/8) := by
  unfold chsh
  rw [source_chsh_born]
  split_ifs <;> simp

private theorem chsh_context_divergence (x y : Fin 2) :
    (∑ a, ∑ b, (chsh x y a b : ℝ) *
      Real.log ((chsh x y a b : ℝ)/(chshPstar x y a b : ℝ))) / Real.log 2 = c := by
  have hs := Comparison.sqrt_two_bounds
  have hpos : 0 ≤ (2+Real.sqrt 2)/8 := by positivity
  have hneg : 0 ≤ (2-Real.sqrt 2)/8 := by linarith
  have hrp : ((2+Real.sqrt 2)/8)/(3/8) = (2+Real.sqrt 2)/3 := by ring
  have hrn : ((2-Real.sqrt 2)/8)/(1/8) = 2-Real.sqrt 2 := by ring
  fin_cases x <;> fin_cases y <;>
    simp only [chsh_table] <;>
    norm_num [chshPstar, chshWin, Fin.sum_univ_two,
      Real.coe_toNNReal, hpos, hneg, hrp, hrn, c] <;> ring

private theorem pstar_positive (x y a b : Fin 2) : chshPstar x y a b ≠ 0 := by
  unfold chshPstar
  split_ifs <;> norm_num

private theorem pstar_joint_support (σ : (stdSimplex NNReal (Fin 2 × Fin 2))) :
    ∀ z, joint σ chshPstar z = 0 → joint σ chsh z = 0 := by
  intro z hz
  change σ z.1 * chshPstar z.1.1 z.1.2 z.2.1 z.2.2 = 0 at hz
  have hσ : σ z.1 = 0 := (mul_eq_zero.mp hz).resolve_right (pstar_positive _ _ _ _)
  simp [joint, hσ]

private theorem scale_kl_term (s q p : ℝ) :
    (s*q)*Real.log ((s*q)/(s*p)) = s*(q*Real.log (q/p)) := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [mul_div_mul_left _ _ hs]
    ring

private theorem pstar_every_law (σ : (stdSimplex NNReal (Fin 2 × Fin 2))) :
    D (joint σ chsh) (joint σ chshPstar) = (c : EReal) := by
  unfold D
  rw [if_pos (pstar_joint_support σ)]
  congr 1
  have htotal : ∑ xy, (σ xy : ℝ) = 1 := by exact_mod_cast σ.property.2
  calc
    (∑ z : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
      (joint σ chsh z : ℝ) * Real.log ((joint σ chsh z : ℝ)/(joint σ chshPstar z : ℝ)) /
        Real.log 2) =
      ∑ xy : Fin 2 × Fin 2, (σ xy : ℝ) *
        ((∑ a, ∑ b, (chsh xy.1 xy.2 a b : ℝ) *
          Real.log ((chsh xy.1 xy.2 a b : ℝ)/(chshPstar xy.1 xy.2 a b : ℝ))) / Real.log 2) := by
      simp only [Fintype.sum_prod_type, joint, NNReal.coe_mul]
      simp_rw [scale_kl_term]
      simp only [Finset.mul_sum, Finset.sum_div, mul_div_assoc]
    _ = ∑ xy : Fin 2 × Fin 2, (σ xy : ℝ) * c := by simp_rw [chsh_context_divergence]
    _ = c := by rw [← Finset.sum_mul, htotal]; ring

private theorem chsh_all_setting_strength_upper (σ : (stdSimplex NNReal (Fin 2 × Fin 2))) : strengthAt chsh σ ≤ (c : EReal) := by
  unfold strengthAt
  calc
    _ ≤ D (joint σ chsh) (joint σ (localBehavior pstarTheory)) := iInf_le _ pstarTheory
    _ = (c : EReal) := by rw [pstar_is_local]; exact pstar_every_law σ

private theorem chsh_correlated_upper : S_cor chsh ≤ (c : EReal) := by
  unfold S_cor
  exact iSup_le chsh_all_setting_strength_upper

private theorem magic_block_losing (x y : Fin 3) (a b : Fin 4)
    (hw : ¬ Classical.wins x y a b) :
    born magicSquare (Fin.castSucc x) (Fin.castSucc y) a b = 0 := by
  change dotProduct (star twoSinglets)
    ((projector (aliceObservable (Fin.castSucc x) 0) (aliceObservable (Fin.castSucc x) 1) a ⊗ₖ
      convertBob (projector (bobObservable (Fin.castSucc y) 0) (bobObservable (Fin.castSucc y) 1) b)).mulVec twoSinglets) = _
  rw [born_converted]
  fin_cases x <;> fin_cases y <;> fin_cases a <;> fin_cases b
  all_goals try exact (hw (by decide)).elim
  all_goals norm_num [Fin.castSucc,projector,aliceObservable,bobObservable,square,pauliMatrix,qubitX,qubitZ,
    Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.kronecker_apply,
    Fintype.sum_prod_type,Fin.sum_univ_two]

private theorem quantum_total (x y : Fin 4) :
    ∑ a, ∑ b, (quantum magicSquare x y a b : ℝ) = 1 :=
  quantum_total_of_valid magicSquare magic_valid x y

private theorem quantum_push :
    pushforward coarse (fun z => (joint (uniformLaw 4) (quantum magicSquare) z : ℝ)) =
      ![7/16,9/16,0] := by
  let q := fun z : ((Fin 4 × Fin 4) × (Fin 4 × Fin 4)) => (joint (uniformLaw 4) (quantum magicSquare) z : ℝ)
  have hzero : pushforward coarse q 2 = 0 := by
    apply Finset.sum_eq_zero
    intro z _
    rcases z with ⟨⟨x,y⟩,⟨a,b⟩⟩
    by_cases hx : x.val < 3
    · by_cases hy : y.val < 3
      · by_cases hw : D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.Classical.wins ⟨x.val,hx⟩ ⟨y.val,hy⟩ a b
        · simp [coarse,hx,hy,hw]
        · simp only [coarse,hx,hy,hw,↓reduceDIte,↓reduceIte]
          change (joint (uniformLaw 4) (quantum magicSquare) ((x,y),(a,b)) : ℝ) = 0
          rw [uniform_joint]
          have hborn := magic_block_losing ⟨x.val,hx⟩ ⟨y.val,hy⟩ a b hw
          have hex : Fin.castSucc ⟨x.val,hx⟩ = x := by ext; rfl
          have hey : Fin.castSucc ⟨y.val,hy⟩ = y := by ext; rfl
          rw [hex,hey] at hborn
          simp [quantum,hborn]
      · simp [coarse,hx,hy]
    · simp [coarse,hx]
  have htotal : ∑ i, pushforward coarse q i = 1 := by
    let : DecidableEq (Fin 3) := Classical.decEq _
    simp only [pushforward]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    change (∑ z : ((Fin 4 × Fin 4) × (Fin 4 × Fin 4)), (joint (uniformLaw 4) (quantum magicSquare) z : ℝ)) = 1
    simp only [Fintype.sum_prod_type,uniform_joint,← Finset.mul_sum,quantum_total]
    norm_num
  have hout := outside_push (quantum magicSquare) quantum_total
  change pushforward coarse q 0 = 7/16 at hout
  simp only [Fin.sum_univ_succ] at htotal
  funext i
  fin_cases i
  · exact hout
  · change pushforward coarse q 1 = 9/16
    norm_num at htotal
    linarith
  · exact hzero

private theorem magic_local_lower (μ : (stdSimplex NNReal ((Fin 4 → Fin 4) × (Fin 4 → Fin 4)))) :
    (((9/16)*Real.log (9/8)/Real.log 2 : ℝ) : EReal) ≤
      D (joint (uniformLaw 4) (quantum magicSquare))
        (joint (uniformLaw 4) (localBehavior μ)) := by
  unfold D
  split_ifs with hac
  · apply EReal.coe_le_coe_iff.mpr
    have hacR : ∀ z,
        (joint (uniformLaw 4) (localBehavior μ) z : ℝ) = 0 →
        (joint (uniformLaw 4) (quantum magicSquare) z : ℝ) = 0 := by
      intro z hz
      have hz' : joint (uniformLaw 4) (localBehavior μ) z = 0 := by exact_mod_cast hz
      exact_mod_cast hac z hz'
    have htotal (x y : Fin 4) : ∑ a, ∑ b, (localBehavior μ x y a b : ℝ) = 1 := by
      exact_mod_cast localBehavior_total μ x y
    have hwin : pushforward coarse
        (fun z => (joint (uniformLaw 4) (localBehavior μ) z : ℝ)) 1 ≤ 1/2 := by
      rw [local_win_push]
      linarith [local_block_win_le_eight μ]
    have h := CoarseGrain.three_bin_bound
      (fun z => (joint (uniformLaw 4) (quantum magicSquare) z : ℝ))
      (fun z => (joint (uniformLaw 4) (localBehavior μ) z : ℝ)) coarse
      (fun z => NNReal.coe_nonneg _) (fun z => NNReal.coe_nonneg _) hacR
      quantum_push (outside_push _ htotal) hwin
    simpa [klDivergence, Finset.sum_div] using h
  · exact le_top

private theorem magic_uniform_lower :
    (((9/16)*Real.log (9/8)/Real.log 2 : ℝ) : EReal) ≤ S_uni (quantum magicSquare) := by
  exact le_iInf magic_local_lower

private theorem magic_joint : JointMeasurement magicSquare := by
  left
  refine ⟨2, 0, ?_⟩
  rintro ⟨A,B,h⟩
  have hm : (A ⊗ₖ B) (0,0) (0,0) * (A ⊗ₖ B) (1,0) (1,1) -
      (A ⊗ₖ B) (0,0) (0,1) * (A ⊗ₖ B) (1,0) (1,0) = 0 := by
    simp only [Matrix.kronecker_apply]
    ring
  rw [← h] at hm
  norm_num [magicSquare, projector, aliceObservable, square, qubitX, qubitZ, pauliMatrix,
    D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
    Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kronecker_apply] at hm

theorem result : claim := by
  refine ⟨magicSquare, magic_valid, magic_joint, ?_⟩
  have hc : (2 : EReal) * S_cor chsh ≤ ((2*c : ℝ) : EReal) := by
    calc
      _ ≤ (2 : EReal) * (c : EReal) :=
        mul_le_mul_of_nonneg_left chsh_correlated_upper (by norm_num)
      _ = ((2*c : ℝ) : EReal) := by norm_cast
  have hcmp : ((2*c : ℝ) : EReal) < (((9/16)*Real.log (9/8)/Real.log 2 : ℝ) : EReal) := by
    apply EReal.coe_lt_coe_iff.mpr
    exact Comparison.comparison
  exact lt_of_le_of_lt hc (lt_of_lt_of_le hcmp magic_uniform_lower)

end D5.S3.QuantumBounds.StatisticalStrengthMagicSquare
