/- GID: D5/S3/Quantum/QuantumChannels/ChoiRecoveryIdentifiability
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/ChoiRecoveryIdentifiability
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Arbitrary CPTP recovery relates full Choi input defect to full output error. -/

import D5.S3.Estimation.DataProcessing.InversePreparationOscillation
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Foundation.FiniteTraceDistance

/-!
The public arbitrary_cptp_choi_bridge has proof_shape: content and
admission_basis: escape-witness. Its live inference combines the inverse preparation
oscillation estimate with the actual CPTP conditional matrices, full input marginal,
and full output equality-event error. It is an unbounded dimension/real/channel family;
utility: none refers to the absence of a certified finite enumeration.

Consumed adapter proofs have proof_shape: bind-only:
basis_psd, omega_psd, basis_trace, omega_trace -> preparation, output_psd, output_trace;
recovered_psd, recovered_trace -> conditional_psd, conditional_trace, output_psd, output_trace;
conditional_psd, conditional_trace -> born_nonneg, born_rows, arbitrary_cptp_choi_bridge;
output_entry -> output_event, reduced_input_entries, reduced_output_entries;
output_psd, output_trace, target_psd, target_trace -> density states, measured/event bounds;
trace_inputMarginal, full_input_entries -> arbitrary_cptp_choi_bridge;
output_eq_local_action, target_input_marginal, born_stochastic, reduced_output_entries
  -> arbitrary_cptp_choi_bridge;
inputMarginal_psd, uniformInput_psd, uniform_reduced_entry, measured_defect_entry,
diagonal_l1_le -> measured_defect_le_full;
reduced_input_entries -> measured_defect_entry, exact_input_forces_uniform;
target_event, output_event, diagonal_l1_le -> equality_event_error_bound;
exact_input_forces_uniform -> exact_input_recovery_obstruction.
The private measured_defect_le_full, equality_event_error_bound and
arbitrary_cptp_recovery_tradeoff form the live quantitative bridge. The last is consumed
by exact_input_recovery_obstruction and the public theorem; exact_input_recovery_obstruction
is consumed by the public theorem. These helpers provide no independent novelty claim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.QuantumChannels.ChoiRecoveryIdentifiability
open Matrix Finset
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Classical
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Estimation.DataProcessing.InversePreparationOscillation

variable {d : ℕ} [NeZero d]
abbrev Q (d : ℕ) := Fin d
abbrev B (d : ℕ) := Q d × Q d
abbrev Bout (d : ℕ) := B d × B d
abbrev G (d : ℕ) := B d × Bout d
abbrev Inputs (d : ℕ) := Q d × B d

/-- Computational basis density matrix. -/
def basis (x : Q d) : Matrix (Q d) (Q d) ℂ := diagonal (fun i => if i = x then 1 else 0)
/-- Maximally mixed state matrix, on the existing matrix carrier. -/
def omega : Matrix (Q d) (Q d) ℂ := diagonal (fun _ => (1 / (d : ℂ)))

private theorem basis_psd (x : Q d) : (basis x).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  split_ifs <;> norm_num
private theorem omega_psd : (omega (d := d)).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  exact div_nonneg (by norm_num) (by positivity)
private theorem basis_trace (x : Q d) : (basis x).trace = 1 := by simp [basis, trace, Matrix.diag]
private theorem omega_trace : (omega (d := d)).trace = 1 := by
  simp [omega, trace, Matrix.diag, NeZero.ne d]

/-- The actual state fed into the arbitrary recovery channel for initializer label x. -/
def preparation (x : Q d) : DensityState (B d) :=
  ⟨CStarMatrix.ofMatrix ((omega (d := d)) ⊗ₖ basis x),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (omega_psd.kronecker (basis_psd x)).nonneg,
    by
      change (omega ⊗ₖ basis x).trace = 1
      rw [trace_kronecker, omega_trace, basis_trace, mul_one]⟩

/-- Raw matrix view of the arbitrary CPTP output; no diagonality is imposed. -/
def recovered (R : QuantumChannel (B d) (Bout d)) (x : Q d) : Matrix (Bout d) (Bout d) ℂ :=
  CStarMatrix.ofMatrix.symm (R.mapState (preparation x)).1

/-- Full Ci conditional density, tracing Bi,Bo,Co and preserving Ci coherences. -/
def conditional (R : QuantumChannel (B d) (Bout d)) (x : Q d) : Matrix (Q d) (Q d) ℂ :=
  partialTraceRight (partialTraceLeft (recovered R x))

private theorem recovered_psd (R : QuantumChannel (B d) (Bout d)) (x : Q d) :
    (recovered R x).PosSemidef := density_posSemidef _
private theorem recovered_trace (R : QuantumChannel (B d) (Bout d)) (x : Q d) :
    (recovered R x).trace = 1 := (R.mapState (preparation x)).2.2
private theorem conditional_psd (R : QuantumChannel (B d) (Bout d)) (x : Q d) :
    (conditional R x).PosSemidef :=
  partialTraceRight_posSemidef (partialTraceLeft_posSemidef (recovered_psd R x))
private theorem conditional_trace (R : QuantumChannel (B d) (Bout d)) (x : Q d) :
    (conditional R x).trace = 1 := by
  rw [conditional, trace_partialTraceRight, trace_partialTraceLeft, recovered_trace]

/-- Preparation matrix column on Ai. -/
def alpha (M : Matrix (Q d) (Q d) ℝ) (x : Q d) : Matrix (Q d) (Q d) ℂ :=
  diagonal (fun a => (M a x : ℂ))

/-- Fixed initializer, before applying id on AiAo and R on BiBo. -/
def initializer (M : Matrix (Q d) (Q d) ℝ) : Matrix (B d × B d) (B d × B d) ℂ :=
  ∑ x, (1 / (d : ℂ)) • ((alpha M x ⊗ₖ basis x) ⊗ₖ (omega ⊗ₖ basis x))

/-- Actual recovered full output, as the CP-positive block sum of id tensor R. -/
def output (M : Matrix (Q d) (Q d) ℝ) (R : QuantumChannel (B d) (Bout d)) :
    Matrix (G d) (G d) ℂ :=
  ∑ x, (1 / (d : ℂ)) • ((alpha M x ⊗ₖ basis x) ⊗ₖ recovered R x)

private theorem output_entry (M : Matrix (Q d) (Q d) ℝ)
    (R : QuantumChannel (B d) (Bout d)) (a x a' x' : Q d) (b b' : Bout d) :
    output M R ((a,x),b) ((a',x'),b') =
      if a = a' ∧ x = x' then (M a x : ℂ) / d * recovered R x b b' else 0 := by
  classical
  by_cases ha : a = a'
  · subst a'
    by_cases hx : x = x'
    · subst x'
      simp [output, alpha, basis, Matrix.sum_apply, Matrix.kronecker_apply,
        Matrix.diagonal_apply, Matrix.smul_apply, mul_ite, ite_mul, div_eq_mul_inv, mul_comm,
        mul_left_comm, mul_assoc]
    · simp [output, alpha, basis, Matrix.sum_apply, Matrix.kronecker_apply,
        Matrix.diagonal_apply, Matrix.smul_apply, mul_ite, ite_mul, hx]
  · simp [output, alpha, Matrix.sum_apply, Matrix.kronecker_apply,
      Matrix.diagonal_apply, Matrix.smul_apply, ha]

private theorem output_psd (M : Matrix (Q d) (Q d) ℝ)
    (hM : ∀ a x, 0 ≤ M a x) (R : QuantumChannel (B d) (Bout d)) :
    (output M R).PosSemidef := by
  apply posSemidef_sum
  intro x _
  apply PosSemidef.smul
  · apply PosSemidef.kronecker
    · exact (PosSemidef.diagonal fun a => (by change (0 : ℂ) ≤ (M a x : ℂ); exact_mod_cast hM a x)).kronecker (basis_psd x)
    · exact recovered_psd R x
  · exact div_nonneg (by norm_num) (by positivity)

private theorem output_trace (M : Matrix (Q d) (Q d) ℝ)
    (hcol : ∀ x, ∑ a, M a x = 1) (R : QuantumChannel (B d) (Bout d)) :
    (output M R).trace = 1 := by
  have ha (x : Q d) : (alpha M x).trace = 1 := by
    simpa [alpha, trace, Matrix.diag] using congrArg Complex.ofReal (hcol x)
  simp [output, trace_sum, trace_smul, trace_kronecker, recovered_trace, basis_trace,
    ha, NeZero.ne d]

/-- Stated physical target: Ai,Bi uniform; Ao=Bo=Ci and Co=0. -/
def target : Matrix (G d) (G d) ℂ :=
  diagonal (fun z => if z.1.2 = z.2.1.2 ∧ z.1.2 = z.2.2.1 ∧ z.2.2.2 = 0
    then 1 / (d : ℂ)^3 else 0)

private theorem target_psd : (target (d := d)).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro z
  split_ifs
  · exact div_nonneg (by norm_num) (by positivity)
  · exact le_rfl
private theorem target_trace : (target (d := d)).trace = 1 := by
  classical
  simp [target, trace, Matrix.diag, Fintype.sum_prod_type, ite_and, NeZero.ne d]
  all_goals field_simp [NeZero.ne d]

/-- Trace Ao,Bo,Co, retaining all complex Ai,Bi,Ci matrix entries. -/
def inputMarginal (X : Matrix (G d) (G d) ℂ) : Matrix (Inputs d) (Inputs d) ℂ :=
  fun u v => ∑ ao, ∑ bo, ∑ co,
    X ((u.1,ao),((u.2.1,bo),(u.2.2,co))) ((v.1,ao),((v.2.1,bo),(v.2.2,co)))

/-- The normalized input-Choi constraint is an equation on this existing matrix. -/
def uniformInput : Matrix (Inputs d) (Inputs d) ℂ := omega ⊗ₖ (omega ⊗ₖ omega)

/-- The actual CP-positive recovered output as the canonical density-state subtype. -/
def outputState (M : Matrix (Q d) (Q d) ℝ) (hM : ∀ a x, 0 ≤ M a x)
    (hcol : ∀ x, ∑ a, M a x = 1) (R : QuantumChannel (B d) (Bout d)) : DensityState (G d) :=
  ⟨CStarMatrix.ofMatrix (output M R),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (output_psd M hM R).nonneg,
    output_trace M hcol R⟩

/-- The physical target on the canonical density-state carrier. -/
def targetState : DensityState (G d) :=
  ⟨CStarMatrix.ofMatrix target,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv target_psd.nonneg, target_trace⟩

def fullError (M : Matrix (Q d) (Q d) ℝ) (R : QuantumChannel (B d) (Bout d)) : ℝ :=
  traceNorm (output M R - target) / 2

def inputDefect (M : Matrix (Q d) (Q d) ℝ) (R : QuantumChannel (B d) (Bout d)) : ℝ :=
  traceNorm (inputMarginal (output M R) - uniformInput) / 2

def born (R : QuantumChannel (B d) (Bout d)) : Matrix (Q d) (Q d) ℝ :=
  fun x c => (conditional R x c c).re

private theorem born_nonneg (R : QuantumChannel (B d) (Bout d)) (x c : Q d) :
    0 ≤ born R x c := (Complex.nonneg_iff.mp (conditional_psd R x).diag_nonneg).1
private theorem born_rows (R : QuantumChannel (B d) (Bout d)) : born R *ᵥ 1 = 1 := by
  ext x
  have := congrArg Complex.re (conditional_trace R x)
  simpa [Matrix.mulVec, dotProduct, born, trace, Matrix.diag] using this


/-- The full complex matrix action of a quantum channel. -/
def rawMap (R : QuantumChannel (B d) (Bout d)) :
    Matrix (B d) (B d) ℂ →ₗ[ℂ] Matrix (Bout d) (Bout d) ℂ :=
  CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
    (R.toCompletelyPositiveMap.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)

/-- The recovered sum is the genuine id tensor R action on the fixed initializer,
entry by entry, on the full complex output algebra. -/
private theorem output_eq_local_action (M : Matrix (Q d) (Q d) ℝ)
    (R : QuantumChannel (B d) (Bout d)) (u v : G d) :
    output M R u v = rawMap R (fun b b' => initializer M (u.1,b) (v.1,b')) u.2 v.2 := by
  have hb : (fun b b' => initializer M (u.1,b) (v.1,b')) =
      ∑ x, ((1 / (d : ℂ)) * (alpha M x ⊗ₖ basis x) u.1 v.1) •
        (omega ⊗ₖ basis x) := by
    ext b b'
    simp [initializer, Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker_apply,
      smul_eq_mul, mul_assoc]
  rw [hb, map_sum]
  simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [output, Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  have hr : rawMap R (omega ⊗ₖ basis x) = recovered R x := by rfl
  rw [hr]
  ring

private theorem inputMarginal_psd (X : Matrix (G d) (G d) ℂ) (hX : X.PosSemidef) :
    (inputMarginal X).PosSemidef := by
  have he : inputMarginal X = ∑ ao : Q d, ∑ bo : Q d, ∑ co : Q d,
      X.submatrix (fun u : Inputs d => ((u.1,ao),((u.2.1,bo),(u.2.2,co))))
        (fun u : Inputs d => ((u.1,ao),((u.2.1,bo),(u.2.2,co)))) := by
    ext u v
    simp [inputMarginal, Matrix.sum_apply]
  rw [he]
  exact posSemidef_sum _ fun ao _ => posSemidef_sum _ fun bo _ =>
    posSemidef_sum _ fun co _ => hX.submatrix _

private theorem uniformInput_psd : (uniformInput (d := d)).PosSemidef :=
  omega_psd.kronecker (omega_psd.kronecker omega_psd)

/-- The target obeys the full normalized input-Choi equation. -/
private theorem target_input_marginal : inputMarginal (target (d := d)) = uniformInput := by
  classical
  ext ⟨a,b,c⟩ ⟨a',b',c'⟩
  by_cases ha : a = a' <;> by_cases hb : b = b' <;> by_cases hc : c = c'
  all_goals simp [inputMarginal, target, uniformInput, omega, Matrix.kronecker_apply,
    Matrix.diagonal_apply, ha, hb, hc, Prod.mk.injEq, ite_and, eq_comm]
  all_goals field_simp
  all_goals ring

/-- Trace Bi after the actual full input marginal; no Ci off-diagonal is discarded. -/
private theorem reduced_input_entries (M : Matrix (Q d) (Q d) ℝ)
    (R : QuantumChannel (B d) (Bout d)) (a a' c c' : Q d) :
    (∑ b : Q d, inputMarginal (output M R) (a,(b,c)) (a',(b,c'))) =
    if a = a' then (1 / (d : ℂ)) * ∑ x, (M a x : ℂ) * conditional R x c c' else 0 := by
  classical
  simp only [inputMarginal, output_entry, and_true]
  split_ifs with ha
  · subst a'
    simp only [conditional, partialTraceRight, partialTraceLeft, Fintype.sum_prod_type]
    simp only [Finset.mul_sum, div_eq_mul_inv, one_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    calc
      (∑ b : Q d, ∑ bo : Q d, ∑ co : Q d,
          (M a x : ℂ) * (d : ℂ)⁻¹ * recovered R x ((b,bo),(c,co)) ((b,bo),(c',co))) =
          ∑ b : Q d, ∑ co : Q d, ∑ bo : Q d,
          (M a x : ℂ) * (d : ℂ)⁻¹ * recovered R x ((b,bo),(c,co)) ((b,bo),(c',co)) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_comm]
      _ = ∑ co : Q d, ∑ b : Q d, ∑ bo : Q d,
          (d : ℂ)⁻¹ * ((M a x : ℂ) * recovered R x ((b,bo),(c,co)) ((b,bo),(c',co))) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro co _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro bo _
        ring
  · simp [ha]

/-- Born statistics are a row-stochastic matrix, although the conditional states are arbitrary. -/
private theorem born_stochastic (R : QuantumChannel (B d) (Bout d)) :
    (∀ x c, 0 ≤ born R x c) ∧ born R *ᵥ 1 = 1 := ⟨born_nonneg R, born_rows R⟩

private theorem diagonal_l1_le {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : X.IsHermitian) : ∑ i, |(X i i).re| ≤ traceNorm X := by
  let P := posPart X
  let N := negPart X
  have hP : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg X)
  have hN : N.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg X)
  have he : X = P - N := (CFC.posPart_sub_negPart X hX).symm
  rw [trace_norm_jordan_mass X hX]
  change (∑ i, |(X i i).re|) ≤ P.trace.re + N.trace.re
  have hi (i : n) : |(X i i).re| ≤ (P i i).re + (N i i).re := by
    rw [he]
    change |(P i i).re - (N i i).re| ≤ _
    exact abs_sub_le_iff.mpr ⟨by linarith [(Complex.nonneg_iff.mp (hN.diag_nonneg (i := i))).1],
      by linarith [(Complex.nonneg_iff.mp (hP.diag_nonneg (i := i))).1]⟩
  simpa [trace, Matrix.diag, sum_add_distrib] using sum_le_sum fun i _ => hi i


private theorem uniform_reduced_entry (a c c' : Q d) :
    (∑ b : Q d, uniformInput (a,(b,c)) (a,(b,c'))) =
      (1 / (d : ℂ)) * omega c c' := by
  by_cases hc : c = c'
  · subst c'
    simp [uniformInput, omega, Matrix.diagonal_apply]
    field_simp
  · simp [uniformInput, omega, Matrix.diagonal_apply, hc]

private theorem measured_defect_entry (M : Matrix (Q d) (Q d) ℝ)
    (R : QuantumChannel (B d) (Bout d)) (a c : Q d) :
    (∑ b : Q d, ((inputMarginal (output M R) - uniformInput : Matrix (Inputs d) (Inputs d) ℂ) (a,(b,c)) (a,(b,c))).re) =
      (1 / (d : ℝ)) * ((M * born R) a c - 1 / (d : ℝ)) := by
  have h := reduced_input_entries M R a a c c
  have hu := uniform_reduced_entry (d := d) a c c
  simp only [if_pos rfl] at h
  have he : (∑ b : Q d, (inputMarginal (output M R) - uniformInput : Matrix (Inputs d) (Inputs d) ℂ) (a,(b,c)) (a,(b,c))) =
      (1 / (d : ℂ)) * ((∑ x, (M a x : ℂ) * conditional R x c c) - 1 / (d : ℂ)) := by
    change (∑ b, (inputMarginal (output M R) (a,(b,c)) (a,(b,c)) -
      uniformInput (a,(b,c)) (a,(b,c)))) = _
    rw [sum_sub_distrib, h, hu]
    simp [omega, mul_sub]
  have hre := congrArg Complex.re he
  have hd : (1 / (d : ℂ)) = ((1 / (d : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hd] at hre
  simpa [born, Matrix.mul_apply, Complex.mul_re, Complex.sub_re] using hre

/-- The measured AiCi defect is dominated by the FULL AiBiCi Choi input defect. -/
private theorem measured_defect_le_full (M : Matrix (Q d) (Q d) ℝ)
    (hM : ∀ a x, 0 ≤ M a x) (R : QuantumChannel (B d) (Bout d)) :
    (1 / (2 * (d : ℝ))) * ∑ a, ∑ c,
      |(M * born R) a c - 1 / (d : ℝ)| ≤ inputDefect M R := by
  let X := inputMarginal (output M R) - uniformInput
  have hh : X.IsHermitian := (inputMarginal_psd _ (output_psd M hM R)).isHermitian.sub
    uniformInput_psd.isHermitian
  have hb : (∑ a : Q d, ∑ c : Q d, |∑ b : Q d, (X (a,(b,c)) (a,(b,c))).re|) ≤ traceNorm X := by
    calc
      _ ≤ ∑ a : Q d, ∑ c : Q d, ∑ b : Q d, |(X (a,(b,c)) (a,(b,c))).re| := by
        apply sum_le_sum
        intro a _
        exact sum_le_sum fun c _ => abs_sum_le_sum_abs _ _
      _ = ∑ i : Inputs d, |(X i i).re| := by
        simp only [Fintype.sum_prod_type]
        apply sum_congr rfl
        intro a _
        rw [sum_comm]
      _ ≤ traceNorm X := diagonal_l1_le X hh
  have hc : (0 : ℝ) ≤ 1 / d := by positivity
  have he (a c : Q d) : |∑ b : Q d, (X (a,(b,c)) (a,(b,c))).re| =
      (1 / (d : ℝ)) * |(M * born R) a c - 1 / (d : ℝ)| := by
    rw [show (∑ b : Q d, (X (a,(b,c)) (a,(b,c))).re) = _ from measured_defect_entry M R a c,
      abs_mul, abs_of_nonneg hc]
  simp_rw [he] at hb
  simp only [← mul_sum] at hb
  unfold inputDefect
  dsimp only [X] at hb
  convert (div_le_div_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 2)) using 1 <;>
    simp only [div_eq_mul_inv, _root_.mul_inv_rev] <;> ring

private def event (z : G d) : Prop := z.1.2 = z.2.2.1
private def eventMass (X : Matrix (G d) (G d) ℂ) : ℝ :=
  ∑ z, if event z then (X z z).re else 0

private theorem target_event : eventMass (target (d := d)) = 1 := by
  classical
  have he : eventMass (target (d := d)) = (target (d := d)).trace.re := by
    simp only [eventMass, trace, Matrix.diag, Complex.re_sum]
    apply sum_congr rfl
    intro z _
    by_cases hz : event z
    · simp [hz]
    · have hz' : ¬ z.1.2 = z.2.2.1 := hz
      have hn : ¬ (z.1.2 = z.2.1.2 ∧ z.1.2 = z.2.2.1 ∧ z.2.2.2 = 0) :=
        fun h => hz' h.2.1
      simp [hz, target, hn]
  rw [he, target_trace]
  norm_num

private theorem output_event (M : Matrix (Q d) (Q d) ℝ)
    (hcol : ∀ x, ∑ a, M a x = 1) (R : QuantumChannel (B d) (Bout d)) :
    eventMass (output M R) = (born R).trace / d := by
  classical
  have he (a x : Q d) (b : Bout d) :
      (output M R ((a,x),b) ((a,x),b)).re =
        (M a x / (d : ℝ)) * (recovered R x b b).re := by
    rw [output_entry]
    simp only [and_self, ite_true]
    have hd : (M a x : ℂ) / (d : ℂ) = ((M a x / (d : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [hd]
    simp
  have hc (x : Q d) : (∑ bi : Q d, ∑ bo : Q d, ∑ co : Q d,
      (recovered R x ((bi,bo),(x,co)) ((bi,bo),(x,co))).re) = born R x x := by
    simp only [born, conditional, partialTraceRight, partialTraceLeft,
      Fintype.sum_prod_type, Complex.re_sum]
    calc
      _ = ∑ bi : Q d, ∑ co : Q d, ∑ bo : Q d,
          (recovered R x ((bi,bo),(x,co)) ((bi,bo),(x,co))).re := by
        apply sum_congr rfl
        intro bi _
        rw [sum_comm]
      _ = _ := by rw [sum_comm]
  have hs : eventMass (output M R) = ∑ a : Q d, ∑ x : Q d,
      ∑ bi : Q d, ∑ bo : Q d, ∑ co : Q d,
      (M a x / (d : ℝ)) * (recovered R x ((bi,bo),(x,co)) ((bi,bo),(x,co))).re := by
    simp [eventMass, event, Fintype.sum_prod_type, he, Finset.sum_ite_irrel]
  rw [hs]
  simp_rw [← mul_sum, hc]
  rw [sum_comm]
  have hh (x : Q d) : ∑ a : Q d, (M a x / (d : ℝ)) * born R x x =
      (1 / (d : ℝ)) * born R x x := by rw [← sum_mul, ← sum_div, hcol]
  simp_rw [hh]
  simp [trace, Matrix.diag, ← mul_sum, div_eq_mul_inv, mul_comm]

/-- The Ao=Ci equality event has probability trace(P)/d on the actual arbitrary-CPTP output.
Its probability one on the target bounds FULL output trace distance. -/
private theorem equality_event_error_bound (M : Matrix (Q d) (Q d) ℝ)
    (hM : ∀ a x, 0 ≤ M a x) (hcol : ∀ x, ∑ a, M a x = 1)
    (R : QuantumChannel (B d) (Bout d)) :
    1 - (born R).trace / d ≤ fullError M R := by
  classical
  let X := output M R - target
  let v : G d → ℝ := fun z => (X z z).re
  let w : G d → ℝ := fun z => if event z then 1 else 0
  have hv : ∑ z, v z = 0 := by
    have ht : X.trace = 0 := by
      simp [X, Matrix.trace_sub, output_trace M hcol R, target_trace]
    simpa [v, trace, Matrix.diag] using congrArg Complex.re ht
  have hw (i j : G d) : w i - w j ≤ 1 := by
    dsimp [w]
    split_ifs <;> norm_num
  have hh := zero_sum_pairing_bound v w 1 hv hw
  have he : (∑ z, v z * w z) = eventMass (output M R) - eventMass (target (d := d)) := by
    simp only [v, w, X, eventMass, ← sum_sub_distrib]
    apply sum_congr rfl
    intro z _
    by_cases hz : event z <;> simp [hz]
  rw [he, output_event M hcol R, target_event] at hh
  have hn := diagonal_l1_le X ((output_psd M hM R).isHermitian.sub target_psd.isHermitian)
  have ha : 1 - (born R).trace / d ≤ |(born R).trace / d - 1| := by
    simpa using neg_le_abs ((born R).trace / d - 1)
  unfold fullError
  dsimp only [v] at hh
  dsimp only [X] at hn
  linarith

/-- Statistical inverse identifiability constrains arbitrary quantum recovery: full output error
plus inverse-column oscillation times full normalized input-Choi defect is at least 1-1/d. -/
private theorem arbitrary_cptp_recovery_tradeoff (M N : Matrix (Q d) (Q d) ℝ) (L : ℝ)
    (hM : ∀ a x, 0 ≤ M a x) (hrow : M *ᵥ 1 = 1)
    (hcol : ∀ x, ∑ a, M a x = 1) (hNM : N * M = 1)
    (hL : ∀ a c b, N c a - N b a ≤ L)
    (R : QuantumChannel (B d) (Bout d)) :
    1 - 1 / (d : ℝ) ≤ traceDistance (outputState M hM hcol R) targetState +
      L * inputDefect M R := by
  change 1 - 1 / (d : ℝ) ≤ fullError M R + L * inputDefect M R
  have hd : (0 : ℝ) < d := by exact_mod_cast (NeZero.pos d)
  have hLn : 0 ≤ L := by simpa using hL 0 0 0
  have ht := inverse_preparation_trace_bound M N (born R) L hrow hNM (born_rows R) hL
  simp only [Fintype.card_fin] at ht
  have hm := measured_defect_le_full M hM R
  have hg := equality_event_error_bound M hM hcol R
  let S := ∑ a, ∑ c, |(M * born R) a c - 1 / (d : ℝ)|
  have hm' : S / (2 * (d : ℝ)) ≤ inputDefect M R := by
    convert hm using 1 <;> dsimp [S] <;> ring
  have hs := (div_le_iff₀ (by positivity : 0 < 2 * (d : ℝ))).mp hm'
  have ht' : (born R).trace - 1 ≤ L * (d : ℝ) * inputDefect M R := by
    have hb : (born R).trace - 1 ≤ L / 2 * S := (le_abs_self _).trans ht
    have := mul_le_mul_of_nonneg_left hs hLn
    nlinarith
  have hgd := mul_le_mul_of_nonneg_left hg hd.le
  have hcancel : (d : ℝ) * ((born R).trace / d) = (born R).trace := by field_simp
  suffices hh : (d : ℝ) * (1 - 1 / (d : ℝ)) ≤
      (d : ℝ) * (fullError M R + L * inputDefect M R) by nlinarith
  have hone : (d : ℝ) * (1 - 1 / (d : ℝ)) = d - 1 := by field_simp <;> ring
  rw [hone]
  nlinarith [hcancel]

/-- Exact full input-Choi normalization fixes every COMPLETE conditional Ci matrix.
This conclusion includes all off-diagonal entries. -/
private theorem exact_input_forces_uniform (M N : Matrix (Q d) (Q d) ℝ)
    (hrow : M *ᵥ 1 = 1) (hNM : N * M = 1)
    (R : QuantumChannel (B d) (Bout d))
    (hTP : inputMarginal (output M R) = uniformInput) :
    ∀ x, conditional R x = omega := by
  have hn : N *ᵥ (1 : Q d → ℝ) = 1 := by
    calc
      N *ᵥ 1 = N *ᵥ (M *ᵥ 1) := by rw [hrow]
      _ = 1 := by rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
  have hnc (x : Q d) : ∑ a, (N x a : ℂ) = 1 := by
    have hh := congrArg Complex.ofReal (congrFun hn x)
    simpa [Matrix.mulVec, dotProduct] using hh
  have hprod (x y : Q d) : ∑ a, (N x a : ℂ) * (M a y : ℂ) = if x = y then 1 else 0 := by
    have hh := congrArg Complex.ofReal (congrFun (congrFun hNM x) y)
    simpa [Matrix.mul_apply, Matrix.one_apply, apply_ite] using hh
  intro x
  ext c c'
  have hw (a : Q d) : ∑ y, (M a y : ℂ) * conditional R y c c' = omega c c' := by
    have hh := reduced_input_entries M R a a c c'
    rw [hTP, uniform_reduced_entry, if_pos rfl] at hh
    exact (mul_left_cancel₀ (by exact one_div_ne_zero (by exact_mod_cast NeZero.ne d)) hh).symm
  calc
    conditional R x c c' = ∑ y, (if x = y then (1 : ℂ) else 0) * conditional R y c c' := by
      simp
    _ = ∑ y, (∑ a, (N x a : ℂ) * (M a y : ℂ)) * conditional R y c c' := by simp_rw [hprod]
    _ = ∑ a, (N x a : ℂ) * (∑ y, (M a y : ℂ) * conditional R y c c') := by
      simp only [sum_mul, mul_sum, mul_assoc]
      rw [sum_comm]
    _ = ∑ a, (N x a : ℂ) * omega c c' := by simp_rw [hw]
    _ = omega c c' := by rw [← sum_mul, hnc, one_mul]

/-- Exact TP forces uniform conditional states AND the full quantum distance obstruction. -/
private theorem exact_input_recovery_obstruction (M N : Matrix (Q d) (Q d) ℝ) (L : ℝ)
    (hM : ∀ a x, 0 ≤ M a x) (hrow : M *ᵥ 1 = 1)
    (hcol : ∀ x, ∑ a, M a x = 1) (hNM : N * M = 1)
    (hL : ∀ a c b, N c a - N b a ≤ L)
    (R : QuantumChannel (B d) (Bout d))
    (hTP : inputMarginal (output M R) = uniformInput) :
    (∀ x, conditional R x = omega) ∧ 1 - 1 / (d : ℝ) ≤ fullError M R := by
  refine ⟨exact_input_forces_uniform M N hrow hNM R hTP, ?_⟩
  have hh := arbitrary_cptp_recovery_tradeoff M N L hM hrow hcol hNM hL R
  have hz : inputDefect M R = 0 := by simp [inputDefect, hTP, traceNorm]
  change 1 - 1 / (d : ℝ) ≤ fullError M R + L * inputDefect M R at hh
  simpa [hz] using hh


private theorem reduced_output_entries (M : Matrix (Q d) (Q d) ℝ)
    (R : QuantumChannel (B d) (Bout d)) (a x a' x' c c' : Q d) :
    (∑ bi : Q d, ∑ bo : Q d, ∑ co : Q d,
      output M R ((a,x),((bi,bo),(c,co))) ((a',x'),((bi,bo),(c',co)))) =
    if a = a' ∧ x = x' then (M a x : ℂ) / d * conditional R x c c' else 0 := by
  classical
  simp only [output_entry]
  by_cases h : a = a' ∧ x = x'
  · obtain ⟨ha, hx⟩ := h
    subst a'
    subst x'
    simp only [and_self, ite_true, conditional, partialTraceRight, partialTraceLeft,
      Fintype.sum_prod_type, Finset.mul_sum]
    calc
      _ = ∑ bi : Q d, ∑ co : Q d, ∑ bo : Q d,
          (M a x : ℂ) / d * recovered R x ((bi,bo),(c,co)) ((bi,bo),(c',co)) := by
        apply sum_congr rfl
        intro bi _
        rw [sum_comm]
      _ = _ := by rw [sum_comm]
  · simp [h]


private theorem trace_inputMarginal (X : Matrix (G d) (G d) ℂ) :
    (inputMarginal X).trace = X.trace := by
  simp only [trace, Matrix.diag, inputMarginal, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  calc
    _ = ∑ b : Q d, ∑ ao : Q d, ∑ c : Q d, ∑ bo : Q d, ∑ co : Q d,
        X ((a,ao),((b,bo),(c,co))) ((a,ao),((b,bo),(c,co))) := by
      apply sum_congr rfl
      intro b _
      rw [sum_comm]
    _ = ∑ ao : Q d, ∑ b : Q d, ∑ c : Q d, ∑ bo : Q d, ∑ co : Q d,
        X ((a,ao),((b,bo),(c,co))) ((a,ao),((b,bo),(c,co))) := by rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro ao _
      apply sum_congr rfl
      intro b _
      rw [sum_comm]

private theorem full_input_entries (M : Matrix (Q d) (Q d) ℝ)
    (R : QuantumChannel (B d) (Bout d)) (a a' b b' c c' : Q d) :
    inputMarginal (output M R) (a,(b,c)) (a',(b',c')) =
      if a = a' then (1 / (d : ℂ)) * ∑ x, (M a x : ℂ) *
        ∑ bo : Q d, ∑ co : Q d,
          recovered R x ((b,bo),(c,co)) ((b',bo),(c',co)) else 0 := by
  simp only [inputMarginal, output_entry, and_true]
  by_cases ha : a = a'
  · simp only [ha, ite_true, mul_sum, div_eq_mul_inv, one_mul]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro bo _
    apply sum_congr rfl
    intro co _
    ring
  · simp [ha]

/-- For every finite dimension and arbitrary CPTP recovery, the actual fixed-initializer output
has full conditional Ci densities and an explicit complete input-marginal formula.
Inverse preparation oscillation bounds its full output error by its full input defect.
Exact full TP fixes the entire conditional matrices, including every off-diagonal entry. -/
theorem arbitrary_cptp_choi_bridge (M N : Matrix (Q d) (Q d) ℝ) (L : ℝ)
    (hM : ∀ a x, 0 ≤ M a x) (hrow : M *ᵥ 1 = 1)
    (hcol : ∀ x, ∑ a, M a x = 1) (hNM : N * M = 1)
    (hL : ∀ a c b, N c a - N b a ≤ L)
    (R : QuantumChannel (B d) (Bout d)) :
    (∀ u v, output M R u v =
      rawMap R (fun b b' => initializer M (u.1,b) (v.1,b')) u.2 v.2) ∧
    inputMarginal (target (d := d)) = uniformInput ∧
    ((∀ x c, 0 ≤ born R x c) ∧ born R *ᵥ 1 = 1) ∧
    ((∀ x, (conditional R x).PosSemidef ∧ (conditional R x).trace = 1) ∧
      ((inputMarginal (output M R)).PosSemidef ∧
        (inputMarginal (output M R)).trace = 1) ∧
      (∀ a a' b b' c c',
        inputMarginal (output M R) (a,(b,c)) (a',(b',c')) =
          if a = a' then (1 / (d : ℂ)) * ∑ x, (M a x : ℂ) *
            ∑ bo : Q d, ∑ co : Q d,
              recovered R x ((b,bo),(c,co)) ((b',bo),(c',co)) else 0)) ∧
    (∀ a x a' x' c c',
      (∑ bi : Q d, ∑ bo : Q d, ∑ co : Q d,
        output M R ((a,x),((bi,bo),(c,co))) ((a',x'),((bi,bo),(c',co)))) =
      if a = a' ∧ x = x' then (M a x : ℂ) / d * conditional R x c c' else 0) ∧
    (1 - 1 / (d : ℝ) ≤ traceDistance (outputState M hM hcol R) targetState +
      L * inputDefect M R) ∧
    (inputMarginal (output M R) = uniformInput →
      (∀ x, conditional R x = omega) ∧ 1 - 1 / (d : ℝ) ≤ fullError M R) := by
  exact ⟨output_eq_local_action M R, target_input_marginal, born_stochastic R,
    ⟨fun x => ⟨conditional_psd R x, conditional_trace R x⟩,
      ⟨inputMarginal_psd _ (output_psd M hM R), by
        rw [trace_inputMarginal, output_trace M hcol R]⟩,
      full_input_entries M R⟩,
    reduced_output_entries M R,
    arbitrary_cptp_recovery_tradeoff M N L hM hrow hcol hNM hL R,
    exact_input_recovery_obstruction M N L hM hrow hcol hNM hL R⟩

#print axioms arbitrary_cptp_choi_bridge
end D5.S3.Quantum.QuantumChannels.ChoiRecoveryIdentifiability
