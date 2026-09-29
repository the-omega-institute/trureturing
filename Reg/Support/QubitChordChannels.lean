import D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily
import D5.S3.Quantum.Foundation.FiniteKrausChannel

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix Set Filter Finset
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open D5.S3.Quantum.Information.ActualQubitChordObstruction
open D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily

noncomputable section
namespace Reg.Support.QubitChordChannels

/-- Two diagonal Schur multipliers conditioned on the program basis. -/
def signs : Fin 2 → Fin 4 → Fin 3 → ℂ :=
  ![![![1,1,1], ![1,1,1], ![1,1,1], ![1,-1,1]],
    ![![1,1,1], ![1,1,1], ![1,1,-1], ![-1,1,1]]]

def kraus (r : Fin 2 × Fin 4) : Matrix (Fin 3) (Fin 3 × Fin 2) ℂ := fun i jp =>
  if i = jp.1 ∧ jp.2 = r.1 then signs r.1 r.2 i / 2 else 0

theorem kraus_complete : (∑ r, (kraus r).conjTranspose * kraus r) = 1 := by
  apply Matrix.ext
  intro ⟨i,p⟩ ⟨j,q⟩
  fin_cases i <;> fin_cases p <;> fin_cases j <;> fin_cases q <;>
    norm_num [kraus, signs, Matrix.mul_apply, Matrix.sum_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
      map_ofNat, Matrix.cons_val_two, Matrix.cons_val_three, Fin.isValue, Matrix.one_apply] <;> norm_num [Fin.ext_iff, map_ofNat]

def processor : QuantumChannel (Fin 3 × Fin 2) (Fin 3) :=
  (finite_kraus_quantum_channel kraus kraus_complete).choose

theorem processor_action (X : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    CStarMatrix.ofMatrix.symm (processor.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      ∑ r, kraus r * X * (kraus r).conjTranspose :=
  (finite_kraus_quantum_channel kraus kraus_complete).choose_spec X

def curve (u : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(u : ℂ), ((1-u : ℝ) : ℂ)]

theorem curve_density (u : ℝ) (hu : u ∈ Ioo (2 * (1/2 : ℝ) - 1) 1) :
    (curve u).PosSemidef ∧ trace (curve u) = 1 := by
  constructor
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i
    · exact Complex.zero_le_real.mpr (by linarith [hu.1])
    · exact Complex.zero_le_real.mpr (by linarith [hu.2])
  · simp [curve, Matrix.trace, Fin.sum_univ_two]

/-- The QFI implication is nonvacuous on this exact witness at every interior point. -/
theorem curve_differentiable : Differentiable ℝ curve := by
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp [curve, Matrix.diagonal] <;> fun_prop

theorem processor_output (k : Fin 2) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    programOutput processor k M =
      ∑ r, kraus r * Matrix.kronecker (signalProbe k) M * (kraus r).conjTranspose := by
  exact processor_action _

def weights : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![1,1/2,1; 1/2,1,1/2; 1,1/2,1],
    !![1,1/2,0; 1/2,1,1/2; 0,1/2,1]]

theorem processor_entry (k : Fin 2) (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 3) :
    programOutput processor k M i j =
      signalProbe k i j * (weights 0 i j * M 0 0 + weights 1 i j * M 1 1) := by
  rw [processor_output]
  fin_cases i <;> fin_cases j <;>
    simp [kraus, signs, weights, Matrix.mul_apply, Matrix.sum_apply,
      Matrix.conjTranspose_apply, Matrix.kronecker_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
      map_ofNat, Matrix.cons_val_two] <;> ring

theorem processor_exact (u : ℝ) (k : Fin 2) :
    programOutput processor k (curve u) = probeTarget (1/2) u k := by
  ext i j
  rw [processor_entry]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [curve, weights, signalProbe, probeTarget, Matrix.vecMulVec] <;> ring

theorem erased_observation : (jointObservation processor).comp projectX = 0 := by
  ext x k i j
  change programOutput processor k (blochMatrix 0 (projectX x)) i j = 0
  rw [processor_entry]
  simp [blochMatrix, projectX]

def discardKraus (q : Fin 2) : Matrix (Fin 3) (Fin 3 × Fin 2) ℂ := fun i jp =>
  if i = jp.1 ∧ jp.2 = q then 1 else 0

theorem discard_complete : (∑ q, (discardKraus q).conjTranspose * discardKraus q) = 1 := by
  apply Matrix.ext
  intro ⟨i,p⟩ ⟨j,q⟩
  fin_cases i <;> fin_cases p <;> fin_cases j <;> fin_cases q <;>
    norm_num [discardKraus, Matrix.mul_apply, Matrix.sum_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
      map_ofNat, Matrix.cons_val_two, Matrix.cons_val_three, Fin.isValue, Matrix.one_apply] <;> norm_num [Fin.ext_iff, map_ofNat]

def discardProcessor : QuantumChannel (Fin 3 × Fin 2) (Fin 3) :=
  (finite_kraus_quantum_channel discardKraus discard_complete).choose

theorem discard_output (k : Fin 2) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    programOutput discardProcessor k M =
      ∑ q, discardKraus q * Matrix.kronecker (signalProbe k) M *
        (discardKraus q).conjTranspose := by
  exact (finite_kraus_quantum_channel discardKraus discard_complete).choose_spec _

theorem discard_entry (k : Fin 2) (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 3) :
    programOutput discardProcessor k M i j = signalProbe k i j * (M 0 0 + M 1 1) := by
  rw [discard_output]
  fin_cases i <;> fin_cases j <;>
    simp [discardKraus, Matrix.mul_apply, Matrix.sum_apply, Matrix.conjTranspose_apply,
      Matrix.kronecker_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
      map_ofNat, Matrix.cons_val_two] <;> ring

theorem observations_differ : jointObservation processor ≠ jointObservation discardProcessor := by
  intro h
  have entry := congrArg
    (fun f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] (Fin 2 → Matrix (Fin 3) (Fin 3) ℂ) =>
      f (WithLp.toLp 2 ![0,0,1]) 1 0 2) h
  change programOutput processor 1 (blochMatrix 0 (WithLp.toLp 2 ![0,0,1])) 0 2 =
    programOutput discardProcessor 1 (blochMatrix 0 (WithLp.toLp 2 ![0,0,1])) 0 2 at entry
  rw [processor_entry, discard_entry] at entry
  norm_num [blochMatrix, signalProbe, weights, Matrix.vecMulVec, Matrix.cons_val_two] at entry

/-- Abstracting the law keeps the finite-role logic independent of its telescope. -/
theorem sole_role_sensitivity
    (law : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization signature → Prop)
    (r bad : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization signature)
    (ha : r.anchor = bad.anchor) (hb : ¬ law bad) :
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Sensitivity
      ⟨signature, law⟩ r := by
  constructor
  · intro i
    refine ⟨bad, ?_, ha, hb⟩
    intro j h
    exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
  · intro i
    exact Empty.elim i

end Reg.Support.QubitChordChannels
