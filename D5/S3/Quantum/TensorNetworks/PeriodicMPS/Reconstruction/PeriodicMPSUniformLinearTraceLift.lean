/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLinearTraceLift
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLinearTraceLift
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectiveCoordinates]
   utility: none
   digest: Full-amplitude linear reconstruction of the weighted trace projectors across ring lengths. -/
import D5.S0.Observation.MatrixTracePowerSum
import D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectiveCoordinates
import D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformDeterminantPencil
import Mathlib.Tactic.NoncommRing

/-! A uniform linear readout of six weighted coordinates from the full
periodic binary bond-two trace tensor at length `6 + r`.

The trace coordinates are those of Czapliński–Michałek–Seynnaeve,
*Uniform matrix product states from an algebraic geometer's point of view*,
§3.3 (arXiv:1904.07563), replacing the two square traces by determinants.
The statements here recover weighted coordinates and their projector on
explicitly guarded domains. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformLinearTraceLift

open Matrix Set Filter
open PeriodicMPSParentIntersection (Bond Word wordMatrix wordMatrix_append)
open UniformMPSExpectedDimensionRefutation (traceWord)
open PeriodicMPSUniformDeterminantPencil (witnessCore)
open PeriodicMPSProjectiveCoordinates
  (mass outer projector projector_scale continuousAt_projector projective projector_mem
    isCompact_projective mass_pos)
open D5.S0.Observation.MatrixTracePowerSum (pow_add_two)
open scoped Matrix ComplexConjugate Topology

noncomputable section

abbrev Amp (r : ℕ) := Word (6 + r) → ℂ

def weighted (A : Fin 2 → Bond) : Fin 6 → ℂ :=
  ![(A 0).trace ^ 2, (A 0).trace * (A 1).trace, (A 1).trace ^ 2,
    (A 0).det, (A 1).det, (A 0 * A 1).trace]

private def commutator (A B : Bond) : Bond := A * B - B * A

/-- The scalar square of the traceless commutator. -/
def commutatorSquare (A : Fin 2 → Bond) : ℂ :=
  -(commutator (A 0) (A 1)).det

def readoutGuard (r : ℕ) (A : Fin 2 → Bond) : ℂ :=
  commutatorSquare A * (A 0 ^ r).trace

/-- The four terms of each sextic, in coefficient order `(+2,-2,-2,+2)`. -/
private def rowWords : Fin 6 → Fin 4 → Word 6 :=
  ![![![0,0,1,0,0,1], ![0,0,1,1,0,0], ![1,0,0,0,0,1], ![1,0,0,1,0,0]],
    ![![0,0,1,0,1,1], ![0,0,1,1,1,0], ![1,0,0,0,1,1], ![1,0,0,1,1,0]],
    ![![0,1,1,0,1,1], ![0,1,1,1,1,0], ![1,1,0,0,1,1], ![1,1,0,1,1,0]],
    ![![0,1,0,0,1,0], ![0,1,0,1,0,0], ![1,0,0,0,1,0], ![1,0,0,1,0,0]],
    ![![0,1,1,0,1,1], ![0,1,1,1,0,1], ![1,0,1,0,1,1], ![1,0,1,1,0,1]],
    ![![0,1,0,1,0,1], ![0,1,1,0,1,0], ![1,0,0,1,0,1], ![1,0,1,0,1,0]]]

private def rowEval {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Word 6 → V) (i : Fin 6) : V :=
  (2 : ℂ) • (f (rowWords i 0) - f (rowWords i 1) - f (rowWords i 2) + f (rowWords i 3))

private theorem rowEval_map {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (L : V →ₗ[ℂ] W) (f : Word 6 → V) (i : Fin 6) :
    rowEval (L ∘ f) i = L (rowEval f i) := by
  simp [rowEval]

/-- A fixed complex-linear map on the entire tensor, obtained by appending
`r` zeros to each of the four words in each row. -/
def linearReadout (r : ℕ) : Amp r →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun T := rowEval fun w => T (Fin.append w (fun _ : Fin r => 0))
  map_add' X Y := by
    funext i
    simp only [rowEval, Pi.add_apply, smul_eq_mul]
    ring
  map_smul' c X := by
    funext i
    simp only [rowEval, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

private def degreeSix (A B : Bond) : Fin 6 → Bond :=
  let C := commutator A B
  let DA := A * C + C * A
  let DB := B * C + C * B
  let M := A * B + B * A
  ![(2 : ℂ) • (DA * DA), (2 : ℂ) • (DA * DB), (2 : ℂ) • (DB * DB),
    (2 : ℂ) • ((C * A) * (C * A)), (2 : ℂ) • ((C * B) * (C * B)),
    C * (C * M + M * C)]

private theorem rowEval_wordMatrix (A : Fin 2 → Bond) (i : Fin 6) :
    rowEval (wordMatrix A) i = degreeSix (A 0) (A 1) i := by
  fin_cases i <;>
    simp only [rowEval, rowWords, degreeSix, commutator, wordMatrix, List.ofFn_succ,
      List.ofFn_zero, List.prod_cons, List.prod_nil, Matrix.cons_val_zero',
      Matrix.cons_val_succ', mul_one, two_smul] <;>
    noncomm_ring <;> abel

private theorem square_of_trace_zero (X : Bond) (hX : X.trace = 0) :
    X * X = (-X.det) • (1 : Bond) := by
  simpa [hX, pow_two, neg_smul] using pow_add_two X 0

private theorem anti_commutator_left (A B : Bond) :
    A * commutator A B + commutator A B * A = A.trace • commutator A B := by
  have h : A * A = A.trace • A - A.det • (1 : Bond) := by
    simpa [pow_two] using pow_add_two A 0
  calc
    _ = (A * A) * B - B * (A * A) := by unfold commutator; noncomm_ring
    _ = _ := by
      rw [h]
      simp [commutator, sub_mul, mul_sub, smul_sub]

private theorem anti_commutator_right (A B : Bond) :
    B * commutator A B + commutator A B * B = B.trace • commutator A B := by
  have h : commutator A B = -commutator B A := by unfold commutator; abel
  rw [h, mul_neg, neg_mul, ← neg_add, anti_commutator_left, smul_neg]

private theorem anti_commutator_mixed (A B : Bond) :
    commutator A B * (A * B + B * A) + (A * B + B * A) * commutator A B =
      (2 * (A * B).trace) • commutator A B := by
  have square (X : Bond) : X * X = X.trace • X - X.det • (1 : Bond) := by
    simpa [pow_two] using pow_add_two X 0
  calc
    _ = (2 : ℂ) • ((A * B) * (A * B) - (B * A) * (B * A)) := by
      unfold commutator
      rw [two_smul]
      noncomm_ring
    _ = _ := by
      rw [square (A * B), square (B * A), Matrix.trace_mul_comm B A,
        Matrix.det_mul A B, Matrix.det_mul B A, mul_comm B.det A.det]
      simp [commutator, smul_sub, mul_smul, sub_sub_sub_cancel_right]

private theorem trace_commutator_mul_left (A B : Bond) :
    (commutator A B * A).trace = 0 := by
  rw [commutator, sub_mul, Matrix.trace_sub, Matrix.trace_mul_comm (B * A) A,
    mul_assoc, sub_self]

private theorem trace_commutator_mul_right (A B : Bond) :
    (commutator A B * B).trace = 0 := by
  rw [commutator, sub_mul, Matrix.trace_sub, mul_assoc B A B,
    Matrix.trace_mul_comm B (A * B), sub_self]

private theorem degreeSix_eq (A : Fin 2 → Bond) (i : Fin 6) :
    degreeSix (A 0) (A 1) i = (2 * commutatorSquare A * weighted A i) • (1 : Bond) := by
  let X := A 0
  let Y := A 1
  let C := commutator X Y
  have hC : C * C = commutatorSquare A • (1 : Bond) :=
    square_of_trace_zero C (by simp [C, commutator, Matrix.trace_sub, Matrix.trace_mul_comm X Y])
  have hX : (C * X) * (C * X) = (commutatorSquare A * X.det) • (1 : Bond) := by
    rw [square_of_trace_zero _ (trace_commutator_mul_left X Y), Matrix.det_mul, ← neg_mul]
    rfl
  have hY : (C * Y) * (C * Y) = (commutatorSquare A * Y.det) • (1 : Bond) := by
    rw [square_of_trace_zero _ (trace_commutator_mul_right X Y), Matrix.det_mul, ← neg_mul]
    rfl
  have hLeft := anti_commutator_left X Y
  have hRight := anti_commutator_right X Y
  have hMixed := anti_commutator_mixed X Y
  dsimp only [X, Y, C] at hC hX hY hLeft hRight hMixed
  fin_cases i <;>
    simp only [degreeSix, weighted, Matrix.cons_val_zero', Matrix.cons_val_succ', hLeft,
      hRight, hMixed, hX, hY, Matrix.smul_mul, Matrix.mul_smul, hC, smul_smul] <;>
    congr 1 <;> ring

private theorem wordMatrix_zero (A : Fin 2 → Bond) (r : ℕ) :
    wordMatrix A (fun _ : Fin r => 0) = A 0 ^ r := by
  simp only [wordMatrix, List.ofFn_const, List.prod_replicate]

/-- The same four word coefficients per row work at every length, including length six.
The identity holds for all cores, including on the zero locus of the common scalar. -/
theorem linearReadout_traceWord (r : ℕ) (A : Fin 2 → Bond) :
    linearReadout r (traceWord 2 2 (6 + r) A) = (2 * readoutGuard r A) • weighted A := by
  let L : Bond →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap (α := ℂ) (R := ℂ) (n := Fin 2)).comp
      (LinearMap.mulRight ℂ (A 0 ^ r))
  have h (w : Word 6) :
      traceWord 2 2 (6 + r) A (Fin.append w (fun _ : Fin r => 0)) = L (wordMatrix A w) := by
    change (wordMatrix A (Fin.append w (fun _ : Fin r => 0))).trace = _
    rw [wordMatrix_append, wordMatrix_zero]
    rfl
  funext i
  change rowEval (fun w => traceWord 2 2 (6 + r) A (Fin.append w (fun _ : Fin r => 0))) i = _
  simp_rw [h]
  rw [show (fun w => L (wordMatrix A w)) = L ∘ wordMatrix A from rfl,
    rowEval_map, rowEval_wordMatrix, degreeSix_eq]
  change (((2 * commutatorSquare A * weighted A i) • (1 : Bond)) * A 0 ^ r).trace = _
  simp only [Matrix.smul_mul, one_mul, Matrix.trace_smul, Pi.smul_apply, smul_eq_mul, readoutGuard]
  ring

/-- Dividing by the common scalar recovers the six weighted coordinates
on the guarded locus of the literal parametrization. -/
theorem weighted_eq_of_readoutGuard (r : ℕ) (A : Fin 2 → Bond) (h : readoutGuard r A ≠ 0) :
    weighted A = (2 * readoutGuard r A)⁻¹ • linearReadout r (traceWord 2 2 (6 + r) A) := by
  rw [linearReadout_traceWord, smul_smul, inv_mul_cancel₀ (mul_ne_zero (by norm_num) h), one_smul]

/-- The all-zero tail has trace two at length zero and trace one thereafter
for the repository's hard-core witness. -/
theorem witnessCore_trace_zero_pow (r : ℕ) :
    (witnessCore 0 ^ r).trace = if r = 0 then 2 else 1 := by
  by_cases h : r = 0
  · subst r
    norm_num [Matrix.trace_fin_two]
  rw [ite_eq_right h]
  have hr : 0 < r := Nat.pos_of_ne_zero h
  have hid : witnessCore 0 * witnessCore 0 = witnessCore 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [witnessCore, Matrix.mul_apply, Fin.sum_univ_two]
  have hp (m : ℕ) : witnessCore 0 ^ (m + 1) = witnessCore 0 := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, hid]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [hp]
  norm_num [witnessCore, Matrix.trace_fin_two]

/-- The hard-core witness satisfies the uniform guard at every length. -/
theorem readoutGuard_witnessCore (r : ℕ) :
    readoutGuard r witnessCore = if r = 0 then 2 else 1 := by
  have hc : commutatorSquare witnessCore = 1 := by
    norm_num [commutatorSquare, commutator, witnessCore, Matrix.det_fin_two,
      Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  rw [readoutGuard, hc, one_mul, witnessCore_trace_zero_pow]

abbrev Ambient (r : ℕ) := Matrix (Fin 6) (Fin 6) ℂ × Matrix (Word (6 + r)) (Word (6 + r)) ℂ

/-- The joint projector of the weighted coordinates and the full trace tensor. -/
def projectorGraph (r : ℕ) (A : Fin 2 → Bond) : Ambient r :=
  (projector (weighted A), projector (traceWord 2 2 (6 + r) A))

/-- The closure of the joint projectors with both representatives nonzero. -/
def projectorSource (r : ℕ) : Set (Ambient r) :=
  closure (projectorGraph r '' {A | weighted A ≠ 0 ∧ traceWord 2 2 (6 + r) A ≠ 0})

theorem isCompact_projectorSource (r : ℕ) : IsCompact (projectorSource r) := by
  have hk : IsCompact (projective (ι := Fin 6) ×ˢ projective (ι := Word (6 + r))) :=
    isCompact_projective.prod isCompact_projective
  refine hk.of_isClosed_subset isClosed_closure (closure_minimal ?_ hk.isClosed)
  rintro _ ⟨A, ⟨hw, hT⟩, rfl⟩
  exact ⟨projector_mem _ hw, projector_mem _ hT⟩

/-- Apply the amplitude readout to a column of a full tensor projector. -/
def readColumn (r : ℕ) (j : Word (6 + r))
    (P : Matrix (Word (6 + r)) (Word (6 + r)) ℂ) : Fin 6 → ℂ :=
  linearReadout r (fun i => P i j)

private theorem continuous_readColumn (r : ℕ) (j : Word (6 + r)) :
    Continuous (readColumn r j) := by
  apply continuous_pi
  intro i
  change Continuous (fun P : Matrix (Word (6 + r)) (Word (6 + r)) ℂ =>
    rowEval (fun w => P (Fin.append w (fun _ : Fin r => 0)) j) i)
  unfold rowEval
  fun_prop

theorem readColumn_projectorGraph (r : ℕ) (j : Word (6 + r)) (A : Fin 2 → Bond) :
    readColumn r j (projectorGraph r A).2 =
      ((((mass (traceWord 2 2 (6 + r) A))⁻¹ : ℝ) : ℂ) *
        conj (traceWord 2 2 (6 + r) A j) * (2 * readoutGuard r A)) • weighted A := by
  let T := traceWord 2 2 (6 + r) A
  let c : ℂ := ((mass T)⁻¹ : ℝ) * conj (T j)
  have h : (fun i => projector T i j) = c • T := by
    funext i
    simp only [projector, outer, Matrix.smul_apply, Complex.real_smul, Pi.smul_apply, smul_eq_mul, c]
    ring
  change linearReadout r (fun i => projector T i j) = _
  rw [h, map_smul, linearReadout_traceWord, smul_smul]

/-- A nonzero column readout recovers the weighted projector even at a
limit of the joint projector graph. -/
theorem lift_eq_of_readColumn_ne_zero {r : ℕ} {x : Ambient r}
    (hx : x ∈ projectorSource r) (j : Word (6 + r)) (hj : readColumn r j x.2 ≠ 0) :
    x.1 = projector (readColumn r j x.2) := by
  let S := projectorGraph r '' {A | weighted A ≠ 0 ∧ traceWord 2 2 (6 + r) A ≠ 0}
  have hS : NeBot (𝓝[S] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hcol : Tendsto (fun y : Ambient r => readColumn r j y.2)
      (𝓝[S] x) (𝓝 (readColumn r j x.2)) :=
    ((continuous_readColumn r j).comp continuous_snd).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hdecoded := (continuousAt_projector hj).tendsto.comp hcol
  have hfst : Tendsto (fun y : Ambient r => projector (readColumn r j y.2))
      (𝓝[S] x) (𝓝 x.1) := by
    apply (continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [hcol.eventually_ne hj, self_mem_nhdsWithin] with y hn hy
    obtain ⟨A, _, rfl⟩ := hy
    rw [readColumn_projectorGraph] at hn ⊢
    exact (projector_scale _ (fun hc => hn (by rw [hc, zero_smul]))).symm
  exact tendsto_nhds_unique hfst hdecoded

/-- The all-zero projector column certifies the lift guard on the hard-core witness. -/
theorem readColumn_witnessCore_ne_zero (r : ℕ) :
    readColumn r (fun _ => 0) (projectorGraph r witnessCore).2 ≠ 0 := by
  let T := traceWord 2 2 (6 + r) witnessCore
  have hT : T (fun _ => 0) = 1 := by
    change (wordMatrix witnessCore (fun _ : Fin (6 + r) => 0)).trace = 1
    rw [wordMatrix_zero, witnessCore_trace_zero_pow, ite_eq_right (by omega)]
  have hmass := mass_pos T (fun h => by simp [h] at hT)
  have hguard : readoutGuard r witnessCore ≠ 0 := by
    rw [readoutGuard_witnessCore]
    split <;> norm_num
  have hw : weighted witnessCore 0 = 1 := by
    norm_num [weighted, witnessCore, Matrix.trace_fin_two]
  intro hz
  have hz0 := congrFun hz (0 : Fin 6)
  rw [readColumn_projectorGraph] at hz0
  change ((((mass T)⁻¹ : ℝ) : ℂ) * conj (T (fun _ => 0)) * (2 * readoutGuard r witnessCore)) *
    weighted witnessCore 0 = 0 at hz0
  rw [hT, map_one, mul_one, hw, mul_one] at hz0
  exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero hmass.ne'))
    (mul_ne_zero (by norm_num) hguard)) hz0

#print axioms linearReadout_traceWord
#print axioms weighted_eq_of_readoutGuard
#print axioms readoutGuard_witnessCore
#print axioms isCompact_projectorSource
#print axioms lift_eq_of_readColumn_ne_zero
#print axioms readColumn_witnessCore_ne_zero

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformLinearTraceLift
