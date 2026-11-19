/- GID: D5/S3/Quantum/Measurement/Auric/UnitaryTransport
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/UnitaryTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Input and flag-conditioned output unitaries preserve the protocol distance. -/

import D5.S3.Quantum.Measurement.Auric.DiamondClosure
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability

/-! # Input and flag-conditioned output unitaries preserve the protocol distance -/

namespace D5.S3.Quantum.Measurement.Auric.UnitaryTransport

open _root_.Matrix D5.S3.Quantum.Foundation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Measurement.Auric.ExactDistance
open D5.S3.Quantum.Measurement.Auric.DiamondClosure
open D5.S3.Quantum.Measurement.Auric.ProjectiveTree
open D5.S3.Quantum.Measurement.Auric.ScoreReadout (protocolMap)
open D5.S3.Quantum.Measurement.Auric.SimulatorUpper
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_isometry)
open scoped Kronecker

noncomputable section

abbrev RegisterUnitary := Matrix.unitaryGroup Level ℂ
abbrev FeedbackUnitary := Flag → RegisterUnitary

private def feedbackMatrix (v : FeedbackUnitary) : Matrix (Flag × Level) (Flag × Level) ℂ :=
  (Matrix.blockDiagonal fun j => (v j).val).submatrix
    (Equiv.prodComm Flag Level) (Equiv.prodComm Flag Level)

private theorem feedbackMatrix_star (v : FeedbackUnitary) :
    feedbackMatrix (fun j => star (v j)) = (feedbackMatrix v)ᴴ := by
  simp [feedbackMatrix, Matrix.conjTranspose_submatrix, Matrix.blockDiagonal_conjTranspose,
    Matrix.star_eq_conjTranspose]

private theorem feedbackMatrix_unitary (v : FeedbackUnitary) :
    (feedbackMatrix v)ᴴ * feedbackMatrix v = 1 := by
  rw [← feedbackMatrix_star]
  unfold feedbackMatrix
  rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
  have h : (fun j => ((star (v j)).val * (v j).val)) = 1 := by
    funext j
    exact Matrix.mem_unitaryGroup_iff'.1 (v j).prop
  rw [h, Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]

private theorem feedback_flag (v : FeedbackUnitary) (j : Flag) (K : Matrix Level Level ℂ) :
    feedbackMatrix v * flagKraus j K = flagKraus j ((v j).val * K) := by
  ext ⟨f, o⟩ i
  by_cases h : f = j
  · subst f
    simp [feedbackMatrix, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.blockDiagonal_apply,
      flagKraus, ite_mul, mul_ite, eq_comm]
  · simp [feedbackMatrix, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.blockDiagonal_apply,
      flagKraus, ite_mul, mul_ite, h]

private theorem flag_mul (j : Flag) (K U : Matrix Level Level ℂ) :
    flagKraus j (K * U) = flagKraus j K * U := by
  ext ⟨f, o⟩ i
  by_cases h : f = j <;> simp [flagKraus, Matrix.mul_apply, h]

private def boundaryTree (u : RegisterUnitary) (v : FeedbackUnitary) :
    Protocol Level → Protocol Level
  | .leaf j w => .leaf j (v j * w * u)
  | .branch w k E p => .branch (w * u) k E (fun i => boundaryTree 1 v (p i))

private def boundaryTerminal (u : RegisterUnitary) (v : FeedbackUnitary) :
    (p : Protocol Level) → Terminal (boundaryTree u v p) ≃ Terminal p
  | .leaf _ _ => Equiv.refl Unit
  | .branch _ _ _ p => Equiv.sigmaCongrRight fun i => boundaryTerminal 1 v (p i)

private theorem boundaryTerminal_kraus (u : RegisterUnitary) (v : FeedbackUnitary)
    (p : Protocol Level) (h : Terminal (boundaryTree u v p)) :
    let old := boundaryTerminal u v p h
    flag (boundaryTree u v p) h = flag p old ∧
      kraus (boundaryTree u v p) h = (v (flag p old)).val * kraus p old * u.val := by
  induction p generalizing u with
  | leaf j w => exact ⟨rfl, rfl⟩
  | branch w k E p ih =>
    rcases h with ⟨i, h⟩
    obtain ⟨hflag, hK⟩ := ih i 1 h
    change flag (boundaryTree 1 v (p i)) h = flag (p i) (boundaryTerminal 1 v (p i) h) ∧ _
    refine ⟨hflag, ?_⟩
    change kraus (boundaryTree 1 v (p i)) h * (E.proj i * (w.val * u.val)) =
      (v (flag (p i) (boundaryTerminal 1 v (p i) h))).val *
        (kraus (p i) (boundaryTerminal 1 v (p i) h) * (E.proj i * w.val)) * u.val
    rw [hK]
    simp [Matrix.mul_assoc]

/-- Preprocess by a register unitary and postprocess by the unitary selected by the flag. -/
def transport (u : RegisterUnitary) (v : FeedbackUnitary) : RecordedMap →ₗ[ℂ] RecordedMap where
  toFun F := (MatrixMap.conj (feedbackMatrix v)).comp (F.comp (MatrixMap.conj u.val))
  map_add' F G := by ext X i j; simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' z F := by ext X i j; simp

private theorem transport_protocol (u : RegisterUnitary) (v : FeedbackUnitary)
    (p : Protocol Level) : transport u v (protocolMap p) = protocolMap (boundaryTree u v p) := by
  classical
  apply LinearMap.ext
  intro X
  let p' := boundaryTree u v p
  let e := boundaryTerminal u v p
  let K (h : Terminal p) := flagKraus (flag p h) (kraus p h)
  let K' (h : Terminal p') := flagKraus (flag p' h) (kraus p' h)
  have hK (h : Terminal p') : K' h = feedbackMatrix v * K (e h) * u.val := by
    have h := boundaryTerminal_kraus u v p h
    simp only [K', K, p', e, h.1, h.2, flag_mul, feedback_flag]
  change feedbackMatrix v * (protocolMap p (u.val * X * u.valᴴ)) * (feedbackMatrix v)ᴴ =
    protocolMap p' X
  simp only [protocolMap, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  change feedbackMatrix v * (∑ h : Terminal p, K h * (u.val * X * u.valᴴ) * (K h)ᴴ) *
    (feedbackMatrix v)ᴴ = ∑ h : Terminal p', K' h * X * (K' h)ᴴ
  rw [Matrix.mul_sum, Matrix.sum_mul, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro h _
  rw [hK]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem transport_finite (u : RegisterUnitary) (v : FeedbackUnitary) {F : RecordedMap}
    (hF : FiniteProtocolMixture F) : FiniteProtocolMixture (transport u v F) := by
  obtain ⟨m, p, w, hw, hw1, rfl⟩ := hF
  refine ⟨m, fun i => boundaryTree u v (p i), w, hw, hw1, ?_⟩
  simp only [map_sum, map_smul, transport_protocol]

theorem transport_flagged (u : RegisterUnitary) (v : FeedbackUnitary)
    (K : Flag → Matrix Level Level ℂ) :
    transport u v (flagged K) = flagged (fun j => (v j).val * K j * u.val) := by
  apply LinearMap.ext
  intro X
  change feedbackMatrix v * (∑ j, flagKraus j (K j) * (u.val * X * u.valᴴ) *
    (flagKraus j (K j))ᴴ) * (feedbackMatrix v)ᴴ =
    ∑ j, flagKraus j ((v j).val * K j * u.val) * X *
      (flagKraus j ((v j).val * K j * u.val))ᴴ
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [flag_mul, ← feedback_flag]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem reference_entry {a b R : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [Fintype R] [DecidableEq R] (F : MatrixMap a b ℂ)
    (X : Matrix (a × R) (a × R) ℂ) (i j : b) (s t : R) :
    MatrixMap.kron F (LinearMap.id : MatrixMap R R ℂ) X (i, s) (j, t) =
      F (fun u v => X (u, s) (v, t)) i j := by
  classical
  rw [MatrixMap.kron_def]
  calc
    _ = ∑ u, ∑ v, X (u, s) (v, t) * F (Matrix.single u v 1) i j := by
      congr! 2 with u v
      simp [Matrix.single, ite_and, Finset.sum_ite_irrel, mul_comm]
    _ = _ := by
      have h := congrArg (fun A : MatrixMap a b ℂ =>
        A (fun u v => X (u, s) (v, t)) i j) (MatrixMap.choi_map_inv F)
      exact h

private theorem conjugation_entry {a R : Type*} [Fintype a] [Fintype R] [DecidableEq R]
    (U : Matrix a a ℂ) (X : Matrix (a × R) (a × R) ℂ) (i j : a) (s t : R) :
    ((U ⊗ₖ (1 : Matrix R R ℂ)) * X * (U ⊗ₖ (1 : Matrix R R ℂ))ᴴ) (i, s) (j, t) =
      (U * Matrix.of (fun u v => X (u, s) (v, t)) * Uᴴ) i j := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply,
    mul_ite, ite_mul]

private theorem transport_reference {R : Type} [Fintype R] [DecidableEq R]
    (u : RegisterUnitary) (v : FeedbackUnitary) (F : RecordedMap)
    (X : Matrix (Level × R) (Level × R) ℂ) :
    let U := u.val ⊗ₖ (1 : Matrix R R ℂ)
    let V := feedbackMatrix v ⊗ₖ (1 : Matrix R R ℂ)
    MatrixMap.kron (transport u v F) (LinearMap.id : MatrixMap R R ℂ) X =
      V * (MatrixMap.kron F (LinearMap.id : MatrixMap R R ℂ) (U * X * Uᴴ)) * Vᴴ := by
  dsimp only
  ext ⟨i, s⟩ ⟨j, t⟩
  rw [reference_entry, conjugation_entry]
  have hblock : (fun u' v' =>
      (MatrixMap.kron F (LinearMap.id : MatrixMap R R ℂ)
        ((u.val ⊗ₖ (1 : Matrix R R ℂ)) * X * (u.val ⊗ₖ (1 : Matrix R R ℂ))ᴴ))
          (u', s) (v', t)) =
      F (u.val * Matrix.of (fun x y => X (x, s) (y, t)) * u.valᴴ) := by
    ext x y
    exact (reference_entry _ _ x y s t).trans (congrArg (fun Y => F Y x y)
      (by ext a b; exact conjugation_entry _ _ a b s t))
  rw [hblock]
  rfl

/-- Both unitary boundary operations preserve the uniform bound over all references. -/
theorem transport_bound (u : RegisterUnitary) (v : FeedbackUnitary) {F : RecordedMap} {c : ℝ}
    (hc : DiamondBound F c) : DiamondBound (transport u v F) c := by
  intro R _ _ X
  let U := u.val ⊗ₖ (1 : Matrix R R ℂ)
  let V := feedbackMatrix v ⊗ₖ (1 : Matrix R R ℂ)
  have hU : Uᴴ * U = 1 := by
    have hu : u.valᴴ * u.val = 1 := Matrix.mem_unitaryGroup_iff'.1 u.prop
    dsimp only [U]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      hu, Matrix.one_mul, Matrix.one_kronecker_one]
  have hV : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      feedbackMatrix_unitary, Matrix.one_mul, Matrix.one_kronecker_one]
  rw [transport_reference, traceNorm_isometry V hV]
  rw [← traceNorm_isometry U hU X]
  exact hc R _

private theorem transport_inverse (u : RegisterUnitary) (v : FeedbackUnitary) (F : RecordedMap) :
    transport (star u) (fun j => star (v j)) (transport u v F) = F := by
  apply LinearMap.ext
  intro X
  have hu : u.val * u.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 u.prop
  have hv := feedbackMatrix_unitary v
  have hstar : (star u).val = u.valᴴ := Matrix.star_eq_conjTranspose u.val
  change feedbackMatrix (fun j => star (v j)) * (feedbackMatrix v *
    F (u.val * ((star u).val * X * (star u).valᴴ) * u.valᴴ) * (feedbackMatrix v)ᴴ) *
    (feedbackMatrix (fun j => star (v j)))ᴴ = F X
  rw [feedbackMatrix_star v, hstar, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  rw [show u.val * (u.valᴴ * X * u.val) * u.valᴴ = X by
    calc
      _ = (u.val * u.valᴴ) * X * (u.val * u.valᴴ) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hu, Matrix.one_mul, Matrix.mul_one]]
  calc
    _ = ((feedbackMatrix v)ᴴ * feedbackMatrix v) * F X *
        ((feedbackMatrix v)ᴴ * feedbackMatrix v) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hv, Matrix.one_mul, Matrix.mul_one]

theorem transport_closure (u : RegisterUnitary) (v : FeedbackUnitary) {F : RecordedMap}
    (hF : ProtocolClosure F) : ProtocolClosure (transport u v F) := by
  intro ε hε
  obtain ⟨G, hG, hdist⟩ := hF ε hε
  refine ⟨transport u v G, transport_finite u v hG, ?_⟩
  rw [← map_sub]
  exact transport_bound u v hdist

/-- The optimized diamond error is invariant under the allowed unitary boundary operations. -/
theorem transport_distance_set (u : RegisterUnitary) (v : FeedbackUnitary) (A : RecordedMap) :
    {d : ℝ | ∃ F, ProtocolClosure F ∧ DiamondBound (transport u v A - F) d} =
      {d : ℝ | ∃ F, ProtocolClosure F ∧ DiamondBound (A - F) d} := by
  ext d
  constructor
  · rintro ⟨F, hF, hdist⟩
    let inv := transport (star u) (fun j => star (v j))
    refine ⟨inv F, transport_closure _ _ hF, ?_⟩
    have h := transport_bound (star u) (fun j => star (v j)) hdist
    rwa [map_sub, transport_inverse] at h
  · rintro ⟨F, hF, hdist⟩
    refine ⟨transport u v F, transport_closure u v hF, ?_⟩
    rw [← map_sub]
    exact transport_bound u v hdist

end

end D5.S3.Quantum.Measurement.Auric.UnitaryTransport
