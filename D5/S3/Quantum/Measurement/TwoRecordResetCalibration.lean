/- GID: D5/S3/Quantum/Measurement/TwoRecordResetCalibration
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/TwoRecordResetCalibration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reference calibration of arbitrary two-record CP instruments by successor reset. -/

import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Recovery.KrausCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Measurement.TwoRecordResetCalibration

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Recovery.KrausCompletion
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- An orthogonal classical record is retained together with the quantum successor. -/
def recordEmbedding (r : Bool) : Matrix (Bool × b) b ℂ :=
  fun p j => if p.1 = r then if p.2 = j then 1 else 0 else 0

private theorem record_embedding_gram (r : Bool) :
    (recordEmbedding (b := b) r)ᴴ * recordEmbedding (b := b) r = 1 := by
  ext i j
  simp [recordEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, eq_comm]

/-- Inserting a record is a trace-preserving isometric channel. -/
def recordInsertion (r : Bool) : QuantumChannel b (Bool × b) :=
  Classical.choose (finite_kraus_quantum_channel
    (fun _ : Unit => recordEmbedding (b := b) r)
    (by simpa using record_embedding_gram (b := b) r))

private theorem record_insertion_apply (r : Bool) (X : CStarMatrix b b ℂ) :
    (recordInsertion r).toCompletelyPositiveMap X =
      CStarMatrix.ofMatrix (recordEmbedding (b := b) r * CStarMatrix.ofMatrix.symm X *
        (recordEmbedding (b := b) r)ᴴ) := by
  have h := Classical.choose_spec (finite_kraus_quantum_channel
    (fun _ : Unit => recordEmbedding (b := b) r)
    (by simpa using record_embedding_gram (b := b) r))
  simpa [recordInsertion] using congrArg CStarMatrix.ofMatrix
    (h (CStarMatrix.ofMatrix.symm X))

/-- Composition at the CP subchannel level does not impose trace preservation on a branch. -/
def cpComp {c : Type*} [Fintype c] [DecidableEq c]
    (G : CStarMatrix b b ℂ →CP CStarMatrix c c ℂ)
    (F : CStarMatrix a a ℂ →CP CStarMatrix b b ℂ) :
    CStarMatrix a a ℂ →CP CStarMatrix c c ℂ where
  toLinearMap := G.toLinearMap.comp F.toLinearMap
  map_cstarMatrix_nonneg' k X hX := by
    have h := G.map_cstarMatrix_nonneg (X.map F) (F.map_cstarMatrix_nonneg X hX)
    exact h

/-- The sum is positive on every amplification, including singular inputs. -/
def cpAdd (F G : CStarMatrix a a ℂ →CP CStarMatrix b b ℂ) :
    CStarMatrix a a ℂ →CP CStarMatrix b b ℂ where
  toLinearMap := F.toLinearMap + G.toLinearMap
  map_cstarMatrix_nonneg' k X hX := by
    have h := add_nonneg (F.map_cstarMatrix_nonneg X hX)
      (G.map_cstarMatrix_nonneg X hX)
    convert h using 1
    ext i j
    rfl

/-- Legal branches are arbitrary CP maps; only their sum must preserve trace. -/
structure TwoRecordInstrument (a b : Type*)
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] where
  noClick : CStarMatrix a a ℂ →CP CStarMatrix b b ℂ
  click : CStarMatrix a a ℂ →CP CStarMatrix b b ℂ
  trace_sum : ∀ X, Matrix.trace (noClick X) + Matrix.trace (click X) = Matrix.trace X

/-- The actual instrument, with its quantum successor in both record blocks. -/
def TwoRecordInstrument.channel (I : TwoRecordInstrument a b) :
    QuantumChannel a (Bool × b) where
  toCompletelyPositiveMap := cpAdd
    (cpComp (recordInsertion false).toCompletelyPositiveMap I.noClick)
    (cpComp (recordInsertion true).toCompletelyPositiveMap I.click)
  trace_preserving X := by
    change Matrix.trace ((recordInsertion false).toCompletelyPositiveMap (I.noClick X) +
      (recordInsertion true).toCompletelyPositiveMap (I.click X)) = _
    change Matrix.trace (CStarMatrix.ofMatrix.symm
      ((recordInsertion false).toCompletelyPositiveMap (I.noClick X)) +
      CStarMatrix.ofMatrix.symm ((recordInsertion true).toCompletelyPositiveMap (I.click X))) = _
    rw [Matrix.trace_add]
    change Matrix.trace ((recordInsertion false).toCompletelyPositiveMap (I.noClick X)) +
      Matrix.trace ((recordInsertion true).toCompletelyPositiveMap (I.click X)) = _
    rw [(recordInsertion false).trace_preserving, (recordInsertion true).trace_preserving]
    exact I.trace_sum X

/-- The joint record output has no coherence between different classical records. -/
def recordBlocks (N C : CStarMatrix b b ℂ) : CStarMatrix (Bool × b) (Bool × b) ℂ :=
  CStarMatrix.ofMatrix fun p q =>
    if p.1 = q.1 then (if p.1 then C p.2 q.2 else N p.2 q.2) else 0

private theorem inserted_entry (r : Bool) (X : CStarMatrix b b ℂ)
    (p q : Bool × b) :
    (recordEmbedding (b := b) r * CStarMatrix.ofMatrix.symm X * (recordEmbedding (b := b) r)ᴴ) p q =
      if p.1 = r ∧ q.1 = r then X p.2 q.2 else 0 := by
  by_cases hp : p.1 = r <;> by_cases hq : q.1 = r <;>
    simp [CStarMatrix, CStarMatrix.ofMatrix, recordEmbedding, Matrix.mul_apply,
      Matrix.conjTranspose_apply, hp, hq, eq_comm]; rfl

private theorem instrument_channel_apply (I : TwoRecordInstrument a b)
    (X : CStarMatrix a a ℂ) :
    I.channel.toCompletelyPositiveMap X = recordBlocks (I.noClick X) (I.click X) := by
  change (recordInsertion false).toCompletelyPositiveMap (I.noClick X) +
    (recordInsertion true).toCompletelyPositiveMap (I.click X) = _
  rw [record_insertion_apply, record_insertion_apply]
  ext ⟨r,i⟩ ⟨s,j⟩
  change (recordEmbedding (b := b) false * CStarMatrix.ofMatrix.symm (I.noClick X) *
      (recordEmbedding (b := b) false)ᴴ) (r,i) (s,j) +
    (recordEmbedding (b := b) true * CStarMatrix.ofMatrix.symm (I.click X) *
      (recordEmbedding (b := b) true)ᴴ) (r,i) (s,j) = _
  rw [inserted_entry, inserted_entry]
  cases r <;> cases s <;> simp [CStarMatrix, recordBlocks, CStarMatrix.ofMatrix] <;> rfl

/-- The full untouched record support. -/
def noClickSupport : Matrix (Bool × b) (Bool × b) ℂ :=
  Matrix.diagonal fun p => if p.1 then 0 else 1

private theorem no_click_support_projection :
    (noClickSupport (b := b))ᴴ = noClickSupport (b := b) ∧
      noClickSupport (b := b) * noClickSupport = noClickSupport := by
  constructor
  · rw [noClickSupport, Matrix.diagonal_conjTranspose]
    congr 1
    funext ⟨r,i⟩
    cases r <;> simp
  · rw [noClickSupport, Matrix.diagonal_mul_diagonal]
    congr 1
    funext ⟨r,i⟩
    cases r <;> simp

/-- One CPTP map keeps the unclicked successor and resets the clicked successor. -/
def selectiveReset (v : b) : QuantumChannel (Bool × b) (Bool × b) :=
  Classical.choose (complete_quantum_channel
    (fun _ : Unit => noClickSupport (b := b)) noClickSupport (true,v)
    no_click_support_projection.1 no_click_support_projection.2
    (by simpa [no_click_support_projection.1] using no_click_support_projection.2))

private theorem selective_reset_apply (v : b)
    (X : CStarMatrix (Bool × b) (Bool × b) ℂ) :
    (selectiveReset v).toCompletelyPositiveMap X = CStarMatrix.ofMatrix
      (noClickSupport * CStarMatrix.ofMatrix.symm X * noClickSupport +
        Matrix.trace ((1-noClickSupport) * CStarMatrix.ofMatrix.symm X) •
          Matrix.single (true,v) (true,v) 1) := by
  have h := Classical.choose_spec (complete_quantum_channel
    (fun _ : Unit => noClickSupport (b := b)) noClickSupport (true,v)
    no_click_support_projection.1 no_click_support_projection.2
    (by simpa [no_click_support_projection.1] using no_click_support_projection.2))
  simpa [selectiveReset, no_click_support_projection.1] using
    congrArg CStarMatrix.ofMatrix (h (CStarMatrix.ofMatrix.symm X))

private theorem reset_record_blocks (v : b) (N C : CStarMatrix b b ℂ) :
    (selectiveReset v).toCompletelyPositiveMap (recordBlocks N C) =
      recordBlocks N (CStarMatrix.ofMatrix (Matrix.trace C • Matrix.single v v 1)) := by
  rw [selective_reset_apply]
  have htrace : Matrix.trace
      ((1-noClickSupport) * CStarMatrix.ofMatrix.symm (recordBlocks N C)) =
      Matrix.trace C := by
    change Matrix.trace ((1-noClickSupport (b := b)) *
      (Matrix.of fun p q : Bool × b =>
        if p.1 = q.1 then (if p.1 then C p.2 q.2 else N p.2 q.2) else 0)) =
      Matrix.trace (fun i j => C i j)
    simp [Matrix.trace, Matrix.diag, noClickSupport, Matrix.sub_mul,
      Fintype.sum_prod_type, Matrix.diagonal_mul]
  rw [htrace]
  ext ⟨r,i⟩ ⟨s,j⟩
  change ((noClickSupport (b := b) * (Matrix.of fun p q : Bool × b =>
    if p.1 = q.1 then (if p.1 then C p.2 q.2 else N p.2 q.2) else 0) *
      noClickSupport (b := b) + Matrix.trace C • Matrix.single (true,v) (true,v) 1) :
      Matrix (Bool × b) (Bool × b) ℂ) (r,i) (s,j) =
    if r = s then (if r then (Matrix.trace C • Matrix.single v v 1) i j else N i j) else 0
  cases r <;> cases s <;>
    simp [noClickSupport, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.single, Matrix.smul_apply]

/-- The reset channel acts on the original full instrument, not separate copies of its branches. -/
def TwoRecordInstrument.resetChannel (I : TwoRecordInstrument a b) (v : b) :
    QuantumChannel a (Bool × b) := (selectiveReset v).comp I.channel

private theorem reset_channel_apply (I : TwoRecordInstrument a b) (v : b)
    (X : CStarMatrix a a ℂ) :
    (I.resetChannel v).toCompletelyPositiveMap X = recordBlocks (I.noClick X)
      (CStarMatrix.ofMatrix (Matrix.trace (I.click X) • Matrix.single v v 1)) := by
  change (selectiveReset v).toCompletelyPositiveMap (I.channel.toCompletelyPositiveMap X) = _
  rw [instrument_channel_apply, reset_record_blocks]


private theorem channel_kraus_gram (G : QuantumChannel a b)
    {k : Type*} [Fintype k] (K : k → Matrix b a ℂ)
    (hK : ∀ X : Matrix a a ℂ, CStarMatrix.ofMatrix.symm
      (G.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = ∑ j, K j * X * (K j)ᴴ) :
    (∑ j, (K j)ᴴ * K j) = 1 := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro X
  calc
    Matrix.trace (X * ∑ j, (K j)ᴴ * K j) =
        Matrix.trace (∑ j, K j * X * (K j)ᴴ) := by
      simp only [Matrix.mul_sum, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = Matrix.trace (((K j)ᴴ * K j) * X) := Matrix.trace_mul_comm _ _
        _ = _ := (Matrix.trace_mul_cycle (K j) X (K j)ᴴ).symm
    _ = Matrix.trace (G.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) := by
      rw [← hK X]
      rfl
    _ = Matrix.trace (X * 1) := by
      rw [G.trace_preserving]
      change Matrix.trace X = Matrix.trace (X * 1)
      rw [Matrix.mul_one]

private theorem reference_kraus_action {r k : Type*}
    [Fintype r] [DecidableEq r] [Fintype k]
    (G : QuantumChannel a b) (K : k → Matrix b a ℂ)
    (hK : ∀ X : Matrix a a ℂ, CStarMatrix.ofMatrix.symm
      (G.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = ∑ j, K j * X * (K j)ᴴ)
    (X : CStarMatrix (r × a) (r × a) ℂ) :
    referenceLinear G X = CStarMatrix.ofMatrix
      (∑ j, ((1 : Matrix r r ℂ) ⊗ₖ K j) * CStarMatrix.ofMatrix.symm X *
        ((1 : Matrix r r ℂ) ⊗ₖ K j)ᴴ) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  change G.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (fun x y => X (i,x) (j,y))) u v = _
  have h := congrArg (fun M : Matrix b b ℂ => M u v)
    (hK (fun x y => X (i,x) (j,y)))
  change G.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (fun x y => X (i,x) (j,y))) u v =
      (∑ t, ((1 : Matrix r r ℂ) ⊗ₖ K t) *
        (Matrix.of fun p q => X p q) *
        ((1 : Matrix r r ℂ) ⊗ₖ K t)ᴴ) (i,u) (j,v)
  change G.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (fun x y => X (i,x) (j,y))) u v =
      (∑ t, K t * (Matrix.of fun x y => X (i,x) (j,y)) * (K t)ᴴ) u v at h
  simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, apply_ite, mul_ite, ite_mul] using h

private theorem reference_channel_exists {r : Type*} [Fintype r] [DecidableEq r]
    (G : QuantumChannel a b) :
    ∃ lifted : QuantumChannel (r × a) (r × b),
      ∀ X, lifted.toCompletelyPositiveMap X = referenceLinear G X := by
  let K := (krausRepresentation G.toCompletelyPositiveMap).1
  have hK := (krausRepresentation G.toCompletelyPositiveMap).2
  have hgram := channel_kraus_gram G K hK
  have hnorm : (∑ j, ((1 : Matrix r r ℂ) ⊗ₖ K j)ᴴ * ((1 : Matrix r r ℂ) ⊗ₖ K j)) =
      (1 : Matrix (r × a) (r × a) ℂ) := by
    simp_rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.conjTranspose_one, Matrix.one_mul]
    calc
      _ = (1 : Matrix r r ℂ) ⊗ₖ (∑ j, (K j)ᴴ * K j) := by
        ext ⟨i,u⟩ ⟨j,v⟩
        simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]
      _ = 1 := by rw [hgram, Matrix.one_kronecker_one]
  obtain ⟨lifted, hlift⟩ := finite_kraus_quantum_channel
    (fun j => (1 : Matrix r r ℂ) ⊗ₖ K j) hnorm
  refine ⟨lifted, fun X => ?_⟩
  have h := congrArg CStarMatrix.ofMatrix (hlift (CStarMatrix.ofMatrix.symm X))
  have h' : lifted.toCompletelyPositiveMap X = CStarMatrix.ofMatrix
      (∑ j, ((1 : Matrix r r ℂ) ⊗ₖ K j) * CStarMatrix.ofMatrix.symm X *
        ((1 : Matrix r r ℂ) ⊗ₖ K j)ᴴ) := by
    simpa only [Equiv.apply_symm_apply] using h
  exact h'.trans (reference_kraus_action G K hK X).symm

private theorem reference_comp_action {r c : Type*}
    [Fintype r] [DecidableEq r] [Fintype c] [DecidableEq c]
    (G : QuantumChannel b c) (F : QuantumChannel a b)
    (X : CStarMatrix (r × a) (r × a) ℂ) :
    referenceLinear (G.comp F) X = referenceLinear G (referenceLinear F X) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  rfl

private theorem reference_error_postprocess {r : Type*} [Fintype r] [DecidableEq r]
    (post : QuantumChannel b b) (F G : QuantumChannel a b)
    (rho : DensityState (r × a)) :
    referenceError (post.comp F) (post.comp G) rho ≤ referenceError F G rho := by
  obtain ⟨lifted, hlift⟩ := reference_channel_exists (r := r) post
  have hstate (C : QuantumChannel a b) :
      referenceState (post.comp C) rho = lifted.mapState (referenceState C rho) := by
    apply Subtype.ext
    change referenceLinear (post.comp C) rho.1 =
      lifted.toCompletelyPositiveMap (referenceLinear C rho.1)
    rw [hlift, reference_comp_action]
  have h := traceDistance_contract lifted (referenceState F rho) (referenceState G rho)
  rw [← hstate F, ← hstate G] at h
  change referenceError (post.comp F) (post.comp G) rho / 2 ≤
    referenceError F G rho / 2 at h
  linarith

private theorem reference_error_le_two {r : Type*} [Fintype r] [DecidableEq r]
    (F G : QuantumChannel a b) (rho : DensityState (r × a)) :
    referenceError F G rho ≤ 2 := by
  have h := traceDistance_le_one (referenceState F rho) (referenceState G rho)
  change referenceError F G rho / 2 ≤ 1 at h
  linarith

private theorem diamond_postprocess (post : QuantumChannel b b)
    (F G : QuantumChannel a b) :
    diamondDistance (post.comp F) (post.comp G) ≤ diamondDistance F G := by
  let S := ({0} ∪ {x : ℝ | ∃ n : ℕ, ∃ rho : DensityState (Fin n × a),
    x = referenceError F G rho})
  have hb : BddAbove S := by
    refine ⟨2, ?_⟩
    rintro x (hx | ⟨n,rho,rfl⟩)
    · have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      subst x
      norm_num
    · exact reference_error_le_two F G rho
  have hzero : 0 ≤ diamondDistance F G :=
    le_csSup hb (Or.inl (Set.mem_singleton 0))
  apply csSup_le (by exact ⟨0, Or.inl (Set.mem_singleton 0)⟩)
  rintro x (hx | ⟨n,rho,rfl⟩)
  · have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    exact hzero
  · exact (reference_error_postprocess post F G rho).trans
      (le_csSup hb (Or.inr ⟨n,rho,rfl⟩))

/-- A branch acts on the successor and leaves the same finite reference untouched. -/
def referenceBranch {r : Type*} [Fintype r] [DecidableEq r]
    (F : CStarMatrix a a ℂ →CP CStarMatrix b b ℂ)
    (X : CStarMatrix (r × a) (r × a) ℂ) : CStarMatrix (r × b) (r × b) ℂ :=
  CStarMatrix.ofMatrix fun p q =>
    F (CStarMatrix.ofMatrix (fun x y => X (p.1,x) (q.1,y))) p.2 q.2

/-- The actual reference marginal of the clicked branch, including its off-diagonal entries. -/
def referenceMarginal {r : Type*} [Fintype r] [DecidableEq r]
    (F : CStarMatrix a a ℂ →CP CStarMatrix b b ℂ)
    (X : CStarMatrix (r × a) (r × a) ℂ) : Matrix r r ℂ :=
  fun i j => Matrix.trace (F (CStarMatrix.ofMatrix (fun x y => X (i,x) (j,y))))

/-- Partial trace over the successor in a joint reference matrix. -/
def successorTrace {r q : Type*} [Fintype q]
    (X : CStarMatrix (r × q) (r × q) ℂ) : Matrix r r ℂ :=
  fun i j => ∑ x, X (i,x) (j,x)

/-- Orthogonal record blocks with the reference factor outside both blocks. -/
def referenceRecordBlocks {r : Type*} [Fintype r] [DecidableEq r]
    (N C : CStarMatrix (r × b) (r × b) ℂ) :
    CStarMatrix (r × (Bool × b)) (r × (Bool × b)) ℂ :=
  CStarMatrix.ofMatrix fun p q => if p.2.1 = q.2.1 then
    (if p.2.1 then C (p.1,p.2.2) (q.1,q.2.2) else N (p.1,p.2.2) (q.1,q.2.2)) else 0

private theorem instrument_reference_action {r : Type*} [Fintype r] [DecidableEq r]
    (I : TwoRecordInstrument a b) (X : CStarMatrix (r × a) (r × a) ℂ) :
    referenceLinear I.channel X =
      referenceRecordBlocks (referenceBranch I.noClick X) (referenceBranch I.click X) := by
  ext ⟨i,s,u⟩ ⟨j,t,v⟩
  change I.channel.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (fun x y => X (i,x) (j,y))) (s,u) (t,v) = _
  rw [instrument_channel_apply]
  rfl

private theorem reset_reference_action {r : Type*} [Fintype r] [DecidableEq r]
    (I : TwoRecordInstrument a b) (v : b) (X : CStarMatrix (r × a) (r × a) ℂ) :
    referenceLinear (I.resetChannel v) X = referenceRecordBlocks (referenceBranch I.noClick X)
      (CStarMatrix.ofMatrix (referenceMarginal I.click X ⊗ₖ Matrix.single v v 1)) := by
  ext ⟨i,s,u⟩ ⟨j,t,w⟩
  change (I.resetChannel v).toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (fun x y => X (i,x) (j,y))) (s,u) (t,w) = _
  rw [reset_channel_apply]
  rfl

private theorem common_reference_completeness {r : Type*} [Fintype r] [DecidableEq r]
    (I : TwoRecordInstrument a b) (X : CStarMatrix (r × a) (r × a) ℂ) :
    referenceMarginal I.click X =
      successorTrace X - successorTrace (referenceBranch I.noClick X) := by
  ext i j
  have h := I.trace_sum (CStarMatrix.ofMatrix (fun x y => X (i,x) (j,y)))
  change Matrix.trace (I.click (CStarMatrix.ofMatrix (fun x y => X (i,x) (j,y)))) =
    Matrix.trace (CStarMatrix.ofMatrix (fun x y => X (i,x) (j,y))) -
      Matrix.trace (I.noClick (CStarMatrix.ofMatrix (fun x y => X (i,x) (j,y))))
  exact eq_sub_of_add_eq' h


/-- The original nominal qubit instrument retains both records and successors. -/
def nominalKraus (k : Fin 2) : Matrix (Bool × Fin 2) (Fin 2) ℂ :=
  if k = 0 then Matrix.single (false,0) 1 1 else Matrix.single (true,0) 0 1

private theorem nominal_kraus_complete : (∑ k, (nominalKraus k)ᴴ * nominalKraus k) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nominalKraus, Fin.sum_univ_two, Matrix.mul_apply, Matrix.single,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type]

/-- The no-click branch is Ad_|0><1| and the click branch is Ad_|0><0|. -/
def nominalChannel : QuantumChannel (Fin 2) (Bool × Fin 2) :=
  Classical.choose (finite_kraus_quantum_channel nominalKraus nominal_kraus_complete)

private theorem nominal_channel_apply (X : CStarMatrix (Fin 2) (Fin 2) ℂ) :
    nominalChannel.toCompletelyPositiveMap X = recordBlocks
      (CStarMatrix.ofMatrix (X 1 1 • Matrix.single (0 : Fin 2) 0 (1 : ℂ)))
      (CStarMatrix.ofMatrix (X 0 0 • Matrix.single (0 : Fin 2) 0 (1 : ℂ))) := by
  have h := Classical.choose_spec
    (finite_kraus_quantum_channel nominalKraus nominal_kraus_complete)
  apply CStarMatrix.ofMatrix.symm.injective
  rw [show CStarMatrix.ofMatrix.symm (nominalChannel.toCompletelyPositiveMap X) =
      ∑ k, nominalKraus k * CStarMatrix.ofMatrix.symm X * (nominalKraus k)ᴴ from
    h (CStarMatrix.ofMatrix.symm X)]
  ext ⟨r,i⟩ ⟨s,j⟩
  change (∑ k, nominalKraus k *
    (Matrix.of fun x y => X x y) *
    (nominalKraus k)ᴴ) (r,i) (s,j) =
    if r = s then
      (if r then (X 0 0 • Matrix.single (0 : Fin 2) 0 (1 : ℂ)) i j
       else (X 1 1 • Matrix.single (0 : Fin 2) 0 (1 : ℂ)) i j)
    else 0
  cases r <;> cases s <;> fin_cases i <;> fin_cases j <;>
    simp [nominalKraus, Fin.sum_univ_two, Matrix.mul_apply, Matrix.single,
      Matrix.conjTranspose_apply, Matrix.smul_apply]

private theorem quantum_channel_ext {c : Type*} [Fintype c] [DecidableEq c]
    (F G : QuantumChannel a c)
    (h : ∀ X, F.toCompletelyPositiveMap X = G.toCompletelyPositiveMap X) : F = G := by
  have hCP : F.toCompletelyPositiveMap = G.toCompletelyPositiveMap := DFunLike.ext _ _ h
  cases F
  cases G
  cases hCP
  rfl

private theorem nominal_reset_fixed :
    (selectiveReset (0 : Fin 2)).comp nominalChannel = nominalChannel := by
  apply quantum_channel_ext
  intro X
  rw [QuantumChannel.comp_apply, nominal_channel_apply, reset_record_blocks]
  simp only [show Matrix.trace
      (CStarMatrix.ofMatrix (X 0 0 • Matrix.single (0 : Fin 2) 0 (1 : ℂ))) =
    X 0 0 from by change Matrix.trace (X 0 0 • Matrix.single (0 : Fin 2) 0 (1 : ℂ)) = _
                  simp]

/-- One common record-selective channel preserves the actual no-click joint output,
resets only the clicked successor using its actual reference marginal, fixes the
original nominal instrument, and decreases calibration for every finite joint input
and for the full stabilized half-diamond distance. -/
theorem two_record_reset_calibration (I : TwoRecordInstrument (Fin 2) (Fin 2)) :
    (∀ X, I.channel.toCompletelyPositiveMap X = recordBlocks (I.noClick X) (I.click X)) ∧
    (∀ {r : Type*} [Fintype r] [DecidableEq r]
      (X : CStarMatrix (r × Fin 2) (r × Fin 2) ℂ),
      referenceLinear I.channel X =
        referenceRecordBlocks (referenceBranch I.noClick X) (referenceBranch I.click X) ∧
      referenceLinear (I.resetChannel 0) X =
        referenceRecordBlocks (referenceBranch I.noClick X)
          (CStarMatrix.ofMatrix
            (referenceMarginal I.click X ⊗ₖ Matrix.single (0 : Fin 2) 0 (1 : ℂ))) ∧
      referenceMarginal I.click X =
        successorTrace X - successorTrace (referenceBranch I.noClick X)) ∧
    (selectiveReset (0 : Fin 2)).comp nominalChannel = nominalChannel ∧
    (∀ {r : Type*} [Fintype r] [DecidableEq r] (rho : DensityState (r × Fin 2)),
      referenceError (I.resetChannel 0) nominalChannel rho / 2 ≤
        referenceError I.channel nominalChannel rho / 2) ∧
    diamondDistance (I.resetChannel 0) nominalChannel / 2 ≤
      diamondDistance I.channel nominalChannel / 2 := by
  refine ⟨instrument_channel_apply I, ?_, nominal_reset_fixed, ?_, ?_⟩
  · intro r _ _ X
    exact ⟨instrument_reference_action I X, reset_reference_action I 0 X,
      common_reference_completeness I X⟩
  · intro r _ _ rho
    have h := reference_error_postprocess (selectiveReset (0 : Fin 2))
      I.channel nominalChannel rho
    rw [nominal_reset_fixed] at h
    exact div_le_div_of_nonneg_right h (by norm_num)
  · have h := diamond_postprocess (selectiveReset (0 : Fin 2)) I.channel nominalChannel
    rw [nominal_reset_fixed] at h
    exact div_le_div_of_nonneg_right h (by norm_num)

end D5.S3.Quantum.Measurement.TwoRecordResetCalibration
