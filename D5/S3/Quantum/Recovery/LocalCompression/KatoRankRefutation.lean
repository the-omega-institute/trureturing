/- GID: D5/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation.claim; result=D5/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation.result; claim=D5/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation.claim
   digest: Faithful classical states refute Kato's unrestricted Choi marginal-rank proposal. -/

import D5.S3.Quantum.Recovery.DiagonalRecordCapacity
import D5.S3.Quantum.ProcessReconstruction.LiuWildChoiObstruction
import D5.S3.Quantum.Measurement.Auric.CoordinatePinching

/-!
Kato, *Exact and Local Compression of Quantum Bipartite States*,
arXiv:2309.07434v2, Eqs. (17), (19), (22), (61), and (62).
The normalized Choi state in Eq. (17) is obtained by the actual CPTP
dephasing channel for this family. Equation (61) optimizes over unitaries
on that Choi state's two factors. Equation (19) uses a purification.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Recovery.LocalCompression.KatoRankRefutation

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance (referenceState)
open D5.S3.Quantum.Recovery.DiagonalRecordCapacity
open D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation (diagonalState)
open D5.S3.Quantum.Measurement.Auric.CoordinatePinching
  (coordinatePVM pinchingChannel pinchingChannel_apply)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight trace_partialTraceRight)
open UnitaryReconstruction.LiuWildChoiObstruction
  (pairMatrix normalizedChoi normalizedChoi_entry)
open UnitaryReconstruction (referenceMatrix referenceMatrix_apply)

variable {n : ℕ}

private theorem uniform_pos [NeZero n] : 0 < (n : ℝ)⁻¹ :=
  inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n)))

private theorem sum_uniform [NeZero n] : (∑ _ : Fin n, (n : ℝ)⁻¹) = 1 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp [hn]

/-- Both conditional laws are the same symmetric noisy copy law. -/
def conditional (t : ℝ) (a b : Fin n) : ℝ :=
  (if a = b then t else 0) + (1 - t) * (n : ℝ)⁻¹

private theorem conditional_pos [NeZero n] {t : ℝ} (ht : 0 < t) (ht' : t < 1)
    (a b : Fin n) : 0 < conditional t a b := by
  have h := mul_pos (sub_pos.mpr ht') (uniform_pos (n := n))
  by_cases hab : a = b <;> simp [conditional, hab] <;> linarith

private theorem conditional_sum [NeZero n] (t : ℝ) (a : Fin n) :
    ∑ b, conditional t a b = 1 := by
  classical
  simp only [conditional, Finset.sum_add_distrib, ← Finset.mul_sum, sum_uniform, mul_one]
  rw [show (∑ b : Fin n, if a = b then t else 0) = t by
    simp]
  ring

private theorem conditional_sum_left [NeZero n] (t : ℝ) (b : Fin n) :
    ∑ a, conditional t a b = 1 := by
  simpa only [conditional, eq_comm] using conditional_sum t b

/-- The experiment on B with the uniform marginal as reference and one
comparison for each A label. -/
def experiment [NeZero n] (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    DiagonalExperiment (Fin n) (Fin n) where
  reference := fun _ => (n : ℝ)⁻¹
  comparison := conditional t
  reference_nonneg := fun _ => by positivity
  reference_sum := sum_uniform
  comparison_nonneg := fun i b => (conditional_pos ht ht' i b).le
  comparison_sum := conditional_sum t
  comparison_zero := fun _ _ h => (inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne n)) h).elim

/-- Joint probability in the A-first product basis. -/
def weights (t : ℝ) (p : Fin n × Fin n) : ℝ :=
  (n : ℝ)⁻¹ * conditional t p.1 p.2

private theorem weights_pos [NeZero n] {t : ℝ} (ht : 0 < t) (ht' : t < 1)
    (p : Fin n × Fin n) : 0 < weights t p :=
  mul_pos uniform_pos (conditional_pos ht ht' _ _)

/-- The actual faithful diagonal bipartite density state. -/
def source [NeZero n] (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    DensityState (Fin n × Fin n) :=
  diagonalState (weights t) (fun p => (weights_pos ht ht' p).le) (by
    rw [Fintype.sum_prod_type]
    simp only [weights, ← Finset.mul_sum, conditional_sum, mul_one, sum_uniform])

/-- Kato's local recovery condition, applying the encoded-decoded channel on B
while leaving A untouched. -/
def recoveryDimensions [NeZero n] (t : ℝ) (ht : 0 < t) (ht' : t < 1) : Set ℕ :=
  {d | ∃ encoder : QuantumChannel (Fin n) (Fin d),
    ∃ decoder : QuantumChannel (Fin d) (Fin n),
      referenceState (decoder.comp encoder) (source t ht ht') = source t ht ht'}

private theorem fixes_source_iff [NeZero n] {t : ℝ} (ht : 0 < t) (ht' : t < 1)
    (T : QuantumChannel (Fin n) (Fin n)) :
    referenceState T (source t ht ht') = source t ht ht' ↔
      ∀ a, T.mapState ((experiment t ht ht').comparisonState a) =
        (experiment t ht ht').comparisonState a := by
  let D : DiagonalExperiment (Fin n) (Fin n) := experiment t ht ht'
  let ρ : DensityState (Fin n × Fin n) := source t ht ht'
  let c : ℂ := (n : ℂ)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have hblock (a a' : Fin n) :
      (fun b b' => pairMatrix ρ (a,b) (a',b')) =
        if a = a' then c • pairMatrix (D.comparisonState a) else 0 := by
    ext b b'
    by_cases ha : a = a'
    · subst a'
      by_cases hb : b = b' <;>
        simp [ρ, D, c, source, weights, DiagonalExperiment.comparisonState, experiment,
          diagonalState, Prod.mk.injEq, hb]
    · simp [ρ, source, diagonalState, Prod.mk.injEq, ha]
  have hentry (a a' b b' : Fin n) :
      pairMatrix (referenceState T ρ) (a,b) (a',b') =
        T.toCompletelyPositiveMap (CStarMatrix.ofMatrix
          (if a = a' then c • pairMatrix (D.comparisonState a) else 0)) b b' := by
    change referenceMatrix T (pairMatrix ρ) (a,b) (a',b') = _
    rw [referenceMatrix_apply, hblock]
  constructor
  · intro h a
    apply Subtype.ext
    ext b b'
    have he := congrArg (fun σ : DensityState (Fin n × Fin n) =>
      pairMatrix σ (a,b) (a,b')) h
    rw [hentry] at he
    change _ = pairMatrix ρ (a,b) (a,b') at he
    have hr := congrFun (congrFun (hblock a a) b) b'
    rw [hr] at he
    simp only [ite_eq_left (show a = a from rfl)] at he
    change (T.toCompletelyPositiveMap (c • (D.comparisonState a).val)) b b' = _ at he
    rw [map_smul] at he
    exact mul_left_cancel₀ hc he
  · intro h
    apply Subtype.ext
    ext ⟨a,b⟩ ⟨a',b'⟩
    change pairMatrix (referenceState T ρ) (a,b) (a',b') = pairMatrix ρ (a,b) (a',b')
    rw [hentry]
    have hr := congrFun (congrFun (hblock a a') b) b'
    change pairMatrix ρ (a,b) (a',b') = _ at hr
    rw [hr]
    by_cases ha : a = a'
    · simp only [ite_eq_left ha]
      change (T.toCompletelyPositiveMap (c • (D.comparisonState a).val)) b b' = _
      rw [map_smul]
      exact congrArg (fun σ : DensityState (Fin n) => c * σ.val b b') (h a)
    · simp [ha]

private theorem fixes_reference [NeZero n] {t : ℝ} (ht : 0 < t) (ht' : t < 1)
    (T : QuantumChannel (Fin n) (Fin n))
    (h : ∀ a, T.mapState ((experiment t ht ht').comparisonState a) =
      (experiment t ht ht').comparisonState a) :
    T.mapState (experiment t ht ht').referenceState = (experiment t ht ht').referenceState := by
  let D : DiagonalExperiment (Fin n) (Fin n) := experiment t ht ht'
  have hmix : D.referenceState.val = (n : ℂ)⁻¹ • ∑ a, (D.comparisonState a).val := by
    change diagonal (fun _ : Fin n => (((n : ℝ)⁻¹ : ℝ) : ℂ)) =
      (n : ℂ)⁻¹ • ∑ a : Fin n, diagonal (fun b : Fin n => (conditional t a b : ℂ))
    ext b b'
    by_cases hb : b = b'
    · subst b'
      simp only [Matrix.diagonal_apply_eq,
        Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
        ← Complex.ofReal_sum, conditional_sum_left, Complex.ofReal_one, mul_one,
        Complex.ofReal_inv, Complex.ofReal_natCast]
    · simp [Matrix.diagonal_apply_ne _ hb, Matrix.sum_apply]
  have hfix (a : Fin n) : T.toCompletelyPositiveMap (D.comparisonState a).val =
      (D.comparisonState a).val := congrArg Subtype.val (h a)
  apply Subtype.ext
  change T.toCompletelyPositiveMap D.referenceState.val = D.referenceState.val
  rw [hmix, map_smul, map_sum]
  simp_rw [hfix]

private theorem recovery_minimum [NeZero n] {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    IsLeast (recoveryDimensions (n := n) t ht ht') n := by
  let D : DiagonalExperiment (Fin n) (Fin n) := experiment t ht ht'
  have hpos (b : Fin n) : 0 < D.reference b := uniform_pos
  have hlabel : D.LabelsClasses id := by
    refine ⟨fun b => ⟨b, hpos b, rfl⟩, ?_⟩
    intro b c _ _
    constructor
    · rintro rfl
      rfl
    · intro h
      by_contra hbc
      change b ≠ c at hbc
      have he := congrFun h b
      change conditional t b b / (n : ℝ)⁻¹ = conditional t b c / (n : ℝ)⁻¹ at he
      have hne : (n : ℝ)⁻¹ ≠ 0 := (hpos b).ne'
      have he' := (div_left_inj' hne).mp he
      simp [conditional, hbc] at he'
      linarith
  have hcard := D.likelihoodClasses_card_of_labels hlabel
  obtain ⟨hlower, hattain⟩ := D.sharp_recovery_dimension
  rw [hcard] at hattain
  refine ⟨?_, ?_⟩
  · obtain ⟨encoder, decoder, _, hcomp⟩ := hattain
    exact ⟨encoder, decoder, (fixes_source_iff ht ht' _).2 (by simpa using hcomp)⟩
  · rintro d ⟨encoder, decoder, hjoint⟩
    have hcomp := (fixes_source_iff ht ht' _).1 hjoint
    have href := fixes_reference ht ht' _ hcomp
    rw [← hcard]
    exact hlower encoder decoder (by simpa using href) (by simpa using hcomp)

/-- The trace conditional expectation for the singleton classical sectors. -/
def dephasing (n : ℕ) : QuantumChannel (Fin n) (Fin n) :=
  pinchingChannel (coordinatePVM (id : Fin n → Fin n))

private theorem dephasing_apply (X : Matrix (Fin n) (Fin n) ℂ) :
    CStarMatrix.ofMatrix.symm ((dephasing n).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      diagonal X.diag := by
  rw [dephasing, pinchingChannel_apply]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [D5.S3.Observer.Conditioning.unreadState, coordinatePVM, Matrix.sum_apply,
      mul_diagonal, diagonal_mul]
  · have h (k : Fin n) : ¬ (j = k ∧ i = k) := fun hk => hij (hk.2.trans hk.1.symm)
    simp [D5.S3.Observer.Conditioning.unreadState, coordinatePVM, Matrix.sum_apply,
      mul_diagonal, diagonal_mul, Matrix.diagonal_apply_ne _ hij, ← ite_and, h]

private theorem comparison_commutant [NeZero n] {t : ℝ} (ht : 0 < t) (ht' : t < 1)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    (∀ a, Commute X (pairMatrix ((experiment t ht ht').comparisonState a))) ↔
      X = diagonal X.diag := by
  change (∀ a, Commute X (diagonal fun b => (conditional t a b : ℂ))) ↔ _
  constructor
  · intro h
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) (h i).eq
      simp only [mul_diagonal, diagonal_mul, conditional, ite_true, ite_eq_right hij,
        Complex.ofReal_add, Complex.ofReal_zero, zero_add] at he
      rw [Matrix.diagonal_apply_ne _ hij]
      have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      apply (mul_eq_zero.mp (show X i j * (t : ℂ) = 0 by linear_combination -he)).resolve_right htC
  · intro h a
    conv_lhs => rw [h]
    exact Matrix.commute_diagonal _ _

/-- Kato's reference-first Eq. (17) evaluated for the family. -/
def choi (n : ℕ) [NeZero n] : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  pairMatrix (normalizedChoi (dephasing n))

private theorem choi_diagonal [NeZero n] :
    choi n = diagonal (fun p : Fin n × Fin n => if p.1 = p.2 then (n : ℂ)⁻¹ else 0) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  rw [choi, normalizedChoi_entry]
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M x y)
    (dephasing_apply (single i j 1))
  change (dephasing n).toCompletelyPositiveMap (CStarMatrix.ofMatrix (single i j 1)) x y = _ at he
  rw [he]
  by_cases hxy : x = y
  · subst y
    by_cases hix : i = x
    · subst i
      by_cases hxj : x = j
      · subst j
        simp
      · simp [Prod.mk.injEq, hxj]
    · simp [Matrix.diagonal_apply, Prod.mk.injEq, hix]
  · simp [Prod.mk.injEq, hxy]

/-- The inverse of the change of basis on kets. Mathlib's permutation matrix
acts on a coordinate function by precomposition. -/
def addSecond (n : ℕ) [NeZero n] : Equiv.Perm (Fin n × Fin n) where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 - p.2, p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- The unitary that sends the ket indexed by `(x,y)` to `(x-y,y)`. -/
def subtractUnitary (n : ℕ) [NeZero n] : unitaryGroup (Fin n × Fin n) ℂ :=
  ⟨(addSecond n).permMatrix ℂ, by
    rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
      ← Matrix.permMatrix_mul]
    simp⟩

/-- The rank objective of Eq. (61) at a joint unitary. -/
def marginalRank [NeZero n] (U : unitaryGroup (Fin n × Fin n) ℂ) : ℕ :=
  (partialTraceRight ((U : Matrix _ _ ℂ) * choi n * (U : Matrix _ _ ℂ)ᴴ)).rank

private theorem subtractUnitary_ket [NeZero n] (x y : Fin n) :
    (subtractUnitary n : Matrix _ _ ℂ) *ᵥ Pi.single (x,y) 1 =
      Pi.single (x - y,y) 1 := by
  change (addSecond n).permMatrix ℂ *ᵥ Pi.single (x,y) 1 = _
  rw [Matrix.permMatrix_mulVec]
  funext p
  have he : addSecond n p = (x,y) ↔ p = (x-y,y) :=
    (Equiv.eq_symm_apply (addSecond n)).symm
  simp [Pi.single_apply, he]

private theorem subtract_marginal [NeZero n] :
    partialTraceRight ((subtractUnitary n : Matrix _ _ ℂ) * choi n *
      (subtractUnitary n : Matrix _ _ ℂ)ᴴ) =
        diagonal (fun i : Fin n => if i = 0 then 1 else 0) := by
  let e := addSecond n
  have hconj : (subtractUnitary n : Matrix _ _ ℂ) * choi n *
      (subtractUnitary n : Matrix _ _ ℂ)ᴴ = (choi n).submatrix e e := by
    change e.permMatrix ℂ * choi n * (e.permMatrix ℂ)ᴴ = _
    rw [Matrix.conjTranspose_permMatrix]
    change e.toPEquiv.toMatrix * choi n * (e⁻¹).toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    rfl
  rw [hconj, choi_diagonal]
  ext x x'
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp only [partialTraceRight, Matrix.submatrix_apply,
    Matrix.diagonal_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq, and_true]
  change (∑ y : Fin n, if x = x' then
    (if x + y = y then (n : ℂ)⁻¹ else 0) else 0) = _
  by_cases hx : x = x' <;> by_cases hz : x = 0 <;>
    simp [hx, hz, hn]

private theorem subtract_rank [NeZero n] : marginalRank (subtractUnitary n) = 1 := by
  rw [marginalRank, subtract_marginal, Matrix.rank_diagonal, Fintype.card_eq_one_iff]
  refine ⟨⟨0, by simp⟩, fun i => Subtype.ext ?_⟩
  by_contra h
  exact i.property (by simp [h])

private theorem rank_minimum [NeZero n] :
    IsLeast (Set.range (marginalRank (n := n))) 1 := by
  refine ⟨⟨subtractUnitary n, subtract_rank⟩, ?_⟩
  · rintro r ⟨U, rfl⟩
    let M := partialTraceRight ((U : Matrix _ _ ℂ) * choi n * (U : Matrix _ _ ℂ)ᴴ)
    have ht : M.trace = 1 := by
      change (partialTraceRight _).trace = 1
      rw [trace_partialTraceRight, Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose,
        Unitary.coe_star_mul_self, one_mul]
      exact (normalizedChoi (dephasing n)).property.2
    change 1 ≤ M.rank
    by_contra! h
    have hz : M.rank = 0 := by omega
    have hlin : M.mulVecLin = 0 :=
      LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
    have hM : M = 0 := by
      apply Matrix.toLin'.injective
      simpa only [Matrix.toLin'_apply', Matrix.mulVecLin_zero] using hlin
    simp [hM] at ht

/-- Every faithful noisy copy law on a nonempty alphabet gives an exact
recovery dimension of n and an Eq. (61) minimum of one. -/
theorem faithful_family (n : ℕ) [NeZero n]
    (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    (∀ p : Fin n × Fin n, 0 < weights t p) ∧
    (∀ a : Fin n, (∑ b : Fin n, weights t (a,b)) = (n : ℝ)⁻¹) ∧
    (∀ b : Fin n, (∑ a : Fin n, weights t (a,b)) = (n : ℝ)⁻¹) ∧
    (∀ X : Matrix (Fin n) (Fin n) ℂ,
      (∀ a, Commute X (pairMatrix ((experiment t ht ht').comparisonState a))) ↔
        X = diagonal X.diag) ∧
    (∀ X : Matrix (Fin n) (Fin n) ℂ,
      CStarMatrix.ofMatrix.symm ((dephasing n).toCompletelyPositiveMap
        (CStarMatrix.ofMatrix X)) = diagonal X.diag) ∧
    IsLeast (recoveryDimensions (n := n) t ht ht') n ∧
    choi n = diagonal (fun p => if p.1 = p.2 then (n : ℂ)⁻¹ else 0) ∧
    (∀ x y : Fin n, (subtractUnitary n : Matrix _ _ ℂ) *ᵥ Pi.single (x,y) 1 =
      Pi.single (x-y,y) 1) ∧
    partialTraceRight ((subtractUnitary n : Matrix _ _ ℂ) * choi n *
      (subtractUnitary n : Matrix _ _ ℂ)ᴴ) =
      diagonal (fun i : Fin n => if i = 0 then 1 else 0) ∧
    marginalRank (subtractUnitary n) = 1 ∧
    IsLeast (Set.range (marginalRank (n := n))) 1 := by
  refine ⟨weights_pos ht ht', ?_, ?_, comparison_commutant ht ht', dephasing_apply,
    recovery_minimum ht ht', choi_diagonal, subtractUnitary_ket, subtract_marginal,
    subtract_rank, rank_minimum⟩
  · intro a
    simp only [weights, ← Finset.mul_sum, conditional_sum, mul_one]
  · intro b
    simp only [weights, ← Finset.mul_sum, conditional_sum_left, mul_one]

/-- The restriction of Kato's Eq. (61) proposal to the faithful noisy copy laws. -/
def claim : Prop :=
  ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ t (ht : 0 < t) (ht' : t < 1),
    ∃ d, IsLeast (recoveryDimensions (n := n) t ht ht') d ∧
      IsLeast (Set.range (marginalRank (n := n))) d

/-- Equation (61) already fails on faithful classical states. -/
theorem result : ¬ claim := by
  intro h
  have h₂ : 2 ≤ (2 : ℕ) := le_rfl
  have ht : (0 : ℝ) < 1/2 := by norm_num
  have ht' : (1/2 : ℝ) < 1 := by norm_num
  obtain ⟨d, hrec, hrank⟩ := h 2 h₂ (1/2) ht ht'
  obtain ⟨_, _, _, _, _, hfrec, _, _, _, _, hfrank⟩ := faithful_family 2 (1/2) ht ht'
  have hd₂ := hrec.unique hfrec
  have hd₁ := hrank.unique hfrank
  omega

#print axioms faithful_family
#print axioms claim
#print axioms result

end D5.S3.Quantum.Recovery.LocalCompression.KatoRankRefutation
