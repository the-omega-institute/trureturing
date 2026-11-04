/- GID: D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.claim; result=D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.result; claim=D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.claim
   digest: A spin-four covariant channel lowers order-seven trace-distance anticoherence. -/

import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
import D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
import D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
import D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization
import D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness

/-!
The mixed-state reading of axiom (T4) in Denis–Lacaille–Martin–Serrano-Ensástiga,
arXiv:2605.29436v1, with the witness specified in preregistration #24441.
Reduced states are expressed in the normalized Dicke basis. Their splitting
isometry implements the ordinary qubit partial trace in these coordinates.
-/

set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
namespace D5.S3.Quantum.Measurement.AnticoherenceTraceDistanceRefutation

open scoped BigOperators ComplexOrder MatrixOrder
open _root_.Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (Jplus Jx Jy Jz)
open D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
  (pauli_rotation tensor_unitary quadratic_rotation orthogonal_sandwich
    local_action collectiveSpin collective_tensor_rotation
    dickeIsometry partialTrace_isometries dickeCoefficient dicke_site_sum)

open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (tensorOp)
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (pauli)
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness (designAverage)

private def witnessState : Matrix (Fin 9) (Fin 9) ℂ :=
  diagonal (fun r => (![209, 92, 560, 0, 441, 0, 294, 168, 0] r : ℂ) / 1764)

private def witnessKraus : Fin 5 → Matrix (Fin 9) (Fin 9) ℂ :=
  let z : Matrix (Fin 9) (Fin 9) ℂ := Jz 8
  let p : Matrix (Fin 9) (Fin 9) ℂ := Jplus 8
  ![(1 / (Real.sqrt 1540 : ℂ)) • ((3 : ℂ) • (z * z) - (20 : ℂ) • 1),
    (-(Real.sqrt (3 / 3080) : ℂ)) • (z * p + p * z),
    (Real.sqrt (3 / 3080) : ℂ) • (z * pᴴ + pᴴ * z),
    (Real.sqrt (3 / 3080) : ℂ) • (p * p),
    (Real.sqrt (3 / 3080) : ℂ) • (pᴴ * pᴴ)]

private def witnessChannel : MatrixMap (Fin 9) (Fin 9) ℂ :=
  MatrixMap.of_kraus witnessKraus witnessKraus

private def quadrupole (a b : Fin 3) : Matrix (Fin 9) (Fin 9) ℂ :=
  let j : Fin 3 → Matrix (Fin 9) (Fin 9) ℂ := ![Jx 8, Jy 8, Jz 8]
  (1 / 2 : ℂ) • (j a * j b + j b * j a) -
    (if a = b then (20 / 3 : ℂ) else 0) • 1

private def witnessOutput : Matrix (Fin 9) (Fin 9) ℂ :=
  diagonal (fun r =>
    (![22288, 30100, 25528, 13149, 45540, 10584, 24654, 11613, 10584] r : ℂ) / 194040)

private def krausShift : Fin 5 → ℤ := ![0, -1, 1, -2, 2]

private def krausAmplitude (q : Fin 5) (r : Fin 9) : ℝ :=
  let z : ℝ := 4 - r.val
  let c := Real.sqrt (3 / 3080)
  ![(3 * z ^ 2 - 20) / Real.sqrt 1540,
    -c * (2 * z + 1) * Real.sqrt (20 - z * (z + 1)),
    c * (2 * z - 1) * Real.sqrt (20 - (z - 1) * z),
    c * Real.sqrt (20 - z * (z + 1)) * Real.sqrt (20 - (z + 1) * (z + 2)),
    c * Real.sqrt (20 - (z - 1) * z) * Real.sqrt (20 - (z - 2) * (z - 1))] q

private def krausWeight (q : Fin 5) (r : Fin 9) : ℝ :=
  let z : ℝ := 4 - r.val
  ![(3 * z ^ 2 - 20) ^ 2 / 1540,
    3 / 3080 * (2 * z + 1) ^ 2 * (20 - z * (z + 1)),
    3 / 3080 * (2 * z - 1) ^ 2 * (20 - (z - 1) * z),
    3 / 3080 * (20 - z * (z + 1)) * (20 - (z + 1) * (z + 2)),
    3 / 3080 * (20 - (z - 1) * z) * (20 - (z - 2) * (z - 1))] q

set_option maxHeartbeats 4000000 in
-- The five sparse matrices have nine input and output indices.
private lemma kraus_entry (q : Fin 5) (i r : Fin 9) :
    witnessKraus q i r =
      if (i.val : ℤ) = (r.val : ℤ) + krausShift q then (krausAmplitude q r : ℂ)
      else 0 := by
  rw [witnessKraus, krausShift, krausAmplitude]
  dsimp only [Jz]
  fin_cases q <;> fin_cases i <;> fin_cases r <;>
    norm_num [witnessKraus, krausShift, krausAmplitude, Jplus, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.conj_ofReal] <;> ring

private lemma kraus_amplitude_sq (q : Fin 5) (r : Fin 9) :
    krausAmplitude q r ^ 2 = krausWeight q r := by
  rw [krausWeight]
  fin_cases q <;> fin_cases r <;>
    norm_num [krausAmplitude, krausWeight, mul_pow, div_pow, Real.sq_sqrt]

private lemma kraus_column_product (q : Fin 5) (i : Fin 9) (r s : Fin 9) :
    star (witnessKraus q i r) * witnessKraus q i s =
      if r = s ∧ (i.val : ℤ) = (r.val : ℤ) + krausShift q then
        (krausWeight q r : ℂ) else 0 := by
  rw [kraus_entry, kraus_entry]
  by_cases hr : (i.val : ℤ) = (r.val : ℤ) + krausShift q
  · by_cases hs : (i.val : ℤ) = (s.val : ℤ) + krausShift q
    · have hrs : r = s := Fin.ext (by omega)
      subst s
      simp only [hr, ite_true, true_and, Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, ← sq, kraus_amplitude_sq]
    · have hrs : r ≠ s := by intro he; subst s; exact hs hr
      have hnot : ¬ (r = s ∧ (i.val : ℤ) = (r.val : ℤ) + krausShift q) :=
        fun h => hrs h.1
      rw [if_pos hr, if_neg hs, if_neg hnot, mul_zero]
  · simp [hr]

private theorem kraus_complete : ∑ q, (witnessKraus q)ᴴ * witnessKraus q = 1 := by
  ext r s
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [kraus_column_product]
  fin_cases r <;> fin_cases s <;>
    norm_num [Fin.sum_univ_succ, krausShift, krausWeight, Matrix.one_apply]

private theorem witness_state : witnessState.PosSemidef ∧ witnessState.trace = 1 := by
  rw [witnessState]
  constructor
  · apply posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im]
  · norm_num [witnessState, trace_diagonal, Fin.sum_univ_succ]

private lemma kraus_row_product (q : Fin 5) (i j r : Fin 9) :
    witnessKraus q i r * star (witnessKraus q j r) =
      if i = j ∧ (i.val : ℤ) = (r.val : ℤ) + krausShift q then
        (krausWeight q r : ℂ) else 0 := by
  rw [kraus_entry, kraus_entry]
  by_cases hi : (i.val : ℤ) = (r.val : ℤ) + krausShift q
  · by_cases hj : (j.val : ℤ) = (r.val : ℤ) + krausShift q
    · have hij : i = j := Fin.ext (by omega)
      subst j
      simp only [hi, ite_true, true_and, Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, ← sq, kraus_amplitude_sq]
    · have hij : i ≠ j := by intro he; subst j; exact hj hi
      simp [hi, hj, hij]
  · simp [hi]

private lemma channel_diagonal_entry (p : Fin 9 → ℂ) (i j : Fin 9) :
    witnessChannel (diagonal p) i j = ∑ q : Fin 5, ∑ r : Fin 9,
      p r * (witnessKraus q i r * star (witnessKraus q j r)) := by
  rw [witnessChannel,
    D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization.diagonal_entry_expansion]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  exact mul_comm _ _

set_option maxHeartbeats 1000000 in
-- Nine diagonal entries each sum the five Kraus contributions.
private theorem witness_output : witnessChannel witnessState = witnessOutput := by
  rw [witnessOutput]
  ext i j
  change witnessChannel (diagonal (fun r =>
    (![209, 92, 560, 0, 441, 0, 294, 168, 0] r : ℂ) / 1764)) i j = witnessOutput i j
  rw [channel_diagonal_entry]
  simp_rw [kraus_row_product]
  by_cases hij : i = j
  · subst j
    fin_cases i <;>
      norm_num [Fin.sum_univ_succ, krausShift, krausWeight, witnessOutput]
  · simp [hij, witnessOutput]

/-- The spin-`n/2` representation obtained by restricting the qubit tensor power. -/
def spinAction (n : ℕ) (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (dickeIsometry n)ᴴ * tensorOp (fun _ : Fin n => u.val) * dickeIsometry n

/-- The Dicke splitting coefficients for the first `t` and last `n-t` qubits. -/
private def dickeSplit (n t : ℕ) :
    Matrix (Fin (t + 1) × Fin (n - t + 1)) (Fin (n + 1)) ℂ :=
  fun kl r => if kl.1.val + kl.2.val = r.val then
    ((Real.sqrt ((t.choose kl.1.val : ℝ) * ((n - t).choose kl.2.val : ℝ)) /
      Real.sqrt (n.choose r.val : ℝ) : ℝ) : ℂ) else 0

/-- For `t ≤ n`, form the symmetric qubit operator `ρ_S = V_n * ρ * V_nᴴ`,
reindex its computational basis by the explicit equivalence appending the first `t`
and last `n - t` qubits, take the partial trace over the latter, and return
`V_tᴴ * Tr_{n-t}(ρ_S) * V_t` in the normalized `t`-qubit Dicke basis.
For `n < t`, the value is zero. -/
def reducedState {n : ℕ} (t : ℕ) (ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ :=
  if ht : t ≤ n then
    let e : (Fin t → Fin 2) × (Fin (n - t) → Fin 2) ≃ (Fin n → Fin 2) :=
      (Fin.appendEquiv t (n - t)).trans
        (Equiv.cast (congrArg (fun m => Fin m → Fin 2) (Nat.add_sub_of_le ht)))
    (dickeIsometry t)ᴴ *
      partialTraceRight ((dickeIsometry n * ρ * (dickeIsometry n)ᴴ).submatrix e e) *
        dickeIsometry t
  else 0

/-- The source's maximum trace distance over all states of spin `t/2`. -/
def normalizer (t : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ σ : Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ,
    σ.PosSemidef ∧ σ.trace = 1 ∧ d = traceNorm (σ - designAverage (t + 1))}

/-- The distance-based total anticoherence measure for Schatten exponent one. -/
def anticoherence {n : ℕ} (t : ℕ)
    (ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℝ :=
  1 - traceNorm (reducedState t ρ - designAverage (t + 1)) / normalizer t

/-- Complete positivity, trace preservation, and covariance under every single-qubit SU(2). -/
def IsCovariantChannel {n : ℕ} (φ : MatrixMap (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  φ.IsCompletelyPositive ∧ φ.IsTracePreserving ∧
    ∀ (u : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      φ (spinAction n u * x * (spinAction n u)ᴴ) =
        spinAction n u * φ x * (spinAction n u)ᴴ

/-- Axiom (T4), including the source's full mixed-state range `1 ≤ t ≤ n`. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ t : ℕ, 1 ≤ t → t ≤ n →
    ∀ φ : MatrixMap (Fin (n + 1)) (Fin (n + 1)) ℂ, IsCovariantChannel φ →
    ∀ ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ρ.PosSemidef → ρ.trace = 1 → anticoherence t ρ ≤ anticoherence t (φ ρ)

private lemma weight_card (n : ℕ) (x : Fin n → Fin 2) :
    (∑ i, (x i).val) = (Finset.univ.filter (fun i => x i = 1)).card := by
  calc
    _ = ∑ i : Fin n, if x i = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      generalize hx : x i = b
      fin_cases b <;> simp
    _ = _ := by simpa using (Finset.sum_boole (Finset.univ : Finset (Fin n)) (fun i => x i = 1))

private lemma weight_count (n : ℕ) (x : Fin n → Fin 2) :
    (occupation x).count 1 = ∑ i, (x i).val := by
  rw [← D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.occupation_fiber_card x 1, Fintype.subtype_card, weight_card]

private lemma occupation_eq_iff_weight (n : ℕ) (x : Fin n → Fin 2)
    (a : Multiset (Fin 2)) (ha : a.card = n) :
    occupation x = a ↔ (∑ i, (x i).val) = a.count 1 := by
  constructor
  · intro h
    rw [← weight_count n x, h]
  · intro h
    have hx : (occupation x).count 0 + (occupation x).count 1 = n := by
      simpa only [Fin.sum_univ_two, occupation_card] using
        (Multiset.sum_count_eq_card (s := Finset.univ) (m := occupation x)
          (fun _ _ => Finset.mem_univ _))
    have ha' : a.count 0 + a.count 1 = n := by
      simpa only [Fin.sum_univ_two, ha] using
        (Multiset.sum_count_eq_card (s := Finset.univ) (m := a)
          (fun _ _ => Finset.mem_univ _))
    rw [← weight_count n x] at h
    apply Multiset.ext.mpr
    intro b
    fin_cases b <;> simp_all
    omega

private lemma dicke_count (n k : ℕ) :
    (∑ x : Fin n → Fin 2, if (∑ i, (x i).val) = k then (1 : ℂ) else 0) =
      (n.choose k : ℂ) := by
  let e : (Fin n → Fin 2) ≃ (Fin n → Bool) :=
    Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv
  have hw (x : Fin n → Fin 2) :
      (Finset.univ.filter (fun j => e x j = true)).card = ∑ i, (x i).val := by
    rw [weight_card]
    congr 1
  have hc : (∑ y : Fin n → Bool,
      if (Finset.univ.filter (fun j => y j = true)).card = k then (1 : ℂ) else 0) =
      (n.choose k : ℂ) := by
    rw [← Finset.sum_filter]
    simp [D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.weight_class_card]
  rw [← e.sum_comp] at hc
  simpa only [hw] using hc

private lemma binary_multiplicity (n : ℕ) (a : Multiset (Fin 2)) (ha : a.card = n) :
    multiplicity n a = n.choose (a.count 1) := by
  rw [D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity, sector_words_card_multinomial a ha,
    show (Finset.univ : Finset (Fin 2)) = {1, 0} by decide,
    Nat.binomial_eq_choose (by decide : (1 : Fin 2) ≠ 0)]
  congr 1
  simpa only [Fin.sum_univ_two, ha, add_comm] using
    (Multiset.sum_count_eq_card (s := Finset.univ) (m := a)
      (fun _ _ => Finset.mem_univ _))

private lemma dicke_sector (n : ℕ) (a : Multiset (Fin 2)) (ha : a.card = n)
    (r : Fin (n + 1)) (hr : a.count 1 = r.val) (x : Fin n → Fin 2) :
    dickeIsometry n x r = sectorVector n a x := by
  simp only [dickeIsometry.eq_1, sectorVector, sectorWords, Finset.mem_filter,
    Finset.mem_univ, true_and, occupation_eq_iff_weight n x a ha,
    binary_multiplicity n a ha, hr]

private lemma dicke_isometry (n : ℕ) : (dickeIsometry n)ᴴ * dickeIsometry n = 1 := by
  let a (r : Fin (n + 1)) : Multiset (Fin 2) :=
    Multiset.replicate (n - r.val) 0 + Multiset.replicate r.val 1
  have ha (r : Fin (n + 1)) : (a r).card = n := by
    simp [a]; omega
  have hcount (r : Fin (n + 1)) : (a r).count 1 = r.val := by simp [a, Multiset.count_replicate]
  have hv (r : Fin (n + 1)) (x : Fin n → Fin 2) :
      dickeIsometry n x r = sectorVector n (a r) x :=
    dicke_sector n (a r) (ha r) r (hcount r) x
  have hi (r s : Fin (n + 1)) : a r = a s ↔ r = s := by
    constructor
    · intro h
      apply Fin.ext
      simpa only [hcount] using congrArg (fun z : Multiset (Fin 2) => z.count 1) h
    · exact congrArg a
  ext r s
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hv]
  rw [sector_gram _ _ (ha r)]
  simp only [hi, Matrix.one_apply]

private lemma weight_le (n : ℕ) (x : Fin n → Fin 2) : (∑ i, (x i).val) ≤ n := by
  rw [weight_card]
  exact card_finset_fin_le _

private lemma tensor_weight_constant (n : ℕ) (u : Matrix (Fin 2) (Fin 2) ℂ)
    (x y : Fin n → Fin 2) (r : Fin (n + 1))
    (h : (∑ i, (x i).val) = ∑ i, (y i).val) :
    (tensorOp (fun _ : Fin n => u) * dickeIsometry n) x r =
      (tensorOp (fun _ : Fin n => u) * dickeIsometry n) y r := by
  have hp (σ : Equiv.Perm (Fin n)) (x : Fin n → Fin 2) :
      (tensorOp (fun _ : Fin n => u) * dickeIsometry n) (x ∘ σ) r =
        (tensorOp (fun _ : Fin n => u) * dickeIsometry n) x r := by
    let e := Equiv.arrowCongr σ.symm (Equiv.refl (Fin 2))
    rw [Matrix.mul_apply, Matrix.mul_apply]
    calc
      _ = ∑ z : Fin n → Fin 2,
          tensorOp (fun _ : Fin n => u) (x ∘ σ) (z ∘ σ) * dickeIsometry n (z ∘ σ) r :=
        (e.sum_comp (fun z => tensorOp (fun _ : Fin n => u) (x ∘ σ) z * dickeIsometry n z r)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z _
        have hw : (∑ i, (z (σ i)).val) = ∑ i, (z i).val :=
          Equiv.sum_comp σ (fun i => (z i).val)
        have hu : tensorOp (fun _ : Fin n => u) (x ∘ σ) (z ∘ σ) = tensorOp (fun _ : Fin n => u) x z :=
          Equiv.prod_comp σ (fun i => u (x i) (z i))
        simp only [hu, dickeIsometry, Function.comp_apply, hw]
  apply D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.symmetric_occupation_constant
    (fun x => (tensorOp (fun _ : Fin n => u) * dickeIsometry n) x r) hp x y
  apply (occupation_eq_iff_weight n x (occupation y) (occupation_card y)).2
  rw [weight_count, h]

private lemma dicke_projector_entry (n : ℕ) (x y : Fin n → Fin 2) :
    (dickeIsometry n * (dickeIsometry n)ᴴ) x y =
      if (∑ i, (x i).val) = ∑ i, (y i).val then
        (n.choose (∑ i, (x i).val) : ℂ)⁻¹ else 0 := by
  let r : Fin (n + 1) := ⟨∑ i, (x i).val, Nat.lt_succ_of_le (weight_le n x)⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · have hs : (Real.sqrt (n.choose r.val : ℝ) : ℂ) ^ 2 = (n.choose r.val : ℂ) := by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (n.choose r.val))
    by_cases hxy : (∑ i, (x i).val) = ∑ i, (y i).val
    · have hy : (∑ i, (y i).val) = r.val := hxy.symm
      have hx : (∑ i, (x i).val) = r.val := rfl
      rw [if_pos hxy]
      simp only [Matrix.conjTranspose_apply, dickeIsometry, hx, hy,
        ite_true, Complex.star_def, map_inv₀, Complex.conj_ofReal]
      rw [← mul_inv, ← sq]
      exact congrArg Inv.inv hs
    · have hy : (∑ i, (y i).val) ≠ r.val := by
        intro he
        exact hxy he.symm
      simp [Matrix.conjTranspose_apply, dickeIsometry, r, hxy, hy]
  · intro s _ hsr
    have hx : (∑ i, (x i).val) ≠ s.val := by
      intro he
      exact hsr (Fin.ext he.symm)
    simp [dickeIsometry, hx]
  · simp

private lemma tensor_preserves_symmetric (n : ℕ)
    (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    tensorOp (fun _ : Fin n => u.val) * dickeIsometry n = dickeIsometry n * spinAction n u := by
  have hp : (dickeIsometry n * (dickeIsometry n)ᴴ) *
      (tensorOp (fun _ : Fin n => u.val) * dickeIsometry n) = tensorOp (fun _ : Fin n => u.val) * dickeIsometry n := by
    ext x r
    rw [Matrix.mul_apply]
    simp_rw [dicke_projector_entry]
    have he (y : Fin n → Fin 2) :
        (if (∑ i, (x i).val) = ∑ i, (y i).val then
          (n.choose (∑ i, (x i).val) : ℂ)⁻¹ else 0) *
            (tensorOp (fun _ : Fin n => u.val) * dickeIsometry n) y r =
        (if (∑ i, (y i).val) = ∑ i, (x i).val then (1 : ℂ) else 0) *
          ((n.choose (∑ i, (x i).val) : ℂ)⁻¹ *
            (tensorOp (fun _ : Fin n => u.val) * dickeIsometry n) x r) := by
      by_cases hxy : (∑ i, (x i).val) = ∑ i, (y i).val
      · rw [if_pos hxy, if_pos hxy.symm, one_mul,
          tensor_weight_constant n u.val y x r hxy.symm]
      · simp [hxy, Ne.symm hxy]
    simp_rw [he]
    rw [← Finset.sum_mul, dicke_count]
    have hn : (n.choose (∑ i, (x i).val) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (weight_le n x)).ne'
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  rw [spinAction]
  simpa only [Matrix.mul_assoc] using hp.symm

private def dickeSplitSum (t s : ℕ) :
    Matrix (Fin (t + 1) × Fin (s + 1)) (Fin (t + s + 1)) ℂ :=
  fun kl r => dickeSplit (t + s) t
    (kl.1, ⟨kl.2.val, by have := kl.2.isLt; omega⟩) r

private lemma dicke_split_factor (t s : ℕ) :
    (dickeIsometry (t + s)).submatrix
      (fun xy : (Fin t → Fin 2) × (Fin s → Fin 2) => Fin.append xy.1 xy.2) id =
      Matrix.kronecker (dickeIsometry t) (dickeIsometry s) * dickeSplitSum t s := by
  ext ⟨x, y⟩ r
  let k : Fin (t + 1) := ⟨∑ i, (x i).val, Nat.lt_succ_of_le (weight_le t x)⟩
  let l : Fin (s + 1) := ⟨∑ i, (y i).val, Nat.lt_succ_of_le (weight_le s y)⟩
  have hw : (∑ i : Fin (t + s), (Fin.append x y i).val) = k.val + l.val := by
    rw [Fin.sum_univ_add]
    simp [k, l]
  rw [Matrix.mul_apply, Finset.sum_eq_single (k, l)]
  · dsimp only [Matrix.submatrix_apply, id_eq, Matrix.kronecker, Matrix.kroneckerMap,
      Matrix.of_apply, dickeSplitSum, dickeSplit]
    simp only [Nat.add_sub_cancel_left]
    by_cases h : k.val + l.val = r.val
    · rw [if_pos h]
      let a : Multiset (Fin 2) :=
        Multiset.replicate (t + s - r.val) 0 + Multiset.replicate r.val 1
      have ha : a.card = t + s := by simp [a]; omega
      have har : a.count 1 = r.val := by simp [a, Multiset.count_replicate]
      have hxy : occupation (Fin.append x y) = a :=
        (occupation_eq_iff_weight (t + s) (Fin.append x y) a ha).2 (by rw [hw, har]; exact h)
      obtain ⟨b, hxb, hyb⟩ :=
        (D5.S3.Quantum.Entanglement.CoherentHistorySchmidt.legal_iff x y).mp hxy
      have hb : b.val.count 1 = k.val := by rw [← hxb]; exact weight_count t x
      have hc : (a - b.val).count 1 = l.val := by rw [← hyb]; exact weight_count s y
      have hf := D5.S3.Quantum.Entanglement.CoherentHistorySchmidt.normalized_coefficient_factorization
        ha x y
      rw [D5.S3.Quantum.Entanglement.CoherentHistorySchmidt.coefficient_eq_uniform_word,
        ← dicke_sector (t + s) a ha r har, Finset.sum_eq_single b] at hf
      · rw [D5.S3.Quantum.Entanglement.CoherentHistorySchmidt.schmidtCoefficient,
          binary_multiplicity t b.val (boundary_spec a t b).2,
          binary_multiplicity s (a - b.val) (complement_card ha b),
          binary_multiplicity (t + s) a ha, hb, hc, har,
          ← dicke_sector t b.val (boundary_spec a t b).2 k hb,
          ← dicke_sector s (a - b.val) (complement_card ha b) l hc] at hf
        rw [hf, Real.sqrt_mul (by positivity)]
        push_cast
        ring
      · intro c _ hcb
        have hxc : occupation x ≠ c.val :=
          ne_of_eq_of_ne hxb (Subtype.val_injective.ne hcb).symm
        simp [sectorVector, sectorWords, hxc]
      · simp
    · simp [dickeIsometry, hw, h]
  · rintro ⟨a, b⟩ _ hab
    by_cases ha : a = k
    · have hb : (∑ i, (y i).val) ≠ b.val := by
        intro hb
        exact hab (Prod.ext ha (Fin.ext hb.symm))
      dsimp only [Matrix.kronecker, Matrix.kroneckerMap]
      simp [dickeIsometry, hb]
    · have hx : (∑ i, (x i).val) ≠ a.val := by
        intro hx
        exact ha (Fin.ext hx.symm)
      dsimp only [Matrix.kronecker, Matrix.kroneckerMap]
      simp [dickeIsometry, hx]
  · simp

set_option backward.isDefEq.respectTransparency false in
private lemma dicke_split_partialTrace (t s : ℕ)
    (ρ : Matrix (Fin (t + s + 1)) (Fin (t + s + 1)) ℂ) :
    let v := dickeIsometry (t + s)
    let w := fun xy : (Fin t → Fin 2) × (Fin s → Fin 2) =>
      Fin.append xy.1 xy.2
    partialTraceRight ((v * ρ * vᴴ).submatrix w w) =
      dickeIsometry t *
        partialTraceRight (dickeSplitSum t s * ρ * (dickeSplitSum t s)ᴴ) *
          (dickeIsometry t)ᴴ := by
  dsimp only
  have hf := dicke_split_factor t s
  have he : ((dickeIsometry (t + s) * ρ * (dickeIsometry (t + s))ᴴ).submatrix
      (fun xy : (Fin t → Fin 2) × (Fin s → Fin 2) => Fin.append xy.1 xy.2)
      (fun xy : (Fin t → Fin 2) × (Fin s → Fin 2) => Fin.append xy.1 xy.2)) =
      Matrix.kronecker (dickeIsometry t) (dickeIsometry s) *
        (dickeSplitSum t s * ρ * (dickeSplitSum t s)ᴴ) *
          (Matrix.kronecker (dickeIsometry t) (dickeIsometry s))ᴴ := by
    rw [← Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl _) _,
      ← Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl _) _]
    change ((dickeIsometry (t + s)).submatrix _ id) * ρ *
      ((dickeIsometry (t + s)).submatrix _ id)ᴴ = _
    rw [hf, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [he, partialTrace_isometries _ _ (dicke_isometry s)]

private lemma reducedState_eq_dickeSplit (n t : ℕ) (ht : t ≤ n)
    (ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    reducedState t ρ = partialTraceRight (dickeSplit n t * ρ * (dickeSplit n t)ᴴ) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
  have hr : reducedState t ρ = (dickeIsometry t)ᴴ *
      partialTraceRight ((dickeIsometry (t + s) * ρ * (dickeIsometry (t + s))ᴴ).submatrix
        (fun xy : (Fin t → Fin 2) × (Fin s → Fin 2) => Fin.append xy.1 xy.2)
        (fun xy : (Fin t → Fin 2) × (Fin s → Fin 2) => Fin.append xy.1 xy.2)) *
          dickeIsometry t := by
    unfold reducedState
    rw [dite_eq_left (show t ≤ t + s by omega)]
    let p (m : ℕ) : Prop := ∀ h : t + m = t + s,
      let e := (Fin.appendEquiv t m).trans
        (Equiv.cast (congrArg (fun a => Fin a → Fin 2) h))
      (dickeIsometry t)ᴴ *
        partialTraceRight
          ((dickeIsometry (t + s) * ρ * (dickeIsometry (t + s))ᴴ).submatrix e e) * dickeIsometry t =
        (dickeIsometry t)ᴴ *
          partialTraceRight
            ((dickeIsometry (t + s) * ρ * (dickeIsometry (t + s))ᴴ).submatrix
              (Fin.appendEquiv t s) (Fin.appendEquiv t s)) * dickeIsometry t
    have hp : p s := by intro h; rfl
    have hm : p (t + s - t) := (congrArg p (Nat.add_sub_cancel_left t s)).mpr hp
    exact hm (Nat.add_sub_of_le (show t ≤ t + s by omega))
  rw [hr, dicke_split_partialTrace]
  have hi := dicke_isometry t
  calc
    _ = partialTraceRight (dickeSplitSum t s * ρ * (dickeSplitSum t s)ᴴ) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (dickeIsometry t)ᴴ (dickeIsometry t), hi,
        Matrix.one_mul, Matrix.mul_one]
    _ = _ := by
      let v (m : ℕ) : Matrix (Fin (t + 1) × Fin (m + 1)) (Fin (t + s + 1)) ℂ :=
        fun kl r => if kl.1.val + kl.2.val = r.val then
          ((Real.sqrt ((t.choose kl.1.val : ℝ) * (m.choose kl.2.val : ℝ)) /
            Real.sqrt ((t + s).choose r.val : ℝ) : ℝ) : ℂ) else 0
      have hv : dickeSplitSum t s = v s := by
        ext kl r
        rw [dickeSplitSum.eq_1]
        simp only [dickeSplit, v, Nat.add_sub_cancel_left]
      rw [hv]
      change partialTraceRight (v s * ρ * (v s)ᴴ) =
        partialTraceRight (v (t + s - t) * ρ * (v (t + s - t))ᴴ)
      exact congrArg (fun m => partialTraceRight (v m * ρ * (v m)ᴴ))
        (Nat.add_sub_cancel_left t s).symm

set_option maxHeartbeats 1000000 in
-- The ladder Casimir identity is diagonal on nine coordinates.
private lemma ladder_casimir :
    Jplus 8 * (Jplus 8)ᴴ + (Jplus 8)ᴴ * Jplus 8 =
      (40 : ℂ) • 1 - (2 : ℂ) • (Jz 8 * Jz 8) := by
  ext i j
  dsimp only [Jz]
  fin_cases i <;> fin_cases j <;>
    norm_num [Jplus, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_ofReal] <;>
    ring_nf <;> norm_num [← Complex.ofReal_pow, Real.sq_sqrt]

private lemma quadrupole_tracefree :
    quadrupole 0 0 + quadrupole 1 1 = -quadrupole 2 2 := by
  rw [quadrupole]
  dsimp only [quadrupole, Jx, Jy]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Fin.isValue, ite_true]
  norm_num [div_eq_mul_inv]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, smul_smul]
  have h := ladder_casimir
  linear_combination (norm := (match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]))
    (1 / 2 : ℂ) • h

private lemma kraus_cartesian (q : Fin 5) : witnessKraus q =
    ![(3 / (Real.sqrt 1540 : ℂ)) • quadrupole 2 2,
      (-2 * (Real.sqrt (3 / 3080) : ℂ)) •
        (quadrupole 0 2 + Complex.I • quadrupole 1 2),
      (2 * (Real.sqrt (3 / 3080) : ℂ)) •
        (quadrupole 0 2 - Complex.I • quadrupole 1 2),
      (Real.sqrt (3 / 3080) : ℂ) •
        (quadrupole 0 0 - quadrupole 1 1 + (2 * Complex.I) • quadrupole 0 1),
      (Real.sqrt (3 / 3080) : ℂ) •
        (quadrupole 0 0 - quadrupole 1 1 - (2 * Complex.I) • quadrupole 0 1)] q := by
  fin_cases q <;>
    dsimp only [witnessKraus, quadrupole, Jx, Jy] <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons, Fin.isValue] <;>
    norm_num [div_eq_mul_inv] <;>
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, smul_smul] <;>
    match_scalars <;> ring_nf <;> norm_num [Complex.I_sq] <;> ring

private lemma quadrupole_adjoint (a b : Fin 3) :
    (quadrupole a b)ᴴ = quadrupole a b := by
  have hz : (Jz 8)ᴴ = Jz 8 := by dsimp only [Jz]; simp
  fin_cases a <;> fin_cases b <;>
    dsimp only [quadrupole, Jx, Jy] <;>
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hz] <;>
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, smul_smul] <;>
    match_scalars <;> ring_nf <;> norm_num [Complex.I_sq] <;> ring

private lemma cartesian_channel (x : Matrix (Fin 9) (Fin 9) ℂ) :
    witnessChannel x = (3 / 770 : ℂ) •
      ∑ a : Fin 3, ∑ b : Fin 3, quadrupole a b * x * quadrupole a b := by
  have h22 : quadrupole 2 2 = -(quadrupole 0 0 + quadrupole 1 1) := by
    linear_combination (norm := module) quadrupole_tracefree
  have hs (a b : Fin 3) : quadrupole a b = quadrupole b a := by
    simp only [quadrupole, add_comm, eq_comm]
  simp only [witnessChannel, MatrixMap.of_kraus, LinearMap.coe_sum,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, kraus_cartesian]
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue, Finset.sum_empty, add_zero]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, quadrupole_adjoint, h22,
    hs 1 0, hs 2 0, hs 2 1]
  norm_num
  simp only [quadrupole_adjoint, h22, hs 1 0, hs 2 0, hs 2 1]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg,
    smul_add, smul_sub, smul_neg, neg_smul, smul_smul, Matrix.mul_assoc]
  match_scalars <;> (try ring_nf) <;>
    norm_num [Complex.I_sq, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt]

private lemma spin_action_unitary (n : ℕ)
    (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (spinAction n u)ᴴ * spinAction n u = 1 := by
  have ht : (tensorOp (fun _ : Fin n => u.val))ᴴ * tensorOp (fun _ : Fin n => u.val) = 1 := tensor_unitary n u
  calc
    _ = (dickeIsometry n * spinAction n u)ᴴ *
        (dickeIsometry n * spinAction n u) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (dickeIsometry n)ᴴ (dickeIsometry n), dicke_isometry,
        Matrix.one_mul]
    _ = (tensorOp (fun _ : Fin n => u.val) * dickeIsometry n)ᴴ *
        (tensorOp (fun _ : Fin n => u.val) * dickeIsometry n) := by
      rw [tensor_preserves_symmetric]
    _ = (dickeIsometry n)ᴴ * ((tensorOp (fun _ : Fin n => u.val))ᴴ * tensorOp (fun _ : Fin n => u.val)) *
        dickeIsometry n := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [ht, Matrix.mul_one, dicke_isometry]

set_option maxHeartbeats 2000000 in
-- The three axes are checked on nine Dicke weights and nine input coordinates.
private lemma dicke_collective (a : Fin 3) :
    collectiveSpin 8 a * dickeIsometry 8 =
      dickeIsometry 8 * (![Jx 8, Jy 8, Jz 8] a) := by
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by positivity)]; norm_num
  have h14 : Real.sqrt 14 = Real.sqrt 2 * Real.sqrt 7 := by rw [← Real.sqrt_mul (by positivity)]; norm_num
  have h18 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
    rw [show (18 : ℝ) = 9 * 2 by norm_num, Real.sqrt_mul (by positivity)]; norm_num
  have h20 : Real.sqrt 20 = 2 * Real.sqrt 5 := by
    rw [show (20 : ℝ) = 4 * 5 by norm_num, Real.sqrt_mul (by positivity)]; norm_num
  have h28 : Real.sqrt 28 = 2 * Real.sqrt 7 := by
    rw [show (28 : ℝ) = 4 * 7 by norm_num, Real.sqrt_mul (by positivity)]; norm_num
  have h56 : Real.sqrt 56 = 2 * Real.sqrt 2 * Real.sqrt 7 := by
    rw [show (56 : ℝ) = 4 * (2 * 7) by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    norm_num
    ring
  have h70 : Real.sqrt 70 = Real.sqrt 2 * Real.sqrt 5 * Real.sqrt 7 := by
    rw [show (70 : ℝ) = (2 * 5) * 7 by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  ext x r
  have he (k : Fin 8) :
      (D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k
        (pauli a) * dickeIsometry 8) x r =
      ∑ b : Fin 2, pauli a (x k) b * dickeIsometry 8 (Function.update x k b) r :=
    local_action k (pauli a) (fun y => dickeIsometry 8 y r) x
  simp only [collectiveSpin, Matrix.smul_mul, Matrix.sum_mul, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul]
  simp_rw [he]
  rw [dicke_site_sum]
  rw [dickeCoefficient]
  have hwle := weight_le 8 x
  generalize hw : (∑ k, (x k).val) = w at *
  dsimp only [Jx, Jy, Jz]
  fin_cases a <;> fin_cases r <;> interval_cases w <;>
    norm_num [pauli,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
      dickeCoefficient, dickeIsometry, hw, Matrix.mul_apply, Fin.sum_univ_succ, Nat.choose,
      Jplus, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.conj_ofReal, h8, h14, h18, h20, h28, h56, h70] <;>
    field_simp (disch := first | norm_num | (norm_cast <;> positivity)) <;> (try ring_nf) <;>
    norm_num [← Complex.ofReal_pow, Real.sq_sqrt] <;> (try ring) <;>
    norm_num [starRingEnd_apply]

private lemma collective_rotation (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ r : Matrix (Fin 3) (Fin 3) ℝ, rᵀ * r = 1 ∧
      ∀ a : Fin 3,
        spinAction 8 u * (![Jx 8, Jy 8, Jz 8] a) * (spinAction 8 u)ᴴ =
          ∑ c : Fin 3, (r a c : ℂ) • (![Jx 8, Jy 8, Jz 8] c) := by
  obtain ⟨r, hr, hpauli⟩ := pauli_rotation u
  refine ⟨r, hr, ?_⟩
  have ht : (tensorOp (fun _ : Fin 8 => u.val))ᴴ * tensorOp (fun _ : Fin 8 => u.val) = 1 := tensor_unitary 8 u
  have hd : spinAction 8 u * (spinAction 8 u)ᴴ = 1 :=
    mul_eq_one_comm.mp (spin_action_unitary 8 u)
  have hi : (tensorOp (fun _ : Fin 8 => u.val))ᴴ * dickeIsometry 8 =
      dickeIsometry 8 * (spinAction 8 u)ᴴ := by
    calc
      _ = (tensorOp (fun _ : Fin 8 => u.val))ᴴ * (dickeIsometry 8 * spinAction 8 u) *
          (spinAction 8 u)ᴴ := by simp only [Matrix.mul_assoc, hd, Matrix.mul_one]
      _ = (tensorOp (fun _ : Fin 8 => u.val))ᴴ * (tensorOp (fun _ : Fin 8 => u.val) * dickeIsometry 8) *
          (spinAction 8 u)ᴴ := by rw [tensor_preserves_symmetric]
      _ = _ := by rw [← Matrix.mul_assoc _ _ (dickeIsometry 8), ht, Matrix.one_mul]
  have hc (a : Fin 3) : (dickeIsometry 8)ᴴ * collectiveSpin 8 a *
      dickeIsometry 8 = ![Jx 8, Jy 8, Jz 8] a := by
    rw [Matrix.mul_assoc, dicke_collective, ← Matrix.mul_assoc,
      dicke_isometry, Matrix.one_mul]
  intro a
  have hrot : tensorOp (fun _ : Fin 8 => u.val) * collectiveSpin 8 a * (tensorOp (fun _ : Fin 8 => u.val))ᴴ =
      ∑ c : Fin 3, (r a c : ℂ) • collectiveSpin 8 c :=
    collective_tensor_rotation 8 u r hpauli a
  calc
    _ = (dickeIsometry 8)ᴴ * tensorOp (fun _ : Fin 8 => u.val) *
        (dickeIsometry 8 * (![Jx 8, Jy 8, Jz 8] a)) * (spinAction 8 u)ᴴ := by
      change ((dickeIsometry 8)ᴴ * tensorOp (fun _ : Fin 8 => u.val) * dickeIsometry 8) * _ * _ = _
      simp only [Matrix.mul_assoc]
    _ = (dickeIsometry 8)ᴴ *
        (tensorOp (fun _ : Fin 8 => u.val) * collectiveSpin 8 a * (tensorOp (fun _ : Fin 8 => u.val))ᴴ) *
          dickeIsometry 8 := by
      rw [← dicke_collective]
      simp only [Matrix.mul_assoc]
      rw [← hi]
    _ = _ := by
      rw [hrot]
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hc]

private lemma channel_covariant (u : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (x : Matrix (Fin 9) (Fin 9) ℂ) :
    witnessChannel (spinAction 8 u * x * (spinAction 8 u)ᴴ) =
      spinAction 8 u * witnessChannel x * (spinAction 8 u)ᴴ := by
  obtain ⟨r, hr, hj⟩ := collective_rotation u
  let q : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
    Matrix.kronecker (r.map Complex.ofReal) (r.map Complex.ofReal)
  have hrc : (r.map Complex.ofReal)ᵀ * r.map Complex.ofReal = 1 := by
    have h := congrArg (fun m : Matrix (Fin 3) (Fin 3) ℝ => m.map Complex.ofRealHom) hr
    rw [Matrix.map_mul, Matrix.transpose_map,
      Matrix.map_one Complex.ofRealHom (map_zero _) (map_one _)] at h
    exact h
  have hq : qᵀ * q = 1 := by
    dsimp only [q, Matrix.kronecker]
    rw [← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, hrc]
    exact Matrix.one_kronecker_one
  have hs (ab : Fin 3 × Fin 3) : spinAction 8 u * quadrupole ab.1 ab.2 *
      (spinAction 8 u)ᴴ = ∑ ce : Fin 3 × Fin 3,
        q ab ce • quadrupole ce.1 ce.2 := by
    dsimp only [q, Matrix.kronecker, Matrix.kroneckerMap]
    simpa only [quadrupole, Fintype.sum_prod_type, Matrix.of_apply, Matrix.map_apply] using
      quadratic_rotation (spinAction 8 u) (spin_action_unitary 8 u) r hr
        (![Jx 8, Jy 8, Jz 8]) hj (20 / 3) ab.1 ab.2
  have hd : (spinAction 8 u)ᴴ * spinAction 8 u = 1 := spin_action_unitary 8 u
  have hsum : spinAction 8 u *
      (∑ ab : Fin 3 × Fin 3, quadrupole ab.1 ab.2 * x * quadrupole ab.1 ab.2) *
        (spinAction 8 u)ᴴ =
      ∑ ab : Fin 3 × Fin 3, quadrupole ab.1 ab.2 *
        (spinAction 8 u * x * (spinAction 8 u)ᴴ) * quadrupole ab.1 ab.2 := by
    calc
      _ = ∑ ab : Fin 3 × Fin 3,
          (spinAction 8 u * quadrupole ab.1 ab.2 * (spinAction 8 u)ᴴ) *
            (spinAction 8 u * x * (spinAction 8 u)ᴴ) *
              (spinAction 8 u * quadrupole ab.1 ab.2 * (spinAction 8 u)ᴴ) := by
        simp only [Matrix.mul_sum, Matrix.sum_mul]
        apply Finset.sum_congr rfl
        intro ab _
        simp only [Matrix.mul_assoc]
        simp only [← Matrix.mul_assoc (spinAction 8 u)ᴴ (spinAction 8 u), hd,
          Matrix.one_mul]
      _ = _ := by
        simp_rw [hs]
        exact orthogonal_sandwich q hq (fun ab => quadrupole ab.1 ab.2)
          (spinAction 8 u * x * (spinAction 8 u)ᴴ)
  rw [cartesian_channel, cartesian_channel]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simpa only [Fintype.sum_prod_type] using hsum.symm

private lemma witness_channel : IsCovariantChannel (n := 8) witnessChannel := by
  exact ⟨MatrixMap.of_kraus_isCompletelyPositive witnessKraus,
    MatrixMap.IsTracePreserving.of_kraus_isTracePreserving
      witnessKraus witnessKraus kraus_complete, channel_covariant⟩

private lemma split_product (n t : ℕ) (k m : Fin (t + 1))
    (l : Fin (n - t + 1)) (r : Fin (n + 1)) :
    dickeSplit n t (k, l) r * star (dickeSplit n t (m, l) r) =
      if k = m ∧ k.val + l.val = r.val then
        (((t.choose k.val : ℝ) * ((n - t).choose l.val : ℝ) /
          (n.choose r.val : ℝ) : ℝ) : ℂ) else 0 := by
  rw [dickeSplit]
  by_cases hk : k.val + l.val = r.val
  · by_cases hm : m.val + l.val = r.val
    · have hkm : k = m := Fin.ext (by omega)
      subst m
      simp only [dickeSplit, hk, and_self, ite_true, Complex.star_def,
        Complex.conj_ofReal]
      rw [← Complex.ofReal_mul]
      congr 1
      rw [← sq, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    · have hkm : k ≠ m := by intro h; subst m; exact hm hk
      simp [dickeSplit, hk, hm, hkm]
  · simp [dickeSplit, hk]

private lemma split_weight_sum (n t : ℕ) (k : Fin (t + 1)) (r : Fin (n + 1)) :
    (∑ l : Fin (n - t + 1), if k.val + l.val = r.val then
      (t.choose k.val : ℝ) * ((n - t).choose l.val : ℝ) / (n.choose r.val : ℝ)
      else 0) =
      (t.choose k.val : ℝ) * ((n - t).choose (r.val - k.val) : ℝ) /
        (n.choose r.val : ℝ) * (if k.val ≤ r.val then 1 else 0) := by
  by_cases hk : k.val ≤ r.val
  · by_cases hl : r.val - k.val ≤ n - t
    · let l : Fin (n - t + 1) := ⟨r.val - k.val, by omega⟩
      rw [Finset.sum_eq_single l]
      · simp [l, hk, Nat.add_sub_of_le hk]
      · intro b _ hbl
        have hne : k.val + b.val ≠ r.val := by
          intro he
          apply hbl
          apply Fin.ext
          dsimp [l]
          omega
        simp [hne]
      · simp
    · have hc : (n - t).choose (r.val - k.val) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simp only [hc, Nat.cast_zero, mul_zero, zero_div, zero_mul]
      apply Finset.sum_eq_zero
      intro l _
      have hne : k.val + l.val ≠ r.val := by omega
      simp [hne]
  · simp only [hk, ite_false, mul_zero]
    apply Finset.sum_eq_zero
    intro l _
    have hne : k.val + l.val ≠ r.val := by omega
    simp [hne]

private lemma diagonal_reduction (n t : ℕ) (ht : t ≤ n) (p : Fin (n + 1) → ℝ) :
    reducedState t (diagonal (fun r => (p r : ℂ))) =
      diagonal (fun k => ((∑ r : Fin (n + 1), p r *
        (t.choose k.val : ℝ) * ((n - t).choose (r.val - k.val) : ℝ) /
        (n.choose r.val : ℝ) * (if k.val ≤ r.val then 1 else 0) : ℝ) : ℂ)) := by
  have he (k m : Fin (t + 1)) :
      reducedState t (diagonal (fun r => (p r : ℂ))) k m =
        ∑ l : Fin (n - t + 1), ∑ r : Fin (n + 1),
          (p r : ℂ) * (dickeSplit n t (k, l) r * star (dickeSplit n t (m, l) r)) := by
    rw [reducedState_eq_dickeSplit n t ht]
    change (∑ l : Fin (n - t + 1),
      (dickeSplit n t * diagonal (fun r => (p r : ℂ)) * (dickeSplit n t)ᴴ)
        (k, l) (m, l)) = _
    apply Finset.sum_congr rfl
    intro l _
    have h := D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization.diagonal_entry_expansion
      (fun _ : Unit => dickeSplit n t) (fun r => (p r : ℂ)) (k, l) (m, l)
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Fintype.sum_unique] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro r _
    exact mul_comm _ _
  ext k m
  rw [he]
  simp_rw [split_product]
  by_cases hkm : k = m
  · subst m
    simp only [true_and, diagonal_apply_eq]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    push_cast
    congr 1
    funext r
    have hh : p r * (∑ l : Fin (n - t + 1), if k.val + l.val = r.val then
        (t.choose k.val : ℝ) * ((n - t).choose l.val : ℝ) / (n.choose r.val : ℝ)
        else 0) = p r * (t.choose k.val : ℝ) *
          ((n - t).choose (r.val - k.val) : ℝ) / (n.choose r.val : ℝ) *
            (if k.val ≤ r.val then 1 else 0) := by
      rw [split_weight_sum]
      ring
    have hhh := congrArg (fun a : ℝ => (a : ℂ)) hh
    push_cast at hhh
    simpa only [Nat.cast_mul, apply_ite, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_zero, Complex.ofReal_natCast] using hhh
  · simp [hkm, diagonal_apply_ne _ hkm]

private lemma input_reduction : reducedState 7 witnessState =
    diagonal (fun k => (![21, 21, 40, 21, 21, 21, 21, 2] k : ℂ) / 168) := by
  have hp : witnessState = diagonal (fun r : Fin 9 =>
      (((![209, 92, 560, 0, 441, 0, 294, 168, 0] r : ℝ) / 1764 : ℝ) : ℂ)) := by
    unfold witnessState
    congr 1
    funext r
    fin_cases r <;> norm_num
  rw [hp, diagonal_reduction 8 7 (by norm_num)]
  congr 1
  funext k
  fin_cases k <;> norm_num [Fin.sum_univ_succ, Nat.choose]

private lemma output_reduction : reducedState 7 witnessOutput =
    diagonal (fun k =>
      (![69468, 87252, 64205, 82635, 78360, 59892, 43533, 32095] k : ℂ) / 517440) := by
  have hp : witnessOutput = diagonal (fun r : Fin 9 =>
      (((![22288, 30100, 25528, 13149, 45540, 10584, 24654, 11613, 10584] r : ℝ) /
        194040 : ℝ) : ℂ)) := by
    unfold witnessOutput
    congr 1
    funext r
    fin_cases r <;> norm_num
  rw [hp, diagonal_reduction 8 7 (by norm_num)]
  congr 1
  funext k
  fin_cases k <;> norm_num [Fin.sum_univ_succ, Nat.choose]

private lemma input_distance :
    traceNorm (reducedState 7 witnessState - designAverage (7 + 1)) = 19 / 84 := by
  rw [input_reduction]
  have he : diagonal (fun k => (![21, 21, 40, 21, 21, 21, 21, 2] k : ℂ) / 168) -
      designAverage (7 + 1) = diagonal (fun k : Fin 8 =>
        (((![21, 21, 40, 21, 21, 21, 21, 2] k : ℝ) / 168 - 1 / 8 : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      fin_cases i <;> norm_num [designAverage, Matrix.smul_apply, Complex.real_smul]
    · simp [designAverage, Matrix.smul_apply, Complex.real_smul, diagonal_apply, hij]
  rw [he, D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.diagonal_norm]
  norm_num [Fin.sum_univ_succ]

private lemma output_distance :
    traceNorm (reducedState 7 (witnessChannel witnessState) - designAverage (7 + 1)) =
      3933 / 17248 := by
  rw [witness_output, output_reduction]
  have he : diagonal (fun k =>
      (![69468, 87252, 64205, 82635, 78360, 59892, 43533, 32095] k : ℂ) / 517440) -
      designAverage (7 + 1) = diagonal (fun k : Fin 8 =>
        (((![69468, 87252, 64205, 82635, 78360, 59892, 43533, 32095] k : ℝ) /
          517440 - 1 / 8 : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      fin_cases i <;> norm_num [designAverage, Matrix.smul_apply, Complex.real_smul]
    · simp [designAverage, Matrix.smul_apply, Complex.real_smul, diagonal_apply, hij]
  rw [he, D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.diagonal_norm]
  norm_num [Fin.sum_univ_succ]

private lemma normalizer_positive : 0 < normalizer 7 := by
  have hm : (designAverage (7 + 1)).PosSemidef ∧ (designAverage (7 + 1)).trace = 1 := by
    have he : designAverage (7 + 1) = diagonal (fun _ : Fin 8 => (1 / 8 : ℂ)) := by
      rw [designAverage]
      ext i j
      by_cases hij : i = j <;> norm_num [designAverage, Matrix.smul_apply, Complex.real_smul, diagonal_apply, hij]
    rw [he]
    exact ⟨posSemidef_diagonal_iff.mpr (by
      intro i; norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im]), by norm_num⟩
  have hnorm (σ : Matrix (Fin 8) (Fin 8) ℂ) (hσ : σ.PosSemidef) (ht : σ.trace = 1) :
      traceNorm σ = 1 := by
    have h := congrArg Complex.re
      (D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_of_posSemidef hσ)
    simpa [ht] using h
  have hb : BddAbove {d : ℝ | ∃ σ : Matrix (Fin 8) (Fin 8) ℂ,
      σ.PosSemidef ∧ σ.trace = 1 ∧ d = traceNorm (σ - designAverage (7 + 1))} := by
    refine ⟨2, ?_⟩
    rintro d ⟨σ, hσ, ht, rfl⟩
    have h := D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_add_le
      σ (-(designAverage (7 + 1)))
    rw [D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_neg,
      hnorm σ hσ ht, hnorm _ hm.1 hm.2, ← sub_eq_add_neg] at h
    norm_num at h ⊢
    exact h
  let σ : Matrix (Fin 8) (Fin 8) ℂ := diagonal (fun i => if i = 0 then 1 else 0)
  have hσ : σ.PosSemidef ∧ σ.trace = 1 := by
    constructor
    · apply posSemidef_diagonal_iff.mpr
      intro i
      split_ifs <;> norm_num
    · simp [σ]
  have hd : traceNorm (σ - designAverage (7 + 1)) = 7 / 4 := by
    have he : σ - designAverage (7 + 1) = diagonal (fun i : Fin 8 =>
        (((if i = 0 then 1 else 0) - 1 / 8 : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        fin_cases i <;> norm_num [σ, designAverage, Matrix.smul_apply, Complex.real_smul]
      · simp [σ, designAverage, Matrix.smul_apply, Complex.real_smul, diagonal_apply, hij]
    rw [he, D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.diagonal_norm]
    norm_num [Fin.sum_univ_succ]
  have hle : 7 / 4 ≤ normalizer 7 :=
    le_csSup hb ⟨σ, hσ.1, hσ.2, hd.symm⟩
  linarith

theorem result : ¬ claim := by
  intro h
  have hm := h 8 (by norm_num) 7 (by norm_num) (by norm_num)
    witnessChannel witness_channel witnessState witness_state.1 witness_state.2
  change 1 - traceNorm (reducedState 7 witnessState - designAverage (7 + 1)) / normalizer 7 ≤
    1 - traceNorm (reducedState 7 (witnessChannel witnessState) - designAverage (7 + 1)) /
      normalizer 7 at hm
  rw [input_distance, output_distance] at hm
  have hlt : (19 / 84 : ℝ) / normalizer 7 < (3933 / 17248 : ℝ) / normalizer 7 :=
    (div_lt_div_iff_of_pos_right normalizer_positive).2 (by norm_num)
  linarith
end D5.S3.Quantum.Measurement.AnticoherenceTraceDistanceRefutation
