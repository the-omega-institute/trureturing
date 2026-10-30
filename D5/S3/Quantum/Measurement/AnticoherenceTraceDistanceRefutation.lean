/- GID: D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.claim; result=D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.result; claim=D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.claim
   digest: A spin-four covariant channel lowers order-seven trace-distance anticoherence. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
import D5.S3.Quantum.Measurement.AnticoherenceCovariantChannel
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability

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
open Matrix
open D5.S3.Quantum.Measurement.AnticoherenceCovariantChannel
  (witnessState witnessKraus witnessChannel quadrupole witnessOutput
    kraus_complete witness_state witness_output)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (Jplus Jx Jy Jz)

/-- The tensor power in the computational basis of `n` qubits. -/
def qubitPower (n : ℕ) (u : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun x y => ∏ k, u (x k) (y k)

/-- The normalized Dicke embedding; the spin index counts qubits in state one. -/
def dickeIsometry (n : ℕ) : Matrix (Fin n → Fin 2) (Fin (n + 1)) ℂ :=
  fun x r => if (∑ k, (x k).val) = r.val then
    (Real.sqrt (n.choose r.val : ℝ) : ℂ)⁻¹ else 0

/-- The spin-`n/2` representation obtained by restricting the qubit tensor power. -/
def spinAction (n : ℕ) (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (dickeIsometry n)ᴴ * qubitPower n u.val * dickeIsometry n

/-- The Dicke splitting coefficients for the first `t` and last `n-t` qubits. -/
def dickeSplit (n t : ℕ) :
    Matrix (Fin (t + 1) × Fin (n - t + 1)) (Fin (n + 1)) ℂ :=
  fun kl r => if kl.1.val + kl.2.val = r.val then
    ((Real.sqrt ((t.choose kl.1.val : ℝ) * ((n - t).choose kl.2.val : ℝ)) /
      Real.sqrt (n.choose r.val : ℝ) : ℝ) : ℂ) else 0

/-- The qubit partial trace, expressed in the normalized `t`-qubit Dicke basis. -/
def reducedState {n : ℕ} (t : ℕ) (ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ :=
  partialTraceRight (dickeSplit n t * ρ * (dickeSplit n t)ᴴ)

/-- The maximally mixed state on the symmetric `t`-qubit subspace. -/
def mixedState (t : ℕ) : Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ :=
  (1 / ((t : ℂ) + 1)) • 1

/-- The source's maximum trace distance over all states of spin `t/2`. -/
def normalizer (t : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ σ : Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ,
    σ.PosSemidef ∧ σ.trace = 1 ∧ d = traceNorm (σ - mixedState t)}

/-- The distance-based total anticoherence measure for Schatten exponent one. -/
def anticoherence {n : ℕ} (t : ℕ)
    (ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℝ :=
  1 - traceNorm (reducedState t ρ - mixedState t) / normalizer t

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

private lemma dicke_count (n k : ℕ) :
    (∑ x : Fin n → Fin 2, if (∑ i, (x i).val) = k then (1 : ℂ) else 0) =
      (n.choose k : ℂ) := by
  have hp : (∏ _i : Fin n, ∑ b : Fin 2, (Polynomial.X : ℂ[X]) ^ b.val) =
      (1 + Polynomial.X) ^ n := by simp [Fin.sum_univ_two]
  rw [Fintype.prod_sum] at hp
  simp_rw [Finset.prod_pow_eq_pow_sum] at hp
  have h := congrArg (fun p : ℂ[X] => p.coeff k) hp
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, eq_comm,
    Polynomial.coeff_one_add_X_pow] using h

private lemma dicke_isometry (n : ℕ) : (dickeIsometry n)ᴴ * dickeIsometry n = 1 := by
  ext r s
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  by_cases hrs : r = s
  · subst s
    have hs : (Real.sqrt (n.choose r.val : ℝ) : ℂ) ^ 2 = (n.choose r.val : ℂ) := by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (n.choose r.val))
    have hn : (n.choose r.val : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : r.val ≤ n)).ne'
    have he (x : Fin n → Fin 2) :
        star (dickeIsometry n x r) * dickeIsometry n x r =
          (if (∑ i, (x i).val) = r.val then (1 : ℂ) else 0) /
            (n.choose r.val : ℂ) := by
      by_cases hx : (∑ i, (x i).val) = r.val
      · simp only [dickeIsometry, hx, ite_true, Complex.star_def, map_inv₀,
          Complex.conj_ofReal]
        rw [← mul_inv, ← sq, hs, one_div]
      · simp [dickeIsometry, hx]
    simp_rw [he]
    rw [← Finset.sum_div, dicke_count, div_self hn]
    simp
  · rw [Matrix.one_apply_ne hrs]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hr : (∑ i, (x i).val) = r.val
    · have hs : (∑ i, (x i).val) ≠ s.val := by
        intro hs
        exact hrs (Fin.ext (hr.symm.trans hs))
      simp [dickeIsometry, hr, hs]
    · simp [dickeIsometry, hr]

private lemma weight_card (n : ℕ) (x : Fin n → Fin 2) :
    (∑ i, (x i).val) = (Finset.univ.filter (fun i => x i = 1)).card := by
  calc
    _ = ∑ i : Fin n, if x i = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      fin_cases hx : x i <;> simp [hx]
    _ = _ := by rw [Finset.sum_boole]

private lemma weight_le (n : ℕ) (x : Fin n → Fin 2) : (∑ i, (x i).val) ≤ n := by
  rw [weight_card]
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

private lemma same_weight_permutation (n : ℕ) (x y : Fin n → Fin 2)
    (h : (∑ i, (x i).val) = ∑ i, (y i).val) :
    ∃ σ : Equiv.Perm (Fin n), y ∘ σ = x := by
  have hc : (Finset.univ.filter (fun i => x i = 1)).card =
      (Finset.univ.filter (fun i => y i = 1)).card := by
    rw [← weight_card, ← weight_card, h]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq _ _ hc
  refine ⟨σ, ?_⟩
  funext i
  have hm : y (σ i) = 1 ↔ x i = 1 := by
    have he : σ i ∈ Finset.univ.filter (fun i => y i = 1) ↔
        i ∈ Finset.univ.filter (fun i => x i = 1) := by rw [← hσ]; simp
    simpa using he
  change y (σ i) = x i
  fin_cases hx : x i <;> fin_cases hy : y (σ i) <;> simp_all

private lemma tensor_weight_constant (n : ℕ) (u : Matrix (Fin 2) (Fin 2) ℂ)
    (x y : Fin n → Fin 2) (r : Fin (n + 1))
    (h : (∑ i, (x i).val) = ∑ i, (y i).val) :
    (qubitPower n u * dickeIsometry n) x r =
      (qubitPower n u * dickeIsometry n) y r := by
  have hp (σ : Equiv.Perm (Fin n)) (x : Fin n → Fin 2) :
      (qubitPower n u * dickeIsometry n) (x ∘ σ) r =
        (qubitPower n u * dickeIsometry n) x r := by
    let e := Equiv.arrowCongr σ.symm (Equiv.refl (Fin 2))
    rw [Matrix.mul_apply, Matrix.mul_apply]
    calc
      _ = ∑ z : Fin n → Fin 2,
          qubitPower n u (x ∘ σ) (z ∘ σ) * dickeIsometry n (z ∘ σ) r :=
        (e.sum_comp (fun z => qubitPower n u (x ∘ σ) z * dickeIsometry n z r)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z _
        have hw : (∑ i, (z (σ i)).val) = ∑ i, (z i).val := σ.sum_comp _
        have hu : qubitPower n u (x ∘ σ) (z ∘ σ) = qubitPower n u x z :=
          σ.prod_comp (fun i => u (x i) (z i))
        simp only [hu, dickeIsometry, Function.comp_apply, hw]
  obtain ⟨σ, hσ⟩ := same_weight_permutation n x y h
  rw [← hσ]
  exact hp σ y

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
      simp only [Matrix.conjTranspose_apply, dickeIsometry, r, ite_true, hy,
        hxy, Complex.star_def, map_inv₀, Complex.conj_ofReal]
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
    qubitPower n u.val * dickeIsometry n = dickeIsometry n * spinAction n u := by
  have hp : (dickeIsometry n * (dickeIsometry n)ᴴ) *
      (qubitPower n u.val * dickeIsometry n) = qubitPower n u.val * dickeIsometry n := by
    ext x r
    rw [Matrix.mul_apply]
    simp_rw [dicke_projector_entry]
    have he (y : Fin n → Fin 2) :
        (if (∑ i, (x i).val) = ∑ i, (y i).val then
          (n.choose (∑ i, (x i).val) : ℂ)⁻¹ else 0) *
            (qubitPower n u.val * dickeIsometry n) y r =
        (if (∑ i, (y i).val) = ∑ i, (x i).val then (1 : ℂ) else 0) *
          ((n.choose (∑ i, (x i).val) : ℂ)⁻¹ *
            (qubitPower n u.val * dickeIsometry n) x r) := by
      by_cases hxy : (∑ i, (x i).val) = ∑ i, (y i).val
      · rw [if_pos hxy, if_pos hxy.symm, one_mul,
          tensor_weight_constant n u.val y x r hxy.symm]
      · simp [hxy, Ne.symm hxy]
    simp_rw [he]
    rw [← Finset.sum_mul, dicke_count]
    have hn : (n.choose (∑ i, (x i).val) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (weight_le n x)).ne'
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  simpa only [spinAction, Matrix.mul_assoc] using hp.symm

private lemma dicke_split_partialTrace (t s : ℕ)
    (ρ : Matrix (Fin (t + s + 1)) (Fin (t + s + 1)) ℂ) :
    let v := dickeIsometry (t + s)
    let w := fun xy : (Fin t → Fin 2) × (Fin s → Fin 2) =>
      Fin.append xy.1 xy.2
    partialTraceRight ((v * ρ * vᴴ).submatrix w w) =
      dickeIsometry t * reducedState t ρ * (dickeIsometry t)ᴴ := by
  sorry

private lemma cartesian_channel (x : Matrix (Fin 9) (Fin 9) ℂ) :
    witnessChannel x = (3 / 770 : ℂ) •
      ∑ a : Fin 3, ∑ b : Fin 3, quadrupole a b * x * quadrupole a b := by
  sorry

private lemma collective_rotation (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ r : Matrix (Fin 3) (Fin 3) ℝ, rᵀ * r = 1 ∧
      ∀ a : Fin 3,
        spinAction 8 u * (![Jx 8, Jy 8, Jz 8] a) * (spinAction 8 u)ᴴ =
          ∑ c : Fin 3, (r a c : ℂ) • (![Jx 8, Jy 8, Jz 8] c) := by
  sorry

private lemma channel_covariant (u : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (x : Matrix (Fin 9) (Fin 9) ℂ) :
    witnessChannel (spinAction 8 u * x * (spinAction 8 u)ᴴ) =
      spinAction 8 u * witnessChannel x * (spinAction 8 u)ᴴ := by
  sorry

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
    change (∑ l : Fin (n - t + 1),
      (dickeSplit n t * diagonal (fun r => (p r : ℂ)) * (dickeSplit n t)ᴴ)
        (k, l) (m, l)) = _
    apply Finset.sum_congr rfl
    intro l _
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro r _
    ring
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
    exact_mod_cast hh
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
    traceNorm (reducedState 7 witnessState - mixedState 7) = 19 / 84 := by
  rw [input_reduction]
  have he : diagonal (fun k => (![21, 21, 40, 21, 21, 21, 21, 2] k : ℂ) / 168) -
      mixedState 7 = diagonal (fun k : Fin 8 =>
        (((![21, 21, 40, 21, 21, 21, 21, 2] k : ℝ) / 168 - 1 / 8 : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      fin_cases i <;> norm_num [mixedState]
    · simp [mixedState, diagonal_apply, hij]
  rw [he, D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.diagonal_norm]
  norm_num [Fin.sum_univ_succ]

private lemma output_distance :
    traceNorm (reducedState 7 (witnessChannel witnessState) - mixedState 7) =
      3933 / 17248 := by
  rw [witness_output, output_reduction]
  have he : diagonal (fun k =>
      (![69468, 87252, 64205, 82635, 78360, 59892, 43533, 32095] k : ℂ) / 517440) -
      mixedState 7 = diagonal (fun k : Fin 8 =>
        (((![69468, 87252, 64205, 82635, 78360, 59892, 43533, 32095] k : ℝ) /
          517440 - 1 / 8 : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      fin_cases i <;> norm_num [mixedState]
    · simp [mixedState, diagonal_apply, hij]
  rw [he, D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.diagonal_norm]
  norm_num [Fin.sum_univ_succ]

private lemma normalizer_positive : 0 < normalizer 7 := by
  have hm : (mixedState 7).PosSemidef ∧ (mixedState 7).trace = 1 := by
    have he : mixedState 7 = diagonal (fun _ : Fin 8 => (1 / 8 : ℂ)) := by
      ext i j
      by_cases hij : i = j <;> norm_num [mixedState, diagonal_apply, hij]
    rw [he]
    exact ⟨posSemidef_diagonal_iff.mpr (by
      intro i; norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im]), by norm_num⟩
  have hnorm (σ : Matrix (Fin 8) (Fin 8) ℂ) (hσ : σ.PosSemidef) (ht : σ.trace = 1) :
      traceNorm σ = 1 := by
    have h := congrArg Complex.re
      (D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_of_posSemidef hσ)
    simpa [ht] using h
  have hb : BddAbove {d : ℝ | ∃ σ : Matrix (Fin 8) (Fin 8) ℂ,
      σ.PosSemidef ∧ σ.trace = 1 ∧ d = traceNorm (σ - mixedState 7)} := by
    refine ⟨2, ?_⟩
    rintro d ⟨σ, hσ, ht, rfl⟩
    have h := D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_add_le
      σ (-(mixedState 7))
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
  have hd : traceNorm (σ - mixedState 7) = 7 / 4 := by
    have he : σ - mixedState 7 = diagonal (fun i : Fin 8 =>
        (((if i = 0 then 1 else 0) - 1 / 8 : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        fin_cases i <;> norm_num [σ, mixedState]
      · simp [σ, mixedState, diagonal_apply, hij]
    rw [he, D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.diagonal_norm]
    norm_num [Fin.sum_univ_succ]
  have hle : 7 / 4 ≤ normalizer 7 :=
    le_csSup hb ⟨σ, hσ.1, hσ.2, hd.symm⟩
  linarith

theorem result : ¬ claim := by
  intro h
  have hm := h 8 (by norm_num) 7 (by norm_num) (by norm_num)
    witnessChannel witness_channel witnessState witness_state.1 witness_state.2
  change 1 - traceNorm (reducedState 7 witnessState - mixedState 7) / normalizer 7 ≤
    1 - traceNorm (reducedState 7 (witnessChannel witnessState) - mixedState 7) /
      normalizer 7 at hm
  rw [input_distance, output_distance] at hm
  have hlt : (19 / 84 : ℝ) / normalizer 7 < (3933 / 17248 : ℝ) / normalizer 7 :=
    (div_lt_div_iff_of_pos_right normalizer_positive).2 (by norm_num)
  linarith

end D5.S3.Quantum.Measurement.AnticoherenceTraceDistanceRefutation
