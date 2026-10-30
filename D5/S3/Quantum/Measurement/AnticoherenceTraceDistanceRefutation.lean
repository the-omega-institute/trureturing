/- GID: D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.claim; result=D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.result; claim=D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.claim
   digest: A spin-four covariant channel lowers order-seven trace-distance anticoherence. -/

import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
import D5.S3.Quantum.Measurement.AnticoherenceCovariantChannel
import D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
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
open D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
  (pauliAxes pauli_rotation tensor_unitary quadratic_rotation orthogonal_sandwich
    local_action collectiveSpin collective_tensor_rotation)

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
  have hp : (∏ _i : Fin n, ∑ b : Fin 2, (Polynomial.X : Polynomial ℂ) ^ b.val) =
      (1 + Polynomial.X) ^ n := by simp [Fin.sum_univ_two]
  rw [Fintype.prod_sum] at hp
  simp_rw [Finset.prod_pow_eq_pow_sum] at hp
  have h := congrArg (fun p : Polynomial ℂ => p.coeff k) hp
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
      have hrsval : r.val ≠ s.val := fun he => hrs (Fin.ext he)
      simp [dickeIsometry, hr, hrsval]
    · simp only [dickeIsometry, hr, ite_false, star_zero, zero_mul]

private lemma weight_card (n : ℕ) (x : Fin n → Fin 2) :
    (∑ i, (x i).val) = (Finset.univ.filter (fun i => x i = 1)).card := by
  calc
    _ = ∑ i : Fin n, if x i = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      generalize hx : x i = b
      fin_cases b <;> simp
    _ = _ := by simpa using (Finset.sum_boole (Finset.univ : Finset (Fin n)) (fun i => x i = 1))

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
  generalize hx : x i = b at *
  generalize hy : y (σ i) = c at *
  fin_cases b <;> fin_cases c <;> simp_all

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
        have hw : (∑ i, (z (σ i)).val) = ∑ i, (z i).val :=
          Equiv.sum_comp σ (fun i => (z i).val)
        have hu : qubitPower n u (x ∘ σ) (z ∘ σ) = qubitPower n u x z :=
          Equiv.prod_comp σ (fun i => u (x i) (z i))
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

private def dickeSplitSum (t s : ℕ) :
    Matrix (Fin (t + 1) × Fin (s + 1)) (Fin (t + s + 1)) ℂ :=
  fun kl r => if kl.1.val + kl.2.val = r.val then
    ((Real.sqrt ((t.choose kl.1.val : ℝ) * (s.choose kl.2.val : ℝ)) /
      Real.sqrt ((t + s).choose r.val : ℝ) : ℝ) : ℂ) else 0

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
  · simp only [Matrix.submatrix_apply, id_eq, Matrix.kronecker, Matrix.kroneckerMap,
      Matrix.of_apply, dickeIsometry,
      hw, show (∑ i, (x i).val) = k.val from rfl,
      show (∑ i, (y i).val) = l.val from rfl, ite_true, dickeSplitSum,
      Nat.add_sub_cancel_left]
    by_cases h : k.val + l.val = r.val
    · rw [if_pos h, if_pos h, Real.sqrt_mul (by positivity)]
      have hk : Real.sqrt (t.choose k.val : ℝ) ≠ 0 :=
        (Real.sqrt_pos.2 (by exact_mod_cast Nat.choose_pos (by omega : k.val ≤ t))).ne'
      have hl : Real.sqrt (s.choose l.val : ℝ) ≠ 0 :=
        (Real.sqrt_pos.2 (by exact_mod_cast Nat.choose_pos (by omega : l.val ≤ s))).ne'
      push_cast
      field_simp [hk, hl]
    · simp [h]
  · rintro ⟨a, b⟩ _ hab
    by_cases ha : a = k
    · have hb : (∑ i, (y i).val) ≠ b.val := by
        intro hb
        exact hab (Prod.ext ha (Fin.ext hb.symm))
      simp [Matrix.kronecker, Matrix.kroneckerMap, dickeIsometry, hb]
    · have hx : (∑ i, (x i).val) ≠ a.val := by
        intro hx
        exact ha (Fin.ext hx.symm)
      simp [Matrix.kronecker, Matrix.kroneckerMap, dickeIsometry, hx]
  · simp

set_option backward.isDefEq.respectTransparency false in
private lemma partialTrace_isometries {a b i j : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    [DecidableEq j] (v : Matrix a i ℂ) (w : Matrix b j ℂ)
    (hw : wᴴ * w = 1) (z : Matrix (i × j) (i × j) ℂ) :
    partialTraceRight (Matrix.kronecker v w * z * (Matrix.kronecker v w)ᴴ) =
      v * partialTraceRight z * vᴴ := by
  have hb (k l : j) : (∑ d : b, w d k * star (w d l)) = if k = l then 1 else 0 := by
    have h := congrFun (congrFun hw l) k
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      mul_comm, eq_comm] using h
  ext x y
  simp only [partialTraceRight, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, Fintype.sum_prod_type, star_mul]
  simp_rw [Finset.sum_mul]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext k
    rw [Finset.sum_comm]
    arg 2
    ext l
    rw [Finset.sum_comm]
    arg 2
    ext m
    rw [Finset.sum_comm]
  have he (k m : i) (l n : j) :
      (∑ d : b, v x m * w d n * z (m, n) (k, l) *
        (star (w d l) * star (v y k))) =
      v x m * z (m, l) (k, l) * star (v y k) * (if n = l then 1 else 0) := by
    calc
      _ = (v x m * z (m, n) (k, l) * star (v y k)) *
          (∑ d : b, w d n * star (w d l)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
      _ = _ := by rw [hb]; split_ifs with h <;> simp_all
  simp_rw [he]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

set_option backward.isDefEq.respectTransparency false in
private lemma dicke_split_partialTrace (t s : ℕ)
    (ρ : Matrix (Fin (t + s + 1)) (Fin (t + s + 1)) ℂ) :
    let v := dickeIsometry (t + s)
    let w := fun xy : (Fin t → Fin 2) × (Fin s → Fin 2) =>
      Fin.append xy.1 xy.2
    partialTraceRight ((v * ρ * vᴴ).submatrix w w) =
      dickeIsometry t * reducedState t ρ * (dickeIsometry t)ᴴ := by
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
  have hd : partialTraceRight (dickeSplitSum t s * ρ * (dickeSplitSum t s)ᴴ) =
      reducedState t ρ := by
    let v (m : ℕ) : Matrix (Fin (t + 1) × Fin (m + 1)) (Fin (t + s + 1)) ℂ :=
      fun kl r => if kl.1.val + kl.2.val = r.val then
        ((Real.sqrt ((t.choose kl.1.val : ℝ) * (m.choose kl.2.val : ℝ)) /
          Real.sqrt ((t + s).choose r.val : ℝ) : ℝ) : ℂ) else 0
    change partialTraceRight (v s * ρ * (v s)ᴴ) =
      partialTraceRight (v (t + s - t) * ρ * (v (t + s - t))ᴴ)
    exact congrArg (fun m => partialTraceRight (v m * ρ * (v m)ᴴ))
      (Nat.add_sub_cancel_left t s).symm
  rw [hd]

set_option maxHeartbeats 1000000 in
-- The ladder Casimir identity is diagonal on nine coordinates.
private lemma ladder_casimir :
    Jplus 8 * (Jplus 8)ᴴ + (Jplus 8)ᴴ * Jplus 8 =
      (40 : ℂ) • 1 - (2 : ℂ) • (Jz 8 * Jz 8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Jplus, Jz, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_ofReal] <;>
    ring_nf <;> norm_num [← Complex.ofReal_pow, Real.sq_sqrt]

private lemma quadrupole_tracefree :
    quadrupole 0 0 + quadrupole 1 1 = -quadrupole 2 2 := by
  simp only [quadrupole, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Fin.isValue, ite_true, Jx, Jy]
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
    simp only [witnessKraus, quadrupole, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons, Fin.isValue, Jx, Jy] <;>
    norm_num [div_eq_mul_inv] <;>
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, smul_smul] <;>
    match_scalars <;> ring_nf <;> norm_num [Complex.I_sq] <;> ring

private lemma quadrupole_adjoint (a b : Fin 3) :
    (quadrupole a b)ᴴ = quadrupole a b := by
  have hz : (Jz 8)ᴴ = Jz 8 := by simp [Jz]
  fin_cases a <;> fin_cases b <;>
    simp [quadrupole, Jx, Jy, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
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
  have ht : (qubitPower n u.val)ᴴ * qubitPower n u.val = 1 := tensor_unitary n u
  calc
    _ = (dickeIsometry n * spinAction n u)ᴴ *
        (dickeIsometry n * spinAction n u) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (dickeIsometry n)ᴴ (dickeIsometry n), dicke_isometry,
        Matrix.one_mul]
    _ = (qubitPower n u.val * dickeIsometry n)ᴴ *
        (qubitPower n u.val * dickeIsometry n) := by
      rw [tensor_preserves_symmetric]
    _ = (dickeIsometry n)ᴴ * ((qubitPower n u.val)ᴴ * qubitPower n u.val) *
        dickeIsometry n := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [ht, Matrix.mul_one, dicke_isometry]

private def dickeCoefficient (n w r : ℕ) : ℂ :=
  if w = r then (Real.sqrt (n.choose r : ℝ) : ℂ)⁻¹ else 0

private lemma two_value_sum (n : ℕ) (x : Fin n → Fin 2) (f : Fin 2 → ℂ) :
    (∑ k, f (x k)) = ((n : ℂ) - (∑ k, (x k).val : ℕ)) * f 0 +
      (∑ k, (x k).val : ℕ) * f 1 := by
  have he (b : Fin 2) : f b = f 0 + (b.val : ℂ) * (f 1 - f 0) := by
    fin_cases b <;> norm_num
  calc
    _ = ∑ k : Fin n, (f 0 + ((x k).val : ℂ) * (f 1 - f 0)) :=
      Finset.sum_congr rfl (fun k _ => he (x k))
    _ = _ := ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

private lemma dicke_site_sum (n : ℕ) (a : Matrix (Fin 2) (Fin 2) ℂ)
    (x : Fin n → Fin 2) (r : Fin (n + 1)) :
    (∑ k : Fin n, ∑ b : Fin 2, a (x k) b *
      dickeIsometry n (Function.update x k b) r) =
      ((n : ℂ) - (∑ k, (x k).val : ℕ)) *
        (a 0 0 * dickeCoefficient n (∑ k, (x k).val) r.val +
          a 0 1 * dickeCoefficient n ((∑ k, (x k).val) + 1) r.val) +
      (∑ k, (x k).val : ℕ) *
        (a 1 0 * dickeCoefficient n ((∑ k, (x k).val) - 1) r.val +
          a 1 1 * dickeCoefficient n (∑ k, (x k).val) r.val) := by
  let w := ∑ k, (x k).val
  have hu (k : Fin n) (b : Fin 2) :
      (∑ i, (Function.update x k b i).val) + (x k).val = w + b.val := by
    have he : (fun i => (Function.update x k b i).val) =
        Function.update (fun i => (x i).val) k b.val := by
      funext i
      by_cases hi : i = k <;> simp [Function.update_apply, hi]
    rw [he, Finset.sum_update_of_mem (Finset.mem_univ k)]
    simp only [Finset.sdiff_singleton_eq_erase]
    have h := Finset.add_sum_erase Finset.univ (fun i => (x i).val) (Finset.mem_univ k)
    dsimp only [w]
    omega
  let f : Fin 2 → ℂ :=
    ![a 0 0 * dickeCoefficient n w r.val + a 0 1 * dickeCoefficient n (w + 1) r.val,
      a 1 0 * dickeCoefficient n (w - 1) r.val + a 1 1 * dickeCoefficient n w r.val]
  have hf (k : Fin n) : (∑ b : Fin 2, a (x k) b *
      dickeIsometry n (Function.update x k b) r) = f (x k) := by
    have h0 := hu k 0
    have h1 := hu k 1
    by_cases hk : x k = 0
    · have hz : (∑ i, (Function.update x k 0 i).val) = w := by simp [hk] at h0; omega
      have ho : (∑ i, (Function.update x k 1 i).val) = w + 1 := by simp [hk] at h1; omega
      simp [Fin.sum_univ_two, dickeIsometry, hz, ho, f, hk, dickeCoefficient]
    · have hk1 : x k = 1 := Fin.ext (by have hh := (x k).isLt; omega)
      have hz : (∑ i, (Function.update x k 0 i).val) = w - 1 := by simp [hk1] at h0; omega
      have ho : (∑ i, (Function.update x k 1 i).val) = w := by simp [hk1] at h1; omega
      simp [Fin.sum_univ_two, dickeIsometry, hz, ho, f, hk1, dickeCoefficient]
  simp_rw [hf]
  simpa only [f, Matrix.cons_val_zero, Matrix.cons_val_one] using two_value_sum n x f

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
        (pauliAxes a) * dickeIsometry 8) x r =
      ∑ b : Fin 2, pauliAxes a (x k) b * dickeIsometry 8 (Function.update x k b) r :=
    local_action k (pauliAxes a) (fun y => dickeIsometry 8 y r) x
  simp only [collectiveSpin, Matrix.smul_mul, Matrix.sum_mul, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul]
  simp_rw [he]
  rw [dicke_site_sum]
  have hwle := weight_le 8 x
  generalize hw : (∑ k, (x k).val) = w at *
  fin_cases a <;> fin_cases r <;> interval_cases w <;>
    norm_num [pauliAxes,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
      dickeCoefficient, dickeIsometry, hw, Matrix.mul_apply, Fin.sum_univ_succ, Nat.choose,
      Jx, Jy, Jplus, Jz, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.conj_ofReal, h8, h14, h18, h20, h28, h56, h70] <;>
    field_simp <;> (try ring_nf) <;>
    norm_num [← Complex.ofReal_pow, Real.sq_sqrt] <;> (try ring) <;>
    norm_num [starRingEnd_apply]

private lemma collective_rotation (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ r : Matrix (Fin 3) (Fin 3) ℝ, rᵀ * r = 1 ∧
      ∀ a : Fin 3,
        spinAction 8 u * (![Jx 8, Jy 8, Jz 8] a) * (spinAction 8 u)ᴴ =
          ∑ c : Fin 3, (r a c : ℂ) • (![Jx 8, Jy 8, Jz 8] c) := by
  obtain ⟨r, hr, hpauli⟩ := pauli_rotation u
  refine ⟨r, hr, ?_⟩
  have ht : (qubitPower 8 u.val)ᴴ * qubitPower 8 u.val = 1 := tensor_unitary 8 u
  have hd : spinAction 8 u * (spinAction 8 u)ᴴ = 1 :=
    mul_eq_one_comm.mp (spin_action_unitary 8 u)
  have hi : (qubitPower 8 u.val)ᴴ * dickeIsometry 8 =
      dickeIsometry 8 * (spinAction 8 u)ᴴ := by
    calc
      _ = (qubitPower 8 u.val)ᴴ * (dickeIsometry 8 * spinAction 8 u) *
          (spinAction 8 u)ᴴ := by simp only [Matrix.mul_assoc, hd, Matrix.mul_one]
      _ = (qubitPower 8 u.val)ᴴ * (qubitPower 8 u.val * dickeIsometry 8) *
          (spinAction 8 u)ᴴ := by rw [tensor_preserves_symmetric]
      _ = _ := by rw [← Matrix.mul_assoc _ _ (dickeIsometry 8), ht, Matrix.one_mul]
  have hc (a : Fin 3) : (dickeIsometry 8)ᴴ * collectiveSpin 8 a *
      dickeIsometry 8 = ![Jx 8, Jy 8, Jz 8] a := by
    rw [Matrix.mul_assoc, dicke_collective, ← Matrix.mul_assoc,
      dicke_isometry, Matrix.one_mul]
  intro a
  have hrot : qubitPower 8 u.val * collectiveSpin 8 a * (qubitPower 8 u.val)ᴴ =
      ∑ c : Fin 3, (r a c : ℂ) • collectiveSpin 8 c :=
    collective_tensor_rotation 8 u r hpauli a
  calc
    _ = (dickeIsometry 8)ᴴ * qubitPower 8 u.val *
        (dickeIsometry 8 * (![Jx 8, Jy 8, Jz 8] a)) * (spinAction 8 u)ᴴ := by
      change ((dickeIsometry 8)ᴴ * qubitPower 8 u.val * dickeIsometry 8) * _ * _ = _
      simp only [Matrix.mul_assoc]
    _ = (dickeIsometry 8)ᴴ *
        (qubitPower 8 u.val * collectiveSpin 8 a * (qubitPower 8 u.val)ᴴ) *
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
    simpa only [quadrupole, Fintype.sum_prod_type, q, Matrix.kronecker,
      Matrix.kroneckerMap, Matrix.of_apply, Matrix.map_apply] using
      quadratic_rotation (spinAction 8 u) (spin_action_unitary 8 u) r hr
        (![Jx 8, Jy 8, Jz 8]) hj ab.1 ab.2
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
    traceNorm (reducedState 7 witnessState - mixedState 7) = 19 / 84 := by
  let v := dickeIsometry 7
  let w := fun xy : (Fin 7 → Fin 2) × (Fin 1 → Fin 2) => Fin.append xy.1 xy.2
  let p := partialTraceRight
    ((dickeIsometry 8 * witnessState * (dickeIsometry 8)ᴴ).submatrix w w)
  have hp : p = v * reducedState 7 witnessState * vᴴ :=
    dicke_split_partialTrace 7 1 witnessState
  suffices h : traceNorm (p - v * mixedState 7 * vᴴ) = 19 / 84 by
    rw [hp, ← Matrix.sub_mul, ← Matrix.mul_sub,
      D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_isometry
        v (dicke_isometry 7)] at h
    exact h
  rw [hp, ← Matrix.sub_mul, ← Matrix.mul_sub,
    D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_isometry
      v (dicke_isometry 7)]
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

