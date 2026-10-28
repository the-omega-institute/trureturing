/- GID: D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.claim; result=D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.result; claim=D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.claim
   digest: A divisible qutrit channel outside P-divisibility is not entanglement breaking. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Resource.CompositeCones
import D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite

/-! A fixed qutrit counterexample to the higher-dimensional divisibility claim. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Resource.CompositeCones
open D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite (partialTranspose)

namespace D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation

noncomputable section

def IsCPTP (t : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  t.IsCompletelyPositive ∧ t.IsTracePreserving

def IsUnitaryChannel (t : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  ∃ U : Matrix.unitaryGroup (Fin 3) ℂ, ∀ X,
    t X = (U : Matrix (Fin 3) (Fin 3) ℂ) * X *
      (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose

def IsDivisible (t : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  ∃ t1 t2, IsCPTP t1 ∧ IsCPTP t2 ∧ t = t1.comp t2 ∧
    ¬ IsUnitaryChannel t1 ∧ ¬ IsUnitaryChannel t2

def IsPositiveTP (v : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  (∀ ⦃X⦄, X.PosSemidef → (v X).PosSemidef) ∧ v.IsTracePreserving

private noncomputable def transferMatrix (T : MatrixMap (Fin 3) (Fin 3) ℂ) :=
  LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin 3) (Fin 3))
    (Matrix.stdBasis ℂ (Fin 3) (Fin 3)) T

def IsPDivisibleMap (e : ℝ → MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  e 0 = LinearMap.id ∧
    (∀ t, 0 ≤ t → IsCPTP (e t)) ∧
    ContinuousOn (fun t => transferMatrix (e t)) (Set.Ici (0 : ℝ)) ∧
    (∀ t s, 0 ≤ t → t < s → ∃ v, IsPositiveTP v ∧ e s = v.comp (e t))

def pDivisibleSet : Set (MatrixMap (Fin 3) (Fin 3) ℂ) :=
  {T | transferMatrix T ∈ closure {M | ∃ E, IsPDivisibleMap E ∧ ∃ t, 0 ≤ t ∧
    M = transferMatrix (E t)}}

def IsEntanglementBreaking (t : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  ∀ n : ℕ, ∀ rho : Matrix (Fin n × Fin 3) (Fin n × Fin 3) ℂ,
    rho.PosSemidef → rho.trace = 1 →
      separableCone (MatrixMap.kron (LinearMap.id : MatrixMap (Fin n) (Fin n) ℂ) t rho)

def claim : Prop :=
  ∀ t, IsCPTP t → IsDivisible t → t ∉ pDivisibleSet → IsEntanglementBreaking t

private def wk : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ := ![
  (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.single 0 1 1 - Matrix.single 1 0 1),
  (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.single 0 2 1 - Matrix.single 2 0 1),
  (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.single 1 2 1 - Matrix.single 2 1 1)]

private def w : MatrixMap (Fin 3) (Fin 3) ℂ := MatrixMap.of_kraus wk wk

private def dk : Fin 10 → Matrix (Fin 3) (Fin 3) ℂ := ![
  (Real.sqrt 2 : ℂ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℂ),
  (Real.sqrt 6 : ℂ)⁻¹ • Matrix.single (0 : Fin 3) (0 : Fin 3) 1,
  (Real.sqrt 6 : ℂ)⁻¹ • Matrix.single 0 1 1,
  (Real.sqrt 6 : ℂ)⁻¹ • Matrix.single 0 2 1,
  (Real.sqrt 6 : ℂ)⁻¹ • Matrix.single 1 0 1,
  (Real.sqrt 6 : ℂ)⁻¹ • Matrix.single 1 1 1,
  (Real.sqrt 6 : ℂ)⁻¹ • Matrix.single 1 2 1,
  (Real.sqrt 6 : ℂ)⁻¹ • Matrix.single 2 0 1,
  (Real.sqrt 6 : ℂ)⁻¹ • Matrix.single 2 1 1,
  (Real.sqrt 6 : ℂ)⁻¹ • Matrix.single 2 2 1]

private def d : MatrixMap (Fin 3) (Fin 3) ℂ := MatrixMap.of_kraus dk dk

private lemma sqrt2_inv_sq : (Real.sqrt 2 : ℂ)⁻¹ ^ 2 = (1 / 2 : ℂ) := by
  have h : (Real.sqrt 2 : ℂ) ^ 2 = (2 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [inv_pow, h]
  norm_num

private lemma sqrt2_sq : (Real.sqrt 2 : ℂ) ^ 2 = (2 : ℂ) := by
  exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)

private lemma sqrt6_sq : (Real.sqrt 6 : ℂ) ^ 2 = (6 : ℂ) := by
  exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)

private lemma sqrt6_inv_sq : (Real.sqrt 6 : ℂ)⁻¹ ^ 2 = (1 / 6 : ℂ) := by
  have h : (Real.sqrt 6 : ℂ) ^ 2 = (6 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  rw [inv_pow, h]
  norm_num

private def t : MatrixMap (Fin 3) (Fin 3) ℂ := d.comp w

private lemma w_formula (X : Matrix (Fin 3) (Fin 3) ℂ) :
    w X = (1 / 2 : ℂ) • (X.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ) - X.transpose) := by
  ext i j
  simp [w, MatrixMap.of_kraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single, wk, Fin.sum_univ_three, Matrix.trace, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.single, Matrix.one_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_three] <;>
    ring_nf <;> simp only [sqrt2_inv_sq] <;> ring

private lemma d_formula (X : Matrix (Fin 3) (Fin 3) ℂ) :
    d X = (1 / 2 : ℂ) • X + (1 / 2 : ℂ) • (X.trace / 3) •
      (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  simp [d, MatrixMap.of_kraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single, dk, Fin.sum_univ_succ, Matrix.trace, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.single, Matrix.one_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [sqrt2_inv_sq, sqrt6_inv_sq] <;> ring

private lemma t_formula (X : Matrix (Fin 3) (Fin 3) ℂ) :
    t X = (5 / 12 : ℂ) • X.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      (1 / 4 : ℂ) • X.transpose := by
  ext i j
  simp [t, d_formula, w_formula, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_transpose, Matrix.trace_one, Fintype.card_fin]
  ring

private lemma kraus_trace_preserving {κ : Type*} [Fintype κ]
    (K : κ → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : (∑ r, (K r).conjTranspose * K r) = 1) :
    (MatrixMap.of_kraus K K).IsTracePreserving := by
  exact MatrixMap.IsTracePreserving.of_kraus_isTracePreserving K K hK

private lemma wk_complete : (∑ r, (wk r).conjTranspose * wk r) =
    (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wk, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
      Fin.sum_univ_three] <;> ring_nf <;> simp [sqrt2_sq] <;> norm_num

private lemma dk_complete : (∑ r, (dk r).conjTranspose * dk r) =
    (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dk, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
      Fin.sum_univ_succ] <;> ring_nf <;>
    simp [sqrt2_sq, sqrt6_sq] <;> norm_num

private lemma w_cptp : IsCPTP w := by
  refine ⟨?_, ?_⟩
  · exact MatrixMap.of_kraus_isCompletelyPositive wk
  · exact kraus_trace_preserving wk wk_complete

private lemma d_cptp : IsCPTP d := by
  refine ⟨?_, ?_⟩
  · exact MatrixMap.of_kraus_isCompletelyPositive dk
  · exact kraus_trace_preserving dk dk_complete

private lemma of_kraus_comp {κ ι : Type*} [Fintype κ] [Fintype ι]
    (M : κ → Matrix (Fin 3) (Fin 3) ℂ)
    (N : ι → Matrix (Fin 3) (Fin 3) ℂ) :
    (MatrixMap.of_kraus M M).comp (MatrixMap.of_kraus N N) =
      MatrixMap.of_kraus (fun p : κ × ι => M p.1 * N p.2)
        (fun p : κ × ι => M p.1 * N p.2) := by
  ext X i j
  simp only [MatrixMap.of_kraus, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Matrix.mul_sum, Finset.sum_mul]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [Fintype.sum_prod_type]

private lemma t_kraus : t =
    MatrixMap.of_kraus (fun p : Fin 10 × Fin 3 => dk p.1 * wk p.2)
      (fun p : Fin 10 × Fin 3 => dk p.1 * wk p.2) := by
  change (MatrixMap.of_kraus dk dk).comp (MatrixMap.of_kraus wk wk) = _
  exact of_kraus_comp dk wk

private lemma t_cptp : IsCPTP t := by
  refine ⟨?_, ?_⟩
  · rw [t_kraus]
    exact MatrixMap.of_kraus_isCompletelyPositive _
  · intro X
    change Matrix.trace (d (w X)) = Matrix.trace X
    rw [d_cptp.2, w_cptp.2]

private lemma unitary_purity (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    Matrix.trace (((U : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.single (0 : Fin 3) (0 : Fin 3) 1 *
      (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose) *
      ((U : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.single (0 : Fin 3) (0 : Fin 3) 1 *
      (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose)) = 1 := by
  have hu : (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose * (U : Matrix (Fin 3) (Fin 3) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  have he : Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ) *
      Matrix.single (0 : Fin 3) (0 : Fin 3) 1 =
      Matrix.single (0 : Fin 3) (0 : Fin 3) 1 := by
    ext i j
    simp [Matrix.mul_apply, Matrix.single, Fin.sum_univ_three] <;>
      split_ifs <;> simp_all <;> omega
  have hid :
      ((U : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.single (0 : Fin 3) (0 : Fin 3) 1 *
        (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose) *
        ((U : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.single (0 : Fin 3) (0 : Fin 3) 1 *
        (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose) =
      (U : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.single (0 : Fin 3) (0 : Fin 3) 1 *
        (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose := by
    calc
      _ = (U : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.single (0 : Fin 3) (0 : Fin 3) 1 *
          (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose *
          (U : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.single (0 : Fin 3) (0 : Fin 3) 1 *
          (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose := by
            simp only [Matrix.mul_assoc]
      _ = (U : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.single (0 : Fin 3) (0 : Fin 3) 1 *
          ((U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose *
            (U : Matrix (Fin 3) (Fin 3) ℂ)) * Matrix.single (0 : Fin 3) (0 : Fin 3) 1 *
          (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose := by
            noncomm_ring
      _ = (U : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.single (0 : Fin 3) (0 : Fin 3) 1 *
          Matrix.single (0 : Fin 3) (0 : Fin 3) 1 * (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose := by
            rw [hu, Matrix.mul_one]
      _ = (U : Matrix (Fin 3) (Fin 3) ℂ) *
          (Matrix.single (0 : Fin 3) (0 : Fin 3) 1 *
            Matrix.single (0 : Fin 3) (0 : Fin 3) 1) *
          (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose := by
            noncomm_ring
      _ = _ := by rw [he]
  rw [hid, Matrix.trace_mul_cycle (U : Matrix (Fin 3) (Fin 3) ℂ)
    (Matrix.single (0 : Fin 3) (0 : Fin 3) 1) (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose]
  rw [hu, Matrix.one_mul]
  simp [Matrix.trace, Matrix.single]

private lemma w_not_unitary : ¬ IsUnitaryChannel w := by
  rintro ⟨U, hU⟩
  have hp := unitary_purity U
  have hw := congrArg (fun Z => Matrix.trace (Z * Z)) (hU (Matrix.single (0 : Fin 3) (0 : Fin 3) 1))
  have hw' : Matrix.trace (w (Matrix.single (0 : Fin 3) (0 : Fin 3) 1) *
      w (Matrix.single (0 : Fin 3) (0 : Fin 3) 1)) = 1 := hw.trans hp
  rw [w_formula] at hw'
  norm_num [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.single, Matrix.one_apply, Fin.sum_univ_three] at hw'

private lemma d_not_unitary : ¬ IsUnitaryChannel d := by
  rintro ⟨U, hU⟩
  have hp := unitary_purity U
  have hw := congrArg (fun Z => Matrix.trace (Z * Z)) (hU (Matrix.single (0 : Fin 3) (0 : Fin 3) 1))
  have hw' : Matrix.trace (d (Matrix.single (0 : Fin 3) (0 : Fin 3) 1) *
      d (Matrix.single (0 : Fin 3) (0 : Fin 3) 1)) = 1 := hw.trans hp
  rw [d_formula] at hw'
  norm_num [Matrix.trace, Matrix.mul_apply, Matrix.single, Matrix.one_apply,
    Fin.sum_univ_three] at hw'

private lemma t_divisible : IsDivisible t := by
  exact ⟨d, w, d_cptp, w_cptp, rfl, d_not_unitary, w_not_unitary⟩

private lemma hermiticity_preserving_det_real (T : MatrixMap (Fin 3) (Fin 3) ℂ)
    (hT : ∀ X, T X.conjTranspose = (T X).conjTranspose) :
    (Matrix.det (transferMatrix T)).im = 0 := by sorry

private lemma pdivisible_endpoint_det_nonneg {E : ℝ → MatrixMap (Fin 3) (Fin 3) ℂ}
    (hE : IsPDivisibleMap E) (u : ℝ) (hu : 0 ≤ u) :
    (Matrix.det (transferMatrix (E u))).im = 0 ∧
      0 ≤ (Matrix.det (transferMatrix (E u))).re := by sorry

private def nonnegativeDetSet : Set (MatrixMap (Fin 3) (Fin 3) ℂ) :=
  {T | (Matrix.det (transferMatrix T)).im = 0 ∧
    0 ≤ (Matrix.det (transferMatrix T)).re}

private lemma pdivisibleSet_subset_nonnegativeDet :
    pDivisibleSet ⊆ nonnegativeDetSet := by sorry

private lemma t_det : Matrix.det (transferMatrix t) = -(1 / 4 : ℂ) ^ 8 := by sorry

private lemma t_not_pdivisible : t ∉ pDivisibleSet := by
  intro ht
  have hnonneg := pdivisibleSet_subset_nonnegativeDet ht
  change (Matrix.det (transferMatrix t)).im = 0 ∧
    0 ≤ (Matrix.det (transferMatrix t)).re at hnonneg
  rw [t_det] at hnonneg
  norm_num at hnonneg

private def omega : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  ((1 / 3 : ℝ) : ℂ) • Matrix.vecMulVec
    (fun p : Fin 3 × Fin 3 => if p.1 = p.2 then 1 else 0)
    (star (fun p : Fin 3 × Fin 3 => if p.1 = p.2 then 1 else 0))

private def witnessVector : Fin 3 × Fin 3 → ℂ :=
  ((1 / Real.sqrt 3 : ℝ) : ℂ) •
    (fun p : Fin 3 × Fin 3 => if p.1 = p.2 then 1 else 0)

private lemma omega_density : omega.PosSemidef ∧ omega.trace = 1 := by
  constructor
  · apply Matrix.PosSemidef.smul _ (Complex.zero_le_real.mpr (by norm_num))
    exact Matrix.posSemidef_vecMulVec_self_star _
  · have hpsi : star (fun p : Fin 3 × Fin 3 => if p.1 = p.2 then 1 else 0) ⬝ᵥ
        (fun p : Fin 3 × Fin 3 => if p.1 = p.2 then 1 else 0) = (3 : ℂ) := by
      simp [dotProduct, Fintype.sum_prod_type]
    rw [omega, Matrix.trace_smul, Matrix.trace_vecMulVec]
    rw [dotProduct_comm, hpsi]
    norm_num

private lemma separableCone_partialTranspose_posSemidef {m n : ℕ}
    {rho : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hsep : separableCone rho) : (partialTranspose rho).PosSemidef := by
  rcases hsep with ⟨k, A, B, hAB, rfl⟩
  have hterm : ∀ i : Fin k, (partialTranspose (A i ⊗ₖ B i)).PosSemidef := by
    intro i
    have heq : partialTranspose (A i ⊗ₖ B i) = A i ⊗ₖ (B i).transpose := by
      ext ⟨a, b⟩ ⟨c, d⟩
      simp [partialTranspose, Matrix.kronecker_apply]
    rw [heq]
    exact (hAB i).1.kronecker (hAB i).2.transpose
  have hs := Matrix.posSemidef_sum (s := (Finset.univ : Finset (Fin k)))
    (x := fun i : Fin k => partialTranspose (A i ⊗ₖ B i)) (by
      intro i hi
      exact hterm i)
  have hlin : partialTranspose (∑ i, A i ⊗ₖ B i) =
      ∑ i, partialTranspose (A i ⊗ₖ B i) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp [partialTranspose, Matrix.sum_apply]
  rw [hlin]
  exact hs

private lemma witness_partial_transpose_negative :
    RCLike.re (dotProduct (star witnessVector)
      (Matrix.mulVec (partialTranspose
        (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) t omega))
        witnessVector)) = -1 / 9 := by sorry

private lemma t_not_entanglementBreaking : ¬ IsEntanglementBreaking t := by
  intro h
  have hs := h 3 omega omega_density.1 omega_density.2
  have hp := separableCone_partialTranspose_posSemidef hs
  have hn := hp.re_dotProduct_nonneg witnessVector
  rw [witness_partial_transpose_negative] at hn
  norm_num at hn

theorem result : ¬ claim := by
  intro h
  exact t_not_entanglementBreaking
    (h t t_cptp t_divisible t_not_pdivisible)

end
end D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation
