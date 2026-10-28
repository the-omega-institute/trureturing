/- GID: D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.claim; result=D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.result; claim=D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.claim
   digest: A divisible qutrit channel outside P-divisibility is not entanglement breaking. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Resource.CompositeCones
import D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding
import D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity
import D5.S3.QuantumBounds.PeritoTsirelson

/-! A fixed qutrit counterexample to the higher-dimensional divisibility claim. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Resource.CompositeCones
open D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite (partialTranspose)
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsCPTP)
open D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding (wernerHolevo)
open D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound (depolarized)
open D5.S3.QuantumBounds.PeritoTsirelson (maxEntangled maxEntangledVector max_entangled_density)

namespace D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation

noncomputable section

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

private lemma wernerHolevo_one_eq_kraus :
    wernerHolevo 1 = MatrixMap.of_kraus wk wk := by
  symm
  ext X i j
  simp [MatrixMap.of_kraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single, wk, Fin.sum_univ_three, Matrix.trace,
    wernerHolevo, Matrix.transposeLinearEquiv, Matrix.traceLinearMap,
    Matrix.one_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.single, Matrix.one_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_three] <;>
    ring_nf <;> simp only [sqrt2_inv_sq] <;> ring

private lemma depolarized_one_eq_kraus :
    depolarized (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) (1 / 2) =
      MatrixMap.of_kraus dk dk := by
  symm
  ext X i j
  simp [MatrixMap.of_kraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single, dk, Fin.sum_univ_succ, Matrix.trace,
    depolarized, Matrix.traceLinearMap, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.single, Matrix.one_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [sqrt2_inv_sq, sqrt6_inv_sq] <;> ring

private def t : MatrixMap (Fin 3) (Fin 3) ℂ :=
  (depolarized (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) (1 / 2)).comp
    (wernerHolevo 1)

private lemma w_formula (X : Matrix (Fin 3) (Fin 3) ℂ) :
    wernerHolevo 1 X =
      (1 / 2 : ℂ) • (X.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ) - X.transpose) := by
  unfold wernerHolevo
  simp [Matrix.transposeLinearEquiv, Matrix.traceLinearMap]
  module

private lemma d_formula (X : Matrix (Fin 3) (Fin 3) ℂ) :
    depolarized (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) (1 / 2) X =
      (1 / 2 : ℂ) • X + (1 / 2 : ℂ) • (X.trace / 3) •
      (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  unfold depolarized
  simp [Matrix.traceLinearMap]
  module

private lemma t_formula (X : Matrix (Fin 3) (Fin 3) ℂ) :
    t X = (5 / 12 : ℂ) • X.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      (1 / 4 : ℂ) • X.transpose := by
  ext i j
  change
    (depolarized (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) (1 / 2)
      (wernerHolevo 1 X)) i j = _
  rw [d_formula, w_formula]
  simp [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_transpose,
    Matrix.trace_one, Fintype.card_fin]
  ring

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

private lemma w_cptp : IsCPTP (wernerHolevo 1) := by
  rw [wernerHolevo_one_eq_kraus]
  refine ⟨?_, ?_⟩
  · exact MatrixMap.of_kraus_isCompletelyPositive wk
  · exact MatrixMap.IsTracePreserving.of_kraus_isTracePreserving wk wk wk_complete

private lemma d_cptp : IsCPTP (depolarized (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) (1 / 2)) := by
  rw [depolarized_one_eq_kraus]
  refine ⟨?_, ?_⟩
  · exact MatrixMap.of_kraus_isCompletelyPositive dk
  · exact MatrixMap.IsTracePreserving.of_kraus_isTracePreserving dk dk dk_complete

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
  change
    (depolarized (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) (1 / 2)).comp
        (wernerHolevo 1) = _
  rw [depolarized_one_eq_kraus, wernerHolevo_one_eq_kraus]
  exact of_kraus_comp dk wk

private lemma t_cptp : IsCPTP t := by
  refine ⟨?_, ?_⟩
  · rw [t_kraus]
    exact MatrixMap.of_kraus_isCompletelyPositive _
  · intro X
    change Matrix.trace
      (depolarized (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) (1 / 2)
        (wernerHolevo 1 X)) = Matrix.trace X
    rw [d_cptp.2, w_cptp.2]

private lemma cptp_hermiticity (T : MatrixMap (Fin 3) (Fin 3) ℂ)
    (hT : IsCPTP T) : ∀ X, T X.conjTranspose = (T X).conjTranspose := by
  obtain ⟨K, hK⟩ := MatrixMap.IsCompletelyPositive.exists_kraus T hT.1
  rw [hK]
  intro X
  change (∑ c, K c * X.conjTranspose * (K c).conjTranspose) =
    (∑ c, K c * X * (K c).conjTranspose).conjTranspose
  simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

private lemma unitary_purity (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    Matrix.trace (((U : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.single (0 : Fin 3) (0 : Fin 3) 1 *
      (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose) *
      ((U : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.single (0 : Fin 3) (0 : Fin 3) 1 *
      (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose)) = 1 := by
  rw [D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction.unitary_purity_trace]
  have he : Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ) *
      Matrix.single (0 : Fin 3) (0 : Fin 3) 1 =
      Matrix.single (0 : Fin 3) (0 : Fin 3) 1 := by
    ext i j
    simp [Matrix.mul_apply, Matrix.single, Fin.sum_univ_three] <;>
      split_ifs <;> simp_all <;> omega
  rw [he]
  simp [Matrix.trace, Matrix.single]

private lemma w_not_unitary : ¬ IsUnitaryChannel (wernerHolevo 1) := by
  rintro ⟨U, hU⟩
  have hp := unitary_purity U
  have hw := congrArg (fun Z => Matrix.trace (Z * Z)) (hU (Matrix.single (0 : Fin 3) (0 : Fin 3) 1))
  have hw' : Matrix.trace (wernerHolevo 1 (Matrix.single (0 : Fin 3) (0 : Fin 3) 1) *
      wernerHolevo 1 (Matrix.single (0 : Fin 3) (0 : Fin 3) 1)) = 1 := hw.trans hp
  rw [w_formula] at hw'
  norm_num [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.single, Matrix.one_apply, Fin.sum_univ_three] at hw'

private lemma d_not_unitary : ¬ IsUnitaryChannel
    (depolarized (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) (1 / 2)) := by
  rintro ⟨U, hU⟩
  have hp := unitary_purity U
  have hw := congrArg (fun Z => Matrix.trace (Z * Z)) (hU (Matrix.single (0 : Fin 3) (0 : Fin 3) 1))
  have hw' : Matrix.trace
      (depolarized (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) (1 / 2)
        (Matrix.single (0 : Fin 3) (0 : Fin 3) 1) *
      depolarized (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) (1 / 2)
        (Matrix.single (0 : Fin 3) (0 : Fin 3) 1)) = 1 := hw.trans hp
  rw [d_formula] at hw'
  norm_num [Matrix.trace, Matrix.mul_apply, Matrix.single, Matrix.one_apply,
    Fin.sum_univ_three] at hw'

private lemma t_divisible : IsDivisible t := by
  exact ⟨depolarized (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) (1 / 2),
    wernerHolevo 1, d_cptp, w_cptp, rfl, d_not_unitary, w_not_unitary⟩

private lemma hermiticity_preserving_det_real (T : MatrixMap (Fin 3) (Fin 3) ℂ)
    (hT : ∀ X, T X.conjTranspose = (T X).conjTranspose) :
    (Matrix.det (transferMatrix T)).im = 0 := by
  let e : (Fin 3 × Fin 3) ≃ (Fin 3 × Fin 3) := Equiv.prodComm (Fin 3) (Fin 3)
  have hmap : (starRingEnd ℂ).mapMatrix (transferMatrix T) =
      Matrix.reindex e e (transferMatrix T) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp [transferMatrix, LinearMap.toMatrix_apply, Matrix.stdBasis,
      Matrix.map_apply, e, Matrix.reindex_apply,
      ← Matrix.single_eq_of_single_single, Matrix.single,
      Pi.single_apply, ite_and]
    have hcd :
        (fun i' j' : Fin 3 => if c = i' ∧ d = j' then (1 : ℂ) else 0) =
          (fun i' j' : Fin 3 => if c = i' then if d = j' then 1 else 0 else 0) := by
      funext i' j'
      by_cases hc : c = i' <;> by_cases hd : d = j' <;> simp [hc, hd]
    have hdc :
        (fun i' j' : Fin 3 => if d = i' ∧ c = j' then (1 : ℂ) else 0) =
          (fun i' j' : Fin 3 => if d = i' then if c = j' then 1 else 0 else 0) := by
      funext i' j'
      by_cases hd : d = i' <;> by_cases hc : c = j' <;> simp [hc, hd]
    have htrans :
        (Matrix.of (fun i' j' : Fin 3 => if c = i' then if d = j' then (1 : ℂ) else 0 else 0)).conjTranspose =
          Matrix.of (fun i' j' : Fin 3 => if d = i' then if c = j' then (1 : ℂ) else 0 else 0) := by
      ext i' j'
      by_cases hd : d = i' <;> by_cases hc : c = j' <;>
        simp [Matrix.conjTranspose_apply, eq_comm, hd, hc]
    have hh := congrArg (fun Z : Matrix (Fin 3) (Fin 3) ℂ => Z b a)
      (hT (Matrix.single (c : Fin 3) d 1))
    simpa [Matrix.single, Matrix.conjTranspose_apply, hcd, hdc, htrans] using hh.symm
  have hstar : star (Matrix.det (transferMatrix T)) =
      Matrix.det (transferMatrix T) := by
    calc
      star (Matrix.det (transferMatrix T)) =
          Matrix.det ((starRingEnd ℂ).mapMatrix (transferMatrix T)) :=
            RingHom.map_det (starRingEnd ℂ) (transferMatrix T)
      _ = Matrix.det (Matrix.reindex e e (transferMatrix T)) := by rw [hmap]
      _ = Matrix.det (transferMatrix T) := Matrix.det_reindex_self e _
  exact Complex.conj_eq_iff_im.mp hstar

private lemma pdivisible_endpoint_det_nonneg {E : ℝ → MatrixMap (Fin 3) (Fin 3) ℂ}
    (hE : IsPDivisibleMap E) (u : ℝ) (hu : 0 ≤ u) :
    (Matrix.det (transferMatrix (E u))).im = 0 ∧
      0 ≤ (Matrix.det (transferMatrix (E u))).re := by
  have hreal : ∀ x, 0 ≤ x →
      (Matrix.det (transferMatrix (E x))).im = 0 := by
    intro x hx
    exact hermiticity_preserving_det_real (E x)
      (cptp_hermiticity (E x) (hE.2.1 x hx))
  have hcontDet : ContinuousOn
      (fun x => Matrix.det (transferMatrix (E x))) (Set.Ici (0 : ℝ)) := by
    exact (continuous_id.matrix_det.continuousOn.comp'
      hE.2.2.1 (Set.mapsTo_univ _ _))
  have hcont : ContinuousOn
      (fun x => (Matrix.det (transferMatrix (E x))).re) (Set.Ici (0 : ℝ)) := by
    exact Complex.continuous_re.continuousOn.comp' hcontDet
      (Set.mapsTo_univ _ _)
  constructor
  · exact hreal u hu
  by_contra hneg
  have hlt : (Matrix.det (transferMatrix (E u))).re < 0 := lt_of_not_ge hneg
  let f : ℝ → ℝ := fun x => (Matrix.det (transferMatrix (E x))).re
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) u) := by
    exact hcont.mono Set.Icc_subset_Ici_self
  have hfzero : f 0 = 1 := by
    dsimp [f]
    rw [hE.1]
    simp [transferMatrix]
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (f u) (f 0) := by
    constructor
    · exact le_of_lt (by simpa [f] using hlt)
    · simpa [hfzero]
  have himage := intermediate_value_Icc' hu hfcont hzero_mem
  rcases himage with ⟨z, hz, hzf⟩
  have hz0 : f z = 0 := hzf
  have hzdet : Matrix.det (transferMatrix (E z)) = 0 := by
    apply Complex.ext
    · simpa [f] using hz0
    · exact hreal z hz.1
  have hzu : z < u := by
    apply lt_of_le_of_ne hz.2
    intro hzu
    subst z
    linarith
  obtain ⟨v, hv, hcomp⟩ := hE.2.2.2 z u hz.1 hzu
  have hcompM : transferMatrix (E u) =
      transferMatrix v * transferMatrix (E z) := by
    rw [hcomp]
    exact LinearMap.toMatrix_comp _ _ _ _ _
  have hdetu : Matrix.det (transferMatrix (E u)) = 0 := by
    rw [hcompM, Matrix.det_mul, hzdet, mul_zero]
  have : f u = 0 := by
    simpa [f, hdetu]
  linarith

private def nonnegativeDetSet : Set (MatrixMap (Fin 3) (Fin 3) ℂ) :=
  {T | (Matrix.det (transferMatrix T)).im = 0 ∧
    0 ≤ (Matrix.det (transferMatrix T)).re}

private lemma pdivisibleSet_subset_nonnegativeDet :
    pDivisibleSet ⊆ nonnegativeDetSet := by
  let s : Set (Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :=
    {M : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ |
      M.det.im = 0 ∧ 0 ≤ M.det.re}
  have hdet : Continuous (fun M : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ => M.det) :=
    continuous_id.matrix_det
  have hclosed : IsClosed s := by
    change IsClosed {M : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ |
      M.det.im = 0 ∧ 0 ≤ M.det.re}
    exact (isClosed_eq (Complex.continuous_im.comp hdet) continuous_const).inter
      (isClosed_le continuous_const (Complex.continuous_re.comp hdet))
  have hsubset :
      {M | ∃ E, IsPDivisibleMap E ∧ ∃ u, 0 ≤ u ∧ M = transferMatrix (E u)} ⊆ s := by
    intro M hM
    rcases hM with ⟨E, hE, u, hu, rfl⟩
    exact pdivisible_endpoint_det_nonneg hE u hu
  intro T hT
  change transferMatrix T ∈ closure
    {M | ∃ E, IsPDivisibleMap E ∧ ∃ u, 0 ≤ u ∧ M = transferMatrix (E u)} at hT
  have hcl := hclosed.closure_subset_iff.mpr hsubset
  exact hcl hT

private lemma transfer_entry (i j k l : Fin 3) :
    (transferMatrix t) (i, j) (k, l) =
      (if i = j then if k = l then (5 / 12 : ℂ) else 0 else 0) -
        (if j = k ∧ i = l then (1 / 4 : ℂ) else 0) := by
  simp [transferMatrix, LinearMap.toMatrix_apply, Matrix.stdBasis, t_formula,
    Matrix.single, Matrix.trace, Matrix.one_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Matrix.single, Fin.sum_univ_three] <;> norm_num

private lemma t_det : Matrix.det (transferMatrix t) = -(1 / 4 : ℂ) ^ 8 := by
  classical
  let S := Fin 3 ⊕ (Fin 2 × Fin 3)
  let q : S → (Fin 3 × Fin 3) := fun s =>
    match s with
    | Sum.inl i => (i, i)
    | Sum.inr ⟨b, k⟩ =>
        if k = 0 then if b = 0 then (0, 1) else (1, 0)
        else if k = 1 then if b = 0 then (0, 2) else (2, 0)
        else if b = 0 then (1, 2) else (2, 1)
  have hq : Function.Bijective q := by
    dsimp [q]
    decide
  let e : S ≃ (Fin 3 × Fin 3) := Equiv.ofBijective q hq
  let R : Matrix S S ℂ := Matrix.reindex e.symm e.symm (transferMatrix t)
  let A : Matrix (Fin 3) (Fin 3) ℂ := fun i j => R (Sum.inl i) (Sum.inl j)
  let B : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
    fun p r => R (Sum.inr p) (Sum.inr r)
  have hcross₁ : ∀ i : Fin 3, ∀ p : Fin 2 × Fin 3,
      R (Sum.inl i) (Sum.inr p) = 0 := by
    intro i p
    rcases p with ⟨b, k⟩
    fin_cases i <;> fin_cases b <;> fin_cases k <;>
      simp [R, Matrix.reindex_apply, e, q, transfer_entry]
  have hcross₂ : ∀ p : Fin 2 × Fin 3, ∀ i : Fin 3,
      R (Sum.inr p) (Sum.inl i) = 0 := by
    intro p i
    rcases p with ⟨b, k⟩
    fin_cases i <;> fin_cases b <;> fin_cases k <;>
      simp [R, Matrix.reindex_apply, e, q, transfer_entry]
  have hblock : R = Matrix.fromBlocks A 0 0 B := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j => rfl
        | inr p => simp [hcross₁ i p]
    | inr p =>
        cases j with
        | inl i => simp [hcross₂ p i]
        | inr r => rfl
  have hA : Matrix.det A = (1 / 16 : ℂ) := by
    rw [Matrix.det_fin_three]
    simp [A, R, Matrix.reindex_apply, e, q, transfer_entry]
    ring
  have hB : Matrix.det B = -(1 / 4 : ℂ) ^ 6 := by
    let blocks : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := fun k =>
      !![0, -(1 / 4 : ℂ); -(1 / 4 : ℂ), 0]
    have hBblock : B = Matrix.blockDiagonal blocks := by
      ext p r
      rcases p with ⟨b, k⟩
      rcases r with ⟨c, l⟩
      fin_cases b <;> fin_cases c <;> fin_cases k <;> fin_cases l <;>
        simp [B, R, Matrix.reindex_apply, e, q, transfer_entry, blocks,
          Matrix.blockDiagonal]
    rw [hBblock, Matrix.det_blockDiagonal]
    simp [blocks, Matrix.det_fin_two]
    ring
  calc
    Matrix.det (transferMatrix t) = Matrix.det R := by
      symm
      exact Matrix.det_reindex_self e.symm (transferMatrix t)
    _ = Matrix.det (Matrix.fromBlocks A 0 0 B) := by rw [hblock]
    _ = Matrix.det A * Matrix.det B := Matrix.det_fromBlocks_zero₂₁ _ _ _
    _ = -(1 / 4 : ℂ) ^ 8 := by rw [hA, hB]; norm_num

private lemma t_not_pdivisible : t ∉ pDivisibleSet := by
  intro ht
  have hnonneg := pdivisibleSet_subset_nonnegativeDet ht
  change (Matrix.det (transferMatrix t)).im = 0 ∧
    0 ≤ (Matrix.det (transferMatrix t)).re at hnonneg
  rw [t_det] at hnonneg
  norm_num at hnonneg

private lemma omega_density :
    Matrix.PosSemidef (maxEntangled (Fin 3)) ∧
      Matrix.trace (maxEntangled (Fin 3)) = 1 := by
  have h := max_entangled_density (Fin 3)
  constructor
  · exact (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm h.1).posSemidef
  · exact h.2

private lemma witness_partial_transpose_negative :
    RCLike.re (dotProduct (star (maxEntangledVector (Fin 3)))
      (Matrix.mulVec (partialTranspose
        (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) t
          (maxEntangled (Fin 3)))) (maxEntangledVector (Fin 3)))) = -1 / 9 := by
  classical
  have hsqrtR : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hc0 : (Finset.univ.filter (fun x : Fin 3 => (0 : Fin 3) = x)).card = 1 := by
    decide
  have hc1 : (Finset.univ.filter (fun x : Fin 3 => (1 : Fin 3) = x)).card = 1 := by
    decide
  have hc2 : (Finset.univ.filter (fun x : Fin 3 => (2 : Fin 3) = x)).card = 1 := by
    decide
  simp [maxEntangledVector, maxEntangled, partialTranspose, MatrixMap.kron_def,
    MatrixMap.id, t_formula, Matrix.mulVec, dotProduct, Matrix.vecMulVec,
    Matrix.single, Matrix.trace, Matrix.transpose_apply, Fin.sum_univ_three,
    Fin.sum_univ_succ, Fintype.sum_prod_type]
  norm_num [hc0, hc1, hc2]
  ring_nf
  have hsqrt4 : (Real.sqrt 3 : ℝ) ^ 4 = 9 := by
    calc
      (Real.sqrt 3 : ℝ) ^ 4 = ((Real.sqrt 3 : ℝ) ^ 2) ^ 2 := by ring
      _ = 9 := by rw [hsqrtR]; norm_num
  rw [hsqrt4]
  norm_num

private lemma t_not_entanglementBreaking : ¬ IsEntanglementBreaking t := by
  intro h
  have hs := h 3 (maxEntangled (Fin 3)) omega_density.1 omega_density.2
  have hp :=
    D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef hs
  have hn := hp.re_dotProduct_nonneg (maxEntangledVector (Fin 3))
  change 0 ≤ RCLike.re
      (dotProduct (star (maxEntangledVector (Fin 3)))
        (Matrix.mulVec (partialTranspose
          (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) t
            (maxEntangled (Fin 3)))) (maxEntangledVector (Fin 3)))) at hn
  rw [witness_partial_transpose_negative] at hn
  norm_num at hn

theorem result : ¬ claim := by
  intro h
  exact t_not_entanglementBreaking
    (h t t_cptp t_divisible t_not_pdivisible)

end
end D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation
