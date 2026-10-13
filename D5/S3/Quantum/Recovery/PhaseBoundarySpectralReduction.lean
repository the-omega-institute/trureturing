/- GID: D5/S3/Quantum/Recovery/PhaseBoundarySpectralReduction
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PhaseBoundarySpectralReduction
   mirror-E: none(waiver:research-interface)
   anchors: []
   utility: none
   digest: Pure-reference recovery error and rank-one spectral inertia. -/
import D5.S3.Quantum.Recovery.PhaseBoundarySourceModel
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Recovery.PhaseBoundarySpectralReduction
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Recovery.PhaseBoundarySourceModel
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

private theorem rank_one_sub_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → ℂ) {B : Matrix n n ℂ} (hB : B.PosSemidef) :
    (vecMulVec v (star v) - B).IsHermitian :=
  (posSemidef_vecMulVec_self_star v).isHermitian.sub hB.isHermitian

private theorem quadratic_nonpositive_on_perp {n : Type*} [Fintype n]
    (v : n → ℂ) {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (x : n → ℂ) (hx : star v ⬝ᵥ x = 0) :
    (star x ⬝ᵥ ((vecMulVec v (star v) - B) *ᵥ x)).re ≤ 0 := by
  have hp := (Complex.nonneg_iff.mp (hB.dotProduct_mulVec_nonneg x)).1
  rw [Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, hx]
  simpa using neg_nonpos.mpr hp

/-- A rank-one positive update of a negative semidefinite matrix has at most
one strictly positive eigenvalue, counted with multiplicity. -/
theorem positive_eigenvalues_unique {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → ℂ) {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (i j : n)
    (hi : 0 < (rank_one_sub_hermitian v hB).eigenvalues i)
    (hj : 0 < (rank_one_sub_hermitian v hB).eigenvalues j) : i = j := by
  classical
  by_contra hij
  let A := vecMulVec v (star v) - B
  let hA : A.IsHermitian := rank_one_sub_hermitian v hB
  let e : n → n → ℂ := fun k => ⇑(hA.eigenvectorBasis k)
  have he (k l : n) : star (e k) ⬝ᵥ e l = if k = l then 1 else 0 := by
    change star (⇑(hA.eigenvectorBasis k)) ⬝ᵥ ⇑(hA.eigenvectorBasis l) = _
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    exact orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal k l
  have hAe (k : n) : A *ᵥ e k = (hA.eigenvalues k : ℂ) • e k :=
    hA.mulVec_eigenvectorBasis k
  let a := star v ⬝ᵥ e i
  let b := star v ⬝ᵥ e j
  have ha : a ≠ 0 := by
    intro ha
    have hh := quadratic_nonpositive_on_perp v hB (e i) ha
    change (star (e i) ⬝ᵥ (A *ᵥ e i)).re ≤ 0 at hh
    rw [hAe, dotProduct_smul, he] at hh
    have hh' : hA.eigenvalues i ≤ 0 := by simpa using hh
    exact (not_le_of_gt hi) hh'
  let x := b • e i - a • e j
  have hx : star v ⬝ᵥ x = 0 := by
    simp only [x, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    change b * a - a * b = 0
    ring
  have hnonpos := quadratic_nonpositive_on_perp v hB x hx
  have hquad : star x ⬝ᵥ (A *ᵥ x) =
      (hA.eigenvalues i : ℂ) * (Complex.normSq b : ℂ) +
        (hA.eigenvalues j : ℂ) * (Complex.normSq a : ℂ) := by
    simp only [x, Matrix.mulVec_sub, Matrix.mulVec_smul, hAe,
      star_sub, star_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, he, hij, Ne.symm hij,
      if_true, if_false, mul_one, mul_zero, sub_zero, zero_sub]
    simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  change (star x ⬝ᵥ (A *ᵥ x)).re ≤ 0 at hnonpos
  rw [hquad] at hnonpos
  have hpos : 0 < hA.eigenvalues i * Complex.normSq b +
      hA.eigenvalues j * Complex.normSq a :=
    add_pos_of_nonneg_of_pos (mul_nonneg hi.le (Complex.normSq_nonneg b))
      (mul_pos hj (Complex.normSq_pos.mpr ha))
  have hr : (hA.eigenvalues i * Complex.normSq b +
      hA.eigenvalues j * Complex.normSq a : ℝ) ≤ 0 := by
    simpa using hnonpos
  exact (not_le_of_gt hpos) hr

/-
Copyright (c) 2026 QuAIR. Authors: QuAIR Team.
Released under Apache 2.0; full license: docs/reports/recordtimebound/Lean-QIT-LICENSE.txt.
The positive-part trace primitive is from QIT/States/TraceNorm/PositivePart.lean,
revision 15a0a5ef13e5824327e0850ea896e472366287af, with its local real-part helper
inlined and the repository's matrix notation. No NOTICE is present at that revision.
This primitive is replaced by direct application when the repository's pinned
Mathlib contains the equivalent positive-part trace theorem.
-/
private theorem positive_part_trace {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (posPart A).trace.re = ∑ i, if 0 < hA.eigenvalues i then hA.eigenvalues i else 0 := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc, hA.cfc_eq, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul]
  have hr (x : ℝ) : posPart x = if 0 < x then x else 0 := by
    by_cases hx : 0 < x
    · simp [posPart_def, hx, max_eq_left hx.le]
    · simp [posPart_def, hx, max_eq_right (le_of_not_gt hx)]
  simp [Matrix.trace, hr]

/-- For a trace-zero rank-one-minus-positive difference, the half trace norm
is its largest eigenvalue. No strict positivity or invertibility is required. -/
theorem rank_one_half_trace_norm {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (v : n → ℂ) {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (htr : (vecMulVec v (star v) - B).trace = 0) :
    IsGreatest (Set.range (rank_one_sub_hermitian v hB).eigenvalues)
      (traceNorm (vecMulVec v (star v) - B) / 2) := by
  classical
  let A := vecMulVec v (star v) - B
  let hA : A.IsHermitian := rank_one_sub_hermitian v hB
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.univ : Finset n)
    hA.eigenvalues Finset.univ_nonempty
  have hzero : ∑ i, hA.eigenvalues i = 0 := by
    have hh := congrArg Complex.re hA.trace_eq_sum_eigenvalues
    rw [htr] at hh
    simpa using hh.symm
  have hnonnegative : 0 ≤ hA.eigenvalues k := by
    by_contra hn
    have hneg : ∑ i, hA.eigenvalues i < 0 :=
      Finset.sum_neg (fun i _ => lt_of_le_of_lt (hk i (Finset.mem_univ i))
        (lt_of_not_ge hn)) Finset.univ_nonempty
    rw [hzero] at hneg
    exact lt_irrefl _ hneg
  have hother (i : n) (hik : i ≠ k) : hA.eigenvalues i ≤ 0 := by
    by_contra hn
    have hi := lt_of_not_ge hn
    have hp := hi.trans_le (hk i (Finset.mem_univ i))
    exact hik (positive_eigenvalues_unique v hB i k hi hp)
  have hsum : (∑ i, if 0 < hA.eigenvalues i then hA.eigenvalues i else 0) =
      hA.eigenvalues k := by
    rw [Finset.sum_eq_single k]
    · split_ifs with hp
      · rfl
      · exact (le_antisymm (le_of_not_gt hp) hnonnegative).symm
    · intro i _ hik
      exact if_neg (not_lt.mpr (hother i hik))
    · simp
  have hmass := trace_norm_jordan_mass A hA
  have hbalance : (posPart A).trace.re = (negPart A).trace.re := by
    have hh := congrArg (fun X : Matrix n n ℂ => X.trace.re)
      (CFC.posPart_sub_negPart A hA)
    rw [htr] at hh
    simpa only [Matrix.trace_sub, Complex.sub_re, Complex.zero_re, sub_eq_zero] using hh
  have hnorm : traceNorm A / 2 = hA.eigenvalues k := by
    rw [hmass, ← hbalance, positive_part_trace A hA, hsum]
    ring
  rw [show traceNorm (vecMulVec v (star v) - B) / 2 = hA.eigenvalues k from hnorm]
  exact ⟨⟨k, rfl⟩, fun x ⟨i, hi⟩ => hi ▸ hk i (Finset.mem_univ i)⟩

/-- The coherent target minus the recovered actual source, on a joint input.
Memory belongs to the output index and is untouched by the decoder. -/
def recoveryDifference {F : Type*} [Fintype F] [DecidableEq F]
    (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit))
    (rho : DensityState (F × Qubit)) :
    Matrix (F × (Qubit × (Qubit × Qubit))) (F × (Qubit × (Qubit × Qubit))) ℂ :=
  CStarMatrix.ofMatrix.symm (referenceState (targetChannel ell hl hu) rho).1 -
    CStarMatrix.ofMatrix.symm (referenceState ((receiverChannel (M := Qubit) D).comp
      (sourceChannel ell beta gamma w hl hu hb hw hmax)) rho).1

/-- On every normalized pure input and every finite reference, the half error
of the actual recovery problem is the largest eigenvalue of its output
difference. All CPTP receiver decoders and the boundary `ell = 0` are included. -/
theorem pure_reference_error_eq_top_eigenvalue {F : Type*} [Fintype F] [DecidableEq F]
    (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit))
    (v : F × Qubit → ℂ) (hv : star v ⬝ᵥ v = 1) :
    let rho := pureState v hv
    let A := recoveryDifference ell beta gamma w hl hu hb hw hmax D rho
    ∃ hA : A.IsHermitian, IsGreatest (Set.range hA.eigenvalues)
      (referenceError (targetChannel ell hl hu)
        ((receiverChannel (M := Qubit) D).comp
          (sourceChannel ell beta gamma w hl hu hb hw hmax)) rho / 2) := by
  classical
  intro rho A
  let target := referenceState (targetChannel ell hl hu) rho
  let actual := referenceState ((receiverChannel (M := Qubit) D).comp
    (sourceChannel ell beta gamma w hl hu hb hw hmax)) rho
  let t : F × (Qubit × (Qubit × Qubit)) → ℂ := fun p =>
    v (p.1, p.2.2.1) * xi ell (p.2.1, p.2.2.2)
  have ht : CStarMatrix.ofMatrix.symm target.1 = vecMulVec t (star t) := by
    ext ⟨f, m, j, a⟩ ⟨g, n, k, b⟩
    change referenceAction (targetChannel ell hl hu) rho.1
      (f, (m, (j, a))) (g, (n, (k, b))) = _
    rw [target_reference]
    simp only [rho, pureState, CStarMatrix.ofMatrix_apply,
      Matrix.vecMulVec_apply, t, Pi.star_apply, star_mul]
    ring
  let B := CStarMatrix.ofMatrix.symm actual.1
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm actual.2.1)
  have hA : A = vecMulVec t (star t) - B := by
    change CStarMatrix.ofMatrix.symm target.1 - B = _
    rw [ht]
  have htr : A.trace = 0 := by
    change (CStarMatrix.ofMatrix.symm target.1 - B).trace = 0
    rw [Matrix.trace_sub]
    change Matrix.trace target.1 - Matrix.trace actual.1 = 0
    rw [target.2.2, actual.2.2, sub_self]
  haveI : Nonempty (F × (Qubit × (Qubit × Qubit))) := by
    by_contra hn
    haveI : IsEmpty (F × (Qubit × (Qubit × Qubit))) := not_nonempty_iff.mp hn
    have hh := target.2.2
    simpa [Matrix.trace] using hh
  have hAH : A.IsHermitian := hA ▸ rank_one_sub_hermitian t hB
  refine ⟨hAH, ?_⟩
  change IsGreatest (Set.range hAH.eigenvalues) (traceNorm A / 2)
  clear_value A
  subst A
  exact rank_one_half_trace_norm t hB htr

private theorem eigenvalue_mem {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) (hx : x ≠ 0)
    (lambda : ℝ) (he : A *ᵥ x = (lambda : ℂ) • x) :
    lambda ∈ Set.range hA.eigenvalues := by
  have hv : Module.End.HasEigenvector A.toLin' (lambda : ℂ) x :=
    ⟨Module.End.mem_eigenspace_iff.mpr he, hx⟩
  have hs : (lambda : ℂ) ∈ spectrum ℂ A := by
    rw [← AlgEquiv.spectrum_eq Matrix.toLinAlgEquiv' A]
    exact (Module.End.hasEigenvalue_of_hasEigenvector hv).mem_spectrum
  have hsR : lambda ∈ spectrum ℝ A := spectrum.of_algebraMap_mem ℂ hs
  rwa [hA.spectrum_real_eq_range_eigenvalues] at hsR

private theorem eigenvector_norm {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) :
    star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ ⇑(hA.eigenvectorBasis i) = 1 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, hA.eigenvectorBasis.orthonormal.1 i]
  norm_num

private theorem maximum_eigenvalue_nonnegative {n : Type*}
    [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (htr : 0 ≤ A.trace.re) :
    ∃ k, 0 ≤ hA.eigenvalues k ∧ ∀ i, hA.eigenvalues i ≤ hA.eigenvalues k := by
  classical
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.univ : Finset n)
    hA.eigenvalues Finset.univ_nonempty
  refine ⟨k, ?_, fun i => hk i (Finset.mem_univ i)⟩
  by_contra hn
  have hh : ∑ i, hA.eigenvalues i < 0 :=
    Finset.sum_neg (fun i _ => lt_of_le_of_lt (hk i (Finset.mem_univ i))
      (lt_of_not_ge hn)) Finset.univ_nonempty
  have hsum := congrArg Complex.re hA.trace_eq_sum_eigenvalues
  simp only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] at hsum
  rw [← hsum] at hh
  exact (not_lt_of_ge htr) hh

theorem compression_retains_half_error {n m : Type*}
    [Fintype n] [DecidableEq n] [Nonempty n]
    [Fintype m] [DecidableEq m] [Nonempty m]
    (v : n → ℂ) {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (htr : (vecMulVec v (star v) - B).trace = 0)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) (t : m → ℂ) (hvt : V *ᵥ t = v)
    (hcomm : (vecMulVec v (star v) - B) * V =
      V * (Vᴴ * (vecMulVec v (star v) - B) * V))
    (hcTr : 0 ≤ (Vᴴ * (vecMulVec v (star v) - B) * V).trace.re) :
    ∃ hC : (Vᴴ * (vecMulVec v (star v) - B) * V).IsHermitian,
      IsGreatest (Set.range hC.eigenvalues)
        (traceNorm (vecMulVec v (star v) - B) / 2) := by
  classical
  let A := vecMulVec v (star v) - B
  let hA : A.IsHermitian := rank_one_sub_hermitian v hB
  let C := Vᴴ * A * V
  have hC : C.IsHermitian := by
    change (Vᴴ * A * V)ᴴ = Vᴴ * A * V
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]
  let E := traceNorm A / 2
  have hg : IsGreatest (Set.range hA.eigenvalues) E := rank_one_half_trace_norm v hB htr
  have hPush (i : m) : hC.eigenvalues i ∈ Set.range hA.eigenvalues := by
    let e : m → ℂ := ⇑(hC.eigenvectorBasis i)
    have he : V *ᵥ e ≠ 0 := by
      intro he
      have hh := congrArg (fun z => Vᴴ *ᵥ z) he
      rw [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec, Matrix.mulVec_zero] at hh
      have hn := eigenvector_norm hC i
      change star e ⬝ᵥ e = 1 at hn
      rw [hh] at hn
      simp at hn
    apply eigenvalue_mem hA (V *ᵥ e) he
    change A *ᵥ (V *ᵥ e) = (hC.eigenvalues i : ℂ) • (V *ᵥ e)
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec,
      hC.mulVec_eigenvectorBasis, Matrix.mulVec_smul]
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
  obtain ⟨k, hk0, hk⟩ := maximum_eigenvalue_nonnegative hC hcTr
  have htop_le : hC.eigenvalues k ≤ E := hg.2 (hPush k)
  have hnonneg : 0 ≤ E := div_nonneg (traceNorm_nonneg A) (by norm_num)
  have hmem : E ∈ Set.range hC.eigenvalues := by
    by_cases hE : E = 0
    · have hh : hC.eigenvalues k = E := le_antisymm htop_le (hE ▸ hk0)
      exact ⟨k, hh⟩
    have hEpos : 0 < E := lt_of_le_of_ne hnonneg (Ne.symm hE)
    obtain ⟨i, hi⟩ := hg.1
    let e : n → ℂ := ⇑(hA.eigenvectorBasis i)
    have he : A *ᵥ e = (E : ℂ) • e := by rw [← hi]; exact hA.mulVec_eigenvectorBasis i
    have hz : Vᴴ *ᵥ e ≠ 0 := by
      intro hz
      have hp : star v ⬝ᵥ e = 0 := by
        rw [← hvt, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hz, dotProduct_zero]
      have hh := quadratic_nonpositive_on_perp v hB e hp
      change (star e ⬝ᵥ (A *ᵥ e)).re ≤ 0 at hh
      rw [he, dotProduct_smul, eigenvector_norm hA i] at hh
      have hh' : E ≤ 0 := by simpa using hh
      exact (not_le_of_gt hEpos) hh'
    apply eigenvalue_mem hC (Vᴴ *ᵥ e) hz E
    have hcAdj : Vᴴ * A = C * Vᴴ := by
      change A * V = V * C at hcomm
      have hh := congrArg Matrix.conjTranspose hcomm
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hA.eq, hC.eq] using hh
    rw [Matrix.mulVec_mulVec, ← hcAdj, ← Matrix.mulVec_mulVec, he, Matrix.mulVec_smul]
  refine ⟨hC, hmem, ?_⟩
  rintro x ⟨i, rfl⟩
  exact (hk i).trans htop_le

open D5.S3.Quantum.Recovery.PhaseBoundaryFlagInstrument

/-- A canonical full receiver realization of one common flag instrument. -/
def instrumentRealization
    (Γ : FlagInstrument (S := Qubit) (J := Qubit) (A := Qubit) (B := Qubit)) :
    QuantumChannel (Qubit × Qubit) (Qubit × Qubit) :=
  (common_flag_instrument_complete.{0,0,0,0,0,0}.1 Γ).choose

theorem realization_entry
    (Γ : FlagInstrument (S := Qubit) (J := Qubit) (A := Qubit) (B := Qubit))
    (X : CStarMatrix (Qubit × Qubit) (Qubit × Qubit) ℂ)
    (j k a b : Qubit) :
    (instrumentRealization Γ).toCompletelyPositiveMap X (j,a) (k,b) =
      if j = k then ∑ s, Γ.operation j s
        (CStarMatrix.ofMatrix fun r t => X (s,r) (s,t)) a b else 0 := by
  have hh := (common_flag_instrument_complete.{0,0,0,0,0,0}.1 Γ).choose_spec.2 Unit
    (CStarMatrix.ofMatrix fun p q => X p.2 q.2)
  have he := congrArg (fun Y => Y ((),(j,a)) ((),(k,b))) hh
  exact he

/-- A diagonal-edge pure test input, with arbitrary complex amplitudes. -/
def diagonalInput (c : Qubit → ℂ) : Qubit × Qubit → ℂ :=
  fun p => if p.1 = p.2 then c p.1 else 0

theorem diagonal_input_norm (c : Qubit → ℂ) (hc : ∑ j, Complex.normSq (c j) = 1) :
    star (diagonalInput c) ⬝ᵥ diagonalInput c = 1 := by
  have hh : (∑ j, (Complex.normSq (c j) : ℂ)) = 1 := by exact_mod_cast hc
  simpa [diagonalInput, dotProduct, Fintype.sum_prod_type,
    Complex.normSq_eq_conj_mul_self, Complex.star_def] using hh

private abbrev Output := Qubit × (Qubit × Qubit)
private abbrev Full := Qubit × Output
private abbrev Matched := Qubit × (Qubit × Qubit)
private def matchEmbedding (p : Matched) : Full := (p.1,(p.2.1,(p.1,p.2.2)))
private def matchIsometry : Matrix Full Matched ℂ :=
  fun p t => if p = matchEmbedding t then 1 else 0

private theorem match_isometry : matchIsometryᴴ * matchIsometry = 1 := by
  ext ⟨j,m,a⟩ ⟨k,n,b⟩
  fin_cases j <;> fin_cases m <;> fin_cases a <;>
    fin_cases k <;> fin_cases n <;> fin_cases b <;>
    simp [matchIsometry, matchEmbedding, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]

private theorem match_compression (A : Matrix Full Full ℂ) :
    matchIsometryᴴ * A * matchIsometry = A.submatrix matchEmbedding matchEmbedding := by
  ext ⟨j,m,a⟩ ⟨k,n,b⟩
  fin_cases j <;> fin_cases m <;> fin_cases a <;>
    fin_cases k <;> fin_cases n <;> fin_cases b <;>
    simp [matchIsometry, matchEmbedding, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem match_mul_right (A : Matrix Full Full ℂ) (p : Full) (t : Matched) :
    (A * matchIsometry) p t = A p (matchEmbedding t) := by
  rcases p with ⟨f,m,j,a⟩
  rcases t with ⟨g,n,b⟩
  fin_cases g <;> fin_cases n <;> fin_cases b <;>
    simp [matchIsometry, matchEmbedding, Matrix.mul_apply, Fintype.sum_prod_type]

private theorem match_mul_left (C : Matrix Matched Matched ℂ)
    (p : Full) (t : Matched) :
    (matchIsometry * C) p t =
      if p.1 = p.2.2.1 then C (p.1,p.2.1,p.2.2.2) t else 0 := by
  rcases p with ⟨f,m,j,a⟩
  fin_cases f <;> fin_cases m <;> fin_cases j <;> fin_cases a <;>
    simp [matchIsometry, matchEmbedding, Matrix.mul_apply, Fintype.sum_prod_type]

/-- The actual matched-label block, with memory and receiver qubits retained. -/
def matchedBlock
    (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))
    (Γ : FlagInstrument (S := Qubit) (J := Qubit) (A := Qubit) (B := Qubit))
    (c : Qubit → ℂ) (hc : ∑ j, Complex.normSq (c j) = 1) : Matrix Matched Matched ℂ :=
  (recoveryDifference ell beta gamma w hl hu hb hw hmax (instrumentRealization Γ)
    (pureState (diagonalInput c) (diagonal_input_norm c hc))).submatrix
      matchEmbedding matchEmbedding

/-- Unmatched labels contribute no positive eigenvalues: for the same actual
common instrument, the half error of a diagonal-edge pure test input is the
largest eigenvalue of the matched-label block. -/
theorem matched_label_error_eq_top_eigenvalue
    (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))
    (Γ : FlagInstrument (S := Qubit) (J := Qubit) (A := Qubit) (B := Qubit))
    (c : Qubit → ℂ) (hc : ∑ j, Complex.normSq (c j) = 1) :
    ∃ hC : (matchedBlock ell beta gamma w hl hu hb hw hmax Γ c hc).IsHermitian,
      IsGreatest (Set.range hC.eigenvalues)
        (referenceError (targetChannel ell hl hu)
          ((receiverChannel (M := Qubit) (instrumentRealization Γ)).comp
            (sourceChannel ell beta gamma w hl hu hb hw hmax))
          (pureState (diagonalInput c) (diagonal_input_norm c hc)) / 2) := by
  classical
  let rho := pureState (diagonalInput c) (diagonal_input_norm c hc)
  let target := referenceState (targetChannel ell hl hu) rho
  let actual := referenceState ((receiverChannel (M := Qubit) (instrumentRealization Γ)).comp
    (sourceChannel ell beta gamma w hl hu hb hw hmax)) rho
  let B : Matrix Full Full ℂ := CStarMatrix.ofMatrix.symm actual.1
  let t : Matched → ℂ := fun p => c p.1 * xi ell p.2
  let v : Full → ℂ := fun p => diagonalInput c (p.1,p.2.2.1) * xi ell (p.2.1,p.2.2.2)
  have ht : CStarMatrix.ofMatrix.symm target.1 = vecMulVec v (star v) := by
    ext ⟨f,m,j,a⟩ ⟨g,n,k,b⟩
    change referenceAction (targetChannel ell hl hu) rho.1
      (f,(m,(j,a))) (g,(n,(k,b))) = _
    rw [target_reference]
    simp only [rho, pureState, CStarMatrix.ofMatrix_apply,
      Matrix.vecMulVec_apply, v, Pi.star_apply, star_mul]
    ring
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm actual.2.1)
  have htr : (vecMulVec v (star v) - B).trace = 0 := by
    rw [← ht, Matrix.trace_sub]
    change Matrix.trace target.1 - Matrix.trace actual.1 = 0
    rw [target.2.2, actual.2.2, sub_self]
  have hvt : matchIsometry *ᵥ t = v := by
    ext ⟨f,m,j,a⟩
    fin_cases f <;> fin_cases m <;> fin_cases j <;> fin_cases a <;>
      simp [matchIsometry, matchEmbedding, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, t, v, diagonalInput]
  have hBzero (p q : Full) (hpq : p.1 ≠ q.1 ∨ p.2.2.1 ≠ q.2.2.1) : B p q = 0 := by
    rcases p with ⟨f,m,j,a⟩
    rcases q with ⟨g,n,k,b⟩
    let X : CStarMatrix (Qubit × Qubit) (Qubit × Qubit) ℂ := CStarMatrix.ofMatrix
      fun s t => referenceAction (sourceChannel ell beta gamma w hl hu hb hw hmax)
        rho.1 (f,(m,s)) (g,(n,t))
    change referenceAction ((receiverChannel (M := Qubit) (instrumentRealization Γ)).comp
      (sourceChannel ell beta gamma w hl hu hb hw hmax)) rho.1
        (f,(m,(j,a))) (g,(n,(k,b))) = 0
    change referenceAction (receiverChannel (M := Qubit) (instrumentRealization Γ))
      (referenceAction (sourceChannel ell beta gamma w hl hu hb hw hmax) rho.1)
        (f,(m,(j,a))) (g,(n,(k,b))) = 0
    rw [PhaseBoundarySourceModel.receiver_reference]
    change (instrumentRealization Γ).toCompletelyPositiveMap X (j,a) (k,b) = 0
    rcases hpq with hfg | hjk
    · have hX : X = 0 := by
        ext ⟨s,r⟩ ⟨u,t⟩
        change referenceAction (sourceChannel ell beta gamma w hl hu hb hw hmax)
          rho.1 (f,(m,(s,r))) (g,(n,(u,t))) = 0
        rw [source_reference]
        have hz (i : Qubit) : rho.1 (f,i) (g,i) = 0 := by
          change diagonalInput c (f,i) * star (diagonalInput c (g,i)) = 0
          by_cases hfi : f = i
          · subst i
            simp [diagonalInput, Ne.symm hfg]
          · simp [diagonalInput, hfi]
        simp [hz]
      rw [hX, map_zero]
      rfl
    · rw [realization_entry, if_neg hjk]
  let A := vecMulVec v (star v) - B
  have hcomm : A * matchIsometry = matchIsometry * (matchIsometryᴴ * A * matchIsometry) := by
    rw [match_compression]
    ext p t
    rw [match_mul_right, match_mul_left]
    by_cases hp : p.1 = p.2.2.1
    · rw [if_pos hp]
      congr 2
      rcases p with ⟨f,m,j,a⟩
      dsimp at hp
      subst j
      rfl
    · rw [if_neg hp]
      change v p * star (v (matchEmbedding t)) - B p (matchEmbedding t) = 0
      have hvp : v p = 0 := by simp [v, diagonalInput, hp]
      have hbp : B p (matchEmbedding t) = 0 := by
        apply hBzero
        by_cases hf : p.1 = t.1
        · right
          simpa [matchEmbedding, ← hf] using Ne.symm hp
        · exact Or.inl hf
      rw [hvp, hbp, zero_mul, sub_self]
  have hcTr : 0 ≤ (matchIsometryᴴ * A * matchIsometry).trace.re := by
    rw [match_compression]
    have htotal : A.trace.re = 0 := by rw [htr]; rfl
    have hdiag (p : Full) (hp : p.1 ≠ p.2.2.1) : A p p ≤ 0 := by
      have hvp : v p = 0 := by simp [v, diagonalInput, hp]
      change v p * star (v p) - B p p ≤ 0
      rw [hvp, zero_mul, zero_sub]
      exact neg_nonpos.mpr hB.diag_nonneg
    have hsplit : A.trace = (A.submatrix matchEmbedding matchEmbedding).trace +
        ∑ p : Full, if p.1 ≠ p.2.2.1 then A p p else 0 := by
      simp [Matrix.trace, matchEmbedding, Fintype.sum_prod_type, Fin.sum_univ_two]
      ring
    have hn : (∑ p : Full, if p.1 ≠ p.2.2.1 then A p p else 0).re ≤ 0 := by
      rw [Complex.re_sum]
      apply Finset.sum_nonpos
      intro p _
      by_cases hp : p.1 ≠ p.2.2.1
      · rw [if_pos hp]
        exact (Complex.nonpos_iff.mp (hdiag p hp)).1
      · simp [hp]
    have hh := congrArg Complex.re hsplit
    rw [htotal, Complex.add_re] at hh
    linarith
  obtain ⟨hC,hg⟩ := compression_retains_half_error v hB htr
    matchIsometry match_isometry t hvt hcomm hcTr
  have hmatch : matchIsometryᴴ * A * matchIsometry =
      matchedBlock ell beta gamma w hl hu hb hw hmax Γ c hc := by
    rw [match_compression]
    change A.submatrix matchEmbedding matchEmbedding =
      (CStarMatrix.ofMatrix.symm target.1 - B).submatrix matchEmbedding matchEmbedding
    rw [ht]
  have herror : referenceError (targetChannel ell hl hu)
      ((receiverChannel (M := Qubit) (instrumentRealization Γ)).comp
        (sourceChannel ell beta gamma w hl hu hb hw hmax)) rho = traceNorm A := by
    change traceNorm (CStarMatrix.ofMatrix.symm target.1 - B) = traceNorm A
    rw [ht]
  rw [herror]
  rw [← hmatch]
  exact ⟨hC,hg⟩

end D5.S3.Quantum.Recovery.PhaseBoundarySpectralReduction
