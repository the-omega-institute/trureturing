/- GID: D5/S3/Quantum/ProcessReconstruction/SwapReconstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/SwapReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lit/huang2024learning, lit/arrighi2011unitarity, lit/schumacher2004reversible]
   utility: none
   digest: Finite local SWAP comparison and exact unitary channel reconstruction. -/

import D5.S3.Quantum.ProcessReconstruction.ReconstructionChannels

/-! Finite local SWAP comparison and exact unitary channel reconstruction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder CStarAlgebra Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance

namespace UnitaryReconstruction

universe u

variable {a b : Type u} {c r : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c] [Fintype r] [DecidableEq r]

/-- The Euclidean operator norm on finite matrices. -/
def opNorm (X : Matrix a a ℂ) : ℝ := ‖X‖

theorem opNorm_unitary_right (X : Matrix a a ℂ) (U : unitaryGroup a ℂ) :
    opNorm (X * U.val) = opNorm X := by
  exact CStarRing.norm_mul_mem_unitary X U.prop

theorem opNorm_unitary_left (U : unitaryGroup a ℂ) (X : Matrix a a ℂ) :
    opNorm (U.val * X) = opNorm X := by
  exact CStarRing.norm_mem_unitary_mul X U.prop

theorem opNorm_sub_mul (A B C D : unitaryGroup a ℂ) :
    opNorm (A.val * B.val - C.val * D.val) ≤
      opNorm (A.val - C.val) + opNorm (B.val - D.val) := by
  have h : A.val * B.val - C.val * D.val =
      (A.val - C.val) * B.val + C.val * (B.val - D.val) := by noncomm_ring
  rw [h]
  exact (norm_add_le ((A.val - C.val) * B.val)
    (C.val * (B.val - D.val))).trans_eq
    (congrArg₂ (· + ·) (opNorm_unitary_right _ B) (opNorm_unitary_left C _))

set_option linter.unusedDecidableInType false in
private theorem trace_vec (H : Matrix a a ℂ) (v : a → ℂ) :
    (H * vecMulVec v (star v)).trace = star v ⬝ᵥ (H *ᵥ v) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

private theorem eigenvector_unit (H : Matrix a a ℂ) (hH : H.IsHermitian) (i : a) :
    star (⇑(hH.eigenvectorBasis i)) ⬝ᵥ ⇑(hH.eigenvectorBasis i) = 1 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
    hH.eigenvectorBasis.orthonormal.1 i]
  norm_num

open scoped Matrix.Norms.L2Operator in
theorem opNorm_diagonal (v : a → ℂ) : opNorm (Matrix.diagonal v) = ‖v‖ :=
  Matrix.l2_opNorm_diagonal v

/-- A uniform bound on the absolute expectation of a Hermitian matrix in
unit vectors is an operator-norm bound. -/
theorem hermitian_opNorm_le (H : Matrix a a ℂ) (hH : H.IsHermitian)
    {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ v : a → ℂ, star v ⬝ᵥ v = 1 →
      |(H * vecMulVec v (star v)).trace.re| ≤ t) : opNorm H ≤ t := by
  rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
  change opNorm (hH.eigenvectorUnitary.val *
    diagonal (fun i => (hH.eigenvalues i : ℂ)) * (star hH.eigenvectorUnitary).val) ≤ t
  rw [opNorm_unitary_right, opNorm_unitary_left, opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg ht).mpr
  intro i
  let v : a → ℂ := ⇑(hH.eigenvectorBasis i)
  have hv : star v ⬝ᵥ v = 1 := eigenvector_unit H hH i
  have he : H *ᵥ v = (hH.eigenvalues i : ℂ) • v :=
    hH.mulVec_eigenvectorBasis i
  have hval := h v hv
  rw [trace_vec, he, dotProduct_smul, hv, smul_eq_mul, mul_one, Complex.ofReal_re] at hval
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hval

theorem reduced_trace_pairing (e : a ≃ c × b) (U : unitaryGroup a ℂ)
    (S : Matrix (r × b) (r × b) ℂ) (X : Matrix (r × a) (r × a) ℂ) :
    (((referenceUnitary r U).valᴴ * liftObservable e S * (referenceUnitary r U).val) *
      X).trace = (S * referenceMatrix (reducedConjugation e U) X).trace := by
  rw [reducedConjugation, referenceMatrix_comp, referenceMatrix_conjugation,
    ← trace_liftObservable]
  rw [Matrix.mul_assoc _ (liftObservable e S), Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem local_observable_bound (e : a ≃ c × b) (U V : unitaryGroup a ℂ)
    (S : unitaryGroup (r × b) ℂ) (hS : (liftObservable e S.val).IsHermitian) :
    opNorm ((referenceUnitary r U).valᴴ * liftObservable e S.val * (referenceUnitary r U).val -
      (referenceUnitary r V).valᴴ * liftObservable e S.val * (referenceUnitary r V).val) ≤
      diamondDistance (reducedConjugation e U) (reducedConjugation e V) := by
  apply hermitian_opNorm_le
  · apply Matrix.IsHermitian.sub
    · simpa only [Matrix.mul_assoc] using
        Matrix.isHermitian_conjTranspose_mul_mul (referenceUnitary r U).val hS
    · simpa only [Matrix.mul_assoc] using
        Matrix.isHermitian_conjTranspose_mul_mul (referenceUnitary r V).val hS
  · exact diamondDistance_nonneg' _ _
  intro v hv
  let X := vecMulVec v (star v)
  let Y := referenceMatrix (reducedConjugation e U) X -
    referenceMatrix (reducedConjugation e V) X
  rw [Matrix.sub_mul, Matrix.trace_sub, reduced_trace_pairing, reduced_trace_pairing]
  change |(((S.val * referenceMatrix (reducedConjugation e U) X).trace) -
    ((S.val * referenceMatrix (reducedConjugation e V) X).trace)).re| ≤ _
  rw [← Matrix.trace_sub, ← Matrix.mul_sub]
  change |(S.val * Y).trace.re| ≤ _
  have hplus := (traceNorm_eq_max_re_tr_U Y).2 (show
    (S.val * Y).trace.re ∈ {x : ℝ | ∃ W : unitaryGroup (r × b) ℂ,
      (W.val * Y).trace.re = x} from ⟨S, rfl⟩)
  have hminus := (traceNorm_eq_max_re_tr_U (-Y)).2 (show
    (S.val * -Y).trace.re ∈ {x : ℝ | ∃ W : unitaryGroup (r × b) ℂ,
      (W.val * -Y).trace.re = x} from ⟨S, rfl⟩)
  rw [Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re, traceNorm_neg] at hminus
  exact (abs_le.mpr ⟨by linarith, hplus⟩ : |(S.val * Y).trace.re| ≤ traceNorm Y).trans
    (referenceError_le_diamond _ _ (pureState v hv))

set_option linter.unusedFintypeInType false in
theorem perm_entry (p : Equiv.Perm a) (x y : a) :
    p.permMatrix ℂ x y = if p x = y then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

def permUnitary (p : Equiv.Perm a) : unitaryGroup a ℂ :=
  ⟨p.permMatrix ℂ, by
    apply Matrix.mem_unitaryGroup_iff.mpr
    change p.permMatrix ℂ * (p.permMatrix ℂ)ᴴ = 1
    rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
      Matrix.permMatrix_one]⟩

set_option linter.unusedFintypeInType false in
theorem perm_hermitian (p : Equiv.Perm a) (h : Function.Involutive p) :
    (p.permMatrix ℂ).IsHermitian := by
  change (p.permMatrix ℂ)ᴴ = _
  rw [Matrix.conjTranspose_permMatrix]
  congr 1
  ext x
  exact p.injective ((p.apply_symm_apply x).trans (h x).symm)

theorem perm_mul_apply (p : Equiv.Perm a) (X : Matrix a a ℂ) (x y : a) :
    (p.permMatrix ℂ * X) x y = X (p x) y := by
  simp [Matrix.mul_apply]

theorem mul_perm_apply (p : Equiv.Perm a) (X : Matrix a a ℂ) (x y : a) :
    (X * p.permMatrix ℂ) x y = X x (p.symm y) := by
  simp [Matrix.mul_apply, ← Equiv.eq_symm_apply]

abbrev fullSwap (a : Type*) : Equiv.Perm (a × a) := Equiv.prodComm a a

theorem fullSwap_sandwich (X : Matrix a a ℂ) :
    let P := (fullSwap a).permMatrix ℂ
    P * ((1 : Matrix a a ℂ) ⊗ₖ X) * P = X ⊗ₖ (1 : Matrix a a ℂ) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [mul_perm_apply, perm_mul_apply, Equiv.prodComm_apply, Equiv.prodComm_symm,
    Matrix.kroneckerMap_apply]
  exact mul_comm _ _

section Sites

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (d : ι → Type u)
  [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

abbrev System := ∀ i, d i

def splitSite (i : ι) : System d ≃ (∀ j : {j // j ≠ i}, d j) × d i :=
  (Equiv.piSplitAt i d).trans (Equiv.prodComm _ _)

/-- Swap the coordinates in the selected output sites with their reference copies. -/
def swapOn (s : Finset ι) : Equiv.Perm (System d × System d) where
  toFun p := (fun i => if i ∈ s then p.2 i else p.1 i,
    fun i => if i ∈ s then p.1 i else p.2 i)
  invFun p := (fun i => if i ∈ s then p.2 i else p.1 i,
    fun i => if i ∈ s then p.1 i else p.2 i)
  left_inv p := by
    apply Prod.ext <;> funext i <;> by_cases hi : i ∈ s <;> simp [hi]
  right_inv p := by
    apply Prod.ext <;> funext i <;> by_cases hi : i ∈ s <;> simp [hi]

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
theorem swapOn_involutive (s : Finset ι) : Function.Involutive (swapOn d s) :=
  (swapOn d s).left_inv

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
theorem swapOn_empty : swapOn d ∅ = 1 := by
  ext p : 1
  apply Prod.ext <;> funext i <;> simp [swapOn, Equiv.Perm.one_apply]

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
theorem swapOn_univ : swapOn d Finset.univ = fullSwap (System d) := by
  ext p : 1
  apply Prod.ext <;> funext i <;> simp [swapOn]

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
theorem swapOn_insert (s : Finset ι) (i : ι) (hi : i ∉ s) :
    swapOn d (insert i s) = swapOn d s * swapOn d {i} := by
  ext p : 1
  apply Prod.ext <;> funext j <;> by_cases hji : j = i
  all_goals
    first
    | subst j; simp [swapOn, hi, Equiv.Perm.mul_apply]
    | by_cases hj : j ∈ s <;> simp [swapOn, hji, hj, Equiv.Perm.mul_apply]

/-- The SWAP on the reduced output and the matching site inside its reference. -/
def reducedSwap (i : ι) : Equiv.Perm (System d × d i) where
  toFun p := ((splitSite d i).symm ((splitSite d i p.1).1,p.2), p.1 i)
  invFun p := ((splitSite d i).symm ((splitSite d i p.1).1,p.2), p.1 i)
  left_inv p := by
    have h : ∀ x : System d, (splitSite d i x).2 = x i := fun _ => rfl
    apply Prod.ext
    · apply (splitSite d i).injective
      simp only [Equiv.apply_symm_apply, ← h, Prod.mk.eta]
    · change ((splitSite d i).symm ((splitSite d i p.1).1,p.2)) i = p.2
      exact congrArg Prod.snd ((splitSite d i).apply_symm_apply ((splitSite d i p.1).1,p.2))
  right_inv p := by
    have h : ∀ x : System d, (splitSite d i x).2 = x i := fun _ => rfl
    apply Prod.ext
    · apply (splitSite d i).injective
      simp only [Equiv.apply_symm_apply, ← h, Prod.mk.eta]
    · change ((splitSite d i).symm ((splitSite d i p.1).1,p.2)) i = p.2
      exact congrArg Prod.snd ((splitSite d i).apply_symm_apply ((splitSite d i p.1).1,p.2))

set_option linter.unusedFintypeInType false in
theorem lift_reducedSwap (i : ι) :
    liftObservable (splitSite d i) ((reducedSwap d i).permMatrix ℂ) =
      (swapOn d {i}).permMatrix ℂ := by
  ext ⟨x,y⟩ ⟨x',y'⟩
  rw [perm_entry]
  change (if (splitSite d i y).1 = (splitSite d i y').1 then
    (reducedSwap d i).permMatrix ℂ (x,y i) (x',y' i) else 0) = _
  rw [perm_entry]
  rw [← ite_and]
  congr 1
  apply propext
  have hcomp (f : System d) : (splitSite d i f).1 = (fun j : {j // j ≠ i} => f j) := rfl
  have hsite (f : System d) : (splitSite d i f).2 = f i := rfl
  change (splitSite d i y).1 = (splitSite d i y').1 ∧
    ((splitSite d i).symm ((splitSite d i x).1, y i), x i) = (x', y' i) ↔
      swapOn d {i} (x,y) = (x',y')
  rw [Prod.mk.injEq, Equiv.symm_apply_eq, Prod.mk.injEq, Prod.ext_iff]
  rw [← (splitSite d i).apply_eq_iff_eq (x := (swapOn d {i} (x,y)).1),
      ← (splitSite d i).apply_eq_iff_eq (x := (swapOn d {i} (x,y)).2)]
  rw [Prod.ext_iff, Prod.ext_iff]
  have hfirst : (splitSite d i (swapOn d {i} (x,y)).1).1 = (splitSite d i x).1 := by
    rw [hcomp, hcomp]
    funext j
    simp [swapOn, j.prop]
  have hsecond : (splitSite d i (swapOn d {i} (x,y)).2).1 = (splitSite d i y).1 := by
    rw [hcomp, hcomp]
    funext j
    simp [swapOn, j.prop]
  rw [hfirst, hsecond]
  simp only [hsite, swapOn, Equiv.coe_fn_mk, Finset.mem_singleton, ite_true]
  tauto

def siteChannel (i : ι) (U : unitaryGroup (System d) ℂ) : QuantumChannel (System d) (d i) :=
  reducedConjugation (splitSite d i) U

def localError (i : ι) (U V : unitaryGroup (System d) ℂ) : ℝ :=
  diamondDistance (siteChannel d i U) (siteChannel d i V)

def conjugatedSwap (s : Finset ι) (U : unitaryGroup (System d) ℂ) :
    unitaryGroup (System d × System d) ℂ :=
  star (referenceUnitary (System d) U) * permUnitary (swapOn d s) * referenceUnitary (System d) U

theorem conjugatedSwap_local (i : ι) (U V : unitaryGroup (System d) ℂ) :
    opNorm ((conjugatedSwap d {i} U).val - (conjugatedSwap d {i} V).val) ≤ localError d i U V := by
  have hH : (liftObservable (splitSite d i) (permUnitary (reducedSwap d i)).val).IsHermitian := by
    change (liftObservable (splitSite d i) ((reducedSwap d i).permMatrix ℂ)).IsHermitian
    rw [lift_reducedSwap]
    exact perm_hermitian _ (swapOn_involutive d _)
  have h := local_observable_bound (splitSite d i) U V (permUnitary (reducedSwap d i)) hH
  change opNorm ((referenceUnitary (System d) U).valᴴ *
    liftObservable (splitSite d i) ((reducedSwap d i).permMatrix ℂ) *
      (referenceUnitary (System d) U).val -
    (referenceUnitary (System d) V).valᴴ *
    liftObservable (splitSite d i) ((reducedSwap d i).permMatrix ℂ) *
      (referenceUnitary (System d) V).val) ≤ localError d i U V at h
  rw [lift_reducedSwap] at h
  exact h

theorem conjugatedSwap_insert (s : Finset ι) (i : ι) (hi : i ∉ s)
    (U : unitaryGroup (System d) ℂ) :
    conjugatedSwap d (insert i s) U = conjugatedSwap d {i} U * conjugatedSwap d s U := by
  unfold conjugatedSwap
  rw [swapOn_insert d s i hi]
  have h (p q : Equiv.Perm (System d × System d)) :
      permUnitary (p * q) = permUnitary q * permUnitary p :=
    Subtype.ext (Matrix.permMatrix_mul p q)
  rw [h]
  generalize referenceUnitary (System d) U = B
  generalize permUnitary (swapOn d {i}) = S
  generalize permUnitary (swapOn d s) = T
  have hcancel : B * star B = 1 := Unitary.mul_star_self B
  simp only [mul_assoc]
  rw [← mul_assoc B, hcancel, one_mul]

theorem conjugatedSwap_bound (s : Finset ι) (U V : unitaryGroup (System d) ℂ) :
    opNorm ((conjugatedSwap d s U).val - (conjugatedSwap d s V).val) ≤
      ∑ i ∈ s, localError d i U V := by
  induction s using Finset.induction_on with
  | empty =>
    unfold conjugatedSwap
    rw [swapOn_empty]
    have h : permUnitary (1 : Equiv.Perm (System d × System d)) = 1 :=
      Subtype.ext Matrix.permMatrix_one
    rw [h]
    simp [opNorm]
  | @insert i s hi ih =>
    rw [conjugatedSwap_insert d s i hi, conjugatedSwap_insert d s i hi, Finset.sum_insert hi]
    exact (opNorm_sub_mul _ _ _ _).trans
      (add_le_add (conjugatedSwap_local d i U V) ih)

set_option maxHeartbeats 800000 in
-- Rewriting the nested Kronecker products needs additional elaboration time.
theorem fullSwap_sewing (U : unitaryGroup (System d) ℂ) :
    ((fullSwap (System d)).permMatrix ℂ) *
      (conjugatedSwap d Finset.univ U).val = U.valᴴ ⊗ₖ U.val := by
  unfold conjugatedSwap
  rw [swapOn_univ]
  change (fullSwap (System d)).permMatrix ℂ *
    (((1 : Matrix (System d) (System d) ℂ) ⊗ₖ U.val)ᴴ *
      (fullSwap (System d)).permMatrix ℂ * ((1 : Matrix (System d) (System d) ℂ) ⊗ₖ U.val)) = _
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, fullSwap_sandwich, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul]

set_option maxHeartbeats 800000 in
-- Rewriting the two doubled matrices at dependent coordinate types needs a larger budget.
/-- Huang et al., arXiv:2401.10095, §§2.1.2 and 5.2.2, use the local SWAP
sewing identity. Here each term is the unhalved diamond distance of two
single-output channels on the entire input. -/
theorem swap_sewing_opNorm_le (U V : unitaryGroup (System d) ℂ) :
    opNorm (U.valᴴ ⊗ₖ U.val - V.valᴴ ⊗ₖ V.val) ≤ ∑ i, localError d i U V := by
  rw [← fullSwap_sewing d U, ← fullSwap_sewing d V, ← Matrix.mul_sub]
  change opNorm ((permUnitary (fullSwap (System d))).val *
    ((conjugatedSwap d Finset.univ U).val - (conjugatedSwap d Finset.univ V).val)) ≤ _
  rw [opNorm_unitary_left]
  exact conjugatedSwap_bound d Finset.univ U V

theorem conjugation_eq_of_sewing_eq (U V : unitaryGroup (System d) ℂ)
    (h : U.valᴴ ⊗ₖ U.val = V.valᴴ ⊗ₖ V.val) :
    conjugation U = conjugation V := by
  apply channel_ext
  intro X
  apply CStarMatrix.ofMatrix.symm.injective
  rw [← CStarMatrix.ofMatrix.apply_symm_apply X]
  rw [conjugation_apply, conjugation_apply]
  ext i j
  simp only [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  have hkl := congrArg (fun A : Matrix (System d × System d) (System d × System d) ℂ =>
    A (k,i) (j,l)) h
  change U.valᴴ k j * U.val i l = V.valᴴ k j * V.val i l at hkl
  calc
    U.val i l * (CStarMatrix.ofMatrix.symm X) l k * U.valᴴ k j =
      (U.valᴴ k j * U.val i l) * (CStarMatrix.ofMatrix.symm X) l k := by ring
    _ = (V.valᴴ k j * V.val i l) * (CStarMatrix.ofMatrix.symm X) l k := by rw [hkl]
    _ = _ := by ring

theorem conjugation_eq_of_zero_localError (U V : unitaryGroup (System d) ℂ)
    (h : ∀ i, localError d i U V = 0) : conjugation U = conjugation V := by
  have hle := swap_sewing_opNorm_le d U V
  simp only [h, Finset.sum_const_zero] at hle
  have hz := norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact conjugation_eq_of_sewing_eq d U V
    (sub_eq_zero.mp hz)

theorem conjugation_eq_of_siteChannel_eq (U V : unitaryGroup (System d) ℂ)
    (h : ∀ i, siteChannel d i U = siteChannel d i V) : conjugation U = conjugation V := by
  apply conjugation_eq_of_zero_localError d U V
  intro i
  unfold localError
  rw [h i]
  apply le_antisymm _ (diamondDistance_nonneg' _ _)
  apply diamondDistance_le _ _ le_rfl
  intro n ρ
  simp [referenceError, traceNorm]

end Sites

end UnitaryReconstruction
