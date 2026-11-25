/- GID: D5/S3/Quantum/ProcessReconstruction/ParityFamily
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/ParityFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unital parity channels with equal proper marginals and diamond distance two. -/

import D5.S3.Quantum.ProcessReconstruction.ReconstructionChannels
import D5.S3.Quantum.Foundation.FinitePreparationChannel

/-! Unital parity channels with equal proper marginals and diamond distance two. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FinitePreparationChannel
open D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence

namespace UnitaryReconstruction.ParityFamily

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

abbrev Bits (ι : Type*) := ι → Bool

def bitSign (b : Bool) : ℝ := if b then -1 else 1

def paritySign (x : Bits ι) : ℝ := ∏ i, bitSign (x i)

omit [DecidableEq ι] in
theorem paritySign_sq (x : Bits ι) : paritySign x ^ 2 = 1 := by
  rw [paritySign, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  cases x i <;> norm_num [bitSign]

def toggle (i : ι) : Equiv.Perm (Bits ι) where
  toFun x := Function.update x i (!(x i))
  invFun x := Function.update x i (!(x i))
  left_inv x := by
    funext j
    by_cases h : j = i <;> simp [h, Function.update_of_ne]
  right_inv x := by
    funext j
    by_cases h : j = i <;> simp [h, Function.update_of_ne]

omit [Fintype ι] in
@[simp] theorem toggle_same (i : ι) (x : Bits ι) : toggle i x i = !(x i) := by
  simp [toggle]

omit [Fintype ι] in
@[simp] theorem toggle_other (i j : ι) (x : Bits ι) (h : j ≠ i) : toggle i x j = x j := by
  simp [toggle, Function.update_of_ne h]

theorem paritySign_toggle (i : ι) (x : Bits ι) : paritySign (toggle i x) = -paritySign x := by
  unfold paritySign
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [toggle_same]
  have h : (∏ j ∈ Finset.univ.erase i, bitSign (toggle i x j)) =
      ∏ j ∈ Finset.univ.erase i, bitSign (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [toggle_other _ _ _ (Finset.ne_of_mem_erase hj)]
  rw [h]
  cases x i <;> simp [bitSign]

theorem sum_paritySign (i : ι) : ∑ x : Bits ι, paritySign x = 0 := by
  have h := Equiv.sum_comp (toggle i) paritySign
  simp only [paritySign_toggle, Finset.sum_neg_distrib] at h
  linarith

def weight (s : Bool) (x : Bits ι) : ℝ :=
  (1 + bitSign s * paritySign x) / Fintype.card (Bits ι)

set_option linter.flexible false in
theorem weight_nonneg (s : Bool) (x : Bits ι) : 0 ≤ weight s x := by
  have h : paritySign x = 1 ∨ paritySign x = -1 := sq_eq_one_iff.mp (paritySign_sq x)
  rcases h with h | h <;> cases s <;> simp [weight, bitSign, h] <;> positivity

theorem sum_weight (i : ι) (s : Bool) : ∑ x : Bits ι, weight s x = 1 := by
  simp [weight, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, sum_paritySign i]

def parityState (i : ι) (s : Bool) : DensityState (Bits ι) :=
  ⟨CStarMatrix.ofMatrix (diagonal (fun x => (weight s x : ℂ))), by
    apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    apply (Matrix.posSemidef_diagonal_iff.mpr _).nonneg
    intro x
    exact_mod_cast weight_nonneg s x, by
    change (diagonal (fun x => (weight s x : ℂ))).trace = 1
    rw [Matrix.trace_diagonal]
    exact_mod_cast sum_weight i s⟩

def parityChannel (i : ι) (flip : Bool) : QuantumChannel (Bits ι) (Bits ι) :=
  (finite_preparation_quantum_channel (fun x : Bits ι => parityState i (x i ^^ flip))).choose

theorem parityChannel_apply (i : ι) (flip : Bool) (X : Matrix (Bits ι) (Bits ι) ℂ) :
    CStarMatrix.ofMatrix.symm ((parityChannel i flip).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix X)) =
      ∑ x : Bits ι, X x x • diagonal (fun y => (weight (x i ^^ flip) y : ℂ)) :=
  (finite_preparation_quantum_channel (fun x : Bits ι => parityState i (x i ^^ flip))).choose_spec X

theorem parityChannel_measure_prepare (i : ι) (flip : Bool) :
    ∃ (E : Bits ι → Matrix (Bits ι) (Bits ι) ℂ) (σ : Bits ι → DensityState (Bits ι)),
      (∀ x, (E x).PosSemidef) ∧ (∑ x, E x) = 1 ∧
      ∀ X : Matrix (Bits ι) (Bits ι) ℂ,
        CStarMatrix.ofMatrix.symm ((parityChannel i flip).toCompletelyPositiveMap
          (CStarMatrix.ofMatrix X)) =
          ∑ x, (E x * X).trace • CStarMatrix.ofMatrix.symm (σ x).1 := by
  let E : Bits ι → Matrix (Bits ι) (Bits ι) ℂ := fun x => diagonal (Pi.single x 1)
  refine ⟨E, fun x => parityState i (x i ^^ flip), ?_, ?_, ?_⟩
  · intro x
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro y
    by_cases h : x = y <;> simp [h, eq_comm]
  · ext x y
    rw [Matrix.sum_apply]
    by_cases h : x = y
    · subst y
      simp [E, Pi.single_apply]
    · simp [E, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  · intro X
    rw [parityChannel_apply]
    apply Finset.sum_congr rfl
    intro x _
    have h : (E x * X).trace = X x x := by
      simp [E, Matrix.trace, Matrix.diagonal_mul, Pi.single_apply]
    rw [h]
    rfl

theorem parityChannel_unital (i : ι) (flip : Bool) :
    (parityChannel i flip).toCompletelyPositiveMap 1 = 1 := by
  apply CStarMatrix.ofMatrix.symm.injective
  change CStarMatrix.ofMatrix.symm ((parityChannel i flip).toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (1 : Matrix (Bits ι) (Bits ι) ℂ))) = 1
  rw [parityChannel_apply]
  ext x y
  rw [Matrix.sum_apply]
  simp only [Matrix.one_apply_eq, one_smul]
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    have hsum : ∑ j : Bits ι, bitSign (j i ^^ flip) = 0 := by
      have h := Equiv.sum_comp (toggle i) (fun x => bitSign (x i ^^ flip))
      have hbit (x : Bits ι) : bitSign (toggle i x i ^^ flip) = -bitSign (x i ^^ flip) := by
        rw [toggle_same]
        cases x i <;> cases flip <;> simp [bitSign]
      simp only [hbit, Finset.sum_neg_distrib] at h
      linarith
    have hw : ∑ j : Bits ι, weight (j i ^^ flip) x = 1 := by
      simp [weight, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
    exact_mod_cast hw
  · simp [Matrix.diagonal_apply_ne _ hxy, Matrix.one_apply_ne hxy]

abbrev Kept (s : Finset ι) := Bits {j // j ∈ s}
abbrev Discarded (s : Finset ι) := Bits {j // j ∉ s}

def split (s : Finset ι) : Bits ι ≃ Discarded s × Kept s :=
  (Equiv.piEquivPiSubtypeProd (· ∈ s) (fun _ => Bool)).trans (Equiv.prodComm _ _)

theorem partialTrace_parity (s : Finset ι) (k : ι) (hk : k ∉ s) (b : Bool) :
    partialTraceFirst ((diagonal (fun x => (weight b x : ℂ))).submatrix
      (split s).symm (split s).symm) =
      ((Fintype.card (Discarded s) : ℂ) / Fintype.card (Bits ι)) •
        (1 : Matrix (Kept s) (Kept s) ℂ) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [partialTraceFirst, Matrix.submatrix_apply, Matrix.diagonal_apply_eq,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    have hswap (z : Discarded s) :
        (split s).symm (toggle ⟨k,hk⟩ z,x) = toggle k ((split s).symm (z,x)) := by
      funext j
      by_cases hz : j = k
      · subst j
        simp [split, hk, Equiv.piEquivPiSubtypeProd]
      · by_cases hm : j ∈ s
        · simp [split, hm, Equiv.piEquivPiSubtypeProd, toggle_other _ _ _ hz]
        · simp [split, hm, Equiv.piEquivPiSubtypeProd, toggle_other _ _ _ hz,
            show (⟨j,hm⟩ : {j // j ∉ s}) ≠ ⟨k,hk⟩ from fun he => hz (congrArg Subtype.val he)]
    have hsum : ∑ z : Discarded s, paritySign ((split s).symm (z,x)) = 0 := by
      have h := Equiv.sum_comp (toggle (⟨k,hk⟩ : {j // j ∉ s}))
        (fun z => paritySign ((split s).symm (z,x)))
      simp only [hswap, paritySign_toggle, Finset.sum_neg_distrib] at h
      linarith
    have hw : (∑ z : Discarded s, weight b ((split s).symm (z,x))) =
        (Fintype.card (Discarded s) : ℝ) / Fintype.card (Bits ι) := by
      simp [weight, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
    have hc := congrArg (fun u : ℝ => (u : ℂ)) hw
    push_cast at hc
    exact hc
  · have hne (z : Discarded s) : (split s).symm (z,x) ≠ (split s).symm (z,y) :=
      fun h => hxy (congrArg Prod.snd ((split s).symm.injective h))
    simp [partialTraceFirst, Matrix.one_apply_ne hxy,
      hne]

theorem parityChannel_proper_marginals (i : ι) (s : Finset ι) (hs : s ≠ Finset.univ) :
    (discard (split s)).comp (parityChannel i false) =
      (discard (split s)).comp (parityChannel i true) := by
  obtain ⟨k, hk⟩ : ∃ k, k ∉ s := by
    by_contra! h
    exact hs (Finset.eq_univ_iff_forall.mpr h)
  apply channel_ext
  intro X
  let Y := CStarMatrix.ofMatrix.symm X
  let M : Matrix (Kept s) (Kept s) ℂ :=
    ((Fintype.card (Discarded s) : ℂ) / Fintype.card (Bits ι)) • 1
  have happly (flip : Bool) :
      ((discard (split s)).comp (parityChannel i flip)).toCompletelyPositiveMap X =
        ∑ j : Bits ι, Y j j • CStarMatrix.ofMatrix M := by
    rw [QuantumChannel.comp_apply]
    have hy : (parityChannel i flip).toCompletelyPositiveMap X =
        ∑ j : Bits ι, Y j j • CStarMatrix.ofMatrix
          (diagonal (fun y => (weight (j i ^^ flip) y : ℂ))) := by
      have h := congrArg CStarMatrix.ofMatrix (parityChannel_apply i flip Y)
      simpa only [Y, Equiv.apply_symm_apply, CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv,
        map_sum, map_smul] using h
    rw [hy, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul]
    congr 1
    apply CStarMatrix.ofMatrix.symm.injective
    rw [discard_apply, Equiv.symm_apply_apply, partialTrace_parity s k hk]
  rw [happly false, happly true]

theorem parityChannel_maximal_diamond (i : ι) :
    diamondDistance (parityChannel i false) (parityChannel i true) = 2 := by
  apply le_antisymm
  · exact diamondDistance_le _ _ (by norm_num) fun _ => referenceError_le_two _ _
  let x₀ : Bits ι := fun _ => false
  let v : Unit × Bits ι → ℂ := Pi.single ((),x₀) 1
  have hv : star v ⬝ᵥ v = 1 := by simp [v, dotProduct, Pi.single_apply]
  let ρ := pureState v hv
  let A : Bool → Matrix (Unit × Bits ι) (Unit × Bits ι) ℂ :=
    fun flip => CStarMatrix.ofMatrix.symm (referenceState (parityChannel i flip) ρ).1
  have hA (flip : Bool) :
      A flip = diagonal (fun x : Unit × Bits ι => (weight flip x.2 : ℂ)) := by
    ext ⟨⟨⟩,x⟩ ⟨⟨⟩,y⟩
    change referenceMatrix (parityChannel i flip) (vecMulVec v (star v)) ((),x) ((),y) = _
    rw [referenceMatrix_apply]
    have h := congrArg (fun M : Matrix (Bits ι) (Bits ι) ℂ => M x y)
      (parityChannel_apply i flip (fun j k => vecMulVec v (star v) ((),j) ((),k)))
    change (parityChannel i flip).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix fun j k => vecMulVec v (star v) ((),j) ((),k)) x y = _ at h
    rw [h, Matrix.sum_apply]
    by_cases hxy : x = y
    · subst y
      simp [v, x₀, Pi.single_apply, Matrix.vecMulVec_apply,
        Matrix.smul_apply, smul_eq_mul, apply_ite, ite_mul]
    · simp [hxy]
  have hpos (flip : Bool) : (A flip).PosSemidef := by
    rw [hA, Matrix.posSemidef_diagonal_iff]
    intro x
    exact_mod_cast weight_nonneg flip x.2
  have htrace (flip : Bool) : (A flip).trace = 1 :=
    (referenceState (parityChannel i flip) ρ).2.2
  have hzero : A false * A true = 0 := by
    rw [hA false, hA true, Matrix.diagonal_mul_diagonal]
    ext x y
    by_cases h : x = y
    · subst y
      simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply]
      rw [← Complex.ofReal_mul]
      have h : paritySign x.2 = 1 ∨ paritySign x.2 = -1 :=
        sq_eq_one_iff.mp (paritySign_sq x.2)
      rcases h with h | h <;> simp [weight, bitSign, h]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.zero_apply]
  have h := referenceError_le_diamond (parityChannel i false) (parityChannel i true) ρ
  change traceNorm (A false - A true) ≤ _ at h
  rwa [traceNorm_sub_orthogonal _ _ (hpos false) (hpos true) hzero, htrace, htrace,
    Complex.one_re, one_add_one_eq_two] at h

end UnitaryReconstruction.ParityFamily
