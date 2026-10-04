/- GID: D5/S3/Quantum/Divergence/CanonicalChannelDPI
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/CanonicalChannelDPI
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Support-aware relative entropy decreases under finite quantum channels. -/

import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Abel
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy

namespace D5.S3.Quantum.Divergence.CanonicalChannelDPI

-- Nested finite carrier and spectral sums require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- Data processing for the canonical support-aware relative entropy, in natural logarithms. -/
theorem extended_quantum_relative_entropy_channel_dpi
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (ρ σ : DensityState a) :
    extendedQuantumRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) ≤
      extendedQuantumRelativeEntropy ρ σ := by
  classical
  by_cases support : SupportContained ρ σ
  ·
    classical
    let ea := Fintype.equivFin a
    let eb := Fintype.equivFin b
    let ra := CStarMatrix.reindexₐ ℂ ℂ ea
    let rb := CStarMatrix.reindexₐ ℂ ℂ eb
    let input : QuantumChannel (Fin (Fintype.card a)) a :=
      { toCompletelyPositiveMap :=
          CompletelyPositiveMapClass.toCompletelyPositiveLinearMap ra.symm
        trace_preserving := fun X => by
          change (∑ i : a, X (ea i) (ea i)) = ∑ i, X i i
          exact Fintype.sum_equiv ea _ _ (fun _ => rfl) }
    let output : QuantumChannel b (Fin (Fintype.card b)) :=
      { toCompletelyPositiveMap :=
          CompletelyPositiveMapClass.toCompletelyPositiveLinearMap rb
        trace_preserving := fun X => by
          change (∑ i : Fin (Fintype.card b), X (eb.symm i) (eb.symm i)) = ∑ i, X i i
          exact Fintype.sum_equiv eb.symm _ _ (fun _ => rfl) }
    let lifted := output.comp (Φ.comp input)
    obtain ⟨kf, hkf, hf⟩ :=
      D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.channel_kraus_stinespring.1 lifted
    let kraus := fun c => Matrix.reindex eb.symm ea.symm (kf c)
    have hkraus : (∑ c, (kraus c)ᴴ * kraus c) = 1 := by
      have heq : (∑ c, (kraus c)ᴴ * kraus c) =
          Matrix.reindex ea.symm ea.symm (∑ c, (kf c)ᴴ * kf c) := by
        ext i j
        simp only [Matrix.sum_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
        apply Finset.sum_congr rfl
        intro c _
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, kraus,
          Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
        exact Fintype.sum_equiv eb _ _ (fun x => by simp)
      rw [hkf] at heq
      simpa [Matrix.reindex_apply, Matrix.one_apply] using heq
    have haction (X : Matrix a a ℂ) :
        CStarMatrix.ofMatrix.symm
          (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          ∑ c, kraus c * X * (kraus c)ᴴ := by
      have h := hf (Matrix.reindex ea ea X)
      apply Matrix.reindex eb eb |>.injective
      change rb (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        Matrix.reindex eb eb (∑ c, kraus c * X * (kraus c)ᴴ)
      have hl : CStarMatrix.ofMatrix.symm
          (lifted.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.reindex ea ea X))) =
          rb (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) := by
        change rb (Φ.toCompletelyPositiveMap (ra.symm (ra (CStarMatrix.ofMatrix X)))) =
          rb (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))
        rw [StarAlgEquiv.symm_apply_apply]
      rw [hl] at h
      refine h.trans ?_
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro c _
      change (kf c * Matrix.reindex ea ea X * (kf c)ᴴ) i j =
        (kraus c * X * (kraus c)ᴴ) (eb.symm i) (eb.symm j)
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, kraus,
        Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        Equiv.apply_symm_apply]
      apply (Fintype.sum_equiv ea.symm _ _ ?_)
      intro k
      simp only [Equiv.apply_symm_apply]
      apply congrArg (fun t : ℂ => t * star (kf c j k))
      exact Fintype.sum_equiv ea.symm _ _ (fun _ => by simp)
    let κ := Fin (Fintype.card b) × Fin (Fintype.card a)
    let Ψ := fun Y : Matrix b b ℂ => ∑ c, (kraus c)ᴴ * Y * kraus c
    have adjointStar (Y : Matrix b b ℂ) : Ψ Yᴴ = (Ψ Y)ᴴ := by
      simp only [Ψ, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have schwarzFamily
        {α : Type u} {β : Type v} {κ : Type} [Fintype α] [DecidableEq α]
        [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ]
        (kraus : κ → Matrix β α ℂ)
        (hkraus : (∑ c, (kraus c)ᴴ * kraus c) = 1) :
        let Ψ := fun Y : Matrix β β ℂ => ∑ c, (kraus c)ᴴ * Y * kraus c
        ∀ Y, (Ψ Y)ᴴ * Ψ Y ≤ Ψ (Yᴴ * Y) := by
      classical
      let Ψ := fun Y : Matrix β β ℂ => ∑ c, (kraus c)ᴴ * Y * kraus c
      change ∀ Y, (Ψ Y)ᴴ * Ψ Y ≤ Ψ (Yᴴ * Y)
      let W : Matrix (β × κ) α ℂ := fun bc i => kraus bc.2 bc.1 i
      have hW : Wᴴ * W = 1 := by
        have heq : Wᴴ * W = ∑ c, (kraus c)ᴴ * kraus c := by
          ext i j
          change (∑ bc : β × κ, star (kraus bc.2 bc.1 i) * kraus bc.2 bc.1 j) =
            (∑ c, (kraus c)ᴴ * kraus c) i j
          simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Fintype.sum_prod_type]
          rw [Finset.sum_comm]
        rw [heq, hkraus]
      have action (Y : Matrix β β ℂ) :
          Wᴴ * Matrix.blockDiagonal (fun _ : κ => Y) * W = Ψ Y := by
        ext i j
        dsimp only [Ψ]
        rw [Matrix.sum_apply]
        change (∑ bc : β × κ, (∑ bd : β × κ,
            star (kraus bd.2 bd.1 i) *
              (if bd.2 = bc.2 then Y bd.1 bc.1 else 0)) * kraus bc.2 bc.1 j) =
          ∑ c : κ, ∑ x : β, (∑ y : β, star (kraus c y i) * Y y x) * kraus c x j
        simp only [Fintype.sum_prod_type, mul_ite, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [Finset.sum_comm]
      have schwarz (Y : Matrix (β × κ) (β × κ) ℂ) :
          (Wᴴ * Y * W)ᴴ * (Wᴴ * Y * W) ≤ Wᴴ * (Yᴴ * Y) * W := by
        have hid : (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ := by
          calc
            (W * Wᴴ) * (W * Wᴴ) = W * (Wᴴ * W) * Wᴴ := by
              simp only [Matrix.mul_assoc]
            _ = W * Wᴴ := by rw [hW, Matrix.mul_one]
        have hp : (1 - W * Wᴴ)ᴴ * (1 - W * Wᴴ) = 1 - W * Wᴴ := by
          rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
            Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, hid]
          abel
        have hpos : (1 - W * Wᴴ).PosSemidef := by
          rw [← hp]
          exact Matrix.posSemidef_conjTranspose_mul_self _
        have hfactor := hpos.mul_mul_conjTranspose_same (Wᴴ * Yᴴ)
        apply Matrix.le_iff.mpr
        simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc] using hfactor
      intro Y
      have h := schwarz (Matrix.blockDiagonal (fun _ : κ => Y))
      rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
        action, action] at h
      exact h
    have schwarzRight : ∀ Y : Matrix b b ℂ, (Ψ Y)ᴴ * Ψ Y ≤ Ψ (Yᴴ * Y) :=
      by
        simpa only [Ψ] using
          schwarzFamily (α := a) (β := b) (κ := κ) kraus hkraus
    have schwarzLeft (Y : Matrix b b ℂ) : Ψ Y * (Ψ Y)ᴴ ≤ Ψ (Y * Yᴴ) := by
      simpa only [adjointStar, Matrix.conjTranspose_conjTranspose] using schwarzRight Yᴴ
    have tracePair (X : Matrix a a ℂ) (Y : Matrix b b ℂ) :
        Matrix.trace (X * Ψ Y) =
          Matrix.trace (CStarMatrix.ofMatrix.symm
            (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) * Y) := by
      rw [haction X]
      change Matrix.trace (X * (∑ c, (kraus c)ᴴ * Y * kraus c)) = _
      rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro c _
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_cycle (X * (kraus c)ᴴ) Y (kraus c)
    have quadratic (X : Matrix a a ℂ) (y : b → ℂ) :
        star y ⬝ᵥ (∑ c, kraus c * X * (kraus c)ᴴ) *ᵥ y =
          ∑ c, star ((kraus c)ᴴ *ᵥ y) ⬝ᵥ X *ᵥ ((kraus c)ᴴ *ᵥ y) := by
      rw [Matrix.sum_mulVec, dotProduct_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec]
      have hv : star y ᵥ* kraus c = star ((kraus c)ᴴ *ᵥ y) := by
        simpa only [Matrix.conjTranspose_conjTranspose, star_star] using
          Matrix.vecMul_conjTranspose ((kraus c)ᴴ) (star y)
      rw [hv]
    have kernel (X : Matrix a a ℂ) (hX : X.PosSemidef) (y : b → ℂ) :
        (∑ c, kraus c * X * (kraus c)ᴴ) *ᵥ y = 0 ↔
          ∀ c, X *ᵥ ((kraus c)ᴴ *ᵥ y) = 0 := by
      constructor
      · intro hy
        have hsum : ∑ c, star ((kraus c)ᴴ *ᵥ y) ⬝ᵥ
            X *ᵥ ((kraus c)ᴴ *ᵥ y) = 0 := by
          rw [← quadratic X y, hy, dotProduct_zero]
        have hz := (Finset.sum_eq_zero_iff_of_nonneg
          (fun c (_ : c ∈ (Finset.univ : Finset (Fin (Fintype.card b) × Fin (Fintype.card a)))) =>
            hX.dotProduct_mulVec_nonneg ((kraus c)ᴴ *ᵥ y))).mp hsum
        intro c
        exact (hX.dotProduct_mulVec_zero_iff _).mp (hz c (Finset.mem_univ _))
      · intro hz
        rw [Matrix.sum_mulVec]
        apply Finset.sum_eq_zero
        intro c _
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz c, Matrix.mulVec_zero]
    have outputSupport : SupportContained (Φ.mapState ρ) (Φ.mapState σ) := by
      intro y hy
      change (CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap σ.1)) *ᵥ y = 0 at hy
      change (CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap ρ.1)) *ᵥ y = 0
      let R : Matrix a a ℂ := CStarMatrix.ofMatrix.symm ρ.1
      let S : Matrix a a ℂ := CStarMatrix.ofMatrix.symm σ.1
      have hS : S.PosSemidef :=
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.2.1).posSemidef
      have hyS : (∑ c, kraus c * S * (kraus c)ᴴ) *ᵥ y = 0 := by
        rw [← haction S]
        exact hy
      have hzero := (kernel S hS y).mp hyS
      have hrAction := haction R
      simp only [R, Equiv.apply_symm_apply] at hrAction
      rw [hrAction, Matrix.sum_mulVec]
      apply Finset.sum_eq_zero
      intro c _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have hs : S *ᵥ ((kraus c)ᴴ *ᵥ y) = 0 := hzero c
      have hr : R *ᵥ ((kraus c)ᴴ *ᵥ y) = 0 := support hs
      rw [hr, Matrix.mulVec_zero]
    rw [extendedQuantumRelativeEntropy_eq_coe_of_support outputSupport,
      extendedQuantumRelativeEntropy_eq_coe_of_support support]
    apply WithTop.coe_le_coe.mpr
    let R : Matrix a a ℂ := CStarMatrix.ofMatrix.symm ρ.1
    let S : Matrix a a ℂ := CStarMatrix.ofMatrix.symm σ.1
    let T : Matrix b b ℂ := CStarMatrix.ofMatrix.symm (Φ.mapState ρ).1
    let Q : Matrix b b ℂ := CStarMatrix.ofMatrix.symm (Φ.mapState σ).1
    have hR : R.PosSemidef :=
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1).posSemidef
    have hS : S.PosSemidef :=
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.2.1).posSemidef
    have hT : T.PosSemidef :=
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (Φ.mapState ρ).2.1).posSemidef
    have hQ : Q.PosSemidef :=
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (Φ.mapState σ).2.1).posSemidef
    let I := {i : a // 0 < hR.1.eigenvalues i}
    let J := {j : a // 0 < hS.1.eigenvalues j}
    let K := {k : b // 0 < hT.1.eigenvalues k}
    let L := {l : b // 0 < hQ.1.eigenvalues l}
    let ri : I → ℝ := fun i => hR.1.eigenvalues i.1
    let sj : J → ℝ := fun j => hS.1.eigenvalues j.1
    let pk : K → ℝ := fun k => hT.1.eigenvalues k.1
    let ql : L → ℝ := fun l => hQ.1.eigenvalues l.1
    let u : I → a → ℂ := fun i x => hR.1.eigenvectorBasis i.1 x
    let v : J → a → ℂ := fun j x => hS.1.eigenvectorBasis j.1 x
    let z : K → b → ℂ := fun k x => hT.1.eigenvectorBasis k.1 x
    let w : L → b → ℂ := fun l x => hQ.1.eigenvectorBasis l.1 x
    let A : Matrix (J × I) (J × I) ℂ :=
      Matrix.diagonal (fun ji => (sj ji.1 / ri ji.2 : ℝ))
    let B : Matrix (L × K) (L × K) ℂ :=
      Matrix.diagonal (fun lk => (ql lk.1 / pk lk.2 : ℝ))
    let ξ : J × I → ℂ :=
      fun ji => (Real.sqrt (ri ji.2) : ℂ) * (star (v ji.1) ⬝ᵥ u ji.2)
    let η : L × K → ℂ :=
      fun lk => (Real.sqrt (pk lk.2) : ℂ) * (star (w lk.1) ⬝ᵥ z lk.2)
    let V : Matrix (J × I) (L × K) ℂ := fun ji lk =>
      (Real.sqrt (ri ji.2) / Real.sqrt (pk lk.2) : ℂ) *
        ∑ c, (star (v ji.1) ⬝ᵥ ((kraus c)ᴴ *ᵥ w lk.1)) *
          (star (z lk.2) ⬝ᵥ (kraus c *ᵥ u ji.2))
    have htrR : R.trace = 1 := ρ.2.2
    have htrT : T.trace = 1 := (Φ.mapState ρ).2.2
    have positiveCoordinatesR :
        ∀ i : {i : a // 0 < hR.1.eigenvalues i},
          ∑ j : {j : a // 0 < hS.1.eigenvalues j},
            ‖star (fun x => hS.1.eigenvectorBasis j.1 x) ⬝ᵥ
              (fun x => hR.1.eigenvectorBasis i.1 x)‖ ^ 2 = 1 := by
      classical
      have zero (j : a) (hj : hS.1.eigenvalues j = 0)
          (i : a) (hi : 0 < hR.1.eigenvalues i) :
          star (fun x => hS.1.eigenvectorBasis j x) ⬝ᵥ
            (fun x => hR.1.eigenvectorBasis i x) = 0 := by
        let v : a → ℂ := fun x => hS.1.eigenvectorBasis j x
        let u : a → ℂ := fun x => hR.1.eigenvectorBasis i x
        have hsv : S *ᵥ v = 0 := by
          simpa only [hj, zero_smul] using hS.1.mulVec_eigenvectorBasis j
        have hrv : R *ᵥ v = 0 := support hsv
        have hv : star v ᵥ* R = star (R *ᵥ v) := by
          simpa only [hR.1.eq, star_star] using Matrix.vecMul_conjTranspose R (star v)
        have hz : star v ⬝ᵥ (R *ᵥ u) = 0 := by
          rw [dotProduct_mulVec, hv, hrv]
          simp
        rw [hR.1.mulVec_eigenvectorBasis i, dotProduct_smul] at hz
        change (hR.1.eigenvalues i : ℂ) * (star v ⬝ᵥ u) = 0 at hz
        exact (mul_eq_zero.mp hz).resolve_left
          (Complex.ofReal_ne_zero.mpr (ne_of_gt hi))
      intro i
      have total : (∑ j : a,
          ‖star (fun x => hS.1.eigenvectorBasis j x) ⬝ᵥ
            (fun x => hR.1.eigenvectorBasis i.1 x)‖ ^ 2) = 1 := by
        have h := hS.1.eigenvectorBasis.sum_sq_norm_inner_right (hR.1.eigenvectorBasis i.1)
        rw [hR.1.eigenvectorBasis.orthonormal.1 i.1, one_pow] at h
        calc
          _ = ∑ j : a, ‖inner ℂ (hS.1.eigenvectorBasis j)
              (hR.1.eigenvectorBasis i.1)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [EuclideanSpace.inner_eq_star_dotProduct]
            congr 2
            exact dotProduct_comm _ _
          _ = 1 := h
      have complement : (∑ j : {j : a // ¬0 < hS.1.eigenvalues j},
          ‖star (fun x => hS.1.eigenvectorBasis j.1 x) ⬝ᵥ
            (fun x => hR.1.eigenvectorBasis i.1 x)‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have hj : hS.1.eigenvalues j.1 = 0 :=
          le_antisymm (le_of_not_gt j.2) (hS.eigenvalues_nonneg j.1)
        rw [zero j.1 hj i.1 i.2, norm_zero, zero_pow (by decide)]
      have h := Fintype.sum_subtype_add_sum_subtype
        (fun j : a => 0 < hS.1.eigenvalues j)
        (fun j : a => ‖star (fun x => hS.1.eigenvectorBasis j x) ⬝ᵥ
          (fun x => hR.1.eigenvectorBasis i.1 x)‖ ^ 2)
      rw [complement, add_zero, total] at h
      exact h
    have normξ : (∑ ji, ‖ξ ji‖ ^ 2) = 1 := by
      dsimp only [ξ, ri, v, u]
      let I := {i : a // 0 < hR.1.eigenvalues i}
      let J := {j : a // 0 < hS.1.eigenvalues j}
      have all : (∑ i : a, hR.1.eigenvalues i) = 1 := by
        have h := hR.1.trace_eq_sum_eigenvalues
        rw [htrR] at h
        have hre := congrArg Complex.re h
        simpa using hre.symm
      have complement : (∑ i : {i : a // ¬0 < hR.1.eigenvalues i},
          hR.1.eigenvalues i.1) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact le_antisymm (le_of_not_gt i.2) (hR.eigenvalues_nonneg i.1)
      have mass : (∑ i : I, hR.1.eigenvalues i.1) = 1 := by
        have h := Fintype.sum_subtype_add_sum_subtype
          (fun i : a => 0 < hR.1.eigenvalues i) hR.1.eigenvalues
        rw [complement, add_zero, all] at h
        exact h
      have overlap := positiveCoordinatesR
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      calc
        _ = ∑ i : I, hR.1.eigenvalues i.1 *
            ∑ j : J, ‖star (fun x => hS.1.eigenvectorBasis j.1 x) ⬝ᵥ
              (fun x => hR.1.eigenvectorBasis i.1 x)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [norm_mul, mul_pow]
          congr 1
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt i.2)]
        _ = 1 := by
          calc
            _ = ∑ i : I, hR.1.eigenvalues i.1 := by
              apply Finset.sum_congr rfl
              intro i _
              simpa only [mul_one] using
                congrArg (fun t : ℝ => hR.1.eigenvalues i.1 * t) (overlap i)
            _ = 1 := mass
    have positiveCoordinatesT :
        ∀ i : {i : b // 0 < hT.1.eigenvalues i},
          ∑ j : {j : b // 0 < hQ.1.eigenvalues j},
            ‖star (fun x => hQ.1.eigenvectorBasis j.1 x) ⬝ᵥ
              (fun x => hT.1.eigenvectorBasis i.1 x)‖ ^ 2 = 1 := by
      classical
      have zero (j : b) (hj : hQ.1.eigenvalues j = 0)
          (i : b) (hi : 0 < hT.1.eigenvalues i) :
          star (fun x => hQ.1.eigenvectorBasis j x) ⬝ᵥ
            (fun x => hT.1.eigenvectorBasis i x) = 0 := by
        let v : b → ℂ := fun x => hQ.1.eigenvectorBasis j x
        let u : b → ℂ := fun x => hT.1.eigenvectorBasis i x
        have hsv : Q *ᵥ v = 0 := by
          simpa only [hj, zero_smul] using hQ.1.mulVec_eigenvectorBasis j
        have hrv : T *ᵥ v = 0 := outputSupport hsv
        have hv : star v ᵥ* T = star (T *ᵥ v) := by
          simpa only [hT.1.eq, star_star] using Matrix.vecMul_conjTranspose T (star v)
        have hz : star v ⬝ᵥ (T *ᵥ u) = 0 := by
          rw [dotProduct_mulVec, hv, hrv]
          simp
        rw [hT.1.mulVec_eigenvectorBasis i, dotProduct_smul] at hz
        change (hT.1.eigenvalues i : ℂ) * (star v ⬝ᵥ u) = 0 at hz
        exact (mul_eq_zero.mp hz).resolve_left
          (Complex.ofReal_ne_zero.mpr (ne_of_gt hi))
      intro i
      have total : (∑ j : b,
          ‖star (fun x => hQ.1.eigenvectorBasis j x) ⬝ᵥ
            (fun x => hT.1.eigenvectorBasis i.1 x)‖ ^ 2) = 1 := by
        have h := hQ.1.eigenvectorBasis.sum_sq_norm_inner_right (hT.1.eigenvectorBasis i.1)
        rw [hT.1.eigenvectorBasis.orthonormal.1 i.1, one_pow] at h
        calc
          _ = ∑ j : b, ‖inner ℂ (hQ.1.eigenvectorBasis j)
              (hT.1.eigenvectorBasis i.1)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [EuclideanSpace.inner_eq_star_dotProduct]
            congr 2
            exact dotProduct_comm _ _
          _ = 1 := h
      have complement : (∑ j : {j : b // ¬0 < hQ.1.eigenvalues j},
          ‖star (fun x => hQ.1.eigenvectorBasis j.1 x) ⬝ᵥ
            (fun x => hT.1.eigenvectorBasis i.1 x)‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have hj : hQ.1.eigenvalues j.1 = 0 :=
          le_antisymm (le_of_not_gt j.2) (hQ.eigenvalues_nonneg j.1)
        rw [zero j.1 hj i.1 i.2, norm_zero, zero_pow (by decide)]
      have h := Fintype.sum_subtype_add_sum_subtype
        (fun j : b => 0 < hQ.1.eigenvalues j)
        (fun j : b => ‖star (fun x => hQ.1.eigenvectorBasis j x) ⬝ᵥ
          (fun x => hT.1.eigenvectorBasis i.1 x)‖ ^ 2)
      rw [complement, add_zero, total] at h
      exact h
    have normη : (∑ ji, ‖η ji‖ ^ 2) = 1 := by
      dsimp only [η, pk, w, z]
      let I := {i : b // 0 < hT.1.eigenvalues i}
      let J := {j : b // 0 < hQ.1.eigenvalues j}
      have all : (∑ i : b, hT.1.eigenvalues i) = 1 := by
        have h := hT.1.trace_eq_sum_eigenvalues
        rw [htrT] at h
        have hre := congrArg Complex.re h
        simpa using hre.symm
      have complement : (∑ i : {i : b // ¬0 < hT.1.eigenvalues i},
          hT.1.eigenvalues i.1) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact le_antisymm (le_of_not_gt i.2) (hT.eigenvalues_nonneg i.1)
      have mass : (∑ i : I, hT.1.eigenvalues i.1) = 1 := by
        have h := Fintype.sum_subtype_add_sum_subtype
          (fun i : b => 0 < hT.1.eigenvalues i) hT.1.eigenvalues
        rw [complement, add_zero, all] at h
        exact h
      have overlap := positiveCoordinatesT
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      calc
        _ = ∑ i : I, hT.1.eigenvalues i.1 *
            ∑ j : J, ‖star (fun x => hQ.1.eigenvectorBasis j.1 x) ⬝ᵥ
              (fun x => hT.1.eigenvectorBasis i.1 x)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [norm_mul, mul_pow]
          congr 1
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt i.2)]
        _ = 1 := by
          calc
            _ = ∑ i : I, hT.1.eigenvalues i.1 := by
              apply Finset.sum_congr rfl
              intro i _
              simpa only [mul_one] using
                congrArg (fun t : ℝ => hT.1.eigenvalues i.1 * t) (overlap i)
            _ = 1 := mass
    have hA : A.PosDef := by
      apply Matrix.PosDef.diagonal
      intro ji
      exact_mod_cast div_pos ji.1.2 ji.2.2
    have hB : B.PosDef := by
      apply Matrix.PosDef.diagonal
      intro lk
      exact_mod_cast div_pos lk.1.2 lk.2.2
    have inputLog (X : DensityState a)
        (hX : (CStarMatrix.ofMatrix.symm X.1).IsHermitian) :
        CStarMatrix.ofMatrix (cfc Real.log (CStarMatrix.ofMatrix.symm X.1)) =
          CFC.log X.1 := by
      exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log _
        ((CStarMatrix.ofMatrix.symm X.1).finite_real_spectrum.continuousOn _)
        CStarMatrix.ofMatrixL.continuous hX (by exact hX)
    have outputLog (X : DensityState b)
        (hX : (CStarMatrix.ofMatrix.symm X.1).IsHermitian) :
        CStarMatrix.ofMatrix (cfc Real.log (CStarMatrix.ofMatrix.symm X.1)) =
          CFC.log X.1 := by
      exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log _
        ((CStarMatrix.ofMatrix.symm X.1).finite_real_spectrum.continuousOn _)
        CStarMatrix.ofMatrixL.continuous hX (by exact hX)
    have hlogR := inputLog ρ hR.1
    have hlogS := inputLog σ hS.1
    have hlogT := outputLog (Φ.mapState ρ) hT.1
    have hlogQ := outputLog (Φ.mapState σ) hQ.1
    unfold finiteTraceLogRelativeEntropy
    rw [← hlogT, ← hlogQ, ← hlogR, ← hlogS]
    change (Matrix.trace (T * (cfc Real.log T - cfc Real.log Q))).re ≤
      (Matrix.trace (R * (cfc Real.log R - cfc Real.log S))).re
    skip
  · rw [extendedQuantumRelativeEntropy_eq_top_of_not_support support]
    exact le_top

end D5.S3.Quantum.Divergence.CanonicalChannelDPI
