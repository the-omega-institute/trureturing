/- GID: D5/S3/Quantum/Divergence/CanonicalChannelDPI
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/CanonicalChannelDPI
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Support-aware relative entropy decreases under finite quantum channels. -/

import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import D5.S3.Weil.ZetaLinear.HermitianPosPart
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Abel
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Topology
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
    let ea := Fintype.equivFin a; let eb := Fintype.equivFin b; let ra := CStarMatrix.reindexₐ ℂ ℂ ea; let rb := CStarMatrix.reindexₐ ℂ ℂ eb
    let input : QuantumChannel (Fin (Fintype.card a)) a :=
      { toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap ra.symm
        trace_preserving := fun X => by
          change (∑ i : a, X (ea i) (ea i)) = ∑ i, X i i; exact Fintype.sum_equiv ea _ _ (fun _ => rfl) }
    let output : QuantumChannel b (Fin (Fintype.card b)) :=
      { toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap rb
        trace_preserving := fun X => by
          change (∑ i : Fin (Fintype.card b), X (eb.symm i) (eb.symm i)) = ∑ i, X i i; exact Fintype.sum_equiv eb.symm _ _ (fun _ => rfl) }
    let lifted := output.comp (Φ.comp input); obtain ⟨kf, hkf, hf⟩ := D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.channel_kraus_stinespring.1 lifted
    let kraus := fun c => Matrix.reindex eb.symm ea.symm (kf c); have hkraus : (∑ c, (kraus c)ᴴ * kraus c) = 1 := by
      have heq : (∑ c, (kraus c)ᴴ * kraus c) = Matrix.reindex ea.symm ea.symm (∑ c, (kf c)ᴴ * kf c) := by
        ext i j; simp only [Matrix.sum_apply, Matrix.reindex_apply, Matrix.submatrix_apply]; apply Finset.sum_congr rfl; intro c _
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, kraus, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
        exact Fintype.sum_equiv eb _ _ (fun x => by simp)
      rw [hkf] at heq; simpa [Matrix.reindex_apply, Matrix.one_apply] using heq
    have haction (X : Matrix a a ℂ) : CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = ∑ c, kraus c * X * (kraus c)ᴴ := by
      have h := hf (Matrix.reindex ea ea X); apply Matrix.reindex eb eb |>.injective; change rb (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        Matrix.reindex eb eb (∑ c, kraus c * X * (kraus c)ᴴ)
      have hl : CStarMatrix.ofMatrix.symm (lifted.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.reindex ea ea X))) = rb (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) := by
        change rb (Φ.toCompletelyPositiveMap (ra.symm (ra (CStarMatrix.ofMatrix X)))) = rb (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))
        rw [StarAlgEquiv.symm_apply_apply]
      rw [hl] at h; refine h.trans ?_; ext i j; simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]; apply Finset.sum_congr rfl; intro c _
      change (kf c * Matrix.reindex ea ea X * (kf c)ᴴ) i j = (kraus c * X * (kraus c)ᴴ) (eb.symm i) (eb.symm j)
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, kraus, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
      apply (Fintype.sum_equiv ea.symm _ _ ?_); intro k; simp only [Equiv.apply_symm_apply]; apply congrArg (fun t : ℂ => t * star (kf c j k))
      exact Fintype.sum_equiv ea.symm _ _ (fun _ => by simp)
    let κ := Fin (Fintype.card b) × Fin (Fintype.card a); let Ψ := fun Y : Matrix b b ℂ => ∑ c, (kraus c)ᴴ * Y * kraus c; have adjointStar (Y : Matrix b b ℂ) : Ψ Yᴴ = (Ψ Y)ᴴ := by
      simp only [Ψ, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

    have schwarzFamily
        {α : Type u} {β : Type v} {κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (kraus : κ → Matrix β α ℂ)
        (hkraus : (∑ c, (kraus c)ᴴ * kraus c) = 1) :
        let Ψ := fun Y : Matrix β β ℂ => ∑ c, (kraus c)ᴴ * Y * kraus c
        ∀ Y, (Ψ Y)ᴴ * Ψ Y ≤ Ψ (Yᴴ * Y) := by
      classical
      let Ψ := fun Y : Matrix β β ℂ => ∑ c, (kraus c)ᴴ * Y * kraus c; change ∀ Y, (Ψ Y)ᴴ * Ψ Y ≤ Ψ (Yᴴ * Y); let W : Matrix (β × κ) α ℂ := fun bc i => kraus bc.2 bc.1 i
      have hW : Wᴴ * W = 1 := by
        have heq : Wᴴ * W = ∑ c, (kraus c)ᴴ * kraus c := by
          ext i j; change (∑ bc : β × κ, star (kraus bc.2 bc.1 i) * kraus bc.2 bc.1 j) = (∑ c, (kraus c)ᴴ * kraus c) i j
          simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
          rw [Finset.sum_comm]
        rw [heq, hkraus]
      have action (Y : Matrix β β ℂ) : Wᴴ * Matrix.blockDiagonal (fun _ : κ => Y) * W = Ψ Y := by
        ext i j; dsimp only [Ψ]; rw [Matrix.sum_apply]; change (∑ bc : β × κ, (∑ bd : β × κ, star (kraus bd.2 bd.1 i) * (if bd.2 = bc.2 then Y bd.1 bc.1 else 0)) * kraus bc.2 bc.1 j) =
          ∑ c : κ, ∑ x : β, (∑ y : β, star (kraus c y i) * Y y x) * kraus c x j
        simp only [Fintype.sum_prod_type, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [Finset.sum_comm]
      have schwarz (Y : Matrix (β × κ) (β × κ) ℂ) : (Wᴴ * Y * W)ᴴ * (Wᴴ * Y * W) ≤ Wᴴ * (Yᴴ * Y) * W := by
        have hid : (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ := by
          calc
            (W * Wᴴ) * (W * Wᴴ) = W * (Wᴴ * W) * Wᴴ := by
              simp only [Matrix.mul_assoc]
            _ = W * Wᴴ := by rw [hW, Matrix.mul_one]
        have hp : (1 - W * Wᴴ)ᴴ * (1 - W * Wᴴ) = 1 - W * Wᴴ := by
          rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, hid]; abel
        have hpos : (1 - W * Wᴴ).PosSemidef := by
          rw [← hp]; exact Matrix.posSemidef_conjTranspose_mul_self _
        have hfactor := hpos.mul_mul_conjTranspose_same (Wᴴ * Yᴴ); apply Matrix.le_iff.mpr; simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc] using hfactor
      intro Y; have h := schwarz (Matrix.blockDiagonal (fun _ : κ => Y)); rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul, action, action] at h
      exact h
    have schwarzRight : ∀ Y : Matrix b b ℂ, (Ψ Y)ᴴ * Ψ Y ≤ Ψ (Yᴴ * Y) := by
        simpa only [Ψ] using schwarzFamily (α := a) (β := b) (κ := κ) kraus hkraus
    have schwarzLeft (Y : Matrix b b ℂ) : Ψ Y * (Ψ Y)ᴴ ≤ Ψ (Y * Yᴴ) := by
      simpa only [adjointStar, Matrix.conjTranspose_conjTranspose] using schwarzRight Yᴴ
    have tracePair (X : Matrix a a ℂ) (Y : Matrix b b ℂ) : Matrix.trace (X * Ψ Y) = Matrix.trace (CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) * Y) := by
      rw [haction X]; change Matrix.trace (X * (∑ c, (kraus c)ᴴ * Y * kraus c)) = _; rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_sum]; apply Finset.sum_congr rfl
      intro c _; simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (X * (kraus c)ᴴ) Y (kraus c)
    have quadratic (X : Matrix a a ℂ) (y : b → ℂ) : star y ⬝ᵥ (∑ c, kraus c * X * (kraus c)ᴴ) *ᵥ y = ∑ c, star ((kraus c)ᴴ *ᵥ y) ⬝ᵥ X *ᵥ ((kraus c)ᴴ *ᵥ y) := by
      rw [Matrix.sum_mulVec, dotProduct_sum]; apply Finset.sum_congr rfl; intro c _; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec]
      have hv : star y ᵥ* kraus c = star ((kraus c)ᴴ *ᵥ y) := by
        simpa only [Matrix.conjTranspose_conjTranspose, star_star] using Matrix.vecMul_conjTranspose ((kraus c)ᴴ) (star y)
      rw [hv]

    have kernel (X : Matrix a a ℂ) (hX : X.PosSemidef) (y : b → ℂ) : (∑ c, kraus c * X * (kraus c)ᴴ) *ᵥ y = 0 ↔ ∀ c, X *ᵥ ((kraus c)ᴴ *ᵥ y) = 0 := by
      constructor
      · intro hy
        have hsum : ∑ c, star ((kraus c)ᴴ *ᵥ y) ⬝ᵥ X *ᵥ ((kraus c)ᴴ *ᵥ y) = 0 := by
          rw [← quadratic X y, hy, dotProduct_zero]
        have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun c (_ : c ∈ (Finset.univ : Finset (Fin (Fintype.card b) × Fin (Fintype.card a)))) =>
            hX.dotProduct_mulVec_nonneg ((kraus c)ᴴ *ᵥ y))).mp hsum
        intro c; exact (hX.dotProduct_mulVec_zero_iff _).mp (hz c (Finset.mem_univ _))
      · intro hz
        rw [Matrix.sum_mulVec]; apply Finset.sum_eq_zero; intro c _; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz c, Matrix.mulVec_zero]
    have outputSupport : SupportContained (Φ.mapState ρ) (Φ.mapState σ) := by
      intro y hy; change (CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap σ.1)) *ᵥ y = 0 at hy; change (CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap ρ.1)) *ᵥ y = 0
      let R : Matrix a a ℂ := CStarMatrix.ofMatrix.symm ρ.1; let S : Matrix a a ℂ := CStarMatrix.ofMatrix.symm σ.1; have hS : S.PosSemidef :=
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.2.1).posSemidef
      have hyS : (∑ c, kraus c * S * (kraus c)ᴴ) *ᵥ y = 0 := by
        rw [← haction S]; exact hy
      have hzero := (kernel S hS y).mp hyS; have hrAction := haction R; simp only [R, Equiv.apply_symm_apply] at hrAction; rw [hrAction, Matrix.sum_mulVec]; apply Finset.sum_eq_zero
      intro c _; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; have hs : S *ᵥ ((kraus c)ᴴ *ᵥ y) = 0 := hzero c; have hr : R *ᵥ ((kraus c)ᴴ *ᵥ y) = 0 := support hs
      rw [hr, Matrix.mulVec_zero]
    rw [extendedQuantumRelativeEntropy_eq_coe_of_support outputSupport, extendedQuantumRelativeEntropy_eq_coe_of_support support]
    apply WithTop.coe_le_coe.mpr; let R : Matrix a a ℂ := CStarMatrix.ofMatrix.symm ρ.1; let S : Matrix a a ℂ := CStarMatrix.ofMatrix.symm σ.1
    let T : Matrix b b ℂ := CStarMatrix.ofMatrix.symm (Φ.mapState ρ).1; let Q : Matrix b b ℂ := CStarMatrix.ofMatrix.symm (Φ.mapState σ).1; have hR : R.PosSemidef :=
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1).posSemidef
    have hS : S.PosSemidef := (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.2.1).posSemidef
    have hT : T.PosSemidef := (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (Φ.mapState ρ).2.1).posSemidef
    have hQ : Q.PosSemidef := (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (Φ.mapState σ).2.1).posSemidef
    let I := {i : a // 0 < hR.1.eigenvalues i}; let J := {j : a // 0 < hS.1.eigenvalues j}; let K := {k : b // 0 < hT.1.eigenvalues k}; let L := {l : b // 0 < hQ.1.eigenvalues l}
    let ri : I → ℝ := fun i => hR.1.eigenvalues i.1; let sj : J → ℝ := fun j => hS.1.eigenvalues j.1; let pk : K → ℝ := fun k => hT.1.eigenvalues k.1
    let ql : L → ℝ := fun l => hQ.1.eigenvalues l.1; let u : I → a → ℂ := fun i x => hR.1.eigenvectorBasis i.1 x; let v : J → a → ℂ := fun j x => hS.1.eigenvectorBasis j.1 x
    let z : K → b → ℂ := fun k x => hT.1.eigenvectorBasis k.1 x; let w : L → b → ℂ := fun l x => hQ.1.eigenvectorBasis l.1 x; let A : Matrix (J × I) (J × I) ℂ :=
      Matrix.diagonal (fun ji => (sj ji.1 / ri ji.2 : ℝ))
    let B : Matrix (L × K) (L × K) ℂ := Matrix.diagonal (fun lk => (ql lk.1 / pk lk.2 : ℝ))
    let ξ : J × I → ℂ := fun ji => (Real.sqrt (ri ji.2) : ℂ) * (star (v ji.1) ⬝ᵥ u ji.2)
    let η : L × K → ℂ := fun lk => (Real.sqrt (pk lk.2) : ℂ) * (star (w lk.1) ⬝ᵥ z lk.2)
    let V : Matrix (J × I) (L × K) ℂ := fun ji lk =>
      (Real.sqrt (ri ji.2) / Real.sqrt (pk lk.2) : ℂ) * ∑ c, (star (v ji.1) ⬝ᵥ ((kraus c)ᴴ *ᵥ w lk.1)) * (star (z lk.2) ⬝ᵥ (kraus c *ᵥ u ji.2))
    have htrR : R.trace = 1 := ρ.2.2; have htrT : T.trace = 1 := (Φ.mapState ρ).2.2; have zeroCoordinatesR (j : a) (hj : hS.1.eigenvalues j = 0) (i : a) (hi : 0 < hR.1.eigenvalues i) :
        star (fun x => hS.1.eigenvectorBasis j x) ⬝ᵥ (fun x => hR.1.eigenvectorBasis i x) = 0 := by
      let v : a → ℂ := fun x => hS.1.eigenvectorBasis j x; let u : a → ℂ := fun x => hR.1.eigenvectorBasis i x; have hsv : S *ᵥ v = 0 := by
        simpa only [hj, zero_smul] using hS.1.mulVec_eigenvectorBasis j
      have hrv : R *ᵥ v = 0 := support hsv; have hv : star v ᵥ* R = star (R *ᵥ v) := by
        simpa only [hR.1.eq, star_star] using Matrix.vecMul_conjTranspose R (star v)
      have hz : star v ⬝ᵥ (R *ᵥ u) = 0 := by
        rw [dotProduct_mulVec, hv, hrv]; simp
      rw [hR.1.mulVec_eigenvectorBasis i, dotProduct_smul] at hz; change (hR.1.eigenvalues i : ℂ) * (star v ⬝ᵥ u) = 0 at hz; exact (mul_eq_zero.mp hz).resolve_left
        (Complex.ofReal_ne_zero.mpr (ne_of_gt hi))
    have positiveCoordinatesR : ∀ i : {i : a // 0 < hR.1.eigenvalues i}, ∑ j : {j : a // 0 < hS.1.eigenvalues j}, ‖star (fun x => hS.1.eigenvectorBasis j.1 x) ⬝ᵥ
              (fun x => hR.1.eigenvectorBasis i.1 x)‖ ^ 2 = 1 := by
      classical
      intro i; have total : (∑ j : a, ‖star (fun x => hS.1.eigenvectorBasis j x) ⬝ᵥ (fun x => hR.1.eigenvectorBasis i.1 x)‖ ^ 2) = 1 := by
        have h := hS.1.eigenvectorBasis.sum_sq_norm_inner_right (hR.1.eigenvectorBasis i.1); rw [hR.1.eigenvectorBasis.orthonormal.1 i.1, one_pow] at h; calc
          _ = ∑ j : a, ‖inner ℂ (hS.1.eigenvectorBasis j) (hR.1.eigenvectorBasis i.1)‖ ^ 2 := by
            apply Finset.sum_congr rfl; intro j _; rw [EuclideanSpace.inner_eq_star_dotProduct]; congr 2; exact dotProduct_comm _ _
          _ = 1 := h
      have complement : (∑ j : {j : a // ¬0 < hS.1.eigenvalues j}, ‖star (fun x => hS.1.eigenvectorBasis j.1 x) ⬝ᵥ (fun x => hR.1.eigenvectorBasis i.1 x)‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero; intro j _; have hj : hS.1.eigenvalues j.1 = 0 := le_antisymm (le_of_not_gt j.2) (hS.eigenvalues_nonneg j.1)
        rw [zeroCoordinatesR j.1 hj i.1 i.2, norm_zero, zero_pow (by decide)]
      have h := Fintype.sum_subtype_add_sum_subtype (fun j : a => 0 < hS.1.eigenvalues j) (fun j : a => ‖star (fun x => hS.1.eigenvectorBasis j x) ⬝ᵥ
          (fun x => hR.1.eigenvectorBasis i.1 x)‖ ^ 2)
      rw [complement, add_zero, total] at h; exact h
    have normξ : (∑ ji, ‖ξ ji‖ ^ 2) = 1 := by
      dsimp only [ξ, ri, v, u]; let I := {i : a // 0 < hR.1.eigenvalues i}; let J := {j : a // 0 < hS.1.eigenvalues j}; have all : (∑ i : a, hR.1.eigenvalues i) = 1 := by
        have h := hR.1.trace_eq_sum_eigenvalues; rw [htrR] at h; have hre := congrArg Complex.re h; simpa using hre.symm
      have complement : (∑ i : {i : a // ¬0 < hR.1.eigenvalues i}, hR.1.eigenvalues i.1) = 0 := by
        apply Finset.sum_eq_zero; intro i _; exact le_antisymm (le_of_not_gt i.2) (hR.eigenvalues_nonneg i.1)
      have mass : (∑ i : I, hR.1.eigenvalues i.1) = 1 := by
        have h := Fintype.sum_subtype_add_sum_subtype (fun i : a => 0 < hR.1.eigenvalues i) hR.1.eigenvalues
        rw [complement, add_zero, all] at h; exact h
      have overlap := positiveCoordinatesR; rw [Fintype.sum_prod_type, Finset.sum_comm]; calc
        _ = ∑ i : I, hR.1.eigenvalues i.1 * ∑ j : J, ‖star (fun x => hS.1.eigenvectorBasis j.1 x) ⬝ᵥ (fun x => hR.1.eigenvectorBasis i.1 x)‖ ^ 2 := by
          apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [norm_mul, mul_pow]; congr 1; rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt i.2)]
        _ = 1 := by
          calc
            _ = ∑ i : I, hR.1.eigenvalues i.1 := by
              apply Finset.sum_congr rfl; intro i _; simpa only [mul_one] using congrArg (fun t : ℝ => hR.1.eigenvalues i.1 * t) (overlap i)
            _ = 1 := mass
    have zeroCoordinatesT (j : b) (hj : hQ.1.eigenvalues j = 0) (i : b) (hi : 0 < hT.1.eigenvalues i) : star (fun x => hQ.1.eigenvectorBasis j x) ⬝ᵥ
          (fun x => hT.1.eigenvectorBasis i x) = 0 := by
      let v : b → ℂ := fun x => hQ.1.eigenvectorBasis j x; let u : b → ℂ := fun x => hT.1.eigenvectorBasis i x; have hsv : Q *ᵥ v = 0 := by
        simpa only [hj, zero_smul] using hQ.1.mulVec_eigenvectorBasis j
      have hrv : T *ᵥ v = 0 := outputSupport hsv; have hv : star v ᵥ* T = star (T *ᵥ v) := by
        simpa only [hT.1.eq, star_star] using Matrix.vecMul_conjTranspose T (star v)
      have hz : star v ⬝ᵥ (T *ᵥ u) = 0 := by
        rw [dotProduct_mulVec, hv, hrv]; simp
      rw [hT.1.mulVec_eigenvectorBasis i, dotProduct_smul] at hz; change (hT.1.eigenvalues i : ℂ) * (star v ⬝ᵥ u) = 0 at hz; exact (mul_eq_zero.mp hz).resolve_left
        (Complex.ofReal_ne_zero.mpr (ne_of_gt hi))
    have positiveCoordinatesT : ∀ i : {i : b // 0 < hT.1.eigenvalues i}, ∑ j : {j : b // 0 < hQ.1.eigenvalues j}, ‖star (fun x => hQ.1.eigenvectorBasis j.1 x) ⬝ᵥ
              (fun x => hT.1.eigenvectorBasis i.1 x)‖ ^ 2 = 1 := by
      classical
      intro i; have total : (∑ j : b, ‖star (fun x => hQ.1.eigenvectorBasis j x) ⬝ᵥ (fun x => hT.1.eigenvectorBasis i.1 x)‖ ^ 2) = 1 := by
        have h := hQ.1.eigenvectorBasis.sum_sq_norm_inner_right (hT.1.eigenvectorBasis i.1); rw [hT.1.eigenvectorBasis.orthonormal.1 i.1, one_pow] at h; calc
          _ = ∑ j : b, ‖inner ℂ (hQ.1.eigenvectorBasis j) (hT.1.eigenvectorBasis i.1)‖ ^ 2 := by
            apply Finset.sum_congr rfl; intro j _; rw [EuclideanSpace.inner_eq_star_dotProduct]; congr 2; exact dotProduct_comm _ _
          _ = 1 := h
      have complement : (∑ j : {j : b // ¬0 < hQ.1.eigenvalues j}, ‖star (fun x => hQ.1.eigenvectorBasis j.1 x) ⬝ᵥ (fun x => hT.1.eigenvectorBasis i.1 x)‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero; intro j _; have hj : hQ.1.eigenvalues j.1 = 0 := le_antisymm (le_of_not_gt j.2) (hQ.eigenvalues_nonneg j.1)
        rw [zeroCoordinatesT j.1 hj i.1 i.2, norm_zero, zero_pow (by decide)]
      have h := Fintype.sum_subtype_add_sum_subtype (fun j : b => 0 < hQ.1.eigenvalues j) (fun j : b => ‖star (fun x => hQ.1.eigenvectorBasis j x) ⬝ᵥ
          (fun x => hT.1.eigenvectorBasis i.1 x)‖ ^ 2)
      rw [complement, add_zero, total] at h; exact h
    have normη : (∑ ji, ‖η ji‖ ^ 2) = 1 := by
      dsimp only [η, pk, w, z]; let I := {i : b // 0 < hT.1.eigenvalues i}; let J := {j : b // 0 < hQ.1.eigenvalues j}; have all : (∑ i : b, hT.1.eigenvalues i) = 1 := by
        have h := hT.1.trace_eq_sum_eigenvalues; rw [htrT] at h; have hre := congrArg Complex.re h; simpa using hre.symm
      have complement : (∑ i : {i : b // ¬0 < hT.1.eigenvalues i}, hT.1.eigenvalues i.1) = 0 := by
        apply Finset.sum_eq_zero; intro i _; exact le_antisymm (le_of_not_gt i.2) (hT.eigenvalues_nonneg i.1)
      have mass : (∑ i : I, hT.1.eigenvalues i.1) = 1 := by
        have h := Fintype.sum_subtype_add_sum_subtype (fun i : b => 0 < hT.1.eigenvalues i) hT.1.eigenvalues
        rw [complement, add_zero, all] at h; exact h
      have overlap := positiveCoordinatesT; rw [Fintype.sum_prod_type, Finset.sum_comm]; calc
        _ = ∑ i : I, hT.1.eigenvalues i.1 * ∑ j : J, ‖star (fun x => hQ.1.eigenvectorBasis j.1 x) ⬝ᵥ (fun x => hT.1.eigenvectorBasis i.1 x)‖ ^ 2 := by
          apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [norm_mul, mul_pow]; congr 1; rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt i.2)]
        _ = 1 := by
          calc
            _ = ∑ i : I, hT.1.eigenvalues i.1 := by
              apply Finset.sum_congr rfl; intro i _; simpa only [mul_one] using congrArg (fun t : ℝ => hT.1.eigenvalues i.1 * t) (overlap i)
            _ = 1 := mass

    have supportedParseval (H : Matrix b b ℂ) (hH : H.IsHermitian) (nonnegH : ∀ j, 0 ≤ hH.eigenvalues j) (x y : b → ℂ) (hy : ∀ j, hH.eigenvalues j = 0 →
          star (fun t => hH.eigenvectorBasis j t) ⬝ᵥ y = 0) : (∑ j : {j : b // 0 < hH.eigenvalues j}, (star x ⬝ᵥ (fun t => hH.eigenvectorBasis j.1 t)) *
            (star (fun t => hH.eigenvectorBasis j.1 t) ⬝ᵥ y)) = star x ⬝ᵥ y := by
      classical
      have innerEq (p q : EuclideanSpace ℂ b) : inner ℂ p q = star (fun t => p t) ⬝ᵥ (fun t => q t) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      have full : (∑ j : b, (star x ⬝ᵥ (fun t => hH.eigenvectorBasis j t)) * (star (fun t => hH.eigenvectorBasis j t) ⬝ᵥ y)) = star x ⬝ᵥ y := by
        simpa only [innerEq, WithLp.ofLp_toLp] using hH.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 x) (WithLp.toLp 2 y)
      have complement : (∑ j : {j : b // ¬ 0 < hH.eigenvalues j}, (star x ⬝ᵥ (fun t => hH.eigenvectorBasis j.1 t)) * (star (fun t => hH.eigenvectorBasis j.1 t) ⬝ᵥ y)) = 0 := by
        apply Finset.sum_eq_zero; intro j _; rw [hy j.1 (le_antisymm (le_of_not_gt j.2) (nonnegH j.1)), mul_zero]
      have split := Fintype.sum_subtype_add_sum_subtype (fun j => 0 < hH.eigenvalues j) (fun j => (star x ⬝ᵥ (fun t => hH.eigenvectorBasis j t)) *
          (star (fun t => hH.eigenvectorBasis j t) ⬝ᵥ y))
      rw [complement, add_zero, full] at split; exact split
    have hTAction : T = ∑ c, kraus c * R * (kraus c)ᴴ := haction R; have zeroKrausCoordinate (c : κ) (i : I) (k : b) (hk : hT.1.eigenvalues k = 0) :
        star (fun x => hT.1.eigenvectorBasis k x) ⬝ᵥ (kraus c *ᵥ u i) = 0 := by
      let y : b → ℂ := fun x => hT.1.eigenvectorBasis k x; let t : a → ℂ := (kraus c)ᴴ *ᵥ y; have hy : T *ᵥ y = 0 := by
        simpa only [hk, zero_smul] using hT.1.mulVec_eigenvectorBasis k
      have ht : R *ᵥ t = 0 := by
        apply (kernel R hR y).mp _ c; rw [← hTAction]; exact hy
      have hv : star t ᵥ* R = star (R *ᵥ t) := by
        simpa only [hR.1.eq, star_star] using Matrix.vecMul_conjTranspose R (star t)
      have hz : star t ⬝ᵥ (R *ᵥ u i) = 0 := by
        rw [dotProduct_mulVec, hv, ht]; simp
      rw [hR.1.mulVec_eigenvectorBasis i.1, dotProduct_smul] at hz; change (ri i : ℂ) * (star t ⬝ᵥ u i) = 0 at hz; have hzero : star t ⬝ᵥ u i = 0 :=
        (mul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr (ne_of_gt i.2))
      have adjoint : star y ᵥ* kraus c = star t := by
        simpa only [t, Matrix.conjTranspose_conjTranspose, star_star] using Matrix.vecMul_conjTranspose ((kraus c)ᴴ) (star y)
      change star y ⬝ᵥ (kraus c *ᵥ u i) = 0; rw [dotProduct_mulVec, adjoint]; exact hzero
    have adjointPair (c : κ) (x : a → ℂ) (y : b → ℂ) : star x ⬝ᵥ ((kraus c)ᴴ *ᵥ y) = star (kraus c *ᵥ x) ⬝ᵥ y := by
      rw [dotProduct_mulVec]; have adjoint : star x ᵥ* (kraus c)ᴴ = star (kraus c *ᵥ x) := by
        simpa only [star_star] using Matrix.vecMul_conjTranspose (kraus c) (star x)
      rw [adjoint]
    have sumQ (c : κ) (j : J) (k : K) : (∑ l : L, (star (v j) ⬝ᵥ ((kraus c)ᴴ *ᵥ w l)) * (star (w l) ⬝ᵥ z k)) = star (v j) ⬝ᵥ ((kraus c)ᴴ *ᵥ z k) := by
      simp only [adjointPair]; exact supportedParseval Q hQ.1 hQ.eigenvalues_nonneg (kraus c *ᵥ v j) (z k) (fun l hl => zeroCoordinatesT l hl k.1 k.2)
    have sumT (c : κ) (j : J) (i : I) : (∑ k : K, (star (v j) ⬝ᵥ ((kraus c)ᴴ *ᵥ z k)) * (star (z k) ⬝ᵥ (kraus c *ᵥ u i))) = star (v j) ⬝ᵥ ((kraus c)ᴴ *ᵥ (kraus c *ᵥ u i)) := by
      simp only [adjointPair]; exact supportedParseval T hT.1 hT.eigenvalues_nonneg (kraus c *ᵥ v j) (kraus c *ᵥ u i) (fun k hk => zeroKrausCoordinate c i k hk)
    have krausPair (j : J) (i : I) : (∑ c : κ, star (v j) ⬝ᵥ ((kraus c)ᴴ *ᵥ (kraus c *ᵥ u i))) = star (v j) ⬝ᵥ u i := by
      simp only [Matrix.mulVec_mulVec]; rw [← dotProduct_sum, ← Matrix.sum_mulVec, hkraus, Matrix.one_mulVec]
    have mapsη : V *ᵥ η = ξ := by
      ext ji; have scalar (l : L) (k : K) (c : κ) : (Real.sqrt (ri ji.2) / Real.sqrt (pk k) : ℂ) * ((star (v ji.1) ⬝ᵥ ((kraus c)ᴴ *ᵥ w l)) * (star (z k) ⬝ᵥ (kraus c *ᵥ u ji.2))) *
              ((Real.sqrt (pk k) : ℂ) * (star (w l) ⬝ᵥ z k)) = (Real.sqrt (ri ji.2) : ℂ) * (((star (v ji.1) ⬝ᵥ ((kraus c)ᴴ *ᵥ w l)) * (star (w l) ⬝ᵥ z k)) *
                (star (z k) ⬝ᵥ (kraus c *ᵥ u ji.2))) := by
        have hpk : (Real.sqrt (pk k) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr k.2))
        field_simp [hpk]
      calc
        (V *ᵥ η) ji = ∑ l : L, ∑ k : K, ∑ c : κ, (Real.sqrt (ri ji.2) : ℂ) * (((star (v ji.1) ⬝ᵥ ((kraus c)ᴴ *ᵥ w l)) * (star (w l) ⬝ᵥ z k)) * (star (z k) ⬝ᵥ (kraus c *ᵥ u ji.2))) := by
          change (∑ lk : L × K, (Real.sqrt (ri ji.2) / Real.sqrt (pk lk.2) : ℂ) * (∑ c : κ, (star (v ji.1) ⬝ᵥ ((kraus c)ᴴ *ᵥ w lk.1)) * (star (z lk.2) ⬝ᵥ (kraus c *ᵥ u ji.2))) *
              ((Real.sqrt (pk lk.2) : ℂ) * (star (w lk.1) ⬝ᵥ z lk.2))) = _
          rw [Fintype.sum_prod_type]; simp only [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl
          intro c _; exact scalar l k c
        _ = (Real.sqrt (ri ji.2) : ℂ) * ∑ c : κ, ∑ k : K, ∑ l : L, ((star (v ji.1) ⬝ᵥ ((kraus c)ᴴ *ᵥ w l)) * (star (w l) ⬝ᵥ z k)) * (star (z k) ⬝ᵥ (kraus c *ᵥ u ji.2)) := by
          let f (l : L) (k : K) (c : κ) : ℂ := (Real.sqrt (ri ji.2) : ℂ) * (((star (v ji.1) ⬝ᵥ ((kraus c)ᴴ *ᵥ w l)) * (star (w l) ⬝ᵥ z k)) * (star (z k) ⬝ᵥ (kraus c *ᵥ u ji.2)))
          simp only [Finset.mul_sum]; change (∑ l : L, ∑ k : K, ∑ c : κ, f l k c) = ∑ c : κ, ∑ k : K, ∑ l : L, f l k c
          calc
            _ = ∑ l : L, ∑ c : κ, ∑ k : K, f l k c := by
              apply Finset.sum_congr rfl; intro l _; rw [Finset.sum_comm]
            _ = ∑ c : κ, ∑ l : L, ∑ k : K, f l k c := by rw [Finset.sum_comm]
            _ = _ := by
              apply Finset.sum_congr rfl; intro c _; rw [Finset.sum_comm]
        _ = (Real.sqrt (ri ji.2) : ℂ) * ∑ c : κ, ∑ k : K, (star (v ji.1) ⬝ᵥ ((kraus c)ᴴ *ᵥ z k)) * (star (z k) ⬝ᵥ (kraus c *ᵥ u ji.2)) := by
          congr 1; apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl; intro k _; rw [← Finset.sum_mul, sumQ c ji.1 k]
        _ = (Real.sqrt (ri ji.2) : ℂ) * ∑ c : κ, star (v ji.1) ⬝ᵥ ((kraus c)ᴴ *ᵥ (kraus c *ᵥ u ji.2)) := by
          congr 1; apply Finset.sum_congr rfl; intro c _; exact sumT c ji.1 ji.2
        _ = (Real.sqrt (ri ji.2) : ℂ) * (star (v ji.1) ⬝ᵥ u ji.2) := by
          rw [krausPair]
        _ = ξ ji := rfl
    let spectralX (x : L × K → ℂ) : Matrix b b ℂ := ∑ lk : L × K, (x lk / (Real.sqrt (pk lk.2) : ℂ)) • Matrix.vecMulVec (w lk.1) (star (z lk.2))
    have outerAction (l : L) (k : K) (y : b → ℂ) : Matrix.vecMulVec (w l) (star (z k)) *ᵥ y = (star (z k) ⬝ᵥ y) • w l := by
      ext t; change (∑ s : b, w l t * star (z k s) * y s) = (∑ s : b, star (z k s) * y s) * w l t
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro s _; ring

    have spectralAction (x : L × K → ℂ) (y : b → ℂ) : spectralX x *ᵥ y = ∑ lk : L × K, (x lk / (Real.sqrt (pk lk.2) : ℂ) * (star (z lk.2) ⬝ᵥ y)) • w lk.1 := by
      dsimp only [spectralX]; rw [Matrix.sum_mulVec]; apply Finset.sum_congr rfl; intro lk _; rw [Matrix.smul_mulVec, outerAction, smul_smul]
    have adjointSpectralAction (x : L × K → ℂ) (i : I) : Ψ (spectralX x) *ᵥ u i = ∑ c : κ, ∑ lk : L × K, (x lk / (Real.sqrt (pk lk.2) : ℂ) * (star (z lk.2) ⬝ᵥ (kraus c *ᵥ u i))) •
                ((kraus c)ᴴ *ᵥ w lk.1) := by
      dsimp only [Ψ]; rw [Matrix.sum_mulVec]; apply Finset.sum_congr rfl; intro c _; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, spectralAction, Matrix.mulVec_sum]
      apply Finset.sum_congr rfl; intro lk _; rw [Matrix.mulVec_smul]
    have coordinateAction (x : L × K → ℂ) (ji : J × I) : (V *ᵥ x) ji = (Real.sqrt (ri ji.2) : ℂ) * (star (v ji.1) ⬝ᵥ (Ψ (spectralX x) *ᵥ u ji.2)) := by
      rw [adjointSpectralAction, dotProduct_sum]; simp only [dotProduct_sum, dotProduct_smul, Finset.mul_sum]; change (∑ lk : L × K, ((Real.sqrt (ri ji.2) / Real.sqrt (pk lk.2) : ℂ) *
          ∑ c : κ, (star (v ji.1) ⬝ᵥ ((kraus c)ᴴ *ᵥ w lk.1)) * (star (z lk.2) ⬝ᵥ (kraus c *ᵥ u ji.2))) * x lk) = _
      simp only [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl; intro lk _; simp only [div_eq_mul_inv]; ring
    have traceSchwarzR (Y : Matrix b b ℂ) : (R * ((Ψ Y)ᴴ * Ψ Y)).trace.re ≤ (T * (Yᴴ * Y)).trace.re := by
      have hD := Matrix.le_iff.mp (schwarzRight Y); have h := RHLinalg.trace_mul_nonneg_of_posSemidef hR hD; have hPair : (R * Ψ (Yᴴ * Y)).trace = (T * (Yᴴ * Y)).trace :=
        tracePair R (Yᴴ * Y)
      rw [Matrix.mul_sub, Matrix.trace_sub, map_sub, RCLike.re_to_complex, RCLike.re_to_complex, hPair] at h
      exact sub_nonneg.mp h
    have traceSchwarzS (Y : Matrix b b ℂ) : (S * (Ψ Y * (Ψ Y)ᴴ)).trace.re ≤ (Q * (Y * Yᴴ)).trace.re := by
      have hD := Matrix.le_iff.mp (schwarzLeft Y); have h := RHLinalg.trace_mul_nonneg_of_posSemidef hS hD; have hPair : (S * Ψ (Y * Yᴴ)).trace = (Q * (Y * Yᴴ)).trace := tracePair S (Y * Yᴴ)
      rw [Matrix.mul_sub, Matrix.trace_sub, map_sub, RCLike.re_to_complex, RCLike.re_to_complex, hPair] at h
      exact sub_nonneg.mp h
    have weightedTraceInput {n : Type u} [Fintype n] [DecidableEq n] (R : Matrix n n ℂ) (hR : R.PosSemidef) (F : Matrix n n ℂ) : (R * F).trace.re = ∑ i : {i : n // 0 < hR.1.eigenvalues i},
            hR.1.eigenvalues i.1 * (star (fun x => hR.1.eigenvectorBasis i.1 x) ⬝ᵥ (F *ᵥ (fun x => hR.1.eigenvectorBasis i.1 x))).re := by
      classical
      let U : Matrix n n ℂ := hR.1.eigenvectorUnitary; have tr : (R * F).trace = (Uᴴ * F * U * diagonal (fun i => (hR.1.eigenvalues i : ℂ))).trace := by
        conv_lhs => rw [hR.1.spectral_theorem, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
        rfl
      have diag (i : n) : (Uᴴ * F * U) i i = star (fun x => hR.1.eigenvectorBasis i x) ⬝ᵥ (F *ᵥ (fun x => hR.1.eigenvectorBasis i x)) := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, U, Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.mulVec, dotProduct, Pi.star_apply]
        simp only [Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; ring
      have ambient : (R * F).trace.re = ∑ i : n, hR.1.eigenvalues i * (star (fun x => hR.1.eigenvectorBasis i x) ⬝ᵥ (F *ᵥ (fun x => hR.1.eigenvectorBasis i x))).re := by
        rw [tr]; change (RCLike.re : ℂ →+ ℝ) _ = _; simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, map_sum,
          RCLike.mul_re, RCLike.re_to_complex, RCLike.im_to_complex, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        apply Finset.sum_congr rfl; intro i _; rw [diag]; ring
      have complement : (∑ i : {i : n // ¬ 0 < hR.1.eigenvalues i}, hR.1.eigenvalues i.1 * (star (fun x => hR.1.eigenvectorBasis i.1 x) ⬝ᵥ
              (F *ᵥ (fun x => hR.1.eigenvectorBasis i.1 x))).re) = 0 := by
        apply Finset.sum_eq_zero; intro i _; have hi : hR.1.eigenvalues i.1 = 0 := le_antisymm (le_of_not_gt i.2) (hR.eigenvalues_nonneg i.1)
        rw [hi, zero_mul]
      have split := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < hR.1.eigenvalues i) (fun i => hR.1.eigenvalues i * (star (fun x => hR.1.eigenvectorBasis i x) ⬝ᵥ
            (F *ᵥ (fun x => hR.1.eigenvectorBasis i x))).re)
      rw [complement, add_zero, ← ambient] at split; exact split.symm
    have supportedBessel {n : Type u} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (y : n → ℂ) : (∑ j : {j : n // 0 < hH.eigenvalues j},
          ‖star (fun t => hH.eigenvectorBasis j.1 t) ⬝ᵥ y‖ ^ 2) ≤ (star y ⬝ᵥ y).re := by
      have hv := hH.eigenvectorBasis.orthonormal.comp (fun j : {j : n // 0 < hH.eigenvalues j} => j.1) Subtype.val_injective
      have h := hv.sum_inner_products_le (WithLp.toLp 2 y) (s := Finset.univ); rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ (EuclideanSpace ℂ n)] at h
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, dotProduct_comm, RCLike.re_to_complex, Function.comp_apply] using h
    have coordinateBound {n : Type u} [Fintype n] [DecidableEq n] (R S : Matrix n n ℂ) (hR : R.PosSemidef) (hS : S.PosSemidef) (M : Matrix n n ℂ) :
        (∑ ji : {j : n // 0 < hS.1.eigenvalues j} × {i : n // 0 < hR.1.eigenvalues i}, ‖(Real.sqrt (hR.1.eigenvalues ji.2.1) : ℂ) * (star (fun t => hS.1.eigenvectorBasis ji.1.1 t) ⬝ᵥ
              (M *ᵥ fun t => hR.1.eigenvectorBasis ji.2.1 t))‖ ^ 2) ≤ (R * (Mᴴ * M)).trace.re := by
      classical
      rw [weightedTraceInput R hR (Mᴴ * M), Fintype.sum_prod_type, Finset.sum_comm]; apply Finset.sum_le_sum; intro i _; have gram (y : n → ℂ) :
          star y ⬝ᵥ ((Mᴴ * M) *ᵥ y) = star (M *ᵥ y) ⬝ᵥ (M *ᵥ y) := by
        rw [← Matrix.mulVec_mulVec, dotProduct_mulVec]; rw [Matrix.vecMul_conjTranspose, star_star]
      rw [gram]; have hb := supportedBessel S hS.1 (M *ᵥ fun t => hR.1.eigenvectorBasis i.1 t); calc
        _ = hR.1.eigenvalues i.1 * ∑ j : {j : n // 0 < hS.1.eigenvalues j}, ‖star (fun t => hS.1.eigenvectorBasis j.1 t) ⬝ᵥ (M *ᵥ fun t => hR.1.eigenvectorBasis i.1 t)‖ ^ 2 := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt i.2)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hb (le_of_lt i.2)
    have adjointNorm {n : Type u} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (x y : n → ℂ) : ‖star x ⬝ᵥ (M *ᵥ y)‖ = ‖star y ⬝ᵥ (Mᴴ *ᵥ x)‖ := by
      have eq : star (star x ⬝ᵥ (M *ᵥ y)) = star y ⬝ᵥ (Mᴴ *ᵥ x) := by
        rw [star_dotProduct, Matrix.star_mulVec, dotProduct_comm, dotProduct_mulVec]; simp only [star_star, dotProduct_comm]
      rw [← eq, norm_star]
    have diagonalQuadratic {n : Type u} [Fintype n] [DecidableEq n] (d : n → ℝ) (y : n → ℂ) : (star y ⬝ᵥ (diagonal (fun i => (d i : ℂ)) *ᵥ y)).re = ∑ i, d i * ‖y i‖ ^ 2 := by
      change (RCLike.re : ℂ →+ ℝ) _ = _; simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, map_sum]; apply Finset.sum_congr rfl; intro i _
      have term : star (y i) * ((d i : ℂ) * y i) = (d i : ℂ) * (star (y i) * y i) := by ring
      have eqnorm : star (y i) * y i = ((‖y i‖ ^ 2 : ℝ) : ℂ) := by
        simpa only [RCLike.star_def, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using RCLike.conj_mul (y i)
      rw [term, eqnorm, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
    have diagonalQuadraticOutput {n : Type v} [Fintype n] [DecidableEq n] (d : n → ℝ) (y : n → ℂ) : (star y ⬝ᵥ (diagonal (fun i => (d i : ℂ)) *ᵥ y)).re = ∑ i, d i * ‖y i‖ ^ 2 := by
      change (RCLike.re : ℂ →+ ℝ) _ = _; simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, map_sum]; apply Finset.sum_congr rfl; intro i _
      have term : star (y i) * ((d i : ℂ) * y i) = (d i : ℂ) * (star (y i) * y i) := by ring
      have eqnorm : star (y i) * y i = ((‖y i‖ ^ 2 : ℝ) : ℂ) := by
        simpa only [RCLike.star_def, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using RCLike.conj_mul (y i)
      rw [term, eqnorm, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
    have coordinateWeighted {n : Type u} [Fintype n] [DecidableEq n] (R S : Matrix n n ℂ) (hR : R.PosSemidef) (hS : S.PosSemidef) (M : Matrix n n ℂ) :
        let I := {i : n // 0 < hR.1.eigenvalues i}
        let J := {j : n // 0 < hS.1.eigenvalues j}
        let g : J × I → ℂ := fun ji => (Real.sqrt (hR.1.eigenvalues ji.2.1) : ℂ) * (star (fun t => hS.1.eigenvectorBasis ji.1.1 t) ⬝ᵥ (M *ᵥ fun t => hR.1.eigenvectorBasis ji.2.1 t))
        (star g ⬝ᵥ (diagonal (fun ji =>
          (hS.1.eigenvalues ji.1.1 / hR.1.eigenvalues ji.2.1 : ℝ)) *ᵥ g)).re ≤ (S * (M * Mᴴ)).trace.re := by
      classical
      dsimp only; rw [diagonalQuadratic, weightedTraceInput S hS (M * Mᴴ), Fintype.sum_prod_type]; apply Finset.sum_le_sum; intro j _; have gram (y : n → ℂ) :
          star y ⬝ᵥ ((M * Mᴴ) *ᵥ y) = star (Mᴴ *ᵥ y) ⬝ᵥ (Mᴴ *ᵥ y) := by
        rw [← Matrix.mulVec_mulVec, dotProduct_mulVec]; rw [← Matrix.conjTranspose_conjTranspose M, Matrix.vecMul_conjTranspose, star_star, Matrix.conjTranspose_conjTranspose]
      rw [gram]; have hb := supportedBessel R hR.1 (Mᴴ *ᵥ fun t => hS.1.eigenvectorBasis j.1 t); calc
        _ = hS.1.eigenvalues j.1 * ∑ i : {i : n // 0 < hR.1.eigenvalues i}, ‖star (fun t => hR.1.eigenvectorBasis i.1 t) ⬝ᵥ (Mᴴ *ᵥ fun t => hS.1.eigenvectorBasis j.1 t)‖ ^ 2 := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt i.2), adjointNorm]
          field_simp [ne_of_gt i.2]
        _ ≤ _ := mul_le_mul_of_nonneg_left hb (le_of_lt j.2)
    have orthonormalForm {n : Type v} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (d : {j : n // 0 < hH.eigenvalues j} → ℂ) :
        (star (∑ j : {j : n // 0 < hH.eigenvalues j}, d j • (fun t => hH.eigenvectorBasis j.1 t)) ⬝ᵥ (∑ j : {j : n // 0 < hH.eigenvalues j}, d j • (fun t => hH.eigenvectorBasis j.1 t))).re =
          ∑ j, ‖d j‖ ^ 2 := by
      classical
      have hv := hH.eigenvectorBasis.orthonormal.comp (fun j : {j : n // 0 < hH.eigenvalues j} => j.1) Subtype.val_injective
      have h := hv.inner_sum d d Finset.univ; have re := congrArg Complex.re h; change (star (∑ j, d j • (hH.eigenvectorBasis j.1).ofLp) ⬝ᵥ
        (∑ j, d j • (hH.eigenvectorBasis j.1).ofLp)).re = ∑ j, ‖d j‖ ^ 2
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, Function.comp_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, dotProduct_comm, map_sum,
        RCLike.conj_mul, RCLike.ofReal_eq_complex_ofReal, pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.re_sum] using re
    have eigenInner {n : Type v} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (j k : {j : n // 0 < hH.eigenvalues j}) : star (fun t => hH.eigenvectorBasis j.1 t) ⬝ᵥ
          (fun t => hH.eigenvectorBasis k.1 t) = if j = k then 1 else 0 := by
      have h := hH.eigenvectorBasis.inner_eq_ite j.1 k.1; simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, Subtype.val_inj] using h
    have weightedTraceOutput {n : Type v} [Fintype n] [DecidableEq n] (R : Matrix n n ℂ) (hR : R.PosSemidef) (F : Matrix n n ℂ) : (R * F).trace.re = ∑ i : {i : n // 0 < hR.1.eigenvalues i},
            hR.1.eigenvalues i.1 * (star (fun x => hR.1.eigenvectorBasis i.1 x) ⬝ᵥ (F *ᵥ (fun x => hR.1.eigenvectorBasis i.1 x))).re := by
      classical
      let U : Matrix n n ℂ := hR.1.eigenvectorUnitary; have tr : (R * F).trace = (Uᴴ * F * U * diagonal (fun i => (hR.1.eigenvalues i : ℂ))).trace := by
        conv_lhs => rw [hR.1.spectral_theorem, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
        rfl
      have diag (i : n) : (Uᴴ * F * U) i i = star (fun x => hR.1.eigenvectorBasis i x) ⬝ᵥ (F *ᵥ (fun x => hR.1.eigenvectorBasis i x)) := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, U, Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.mulVec, dotProduct, Pi.star_apply]
        simp only [Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; ring
      have ambient : (R * F).trace.re = ∑ i : n, hR.1.eigenvalues i * (star (fun x => hR.1.eigenvectorBasis i x) ⬝ᵥ (F *ᵥ (fun x => hR.1.eigenvectorBasis i x))).re := by
        rw [tr]; change (RCLike.re : ℂ →+ ℝ) _ = _; simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, map_sum,
          RCLike.mul_re, RCLike.re_to_complex, RCLike.im_to_complex, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        apply Finset.sum_congr rfl; intro i _; rw [diag]; ring
      have complement : (∑ i : {i : n // ¬ 0 < hR.1.eigenvalues i}, hR.1.eigenvalues i.1 * (star (fun x => hR.1.eigenvectorBasis i.1 x) ⬝ᵥ
              (F *ᵥ (fun x => hR.1.eigenvectorBasis i.1 x))).re) = 0 := by
        apply Finset.sum_eq_zero; intro i _; have hi : hR.1.eigenvalues i.1 = 0 := le_antisymm (le_of_not_gt i.2) (hR.eigenvalues_nonneg i.1)
        rw [hi, zero_mul]
      have split := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < hR.1.eigenvalues i) (fun i => hR.1.eigenvalues i * (star (fun x => hR.1.eigenvectorBasis i x) ⬝ᵥ
            (F *ᵥ (fun x => hR.1.eigenvectorBasis i x))).re)
      rw [complement, add_zero, ← ambient] at split; exact split.symm
    have spectralNormR {n : Type v} [Fintype n] [DecidableEq n] (T Q : Matrix n n ℂ) (hT : T.PosSemidef) (hQ : Q.PosSemidef)
        (x : {l : n // 0 < hQ.1.eigenvalues l} × {k : n // 0 < hT.1.eigenvalues k} → ℂ) :
        let K := {k : n // 0 < hT.1.eigenvalues k}
        let L := {l : n // 0 < hQ.1.eigenvalues l}
        let z : K → n → ℂ := fun k t => hT.1.eigenvectorBasis k.1 t
        let w : L → n → ℂ := fun l t => hQ.1.eigenvectorBasis l.1 t
        let X : Matrix n n ℂ := ∑ lk : L × K, (x lk / (Real.sqrt (hT.1.eigenvalues lk.2.1) : ℂ)) • Matrix.vecMulVec (w lk.1) (star (z lk.2))
        (T * (Xᴴ * X)).trace.re = ∑ lk, ‖x lk‖ ^ 2 := by
      classical
      dsimp only; let K := {k : n // 0 < hT.1.eigenvalues k}; let L := {l : n // 0 < hQ.1.eigenvalues l}; let z : K → n → ℂ := fun k t => hT.1.eigenvectorBasis k.1 t
      let w : L → n → ℂ := fun l t => hQ.1.eigenvectorBasis l.1 t; let X : Matrix n n ℂ := ∑ lk : L × K, (x lk / (Real.sqrt (hT.1.eigenvalues lk.2.1) : ℂ)) •
            Matrix.vecMulVec (w lk.1) (star (z lk.2))
      change (T * (Xᴴ * X)).trace.re = _; have outerAction (l : L) (k : K) (y : n → ℂ) : Matrix.vecMulVec (w l) (star (z k)) *ᵥ y = (star (z k) ⬝ᵥ y) • w l := by
        ext t; change (∑ s : n, w l t * star (z k s) * y s) = (∑ s : n, star (z k s) * y s) * w l t
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro s _; ring
      have innerZ (k k' : K) : star (z k) ⬝ᵥ z k' = if k = k' then 1 else 0 := eigenInner T hT.1 k k'
      have action (k : K) : X *ᵥ z k = ∑ l : L, (x (l,k) / (Real.sqrt (hT.1.eigenvalues k.1) : ℂ)) • w l := by
        dsimp only [X]; rw [Matrix.sum_mulVec]; simp only [Matrix.smul_mulVec, outerAction, smul_smul, innerZ, Fintype.sum_prod_type]
        simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ext t; simp only [Finset.sum_apply, ite_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]; apply Finset.sum_congr rfl; intro l _; exact Fintype.sum_ite_eq' k (fun k' : K =>
          x (l,k') / (Real.sqrt (hT.1.eigenvalues k'.1) : ℂ) * w l t)
      have gram (y : n → ℂ) : star y ⬝ᵥ ((Xᴴ * X) *ᵥ y) = star (X *ᵥ y) ⬝ᵥ (X *ᵥ y) := by
        rw [← Matrix.mulVec_mulVec, dotProduct_mulVec]; rw [Matrix.vecMul_conjTranspose, star_star]
      rw [weightedTraceOutput T hT (Xᴴ * X), Fintype.sum_prod_type, Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _; rw [gram]
      change hT.1.eigenvalues k.1 * (star (X *ᵥ z k) ⬝ᵥ (X *ᵥ z k)).re = _; rw [action, orthonormalForm Q hQ.1, Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _
      rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt k.2)]
      field_simp [ne_of_gt k.2]
    have spectralNormS {n : Type v} [Fintype n] [DecidableEq n] (T Q : Matrix n n ℂ) (hT : T.PosSemidef) (hQ : Q.PosSemidef)
        (x : {l : n // 0 < hQ.1.eigenvalues l} × {k : n // 0 < hT.1.eigenvalues k} → ℂ) :
        let K := {k : n // 0 < hT.1.eigenvalues k}
        let L := {l : n // 0 < hQ.1.eigenvalues l}
        let z : K → n → ℂ := fun k t => hT.1.eigenvectorBasis k.1 t
        let w : L → n → ℂ := fun l t => hQ.1.eigenvectorBasis l.1 t
        let X : Matrix n n ℂ := ∑ lk : L × K, (x lk / (Real.sqrt (hT.1.eigenvalues lk.2.1) : ℂ)) • Matrix.vecMulVec (w lk.1) (star (z lk.2))
        (Q * (X * Xᴴ)).trace.re = ∑ lk, hQ.1.eigenvalues lk.1.1 / hT.1.eigenvalues lk.2.1 * ‖x lk‖ ^ 2 := by
      classical
      dsimp only; let K := {k : n // 0 < hT.1.eigenvalues k}; let L := {l : n // 0 < hQ.1.eigenvalues l}; let z : K → n → ℂ := fun k t => hT.1.eigenvectorBasis k.1 t
      let w : L → n → ℂ := fun l t => hQ.1.eigenvectorBasis l.1 t; let X : Matrix n n ℂ := ∑ lk : L × K, (x lk / (Real.sqrt (hT.1.eigenvalues lk.2.1) : ℂ)) •
            Matrix.vecMulVec (w lk.1) (star (z lk.2))
      change (Q * (X * Xᴴ)).trace.re = _; have outerAdj (l : L) (k : K) : (Matrix.vecMulVec (w l) (star (z k)))ᴴ = Matrix.vecMulVec (z k) (star (w l)) := by
        ext i j; change star (w l j * star (z k i)) = z k i * star (w l j); rw [star_mul, star_star]
      have outerAction (k : K) (l : L) (y : n → ℂ) : Matrix.vecMulVec (z k) (star (w l)) *ᵥ y = (star (w l) ⬝ᵥ y) • z k := by
        ext t; change (∑ s : n, z k t * star (w l s) * y s) = (∑ s : n, star (w l s) * y s) * z k t
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro s _; ring
      have innerW (l l' : L) : star (w l) ⬝ᵥ w l' = if l = l' then 1 else 0 := eigenInner Q hQ.1 l l'
      have action (l : L) : Xᴴ *ᵥ w l = ∑ k : K, star (x (l,k) / (Real.sqrt (hT.1.eigenvalues k.1) : ℂ)) • z k := by
        dsimp only [X]; rw [Matrix.conjTranspose_sum, Matrix.sum_mulVec]; simp only [Matrix.conjTranspose_smul, outerAdj, Matrix.smul_mulVec,
          outerAction, smul_smul, innerW, Fintype.sum_prod_type]
        rw [Finset.sum_comm]; simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ext t; simp only [Finset.sum_apply, ite_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]; apply Finset.sum_congr rfl; intro k _; exact Fintype.sum_ite_eq' l (fun l' : L =>
          star (x (l',k) / (Real.sqrt (hT.1.eigenvalues k.1) : ℂ)) * z k t)
      have gram (y : n → ℂ) : star y ⬝ᵥ ((X * Xᴴ) *ᵥ y) = star (Xᴴ *ᵥ y) ⬝ᵥ (Xᴴ *ᵥ y) := by
        rw [← Matrix.mulVec_mulVec, dotProduct_mulVec]; rw [← Matrix.conjTranspose_conjTranspose X, Matrix.vecMul_conjTranspose, star_star, Matrix.conjTranspose_conjTranspose]
      rw [weightedTraceOutput Q hQ (X * Xᴴ), Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro l _; rw [gram]; change hQ.1.eigenvalues l.1 * (star (Xᴴ *ᵥ w l) ⬝ᵥ (Xᴴ *ᵥ w l)).re = _
      rw [action, orthonormalForm T hT.1, Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; rw [norm_star, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt k.2)]
      ring
    have realFormPSD {n : Type v} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (hM : M.IsHermitian) (h : ∀ x : n → ℂ, 0 ≤ (star x ⬝ᵥ (M *ᵥ x)).re) : M.PosSemidef := by
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM; intro x; have hs : IsSelfAdjoint (star x ⬝ᵥ (M *ᵥ x)) := by
        change star (star x ⬝ᵥ (M *ᵥ x)) = star x ⬝ᵥ (M *ᵥ x); calc
          _ = star (M *ᵥ x) ⬝ᵥ x := by
            rw [star_dotProduct, star_star, dotProduct_comm]
          _ = star x ⬝ᵥ (Mᴴ *ᵥ x) := by
            rw [dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
          _ = _ := by rw [hM.eq]
      exact (Complex.re_nonneg_iff_nonneg hs).mp (h x)
    have hA : A.PosDef := by
      apply Matrix.PosDef.diagonal; intro ji; exact_mod_cast div_pos ji.1.2 ji.2.2
    have hB : B.PosDef := by
      apply Matrix.PosDef.diagonal; intro lk; exact_mod_cast div_pos lk.1.2 lk.2.2
    have normFormOutput (x : L × K → ℂ) : (star x ⬝ᵥ x).re = ∑ i, ‖x i‖ ^ 2 := by
      simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_eq_complex_ofReal, Complex.re_sum, pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
    have normFormInput (x : J × I → ℂ) : (star x ⬝ᵥ x).re = ∑ i, ‖x i‖ ^ 2 := by
      simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_eq_complex_ofReal, Complex.re_sum, pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
    have coordinateNormBound (x : L × K → ℂ) : (∑ ji, ‖(V *ᵥ x) ji‖ ^ 2) ≤ (∑ lk, ‖x lk‖ ^ 2) := by
      calc
        _ ≤ (R * ((Ψ (spectralX x))ᴴ * Ψ (spectralX x))).trace.re := by
          simpa only [coordinateAction, ri, v, u] using coordinateBound R S hR hS (Ψ (spectralX x))
        _ ≤ (T * ((spectralX x)ᴴ * spectralX x)).trace.re := traceSchwarzR (spectralX x)
        _ = _ := spectralNormR T Q hT hQ x
    have hVnorm : Vᴴ * V ≤ 1 := by
      apply Matrix.le_iff.mpr; have herm : (1 - Vᴴ * V).IsHermitian := by
        change (1 - Vᴴ * V)ᴴ = 1 - Vᴴ * V; simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      apply realFormPSD _ herm; intro x; have gram : star x ⬝ᵥ ((Vᴴ * V) *ᵥ x) = star (V *ᵥ x) ⬝ᵥ (V *ᵥ x) := by
        rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
      rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, Matrix.one_mulVec, gram, normFormOutput, normFormInput]
      exact sub_nonneg.mpr (coordinateNormBound x)
    have coordinateWeightedBound (x : L × K → ℂ) : (star (V *ᵥ x) ⬝ᵥ (A *ᵥ (V *ᵥ x))).re ≤ (star x ⬝ᵥ (B *ᵥ x)).re := by
      calc
        _ ≤ (S * (Ψ (spectralX x) * (Ψ (spectralX x))ᴴ)).trace.re := by
          have hx : V *ᵥ x = fun ji : J × I => (Real.sqrt (ri ji.2) : ℂ) * (star (v ji.1) ⬝ᵥ (Ψ (spectralX x) *ᵥ u ji.2)) := funext (coordinateAction x)
          rw [hx]; simpa only [A, sj, ri, v, u] using coordinateWeighted R S hR hS (Ψ (spectralX x))
        _ ≤ (Q * (spectralX x * (spectralX x)ᴴ)).trace.re := traceSchwarzS (spectralX x)
        _ = ∑ lk, ql lk.1 / pk lk.2 * ‖x lk‖ ^ 2 := spectralNormS T Q hT hQ x
        _ = _ := (diagonalQuadraticOutput (fun lk : L × K => ql lk.1 / pk lk.2) x).symm
    have hVA : Vᴴ * A * V ≤ B := by
      apply Matrix.le_iff.mpr; have herm : (B - Vᴴ * A * V).IsHermitian := by
        change (B - Vᴴ * A * V)ᴴ = B - Vᴴ * A * V; simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.1.eq, hB.1.eq, Matrix.mul_assoc]
      apply realFormPSD _ herm; intro x; have gram : star x ⬝ᵥ ((Vᴴ * A * V) *ᵥ x) = star (V *ᵥ x) ⬝ᵥ (A *ᵥ (V *ᵥ x)) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
      rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, gram]; exact sub_nonneg.mpr (coordinateWeightedBound x)

    have traceIdentityR {n : Type u} [Fintype n] [DecidableEq n] (R S : Matrix n n ℂ) (hR : R.IsHermitian) (hS : S.IsHermitian) (nonnegR : ∀ i, 0 ≤ hR.eigenvalues i)
        (nonnegS : ∀ j, 0 ≤ hS.eigenvalues j) (normalization : ∀ i : {i : n // 0 < hR.eigenvalues i}, ∑ j : {j : n // 0 < hS.eigenvalues j}, ‖star (fun x => hS.eigenvectorBasis j.1 x) ⬝ᵥ
              (fun x => hR.eigenvectorBasis i.1 x)‖ ^ 2 = 1) :
        let I := {i : n // 0 < hR.eigenvalues i}
        let J := {j : n // 0 < hS.eigenvalues j}
        let A : Matrix (J × I) (J × I) ℂ := diagonal (fun ji => (hS.eigenvalues ji.1.1 / hR.eigenvalues ji.2.1 : ℝ))
        let ξ : J × I → ℂ := fun ji => (Real.sqrt (hR.eigenvalues ji.2.1) : ℂ) * (star (fun x => hS.eigenvectorBasis ji.1.1 x) ⬝ᵥ (fun x => hR.eigenvectorBasis ji.2.1 x))
        (R * (cfc Real.log R - cfc Real.log S)).trace.re = -(star ξ ⬝ᵥ (cfc Real.log A *ᵥ ξ)).re := by
      classical
      dsimp only; have traceSupport : (R * (cfc Real.log R - cfc Real.log S)).trace.re = ∑ i : {i : n // 0 < hR.eigenvalues i}, ∑ j : {j : n // 0 < hS.eigenvalues j}, hR.eigenvalues i.1 *
                ‖star (fun x => hS.eigenvectorBasis j.1 x) ⬝ᵥ (fun x => hR.eigenvectorBasis i.1 x)‖ ^ 2 * (Real.log (hR.eigenvalues i.1) - Real.log (hS.eigenvalues j.1)) := by
        classical
        have mixed : (R * cfc Real.log S).trace.re = ∑ i, hR.eigenvalues i * ∑ j, Real.log (hS.eigenvalues j) * ‖star (fun x => hS.eigenvectorBasis j x) ⬝ᵥ
                  (fun x => hR.eigenvectorBasis i x)‖ ^ 2 := by
          classical
          let U : Matrix n n ℂ := hR.eigenvectorUnitary; have tr : (R * cfc Real.log S).trace = (Uᴴ * cfc Real.log S * U * diagonal (fun i => (hR.eigenvalues i : ℂ))).trace := by
            conv_lhs => rw [hR.spectral_theorem, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
            rfl
          have diag (i : n) : (Uᴴ * cfc Real.log S * U) i i = star (fun x => hR.eigenvectorBasis i x) ⬝ᵥ (cfc Real.log S *ᵥ (fun x => hR.eigenvectorBasis i x)) := by
            simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, U, Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.mulVec, dotProduct, Pi.star_apply]
            simp only [Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; ring
          have form (i : n) : (star (fun x => hR.eigenvectorBasis i x) ⬝ᵥ (cfc Real.log S *ᵥ (fun x => hR.eigenvectorBasis i x))).re = ∑ j, Real.log (hS.eigenvalues j) *
                  ‖star (fun x => hS.eigenvectorBasis j x) ⬝ᵥ (fun x => hR.eigenvectorBasis i x)‖ ^ 2 := by
            have cfcSpec : cfc Real.log S = RHLinalg.specMap hS Real.log := by
              rw [hS.cfc_eq]; rfl
            rw [cfcSpec]; simpa only [RCLike.re_to_complex, Matrix.mulVec, dotProduct, Matrix.star_apply, Matrix.IsHermitian.eigenvectorUnitary_apply, Pi.star_apply] using
              RHLinalg.hermForm_specMap hS Real.log (fun x => hR.eigenvectorBasis i x)
          rw [tr]; change (RCLike.re : ℂ →+ ℝ) _ = _; simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, map_sum, RCLike.mul_re, mul_zero, sub_zero,
            RCLike.re_to_complex, RCLike.im_to_complex, Complex.ofReal_re, Complex.ofReal_im]
          apply Finset.sum_congr rfl; intro i _; rw [diag, form]; ring
        have selfLog : (R * cfc Real.log R).trace.re = ∑ i, hR.eigenvalues i * Real.log (hR.eigenvalues i) := by
          have cfcSpec : cfc Real.log R = RHLinalg.specMap hR Real.log := by
            rw [hR.cfc_eq]; rfl
          have product : R * cfc Real.log R = RHLinalg.specMap hR (fun t : ℝ => t * Real.log t) := by
            calc
              _ = RHLinalg.specMap hR id * RHLinalg.specMap hR Real.log := by
                rw [RHLinalg.specMap_id, cfcSpec]
              _ = _ := (RHLinalg.specMap_mul hR id Real.log).symm
          rw [product]; simpa only [RHLinalg.rtrace, RCLike.re_to_complex] using RHLinalg.rtrace_specMap hR (fun t : ℝ => t * Real.log t)
        have restrict (e f : n → ℝ) (hne : ∀ i, 0 ≤ e i) (hz : ∀ i, e i = 0 → f i = 0) : (∑ i : {i : n // 0 < e i}, f i.1) = ∑ i, f i := by
          have complement : (∑ i : {i : n // ¬ 0 < e i}, f i.1) = 0 := by
            apply Finset.sum_eq_zero; intro i _; exact hz i.1 (le_antisymm (le_of_not_gt i.2) (hne i.1))
          have h := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < e i) f; rw [complement, add_zero] at h; exact h
        have selfSupport : (R * cfc Real.log R).trace.re = ∑ i : {i : n // 0 < hR.eigenvalues i}, hR.eigenvalues i.1 * Real.log (hR.eigenvalues i.1) := by
          rw [selfLog]; exact (restrict hR.eigenvalues _ nonnegR (fun i hi => by simp [hi])).symm
        have mixedSupport : (R * cfc Real.log S).trace.re = ∑ i : {i : n // 0 < hR.eigenvalues i}, hR.eigenvalues i.1 * ∑ j : {j : n // 0 < hS.eigenvalues j}, Real.log (hS.eigenvalues j.1) *
                  ‖star (fun x => hS.eigenvectorBasis j.1 x) ⬝ᵥ (fun x => hR.eigenvectorBasis i.1 x)‖ ^ 2 := by
          rw [mixed, ← restrict hR.eigenvalues _ nonnegR (fun i hi => by simp [hi])]; apply Finset.sum_congr rfl; intro i _; congr 1; exact (restrict hS.eigenvalues _ nonnegS (fun j hj => by
            simp only [hj, Real.log_zero, zero_mul])).symm
        rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, selfSupport, mixedSupport, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro i _; calc
          _ = hR.eigenvalues i.1 * Real.log (hR.eigenvalues i.1) * (∑ j : {j : n // 0 < hS.eigenvalues j}, ‖star (fun x => hS.eigenvectorBasis j.1 x) ⬝ᵥ
                    (fun x => hR.eigenvectorBasis i.1 x)‖ ^ 2) - hR.eigenvalues i.1 * ∑ j : {j : n // 0 < hS.eigenvalues j}, Real.log (hS.eigenvalues j.1) *
                  ‖star (fun x => hS.eigenvectorBasis j.1 x) ⬝ᵥ (fun x => hR.eigenvectorBasis i.1 x)‖ ^ 2 := by
              rw [normalization, mul_one]
          _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; ring
      have diagonalForm {m : Type u} [Fintype m] [DecidableEq m] (d : m → ℝ) (x : m → ℂ) : (star x ⬝ᵥ (cfc Real.log (diagonal (fun i => (d i : ℂ))) *ᵥ x)).re =
          ∑ i, Real.log (d i) * ‖x i‖ ^ 2 := by
        have hlog : cfc Real.log (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (Real.log (d i) : ℂ)) := by
          exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_log_diagonal d
        rw [hlog]; change (RCLike.re : ℂ →+ ℝ) _ = _; simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, map_sum]; apply Finset.sum_congr rfl; intro i _
        have term : star (x i) * ((Real.log (d i) : ℂ) * x i) = (Real.log (d i) : ℂ) * (star (x i) * x i) := by ring
        have eqnorm : star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
          simpa only [RCLike.star_def, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using RCLike.conj_mul (x i)
        rw [term, eqnorm, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
      rw [diagonalForm]; rw [traceSupport, Fintype.sum_prod_type, Finset.sum_comm, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro i _; dsimp only; rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt i.2),
        Real.log_div (ne_of_gt j.2) (ne_of_gt i.2)]
      ring

    have traceIdentityT {n : Type v} [Fintype n] [DecidableEq n] (R S : Matrix n n ℂ) (hR : R.IsHermitian) (hS : S.IsHermitian) (nonnegR : ∀ i, 0 ≤ hR.eigenvalues i)
        (nonnegS : ∀ j, 0 ≤ hS.eigenvalues j) (normalization : ∀ i : {i : n // 0 < hR.eigenvalues i}, ∑ j : {j : n // 0 < hS.eigenvalues j}, ‖star (fun x => hS.eigenvectorBasis j.1 x) ⬝ᵥ
              (fun x => hR.eigenvectorBasis i.1 x)‖ ^ 2 = 1) :
        let I := {i : n // 0 < hR.eigenvalues i}
        let J := {j : n // 0 < hS.eigenvalues j}
        let A : Matrix (J × I) (J × I) ℂ := diagonal (fun ji => (hS.eigenvalues ji.1.1 / hR.eigenvalues ji.2.1 : ℝ))
        let ξ : J × I → ℂ := fun ji => (Real.sqrt (hR.eigenvalues ji.2.1) : ℂ) * (star (fun x => hS.eigenvectorBasis ji.1.1 x) ⬝ᵥ (fun x => hR.eigenvectorBasis ji.2.1 x))
        (R * (cfc Real.log R - cfc Real.log S)).trace.re = -(star ξ ⬝ᵥ (cfc Real.log A *ᵥ ξ)).re := by
      classical
      dsimp only; have traceSupport : (R * (cfc Real.log R - cfc Real.log S)).trace.re = ∑ i : {i : n // 0 < hR.eigenvalues i}, ∑ j : {j : n // 0 < hS.eigenvalues j}, hR.eigenvalues i.1 *
                ‖star (fun x => hS.eigenvectorBasis j.1 x) ⬝ᵥ (fun x => hR.eigenvectorBasis i.1 x)‖ ^ 2 * (Real.log (hR.eigenvalues i.1) - Real.log (hS.eigenvalues j.1)) := by
        classical
        have mixed : (R * cfc Real.log S).trace.re = ∑ i, hR.eigenvalues i * ∑ j, Real.log (hS.eigenvalues j) * ‖star (fun x => hS.eigenvectorBasis j x) ⬝ᵥ
                  (fun x => hR.eigenvectorBasis i x)‖ ^ 2 := by
          classical
          let U : Matrix n n ℂ := hR.eigenvectorUnitary; have tr : (R * cfc Real.log S).trace = (Uᴴ * cfc Real.log S * U * diagonal (fun i => (hR.eigenvalues i : ℂ))).trace := by
            conv_lhs => rw [hR.spectral_theorem, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
            rfl
          have diag (i : n) : (Uᴴ * cfc Real.log S * U) i i = star (fun x => hR.eigenvectorBasis i x) ⬝ᵥ (cfc Real.log S *ᵥ (fun x => hR.eigenvectorBasis i x)) := by
            simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, U, Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.mulVec, dotProduct, Pi.star_apply]
            simp only [Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; ring
          have form (i : n) : (star (fun x => hR.eigenvectorBasis i x) ⬝ᵥ (cfc Real.log S *ᵥ (fun x => hR.eigenvectorBasis i x))).re = ∑ j, Real.log (hS.eigenvalues j) *
                  ‖star (fun x => hS.eigenvectorBasis j x) ⬝ᵥ (fun x => hR.eigenvectorBasis i x)‖ ^ 2 := by
            have cfcSpec : cfc Real.log S = RHLinalg.specMap hS Real.log := by
              rw [hS.cfc_eq]; rfl
            rw [cfcSpec]; simpa only [RCLike.re_to_complex, Matrix.mulVec, dotProduct, Matrix.star_apply, Matrix.IsHermitian.eigenvectorUnitary_apply, Pi.star_apply] using
              RHLinalg.hermForm_specMap hS Real.log (fun x => hR.eigenvectorBasis i x)
          rw [tr]; change (RCLike.re : ℂ →+ ℝ) _ = _; simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, map_sum, RCLike.mul_re, mul_zero, sub_zero,
            RCLike.re_to_complex, RCLike.im_to_complex, Complex.ofReal_re, Complex.ofReal_im]
          apply Finset.sum_congr rfl; intro i _; rw [diag, form]; ring
        have selfLog : (R * cfc Real.log R).trace.re = ∑ i, hR.eigenvalues i * Real.log (hR.eigenvalues i) := by
          have cfcSpec : cfc Real.log R = RHLinalg.specMap hR Real.log := by
            rw [hR.cfc_eq]; rfl
          have product : R * cfc Real.log R = RHLinalg.specMap hR (fun t : ℝ => t * Real.log t) := by
            calc
              _ = RHLinalg.specMap hR id * RHLinalg.specMap hR Real.log := by
                rw [RHLinalg.specMap_id, cfcSpec]
              _ = _ := (RHLinalg.specMap_mul hR id Real.log).symm
          rw [product]; simpa only [RHLinalg.rtrace, RCLike.re_to_complex] using RHLinalg.rtrace_specMap hR (fun t : ℝ => t * Real.log t)
        have restrict (e f : n → ℝ) (hne : ∀ i, 0 ≤ e i) (hz : ∀ i, e i = 0 → f i = 0) : (∑ i : {i : n // 0 < e i}, f i.1) = ∑ i, f i := by
          have complement : (∑ i : {i : n // ¬ 0 < e i}, f i.1) = 0 := by
            apply Finset.sum_eq_zero; intro i _; exact hz i.1 (le_antisymm (le_of_not_gt i.2) (hne i.1))
          have h := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < e i) f; rw [complement, add_zero] at h; exact h
        have selfSupport : (R * cfc Real.log R).trace.re = ∑ i : {i : n // 0 < hR.eigenvalues i}, hR.eigenvalues i.1 * Real.log (hR.eigenvalues i.1) := by
          rw [selfLog]; exact (restrict hR.eigenvalues _ nonnegR (fun i hi => by simp [hi])).symm
        have mixedSupport : (R * cfc Real.log S).trace.re = ∑ i : {i : n // 0 < hR.eigenvalues i}, hR.eigenvalues i.1 * ∑ j : {j : n // 0 < hS.eigenvalues j}, Real.log (hS.eigenvalues j.1) *
                  ‖star (fun x => hS.eigenvectorBasis j.1 x) ⬝ᵥ (fun x => hR.eigenvectorBasis i.1 x)‖ ^ 2 := by
          rw [mixed, ← restrict hR.eigenvalues _ nonnegR (fun i hi => by simp [hi])]; apply Finset.sum_congr rfl; intro i _; congr 1; exact (restrict hS.eigenvalues _ nonnegS (fun j hj => by
            simp only [hj, Real.log_zero, zero_mul])).symm
        rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, selfSupport, mixedSupport, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro i _; calc
          _ = hR.eigenvalues i.1 * Real.log (hR.eigenvalues i.1) * (∑ j : {j : n // 0 < hS.eigenvalues j}, ‖star (fun x => hS.eigenvectorBasis j.1 x) ⬝ᵥ
                    (fun x => hR.eigenvectorBasis i.1 x)‖ ^ 2) - hR.eigenvalues i.1 * ∑ j : {j : n // 0 < hS.eigenvalues j}, Real.log (hS.eigenvalues j.1) *
                  ‖star (fun x => hS.eigenvectorBasis j.1 x) ⬝ᵥ (fun x => hR.eigenvectorBasis i.1 x)‖ ^ 2 := by
              rw [normalization, mul_one]
          _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; ring
      have diagonalForm {m : Type v} [Fintype m] [DecidableEq m] (d : m → ℝ) (x : m → ℂ) : (star x ⬝ᵥ (cfc Real.log (diagonal (fun i => (d i : ℂ))) *ᵥ x)).re =
          ∑ i, Real.log (d i) * ‖x i‖ ^ 2 := by
        have hlog : cfc Real.log (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (Real.log (d i) : ℂ)) := by
          exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_log_diagonal d
        rw [hlog]; change (RCLike.re : ℂ →+ ℝ) _ = _; simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, map_sum]; apply Finset.sum_congr rfl; intro i _
        have term : star (x i) * ((Real.log (d i) : ℂ) * x i) = (Real.log (d i) : ℂ) * (star (x i) * x i) := by ring
        have eqnorm : star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
          simpa only [RCLike.star_def, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using RCLike.conj_mul (x i)
        rw [term, eqnorm, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
      rw [diagonalForm]; rw [traceSupport, Fintype.sum_prod_type, Finset.sum_comm, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro i _; dsimp only; rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt i.2),
        Real.log_div (ne_of_gt j.2) (ne_of_gt i.2)]
      ring
    have traceR : (R * (cfc Real.log R - cfc Real.log S)).trace.re = -(star ξ ⬝ᵥ (cfc Real.log A *ᵥ ξ)).re := traceIdentityR R S hR.1 hS.1 hR.eigenvalues_nonneg hS.eigenvalues_nonneg
        positiveCoordinatesR
    have traceT : (T * (cfc Real.log T - cfc Real.log Q)).trace.re = -(star η ⬝ᵥ (cfc Real.log B *ᵥ η)).re := traceIdentityT T Q hT.1 hQ.1 hT.eigenvalues_nonneg hQ.eigenvalues_nonneg
        positiveCoordinatesT
    have inputLog (X : DensityState a) (hX : (CStarMatrix.ofMatrix.symm X.1).IsHermitian) : CStarMatrix.ofMatrix (cfc Real.log (CStarMatrix.ofMatrix.symm X.1)) = CFC.log X.1 := by
      exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log _ ((CStarMatrix.ofMatrix.symm X.1).finite_real_spectrum.continuousOn _)
        CStarMatrix.ofMatrixL.continuous hX (by exact hX)
    have outputLog (X : DensityState b) (hX : (CStarMatrix.ofMatrix.symm X.1).IsHermitian) : CStarMatrix.ofMatrix (cfc Real.log (CStarMatrix.ofMatrix.symm X.1)) = CFC.log X.1 := by
      exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log _ ((CStarMatrix.ofMatrix.symm X.1).finite_real_spectrum.continuousOn _)
        CStarMatrix.ofMatrixL.continuous hX (by exact hX)
    have hlogR := inputLog ρ hR.1; have hlogS := inputLog σ hS.1; have hlogT := outputLog (Φ.mapState ρ) hT.1; have hlogQ := outputLog (Φ.mapState σ) hQ.1
    have canonicalTraceR : finiteTraceLogRelativeEntropy ρ σ = -(star ξ ⬝ᵥ (cfc Real.log A *ᵥ ξ)).re := by
      unfold finiteTraceLogRelativeEntropy; rw [← hlogR, ← hlogS]; exact traceR
    have canonicalTraceT : finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) = -(star η ⬝ᵥ (cfc Real.log B *ᵥ η)).re := by
      unfold finiteTraceLogRelativeEntropy; rw [← hlogT, ← hlogQ]; exact traceT

    have rectangularCFCAmbient {n m : Type (max u v)} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (Z : Matrix n n ℂ) (C : Matrix m m ℂ) (hZ : Z.IsHermitian) (hC : C.IsHermitian)
        (W : Matrix n m ℂ) (h : Z * W = W * C) (f : ℝ → ℝ) : cfc f Z * W = W * cfc f C := by
      classical
      let U : Matrix n n ℂ := hZ.eigenvectorUnitary; let T : Matrix m m ℂ := hC.eigenvectorUnitary; let E : Matrix n m ℂ := Uᴴ * W * T; have hU : Uᴴ * U = 1 := hZ.eigenvectorUnitary.2.1
      have hu : U * Uᴴ = 1 := hZ.eigenvectorUnitary.2.2; have hT : Tᴴ * T = 1 := hC.eigenvectorUnitary.2.1; have ht : T * Tᴴ = 1 := hC.eigenvectorUnitary.2.2
      have zs : Z = U * diagonal (fun i => (hZ.eigenvalues i : ℂ)) * Uᴴ := by
        simpa only [Unitary.conjStarAlgAut_apply, U, T, Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose] using hZ.spectral_theorem
      have cs : C = T * diagonal (fun i => (hC.eigenvalues i : ℂ)) * Tᴴ := by
        simpa only [Unitary.conjStarAlgAut_apply, U, T, Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose] using hC.spectral_theorem
      have coeff : diagonal (fun i => (hZ.eigenvalues i : ℂ)) * E = E * diagonal (fun j => (hC.eigenvalues j : ℂ)) := by
        calc
          _ = Uᴴ * (Z * W) * T := by
            conv_rhs => { rw [zs] }; simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
          _ = Uᴴ * (W * C) * T := by rw [h]
          _ = _ := by
            conv_lhs => { rw [cs] }; simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ T, hT, Matrix.one_mul, Matrix.mul_one]
      have fcoeff : diagonal (fun i => (f (hZ.eigenvalues i) : ℂ)) * E = E * diagonal (fun j => (f (hC.eigenvalues j) : ℂ)) := by
        ext i j; simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]; have eq := congrArg (fun M : Matrix n m ℂ => M i j) coeff; simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at eq
        by_cases he : hZ.eigenvalues i = hC.eigenvalues j
        · rw [he, mul_comm]
        · have hz : E i j = 0 := by
            have hn : (hZ.eigenvalues i : ℂ) ≠ (hC.eigenvalues j : ℂ) := by { exact_mod_cast he }; have heq : ((hZ.eigenvalues i : ℂ) - (hC.eigenvalues j : ℂ)) * E i j = 0 := by
              linear_combination eq
            exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hn)
          simp only [hz, mul_zero, zero_mul]
      have reconstruct : U * E * Tᴴ = W := by
        simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc U Uᴴ, hu, Matrix.one_mul, ← Matrix.mul_assoc T Tᴴ, ht, Matrix.mul_one]
      rw [hZ.cfc_eq, hC.cfc_eq, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
      change (U * diagonal (fun i => (f (hZ.eigenvalues i) : ℂ)) * Uᴴ) * W = W * (T * diagonal (fun j => (f (hC.eigenvalues j) : ℂ)) * Tᴴ)
      conv_lhs => { rw [← reconstruct] }; conv_rhs => { rw [← reconstruct] }; simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul,
        ← Matrix.mul_assoc Tᴴ T, hT, Matrix.one_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc _ E, fcoeff]; simp only [Matrix.mul_assoc]
    have rectangularCFCOutput {n : Type (max u v)} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
        (Z : Matrix n n ℂ) (C : Matrix m m ℂ) (hZ : Z.IsHermitian) (hC : C.IsHermitian) (W : Matrix n m ℂ) (h : Z * W = W * C) (f : ℝ → ℝ) : cfc f Z * W = W * cfc f C := by
      classical
      let U : Matrix n n ℂ := hZ.eigenvectorUnitary; let T : Matrix m m ℂ := hC.eigenvectorUnitary; let E : Matrix n m ℂ := Uᴴ * W * T; have hU : Uᴴ * U = 1 := hZ.eigenvectorUnitary.2.1
      have hu : U * Uᴴ = 1 := hZ.eigenvectorUnitary.2.2; have hT : Tᴴ * T = 1 := hC.eigenvectorUnitary.2.1; have ht : T * Tᴴ = 1 := hC.eigenvectorUnitary.2.2
      have zs : Z = U * diagonal (fun i => (hZ.eigenvalues i : ℂ)) * Uᴴ := by
        simpa only [Unitary.conjStarAlgAut_apply, U, T, Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose] using hZ.spectral_theorem
      have cs : C = T * diagonal (fun i => (hC.eigenvalues i : ℂ)) * Tᴴ := by
        simpa only [Unitary.conjStarAlgAut_apply, U, T, Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose] using hC.spectral_theorem
      have coeff : diagonal (fun i => (hZ.eigenvalues i : ℂ)) * E = E * diagonal (fun j => (hC.eigenvalues j : ℂ)) := by
        calc
          _ = Uᴴ * (Z * W) * T := by
            conv_rhs => { rw [zs] }; simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
          _ = Uᴴ * (W * C) * T := by rw [h]
          _ = _ := by
            conv_lhs => { rw [cs] }; simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ T, hT, Matrix.one_mul, Matrix.mul_one]
      have fcoeff : diagonal (fun i => (f (hZ.eigenvalues i) : ℂ)) * E = E * diagonal (fun j => (f (hC.eigenvalues j) : ℂ)) := by
        ext i j; simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]; have eq := congrArg (fun M : Matrix n m ℂ => M i j) coeff; simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at eq
        by_cases he : hZ.eigenvalues i = hC.eigenvalues j
        · rw [he, mul_comm]
        · have hz : E i j = 0 := by
            have hn : (hZ.eigenvalues i : ℂ) ≠ (hC.eigenvalues j : ℂ) := by { exact_mod_cast he }; have heq : ((hZ.eigenvalues i : ℂ) - (hC.eigenvalues j : ℂ)) * E i j = 0 := by
              linear_combination eq
            exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hn)
          simp only [hz, mul_zero, zero_mul]
      have reconstruct : U * E * Tᴴ = W := by
        simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc U Uᴴ, hu, Matrix.one_mul, ← Matrix.mul_assoc T Tᴴ, ht, Matrix.mul_one]
      rw [hZ.cfc_eq, hC.cfc_eq, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
      change (U * diagonal (fun i => (f (hZ.eigenvalues i) : ℂ)) * Uᴴ) * W = W * (T * diagonal (fun j => (f (hC.eigenvalues j) : ℂ)) * Tᴴ)
      conv_lhs => { rw [← reconstruct] }; conv_rhs => { rw [← reconstruct] }; simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul,
        ← Matrix.mul_assoc Tᴴ T, hT, Matrix.one_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc _ E, fcoeff]; simp only [Matrix.mul_assoc]
    have matrixLogOrder {n : Type v} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) (hA : A.PosDef) (hab : A ≤ B) : cfc Real.log A ≤ cfc Real.log B := by
      classical
      let e := CStarMatrix.ofMatrixStarAlgEquiv (n := n) (A := ℂ); have hB : B.PosSemidef := (hA.posSemidef.nonneg.trans hab).posSemidef
      have logMap (X : Matrix n n ℂ) (hX : X.IsHermitian) : e (cfc Real.log X) = CFC.log (e X) := by
        exact StarAlgHomClass.map_cfc e Real.log X (X.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous hX (by exact hX)
      have posA : IsStrictlyPositive (e A) := by
        exact (hA.isUnit.map e.toAlgEquiv.toAlgHom).isStrictlyPositive (map_nonneg e hA.posSemidef.nonneg)
      have hAB : e A ≤ e B := by
        have h := map_nonneg e (sub_nonneg.mpr hab); apply sub_nonneg.mp; simpa only [map_sub] using h
      have h := CFC.log_le_log hAB posA; rw [← logMap A hA.1, ← logMap B hB.1] at h; have h' := map_nonneg e.symm (sub_nonneg.mpr h)
      simpa only [map_sub, StarAlgEquiv.symm_apply_apply, sub_nonneg] using h'
    have matrixLogMidpoint {n : Type (max u v)} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) (hA : A.PosDef) (hB : B.PosDef) : (1/2 : ℝ) • cfc Real.log A + (1/2 : ℝ) • cfc Real.log B ≤
          cfc Real.log ((1/2 : ℝ) • A + (1/2 : ℝ) • B) := by
      classical
      let e := CStarMatrix.ofMatrixStarAlgEquiv (n := n) (A := ℂ); have pos (X : Matrix n n ℂ) (hX : X.PosDef) : IsStrictlyPositive (e X) := by
        exact (hX.isUnit.map e.toAlgEquiv.toAlgHom).isStrictlyPositive (map_nonneg e hX.posSemidef.nonneg)
      have midpoint : ((1/2 : ℝ) • A + (1/2 : ℝ) • B).IsHermitian := by
        exact (hA.1.smul (show IsSelfAdjoint (1/2 : ℝ) from rfl)).add (hB.1.smul (show IsSelfAdjoint (1/2 : ℝ) from rfl))
      have logMap (X : Matrix n n ℂ) (hX : X.IsHermitian) : e (cfc Real.log X) = CFC.log (e X) := by
        exact StarAlgHomClass.map_cfc e Real.log X (X.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous hX (by exact hX)
      have h := (CFC.concaveOn_log (A := CStarMatrix n n ℂ)).2 (pos A hA) (pos B hB) (show 0 ≤ (1/2 : ℝ) by norm_num) (show 0 ≤ (1/2 : ℝ) by norm_num) (show (1/2 : ℝ) + 1/2 = 1 by norm_num)
      rw [← logMap A hA.1, ← logMap B hB.1] at h; change e ((1/2 : ℝ) • cfc Real.log A + (1/2 : ℝ) • cfc Real.log B) ≤ CFC.log (e ((1/2 : ℝ) • A + (1/2 : ℝ) • B)) at h
      rw [← logMap _ midpoint] at h; have h' := map_nonneg e.symm (sub_nonneg.mpr h); change 0 ≤ (cfc Real.log ((1/2 : ℝ) • A + (1/2 : ℝ) • B) -
        ((1/2 : ℝ) • cfc Real.log A + (1/2 : ℝ) • cfc Real.log B)) at h'
      exact sub_nonneg.mp h'
    have compressedPositiveAmbient {n m : Type (max u v)} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (F : Matrix n n ℂ) (W : Matrix n m ℂ) (hF : F.PosDef)
        (hW : Wᴴ * W = 1) : (Wᴴ * F * W).PosDef := by
      classical
      apply hF.conjTranspose_mul_mul_same; intro x y hxy; have h := congrArg (fun z => Wᴴ *ᵥ z) hxy; simpa only [Matrix.mulVec_mulVec, hW, Matrix.one_mulVec] using h
    have compressedPositiveOutput {n : Type (max u v)} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (F : Matrix n n ℂ) (W : Matrix n m ℂ) (hF : F.PosDef)
        (hW : Wᴴ * W = 1) : (Wᴴ * F * W).PosDef := by
      classical
      apply hF.conjTranspose_mul_mul_same; intro x y hxy; have h := congrArg (fun z => Wᴴ *ᵥ z) hxy; simpa only [Matrix.mulVec_mulVec, hW, Matrix.one_mulVec] using h

    have reflectionFacts {n : Type (max u v)} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (F : Matrix n n ℂ) (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) :
        let P := W * Wᴴ
        let U := P + P - 1
        Uᴴ = U ∧ U * U = 1 ∧ U * W = W ∧ ((1 / 2 : ℝ) • (F + U * F * U)) * W = W * (Wᴴ * F * W) := by
      classical
      dsimp only; let P := W * Wᴴ; let U := P + P - 1; have hp : P * P = P := by
        change (W * Wᴴ) * (W * Wᴴ) = _; rw [Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul]
      have hpW : P * W = W := by
        change (W * Wᴴ) * W = _; rw [Matrix.mul_assoc, hW, Matrix.mul_one]
      have hs : Uᴴ = U := by
        simp only [U, P, Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      have hu : U * U = 1 := by
        simp only [U, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hp]
        abel
      have hUW : U * W = W := by
        simp only [U, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, hpW]; abel
      refine ⟨hs, hu, hUW, ?_⟩; change ((1 / 2 : ℝ) • (F + U * F * U)) * W = _; rw [Matrix.smul_mul, Matrix.add_mul]; simp only [Matrix.mul_assoc, hUW]; rw [← Matrix.mul_assoc U F W]
      have twice : F * W + U * F * W = (W * (Wᴴ * F * W)) + (W * (Wᴴ * F * W)) := by
        simp only [U, P, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]; abel
      rw [twice, ← two_smul ℝ, smul_smul]; norm_num <;> simp only [Matrix.mul_assoc]
    have isometryLogCompression {n : Type (max u v)} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (F : Matrix n n ℂ) (W : Matrix n m ℂ) (hF : F.PosDef)
        (hW : Wᴴ * W = 1) : Wᴴ * cfc Real.log F * W ≤ cfc Real.log (Wᴴ * F * W) := by
      classical
      let P := W * Wᴴ; let U := P + P - 1; let C := Wᴴ * F * W; let Z := (1/2 : ℝ) • (F + U * F * U); obtain ⟨hs, hu, hUW, hZW⟩ := reflectionFacts F W hW; change Uᴴ = U at hs
      change U * U = 1 at hu; change U * W = W at hUW; change Z * W = W * C at hZW; have hUiso : Uᴴ * U = 1 := by { rw [hs, hu] }; have hUF : (U * F * U).PosDef := by
        have h := compressedPositiveAmbient F U hF hUiso; simpa only [hs] using h
      have hC : C.PosDef := compressedPositiveOutput F W hF hW; have hZ : Z.IsHermitian := by
        exact (hF.1.add hUF.1).smul (show IsSelfAdjoint (1/2 : ℝ) from rfl)
      have cov : cfc Real.log (U * F * U) = U * cfc Real.log F * U := by
        have he : (U * F * U) * U = U * F := by
          simp only [Matrix.mul_assoc, hu, Matrix.mul_one]
        have h := rectangularCFCAmbient (U * F * U) F hUF.1 hF.1 U he Real.log; have h' := congrArg (fun M : Matrix n n ℂ => M * U) h
        simpa only [Matrix.mul_assoc, hu, Matrix.mul_one] using h'
      have compression : Wᴴ * cfc Real.log Z * W = cfc Real.log C := by
        have h := rectangularCFCOutput Z C hZ hC.1 W hZW Real.log; have h' := congrArg (fun M : Matrix n m ℂ => Wᴴ * M) h; simpa only [← Matrix.mul_assoc, hW, Matrix.one_mul] using h'
      have hWU : Wᴴ * U = Wᴴ := by
        have h := congrArg Matrix.conjTranspose hUW; simpa only [Matrix.conjTranspose_mul, hs] using h
      have midpoint := matrixLogMidpoint F (U * F * U) hF hUF; have hz : (1/2 : ℝ) • F + (1/2 : ℝ) • (U * F * U) = Z := by
        rw [← smul_add]
      rw [hz] at midpoint; have ps := (Matrix.le_iff.mp midpoint).conjTranspose_mul_mul_same W; have hleft : Wᴴ * ((1/2 : ℝ) • cfc Real.log F + (1/2 : ℝ) • cfc Real.log (U * F * U)) * W =
          Wᴴ * cfc Real.log F * W := by
        rw [cov]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hUW, ← Matrix.mul_assoc Wᴴ U, hWU]
        rw [← add_smul]; norm_num
      apply Matrix.le_iff.mpr; simpa only [Matrix.mul_sub, Matrix.sub_mul, compression, hleft] using ps

    have defectFacts {n : Type u} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (V : Matrix n m ℂ) (ξ : n → ℂ) (η : m → ℂ) (hV : Vᴴ * V ≤ 1) (hVX : V *ᵥ η = ξ)
        (hξ : ∑ i, ‖ξ i‖ ^ 2 = 1) (hη : ∑ i, ‖η i‖ ^ 2 = 1) :
        let D := CFC.sqrt (1 - Vᴴ * V)
        let W : Matrix (n ⊕ m) m ℂ := Sum.elim (fun i => V i) (fun i => D i)
        Wᴴ * W = 1 ∧ D *ᵥ η = 0 ∧ W *ᵥ η = Sum.elim ξ 0 := by
      classical
      let E : Matrix m m ℂ := 1 - Vᴴ * V; let D : Matrix m m ℂ := CFC.sqrt E; let W : Matrix (n ⊕ m) m ℂ := Sum.elim (fun i => V i) (fun i => D i)
      change Wᴴ * W = 1 ∧ D *ᵥ η = 0 ∧ W *ᵥ η = Sum.elim ξ 0; have hE : 0 ≤ E := sub_nonneg.mpr hV; have hD : D.PosSemidef := (CFC.sqrt_nonneg E).posSemidef; have hDD : Dᴴ * D = E := by
        rw [hD.1.eq]; exact CFC.sqrt_mul_sqrt_self E hE
      have hW : Wᴴ * W = Vᴴ * V + Dᴴ * D := by
        ext i j; change (∑ t : n ⊕ m, star (W t i) * W t j) = _; simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, W,
          Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.add_apply]
      have hw : Wᴴ * W = 1 := by
        rw [hW, hDD]; change Vᴴ * V + (1 - Vᴴ * V) = 1; abel
      have hnormξ : star ξ ⬝ᵥ ξ = 1 := by
        calc
          _ = ((∑ i, ‖ξ i‖ ^ 2 : ℝ) : ℂ) := by
            simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow, Complex.ofReal_sum]
          _ = 1 := by rw [hξ]; rfl
      have hnormη : star η ⬝ᵥ η = 1 := by
        calc
          _ = ((∑ i, ‖η i‖ ^ 2 : ℝ) : ℂ) := by
            simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow, Complex.ofReal_sum]
          _ = 1 := by rw [hη]; rfl
      have gram : star η ⬝ᵥ ((Vᴴ * V) *ᵥ η) = star (V *ᵥ η) ⬝ᵥ (V *ᵥ η) := by
        rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
      have hz : star η ⬝ᵥ (E *ᵥ η) = 0 := by
        simp only [E, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, gram, hVX, hnormη, hnormξ, sub_self]
      have hd : D *ᵥ η = 0 := by
        have hg : star (D *ᵥ η) ⬝ᵥ (D *ᵥ η) = 0 := by
          calc
            _ = star η ⬝ᵥ ((Dᴴ * D) *ᵥ η) := by
              symm; rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
            _ = 0 := by rw [hDD]; exact hz
        exact dotProduct_star_self_eq_zero.mp hg
      refine ⟨hw, hd, ?_⟩; ext i; cases i with
      | inl i => exact congrFun hVX i
      | inr i => exact congrFun hd i
    have blockCompression {n : Type u} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (V : Matrix n m ℂ) (D : Matrix m m ℂ) (a : n → ℝ) (ε : ℝ) :
        let W : Matrix (n ⊕ m) m ℂ := Sum.elim (fun i => V i) (fun i => D i)
        let F : Matrix (n ⊕ m) (n ⊕ m) ℂ := diagonal (fun i => ((Sum.elim a (fun _ => ε) i : ℝ) : ℂ))
        Wᴴ * F * W = Vᴴ * diagonal (fun i => (a i : ℂ)) * V + ε • (Dᴴ * D) := by
      classical
      let W : Matrix (n ⊕ m) m ℂ := Sum.elim (fun i => V i) (fun i => D i); let F : Matrix (n ⊕ m) (n ⊕ m) ℂ := diagonal (fun i => ((Sum.elim a (fun _ => ε) i : ℝ) : ℂ))
      change Wᴴ * F * W = Vᴴ * diagonal (fun i => (a i : ℂ)) * V + ε • (Dᴴ * D); ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, F, Matrix.diagonal_apply]
      simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Fintype.sum_sum_type]; simp only [W, Sum.elim_inl, Sum.elim_inr]; congr 1; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro k _
      change star (D k i) * (ε : ℂ) * D k j = (ε : ℂ) * (star (D k i) * D k j); ring
    have finiteLogLimit {m : Type v} [Fintype m] (b c : m → ℝ) (hb : ∀ i, 0 < b i) (r : ℝ) (h : ∀ ε : ℝ, 0 < ε → r ≤ ∑ i, Real.log (b i + ε) * c i) : r ≤ ∑ i, Real.log (b i) * c i := by
      classical
      have ht : Filter.Tendsto (fun ε : ℝ => ∑ i, Real.log (b i + ε) * c i) (𝓝[>] 0) (𝓝 (∑ i, Real.log (b i) * c i)) := by
        apply tendsto_finsetSum; intro i _; have hi : ContinuousAt (fun ε : ℝ => Real.log (b i + ε) * c i) 0 := by
          apply ContinuousAt.mul _ continuousAt_const; exact (Real.continuousAt_log (by simpa only [add_zero] using ne_of_gt (hb i))).comp (continuousAt_const.add continuousAt_id)
        simpa only [add_zero] using hi.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
      have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, r ≤ ∑ i, Real.log (b i + ε) * c i := by
        filter_upwards [self_mem_nhdsWithin] with ε hε; exact h ε hε
      simpa only [add_zero] using ge_of_tendsto ht he
    have diagonalLogFormAmbient {m : Type (max u v)} [Fintype m] [DecidableEq m] (d : m → ℝ) (x : m → ℂ) : (star x ⬝ᵥ (cfc Real.log (diagonal (fun i => (d i : ℂ))) *ᵥ x)).re =
        ∑ i, Real.log (d i) * ‖x i‖ ^ 2 := by
      have hlog : cfc Real.log (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (Real.log (d i) : ℂ)) := by
        exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_log_diagonal d
      rw [hlog]; change (RCLike.re : ℂ →+ ℝ) _ = _; simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, map_sum]; apply Finset.sum_congr rfl; intro i _
      have term : star (x i) * ((Real.log (d i) : ℂ) * x i) = (Real.log (d i) : ℂ) * (star (x i) * x i) := by ring
      have eqnorm : star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
        simpa only [RCLike.star_def, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using RCLike.conj_mul (x i)
      rw [term, eqnorm, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
    have diagonalLogFormInput {m : Type u} [Fintype m] [DecidableEq m] (d : m → ℝ) (x : m → ℂ) : (star x ⬝ᵥ (cfc Real.log (diagonal (fun i => (d i : ℂ))) *ᵥ x)).re =
        ∑ i, Real.log (d i) * ‖x i‖ ^ 2 := by
      have hlog : cfc Real.log (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (Real.log (d i) : ℂ)) := by
        exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_log_diagonal d
      rw [hlog]; change (RCLike.re : ℂ →+ ℝ) _ = _; simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, map_sum]; apply Finset.sum_congr rfl; intro i _
      have term : star (x i) * ((Real.log (d i) : ℂ) * x i) = (Real.log (d i) : ℂ) * (star (x i) * x i) := by ring
      have eqnorm : star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
        simpa only [RCLike.star_def, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using RCLike.conj_mul (x i)
      rw [term, eqnorm, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
    have diagonalLogFormOutput {m : Type v} [Fintype m] [DecidableEq m] (d : m → ℝ) (x : m → ℂ) : (star x ⬝ᵥ (cfc Real.log (diagonal (fun i => (d i : ℂ))) *ᵥ x)).re =
        ∑ i, Real.log (d i) * ‖x i‖ ^ 2 := by
      have hlog : cfc Real.log (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (Real.log (d i) : ℂ)) := by
        exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_log_diagonal d
      rw [hlog]; change (RCLike.re : ℂ →+ ℝ) _ = _; simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, map_sum]; apply Finset.sum_congr rfl; intro i _
      have term : star (x i) * ((Real.log (d i) : ℂ) * x i) = (Real.log (d i) : ℂ) * (star (x i) * x i) := by ring
      have eqnorm : star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
        simpa only [RCLike.star_def, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using RCLike.conj_mul (x i)
      rw [term, eqnorm, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]

    have regularizedCore {n : Type u} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (p : n → ℝ) (q : m → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
        (V : Matrix n m ℂ) (ξ : n → ℂ) (η : m → ℂ) (hV : Vᴴ * V ≤ 1) (hVA : Vᴴ * diagonal (fun i => (p i : ℂ)) * V ≤ diagonal (fun i => (q i : ℂ)))
        (hVX : V *ᵥ η = ξ) (hξ : ∑ i, ‖ξ i‖ ^ 2 = 1) (hη : ∑ i, ‖η i‖ ^ 2 = 1) : (star ξ ⬝ᵥ (cfc Real.log (diagonal (fun i => (p i : ℂ))) *ᵥ ξ)).re ≤
          (star η ⬝ᵥ (cfc Real.log (diagonal (fun i => (q i : ℂ))) *ᵥ η)).re := by
      classical
      let A : Matrix n n ℂ := diagonal (fun i => (p i : ℂ)); let B : Matrix m m ℂ := diagonal (fun i => (q i : ℂ)); let E : Matrix m m ℂ := 1 - Vᴴ * V; let D := CFC.sqrt E
      let W : Matrix (n ⊕ m) m ℂ := Sum.elim (fun i => V i) (fun i => D i); obtain ⟨hW, hdη, hWη⟩ := defectFacts V ξ η hV hVX hξ hη; change Wᴴ * W = 1 at hW
      change W *ᵥ η = Sum.elim ξ 0 at hWη; have hE : 0 ≤ E := sub_nonneg.mpr hV; have hD : D.PosSemidef := (CFC.sqrt_nonneg E).posSemidef; have hDD : Dᴴ * D = E := by
        rw [hD.1.eq]; exact CFC.sqrt_mul_sqrt_self E hE
      have hbound (ε : ℝ) (hε : 0 < ε) : (star ξ ⬝ᵥ (cfc Real.log A *ᵥ ξ)).re ≤ ∑ i, Real.log (q i + ε) * ‖η i‖ ^ 2 := by
        let F : Matrix (n ⊕ m) (n ⊕ m) ℂ := diagonal (fun i => ((Sum.elim p (fun _ => ε) i : ℝ) : ℂ))
        let C := Wᴴ * F * W; have hF : F.PosDef := by
          apply Matrix.PosDef.diagonal; intro i; cases i with
          | inl i => exact_mod_cast hp i
          | inr i => exact_mod_cast hε
        have hC : C.PosDef := compressedPositiveOutput F W hF hW; have cf : C = Vᴴ * A * V + ε • E := by
          have h := blockCompression V D p ε; simpa only [hDD] using h
        have eLe : E ≤ 1 := sub_le_self _ (Matrix.posSemidef_conjTranspose_mul_self V).nonneg; have cLe : C ≤ B + ε • (1 : Matrix m m ℂ) := by
          rw [cf]; exact add_le_add hVA (smul_le_smul_of_nonneg_left eLe hε.le)
        have ord := (isometryLogCompression F W hF hW).trans (matrixLogOrder C (B + ε • (1 : Matrix m m ℂ)) hC cLe)
        have hr := (Matrix.le_iff.mp ord).re_dotProduct_nonneg η; rw [Matrix.sub_mulVec, dotProduct_sub, RCLike.re_to_complex, Complex.sub_re] at hr
        have gram : star η ⬝ᵥ (Wᴴ * cfc Real.log F * W) *ᵥ η = star (W *ᵥ η) ⬝ᵥ (cfc Real.log F *ᵥ (W *ᵥ η)) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
        have ambient : (star (W *ᵥ η) ⬝ᵥ (cfc Real.log F *ᵥ (W *ᵥ η))).re = (star ξ ⬝ᵥ (cfc Real.log A *ᵥ ξ)).re := by
          rw [hWη]; rw [diagonalLogFormAmbient, diagonalLogFormInput]; simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
            norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, Finset.sum_const_zero, add_zero]
        have bl : B + ε • (1 : Matrix m m ℂ) = diagonal (fun i => ((q i + ε : ℝ) : ℂ)) := by
          ext i j; by_cases h : i = j <;> simp [B, Matrix.diagonal_apply, Matrix.one_apply, h]
        rw [gram, ambient, bl, diagonalLogFormOutput] at hr; exact sub_nonneg.mp hr
      change (star ξ ⬝ᵥ (cfc Real.log A *ᵥ ξ)).re ≤ (star η ⬝ᵥ (cfc Real.log B *ᵥ η)).re
      conv_rhs => { rw [diagonalLogFormOutput] }; exact finiteLogLimit q (fun i => ‖η i‖ ^ 2) hq _ hbound
    rw [canonicalTraceT, canonicalTraceR]; apply neg_le_neg; exact regularizedCore (fun ji : J × I => sj ji.1 / ri ji.2) (fun lk : L × K => ql lk.1 / pk lk.2)
      (fun ji => div_pos ji.1.2 ji.2.2) (fun lk => div_pos lk.1.2 lk.2.2) V ξ η hVnorm hVA mapsη normξ normη
  · rw [extendedQuantumRelativeEntropy_eq_top_of_not_support support]
    exact le_top
end D5.S3.Quantum.Divergence.CanonicalChannelDPI
