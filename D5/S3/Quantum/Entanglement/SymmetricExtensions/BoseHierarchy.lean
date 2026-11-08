/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native Parrilo hierarchy and actual Bose extension marginal duality. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseSOSDuality
import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseLDUI
import D5.S3.QuadraticForms.ParriloHierarchy

/-! The complete-graph characterization is prior Gulati--Nechita--Park,
Theorem 8.16. The star and companion applications are from the note by
Haobo Ma, then Wenlin Zhang. All cones are unnormalized. -/

open scoped BigOperators ComplexOrder RealInnerProductSpace Kronecker
open Matrix MvPolynomial
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDPS
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDual
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseRootTranspose
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseLDUI

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseHierarchy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {n : ℕ}

open D5.S3.QuadraticForms.ParriloHierarchy
open private liftedForm_homogeneous from
  D5.S3.QuadraticForms.ParriloHierarchy

/-- The positive polar uses the ordinary real matrix pairing. -/
def parriloPolar (k : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ M ∈ K k, 0 ≤ ∑ i, ∑ j, P i j * M i j

section Tensor

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

open private ordinary_input_pos from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDual
open private marginal_bose from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDPS
open private edgeLift edge_trace_duality from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl

private lemma tensorPhase_split (a b : I) (hab : a ≠ b) (z : L → ℂ) (x : I → L) :
    tensorPhase z x = z (x a) * z (x b) *
      ∏ i : {k : I // k ≠ a ∧ k ≠ b}, z (x i) := by
  have he : (∏ i : {k : I // k ≠ a ∧ k ≠ b}, z (x i)) =
      ∏ i ∈ ({a,b} : Finset I)ᶜ, z (x i) := by
    symm
    apply Finset.prod_subtype
    intro i
    simp
  rw [he]
  simpa only [tensorPhase,Finset.prod_pair hab] using
    (Finset.prod_mul_prod_compl {a,b} (fun i => z (x i))).symm

private lemma tensorPhase_edgeSplit (a b : I) (hab : a ≠ b) (z : L → ℂ)
    (v : L × L) (c : {k : I // k ≠ a ∧ k ≠ b} → L) :
    tensorPhase z ((edgeSplit a b hab).symm (v,c)) =
      (z v.1 * z v.2) * tensorPhase z c := by
  rw [tensorPhase_split a b hab]
  have ha : ((edgeSplit a b hab).symm (v,c)) a = v.1 := by simp [edgeSplit]
  have hb : ((edgeSplit a b hab).symm (v,c)) b = v.2 := by
    simp [edgeSplit,Ne.symm hab]
  rw [ha,hb]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp [edgeSplit,i.property.1,i.property.2]

/-- The actual adjoint of the unnormalized marginal has the coherent symbol
of the pair multiplied by the norm contribution of the remaining registers. -/
private lemma edgeLift_coherent (a b : I) (hab : a ≠ b)
    (A : Matrix (L × L) (L × L) ℂ) (z : L → ℂ) :
    star (tensorPhase z) ⬝ᵥ (edgeLift a b hab A *ᵥ tensorPhase z) =
      (∑ c : {k : I // k ≠ a ∧ k ≠ b} → L,
        star (tensorPhase z c) * tensorPhase z c) *
      (star (fun v : L × L => z v.1 * z v.2) ⬝ᵥ
        (A *ᵥ (fun v => z v.1 * z v.2))) := by
  let e := edgeSplit (L := L) a b hab
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,Pi.star_apply,
    edgeLift,Matrix.submatrix_apply]
  conv_lhs =>
    arg 2
    ext x
    rw [← e.symm.sum_comp]
  rw [← e.symm.sum_comp]
  dsimp only [e]
  simp only [Equiv.apply_symm_apply,Fintype.sum_prod_type]
  simp_rw [tensorPhase_edgeSplit]
  simp only [edgeLift,Matrix.submatrix_apply,Equiv.apply_symm_apply,
    Matrix.kronecker_apply,Matrix.one_apply,mul_ite,ite_mul,mul_one,mul_zero,zero_mul,
    Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp only [Finset.mul_sum,Finset.sum_mul,star_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro c hc
  ring

private lemma tensor_norm_sum (z : L → ℂ) :
    (∑ c : I → L, star (tensorPhase z c) * tensorPhase z c) =
      (∑ i : L, star (z i) * z i) ^ Fintype.card I := by
  simp only [tensorPhase,star_prod,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : I) i => star (z i) * z i)]
  simp


open private allCuts_iff from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseRootTranspose

private def adaptedCone (root leaf : I) (hne : root ≠ leaf) :
    ProperCone ℝ (HermitianMat (L × L) ℂ) where
  carrier := {ρ | ρ ∈ ordinaryCone root leaf hne ∧ ρ ∈ boseSubspace}
  zero_mem' := ⟨(ordinaryCone root leaf hne).zero_mem, (boseSubspace (L := L)).zero_mem⟩
  add_mem' := by
    intro ρ τ hρ hτ
    exact ⟨(ordinaryCone root leaf hne).add_mem hρ.1 hτ.1,
      (boseSubspace (L := L)).add_mem hρ.2 hτ.2⟩
  smul_mem' := fun c ρ hρ => ⟨(ordinaryCone root leaf hne).smul_mem hρ.1 c.property,
    (boseSubspace (L := L)).smul_mem c.val hρ.2⟩
  isClosed' := (ordinaryCone root leaf hne).isClosed.inter
    (boseSubspace (L := L)).closed_of_finiteDimensional

private lemma mem_adaptedCone (root leaf : I) (hne : root ≠ leaf)
    (ρ : HermitianMat (L × L) ℂ) :
    ρ ∈ adaptedCone root leaf hne ↔ ρ.mat ∈ adaptedDPS root leaf hne := by
  rw [adapted_eq_inter]
  change (ρ.mat ∈ ordinaryDPS root leaf hne ∧
    pairSymmetricProjector * ρ.mat * pairSymmetricProjector = ρ.mat) ↔
      ρ.mat ∈ ordinaryDPS root leaf hne ∧ ρ.mat.PosSemidef ∧
        pairSymmetricProjector * ρ.mat * pairSymmetricProjector = ρ.mat
  exact ⟨fun h => ⟨h.1,ordinary_input_pos root leaf hne ρ.mat h.1,h.2⟩,
    fun h => ⟨h.1,h.2.2⟩⟩

private def marginalAdjoint (root leaf : I) (hne : root ≠ leaf)
    (A : HermitianMat (L × L) ℂ) : HermitianMat (I → L) ℂ :=
  ⟨edgeLift root leaf hne A.mat,by
    change ((A.mat ⊗ₖ 1).submatrix (edgeSplit root leaf hne) (edgeSplit root leaf hne))ᴴ = _
    rw [Matrix.conjTranspose_submatrix,Matrix.conjTranspose_kronecker,A.H.eq,
      Matrix.conjTranspose_one]
    rfl⟩

private lemma dual_marginalAdjoint (root leaf : I) (hne : root ≠ leaf)
    (A : HermitianMat (L × L) ℂ)
    (hA : A ∈ ProperCone.dual (innerₗ (HermitianMat (L × L) ℂ))
      (adaptedCone (L := L) root leaf hne : Set (HermitianMat (L × L) ℂ))) :
    marginalAdjoint root leaf hne A ∈
      ProperCone.dual (innerₗ (HermitianMat (I → L) ℂ))
        (bosePPT : Set (HermitianMat (I → L) ℂ)) := by
  intro E hE
  have hp := ((allCuts_iff E.mat).mp hE.2).1
  let ρ : HermitianMat (L × L) ℂ :=
    ⟨edgeMarginal root leaf hne E.mat,
      (partialTraceRight_posSemidef (hp.submatrix (edgeSplit root leaf hne).symm)).1⟩
  have hρ : ρ ∈ adaptedCone root leaf hne :=
    (mem_adaptedCone root leaf hne ρ).mpr ⟨E.mat,hE.1,rfl,hE.2⟩
  have hh := hA hρ
  change 0 ≤ inner ℝ E (marginalAdjoint root leaf hne A)
  rw [HermitianMat.inner_eq_re_trace]
  change 0 ≤ (E.mat * edgeLift root leaf hne A.mat).trace.re
  rw [edge_trace_duality]
  exact hh

open private antiPair antiPair_projection from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

private lemma pairProjector_hermitian :
    (pairSymmetricProjector (L := L)).IsHermitian := by
  exact Matrix.isHermitian_one.sub antiPair_projection.1

private def pairCompression (A : HermitianMat (L × L) ℂ) :
    HermitianMat (L × L) ℂ :=
  ⟨pairSymmetricProjector * A.mat * pairSymmetricProjector,by
    change (pairSymmetricProjector * A.mat * pairSymmetricProjector).IsHermitian
    simpa only [pairProjector_hermitian.eq] using
      Matrix.isHermitian_conjTranspose_mul_mul pairSymmetricProjector A.H⟩

private lemma pairCompression_pairing (A B : HermitianMat (L × L) ℂ)
    (hB : B ∈ boseSubspace) : inner ℝ B (pairCompression A) = inner ℝ B A := by
  let Q : Matrix (L × L) (L × L) ℂ := pairSymmetricProjector
  change Q * B.mat * Q = B.mat at hB
  rw [HermitianMat.inner_eq_re_trace,HermitianMat.inner_eq_re_trace]
  change (B.mat * (Q * A.mat * Q)).trace.re = (B.mat * A.mat).trace.re
  have he : (B.mat * (Q * A.mat * Q)).trace = ((Q * B.mat * Q) * A.mat).trace := by
    rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  rw [he,hB]

private lemma pairCompression_dual (root leaf : I) (hne : root ≠ leaf)
    (A : HermitianMat (L × L) ℂ)
    (hA : A ∈ ProperCone.dual (innerₗ (HermitianMat (L × L) ℂ))
      (adaptedCone (L := L) root leaf hne : Set (HermitianMat (L × L) ℂ))) :
    pairCompression A ∈ ProperCone.dual (innerₗ (HermitianMat (L × L) ℂ))
      (adaptedCone (L := L) root leaf hne : Set (HermitianMat (L × L) ℂ)) := by
  intro B hB
  change 0 ≤ inner ℝ B (pairCompression A)
  rw [pairCompression_pairing A B hB.2]
  exact hA hB

private lemma pairCompression_swap (A : HermitianMat (L × L) ℂ)
    (v w : L × L) : (pairCompression A).mat v.swap w = (pairCompression A).mat v w := by
  let F := Equiv.Perm.permMatrix ℂ (Equiv.prodComm L L)
  have hFF : F * F = 1 := by
    have hs : (Equiv.prodComm L L : Equiv.Perm (L × L)) * Equiv.prodComm L L = 1 := by
      ext x <;> rfl
    change Equiv.Perm.permMatrix ℂ (Equiv.prodComm L L) * _ = _
    rw [← Matrix.permMatrix_mul,hs,Matrix.permMatrix_one]
  have hf : F * pairSymmetricProjector = pairSymmetricProjector := by
    simp only [pairSymmetricProjector,antiPair,Matrix.mul_sub,Matrix.mul_smul,
      Matrix.mul_one,show Equiv.Perm.permMatrix ℂ (Equiv.prodComm L L) = F from rfl,hFF]
    module
  have he : F * (pairCompression A).mat = (pairCompression A).mat := by
    change F * (pairSymmetricProjector * A.mat * pairSymmetricProjector) = _
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hf]
    rfl
  have hv := congrArg (fun B : Matrix (L × L) (L × L) ℂ => B v w) he
  change (F *ᵥ (fun x => (pairCompression A).mat x w)) v = _ at hv
  rw [Matrix.permMatrix_mulVec] at hv
  exact hv

end Tensor

section Diagonal

variable {I : Type*} [Fintype I] [DecidableEq I]

open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl
open private pairAction pairTwirl pairTwirl_hermitian trace_pairAction
  pairTwirl_apply pairTwirl_reconstruction ldui_bose ldui_entry ldui_hermitian
  dualCoordinates dualCoordinates_symm ldui_trace_pairing ldui_coherent from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseLDUI
open private allCuts_iff from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseRootTranspose

private def actedPair (u : Fin n → ℂ) (A : HermitianMat (Fin n × Fin n) ℂ) :
    HermitianMat (Fin n × Fin n) ℂ :=
  ⟨pairAction u A.mat,Matrix.isHermitian_mul_mul_conjTranspose _ A.H⟩

private lemma adapted_diagonal (root leaf : I) (hne : root ≠ leaf)
    (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (ρ : HermitianMat (Fin n × Fin n) ℂ)
    (hρ : ρ ∈ adaptedCone root leaf hne) :
    actedPair u ρ ∈ adaptedCone root leaf hne := by
  obtain ⟨E,hE⟩ := (mem_adaptedCone root leaf hne ρ).mp hρ
  have hp := ((allCuts_iff E).mp hE.2.2).1
  apply (mem_adaptedCone root leaf hne _).mpr
  refine ⟨diagonalAction u E,diagonalAction_bose u E hp hE.1,?_,?_⟩
  · change edgeMarginal root leaf hne (diagonalAction u E) = pairAction u ρ.mat
    rw [edgeMarginal_diagonalAction u hu,hE.2.1]
    rfl
  · intro S
    rw [partialTranspose_diagonalAction]
    exact (hE.2.2 S).mul_mul_conjTranspose_same _

private lemma dual_diagonal (root leaf : I) (hne : root ≠ leaf)
    (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (A : HermitianMat (Fin n × Fin n) ℂ)
    (hA : A ∈ ProperCone.dual (innerₗ (HermitianMat (Fin n × Fin n) ℂ))
      (adaptedCone (L := Fin n) root leaf hne : Set (HermitianMat (Fin n × Fin n) ℂ))) :
    actedPair u A ∈ ProperCone.dual (innerₗ (HermitianMat (Fin n × Fin n) ℂ))
      (adaptedCone (L := Fin n) root leaf hne : Set (HermitianMat (Fin n × Fin n) ℂ)) := by
  intro ρ hρ
  have h := hA (adapted_diagonal root leaf hne (star u)
    (fun i => by simpa only [Pi.star_apply,norm_star] using hu i) ρ hρ)
  change 0 ≤ inner ℝ ρ (actedPair u A)
  rw [HermitianMat.inner_eq_re_trace,Matrix.trace_mul_comm]
  change 0 ≤ (pairAction u A.mat * ρ.mat).trace.re
  rw [trace_pairAction]
  change 0 ≤ inner ℝ (actedPair (star u) ρ) A at h
  rw [HermitianMat.inner_eq_re_trace] at h
  change 0 ≤ (pairAction (star u) ρ.mat * A.mat).trace.re at h
  rw [Matrix.trace_mul_comm] at h
  exact h

open private occupationPhase_norm from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl

private lemma dual_pairTwirl (root leaf : I) (hne : root ≠ leaf)
    (A : HermitianMat (Fin n × Fin n) ℂ)
    (hA : A ∈ ProperCone.dual (innerₗ (HermitianMat (Fin n × Fin n) ℂ))
      (adaptedCone (L := Fin n) root leaf hne : Set (HermitianMat (Fin n × Fin n) ℂ))) :
    (⟨pairTwirl A.mat,pairTwirl_hermitian A.mat A.H⟩ : HermitianMat (Fin n × Fin n) ℂ) ∈
      ProperCone.dual (innerₗ (HermitianMat (Fin n × Fin n) ℂ))
        (adaptedCone (L := Fin n) root leaf hne : Set (HermitianMat (Fin n × Fin n) ℂ)) := by
  intro ρ hρ
  change 0 ≤ inner ℝ ρ ⟨pairTwirl A.mat,pairTwirl_hermitian A.mat A.H⟩
  rw [HermitianMat.inner_eq_re_trace]
  change 0 ≤ (ρ.mat * pairTwirl A.mat).trace.re
  simp only [pairTwirl,Matrix.mul_smul,Matrix.mul_sum,Matrix.trace_smul,Matrix.trace_sum,
    Complex.smul_re,Complex.re_sum]
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro t ht
  have h := dual_diagonal root leaf hne (occupationPhase (r := 2) t)
    (occupationPhase_norm t) A hA hρ
  change 0 ≤ inner ℝ ρ (actedPair (occupationPhase t) A) at h
  rw [HermitianMat.inner_eq_re_trace] at h
  exact h

private lemma trace_twirl_ldui (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsSymm)
    (A : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    (ldui P * pairTwirl A).trace = (ldui P * A).trace := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  rw [ldui_entry P hP,pairTwirl_apply]
  split_ifs <;> simp_all <;> aesop

private lemma dual_normal_form (root leaf : I) (hne : root ≠ leaf)
    (A : HermitianMat (Fin n × Fin n) ℂ)
    (hA : A ∈ ProperCone.dual (innerₗ (HermitianMat (Fin n × Fin n) ℂ))
      (adaptedCone (L := Fin n) root leaf hne : Set (HermitianMat (Fin n × Fin n) ℂ))) :
    ∃ R : Matrix (Fin n) (Fin n) ℝ, ∃ hR : R.IsSymm,
      (⟨ldui R,ldui_hermitian R⟩ : HermitianMat (Fin n × Fin n) ℂ) ∈
        ProperCone.dual (innerₗ (HermitianMat (Fin n × Fin n) ℂ))
          (adaptedCone (L := Fin n) root leaf hne : Set (HermitianMat (Fin n × Fin n) ℂ)) ∧
      ∀ P : Matrix (Fin n) (Fin n) ℝ, P.IsSymm →
        (ldui P * ldui R).trace = (ldui P * A.mat).trace := by
  let B := pairCompression A
  obtain ⟨R,hR,he⟩ := pairTwirl_reconstruction B.mat B.H (pairCompression_swap A)
  refine ⟨R,hR,?_,?_⟩
  · have h := dual_pairTwirl root leaf hne B (pairCompression_dual root leaf hne A hA)
    simpa only [he] using h
  · intro P hP
    rw [← he,trace_twirl_ldui P hP]
    change (ldui P * (pairSymmetricProjector * A.mat * pairSymmetricProjector)).trace = _
    let Q : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := pairSymmetricProjector
    change (ldui P * (Q * A.mat * Q)).trace = (ldui P * A.mat).trace
    have heq : (ldui P * (Q * A.mat * Q)).trace = ((Q * ldui P * Q) * A.mat).trace := by
      rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle]
      simp only [Matrix.mul_assoc]
    rw [heq,show Q * ldui P * Q = ldui P from ldui_bose P]

end Diagonal

section Polynomial

open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol
open private edgeLift edge_trace_duality from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
open private dualCoordinates dualCoordinates_symm ldui_coherent ldui_hermitian ldui_bose
  ldui_trace_pairing from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseLDUI
open private allCuts_iff from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseRootTranspose

variable {r : ℕ}

private lemma complement_card (root leaf : Fin r) (hne : root ≠ leaf) :
    Fintype.card {k : Fin r // k ≠ root ∧ k ≠ leaf} = r - 2 := by
  rw [Fintype.card_of_subtype ({root,leaf}ᶜ : Finset (Fin r)) (by intro i; simp)]
  simp [Finset.card_compl,hne]
  omega

private def lduiHermitian (P : Matrix (Fin n) (Fin n) ℝ) :
    HermitianMat (Fin n × Fin n) ℂ := ⟨ldui P,ldui_hermitian P⟩

private lemma lift_ldui_coherent (root leaf : Fin r) (hne : root ≠ leaf)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) (z : Fin n → ℂ) :
    star (tensorPhase z) ⬝ᵥ
      (edgeLift root leaf hne (ldui R) *ᵥ tensorPhase z) =
        eval₂ Complex.ofRealHom (fun i => star (z i) * z i)
          (liftedForm (r-2) (dualCoordinates R)) := by
  rw [edgeLift_coherent,tensor_norm_sum,complement_card root leaf hne,ldui_coherent R hR]
  simp [liftedForm]

private lemma lift_ldui_realSymbol (root leaf : Fin r) (hne : root ≠ leaf)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) :
    realSymbol (edgeLift root leaf hne (ldui R)) =
      polynomial (r-2) (dualCoordinates R) := by
  apply MvPolynomial.funext
  intro u
  rw [eval_realSymbol,lift_ldui_coherent root leaf hne R hR]
  change (eval₂ Complex.ofRealHom (fun i => star (u i : ℂ) * (u i : ℂ))
    (liftedForm (r-2) (dualCoordinates R))).re =
      eval u (expand 2 (liftedForm (r-2) (dualCoordinates R)))
  simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul]
  change (eval₂ Complex.ofRealHom (Complex.ofRealHom ∘ (fun i => u i * u i))
    (liftedForm (r-2) (dualCoordinates R))).re = _
  rw [← MvPolynomial.eval₂_comp Complex.ofRealHom (fun i => u i * u i)]
  simp only [Complex.ofRealHom_eq_coe,Complex.ofReal_re,MvPolynomial.eval_expand,pow_two]
  rfl

private lemma dual_of_marginalAdjoint (root leaf : Fin r) (hne : root ≠ leaf)
    (A : HermitianMat (Fin n × Fin n) ℂ)
    (hA : marginalAdjoint root leaf hne A ∈
      ProperCone.dual (innerₗ (HermitianMat (Fin r → Fin n) ℂ))
        (bosePPT : Set (HermitianMat (Fin r → Fin n) ℂ))) :
    A ∈ ProperCone.dual (innerₗ (HermitianMat (Fin n × Fin n) ℂ))
      (adaptedCone (L := Fin n) root leaf hne : Set (HermitianMat (Fin n × Fin n) ℂ)) := by
  intro ρ hρ
  obtain ⟨E,hE⟩ := (mem_adaptedCone root leaf hne ρ).mp hρ
  have hp := ((allCuts_iff E).mp hE.2.2).1
  let F : HermitianMat (Fin r → Fin n) ℂ := ⟨E,hp.1⟩
  have hF : F ∈ bosePPT := ⟨hE.1,hE.2.2⟩
  have hh := hA hF
  change 0 ≤ inner ℝ F (marginalAdjoint root leaf hne A) at hh
  rw [HermitianMat.inner_eq_re_trace] at hh
  change 0 ≤ (E * edgeLift root leaf hne A.mat).trace.re at hh
  rw [edge_trace_duality,hE.2.1] at hh
  exact hh

private lemma sos_of_dual_ldui (root leaf : Fin r) (hne : root ≠ leaf)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm)
    (hD : (lduiHermitian R : HermitianMat (Fin n × Fin n) ℂ) ∈
      ProperCone.dual (innerₗ (HermitianMat (Fin n × Fin n) ℂ))
        (adaptedCone (L := Fin n) root leaf hne : Set (HermitianMat (Fin n × Fin n) ℂ))) :
    dualCoordinates R ∈ K (r-2) := by
  have hs := dual_bosePPT_real_sos
    (marginalAdjoint root leaf hne (lduiHermitian R))
    (dual_marginalAdjoint root leaf hne _ hD)
  change IsSumSq (realSymbol (edgeLift root leaf hne (ldui R))) at hs
  rw [lift_ldui_realSymbol root leaf hne R hR] at hs
  exact ⟨dualCoordinates_symm R hR,hs⟩

private lemma dual_ldui_of_sos (root leaf : Fin r) (hne : root ≠ leaf)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm)
    (hM : dualCoordinates R ∈ K (r-2)) :
    (lduiHermitian R : HermitianMat (Fin n × Fin n) ℂ) ∈
      ProperCone.dual (innerₗ (HermitianMat (Fin n × Fin n) ℂ))
        (adaptedCone (L := Fin n) root leaf hne : Set (HermitianMat (Fin n × Fin n) ℂ)) := by
  apply dual_of_marginalAdjoint root leaf hne
  apply D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseSOSDuality.even_sos_nonnegative
    (marginalAdjoint root leaf hne (lduiHermitian R))
    (liftedForm (r-2) (dualCoordinates R))
    (by
      have hr : 2 ≤ r := by
        simpa [hne] using (Finset.card_le_univ ({root,leaf} : Finset (Fin r)))
      convert liftedForm_homogeneous (r-2) (dualCoordinates R) using 1 <;> omega)
    (lift_ldui_coherent root leaf hne R hR)
  exact hM.2

/-- Gulati--Nechita--Park's complete-graph characterization, proved for the
actual tensor marginal and the full native SOS hierarchy. No prior GNP
theorem, custom axiom, normalization or strict positivity is assumed. -/
theorem gnp_characterization (root leaf : Fin r) (hne : root ≠ leaf)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsSymm) :
    ldui P ∈ adaptedDPS root leaf hne ↔ parriloPolar (r-2) P := by
  constructor
  · intro hρ M hM
    let R : Matrix (Fin n) (Fin n) ℝ :=
      fun i j => if i = j then M i i else M i j / 2
    have hR : R.IsSymm := by
      ext i j
      by_cases hij : i = j
      · subst j; rfl
      · simp [R,hij,Ne.symm hij,hM.1.apply i j]
    have he : dualCoordinates R = M := by
      ext i j
      by_cases hij : i = j
      · subst j; simp [dualCoordinates,R]
      · simp [dualCoordinates,R,hij]
        ring
    have hD := dual_ldui_of_sos root leaf hne R hR (by simpa only [he] using hM)
    have hh := hD ((mem_adaptedCone root leaf hne (lduiHermitian P)).mpr hρ)
    change 0 ≤ inner ℝ (lduiHermitian P : HermitianMat (Fin n × Fin n) ℂ)
      (lduiHermitian R) at hh
    rw [HermitianMat.inner_eq_re_trace] at hh
    change 0 ≤ (ldui P * ldui R).trace.re at hh
    rw [ldui_trace_pairing P R hP hR,he,
      Complex.ofReal_re] at hh
    exact hh
  · intro hPpolar
    apply (mem_adaptedCone root leaf hne (lduiHermitian P)).mp
    have hB : (lduiHermitian P : HermitianMat (Fin n × Fin n) ℂ) ∈
        ProperCone.dual (innerₗ (HermitianMat (Fin n × Fin n) ℂ)).flip
          (ProperCone.dual (innerₗ (HermitianMat (Fin n × Fin n) ℂ))
            (adaptedCone (L := Fin n) root leaf hne : Set (HermitianMat (Fin n × Fin n) ℂ)) :
              Set (HermitianMat (Fin n × Fin n) ℂ)) := by
      intro A hA
      obtain ⟨R,hR,hD,he⟩ := dual_normal_form root leaf hne A hA
      have hh := hPpolar (dualCoordinates R) (sos_of_dual_ldui root leaf hne R hR hD)
      rw [flip_innerₗ]
      change 0 ≤ inner ℝ A (lduiHermitian P : HermitianMat (Fin n × Fin n) ℂ)
      rw [HermitianMat.inner_eq_re_trace,Matrix.trace_mul_comm]
      change 0 ≤ (ldui P * A.mat).trace.re
      rw [← he P hP,
        ldui_trace_pairing P R hP hR,Complex.ofReal_re]
      exact hh
    rwa [ProperCone.dual_flip_dual] at hB

#print axioms gnp_characterization

/-- Attainable objective values of the actual unnormalized LDUI DPS program. -/
def objectiveValues (root leaf : Fin r) (hne : root ≠ leaf)
    (C : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  {v | ∃ P : Matrix (Fin n) (Fin n) ℝ, P.IsSymm ∧
    ldui P ∈ ordinaryDPS root leaf hne ∧ v = ∑ i, ∑ j, C i j * P i j}

/-- Every objective in the corresponding full Parrilo level has attained
minimum zero in the unnormalized ordinary DPS program. The n=5,r=3 case
is Britz--Laurent's t=2 program; no normalized conclusion is asserted. -/
theorem objective_minimum (root leaf : Fin r) (hne : root ≠ leaf)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C ∈ K (r-2)) :
    IsLeast (objectiveValues root leaf hne C) 0 := by
  constructor
  · refine ⟨0,by simp,?_,by simp⟩
    have he : ldui (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
      simp [ldui,dickeOperator]
    rw [he]
    exact (ordinaryCone (L := Fin n) root leaf hne).zero_mem
  · rintro v ⟨P,hP,⟨E,hE⟩,rfl⟩
    have hA : ldui P ∈ adaptedDPS root leaf hne :=
      ⟨E,(adapted_iff_ordinary root leaf hne _ (ldui_bose P) E).mpr hE⟩
    have hp := ((gnp_characterization root leaf hne P hP).mp hA) C hC
    simpa only [mul_comm] using hp

#print axioms objective_minimum

end Polynomial
end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseHierarchy
