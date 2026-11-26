/- GID: D5/S3/Quantum/Divergence/CompleteHockeyStickChoiSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/CompleteHockeyStickChoiSupport
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: A Choi support criterion for unit complete hockey-stick contraction. -/

import D5.S3.Quantum.Divergence.CompleteHockeyStickBasisSupport
import D5.S3.Quantum.Divergence.UmegakiKernelContraction
import D5.S3.Quantum.Foundation.FinitePreparationChannel
import D5.S3.Quantum.ProcessReconstruction.LiuWildChoiObstruction
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RingTheory.Artinian.Module

/-! A finite family of reference-unitary translates turns the Choi support
condition into a basis-output support condition. The Bell preparations share
a reference marginal, so data processing transfers the simplex ratios to the
original channel at each fixed parameter greater than one. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport

open _root_.Matrix
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FinitePreparationChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport
  (amp_kronecker partialTraceRight_mul_embed partialTraceRight_embed_mul)
open UnitaryReconstruction.LiuWildChoiObstruction
  (bell bell_norm diagonalVector normalizedChoi pairMatrix)

open private E_contract from D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation
open private posTrace_reindex from
  D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open private bell_outer_entry from D5.S3.Quantum.ProcessReconstruction.LiuWildChoiObstruction

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

private def actingOnReference (M : Matrix A A ℂ) :
    ((A × B) → ℂ) →ₗ[ℂ] ((A × B) → ℂ) :=
  (M ⊗ₖ (1 : Matrix B B ℂ)).mulVecLin

private def referenceSlice (i : A) (v : B → ℂ) : A × B → ℂ :=
  fun p => if p.1 = i then v p.2 else 0

private theorem matrixUnit_action (i j : A) (x : A × B → ℂ) :
    actingOnReference (Matrix.single i j 1) x = referenceSlice i (fun b => x (j, b)) := by
  ext ⟨a, b⟩
  by_cases h : i = a <;>
    simp [actingOnReference, referenceSlice, Matrix.mulVec, dotProduct, Matrix.single,
      Matrix.one_apply, Fintype.sum_prod_type, ite_mul, mul_ite, eq_comm, h]

private theorem unitary_test_iff_full_matrix_test (S : Submodule ℂ (A × B → ℂ))
    (x : A × B → ℂ) :
    (∀ U : unitary (Matrix A A ℂ), actingOnReference (U : Matrix A A ℂ) x ∈ S) ↔
      ∀ M : Matrix A A ℂ, actingOnReference M x ∈ S := by
  refine ⟨fun h M => ?_, fun h U => h U⟩
  let f : Matrix A A ℂ →ₗ[ℂ] (A × B → ℂ) :=
    { toFun := fun T => actingOnReference T x
      map_add' := fun T P => by
        simp [actingOnReference, Matrix.add_kronecker]
      map_smul' := fun c T => by
        simp [actingOnReference, Matrix.smul_kronecker] }
  have hspan : Submodule.span ℂ (unitary (Matrix A A ℂ) : Set (Matrix A A ℂ)) ≤ S.comap f :=
    Submodule.span_le.mpr fun U hU => h ⟨U, hU⟩
  rw [CStarAlgebra.span_unitary] at hspan
  exact hspan (Submodule.mem_top : M ∈ (⊤ : Submodule ℂ (Matrix A A ℂ)))

private theorem no_common_unitary_direction (S : Submodule ℂ (A × B → ℂ))
    (hS : ∀ v : B → ℂ, (∀ i, referenceSlice i v ∈ S) → v = 0) :
    (⨅ U : unitary (Matrix A A ℂ), S.comap (actingOnReference (U : Matrix A A ℂ))) = ⊥ := by
  apply bot_unique
  intro x hx
  have hact := (unitary_test_iff_full_matrix_test S x).mp ((Submodule.mem_iInf _).mp hx)
  have hz (j : A) : (fun b => x (j, b)) = 0 := by
    apply hS
    intro i
    simpa only [matrixUnit_action] using hact (Matrix.single i j 1)
  rw [Submodule.mem_bot]
  ext ⟨j, b⟩
  exact congrFun (hz j) b

private theorem finite_test_of_artinian
    {ι V : Type*} [AddCommGroup V] [Module ℂ V] [IsArtinian ℂ V]
    (S : ι → Submodule ℂ V) :
    ∃ t : Finset ι, t.inf S = ⨅ i, S i := by
  classical
  obtain ⟨m, ⟨t, rfl⟩, hmin⟩ :=
    IsArtinian.set_has_minimal (Set.range (fun t : Finset ι => t.inf S))
      ⟨(∅ : Finset ι).inf S, ⟨∅, rfl⟩⟩
  refine ⟨t, le_antisymm (le_iInf fun i => ?_) (Finset.le_inf fun i _ => iInf_le S i)⟩
  have hle : (insert i t).inf S ≤ t.inf S :=
    Finset.le_inf fun j hj => Finset.inf_le (Finset.mem_insert_of_mem hj)
  have heq : (insert i t).inf S = t.inf S :=
    hle.eq_of_not_lt (hmin _ ⟨insert i t, rfl⟩)
  rw [← heq]
  exact Finset.inf_le (Finset.mem_insert_self i t)

private theorem conjugate_range (H : Matrix (A × B) (A × B) ℂ)
    (U : unitary (Matrix A A ℂ)) :
    let K := (U : Matrix A A ℂ) ⊗ₖ (1 : Matrix B B ℂ)
    (Kᴴ * H * K).mulVecLin.range =
      H.mulVecLin.range.comap (actingOnReference (U : Matrix A A ℂ)) := by
  intro K
  have hU : K ∈ unitary (Matrix (A × B) (A × B) ℂ) :=
    Matrix.kronecker_mem_unitary U.property (Submonoid.one_mem _)
  have hleft : Kᴴ * K = 1 := hU.1
  have hright : K * Kᴴ = 1 := hU.2
  ext x
  change (∃ y, (Kᴴ * H * K) *ᵥ y = x) ↔ ∃ y, H *ᵥ y = K *ᵥ x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨K *ᵥ y, ?_⟩
    simp only [mulVec_mulVec, ← Matrix.mul_assoc K, hright, Matrix.one_mul]
  · rintro ⟨y, hy⟩
    refine ⟨Kᴴ *ᵥ y, ?_⟩
    rw [mulVec_mulVec, Matrix.mul_assoc (Kᴴ * H), hright, Matrix.mul_one,
      ← mulVec_mulVec, hy, mulVec_mulVec, hleft, one_mulVec]

/-- Finite unitary translates of a joint matrix have trivial common range
exactly when its range contains no full reference factor over a nonzero
output vector. -/
private theorem finite_unitary_support_test [Nonempty A]
    (H : Matrix (A × B) (A × B) ℂ) :
    (∃ t : Finset (unitary (Matrix A A ℂ)),
      t.inf (fun U =>
        let K := (U : Matrix A A ℂ) ⊗ₖ (1 : Matrix B B ℂ)
        (Kᴴ * H * K).mulVecLin.range) = ⊥) ↔
      ∀ v : B → ℂ, (∀ i : A, (fun p : A × B => if p.1 = i then v p.2 else 0) ∈
        H.mulVecLin.range) → v = 0 := by
  let S := H.mulVecLin.range
  let C := fun U : unitary (Matrix A A ℂ) => S.comap (actingOnReference (U : Matrix A A ℂ))
  change (∃ t : Finset (unitary (Matrix A A ℂ)), t.inf _ = ⊥) ↔
    ∀ v : B → ℂ, (∀ i : A, referenceSlice i v ∈ S) → v = 0
  have hconj (U : unitary (Matrix A A ℂ)) :
      let K := (U : Matrix A A ℂ) ⊗ₖ (1 : Matrix B B ℂ)
      (Kᴴ * H * K).mulVecLin.range = C U := conjugate_range H U
  simp_rw [hconj]
  constructor
  · rintro ⟨t, ht⟩ v hv
    let j : A := Classical.choice ‹Nonempty A›
    have hs : referenceSlice j v ∈ t.inf C := by
      have hle (U : unitary (Matrix A A ℂ)) : referenceSlice j v ∈ C U := by
        change actingOnReference (U : Matrix A A ℂ) (referenceSlice j v) ∈ S
        have heq : actingOnReference (U : Matrix A A ℂ) (referenceSlice j v) =
            ∑ i, (U : Matrix A A ℂ) i j • referenceSlice i v := by
          ext ⟨a, b⟩
          simp [actingOnReference, referenceSlice, Matrix.mulVec, dotProduct, Matrix.one_apply,
            Fintype.sum_prod_type, Finset.sum_apply, ite_mul, mul_ite]
        rw [heq]
        exact S.sum_mem fun i _ => S.smul_mem _ (hv i)
      rw [Finset.inf_eq_iInf]
      exact (Submodule.mem_iInf _).mpr fun U => (Submodule.mem_iInf _).mpr fun _ => hle U
    rw [ht, Submodule.mem_bot] at hs
    ext b
    simpa [referenceSlice] using congrFun hs (j, b)
  · intro h
    obtain ⟨t, ht⟩ := finite_test_of_artinian C
    exact ⟨t, ht.trans (no_common_unitary_direction S h)⟩

private def ampLinear {R : Type*} [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) :
    Matrix (R × A) (R × A) ℂ →ₗ[ℂ] Matrix (R × B) (R × B) ℂ :=
  CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
    ((referenceLinear N).comp CStarMatrix.ofMatrixₗ.toLinearMap)

private theorem mul_reference_kronecker {R C : Type*} [Fintype R]
    [Fintype C] [DecidableEq C] (U V : Matrix R R ℂ) (Y : Matrix C C ℂ) :
    (Uᴴ ⊗ₖ (1 : Matrix C C ℂ)) * (V ⊗ₖ Y) * (U ⊗ₖ (1 : Matrix C C ℂ)) =
      (Uᴴ * V * U) ⊗ₖ Y := by
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

private theorem amp_reference_conjugation {R : Type*} [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) (U : Matrix R R ℂ) (X : Matrix (R × A) (R × A) ℂ) :
    amp N ((Uᴴ ⊗ₖ (1 : Matrix A A ℂ)) * X * (U ⊗ₖ (1 : Matrix A A ℂ))) =
      (Uᴴ ⊗ₖ (1 : Matrix B B ℂ)) * amp N X * (U ⊗ₖ (1 : Matrix B B ℂ)) := by
  let term (i j : R) : Matrix (R × A) (R × A) ℂ :=
    Matrix.single i j 1 ⊗ₖ (fun a b => X (i, a) (j, b))
  have hX : X = ∑ i : R, ∑ j : R, term i j := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp only [Matrix.sum_apply]
    change X (i, a) (j, b) = ∑ x : R, ∑ y : R, (Matrix.single x y (1 : ℂ)) i j * X (x, a) (y, b)
    simp [Matrix.single, ite_mul, ite_and]
  let L := ampLinear (R := R) N
  let V := U ⊗ₖ (1 : Matrix A A ℂ)
  let V' := Uᴴ ⊗ₖ (1 : Matrix A A ℂ)
  let W := U ⊗ₖ (1 : Matrix B B ℂ)
  let W' := Uᴴ ⊗ₖ (1 : Matrix B B ℂ)
  have hterm (i j : R) : L (V' * term i j * V) = W' * L (term i j) * W := by
    let Z : Matrix A A ℂ := fun a b => X (i, a) (j, b)
    let e : Matrix R R ℂ := Matrix.single i j 1
    change amp N ((Uᴴ ⊗ₖ (1 : Matrix A A ℂ)) * (e ⊗ₖ Z) *
      (U ⊗ₖ (1 : Matrix A A ℂ))) =
        (Uᴴ ⊗ₖ (1 : Matrix B B ℂ)) * amp N (e ⊗ₖ Z) * (U ⊗ₖ (1 : Matrix B B ℂ))
    calc
      _ = amp N ((Uᴴ * e * U) ⊗ₖ Z) := congrArg (amp N) (mul_reference_kronecker U e Z)
      _ = (Uᴴ * e * U) ⊗ₖ act N Z := amp_kronecker N _ Z
      _ = (Uᴴ ⊗ₖ (1 : Matrix B B ℂ)) * (e ⊗ₖ act N Z) * (U ⊗ₖ (1 : Matrix B B ℂ)) :=
        (mul_reference_kronecker U e (act N Z)).symm
      _ = _ := by rw [amp_kronecker N e Z]
  change L (V' * X * V) = W' * L X * W
  calc
    L (V' * X * V) = L (∑ i : R, ∑ j : R, V' * term i j * V) := by
      congr 1
      rw [hX]
      simp only [Matrix.mul_sum, Matrix.sum_mul]
    _ = ∑ i : R, ∑ j : R, L (V' * term i j * V) := by simp only [map_sum]
    _ = ∑ i : R, ∑ j : R, W' * L (term i j) * W := by simp only [hterm]
    _ = W' * L X * W := by
      rw [hX]
      simp only [map_sum, Matrix.mul_sum, Matrix.sum_mul]


private def bellState [Nonempty A] : DensityState (A × A) :=
  pureState (bell A) bell_norm

private theorem bell_marginal [Nonempty A] :
    ptr (pairMatrix (bellState (A := A))) = (Fintype.card A : ℂ)⁻¹ • (1 : Matrix A A ℂ) := by
  ext i j
  change (∑ a : A, vecMulVec (bell A) (star (bell A)) (i, a) (j, a)) =
    ((Fintype.card A : ℂ)⁻¹ • (1 : Matrix A A ℂ)) i j
  simp only [bell_outer_entry, diagonalVector, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    ← Finset.mul_sum]
  congr 1
  by_cases hij : i = j
  · subst j
    simp
  · have hz (a : A) : (if i = a then (1 : ℂ) else 0) * (if j = a then 1 else 0) = 0 := by
      by_cases h : i = a
      · subst a
        simp [Ne.symm hij]
      · simp [h]
    simp [hz, hij]

private def translatedBell [Nonempty A] (U : unitary (Matrix A A ℂ)) :
    DensityState (A × A) := by
  let K := (U : Matrix A A ℂ) ⊗ₖ (1 : Matrix A A ℂ)
  have hK : K ∈ unitary (Matrix (A × A) (A × A) ℂ) :=
    Matrix.kronecker_mem_unitary U.property (Submonoid.one_mem _)
  let H := pairMatrix (bellState (A := A))
  refine ⟨CStarMatrix.ofMatrix (Kᴴ * H * K), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((density_posSemidef (bellState (A := A))).conjTranspose_mul_mul_same K).nonneg
  · change (Kᴴ * H * K).trace = 1
    rw [Matrix.trace_mul_cycle, show K * Kᴴ = 1 from hK.2, Matrix.one_mul]
    exact (bellState (A := A)).2.2

private theorem translatedBell_marginal [Nonempty A] (U : unitary (Matrix A A ℂ)) :
    ptr (pairMatrix (translatedBell U)) = (Fintype.card A : ℂ)⁻¹ • (1 : Matrix A A ℂ) := by
  let V := (U : Matrix A A ℂ)
  let H := pairMatrix (bellState (A := A))
  change partialTraceRight ((V ⊗ₖ (1 : Matrix A A ℂ))ᴴ * H *
    (V ⊗ₖ (1 : Matrix A A ℂ))) = _
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, partialTraceRight_mul_embed,
    partialTraceRight_embed_mul, show partialTraceRight H = _ from bell_marginal,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, show Vᴴ * V = 1 from U.property.1]

universe u

private theorem translatedBell_output {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] (N : QuantumChannel a b)
    (U : unitary (Matrix a a ℂ)) :
    pairMatrix (referenceState N (translatedBell U)) =
      let K := (U : Matrix a a ℂ) ⊗ₖ (1 : Matrix b b ℂ)
      Kᴴ * pairMatrix (normalizedChoi N) * K := by
  let V := (U : Matrix a a ℂ)
  change amp N ((V ⊗ₖ (1 : Matrix a a ℂ))ᴴ * pairMatrix (bellState (A := a)) *
    (V ⊗ₖ (1 : Matrix a a ℂ))) = _
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, amp_reference_conjugation]
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  rfl

section Preparation

variable {X S R : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
  [Fintype R] [DecidableEq R]

set_option backward.isDefEq.respectTransparency false in
private theorem preparation_amp (P : QuantumChannel X S) (β : X → DensityState S)
    (hP : ∀ Z, act P Z = ∑ i, Z i i • pairMatrix (β i))
    (Z : Matrix (R × X) (R × X) ℂ) :
    amp P Z = ∑ i, Z.submatrix (fun r => (r, i)) (fun r => (r, i)) ⊗ₖ pairMatrix (β i) := by
  ext ⟨r, a⟩ ⟨s, b⟩
  rw [amp_entry, hP]
  simp [Matrix.sum_apply, smul_eq_mul]

private theorem preparation_marginal (P : QuantumChannel X (S × A))
    (β : X → DensityState (S × A))
    (hP : ∀ Z, act P Z = ∑ i, Z i i • pairMatrix (β i))
    (ω : Matrix S S ℂ) (hω : ∀ i, ptr (pairMatrix (β i)) = ω)
    (Z : Matrix (R × X) (R × X) ℂ) :
    ptr ((amp P Z).reindex (Equiv.prodAssoc R S A).symm (Equiv.prodAssoc R S A).symm) =
      ptr Z ⊗ₖ ω := by
  rw [preparation_amp P β hP]
  ext ⟨r, u⟩ ⟨s, v⟩
  change (∑ a : A, (∑ i, Z.submatrix (fun r => (r, i)) (fun r => (r, i)) ⊗ₖ
    pairMatrix (β i)) (r, u, a) (s, v, a)) = (∑ i : X, Z (r, i) (s, i)) * ω u v
  simp only [Matrix.sum_apply, Matrix.kronecker_apply, Matrix.submatrix_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp only [show ∀ i, (∑ a : A, pairMatrix (β i) (u, a) (v, a)) = ω u v from
    fun i => congrFun (congrFun (hω i) u) v, Finset.sum_mul]

set_option backward.isDefEq.respectTransparency false in
private theorem preparation_output (N : QuantumChannel A B)
    (P : QuantumChannel X (S × A)) (C : QuantumChannel X (S × B))
    (β : X → DensityState (S × A))
    (hP : ∀ Z, act P Z = ∑ i, Z i i • pairMatrix (β i))
    (hC : ∀ Z, act C Z = ∑ i, Z i i • pairMatrix (referenceState N (β i)))
    (Z : Matrix (R × X) (R × X) ℂ) :
    amp N ((amp P Z).reindex (Equiv.prodAssoc R S A).symm (Equiv.prodAssoc R S A).symm) =
      (amp C Z).reindex (Equiv.prodAssoc R S B).symm (Equiv.prodAssoc R S B).symm := by
  rw [preparation_amp P β hP, preparation_amp C (fun i => referenceState N (β i)) hC]
  let e := (Equiv.prodAssoc R S A).symm
  let f := (Equiv.prodAssoc R S B).symm
  let L := (reindexLinearEquiv ℂ ℂ e e).toLinearMap
  let M := (reindexLinearEquiv ℂ ℂ f f).toLinearMap
  change ampLinear N (L _) = M _
  rw [map_sum L, map_sum (ampLinear N), map_sum M]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext ⟨⟨r, u⟩, b⟩ ⟨⟨s, v⟩, d⟩
  change amp N _ ((r, u), b) ((s, v), d) = _
  rw [amp_entry]
  change (N.toCompletelyPositiveMap
    (Z (r, i) (s, i) • CStarMatrix.ofMatrix (fun a a' => pairMatrix (β i) (u, a) (v, a'))))
      b d = _
  rw [map_smul]
  rfl

end Preparation

private theorem amp_trace {R : Type*} [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) (Z : Matrix (R × A) (R × A) ℂ) :
    (amp N Z).trace = Z.trace :=
  referenceAction_trace N (CStarMatrix.ofMatrix Z)

private theorem E_reindex_eq {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) (γ : ℝ) {ρ σ : Matrix m m ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    E γ (ρ.reindex e e) (σ.reindex e e) = E γ ρ σ :=
  posTrace_reindex e (hρ.isHermitian.sub (hσ.isHermitian.smul (IsSelfAdjoint.all γ)))

section Coefficients

variable {A B X S : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]

private theorem preparation_witness (N : QuantumChannel A B)
    (P : QuantumChannel X (S × A)) (C : QuantumChannel X (S × B))
    (β : X → DensityState (S × A))
    (hP : ∀ Z, act P Z = ∑ i, Z i i • pairMatrix (β i))
    (hC : ∀ Z, act C Z = ∑ i, Z i i • pairMatrix (referenceState N (β i)))
    (ω : Matrix S S ℂ) (hω : ∀ i, ptr (pairMatrix (β i)) = ω) (γ : ℝ)
    {R : Type} [Fintype R] [DecidableEq R] {ρ σ : Matrix (R × X) (R × X) ℂ}
    (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1) (hσ : σ.PosSemidef) (htσ : σ.trace = 1)
    (hm : ptr ρ = ptr σ) :
    ∃ ρ' σ' : Matrix ((R × S) × A) ((R × S) × A) ℂ,
      ρ'.PosSemidef ∧ ρ'.trace = 1 ∧ σ'.PosSemidef ∧ σ'.trace = 1 ∧ ptr ρ' = ptr σ' ∧
      E γ ρ' σ' ≤ E γ ρ σ ∧ E γ (amp N ρ') (amp N σ') = E γ (amp C ρ) (amp C σ) := by
  let e := (Equiv.prodAssoc R S A).symm
  let f := (Equiv.prodAssoc R S B).symm
  let ρ' := (amp P ρ).reindex e e
  let σ' := (amp P σ).reindex e e
  have hρ' : ρ'.PosSemidef := (amp_psd P hρ).submatrix e.symm
  have hσ' : σ'.PosSemidef := (amp_psd P hσ).submatrix e.symm
  have htρ' : ρ'.trace = 1 := (trace_reindex e _).trans ((amp_trace P ρ).trans htρ)
  have htσ' : σ'.trace = 1 := (trace_reindex e _).trans ((amp_trace P σ).trans htσ)
  have hm' : ptr ρ' = ptr σ' := by
    change ptr ((amp P ρ).reindex e e) = ptr ((amp P σ).reindex e e)
    rw [preparation_marginal P β hP ω hω, preparation_marginal P β hP ω hω, hm]
  have hba : E γ ρ' σ' ≤ E γ ρ σ :=
    (E_reindex_eq e γ (amp_psd P hρ) (amp_psd P hσ)).le.trans (E_contract P γ hρ hσ)
  have he : E γ (amp N ρ') (amp N σ') = E γ (amp C ρ) (amp C σ) := by
    change E γ (amp N ((amp P ρ).reindex e e)) (amp N ((amp P σ).reindex e e)) = _
    rw [preparation_output N P C β hP hC, preparation_output N P C β hP hC]
    exact E_reindex_eq f γ (amp_psd C hρ) (amp_psd C hσ)
  exact ⟨ρ', σ', hρ', htρ', hσ', htσ', hm', hba, he⟩

set_option maxHeartbeats 600000 in
-- The two factor orders and inferred finite product instances require extra elaboration.
/-- If the normalized Choi support contains no full reference factor over a nonzero output
vector, a fixed finite reference admits equal-marginal witnesses at every sufficiently small
positive input budget. -/
theorem exists_budget_witness [Nonempty A] (N : QuantumChannel A B) (γ : ℝ) (hγ : 1 < γ)
    (hS : ∀ v : B → ℂ, (∀ i : A, (fun p : A × B => if p.1 = i then v p.2 else 0) ∈
      (pairMatrix (normalizedChoi N)).mulVecLin.range) → v = 0) :
    ∃ (R : Type) (fR : Fintype R) (dR : DecidableEq R),
      letI := fR
      letI := dR
      ∃ δ D : ℝ, 0 < δ ∧ 0 ≤ D ∧ ∀ a : ℝ, 0 < a → a ≤ δ →
        ∃ ρ σ : Matrix (R × A) (R × A) ℂ,
          ρ.PosSemidef ∧ ρ.trace = 1 ∧ σ.PosSemidef ∧ σ.trace = 1 ∧ ptr ρ = ptr σ ∧
          0 < E γ ρ σ ∧ E γ ρ σ ≤ a ∧
          a / (1 + D * a) ≤ E γ (amp N ρ) (amp N σ) := by
  classical
  let J := pairMatrix (normalizedChoi N)
  have hJ : J.trace = 1 := (normalizedChoi N).2.2
  have : Nonempty B := by
    rcases isEmpty_or_nonempty B with hB | hB
    · let := hB
      have hz : J.trace = 0 := by simp [Matrix.trace]
      exact False.elim (zero_ne_one (hz.symm.trans hJ))
    · exact hB
  obtain ⟨t, ht⟩ := (finite_unitary_support_test J).mpr hS
  have htne : t.Nonempty := by
    by_contra h
    have hz : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hz, Finset.inf_empty] at ht
    exact top_ne_bot ht
  obtain ⟨U₀, hU₀⟩ := htne
  let label : Option (↥t) → unitary (Matrix A A ℂ) := fun i =>
    i.elim (1 : unitary (Matrix A A ℂ)) Subtype.val
  let β := fun i => translatedBell (label i)
  obtain ⟨P, hP⟩ := finite_preparation_quantum_channel β
  obtain ⟨C, hC⟩ := finite_preparation_quantum_channel (fun i => referenceState N (β i))
  have hunit (i : Option (↥t)) :
      act C (Matrix.single i i 1) = pairMatrix (referenceState N (β i)) := by
    rw [show act C (Matrix.single i i 1) =
      ∑ j, (Matrix.single i i (1 : ℂ)) j j • pairMatrix (referenceState N (β j)) from hC _]
    simp [Matrix.single_apply, ite_smul]
  have hs : (⨅ i, (act C (Matrix.single i i 1)).mulVecLin.range) = ⊥ := by
    simp_rw [hunit]
    change (⨅ i, (pairMatrix (referenceState N (translatedBell (label i)))).mulVecLin.range) = ⊥
    simp_rw [translatedBell_output]
    apply bot_unique
    rw [← ht]
    exact Finset.le_inf fun U hU => iInf_le _ (some (⟨U, hU⟩ : ↥t))
  obtain ⟨δ, D, hδ, hD, hWitness⟩ :=
    CompleteHockeyStickBasisSupport.exists_budget_witness C ⟨U₀, hU₀⟩ γ hγ hs
  refine ⟨Option (↥t) × A, inferInstance, inferInstance, δ, D, hδ, hD, ?_⟩
  intro a ha hsmall
  obtain ⟨ρ, σ, hρ, htρ, hσ, htσ, hm, hinput, hpay⟩ := hWitness a ha hsmall
  obtain ⟨ρ', σ', hρ', htρ', hσ', htσ', hm', hba, he⟩ :=
    preparation_witness (S := A) N P C β hP hC
      ((Fintype.card A : ℂ)⁻¹ • (1 : Matrix A A ℂ))
      (fun i => translatedBell_marginal (label i)) γ hρ htρ hσ htσ hm
  have hpay' := hpay.trans he.symm.le
  have hden : 0 < 1 + D * a := by positivity
  have hpositive := ((div_pos ha hden).trans_le hpay').trans_le (E_contract N γ hρ' hσ')
  exact ⟨ρ', σ', hρ', htρ', hσ', htσ', hm', hpositive, hba.trans hinput.le, hpay'⟩

/-- At every fixed parameter strictly greater than one, a finite channel has complete
hockey-stick coefficient one if its normalized Choi support contains no full reference
factor over a nonzero output vector. -/
theorem result [Nonempty A] (N : QuantumChannel A B) (γ : ℝ) (hγ : 1 < γ)
    (hS : ∀ v : B → ℂ, (∀ i : A, (fun p : A × B => if p.1 = i then v p.2 else 0) ∈
      (pairMatrix (normalizedChoi N)).mulVecLin.range) → v = 0) :
    completeCoefficient N γ false = 1 := by
  obtain ⟨R, fR, dR, δ, D, hδ, hD, hWitness⟩ := exists_budget_witness N γ hγ hS
  letI := fR
  letI := dR
  have hBound : BddAbove (insert 0 (completeRatios N γ false)) :=
    ⟨1, fun _ h => ratio_le_one N γ false h⟩
  apply le_antisymm (csSup_le ⟨0, Set.mem_insert _ _⟩ fun _ h => ratio_le_one N γ false h)
  apply le_of_forall_lt_imp_le_of_dense
  intro t ht
  have hD₁ : 0 < 1 + D := by positivity
  let a := min δ ((1 - t) / (1 + D))
  have ha : 0 < a := lt_min hδ (div_pos (sub_pos.mpr ht) hD₁)
  have hscale : a * (1 + D) ≤ 1 - t :=
    (le_div_iff₀ hD₁).mp (min_le_right _ _)
  have hden : 0 < 1 + D * a := by positivity
  have hfac : t ≤ (1 + D * a)⁻¹ := by
    rw [← one_div, le_div_iff₀ hden]
    have hDa : D * a ≤ 1 - t := by nlinarith only [hscale, ha.le]
    nlinarith only [hDa, mul_nonneg (sub_nonneg.mpr ht.le) (mul_nonneg hD ha.le)]
  obtain ⟨ρ, σ, hρ, htρ, hσ, htσ, hm, hx, hinput, hpay⟩ :=
    hWitness a ha (min_le_left _ _)
  have hratio : E γ (amp N ρ) (amp N σ) / E γ ρ σ ∈ completeRatios N γ false :=
    ⟨R, fR, dR, ρ, σ, hρ, htρ, hσ, htσ, hm, by simp, hx, rfl⟩
  refine hfac.trans ((le_div_iff₀ hx).mpr ?_) |>.trans
    (le_csSup hBound (Set.mem_insert_of_mem _ hratio))
  calc
    _ ≤ (1 + D * a)⁻¹ * a := mul_le_mul_of_nonneg_left hinput (inv_nonneg.mpr hden.le)
    _ ≤ _ := by simpa only [div_eq_mul_inv, mul_comm a] using hpay

open private posTrace_mono from D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation
open private posTrace_smul from
  D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction

/-- A replacement component with probability (p) bounds the complete coefficient by
(1-p) for all hockey-stick parameters at least one. -/
theorem coefficient_le_of_replacement (N M : QuantumChannel A B) (τ : DensityState B)
    {p γ : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1) (hγ : 1 ≤ γ)
    (hN : ∀ Z, act N Z = (1 - p) • act M Z + p • (Z.trace • pairMatrix τ)) :
    completeCoefficient N γ false ≤ 1 - p := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp₁
  apply csSup_le ⟨0, Set.mem_insert _ _⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact hq
  rcases hx with ⟨R, fR, dR, ρ, σ, hρ, _, hσ, _, hm, _, hd, rfl⟩
  let := fR
  let := dR
  have hAmp (Z : Matrix (R × A) (R × A) ℂ) :
      amp N Z = (1 - p) • amp M Z + p • (ptr Z ⊗ₖ pairMatrix τ) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    have h := congrArg (fun K : Matrix B B ℂ => K a b)
      (hN (fun x y => Z (i, x) (j, y)))
    rw [amp_entry]
    exact h
  let Δ := ρ - γ • σ
  have hΔ : ptr Δ = (1 - γ) • ptr ρ := by
    rw [show Δ = ρ - γ • σ from rfl, ptr_sub_smul, ← hm, sub_smul, one_smul]
  have hnonpos : p • (ptr Δ ⊗ₖ pairMatrix τ) ≤ 0 := by
    rw [hΔ, Matrix.smul_kronecker, smul_smul]
    exact smul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hp (sub_nonpos.mpr hγ))
      ((partialTraceRight_posSemidef hρ).kronecker (density_posSemidef τ)).nonneg
  have hle : amp N Δ ≤ (1 - p) • amp M Δ := by
    rw [hAmp]
    exact add_le_of_nonpos_right hnonpos
  have hHerm (C : QuantumChannel A B) : (amp C Δ).IsHermitian := by
    rw [show Δ = ρ - γ • σ from rfl, amp_sub_smul]
    exact (amp_psd C hρ).isHermitian.sub ((amp_psd C hσ).isHermitian.smul (IsSelfAdjoint.all γ))
  have hmono := posTrace_mono (hHerm N) ((hHerm M).smul (IsSelfAdjoint.all (1 - p))) hle
  rw [posTrace_smul (1 - p) hq] at hmono
  change posTrace (amp N (ρ - γ • σ)) ≤ (1 - p) * posTrace (amp M (ρ - γ • σ)) at hmono
  rw [amp_sub_smul, amp_sub_smul] at hmono
  apply (div_le_iff₀ hd).mpr
  exact hmono.trans (mul_le_mul_of_nonneg_left (E_contract M γ hρ hσ) hq)

end Coefficients

#print axioms result
#print axioms coefficient_le_of_replacement

end D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport
