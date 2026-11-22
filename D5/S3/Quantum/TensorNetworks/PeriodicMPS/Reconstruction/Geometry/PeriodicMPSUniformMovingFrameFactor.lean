/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameFactor
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameFactor
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Matrix factorization through the native frame. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameColumns

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame

open Matrix
open scoped Matrix Kronecker
open PeriodicMPSUniformAntisymmetricTransfer (BondMatrix TransferMatrix mixedRaw)
open PeriodicMPSUniformHardCoreTransferRecurrence (TwoBits)
open SevenSiteCriticalCertificate (observedRow)
open private rowOf from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameRows

noncomputable section

variable {E : Type*} [Field E] [Algebra ℂ E]

private def swapConj {R : Type*} [CommRing R] :
    TransferMatrix R ≃+* TransferMatrix R :=
  Matrix.reindexRingEquiv R (Equiv.prodComm (Fin 2) (Fin 2))

private theorem swap_apply {R : Type*} [CommRing R] (W : TransferMatrix R) (p q : TwoBits) :
    swapConj W p q = W p.swap q.swap := rfl

private theorem symmetric_iff {R : Type*} [CommRing R] (W : TransferMatrix R) :
    SwapSymmetric W ↔ swapConj W = W := by
  constructor
  · intro h
    apply Matrix.ext
    exact h
  · intro h p q
    exact congrFun (congrFun h p) q

private theorem swap_pairFrame {R : Type*} [CommRing R] (g : BondMatrix R) :
    swapConj (pairFrame g) = pairFrame g := by
  apply Matrix.ext
  intro p q
  exact mul_comm _ _

/-- Physical conjugation and first-order differentiation preserve the
simultaneous site exchange used by the native Pauli row reconstruction. -/
theorem swapSymmetric_frame {R : Type*} [CommRing R] (g h : BondMatrix R)
    {W : TransferMatrix R} (hW : SwapSymmetric W) :
    SwapSymmetric (pairFrame g * W * pairFrame h) := by
  rw [symmetric_iff, map_mul, map_mul, swap_pairFrame, swap_pairFrame, (symmetric_iff _).mp hW]

omit [Field E] [Algebra ℂ E] in
theorem swapSymmetric_tangent {W : TransferMatrix (DualNumber E)} (hW : SwapSymmetric W) :
    SwapSymmetric (jetTangent W) := by
  intro p q
  exact congrArg TrivSqZeroExt.snd (hW p q)

omit [Algebra ℂ E] in
theorem swapSymmetric_rotation (H : BondMatrix E)
    {W : TransferMatrix E} (hW : SwapSymmetric W) :
    SwapSymmetric (physicalTangent H W) := by
  have hH : swapConj (pairGenerator H) = pairGenerator H := by
    apply Matrix.ext
    intro p q
    simp only [swap_apply, pairGenerator, Matrix.kroneckerMap_apply, Matrix.add_apply]
    change H p.2 q.2 * (1 : BondMatrix E) p.1 q.1 +
      (1 : BondMatrix E) p.2 q.2 * H p.1 q.1 =
      H p.1 q.1 * (1 : BondMatrix E) p.2 q.2 +
      (1 : BondMatrix E) p.1 q.1 * H p.2 q.2
    ring
  rw [symmetric_iff, physicalTangent, map_sub, map_mul, map_mul, hH, (symmetric_iff _).mp hW]

private def unobserveLinear : (Fin 10 → E) →ₗ[E] TransferMatrix E where
  toFun := unobserve
  map_add' u v := by
    apply Matrix.ext
    intro p q
    simp [unobserve, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c v := by
    apply Matrix.ext
    intro p q
    simp only [unobserve, Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

private def undoSectionFrame (x : Fin 5 → E) (τ : E) :
    (Fin 10 → E) →ₗ[E] TransferMatrix E where
  toFun v := pairFrame (sectionBalancedBraInverse x τ) * unobserve v *
    pairFrame (sectionBalancedKetFrame x τ)
  map_add' u v := by
    change _ * unobserveLinear (u + v) * _ = _
    rw [map_add, mul_add, add_mul]
    rfl
  map_smul' c v := by
    change _ * unobserveLinear (c • v) * _ = _
    rw [map_smul, Matrix.mul_smul, Matrix.smul_mul]
    rfl

private theorem undoSectionFrame_column (x : Fin 5 → E) (τ : E)
    (hs : sectionTraceSum x ≠ 0) (ht : τ ≠ 0)
    (W : TransferMatrix E) (hW : SwapSymmetric W) :
    undoSectionFrame x τ (sectionPauliColumn x τ W) = W := by
  let g := sectionBalancedKetFrame x τ
  let h := sectionBalancedBraInverse x τ
  have hi := (sectionFrame_inverse x hs τ ht).1
  have hp : pairFrame h * pairFrame g = 1 := by rw [← pairFrame_mul, hi, pairFrame_one]
  change pairFrame h * unobserve (fun i => pauliRead
    (pairFrame g * W * pairFrame h) (observedRow i)) * pairFrame g = W
  rw [unobserve_pauliRead _ (swapSymmetric_frame g h hW)]
  simp only [← mul_assoc, hp, one_mul]
  rw [mul_assoc W, hp, mul_one]

private def evalRows {ι : Type*} (rows : ι → TransferMatrix E →ₗ[E] E) :
    TransferMatrix E →ₗ[E] (ι → E) :=
  LinearMap.pi rows

/-- Contract actual section columns by any linear rows. If the transported
columns are combinations of the native columns, the displayed section
matrix product follows from the checked Pauli reconstruction. -/
theorem sectionColumns_factor {ι κ : Type*} (x : Fin 5 → E) (τ : E)
    (hs : sectionTraceSum x ≠ 0) (ht : τ ≠ 0) (N : Matrix (Fin 10) (Fin 9) E)
    (rows : ι → TransferMatrix E →ₗ[E] E) (cols : κ → TransferMatrix E)
    (hsym : ∀ j, SwapSymmetric (cols j))
    (hcols : ∀ j, ∃ v : Fin 9 → E, sectionPauliColumn x τ (cols j) = N *ᵥ v) :
    ∃ (L : Matrix ι (Fin 10) E) (C : Matrix (Fin 9) κ E),
      Matrix.of (fun i j => rows i (cols j)) = L * N * C := by
  classical
  choose v hv using hcols
  let C : Matrix (Fin 9) κ E := Matrix.of fun k j => v j k
  let F := (evalRows rows).comp (undoSectionFrame x τ)
  let L : Matrix ι (Fin 10) E := Matrix.of fun i k => F (Pi.single k 1) i
  refine ⟨L, C, ?_⟩
  apply Matrix.ext
  intro i j
  have hF : F (N *ᵥ v j) i = rows i (cols j) := by
    rw [← hv j]
    change rows i (undoSectionFrame x τ (sectionPauliColumn x τ (cols j))) = _
    rw [undoSectionFrame_column x τ hs ht _ (hsym j)]
  change rows i (cols j) = _
  rw [← hF, Matrix.mul_assoc]
  have hvec : N *ᵥ v j = ∑ k : Fin 10, (N *ᵥ v j) k • Pi.single k (1 : E) := by
    funext k
    simp [Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [hvec]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply,
    L, Matrix.of_apply, C, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame
