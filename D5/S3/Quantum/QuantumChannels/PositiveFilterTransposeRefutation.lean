/- GID: D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.claim; result=D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.result; claim=D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.claim
   digest: A unital qutrit channel fails positive-filter transpose factorization. -/

/-
proof_shape:
  PhyslibLeaf.MatrixMap.IsHermitianPreserving: bind-only (definition)
  PhyslibLeaf.MatrixMap.IsPositive.IsHermitianPreserving: bind-only
  PhyslibLeaf.MatrixMap.IsCompletelyPositive.IsPositive: bind-only
  PhyslibLeaf.MatrixMap.dual: bind-only (definition)
  PhyslibLeaf.MatrixMap.Dual.trace_eq: bind-only
  PhyslibLeaf.MatrixMap.IsHermitianPreserving.dual: bind-only
  Matrix.PosSemidef.trace_mul_nonneg: bind-only
  PhyslibLeaf.MatrixMap.IsPositive.dual: bind-only
  HermitianMat.ker_sum: bind-only
  claim: definition
  positive_functional: bind-only
  zero_pattern_obstruction: content
  result: content
escape_witness:
  positive_functional: bind-only; Physlib dual positivity and trace duality
    applied to a positive diagonal matrix unit.
  zero_pattern_obstruction: positive coefficients force kernel constraints, and
    the row bound forces a permutation of zeros and a diagonal Gram matrix.
  result: the twelve rational Kraus matrices instantiate that obstruction for
    a unital channel with nonorthogonal kernel vectors.
admission_basis: open-problem-resolution (#13926; Refuted)
The Physlib transplants and private parameterized helpers are consumed by result.
The bind-only helpers supply no admission basis of their own.
Direct frozen dependencies:
  D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.UnitalChannel
    statement_id: sha256:8cbb15c2bd7883d92b9abc540229632657c8a3d450151c4b6b9ca7bcd2905990
  D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsCPTP
    statement_id: sha256:1440f7e681ed2017e7c90aedfe54aa0ad218d57311655f9d554863853dd8f53c
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap
    statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsPositive
    statement_id: sha256:f17d83cade270607ed26a249661ca93167b5a57d01906f355672261f7aaa0cb6
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsCompletelyPositive
    statement_id: sha256:39e2682fd93035c705a08181bb7fdfb77067eba43afcc98c200c30543b913ed4
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus_isCompletelyPositive
    statement_id: sha256:522daaecff9970808def6ecdd938d4b89107d2820c79bafbf378ab083767f57f
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron
    statement_id: sha256:6bbbe42180d7cde8ee171b8a1aeeb16449194862345f2042d95ec7c0b2055471
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron_def
    statement_id: sha256:0a066df1b1de64e4fda175d1ac776d744674a6465abc8a7f13b12f185ce29405
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
    statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.QuantumChannels.CPFilterTransposeRefutation

/-
Source: leanprover-community/physlib, commit 6a09b2d1761a0d4430083045a247eb121d8da260,
QuantumInfo/Channels/Unbundled.lean, QuantumInfo/Channels/Dual.lean,
and QuantumInfo/ForMathlib/HermitianMat/Order.lean.
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Authors: Alex Meiburg (Unbundled.lean and HermitianMat/Order.lean);
Alex Meiburg and Dennj Osele (Dual.lean), as credited in the upstream headers.
Apache-2.0; full license, source mapping and retirement condition: Library/QuantumChannels/meiburg2025physlibdual.md.
Adaptations: reopen the frozen PhyslibLeaf namespace; reuse its MatrixMap,
IsPositive, IsCompletelyPositive and kron; select imports and explicit binders;
replace HermitianMat positive/negative parts by Mathlib CFC positive/negative
parts, and HermitianMat.H by the selfAdjoint subtype property;
expand HermitianMat, mat and ker to Mathlib selfAdjoint, Subtype.val and
LinearMap.ker of Matrix.toEuclideanLin in ker_sum.
The pinned upstream tree has no NOTICE file.
-/

/-! ## Physlib trace duality and positivity -/

noncomputable section PhyslibChannelDual
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra
open Kronecker

namespace D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap

section unbundled
variable {A B R : Type*} [Fintype A] [Fintype B] [RCLike R]

/-- A linear matrix map is *Hermitian preserving* if it maps `IsHermitian` matrices to `IsHermitian`.-/
def IsHermitianPreserving (M : MatrixMap A B R) : Prop :=
  ∀⦃x⦄, x.IsHermitian → (M x).IsHermitian

namespace IsPositive

/- Every `MatrixMap` that `IsPositive` is also `IsHermitianPreserving`. -/
theorem IsHermitianPreserving {M : MatrixMap A B R}
    (hM : IsPositive M) : IsHermitianPreserving M := by
  intro x hx
  classical
  have hMPos := hM (Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg x))
  have hMNeg := hM (Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg x))
  have hSub := hMPos.isHermitian.sub hMNeg.isHermitian
  rw [← map_sub] at hSub
  convert ← hSub
  exact CFC.posPart_sub_negPart x hx

end IsPositive

namespace IsCompletelyPositive
variable [DecidableEq A]
/- Every `MatrixMap` that `IsCompletelyPositive` also `IsPositiveMap`. -/
theorem IsPositive {M : MatrixMap A B R}
    (hM : IsCompletelyPositive M) : IsPositive M := by
  intro x hx
  let x' : Matrix (A × Fin 1) (A × Fin 1) R := x ⊗ₖ 1
  let eqA : (A × Fin 1) ≃ A :=
    (Equiv.prodCongrRight (fun _ ↦ finOneEquiv)).trans (Equiv.prodPUnit A)
  let eqB : (B × Fin 1) ≃ B :=
    (Equiv.prodCongrRight (fun _ ↦ finOneEquiv)).trans (Equiv.prodPUnit B)
  specialize @hM 1 (x.submatrix eqA eqA) (Matrix.PosSemidef.submatrix hx _)
  convert Matrix.PosSemidef.submatrix hM eqB.symm; clear hM
  --TODO Cleanup
  ext i j
  simp only [Matrix.submatrix, Matrix.of_apply]
  rw [MatrixMap.kron_def]
  suffices h : M x = ∑ a₁, ∑ a₂, x a₁ a₂ • M (Matrix.single a₁ a₂ 1) by
    simp [h, Matrix.sum_apply, Matrix.single, eqA, eqB]
    ac_rfl
  simp only [← M.map_smul, ← map_sum]
  congr
  ext k l
  simp [Matrix.sum_apply, Matrix.single]
  rw [Finset.sum_eq_single k]
  · simp
  · simp +contextual
  · simp +contextual
end IsCompletelyPositive
end unbundled

section duality
variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut]
variable {R : Type*} [CommRing R]
variable {𝕜 : Type*} [RCLike 𝕜]
variable [DecidableEq dIn] [DecidableEq dOut]

/-- The dual of a map between matrices, defined by `Tr[A M(B)] = Tr[(dual M)(A) B]`. Sometimes
 called the adjoint of the map instead. -/
@[irreducible]
def dual (M : MatrixMap dIn dOut R) : MatrixMap dOut dIn R :=
  let coordDual :=
    let iso1 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dIn dIn).symm
    let iso2 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dOut dOut)
    iso1 ∘ₗ LinearMap.dualMap M ∘ₗ iso2
  (Matrix.transposeLinearEquiv dIn dIn R R).toLinearMap ∘ₗ coordDual ∘ₗ
    (Matrix.transposeLinearEquiv dOut dOut R R).toLinearMap

/-- The defining property of a dual map: inner products are preserved on the opposite argument. -/
theorem Dual.trace_eq (M : MatrixMap dIn dOut R) (A : Matrix dIn dIn R) (B : Matrix dOut dOut R) :
    (M A * B).trace = (A * M.dual B).trace := by
  have hDualIn (X Y : Matrix dIn dIn R) :
      ((Matrix.stdBasis R dIn dIn).toDualEquiv Y) X = (X * Y.transpose).trace := by
    simp [Module.Basis.toDualEquiv_apply, Module.Basis.toDual, Matrix.trace, Matrix.mul_apply,
      Matrix.stdBasis, Fintype.sum_prod_type, mul_comm]
  have hDualOut (X Y : Matrix dOut dOut R) :
      ((Matrix.stdBasis R dOut dOut).toDualEquiv Y) X = (X * Y.transpose).trace := by
    simp [Module.Basis.toDualEquiv_apply, Module.Basis.toDual, Matrix.trace, Matrix.mul_apply,
      Matrix.stdBasis, Fintype.sum_prod_type, mul_comm]
  let coordDual : MatrixMap dOut dIn R :=
    let iso1 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dIn dIn).symm
    let iso2 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dOut dOut)
    iso1 ∘ₗ LinearMap.dualMap M ∘ₗ iso2
  rw [show (M A * B).trace =
      ((Matrix.stdBasis R dOut dOut).toDualEquiv B.transpose) (M A) by
    simpa using (hDualOut (M A) B.transpose).symm]
  rw [show
      ((Matrix.stdBasis R dOut dOut).toDualEquiv B.transpose) (M A) =
        ((Matrix.stdBasis R dIn dIn).toDualEquiv (coordDual B.transpose)) A by
    simp [coordDual]]
  simpa [dual, coordDual] using hDualIn A (coordDual B.transpose)

set_option backward.isDefEq.respectTransparency false in
/-- The dual of a `IsHermitianPreserving` map also `IsHermitianPreserving`. -/
theorem IsHermitianPreserving.dual {M : MatrixMap dIn dOut ℂ} (h : M.IsHermitianPreserving) :
    M.dual.IsHermitianPreserving := by
  have map_conjTranspose (x : Matrix dIn dIn ℂ) :
      M (Matrix.conjTranspose x) = Matrix.conjTranspose (M x) := by
    have hxstar : (realPart x : Matrix dIn dIn ℂ) - Complex.I • (imaginaryPart x : Matrix dIn dIn ℂ) =
        Matrix.conjTranspose x := by
      rw [← Matrix.star_eq_conjTranspose]
      have hreal_star : (realPart (star x) : Matrix dIn dIn ℂ) = realPart x := by
        rw [realPart_apply_coe, realPart_apply_coe, star_star, add_comm]
      have himag_star : (imaginaryPart (star x) : Matrix dIn dIn ℂ) = -imaginaryPart x := by
        rw [imaginaryPart_apply_coe, imaginaryPart_apply_coe, star_star]
        module
      have h := realPart_add_I_smul_imaginaryPart (star x : Matrix dIn dIn ℂ)
      rw [hreal_star, himag_star, smul_neg] at h
      simpa [sub_eq_add_neg] using h
    calc
      M (Matrix.conjTranspose x) = M (realPart x - Complex.I • imaginaryPart x) := by
        rw [← hxstar]
      _ = M (realPart x) - Complex.I • M (imaginaryPart x) := by
        simp [sub_eq_add_neg, map_add, map_smul]
      _ = Matrix.conjTranspose (M (realPart x) + Complex.I • M (imaginaryPart x)) := by
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
        rw [show Matrix.conjTranspose (M (realPart x)) = M (realPart x) by
          simpa [Matrix.IsHermitian] using h ((realPart x).property)]
        rw [show Matrix.conjTranspose (M (imaginaryPart x)) = M (imaginaryPart x) by
          simpa [Matrix.IsHermitian] using h ((imaginaryPart x).property)]
        simp [sub_eq_add_neg]
      _ = Matrix.conjTranspose (M x) := by
        congr 1
        simpa [map_add, map_smul] using congrArg M (realPart_add_I_smul_imaginaryPart x)
  intro x hx
  simpa [Matrix.IsHermitian] using show Matrix.conjTranspose (M.dual x) = M.dual x by
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro A
    have htrace2 := congrArg star (Dual.trace_eq M (Matrix.conjTranspose A) (Matrix.conjTranspose x))
    rw [← Matrix.trace_conjTranspose, ← Matrix.trace_conjTranspose] at htrace2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
      map_conjTranspose, hx, Matrix.conjTranspose_conjTranspose,
      Matrix.trace_mul_comm x (M A),
      Matrix.trace_mul_comm (Matrix.conjTranspose (M.dual x)) A] at htrace2
    exact htrace2.symm.trans (Dual.trace_eq M A x)

open MatrixOrder
--TODO Cleanup, find home, abstract out to HermitianMats...?
theorem _root_.Matrix.PosSemidef.trace_mul_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  open scoped Matrix in
  obtain ⟨sqrtB, rfl⟩ : ∃ sqrtB : Matrix n n 𝕜, B = sqrtBᴴ * sqrtB := by
    classical
    apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    exact Matrix.nonneg_iff_posSemidef.mpr hB
  simp only [← Matrix.mul_assoc, ← Matrix.trace_mul_comm sqrtB]
  have h : (sqrtB * A * sqrtBᴴ).PosSemidef := by
    convert hA.conjTranspose_mul_mul_same sqrtBᴴ using 1
    simp [Matrix.mul_assoc]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at h
  simpa [Matrix.mulVec, dotProduct, Matrix.trace, Pi.single_apply] using
    Finset.sum_nonneg fun i _ ↦ h.2 (Pi.single i 1)

/-- The dual of a `IsPositive` map also `IsPositive`. -/
theorem IsPositive.dual {M : MatrixMap dIn dOut ℂ} (h : M.IsPositive) : M.dual.IsPositive := by
  intro x hx
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hx ⊢
  use IsHermitianPreserving.dual h.IsHermitianPreserving hx.1
  intro v
  have h_dual_pos : 0 ≤ (M (Matrix.vecMulVec v (star v)) * x).trace := by
    --TODO Cleanup. Should be all in terms of HermitianMat
    apply Matrix.PosSemidef.trace_mul_nonneg;
    · apply h;
      exact Matrix.posSemidef_vecMulVec_self_star v;
    · rw [← Matrix.posSemidef_iff_dotProduct_mulVec] at hx
      exact hx;
  convert h_dual_pos using 1;
  rw [ MatrixMap.Dual.trace_eq ];
  simp [ Matrix.vecMulVec, Matrix.mul_apply, Matrix.trace ];
  simp [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )

end duality
end D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap

/-- The kernel of a finite sum of positive semidefinite Hermitian matrices is the
intersection of their kernels. -/
theorem HermitianMat.ker_sum {n ι 𝕜 : Type*} [Fintype n] [Fintype ι] [RCLike 𝕜]
    [DecidableEq n] (f : ι → selfAdjoint (Matrix n n 𝕜)) (hf : ∀ i, 0 ≤ f i) :
    LinearMap.ker ((∑ i, f i).val.toEuclideanLin) =
      ⨅ i, LinearMap.ker ((f i).val.toEuclideanLin) := by
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.toLpLin_apply,
    WithLp.toLp_eq_zero, AddSubgroup.val_finsetSum]
  constructor
  · intro hv i
    have hfi := Matrix.nonneg_iff_posSemidef.mp (show 0 ≤ (f i).val from hf i)
    rw [← hfi.dotProduct_mulVec_zero_iff]
    have hge : ∀ j, 0 ≤ star (WithLp.ofLp v) ⬝ᵥ (f j).val *ᵥ WithLp.ofLp v := by
      intro j
      have := Matrix.nonneg_iff_posSemidef.mp (show 0 ≤ (f j).val from hf j)
      rw [Matrix.posSemidef_iff_dotProduct_mulVec] at this
      exact this.2 (WithLp.ofLp v)
    have hsum : ∑ j, star (WithLp.ofLp v) ⬝ᵥ (f j).val *ᵥ WithLp.ofLp v = 0 := by
      rw [← dotProduct_sum, ← Matrix.sum_mulVec, hv, dotProduct_zero]
    exact le_antisymm
      (hsum ▸ Finset.single_le_sum (fun j _ => hge j) (Finset.mem_univ i))
      (hge i)
  · intro h
    simp [Matrix.sum_mulVec, h]

end PhyslibChannelDual

/-! ## Positive-filter transpose obstruction -/

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.CPFilterTransposeRefutation (UnitalChannel)
-- The canonical utility header occupies a single line.
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
def claim : Prop := ∀ F : MatrixMap (Fin 3) (Fin 3) ℂ, UnitalChannel F →
  ∀ (S : Type) [Fintype S] (K : S → Matrix (Fin 3) (Fin 3) ℂ),
    F = MatrixMap.of_kraus K K →
    ∃ P E : MatrixMap (Fin 3) (Fin 3) ℂ, MatrixMap.IsPositive P ∧
      MatrixMap.IsCompletelyPositive E ∧
      MatrixMap.of_kraus (fun i => (K i)ᵀ) (fun i => (K i)ᵀ) = P ∘ₗ F ∘ₗ E


/-- A positive diagonal functional has a positive semidefinite trace representative. -/
private theorem positive_functional (f : MatrixMap (Fin 3) (Fin 3) ℂ)
    (hf : MatrixMap.IsPositive f) (k : Fin 3) :
    ∃ B : Matrix (Fin 3) (Fin 3) ℂ, B.PosSemidef ∧
      ∀ X, Matrix.trace (B * X) = f X k k := by
  refine ⟨f.dual (Matrix.single k k 1), hf.dual ?_, ?_⟩
  · rw [← Matrix.diagonal_single]
    exact Matrix.posSemidef_diagonal_iff.mpr (by
      intro i
      by_cases hi : i = k <;> simp [hi])
  · intro X
    rw [Matrix.trace_mul_comm, ← MatrixMap.Dual.trace_eq]
    simp [Matrix.trace_mul_single]


/-- A positive three-state decomposition with these kernels forces orthogonality. -/
private theorem zero_pattern_obstruction (rho sigma : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (V C : Matrix (Fin 3) (Fin 3) ℂ)
    (hs : ∀ j, (sigma j).PosSemidef)
    (hC : ∀ k j, 0 ≤ C k j)
    (hr : ∀ k, rho k = ∑ j, C k j • sigma j)
    (hker : ∀ k, rho k *ᵥ (fun a => V a k) = 0)
    (hsum : ∑ k, rho k = 1)
    (hdet : Matrix.det ((fun k a => rho k a a) : Matrix (Fin 3) (Fin 3) ℂ) ≠ 0)
    (hVu : IsUnit V)
    (hrow : ∀ k a b, C k a = 0 → C k b = 0 → a = b)
    (hgram : (Vᴴ * V) 0 1 ≠ 0) : False := by
  classical
  let T : Matrix (Fin 3) (Fin 3) ℂ := fun j a => sigma j a a
  have hRT : ((fun k a => rho k a a) : Matrix (Fin 3) (Fin 3) ℂ) = C * T := by
    ext k a
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, T]
      using congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M a a) (hr k)
  have hT : T.det ≠ 0 := by
    rw [hRT, Matrix.det_mul] at hdet
    exact (mul_ne_zero_iff.mp hdet).2
  have kill (k j : Fin 3) (hc : C k j ≠ 0) :
      sigma j *ᵥ (fun a => V a k) = 0 := by
    let x : Fin 3 → ℂ := fun a => V a k
    let f : Fin 3 → selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
      fun l => ⟨C k l • sigma l, ((hs l).smul (hC k l)).isHermitian⟩
    have hf (l : Fin 3) : 0 ≤ f l :=
      Matrix.nonneg_iff_posSemidef.mpr ((hs l).smul (hC k l))
    have hv : WithLp.toLp 2 x ∈ LinearMap.ker ((∑ l, f l).val.toEuclideanLin) := by
      simp only [LinearMap.mem_ker, Matrix.toLpLin_apply,
        WithLp.toLp_eq_zero, AddSubgroup.val_finsetSum]
      change (∑ l, C k l • sigma l) *ᵥ x = 0
      rw [← hr k]
      exact hker k
    rw [HermitianMat.ker_sum f hf] at hv
    have hj := (Submodule.mem_iInf _).mp hv j
    have hz : C k j • (sigma j *ᵥ x) = 0 := by
      simpa only [f, LinearMap.mem_ker, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
        WithLp.toLp_eq_zero, Matrix.smul_mulVec] using hj
    exact (smul_eq_zero.mp hz).resolve_left hc

  have column_zero (j : Fin 3) : ∃ k, C k j = 0 := by
    by_contra hn
    push Not at hn
    have hz : sigma j * V = 0 := by
      ext a k
      exact congrFun (kill k j (hn k)) a
    have hsj : sigma j = 0 := by
      apply hVu.mul_right_cancel
      simpa only [Matrix.zero_mul] using hz
    exact hT (Matrix.det_eq_zero_of_row_eq_zero j (by simp [T, hsj]))
  choose q hq using column_zero
  have qi : Function.Injective q := by
    intro a b he
    exact hrow (q a) a b (hq a) (he ▸ hq b)
  have qs := Finite.surjective_of_injective qi
  have hcol (a b j : Fin 3) (ha : C a j = 0) (hb : C b j = 0) : a = b := by
    obtain ⟨l, hl⟩ := qs a
    obtain ⟨m, hm⟩ := qs b
    have hlj : l = j := hrow a l j (hl ▸ hq l) ha
    have hmj : m = j := hrow b m j (hm ▸ hq m) hb
    rw [← hl, ← hm, hlj, hmj]
  have diag (j : Fin 3) : (Vᴴ * sigma j * V) 0 1 = 0 := by
    by_cases hc : C 1 j = 0
    · have hc0 : C 0 j ≠ 0 := by
        intro hz
        have he := hcol 0 1 j hz hc
        norm_num at he
      have hk := kill 0 j hc0
      have hr0 : (Vᴴ * sigma j) 0 = 0 := by
        funext a
        have he := congrArg star (congrFun hk a)
        simpa only [Matrix.mulVec, dotProduct, star_sum, star_mul,
          Matrix.conjTranspose_apply, Pi.zero_apply, star_zero,
          (hs j).isHermitian.apply, Matrix.mul_apply] using he
      change (∑ x, (Vᴴ * sigma j) 0 x * V x 1) = 0
      simp only [hr0, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    · have hk := kill 1 j hc
      rw [Matrix.mul_assoc]
      change (Vᴴ *ᵥ (sigma j *ᵥ (fun a => V a 1))) 0 = 0
      rw [hk, Matrix.mulVec_zero]
      rfl
  have rdiag (k : Fin 3) : (Vᴴ * rho k * V) 0 1 = 0 := by
    rw [hr k]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, diag, mul_zero,
      Finset.sum_const_zero]
  have hg : (Vᴴ * V) 0 1 = 0 := by
    have he : (Vᴴ * (∑ k, rho k) * V) 0 1 = 0 := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, rdiag,
        Finset.sum_const_zero]
    simpa only [hsum, Matrix.mul_one] using he
  exact hgram hg


set_option maxHeartbeats 6000000 in
-- Exact Kraus and support-pattern certificates require finite matrix expansions.
/-- The weak positive/CP factorization question fails for a unital qutrit channel. -/
theorem result : ¬ claim := by
  classical
  let u : Fin 3 → Fin 3 → ℂ :=
    ![![(3/7:ℂ),6/7,-2/7], ![(-2/7:ℂ),3/7,6/7], ![(6/7:ℂ),-2/7,3/7]]
  let e : Fin 3 → Fin 3 → ℂ := fun j => Pi.single j 1
  let rho : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
    ![!![(29/49:ℂ),9/49,-3/49; 9/49,18/49,-6/49; -3/49,-6/49,2/49],
      !![(2/49:ℂ),-3/49,-6/49; -3/49,29/49,9/49; -6/49,9/49,18/49],
      !![(18/49:ℂ),-6/49,9/49; -6/49,2/49,-3/49; 9/49,-3/49,29/49]]
  let K : (Fin 3 × (Fin 2 × Fin 2)) → Matrix (Fin 3) (Fin 3) ℂ := fun s =>
    (1/2:ℂ) • Matrix.vecMulVec (if s.2.1 = 0 then e s.1 else u s.1) (e s.1)
  let F := MatrixMap.of_kraus K K
  have rho_form (j : Fin 3) : rho j = (1/2:ℂ) •
      (Matrix.vecMulVec (e j) (star (e j)) + Matrix.vecMulVec (u j) (star (u j))) := by
    ext a b
    fin_cases j <;> fin_cases a <;> fin_cases b <;>
      norm_num [rho, u, e, Pi.single_apply, Matrix.vecMulVec, Matrix.smul_apply, map_ofNat]
  have rho_psd (j : Fin 3) : (rho j).PosSemidef := by
    rw [rho_form j]
    exact ((Matrix.posSemidef_vecMulVec_self_star (e j)).add
      (Matrix.posSemidef_vecMulVec_self_star (u j))).smul (by norm_num [Complex.nonneg_iff])
  have estar (j : Fin 3) : star (e j) = e j := by
    simp [e, Pi.star_single]
  have ustar (j : Fin 3) : star (u j) = u j := by
    ext a
    fin_cases j <;> fin_cases a <;> norm_num [u, map_ofNat]
  have term (z : Fin 3 → ℂ) (j : Fin 3) (X : Matrix (Fin 3) (Fin 3) ℂ) :
      ((1/2:ℂ) • Matrix.vecMulVec z (e j)) * X *
        ((1/2:ℂ) • Matrix.vecMulVec z (e j))ᴴ =
          ((1/4:ℂ) * X j j) • Matrix.vecMulVec z (star z) := by
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec, estar,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.vecMulVec_mul]
    ext a b
    simp only [one_div, star_inv₀, star_ofNat, Matrix.vecMulVec, Matrix.vecMul,
      dotProduct, e, Pi.single_apply, mul_comm, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Pi.star_apply,
      RCLike.star_def, ite_mul, one_mul, zero_mul, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, mul_left_comm, mul_assoc, mul_eq_mul_left_iff]
    left
    left
    ring
  have hF (X : Matrix (Fin 3) (Fin 3) ℂ) : F X = ∑ j, X j j • rho j := by
    change (∑ s, K s * X * (K s)ᴴ) = _
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, K, Fin.isValue,
      if_true, Fin.reduceEq, if_false, term]
    apply Finset.sum_congr rfl
    intro j _
    rw [rho_form j]
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have Kre (s : Fin 3 × (Fin 2 × Fin 2)) : (K s)ᴴ = (K s)ᵀ := by
    dsimp only [K]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec,
      Matrix.transpose_smul, Matrix.transpose_vecMulVec, estar]
    by_cases hs : s.2.1 = 0 <;> simp [hs, estar, ustar]
  have KT (s : Fin 3 × (Fin 2 × Fin 2)) : ((K s)ᵀ)ᴴ = K s := by
    rw [← Kre, Matrix.conjTranspose_conjTranspose]
  have dual (X Y : Matrix (Fin 3) (Fin 3) ℂ) :
      Matrix.trace (MatrixMap.of_kraus (fun i => (K i)ᵀ) (fun i => (K i)ᵀ) X * Y) =
        Matrix.trace (X * F Y) := by
    simp only [F, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [KT, ← Kre]
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (K s)ᴴ (X * (K s * Y))
  have hFT (X : Matrix (Fin 3) (Fin 3) ℂ) :
      MatrixMap.of_kraus (fun i => (K i)ᵀ) (fun i => (K i)ᵀ) X =
        Matrix.diagonal (fun k => Matrix.trace (rho k * X)) := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro Y
    rw [dual, hF]
    simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul]
    simp_rw [Matrix.trace_mul_comm X]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal, mul_comm]
  have hsum : (∑ j, rho j) = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [rho, Matrix.sum_apply, Fin.sum_univ_succ]
  have htrace (j : Fin 3) : Matrix.trace (rho j) = 1 := by
    fin_cases j <;> norm_num [rho, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
  have channel : UnitalChannel F := by
    refine ⟨⟨MatrixMap.of_kraus_isCompletelyPositive K, ?_⟩, ?_⟩
    · intro X
      rw [hF, Matrix.trace_sum]
      simp only [Matrix.trace_smul, htrace, smul_eq_mul, mul_one]
      rfl
    · simpa [hF] using hsum
  let V : Matrix (Fin 3) (Fin 3) ℂ := !![0,3,1; 1,0,3; 3,1,0]
  have hker (k : Fin 3) : rho k *ᵥ (fun a => V a k) = 0 := by
    ext a
    fin_cases k <;> fin_cases a <;> norm_num [rho, V, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
  have hdet : Matrix.det ((fun k a => rho k a a) : Matrix (Fin 3) (Fin 3) ℂ) ≠ 0 := by
    norm_num [rho, Matrix.det_fin_three, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Fin.isValue]
  have hVu : IsUnit V := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [isUnit_iff_ne_zero]
    norm_num [V, Matrix.det_fin_three,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.isValue])
  have hgram : (Vᴴ * V) 0 1 ≠ 0 := by
    norm_num [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  have annihilate (B : Matrix (Fin 3) (Fin 3) ℂ) (hB : B.PosSemidef)
      (j : Fin 3) (hz : Matrix.trace (B * rho j) = 0) :
      B *ᵥ e j = 0 ∧ B *ᵥ u j = 0 := by
    rw [rho_form, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul,
      Matrix.trace_add, smul_eq_mul] at hz
    simp only [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
      dotProduct_comm (B *ᵥ e j), dotProduct_comm (B *ᵥ u j)] at hz
    have he : star (e j) ⬝ᵥ (B *ᵥ e j) + star (u j) ⬝ᵥ (B *ᵥ u j) = 0 :=
      (mul_eq_zero.mp hz).resolve_left (by norm_num)
    have hh := (add_eq_zero_iff_of_nonneg (hB.dotProduct_mulVec_nonneg (e j))
      (hB.dotProduct_mulVec_nonneg (u j))).mp he
    exact ⟨(hB.dotProduct_mulVec_zero_iff (x := (e j))).mp hh.1,
      (hB.dotProduct_mulVec_zero_iff (x := (u j))).mp hh.2⟩
  have two_zero (B : Matrix (Fin 3) (Fin 3) ℂ) (hB : B.PosSemidef)
      (hne : B ≠ 0) (j l : Fin 3) (hj : Matrix.trace (B * rho j) = 0)
      (hl : Matrix.trace (B * rho l) = 0) : j = l := by
    by_contra hjl
    obtain ⟨hej, huj⟩ := annihilate B hB j hj
    obtain ⟨hel, _⟩ := annihilate B hB l hl
    let A : Matrix (Fin 3) (Fin 3) ℂ := fun a b => ![e j a, e l a, u j a] b
    have hAu : IsUnit A := by
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      have h21 : (2 : Fin 3) ≠ 1 := by decide
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      rw [isUnit_iff_ne_zero]
      fin_cases j <;> fin_cases l <;>
        first | exact False.elim (hjl rfl)
              | norm_num [A, e, u, Pi.single_apply, Matrix.det_fin_three,
                  Matrix.cons_val_two, Matrix.vecHead,
                  Matrix.vecTail, Fin.isValue, h20, h21] <;> rfl
    have hBA : B * A = 0 := by
      ext a b
      fin_cases b <;>
        first | simpa [A, Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hej a
              | simpa [A, Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hel a
              | simpa [A, Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun huj a
    apply hne
    apply hAu.mul_right_cancel
    simpa only [Matrix.zero_mul] using hBA
  intro hclaim
  obtain ⟨P, E, hP, hE, heq⟩ := hclaim F channel (Fin 3 × (Fin 2 × Fin 2)) K rfl
  have hEpos := MatrixMap.IsCompletelyPositive.IsPositive hE
  choose B hB hPB using fun k => positive_functional P hP k
  choose sigma hs hES using fun j => positive_functional E hEpos j
  let C : Matrix (Fin 3) (Fin 3) ℂ := fun k j => P (rho j) k k
  have hC (k j : Fin 3) : 0 ≤ C k j := (hP (rho_psd j)).diag_nonneg
  have hr (k : Fin 3) : rho k = ∑ j, C k j • sigma j := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro X
    have he := congrArg (fun G : MatrixMap (Fin 3) (Fin 3) ℂ => G X k k) heq
    simp only [LinearMap.comp_apply, hFT, Matrix.diagonal_apply_eq] at he
    rw [hF, map_sum] at he
    simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at he
    simpa only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
      Matrix.trace_smul, smul_eq_mul, hES, C, mul_comm] using he
  have hBn (k : Fin 3) : B k ≠ 0 := by
    intro hz
    have hc (j : Fin 3) : C k j = 0 := by
      dsimp only [C]
      rw [← hPB, hz, Matrix.zero_mul, Matrix.trace_zero]
    have he := congrArg Matrix.trace (hr k)
    simp only [hc, zero_smul, Finset.sum_const_zero, Matrix.trace_zero, htrace] at he
    norm_num at he
  have hrow (k a b : Fin 3) (ha : C k a = 0) (hb : C k b = 0) : a = b := by
    exact two_zero (B k) (hB k) (hBn k) a b
      ((hPB k (rho a)).trans ha) ((hPB k (rho b)).trans hb)
  exact zero_pattern_obstruction rho sigma V C hs hC hr hker hsum hdet hVu hrow hgram

#print axioms result
end D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
