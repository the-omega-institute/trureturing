/- GID: D5/S3/Arith/LocalDold/QuotientBlock
   generality: G
   mirror-B: D5/B/S3/Arith/LocalDold/QuotientBlock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual normalized blocks and nonconstant quotient coefficients have equal ideals. -/
import D5.S3.Arith.LocalDold.NormalizedQuotient
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The monic quotient pairing is unitriangular after reversing the nonconstant
coordinates. This is the actual quotient/block bridge in manuscript Section 3.1. -/
set_option autoImplicit false
namespace D5.S3.Arith.LocalDold.QuotientBlock
open Polynomial Matrix
open D5.S3.Arith.LocalDold.NormalizedQuotient

private theorem initial (E : LinearRecurrence ℤ) (i : ℕ) (hi : i < E.order) :
    impulse E i = if i+1=E.order then 1 else 0 :=
  E.mkSol_eq_init _ ⟨i,hi⟩

private theorem degree (E : LinearRecurrence ℤ) : E.charPoly.natDegree = E.order :=
  Polynomial.natDegree_eq_of_degree_eq_some E.charPoly_degree_eq_order

private noncomputable def pairing (E : LinearRecurrence ℤ) :
    Matrix (Fin (E.order-1)) (Fin (E.order-1)) ℤ :=
  fun j i => impulse E (E.order-1-i.val+j.val)

private theorem pairing_det (E : LinearRecurrence ℤ) (hk : 2 ≤ E.order) :
    (pairing E).det = 1 := by
  have hl : (pairing E).IsLowerTriangular := by
    intro j i hij
    change i.val > j.val at hij
    change impulse E (E.order-1-i.val+j.val)=0
    rw [initial E _ (by omega),ite_eq_right (by omega)]
  rw [Matrix.det_of_isLowerTriangular _ hl]
  have hd : ∀ i : Fin (E.order-1), pairing E i i=1 := by
    intro i
    change impulse E (E.order-1-i.val+i.val)=1
    rw [initial E _ (by omega),ite_eq_left (by omega)]
  simp only [hd,Finset.prod_const_one]

private theorem span_mulVec_le {I : Type*} [Fintype I] (A : Matrix I I ℤ) (v : I → ℤ) :
    Ideal.span (Set.range (A *ᵥ v)) ≤ Ideal.span (Set.range v) := by
  apply Ideal.span_le.mpr
  rintro x ⟨i,rfl⟩
  change (∑ j, A i j*v j) ∈ Ideal.span (Set.range v)
  apply Ideal.sum_mem
  intro j _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩)

private theorem span_mulVec_eq {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hA : IsUnit A.det) (v : I → ℤ) :
    Ideal.span (Set.range (A *ᵥ v)) = Ideal.span (Set.range v) := by
  apply le_antisymm (span_mulVec_le A v)
  have he : A⁻¹ *ᵥ (A *ᵥ v)=v := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hA,Matrix.one_mulVec]
  conv_lhs => rw [← he]
  exact span_mulVec_le A⁻¹ (A *ᵥ v)

private theorem quotient_expansion (E : LinearRecurrence ℤ) (hk : 2 ≤ E.order)
    (q : Algebra E) :
    (∑ i : Fin (E.order-1),
      (AdjoinRoot.modByMonicHom E.charPoly_monic q).coeff (E.order-1-i.val) •
        (AdjoinRoot.root E.charPoly)^(E.order-1-i.val)) +
      (AdjoinRoot.modByMonicHom E.charPoly_monic q).coeff 0 • (1 : Algebra E) = q := by
  have hs := (AdjoinRoot.powerBasis' E.charPoly_monic).basis.sum_repr q
  simp_rw [(AdjoinRoot.powerBasis' E.charPoly_monic).basis_eq_pow] at hs
  change (∑ i : Fin E.charPoly.natDegree,
    (AdjoinRoot.modByMonicHom E.charPoly_monic q).coeff i.val •
      (AdjoinRoot.root E.charPoly)^i.val) = q at hs
  rw [degree E] at hs
  rw [← Equiv.sum_comp (Fin.revPerm : Fin E.order ≃ Fin E.order)] at hs
  have ho : E.order=E.order-1+1 := by omega
  conv at hs => lhs; rw [ho]
  rw [Fin.sum_univ_castSucc] at hs
  simpa only [Fin.revPerm_apply,Fin.val_rev,Fin.val_castSucc,Fin.val_last,
    Nat.sub_self,pow_zero,Nat.add_sub_add_right] using hs

/-- For every actual quotient element, top-coefficient observations against the
first order-minus-one powers generate exactly its nonconstant coefficient ideal. -/
theorem observation_ideal (E : LinearRecurrence ℤ) (hk : 2 ≤ E.order) (q : Algebra E) :
    Ideal.span (Set.range (fun j : Fin (E.order-1) =>
      observation E (q*(AdjoinRoot.root E.charPoly)^j.val))) =
    Ideal.span (Set.range (fun i : Fin (E.order-1) =>
      (AdjoinRoot.modByMonicHom E.charPoly_monic q).coeff (E.order-1-i.val))) := by
  let v : Fin (E.order-1) → ℤ := fun i =>
    (AdjoinRoot.modByMonicHom E.charPoly_monic q).coeff (E.order-1-i.val)
  have he : (fun j : Fin (E.order-1) =>
      observation E (q*(AdjoinRoot.root E.charPoly)^j.val)) = pairing E *ᵥ v := by
    funext j
    conv_lhs => rw [← quotient_expansion E hk q]
    rw [add_mul,map_add,Finset.sum_mul,map_sum]
    have hz : observation E ((AdjoinRoot.modByMonicHom E.charPoly_monic q).coeff 0 •
        (1 : Algebra E) * (AdjoinRoot.root E.charPoly)^j.val)=0 := by
      rw [smul_mul_assoc,map_smul,one_mul,
        observation_eq_impulse E (by omega),initial E _ (by omega),ite_eq_right (by omega)]
      simp
    rw [hz,add_zero]
    change _ = ∑ i, pairing E j i*v i
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_mul_assoc,map_smul,← pow_add,observation_eq_impulse E (by omega)]
    change v i*impulse E (E.order-1-i.val+j.val) =
      impulse E (E.order-1-i.val+j.val)*v i
    exact mul_comm _ _
  rw [he]
  exact span_mulVec_eq (pairing E) (by rw [pairing_det E hk]; exact isUnit_one) v

/-- Apply the unitriangular pairing to the actual nth root power and impulse block.
There is no supplied block-equivalence assumption and no irreducibility hypothesis. -/
theorem block_coefficient_ideal (E : LinearRecurrence ℤ) (hk : 2 ≤ E.order) (n : ℕ) :
    Ideal.span (Set.range (fun j : Fin (E.order-1) => impulse E (n+j.val))) =
    Ideal.span (Set.range (fun i : Fin (E.order-1) =>
      (AdjoinRoot.modByMonicHom E.charPoly_monic ((AdjoinRoot.root E.charPoly)^n)).coeff
        (E.order-1-i.val))) := by
  have h := observation_ideal E hk ((AdjoinRoot.root E.charPoly)^n)
  simpa only [← pow_add,observation_eq_impulse E (by omega)] using h

#print axioms observation_ideal
#print axioms block_coefficient_ideal
end D5.S3.Arith.LocalDold.QuotientBlock
