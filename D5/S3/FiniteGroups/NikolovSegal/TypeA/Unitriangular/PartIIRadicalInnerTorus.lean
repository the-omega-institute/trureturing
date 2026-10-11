/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIPropositionSixFive
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace NikolovSegal.PartIIRadicalInnerTorus
open PartIIUnitriangularLayers PartIIUnitriangularActions
universe u
variable {F : Type u} [Field F] {n : ℕ}
private def diagonalSL (a : Fin n → Fˣ) (ha : ∏ i, a i=1) :
    Matrix.SpecialLinearGroup (Fin n) F :=
  ⟨Matrix.diagonal (fun i => (a i:F)),by
    rw [Matrix.det_diagonal]
    have hp : (Units.coeHom F) (∏ i, a i)=∏ i, (Units.coeHom F) (a i) := map_prod (Units.coeHom F) _ _
    change (∏ i, (Units.coeHom F) (a i))=1
    rw [← hp,ha]
    rfl⟩
private theorem diagonalSL_inverse (a : Fin n → Fˣ) (ha : ∏ i, a i=1) :
    (diagonalSL a ha)⁻¹=diagonalSL (fun i => (a i)⁻¹) (by simp only [Finset.prod_inv_distrib,ha,inv_one]) := by
  let b := diagonalSL (fun i => (a i)⁻¹) (by simp only [Finset.prod_inv_distrib,ha,inv_one])
  have h : diagonalSL a ha*b=1 := by
    apply Subtype.ext
    change Matrix.diagonal (fun i => (a i:F))*Matrix.diagonal (fun i => (((a i)⁻¹:Fˣ):F))=1
    rw [Matrix.diagonal_mul_diagonal]
    apply Matrix.diagonal_eq_one.mpr
    funext i; simp
  change (diagonalSL a ha)⁻¹=b
  calc
    _ = (diagonalSL a ha)⁻¹*(diagonalSL a ha*b) := by rw [h,mul_one]
    _ = b := by group
private theorem diagonalSL_action (a : Fin n → Fˣ) (ha : ∏ i, a i=1) :
    MulAut.conj (diagonalSL a ha)=(unitOdd% diagonalAut) a := by
  apply MulEquiv.ext; intro g
  rw [MulAut.conj_apply,diagonalSL_inverse]
  apply Matrix.SpecialLinearGroup.ext; intro i j
  change (Matrix.diagonal (fun i => (a i:F))*g.val*Matrix.diagonal (fun i => (((a i)⁻¹:Fˣ):F))) i j=_
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,(unitOdd% diagonal_entry)]

/-- The determinant equality is exactly the inner-correction obstruction.
The actual determinant-one matrix is constructed and its FULL action is
proved for every field/graph tuple, before any coordinate targets. -/
theorem actual_diagonal_inner_normalization (a b : Fin n → Fˣ)
    (hab : ∏ i, b i=∏ i, a i) (phi : RingAut F) (eps : Bool) :
    ∃ h : Matrix.SpecialLinearGroup (Fin n) F,
      (∀ i j : Fin n, i≠j → h i j=0) ∧
      MulAut.conj h*PartIIProposition6_5.diagonalFieldGraph a phi eps=
        (unitOdd% diagonalAut) b*fieldGraphAut phi eps := by
  let c : Fin n → Fˣ := fun i => b i*(a i)⁻¹
  have hc : ∏ i, c i=1 := by
    simp only [c,Finset.prod_mul_distrib,Finset.prod_inv_distrib,hab,mul_inv_cancel]
  let h := diagonalSL c hc
  refine ⟨h,?_,?_⟩
  · intro i j hij; change (Matrix.diagonal (fun i => (c i:F))) i j=0
    simp [Matrix.diagonal_apply,hij]
  · rw [diagonalSL_action]
    apply MulEquiv.ext; intro g
    apply Matrix.SpecialLinearGroup.ext; intro i j
    change ((unitOdd% diagonalAut) c ((unitOdd% diagonalAut) a (fieldGraphAut phi eps g))) i j=
      ((unitOdd% diagonalAut) b (fieldGraphAut phi eps g)) i j
    rw [(unitOdd% diagonal_entry),(unitOdd% diagonal_entry),(unitOdd% diagonal_entry)]
    dsimp only [c]
    simp only [Units.val_mul,mul_inv_rev,inv_inv,Units.val_inv_eq_inv_val]
    have hi : (a i:F)≠0 := (a i).ne_zero
    have hj : (a j:F)≠0 := (a j).ne_zero
    field_simp
    <;> ring

/-- The actual p263 diagonal pattern. Its two exceptional entries absorb
all prescribed determinant obstruction; the length of the middle block
has no effect on the scalar exponent. -/
def radicalDiagonal {k : ℕ} (a : Fin (k+3) → Fˣ) (lambda : Fˣ) : Fin (k+3) → Fˣ :=
  Fin.cons lambda⁻¹ (Fin.cons (∏ i, a i) (Fin.snoc (fun _ : Fin k => 1) lambda))
private theorem radicalDiagonal_product {k : ℕ} (a : Fin (k+3) → Fˣ) (lambda : Fˣ) :
    ∏ i, radicalDiagonal a lambda i=∏ i, a i := by
  simp only [radicalDiagonal,Fin.prod_cons,Fin.prod_snoc,Finset.prod_const_one,one_mul]
  simp [mul_comm,mul_left_comm,mul_assoc]
/-- The exact determinant-one INNER correction construction used by
PartII Proposition6.7, p263. This consumes the actual determinant and full
automorphism laws above, and leaves no supplied diagonal-normalization
premise. The middle tuple is genuinely constant, even in unbounded rank.
It is the correction step, not radical VALUE coverage. -/
theorem actual_radical_inner_torus {k : ℕ} (a : Fin (k+3) → Fˣ)
    (lambda : Fˣ) (phi : RingAut F) (eps : Bool) :
    ∃ h : Matrix.SpecialLinearGroup (Fin (k+3)) F,
      (∀ i j : Fin (k+3), i≠j → h i j=0) ∧
      MulAut.conj h*PartIIProposition6_5.diagonalFieldGraph a phi eps=
        (unitOdd% diagonalAut) (radicalDiagonal a lambda)*fieldGraphAut phi eps :=
  actual_diagonal_inner_normalization a (radicalDiagonal a lambda)
    (radicalDiagonal_product a lambda) phi eps
end NikolovSegal.PartIIRadicalInnerTorus
