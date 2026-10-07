/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIISL2Semilinear
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIISL2Semilinear
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit diagonal and field actions with corrected SL2 scalar products. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIISL2Scalar
set_option autoImplicit false
/-! Actual A1 diagonal/field automorphisms and their scalar PRODUCT supply.
PartII pp241--243 and pp251,260--261: D Phi normalization is made concrete;
classification of arbitrary automorphisms is not assumed or asserted. -/
namespace NikolovSegal.PartIIA1RootSupply
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

/-- Entrywise field action on actual determinant-one matrices. -/
def fieldAut (phi : RingAut F) : MulAut SL(2,F) where
  toFun := Matrix.SpecialLinearGroup.map phi.toRingHom
  invFun := Matrix.SpecialLinearGroup.map phi.symm.toRingHom
  left_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply]
  right_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply]
  map_mul' := (Matrix.SpecialLinearGroup.map phi.toRingHom).map_mul

private def scaled (a : Fˣ) (g : SL(2,F)) : SL(2,F) :=
  ⟨!![g 0 0, (a:F)*g 0 1; (↑a⁻¹:F)*g 1 0, g 1 1], by
    rw [Matrix.det_fin_two]
    have hg := g.property
    rw [Matrix.det_fin_two] at hg
    change g 0 0*g 1 1-((a:F)*g 0 1)*((↑a⁻¹:F)*g 1 0)=1
    rw [mul_mul_mul_comm,Units.mul_inv,one_mul]
    exact hg⟩

private theorem scaled_inv (a : Fˣ) (g : SL(2,F)) : scaled a⁻¹ (scaled a g) = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp [scaled,mul_assoc,← mul_assoc]

private theorem scaled_mul (a : Fˣ) (g h : SL(2,F)) : scaled a (g*h) = scaled a g*scaled a h := by
  apply Subtype.ext
  change (scaled a (g*h)).val = (scaled a g).val * (scaled a h).val
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [scaled,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring_nf
  all_goals try simp [← mul_assoc]

/-- The diagonal outer action induced by diag(a,1), including nonsquare a. -/
def diagonalAut (a : Fˣ) : MulAut SL(2,F) where
  toFun := scaled a
  invFun := scaled a⁻¹
  left_inv := scaled_inv a
  right_inv := by intro g; simpa only [inv_inv] using scaled_inv a⁻¹ g
  map_mul' := scaled_mul a

/-- Actual normalized A1 semilinear action, with arbitrary diagonal unit. -/
def semilinearAut (a : Fˣ) (phi : RingAut F) : MulAut SL(2,F) := diagonalAut a * fieldAut phi

private theorem field_upper (phi : RingAut F) (t : F) : fieldAut phi (upper t) = upper (phi t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp [fieldAut,upper,Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,
    transvection_coe]

private theorem field_lower (phi : RingAut F) (t : F) : fieldAut phi (lower t) = lower (phi t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp [fieldAut,lower,Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,
    transvection_coe]

private theorem diagonal_upper (a : Fˣ) (t : F) : diagonalAut a (upper t) = upper ((a:F)*t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp [diagonalAut,scaled,upper,transvection_coe]

private theorem diagonal_lower (a : Fˣ) (t : F) : diagonalAut a (lower t) = lower ((↑a⁻¹:F)*t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp [diagonalAut,scaled,lower,transvection_coe]

/-- Genuine full SL2 scalar coverage for actual D Phi automorphisms, without
any prescribed-root-action or coverage hypothesis. -/
theorem actual_semilinear_SL2_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (a : Fin (4*M) → Fˣ) (phi : Fin (4*M) → RingAut F)
    (e : Fin (4*M) → ℕ) :
    PartIIScalarProductInput q (4*M) (fun j => semilinearAut (a j) (phi j)) e := by
  apply actual_normalized_SL2_scalar_product hq hM hF _ e phi phi
    (fun j => (a j:F)) (fun j => (↑(a j)⁻¹:F))
    (fun j => Units.ne_zero _) (fun j => Units.ne_zero _)
  · intro j t
    rw [semilinearAut,MulAut.mul_apply,field_upper,diagonal_upper]
  · intro j t
    rw [semilinearAut,MulAut.mul_apply,field_lower,diagonal_lower]

/-- Absorb arbitrary original inner factors into the SAME pre-target correction
chosen by the scalar theorem. This is actual Inn(SL2) D Phi supply, not a
claim that every automorphism has this form. -/
theorem actual_inner_semilinear_SL2_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (a : Fin (4*M) → Fˣ) (phi : Fin (4*M) → RingAut F)
    (g : Fin (4*M) → SL(2,F)) (e : Fin (4*M) → ℕ) :
    PartIIScalarProductInput q (4*M)
      (fun j => MulAut.conj (g j) * semilinearAut (a j) (phi j)) e := by
  intro he
  let gamma := fun j => semilinearAut (a j) (phi j)
  obtain ⟨y,hy⟩ := actual_semilinear_SL2_scalar_product hq hM hF a phi e he
  let x := fun j => y j * (gamma j).symm (g j)
  have hx : ∀ j, (MulAut.conj (g j)*gamma j)*MulAut.conj (x j)⁻¹ =
      gamma j*MulAut.conj (y j)⁻¹ := by
    intro j
    apply MulEquiv.ext
    intro z
    simp only [MulAut.mul_apply,MulAut.conj_inv_apply,MulAut.conj_apply]
    simp only [x,map_mul,map_inv,MulEquiv.apply_symm_apply]
    group
  refine ⟨x,?_⟩
  intro target
  obtain ⟨c,hc⟩ := hy target
  refine ⟨c,?_⟩
  change orderedProduct (fun j => (c j)⁻¹ *
    (((MulAut.conj (g j)*gamma j)*MulAut.conj (x j)⁻¹)^(q/e j)) (c j)) = target
  simpa only [hx] using hc
end NikolovSegal.PartIIA1RootSupply
