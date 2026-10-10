/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedDetOneTransport
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedDetOneTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIISupportedBlockExtraction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace NikolovSegal.PartIISupportedClassTransport
open Matrix Equiv PartIISLnDisplacedClassWords
universe u
variable {F : Type u} [Field F] {N d : ℕ}
local notation "G" => SpecialLinearGroup (Fin N) F

/-- An actual unused coordinate exists from the strict cardinal bound. -/
theorem exists_outside_embedding (e : Fin d ↪ Fin N) (h : d<N) : ∃ j, j∉Set.range e := by
  by_contra hno
  have hall : ∀ x : Fin N, ∃ y : Fin d, e y=x := by simpa using hno
  have hs : Function.Surjective e := fun x => hall x
  have hc := Fintype.card_le_of_surjective e hs
  simp only [Fintype.card_fin] at hc
  omega

/-- Scaling an unused coordinate commutes with the genuine supported
matrix, rather than assuming a determinant-one transport oracle. -/
theorem outside_scalar_commutes (T : Set (Fin N)) (a : G) (ha : Supported T a)
    (j : Fin N) (hj : j∉T) (t : Fˣ) :
    (supportKernel% scalarAt) j t*a.val=a.val*(supportKernel% scalarAt) j t := by
  classical
  change Matrix.diagonal (fun x => if x=j then (t:F) else 1)*a.val=
    a.val*Matrix.diagonal (fun x => if x=j then (t:F) else 1)
  ext r c
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hr : r=j
  · subst r
    rw [ha j c (Or.inl hj)]
    by_cases hc : c=j
    · subst c; simp
    · simp [hc,Ne.symm hc,Matrix.one_apply]
  · by_cases hc : c=j
    · subst c
      rw [ha r j (Or.inr hj)]
      simp [hr,Matrix.one_apply]
    · simp [hr,hc]

/-- Every coordinate permutation of a supported target is realized by a
GENUINE determinant-one matrix. A single unused diagonal coordinate
corrects the permutation determinant and leaves the target unchanged. -/
theorem supported_permutation_SL_transport (T : Set (Fin N)) (a b : G)
    (ha : Supported T a) (j : Fin N) (hj : j∉T) (sigma : Perm (Fin N))
    (hab : ∀ i l, b (sigma i) (sigma l)=a i l) :
    ∃ c : G, (MulAut.conj c) b=a := by
  classical
  let t : Fˣ := (Units.map (Int.castRingHom F).toMonoidHom) (Perm.sign sigma)
  let P : Matrix (Fin N) (Fin N) F := (cycleClass% pMatrix) sigma
  let Q : Matrix (Fin N) (Fin N) F := (cycleClass% pMatrix) sigma⁻¹
  let D := (supportKernel% scalarAt) j t⁻¹
  let E := (supportKernel% scalarAt) j t
  have hPQ : P*Q=1 := by
    dsimp [P,Q]
    rw [(cycleClass% pMatrix_mul),inv_mul_cancel,(cycleClass% pMatrix_one)]
  have hDE : D*E=1 := (supportKernel% scalarAt_inverse) j t⁻¹
  have hED : E*D=1 := (supportKernel% scalarAt_inverse) j t
  have hdet : det (D*P)=1 := by
    rw [det_mul,(supportKernel% scalarAt_det),(cycleClass% pMatrix_det)]
    change ((t⁻¹:Fˣ):F)*(t:F)=1
    simp
  let c : G := ⟨D*P,hdet⟩
  have hinv : c⁻¹.val=Q*E := by
    have hh : c.val*(Q*E)=1 := by
      change (D*P)*(Q*E)=1
      rw [mul_assoc,← mul_assoc P Q E,hPQ,one_mul,hDE]
    have hcc : c⁻¹.val*c.val=1 := congrArg Subtype.val (inv_mul_cancel c)
    calc c⁻¹.val=c⁻¹.val*(c.val*(Q*E)) := by rw [hh,mul_one]
         _ = Q*E := by rw [← mul_assoc,hcc,one_mul]
  have hconj : P*b.val*Q=a.val := by
    change ((sigma.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) F)*b.val*
      (sigma⁻¹.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) F))= _
    rw [PEquiv.toMatrix_toPEquiv_mul,PEquiv.mul_toMatrix_toPEquiv]
    ext i l
    exact hab i l
  have hDa : D*a.val=a.val*D := outside_scalar_commutes T a ha j hj t⁻¹
  refine ⟨c,?_⟩
  apply Subtype.ext
  change (c*b*c⁻¹).val=a.val
  rw [SpecialLinearGroup.coe_mul,SpecialLinearGroup.coe_mul,hinv]
  change (D*P)*b.val*(Q*E)=a.val
  calc
    _ = D*(P*b.val*Q)*E := by simp only [mul_assoc]
    _ = D*a.val*E := by rw [hconj]
    _ = a.val := by rw [hDa,mul_assoc,hDE,mul_one]

/-- Native extension of the precise first-block coordinate correspondence,
with literal support recovery for both matrices. -/
theorem supported_coordinate_SL_transport (e f : Fin d ↪ Fin N)
    (hN : d<N) (a b : G) (ha : Supported (Set.range e) a)
    (hb : Supported (Set.range f) b) (hab : ∀ i j, b (f i) (f j)=a (e i) (e j)) :
    ∃ c : G, (MulAut.conj c) b=a := by
  classical
  obtain ⟨sigma,hs⟩ := Perm.exists_extending_pair e f e.injective f.injective
  obtain ⟨j,hj⟩ := exists_outside_embedding e hN
  apply supported_permutation_SL_transport (Set.range e) a b ha j hj sigma
  intro i l
  have hrange : ∀ i : Fin N, sigma i∈Set.range f ↔ i∈Set.range e := by
    intro i
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨x,sigma.injective ((hs x).trans hx)⟩
    · rintro ⟨x,rfl⟩
      exact ⟨x,(hs x).symm⟩
  by_cases hi : i∈Set.range e
  · by_cases hl : l∈Set.range e
    · obtain ⟨i,rfl⟩ := hi; obtain ⟨l,rfl⟩ := hl
      rw [hs,hs,hab]
    · rw [hb _ _ (Or.inr (mt (hrange l).mp hl)),ha _ _ (Or.inr hl)]
      simp only [Matrix.one_apply,sigma.injective.eq_iff]
  · rw [hb _ _ (Or.inl (mt (hrange i).mp hi)),ha _ _ (Or.inl hi)]
    simp only [Matrix.one_apply,sigma.injective.eq_iff]

end NikolovSegal.PartIISupportedClassTransport
