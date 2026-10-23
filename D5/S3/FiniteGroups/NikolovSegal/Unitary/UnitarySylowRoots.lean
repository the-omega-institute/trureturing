/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowRoots
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowRoots
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitarySylowCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace NikolovSegal.UnitarySylow
open Matrix SLnNormalizer PartIIUnitaryUpperTorus
universe u
variable {F : Type u} [Field F] {n : ℕ}

/-- The genuine field/graph action on actual SL transvections. -/
theorem steinberg_transvection (ι : RingAut F) {i j : Fin n}
    (hij : i≠j) (t : F) :
    steinberg ι (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection
        (show j.rev≠i.rev from fun h => hij (Fin.rev_injective h).symm) (-ι t) := by
  apply SpecialLinearGroup.ext
  intro r c
  rw [steinberg_entry, SpecialLinearGroup.transvection_inv]
  simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply, map_add, apply_ite, map_one, map_zero, map_neg]
  have hc : (i=c.rev ∧ j=r.rev) ↔ (j.rev=r ∧ i.rev=c) := by
    simp only [← Fin.rev_eq_iff, Fin.rev_rev, and_comm]
  simp only [hc,Fin.rev_inj,eq_comm]
  split_ifs <;> rfl

/-- Two actual transvections with disjoint multiplication positions commute. -/
theorem transvections_commute {i j k l : Fin n} (hij : i≠j) (hkl : k≠l)
    (hjk : j≠k) (hli : l≠i) (x y : F) :
    SpecialLinearGroup.transvection hij x * SpecialLinearGroup.transvection hkl y =
    SpecialLinearGroup.transvection hkl y * SpecialLinearGroup.transvection hij x := by
  apply Subtype.ext
  simp [SpecialLinearGroup.transvection_coe, mul_add, add_mul,
    single_mul_single_of_ne _ _ _ _ hjk, single_mul_single_of_ne _ _ _ _ hli,
    add_comm, add_left_comm]

/-- A paired upper root away from the middle of the anti-diagonal. -/
theorem paired_root_fixed (ι : RingAut F) (hinv : Function.Involutive ι)
    {i j : Fin n} (hij : i.val<j.val) (hi : i≠i.rev) (hj : j≠j.rev) (t : F) :
    steinberg ι
      (SpecialLinearGroup.transvection (ne_of_lt (show i<j from hij)) t *
        SpecialLinearGroup.transvection
          (show j.rev≠i.rev from Fin.rev_injective.ne (ne_of_lt (show i<j from hij)).symm)
          (-ι t)) =
      SpecialLinearGroup.transvection (ne_of_lt (show i<j from hij)) t *
        SpecialLinearGroup.transvection
          (show j.rev≠i.rev from Fin.rev_injective.ne (ne_of_lt (show i<j from hij)).symm)
          (-ι t) := by
  rw [map_mul,steinberg_transvection,steinberg_transvection]
  simp only [Fin.rev_rev,map_neg,hinv t,neg_neg]
  exact transvections_commute (i := j.rev) (j := i.rev) (k := i) (l := j)
    _ _ hi.symm hj _ _

/-- Literal matrix of the paired root, with no hidden root-group assumptions. -/
theorem paired_root_matrix {i j : Fin n} (hij : i≠j) (hj : j≠j.rev) (x y : F) :
    (SpecialLinearGroup.transvection hij x *
      SpecialLinearGroup.transvection (Fin.rev_injective.ne hij.symm) y).val =
      1 + single i j x + single j.rev i.rev y := by
  simp [SpecialLinearGroup.transvection_coe, mul_add, add_mul,
    single_mul_single_of_ne _ _ _ _ hj,add_assoc]

/-- Central long root, including characteristic two. -/
theorem central_root_fixed (ι : RingAut F) {i j : Fin n} (hij : i≠j)
    (hr : j.rev=i) (t : F) (ht : ι t = -t) :
    steinberg ι (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij t := by
  rw [steinberg_transvection]
  have hi : i.rev=j := by rw [←hr,Fin.rev_rev]
  simp [hr,hi,ht]

/-- The actual three-entry short root is a product of determinant-one transvections. -/
def shortRoot {a b c : Fin n} (hab : a≠b) (hbc : b≠c) (hac : a≠c)
    (x z y : F) : SpecialLinearGroup (Fin n) F :=
  SpecialLinearGroup.transvection hab x * SpecialLinearGroup.transvection hbc z *
    SpecialLinearGroup.transvection hac (y-x*z)

theorem shortRoot_matrix {a b c : Fin n} (hab : a≠b) (hbc : b≠c) (hac : a≠c)
    (x z y : F) : (shortRoot hab hbc hac x z y).val =
    1 + single a b x + single b c z + single a c y := by
  simp only [shortRoot, SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  simp [mul_add,add_mul,single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hab.symm,
    single_mul_single_of_ne _ _ _ _ hac.symm,
    single_mul_single_of_ne _ _ _ _ hbc.symm]
  simp only [add_assoc]
  rw [show (single a c (x*z) + single a c (y-x*z) : Matrix (Fin n) (Fin n) F) =
    single a c y by rw [←single_add]; congr 1; ring]

/-- Explicit inverse matrix of the actual short-root product. -/
theorem shortRoot_inverse_matrix {a b c : Fin n} (hab : a≠b) (hbc : b≠c) (hac : a≠c)
    (x z y : F) : (shortRoot hab hbc hac x z y)⁻¹.val =
    1 + single a b (-x) + single b c (-z) + single a c (x*z-y) := by
  simp only [shortRoot, _root_.mul_inv_rev, SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.coe_mul,SpecialLinearGroup.transvection_coe]
  simp [mul_add,add_mul,single_mul_single_of_ne _ _ _ _ hab.symm,
    single_mul_single_of_ne _ _ _ _ hac.symm,
    single_mul_single_of_ne _ _ _ _ hbc.symm]
  simp [single_neg,sub_eq_add_neg,add_comm,add_left_comm,add_assoc]

/-- Actual short-root fixedness follows from the trace equation. -/
theorem shortRoot_fixed (ι : RingAut F) (hinv : Function.Involutive ι)
    {a b c : Fin n} (hab : a≠b) (hbc : b≠c) (hac : a≠c)
    (ha : a.rev=c) (hb : b.rev=b) (x y : F)
    (hy : y+ι y=-(x*ι x)) :
    steinberg ι (shortRoot hab hbc hac x (-ι x) y) =
      shortRoot hab hbc hac x (-ι x) y := by
  have hc : c.rev=a := by rw [←ha,Fin.rev_rev]
  have hy' : ι (x*(-ι x)-y)=y := by
    rw [map_sub,map_mul,map_neg,hinv x]
    linear_combination -hy
  apply SpecialLinearGroup.ext
  intro r s
  rw [steinberg_entry,shortRoot_inverse_matrix,shortRoot_matrix]
  simp only [Matrix.add_apply,Matrix.one_apply,Matrix.single_apply,map_add]
  have hab' : (a=s.rev ∧ b=r.rev) ↔ (b=r ∧ c=s) := by
    simp only [← Fin.rev_eq_iff,Fin.rev_rev,ha,hb,and_comm]
  have hbc' : (b=s.rev ∧ c=r.rev) ↔ (a=r ∧ b=s) := by
    simp only [← Fin.rev_eq_iff,Fin.rev_rev,hb,hc,and_comm]
  have hac' : (a=s.rev ∧ c=r.rev) ↔ (a=r ∧ c=s) := by
    simp only [← Fin.rev_eq_iff,Fin.rev_rev,ha,hc,and_comm]
  simp only [hab',hbc',hac',apply_ite,map_one,map_zero,map_neg,neg_neg,hinv x,
    hy',Fin.rev_inj]
  simp only [eq_comm]
  split_ifs <;> ring

end NikolovSegal.UnitarySylow
