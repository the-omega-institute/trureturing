/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIISLnBigCellCard
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIISLnBigCellCard
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.SLnUnitriangularCard
import Mathlib.Algebra.Ring.Parity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/-! Actual type-A class-size counting for PartII Section5. The accepted
free-entry Uplus cardinality is reused; unique UL coordinates give the
group-size lower bound needed by the actual fixed-power class estimate. -/
namespace NikolovSegal.PartIISLnBigCellCard
open Matrix SLnNormalizer
universe u
variable {F : Type u} [Field F] {n : ℕ}
private abbrev tr (g : SpecialLinearGroup (Fin n) F) := SpecialLinearGroup.transpose g
private theorem tr_mul (a b : SpecialLinearGroup (Fin n) F) : tr (a*b)=tr b*tr a := by
  apply Subtype.ext
  exact Matrix.transpose_mul _ _
private theorem tr_one : tr (1 : SpecialLinearGroup (Fin n) F)=1 := by
  apply Subtype.ext
  exact Matrix.transpose_one
private theorem tr_twice (g : SpecialLinearGroup (Fin n) F) : tr (tr g)=g := by
  apply Subtype.ext
  exact Matrix.transpose_transpose _
private theorem tr_inv (g : SpecialLinearGroup (Fin n) F) : tr g⁻¹=(tr g)⁻¹ := by
  have he : tr g*tr g⁻¹=1 := by rw [← tr_mul,inv_mul_cancel,tr_one]
  calc
    _ = (tr g)⁻¹*(tr g*tr g⁻¹) := by group
    _ = _ := by rw [he,mul_one]
private def bigCell (a : Uplus n F×Uplus n F) : SpecialLinearGroup (Fin n) F :=
  a.1.val*tr a.2.val
private theorem bigCell_injective : Function.Injective (bigCell (F:=F) (n:=n)) := by
  intro a b he
  let A : Uplus n F := b.1⁻¹*a.1
  let B : Uplus n F := a.2⁻¹*b.2
  have hAB : A.val=tr B.val := by
    change b.1.val⁻¹*a.1.val=tr (a.2.val⁻¹*b.2.val)
    rw [tr_mul,tr_inv]
    change a.1.val*tr a.2.val=b.1.val*tr b.2.val at he
    calc
      _ = b.1.val⁻¹*(a.1.val*tr a.2.val)*(tr a.2.val)⁻¹ := by group
      _ = b.1.val⁻¹*(b.1.val*tr b.2.val)*(tr a.2.val)⁻¹ := by rw [he]
      _ = _ := by group
  have hA : A.val=1 := by
    apply SpecialLinearGroup.ext
    intro i j
    by_cases hij : i=j
    · subst j
      simpa only [SpecialLinearGroup.coe_one,Matrix.one_apply,ite_true] using A.prop.2 i
    · have hval : i.val≠j.val := fun h => hij (Fin.ext h)
      by_cases hlt : j.val < i.val
      · simpa only [SpecialLinearGroup.coe_one,Matrix.one_apply,if_neg hij] using A.prop.1 i j hlt
      · have hgt : i.val < j.val := by omega
        rw [hAB]
        change B.val j i=(1:Matrix (Fin n) (Fin n) F) i j
        simpa only [Matrix.one_apply,if_neg hij] using B.prop.1 j i hgt
  have hfirst : a.1.val=b.1.val := by
    calc
      _ = b.1.val*(b.1.val⁻¹*a.1.val) := by group
      _ = b.1.val := by change b.1.val*A.val=b.1.val;rw [hA,mul_one]
  have hsecond : a.2.val=b.2.val := by
    change a.1.val*tr a.2.val=b.1.val*tr b.2.val at he
    rw [hfirst] at he
    have ht := congrArg tr (mul_left_cancel he)
    simpa only [tr_twice] using ht
  exact Prod.ext (Subtype.ext hfirst) (Subtype.ext hsecond)
/-- Every field/rank, including ranks0/1: the actual group contains an
injective upper/lower unitriangular big cell of size |F|^(n(n-1)). -/
theorem actual_SLn_card_lower [Fintype F] (n : ℕ) :
    Fintype.card F^(n*(n-1))≤Nat.card (SpecialLinearGroup (Fin n) F) := by
  have h := Nat.card_le_card_of_injective (bigCell (F:=F) (n:=n)) bigCell_injective
  rw [Nat.card_prod,SLnSylow.card_Uplus,← pow_add] at h
  have hd : n*(n-1)/2+n*(n-1)/2=n*(n-1) := by
    have he := Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one n)
    omega
  rwa [hd] at h
end NikolovSegal.PartIISLnBigCellCard
