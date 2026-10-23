/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnFixedPowerClass
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnFixedPowerClass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIIFixedSLnPower
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
/-! The genuine central-quotient class-size step of PartII Section5.
Class fibres inject into the ACTUAL scalar center; no class-size or
automorphism-lifting premise is used. Uniform class width remains open. -/
namespace NikolovSegal.PartIIPSLnFixedPowerClass
open Matrix
universe u
variable {F : Type u} [Field F] {n : ℕ}
private abbrev G := SpecialLinearGroup (Fin n) F
private abbrev Q := ProjectiveSpecialLinearGroup (Fin n) F
private abbrev pi : G (F:=F) (n:=n) →* Q (F:=F) (n:=n) :=
  QuotientGroup.mk' (Subgroup.center _)
private def classMap (z : G (F:=F) (n:=n)) :
    (ConjClasses.mk z).carrier → (ConjClasses.mk (pi z)).carrier :=
  fun x => ⟨pi x.val,pi.map_isConj x.prop⟩
private theorem classMap_surjective (z : G (F:=F) (n:=n)) :
    Function.Surjective (classMap z) := by
  intro v
  have hv : IsConj (pi z) v.val := v.prop
  obtain ⟨c,hc⟩ := isConj_iff.mp hv
  obtain ⟨d,hd⟩ := QuotientGroup.mk'_surjective (Subgroup.center (G (F:=F) (n:=n))) c
  refine ⟨⟨d*z*d⁻¹,isConj_iff.mpr ⟨d,rfl⟩⟩,?_⟩
  apply Subtype.ext
  change pi (d*z*d⁻¹)=v.val
  rw [map_mul,map_mul,map_inv,hd,hc]
private theorem class_card_center [Fintype F] (z : G (F:=F) (n:=n)) :
    Nat.card (ConjClasses.mk z).carrier≤
      Nat.card (ConjClasses.mk (pi z)).carrier*Nat.card (Subgroup.center (G (F:=F) (n:=n))) := by
  classical
  choose lift hlift using classMap_surjective z
  let f : (ConjClasses.mk z).carrier →
      (ConjClasses.mk (pi z)).carrier×Subgroup.center (G (F:=F) (n:=n)) := fun x =>
    (classMap z x,⟨x.val*(lift (classMap z x)).val⁻¹,by
      rw [← QuotientGroup.ker_mk' (Subgroup.center (G (F:=F) (n:=n)))]
      change pi (x.val*(lift (classMap z x)).val⁻¹)=1
      have hh := congrArg Subtype.val (hlift (classMap z x))
      change pi (lift (classMap z x)).val=pi x.val at hh
      rw [map_mul,map_inv,hh,mul_inv_cancel]⟩)
  have hinj : Function.Injective f := by
    intro a b he
    have hfirst : classMap z a=classMap z b := congrArg Prod.fst he
    have hsecond := congrArg (fun p : (ConjClasses.mk (pi z)).carrier×Subgroup.center (G (F:=F) (n:=n)) => p.2.val) he
    change a.val*(lift (classMap z a)).val⁻¹=b.val*(lift (classMap z b)).val⁻¹ at hsecond
    rw [hfirst] at hsecond
    exact Subtype.ext (mul_right_cancel hsecond)
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hinj
private theorem center_card [Fintype F] (i : Fin n) :
    Nat.card (Subgroup.center (G (F:=F) (n:=n)))≤Fintype.card F := by
  let f : Subgroup.center (G (F:=F) (n:=n)) → F := fun a => a.val i i
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    calc
      a.val.val=Matrix.scalar (Fin n) (a.val i i) :=
        (SpecialLinearGroup.scalar_eq_self_of_mem_center a.prop i).symm
      _ = Matrix.scalar (Fin n) (b.val i i) := congrArg (Matrix.scalar (Fin n)) he
      _ = b.val.val := SpecialLinearGroup.scalar_eq_self_of_mem_center b.prop i
  simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hinj
/-- Actual simple-quotient class estimate, including characteristics2/3:
|PSLn(F)| <= |class(pi(z^q))|^16. The matrix z is the constructed fixed
long-cycle element; the scalar-center fibre loss is proved explicitly. -/
theorem actual_projective_q_power_large_class [Fintype F]
    (q r k : ℕ) (hp : k+2≤q*r) :
    Nat.card (ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F)≤
      (Nat.card (ConjClasses.mk
        (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F))
          ((PartIIFixedSLnPower.fixedElement (F:=F) (q*r) k)^q))).carrier)^16 := by
  let n := k+4*(q*r+1)+2
  let z := (PartIIFixedSLnPower.fixedElement (F:=F) (q*r) k)^q
  let A := Nat.card (ConjClasses.mk z).carrier
  let B := Nat.card (ConjClasses.mk (pi z)).carrier
  have hcenter : Nat.card (Subgroup.center (G (F:=F) (n:=n)))≤Fintype.card F := center_card 0
  have hab : A≤B*Fintype.card F :=
    (class_card_center z).trans (Nat.mul_le_mul_left B hcenter)
  have he2 : 2≤n*(2*(q*r+1)-3) := by
    have hn : 2≤n := by dsimp [n];omega
    have hq : 1≤2*(q*r+1)-3 := by omega
    simpa only [mul_one] using Nat.mul_le_mul hn hq
  have hf2 : Fintype.card F^2≤A :=
    (Nat.pow_le_pow_right Fintype.card_pos he2).trans
      (PartIIFixedSLnPower.actual_q_power_class_lower q r k (by omega))
  have hf : Fintype.card F≤B := Nat.le_of_mul_le_mul_right
    (by simpa only [pow_two] using hf2.trans hab) Fintype.card_pos
  have hquot : Nat.card (Q (F:=F) (n:=n))≤Nat.card (G (F:=F) (n:=n)) :=
    Nat.card_le_card_of_surjective pi (QuotientGroup.mk'_surjective _)
  calc
    _ ≤ Nat.card (G (F:=F) (n:=n)) := hquot
    _ ≤ A^8 := PartIIFixedSLnPower.actual_q_power_large_class q r k hp
    _ ≤ (B*Fintype.card F)^8 := Nat.pow_le_pow_left hab 8
    _ ≤ (B*B)^8 := Nat.pow_le_pow_left (Nat.mul_le_mul_left B hf) 8
    _ = B^16 := by rw [← pow_two,← pow_mul]
end NikolovSegal.PartIIPSLnFixedPowerClass
