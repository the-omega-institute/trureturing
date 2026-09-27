/- GID: D5/S3/Arith/Covering/Erdos203SixCapacity
   generality: I
   mirror-B: D5/B/S3/Arith/Covering/Erdos203SixCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Lattice.Fold]
   utility: none
   digest: Actual six-row uncovered cosets and the original modular histogram capacity -/

import D5.S3.Arith.Covering.Erdos203TorusFibers
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace D5.S3.Arith.Covering.Erdos203
open scoped BigOperators
/-- The complete rectangular transversal of the actual six-row kernel. -/
abbrev SixRect := Fin 360 × Fin 24

/-- A rectangular representative embedded in the full original torus. -/
def sixRepresentative (q : SixRect) : Torus := periodMap (q.1,q.2)
/-- Assemble a coset representative and a homogeneous-kernel element. -/
def sixAssembly (q : SixRect × sixTorus) : Torus := sixRepresentative q.1 + q.2

/-- The union of the full six-row cosets selected by the given rectangle subset. -/
def sixRegion (U : Finset SixRect) : Set Torus :=
  {z | ∃ q ∈ U, z-sixRepresentative q ∈ sixTorus}

/-- The exact gcd of the original modulus and the two restricted coefficients. -/
def restrictedGcd (i : Fin 252) : Nat :=
  Nat.gcd (rows i).e (Nat.gcd (360*(rows i).a) (228*(rows i).a+24*(rows i).b))

/-- The unchanged original linear form, reduced modulo its restricted image gcd. -/
def originalResidue (i : Fin 252) (q : SixRect) : Nat :=
  ((rows i).a*q.1.val+(rows i).b*q.2.val)%restrictedGcd i

/-- The largest original-residue histogram bucket in the selected cosets. -/
def histogramMaximum (U : Finset SixRect) (i : Fin 252) : Nat :=
  (Finset.range (restrictedGcd i)).sup (fun t => (U.filter (originalResidue i · = t)).card)

/-- Representatives missed by the first six rows at their fixed original phases. -/
def sixMissed (c : Phases) : Finset SixRect :=
  Finset.univ.filter (fun q => ∀ j : Fin 6,
    originalMap (j.castLE (by decide : 6 ≤ 252)) (sixRepresentative q) ≠
      (c (j.castLE (by decide : 6 ≤ 252)) : ZMod (rows (j.castLE (by decide : 6 ≤ 252))).e))

/-- The full torus splits into the 8,640 genuine six-row cosets. The selected cosets
are exactly the points missed by those six original phases. On any set of such cosets,
every original row has the stated histogram capacity, without a primitivity assumption.
This theorem does not yet impose the seventh row or certify the 252-row numerical gap. -/
theorem six_row_conditional_capacity : Function.Bijective sixAssembly ∧
    (∀ c : Phases, sixRegion (sixMissed c) =
      {z : Torus | ∀ j : Fin 6,
        originalMap (j.castLE (by decide : 6 ≤ 252)) z ≠
          (c (j.castLE (by decide : 6 ≤ 252)) : ZMod (rows (j.castLE (by decide : 6 ≤ 252))).e)}) ∧
    ∀ (U : Finset SixRect) (i : Fin 252) (c : ZMod (rows i).e),
      (rows i).e*8640*Nat.card {z : Torus // z ∈ sixRegion U ∧ originalMap i z=c} ≤
        period^2*restrictedGcd i*histogramMaximum U i := by
  classical
  have bij : Function.Bijective sixAssembly := by
    apply (Nat.bijective_iff_injective_and_card _).mpr
    constructor
    · rintro ⟨q,z⟩ ⟨q',z'⟩ heq
      have hd : sixRepresentative q-sixRepresentative q' ∈ sixTorus := by
        have he : sixRepresentative q-sixRepresentative q' = (z':Torus)-z := by
          change sixRepresentative q+(z:Torus)=sixRepresentative q'+(z':Torus) at heq
          exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using heq)
        rw [he]
        exact sixTorus.sub_mem z'.property z.property
      have hq : q=q' := by
        apply base_lattice_geometry.2.1.1
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        change ((q.1:ℤ),(q.2:ℤ))-((q'.1:ℤ),(q'.2:ℤ)) ∈ sixLattice
        rw [← original_six_fibers.1]
        change periodMap ((q.1:ℤ),(q.2:ℤ))-periodMap ((q'.1:ℤ),(q'.2:ℤ)) ∈ sixTorus at hd
        simpa only [AddSubgroup.mem_comap,map_sub] using hd
      subst q'
      have hz : z=z' := by
        apply Subtype.ext
        exact add_left_cancel heq
      subst z'
      rfl
    · rw [Nat.card_prod,show Nat.card SixRect=8640 by simp only [Nat.card_prod,Nat.card_fin]]
      rw [mul_comm,original_six_fibers.2.2.1]
      simp only [Nat.card_eq_fintype_card,ZMod.card, Fintype.card_prod, pow_two]
  have region (U : Finset SixRect) (q : SixRect × sixTorus) :
      sixAssembly q ∈ sixRegion U ↔ q.1 ∈ U := by
    constructor
    · rintro ⟨q',hq',hz⟩
      have eq : sixAssembly (q',⟨sixAssembly q-sixRepresentative q',hz⟩)=sixAssembly q := by
        change sixRepresentative q'+(sixAssembly q-sixRepresentative q')=sixAssembly q
        abel
      have hh := congrArg Prod.fst (bij.1 eq)
      exact hh ▸ hq'
    · intro hq
      refine ⟨q.1,hq,?_⟩
      change sixRepresentative q.1+(q.2:Torus)-sixRepresentative q.1 ∈ sixTorus
      simpa only [add_sub_cancel_left] using q.2.property
  have missed (c : Phases) (q : SixRect × sixTorus) :
      (∀ j : Fin 6, originalMap (j.castLE (by decide : 6 ≤ 252)) (sixAssembly q) ≠
        (c (j.castLE (by decide : 6 ≤ 252)) : ZMod (rows (j.castLE (by decide : 6 ≤ 252))).e)) ↔
      q.1 ∈ sixMissed c := by
    have hz (j : Fin 6) : originalMap (j.castLE (by decide : 6 ≤ 252)) q.2=0 := by
      exact (AddSubgroup.mem_iInf.mp q.2.property) j
    simp only [sixMissed,Finset.mem_filter,Finset.mem_univ,true_and,
      sixAssembly,map_add,hz,add_zero]
  refine ⟨bij,?_,?_⟩
  · intro c
    apply Set.ext
    intro z
    obtain ⟨q,rfl⟩ := bij.2 z
    exact (region (sixMissed c) q).trans (missed c q).symm
  intro U i c
  let r := rows i
  let g := restrictedGcd i
  have valid : ∀ j : Fin 252, 0<(rows j).e ∧ 0<restrictedGcd j ∧
      restrictedGcd j ∣ (rows j).e := by decide +kernel
  let : NeZero r.e := ⟨Nat.ne_of_gt (valid i).1⟩
  let : NeZero g := ⟨Nat.ne_of_gt (valid i).2.1⟩
  let reduce : ZMod r.e →+* ZMod g := ZMod.castHom (valid i).2.2 (ZMod g)
  have residue (q : SixRect) : (reduce (originalMap i (sixRepresentative q))).val =
      originalResidue i q := by
    have eq : reduce (originalMap i (sixRepresentative q)) =
        ((r.a*q.1.val+r.b*q.2.val : Nat) : ZMod g) := by
      change reduce (r.a * (ZMod.castHom _ (ZMod r.e)) (q.1.val : ZMod period) +
        r.b * (ZMod.castHom _ (ZMod r.e)) (q.2.val : ZMod period)) = _
      simp only [map_add,map_mul,map_natCast,Nat.cast_add,Nat.cast_mul]
    rw [eq,ZMod.val_natCast]
    rfl
  have compat (q : SixRect) : g ∣ (c-originalMap i (sixRepresentative q)).val ↔
      originalResidue i q=(reduce c).val := by
    have zero (v : ZMod r.e) : reduce v=0 ↔ g ∣ v.val := by
      change ZMod.castHom _ (ZMod g) v=0 ↔ _
      rw [ZMod.castHom_apply,ZMod.cast_eq_val,ZMod.natCast_eq_zero_iff]
    rw [← zero,map_sub,sub_eq_zero]
    rw [← (ZMod.val_injective g).eq_iff,eq_comm,residue]
  have card : Nat.card {z : Torus // z ∈ sixRegion U ∧ originalMap i z=c} =
      ∑ q : SixRect, Nat.card {z : sixTorus // q ∈ U ∧ originalMap i (sixAssembly (q,z))=c} := by
    let E := Equiv.ofBijective sixAssembly bij
    let S := E.subtypeEquiv (p := fun q => q.1 ∈ U ∧ originalMap i (sixAssembly q)=c)
      (q := fun z => z ∈ sixRegion U ∧ originalMap i z=c)
      (fun q => and_congr_left (fun _ => (region U q).symm))
    rw [← Nat.card_congr S]
    rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (q : SixRect) (z : sixTorus) => q ∈ U ∧
        originalMap i (sixAssembly (q,z))=c)),Nat.card_sigma]
  have per (q : SixRect) : r.e*8640*
      Nat.card {z : sixTorus // q ∈ U ∧ originalMap i (sixAssembly (q,z))=c} =
      if q ∈ U ∧ originalResidue i q=(reduce c).val then period^2*g else 0 := by
    by_cases hq : q ∈ U
    · have eq : Nat.card {z : sixTorus // q ∈ U ∧ originalMap i (sixAssembly (q,z))=c} =
          Nat.card {z : sixTorus // originalMap i (sixAssembly (q,z))=c} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun _ => and_iff_right hq))
      rw [eq]
      change r.e*8640*Nat.card {z : sixTorus //
        originalMap i (sixRepresentative q+z)=c} = _
      rw [(original_six_fibers.2.2.2 i).2.2.2]
      change (if g ∣ (c-originalMap i (sixRepresentative q)).val then period^2*g else 0)=_
      simp only [compat,hq,true_and]
    · have : IsEmpty {z : sixTorus // q ∈ U ∧ originalMap i (sixAssembly (q,z))=c} :=
        ⟨fun z => hq z.property.1⟩
      simp only [Nat.card_of_isEmpty,mul_zero,hq,false_and,if_false]
  rw [card,Finset.mul_sum]
  calc
    (∑ q : SixRect, r.e*8640*Nat.card {z : sixTorus //
        q ∈ U ∧ originalMap i (sixAssembly (q,z))=c}) =
        period^2*g*(U.filter (originalResidue i · = (reduce c).val)).card := by
      simp_rw [per]
      rw [Finset.card_filter,Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_univ U)
        (fun q _ hq => by simp only [hq, false_and, if_false])]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [hq,true_and,mul_ite,mul_one,mul_zero]
    _ ≤ period^2*g*histogramMaximum U i := by
      apply Nat.mul_le_mul_left
      exact Finset.le_sup (f := fun t => (U.filter (originalResidue i · = t)).card)
        (Finset.mem_range.mpr (ZMod.val_lt (reduce c)))

end D5.S3.Arith.Covering.Erdos203
