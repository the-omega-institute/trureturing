/- GID: D5/S3/Arith/Covering/Erdos203SeventhCapacity
   generality: I
   mirror-B: D5/B/S3/Arith/Covering/Erdos203SeventhCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact seventh-row density and original-row capacity factors -/

import D5.S3.Arith.Covering.Erdos203SixCapacity
import Mathlib.Algebra.BigOperators.Fin
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
namespace D5.S3.Arith.Covering.Erdos203
open scoped BigOperators

def seventh : Torus →+ ZMod 11 := originalMap 6


def elevenInverse (x : ℤ) : ℤ :=
  (![0,1,6,4,3,9,2,8,7,5,10] : Fin 11 → ℤ) ⟨(x%11).toNat,by omega⟩

def elevenWitness (i : Fin 252) : ℤ × ℤ :=
  let r := rows i
  if r.e%11=0 then
    let s := elevenInverse (8640*((r.b:ℤ)-8*r.a))
    (8640*r.b*s,-8640*r.a*s)
  else
    (360*r.e*elevenInverse (360*r.e),0)

def seventhFactor (i : Fin 252) : Nat :=
  if (rows i).p=199 ∨ (rows i).p=2377 then 11 else 10

def sevenRegion (U : Finset SixRect) : Set Torus :=
  {z | z ∈ sixRegion U ∧ seventh z ≠ 0}

theorem seventh_capacity (U : Finset SixRect) :
    11*8640*Nat.card (sevenRegion U) = 10*U.card*period^2 ∧
    ∀ (j : Fin 245) (c : ZMod (rows (Fin.natAdd 7 j)).e),
      11*(rows (Fin.natAdd 7 j)).e*8640*
          Nat.card {z : Torus // z ∈ sevenRegion U ∧ originalMap (Fin.natAdd 7 j) z=c} ≤
        seventhFactor (Fin.natAdd 7 j)*period^2*restrictedGcd (Fin.natAdd 7 j)*
          histogramMaximum U (Fin.natAdd 7 j) := by
  classical
  have eleven_count (F : Set Torus) (w : Torus) (hw : seventh w=1)
      (inv : ∀ (z : Torus) (n : ℤ), z+n • w ∈ F ↔ z ∈ F) (c : ZMod 11) :
      11*Nat.card {z : Torus // z ∈ F ∧ seventh z ≠ c} =
        10*Nat.card {z : Torus // z ∈ F} := by
    classical
    have eqcard (d : ZMod 11) : Nat.card {z : Torus // z ∈ F ∧ seventh z=c} =
        Nat.card {z : Torus // z ∈ F ∧ seventh z=d} := by
      let n : ℤ := (d-c).val
      have hn : (n : ZMod 11)=d-c := by simp [n]
      apply Nat.card_congr
      refine {
        toFun := fun z => ⟨z+n • w,(inv z n).mpr z.property.1,?_⟩
        invFun := fun z => ⟨z+(-n) • w,(inv z (-n)).mpr z.property.1,?_⟩
        left_inv := ?_
        right_inv := ?_ }
      · rw [map_add,map_zsmul,hw,z.property.2,zsmul_eq_mul,mul_one,hn]
        abel
      · rw [map_add,map_zsmul,hw,z.property.2,zsmul_eq_mul,mul_one,Int.cast_neg,hn]
        abel
      · intro z
        apply Subtype.ext
        change (z : Torus)+n • w+(-n) • w=z
        simp
      · intro z
        apply Subtype.ext
        change (z : Torus)+(-n) • w+n • w=z
        simp
    let E : (Σ d : ZMod 11, {z : Torus // z ∈ F ∧ seventh z=d}) ≃ {z : Torus // z ∈ F} := {
      toFun := fun z => ⟨z.2,z.2.property.1⟩
      invFun := fun z => ⟨seventh z,⟨z,z.property,rfl⟩⟩
      left_inv := by
        rintro ⟨d,⟨z,hz,hd⟩⟩
        dsimp
        subst d
        rfl
      right_inv := by intro z; rfl }
    have all : Nat.card {z : Torus // z ∈ F} =
        11*Nat.card {z : Torus // z ∈ F ∧ seventh z=c} := by
      rw [← Nat.card_congr E,Nat.card_sigma]
      simp only [← eqcard]
      simp
    have split : Nat.card {z : Torus // z ∈ F} =
        Nat.card {z : Torus // z ∈ F ∧ seventh z=c} +
        Nat.card {z : Torus // z ∈ F ∧ seventh z≠c} := by
      have h := Fintype.card_subtype_compl (fun z : F => seventh z=c)
      simp only [← Nat.card_eq_fintype_card] at h
      have eq (P : Torus → Prop) : Nat.card {z : F // P z} =
          Nat.card {z : Torus // z∈F ∧ P z} := by
        exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun z => z∈F) P)
      rw [eq (fun z => seventh z≠c),eq (fun z => seventh z=c)] at h
      rw [all] at h
      omega
    omega
  have invariance (w : Torus) (hw : w ∈ sixTorus) (z : Torus) (n : ℤ) :
      z+n • w ∈ sixRegion U ↔ z ∈ sixRegion U := by
    have hn := sixTorus.zsmul_mem hw n
    change (∃ q ∈ U, z+n • w-sixRepresentative q ∈ sixTorus) ↔
      ∃ q ∈ U, z-sixRepresentative q ∈ sixTorus
    have eq (q : SixRect) : z+n • w-sixRepresentative q=(z-sixRepresentative q)+n • w := by abel
    simp only [eq,sixTorus.add_mem_cancel_right hn]
  have total : 8640*Nat.card (sixRegion U)=U.card*period^2 := by
    let f : (U × sixTorus) → (sixRegion U) := fun q =>
      ⟨sixRepresentative q.1+q.2,q.1,q.1.property,by simpa using q.2.property⟩
    have bij : Function.Bijective f := by
      constructor
      · rintro ⟨q,z⟩ ⟨q',z'⟩ he
        have hh : sixAssembly (q,z)=sixAssembly (q',z') := congrArg Subtype.val he
        have eq := six_row_conditional_capacity.1.1 hh
        have hq : q=q' := Subtype.ext (congrArg Prod.fst eq)
        have hz := congrArg Prod.snd eq
        exact Prod.ext hq hz
      · rintro ⟨z,q,hq,hz⟩
        refine ⟨(⟨q,hq⟩,⟨z-sixRepresentative q,hz⟩),?_⟩
        apply Subtype.ext
        change sixRepresentative q+(z-sixRepresentative q)=z
        abel
    rw [← Nat.card_congr (Equiv.ofBijective f bij),Nat.card_prod]
    have hc : Nat.card U=U.card := by simp only [Nat.card_eq_fintype_card,Fintype.card_coe]
    rw [hc,show 8640*(U.card*Nat.card sixTorus)=U.card*(Nat.card sixTorus*8640) by ring,
      original_six_fibers.2.2.1]
  have fullw : periodMap (2520,0) ∈ sixTorus ∧ seventh (periodMap (2520,0))=1 := by
    constructor
    · change (2520,0) ∈ sixTorus.comap periodMap
      rw [original_six_fibers.1]
      exact ⟨(7,0),by decide⟩
    · exact ((original_six_fibers.2.2.2 6).1 1 2520 0).mpr (by unfold Row.hits; decide)
  constructor
  · have h := eleven_count (sixRegion U) (periodMap (2520,0)) fullw.2
      (invariance _ fullw.1) 0
    change 11*Nat.card (sevenRegion U)=10*Nat.card (sixRegion U) at h
    nlinarith [congrArg (8640*·) h]
  intro j c
  let i := Fin.natAdd 7 j
  let F : Set Torus := {z | z ∈ sixRegion U ∧ originalMap i z=c}
  have cap := six_row_conditional_capacity.2.2 U i c
  by_cases ex : (rows i).p=199 ∨ (rows i).p=2377
  · have sub : Nat.card {z : Torus // z ∈ sevenRegion U ∧ originalMap i z=c} ≤
        Nat.card F := by
      apply Nat.card_le_card_of_injective (f := fun z => ⟨z,z.property.1.1,z.property.2⟩)
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : F => (z : Torus)) h
    change _ ≤ seventhFactor i*period^2*restrictedGcd i*histogramMaximum U i
    simp only [seventhFactor,if_pos ex]
    change Nat.card {z : Torus // z ∈ sevenRegion U ∧ originalMap i z=c} ≤
      Nat.card {z : Torus // z ∈ sixRegion U ∧ originalMap i z=c} at sub
    have hh := Nat.mul_le_mul_left 11
      ((Nat.mul_le_mul_left ((rows i).e*8640) sub).trans cap)
    convert hh using 1 <;> ring
  · have valid : ∀ k : Fin 245,
        ¬ ((rows (Fin.natAdd 7 k)).p=199 ∨ (rows (Fin.natAdd 7 k)).p=2377) →
        (∀ t : Fin 6, (rows (t.castLE (by decide : 6 ≤ 252))).hits 0
          (elevenWitness (Fin.natAdd 7 k)).1 (elevenWitness (Fin.natAdd 7 k)).2) ∧
        (rows (Fin.natAdd 7 k)).hits 0 (elevenWitness (Fin.natAdd 7 k)).1
          (elevenWitness (Fin.natAdd 7 k)).2 ∧
        (rows 6).hits 1 (elevenWitness (Fin.natAdd 7 k)).1
          (elevenWitness (Fin.natAdd 7 k)).2 := by unfold Row.hits; decide +kernel
    let w := periodMap (elevenWitness i)
    have wh : w ∈ sixTorus ∧ originalMap i w=0 ∧ seventh w=1 := by
      obtain ⟨h0,h1,h2⟩ := valid j ex
      refine ⟨?_,?_,?_⟩
      · apply AddSubgroup.mem_iInf.mpr
        intro t
        change originalMap (t.castLE (by decide : 6 ≤ 252)) w=0
        simpa only [w,i,periodMap,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Int.cast_zero] using ((original_six_fibers.2.2.2 _).1 0 _ _).mpr (h0 t)
      · simpa only [w,i,periodMap,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Int.cast_zero] using ((original_six_fibers.2.2.2 i).1 0 _ _).mpr h1
      · exact ((original_six_fibers.2.2.2 6).1 1 _ _).mpr h2
    have invF (z : Torus) (n : ℤ) : z+n • w ∈ F ↔ z ∈ F := by
      change (_ ∧ _) ↔ (_ ∧ _)
      rw [invariance w wh.1, map_add,map_zsmul,wh.2.1,zsmul_zero,add_zero]
    have count := eleven_count F w wh.2.2 invF 0
    have cards : Nat.card {z : Torus // z ∈ F ∧ seventh z≠0} =
        Nat.card {z : Torus // z ∈ sevenRegion U ∧ originalMap i z=c} := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro z
      exact and_right_comm
    rw [cards] at count
    change _ ≤ seventhFactor i*period^2*restrictedGcd i*histogramMaximum U i
    simp only [seventhFactor,if_neg ex]
    dsimp [F] at count
    nlinarith [congrArg ((rows i).e*8640*·) count]
end D5.S3.Arith.Covering.Erdos203
