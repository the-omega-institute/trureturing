/- GID: D5/S3/Arith/Covering/Erdos203TorusFibers
   generality: I
   mirror-B: D5/B/S3/Arith/Covering/Erdos203TorusFibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic]
   utility: none
   digest: Exact original modular images, compatibility, and translated torus fibers -/

import D5.S3.Arith.Covering.Erdos203Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

set_option autoImplicit false

namespace D5.S3.Arith.Covering.Erdos203

/-- The full period on which every retained original row is defined. -/
abbrev Torus := ZMod period × ZMod period

/-- Simultaneous reduction of integer coordinates modulo the original period. -/
def periodMap : ℤ × ℤ →+ Torus where
  toFun z := (z.1,z.2)
  map_zero' := by simp
  map_add' x y := by simp

/-- The unchanged original row, evaluated on the full period. -/
def originalMap (i : Fin 252) : Torus →+ ZMod (rows i).e := by
  have hd : ∀ j : Fin 252, (rows j).e ∣ period := by decide +kernel
  let cast := ZMod.castHom (hd i) (ZMod (rows i).e)
  exact {
    toFun := fun z => (rows i).a*cast z.1+(rows i).b*cast z.2
    map_zero' := by simp
    map_add' := by intro x y; simp only [Prod.fst_add,Prod.snd_add,map_add]; ring }

/-- The common homogeneous kernel of the first six actual rows. -/
def sixTorus : AddSubgroup Torus :=
  ⨅ i : Fin 6, (originalMap (i.castLE (by decide : 6 ≤ 252))).ker

/-- An integer linear form used to identify the restricted image. -/
def integerForm (a b : ℤ) : ℤ × ℤ →+ ℤ where
  toFun z := a*z.1+b*z.2
  map_zero' := by simp
  map_add' := by intro x y; dsimp; ring

/-- Exact original-row images and translated fibers inside the actual six-row torus kernel.
Compatibility is certified even when the restricted coefficients are nonprimitive. -/
theorem original_six_fibers :
    sixTorus.comap periodMap = sixLattice ∧ sixTorus.index=8640 ∧
    Nat.card sixTorus*8640=period^2 ∧
    ∀ i : Fin 252,
      let r := rows i
      let g := Nat.gcd r.e (Nat.gcd (360*r.a) (228*r.a+24*r.b))
      let F := (originalMap i).comp sixTorus.subtype
      (∀ c x y : ℤ, originalMap i ((x : ZMod period),(y : ZMod period)) =
        (c : ZMod r.e) ↔ r.hits c x y) ∧
      Nat.card F.range = r.e/g ∧
      (∀ c : ZMod r.e, c ∈ F.range ↔ g ∣ c.val) ∧
      ∀ (t : Torus) (c : ZMod r.e),
        r.e*8640*Nat.card {z : sixTorus // originalMap i (t+z)=c} =
          if g ∣ (c-originalMap i t).val then period^2*g else 0 := by
  classical
  have valid : ∀ j : Fin 252, 0 < (rows j).e ∧ (rows j).e ∣ period := by decide +kernel
  have lift (j : Fin 252) (c x y : ℤ) :
      originalMap j ((x : ZMod period),(y : ZMod period))=(c : ZMod (rows j).e) ↔
        (rows j).hits c x y := by
    have eq : originalMap j ((x : ZMod period),(y : ZMod period)) =
        (((rows j).a*x+(rows j).b*y : ℤ) : ZMod (rows j).e) := by
      change (rows j).a * (ZMod.castHom (valid j).2 (ZMod (rows j).e)) (x : ZMod period) +
        (rows j).b * (ZMod.castHom (valid j).2 (ZMod (rows j).e)) (y : ZMod period) = _
      simp only [map_intCast,Int.cast_add,Int.cast_mul,Int.cast_natCast]
    rw [eq,ZMod.intCast_eq_intCast_iff]
    rfl
  have pre : sixTorus.comap periodMap = sixLattice := by
    ext z
    change (periodMap z ∈ sixTorus) ↔ _
    simp only [sixTorus,AddSubgroup.mem_iInf,AddMonoidHom.mem_ker]
    change (∀ j : Fin 6, originalMap (j.castLE (by decide : 6 ≤ 252))
      ((z.1 : ZMod period),(z.2 : ZMod period))=0) ↔ _
    have lift_zero (j : Fin 252) (x y : ℤ) :
        originalMap j ((x : ZMod period),(y : ZMod period))=0 ↔ (rows j).hits 0 x y := by
      simpa only [Int.cast_zero] using lift j 0 x y
    simp only [lift_zero]
    rw [six_row_kernel_coordinates]
    change (∃ u v : ℤ, z.1=360*u+228*v ∧ z.2=24*v) ↔
      ∃ w : ℤ × ℤ, (360*w.1+228*w.2,24*w.2)=z
    constructor
    · rintro ⟨u,v,hx,hy⟩
      exact ⟨(u,v),Prod.ext hx.symm hy.symm⟩
    · rintro ⟨⟨u,v⟩,h⟩
      exact ⟨u,v,(congrArg Prod.fst h).symm,(congrArg Prod.snd h).symm⟩
  have onto : Function.Surjective periodMap := by
    rintro ⟨x,y⟩
    obtain ⟨x,rfl⟩ := ZMod.intCast_surjective x
    obtain ⟨y,rfl⟩ := ZMod.intCast_surjective y
    exact ⟨(x,y),rfl⟩
  have mapped : sixTorus=sixLattice.map periodMap := by
    rw [← pre,AddSubgroup.map_comap_eq_self_of_surjective onto]
  have index : sixTorus.index=8640 := by
    rw [← sixTorus.index_comap_of_surjective onto,pre]
    exact base_lattice_geometry.2.2.2.1
  have size : Nat.card sixTorus*8640=period^2 := by
    have hc := sixTorus.card_mul_index
    rw [index] at hc
    have cm : Nat.card (ZMod period)=period := by
      rw [Nat.card_eq_fintype_card,ZMod.card]
    change Nat.card sixTorus*8640=period*period
    rw [Nat.card_prod,cm] at hc
    exact hc
  refine ⟨pre,index,size,?_⟩
  intro i
  let r := rows i
  have he : r.e ≠ 0 := Nat.ne_of_gt (valid i).1
  let : NeZero r.e := ⟨he⟩
  let cast : ℤ →+ ZMod r.e := Int.castAddHom (ZMod r.e)
  let α : ℤ := 360*r.a
  let β : ℤ := 228*r.a+24*r.b
  let F := (originalMap i).comp sixTorus.subtype
  have comp : (originalMap i).comp (periodMap.comp (latticeMap 360 228 24)) =
      cast.comp (integerForm α β) := by
    ext z
    change (r.a : ZMod r.e) *
        (ZMod.castHom (valid i).2 (ZMod r.e)) ((360*z.1+228*z.2 : ℤ) : ZMod period) +
      (r.b : ZMod r.e) *
        (ZMod.castHom (valid i).2 (ZMod r.e)) ((24*z.2 : ℤ) : ZMod period) =
      ((α*z.1+β*z.2 : ℤ) : ZMod r.e)
    simp only [map_intCast]
    dsimp [α,β]
    push_cast
    ring
  have range_form : (integerForm α β).range =
      AddSubgroup.zmultiples α ⊔ AddSubgroup.zmultiples β := by
    ext z
    change (∃ w : ℤ × ℤ, α*w.1+β*w.2=z) ↔ _
    simp only [Prod.exists,AddSubgroup.mem_sup,AddSubgroup.mem_zmultiples_iff,
      zsmul_eq_mul]
    constructor
    · rintro ⟨u,v,h⟩
      exact ⟨u*α,⟨u,rfl⟩,v*β,⟨v,rfl⟩,by nlinarith [h]⟩
    · rintro ⟨x,⟨u,rfl⟩,y,⟨v,rfl⟩,h⟩
      exact ⟨u,v,by simpa only [Int.cast_id,mul_comm] using h⟩
  have hrange : F.range = AddSubgroup.zmultiples (cast (Int.gcd α β : ℤ)) := by
    change ((originalMap i).comp sixTorus.subtype).range = _
    rw [AddMonoidHom.range_comp,AddSubgroup.range_subtype]
    rw [mapped]
    change ((latticeMap 360 228 24).range.map periodMap).map (originalMap i) = _
    rw [AddMonoidHom.map_range,AddMonoidHom.map_range,comp,AddMonoidHom.range_comp,
      range_form,Int.zmultiples_sup,AddMonoidHom.map_zmultiples]
  let d : ℕ := Int.gcd α β
  let g : ℕ := Nat.gcd r.e d
  have range_card : Nat.card F.range = r.e/g := by
    rw [hrange,Nat.card_zmultiples]
    change addOrderOf ((Int.gcd α β : ℤ) : ZMod r.e) = _
    rw [Int.cast_natCast,ZMod.addOrderOf_coe _ he]
  have compat : ∀ c : ZMod r.e, c ∈ F.range ↔ g ∣ c.val := by
    intro c
    have preimage : F.range.comap cast = AddSubgroup.zmultiples (g : ℤ) := by
      rw [hrange,← AddMonoidHom.map_zmultiples,AddSubgroup.comap_map_eq]
      change AddSubgroup.zmultiples (d : ℤ) ⊔ (Int.castAddHom (ZMod r.e)).ker = _
      rw [ZMod.ker_intCastAddHom,Int.zmultiples_sup]
      congr 1
      simp only [Int.gcd_natCast_natCast,Nat.gcd_comm]
      rfl
    have h : c ∈ F.range ↔ (c.val : ℤ) ∈ F.range.comap cast := by
      simp only [AddSubgroup.mem_comap,cast,Int.coe_castAddHom,
        Int.cast_natCast,ZMod.natCast_zmod_val]
    rw [h,preimage,Int.mem_zmultiples_iff,Int.natCast_dvd_natCast]
  have fibers : ∀ c : ZMod r.e,
      r.e*8640*Nat.card {z : sixTorus // F z=c} =
        if g ∣ c.val then period^2*g else 0 := by
    intro c
    by_cases hc : g ∣ c.val
    · rw [if_pos hc]
      obtain ⟨z,hz⟩ := (compat c).mpr hc
      have fiber : Nat.card {z : sixTorus // F z=c}=Nat.card F.ker := by
        subst c
        exact Nat.card_congr (F.fiberEquivKer z)
      have total : Nat.card F.ker*(r.e/g)=Nat.card sixTorus := by
        have hk := F.ker.card_mul_index
        rw [AddSubgroup.index_ker,range_card] at hk
        exact hk
      have hg : g ∣ r.e := Nat.gcd_dvd_left _ _
      rw [fiber]
      calc
        r.e*8640*Nat.card F.ker = (Nat.card F.ker*(r.e/g))*8640*g := by
          rw [mul_assoc (Nat.card F.ker*(r.e/g)) 8640 g]
          rw [show Nat.card F.ker * (r.e/g) * (8640*g) =
            (r.e/g*g)*8640*Nat.card F.ker by ring,Nat.div_mul_cancel hg]
        _ = period^2*g := by rw [total, size]
    · rw [if_neg hc]
      have : IsEmpty {z : sixTorus // F z=c} := ⟨by
        rintro ⟨z,hz⟩
        exact hc ((compat c).mp ⟨z,hz⟩)⟩
      simp
  refine ⟨lift i,range_card,compat,?_⟩
  intro t c
  have g_eq : g = Nat.gcd r.e (Nat.gcd (360*r.a) (228*r.a+24*r.b)) := by
    apply congrArg (Nat.gcd r.e)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using
      Int.gcd_natCast_natCast (360*r.a) (228*r.a+24*r.b)
  rw [← g_eq]
  simp only [map_add]
  simpa only [F, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
    eq_sub_iff_add_eq'] using fibers (c-originalMap i t)

end D5.S3.Arith.Covering.Erdos203
