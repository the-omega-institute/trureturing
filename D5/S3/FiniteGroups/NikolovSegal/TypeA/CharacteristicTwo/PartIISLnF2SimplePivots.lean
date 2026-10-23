/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2SimplePivots
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2SimplePivots
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIISLnF2TransvectionRecognition
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnF2Bare
open Matrix NikolovSegal.SLnRootAction NikolovSegal.SLnFullGroup
open NikolovSegal.SLnNormalizer NikolovSegal.SLnF2Residual
universe u
variable {F : Type u} [Field F] [Fintype F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

abbrev simpleEntry (g : G) (i : Fin (n-1)) : F :=
  g.val (simpleRoot i).val.1 (simpleRoot i).val.2

theorem deviation_zero_le (g : G) (hg : g ∈ Uplus n F) (a b : Fin n)
    (hab : b.val ≤ a.val) : deviation g a b=0 := by
  rcases lt_or_eq_of_le hab with hab|hab
  · have hne : a ≠ b := by intro he; subst b; omega
    simp [deviation,Matrix.sub_apply,hg.1 a b hab,Matrix.one_apply,hne]
  · have he : b=a := Fin.ext hab
    subst b
    simp [deviation,Matrix.sub_apply,hg.2 a]

theorem deviation_simple (g : G) (i : Fin (n-1)) :
    deviation g (simpleRoot i).val.1 (simpleRoot i).val.2=simpleEntry g i := by
  simp [deviation,Matrix.sub_apply,Matrix.one_apply,ne_of_lt (simpleRoot i).property]

/-- A genuine rank-one upper-unitriangular matrix has at most one nonzero
simple-root pivot, including characteristic two. -/
theorem minor_simple_unique (g : G) (hg : g ∈ Uplus n F)
    (hm : ∀ a b d e, deviation g a b*deviation g d e=deviation g a e*deviation g d b)
    (i j : Fin (n-1)) (hi : simpleEntry g i ≠ 0) (hj : simpleEntry g j ≠ 0) : i=j := by
  have hdisj : ∀ a b : Fin (n-1), a<b → simpleEntry g a=0 ∨ simpleEntry g b=0 := by
    intro a b hab
    have he := hm (simpleRoot a).val.1 (simpleRoot a).val.2
      (simpleRoot b).val.1 (simpleRoot b).val.2
    have hz := deviation_zero_le g hg (simpleRoot b).val.1 (simpleRoot a).val.2 (by
      change a.val+1 ≤ b.val; change a.val<b.val at hab; omega)
    rw [deviation_simple,deviation_simple,hz,mul_zero] at he
    exact mul_eq_zero.mp he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h|h
  · rcases hdisj i j h with he|he
    · exact hi he
    · exact hj he
  · rcases hdisj j i h with he|he
    · exact hj he
    · exact hi he

/-- Literal simple coordinates add under multiplication of actual U matrices. -/
theorem simpleEntry_mul (g h : G) (hg : g ∈ Uplus n F) (hh : h ∈ Uplus n F)
    (i : Fin (n-1)) : simpleEntry (g*h) i=simpleEntry g i+simpleEntry h i := by
  let a := (simpleRoot i).val.1
  let b := (simpleRoot i).val.2
  have hab : a ≠ b := ne_of_lt (simpleRoot i).property
  change (g.val*h.val) a b=g.val a b+h.val a b
  rw [Matrix.mul_apply]
  have he : ∑ k : Fin n, g.val a k*h.val k b=g.val a a*h.val a b+g.val a b*h.val b b := by
    apply Finset.sum_eq_add_of_mem a b (Finset.mem_univ _) (Finset.mem_univ _) hab
    intro k _ ⟨hka,hkb⟩
    by_cases hlt : k.val<a.val
    · rw [hg.1 a k hlt,zero_mul]
    · have hgt : b.val<k.val := by
        have hkav : k.val ≠ a.val := fun he => hka (Fin.ext he)
        have hkbv : k.val ≠ b.val := fun he => hkb (Fin.ext he)
        change k.val ≠ i.val+1 at hkbv
        change i.val+1<k.val
        change ¬ (k.val < i.val) at hlt
        change k.val ≠ i.val at hkav
        omega
      rw [hh.1 k b hgt,mul_zero]
  rw [he,hg.2 a,hh.2 b,one_mul,mul_one,add_comm]

/-- Subgroup form of the accepted simple-root generation argument. It
consumes the accepted Gaussian U generation and actual commutator relation. -/
theorem Uplus_le_of_simple_roots (H : Subgroup G)
    (hs : ∀ i : Fin (n-1), ∀ t : F, root (simpleRoot i) t ∈ H) : Uplus n F ≤ H := by
  apply Uplus_le_of_roots
  have hall : ∀ d : ℕ, ∀ (i j : Fin n) (hij : i<j), j.val-i.val=d →
      ∀ t : F, root ⟨(i,j),hij⟩ t ∈ H := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i j hij hd t
      by_cases hadj : j.val=i.val+1
      · let a : Fin (n-1) := ⟨i.val,by have hb:=j.isLt; omega⟩
        have he : simpleRoot a=(⟨(i,j),hij⟩ : PositiveIndex n) :=
          Subtype.ext (Prod.ext (Fin.ext rfl) (Fin.ext hadj.symm))
        rw [← he]; exact hs a t
      · let k : Fin n := ⟨j.val-1,by have hb:=j.isLt; omega⟩
        have hik : i<k := by change i.val<j.val-1; change i.val<j.val at hij; omega
        have hkj : k<j := by change j.val-1<j.val; change i.val<j.val at hij; omega
        have h1 := ih (k.val-i.val) (by dsimp [k]; change i.val<j.val at hij; omega) i k hik rfl t
        have h2 := ih (j.val-k.val) (by dsimp [k]; change i.val<j.val at hij; omega) k j hkj rfl 1
        have hc := transvection_commutator_chain hik hkj t (1:F)
        rw [mul_one] at hc
        change root ⟨(i,k),hik⟩ t*root ⟨(k,j),hkj⟩ 1*(root ⟨(i,k),hik⟩ t)⁻¹*
          (root ⟨(k,j),hkj⟩ 1)⁻¹=root ⟨(i,j),hij⟩ t at hc
        rw [← hc]
        exact H.mul_mem (H.mul_mem (H.mul_mem h1 h2) (H.inv_mem h1)) (H.inv_mem h2)
  intro r t
  exact hall _ r.val.1 r.val.2 r.property rfl t

noncomputable def simpleCoordinate (i : Fin (n-1)) : Uplus n F →* Multiplicative F where
  toFun g := Multiplicative.ofAdd (simpleEntry g.val i)
  map_one' := by simp [simpleEntry,Matrix.one_apply,ne_of_lt (simpleRoot i).property]
  map_mul' g h := by
    change Multiplicative.ofAdd (simpleEntry (g.val*h.val) i)=
      Multiplicative.ofAdd (simpleEntry g.val i+simpleEntry h.val i)
    rw [simpleEntry_mul g.val h.val g.property h.property]

/-- Surjectivity on actual U and its genuine simple-root generation imply
that every target simple coordinate occurs in an actual simple-root image. -/
theorem simple_image_column_coverage (hF : Fintype.card F=2) (alpha : MulAut G)
    (hU : (Uplus n F).map alpha.toMonoidHom=Uplus n F) (j : Fin (n-1)) :
    ∃ i : Fin (n-1), simpleEntry (alpha (root (simpleRoot i) 1)) j ≠ 0 := by
  classical
  by_contra hno
  have hz : ∀ i : Fin (n-1), simpleEntry (alpha (root (simpleRoot i) 1)) j=0 := by simpa using hno
  let aU : MulAut (Uplus n F) := (alpha.subgroupMap (Uplus n F)).trans (MulEquiv.subgroupCongr hU)
  let f := (simpleCoordinate (F := F) j).comp aU.toMonoidHom
  let H : Subgroup G := f.ker.map (Uplus n F).subtype
  have hsimple : ∀ i : Fin (n-1), ∀ t : F, root (simpleRoot i) t ∈ H := by
    intro i t
    refine ⟨⟨root (simpleRoot i) t,root_mem_Uplus _ _⟩,?_,rfl⟩
    change Multiplicative.ofAdd (simpleEntry (alpha (root (simpleRoot i) t)) j)=1
    rcases eq_zero_or_one hF t with ht|ht
    · subst t; simp [root,simpleEntry,Matrix.one_apply,ne_of_lt (simpleRoot j).property]
    · subst t; rw [hz]; rfl
  have hgen := Uplus_le_of_simple_roots H hsimple
  let target : Uplus n F := ⟨root (simpleRoot j) 1,root_mem_Uplus _ _⟩
  obtain ⟨x,hx⟩ := aU.surjective target
  have hxH := hgen x.property
  obtain ⟨y,hy,he⟩ := hxH
  have hyx : y=x := Subtype.ext he
  subst y
  have hzero : simpleEntry (alpha x.val) j=0 := by
    change Multiplicative.ofAdd (simpleEntry (alpha x.val) j)=1 at hy
    exact congrArg Multiplicative.toAdd hy
  have htarget : alpha x.val=root (simpleRoot j) 1 := congrArg Subtype.val hx
  rw [htarget] at hzero
  simp [simpleEntry,root,SpecialLinearGroup.transvection_coe,Matrix.one_apply,
    Matrix.single_apply,ne_of_lt (simpleRoot j).property] at hzero

/-- Every normalized bare automorphism has a genuine permutation of all
simple pivots. No root-subgroup-image premise is introduced. -/
theorem normalized_simple_pivot_permutation (hF : Fintype.card F=2) (hn : 4<n)
    (alpha : MulAut G) (hU : (Uplus n F).map alpha.toMonoidHom=Uplus n F) :
    ∃ sigma : Equiv.Perm (Fin (n-1)), ∀ i,
      simpleEntry (alpha (root (simpleRoot i) 1)) (sigma i)=1 ∧
      ∀ j, j ≠ sigma i → simpleEntry (alpha (root (simpleRoot i) 1)) j=0 := by
  classical
  have hmem : ∀ i : Fin (n-1), alpha (root (simpleRoot i) (1:F)) ∈ Uplus n F := by
    intro i; rw [← hU]; exact Subgroup.mem_map_of_mem _ (root_mem_Uplus _ _)
  have huniq : ∀ i j k : Fin (n-1),
      simpleEntry (alpha (root (simpleRoot i) 1)) j ≠ 0 →
      simpleEntry (alpha (root (simpleRoot i) 1)) k ≠ 0 → j=k := by
    intro i j k hj hk
    exact minor_simple_unique _ (hmem i)
      (normalized_transvection_image_minors hF hn alpha hU _ _ _) j k hj hk
  choose f hf using simple_image_column_coverage hF alpha hU
  have hinj : Function.Injective f := by
    intro j k he
    apply huniq (f j) j k (hf j)
    simpa only [← he] using hf k
  let e : Equiv.Perm (Fin (n-1)) := Equiv.ofBijective f ⟨hinj,Finite.surjective_of_injective hinj⟩
  refine ⟨e.symm,?_⟩
  intro i
  have hone : simpleEntry (alpha (root (simpleRoot i) 1)) (e.symm i) ≠ 0 := by
    have hh := hf (e.symm i)
    change simpleEntry (alpha (root (simpleRoot (e (e.symm i))) 1)) (e.symm i) ≠ 0 at hh
    simpa only [e.apply_symm_apply] using hh
  refine ⟨(eq_zero_or_one hF _).resolve_left hone,?_⟩
  intro j hj
  by_contra hz
  exact hj (huniq i j (e.symm i) hz hone)

end NikolovSegal.SLnF2Bare
