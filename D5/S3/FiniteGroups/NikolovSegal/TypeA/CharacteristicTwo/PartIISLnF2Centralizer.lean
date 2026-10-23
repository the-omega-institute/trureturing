/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2Centralizer
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2Centralizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnBareFullGroupClassification
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIIPSLnBareFullGroupClassification
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnF2Residual
open Matrix NikolovSegal.SLnRootAction NikolovSegal.SLnFullGroup
open NikolovSegal.SLnNormalizer
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

/-- A true two-element field consists exactly of zero and one. -/
theorem eq_zero_or_one [Fintype F] (hF : Fintype.card F=2) (x : F) : x=0 ∨ x=1 := by
  classical
  have hs : ({0,1}:Finset F)=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le
    · simp
    · simp [hF,zero_ne_one]
  have hx : x ∈ ({0,1}:Finset F) := by rw [hs]; exact Finset.mem_univ x
  simpa using hx

/-- The discrepancy of an actual U-pointwise automorphism centralizes every
other positive root. This has no torus or field-size hypothesis. -/
theorem discrepancy_commutes (gamma : MulAut G)
    (hU : ∀ x ∈ Uplus n F, gamma x=x) (r : PositiveIndex n)
    (hr : r.val.2.val=r.val.1.val+1) (t : F) :
    ∀ s : PositiveIndex n, s ≠ r →
      (gamma (negativeRoot r t)*(negativeRoot r t)⁻¹)*root s 1=
        root s 1*(gamma (negativeRoot r t)*(negativeRoot r t)⁻¹) := by
  let g := negativeRoot r t
  intro s hsr
  have hy : g⁻¹*root s 1*g ∈ Uplus n F := by
    simpa only [g,negativeRoot,SpecialLinearGroup.transvection_inv,inv_inv,neg_neg] using
      negative_simple_conjugate_mem_U r s hr hsr (-t) (1:F)
  have he : (gamma g)⁻¹*root s 1*gamma g=g⁻¹*root s 1*g := by
    simpa only [map_mul,map_inv,hU (root s 1) (root_mem_Uplus s 1)] using hU _ hy
  calc
    _ = gamma g*(g⁻¹*root s 1*g)*g⁻¹ := by dsimp [g]; group
    _ = gamma g*((gamma g)⁻¹*root s 1*gamma g)*g⁻¹ := by rw [← he]
    _ = _ := by dsimp [g]; group

/-- Deleting one edge of the actual positive-root graph still equates all
centralizer diagonal entries, in rank>=3. -/
theorem centralizer_diagonals (hn : 2 < n) (r : PositiveIndex n) (h : G)
    (hc : ∀ s : PositiveIndex n, s ≠ r → h*root s 1=root s 1*h) :
    ∀ a b : Fin n, h.val a a=h.val b b := by
  obtain ⟨k,hki,hkj⟩ := Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 hn
  have he : ∀ a : Fin n, h.val a a=h.val k k := by
    intro a
    by_cases ha : a=k
    · rw [ha]
    rcases lt_or_gt_of_ne ha with ha|ha
    · let s : PositiveIndex n := ⟨(a,k),ha⟩
      have hsr : s ≠ r := fun he => hkj (congrArg (fun x : PositiveIndex n => x.val.2) he)
      exact commute_transvection_diagonal h a k (ne_of_lt ha) (hc s hsr)
    · let s : PositiveIndex n := ⟨(k,a),ha⟩
      have hsr : s ≠ r := fun he => hki (congrArg (fun x : PositiveIndex n => x.val.1) he)
      exact (commute_transvection_diagonal h k a (ne_of_lt ha) (hc s hsr)).symm
  intro a b
  exact (he a).trans (he b).symm

/-- In F2 the same centralizer has unit diagonal, derived from determinant one
and the two-element field, rather than from the nonexistent torus. -/
theorem F2_centralizer_diagonal [Fintype F] (hF : Fintype.card F=2)
    (hn : 2 < n) (r : PositiveIndex n) (h : G)
    (hc : ∀ s : PositiveIndex n, s ≠ r → h*root s 1=root s 1*h) :
    ∀ a : Fin n, h.val a a=1 := by
  obtain ⟨v,hvi,hvj⟩ := Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 hn
  let s : PositiveIndex n := if hv : v < r.val.1 then ⟨(v,r.val.1),hv⟩
    else ⟨(r.val.1,v),lt_of_le_of_ne (le_of_not_gt hv) hvi.symm⟩
  have hsr : s ≠ r := by
    dsimp only [s]
    split_ifs with hv
    · intro he; exact hvi (congrArg (fun x : PositiveIndex n => x.val.1) he)
    · intro he; exact hvj (congrArg (fun x : PositiveIndex n => x.val.2) he)
  have hnz := commuting_root_diagonal_nonzero h s (hc s hsr)
  have hone : h.val s.val.2 s.val.2=1 := (eq_zero_or_one hF _).resolve_left hnz
  intro a
  exact (centralizer_diagonals hn r h hc a s.val.2).trans hone

/-- For an interior simple root, its other-positive-root centralizer in F2 is
EXACTLY a possible top-right transvection, in every rank>=5. -/
theorem interior_centralizer_shape [Fintype F] (hF : Fintype.card F=2)
    (hn : 4 < n) (r : PositiveIndex n)
    (hi : 0 < r.val.1.val) (hj : r.val.2.val+1 < n) (h : G)
    (hc : ∀ s : PositiveIndex n, s ≠ r → h*root s 1=root s 1*h) :
    let first : Fin n := ⟨0,by omega⟩
    let last : Fin n := ⟨n-1,by omega⟩
    h.val=1+Matrix.single first last (h.val first last) := by
  classical
  let first : Fin n := ⟨0,by omega⟩
  let last : Fin n := ⟨n-1,by omega⟩
  have hd := F2_centralizer_diagonal hF (by omega) r h hc
  have hz : ∀ a b : Fin n, a ≠ b → ¬(a=first ∧ b=last) → h.val a b=0 := by
    intro a b hab hp
    by_cases hbl : b=last
    · have haf : a ≠ first := fun he => hp ⟨he,hbl⟩
      have hfa : first < a := by
        have hv : a.val ≠ 0 := fun he => haf (Fin.ext he)
        change 0 < a.val
        omega
      let s : PositiveIndex n := ⟨(first,a),hfa⟩
      have hsr : s ≠ r := by
        intro he
        have hv := congrArg (fun x : PositiveIndex n => x.val.1.val) he
        change 0=r.val.1.val at hv
        omega
      exact commute_transvection_row h first a (ne_of_lt hfa) (hc s hsr) b hab.symm
    · have hblt : b < last := by
        have hv : b.val ≠ n-1 := fun he => hbl (Fin.ext he)
        change b.val < n-1
        have hb := b.isLt; omega
      let s : PositiveIndex n := ⟨(b,last),hblt⟩
      have hsr : s ≠ r := by
        intro he
        have hv := congrArg (fun x : PositiveIndex n => x.val.2.val) he
        change n-1=r.val.2.val at hv
        omega
      exact commute_transvection_column h b last (ne_of_lt hblt) (hc s hsr) a hab
  change h.val=1+Matrix.single first last (h.val first last)
  ext a b
  by_cases hab : a=b
  · subst b
    have hp : ¬(first=a ∧ last=a) := by
      rintro ⟨ha,hb⟩
      have hv := congrArg Fin.val (ha.trans hb.symm)
      dsimp [first,last] at hv; omega
    simp [hd a,Matrix.single_apply,hp]
  · by_cases hp : a=first ∧ b=last
    · rcases hp with ⟨rfl,rfl⟩; simp [Matrix.one_apply,hab]
    · have hp' : ¬(first=a ∧ last=b) := by
        rintro ⟨ha,hb⟩; exact hp ⟨ha.symm,hb.symm⟩
      simp [Matrix.one_apply,Matrix.single_apply,hab,hp',hz a b hab hp]

/-- At the first simple root, precisely two top-right entries can remain. -/
theorem first_centralizer_shape [Fintype F] (hF : Fintype.card F=2)
    (hn : 4 < n) (r : PositiveIndex n) (hi : r.val.1.val=0)
    (hr : r.val.2.val=r.val.1.val+1) (h : G)
    (hc : ∀ s : PositiveIndex n, s ≠ r → h*root s 1=root s 1*h) :
    let first : Fin n := ⟨0,by omega⟩
    let last : Fin n := ⟨n-1,by omega⟩
    h.val=1+Matrix.single first last (h.val first last)+
      Matrix.single r.val.2 last (h.val r.val.2 last) := by
  classical
  let first : Fin n := ⟨0,by omega⟩
  let last : Fin n := ⟨n-1,by omega⟩
  have hd := F2_centralizer_diagonal hF (by omega) r h hc
  have hfl : first ≠ last := by intro he; have hv:=congrArg Fin.val he; dsimp [first,last] at hv; omega
  have hjl : r.val.2 ≠ last := by intro he; have hv:=congrArg Fin.val he; dsimp [last] at hv; omega
  have hfj : first ≠ r.val.2 := by intro he; have hv:=congrArg Fin.val he; dsimp [first] at hv; omega
  have hz : ∀ a b : Fin n, a ≠ b → ¬(a=first ∧ b=last) →
      ¬(a=r.val.2 ∧ b=last) → h.val a b=0 := by
    intro a b hab hp hq
    by_cases hbl : b=last
    · have haf : a ≠ first := fun he => hp ⟨he,hbl⟩
      have haj : a ≠ r.val.2 := fun he => hq ⟨he,hbl⟩
      have hfa : first < a := by
        have hv : a.val ≠ 0 := fun he => haf (Fin.ext he)
        change 0 < a.val; omega
      let s : PositiveIndex n := ⟨(first,a),hfa⟩
      have hsr : s ≠ r := fun he => haj (congrArg (fun x : PositiveIndex n => x.val.2) he)
      exact commute_transvection_row h first a (ne_of_lt hfa) (hc s hsr) b hab.symm
    · have hblt : b < last := by
        have hv : b.val ≠ n-1 := fun he => hbl (Fin.ext he)
        change b.val < n-1
        have hb := b.isLt; omega
      let s : PositiveIndex n := ⟨(b,last),hblt⟩
      have hsr : s ≠ r := by
        intro he; have hv:=congrArg (fun x : PositiveIndex n => x.val.2.val) he
        change n-1=r.val.2.val at hv; omega
      exact commute_transvection_column h b last (ne_of_lt hblt) (hc s hsr) a hab
  change h.val=1+Matrix.single first last (h.val first last)+
    Matrix.single r.val.2 last (h.val r.val.2 last)
  ext a b
  by_cases hab : a=b
  · subst b
    have hp : ¬(first=a ∧ last=a) := fun ⟨ha,hb⟩ => hfl (ha.trans hb.symm)
    have hq : ¬(r.val.2=a ∧ last=a) := fun ⟨ha,hb⟩ => hjl (ha.trans hb.symm)
    simp [hd a,Matrix.single_apply,hp,hq]
  · by_cases hp : a=first ∧ b=last
    · rcases hp with ⟨rfl,rfl⟩; simp [Matrix.one_apply,Matrix.single_apply,hab,hfj.symm]
    · by_cases hq : a=r.val.2 ∧ b=last
      · rcases hq with ⟨rfl,rfl⟩; simp [Matrix.one_apply,Matrix.single_apply,hab,hfj]
      · have hp' : ¬(first=a ∧ last=b) := by simpa only [eq_comm] using hp
        have hq' : ¬(r.val.2=a ∧ last=b) := by simpa only [eq_comm] using hq
        simp [Matrix.one_apply,Matrix.single_apply,hab,hp',hq',hz a b hab hp hq]

/-- At the last simple root, precisely two top-right entries can remain. -/
theorem last_centralizer_shape [Fintype F] (hF : Fintype.card F=2)
    (hn : 4 < n) (r : PositiveIndex n) (hj : r.val.2.val+1=n)
    (hr : r.val.2.val=r.val.1.val+1) (h : G)
    (hc : ∀ s : PositiveIndex n, s ≠ r → h*root s 1=root s 1*h) :
    let first : Fin n := ⟨0,by omega⟩
    let last : Fin n := ⟨n-1,by omega⟩
    h.val=1+Matrix.single first last (h.val first last)+
      Matrix.single first r.val.1 (h.val first r.val.1) := by
  classical
  let first : Fin n := ⟨0,by omega⟩
  let last : Fin n := ⟨n-1,by omega⟩
  have hd := F2_centralizer_diagonal hF (by omega) r h hc
  have hfl : first ≠ last := by intro he; have hv:=congrArg Fin.val he; dsimp [first,last] at hv; omega
  have hfi : first ≠ r.val.1 := by intro he; have hv:=congrArg Fin.val he; dsimp [first] at hv; omega
  have hil : r.val.1 ≠ last := by intro he; have hv:=congrArg Fin.val he; dsimp [last] at hv; omega
  have hz : ∀ a b : Fin n, a ≠ b → ¬(a=first ∧ b=last) →
      ¬(a=first ∧ b=r.val.1) → h.val a b=0 := by
    intro a b hab hp hq
    by_cases haf : a=first
    · have hbl : b ≠ last := fun he => hp ⟨haf,he⟩
      have hbi : b ≠ r.val.1 := fun he => hq ⟨haf,he⟩
      have hblt : b < last := by
        have hv : b.val ≠ n-1 := fun he => hbl (Fin.ext he)
        change b.val < n-1
        have hb := b.isLt; omega
      let s : PositiveIndex n := ⟨(b,last),hblt⟩
      have hsr : s ≠ r := fun he => hbi (congrArg (fun x : PositiveIndex n => x.val.1) he)
      exact commute_transvection_column h b last (ne_of_lt hblt) (hc s hsr) a hab
    · have hfa : first < a := by
        have hv : a.val ≠ 0 := fun he => haf (Fin.ext he)
        change 0 < a.val; omega
      let s : PositiveIndex n := ⟨(first,a),hfa⟩
      have hsr : s ≠ r := by
        intro he; have hv:=congrArg (fun x : PositiveIndex n => x.val.1.val) he
        change 0=r.val.1.val at hv; omega
      exact commute_transvection_row h first a (ne_of_lt hfa) (hc s hsr) b hab.symm
  change h.val=1+Matrix.single first last (h.val first last)+
    Matrix.single first r.val.1 (h.val first r.val.1)
  ext a b
  by_cases hab : a=b
  · subst b
    have hp : ¬(first=a ∧ last=a) := fun ⟨ha,hb⟩ => hfl (ha.trans hb.symm)
    have hq : ¬(first=a ∧ r.val.1=a) := fun ⟨ha,hb⟩ => hfi (ha.trans hb.symm)
    simp [hd a,Matrix.single_apply,hp,hq]
  · by_cases hp : a=first ∧ b=last
    · rcases hp with ⟨rfl,rfl⟩; simp [Matrix.one_apply,Matrix.single_apply,hab,hil]
    · by_cases hq : a=first ∧ b=r.val.1
      · rcases hq with ⟨rfl,rfl⟩; simp [Matrix.one_apply,Matrix.single_apply,hab,hil.symm]
      · have hp' : ¬(first=a ∧ last=b) := by simpa only [eq_comm] using hp
        have hq' : ¬(first=a ∧ r.val.1=b) := by simpa only [eq_comm] using hq
        simp [Matrix.one_apply,Matrix.single_apply,hab,hp',hq',hz a b hab hp hq]

end NikolovSegal.SLnF2Residual
