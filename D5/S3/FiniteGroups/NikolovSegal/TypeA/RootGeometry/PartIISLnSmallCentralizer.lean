/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnSmallCentralizer
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnSmallCentralizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnSmallTorus
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnSmallField
open Matrix NikolovSegal.SLnRootAction
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "T" => diagonalTorus n F
open NikolovSegal.SLnFullGroup

theorem kernel_commuting_block [Fintype F] (hn : 4 < n) (hF : 2 < Fintype.card F)
    (r : PositiveIndex n) (h : G)
    (hK : ∀ d ∈ torusKernel (F := F) r, d*h=h*d)
    (a b : Fin n) (hab : a ≠ b)
    (hpair : ¬(a=r.val.1 ∧ b=r.val.2) ∧ ¬(a=r.val.2 ∧ b=r.val.1)) :
    h.val a b = 0 := by
  rcases lt_or_gt_of_ne hab with hab|hba
  · let s : PositiveIndex n := ⟨(a,b),hab⟩
    have hsr : s ≠ r := by
      intro he; apply hpair.1
      exact ⟨congrArg (fun x : PositiveIndex n => x.val.1) he,
        congrArg (fun x : PositiveIndex n => x.val.2) he⟩
    obtain ⟨d,hd,hsep⟩ := torusKernel_separates hn hF r s hsr
    have he := (diagonal_commutes_iff d h ((mem_torusKernel_iff r d).mp hd).1).mp (hK d hd) a b
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hsep)
  · let s : PositiveIndex n := ⟨(b,a),hba⟩
    have hsr : s ≠ r := by
      intro he; apply hpair.2
      exact ⟨congrArg (fun x : PositiveIndex n => x.val.2) he,
        congrArg (fun x : PositiveIndex n => x.val.1) he⟩
    obtain ⟨d,hd,hsep⟩ := torusKernel_separates hn hF r s hsr
    have he := (diagonal_commutes_iff d h ((mem_torusKernel_iff r d).mp hd).1).mp (hK d hd) a b
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hsep.symm)

theorem simple_root_centralizer_is_center [Fintype F] (hn : 4 < n)
    (hF : 2 < Fintype.card F) (r : PositiveIndex n)
    (hsimple : r.val.2.val=r.val.1.val+1) (h : G)
    (hK : ∀ d ∈ torusKernel (F := F) r, d*h=h*d)
    (hpos : ∀ s : PositiveIndex n, s ≠ r → h*root s 1=root s 1*h) :
    h ∈ Subgroup.center G := by
  classical
  let i := r.val.1
  let j := r.val.2
  obtain ⟨k,hki,hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  have outside : k < i ∨ j < k := by
    change k.val < i.val ∨ j.val < k.val
    have hkiv : k.val ≠ i.val := fun he => hki (Fin.ext he)
    have hkjv : k.val ≠ j.val := fun he => hkj (Fin.ext he)
    change j.val=i.val+1 at hsimple
    omega
  have hij0 : h.val i j=0 := by
    rcases outside with hk|hk
    · let s : PositiveIndex n := ⟨(k,i),hk⟩
      have hsr : s ≠ r := fun he => hki (congrArg (fun x : PositiveIndex n => x.val.1) he)
      exact commute_transvection_row h k i (ne_of_lt hk) (hpos s hsr) j (ne_of_lt r.property).symm
    · let s : PositiveIndex n := ⟨(j,k),hk⟩
      have hsr : s ≠ r := fun he => hkj (congrArg (fun x : PositiveIndex n => x.val.2) he)
      exact commute_transvection_column h j k (ne_of_lt hk) (hpos s hsr) i (ne_of_lt r.property)
  have hji0 : h.val j i=0 := by
    rcases outside with hk|hk
    · let s : PositiveIndex n := ⟨(k,j),lt_trans hk r.property⟩
      have hsr : s ≠ r := fun he => hki (congrArg (fun x : PositiveIndex n => x.val.1) he)
      exact commute_transvection_row h k j (ne_of_lt s.property) (hpos s hsr) i (ne_of_lt r.property)
    · let s : PositiveIndex n := ⟨(i,k),lt_trans r.property hk⟩
      have hsr : s ≠ r := fun he => hkj (congrArg (fun x : PositiveIndex n => x.val.2) he)
      exact commute_transvection_column h i k (ne_of_lt s.property) (hpos s hsr) j (ne_of_lt r.property).symm
  have hoff : ∀ a b : Fin n, a ≠ b → h.val a b=0 := by
    intro a b hab
    by_cases hp : a=i ∧ b=j
    · rcases hp with ⟨rfl,rfl⟩; exact hij0
    by_cases hp' : a=j ∧ b=i
    · rcases hp' with ⟨rfl,rfl⟩; exact hji0
    exact kernel_commuting_block hn hF r h hK a b hab ⟨hp,hp'⟩
  have hdiag : ∀ a : Fin n, h.val a a=h.val k k := by
    intro a
    by_cases ha : a=k
    · rw [ha]
    rcases lt_or_gt_of_ne ha with ha|ha
    · let s : PositiveIndex n := ⟨(a,k),ha⟩
      have hsr : s ≠ r := fun he => hkj (congrArg (fun x : PositiveIndex n => x.val.2) he)
      exact commute_transvection_diagonal h a k (ne_of_lt ha) (hpos s hsr)
    · let s : PositiveIndex n := ⟨(k,a),ha⟩
      have hsr : s ≠ r := fun he => hki (congrArg (fun x : PositiveIndex n => x.val.1) he)
      exact (commute_transvection_diagonal h k a (ne_of_lt ha) (hpos s hsr)).symm
  have hscalar : Matrix.scalar (Fin n) (h.val k k)=h.val := by
    ext a b
    by_cases hab : a=b
    · subst b; simpa using (hdiag a).symm
    · simp [Matrix.scalar_apply,Matrix.diagonal_apply,hab,hoff a b hab]
  apply Subgroup.mem_center_iff.mpr
  intro b
  apply Subtype.ext
  change b.val*h.val=h.val*b.val
  rw [← hscalar]
  exact (Matrix.scalar_commute (h.val k k) (Commute.all _) b.val).symm

end NikolovSegal.SLnSmallField
