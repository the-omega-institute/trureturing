/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowFlag
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowFlag
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitarySylowRoots

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NikolovSegal.UnitarySylow
open Matrix SLnNormalizer PartIIUnitaryUpperTorus
universe u
variable {F : Type u} [Field F] {n : ℕ}

/-- Forward intrinsic flag relation uses only literal unitriangular entries. -/
theorem prefix_action (k : ℕ) (v : Fin n → F) (hv : Prefix (k+1) v)
    (h : SpecialLinearGroup (Fin n) F) (hh : h  ∈  Uplus n F) :
    Prefix k (h.val *ᵥ v-v) :=
  (SLnNormalizer.prefix_succ_iff k v).mp hv h hh

/-- The actual paired unitary root detects its leading adjacent coordinate. -/
theorem paired_detect {i j : Fin n} (hij : i ≠ j)
    (hj : j ≠ j.rev) (hr : j.rev ≠ i) (v : Fin n → F) :
    ((SpecialLinearGroup.transvection hij (1:F) *
      SpecialLinearGroup.transvection (Fin.rev_injective.ne hij.symm) (-1:F)).val *ᵥ v-v) i = v j := by
  rw [paired_root_matrix hij hj]
  simp [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.single_mulVec,
    Function.update_apply,hr,hr.symm]

theorem short_detect_a {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (x z y : F) (v : Fin n → F) :
    ((shortRoot hab hbc hac x z y).val *ᵥ v-v) a = x*v b+y*v c := by
  rw [shortRoot_matrix]
  simp [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.single_mulVec,
    Function.update_apply,hab,hab.symm]
  ring

theorem short_detect_b {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (x z y : F) (v : Fin n → F) :
    ((shortRoot hab hbc hac x z y).val *ᵥ v-v) b = z*v c := by
  rw [shortRoot_matrix]
  simp [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.single_mulVec,
    Function.update_apply,hab,hab.symm]

/-- Actual short roots are upper unitriangular when the three positions are ordered. -/
theorem shortRoot_mem_Uplus {a b c : Fin n} (hab : a.val < b.val) (hbc : b.val < c.val)
    (x z y : F) :
    shortRoot (ne_of_lt (show a < b from hab)) (ne_of_lt (show b < c from hbc))
      (ne_of_lt (show a < c from lt_trans hab hbc)) x z y  ∈  Uplus n F := by
  exact (Uplus n F).mul_mem
    ((Uplus n F).mul_mem (transvection_mem_Uplus hab x) (transvection_mem_Uplus hbc z))
    (transvection_mem_Uplus (lt_trans hab hbc) _)

/-- The whole standard coordinate flag is intrinsic to actual unitary U.
Central long roots use a nonzero anti-fixed scalar; central short roots use
actual trace surjectivity. This includes characteristic two and every rank. -/
theorem prefix_succ_iff [Finite F] (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι ≠ RingEquiv.refl F) (k : ℕ) (v : Fin n → F) :
    Prefix (k+1) v ↔ ∀ h : specialUnitary n ι, h  ∈  positiveU n ι →
      Prefix k (h.val.val *ᵥ v-v) := by
  constructor
  · intro hv h hh
    exact prefix_action k v hv h.val hh
  · intro hv j hj
    let i : Fin n := ⟨j.val-1,by omega⟩
    have hij : i.val < j.val := by dsimp [i];omega
    have hi : k ≤ i.val := by dsimp [i];omega
    have hneij : i ≠ j := ne_of_lt (show i < j from hij)
    by_cases hr : j.rev=i
    · obtain ⟨τ,hτ,ht⟩ := UnitaryRankTwo.exists_antifixed ι hinv hne
      let h : specialUnitary n ι :=
        ⟨SpecialLinearGroup.transvection hneij τ,central_root_fixed ι hneij hr τ ht⟩
      have hh : h ∈ positiveU n ι := transvection_mem_Uplus hij τ
      have he := hv h hh i hi
      have hm : (h.val.val *ᵥ v-v) i=τ*v j := by
        simp [h,SpecialLinearGroup.transvection_coe,Matrix.add_mulVec,
          Matrix.one_mulVec,Matrix.single_mulVec,Function.update_apply]
      rw [hm] at he
      exact (mul_eq_zero.mp he).resolve_left hτ
    · by_cases hi' : i=i.rev
      · let a := j.rev
        have hab : a.val < i.val := by
          dsimp [a]; have hir := congrArg Fin.val hi';simp only [Fin.val_rev] at hir;omega
        have hac : a.rev=j := by simp [a]
        obtain ⟨y,hy,_⟩ := UnitaryField.actual_trace_root_exists ι hinv hne (1:F)
        let s := shortRoot (ne_of_lt (show a < i from hab)) hneij
          (ne_of_lt (show a < j from lt_trans hab hij)) (1:F) (-ι 1) y
        let h : specialUnitary n ι := ⟨s,shortRoot_fixed ι hinv _ _ _ hac hi'.symm 1 y hy⟩
        have hh : h ∈ positiveU n ι := shortRoot_mem_Uplus hab hij 1 (-ι 1) y
        have he := hv h hh i hi
        change (s.val *ᵥ v-v) i=0 at he
        rw [short_detect_b] at he
        simpa [map_one] using he
      · by_cases hj' : j=j.rev
        · let c := i.rev
          have hbc : j.val < c.val := by
            dsimp [c];have hjr := congrArg Fin.val hj';simp only [Fin.val_rev] at hjr
            omega
          have hc : i.rev=c := rfl
          obtain ⟨y,hy,_⟩ := UnitaryField.actual_trace_root_exists ι hinv hne (1:F)
          let s := shortRoot hneij (ne_of_lt (show j < c from hbc))
            (ne_of_lt (show i < c from lt_trans hij hbc)) (1:F) (-ι 1) y
          let h : specialUnitary n ι := ⟨s,shortRoot_fixed ι hinv _ _ _ hc hj'.symm 1 y hy⟩
          have hh : h ∈ positiveU n ι := shortRoot_mem_Uplus hij hbc 1 (-ι 1) y
          have hec := hv h hh j (by omega)
          change (s.val *ᵥ v-v) j=0 at hec
          rw [short_detect_b] at hec
          have hvc : v c=0 := by simpa [map_one] using hec
          have he := hv h hh i hi
          change (s.val *ᵥ v-v) i=0 at he
          rw [short_detect_a,hvc,mul_zero,add_zero,one_mul] at he
          exact he
        · let s := SpecialLinearGroup.transvection hneij (1:F) *
            SpecialLinearGroup.transvection (Fin.rev_injective.ne hneij.symm) (-1:F)
          let h : specialUnitary n ι :=
            ⟨s,by
              change steinberg ι s=s
              simpa only [s,map_one] using paired_root_fixed ι hinv hij hi' hj' (1:F)⟩
          have hrlt : j.rev.val < i.rev.val := by simp only [Fin.val_rev];omega
          have hh : h ∈ positiveU n ι :=
            (Uplus n F).mul_mem (transvection_mem_Uplus hij 1) (transvection_mem_Uplus hrlt (-1))
          have he := hv h hh i hi
          change (s.val *ᵥ v-v) i=0 at he
          rw [paired_detect hneij hj' hr] at he
          exact he

end NikolovSegal.UnitarySylow
