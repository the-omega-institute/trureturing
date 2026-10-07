/- GID: D5/S1/Words/Palindromes/PeriodDoubling/TightCutLowestPosition
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/TightCutLowestPosition
   mirror-E: none(waiver:literal-tight-cut-lowest-position)
   anchors: []
   utility: none
   digest: Every nonzero tight cut in class S has nondecreasing dyadic lowest position. -/

/-
proof_shape: content (tight_cut_lowest_position)
escape_witness: The minimum-product bound excludes early output digits; valuation decodes their order.
admission_basis: escape-witness
Direct frozen dependencies: none; the imported period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.BaseLowestPosition
import D5.S1.Words.Palindromes.PeriodDoubling.CutRepresentation
import D5.S1.Words.Palindromes.PeriodDoubling.BaseArithmetic
import D5.S1.Words.Palindromes.PeriodDoubling.SignedDigitValuation
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling
open BaseCertificates

theorem tight_cut_lowest_position (n j : ℕ) (hS : classS n) (hj : j < n)
    (hpal : List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i))))
    (htight : signedWeight (((n+1)/2 : ℕ) : ℤ)=signedWeight (((j+1)/2 : ℕ) : ℤ)+1) :
    j=0 ∨ padicValNat 2 ((n+1)/2) ≤ padicValNat 2 ((j+1)/2) := by
  by_cases hj0 : j=0
  · exact Or.inl hj0
  right
  obtain ⟨charge,s,t,xs,hs,ht,⟨p⟩,hsn,hsj,hn,hjv,_⟩:=cut_representation_completeness n j hS hj hpal
  have hf:=base_path_signed_weight_difference charge hs ht p
  have hN : xs.foldr (fun a x => a.2.2.1+2*x) 0+(baseTable s.val).1[2]?.getD 0=(((n+1)/2 : ℕ) : ℤ) := by
    rw [hn,hsn];omega
  have hJ : xs.foldr (fun a x => a.2.2.2+2*x) 0+(baseTable s.val).1[3]?.getD 0=(((j+1)/2 : ℕ) : ℤ) := by
    rw [hjv,hsj];omega
  rw [hN,hJ] at hf
  have hf' : pathCharge (fun _ a _ => a.1) p=1 := by omega
  cases charge with
  | false =>
    have hb:=base_accepted_bound false hs ht p
    simp only [Bool.false_eq_true,if_false,one_mul,add_zero] at hb
    omega
  | true =>
    let dn:=pathOutputs (fun _ _ q => (baseTable q.val).1[10]?.getD 0) p
    let dj:=pathOutputs (fun _ _ q => (baseTable q.val).1[12]?.getD 0) p
    obtain ⟨cn,sn,vn,_⟩:=base_path_sparse_signed_digits true false hs ht p
    obtain ⟨cj,sj,vj,_⟩:=base_path_sparse_signed_digits true true hs ht p
    change (∀ z ∈ dn, z=-1 ∨ z=0 ∨ z=1) at cn
    change (∀ z ∈ dj, z=-1 ∨ z=0 ∨ z=1) at cj
    change dn.foldr (fun z x => z+2*x) 0=2*(xs.foldr (fun a x => a.2.2.1+2*x) 0+(baseTable s.val).1[2]?.getD 0) at vn
    change dj.foldr (fun z x => z+2*x) 0=2*(xs.foldr (fun a x => a.2.2.2+2*x) 0+(baseTable s.val).1[3]?.getD 0) at vj
    rw [hN] at vn
    rw [hJ] at vj
    have first (ds : List ℤ) (hc : ∀ z ∈ ds, z=-1 ∨ z=0 ∨ z=1)
        (hv : ds.foldr (fun z x => z+2*x) 0 ≠ 0) :
        ∃ k : ℕ, ds[k]?.getD 0 ≠ 0 ∧
          (∀ i : ℕ, i < k → ds[i]?.getD 0=0) ∧
          padicValInt 2 (ds.foldr (fun z x => z+2*x) 0)=k := by
      have hex : ∃ z ∈ ds, z ≠ 0 := by
        by_contra hh
        have allzero : ∀ z ∈ ds, z=0 := by simpa using hh
        have hv0 : ds.foldr (fun z x => z+2*x) 0=0 := by
          clear hc hv hh
          induction ds with
          | nil => rfl
          | cons z ds ih =>
            have hz:=allzero z (by simp)
            simp only [List.foldr_cons,hz,zero_add]
            rw [ih (fun a ha => allzero a (by simp [ha]))]
            simp
        exact hv hv0
      let k:=ds.findIdx (fun z => z != 0)
      have hk : k < ds.length := by
        apply List.findIdx_lt_length.mpr
        obtain ⟨z,hz,hnz⟩:=hex
        exact ⟨z,hz,by simpa using hnz⟩
      have hkn : ds[k]?.getD 0 ≠ 0 := by
        have hh:=List.findIdx_getElem (p:=fun z : ℤ => z != 0) (w:=hk)
        simpa only [List.getElem?_eq_getElem hk,Option.getD_some,bne_iff_ne] using hh
      have hz : ∀ i : ℕ, i < k → ds[i]?.getD 0=0 := by
        intro i hi
        have hh:=List.not_of_lt_findIdx hi
        have hil : i < ds.length := hi.trans hk
        simpa only [List.getElem?_eq_getElem hil,Option.getD_some,bne_eq_false_iff_eq] using hh
      have coeff : ds[k]?.getD 0=-1 ∨ ds[k]?.getD 0=1 := by
        have hh:=hc ds[k] (List.getElem_mem hk)
        rw [List.getElem?_eq_getElem hk] at hkn ⊢
        simp only [Option.getD_some] at hkn ⊢
        rcases hh with hh | hh | hh
        · exact Or.inl hh
        · exact (hkn hh).elim
        · exact Or.inr hh
      exact ⟨k,hkn,hz,signed_digits_lowest_valuation ds k hz coeff⟩
    have hxn : (((n+1)/2 : ℕ) : ℤ) ≠ 0 := by omega
    have hxj : (((j+1)/2 : ℕ) : ℤ) ≠ 0 := by omega
    obtain ⟨ki,hki,hzi,hvi⟩:=first dn cn (by rw [vn];exact mul_ne_zero (by decide) hxn)
    obtain ⟨ko,hko,hzo,hvo⟩:=first dj cj (by rw [vj];exact mul_ne_zero (by decide) hxj)
    obtain ⟨l,hl,hnl⟩:=base_path_lowest_order hs ht p hf' ko hko
    have hkile : ki ≤ l := by
      by_contra hh
      exact hnl (hzi l (by omega))
    have kval : ki ≤ ko := hkile.trans hl
    haveI : Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
    have hvi' : padicValInt 2 (dn.foldr (fun z x => z+2*x) 0)=padicValNat 2 ((n+1)/2)+1 := by
      rw [vn]
      have hh:=padicValInt_mul_eq_succ (p:=2) (((n+1)/2 : ℕ) : ℤ) hxn
      simpa only [Nat.cast_ofNat,padicValInt.of_nat,mul_comm (((n+1)/2 : ℕ) : ℤ) (2:ℤ)] using hh
    have hvo' : padicValInt 2 (dj.foldr (fun z x => z+2*x) 0)=padicValNat 2 ((j+1)/2)+1 := by
      rw [vj]
      have hh:=padicValInt_mul_eq_succ (p:=2) (((j+1)/2 : ℕ) : ℤ) hxj
      simpa only [Nat.cast_ofNat,padicValInt.of_nat,mul_comm (((j+1)/2 : ℕ) : ℤ) (2:ℤ)] using hh
    omega

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.tight_cut_lowest_position
