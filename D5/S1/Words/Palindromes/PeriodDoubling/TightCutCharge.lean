/- GID: D5/S1/Words/Palindromes/PeriodDoubling/TightCutCharge
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/TightCutCharge
   mirror-E: none(waiver:literal-tight-cut-class-and-charge)
   anchors: []
   utility: none
   digest: Every tight palindrome cut from class S preserves that class and never increases Q. -/

/-
proof_shape: content (tight_cut_class_and_Q)
escape_witness: Output digit reconstruction transfers distance-two exclusions to the literal class S.
admission_basis: escape-witness
Direct frozen dependencies: none; the imported period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.CutRepresentation
import D5.S1.Words.Palindromes.PeriodDoubling.BaseClassStreams
import D5.S1.Words.Palindromes.PeriodDoubling.BaseArithmetic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling

open BaseCertificates

theorem tight_cut_class_and_Q (n j : ℕ) (hS : classS n) (hj : j < n)
    (hpal : List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i))))
    (htight : signedWeight (((n+1)/2 : ℕ) : ℤ)=signedWeight (((j+1)/2 : ℕ) : ℤ)+1) :
    classS j ∧ signedDigitCharge j ≤ signedDigitCharge n := by
  have class_from_expansion (n : ℕ) (ds : List ℤ)
      (hd : ∀ z ∈ ds, z=-1 ∨ z=0 ∨ z=1)
      (hs : ds.IsChain (fun a b => a=0 ∨ b=0))
      (hspace : (ds.zip ds.tail).IsChain (fun a b => a.1*b.2 ≠ -1))
      (hv : ds.foldr (fun z x => z+2*x) 0=(((n+1)/2 : ℕ) : ℤ)) : classS n := by
    let X:=(n+1)/2
    let h:=Nat.log 2 (3*X)+1
    let cs:=tripleSignedDigits X h
    have hb : 3*X < 2^(h+1) := Nat.lt_pow_of_log_lt (by decide) (by dsimp [h];omega)
    obtain ⟨hcv,hcs,_⟩:=triple_digits_value_and_minimality X h hb
    have hc : ∀ z ∈ cs, z=-1 ∨ z=0 ∨ z=1 := by
      intro z hz
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hz
      have ha:=Nat.mod_lt (3*X/2^(i.val+1)) (by decide : 0 < 2)
      have hb:=Nat.mod_lt (X/2^(i.val+1)) (by decide : 0 < 2)
      omega
    have padcoeff (xs : List ℤ) (k : ℕ) (hc : ∀ z ∈ xs, z=-1 ∨ z=0 ∨ z=1) :
        ∀ z ∈ xs++List.replicate k 0, z=-1 ∨ z=0 ∨ z=1 := by
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hc z hz
      · exact Or.inr (Or.inl (List.mem_replicate.mp hz).2)
    have padsparse (xs : List ℤ) (k : ℕ) (hs : xs.IsChain (fun a b => a=0 ∨ b=0)) :
        (xs++List.replicate k 0).IsChain (fun a b => a=0 ∨ b=0) := by
      refine hs.append (List.isChain_replicate_of_rel _ (Or.inl rfl)) ?_
      intro a ha b hb
      exact Or.inr (List.mem_replicate.mp (List.mem_of_mem_head? hb)).2
    have zero_value (k : ℕ) : (List.replicate k (0:ℤ)).foldr (fun z x => z+2*x) 0=0 := by
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ,ih]
    have hcv' : cs.foldr (fun z x => z+2*x) 0=(X : ℤ) := hcv
    have eq:=nonadjacent_digits_unique (cs++List.replicate ds.length 0)
      (ds++List.replicate cs.length 0) (padcoeff cs ds.length hc) (padcoeff ds cs.length hd)
      (padsparse cs ds.length hcs) (padsparse ds cs.length hs)
      (by simp [Nat.add_comm]) (by simpa only [List.foldr_append,zero_value] using hcv'.trans hv.symm)
    have entry_padding (xs : List ℤ) (k i : ℕ) :
        (xs++List.replicate k 0)[i]?.getD 0=xs[i]?.getD 0 := by
      by_cases hi : i < xs.length
      · simp [List.getElem?_append,hi]
      · rw [List.getElem?_eq_none (by omega : xs.length ≤ i)]
        simp only [List.getElem?_append,if_neg hi,List.getElem?_replicate]
        split <;> rfl
    have entries (i : ℕ) : cs[i]?.getD 0=ds[i]?.getD 0 := by
      have hh:=congrArg (fun xs : List ℤ => xs[i]?.getD 0) eq
      simpa only [entry_padding] using hh
    refine ⟨h,hb,?_⟩
    change ∀ (i j : Fin h), i.val < j.val → cs[i.val]?.getD 0 ≠ 0 → cs[j.val]?.getD 0 ≠ 0 →
      (∀ k : ℕ, i.val < k → k < j.val → cs[k]?.getD 0=0) →
      cs[i.val]?.getD 0 ≠ cs[j.val]?.getD 0 → 3 ≤ j.val-i.val
    intro i j hij hi hj hz hdiff
    simp only [entries] at hi hj hdiff
    have hilen : i.val < ds.length := by
      by_contra hh
      rw [List.getElem?_eq_none (by omega : ds.length ≤ i.val)] at hi
      simp at hi
    have hjlen : j.val < ds.length := by
      by_contra hh
      rw [List.getElem?_eq_none (by omega : ds.length ≤ j.val)] at hj
      simp at hj
    by_contra hh
    have hdif : j.val=i.val+1 ∨ j.val=i.val+2 := by omega
    rcases hdif with he | he
    · have sparse := List.isChain_iff_getElem.mp hs i.val (by omega)
      rw [he] at hj
      simp only [List.getElem?_eq_getElem hilen,List.getElem?_eq_getElem (by omega : i.val+1 < ds.length),Option.getD_some] at hi hj
      exact hj (sparse.resolve_left hi)
    · have hpair := List.isChain_iff_getElem.mp hspace i.val (by
        simp only [List.length_zip,List.length_tail];omega)
      simp only [List.getElem_zip,List.getElem_tail] at hpair
      have ha:=hd ds[i.val] (List.getElem_mem hilen)
      have hb:=hd ds[j.val] (List.getElem_mem hjlen)
      simp only [List.getElem?_eq_getElem hilen,List.getElem?_eq_getElem hjlen,Option.getD_some] at hi hj hdiff
      have hjget : ds[j.val]=ds[i.val+2] := by congr 1
      simp only [hjget] at hb hj hdiff
      simp only [Nat.add_assoc, Nat.reduceAdd] at hpair
      rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> simp_all
  obtain ⟨charge,s,t,xs,hs,ht,⟨p⟩,hsn,hsj,hn,hjv⟩:=cut_representation_completeness n j hS hj hpal
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
    have hq:=base_path_Q_semantics n j hs ht p hsn hsj hn hjv
    have hb:=base_accepted_bound true hs ht p
    have charge_add {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
        (p : (baseAutomaton true).Path s t xs) :
        pathCharge (fun _ a _ => 3*a.1+a.2.1) p=
          3*pathCharge (fun _ a _ => a.1) p+pathCharge (fun _ a _ => a.2.1) p := by
      induction p with
      | nil => simp [pathCharge]
      | cons q s t a xs he p ih => simp only [pathCharge,ih];ring
    change pathCharge (fun _ a _ => 3*a.1+a.2.1) p+baseOffset (baseTable t.val).1 ≤ 3 at hb
    rw [charge_add] at hb
    have hQ : signedDigitCharge j ≤ signedDigitCharge n := by omega
    refine ⟨?_,hQ⟩
    let ds:=pathOutputs (fun _ _ q => (baseTable q.val).1[12]?.getD 0) p
    obtain ⟨hc,hsp,hv,hh⟩:=base_path_sparse_signed_digits true true hs ht p
    have hspace:=base_path_class_spacing true ht p
    change (∀ z ∈ ds, z=-1 ∨ z=0 ∨ z=1) at hc
    change ds.IsChain (fun a b => a=0 ∨ b=0) at hsp
    change ds.foldr (fun z x => z+2*x) 0=2*(xs.foldr (fun a x => a.2.2.2+2*x) 0+(baseTable s.val).1[3]?.getD 0) at hv
    rw [hJ] at hv
    change ds.head?=some 0 at hh
    change (ds.zip ds.tail).IsChain (fun a b => a.1*b.2 ≠ -1) at hspace
    cases he : ds with
    | nil => simp [he] at hh
    | cons d ys =>
      rw [he] at hc hsp hv hh hspace
      have hz : d=0 := by simpa using hh
      subst d
      have hyv : ys.foldr (fun z x => z+2*x) 0=(((j+1)/2 : ℕ) : ℤ) := by
        simp only [List.foldr_cons,zero_add] at hv
        omega
      have hys : (ys.zip ys.tail).IsChain (fun a b => a.1*b.2 ≠ -1) := by
        cases ys with
        | nil => simp
        | cons a ys => simpa only [List.tail_cons,List.zip_cons_cons] using hspace.tail
      exact class_from_expansion j ys (fun z hz => hc z (by simp [hz])) hsp.tail hys hyv

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.tight_cut_class_and_Q
