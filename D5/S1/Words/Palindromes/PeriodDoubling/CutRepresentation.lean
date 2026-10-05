/- GID: D5/S1/Words/Palindromes/PeriodDoubling/CutRepresentation
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/CutRepresentation
   mirror-E: none(waiver:complete-legal-cut-arithmetic-realization)
   anchors: []
   utility: none
   digest: Every legal palindrome cut from class S has a complete accepting transducer path. -/

/-
proof_shape: content (cut_representation_completeness)
escape_witness: Explicit unbounded zero padding and signed-digit construction realize actual cuts.
admission_basis: escape-witness
Direct frozen dependencies: none; the imported period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.BaseDigitRealization
import D5.S1.Words.Palindromes.PeriodDoubling.BaseQArithmetic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling

open BaseCertificates

def classS (n : ℕ) : Prop := ∃ h : ℕ,
  3*((n+1)/2) < 2^(h+1) ∧
  let ds:=tripleSignedDigits ((n+1)/2) h
  ∀ (i j : Fin h), i.val < j.val → ds[i.val]?.getD 0 ≠ 0 → ds[j.val]?.getD 0 ≠ 0 →
    (∀ k : ℕ, i.val < k → k < j.val → ds[k]?.getD 0=0) →
    ds[i.val]?.getD 0 ≠ ds[j.val]?.getD 0 → 3 ≤ j.val-i.val

theorem cut_representation_completeness (n j : ℕ) (hS : classS n) (hj : j < n)
    (hpal : List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i)))) :
    ∃ (charge : Bool) (s t : Fin 1492) (xs : List (ℤ × ℤ × ℤ × ℤ)),
      s ∈ (baseAutomaton charge).start ∧ t ∈ (baseAutomaton charge).accept ∧
      Nonempty ((baseAutomaton charge).Path s t xs) ∧
      (baseTable s.val).1[2]?.getD 0=((n%2 : ℕ) : ℤ) ∧
      (baseTable s.val).1[3]?.getD 0=((j%2 : ℕ) : ℤ) ∧
      xs.foldr (fun a x => a.2.2.1+2*x) 0=((n/2 : ℕ) : ℤ) ∧
      xs.foldr (fun a x => a.2.2.2+2*x) 0=((j/2 : ℕ) : ℤ) := by
  have class_two_spacing (ds : List ℤ)
      (hsparse : ds.IsChain (fun a b => a=0 ∨ b=0))
      (hclass : ∀ (i j : Fin ds.length), i.val < j.val →
        ds[i.val]?.getD 0 ≠ 0 → ds[j.val]?.getD 0 ≠ 0 →
        (∀ k : ℕ, i.val < k → k < j.val → ds[k]?.getD 0=0) →
        ds[i.val]?.getD 0 ≠ ds[j.val]?.getD 0 → 3 ≤ j.val-i.val) :
      ∀ i : ℕ, ds[i]?.getD 0*ds[i+2]?.getD 0 ≠ -1 := by
    intro i hbad
    have hi : i < ds.length := by
      by_contra hh
      rw [List.getElem?_eq_none (by omega : ds.length ≤ i)] at hbad
      simp at hbad
    have hj : i+2 < ds.length := by
      by_contra hh
      rw [List.getElem?_eq_none (by omega : ds.length ≤ i+2)] at hbad
      simp at hbad
    have hn : ds[i]?.getD 0 ≠ 0 := by intro hh;rw [hh] at hbad;norm_num at hbad
    have hm : ds[i+2]?.getD 0 ≠ 0 := by intro hh;rw [hh] at hbad;norm_num at hbad
    have hdiff : ds[i]?.getD 0 ≠ ds[i+2]?.getD 0 := by intro hh;rw [hh] at hbad;nlinarith
    have hz : ds[i+1]?.getD 0=0 := by
      have hc := List.isChain_iff_getElem.mp hsparse i (by omega)
      rw [List.getElem?_eq_getElem hi] at hn
      rw [List.getElem?_eq_getElem (by omega : i+1 < ds.length)]
      simp only [Option.getD_some] at hn ⊢
      exact hc.resolve_left hn
    have hh := hclass ⟨i,hi⟩ ⟨i+2,hj⟩ (by simp) hn hm
      (by
        intro k hk hk'
        change i < k at hk
        change k < i+2 at hk'
        have he : k=i+1 := by omega
        simpa only [he] using hz) hdiff
    dsimp at hh
    omega
  have zero_padding_spacing (ds : List ℤ)
      (hds : ∀ i : ℕ, ds[i]?.getD 0*ds[i+2]?.getD 0 ≠ -1) (k : ℕ) :
      ∀ i : ℕ, (ds++List.replicate k 0)[i]?.getD 0*
        (ds++List.replicate k 0)[i+2]?.getD 0 ≠ -1 := by
    have entry_padding (i : ℕ) : (ds++List.replicate k (0:ℤ))[i]?.getD 0=ds[i]?.getD 0 := by
      by_cases hi : i < ds.length
      · simp [List.getElem?_append,hi]
      · rw [List.getElem?_eq_none (by omega : ds.length ≤ i)]
        simp only [List.getElem?_append,if_neg hi,List.getElem?_replicate]
        split <;> rfl
    intro i
    simpa only [entry_padding] using hds i
  have cons_zero_spacing (ds : List ℤ)
      (hds : ∀ i : ℕ, ds[i]?.getD 0*ds[i+2]?.getD 0 ≠ -1) :
      ∀ i : ℕ, (0::ds)[i]?.getD 0*(0::ds)[i+2]?.getD 0 ≠ -1 := by
    intro i
    cases i with
    | zero => simp
    | succ i => simpa only [List.getElem?_cons_succ,Nat.add_right_comm] using hds i
  have spacing_chain (ds : List ℤ)
      (hds : ∀ i : ℕ, ds[i]?.getD 0*ds[i+2]?.getD 0 ≠ -1) :
      (ds.zip ds.tail).IsChain (fun a b => a.1*b.2 ≠ -1) := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have hlen : i+2 < ds.length := by simp only [List.length_zip,List.length_tail] at hi;omega
    simp only [List.getElem_zip,List.getElem_tail]
    have hh:=hds i
    simpa only [List.getElem?_eq_getElem (by omega : i < ds.length),
      List.getElem?_eq_getElem hlen,Option.getD_some] using hh
  obtain ⟨h,hbound,hS⟩:=hS
  obtain ⟨r,bits,hr,⟨p⟩,hN,hJ,hbits⟩:=cut_bit_relation_completeness n j hj hpal
  let L:=bits.length
  let pad:=h+3
  let bs:=bits++List.replicate pad (0,0)
  let ds:=tripleSignedDigits ((n+1)/2) h
  let dns:=0::(ds++List.replicate (L+2) 0)
  let ys:=tripleSignedDigits ((j+1)/2) (L+h+2)
  let djs:=0::ys
  have zero_value (k : ℕ) : (List.replicate k (0:ℤ)).foldr (fun z x => z+2*x) 0=0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ,ih]
  have bits_zero_value (k : ℕ) (out : Bool) :
      (List.replicate k ((0,0) : ℕ × ℕ)).foldr (fun z x => (if out then z.2 else z.1)+2*x) 0=0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ,ih]
  have zero_path (k : ℕ) : Nonempty (cutBitAutomaton.Path 0 0 (List.replicate k (0,0))) := by
    induction k with
    | zero => exact ⟨.nil 0⟩
    | succ k ih =>
      obtain ⟨p⟩:=ih
      exact ⟨.cons 0 0 0 (0,0) _ (by simp [cutBitAutomaton,relNext]) p⟩
  have app {r u v : ℤ} {xs ys : List (ℕ × ℕ)}
      (p : cutBitAutomaton.Path r u xs) (q : cutBitAutomaton.Path u v ys) :
      Nonempty (cutBitAutomaton.Path r v (xs++ys)) := by
    induction p with
    | nil r => exact ⟨q⟩
    | cons u r z a xs he p ih =>
      obtain ⟨pr⟩:=ih q
      exact ⟨.cons u r v a (xs++ys) he pr⟩
  obtain ⟨zp⟩:=zero_path pad
  obtain ⟨pb⟩:=app p zp
  have hbN : bs.foldr (fun a x => a.1+2*x) 0=n/2 := by
    have hh : (List.replicate pad ((0,0):ℕ × ℕ)).foldr (fun a x => a.1+2*x) 0=0 := by
      simpa using bits_zero_value pad false
    simpa only [bs,List.foldr_append,hh] using hN
  have hbJ : bs.foldr (fun a x => a.2+2*x) 0=j/2 := by
    have hh : (List.replicate pad ((0,0):ℕ × ℕ)).foldr (fun a x => a.2+2*x) 0=0 := by
      simpa using bits_zero_value pad true
    simpa only [bs,List.foldr_append,hh] using hJ
  have hbbits : ∀ a ∈ bs, a.1 ≤ 1 ∧ a.2 ≤ 1 := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hbits a ha
    · have hh: a=(0,0) := (List.mem_replicate.mp ha).2
      subst a;decide
  have bound (xs : List (ℕ × ℕ)) (hb : ∀ a ∈ xs, a.1 ≤ 1 ∧ a.2 ≤ 1) :
      xs.foldr (fun a x => a.1+2*x) 0 < 2^xs.length := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      have ha:=hb a (by simp)
      have ht:=ih (fun b hb' => hb b (by simp [hb']))
      simp only [List.foldr_cons,List.length_cons,pow_succ]
      omega
  have hnlt : n/2 < 2^L := by simpa only [hN,L] using bound bits hbits
  have hybound : 3*((j+1)/2) < 2^((L+h+2)+1) := by
    have hY : (j+1)/2 ≤ 2^L := by omega
    have hpow : 2^(L+3) ≤ 2^((L+h+2)+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have he : 2^(L+3)=8*2^L := by ring
    have hz : 0 < 2^L := by positivity
    rw [he] at hpow
    omega
  obtain ⟨hv,hs,_⟩:=triple_digits_value_and_minimality ((n+1)/2) h hbound
  obtain ⟨hyv,hys,_⟩:=triple_digits_value_and_minimality ((j+1)/2) (L+h+2) hybound
  have coeff (X h : ℕ) : ∀ z ∈ tripleSignedDigits X h, z=-1 ∨ z=0 ∨ z=1 := by
    intro z hz
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hz
    have ha:=Nat.mod_lt (3*X/2^(i.val+1)) (by decide : 0 < 2)
    have hb:=Nat.mod_lt (X/2^(i.val+1)) (by decide : 0 < 2)
    omega
  have hcn : ∀ z ∈ dns, z=-1 ∨ z=0 ∨ z=1 := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · simp
    · rcases List.mem_append.mp hz with hz | hz
      · exact coeff ((n+1)/2) h z hz
      · exact Or.inr (Or.inl (List.mem_replicate.mp hz).2)
  have hcj : ∀ z ∈ djs, z=-1 ∨ z=0 ∨ z=1 := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · simp
    · exact coeff ((j+1)/2) (L+h+2) z hz
  have hpad : (ds++List.replicate (L+2) 0).IsChain (fun a b => a=0 ∨ b=0) := by
    refine hs.append (List.isChain_replicate_of_rel _ (Or.inl rfl)) ?_
    intro a ha b hb
    exact Or.inr (List.mem_replicate.mp (List.mem_of_mem_head? hb)).2
  have prepend (ds : List ℤ) (hs : ds.IsChain (fun a b => a=0 ∨ b=0)) :
      (0::ds).IsChain (fun a b => a=0 ∨ b=0) := by
    cases ds with
    | nil => exact List.IsChain.singleton 0
    | cons d ds => exact List.isChain_cons_cons.mpr ⟨Or.inl rfl,hs⟩
  have hsn : dns.IsChain (fun a b => a=0 ∨ b=0) := prepend _ hpad
  have hsj : djs.IsChain (fun a b => a=0 ∨ b=0) := prepend _ hys
  have hclass0 : ∀ i : ℕ, ds[i]?.getD 0*ds[i+2]?.getD 0 ≠ -1 :=
    class_two_spacing ds hs (by
      have hlen : ds.length=h := by simp [ds,tripleSignedDigits]
      rw [hlen]
      exact hS)
  have hclass : ((0::0::dns).zip (0::0::dns).tail).IsChain (fun a b => a.1*b.2 ≠ -1) :=
    spacing_chain _ (cons_zero_spacing _ (cons_zero_spacing _ (cons_zero_spacing _
      (zero_padding_spacing ds hclass0 (L+2)))))
  have hvn : dns.foldr (fun z x => z+2*x) 0=2*(((n+1)/2 : ℕ) : ℤ) := by
    simp only [dns,List.foldr_cons,zero_add,List.foldr_append,zero_value]
    exact congrArg (fun x : ℤ => 2*x) (show ds.foldr (fun z x => z+2*x) 0=(((n+1)/2 : ℕ) : ℤ) from hv)
  have hvj : djs.foldr (fun z x => z+2*x) 0=2*(((j+1)/2 : ℕ) : ℤ) := by
    simp only [djs,List.foldr_cons,zero_add]
    exact congrArg (fun x : ℤ => 2*x) (show ys.foldr (fun z x => z+2*x) 0=(((j+1)/2 : ℕ) : ℤ) from hyv)
  exact base_bit_path_realization n j r bs hr ⟨pb⟩ hbbits hbN hbJ dns djs
    (by simp [dns,ds,bs,tripleSignedDigits,L,pad];omega)
    (by simp [djs,ys,bs,tripleSignedDigits,L,pad];omega)
    hcn hcj hsn hsj hclass hvn hvj

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.cut_representation_completeness
