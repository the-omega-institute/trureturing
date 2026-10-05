/- GID: D5/S1/Words/Palindromes/PeriodDoubling/BaseDigitRealization
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/BaseDigitRealization
   mirror-E: none(waiver:unbounded-carry-and-digit-realization)
   anchors: []
   utility: none
   digest: Sparse signed expansions lift bit-relation paths to accepting arithmetic graph paths. -/

/-
proof_shape: content (base_bit_path_realization)
escape_witness: Carry induction identifies every emitted digit and rules out all input rejections.
admission_basis: escape-witness
Direct frozen dependencies: none; imported period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.CutBitRelation
import D5.S1.Words.Palindromes.PeriodDoubling.BasePathRealization
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling

open BaseCertificates

/-- Valid sparse expansions and input spacing realize every accepting cut-bit path. -/
theorem base_bit_path_realization (n j : ℕ) (r : ℤ) (bits : List (ℕ × ℕ))
    (hr : r ∈ (if n%2=j%2 then [6] else if n%2>j%2 then [1,2,0] else [1,2] : List ℤ))
    (hp : Nonempty (cutBitAutomaton.Path r 0 bits))
    (hbits : ∀ a ∈ bits, a.1 ≤ 1 ∧ a.2 ≤ 1)
    (hn : bits.foldr (fun a x => a.1+2*x) 0=n/2)
    (hj : bits.foldr (fun a x => a.2+2*x) 0=j/2)
    (dns djs : List ℤ) (hln : dns.length=bits.length) (hlj : djs.length=bits.length)
    (hcn : ∀ z ∈ dns, z=-1 ∨ z=0 ∨ z=1)
    (hcj : ∀ z ∈ djs, z=-1 ∨ z=0 ∨ z=1)
    (hsn : dns.IsChain (fun a b => a=0 ∨ b=0))
    (hsj : djs.IsChain (fun a b => a=0 ∨ b=0))
    (hclass : ((0::0::dns).zip (0::0::dns).tail).IsChain (fun a b => a.1*b.2 ≠ -1))
    (hvn : dns.foldr (fun z x => z+2*x) 0=2*(((n+1)/2 : ℕ) : ℤ))
    (hvj : djs.foldr (fun z x => z+2*x) 0=2*(((j+1)/2 : ℕ) : ℤ)) :
    ∃ (charge : Bool) (s t : Fin 1492) (xs : List (ℤ × ℤ × ℤ × ℤ)),
      s ∈ (baseAutomaton charge).start ∧ t ∈ (baseAutomaton charge).accept ∧
      Nonempty ((baseAutomaton charge).Path s t xs) ∧
      (baseTable s.val).1[2]?.getD 0=((n%2 : ℕ) : ℤ) ∧
      (baseTable s.val).1[3]?.getD 0=((j%2 : ℕ) : ℤ) ∧
      xs.foldr (fun a x => a.2.2.1+2*x) 0=((n/2 : ℕ) : ℤ) ∧
      xs.foldr (fun a x => a.2.2.2+2*x) 0=((j/2 : ℕ) : ℤ) := by
  obtain ⟨p⟩ := hp
  let RN (s : List ℤ) (bits : List (ℕ × ℕ)) : ℤ :=
    2*((bits.foldr (fun a x => a.1+2*x) 0 : ℕ)+(s[4]?.getD 0))+
      s[6]?.getD 0+s[8]?.getD 0
  let RJ (s : List ℤ) (bits : List (ℕ × ℕ)) : ℤ :=
    2*((bits.foldr (fun a x => a.2+2*x) 0 : ℕ)+(s[5]?.getD 0))+
      s[7]?.getD 0+s[9]?.getD 0
  have head_digit (d : ℤ) (ds : List ℤ) (a V : ℤ)
      (hd : d=-1 ∨ d=0 ∨ d=1) (ha : a=-1 ∨ a=0 ∨ a=1)
      (hs : (d::ds).IsChain (fun a b => a=0 ∨ b=0))
      (hpar : a ≠ 0 → V%2=0)
      (hv : d+2*ds.foldr (fun z x => z+2*x) 0=a+2*V) : d=a := by
    have heven : d ≠ 0 → ds.foldr (fun z x => z+2*x) 0%2=0 := by
      intro hdn
      cases ds with
      | nil => simp
      | cons e ds =>
        have he : e=0 := (List.isChain_cons_cons.mp hs).1.resolve_left hdn
        simp only [List.foldr_cons,he]
        omega
    rcases hd with rfl | rfl | rfl <;> rcases ha with rfl | rfl | rfl <;> omega
  have run {r u : ℤ} {bits : List (ℕ × ℕ)} (p : cutBitAutomaton.Path r u bits)
      (hu : u=0) (s : List ℤ) (hrel : s[0]?.getD 0=r)
      (hb : ∀ a ∈ bits, a.1 ≤ 1 ∧ a.2 ≤ 1)
      (hc : ∀ k ∈ ([4,5,6,7,8,9] : List ℕ), 0 ≤ s[k]?.getD 0 ∧ s[k]?.getD 0 ≤ 1)
      (dn dj : List ℤ) (hln : dn.length=bits.length) (hlj : dj.length=bits.length)
      (hcn : ∀ z ∈ dn, z=-1 ∨ z=0 ∨ z=1)
      (hcj : ∀ z ∈ dj, z=-1 ∨ z=0 ∨ z=1)
      (hsn : dn.IsChain (fun a b => a=0 ∨ b=0))
      (hsj : dj.IsChain (fun a b => a=0 ∨ b=0))
      (hclass : (((s[11]?.getD 0)::(s[10]?.getD 0)::dn).zip
        ((s[11]?.getD 0)::(s[10]?.getD 0)::dn).tail).IsChain (fun a b => a.1*b.2 ≠ -1))
      (hvn : dn.foldr (fun z x => z+2*x) 0=RN s bits)
      (hvj : dj.foldr (fun z x => z+2*x) 0=RJ s bits) :
      ∃ (t : List ℤ) (xs : List (ℤ × ℤ × ℤ × ℤ)),
        Nonempty (baseRawAutomaton.Path s t xs) ∧ baseTerminal t=true ∧
        xs.foldr (fun a x => a.2.2.1+2*x) 0=((bits.foldr (fun a x => a.1+2*x) 0 : ℕ) : ℤ) ∧
        xs.foldr (fun a x => a.2.2.2+2*x) 0=((bits.foldr (fun a x => a.2+2*x) 0 : ℕ) : ℤ) := by
    induction p generalizing s dn dj with
    | nil r =>
      rw [hu] at hrel
      have hd : dn=[] := List.eq_nil_of_length_eq_zero (by simpa using hln)
      have he : dj=[] := List.eq_nil_of_length_eq_zero (by simpa using hlj)
      rw [hd] at hvn
      rw [he] at hvj
      have hc4 := (hc 4 (by simp)).1
      have hc5 := (hc 5 (by simp)).1
      have hc6 := (hc 6 (by simp)).1
      have hc7 := (hc 7 (by simp)).1
      have hc8 := (hc 8 (by simp)).1
      have hc9 := (hc 9 (by simp)).1
      dsimp [RN,RJ] at hvn hvj
      have zeros : s[4]?.getD 0=0 ∧ s[5]?.getD 0=0 ∧ s[6]?.getD 0=0 ∧
          s[7]?.getD 0=0 ∧ s[8]?.getD 0=0 ∧ s[9]?.getD 0=0 := by omega
      refine ⟨s,[],⟨.nil s⟩,?_,rfl,rfl⟩
      simp only [baseTerminal,hrel,beq_self_eq_true,Bool.true_and,List.all_eq_true]
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [zeros]
    | cons q r u a bits he p ih =>
      cases dn with
      | nil => simp at hln
      | cons d dn =>
        cases dj with
        | nil => simp at hlj
        | cons e dj =>
          have ha:=hb a (by simp)
          have hc4:=hc 4 (by simp)
          have hc5:=hc 5 (by simp)
          have hc6:=hc 6 (by simp)
          have hc7:=hc 7 (by simp)
          have hc8:=hc 8 (by simp)
          have hc9:=hc 9 (by simp)
          let nv : ℤ := a.1+s[4]?.getD 0
          let jv : ℤ := a.2+s[5]?.getD 0
          let xn : ℤ := nv%2
          let xj : ℤ := jv%2
          let nt : ℤ := xn+s[6]?.getD 0+s[8]?.getD 0
          let jt : ℤ := xj+s[7]?.getD 0+s[9]?.getD 0
          let nd : ℤ := nt%2-xn
          let jd : ℤ := jt%2-xj
          have hnd : nd=-1 ∨ nd=0 ∨ nd=1 := by dsimp [nd,xn];omega
          have hjd : jd=-1 ∨ jd=0 ∨ jd=1 := by dsimp [jd,xj];omega
          have hnp : nd ≠ 0 → (2*((bits.foldr (fun a x => a.1+2*x) 0 : ℕ)+nv/2)+xn+nt/2)%2=0 := by
            dsimp [nd,nt,xn]
            omega
          have hjp : jd ≠ 0 → (2*((bits.foldr (fun a x => a.2+2*x) 0 : ℕ)+jv/2)+xj+jt/2)%2=0 := by
            dsimp [jd,jt,xj]
            omega
          have hstepN : RN s (a::bits)=nd+2*(2*((bits.foldr (fun a x => a.1+2*x) 0 : ℕ)+nv/2)+xn+nt/2) := by
            dsimp [RN,nd,nt,xn,nv]
            push_cast
            omega
          have hstepJ : RJ s (a::bits)=jd+2*(2*((bits.foldr (fun a x => a.2+2*x) 0 : ℕ)+jv/2)+xj+jt/2) := by
            dsimp [RJ,jd,jt,xj,jv]
            push_cast
            omega
          have hd : d=nd := head_digit d dn nd _ (hcn d (by simp)) hnd hsn hnp
            (by simpa only [List.foldr_cons,hstepN] using hvn)
          have hjd' : e=jd := head_digit e dj jd _ (hcj e (by simp)) hjd hsj hjp
            (by simpa only [List.foldr_cons,hstepJ] using hvj)
          subst d;subst e
          simp only [List.tail_cons,List.zip_cons_cons] at hclass
          have hreject : nd*s[11]?.getD 0 ≠ -1 := by
            have hh := (List.isChain_cons_cons.mp hclass).1
            simpa only [mul_comm] using hh
          let f : ℤ := (Bool.toNat (nd != 0) : ℤ)-(Bool.toNat (jd != 0) : ℤ)
          let nq : ℤ := if nd=0 then 0 else 1+2*s[1]?.getD 0+
            (Bool.toNat (s[16]?.getD 0 != 0 && s[16]?.getD 0 != nd) : ℤ)
          let jq : ℤ := if jd=0 then 0 else 1+2*s[1]?.getD 0+
            (Bool.toNat (s[17]?.getD 0 != 0 && s[17]?.getD 0 != jd) : ℤ)
          let ns : List ℤ := [q,1-s[1]?.getD 0,s[2]?.getD 0,s[3]?.getD 0,nv/2,jv/2,xn,xj,nt/2,jt/2,
            nd,s[10]?.getD 0,jd,s[12]?.getD 0,
            (if s[14]?.getD 0=0 then nd else s[14]?.getD 0),
            (if s[15]?.getD 0=0 then jd else s[15]?.getD 0),
            (if nd=0 then s[16]?.getD 0 else nd),(if jd=0 then s[17]?.getD 0 else jd),
            (Bool.toNat (s[18]?.getD 0 != 0 || jd*s[13]?.getD 0 == -1) : ℤ)]
          let label : ℤ × ℤ × ℤ × ℤ := (f,jq-nq,a.1,a.2)
          have hnext : baseNext s a.1 a.2 q=some (ns,label) := by
            simp only [baseNext]
            change (if nd*s[11]?.getD 0 = -1 then none else some (ns,label))=some (ns,label)
            rw [if_neg hreject]
          have hedge : (ns,label) ∈ baseSuccessors s := by
            apply List.mem_flatMap.mpr
            refine ⟨(a.1 : ℤ),?_,?_⟩
            · simp only [List.mem_cons,List.mem_singleton]
              omega
            · apply List.mem_flatMap.mpr
              refine ⟨(a.2 : ℤ),?_,?_⟩
              · simp only [List.mem_cons,List.mem_singleton]
                omega
              · apply List.mem_filterMap.mpr
                refine ⟨q,?_,hnext⟩
                change q ∈ relNext r a.1 a.2 at he
                simpa only [hrel] using he
          have hcarry : ∀ k ∈ ([4,5,6,7,8,9] : List ℕ), 0 ≤ ns[k]?.getD 0 ∧ ns[k]?.getD 0 ≤ 1 := by
            intro k hk
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp only [ns,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] <;>
              dsimp [nv,jv,nt,jt,xn,xj] <;> omega
          have hvn' : dn.foldr (fun z x => z+2*x) 0=RN ns bits := by
            rw [hstepN] at hvn
            simp only [List.foldr_cons] at hvn
            simp [RN,ns]
            omega
          have hvj' : dj.foldr (fun z x => z+2*x) 0=RJ ns bits := by
            rw [hstepJ] at hvj
            simp only [List.foldr_cons] at hvj
            simp [RJ,ns]
            omega
          have hclass' : (((ns[11]?.getD 0)::(ns[10]?.getD 0)::dn).zip
              ((ns[11]?.getD 0)::(ns[10]?.getD 0)::dn).tail).IsChain (fun a b => a.1*b.2 ≠ -1) := by
            simpa [ns,List.zip_cons_cons] using hclass.tail
          obtain ⟨t,xs,⟨pr⟩,ht,hN,hJ⟩ := ih hu ns (by simp [ns])
            (fun z hz => hb z (by simp [hz])) hcarry dn dj (by simpa using hln) (by simpa using hlj)
            (fun z hz => hcn z (by simp [hz])) (fun z hz => hcj z (by simp [hz]))
            hsn.tail hsj.tail hclass' hvn' hvj'
          refine ⟨t,label::xs,⟨.cons ns s t label xs hedge pr⟩,ht,?_,?_⟩
          · simp only [List.foldr_cons,hN,label]
            push_cast
            rfl
          · simp only [List.foldr_cons,hJ,label]
            push_cast
            rfl
  let s : List ℤ := [r,1,n%2,j%2,n%2,j%2,0,0,0,0,0,0,0,0,0,0,0,0,0]
  have hs : s ∈ baseRawAutomaton.start := by
    change s ∈ initialStates
    apply List.mem_flatMap.mpr
    refine ⟨((n%2 : ℕ) : ℤ),by simp;omega,?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨((j%2 : ℕ) : ℤ),by simp;omega,?_⟩
    apply List.mem_map.mpr
    refine ⟨r,?_,rfl⟩
    norm_cast
  have hcarry : ∀ k ∈ ([4,5,6,7,8,9] : List ℕ), 0 ≤ s[k]?.getD 0 ∧ s[k]?.getD 0 ≤ 1 := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [s] <;> omega
  have hRN : RN s bits=2*(((n+1)/2 : ℕ) : ℤ) := by
    simp [RN,s,hn]
    omega
  have hRJ : RJ s bits=2*(((j+1)/2 : ℕ) : ℤ) := by
    simp [RJ,s,hj]
    omega
  obtain ⟨t,xs,⟨pr⟩,ht,hN,hJ⟩ := run p rfl s (by simp [s]) hbits hcarry dns djs hln hlj hcn hcj hsn hsj
    (by simpa [s] using hclass) (hvn.trans hRN.symm) (hvj.trans hRJ.symm)
  obtain ⟨charge,i,k,hi,hk,his,hkt,hp⟩ := base_path_realization hs ht pr
  refine ⟨charge,i,k,xs,hi,hk,hp,?_,?_,?_,?_⟩
  · simp [his,s]
  · simp [his,s]
  · simpa only [hn] using hN
  · simpa only [hj] using hJ

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.base_bit_path_realization
