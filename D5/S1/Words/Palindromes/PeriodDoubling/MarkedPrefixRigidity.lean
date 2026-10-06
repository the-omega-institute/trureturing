/- GID: D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixRigidity
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixRigidity
   mirror-E: none(waiver:literal-marked-prefix-transition)
   anchors: []
   utility: none
   digest: Tight odd cuts preserve a marked prefix or remove its lowest digit with exact charge. -/

/-
proof_shape: content (marked_prefix_rigidity_and_charge)
escape_witness: The selected position, two lower expansions and saved phases reconstruct both alternatives.
admission_basis: escape-witness
Direct frozen dependencies: none; the period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.MarkedPrefixExpansion
import D5.S1.Words.Palindromes.PeriodDoubling.MarkedInputAnnotation
import D5.S1.Words.Palindromes.PeriodDoubling.CutRepresentation
import D5.S1.Words.Palindromes.PeriodDoubling.BaseArithmetic
import D5.S1.Words.Palindromes.PeriodDoubling.MarkedPathSelection
import D5.S1.Words.Palindromes.PeriodDoubling.MarkedBaseProjection
import D5.S1.Words.Palindromes.PeriodDoubling.BasePositionMemory
import D5.S1.Words.Palindromes.PeriodDoubling.UnmarkedFlipSemantics
import D5.S1.Words.Palindromes.PeriodDoubling.SignedDigitPhase
namespace D5.S1.Words.Palindromes.PeriodDoubling
open BaseCertificates MarkedPrefixCertificates
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem marked_prefix_rigidity_and_charge (n j m q : ℕ) (T : ℤ) (hm : 0 < m) (hS : classS n)
    (hmark : markedPrefix n m q T) (hjn : j<n) (hodd : n%2≠j%2)
    (hpal : List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i))))
    (htight : signedWeight (((n+1)/2 : ℕ) : ℤ)=signedWeight (((j+1)/2 : ℕ) : ℤ)+1) :
    let eta : ℕ → ℤ → ℤ := fun n T => if 2*T-((n%2 : ℕ) : ℤ)<0 then 1 else 0
    let wp : ℕ → ℤ := fun p => 1+2*((p%2 : ℕ) : ℤ)
    (∃ Tj : ℤ, markedPrefix j m q Tj ∧
      (signedDigitCharge j : ℤ)-(signedDigitCharge n : ℤ)+(wp q-1)*(eta j Tj-eta n T)≤0) ∨
    (markedPrefix j (m-1) (q+3) (-T) ∧ eta n T=1 ∧ eta j (-T)=0 ∧
      (signedDigitCharge j : ℤ)-(signedDigitCharge n : ℤ)+wp q+1≤0) := by
  dsimp only
  have reconstruct (j r p k : ℕ) (low : List ℤ) (d : ℤ)
      (hlen : low.length=p)
      (hc : ∀ z ∈ low,z=-1 ∨ z=0 ∨ z=1)
      (hs : low.IsChain (fun a b => a=0 ∨ b=0))
      (hz0 : ((0:ℤ)::low).reverse[0]?.getD 0=0)
      (hz1 : ((0:ℤ)::low).reverse[1]?.getD 0=0)
      (hv : (((0:ℤ)::low)++([d,0,0]++(List.replicate r [1,0,0]).flatten++List.replicate k 0)).foldr
        (fun z x => z+2*x) 0=2*(((j+1)/2 : ℕ) : ℤ)) :
      (d=1 → markedPrefix j (r+1) p (low.foldr (fun z x => z+2*x) 0)) ∧
      (d=0 → markedPrefix j r (p+3) (low.foldr (fun z x => z+2*x) 0)) := by
    clear * - j r p k low d hlen hc hs hz0 hz1 hv
    have support (i : ℕ) (hi : low[i]?.getD 0≠0) : i+3≤p := by
      have hil : i<low.length := by
        by_contra hh
        have hnone : low[i]? = none := List.getElem?_eq_none (by omega)
        simp only [hnone,Option.getD_none,ne_self_iff_false] at hi
      by_contra hh
      have he : i+1=p ∨ i+2=p := by omega
      rcases he with he|he
      · have hx := hz0
        rw [List.getElem?_reverse (by simp)] at hx
        have e : ((0:ℤ)::low).length-1-0=i+1 := by simp [hlen];omega
        rw [e] at hx
        simp only [List.getElem?_cons_succ] at hx
        exact hi hx
      · have hx := hz1
        rw [List.getElem?_reverse (by simp [hlen];omega)] at hx
        have e : ((0:ℤ)::low).length-1-1=i+1 := by simp [hlen];omega
        rw [e] at hx
        simp only [List.getElem?_cons_succ] at hx
        exact hi hx
    have zero (k : ℕ) : (List.replicate k (0:ℤ)).foldr (fun z x => z+2*x) 0=0 := by
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ,ih]
    have seed (xs : List ℤ) (v : ℤ) :
        xs.foldr (fun z x => z+2*x) v = xs.foldr (fun z x => z+2*x) 0+2^xs.length*v := by
      induction xs with
      | nil => simp
      | cons x xs ih => simp only [List.foldr_cons,List.length_cons,pow_succ,ih];ring
    have blockval (m : ℕ) : ((List.replicate m ([1,0,0] : List ℤ)).flatten).foldr
        (fun z x => z+2*x) 0=(markedPowers m 0 : ℤ) := by
      induction m with
      | zero => simp [markedPowers]
      | succ m ih =>
        have recurrence : markedPowers (m+1) 0=8*markedPowers m 0+1 := by
          unfold markedPowers
          rw [Finset.sum_range_succ']
          simp only [Nat.zero_add,Nat.mul_add,Nat.mul_one,pow_add]
          simp only [show (2:ℕ)^3=8 by decide,← Finset.sum_mul]
          ring
        simp only [List.replicate_succ,List.flatten_cons,List.cons_append,List.nil_append,List.foldr_cons,ih,recurrence]
        push_cast;ring
    have scale (m p : ℕ) : markedPowers m p=2^p*markedPowers m 0 := by
      simp only [markedPowers,Nat.zero_add,pow_add,Finset.mul_sum]
    have recurrence : markedPowers (r+1) p=markedPowers r (p+3)+2^p := by
      unfold markedPowers
      rw [Finset.sum_range_succ']
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1;omega
    have hvalue : 2*low.foldr (fun z x => z+2*x) 0+
        (2:ℤ)^(p+1)*(d+8*(markedPowers r 0 : ℤ))=2*(((j+1)/2 : ℕ) : ℤ) := by
      rw [List.foldr_append,seed] at hv
      simp only [List.foldr_append,zero,blockval,List.foldr_cons,List.foldr_nil,zero_add,List.length_cons,hlen] at hv
      convert hv using 1 <;> ring
    have high : (markedPowers r (p+3) : ℤ)=(2:ℤ)^p*8*(markedPowers r 0 : ℤ) := by
      rw [scale];push_cast;ring
    constructor
    · intro hd
      refine ⟨?_,low,rfl,hc,hs,support⟩
      rw [hd,pow_succ] at hvalue
      rw [recurrence]
      simp only [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat]
      rw [high]
      nlinarith
    · intro hd
      refine ⟨?_,low,rfl,hc,hs,fun i hi => Nat.le_trans (support i hi) (by omega)⟩
      rw [hd,pow_succ] at hvalue
      rw [high]
      nlinarith
  have phase (ds : List ℤ) (delta : ℕ) (T : ℤ) (hd : delta≤1)
      (hc : ∀ z ∈ ds,z=-1 ∨ z=0 ∨ z=1)
      (hv : ds.foldr (fun z x => z+2*x) 0=2*T) :
      (Bool.toNat ((ds.filter (fun z => z != 0)).getLast?.getD 0 < 0 ||
        ((ds.filter (fun z => z != 0)).getLast?.getD 0 == 0 && (delta : ℤ) == 1)) : ℤ) =
        if 2*T-(delta : ℤ)<0 then 1 else 0 := by
    clear * - ds delta T hd hc hv
    let last := (ds.filter (fun z => z != 0)).getLast?.getD 0
    have empty : last=0 ↔ ds.filter (fun z => z != 0)=[] := by
      constructor
      · intro hz
        cases he : (ds.filter (fun z => z != 0)).getLast? with
        | none => exact List.getLast?_eq_none_iff.mp he
        | some z =>
          have hzmem := List.mem_of_mem_getLast? (show z ∈ (ds.filter (fun z => z != 0)).getLast? from by rw [he];simp)
          have hn : z≠0 := by simpa using (List.mem_filter.mp hzmem).2
          have hh : z=0 := by simpa [last,he] using hz
          exact (hn hh).elim
      · intro hz
        simp [last,hz]
    have hdelta : (Bool.toNat (delta==1) : ℤ)=(delta : ℤ) := by
      have hh : delta=0 ∨ delta=1 := by omega
      rcases hh with rfl|rfl <;> rfl
    have hphase:=signed_digits_negative_phase ds (delta==1) hc
    rw [hv,hdelta] at hphase
    have eqphase : (2*(2*T)-(delta : ℤ)<0) ↔ (2*T-(delta : ℤ)<0) := by omega
    rw [eqphase] at hphase
    have phasebool : (last < 0 || (last==0 && (delta : ℤ)==1))=true ↔ 2*T-(delta : ℤ)<0 := by
      simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
      rw [empty]
      have heq : ((delta : ℤ)=1) ↔ delta=1 := by omega
      rw [heq]
      simpa only [last,beq_iff_eq] using hphase.symm
    change (Bool.toNat (last < 0 || (last==0 && (delta : ℤ)==1)) : ℤ)=_
    by_cases hp : 2*T-(delta : ℤ)<0
    · rw [phasebool.mpr hp]
      simp only [Bool.toNat_true,Int.natCast_one,if_pos hp]
    · have hb : (last < 0 || (last==0 && (delta : ℤ)==1))=false := by
        cases he : (last < 0 || (last==0 && (delta : ℤ)==1))
        · rfl
        · exact (hp (phasebool.mp he)).elim
      rw [hb]
      simp only [Bool.toNat_false,Int.natCast_zero,if_neg hp]
  have selectindex (modes suffix : List ℤ) (q k : ℕ)
      (hm : modes=List.replicate k 0++1::suffix)
      (hbefore : modes.take q=List.replicate q 0)
      (hselected : modes[q]?=some 1) : k=q := by
    by_cases hlt : k<q
    · have hv:=congrArg (fun l : List ℤ => l[k]?) hbefore
      simp only [List.getElem?_take,if_pos hlt,List.getElem?_replicate,if_pos hlt] at hv
      rw [hm] at hv
      simp only [List.getElem?_append,List.length_replicate,Nat.lt_irrefl,if_false,Nat.sub_self,
        List.getElem?_cons_zero] at hv
      contradiction
    · by_cases hgt : q<k
      · rw [hm] at hselected
        simp only [List.getElem?_append,List.length_replicate,if_pos hgt,List.getElem?_replicate,if_pos hgt] at hselected
        contradiction
      · omega
  obtain ⟨charge,s,t,xs,hs,ht,⟨bp⟩,hsn,hsj,hn,hjv,hlen⟩ :=
    cut_representation_completeness n j hS hjn hpal (q+3*m+2)
  have hN : xs.foldr (fun a x => a.2.2.1+2*x) 0+(baseTable s.val).1[2]?.getD 0=(((n+1)/2 : ℕ) : ℤ) := by
    rw [hn,hsn]
    clear * - n
    omega
  have hJ : xs.foldr (fun a x => a.2.2.2+2*x) 0+(baseTable s.val).1[3]?.getD 0=(((j+1)/2 : ℕ) : ℤ) := by
    rw [hjv,hsj]
    clear * - j
    omega
  have hf:=base_path_signed_weight_difference charge hs ht bp
  rw [hN,hJ] at hf
  have hf' : pathCharge (fun _ a _ => a.1) bp=1 := by
    clear * - hf htight
    omega
  cases charge with
  | false =>
    have hb:=base_accepted_bound false hs ht bp
    simp only [Bool.false_eq_true,if_false,one_mul,add_zero] at hb
    clear * - hb hf'
    omega
  | true =>
    let ds:=pathOutputs (fun _ _ (r : Fin 1492) => (baseTable r.val).1[10]?.getD 0) bp
    obtain ⟨hc,hsp,hv,hh⟩ := base_path_sparse_signed_digits true false hs ht bp
    change (∀ z ∈ ds,z=-1 ∨ z=0 ∨ z=1) at hc
    change ds.IsChain (fun a b => a=0 ∨ b=0) at hsp
    change ds.foldr (fun z x => z+2*x) 0=2*(xs.foldr (fun a x => a.2.2.1+2*x) 0+(baseTable s.val).1[2]?.getD 0) at hv
    rw [hN] at hv
    have length {σ : Type} {M : NFA (ℤ × ℤ × ℤ × ℤ) σ} {s t : σ}
        {xs : List (ℤ × ℤ × ℤ × ℤ)} (p : M.Path s t xs)
        (f : σ → (ℤ × ℤ × ℤ × ℤ) → σ → ℤ) : (pathOutputs f p).length=xs.length := by
      induction p with
      | nil => rfl
      | cons u s t a xs he p ih => simp only [pathOutputs,List.length_cons,ih]
    have dslen : ds.length=xs.length := length bp _
    obtain ⟨lower,k,hll,hlv,hlp,hshape,hgap0,hgap1⟩:=marked_prefix_expansion n m q T hmark ds hc hsp hv (by simpa only [dslen] using hlen)
    have hsvals : s.val=0 ∨ s.val=1 ∨ s.val=2 ∨ s.val=3 ∨ s.val=4 ∨ s.val=5 ∨ s.val=6 := by
      change ([0,1,2,3,4,5,6] : List ℕ).contains s.val=true at hs
      simpa using hs
    have hsv : s.val=1 ∨ s.val=2 ∨ s.val=3 ∨ s.val=4 ∨ s.val=5 := by
      rcases hsvals with hh|hh|hh|hh|hh|hh|hh
      · rw [hh] at hsn hsj
        norm_num [baseTable] at hsn hsj
        clear * - hodd hsn hsj
        omega
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr (Or.inl hh))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hh)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hh)))
      · rw [hh] at hsn hsj
        norm_num [baseTable] at hsn hsj
        clear * - hodd hsn hsj
        omega
    let u : Fin 4262:=⟨s.val-1,by
      rcases hsv with hh|hh|hh|hh|hh <;> simp only [hh] <;> decide⟩
    have hu0 : (prefixTable u.val).1[0]?.getD 0=(s.val : ℤ) := by
      rcases hsv with hh|hh|hh|hh|hh <;> simp [u,hh,prefixTable]
    have hum : (prefixTable u.val).1[1]?.getD 0=0 := by
      rcases hsv with hh|hh|hh|hh|hh <;> simp [u,hh,prefixTable]
    have hzeros : (baseTable s.val).1[11]?.getD 0=0 ∧ (baseTable s.val).1[10]?.getD 0=0 := by
      rcases hsv with hh|hh|hh|hh|hh <;> simp [hh,baseTable]
    obtain ⟨full,hfull0,hfullm,rp,hbefore,hselected⟩ := marked_input_path_annotation bp (prefixTable u.val).1 hu0 hum ht lower m k hm
      (by simpa only [hzeros.1,hzeros.2] using And.intro hgap0 hgap1) hshape
    obtain ⟨v,hvfull,⟨pp⟩⟩:=prefix_path_realization true rp u rfl
    have hterminal : baseTerminal (baseTable ((prefixTable v.val).1[0]?.getD 0).toNat).1=true := by
      rw [hvfull,hfull0,Int.toNat_natCast]
      have ht' := ht
      simp only [baseAutomaton,Set.mem_ofPred_eq,Bool.and_eq_true] at ht'
      exact ht'.1
    have hv4 : (prefixTable v.val).1[1]?.getD 0=4 := by rw [hvfull];exact hfullm
    have hterm : terminal (prefixTable v.val).1=true := by
      unfold terminal
      rw [Bool.and_eq_true]
      exact ⟨by simpa only [beq_iff_eq] using hv4,hterminal⟩
    have flagstep {s q : List ℤ} {a : ℤ × ℤ × ℤ × ℤ}
        (he : (q,a) ∈ successors s) : q[7]?.getD 0=0 ∨ q[7]?.getD 0=1 := by
      have bit (b : Bool) : (b.toNat : ℤ)=0 ∨ (b.toNat : ℤ)=1 := by cases b <;> simp
      obtain ⟨e,he,hmem⟩:=List.mem_flatMap.mp he
      unfold nextMarker at hmem
      simp only [Bool.false_eq_true,ite_false,ite_true] at hmem
      split at hmem
      · simp at hmem
      · split at hmem
        · split at hmem
          · simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl,ha⟩|⟨rfl,ha⟩
            · exact Or.inl rfl
            · exact bit _
          · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
            obtain ⟨rfl,ha⟩:=hmem
            exact Or.inl rfl
        · split at hmem
          · split at hmem
            · simp at hmem
            · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
              obtain ⟨rfl,ha⟩:=hmem
              exact bit _
          · split at hmem
            · split at hmem
              · simp at hmem
              · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
                obtain ⟨rfl,ha⟩:=hmem
                exact bit _
            · split at hmem
              · simp at hmem
              · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
                obtain ⟨rfl,ha⟩:=hmem
                exact bit _
    have flagpath {s t : List ℤ} {xs : List (ℤ × ℤ × ℤ × ℤ)}
        (p : prefixRawAutomaton.Path s t xs) (hflag : s[7]?.getD 0=0 ∨ s[7]?.getD 0=1) :
        t[7]?.getD 0=0 ∨ t[7]?.getD 0=1 := by
      induction p with
      | nil => exact hflag
      | cons q s t a xs he p ih => exact ih (flagstep he)
    have hsourceflag : (prefixTable u.val).1[7]?.getD 0=0 := by
      rcases hsv with hh|hh|hh|hh|hh <;> simp [u,hh,prefixTable]
    have checked := flagpath rp (Or.inl hsourceflag)
    have charges {σ : Type} {M : NFA (ℤ × ℤ × ℤ × ℤ) σ}
        {s t : σ} {xs : List (ℤ × ℤ × ℤ × ℤ)} (p : M.Path s t xs) :
        pathCharge (fun _ a _ => a.1) p=(xs.map (fun a => a.1)).sum := by
      induction p with
      | nil => rfl
      | cons q s t a xs he p ih => simp only [pathCharge,List.map_cons,List.sum_cons,ih]
    have hrawf : pathCharge (fun _ a _ => a.1) rp=1 := by rw [charges,← charges bp];exact hf'
    have hppf : pathCharge (fun _ a _ => a.1) pp=1 := by rw [charges,← charges bp];exact hf'
    have hustart : u ∈ (prefixAutomaton true).start := by
      change u.val<5
      rcases hsv with hh|hh|hh|hh|hh <;> simp [u,hh]
    have switch {u v : Fin 4262} {xs : List (ℤ × ℤ × ℤ × ℤ)}
        (p : (prefixAutomaton true).Path u v xs) :
        Nonempty ((prefixAutomaton false).Path u v xs) := by
      induction p with
      | nil u => exact ⟨.nil u⟩
      | cons q u v a xs he p ih =>
        obtain ⟨p'⟩:=ih
        exact ⟨.cons q u v a xs he p'⟩
    have hgood : (prefixTable v.val).1[7]?.getD 0=0 := by
      rw [← hvfull] at checked
      rcases checked with hh|hh
      · exact hh
      · have hbad : v ∈ (prefixAutomaton false).accept := by
          change (terminal (prefixTable v.val).1 &&
            ((prefixTable v.val).1[7]?.getD 0 == 1))=true
          simp only [hterm,hh,beq_self_eq_true,Bool.true_and]
        obtain ⟨ppf⟩:=switch pp
        have hb:=prefix_accepted_bound false hustart hbad ppf
        simp only [Bool.false_eq_true,if_false,one_mul,add_zero] at hb
        rw [charges,← charges bp,hf'] at hb
        clear * - hb
        omega
    have hvaccept : v ∈ (prefixAutomaton true).accept := by
      change (terminal (prefixTable v.val).1 &&
        ((prefixTable v.val).1[7]?.getD 0 == 0))=true
      simp only [hterm,hgood,beq_self_eq_true,Bool.true_and]
    have hfullgood : full[7]?.getD 0=0 := by rw [← hvfull];exact hgood
    obtain ⟨r,z,as,bs,a,before,after,hxs,hr0,hz1,hedge,hzgood,
      hin,hout,hmodes,hpres,hnd,hr10,hr11,hr12,hr13,hpar,hkeep,hni,hnj,hbranches⟩ :=
      marked_path_selection rp hum hfullm hfullgood
    have hpos : as.length=q+1 := selectindex _ _ (q+1) as.length hmodes
      (by simpa only [hll] using hbefore) (by simpa only [hll] using hselected)
    obtain ⟨t',bq,hti,hemit⟩:=marker_base_projection true rp s hu0
    have hteq : t'=t := by
      apply Fin.ext
      exact Int.natCast_inj.mp (hti.symm.trans hfull0)
    subst t'
    have emitN:=hemit false
    have emitJ:=hemit true
    simp only [Bool.false_eq_true,ite_false,ite_true] at emitN emitJ
    have input_same : pathOutputs (fun _ _ (r : List ℤ) => (baseTable (r[0]?.getD 0).toNat).1[10]?.getD 0) rp=ds := by
      rw [emitN]
      obtain ⟨hc',hs',hv',_⟩:=base_path_sparse_signed_digits true false hs ht bq
      simp only [Bool.false_eq_true,ite_false,ite_true] at hc' hs' hv'
      apply nonadjacent_digits_unique _ ds hc' hc hs' hsp
      · exact (length bq _).trans dslen.symm
      · rw [hv]
        simpa only [hN] using hv'
    let outlow:=pathOutputs (fun _ _ (r : List ℤ) => (baseTable (r[0]?.getD 0).toNat).1[12]?.getD 0) before
    let inlow:=pathOutputs (fun _ _ (r : List ℤ) => (baseTable (r[0]?.getD 0).toNat).1[10]?.getD 0) before
    let higher:=pathOutputs (fun _ _ (r : List ℤ) => (baseTable (r[0]?.getD 0).toNat).1[10]?.getD 0) after
    change pathOutputs (fun _ _ (r : List ℤ) => (baseTable (r[0]?.getD 0).toNat).1[10]?.getD 0) rp =
      inlow ++ (baseTable (z[0]?.getD 0).toNat).1[10]?.getD 0 :: higher at hin
    change pathOutputs (fun _ _ (r : List ℤ) => (baseTable (r[0]?.getD 0).toNat).1[12]?.getD 0) rp =
      outlow ++ (baseTable (z[0]?.getD 0).toNat).1[12]?.getD 0 :: higher at hout
    have ilen : inlow.length=as.length := length before _
    have olen : outlow.length=as.length := length before _
    have iloweq : inlow=lower := by
      have hlens : as.length=lower.length := hpos.trans hll.symm
      have hh:=congrArg (List.take lower.length) hin
      rw [input_same,hshape,List.append_assoc,List.take_left] at hh
      rw [← hlens,← ilen,List.take_left] at hh
      exact hh.symm
    obtain ⟨ub,beforeB,hri,hbeforeemit⟩:=marker_base_projection true before s hu0
    have beforeN:=hbeforeemit false
    have beforeJ:=hbeforeemit true
    simp only [Bool.false_eq_true,ite_false,ite_true] at beforeN beforeJ
    have mem:=base_path_position_memory true hs beforeB
    have par : z[3]?.getD 0=((q%2 : ℕ) : ℤ) := by
      rw [hpar,hri,Int.toNat_natCast,mem.1,hpos]
      clear * - q
      omega
    obtain ⟨oc,osp,ov,oh⟩:=base_path_sparse_signed_digits true true hs ht bq
    simp only [ite_true] at oc osp ov oh
    have rawnOut : ∀ d ∈ pathOutputs (fun _ _ (r : List ℤ) => (baseTable (r[0]?.getD 0).toNat).1[12]?.getD 0) rp,
        d=-1 ∨ d=0 ∨ d=1 := by rw [emitJ];exact oc
    have rawOutValue : (pathOutputs (fun _ _ (r : List ℤ) => (baseTable (r[0]?.getD 0).toNat).1[12]?.getD 0) rp).foldr
        (fun d x => d+2*x) 0=2*(((j+1)/2 : ℕ) : ℤ) := by
      rw [emitJ]
      simpa only [hJ] using ov
    have outhead : outlow.head?=some 0 := by
      have hhh : (pathOutputs (fun _ _ (r : List ℤ) => (baseTable (r[0]?.getD 0).toNat).1[12]?.getD 0) rp).head?=some 0 := by
        rw [emitJ];exact oh
      rw [hout] at hhh
      cases he : outlow with
      | nil => have hh:=olen;rw [he,hpos] at hh;simp at hh
      | cons d es => simpa only [he,List.cons_append,List.head?_cons] using hhh
    have ocoef : ∀ d ∈ outlow,d=-1 ∨ d=0 ∨ d=1 := by
      intro d hd
      apply rawnOut
      rw [hout]
      exact List.mem_append_left _ hd
    have osparse : outlow.IsChain (fun a b => a=0 ∨ b=0) := by
      have hh : (pathOutputs (fun _ _ (r : List ℤ) => (baseTable (r[0]?.getD 0).toNat).1[12]?.getD 0) rp).IsChain
          (fun a b => a=0 ∨ b=0) := by rw [emitJ];exact osp
      rw [hout] at hh
      exact (List.isChain_append.mp hh).1
    have ozeros : outlow.reverse[0]?.getD 0=0 ∧ outlow.reverse[1]?.getD 0=0 := by
      have hm:=(mem.2.2.2 true)
      simp only [Bool.false_eq_true,ite_false,ite_true] at hm
      rw [← beforeJ] at hm
      rw [hri,Int.toNat_natCast] at hr12 hr13
      exact ⟨hm.1.symm.trans hr12,hm.2.1.symm.trans hr13⟩
    have icoef : ∀ d ∈ inlow,d=-1 ∨ d=0 ∨ d=1 := by
      intro d hd
      apply hc
      rw [hshape,← iloweq]
      exact List.mem_append_left _ (List.mem_append_left _ hd)
    have ilowvalue : inlow.foldr (fun d x => d+2*x) 0=2*T := by rw [iloweq];exact hlv
    have ni : z[5]?.getD 0=if 2*T-((n%2 : ℕ) : ℤ)<0 then 1 else 0 := by
      rw [hni,hri,Int.toNat_natCast,mem.2.1,hsn]
      have hm:=(mem.2.2.2 false).2.2
      simp only [Bool.false_eq_true,ite_false,ite_true] at hm
      rw [← beforeN] at hm
      rw [hm]
      exact phase inlow (n%2) T (by omega) icoef ilowvalue
    have qcharges {σ : Type} {M : NFA (ℤ × ℤ × ℤ × ℤ) σ}
        {s t : σ} {xs : List (ℤ × ℤ × ℤ × ℤ)} (p : M.Path s t xs) :
        pathCharge (fun _ a _ => a.2.1) p=(xs.map (fun a => a.2.1)).sum := by
      induction p with
      | nil => rfl
      | cons q s t a xs he p ih => simp only [pathCharge,List.map_cons,List.sum_cons,ih]
    have combined {σ : Type} {M : NFA (ℤ × ℤ × ℤ × ℤ) σ}
        {s t : σ} {xs : List (ℤ × ℤ × ℤ × ℤ)} (p : M.Path s t xs) :
        pathCharge (fun _ a _ => 5*a.1+a.2.1) p =
          5*pathCharge (fun _ a _ => a.1) p+pathCharge (fun _ a _ => a.2.1) p := by
      induction p with
      | nil => simp only [pathCharge];ring
      | cons q s t a xs he p ih => simp only [pathCharge,ih];ring
    have hq:=base_path_Q_semantics n j hs ht bq hsn hsj hn hjv
    have hbound:=prefix_accepted_bound true hustart hvaccept pp
    simp only [ite_true] at hbound
    rw [combined,hppf,qcharges,← qcharges bq] at hbound
    unfold prefixOffset at hbound
    rw [hvfull,hfull0,Int.toNat_natCast,hpres 3 (by omega) (by omega),
      hpres 4 (by omega) (by omega),hpres 5 (by omega) (by omega),hpres 6 (by omega) (by omega),par,ni] at hbound
    dsimp only at hbound
    have bound : (signedDigitCharge j : ℤ)-(signedDigitCharge n : ℤ)+
        (if z[4]?.getD 0 != 0 then
          (1+2*((q%2 : ℕ) : ℤ)-1)*(z[6]?.getD 0-(if 2*T-((n%2 : ℕ) : ℤ)<0 then 1 else 0))
         else (1+2*((q%2 : ℕ) : ℤ))+1)≤0 := by
      clear * - hbound hq
      omega
    cases m with
    | zero => omega
    | succ rcount =>
      have highereq : higher=[0,0]++(List.replicate rcount [1,0,0]).flatten++List.replicate (k+1) 0 := by
        have hh:=hin
        rw [input_same,hshape,List.append_assoc,← iloweq] at hh
        have tailEq:=List.append_cancel_left hh
        simp only [List.replicate_succ,List.flatten_cons,List.cons_append,List.nil_append,hnd] at tailEq
        exact (List.cons.inj tailEq).2.symm
      cases hoe : outlow with
      | nil => rw [hoe] at outhead;simp at outhead
      | cons d lo =>
        have hd : d=0 := by simpa only [hoe,List.head?_cons,Option.some.injEq] using outhead
        subst d
        have loLen : lo.length=q := by rw [hoe,hpos] at olen;simp at olen;omega
        have loCoeff : ∀ d ∈ lo,d=-1 ∨ d=0 ∨ d=1 := fun d hd => ocoef d (by rw [hoe];simp [hd])
        have loSparse : lo.IsChain (fun a b => a=0 ∨ b=0) := by rw [hoe] at osparse;exact osparse.tail
        let Tj:=lo.foldr (fun d x => d+2*x) 0
        have outlowvalue : outlow.foldr (fun d x => d+2*x) 0=2*Tj := by simp only [hoe,List.foldr_cons,zero_add,Tj]
        have nj : z[6]?.getD 0=if 2*Tj-((j%2 : ℕ) : ℤ)<0 then 1 else 0 := by
          rw [hnj,hri,Int.toNat_natCast,mem.2.2.1,hsj]
          have hm:=(mem.2.2.2 true).2.2
          simp only [Bool.false_eq_true,ite_false,ite_true] at hm
          rw [← beforeJ] at hm
          rw [hm]
          exact phase outlow (j%2) Tj (by omega) ocoef outlowvalue
        have outConstruct := reconstruct j rcount q (k+1) lo
          ((baseTable (z[0]?.getD 0).toNat).1[12]?.getD 0) loLen loCoeff loSparse
          (by simpa only [hoe] using ozeros.1) (by simpa only [hoe] using ozeros.2)
          (by simpa only [hout,hoe,highereq,List.append_assoc,List.cons_append,List.nil_append] using rawOutValue)
        rcases hbranches with hretain | ⟨hremove,hnphase,hjphase,hflip⟩
        · left
          refine ⟨Tj,outConstruct.1 hretain,?_⟩
          have keep : z[4]?.getD 0=1 := by rw [hkeep,hretain];rfl
          rw [keep,show ((1:ℤ)!=0)=true by decide] at bound
          simp only [ite_true] at bound
          rw [nj] at bound
          exact bound
        · right
          have negvalue (ds es : List ℤ) (hlen : ds.length=es.length)
              (hz : ∀ z ∈ ds.zip es,z.1+z.2=0) :
              ds.foldr (fun d x => d+2*x) 0+es.foldr (fun d x => d+2*x) 0=0 := by
            induction ds generalizing es with
            | nil => have he : es=[] := List.length_eq_zero_iff.mp (by simpa only [List.length_nil] using hlen.symm)
                     subst es;rfl
            | cons d ds ih =>
              cases es with
              | nil => simp at hlen
              | cons e es =>
                have hd:=hz (d,e) (by exact List.mem_cons_self)
                have ht : ∀ z ∈ ds.zip es,z.1+z.2=0 := fun z hm => hz z (by exact List.mem_cons_of_mem _ hm)
                have hv:=ih es (by simpa only [List.length_cons,Nat.succ.injEq] using hlen) ht
                simp only [List.foldr_cons]
                linarith
          have hflipDigits := ((unmarked_path_flip_semantics before hr0).mp hflip).2
          have hneg:=negvalue inlow outlow (ilen.trans olen.symm) hflipDigits
          rw [ilowvalue,outlowvalue] at hneg
          have hTj : Tj = -T := by clear * - hneg;omega
          have newMarked : markedPrefix j rcount (q+3) (-T) := by
            rw [← hTj]
            exact outConstruct.2 hremove
          have eni : (if 2*T-((n%2 : ℕ) : ℤ)<0 then (1:ℤ) else 0)=1 := ni.symm.trans hnphase
          have enj : (if 2*(-T)-((j%2 : ℕ) : ℤ)<0 then (1:ℤ) else 0)=0 := by
            rw [← hTj]
            exact nj.symm.trans hjphase
          have keep : z[4]?.getD 0=0 := by rw [hkeep,hremove];rfl
          rw [keep,show ((0:ℤ)!=0)=false by decide] at bound
          simp only [Bool.false_eq_true,ite_false] at bound
          refine ⟨?_,eni,enj,?_⟩
          · simpa only [Nat.add_sub_cancel] using newMarked
          · clear * - bound
            omega

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.marked_prefix_rigidity_and_charge
