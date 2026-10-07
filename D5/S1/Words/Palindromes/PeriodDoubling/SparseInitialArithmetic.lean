/- GID: D5/S1/Words/Palindromes/PeriodDoubling/SparseInitialArithmetic
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/SparseInitialArithmetic
   mirror-E: none(waiver:unbounded-sparse-family-digit-identification)
   anchors: []
   utility: none
   digest: Sparse digits determine weight, charge, class and the initial marker. -/

/-
proof_shape: content (sparse_initial_arithmetic)
escape_witness: Nonadjacent uniqueness identifies all canonical digits and their alternating charges.
admission_basis: escape-witness
Direct frozen dependencies: none; the period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.CutRepresentation
import D5.S1.Words.Palindromes.PeriodDoubling.MarkedPrefixArithmetic
namespace D5.S1.Words.Palindromes.PeriodDoubling
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0
theorem sparse_initial_arithmetic (a b : ℕ) :
    let N := (∑ i ∈ Finset.range a, 2^(2*b+2+3*i)) +
      (∑ j ∈ Finset.range b, 2^(2*j+1))
    N%2 = 0 ∧ signedWeight (((N+1)/2 : ℕ) : ℤ) = a+b ∧ classS N ∧
      signedDigitCharge N = 2*a+a%2+b ∧
      markedPrefix N a (2*b+1) ((∑ j ∈ Finset.range b,2^(2*j) : ℕ) : ℤ) := by
  dsimp only
  let L : ℕ → List ℤ := fun b => (List.replicate b [1,0]).flatten
  let M : ℕ → List ℤ := fun a => (List.replicate a [1,0,0]).flatten
  let ds:=L b++[0]++M a
  let N := (∑ i ∈ Finset.range a,2^(2*b+2+3*i)) + (∑ j ∈ Finset.range b,2^(2*j+1))
  let half := (∑ i ∈ Finset.range a,2^(2*b+1+3*i)) + (∑ j ∈ Finset.range b,2^(2*j))
  have hN : N = 2*half := by
    dsimp [N,half]
    rw [mul_add,Finset.mul_sum,Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [show 2*b+2+3*i = (2*b+1+3*i)+1 by omega,pow_succ]
      ring
    · apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ]
      ring
  have hhalf : (N+1)/2 = half := by omega
  have Lstep (b : ℕ) : L (b+1) = 1::0::L b := by simp [L,List.replicate_succ]
  have Mstep (a : ℕ) : M (a+1) = 1::0::0::M a := by simp [M,List.replicate_succ]
  have affine (xs : List ℤ) (v : ℤ) : xs.foldr (fun z x=>z+2*x) v =
      xs.foldr (fun z x=>z+2*x) 0+2^xs.length*v := by
    induction xs with
    | nil => simp
    | cons z xs ih => simp only [List.foldr_cons,List.length_cons,ih,pow_succ];ring
  have Llen (b : ℕ) : (L b).length = 2*b := by
    induction b with
    | zero => rfl
    | succ b ih => rw [Lstep];simp only [List.length_cons,ih];omega
  have Lvalue (b : ℕ) : (L b).foldr (fun z x=>z+2*x) 0=
      ((∑ j ∈ Finset.range b,2^(2*j) : ℕ) : ℤ) := by
    induction b with
    | zero => simp [L]
    | succ b ih =>
      rw [Lstep]
      simp only [List.foldr_cons,ih,Nat.cast_sum]
      rw [Finset.sum_range_succ']
      simp only [Nat.mul_zero,pow_zero,Nat.cast_add,Nat.cast_sum,Nat.cast_one]
      have hh : (∑ j ∈ Finset.range b,((2^(2*(j+1)) : ℕ) : ℤ))=
          4*∑ j ∈ Finset.range b,((2^(2*j) : ℕ) : ℤ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [show 2*(j+1) = 2*j+2 by omega,pow_add]
        push_cast
        norm_num
        ring
      rw [hh]
      ring
  have Mvalue (a : ℕ) : (M a).foldr (fun z x=>z+2*x) 0=
      ((∑ j ∈ Finset.range a,2^(3*j) : ℕ) : ℤ) := by
    induction a with
    | zero => simp [M]
    | succ a ih =>
      rw [Mstep]
      simp only [List.foldr_cons,ih,Nat.cast_sum]
      rw [Finset.sum_range_succ']
      simp only [Nat.mul_zero,pow_zero,Nat.cast_add,Nat.cast_sum,Nat.cast_one]
      have hh : (∑ j ∈ Finset.range a,((2^(3*(j+1)) : ℕ) : ℤ))=
          8*∑ j ∈ Finset.range a,((2^(3*j) : ℕ) : ℤ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [show 3*(j+1) = 3*j+3 by omega,pow_add]
        push_cast
        norm_num
        ring
      rw [hh]
      ring
  have hvalue : ds.foldr (fun z x=>z+2*x) 0 = (half : ℤ) := by
    dsimp [ds]
    rw [List.append_assoc,List.foldr_append,affine,Lvalue,Llen]
    simp only [List.singleton_append,List.foldr_cons,zero_add,Mvalue]
    dsimp [half]
    push_cast
    have hh : (∑ i ∈ Finset.range a,(2:ℤ)^(2*b+1+3*i))=
        (2:ℤ)^(2*b+1)*∑ i ∈ Finset.range a,(2:ℤ)^(3*i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_add]
    rw [hh,pow_add]
    norm_num
    ring
  have gapL (b : ℕ) : (L b).IsChain (fun x y=>x = 0 ∨ y = 0) := by
    induction b with
    | zero => exact List.IsChain.nil
    | succ b ih =>
      rw [Lstep]
      apply List.isChain_cons_cons.mpr
      refine ⟨Or.inr rfl,List.isChain_cons.mpr ⟨?_,ih⟩⟩
      intro y hy
      exact Or.inl rfl
  have gapM (a : ℕ) : (M a).IsChain (fun x y=>x = 0 ∨ y = 0) := by
    induction a with
    | zero => exact List.IsChain.nil
    | succ a ih =>
      rw [Mstep]
      apply List.isChain_cons_cons.mpr
      refine ⟨Or.inr rfl,List.isChain_cons_cons.mpr ⟨Or.inl rfl,List.isChain_cons.mpr ⟨?_,ih⟩⟩⟩
      intro y hy
      exact Or.inl rfl
  have hgap : ds.IsChain (fun x y=>x = 0 ∨ y = 0) := by
    dsimp only [ds]
    rw [List.append_assoc]
    change (L b++0::M a).IsChain (fun x y=>x = 0 ∨ y = 0)
    refine (gapL b).append (List.isChain_cons.mpr ⟨?_,gapM a⟩) ?_
    · intro y hy
      exact Or.inl rfl
    · intro x hx y hy
      have he : y = 0 := by simpa using hy.symm
      exact Or.inr he
  have hcoeff : ∀ z ∈ ds,z = 0 ∨ z = 1 := by
    intro z hz
    dsimp [ds,L,M] at hz
    simp only [List.mem_append,List.mem_singleton,List.mem_flatten,List.mem_replicate] at hz
    rcases hz with (⟨xs,⟨_,rfl⟩,hz⟩|hz)|⟨xs,⟨_,rfl⟩,hz⟩
    · simp only [List.mem_cons,List.mem_singleton] at hz
      tauto
    · exact Or.inl hz
    · simp only [List.mem_cons,List.mem_singleton] at hz
      tauto
  have Lcount (b : ℕ) : ((L b).filter (fun z=>z != 0)).length = b := by
    induction b with
    | zero => rfl
    | succ b ih => rw [Lstep];simp [ih]
  have Mcount (a : ℕ) : ((M a).filter (fun z=>z != 0)).length = a := by
    induction a with
    | zero => rfl
    | succ a ih => rw [Mstep];simp [ih]
  have hcount : (ds.filter (fun z=>z != 0)).length = a+b := by
    dsimp [ds]
    simp [List.filter_append,Lcount,Mcount]
    omega
  have Mcharge (a : ℕ) (prev : ℤ) (hp : prev = 0 ∨ prev = 1) :
      digitStreamCharge 0 prev (M a) = 2*(a : ℤ)-((a%2 : ℕ) : ℤ) ∧
      digitStreamCharge 1 prev (M a) = 2*(a : ℤ)+((a%2 : ℕ) : ℤ) := by
    induction a generalizing prev with
    | zero => simp [M,digitStreamCharge]
    | succ a ih =>
      have ht:=ih 1 (Or.inr rfl)
      have hm : (((a+1)%2 : ℕ) : ℤ) = 1-((a%2 : ℕ) : ℤ) := by omega
      rw [Mstep]
      rcases hp with rfl|rfl <;> simp [digitStreamCharge,ht.1,ht.2,hm] <;> omega
  have Lcharge (b : ℕ) (prev : ℤ) (hp : prev = 0 ∨ prev = 1) :
      digitStreamCharge 0 prev (L b++0::M a) = ((b : ℕ) : ℤ)+2*(a : ℤ)+((a%2 : ℕ) : ℤ) := by
    induction b generalizing prev with
    | zero =>
      have h:= (Mcharge a prev hp).2
      simpa [L,digitStreamCharge] using h
    | succ b ih =>
      have h:=ih 1 (Or.inr rfl)
      rw [Lstep]
      rcases hp with rfl|rfl <;> simp [digitStreamCharge,h] <;> omega
  have hv : ds.foldr (fun z x=>z+2*x) 0 = (((N+1)/2 : ℕ) : ℤ) := by rw [hhalf];exact hvalue
  have hcharge : digitStreamCharge 0 0 ds = ((2*a+a%2+b : ℕ) : ℤ) := by
    have h:=Lcharge b 0 (Or.inl rfl)
    dsimp only [ds]
    rw [List.append_assoc]
    change digitStreamCharge 0 0 (L b++0::M a) = _
    push_cast
    omega
  have hcoeff3 : ∀ z ∈ ds,z = -1 ∨ z = 0 ∨ z = 1 := by
    intro z hz
    exact Or.inr (hcoeff z hz)
  have hw := signed_weight_nonadjacent ds hcoeff3 hgap
  rw [hv,hcount] at hw
  have heven : N%2 = 0 := by omega
  let X:=(N+1)/2
  let h:=Nat.log 2 (3*X)+1
  let cs:=tripleSignedDigits X h
  have hb : 3*X < 2^(h+1) := Nat.lt_pow_of_log_lt (by decide) (by dsimp [h];omega)
  obtain ⟨hcv,hcs,_⟩:=triple_digits_value_and_minimality X h hb
  have hc : ∀ z ∈ cs,z = -1 ∨ z = 0 ∨ z = 1 := by
    intro z hz
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hz
    have h0:=Nat.mod_lt (3*X/2^(i.val+1)) (by decide : 0 < 2)
    have h1:=Nat.mod_lt (X/2^(i.val+1)) (by decide : 0 < 2)
    omega
  have padcoeff (xs : List ℤ) (k : ℕ) (hc : ∀ z ∈ xs,z = -1 ∨ z = 0 ∨ z = 1) :
      ∀ z ∈ xs++List.replicate k 0,z = -1 ∨ z = 0 ∨ z = 1 := by
    intro z hz
    rcases List.mem_append.mp hz with hz|hz
    · exact hc z hz
    · exact Or.inr (Or.inl (List.mem_replicate.mp hz).2)
  have padsparse (xs : List ℤ) (k : ℕ) (hs : xs.IsChain (fun x y=>x = 0 ∨ y = 0)) :
      (xs++List.replicate k 0).IsChain (fun x y=>x = 0 ∨ y = 0) := by
    refine hs.append (List.isChain_replicate_of_rel k (Or.inl rfl)) ?_
    intro x hx y hy
    exact Or.inr (List.mem_replicate.mp (List.mem_of_mem_head? hy)).2
  have zeros (k : ℕ) : (List.replicate k (0:ℤ)).foldr (fun z x=>z+2*x) 0 = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ,ih]
  have eq:=nonadjacent_digits_unique (cs++List.replicate ds.length 0)
    (ds++List.replicate cs.length 0) (padcoeff cs ds.length hc) (padcoeff ds cs.length hcoeff3)
    (padsparse cs ds.length hcs) (padsparse ds cs.length hgap)
    (by simp [Nat.add_comm]) (by simpa only [cs,tripleSignedDigits,List.foldr_append,zeros] using hcv.trans hv.symm)
  have entrypad (xs : List ℤ) (k i : ℕ) :
      (xs++List.replicate k 0)[i]?.getD 0 = xs[i]?.getD 0 := by
    by_cases hi : i < xs.length
    · simp [List.getElem?_append,hi]
    · rw [List.getElem?_eq_none (by omega : xs.length ≤ i)]
      simp only [List.getElem?_append,if_neg hi,List.getElem?_replicate]
      split <;> rfl
  have entries (i : ℕ) : cs[i]?.getD 0 = ds[i]?.getD 0 := by
    have hh:=congrArg (fun xs : List ℤ=>xs[i]?.getD 0) eq
    simpa only [entrypad] using hh
  have positiveGet (i : ℕ) : cs[i]?.getD 0 = 0 ∨ cs[i]?.getD 0 = 1 := by
    rw [entries]
    by_cases hi : i < ds.length
    · simp only [List.getElem?_eq_getElem hi,Option.getD_some]
      exact hcoeff ds[i] (List.getElem_mem hi)
    · simp only [List.getElem?_eq_none (by omega : ds.length ≤ i),Option.getD_none]
      exact Or.inl True.intro
  have cspositive : ∀ z ∈ cs,z = 0 ∨ z = 1 := by
    intro z hz
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hz
    have hh:=positiveGet i.val
    simpa only [cs,tripleSignedDigits,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some] using hh
  have hclass : classS N := by
    refine ⟨h,hb,?_⟩
    dsimp only
    intro i j hij hi hj hbetween hdifferent
    change cs[i.val]?.getD 0 ≠ 0 at hi
    change cs[j.val]?.getD 0 ≠ 0 at hj
    change cs[i.val]?.getD 0 ≠ cs[j.val]?.getD 0 at hdifferent
    have h0:=positiveGet i.val
    have h1:=positiveGet j.val
    omega
  have chargezeros (k : ℕ) (par prev : ℤ) : digitStreamCharge par prev (List.replicate k 0) = 0 := by
    induction k generalizing par prev with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ,digitStreamCharge,ih]
  have chargepad (xs : List ℤ) (k : ℕ) (par prev : ℤ) :
      digitStreamCharge par prev (xs++List.replicate k 0) = digitStreamCharge par prev xs := by
    induction xs generalizing par prev with
    | nil => simpa only [List.nil_append,digitStreamCharge] using chargezeros k par prev
    | cons z xs ih => simp only [List.cons_append,digitStreamCharge,ih]
  have hcanonical : digitStreamCharge 0 0 cs = digitStreamCharge 0 0 ds := by
    have hh:=congrArg (digitStreamCharge 0 0) eq
    simpa only [chargepad] using hh
  let nz:=(cs.zipIdx).filter (fun z=>z.1 != 0)
  have hphase : (match nz.head? with
      | none => 0
      | some z => Bool.toNat ((N%2 == 1) != decide (z.1 < 0))) = 0 := by
    cases hh : nz.head? with
    | none => rfl
    | some z =>
      have hm : z ∈ nz := List.mem_of_mem_head? (by simp [hh])
      have hz : z.1 ∈ cs := by
        have h1:=List.mem_map_of_mem (f := Prod.fst) (List.mem_filter.mp hm).1
        simpa only [List.zipIdx_map_fst] using h1
      rcases cspositive z.1 hz with he|he <;> simp [he,heven]
  have hQ : (signedDigitCharge N : ℤ) = digitStreamCharge 0 0 cs := by
    have hh:=digit_stream_charge_formula cs 0 0
    change digitStreamCharge 0 0 cs =
      (((nz.map (fun z=>(1+2*(z.2%2) : ℕ))).sum : ℕ) : ℤ)+
      (((nz.zip nz.tail).filter (fun z=>z.1.1 != z.2.1)).length : ℤ)+
      (match nz.head? with
       | none => 0
       | some z => (Bool.toNat ((0:ℤ) != 0 && 0 != z.1) : ℤ)) at hh
    have hinit : (match nz.head? with
       | none => (0:ℤ)
       | some z => (Bool.toNat ((0:ℤ) != 0 && 0 != z.1) : ℤ)) = 0 := by
      cases nz.head? <;> rfl
    rw [hinit,add_zero] at hh
    change (((nz.map (fun z=>1+2*(z.2%2))).sum+
      ((nz.zip nz.tail).filter (fun z=>z.1.1 != z.2.1)).length+
      (match nz.head? with
       | none => 0
       | some z => Bool.toNat ((N%2 == 1) != decide (z.1 < 0))) : ℕ) : ℤ) = _
    rw [hphase,Nat.add_zero,Nat.cast_add]
    exact hh.symm
  have Lsupport (b k : ℕ) (hk : (L b)[k]?.getD 0≠0) : k+3 ≤ 2*b+1 := by
    induction b generalizing k with
    | zero => simp [L] at hk
    | succ b ih =>
      rw [Lstep] at hk
      cases k with
      | zero => omega
      | succ k =>
        cases k with
        | zero => simp at hk
        | succ k =>
          have ht : (L b)[k]?.getD 0≠0 := by simpa using hk
          have hh:=ih k ht
          omega
  have hmark : markedPrefix N a (2*b+1) ((∑ j ∈ Finset.range b,2^(2*j) : ℕ) : ℤ) := by
    refine ⟨?_,L b,Lvalue b,?_,gapL b,Lsupport b⟩
    · rw [hhalf]
      dsimp [half,markedPowers]
    · intro z hz
      exact Or.inr (hcoeff z (by simp [ds,hz]))
  change N%2 = 0 ∧ signedWeight (((N+1)/2 : ℕ) : ℤ) = a+b ∧ classS N ∧
    signedDigitCharge N = 2*a+a%2+b ∧
    markedPrefix N a (2*b+1) ((∑ j ∈ Finset.range b,2^(2*j) : ℕ) : ℤ)
  refine ⟨heven,hw,hclass,?_,hmark⟩
  rw [hcanonical,hcharge] at hQ
  exact_mod_cast hQ

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.sparse_initial_arithmetic
