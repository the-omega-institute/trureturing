/- GID: D5/S1/Words/Palindromes/PeriodDoubling/BaseQArithmetic
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/BaseQArithmetic
   mirror-E: none(waiver:literal-signed-charge-semantics)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.result; instance=D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseTable
   digest: Accepted q path weights and phase offsets equal the literal endpoint Q difference. -/

/-
proof_shape: content (base_path_Q_semantics)
escape_witness: Checked sign-memory transitions and arbitrary-length signed-expansion identification.
admission_basis: escape-witness
Direct frozen dependencies: none; the imported period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.BaseChargeArithmetic
import D5.S1.Words.Palindromes.PeriodDoubling.TripleBinaryDigits
import D5.S1.Words.Palindromes.PeriodDoubling.CanonicalSignedDigits
import Mathlib.Data.Nat.Log
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling

open BaseCertificates

def tripleSignedDigits (X h : ℕ) : List ℤ := List.ofFn (fun i : Fin h =>
  ((3*X/2^(i.val+1)%2 : ℕ) : ℤ) - ((X/2^(i.val+1)%2 : ℕ) : ℤ))
def signedDigitCharge (n : ℕ) : ℕ :=
  let X := (n+1)/2
  let h := Nat.log 2 (3*X)+1
  let nz := ((tripleSignedDigits X h).zipIdx).filter (fun z => z.1 != 0)
  (nz.map (fun z => 1+2*(z.2%2))).sum +
    ((nz.zip nz.tail).filter (fun z => z.1.1 != z.2.1)).length +
    (match nz.head? with
      | none => 0
      | some z => Bool.toNat ((n%2 == 1) != decide (z.1 < 0)))

def memoryRowCheck (i : ℕ) : Bool :=
  let S := (baseTable i).1
  (baseTable i).2.1.all fun e =>
    let T := (baseTable e.1).1
    decide (T[2]?.getD 0 = S[2]?.getD 0 ∧ T[3]?.getD 0 = S[3]?.getD 0 ∧
      T[14]?.getD 0 = (if S[14]?.getD 0 = 0 then T[10]?.getD 0 else S[14]?.getD 0) ∧
      T[15]?.getD 0 = (if S[15]?.getD 0 = 0 then T[12]?.getD 0 else S[15]?.getD 0))
private def memoryBlockCheck (start count : ℕ) : Bool :=
  (List.range count).all fun k => memoryRowCheck (start+k)


/-- The q edge sum with its final phase term is the literal Q difference. -/
theorem base_path_Q_semantics (n j : ℕ) {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (hs : s ∈ (baseAutomaton true).start) (ht : t ∈ (baseAutomaton true).accept)
    (p : (baseAutomaton true).Path s t xs)
    (hsn : (baseTable s.val).1[2]?.getD 0 = ((n%2 : ℕ) : ℤ))
    (hsj : (baseTable s.val).1[3]?.getD 0 = ((j%2 : ℕ) : ℤ))
    (hn : xs.foldr (fun a x => a.2.2.1+2*x) 0 = ((n/2 : ℕ) : ℤ))
    (hj : xs.foldr (fun a x => a.2.2.2+2*x) 0 = ((j/2 : ℕ) : ℤ)) :
    pathCharge (fun _ a _ => a.2.1) p + baseOffset (baseTable t.val).1 =
      (signedDigitCharge j : ℤ) - (signedDigitCharge n : ℤ) := by
  have charge_unique (ds es : List ℤ)
      (hd : ∀ z ∈ ds, z = -1 ∨ z = 0 ∨ z = 1)
      (he : ∀ z ∈ es, z = -1 ∨ z = 0 ∨ z = 1)
      (hnd : ds.IsChain (fun a b => a=0 ∨ b=0))
      (hne : es.IsChain (fun a b => a=0 ∨ b=0))
      (hvalue : ds.foldr (fun z x => z+2*x) 0 = es.foldr (fun z x => z+2*x) 0) :
      digitStreamCharge 0 0 ds = digitStreamCharge 0 0 es ∧
        ds.find? (fun z => z != 0) = es.find? (fun z => z != 0) := by
    have charge_zeros (k : ℕ) (par prev : ℤ) :
        digitStreamCharge par prev (List.replicate k 0) = 0 := by
      induction k generalizing par prev with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ,digitStreamCharge,ih]
    have charge_pad (xs : List ℤ) (k : ℕ) (par prev : ℤ) :
        digitStreamCharge par prev (xs ++ List.replicate k 0) =
          digitStreamCharge par prev xs := by
      induction xs generalizing par prev with
      | nil => simpa only [List.nil_append,digitStreamCharge] using charge_zeros k par prev
      | cons d ds ih => simp only [List.cons_append,digitStreamCharge,ih]
    have value_zeros (k : ℕ) :
        (List.replicate k (0:ℤ)).foldr (fun z x => z+2*x) 0 = 0 := by
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ,ih]
    have value_pad (xs : List ℤ) (k : ℕ) :
        (xs ++ List.replicate k 0).foldr (fun z x => z+2*x) 0 =
          xs.foldr (fun z x => z+2*x) 0 := by
      rw [List.foldr_append,value_zeros]
    have sparse_pad (xs : List ℤ) (k : ℕ)
        (hxs : xs.IsChain (fun a b => a=0 ∨ b=0)) :
        (xs ++ List.replicate k 0).IsChain (fun a b => a=0 ∨ b=0) := by
      refine hxs.append ?_ ?_
      · exact List.isChain_replicate_of_rel k (Or.inl rfl)
      · intro x hx y hy
        right
        have hm : y ∈ List.replicate k (0:ℤ) := List.mem_of_mem_head? hy
        exact (List.mem_replicate.mp hm).2
    have coeff_pad (xs : List ℤ) (k : ℕ)
        (hxs : ∀ z ∈ xs, z=-1 ∨ z=0 ∨ z=1) :
        ∀ z ∈ xs ++ List.replicate k 0, z=-1 ∨ z=0 ∨ z=1 := by
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hxs z hz
      · exact Or.inr (Or.inl (List.mem_replicate.mp hz).2)
    have eq := nonadjacent_digits_unique (ds ++ List.replicate es.length 0)
      (es ++ List.replicate ds.length 0) (coeff_pad ds es.length hd) (coeff_pad es ds.length he)
      (sparse_pad ds es.length hnd) (sparse_pad es ds.length hne)
      (by simp [Nat.add_comm]) (by simpa only [value_pad] using hvalue)
    constructor
    · have h := congrArg (digitStreamCharge 0 0) eq
      simpa only [charge_pad] using h
    · have h := congrArg (fun xs : List ℤ => xs.find? (fun z => z != 0)) eq
      simpa using h
  have metadata (charge : Bool) {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : (baseAutomaton charge).Path s t xs) :
      (baseTable t.val).1[2]?.getD 0 = (baseTable s.val).1[2]?.getD 0 ∧
      (baseTable t.val).1[3]?.getD 0 = (baseTable s.val).1[3]?.getD 0 ∧
      (baseTable t.val).1[14]?.getD 0 =
        (if (baseTable s.val).1[14]?.getD 0 = 0 then
          ((pathOutputs (fun _ _ q => (baseTable q.val).1[10]?.getD 0) p).find?
            (fun z => z != 0)).getD 0 else (baseTable s.val).1[14]?.getD 0) ∧
      (baseTable t.val).1[15]?.getD 0 =
        (if (baseTable s.val).1[15]?.getD 0 = 0 then
          ((pathOutputs (fun _ _ q => (baseTable q.val).1[12]?.getD 0) p).find?
            (fun z => z != 0)).getD 0 else (baseTable s.val).1[15]?.getD 0) := by
    have checked (i : ℕ) (hi : i<1492) : memoryRowCheck i = true := by
      have blocks : ∀ b : Fin 24,
          memoryBlockCheck (64*b.val) (min 64 (1492-64*b.val)) = true := by
        intro b
        fin_cases b <;> decide
      have hb := blocks ⟨i/64,by omega⟩
      dsimp [memoryBlockCheck] at hb
      have hm : i%64 ∈ List.range (min 64 (1492-64*(i/64))) := by
        simp only [List.mem_range];omega
      have hh := List.all_eq_true.mp hb (i%64) hm
      simpa only [show 64*(i/64)+i%64=i by omega] using hh
    induction p with
    | nil s => simp [pathOutputs]
    | cons q s t a xs hstep p ih =>
      have hm : (q.val,a) ∈ (baseTable s.val).2.1 := hstep
      have hh := List.all_eq_true.mp (checked s.val s.isLt) (q.val,a) hm
      dsimp only [memoryRowCheck] at hh
      obtain ⟨hn,hj,hfn,hfj⟩ := of_decide_eq_true hh
      refine ⟨ih.1.trans hn,ih.2.1.trans hj,?_,?_⟩
      · rw [ih.2.2.1,hfn]
        simp only [pathOutputs,List.find?_cons]
        by_cases hs : (baseTable s.val).1[14]?.getD 0=0
        · simp only [hs,if_true]
          by_cases hq : (baseTable q.val).1[10]?.getD 0=0
          · simp [hq]
          · simp only [show ((baseTable q.val).1[10]?.getD 0 != 0) = true by simp [hq],
              Option.getD_some,if_neg hq]
        · simp [hs]
      · rw [ih.2.2.2,hfj]
        simp only [pathOutputs,List.find?_cons]
        by_cases hs : (baseTable s.val).1[15]?.getD 0=0
        · simp only [hs,if_true]
          by_cases hq : (baseTable q.val).1[12]?.getD 0=0
          · simp [hq]
          · simp only [show ((baseTable q.val).1[12]?.getD 0 != 0) = true by simp [hq],
              Option.getD_some,if_neg hq]
        · simp [hs]
  have Q_expansion (n : ℕ) (ds : List ℤ)
      (hcoeff : ∀ z ∈ ds, z = -1 ∨ z = 0 ∨ z = 1)
      (hsparse : ds.IsChain (fun a b => a=0 ∨ b=0))
      (hvalue : ds.foldr (fun z x => z+2*x) 0 = (((n+1)/2 : ℕ) : ℤ)) :
      (signedDigitCharge n : ℤ) = digitStreamCharge 0 0 ds +
        (match ds.find? (fun z => z != 0) with
         | none => 0
         | some z => (Bool.toNat ((n%2 == 1) != decide (z < 0)) : ℤ)) := by
    let X := (n+1)/2
    let h := Nat.log 2 (3*X)+1
    let cs := tripleSignedDigits X h
    let nz := (cs.zipIdx).filter (fun z => z.1 != 0)
    let phase : Option ℤ → ℤ := fun o => match o with
      | none => 0
      | some z => (Bool.toNat ((n%2 == 1) != decide (z < 0)) : ℤ)
    have hb : 3*X < 2^(h+1) := Nat.lt_pow_of_log_lt (by decide) (by dsimp [h];omega)
    obtain ⟨hv,hs,hweight⟩ := triple_digits_value_and_minimality X h hb
    have hc : ∀ z ∈ cs, z=-1 ∨ z=0 ∨ z=1 := by
      intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      have ha := Nat.mod_lt (3*X/2^(i.val+1)) (by decide : 0<2)
      have hd := Nat.mod_lt (X/2^(i.val+1)) (by decide : 0<2)
      omega
    have hs' : cs.IsChain (fun a b => a=0 ∨ b=0) := hs
    have hv' : cs.foldr (fun z x => z+2*x) 0 = ds.foldr (fun z x => z+2*x) 0 :=
      hv.trans hvalue.symm
    obtain ⟨hcharge,hfind⟩ := charge_unique cs ds hc hcoeff hs' hsparse hv'
    have hf : nz.head?.map Prod.fst = cs.find? (fun z => z != 0) := by
      dsimp [nz]
      rw [List.head?_filter]
      have hh := List.find?_map (p := fun z : ℤ => z != 0) (f := Prod.fst) (l := cs.zipIdx)
      rw [List.zipIdx_map_fst] at hh
      exact hh.symm
    have hphase : (match nz.head? with
        | none => (0:ℤ)
        | some z => (Bool.toNat ((n%2 == 1) != decide (z.1 < 0)) : ℤ)) =
        phase (cs.find? (fun z => z != 0)) := by
      rw [← hf]
      cases nz.head? <;> rfl
    have hw := digit_stream_charge_formula cs 0 0
    change digitStreamCharge 0 0 cs =
      (((nz.map (fun z => (1+2*(z.2%2):ℕ))).sum : ℕ) : ℤ) +
        (((nz.zip nz.tail).filter (fun z => z.1.1 != z.2.1)).length : ℤ) +
        (match nz.head? with
         | none => 0
         | some z => (Bool.toNat ((0:ℤ) != 0 && 0 != z.1) : ℤ)) at hw
    have hinit : (match nz.head? with
        | none => (0:ℤ)
        | some z => (Bool.toNat ((0:ℤ) != 0 && 0 != z.1) : ℤ)) = 0 := by
      cases nz.head? <;> rfl
    rw [hinit,add_zero] at hw
    change (signedDigitCharge n : ℤ) = digitStreamCharge 0 0 ds + phase (ds.find? (fun z => z != 0))
    change (((nz.map (fun z => (1+2*(z.2%2) : ℕ))).sum +
      ((nz.zip nz.tail).filter (fun z => z.1.1 != z.2.1)).length +
      (match nz.head? with
        | none => 0
        | some z => Bool.toNat ((n%2 == 1) != decide (z.1 < 0))) : ℕ) : ℤ) = _
    rw [Nat.cast_add,Nat.cast_add]
    have hphase' : (((match nz.head? with
        | none => 0
        | some z => Bool.toNat ((n%2 == 1) != decide (z.1 < 0))) : ℕ) : ℤ) =
        (phase (cs.find? (fun z => z != 0)) : ℤ) := by
      cases hnz : nz.head? <;> simpa only [hnz,Nat.cast_zero] using hphase
    rw [hphase',← hw,hcharge,hfind]
  let dsN := pathOutputs (fun _ _ q => (baseTable q.val).1[10]?.getD 0) p
  let dsJ := pathOutputs (fun _ _ q => (baseTable q.val).1[12]?.getD 0) p
  have src : (baseTable s.val).1[1]?.getD 0=1 ∧
      (baseTable s.val).1[14]?.getD 0=0 ∧ (baseTable s.val).1[15]?.getD 0=0 ∧
      (baseTable s.val).1[16]?.getD 0=0 ∧ (baseTable s.val).1[17]?.getD 0=0 := by
    have hs' : s.val=0 ∨ s.val=1 ∨ s.val=2 ∨ s.val=3 ∨ s.val=4 ∨ s.val=5 ∨ s.val=6 := by
      change ([0,1,2,3,4,5,6] : List ℕ).contains s.val = true at hs
      simpa using hs
    rcases hs' with h | h | h | h | h | h | h <;> rw [h] <;> decide
  have dataN := base_path_sparse_signed_digits true false hs ht p
  have dataJ := base_path_sparse_signed_digits true true hs ht p
  simp only [Bool.false_eq_true,if_false] at dataN
  rw [hn,hsn] at dataN
  simp only [if_true] at dataJ
  rw [hj,hsj] at dataJ
  change (∀ z ∈ dsN, z=-1 ∨ z=0 ∨ z=1) ∧ dsN.IsChain (fun a b => a=0 ∨ b=0) ∧
    dsN.foldr (fun z x => z+2*x) 0 = 2*(((n/2 : ℕ) : ℤ) + ((n%2 : ℕ) : ℤ)) ∧
    dsN.head? = some 0 at dataN
  change (∀ z ∈ dsJ, z=-1 ∨ z=0 ∨ z=1) ∧ dsJ.IsChain (fun a b => a=0 ∨ b=0) ∧
    dsJ.foldr (fun z x => z+2*x) 0 = 2*(((j/2 : ℕ) : ℤ) + ((j%2 : ℕ) : ℤ)) ∧
    dsJ.head? = some 0 at dataJ
  obtain ⟨dns,hdns⟩ : ∃ dns : List ℤ, dsN=0::dns := by
    cases he : dsN with
    | nil => simp [he] at dataN
    | cons d dns =>
      have hd : d=0 := by simpa only [he,List.head?_cons,Option.some.injEq] using dataN.2.2.2
      exact ⟨dns,by simp only [hd]⟩
  obtain ⟨djs,hdjs⟩ : ∃ djs : List ℤ, dsJ=0::djs := by
    cases he : dsJ with
    | nil => simp [he] at dataJ
    | cons d djs =>
      have hd : d=0 := by simpa only [he,List.head?_cons,Option.some.injEq] using dataJ.2.2.2
      exact ⟨djs,by simp only [hd]⟩
  have hnval : dns.foldr (fun z x => z+2*x) 0 = (((n+1)/2 : ℕ) : ℤ) := by
    have hv := dataN.2.2.1
    rw [hdns] at hv
    simp only [List.foldr_cons,zero_add] at hv
    have he : (n+1)/2=n/2+n%2 := by omega
    rw [he,Nat.cast_add]
    omega
  have hjval : djs.foldr (fun z x => z+2*x) 0 = (((j+1)/2 : ℕ) : ℤ) := by
    have hv := dataJ.2.2.1
    rw [hdjs] at hv
    simp only [List.foldr_cons,zero_add] at hv
    have he : (j+1)/2=j/2+j%2 := by omega
    rw [he,Nat.cast_add]
    omega
  have qn := Q_expansion n dns (fun z hz => dataN.1 z (by simp [hdns,hz]))
    (by rw [hdns] at dataN;exact dataN.2.1.tail) hnval
  have qj := Q_expansion j djs (fun z hz => dataJ.1 z (by simp [hdjs,hz]))
    (by rw [hdjs] at dataJ;exact dataJ.2.1.tail) hjval
  have mem := metadata true p
  have htn : (baseTable t.val).1[2]?.getD 0=((n%2 : ℕ) : ℤ) := mem.1.trans hsn
  have htj : (baseTable t.val).1[3]?.getD 0=((j%2 : ℕ) : ℤ) := mem.2.1.trans hsj
  have hfn : (baseTable t.val).1[14]?.getD 0 = (dns.find? (fun z => z != 0)).getD 0 := by
    have h := mem.2.2.1
    change _ = (if (baseTable s.val).1[14]?.getD 0=0 then (dsN.find? (fun z => z != 0)).getD 0 else _) at h
    simpa [src.2.1,hdns] using h
  have hfj : (baseTable t.val).1[15]?.getD 0 = (djs.find? (fun z => z != 0)).getD 0 := by
    have h := mem.2.2.2
    change _ = (if (baseTable s.val).1[15]?.getD 0=0 then (dsJ.find? (fun z => z != 0)).getD 0 else _) at h
    simpa [src.2.2.1,hdjs] using h
  have correction (k : ℕ) (ds : List ℤ)
      (hv : ds.foldr (fun z x => z+2*x) 0 = (((k+1)/2 : ℕ) : ℤ)) :
      (if (ds.find? (fun z => z != 0)).getD 0 < 0 then 1-((k%2 : ℕ) : ℤ) else ((k%2 : ℕ) : ℤ)) =
      (match ds.find? (fun z => z != 0) with
       | none => 0
       | some z => (Bool.toNat ((k%2 == 1) != decide (z < 0)) : ℤ)) := by
    cases hf : ds.find? (fun z => z != 0) with
    | none =>
      have hall : ∀ z ∈ ds, z=0 := by
        have h := List.find?_eq_none.mp hf
        intro z hz
        have hn := h z hz
        simpa using hn
      have hzero : ds.foldr (fun z x => z+2*x) 0 = 0 := by
        clear hv hf
        induction ds with
        | nil => rfl
        | cons d ds ih =>
          have hd : d=0 := hall d (by simp)
          have ht : ∀ z ∈ ds, z=0 := fun z hz => hall z (by simp [hz])
          simp only [List.foldr_cons,hd,ih ht,zero_add,mul_zero]
      have hk : k=0 := by omega
      subst k
      simp
    | some d =>
      simp only [Option.getD_some]
      have hm : k%2=0 ∨ k%2=1 := by omega
      rcases hm with hm | hm <;> rw [hm] <;> by_cases hd : d<0 <;> simp [hd]
  have cn := correction n dns hnval
  have cj := correction j djs hjval
  have off : baseOffset (baseTable t.val).1 =
      (signedDigitCharge j : ℤ) - digitStreamCharge 0 0 djs -
        ((signedDigitCharge n : ℤ) - digitStreamCharge 0 0 dns) := by
    unfold baseOffset
    rw [htn,htj,hfn,hfj,cn,cj,qn,qj]
    ring
  have hp := base_path_charge_reconstruction true p
  change pathCharge (fun _ a _ => a.2.1) p =
    digitStreamCharge ((baseTable s.val).1[1]?.getD 0) ((baseTable s.val).1[17]?.getD 0) dsJ -
    digitStreamCharge ((baseTable s.val).1[1]?.getD 0) ((baseTable s.val).1[16]?.getD 0) dsN at hp
  rw [src.1,src.2.2.2.1,src.2.2.2.2,hdns,hdjs] at hp
  simp only [digitStreamCharge,sub_self,if_true,zero_add] at hp
  rw [hp,off]
  ring

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.base_path_Q_semantics
