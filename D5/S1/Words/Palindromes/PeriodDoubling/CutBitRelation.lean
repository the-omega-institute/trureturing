/- GID: D5/S1/Words/Palindromes/PeriodDoubling/CutBitRelation
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/CutBitRelation
   mirror-E: none(waiver:unbounded-palindrome-bit-realization)
   anchors: []
   utility: none
   digest: Every literal palindrome cut has an accepting nine-state bit-relation path. -/

/-
proof_shape: content (cut_bit_relation_completeness)
escape_witness: Unbounded bit-run construction with the exact dyadic radius and even-cut parity.
admission_basis: escape-witness
Direct frozen dependencies: none; imported period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.BaseCertificates
import D5.S1.Words.Palindromes.PeriodDoubling.OddPalindromeRadius
import D5.S1.Words.Palindromes.PeriodDoubling.EvenPalindrome

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace D5.S1.Words.Palindromes.PeriodDoubling

open BaseCertificates

/-- The literal nine-state relation, before adjoining signed-digit arithmetic. -/
def cutBitAutomaton : NFA (ℕ × ℕ) ℤ where
  start := Set.univ
  step s a := {t | t ∈ relNext s a.1 a.2}
  accept := {0}

/-- Every nonempty palindromic suffix determines a flushed bit-relation path. -/
theorem cut_bit_relation_completeness (n j : ℕ) (hj : j<n)
    (hpal : List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i)))) :
    ∃ (r : ℤ) (xs : List (ℕ × ℕ)),
      r ∈ (if n%2=j%2 then [6] else if n%2>j%2 then [1,2,0] else [1,2] : List ℤ) ∧
      Nonempty (cutBitAutomaton.Path r 0 xs) ∧
      xs.foldr (fun a x => a.1+2*x) 0=n/2 ∧
      xs.foldr (fun a x => a.2+2*x) 0=j/2 ∧
      ∀ a ∈ xs, a.1≤1 ∧ a.2≤1 := by
  have relation_constructors :
      (∀ n : ℕ, ∃ xs : List (ℕ × ℕ),
        Nonempty (cutBitAutomaton.Path 0 0 xs) ∧
        xs.foldr (fun a x => a.1+2*x) 0 = n ∧
        xs.foldr (fun a x => a.2+2*x) 0 = n ∧
        ∀ a ∈ xs, a.1 ≤ 1 ∧ a.2 ≤ 1) ∧
      (∀ k t : ℕ, t < 2^k → ∀ r : ℤ, r=1 ∨ r=2 →
        ∃ xs : List (ℕ × ℕ), Nonempty (cutBitAutomaton.Path r r xs) ∧
        xs.length=k ∧ xs.foldr (fun a x => a.1+2*x) 0 = t ∧
        xs.foldr (fun a x => a.2+2*x) 0 = 2^k-1-t ∧
        ∀ a ∈ xs, a.1 ≤ 1 ∧ a.2 ≤ 1) := by
    constructor
    · intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        by_cases hn : n=0
        · subst n
          exact ⟨[],⟨.nil 0⟩,rfl,rfl,by simp⟩
        · obtain ⟨xs,⟨p⟩,hN,hJ,hbits⟩ := ih (n/2) (by omega)
          refine ⟨(n%2,n%2)::xs,⟨.cons 0 0 0 _ xs ?_ p⟩,?_,?_,?_⟩
          · simp [cutBitAutomaton,relNext]
          · simp only [List.foldr_cons,hN];omega
          · simp only [List.foldr_cons,hJ];omega
          · intro a ha
            rcases List.mem_cons.mp ha with ha | ha
            · subst a;dsimp;omega
            · exact hbits a ha
    · intro k
      induction k with
      | zero =>
        intro t ht r hr
        have ht0 : t=0 := by norm_num at ht;omega
        subst t
        exact ⟨[],⟨.nil r⟩,rfl,rfl,rfl,by simp⟩
      | succ k ih =>
        intro t ht r hr
        have ht' : t/2 < 2^k := by rw [pow_succ] at ht;omega
        obtain ⟨xs,⟨p⟩,hlen,hN,hJ,hbits⟩ := ih (t/2) ht' r hr
        refine ⟨(t%2,1-t%2)::xs,⟨.cons r r r _ xs ?_ p⟩,?_,?_,?_,?_⟩
        · have hb : t%2=0 ∨ t%2=1 := by omega
          rcases hr with rfl | rfl <;> rcases hb with hb | hb <;>
            simp [cutBitAutomaton,relNext,hb]
        · simpa [hlen]
        · simp only [List.foldr_cons,hN];omega
        · simp only [List.foldr_cons,hJ]
          rw [pow_succ]
          omega
        · intro a ha
          rcases List.mem_cons.mp ha with ha | ha
          · subst a;dsimp;omega
          · exact hbits a ha
  have relation_high (H : ℕ) :
      ∀ k : ℕ, ∀ r : ℤ, r=4 ∨ r=7 →
        ∃ xs : List (ℕ × ℕ), Nonempty (cutBitAutomaton.Path r 0 xs) ∧
        xs.foldr (fun a x => a.1+2*x) 0 = (2*H+1)*2^(2*k) ∧
        xs.foldr (fun a x => a.2+2*x) 0 = (2*H+1)*2^(2*k)-1 ∧
        ∀ a ∈ xs, a.1 ≤ 1 ∧ a.2 ≤ 1 := by
    intro k
    induction k with
    | zero =>
      intro r hr
      obtain ⟨xs,⟨p⟩,hN,hJ,hbits⟩ := relation_constructors.1 H
      refine ⟨(1,0)::xs,⟨.cons 0 r 0 _ xs ?_ p⟩,?_,?_,?_⟩
      · rcases hr with rfl | rfl <;> simp [cutBitAutomaton,relNext]
      · simp only [List.foldr_cons,hN,mul_zero,pow_zero,mul_one];omega
      · simp only [List.foldr_cons,hJ,mul_zero,pow_zero,mul_one,zero_add];omega
      · intro a ha
        rcases List.mem_cons.mp ha with ha | ha
        · subst a;decide
        · exact hbits a ha
    | succ k ih =>
      intro r hr
      obtain ⟨xs,⟨p⟩,hN,hJ,hbits⟩ := ih r hr
      let mid : ℤ := if r=4 then 5 else 8
      refine ⟨(0,1)::(0,1)::xs,⟨.cons mid r 0 _ _ ?_ (.cons r mid 0 _ _ ?_ p)⟩,?_,?_,?_⟩
      · rcases hr with rfl | rfl <;> simp [cutBitAutomaton,relNext,mid]
      · rcases hr with rfl | rfl <;> simp [cutBitAutomaton,relNext,mid]
      · simp only [List.foldr_cons,hN]
        rw [show 2*(k+1)=2*k+2 by omega,pow_add]
        ring
      · simp only [List.foldr_cons,hJ]
        rw [show 2*(k+1)=2*k+2 by omega,pow_add]
        norm_num only [Nat.reducePow]
        rw [show (2*H+1)*(2^(2*k)*4)=4*((2*H+1)*2^(2*k)) by ring]
        have hh : 0 < (2*H+1)*2^(2*k) := by positivity
        omega
      · intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with rfl | rfl | ha
        · decide
        · decide
        · exact hbits a ha
  have relation_shapes :
      (∀ k H t : ℕ, t < 2^k →
        ∃ xs : List (ℕ × ℕ), Nonempty (cutBitAutomaton.Path 1 0 xs) ∧
        xs.foldr (fun a x => a.1+2*x) 0 = H*2^(k+1)+2^k+t ∧
        xs.foldr (fun a x => a.2+2*x) 0 = H*2^(k+1)+(2^k-1-t) ∧
        ∀ a ∈ xs, a.1 ≤ 1 ∧ a.2 ≤ 1) ∧
      (∀ b k H c t : ℕ, c ≤ 1 → t < 2^b →
        ∃ xs : List (ℕ × ℕ), Nonempty (cutBitAutomaton.Path 2 0 xs) ∧
        xs.foldr (fun a x => a.1+2*x) 0 = (2*H+1)*2^(b+2*k+2)+c*2^b+t ∧
        xs.foldr (fun a x => a.2+2*x) 0 = (2*H+1)*2^(b+2*k+2)-(1-c)*2^b-1-t ∧
        ∀ a ∈ xs, a.1 ≤ 1 ∧ a.2 ≤ 1) := by
    have app {s t u : ℤ} {xs ys : List (ℕ × ℕ)}
        (p : cutBitAutomaton.Path s t xs) (q : cutBitAutomaton.Path t u ys) :
        Nonempty (cutBitAutomaton.Path s u (xs++ys)) := by
      induction p with
      | nil s => exact ⟨q⟩
      | cons t s v a xs he p ih =>
        obtain ⟨z⟩ := ih q
        exact ⟨.cons t s u a (xs++ys) he z⟩
    have folds (f : ℕ × ℕ → ℕ) (xs ys : List (ℕ × ℕ)) :
        (xs++ys).foldr (fun a x => f a+2*x) 0 =
          xs.foldr (fun a x => f a+2*x) 0 +
            2^xs.length*ys.foldr (fun a x => f a+2*x) 0 := by
      induction xs with
      | nil => simp
      | cons a xs ih =>
        simp only [List.cons_append,List.foldr_cons,List.length_cons,ih,pow_succ]
        ring
    constructor
    · intro k H t ht
      obtain ⟨lo,⟨pl⟩,hlen,hN,hJ,hbits⟩ := relation_constructors.2 k t ht 1 (Or.inl rfl)
      obtain ⟨hi,⟨ph⟩,hhN,hhJ,hhbits⟩ := relation_constructors.1 H
      have ptop : cutBitAutomaton.Path 1 0 ((1,0)::hi) :=
        .cons 0 1 0 (1,0) hi (by simp [cutBitAutomaton,relNext]) ph
      refine ⟨lo++(1,0)::hi,app pl ptop,?_,?_,?_⟩
      · rw [folds,hN,hlen]
        simp only [List.foldr_cons,hhN]
        rw [pow_succ]
        ring
      · rw [folds,hJ,hlen]
        simp only [List.foldr_cons,hhJ,zero_add]
        rw [pow_succ]
        ring
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hbits a ha
        · rcases List.mem_cons.mp ha with rfl | ha
          · decide
          · exact hhbits a ha
    · intro b k H c t hc ht
      obtain ⟨lo,⟨pl⟩,hlen,hN,hJ,hbits⟩ := relation_constructors.2 b t ht 2 (Or.inr rfl)
      obtain ⟨hi,⟨ph⟩,hhN,hhJ,hhbits⟩ := relation_high H k 4 (Or.inl rfl)
      have pgap : cutBitAutomaton.Path 3 0 ((0,1)::hi) :=
        .cons 4 3 0 (0,1) hi (by simp [cutBitAutomaton,relNext]) ph
      have pmid : cutBitAutomaton.Path 2 0 ((c,c)::(0,1)::hi) :=
        .cons 3 2 0 (c,c) _ (by simp [cutBitAutomaton,relNext]) pgap
      refine ⟨lo++(c,c)::(0,1)::hi,app pl pmid,?_,?_,?_⟩
      · rw [folds,hN,hlen]
        simp only [List.foldr_cons,hhN,zero_add]
        rw [show b+2*k+2=b+(2*k)+2 by omega,pow_add,pow_add]
        ring
      · rw [folds,hJ,hlen]
        simp only [List.foldr_cons,hhJ]
        have hpos : 0 < (2*H+1)*2^(2*k) := by positivity
        have ht0 : 0 < 2^b := by positivity
        have hn : (2*H+1)*2^(b+2*k+2) =
            4*2^b*((2*H+1)*2^(2*k)) := by
          rw [show b+2*k+2=b+(2*k)+2 by omega,pow_add,pow_add]
          ring
        rw [hn]
        have hA : (2*H+1)*2^(2*k)-1+1 = (2*H+1)*2^(2*k) := by omega
        have hAm := congrArg (fun z : ℕ => 2^b*z) hA
        have hT : 2^b-1-t+1+t=2^b := by omega
        have he : (2^b-1-t+2^b*(c+2*(1+2*((2*H+1)*2^(2*k)-1)))) +
            (1-c)*2^b+1+t=4*2^b*((2*H+1)*2^(2*k)) := by
          rcases (by omega : c=0 ∨ c=1) with rfl | rfl <;>
            simp only [Nat.sub_self,Nat.sub_zero,zero_add,one_mul,zero_mul] <;>
            nlinarith [hAm,hT]
        omega
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hbits a ha
        · simp only [List.mem_cons] at ha
          rcases ha with rfl | rfl | ha
          · exact ⟨hc,hc⟩
          · decide
          · exact hhbits a ha
  have relation_drop (n j : ℕ) (hpar : n%2≠j%2) (r : ℤ) (hr : r=1 ∨ r=2)
      (xs : List (ℕ × ℕ)) (p : cutBitAutomaton.Path r 0 xs)
      (hn : xs.foldr (fun a x => a.1+2*x) 0=n)
      (hj : xs.foldr (fun a x => a.2+2*x) 0=j)
      (hbits : ∀ a ∈ xs, a.1≤1 ∧ a.2≤1) :
      ∃ (q : ℤ) (ys : List (ℕ × ℕ)),
        q ∈ (if n%2>j%2 then [1,2,0] else [1,2] : List ℤ) ∧
        Nonempty (cutBitAutomaton.Path q 0 ys) ∧
        ys.foldr (fun a x => a.1+2*x) 0=n/2 ∧
        ys.foldr (fun a x => a.2+2*x) 0=j/2 ∧
        ∀ a ∈ ys, a.1≤1 ∧ a.2≤1 := by
    cases p with
    | nil s => simp only [List.foldr_nil] at hn hj;omega
    | cons q s u a ys hs p =>
      have ha:=hbits a (by simp)
      simp only [List.foldr_cons] at hn hj
      have hna : n%2=a.1 := by omega
      have hja : j%2=a.2 := by omega
      refine ⟨q,ys,?_,⟨p⟩,by omega,by omega,?_⟩
      · change q ∈ relNext r a.1 a.2 at hs
        rw [hna,hja] at hpar ⊢
        have hA : a.1=0 ∨ a.1=1 := by omega
        have hB : a.2=0 ∨ a.2=1 := by omega
        rcases hr with rfl | rfl <;> rcases hA with hA | hA <;>
          rcases hB with hB | hB <;> simp [hA,hB] at hpar <;>
          simp [relNext,hA,hB] at hs ⊢ <;> tauto
      · intro b hb
        exact hbits b (by simp [hb])
  have odd_geometry (n j : ℕ) (hj : j<n)
      (hodd : (n-j)%2=1)
      (hpal : List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i)))) :
      (∃ k H t : ℕ, t<2^k ∧ n=H*2^(k+1)+2^k+t ∧ j=H*2^(k+1)+(2^k-1-t)) ∨
      (∃ b k H c t : ℕ, 0<b ∧ c≤1 ∧ t<2^b ∧
        n=(2*H+1)*2^(b+2*k+2)+c*2^b+t ∧
        j=(2*H+1)*2^(b+2*k+2)-(1-c)*2^b-1-t) := by
    let R := (n-j)/2
    let m := j+R+1
    have hL : 2*R+1=n-j := by dsimp [R];omega
    have hm0 : m≠0 := by dsimp [m];omega
    obtain ⟨r,U,hU,hdecomp⟩ := Nat.exists_eq_two_pow_mul_odd hm0
    have ho : U%2=1 := by obtain ⟨k,hk⟩ := hU;omega
    have hU0 : 0<U := by omega
    have hR : R<2^r*U := by rw [← hdecomp];dsimp [m];omega
    have hstart : 2^r*U-R-1=j := by rw [← hdecomp];dsimp [m];omega
    have hn : 2^r*U+R=n := by rw [← hdecomp];dsimp [m];omega
    rw [← hL] at hpal
    have hp : List.Palindrome (List.ofFn (fun i : Fin (2*R+1) => u_pd (2^r*U-R-1+i))) :=
      by simpa [hstart] using hpal
    have hb := (odd_palindrome_radius r U R ho hR).mp hp
    by_cases hshort : R<2^r
    · left
      have hUeq : U=2*(U/2)+1 := by omega
      have he : 2^r*U=(U/2)*2^(r+1)+2^r := by
        calc
          2^r*U=2^r*(2*(U/2)+1) := congrArg (fun x : ℕ => 2^r*x) hUeq
          _=(U/2)*2^(r+1)+2^r := by rw [pow_succ];ring
      refine ⟨r,U/2,R,hshort,?_,?_⟩
      · rw [← hn,he]
      · rw [← hstart,he]
        omega
    · right
      have hu1 : U≠1 := by intro he;simp [he] at hb;omega
      let s := max (padicValNat 2 (U-1)) (padicValNat 2 (U+1))
      have hsodd : s%2=1 := by
        change R < if U=1 then 2^r else if s%2=0 then 2^r else 3*2^r at hb
        by_cases hs : s%2=0
        · simp [hu1,hs] at hb;omega
        · omega
      have hs2 : 2 ≤ s := by
        by_cases he : U%4=1
        · have hd : 2^2 ∣ U-1 := by norm_num;omega
          have hh := (padicValNat_dvd_iff_le (by omega : U-1≠0)).mp hd
          dsimp [s];omega
        · have hd : 2^2 ∣ U+1 := by norm_num;omega
          have hh := (padicValNat_dvd_iff_le (by omega : U+1≠0)).mp hd
          dsimp [s];omega
      have hs3 : 3 ≤ s := by omega
      have hmax : R<3*2^r := by split_ifs at hb <;> omega
      have factor (x : ℕ) (hx : x≠0) :
          ∃ V : ℕ, V%2=1 ∧ x=2^(padicValNat 2 x)*V := by
        obtain ⟨e,V,hV,he⟩ := Nat.exists_eq_two_pow_mul_odd hx
        have hVo : V%2=1 := by obtain ⟨k,hk⟩ := hV;omega
        have hval : padicValNat 2 x=e := by
          rw [he,padicValNat.mul (by positivity : 2^e≠0) (by omega : V≠0),
            padicValNat.prime_pow,padicValNat.eq_zero_of_not_dvd (by omega : ¬2∣V),add_zero]
        exact ⟨V,hVo,by simpa [hval] using he⟩
      let b:=r+1
      let k:=(s-3)/2
      have hs : s=2*k+3 := by dsimp [k];omega
      have hbpow : 2^b=2*2^r := by dsimp [b];rw [pow_succ];ring
      have hexp : r+s=b+2*k+2 := by dsimp [b];omega
      have ht : R-2^r<2^b := by rw [hbpow];omega
      by_cases hh : padicValNat 2 (U+1)≤padicValNat 2 (U-1)
      · have hsp : s=padicValNat 2 (U-1) := max_eq_left hh
        obtain ⟨V,hV,hVeq⟩ := factor (U-1) (by omega)
        have hUeq : U=2^s*V+1 := by rw [← hsp] at hVeq;omega
        have hm : 2^r*U=V*2^(b+2*k+2)+2^r := by
          rw [hUeq,← hexp,pow_add];ring
        have hV2 : 2*(V/2)+1=V := by omega
        refine ⟨b,k,V/2,1,R-2^r,by dsimp [b];omega,by decide,ht,?_,?_⟩
        · rw [hV2,one_mul,hbpow]
          omega
        · rw [hV2]
          simp only [Nat.sub_self,zero_mul,Nat.sub_zero]
          omega
      · have hsp : s=padicValNat 2 (U+1) := max_eq_right (by omega)
        obtain ⟨V,hV,hVeq⟩ := factor (U+1) (by omega)
        have hUeq : U+1=2^s*V := by rw [← hsp] at hVeq;exact hVeq
        have hm : 2^r*U+2^r=V*2^(b+2*k+2) := by
          rw [← hexp,pow_add]
          nlinarith [congrArg (fun z : ℕ => 2^r*z) hUeq]
        have hV2 : 2*(V/2)+1=V := by omega
        refine ⟨b,k,V/2,0,R-2^r,by dsimp [b];omega,by decide,ht,?_,?_⟩
        · rw [hV2]
          simp only [zero_mul,add_zero]
          omega
        · rw [hV2,hbpow]
          simp only [Nat.sub_zero,one_mul]
          omega
  have even_geometry (n j : ℕ) (hj : j<n)
      (heven : (n-j)%2=0)
      (hpal : List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i)))) :
      ∃ k H : ℕ, n/2=(2*H+1)*2^(2*k+1) ∧
        j/2=(2*H+1)*2^(2*k+1)-1 ∧ n%2=j%2 := by
    let l:=(n-j)/2
    have hL : 2*l=n-j := by dsimp [l];omega
    have hk := even_palindrome_length j l (by simpa [hL] using hpal)
    have hnj : n=j+2 := by omega
    have hpal' : List.Palindrome [u_pd j,u_pd (j+1)] := by
      have hp := hpal
      rw [show n-j=2 by omega] at hp
      simpa [List.ofFn_succ] using hp
    have hp : u_pd j=u_pd (j+1) := by
      have hh := congrArg List.head? hpal'.reverse_eq
      simpa using hh.symm
    have word_val (i : ℕ) : u_pd i=decide (padicValNat 2 (i+1)%2=1) := by
      have hh := (block_valuation (i+1)).2 i (by have ht:=Nat.lt_two_pow_self (n:=i+1);omega)
      simp [u_pd,hh]
    have zero_letter (i : ℕ) (hi : i%2=0) : u_pd i=false := by
      rw [word_val,padicValNat.eq_zero_of_not_dvd (by omega : ¬2∣i+1)]
      rfl
    let t:=n-n%2
    have ht0 : t≠0 := by dsimp [t];omega
    have hletter : u_pd (t-1)=false := by
      by_cases hn : n%2=0
      · have hj0 : j%2=0 := by omega
        have hi : t-1=j+1 := by dsimp [t];omega
        rw [hi,← hp]
        exact zero_letter j hj0
      · have hj1 : (j+1)%2=0 := by omega
        have hi : t-1=j := by dsimp [t];omega
        rw [hi,hp]
        exact zero_letter (j+1) hj1
    have hval : padicValNat 2 t%2=0 := by
      rw [word_val,show t-1+1=t by omega] at hletter
      have hh := of_decide_eq_false hletter
      omega
    obtain ⟨r,V,hV,hd⟩ := Nat.exists_eq_two_pow_mul_odd ht0
    have hVo : V%2=1 := by obtain ⟨k,hk⟩ := hV;omega
    have hv : padicValNat 2 t=r := by
      rw [hd,padicValNat.mul (by positivity : 2^r≠0) (by omega : V≠0),
        padicValNat.prime_pow,padicValNat.eq_zero_of_not_dvd (by omega : ¬2∣V),add_zero]
    have hr0 : r≠0 := by
      intro hh
      rw [hh,pow_zero,one_mul] at hd
      dsimp [t] at hd
      omega
    rw [hv] at hval
    have hr2 : 2≤r := by omega
    let k:=(r-2)/2
    have hr : r=2*k+2 := by dsimp [k];omega
    have ht : t=2*(V*2^(2*k+1)) := by
      rw [hd,hr,show 2*k+2=(2*k+1)+1 by omega,pow_succ]
      ring
    have hVe : 2*(V/2)+1=V := by omega
    refine ⟨k,V/2,?_,?_,by omega⟩
    · rw [hVe]
      dsimp [t] at ht
      omega
    · rw [hVe]
      dsimp [t] at ht
      omega
  by_cases heven : (n-j)%2=0
  · obtain ⟨k,H,hN,hJ,hpar⟩ := even_geometry n j hj heven hpal
    obtain ⟨xs,⟨p⟩,hn,hj,hbits⟩ := relation_high H k 7 (Or.inr rfl)
    have pp : cutBitAutomaton.Path 6 0 ((0,1)::xs) :=
      .cons 7 6 0 (0,1) xs (by simp [cutBitAutomaton,relNext]) p
    refine ⟨6,(0,1)::xs,by simp [hpar],⟨pp⟩,?_,?_,?_⟩
    · simp only [List.foldr_cons,hn,zero_add]
      rw [hN,show 2*k+1=(2*k)+1 by omega,pow_succ]
      ring
    · simp only [List.foldr_cons,hj]
      rw [hJ,show 2*k+1=(2*k)+1 by omega,pow_succ]
      have hh : 0<(2*H+1)*2^(2*k) := by positivity
      rw [show (2*H+1)*(2^(2*k)*2)=2*((2*H+1)*2^(2*k)) by ring]
      omega
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · decide
      · exact hbits a ha
  · have hpar : n%2≠j%2 := by omega
    have hodd : (n-j)%2=1 := by omega
    rcases odd_geometry n j hj hodd hpal with ⟨k,H,t,ht,hn,hj⟩ | ⟨b,k,H,c,t,hb,hc,ht,hn,hj⟩
    · obtain ⟨xs,⟨p⟩,hN,hJ,hbits⟩ := relation_shapes.1 k H t ht
      obtain ⟨r,ys,hr,hp,hyN,hyJ,hybits⟩ :=
        relation_drop n j hpar 1 (Or.inl rfl) xs p (hN.trans hn.symm) (hJ.trans hj.symm) hbits
      exact ⟨r,ys,by simpa only [if_neg hpar] using hr,hp,hyN,hyJ,hybits⟩
    · obtain ⟨xs,⟨p⟩,hN,hJ,hbits⟩ := relation_shapes.2 b k H c t hc ht
      obtain ⟨r,ys,hr,hp,hyN,hyJ,hybits⟩ :=
        relation_drop n j hpar 2 (Or.inr rfl) xs p (hN.trans hn.symm) (hJ.trans hj.symm) hbits
      exact ⟨r,ys,by simpa only [if_neg hpar] using hr,hp,hyN,hyJ,hybits⟩

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.cut_bit_relation_completeness
