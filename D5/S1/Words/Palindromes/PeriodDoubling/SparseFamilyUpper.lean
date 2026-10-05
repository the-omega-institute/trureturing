/- GID: D5/S1/Words/Palindromes/PeriodDoubling/SparseFamilyUpper
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/SparseFamilyUpper
   mirror-E: none(waiver:unbounded-sparse-family-factorizations)
   anchors: []
   utility: none
   digest: Repeated sparse-block cuts give diagonal and off-diagonal uniform PPL upper bounds. -/

/-
proof_shape: content (sparse_family_upper)
escape_witness: Induction combines six-cut reductions with the diagonal and alternating terminal paths.
admission_basis: escape-witness
Direct frozen dependencies: D5/S1/Words/Palindromes/FridPrefix/PalindromicLength.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.SparseBlockUpperSteps
import D5.S1.Words.Palindromes.PeriodDoubling.AlternatingTailUpper
namespace D5.S1.Words.Palindromes.PeriodDoubling

open D5.S1.Words.FridPrefix (PL PalFactors)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

theorem sparse_family_upper (a b eps : ℕ) (ha : 0<a) (hao : a%2=1) (hbo : b%2=1)
    (hab : 2*a-1 ≤ b) (heps : eps ≤ 1) :
    let N : ℕ → ℕ → ℕ := fun a b =>
      (∑ i ∈ Finset.range a, 2^(2*b+2+3*i)) +
      (∑ j ∈ Finset.range b, 2^(2*j+1))
    PL (List.ofFn (fun i : Fin (N a b+eps) => u_pd i))  ≤ 
      if b=2*a-1 then 3*a else a+b+eps := by
  classical
  dsimp only
  let P : ℕ → ℕ := fun n => PL (List.ofFn (fun i : Fin n => u_pd i))
  let T : ℕ → ℕ := fun c => ∑ j ∈ Finset.range c, 2^(2*j+1)
  let S : ℕ → ℕ → ℕ → ℕ := fun p z c =>
    (∑ i ∈ Finset.range p, 2^(2*c+z+2+3*i)) + T c
  have terminal (s eps : ℕ) (hs : 4  ≤  s) (hseven : s % 2 = 0) (heps : eps  ≤  1) :
      PL (List.ofFn (fun i : Fin (2^s+2+eps) => u_pd i))  ≤  3 := by
    let P : ℕ → ℕ := fun n => PL (List.ofFn (fun i : Fin n => u_pd i))
    have minimum (w : List Bool) : PalFactors w (PL w) := by
      unfold PL
      exact Nat.find_spec _
    have upper (n j : ℕ) (hj : j<n)
        (hpal : List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i)))) :
        P n ≤ P j+1 := by
      let tail := List.ofFn (fun i : Fin (n-j) => u_pd (j+i))
      have parts :
          (List.ofFn (fun i : Fin n => u_pd i)).take j =
            List.ofFn (fun i : Fin j => u_pd i) ∧
          (List.ofFn (fun i : Fin n => u_pd i)).drop j = tail := by
        constructor
        · apply List.ext_getElem
          · simp only [List.length_take,List.length_ofFn];omega
          · intro i hi hi'
            simp only [List.getElem_take,List.getElem_ofFn]
        · apply List.ext_getElem
          · simp only [tail,List.length_drop,List.length_ofFn]
          · intro i hi hi'
            simp only [tail,List.getElem_drop,List.getElem_ofFn]
      have split := List.take_append_drop j (List.ofFn (fun i : Fin n => u_pd i))
      rw [parts.1,parts.2] at split
      obtain ⟨ps,hflat,hlen,hps⟩ := minimum (List.ofFn (fun i : Fin j => u_pd i))
      apply Nat.find_le
      refine ⟨ps++[tail],?_,?_,?_⟩
      · simpa [List.flatten_append,hflat] using split
      · simpa [P,hlen]
      · intro p hp
        rcases List.mem_append.mp hp with hp|hp
        · exact hps p hp
        · have he : p=tail := List.mem_singleton.mp hp
          subst p
          refine ⟨?_,hpal⟩
          intro he
          have hh := congrArg List.length he
          simp only [tail,List.length_ofFn,List.length_nil] at hh
          omega
    have singleton (n : ℕ) : P (n+1) ≤ P n+1 := by
      apply upper (n+1) n (by omega)
      simpa [List.ofFn_succ] using List.Palindrome.singleton (u_pd n)
    have hzero : P 0=0 := by
      apply Nat.eq_zero_of_le_zero
      apply Nat.find_le
      exact ⟨[],rfl,rfl,by simp⟩
    let q := 2^(s-1)
    have hq : 0<q := by dsimp [q];positivity
    have hpwr : 2^s=2*q := by
      rw [show s=(s-1)+1 by omega,pow_succ]
      dsimp [q]
      omega
    have hp := (odd_palindrome_radius (s-1) 1 (q-1) (by decide) (by dsimp [q];omega)).mpr (by
      change q-1<q
      omega)
    have hs0 : 2^(s-1)*1-(q-1)-1=0 := by dsimp [q];omega
    have hl0 : 2*(q-1)+1=2^s-1 := by rw [hpwr];omega
    have hpal : List.Palindrome (List.ofFn (fun i : Fin (2^s-1) => u_pd i)) := by
      simpa only [hs0,hl0,Nat.zero_add,Fin.val_cast] using hp
    have hend : P (2^s-1) ≤ 1 := by
      have h:=upper (2^s-1) 0 (by rw [hpwr];omega) (by simpa using hpal)
      omega
    have word_val (n : ℕ) : u_pd n=decide (padicValNat 2 (n+1)%2=1) := by
      have hh := (block_valuation (n+1)).2 n (by have h:=Nat.lt_two_pow_self (n:=n+1);omega)
      simp [u_pd,hh]
    rcases (by omega : eps=0 ∨ eps=1) with rfl|rfl
    · have hleft : u_pd (2^s-1)=false := by
        rw [word_val,show 2^s-1+1=2^s by rw [hpwr];omega,padicValNat.prime_pow]
        simp [hseven]
      have hright : u_pd (2^s)=false := by
        rw [word_val,padicValNat.eq_zero_of_not_dvd (by
          have hdiv : 2∣2^s := dvd_pow_self 2 (by omega : s≠0)
          omega : ¬2∣2^s+1)]
        rfl
      have hmid : P (2^s+1) ≤ P (2^s-1)+1 := by
        apply upper (2^s+1) (2^s-1) (by omega)
        have hp : List.Palindrome [u_pd (2^s-1),u_pd (2^s)] := by
          rw [hleft,hright]
          exact List.Palindrome.cons_concat false List.Palindrome.nil
        simpa [show 2^s+1-(2^s-1)=2 by rw [hpwr];omega,List.ofFn_succ,
          show 2^s-1+1=2^s by rw [hpwr];omega] using hp
      have h : P (2^s+2) ≤ P (2^s+1)+1 := by
        simpa only [show 2^s+1+1=2^s+2 by omega] using singleton (2^s+1)
      change P (2^s+2+0) ≤ 3
      simp only [Nat.add_zero]
      omega
    · have hu : (q+1)%2=1 := by
        have hdiv : 2∣q := by dsimp [q];exact dvd_pow_self 2 (by omega : s-1≠0)
        omega
      have hp := (odd_palindrome_radius 1 (q+1) 1 hu (by omega)).mpr (by
        split_ifs <;> norm_num)
      have hs1 : 2^1*(q+1)-1-1=2^s := by rw [hpwr];norm_num;omega
      have hpal : List.Palindrome (List.ofFn (fun i : Fin 3 => u_pd (2^s+i))) := by
        simpa only [show 2*1+1=3 by decide,hs1,Fin.val_cast] using hp
      have hfirst : P (2^s+3) ≤ P (2^s)+1 := by
        apply upper (2^s+3) (2^s) (by omega)
        simpa using hpal
      have hsecond := singleton (2^s-1)
      have hplus : 2^s-1+1=2^s := by rw [hpwr];omega
      rw [hplus] at hsecond
      change P (2^s+2+1) ≤ 3
      rw [show 2^s+2+1=2^s+3 by omega]
      omega
  have reduce (t z c : ℕ) (hz : z%2=0) (hc : 4*t+1 ≤ c) :
      P (S (2*t+1) z c+eps) ≤ P (S 1 (z+14*t) (c-4*t)+eps)+6*t := by
    induction t generalizing z c with
    | zero =>
      simp only [Nat.mul_zero,Nat.zero_add,Nat.add_zero,Nat.sub_zero]
      exact le_rfl
    | succ t ih =>
      have h1:=sparse_block_upper_steps (2*(t+1)+1) z c eps (by omega) heps
      dsimp only at h1
      change ((z%2=0 ∧ 3 ≤ c) → P (S (2*(t+1)+1) z c+eps) ≤ P (S (2*(t+1)+1-1) (z+9) (c-3)+eps)+4) ∧ _ at h1
      have hfirst:=h1.1 ⟨hz,by omega⟩
      have h2:=sparse_block_upper_steps (2*(t+1)) (z+9) (c-3) eps (by omega) heps
      dsimp only at h2
      change _ ∧ (((z+9)%2=1 ∧ 1 ≤ c-3) → P (S (2*(t+1)) (z+9) (c-3)+eps) ≤ 
        P (S (2*(t+1)-1) (z+9+5) (c-3-1)+eps)+2) at h2
      have hsecond:=h2.2 ⟨by omega,by omega⟩
      have hthird:=ih (z+14) (c-4) (by omega) (by omega)
      rw [show 2*(t+1)+1-1=2*(t+1) by omega] at hfirst
      rw [show 2*(t+1)-1=2*t+1 by omega,show z+9+5=z+14 by omega,
        show c-3-1=c-4 by omega] at hsecond
      rw [show z+14+14*t=z+14*(t+1) by omega,
        show c-4-4*t=c-4*(t+1) by omega] at hthird
      omega
  let t:=(a-1)/2
  have haform : a=2*t+1 := by dsimp [t];omega
  have hb : 4*t+1 ≤ b := by omega
  have hr:=reduce t 0 b (by decide) hb
  rw [←haform,Nat.zero_add] at hr
  let c:=b-4*t
  have hco : c%2=1 := by dsimp [c];omega
  have hc : 1 ≤ c := by dsimp [c];omega
  have hinput : (∑ i ∈ Finset.range a,2^(2*b+2+3*i)) +
      (∑ j ∈ Finset.range b,2^(2*j+1))=S a 0 b := by dsimp [S,T]
  change P ((∑ i ∈ Finset.range a,2^(2*b+2+3*i)) +
      (∑ j ∈ Finset.range b,2^(2*j+1))+eps)  ≤  if b=2*a-1 then 3*a else a+b+eps
  rw [hinput]
  by_cases hdiag : b=2*a-1
  · rw [if_pos hdiag]
    have hc1 : c=1 := by dsimp [c];omega
    have hterminal:=terminal (14*t+4) eps (by omega) (by omega) heps
    have he : S 1 (14*t) (b-4*t)=2^(14*t+4)+2 := by
      have hb1 : b-4*t=1 := hc1
      rw [hb1]
      simp [S,T,pow_add]
      ring
    rw [he] at hr
    change P (2^(14*t+4)+2+eps) ≤ 3 at hterminal
    omega
  · rw [if_neg hdiag]
    have hc3 : 3 ≤ c := by dsimp [c];omega
    have hstep:=sparse_block_upper_steps 1 (14*t) c eps (by decide) heps
    dsimp only at hstep
    change (((14*t)%2=0 ∧ 3 ≤ c) → P (S 1 (14*t) c+eps) ≤ P (S (1-1) (14*t+9) (c-3)+eps)+4) ∧ _ at hstep
    have hf:=hstep.1 ⟨by omega,hc3⟩
    have hout : S (1-1) (14*t+9) (c-3)=T (c-3) := by simp [S]
    rw [hout] at hf
    have heven : 2*((c-3)/2)=c-3 := by omega
    have htail:=alternating_tail_upper ((c-3)/2) eps heps
    rw [heven] at htail
    change P (T (c-3)+eps) ≤ c-3+eps at htail
    change P (S a 0 b+eps) ≤ P (S 1 (14*t) c+eps)+6*t at hr
    dsimp [c] at *
    omega

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.sparse_family_upper
