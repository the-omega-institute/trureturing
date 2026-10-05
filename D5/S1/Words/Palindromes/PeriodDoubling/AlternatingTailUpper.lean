/- GID: D5/S1/Words/Palindromes/PeriodDoubling/AlternatingTailUpper
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/AlternatingTailUpper
   mirror-E: none(waiver:unbounded-two-cut-tail-construction)
   anchors: []
   utility: none
   digest: Two legal cuts remove two alternating blocks, giving uniform tail upper bounds. -/

/-
proof_shape: content (alternating_tail_upper)
escape_witness: The two-cut construction removes two blocks at every scale and iterates to the endpoint.
admission_basis: escape-witness
Direct frozen dependencies: none; the period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.OddPalindromeRadius
import D5.S1.Words.Palindromes.PeriodDoubling.PalindromicLength
namespace D5.S1.Words.Palindromes.PeriodDoubling
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

theorem alternating_tail_upper (k eps : ℕ) (heps : eps≤1) :
    PL (List.ofFn (fun i : Fin ((∑ j ∈ Finset.range (2*k), 2^(2*j+1))+eps) => u_pd i)) ≤ 2*k+eps := by
  let P : ℕ → ℕ := fun n => PL (List.ofFn (fun i : Fin n => u_pd i))
  let T : ℕ → ℕ := fun m => ∑ j ∈ Finset.range m, 2^(2*j+1)
  have minimum (w : List Bool) : PalFactors w (PL w) := by
    apply (Nat.sInf_mem (s := {k | PalFactors w k}))
    refine ⟨w.length,w.map (fun a => [a]),?_,by simp,?_⟩
    · induction w with
      | nil => rfl
      | cons a w ih => simpa using congrArg (List.cons a) ih
    · intro p hp
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp hp
      exact ⟨by simp,List.Palindrome.singleton a⟩
  have upper (n j : ℕ) (hj : j<n)
      (hpal : List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i)))) :
      P n≤P j+1 := by
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
    apply Nat.sInf_le
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
  have Tstep (m : ℕ) : T (m+1)=T m+2^(2*m+1) := by
    dsimp [T]
    rw [Finset.sum_range_succ]
  have Tbound (m : ℕ) : T m<2^(2*m) := by
    induction m with
    | zero => simp [T]
    | succ m ih =>
      rw [Tstep,show 2*(m+1)=2*m+2 by omega]
      simp only [pow_add,Nat.reducePow]
      omega
  have pair (m : ℕ) : P (T (m+2)+eps)≤P (T m+eps)+2 := by
    let q := 2^(2*m)
    let low := T m+eps
    let n := T (m+2)+eps
    let j := 8*q-1-low
    have hq : 0<q := by dsimp [q];positivity
    have hlo : low≤q := by dsimp [low,q];have hh:=Tbound m;omega
    have hn : n=10*q+low := by
      dsimp [n,low,q]
      rw [Tstep (m+1),Tstep m,show 2*(m+1)+1=2*m+3 by omega]
      simp only [pow_add,Nat.reducePow]
      ring
    have hj : j<n := by dsimp [j];omega
    have hv8 : padicValNat 2 8=3 := by
      change padicValNat 2 (2^3)=3
      exact padicValNat.prime_pow 3
    have hv10 : padicValNat 2 10=1 := by
      rw [show 10=2*5 by decide,padicValNat.mul (by decide : (2:ℕ)≠0) (by decide : (5:ℕ)≠0),
        padicValNat_self,padicValNat.eq_zero_of_not_dvd (by decide : ¬2∣5)]
    have hp := (odd_palindrome_radius (2*m) 9 (q+low) (by decide) (by dsimp [q];omega)).mpr (by
      norm_num only [show (9:ℕ)≠1 by decide,if_false,show 9-1=8 by decide,
        show 9+1=10 by decide,hv8,hv10,show max (3:ℕ) 1=3 by decide,Nat.reduceMod]
      dsimp [q] at *
      omega)
    have hl : n-j=2*(q+low)+1 := by dsimp [j];omega
    have hs : 2^(2*m)*9-(q+low)-1=j := by dsimp [j,q];omega
    have hpal : List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i))) := by
      simpa only [hs,←hl,Fin.val_cast] using hp
    have hfirst := upper n j hj hpal
    let R := 4*q-1-low
    have hjform : j=4*q+R := by dsimp [j,R];omega
    have hsmall : R<2^(2*m+2) := by
      dsimp [R,q]
      rw [pow_add]
      norm_num only [Nat.reducePow]
      omega
    have hp2 := (odd_palindrome_radius (2*m+2) 1 R (by decide) (by simpa using hsmall)).mpr (by
      simpa using hsmall)
    have hpwr : 2^(2*m+2)=4*q := by dsimp [q];rw [pow_add];norm_num;ring
    have hs2 : 2^(2*m+2)*1-R-1=low := by rw [hpwr];dsimp [R];omega
    have hl2 : j-low=2*R+1 := by dsimp [j,R];omega
    have hpal2 : List.Palindrome (List.ofFn (fun i : Fin (j-low) => u_pd (low+i))) := by
      simpa only [hs2,←hl2,Fin.val_cast] using hp2
    have hsecond := upper j low (by dsimp [j];omega) hpal2
    dsimp only [n,low] at hfirst hsecond
    omega
  change P (T (2*k)+eps)≤2*k+eps
  induction k with
  | zero =>
    have ht : T 0=0 := by simp [T]
    rw [ht,zero_add,Nat.mul_zero,zero_add]
    apply Nat.sInf_le
    rcases (by omega : eps=0 ∨ eps=1) with rfl|rfl
    · exact ⟨[],rfl,rfl,by simp⟩
    · refine ⟨[[u_pd 0]],?_,rfl,?_⟩
      · simp [List.ofFn_succ]
      · intro p hp
        have he : p=[u_pd 0] := List.mem_singleton.mp hp
        subst p
        exact ⟨by simp,List.Palindrome.singleton _⟩
  | succ k ih =>
    have h:=pair (2*k)
    rw [show 2*(k+1)=2*k+2 by omega]
    omega

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.alternating_tail_upper
