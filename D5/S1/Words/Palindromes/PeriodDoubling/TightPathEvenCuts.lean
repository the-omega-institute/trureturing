/- GID: D5/S1/Words/Palindromes/PeriodDoubling/TightPathEvenCuts
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/TightPathEvenCuts
   mirror-E: none(waiver:at-most-one-tight-even-cut)
   anchors: []
   utility: none
   digest: A tight palindrome-cut path starting in class S has at most one even cut. -/

/-
proof_shape: content (tight_path_at_most_one_even_cut)
escape_witness: Path induction preserves a positive valuation after the first even cut and excludes a second.
admission_basis: escape-witness
Direct frozen dependencies: none; the imported period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.TightCutCharge
import D5.S1.Words.Palindromes.PeriodDoubling.TightCutLowestPosition
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S1.Words.Palindromes.PeriodDoubling

theorem tight_path_at_most_one_even_cut (n : ℕ) (cuts : List ℕ)
    (hS : classS n)
    (hchain : (n::cuts).IsChain (fun s t => t < s ∧
      List.Palindrome (List.ofFn (fun i : Fin (s-t) => u_pd (t+i))) ∧
      signedWeight (((s+1)/2 : ℕ) : ℤ)=signedWeight (((t+1)/2 : ℕ) : ℤ)+1)) :
    (((n::cuts).zip cuts).filter (fun e => e.1%2 == e.2%2)).length ≤ 1 := by
  have phase (n j : ℕ) (hj : j < n) (heven : n%2=j%2)
      (hpal : List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i))))
      (htight : signedWeight (((n+1)/2 : ℕ) : ℤ)=signedWeight (((j+1)/2 : ℕ) : ℤ)+1) :
      n=j+2 ∧ n%2=1 ∧ 5≤n ∧ ((n+1)/2)%2=1 ∧
        0 < padicValNat 2 ((j+1)/2) := by
    let k:=(n-j)/2
    have hlen : 2*k=n-j := by dsimp [k];omega
    have hk:=even_palindrome_length j k (by simpa [hlen] using hpal)
    have hnj : n=j+2 := by omega
    have hp : List.Palindrome [u_pd j,u_pd (j+1)] := by
      rw [show n-j=2 by omega] at hpal
      simpa [List.ofFn_succ] using hpal
    have letters : u_pd j=u_pd (j+1) := by
      have hh:=congrArg List.head? hp.reverse_eq
      simpa using hh.symm
    obtain ⟨hz,ho,hneg,htri,htwo,hodd⟩:=signed_weight_arithmetic
    have pred (X : ℕ) (hx : 0 < X) (he : X%2=0) :
        signedWeight (X : ℤ) ≤ signedWeight ((X-1 : ℕ) : ℤ) := by
      have hv : (X : ℤ)=2*(X/2 : ℕ) := by omega
      have hp : ((X-1 : ℕ) : ℤ)=2*((X/2 : ℕ) : ℤ)-1 := by omega
      have hp' : 2*((X/2 : ℕ) : ℤ)-1=2*(((X/2 : ℕ) : ℤ)-1)+1 := by ring
      have ha:=htri (((X/2 : ℕ) : ℤ)-1) 1
      have hs : (((X/2 : ℕ) : ℤ)-1)+1=((X/2 : ℕ) : ℤ) := by ring
      rw [hs,ho] at ha
      rw [hv,htwo,hp,hp',hodd,hs]
      omega
    have Xodd : ((n+1)/2)%2=1 := by
      by_contra hh
      have he : ((n+1)/2)%2=0 := by omega
      have hp:=pred ((n+1)/2) (by omega) he
      have hjX : (j+1)/2=(n+1)/2-1 := by omega
      rw [← hjX] at hp
      omega
    have word_val (i : ℕ) : u_pd i=decide (padicValNat 2 (i+1)%2=1) := by
      have h:=(block_valuation (i+1)).2 i (by have ht:=Nat.lt_two_pow_self (n:=i+1);omega)
      simp [u_pd,h]
    have nodd : n%2=1 := by
      by_contra hh
      have ne : n%2=0 := by omega
      have jm : j%2=0 := by omega
      have jl : u_pd j=false := by
        rw [word_val,padicValNat.eq_zero_of_not_dvd (by omega : ¬2 ∣ j+1)]
        rfl
      have nv : padicValNat 2 n=1 := by
        have hn : n=2*(n/2) := by omega
        have hv : ¬2 ∣ n/2 := by omega
        rw [hn,padicValNat.mul (by decide : (2:ℕ)≠0) (by omega : n/2≠0),
          padicValNat_self,padicValNat.eq_zero_of_not_dvd hv]
      have jr : u_pd (j+1)=true := by rw [word_val,show j+1+1=n by omega,nv];rfl
      rw [jl,jr] at letters
      contradiction
    have nlarge : 5≤n := by
      by_contra hh
      have hn : n=3 := by omega
      have hjj : j=1 := by omega
      subst n;subst j
      have bad : ¬List.Palindrome [u_pd 1,u_pd 2] := by decide
      exact bad hp
    have hpos : 0 < padicValNat 2 ((j+1)/2) := by
      have hd : 2 ∣ (j+1)/2 := by omega
      exact one_le_padicValNat_of_dvd (p:=2) (by omega : (j+1)/2 ≠ 0) hd
    exact ⟨hnj,nodd,nlarge,Xodd,hpos⟩
  let Rel : ℕ → ℕ → Prop := fun s t => t < s ∧
    List.Palindrome (List.ofFn (fun i : Fin (s-t) => u_pd (t+i))) ∧
    signedWeight (((s+1)/2 : ℕ) : ℤ)=signedWeight (((t+1)/2 : ℕ) : ℤ)+1
  have no_even (n : ℕ) (cuts : List ℕ) (hS : classS n)
      (hv : 0 < padicValNat 2 ((n+1)/2)) (hc : (n::cuts).IsChain Rel) :
      (((n::cuts).zip cuts).filter (fun e => e.1%2 == e.2%2)).length=0 := by
    induction cuts generalizing n with
    | nil => simp
    | cons j cuts ih =>
      obtain ⟨⟨hj,hpal,htight⟩,hrest⟩:=List.isChain_cons_cons.mp hc
      have he : n%2 ≠ j%2 := by
        intro hh
        obtain ⟨_,_,_,hX,_⟩:=phase n j hj hh hpal htight
        have h0:=padicValNat.eq_zero_of_not_dvd (p:=2) (by omega : ¬2 ∣ (n+1)/2)
        omega
      have hSj:=(tight_cut_class_and_Q n j hS hj hpal htight).1
      by_cases hj0 : j=0
      · subst j
        have hnil : cuts=[] := by
          cases cuts with
          | nil => rfl
          | cons k cuts =>
            have hbad:=(List.isChain_cons_cons.mp hrest).1.1
            omega
        subst cuts
        simp [he]
      · have hvj : 0 < padicValNat 2 ((j+1)/2) := by
          rcases tight_cut_lowest_position n j hS hj hpal htight with hh | hh
          · exact (hj0 hh).elim
          · omega
        have hh:=ih j hSj hvj hrest
        simpa [he] using hh
  change (n::cuts).IsChain Rel at hchain
  induction cuts generalizing n with
  | nil => simp
  | cons j cuts ih =>
    obtain ⟨⟨hj,hpal,htight⟩,hrest⟩:=List.isChain_cons_cons.mp hchain
    have hSj:=(tight_cut_class_and_Q n j hS hj hpal htight).1
    by_cases he : n%2=j%2
    · have hp:=(phase n j hj he hpal htight).2.2.2.2
      have hh:=no_even j cuts hSj hp hrest
      simp [he,hh]
    · have hh:=ih j hSj hrest
      simpa [he] using hh

end D5.S1.Words.Palindromes.PeriodDoubling
#print axioms D5.S1.Words.Palindromes.PeriodDoubling.tight_path_at_most_one_even_cut
