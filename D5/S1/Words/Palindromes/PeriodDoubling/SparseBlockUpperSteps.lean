/- GID: D5/S1/Words/Palindromes/PeriodDoubling/SparseBlockUpperSteps
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/SparseBlockUpperSteps
   mirror-E: none(waiver:unbounded-sparse-block-cut-constructions)
   anchors: []
   utility: none
   digest: Four or two legal cuts remove a high block and three or one alternating tail blocks. -/

/-
proof_shape: content (sparse_block_upper_steps)
escape_witness: The explicit four-cut and two-cut chains preserve the higher prefix and endpoint bit.
admission_basis: escape-witness
Direct frozen dependencies: D5/S1/Words/Palindromes/FridPrefix/PalindromicLength.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.OddPalindromeRadius
import D5.S1.Words.Palindromes.PeriodDoubling.PalindromicLength
namespace D5.S1.Words.Palindromes.PeriodDoubling

open D5.S1.Words.FridPrefix (PL PalFactors)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

theorem sparse_block_upper_steps (p z c eps : ℕ) (hp : 0<p) (heps : eps≤1) :
    let S : ℕ → ℕ → ℕ → ℕ := fun p z c =>
      (∑ i ∈ Finset.range p, 2^(2*c+z+2+3*i)) +
      (∑ j ∈ Finset.range c, 2^(2*j+1))
    let P : ℕ → ℕ := fun n => PL (List.ofFn (fun i : Fin n => u_pd i))
    ((z%2=0 ∧ 3 ≤ c) → P (S p z c+eps)≤P (S (p-1) (z+9) (c-3)+eps)+4) ∧
    ((z%2=1 ∧ 1 ≤ c) → P (S p z c+eps)≤P (S (p-1) (z+5) (c-1)+eps)+2) := by
  classical
  dsimp only
  let P : ℕ → ℕ := fun n => PL (List.ofFn (fun i : Fin n => u_pd i))
  let T : ℕ → ℕ := fun m => ∑ j ∈ Finset.range m, 2^(2*j+1)
  let A : ℕ → ℕ := fun m => ∑ j ∈ Finset.range m, 2^(3*j)
  let S : ℕ → ℕ → ℕ → ℕ := fun p z c =>
      (∑ i ∈ Finset.range p, 2^(2*c+z+2+3*i)) + T c
  have minimum (w : List Bool) : PalFactors w (PL w) := by
    unfold PL
    exact Nat.find_spec _
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
  have longcut (r s V c t : ℕ) (hs : 3 ≤ s) (hso : s%2=1) (hV : V%2=1)
      (hc : c≤1) (ht : t<2*2^r) :
      let n := V*2^(r+s)+c*2^(r+1)+t
      let j := V*2^(r+s)-(1-c)*2^(r+1)-1-t
      j<n ∧ List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i))) := by
    dsimp only
    let q := 2^r
    let W := V*2^(s-1)
    have hq : 0<q := by dsimp [q];positivity
    have hV0 : 0<V := by omega
    have hW0 : 0<W := by dsimp [W];positivity
    have hWeven : W%2=0 := by
      have hdiv : 2∣W := by
        dsimp [W]
        exact dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega : s-1≠0)) V
      omega
    have hW2 : 2≤W := by omega
    have hscale : V*2^s=2*W := by
      rw [show s=(s-1)+1 by omega,pow_succ]
      dsimp [W]
      ring
    have htop : V*2^(r+s)=q*(2*W) := by
      calc
        V*2^(r+s)=q*(V*2^s) := by dsimp [q];rw [pow_add];ring
        _=q*(2*W) := by rw [hscale]
    have hpow : 2^(r+1)=2*q := by dsimp [q];rw [pow_succ];ring
    have htopbound : 4*q≤V*2^(r+s) := by rw [htop];nlinarith
    have mainval : padicValNat 2 (V*2^s)=s := by
      rw [padicValNat.mul hV0.ne' (by positivity),padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by omega : ¬2∣V)]
      omega
    have nearval (x : ℕ) (hx : x%2=1) : padicValNat 2 (2*x)=1 := by
      rw [padicValNat.mul (by decide : (2:ℕ)≠0) (by omega),padicValNat_self,
        padicValNat.eq_zero_of_not_dvd (by omega : ¬2∣x)]
    rcases (by omega : c=0 ∨ c=1) with rfl|rfl
    · let u := 2*W-1
      have hu : u%2=1 := by dsimp [u];omega
      have hup : u+1=V*2^s := by rw [hscale];dsimp [u];omega
      have hum : u-1=2*(W-1) := by dsimp [u];omega
      have hvalup : padicValNat 2 (u+1)=s := by rw [hup];exact mainval
      have hvaldown : padicValNat 2 (u-1)=1 := by
        rw [hum]
        exact nearval (W-1) (by omega)
      have hU3 : 3≤u := by dsimp [u];omega
      have hR : q+t<2^r*u := by
        have h:=Nat.mul_le_mul_left q hU3
        change q+t<q*u
        dsimp [q] at *
        omega
      have hp := (odd_palindrome_radius r u (q+t) hu hR).mpr (by
        have hu1 : u≠1 := by dsimp [u];omega
        simp only [hu1,if_false,hvaldown,hvalup,max_eq_right (by omega : 1 ≤ s),hso,
          show ¬(1:ℕ)=0 by decide]
        dsimp [q] at *
        omega)
      have hj : V*2^(r+s)-(1-0)*2^(r+1)-1-t < V*2^(r+s)+0*2^(r+1)+t := by
        rw [htop,hpow]
        omega
      have hjform : 2^r*u-(q+t)-1=V*2^(r+s)-(1-0)*2^(r+1)-1-t := by
        rw [htop,hpow]
        dsimp [u,q]
        have hmul := Nat.mul_sub_left_distrib (2^r) (2*W) 1
        have hprod : 4*2^r≤2^r*(2*W) := by nlinarith
        omega
      have hlen : (V*2^(r+s)+0*2^(r+1)+t)-(V*2^(r+s)-(1-0)*2^(r+1)-1-t)=2*(q+t)+1 := by
        rw [htop,hpow]
        omega
      exact ⟨hj,by simpa only [hjform,←hlen,Fin.val_cast] using hp⟩
    · let u := 2*W+1
      have hu : u%2=1 := by dsimp [u];omega
      have hum : u-1=V*2^s := by rw [hscale];dsimp [u]
      have hup : u+1=2*(W+1) := by dsimp [u];omega
      have hvaldown : padicValNat 2 (u-1)=s := by rw [hum];exact mainval
      have hvalup : padicValNat 2 (u+1)=1 := by
        rw [hup]
        exact nearval (W+1) (by omega)
      have hU3 : 3≤u := by dsimp [u];omega
      have hR : q+t<2^r*u := by
        have h:=Nat.mul_le_mul_left q hU3
        change q+t<q*u
        dsimp [q] at *
        omega
      have hp := (odd_palindrome_radius r u (q+t) hu hR).mpr (by
        have hu1 : u≠1 := by dsimp [u];omega
        simp only [hu1,if_false,hvaldown,hvalup,max_eq_left (by omega : 1 ≤ s),hso,
          show ¬(1:ℕ)=0 by decide]
        dsimp [q] at *
        omega)
      have hj : V*2^(r+s)-(1-1)*2^(r+1)-1-t < V*2^(r+s)+1*2^(r+1)+t := by
        rw [htop,hpow]
        omega
      have hjform : 2^r*u-(q+t)-1=V*2^(r+s)-(1-1)*2^(r+1)-1-t := by
        rw [htop,hpow]
        dsimp [u,q]
        have hm : 2^r*(2*W+1)=2^r*(2*W)+2^r := by ring
        omega
      have hlen : (V*2^(r+s)+1*2^(r+1)+t)-(V*2^(r+s)-(1-1)*2^(r+1)-1-t)=2*(q+t)+1 := by
        rw [htop,hpow]
        omega
      exact ⟨hj,by simpa only [hjform,←hlen,Fin.val_cast] using hp⟩
  have shortcut (h H t : ℕ) (ht : t<2^h) :
      let n := H*2^(h+1)+2^h+t
      let j := H*2^(h+1)+(2^h-1-t)
      j<n ∧ List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i))) := by
    dsimp only
    have hpow : 0<2^h := by positivity
    have hcenter : 2^h*(2*H+1)=H*2^(h+1)+2^h := by rw [pow_succ];ring
    have hp := (odd_palindrome_radius h (2*H+1) t (by omega) (by rw [hcenter];omega)).mpr (by
      split_ifs <;> omega)
    have hj : H*2^(h+1)+(2^h-1-t)<H*2^(h+1)+2^h+t := by omega
    have hjform : 2^h*(2*H+1)-t-1=H*2^(h+1)+(2^h-1-t) := by rw [hcenter];omega
    have hlen : (H*2^(h+1)+2^h+t)-(H*2^(h+1)+(2^h-1-t))=2*t+1 := by omega
    exact ⟨hj,by simpa only [hjform,←hlen,Fin.val_cast] using hp⟩
  have removeTop (r s V t : ℕ) (hs : 3 ≤ s) (hso : s%2=1) (hV : V%2=1) (ht : t<2*2^r) :
      PL (List.ofFn (fun i : Fin (V*2^(r+s)+2^(r+1)+t) => u_pd i)) ≤
        PL (List.ofFn (fun i : Fin ((V-1)*2^(r+s)+t) => u_pd i))+2 := by
    let h := r+s
    let q := 2^(h-1)
    have hq : 0<q := by dsimp [q];positivity
    have hpow : 2^h=2*q := by rw [show h=(h-1)+1 by dsimp [h];omega,pow_succ];dsimp [q];ring
    have htq : t<q := by
      have he : 2*2^r=2^(r+1) := by rw [pow_succ];ring
      rw [he] at ht
      exact lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide) (by dsimp [h];omega))
    have h1:=longcut r s V 1 t hs hso hV (by decide) ht
    dsimp only at h1
    let j := V*2^h-1-t
    have hjtop : j=(V-1)*2^h+q+(q-1-t) := by
      have hV0 : 0<V := by omega
      have hVm : (V-1)*2^h+2^h=V*2^h := by
        nlinarith [Nat.sub_add_cancel (show 1≤V by omega)]
      dsimp [j]
      rw [hpow] at hVm ⊢
      omega
    have h2:=shortcut (h-1) (V-1) (q-1-t) (by change q-1-t<q;omega)
    dsimp only at h2
    have he : h-1+1=h := by dsimp [h];omega
    have hback : 2^(h-1)-1-(q-1-t)=t := by change q-1-(q-1-t)=t;omega
    simp only [he,hback] at h2
    have hp1 : P (V*2^h+2^(r+1)+t)≤P j+1 := by
      apply upper
      · simpa [h,j] using h1.1
      · simpa [h,j] using h1.2
    have hp2 : P j≤P ((V-1)*2^h+t)+1 := by
      apply upper
      · simpa [hjtop,q] using h2.1
      · simpa [hjtop,q] using h2.2
    change P (V*2^h+2^(r+1)+t)≤P ((V-1)*2^h+t)+2
    omega
  have state (p z c : ℕ) : S p z c=A p*2^(2*c+z+2)+T c := by
    dsimp [S,A]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_add]
    ring
  have Astep (p : ℕ) : A (p+1)=1+8*A p := by
    dsimp [A]
    rw [Finset.sum_range_succ']
    simp only [Nat.mul_zero,pow_zero]
    have hh : (∑ x ∈ Finset.range p, 2^(3*(x+1)))=8*∑ x ∈ Finset.range p,2^(3*x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show 3*(i+1)=3*i+3 by omega,pow_add]
      norm_num
      ring
    rw [hh]
    omega
  let H:=A (p-1)
  let h:=2*c+z+2
  let B:=H*2^(h+3)
  have hin (c z : ℕ) : S p z c=A (p-1)*2^(2*c+z+5)+2^(2*c+z+2)+T c := by
    rw [state]
    have ha:=Astep (p-1)
    rw [show p-1+1=p by omega] at ha
    rw [ha]
    rw [show 2*c+z+5=(2*c+z+2)+3 by omega,pow_add]
    norm_num only [Nat.reducePow]
    ring
  change ((z%2=0 ∧ 3 ≤ c) → P (S p z c+eps)≤P (S (p-1) (z+9) (c-3)+eps)+4) ∧
    ((z%2=1 ∧ 1 ≤ c) → P (S p z c+eps)≤P (S (p-1) (z+5) (c-1)+eps)+2)
  constructor
  · rintro ⟨hz,hc⟩
    let r:=2*c-6
    let q:=2^r
    let low:=T (c-3)+eps
    have hq : 0<q := by dsimp [q];positivity
    have hlo : low≤q := by
      have hh:=Tbound (c-3)
      have he : 2*(c-3)=r := by dsimp [r];omega
      rw [he] at hh
      dsimp [low,q]
      omega
    have hT : T c=42*q+T (c-3) := by
      conv_lhs => rw [show c=(c-3)+1+1+1 by omega,Tstep,Tstep,Tstep]
      have e0 : 2*(c-3)+1=r+1 := by dsimp [r];omega
      have e1 : 2*(c-3+1)+1=r+3 := by dsimp [r];omega
      have e2 : 2*(c-3+1+1)+1=r+5 := by dsimp [r];omega
      rw [e0,e1,e2]
      simp only [pow_add,Nat.reducePow]
      dsimp [q]
      ring
    have he : h=r+(z+8) := by dsimp [h,r];omega
    have hbase : 2^h=q*2^(z+8) := by rw [he,pow_add]
    have hB : B=H*q*2^(z+11) := by
      dsimp [B]
      rw [he,show r+(z+8)+3=r+(z+11) by omega,pow_add]
      dsimp [q]
      ring
    let V1:=H*2^(z+8)+2^(z+5)+5
    let V2:=H*2^(z+6)+2^(z+3)+1
    have hV1 : V1%2=1 := by dsimp [V1];simp [pow_add,Nat.mul_mod,Nat.add_mod]
    have hV2 : V2%2=1 := by dsimp [V2];simp [pow_add,Nat.mul_mod,Nat.add_mod]
    have htop1 : V1*2^(r+3)=B+2^h+40*q := by
      rw [hB,hbase]
      dsimp [V1,q]
      simp only [pow_add,Nat.reducePow]
      ring
    have htop2 : V2*2^((r+2)+3)=B+2^h+32*q := by
      rw [hB,hbase]
      dsimp [V2,q]
      simp only [pow_add,Nat.reducePow]
      ring
    have h2q : 2^(r+1)=2*q := by dsimp [q];rw [pow_succ];ring
    have h8q : 2^((r+2)+1)=8*q := by dsimp [q];simp only [pow_add,Nat.reducePow];ring
    have hn : S p z c+eps=B+2^h+42*q+low := by
      rw [hin,hT]
      dsimp [B,H,h,low]
      rw [show 2*c+z+5=(2*c+z+2)+3 by omega]
      ring
    let j1:=B+2^h+40*q-1-low
    let j2:=B+2^h+16*q+low
    have h1:=longcut r 3 V1 1 low (by decide) (by decide) hV1 (by decide) (by omega)
    dsimp only at h1
    have n1 : V1*2^(r+3)+1*2^(r+1)+low=S p z c+eps := by rw [htop1,h2q,hn];omega
    have e1 : V1*2^(r+3)-(1-1)*2^(r+1)-1-low=j1 := by rw [htop1];simp only [Nat.sub_self,zero_mul,Nat.sub_zero];rfl
    have hp1 : P (S p z c+eps)≤P j1+1 := by
      apply upper
      · simpa only [n1,e1] using h1.1
      · simpa only [n1,e1,Fin.val_cast] using h1.2
    let t2:=8*q-1-low
    have ht2 : t2<2*2^(r+2) := by dsimp [t2,q];simp only [pow_add,Nat.reducePow];omega
    have h2:=longcut (r+2) 3 V2 0 t2 (by decide) (by decide) hV2 (by decide) ht2
    dsimp only at h2
    have n2 : V2*2^((r+2)+3)+0*2^((r+2)+1)+t2=j1 := by rw [htop2];dsimp [t2,j1];omega
    have e2 : V2*2^((r+2)+3)-(1-0)*2^((r+2)+1)-1-t2=j2 := by
      rw [htop2,h8q]
      dsimp [t2,j2]
      omega
    have hp2 : P j1≤P j2+1 := by
      apply upper
      · simpa only [n2,e2] using h2.1
      · simpa only [n2,e2,Fin.val_cast] using h2.2
    have he3 : r+3+(z+5)=h := by omega
    have h16q : 2^(r+3+1)=16*q := by dsimp [q];simp only [pow_add,Nat.reducePow];ring
    have ht3 : low<2*2^(r+3) := by dsimp [q] at *;simp only [pow_add,Nat.reducePow];omega
    have hp3:=removeTop (r+3) (z+5) (8*H+1) low (by omega) (by omega) (by omega) ht3
    have n3 : (8*H+1)*2^(r+3+(z+5))+2^(r+3+1)+low=j2 := by
      rw [he3,h16q]
      dsimp [j2,B]
      rw [pow_add]
      norm_num only [Nat.reducePow]
      ring
    have e3 : (8*H+1-1)*2^(r+3+(z+5))+low=S (p-1) (z+9) (c-3)+eps := by
      rw [he3,state]
      have heout : 2*(c-3)+(z+9)+2=h+3 := by dsimp [h];omega
      rw [heout]
      dsimp [B,H,low]
      rw [pow_add]
      norm_num only [Nat.reducePow]
      ring
    change P ((8*H+1)*2^(r+3+(z+5))+2^(r+3+1)+low)≤
      P ((8*H+1-1)*2^(r+3+(z+5))+low)+2 at hp3
    rw [n3,e3] at hp3
    omega
  · rintro ⟨hz,hc⟩
    let r:=2*c-2
    let low:=T (c-1)+eps
    have hlo : low≤2^r := by
      have hh:=Tbound (c-1)
      rw [show 2*(c-1)=r by dsimp [r];omega] at hh
      dsimp [low]
      omega
    have hn : S p z c+eps=(8*H+1)*2^(r+(z+4))+2^(r+1)+low := by
      rw [hin,show c=(c-1)+1 by omega,Tstep]
      have e0 : r+(z+4)=2*(c-1+1)+z+2 := by dsimp [r];omega
      have e1 : r+1=2*(c-1)+1 := by dsimp [r];omega
      rw [e0,e1]
      dsimp [H,low]
      simp only [pow_add,Nat.reducePow]
      ring
    have ht : low<2*2^r := by
      have hpos : 0<2^r := by positivity
      omega
    have hp2:=removeTop r (z+4) (8*H+1) low (by omega) (by omega) (by omega) ht
    have hout : (8*H+1-1)*2^(r+(z+4))+low=S (p-1) (z+5) (c-1)+eps := by
      rw [state]
      have e0 : r+(z+4)+3=2*(c-1)+(z+5)+2 := by dsimp [r];omega
      dsimp [H,low]
      rw [←e0,pow_add]
      norm_num only [Nat.reducePow]
      ring
    change P ((8*H+1)*2^(r+(z+4))+2^(r+1)+low)≤
      P ((8*H+1-1)*2^(r+(z+4))+low)+2 at hp2
    rw [←hn,hout] at hp2
    exact hp2

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.sparse_block_upper_steps
