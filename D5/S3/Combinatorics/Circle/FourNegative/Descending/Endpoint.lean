/- GID: D5/S3/Combinatorics/Circle/FourNegative/Descending/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/Descending/Endpoint
   mirror-E: none(waiver:physical-dependent-source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: One actual physical order and the literal cut d throughout the four-independent-gap descending chamber. -/
import D5.S3.Combinatorics.Circle.FourNegative.Descending.Banks

/-! A common physical permutation and its fresh ear at the literal cut d. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.Descending
open SourceWidth PeriodicShortening RunFirstEarTransport
open private size seed sourceMod base newBase charge chainLength chainStart nextBase nextNewBase
  oldValue newValue negatives chain_values source_signs source_totals new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private four_perm four_strip
  from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private reserve_bounds from D5.S3.Combinatorics.Circle.FourNegative.Descending.Arithmetic
open private bank shift mem_shift selected selected_good remainder_eq image_range first_card selected_mass
  from D5.S3.Combinatorics.Circle.FourNegative.Descending.Banks

private theorem half_power (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ)^n = 2*2^(n-1) := by
  conv_lhs => rw [show n = (n-1)+1 by omega,pow_succ]
  ring

set_option maxHeartbeats 1800000 in
/-- The same old physical permutation works in both changing moduli, with the fresh
label inserted after exactly d old labels, for every 2≤d<c≤b<a. -/
theorem actualSource_descending_joint_lift (a b c d : ℕ)
    (hd : 2 ≤ d) (hdc : d < c) (hcb : c ≤ b) (hba : b < a) :
    ∃ sigma : List (Fin (a+b+c+d)),
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma d) := by
  classical
  let k := a+b+c+d
  let s := 1+2^a+2^(a+b)+2^(a+b+c)
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let t : ℤ := 2^d
  let D := 1+y+y*z
  let A := x*D+1
  let B := t*(1+x+x*y)+1
  let L := t*z*(1+x)+1+z
  let M := t*y*z+D
  let J := 2*M-D
  let N := sourceMod a b c d
  let f := oldValue a b c d
  let g := newValue a b c d
  let h : ℤ := 2^(a-d-2)
  let u : ℤ := 2^(a-c-1)
  let v : ℤ := 2^(a-b-1)
  have hbase : base a b c d = ![A,B,L,M] := by
    funext r; fin_cases r <;> dsimp [base,A,B,L,M,D,x,y,z,t] <;> ring
  have hnewbase : newBase a b c d = ![2*A,2*B-1,2*L-1-z,J] := by
    funext r; fin_cases r <;> dsimp [newBase,charge,J]
    all_goals rw [hbase] <;> dsimp <;> ring
  have hseed : (s : ℤ) = A := by
    dsimp [s,A,D,x,y,z]
    push_cast
    simp only [pow_add]
    ring
  have hN : N = x*y*z*t-1 := rfl
  have hmod : modulus k = N := by dsimp [k,N,sourceMod,modulus]; ring
  have hmod' : modulus (k+1) = 2*N+1 := by dsimp [k,N,sourceMod,modulus]; ring
  have ht : 4 ≤ t := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hd
    norm_num at hh
    exact hh
  have hz : 2*t ≤ z := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega : d+1 ≤ c)
    simpa [t,z,pow_succ,mul_comm] using hh
  have hy : z ≤ y := pow_le_pow_right₀ (by norm_num) hcb
  have hx : 2*y ≤ x := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega : b+1 ≤ a)
    simpa [x,y,pow_succ,mul_comm] using hh
  have ex : 4*t*h=x := by
    calc
      4*t*h = (2 : ℤ)^(d+(a-d-2)+2) := by dsimp [t,h]; simp only [pow_add]; norm_num; ring
      _ = x := by dsimp [x]; congr 1; omega
  have eu : 2*z*u=x := by
    calc
      2*z*u = (2 : ℤ)^(c+(a-c-1)+1) := by dsimp [z,u]; simp only [pow_add]; norm_num; ring
      _ = x := by dsimp [x]; congr 1; omega
  have ev : 2*y*v=x := by
    calc
      2*y*v = (2 : ℤ)^(b+(a-b-1)+1) := by dsimp [y,v]; simp only [pow_add]; norm_num; ring
      _ = x := by dsimp [x]; congr 1; omega
  have hh : 1 ≤ h := by dsimp [h]; exact_mod_cast Nat.one_le_two_pow
  have hu : 1 ≤ u := by dsimp [u]; exact_mod_cast Nat.one_le_two_pow
  have hv : 1 ≤ v := by dsimp [v]; exact_mod_cast Nat.one_le_two_pow
  have bounds := reserve_bounds x y z t h u v ht hz hy hx hh hu hv ex eu ev
  change 0 ≤ A-3*h*M ∧ 0 ≤ B-u*M ∧ 0 ≤ L-v*M ∧
    0 ≤ 2*(3*h)*J-3*A-1 ∧ 0 ≤ u*J-B ∧ 0 ≤ 2*v*J-(2*L-1-z)-1 ∧
    0 ≤ 2*A-3*h*J ∧ 0 ≤ (2*B-1)-u*J ∧ 0 ≤ (2*L-1-z)-v*J ∧
    0 ≤ 2*(3*h)*M-A-1 ∧ 0 ≤ 2*u*M-B-1 ∧ 0 ≤ 2*v*M-L-1 at bounds
  obtain ⟨s0,s1,s2,t0,t1,t2,k0,k1,k2,o0,o1,o2⟩ := bounds
  have tab := chain_values a b c d (by omega) (by omega) (by omega) hd
  have positives (r : Fin 4) (i : ℕ) (hi : i+1 < chainLength a b c d r) :
      f (chainStart b c d r+i) = (2 : ℤ)^i*base a b c d r ∧
      g (chainStart b c d r+i) = (2 : ℤ)^i*newBase a b c d r := by
    exact ⟨by simpa only [if_pos hi] using tab.2.1 r i (by omega),
      by simpa only [if_pos hi] using tab.2.2.1 r i (by omega)⟩
  have mf := selected_mass a b c d hd hdc hcb hba f A B M
    (fun i hi => by simpa [chainStart,hbase] using (positives 0 i (by dsimp [chainLength]; omega)).1)
    (fun i hi => by simpa [chainStart,hbase] using (positives 1 i (by dsimp [chainLength]; omega)).1)
    (fun i hi => by simpa [chainStart,hbase] using (positives 3 i (by dsimp [chainLength]; omega)).1)
  have mg := selected_mass a b c d hd hdc hcb hba g (2*A) (2*B-1) J
    (fun i hi => by simpa [chainStart,hnewbase] using (positives 0 i (by dsimp [chainLength]; omega)).2)
    (fun i hi => by simpa [chainStart,hnewbase] using (positives 1 i (by dsimp [chainLength]; omega)).2)
    (fun i hi => by simpa [chainStart,hnewbase] using (positives 3 i (by dsimp [chainLength]; omega)).2)
  let P := selected a b c d 0
  let Q := selected a b c d 1
  let R := selected a b c d 2
  let nx := k-1
  let nu := d-1
  let nv := d+c-1
  let nw := d+c+b-1
  let G := Finset.range k \ (P ∪ Q ∪ R ∪ {nx,nu,nv,nw})
  let post := nx :: Q.toList ++ nu :: R.toList ++ nv :: G.toList ++ [nw]
  let word := P.toList ++ post
  have good := selected_good a b c d hd hdc hcb hba
  have hp := four_perm k nx nu nv nw P Q R (good.1 0) (good.1 1) (good.1 2)
    (good.2 0 1 (by decide)) (good.2 0 2 (by decide)) (good.2 1 2 (by decide))
    (by simp [nx,nu,nv,nw,k]; omega)
    (by intro i hi; simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl <;> dsimp [nx,nu,nv,nw,k] <;> omega)
  have hp : word.Perm (List.range k) := by
    simpa only [word,post,G,List.append_assoc,List.cons_append,List.nil_append] using hp
  have allpos (i : ℕ) (hi : i < k) (hn : i ≠ nx ∧ i ≠ nu ∧ i ≠ nv ∧ i ≠ nw) :
      0 ≤ f i ∧ 0 ≤ g i := by
    have hs := source_signs a b c d (by omega) (by omega) (by omega) hd i hi
    have hnot : i ∉ negatives a b c d := by simp [negatives,size,nx,nu,nv,nw,k] at *; tauto
    rw [if_neg hnot] at hs
    exact ⟨hs.1.le,hs.2.le⟩
  have pos (j : Fin 3) (i : ℕ) (hi : i ∈ (selected a b c d j).toList) : 0 ≤ f i ∧ 0 ≤ g i := by
    have hg := good.1 j i (Finset.mem_toList.mp hi)
    exact allpos i hg.1 hg.2
  have Gform : G = shift (d+c) (Finset.range (b-1)) ∪
      shift (d+c+b) (bank a (a-d-2) (a-c-1) (a-b-1) 3) :=
    remainder_eq a b c d hd hdc hcb hba
  have posG (i : ℕ) (hi : i ∈ G.toList) : 0 ≤ f i ∧ 0 ≤ g i := by
    have hg := Finset.mem_toList.mp hi
    rw [Gform] at hg
    change i ∈ shift (d+c) (Finset.range (b-1)) ∪
      shift (d+c+b) (Finset.range (a-b-1)) at hg
    simp only [shift,image_range,Finset.mem_union,Finset.mem_Ico] at hg
    rcases hg with hg | hg
    all_goals apply allpos i
    all_goals dsimp [k,nx,nu,nv,nw] <;> omega
  have totals := source_totals a b c d (by omega) (by omega) (by omega) hd
  have hfzero : (word.map f).sum = 0 := (hp.map f).sum_eq.trans totals.1
  have hear : g k = A := by simpa [k,size,hbase] using tab.2.2.2
  have hgzero : A+(word.map g).sum = 0 := by
    have he := (hp.map g).sum_eq.trans totals.2.1
    rw [hbase] at he
    dsimp at he
    omega
  have hxhalf : x=2*(2 : ℤ)^(a-1) := half_power a (by omega)
  have hthalf : t=2*(2 : ℤ)^(d-1) := half_power d (by omega)
  have hzhalf : z=2*(2 : ℤ)^(c-1) := half_power c (by omega)
  have terminal (r : Fin 4) :
      f (chainStart b c d r+(chainLength a b c d r-1)) = -(N-nextBase a b c d r)/2 ∧
      g (chainStart b c d r+(chainLength a b c d r-1)) = -((2*N+1)-nextNewBase a b c d r)/2 := by
    have hl : 2 ≤ chainLength a b c d r := by fin_cases r <;> dsimp [chainLength] <;> omega
    exact ⟨by simpa only [if_neg (by omega : ¬chainLength a b c d r-1+1 < chainLength a b c d r)] using tab.2.1 r (chainLength a b c d r-1) (by omega),
      by simpa only [if_neg (by omega : ¬chainLength a b c d r-1+1 < chainLength a b c d r)] using tab.2.2.1 r (chainLength a b c d r-1) (by omega)⟩
  have nt0 := terminal 3
  have nt1 := terminal 0
  have nt2 := terminal 1
  have nt3 := terminal 2
  simp only [chainStart,chainLength,nextBase,nextNewBase,hbase,hnewbase,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,zero_add] at nt0 nt1 nt2 nt3
  have en0 : d+c+b+(a-1)=nx := by dsimp [nx,k]; omega
  have en1 : d+(c-1)=nv := by dsimp [nv]; omega
  have en2 : d+c+(b-1)=nw := by dsimp [nw]; omega
  rw [en0] at nt0
  rw [en1] at nt2
  rw [en2] at nt3
  have nf0 : 2*f nx=A-N := by
    have he : A-N=2*((2 : ℤ)^(a-1)*(D-y*z*t)+1) := by dsimp [A]; rw [hN,hxhalf]; ring
    rw [nt0.1]; omega
  have ng0 : 2*g nx=A-(2*N+1) := by
    have he : A-(2*N+1)=2*((2 : ℤ)^(a-1)*(D-2*y*z*t)+1) := by dsimp [A]; rw [hN,hxhalf]; ring
    rw [nt0.2]; omega
  have nf1 : 2*f nu=B-N := by
    have he : B-N=2*((2 : ℤ)^(d-1)*(1+x+x*y-x*y*z)+1) := by dsimp [B]; rw [hN,hthalf]; ring
    rw [nt1.1]; change 2*(-(N-B)/2)=B-N; omega
  have ng1 : 2*g nu=(2*B-1)-(2*N+1) := by rw [nt1.2]; omega
  have nf2 : 2*f nv=L-N := by
    have he : L-N=2*((2 : ℤ)^(c-1)*(t*(1+x)-x*y*t+1)+1) := by dsimp [L]; rw [hN,hzhalf]; ring
    rw [nt2.1]; omega
  have ng2 : 2*g nv=(2*L-1-z)-(2*N+1) := by
    have he : (2*L-1-z)-(2*N+1)=2*(L-N-1-(2 : ℤ)^(c-1)) := by rw [hzhalf]; ring
    rw [nt2.2]; omega
  have relx : x*M=N+A := by dsimp [M,A,D]; rw [hN]; ring
  have relt : t*A=N+B := by dsimp [A,B,D]; rw [hN]; ring
  have relz : z*B=N+L := by dsimp [B,L]; rw [hN]; ring
  have sumlist (S : Finset ℕ) (f : ℕ → ℤ) : (S.toList.map f).sum=∑ i ∈ S,f i := by
    change ((S.toList : Multiset ℕ).map f).sum=_
    simp
  simp only [←sumlist] at mf mg
  have m0 : 2*(P.toList.map f).sum=(x-6*h)*M := by rw [hxhalf]; dsimp [P,h]; nlinarith only [mf.1]
  have m1 : 2*(Q.toList.map f).sum=(t-2)*A+2*(3*h-u)*M := by rw [hthalf]; dsimp [Q,h,u]; nlinarith only [mf.2.1]
  have m2 : 2*(R.toList.map f).sum=(z-2)*B+2*(u-v)*M := by rw [hzhalf]; dsimp [R,u,v]; nlinarith only [mf.2.2]
  have j0 : 2*(P.toList.map g).sum=(x-6*h)*J := by rw [hxhalf]; dsimp [P,h]; nlinarith only [mg.1]
  have j1 : 2*(Q.toList.map g).sum=(t-2)*(2*A)+2*(3*h-u)*J := by rw [hthalf]; dsimp [Q,h,u]; nlinarith only [mg.2.1]
  have j2 : 2*(R.toList.map g).sum=(z-2)*(2*B-1)+2*(u-v)*J := by rw [hzhalf]; dsimp [R,u,v]; nlinarith only [mg.2.2]
  have hNodd : N%2=1 := by
    have he : N=2*(x*y*z*(2 : ℤ)^(d-1)-1)+1 := by rw [hN,hthalf]; ring
    omega
  have hN0 : 0 ≤ N := by have hb := tab.1 0; change 1 ≤ base a b c d 0 ∧ base a b c d 0 < N at hb; omega
  have lastold : 0 ≤ -f nw ∧ -f nw ≤ N/2 := by
    have hb := tab.1 3
    rw [hbase] at hb
    dsimp at hb
    rw [nt3.1]
    omega
  have lastnew : 0 ≤ -g nw ∧ -g nw ≤ N := by
    have hb := new_base_bounds a b c d (by omega) (by omega) (by omega) hd 3
    rw [hnewbase] at hb
    dsimp at hb
    rw [nt3.2]
    omega
  have oldstrip : InStrip f (N/2) 0 word := by
    suffices hs : InStrip f (N/2) 0
        (P.toList ++ nx :: Q.toList ++ nu :: R.toList ++ nv :: G.toList ++ [nw]) by
      simpa only [word,post,List.append_assoc,List.cons_append,List.nil_append] using hs
    apply four_strip f P.toList Q.toList R.toList G.toList nx nu nv nw (N/2) 0
      (fun i hi => (pos 0 i hi).1) (fun i hi => (pos 1 i hi).1)
      (fun i hi => (pos 2 i hi).1) (fun i hi => (posG i hi).1) (by omega)
    · constructor <;> nlinarith only [m0,nf0,relx,s0,o0,hNodd,Int.emod_add_mul_ediv N 2]
    · constructor <;> nlinarith only [m0,m1,nf0,nf1,relx,relt,s1,o1,hNodd,Int.emod_add_mul_ediv N 2]
    · constructor <;> nlinarith only [m0,m1,m2,nf0,nf1,nf2,relx,relt,relz,s2,o2,hNodd,Int.emod_add_mul_ediv N 2]
    · exact lastold
    · simpa only [word,post,List.append_assoc,List.cons_append,List.nil_append,zero_add] using hfzero
  have newstrip : InStrip g N 0 (P.toList ++ k :: post) := by
    have hm0 : ((P.toList ++ [k]).map g).sum=(P.toList.map g).sum+A := by simp [hear]
    have htzero : ((P.toList ++ [k] ++ post).map g).sum=0 := by
      simpa [word,List.map_append,List.sum_append,hear,add_assoc,add_comm,add_left_comm] using hgzero
    have hrelx : x*J=2*N+1+A := by dsimp [J,M,D,A]; rw [hN]; ring
    have hrelt : t*(2*A)=2*N+1+(2*B-1) := by nlinarith only [relt]
    have hrelz : z*(2*B-1)=2*N+1+(2*L-1-z) := by nlinarith only [relz]
    have hs := four_strip g (P.toList ++ [k]) Q.toList R.toList G.toList nx nu nv nw N 0
      (by intro i hi; rcases List.mem_append.mp hi with hi|hi
          · exact (pos 0 i hi).2
          · have he := List.mem_singleton.mp hi
            subst i
            rw [hear]
            have hb := tab.1 0
            rw [hbase] at hb
            change 1 ≤ A ∧ A < N at hb
            omega)
      (fun i hi => (pos 1 i hi).2) (fun i hi => (pos 2 i hi).2)
      (fun i hi => (posG i hi).2) (by omega)
      (by rw [hm0]; constructor <;> nlinarith only [j0,ng0,hrelx,k0,t0])
      (by rw [hm0]; constructor <;> nlinarith only [j0,j1,ng0,ng1,hrelx,hrelt,k1,t1])
      (by rw [hm0]; constructor <;> nlinarith only [j0,j1,j2,ng0,ng1,ng2,hrelx,hrelt,hrelz,k2,t2])
      lastnew (by simpa only [post,List.append_assoc,List.cons_append,
        List.nil_append,zero_add] using htzero)
    simpa only [post,List.append_assoc,List.singleton_append,List.cons_append,
      List.nil_append] using hs
  have plen : P.toList.length=d := by simpa [P] using first_card a b c d hd hdc hcb hba
  have hpnew : (P.toList ++ k :: post).Perm (List.range (k+1)) := by
    have hh : (P.toList ++ k :: post).Perm (word ++ [k]) := by
      simpa [word,List.append_assoc] using (List.perm_append_singleton k post).symm.append_left P.toList
    exact hh.trans (by simpa [List.range_succ] using hp.append_right [k])
  have fform : f = fun i => centered N ((2 : ℤ)^i*A) := by
    funext i
    change centered N ((2 : ℤ)^i*base a b c d 0) = _
    rw [hbase]
    rfl
  have gform : g = fun i => centered (2*N+1) ((2 : ℤ)^i*(2*A)) := by
    funext i
    change centered (2*N+1) ((2 : ℤ)^i*(2*base a b c d 0)) = _
    rw [hbase]
    rfl
  refine ⟨word.map (label k (by dsimp [k]; omega)),?_,?_⟩
  · apply lift_order k s (by dsimp [k]; omega) word hp
    · simpa only [fform,hmod,hseed] using oldstrip
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero k s (by dsimp [k]; omega)
  · have marked := marked_word k d (by dsimp [k]; omega) P.toList post plen hp
    rw [marked]
    apply lift_order (k+1) (2*s) (by omega) (P.toList ++ k :: post) hpnew
    · have hseed' : ((2*s : ℕ) : ℤ)=2*A := by push_cast; rw [hseed]
      simpa only [gform,hmod',hseed',show (2*N+1)/2=N by omega] using newstrip
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*s) (by dsimp [k]; omega)

end D5.S3.Combinatorics.Circle.FourNegative.Descending
