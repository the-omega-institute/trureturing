/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Certificate
   generality: I
   mirror-B: none(waiver:private-consumed-certificate-existence)
   mirror-E: none(waiver:private-consumed-certificate-existence)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Unconditional exact PacketNormalForm certificate existence throughout the middle-gap cone. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.PhysicalBanks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Arithmetic

/-! Private consumed arithmetic and physical construction for the middle-gap joint lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private Values values route_windows
  Values.z Values.x Values.y Values.H Values.A Values.B Values.L Values.K
  Values.SU Values.SV Values.SW Values.alpha Values.gamma Values.D Values.Dp Values.E Values.F
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Arithmetic
open private pieces banks terminals word banks_inventory banks_good banks_masses
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.PhysicalBanks
open private sourceMod base newBase charge nextBase nextNewBase oldValue newValue chain_values new_base_bounds weightedMask packet_masses from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source (size chainLength chainStart negatives)
open private oldMass newMass
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private DataCertificate DataCertificate.mk orderedPackets finiteChecks finiteEarChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure (blocksWord)
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private half_power gap_power
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Arithmetic

set_option maxHeartbeats 2400000 in
private theorem certificate_exists (a b c d : ℕ) (hd : 2≤d) (hdc : d<c)
    (hca : c<a) (hab : a≤b) : Nonempty (Certificate a b c d) := by
  classical
  let w : ℤ := 2^d
  let h : ℤ := 2^(c-d-1)
  let v : ℤ := 2^(a-c-1)
  let q : ℤ := 2^(b-a)
  let s : ℤ := 2^(a-d-2)
  let V := values w h v q
  let first := decide ((Values.gamma V)≤(Values.Dp V))
  let r := if first then 2*s else 3*s
  have hw : 4≤w := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hd
    norm_num at hh
    exact hh
  have hh : 1≤h := one_le_pow₀ (by norm_num)
  have hv : 1≤v := one_le_pow₀ (by norm_num)
  have hq : 1≤q := one_le_pow₀ (by norm_num)
  have hs : s=h*v := by
    dsimp [s,h,v]
    rw [←pow_add]
    congr 1
    omega
  have hz : (2:ℤ)^c=2*w*h := by
    simpa only [pow_one] using gap_power c d 1 (by omega)
  have hx : (2:ℤ)^a=4*w*h*v := by
    have he := gap_power a c 1 (by omega)
    rw [hz] at he
    dsimp [v]
    nlinarith only [he]
  have hy : (2:ℤ)^b=q*(2:ℤ)^a := by
    dsimp [q]
    rw [←pow_add]
    congr 1
    omega
  have hbase : base a b c d=![(Values.A V),(Values.B V),(Values.L V),(Values.K V)] := by
    funext i
    fin_cases i <;> dsimp [base,V,values]
    all_goals try simp only [hy,hx,hz]
    all_goals dsimp [w];ring
  have hnewbase : newBase a b c d=![2*(Values.A V),(Values.SU V),(Values.SV V),(Values.SW V)] := by
    funext i
    fin_cases i <;> dsimp [newBase,charge]
    all_goals rw [hbase]
    all_goals dsimp [V,values]
    all_goals try simp only [hy,hx,hz]
    all_goals ring
  let f := oldValue a b c d
  let g := newValue a b c d
  let N := sourceMod a b c d
  let P := banks a b c d first
  let T := terminals a b c d
  let B := fun j : Fin 4 => (P j).toFinset
  let ps : List (Finset ℕ × ℕ) := [(B 0,T 0),(B 1,T 1),(B 2,T 2),(B 3,T 3)]
  have hp := banks_inventory a b c d hd hdc hca hab first
  have hn (j : Fin 4) : (P j).Nodup := by
    have ht := hp.nodup_iff.mpr List.nodup_range
    simp only [word,List.nodup_append] at ht
    fin_cases j <;> tauto
  have hperm (j : Fin 4) : (B j).toList.Perm (P j) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (hn j)).mpr
    intro i
    simp [B]
  have hm (side : Bool) (j : Fin 4) :
      (if side then newMass a b c d (B j) else oldMass a b c d (B j)) =
      ((P j).map (if side then g else f)).sum := by
    have good : ∀ i∈B j, i<size a b c d ∧ i∉negatives a b c d := by
      intro i hi
      exact banks_good a b c d hd hdc hca hab first j i (List.mem_toFinset.mp hi)
    have mm := packet_masses a b c d (by omega) (by omega) (by omega) hd (B j) good
    have tosum (ff : ℕ→ℤ) : (∑ i∈B j,ff i)=((P j).map ff).sum := by
      exact List.sum_toFinset ff (hn j)
    cases side
    · exact mm.1.symm.trans (tosum f)
    · exact mm.2.symm.trans (tosum g)
  have tab := chain_values a b c d (by omega) (by omega) (by omega) hd
  have series (side : Bool) (j : Fin 4) (i : ℕ) (hi : i<chainLength a b c d j-1) :
      (if side then g else f) (chainStart b c d j+i)=
        2^i*(if side then newBase a b c d else base a b c d) j := by
    cases side
    · exact (tab.2.1 j i (by omega)).trans (if_pos (by omega))
    · exact (tab.2.2.1 j i (by omega)).trans (if_pos (by omega))
  have mo := banks_masses a b c d hd hdc hca hab first f (base a b c d) (series false)
  have mg := banks_masses a b c d hd hdc hca hab first g (newBase a b c d) (series true)
  rw [hbase] at mo
  rw [hnewbase] at mg
  dsimp only at mo mg
  simp only [sub_add_cancel,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three] at mo mg
  change ((P 0).map f).sum=((2:ℤ)^(b-1)-q)*(Values.L V) ∧
    ((P 1).map f).sum=((2:ℤ)^(a-1)-r)*(Values.K V) ∧
    ((P 2).map f).sum=((2:ℤ)^(d-1)-1)*(Values.A V)+(r-v)*(Values.K V) ∧
    ((P 3).map f).sum=((2:ℤ)^(c-1)-1)*(Values.B V)+(q-1)*(Values.L V)+(v-1)*(Values.K V) at mo
  change ((P 0).map g).sum=((2:ℤ)^(b-1)-q)*(Values.SV V) ∧
    ((P 1).map g).sum=((2:ℤ)^(a-1)-r)*(Values.SW V) ∧
    ((P 2).map g).sum=((2:ℤ)^(d-1)-1)*(2*(Values.A V))+(r-v)*(Values.SW V) ∧
    ((P 3).map g).sum=((2:ℤ)^(c-1)-1)*(Values.SU V)+(q-1)*(Values.SV V)+(v-1)*(Values.SW V) at mg
  have native (j : Fin 4) := native_masses a b c d (by omega) (by omega) (by omega) hd j
  have n0 := native 2
  have n1 := native 3
  have n2 := native 0
  have n3 := native 1
  have hcast (n : ℕ) : ((2^(n-1)-1:ℕ):ℤ)=(2:ℤ)^(n-1)-1 := by
    rw [Nat.cast_sub (by have := Nat.two_pow_pos (n-1);omega)]
    norm_cast
  simp only [chainLength,chainStart,nextBase,nextNewBase,hbase,hnewbase,hcast,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_add] at n0 n1 n2 n3
  have e0 : d+c+(b-1)=T 0 := by dsimp [T,terminals];omega
  have e1 : d+c+b+(a-1)=T 1 := by dsimp [T,terminals];omega
  have e2 : d-1=T 2 := rfl
  have e3 : d+(c-1)=T 3 := by dsimp [T,terminals];omega
  rw [e0] at n0
  rw [e1] at n1
  rw [e3] at n3
  change ((2:ℤ)^(b-1)-1)*(Values.L V)+f (T 0)=(Values.K V)-(Values.L V) ∧
    ((2:ℤ)^(b-1)-1)*(Values.SV V)+g (T 0)=(Values.SW V)-(Values.SV V) ∧
    2*f (T 0)=(Values.K V)-N ∧ 2*g (T 0)=(Values.SW V)-(2*N+1) at n0
  change ((2:ℤ)^(a-1)-1)*(Values.K V)+f (T 1)=(Values.A V)-(Values.K V) ∧
    ((2:ℤ)^(a-1)-1)*(Values.SW V)+g (T 1)=(Values.A V)-(Values.SW V) ∧
    2*f (T 1)=(Values.A V)-N ∧ 2*g (T 1)=(Values.A V)-(2*N+1) at n1
  change ((2:ℤ)^(d-1)-1)*(Values.A V)+f (T 2)=(Values.B V)-(Values.A V) ∧
    ((2:ℤ)^(d-1)-1)*((2*Values.A V))+g (T 2)=(Values.SU V)-((2*Values.A V)) ∧
    2*f (T 2)=(Values.B V)-N ∧ 2*g (T 2)=(Values.SU V)-(2*N+1) at n2
  change ((2:ℤ)^(c-1)-1)*(Values.B V)+f (T 3)=(Values.L V)-(Values.B V) ∧
    ((2:ℤ)^(c-1)-1)*(Values.SU V)+g (T 3)=(Values.SV V)-(Values.SU V) ∧
    2*f (T 3)=(Values.L V)-N ∧ 2*g (T 3)=(Values.SV V)-(2*N+1) at n3
  let M := fun j : Fin 4 => oldMass a b c d (B j)
  let G := fun j : Fin 4 => newMass a b c d (B j)
  have m0 : M 0+f (T 0)=(Values.D V) := by
    rw [show M 0=((P 0).map f).sum from hm false 0,mo.1]
    have he : (Values.D V)=(Values.K V)-q*(Values.L V) := rfl
    rw [he]
    nlinarith only [n0.1]
  have m1 : M 1+f (T 1)=(Values.A V)-r*(Values.K V) := by
    rw [show M 1=((P 1).map f).sum from hm false 1,mo.2.1]
    nlinarith only [n1.1]
  have m2 : M 2+f (T 2)=(Values.B V)-(Values.A V)+(r-v)*(Values.K V) := by
    rw [show M 2=((P 2).map f).sum from hm false 2,mo.2.2.1]
    nlinarith only [n2.1]
  have m3 : M 3+f (T 3)=(Values.L V)-(Values.B V)+(q-1)*(Values.L V)+(v-1)*(Values.K V) := by
    rw [show M 3=((P 3).map f).sum from hm false 3,mo.2.2.2]
    nlinarith only [n3.1]
  have g0 : G 0+g (T 0)=(Values.Dp V) := by
    rw [show G 0=((P 0).map g).sum from hm true 0,mg.1]
    have he : (Values.Dp V)=(Values.SW V)-q*(Values.SV V) := rfl
    rw [he]
    nlinarith only [n0.2.1]
  have g1 : G 1+g (T 1)=(Values.A V)-r*(Values.SW V) := by
    rw [show G 1=((P 1).map g).sum from hm true 1,mg.2.1]
    nlinarith only [n1.2.1]
  have g2 : G 2+g (T 2)=(Values.SU V)-2*(Values.A V)+(r-v)*(Values.SW V) := by
    rw [show G 2=((P 2).map g).sum from hm true 2,mg.2.2.1]
    nlinarith only [n2.2.1]
  have g3 : G 3+g (T 3)=(Values.SV V)-(Values.SU V)+(q-1)*(Values.SV V)+(v-1)*(Values.SW V) := by
    rw [show G 3=((P 3).map g).sum from hm true 3,mg.2.2.2]
    nlinarith only [n3.2.1]
  have eold : M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2)=(Values.E V) := by
    have he : (Values.E V)=(Values.B V)+(Values.D V)-v*(Values.K V) := rfl
    rw [he]
    nlinarith only [m0,m1,m2]
  have enew : G 0+g (T 0)+G 1+g (T 1)+G 2+g (T 2)+(Values.A V)=(Values.F V) := by
    have he : (Values.F V)=(Values.SU V)+(Values.Dp V)-v*(Values.SW V) := rfl
    rw [he]
    nlinarith only [g0,g1,g2]
  have zold : M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2)+M 3+f (T 3)=0 := by
    have he : (Values.D V)=(Values.K V)-q*(Values.L V) := rfl
    nlinarith only [he,m0,m1,m2,m3]
  have znew : G 0+g (T 0)+G 1+g (T 1)+G 2+g (T 2)+G 3+g (T 3)+(Values.A V)=0 := by
    have he : (Values.Dp V)=(Values.SW V)-q*(Values.SV V) := rfl
    nlinarith only [he,g0,g1,g2,g3]
  obtain ⟨w0,w0n,w1,w1n,w2,w2n⟩ := route_windows w h v q hw hh hv hq
  have rdef : r=(if (Values.gamma V)≤(Values.Dp V) then 2*h*v else 3*h*v) := by simp [r,first,hs,mul_assoc]
  dsimp only [V] at rdef
  rw [←rdef] at w1 w1n
  change 0≤Values.D V ∧ 2*Values.D V≤Values.K V-1 at w0
  change 0≤Values.Dp V ∧ 2*Values.Dp V≤Values.SW V-1 at w0n
  change 0≤Values.D V+Values.A V-r*Values.K V ∧
    2*(Values.D V+Values.A V-r*Values.K V)≤Values.A V-1 at w1
  change 0≤Values.Dp V+Values.A V+(if Values.gamma V≤Values.Dp V then 0 else Values.A V)-r*Values.SW V ∧
    2*(Values.Dp V+Values.A V+(if Values.gamma V≤Values.Dp V then 0 else Values.A V)-r*Values.SW V)≤Values.A V-1 at w1n
  change 0≤Values.E V ∧ 2*Values.E V≤Values.B V-1 at w2
  change 0≤Values.F V ∧ 2*Values.F V≤Values.SU V-1 at w2n
  have win (e S z C : ℤ) (he : 0≤e ∧ 2*e≤S-1)
      (hz : 2*z=S-(2*C+1)) : 0≤e ∧ e-z≤C := by omega
  have hN : 2*(N/2)+1=N := by
    have hn : N=2*((2:ℤ)^a*2^b*2^c*2^(d-1))-1 := by
      dsimp [N,sourceMod];rw [half_power d (by omega)];ring
    omega
  have lastO : 0≤-f (T 3) ∧ -f (T 3)≤N/2 := by
    have hh := tab.1 2
    rw [hbase] at hh
    change 1 ≤ Values.L V ∧ Values.L V < N at hh
    have hz := n3.2.2.1
    change 2*f (T 3)=Values.L V-N at hz
    omega
  have lastN : 0≤-g (T 3) ∧ -g (T 3)≤N := by
    have hb := new_base_bounds a b c d (by omega) (by omega) (by omega) hd 2
    rw [hnewbase] at hb
    change 1 ≤ Values.SV V ∧ Values.SV V < 2*N+1 at hb
    have hz := n3.2.2.2
    change 2*g (T 3)=Values.SV V-(2*N+1) at hz
    omega
  refine ⟨DataCertificate.mk ps ?_ ⟨if first then 2 else 1,by cases first <;> decide⟩ ?_ ?_ ?_ ?_⟩
  · change [T 0,T 1,T 2,T 3].Perm (negatives a b c d)
    have he : negatives a b c d=[T 2,T 3,T 0,T 1] := by
      dsimp [negatives,T,terminals,size]
    rw [he]
    change ([T 0,T 1]++[T 2,T 3]).Perm ([T 2,T 3]++[T 0,T 1])
    exact List.perm_append_comm
  · intro pkt hpkt i hi
    simp only [ps,List.mem_cons,List.mem_nil_iff,or_false] at hpkt
    rcases hpkt with rfl|rfl|rfl|rfl
    all_goals exact banks_good a b c d hd hdc hca hab first _ i (List.mem_toFinset.mp hi)
  · have he : (blocksWord (orderedPackets ps)).Perm (word a b c d first) := by
      dsimp [ps,orderedPackets,blocksWord,word]
      simpa only [List.map_cons,List.map_nil,blocksWord,
        List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
        (((((((hperm 0).append_right [T 0]).append (hperm 1)).append_right [T 1]).append
          (hperm 2)).append_right [T 2]).append (hperm 3)).append_right [T 3]
    exact Multiset.coe_eq_coe.mpr (he.trans hp)
  · change finiteChecks (oldMass a b c d) f (N/2) 0 ps
    simp only [ps,finiteChecks,zero_add]
    change 0≤M 0+f (T 0) ∧ M 0≤N/2 ∧
      0≤M 0+f (T 0)+M 1+f (T 1) ∧ M 0+f (T 0)+M 1≤N/2 ∧
      0≤M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2) ∧
      M 0+f (T 0)+M 1+f (T 1)+M 2≤N/2 ∧
      0≤M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2)+M 3+f (T 3) ∧
      M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2)+M 3≤N/2 ∧ True
    have k0 := win (Values.D V) (Values.K V) (f (T 0)) (N/2) w0 (by have hz := n0.2.2.1;omega)
    have k1 := win ((Values.D V)+(Values.A V)-r*(Values.K V)) (Values.A V) (f (T 1)) (N/2) w1
      (by have hz := n1.2.2.1;omega)
    have k2 := win (Values.E V) (Values.B V) (f (T 2)) (N/2) w2 (by have hz := n2.2.2.1;omega)
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,trivial⟩ <;>
      nlinarith only [k0.1,k0.2,k1.1,k1.2,k2.1,k2.2,m0,m1,m2,eold,zold,lastO.2]
  · change finiteEarChecks (newMass a b c d) g N (base a b c d 0) 0
      (if first then (2:ℕ) else 1) ps
    rw [hbase]
    change finiteEarChecks (newMass a b c d) g N (Values.A V) 0
      (if first then (2:ℕ) else 1) ps
    have k0 := win (Values.Dp V) (Values.SW V) (g (T 0)) N w0n n0.2.2.2
    have k2 := win (Values.F V) (Values.SU V) (g (T 2)) N w2n n2.2.2.2
    by_cases he : (Values.gamma V)≤(Values.Dp V)
    all_goals have k1 := win _ (Values.A V) (g (T 1)) N w1n n1.2.2.2
    all_goals simp only [first,he,decide_true,decide_false,ite_true,ite_false,
      finiteEarChecks,finiteChecks,ps,zero_add] at *
    all_goals change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ True
    all_goals refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,trivial⟩ <;>
      nlinarith only [k0.1,k0.2,k1.1,k1.2,k2.1,k2.2,g0,g1,g2,enew,znew,lastN.2]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap
