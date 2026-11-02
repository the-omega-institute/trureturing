/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakSecondMaximum/BoundaryCertificates
   generality: I
   mirror-B: none(waiver:private-consumed-boundary-certificates)
   mirror-E: none(waiver:private-consumed-boundary-certificates)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Native physical certificates for equal and adjacent final gaps. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum.Boundaries
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum.BoundaryArithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private Values values
  Values.z Values.w Values.r Values.q Values.x Values.y Values.H Values.S
  Values.A Values.B Values.L Values.K Values.SU Values.SV Values.SW Values.D Values.Dp
  broadTerminals
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum.BroadData
open private boundaryBanks boundaryWord boundary_inventory boundary_good boundary_masses
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum.Boundaries
open private window adjacent_windows diagonal_windows
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum.BoundaryArithmetic
open private size sourceMod base newBase charge oldValue newValue negatives chainLength chainStart
  nextBase nextNewBase weightedMask packet_masses chain_values new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private oldMass newMass from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private DataCertificate DataCertificate.mk orderedPackets finiteChecks finiteEarChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

set_option maxHeartbeats 2400000 in
private theorem boundary_certificate (a b c d : ℕ) (hc : 2≤c) (hd : 2≤d)
    (hda : d<a) (hab : a≤b) (equal swap : Bool) (hswap : swap=true → equal=true)
    (hwindows :
      let t : ℤ := 2^(a-d-1)
      let V := values (2^c) (2^d) (2*t) (2^(b-a))
      let v := if equal then t else 2*t
      window (Values.D V) (Values.K V) ∧ window (Values.Dp V) (Values.SW V) ∧
      window ((Values.D V)+(Values.A V)-(if swap then 3*t else 2*t)*(Values.K V)+(if swap then (Values.A V) else 0)) (Values.A V) ∧
      window ((Values.Dp V)+(Values.A V)-(if swap then 3*t else 2*t)*(Values.SW V)+(if swap then 2*(Values.A V) else (Values.A V))) (Values.A V) ∧
      window ((Values.D V)+(Values.B V)-v*(Values.K V)) (Values.B V) ∧ window ((Values.Dp V)+(Values.SU V)-v*(Values.SW V)) (Values.SU V)) :
    Nonempty (Certificate a b c d) := by
  classical
  let t : ℤ := 2^(a-d-1)
  let q : ℤ := 2^(b-a)
  let V := values (2^c) (2^d) (2*t) q
  let r := if swap then 3*t else 2*t
  let v := if equal then t else 2*t
  let ell := if equal then (if swap then 2*t else t) else 0
  have hrl : r-ell=v := by
    cases equal <;> cases swap <;> simp_all [r,ell,v] <;> ring
  have hx : (2:ℤ)^a = (2*t)*2^d := by
    dsimp [t]
    rw [←pow_succ',←pow_add]
    congr 1
    omega
  have hy : (2:ℤ)^b = q*((2*t)*2^d) := by
    rw [←hx]
    dsimp [q]
    rw [←pow_add]
    congr 1
    omega
  have hbase : base a b c d = ![(Values.A V),(Values.B V),(Values.L V),(Values.K V)] := by
    funext i
    fin_cases i <;> dsimp [base,V,values]
    all_goals try rw [hx]
    all_goals try rw [hy]
    all_goals ring_nf
  have hnewbase : newBase a b c d = ![2*(Values.A V),(Values.SU V),(Values.SV V),(Values.SW V)] := by
    funext i
    fin_cases i <;> dsimp [newBase,charge,base,V,values]
    all_goals try rw [hx]
    all_goals try rw [hy]
    all_goals ring_nf
  let f := oldValue a b c d
  let g := newValue a b c d
  let N := sourceMod a b c d
  let P := boundaryBanks a b c d equal swap
  let T := broadTerminals a b c d
  let B := fun j : Fin 4 => (P j).toFinset
  let ps : List (Finset ℕ × ℕ) := [(B 0,T 0),(B 1,T 1),(B 2,T 2),(B 3,T 3)]
  have hp := boundary_inventory a b c d hc hd hda hab equal swap hswap
  have hn (j : Fin 4) : (P j).Nodup := by
    have ht := hp.nodup_iff.mpr List.nodup_range
    simp only [boundaryWord,List.nodup_append] at ht
    fin_cases j <;> tauto
  have hperm (j : Fin 4) : (B j).toList.Perm (P j) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (hn j)).mpr
    intro i
    simp [B]
  have good (j : Fin 4) (i : ℕ) (hi : i∈B j) :
      i<size a b c d ∧ i∉negatives a b c d :=
    boundary_good a b c d hc hd hda hab equal swap j i (List.mem_toFinset.mp hi)
  have hm (side : Bool) (j : Fin 4) :
      (if side then newMass a b c d (B j) else oldMass a b c d (B j)) =
      ((P j).map (if side then g else f)).sum := by
    have mm := packet_masses a b c d (by omega) (by omega) hc hd (B j) (good j)
    have tosum (ff : ℕ→ℤ) : (∑ i∈B j,ff i)=((P j).map ff).sum :=
      List.sum_toFinset ff (hn j)
    cases side
    · exact mm.1.symm.trans (tosum f)
    · exact mm.2.symm.trans (tosum g)
  have tab := chain_values a b c d (by omega) (by omega) hc hd
  have series (side : Bool) (j : Fin 4) (i : ℕ) (hi : i<chainLength a b c d j-1) :
      (if side then g else f) (chainStart b c d j+i)=
        2^i*(if side then newBase a b c d else base a b c d) j := by
    cases side
    · exact (tab.2.1 j i (by omega)).trans (if_pos (by omega))
    · exact (tab.2.2.1 j i (by omega)).trans (if_pos (by omega))
  have mo := boundary_masses a b c d hc hd hda hab equal swap hswap f (base a b c d) (series false)
  have mg := boundary_masses a b c d hc hd hda hab equal swap hswap g (newBase a b c d) (series true)
  rw [hbase] at mo
  rw [hnewbase] at mg
  change ((P 0).map f).sum=((2:ℤ)^(b-1)-q)*(Values.L V) ∧
    ((P 1).map f).sum=((2:ℤ)^(a-1)-r)*(Values.K V)+(if swap then (Values.A V) else 0) ∧
    ((P 2).map f).sum=((2:ℤ)^(d-1)-1-(if swap then 1 else 0))*(Values.A V)+ell*(Values.K V) ∧
    ((P 3).map f).sum=((2:ℤ)^(c-1)-1)*(Values.B V)+(q-1)*(Values.L V)+(v-1)*(Values.K V) at mo
  change ((P 0).map g).sum=((2:ℤ)^(b-1)-q)*(Values.SV V) ∧
    ((P 1).map g).sum=((2:ℤ)^(a-1)-r)*(Values.SW V)+(if swap then 2*(Values.A V) else 0) ∧
    ((P 2).map g).sum=((2:ℤ)^(d-1)-1-(if swap then 1 else 0))*(2*(Values.A V))+ell*(Values.SW V) ∧
    ((P 3).map g).sum=((2:ℤ)^(c-1)-1)*(Values.SU V)+(q-1)*(Values.SV V)+(v-1)*(Values.SW V) at mg
  have native (j : Fin 4) := native_masses a b c d (by omega) (by omega) hc hd j
  have n0 := native 2
  have n1 := native 3
  have n2 := native 0
  have n3 := native 1
  have hcast (n : ℕ) : ((2^(n-1)-1:ℕ):ℤ)=(2:ℤ)^(n-1)-1 := by
    rw [Nat.cast_sub (by have := Nat.two_pow_pos (n-1);omega)]
    norm_cast
  simp only [chainLength,chainStart,nextBase,nextNewBase,hbase,hnewbase,hcast,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_add] at n0 n1 n2 n3
  have e0 : d+c+(b-1)=T 0 := by dsimp [T,broadTerminals];omega
  have e1 : d+c+b+(a-1)=T 1 := by dsimp [T,broadTerminals];omega
  have e3 : d+(c-1)=T 3 := by dsimp [T,broadTerminals];omega
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
    ((2:ℤ)^(d-1)-1)*(2*(Values.A V))+g (T 2)=(Values.SU V)-2*(Values.A V) ∧
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
  have g0 : G 0+g (T 0)=(Values.Dp V) := by
    rw [show G 0=((P 0).map g).sum from hm true 0,mg.1]
    have he : (Values.Dp V)=(Values.SW V)-q*(Values.SV V) := rfl
    rw [he]
    nlinarith only [n0.2.1]
  have m1 : M 1+f (T 1)=(Values.A V)-r*(Values.K V)+(if swap then (Values.A V) else 0) := by
    rw [show M 1=((P 1).map f).sum from hm false 1,mo.2.1]
    nlinarith only [n1.1]
  have g1 : G 1+g (T 1)=(Values.A V)-r*(Values.SW V)+(if swap then 2*(Values.A V) else 0) := by
    rw [show G 1=((P 1).map g).sum from hm true 1,mg.2.1]
    nlinarith only [n1.2.1]
  have m2 : M 2+f (T 2)=(Values.B V)-(Values.A V)-(if swap then 1 else 0)*(Values.A V)+ell*(Values.K V) := by
    rw [show M 2=((P 2).map f).sum from hm false 2,mo.2.2.1]
    nlinarith only [n2.1]
  have g2 : G 2+g (T 2)=(Values.SU V)-2*(Values.A V)-(if swap then 1 else 0)*(2*(Values.A V))+ell*(Values.SW V) := by
    rw [show G 2=((P 2).map g).sum from hm true 2,mg.2.2.1]
    nlinarith only [n2.2.1]
  have m3 : M 3+f (T 3)=(Values.L V)-(Values.B V)+(q-1)*(Values.L V)+(v-1)*(Values.K V) := by
    rw [show M 3=((P 3).map f).sum from hm false 3,mo.2.2.2]
    nlinarith only [n3.1]
  have g3 : G 3+g (T 3)=(Values.SV V)-(Values.SU V)+(q-1)*(Values.SV V)+(v-1)*(Values.SW V) := by
    rw [show G 3=((P 3).map g).sum from hm true 3,mg.2.2.2]
    nlinarith only [n3.2.1]
  let earX := if swap then 0 else (Values.A V)
  let earU := if swap then (Values.A V) else 0
  have earSum : earX+earU=(Values.A V) := by cases swap <;> simp [earX,earU]
  have px : M 0+f (T 0)+M 1+f (T 1)=(Values.D V)+(Values.A V)-r*(Values.K V)+(if swap then (Values.A V) else 0) := by
    linarith only [m0,m1]
  have pxn : G 0+g (T 0)+G 1+earX+g (T 1)=
      (Values.Dp V)+(Values.A V)-r*(Values.SW V)+(if swap then 2*(Values.A V) else (Values.A V)) := by
    cases swap <;> simp only [Bool.false_eq_true,ite_true,ite_false,earX] at * <;> linarith only [g0,g1]
  have pu : M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2)=(Values.D V)+(Values.B V)-v*(Values.K V) := by
    have hh : (r-ell)*(Values.K V)=v*(Values.K V) := by rw [hrl]
    cases swap <;> simp only [Bool.false_eq_true,ite_true,ite_false] at m1 m2 <;>
      nlinarith only [m0,m1,m2,hh]
  have pun : G 0+g (T 0)+G 1+earX+g (T 1)+G 2+earU+g (T 2)=(Values.Dp V)+(Values.SU V)-v*(Values.SW V) := by
    have hh : (r-ell)*(Values.SW V)=v*(Values.SW V) := by rw [hrl]
    cases swap <;> simp only [Bool.false_eq_true,ite_true,ite_false,earX,earU] at * <;>
      nlinarith only [g0,g1,g2,hh]
  have zo : M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2)+M 3+f (T 3)=0 := by
    have he : (Values.D V)=(Values.K V)-q*(Values.L V) := rfl
    nlinarith only [pu,m3,he]
  have zn : G 0+g (T 0)+G 1+earX+g (T 1)+G 2+earU+g (T 2)+G 3+g (T 3)=0 := by
    have he : (Values.Dp V)=(Values.SW V)-q*(Values.SV V) := rfl
    nlinarith only [pun,g3,he]
  obtain ⟨w0,w0n,w1,w1n,w2,w2n⟩ := hwindows
  change window (Values.D V) (Values.K V) at w0
  change window (Values.Dp V) (Values.SW V) at w0n
  change window ((Values.D V)+(Values.A V)-r*(Values.K V)+(if swap then (Values.A V) else 0)) (Values.A V) at w1
  change window ((Values.Dp V)+(Values.A V)-r*(Values.SW V)+(if swap then 2*(Values.A V) else (Values.A V))) (Values.A V) at w1n
  change window ((Values.D V)+(Values.B V)-v*(Values.K V)) (Values.B V) at w2
  change window ((Values.Dp V)+(Values.SU V)-v*(Values.SW V)) (Values.SU V) at w2n
  have win (e S z C : ℤ) (he : window e S) (hz : 2*z=S-(2*C+1)) :
      0≤e ∧ e-z≤C := by dsimp [window] at he;omega
  have hN : 2*(N/2)+1=N := by
    have he : N=2*((2:ℤ)^a*2^b*2^c*2^(d-1))-1 := by
      dsimp [N,sourceMod]
      conv_lhs => rw [show d=d-1+1 by omega,pow_succ]
      ring
    omega
  have k0 := win _ _ (f (T 0)) (N/2) w0 (by have := n0.2.2.1;omega)
  have k1 := win _ _ (f (T 1)) (N/2) w1 (by have := n1.2.2.1;omega)
  have k2 := win _ _ (f (T 2)) (N/2) w2 (by have := n2.2.2.1;omega)
  have k0n := win _ _ (g (T 0)) N w0n n0.2.2.2
  have k1n := win _ _ (g (T 1)) N w1n n1.2.2.2
  have k2n := win _ _ (g (T 2)) N w2n n2.2.2.2
  have lastO : 0≤-f (T 3) ∧ -f (T 3)≤N/2 := by
    have hb := tab.1 2
    rw [hbase] at hb
    change 1≤(Values.L V) ∧ (Values.L V)<N at hb
    have hh := n3.2.2.1
    omega
  have lastN : 0≤-g (T 3) ∧ -g (T 3)≤N := by
    have hb := new_base_bounds a b c d (by omega) (by omega) hc hd 2
    rw [hnewbase] at hb
    change 1≤(Values.SV V) ∧ (Values.SV V)<2*N+1 at hb
    have hh := n3.2.2.2
    omega
  refine ⟨DataCertificate.mk ps ?_ ⟨if swap then 2 else 1,by cases swap <;> decide⟩ ?_ ?_ ?_ ?_⟩
  · change [T 0,T 1,T 2,T 3].Perm (negatives a b c d)
    have he : negatives a b c d=[T 2,T 3,T 0,T 1] := by dsimp [negatives,T,broadTerminals,size]
    rw [he]
    change ([T 0,T 1]++[T 2,T 3]).Perm ([T 2,T 3]++[T 0,T 1])
    exact List.perm_append_comm
  · intro pkt hpkt i hi
    simp only [ps,List.mem_cons,List.mem_nil_iff,or_false] at hpkt
    rcases hpkt with rfl|rfl|rfl|rfl
    all_goals exact good _ i hi
  · have he : (blocksWord (orderedPackets ps)).Perm (boundaryWord a b c d equal swap) := by
      have hh := (((((((hperm 0).append_right [T 0]).append (hperm 1)).append_right [T 1]).append
        (hperm 2)).append_right [T 2]).append (hperm 3)).append_right [T 3]
      simpa [ps,orderedPackets,blocksWord,boundaryWord] using hh
    exact Multiset.coe_eq_coe.mpr (he.trans hp)
  · change finiteChecks (oldMass a b c d) f (N/2) 0 ps
    simp only [ps,finiteChecks,zero_add]
    change 0≤M 0+f (T 0) ∧ M 0≤N/2 ∧
      0≤M 0+f (T 0)+M 1+f (T 1) ∧ M 0+f (T 0)+M 1≤N/2 ∧
      0≤M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2) ∧
      M 0+f (T 0)+M 1+f (T 1)+M 2≤N/2 ∧
      0≤M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2)+M 3+f (T 3) ∧
      M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2)+M 3≤N/2 ∧ True
    rcases k0 with ⟨k00,k01⟩
    rcases k1 with ⟨k10,k11⟩
    rcases k2 with ⟨k20,k21⟩
    exact ⟨by linarith only [m0,k00],by linarith only [m0,k01],
      by linarith only [px,k10],by linarith only [px,k11],
      by linarith only [pu,k20],by linarith only [pu,k21],
      by linarith only [zo],by linarith only [zo,lastO.2],trivial⟩
  · change finiteEarChecks (newMass a b c d) g N (base a b c d 0) 0
      (if swap then 2 else 1) ps
    rw [hbase]
    change finiteEarChecks (newMass a b c d) g N (Values.A V) 0 (if swap then 2 else 1) ps
    rcases k0n with ⟨k00,k01⟩
    rcases k1n with ⟨k10,k11⟩
    rcases k2n with ⟨k20,k21⟩
    cases swap <;> dsimp [earX,earU] at pxn pun zn
    all_goals simp only [Bool.false_eq_true,ite_false,ite_true,ps,finiteEarChecks,finiteChecks,zero_add]
    all_goals simp only [Bool.false_eq_true,ite_false,ite_true] at k10 k11
    all_goals change 0≤G 0+g (T 0) ∧ G 0≤N ∧ _
    all_goals exact ⟨by linarith only [g0,k00],by linarith only [g0,k01],
      by linarith only [pxn,k10],by linarith only [pxn,k11],
      by linarith only [pun,k20],by linarith only [pun,k21],
      by linarith only [zn],by linarith only [zn,lastN.2],trivial⟩

private theorem adjacent_certificate_exists (a b c d : ℕ) (hc : 2≤c)
    (hcd : d=c+1) (hda : d<a) (hab : a≤b) : Nonempty (Certificate a b c d) := by
  apply boundary_certificate a b c d hc (by omega) hda hab false false (by simp)
  have hz : (4:ℤ)≤2^c := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hc
  have hw : (2:ℤ)^d=2*2^c := by rw [hcd,pow_succ];ring
  have hh := adjacent_windows (2^c) (2^(a-d-1)) (2^(b-a)) hz
    (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  simp only [hw,Bool.false_eq_true,ite_false,add_zero]
  dsimp only at hh
  unfold window at hh ⊢
  ring_nf at hh ⊢
  exact hh

private theorem diagonal_certificate_exists (a b d : ℕ) (hd : 2≤d)
    (hda : d<a) (hab : a≤b) : Nonempty (Certificate a b d d) := by
  let t : ℤ := 2^(a-d-1)
  let V := values (2^d) (2^d) (2*t) (2^(b-a))
  let swap := decide ((Values.D V)<2*t*(Values.H V)-(Values.S V))
  apply boundary_certificate a b d d hd hd hda hab true swap (by simp)
  have hw : (4:ℤ)≤2^d := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hd
  exact diagonal_windows (2^d) t (2^(b-a)) hw
    (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum
