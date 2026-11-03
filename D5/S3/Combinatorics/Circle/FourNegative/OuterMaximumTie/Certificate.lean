/- GID: D5/S3/Combinatorics/Circle/FourNegative/OuterMaximumTie/Certificate
   generality: I
   mirror-B: none(waiver:consumed-physical-certificate)
   mirror-E: none(waiver:consumed-physical-certificate)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical certificates with the actual inherited charge and literal first ear. -/
import D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie.Physical
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie
open SourceWidth PeriodicShortening RunFirstEarTransport PacketNormalForm
open private D A B L M eps oldSeam newSeam oldHead newHead Gates Stock
  from D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie.Arithmetic
open private cap bank terminal word bank_inventory bank_good bank_nodup bank_masses masses
  from D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie.Physical
open private size sourceMod base newBase charge chainLength chainStart nextBase nextNewBase
  oldValue newValue negatives chain_values packet_masses source_totals source_signs
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private oldMass newMass
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private finiteChecks finiteEarChecks orderedPackets DataCertificate DataCertificate.mk
  DataCertificate.packets DataCertificate.negativeOrder DataCertificate.earSlot
  DataCertificate.positiveLabels DataCertificate.partition
  DataCertificate.oldEndpoints DataCertificate.newEndpoints
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate
open private four_strip
  from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private inserted_perm
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical
open private blocksWord
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure

private def height (f : ℕ→ℤ) (P : Fin 4→List ℕ) (T : Fin 4→ℕ) : Fin 4→ℤ :=
  let m := fun j => ((P j).map f).sum+f (T j)
  ![m 0,m 0+m 1,m 0+m 1+m 2,m 0+m 1+m 2+m 3]

set_option maxHeartbeats 2400000 in
private theorem physical_joint_construction (asc : Bool) (a b c : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (vZ wZ : ℤ)
    (stock : Stock asc (2^a) (2^b) (2^c) vZ wZ)
    (gates : Gates asc (2^a) (2^b) (2^c) vZ wZ) :
    ∃ sigma : List (Fin (a+b+c+a)),
      OriginalOrder (a+b+c+a) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+a+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+a) sigma 0) := by
  classical
  obtain ⟨hv0,hvCap,hw0,hwCap⟩ := stock
  let v := vZ.toNat
  let w := wZ.toNat
  have ev : (v:ℤ)=vZ := Int.toNat_of_nonneg hv0
  have ew : (w:ℤ)=wZ := Int.toNat_of_nonneg hw0
  have half (n : ℕ) (hn : 1≤n) : (2:ℤ)^n=2*2^(n-1) := by
    calc
      (2:ℤ)^n = 2^((n-1)+1) := congrArg (fun k : ℕ => (2:ℤ)^k) (by omega)
      _ = 2*2^(n-1) := by rw [pow_succ]; ring
  have hv : v<2^(a-1) := by
    have h : (v:ℤ)<(2:ℤ)^(a-1) := by rw [ev]; nlinarith [half a (by omega)]
    exact_mod_cast h
  have hw : w<2^((if asc then c else b)-1) := by
    have h : (w:ℤ)<(2:ℤ)^((if asc then c else b)-1) := by
      rw [ew]
      cases asc <;> simp only [Bool.false_eq_true,ite_false,ite_true] at *
      · nlinarith [half b (by omega)]
      · nlinarith [half c (by omega)]
    exact_mod_cast h
  let P := bank asc a b c v w
  let T := terminal asc a b c
  let l := word asc a b c v w
  let f := oldValue a b c a
  let g := newValue a b c a
  let N := sourceMod a b c a
  let AA := A (2^a) (2^b) (2^c)
  have hbases : base a b c a=![AA,B (2^a) (2^b),L (2^a) (2^c),M (2^a) (2^b) (2^c)] := by
    funext r; fin_cases r <;> dsimp [base,AA,A,B,L,M,D] <;> ring
  have hnewbases : newBase a b c a=
      ![2*AA,2*B (2^a) (2^b)-1,2*L (2^a) (2^c)-2^c-1,
        2*M (2^a) (2^b) (2^c)-D (2^b) (2^c)] := by
    funext r; fin_cases r <;> dsimp [newBase,charge]
    all_goals rw [hbases] <;> dsimp [D] <;> ring
  have inv : l.Perm (List.range (size a b c a)) := bank_inventory asc a b c v w ha hb hc hv hw
  have good (j : Fin 4) (i : ℕ) (hi : i∈P j) : i<size a b c a ∧ i∉negatives a b c a :=
    bank_good asc a b c v w ha hb hc j i hi
  have nd (j : Fin 4) : (P j).Nodup := bank_nodup asc a b c v w ha hb hc hv hw j
  have mo := bank_masses asc a b c v w ha hb hc hv hw false
  have mg := bank_masses asc a b c v w ha hb hc hv hw true
  dsimp only [Bool.false_eq_true,ite_false,ite_true] at mo mg
  rw [hbases] at mo
  rw [hnewbases] at mg
  have n0 := native_masses a b c a ha hb hc ha 0
  have n1 := native_masses a b c a ha hb hc ha 1
  have n2 := native_masses a b c a ha hb hc ha 2
  have n3 := native_masses a b c a ha hb hc ha 3
  simp only [chainLength,chainStart,nextBase,nextNewBase,hbases,hnewbases,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Nat.zero_add,
    show a+(c-1)=a+c-1 by omega,
    show a+c+(b-1)=a+c+b-1 by omega,
    show a+c+b+(a-1)=a+b+c+a-1 by omega] at n0 n1 n2 n3
  have totals := source_totals a b c a ha hb hc ha
  have oldZero : (l.map f).sum=0 := (inv.map f).sum_eq.trans totals.1
  have newZero : AA+(l.map g).sum=0 := by
    have h := (inv.map g).sum_eq.trans totals.2.1
    rw [hbases] at h
    change (l.map g).sum= -AA at h
    omega
  have fresh : g (size a b c a)=AA := by simpa [hbases] using totals.2.2
  have os (j : Fin 4) : height f P T j=oldSeam asc (2^a) (2^b) (2^c) vZ wZ j := by
    have m0 := mo 0; have m1 := mo 1; have m2 := mo 2; have m3 := mo 3
    cases asc <;> fin_cases j
    all_goals dsimp [height,P,T,terminal,oldSeam,eps]
    all_goals dsimp [masses,cap] at m0 m1 m2 m3
    all_goals simp only [ev,ew] at m0 m1 m2 m3
    all_goals nlinarith only [m0,m1,m2,m3,n0.1,n1.1,n2.1,n3.1]
  have ns (j : Fin 4) : AA+height g P T j=newSeam asc (2^a) (2^b) (2^c) vZ wZ j := by
    have m0 := mg 0; have m1 := mg 1; have m2 := mg 2; have m3 := mg 3
    cases asc <;> fin_cases j
    all_goals dsimp [height,P,T,terminal,newSeam,oldSeam,eps]
    all_goals dsimp [masses,cap] at m0 m1 m2 m3
    all_goals simp only [ev,ew] at m0 m1 m2 m3
    all_goals nlinarith only [m0,m1,m2,m3,n0.2.1,n1.2.1,n2.2.1,n3.2.1]
  have terminal_values (j : Fin 4) :
      2*f (T j)=oldHead asc (2^a) (2^b) (2^c) j-N ∧
      2*g (T j)=newHead asc (2^a) (2^b) (2^c) j-(2*N+1) := by
    cases asc <;> fin_cases j
    all_goals dsimp [T,terminal,oldHead,newHead]
    all_goals constructor <;> nlinarith only
      [n0.2.2.1,n0.2.2.2,n1.2.2.1,n1.2.2.2,n2.2.2.1,n2.2.2.2,n3.2.2.1,n3.2.2.2]
  have odd : N%2=1 := by
    have hn : N=2*((2:ℤ)^(a-1)*2^b*2^c*2^a-1)+1 := by
      dsimp [N,sourceMod]
      calc
        (2:ℤ)^a*2^b*2^c*2^a-1 = (2*2^(a-1))*2^b*2^c*2^a-1 :=
          congrArg (fun x : ℤ => x*2^b*2^c*2^a-1) (half a (by omega))
        _ = _ := by ring
    omega
  have parity := Int.emod_add_mul_ediv N 2
  have os0 := os 0; have os1 := os 1; have os2 := os 2; have os3 := os 3
  have ns0 := ns 0; have ns1 := ns 1; have ns2 := ns 2; have ns3 := ns 3
  have t0 := terminal_values 0; have t1 := terminal_values 1
  have t2 := terminal_values 2; have t3 := terminal_values 3
  have g0 := gates 0; have g1 := gates 1; have g2 := gates 2; have g3 := gates 3
  dsimp [height] at os0 os1 os2 os3 ns0 ns1 ns2 ns3
  let packets : List (Finset ℕ × ℕ) :=
    [((P 0).toFinset,T 0),((P 1).toFinset,T 1),((P 2).toFinset,T 2),((P 3).toFinset,T 3)]
  have massOld (j : Fin 4) : oldMass a b c a (P j).toFinset=((P j).map f).sum := by
    have h := (packet_masses a b c a ha hb hc ha (P j).toFinset
      (by intro i hi; exact good j i (List.mem_toFinset.mp hi))).1.symm
    exact h.trans (List.sum_toFinset f (nd j))
  have massNew (j : Fin 4) : newMass a b c a (P j).toFinset=((P j).map g).sum := by
    have h := (packet_masses a b c a ha hb hc ha (P j).toFinset
      (by intro i hi; exact good j i (List.mem_toFinset.mp hi))).2.symm
    exact h.trans (List.sum_toFinset g (nd j))
  have packetPerm (j : Fin 4) : (P j).toFinset.toList.Perm (P j) :=
    (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (nd j)).mpr (by intro i; simp)
  have packetWordPerm : (blocksWord (orderedPackets packets)).Perm l := by
    have h3 := (packetPerm 3).append (List.Perm.refl [T 3])
    have h2 := (packetPerm 2).append (h3.cons (T 2))
    have h1 := (packetPerm 1).append (h2.cons (T 1))
    simpa only [orderedPackets,packets,List.map_cons,List.map_nil,blocksWord,
      List.append_nil,l,word,P,T] using (packetPerm 0).append (h1.cons (T 0))
  have cert : Certificate a b c a := by
    refine DataCertificate.mk packets ?_ 0 ?_ ?_ ?_ ?_
    · apply Multiset.coe_eq_coe.mp
      cases asc <;> dsimp [packets,T,terminal,negatives,size]
      all_goals simp only [List.map_cons,List.map_nil,Prod.snd,Multiset.coe_cons,Multiset.coe_nil]
      all_goals ac_rfl
    · intro p hp i hi
      simp only [packets,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl <;> exact good _ i (List.mem_toFinset.mp hi)
    · exact Multiset.coe_eq_coe.mpr (packetWordPerm.trans inv)
    · change finiteChecks (oldMass a b c a) f (N/2) 0 packets
      simp only [packets,finiteChecks,massOld]
      repeat' constructor
      all_goals nlinarith only [os0,os1,os2,os3,t0.1,t1.1,t2.1,t3.1,
        g0.1.1,g0.1.2,g1.1.1,g1.1.2,g2.1.1,g2.1.2,g3.1.1,g3.1.2,odd,parity]
    · change finiteEarChecks (newMass a b c a) g N (base a b c a 0) 0 0 packets
      rw [hbases]
      simp only [Matrix.cons_val_zero,packets,finiteEarChecks,finiteChecks,massNew]
      repeat' constructor
      all_goals nlinarith only [ns0,ns1,ns2,ns3,t0.2,t1.2,t2.2,t3.2,
        g0.2.1,g0.2.2,g1.2.1,g1.2.2,g2.2.1,g2.2.2,g3.2.1,g3.2.2]
  have physicalInventory : l.Perm (List.range (size a b c a)) :=
    packetWordPerm.symm.trans (Multiset.coe_eq_coe.mp cert.partition)
  have packetMember (j : Fin 4) : ((P j).toFinset,T j)∈cert.packets := by
    change ((P j).toFinset,T j)∈packets
    fin_cases j <;> simp [packets]
  -- Consume the certificate's endpoint fields. Its first-slot placement is
  -- freely ordered within the positive packet, here literally fresh FIRST.
  have oc := cert.oldEndpoints
  have nc := cert.newEndpoints
  change finiteChecks (oldMass a b c a) f (N/2) 0 packets at oc
  change finiteEarChecks (newMass a b c a) g N (base a b c a 0) 0 0 packets at nc
  rw [hbases] at nc
  simp only [Matrix.cons_val_zero,packets,finiteChecks,massOld] at oc
  simp only [Matrix.cons_val_zero,packets,finiteEarChecks,finiteChecks,massNew] at nc
  obtain ⟨ol0,op0,ol1,op1,ol2,op2,ol3,op3,_⟩ := oc
  obtain ⟨nl0,np0,nl1,np1,nl2,np2,nl3,np3,_⟩ := nc
  have pos (j : Fin 4) (i : ℕ) (hi : i∈P j) : 0≤f i ∧ 0≤g i := by
    have hi' := cert.positiveLabels _ (packetMember j) i (List.mem_toFinset.mpr hi)
    have hs := source_signs a b c a ha hb hc ha i hi'.1
    rw [if_neg hi'.2] at hs
    exact ⟨hs.1.le,hs.2.le⟩
  have neg (j : Fin 4) : f (T j)<0 ∧ g (T j)<0 := by
    have hn : T j∈negatives a b c a := cert.negativeOrder.mem_iff.mp
      (List.mem_map.mpr ⟨((P j).toFinset,T j),packetMember j,rfl⟩)
    have ht : T j<size a b c a := by
      simp only [negatives,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false,size] at hn
      dsimp [size]; omega
    simpa only [if_pos hn] using source_signs a b c a ha hb hc ha (T j) ht
  have start := (chain_values a b c a ha hb hc ha).1 0
  rw [hbases] at start
  change 1≤AA ∧ AA<N at start
  have zo : ((P 0).map f).sum+f (T 0)+((P 1).map f).sum+f (T 1)+
      ((P 2).map f).sum+f (T 2)+((P 3).map f).sum+f (T 3)=0 := by
    simpa [l,word,P,T,List.map_append,List.sum_append,List.sum_cons,add_assoc] using oldZero
  have zn : AA+((P 0).map g).sum+g (T 0)+((P 1).map g).sum+g (T 1)+
      ((P 2).map g).sum+g (T 2)+((P 3).map g).sum+g (T 3)=0 := by
    simpa [l,word,P,T,List.map_append,List.sum_append,List.sum_cons,add_assoc] using newZero
  have oldstrip : InStrip f (N/2) 0 l := by
    apply four_strip f (P 0) (P 1) (P 2) (P 3) (T 0) (T 1) (T 2) (T 3) (N/2) 0
      (fun i hi => (pos 0 i hi).1) (fun i hi => (pos 1 i hi).1)
      (fun i hi => (pos 2 i hi).1) (fun i hi => (pos 3 i hi).1) le_rfl
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith [(neg 3).1]
    · simpa [l,word,P,T] using oldZero
  have newtail : InStrip g N AA l := by
    apply four_strip g (P 0) (P 1) (P 2) (P 3) (T 0) (T 1) (T 2) (T 3) N AA
      (fun i hi => (pos 0 i hi).2) (fun i hi => (pos 1 i hi).2)
      (fun i hi => (pos 2 i hi).2) (fun i hi => (pos 3 i hi).2) (by omega)
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith [(neg 3).2]
    · simpa [l,word,P,T] using newZero
  have newstrip : InStrip g N 0 (size a b c a::l) := by
    refine ⟨le_rfl,by omega,?_⟩
    simpa only [fresh,zero_add] using newtail
  let k := a+b+c+a
  let s := 1+2^a+2^(a+b)+2^(a+b+c)
  have hmod : modulus k=N := by dsimp [k,N,modulus,sourceMod]; ring
  have hmodn : modulus (k+1)=2*N+1 := by dsimp [k,N,modulus,sourceMod]; ring
  have hseed : (s:ℤ)=AA := by
    dsimp [s,AA,A,D]; push_cast; simp only [pow_add]; ring
  have fform : f=(fun i => centered N ((2:ℤ)^i*AA)) := by
    funext i; dsimp [f,oldValue]; rw [hbases]; rfl
  have gform : g=(fun i => centered (2*N+1) ((2:ℤ)^i*(2*AA))) := by
    funext i; dsimp [g,newValue]; rw [hbases]; rfl
  have hpnew : (k::l).Perm (List.range (k+1)) := by
    simpa only [List.nil_append] using inserted_perm k [] l physicalInventory
  refine ⟨l.map (label k (by dsimp [k]; omega)),?_,?_⟩
  · apply lift_order k s (by dsimp [k]; omega) l physicalInventory
    · simpa only [fform,hmod,hseed] using oldstrip
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero k s (by dsimp [k]; omega)
  · have hm := marked_word k 0 (by dsimp [k]; omega) [] l rfl physicalInventory
    simp only [List.nil_append] at hm
    rw [hm]
    apply lift_order (k+1) (2*s) (by omega) (k::l) hpnew
    · have hs : ((2*s:ℕ):ℤ)=2*AA := by push_cast; rw [hseed]
      simpa only [gform,hmodn,hs,show (2*N+1)/2=N by omega] using newstrip
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*s) (by dsimp [k]; omega)

end D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie
