/- GID: D5/S3/Combinatorics/Circle/FourNegative/UpperGap/BoundaryReordered
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-physical-packet-checks)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical packet checks in the U W V X terminal order. -/
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryPackets

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.UpperGap
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private size sourceMod base newBase charge chainLength chainStart nextBase nextNewBase
  oldValue newValue negatives chain_values source_totals
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private packetChecks withEar from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private masked_inventory
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks
open private paired_terminal masked_source_masses
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.SourceMasses
open private certificate_of_checks
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.PacketBridge

open private decoded_label_good native_masses four_packet_checks
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryPackets

private def reorderedMargins (a b c d p q : ℕ) : Prop :=
  let A := base a b c d 0
  let B := base a b c d 1
  let L := base a b c d 2
  let M := base a b c d 3
  let Bp := newBase a b c d 1
  let Lp := newBase a b c d 2
  let Mp := newBase a b c d 3
  let S1 := B-2*A
  let S2 := B-A+M-L+(p:ℤ)*B
  let S3 := M-A-(q:ℤ)*B
  let T1 := Bp-4*A
  let T2 := Bp-2*A+Mp-Lp+(p:ℤ)*Bp
  let T3 := Mp-2*A-(q:ℤ)*Bp
  0≤S1 ∧ 0≤T1 ∧ 2*S1≤B-1 ∧ 2*T1≤Bp-1 ∧
  0≤S2 ∧ 0≤T2 ∧ 2*S2≤M-1 ∧ 2*T2≤Mp-1 ∧
  0≤S3 ∧ 0≤T3 ∧ 2*S3≤L-1 ∧ 2*T3≤Lp-1

set_option maxHeartbeats 1600000 in
private theorem reordered_certificate (a b c d p q : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hu : 1<2^(d-1))
    (hp : p+q<2^(c-1)) (hq : q<2^(c-1))
    (hqp : ∀ e<c-1, q.testBit e=true → (p+q).testBit e=true)
    (hm : reorderedMargins a b c d p q) : Nonempty (Certificate a b c d) := by
  let P := maskedBlocks a b c d 1 1 0 0 (p+q) q 0
  let nu := d-1
  let nv := d+c-1
  let nw := d+c+b-1
  let nx := d+c+b+a-1
  let bs := [(P.first,nu),(P.third,nw),(P.second,nv),(P.fourth,nx)]
  have hinv : (blocksWord bs).Perm (List.range (size a b c d)) := by
    have h := masked_inventory a b c d 1 1 0 0 (p+q) q 0
      (by omega) (by omega) (by omega) (by omega)
      (by intro e _ he;exact he)
      (by intro e _ he;simp at he)
      (by intro e he _;simp [Nat.testBit_two_pow_sub_one,he])
      (by intro e _ he;simpa using he) hqp (by simp)
    have hs : (blocksWord [(P.first,nu),(P.second,nv),(P.third,nw),(P.fourth,nx)]).Perm
        (List.range (size a b c d)) := by
      simpa [blocksWord,P,nu,nv,nw,nx,chamberMaskedWord,Blocks.word,maskedBlocks,
        chamberLabels,labels,size,List.append_assoc,Nat.add_assoc,Nat.add_comm,
        Nat.add_left_comm] using h
    have he := ((List.perm_append_comm (l₁:=P.third++[nw]) (l₂:=P.second++[nv])).append_right
      (P.fourth++[nx])).append_left (P.first++[nu])
    have he' : (blocksWord bs).Perm
        (blocksWord [(P.first,nu),(P.second,nv),(P.third,nw),(P.fourth,nx)]) := by
      simpa [blocksWord,bs,List.append_assoc] using he
    exact he'.trans hs
  have hneg : (bs.map Prod.snd).Perm (negatives a b c d) := by
    have h := (List.Perm.swap nv nw [nx]).cons nu
    simpa [bs,nu,nv,nw,nx,negatives,size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  have hpos : ∀ block∈bs, ∀ i∈block.1, i<size a b c d ∧ i∉negatives a b c d := by
    intro block hblock i hi
    simp only [bs,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hblock
    rcases hblock with rfl|rfl|rfl|rfl
    all_goals dsimp [P,maskedBlocks] at hi
    all_goals simp only [List.mem_append] at hi
    all_goals repeat' first
      | exact decoded_label_good a b c d ha hb hc hd 0 _ i hi
      | exact decoded_label_good a b c d ha hb hc hd 1 _ i hi
      | exact decoded_label_good a b c d ha hb hc hd 2 _ i hi
      | exact decoded_label_good a b c d ha hb hc hd 3 _ i hi
      | rcases hi with hi|hi
  have h0 := native_masses a b c d ha hb hc hd 0
  have h1 := native_masses a b c d ha hb hc hd 1
  have h2 := native_masses a b c d ha hb hc hd 2
  have h3 := native_masses a b c d ha hb hc hd 3
  dsimp [chainLength,chainStart,nextBase,nextNewBase] at h0 h1 h2 h3
  rw [show d+(c-1)=nv by dsimp [nv];omega] at h1
  rw [show d+c+(b-1)=nw by dsimp [nw];omega] at h2
  rw [show d+c+b+(a-1)=nx by dsimp [nx];omega] at h3
  simp only [Nat.zero_add] at h0
  change _+oldValue a b c d nu=_ ∧ _+newValue a b c d nu=_ ∧ _ ∧ _ at h0
  have mass := masked_source_masses a b c d 1 1 (p+q) q 0 ha hb hc hd
    hu hu hp hq (by positivity) (by intro e _ he;exact he) hqp
  have mo := mass false
  have mn := mass true
  dsimp only at mo mn
  simp only [Bool.false_eq_true,↓reduceIte] at mo mn
  change (P.first.map (oldValue a b c d)).sum=_ ∧
    (P.second.map (oldValue a b c d)).sum=_ ∧
    (P.third.map (oldValue a b c d)).sum=_ ∧
    (P.fourth.map (oldValue a b c d)).sum=_ at mo
  change (P.first.map (newValue a b c d)).sum=_ ∧
    (P.second.map (newValue a b c d)).sum=_ ∧
    (P.third.map (newValue a b c d)).sum=_ ∧
    (P.fourth.map (newValue a b c d)).sum=_ at mn
  have ht := source_totals a b c d ha hb hc hd
  have hear := ht.2.2
  have hto := ((hinv.map (oldValue a b c d)).sum_eq).trans ht.1
  have htn := ((hinv.map (newValue a b c d)).sum_eq).trans ht.2.1
  have hA := ((chain_values a b c d ha hb hc hd).1 0).1
  have hnA : newBase a b c d 0=2*base a b c d 0 := by simp [newBase,charge]
  rw [hnA] at mn h0
  dsimp only [reorderedMargins] at hm
  obtain ⟨s1,t1,p1,z1,s2,t2,p2,z2,s3,t3,p3,z3⟩ := hm
  have os1 : (P.first.map (oldValue a b c d)).sum+oldValue a b c d nu=
      base a b c d 1-2*base a b c d 0 := by
    rw [mo.1];push_cast;nlinarith only [h0.1]
  have os2 : (P.first.map (oldValue a b c d)).sum+oldValue a b c d nu+(P.third.map (oldValue a b c d)).sum+oldValue a b c d nw=
      base a b c d 1-base a b c d 0+base a b c d 3-base a b c d 2+(p:ℤ)*base a b c d 1 := by
    rw [os1,mo.2.2.1];push_cast;nlinarith only [h2.1]
  have os3 : (P.first.map (oldValue a b c d)).sum+oldValue a b c d nu+(P.third.map (oldValue a b c d)).sum+oldValue a b c d nw+(P.second.map (oldValue a b c d)).sum+oldValue a b c d nv=
      base a b c d 3-base a b c d 0-(q:ℤ)*base a b c d 1 := by
    rw [os2,mo.2.1];push_cast;nlinarith only [h1.1]
  have ns1 : (P.first.map (newValue a b c d)).sum+newValue a b c d nu=
      newBase a b c d 1-4*base a b c d 0 := by
    rw [mn.1];push_cast;nlinarith only [h0.2.1,hnA]
  have ns2 : (P.first.map (newValue a b c d)).sum+newValue a b c d nu+(P.third.map (newValue a b c d)).sum+newValue a b c d nw=
      newBase a b c d 1-2*base a b c d 0+newBase a b c d 3-newBase a b c d 2+(p:ℤ)*newBase a b c d 1 := by
    rw [ns1,mn.2.2.1];push_cast;nlinarith only [h2.2.1,hnA]
  have ns3 : (P.first.map (newValue a b c d)).sum+newValue a b c d nu+(P.third.map (newValue a b c d)).sum+newValue a b c d nw+(P.second.map (newValue a b c d)).sum+newValue a b c d nv=
      newBase a b c d 3-2*base a b c d 0-(q:ℤ)*newBase a b c d 1 := by
    rw [ns2,mn.2.1];push_cast;nlinarith only [h1.2.1,hnA]
  apply certificate_of_checks a b c d ha hb hc hd bs hinv hneg hpos
  · apply four_packet_checks (oldValue a b c d) (sourceMod a b c d/2)
      P.first P.third P.second P.fourth nu nw nv nx
    · simpa only [blocksWord,bs,List.append_assoc,List.cons_append,List.nil_append] using hto
    · constructor
      · rw [os1];exact s1
      · have hdoubled : 2*((P.first.map (oldValue a b c d)).sum)≤sourceMod a b c d-1 := by
          nlinarith only [os1,p1,h0.2.2.1]
        omega
    · constructor
      · rw [os2];exact s2
      · have hdoubled : 2*((P.first.map (oldValue a b c d)).sum+oldValue a b c d nu+(P.third.map (oldValue a b c d)).sum)≤sourceMod a b c d-1 := by
          nlinarith only [os2,p2,h2.2.2.1]
        omega
    · constructor
      · rw [os3];exact s3
      · have hdoubled : 2*((P.first.map (oldValue a b c d)).sum+oldValue a b c d nu+(P.third.map (oldValue a b c d)).sum+oldValue a b c d nw+(P.second.map (oldValue a b c d)).sum)≤sourceMod a b c d-1 := by
          nlinarith only [os3,p3,h1.2.2.1]
        omega
    · omega
  · change packetChecks (newValue a b c d) (sourceMod a b c d) 0
      [(P.first,nu),(P.third,nw),(P.second,nv),
        (P.fourth++[size a b c d],nx)]
    apply four_packet_checks
    · simp only [blocksWord,bs,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
        List.map_singleton,List.sum_singleton,List.map_nil,List.sum_nil,add_zero] at htn ⊢
      omega
    · constructor
      · rw [ns1];exact t1
      · have hdoubled : 2*((P.first.map (newValue a b c d)).sum)≤2*sourceMod a b c d := by
          nlinarith only [ns1,z1,h0.2.2.2]
        omega
    · constructor
      · rw [ns2];exact t2
      · have hdoubled : 2*((P.first.map (newValue a b c d)).sum+newValue a b c d nu+(P.third.map (newValue a b c d)).sum)≤2*sourceMod a b c d := by
          nlinarith only [ns2,z2,h2.2.2.2]
        omega
    · constructor
      · rw [ns3];exact t3
      · have hdoubled : 2*((P.first.map (newValue a b c d)).sum+newValue a b c d nu+(P.third.map (newValue a b c d)).sum+newValue a b c d nw+(P.second.map (newValue a b c d)).sum)≤2*sourceMod a b c d := by
          nlinarith only [ns3,z3,h1.2.2.2]
        omega
    · omega

end D5.S3.Combinatorics.Circle.FourNegative.UpperGap
