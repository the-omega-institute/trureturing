/- GID: D5/S3/Combinatorics/Circle/FourNegative/UpperGap/BoundaryPackets
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-physical-packet-checks)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical packet checks from exact source masses and terminal margins. -/
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.PacketBridge

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

private theorem dyadic_half (n : ℕ) (hn : 1≤n) :
    (2:ℤ)^n=2*2^(n-1) := by
  calc
    _ = (2:ℤ)^((n-1)+1) := by congr 1;omega
    _ = _ := by rw [pow_succ];ring

private theorem decoded_label_good (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (r : Fin 4) (m i : ℕ)
    (hi : i∈chamberLabels (chainLength a b c d r-1) (chainStart b c d r) m) :
    i<size a b c d ∧ i∉negatives a b c d := by
  obtain ⟨e,he,_,hi⟩ := (chamberLabels_mem _ _ _ _).mp hi
  fin_cases r <;> dsimp [chainLength,chainStart,size] at * <;>
    simp only [negatives,size,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] <;> omega

private theorem native_masses (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (r : Fin 4) :
    let C := (((2^(chainLength a b c d r-1)-1:ℕ):ℤ))
    let n := chainStart b c d r+(chainLength a b c d r-1)
    C*base a b c d r+oldValue a b c d n = nextBase a b c d r-base a b c d r ∧
    C*newBase a b c d r+newValue a b c d n = nextNewBase a b c d r-newBase a b c d r ∧
    2*oldValue a b c d n = nextBase a b c d r-sourceMod a b c d ∧
    2*newValue a b c d n = nextNewBase a b c d r-(2*sourceMod a b c d+1) := by
  have hn : 1≤chainLength a b c d r := by
    fin_cases r <;> simp [chainLength] <;> omega
  have hhalf := dyadic_half (chainLength a b c d r) hn
  have hcst : (((2^(chainLength a b c d r-1)-1:ℕ):ℤ))=
      (2:ℤ)^(chainLength a b c d r-1)-1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow),Nat.cast_pow]
    norm_num
  have hold : (2:ℤ)^(chainLength a b c d r)*base a b c d r =
      sourceMod a b c d+nextBase a b c d r := by
    fin_cases r <;> dsimp [chainLength,base,nextBase,sourceMod] <;> ring
  have hnew : (2:ℤ)^(chainLength a b c d r)*newBase a b c d r =
      (2*sourceMod a b c d+1)+nextNewBase a b c d r := by
    fin_cases r <;> dsimp [chainLength,newBase,charge,base,nextNewBase,sourceMod] <;> ring
  rw [hhalf,mul_assoc] at hold hnew
  have eto : -(sourceMod a b c d-nextBase a b c d r)/2 =
      nextBase a b c d r-(2:ℤ)^(chainLength a b c d r-1)*base a b c d r := by omega
  have etn : -((2*sourceMod a b c d+1)-nextNewBase a b c d r)/2 =
      nextNewBase a b c d r-(2:ℤ)^(chainLength a b c d r-1)*newBase a b c d r := by omega
  have ht := paired_terminal a b c d ha hb hc hd r
  dsimp only at ht ⊢
  rw [hcst,ht.1,ht.2,eto,etn]
  refine ⟨by ring,by ring,?_,?_⟩ <;> omega

private theorem four_packet_checks (f : ℕ→ℤ) (C : ℤ)
    (P Q R G : List ℕ) (nu nv nw nx : ℕ)
    (htotal : ((P++nu::Q++nv::R++nw::G++[nx]).map f).sum=0)
    (h1 : 0≤(P.map f).sum+f nu ∧ (P.map f).sum≤C)
    (h2 : 0≤(P.map f).sum+f nu+(Q.map f).sum+f nv ∧
      (P.map f).sum+f nu+(Q.map f).sum≤C)
    (h3 : 0≤(P.map f).sum+f nu+(Q.map f).sum+f nv+(R.map f).sum+f nw ∧
      (P.map f).sum+f nu+(Q.map f).sum+f nv+(R.map f).sum≤C)
    (h4 : -f nx≤C) :
    packetChecks f C 0 [(P,nu),(Q,nv),(R,nw),(G,nx)] := by
  simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons,
    List.map_nil,List.sum_nil,add_zero] at htotal
  simp only [packetChecks,zero_add]
  exact ⟨h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,by omega,by omega,trivial⟩

private def standardMargins (a b c d u r p q w : ℕ) : Prop :=
  let A := base a b c d 0
  let B := base a b c d 1
  let L := base a b c d 2
  let M := base a b c d 3
  let Bp := newBase a b c d 1
  let Lp := newBase a b c d 2
  let Mp := newBase a b c d 3
  let S1 := B-((u:ℤ)+1)*A
  let S2 := L-((r:ℤ)+1)*A-(p:ℤ)*B
  let S3 := M-A-(q:ℤ)*B-(w:ℤ)*L
  let T1 := Bp-2*((u:ℤ)+1)*A
  let T2 := Lp-2*((r:ℤ)+1)*A-(p:ℤ)*Bp
  let T3 := Mp-2*A-(q:ℤ)*Bp-(w:ℤ)*Lp
  0≤S1 ∧ 0≤T1 ∧ 2*S1≤B-1 ∧ 2*T1≤Bp-1 ∧
  0≤S2 ∧ 0≤T2 ∧ 2*S2≤L-1 ∧ 2*T2≤Lp-1 ∧
  0≤S3 ∧ 0≤T3 ∧ 2*S3≤M-1 ∧ 2*T3≤Mp-1

set_option maxHeartbeats 1600000 in
private theorem standard_certificate (a b c d u r p q w : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hu : u<2^(d-1)) (hr : r<2^(d-1))
    (hp : p<2^(c-1)) (hq : q<2^(c-1)) (hw : w<2^(b-1))
    (hru : ∀ e<d-1, r.testBit e=true → u.testBit e=true)
    (hqp : ∀ e<c-1, q.testBit e=true → p.testBit e=true)
    (hm : standardMargins a b c d u r p q w) : Nonempty (Certificate a b c d) := by
  let P := maskedBlocks a b c d u r 0 0 p q w
  let nu := d-1
  let nv := d+c-1
  let nw := d+c+b-1
  let nx := d+c+b+a-1
  let bs := [(P.first,nu),(P.second,nv),(P.third,nw),(P.fourth,nx)]
  have hinv : (blocksWord bs).Perm (List.range (size a b c d)) := by
    have h := masked_inventory a b c d u r 0 0 p q w
      (by omega) (by omega) (by omega) (by omega) hru
      (by intro e _ he; simp at he)
      (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he])
      (by intro e _ he; simpa using he) hqp (by simp)
    simpa [blocksWord,bs,P,nu,nv,nw,nx,chamberMaskedWord,Blocks.word,maskedBlocks,
      chamberLabels,labels,size,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  have hneg : (bs.map Prod.snd).Perm (negatives a b c d) := by
    simp [bs,nu,nv,nw,nx,negatives,size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
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
  have mass := masked_source_masses a b c d u r p q w ha hb hc hd
    hu hr hp hq hw hru hqp
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
  dsimp only [standardMargins] at hm
  obtain ⟨s1,t1,p1,z1,s2,t2,p2,z2,s3,t3,p3,z3⟩ := hm
  have os1 : (P.first.map (oldValue a b c d)).sum+oldValue a b c d nu=
      base a b c d 1-((u:ℤ)+1)*base a b c d 0 := by
    rw [mo.1]; nlinarith only [h0.1]
  have os2 : (P.first.map (oldValue a b c d)).sum+oldValue a b c d nu+
      (P.second.map (oldValue a b c d)).sum+oldValue a b c d nv=
      base a b c d 2-((r:ℤ)+1)*base a b c d 0-(p:ℤ)*base a b c d 1 := by
    rw [os1,mo.2.1]; nlinarith only [h1.1]
  have os3 : (P.first.map (oldValue a b c d)).sum+oldValue a b c d nu+
      (P.second.map (oldValue a b c d)).sum+oldValue a b c d nv+
      (P.third.map (oldValue a b c d)).sum+oldValue a b c d nw=
      base a b c d 3-base a b c d 0-(q:ℤ)*base a b c d 1-(w:ℤ)*base a b c d 2 := by
    rw [os2,mo.2.2.1]; nlinarith only [h2.1]
  have ns1 : (P.first.map (newValue a b c d)).sum+newValue a b c d nu=
      newBase a b c d 1-2*((u:ℤ)+1)*base a b c d 0 := by
    rw [mn.1]; nlinarith only [h0.2.1,hnA]
  have ns2 : (P.first.map (newValue a b c d)).sum+newValue a b c d nu+
      (P.second.map (newValue a b c d)).sum+newValue a b c d nv=
      newBase a b c d 2-2*((r:ℤ)+1)*base a b c d 0-(p:ℤ)*newBase a b c d 1 := by
    rw [ns1,mn.2.1]; nlinarith only [h1.2.1,hnA]
  have ns3 : (P.first.map (newValue a b c d)).sum+newValue a b c d nu+
      (P.second.map (newValue a b c d)).sum+newValue a b c d nv+
      (P.third.map (newValue a b c d)).sum+newValue a b c d nw=
      newBase a b c d 3-2*base a b c d 0-(q:ℤ)*newBase a b c d 1-(w:ℤ)*newBase a b c d 2 := by
    rw [ns2,mn.2.2.1]; nlinarith only [h2.2.1,hnA]
  apply certificate_of_checks a b c d ha hb hc hd bs hinv hneg hpos
  · apply four_packet_checks (oldValue a b c d) (sourceMod a b c d/2)
      P.first P.second P.third P.fourth nu nv nw nx
    · simpa only [blocksWord,bs,List.append_assoc,List.cons_append,List.nil_append] using hto
    · constructor
      · rw [os1];exact s1
      · have hdoubled : 2*((P.first.map (oldValue a b c d)).sum)≤sourceMod a b c d-1 := by
          nlinarith only [os1,p1,h0.2.2.1]
        omega
    · constructor
      · rw [os2];exact s2
      · have hdoubled : 2*((P.first.map (oldValue a b c d)).sum+oldValue a b c d nu+(P.second.map (oldValue a b c d)).sum)≤sourceMod a b c d-1 := by
          nlinarith only [os2,p2,h1.2.2.1]
        omega
    · constructor
      · rw [os3];exact s3
      · have hdoubled : 2*((P.first.map (oldValue a b c d)).sum+oldValue a b c d nu+(P.second.map (oldValue a b c d)).sum+oldValue a b c d nv+(P.third.map (oldValue a b c d)).sum)≤sourceMod a b c d-1 := by
          nlinarith only [os3,p3,h2.2.2.1]
        omega
    · omega
  · change packetChecks (newValue a b c d) (sourceMod a b c d) 0
      [(P.first,nu),(P.second,nv),(P.third,nw),
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
      · have hdoubled : 2*((P.first.map (newValue a b c d)).sum+newValue a b c d nu+(P.second.map (newValue a b c d)).sum)≤2*sourceMod a b c d := by
          nlinarith only [ns2,z2,h1.2.2.2]
        omega
    · constructor
      · rw [ns3];exact t3
      · have hdoubled : 2*((P.first.map (newValue a b c d)).sum+newValue a b c d nu+(P.second.map (newValue a b c d)).sum+newValue a b c d nv+(P.third.map (newValue a b c d)).sum)≤2*sourceMod a b c d := by
          nlinarith only [ns3,z3,h2.2.2.2]
        omega
    · omega

end D5.S3.Combinatorics.Circle.FourNegative.UpperGap
