/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/Physical
   generality: I
   mirror-B: none(waiver:private-consumed-literal-physical-construction)
   mirror-E: none(waiver:private-consumed-literal-physical-construction)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical packet decoder with the actual front or preterminal fresh cut. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Source

/-! Physical packet decoder with the actual front or preterminal fresh cut. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
open SourceWidth PeriodicShortening RunFirstEarTransport
open PacketNormalForm (size base newBase oldValue newValue chainLength chainStart blocksWord insertAt)
open private sourceMod
  source_totals chain_values nextBase nextNewBase
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private mask full terminal full_split sub_split chain_inventory mask_mass mask_positive
  complement_mass split_mass terminal_double terminal_nonpositive source_odd native_balance
  full_double four_checks fresh_total freshAfter fresh_positive fresh_word mask_numeric_split
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddleCore
open private actual_nat_joint_iff
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private packetChecks withEar withEar_split
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private withEar_positive withEar_negatives
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Equivalence
open private packets_strip
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Source

private def marked (k : ℕ) (front : Bool) (e : Fin 4) (bs : List (List ℕ×ℕ)) :=
  if front then freshAfter k e.val bs else withEar k e.val bs

private theorem front_negatives (k e : ℕ) (bs : List (List ℕ×ℕ)) :
    (freshAfter k e bs).map Prod.snd=bs.map Prod.snd := by
  induction bs generalizing e with
  | nil => cases e <;> rfl
  | cons p ps ih => cases e <;> simp [freshAfter,ih]

private theorem blocks_append (bs cs : List (List ℕ×ℕ)) :
    blocksWord (bs++cs)=blocksWord bs++blocksWord cs := by
  induction bs with
  | nil => simp [blocksWord]
  | cons p ps ih => simp [blocksWord,ih,List.append_assoc]

private theorem marked_total (a b c : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c)
    (front : Bool) (e : Fin 4) (bs : List (List ℕ×ℕ)) (hlen : bs.length=4)
    (hp : (blocksWord bs).Perm (List.range (size a b c a))) :
    ((blocksWord (marked (size a b c a) front e bs)).map (newValue a b c a)).sum=0 := by
  have he : e.val<bs.length := by omega
  cases front
  · obtain ⟨pre,post,hw,hm⟩:=withEar_split (size a b c a) e.val bs he
    have hi : blocksWord (withEar (size a b c a) e.val bs)=
        insertAt (size a b c a) (blocksWord bs) pre.length := by
      rw [hw]
      simpa [insertAt] using hm
    simpa only [marked,ite_false,Bool.false_eq_true,hi] using
      fresh_total a b c a (blocksWord bs) pre.length ha hb hc ha hp
  · simpa only [marked,ite_true,fresh_word (size a b c a) e.val bs he] using
      fresh_total a b c a (blocksWord bs) (blocksWord (bs.take e.val)).length ha hb hc ha hp

private theorem realize_packets (a b c : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c)
    (front : Bool) (e : Fin 4) (bs : List (List ℕ×ℕ)) (hlen : bs.length=4)
    (hp : (blocksWord bs).Perm (List.range (size a b c a)))
    (hpos : ∀ pkt∈bs, ∀ i∈pkt.1, 0≤oldValue a b c a i ∧ 0≤newValue a b c a i)
    (hneg : ∀ pkt∈bs, oldValue a b c a pkt.2≤0 ∧ newValue a b c a pkt.2≤0)
    (ho : packetChecks (oldValue a b c a) (sourceMod a b c a/2) 0 bs)
    (hn : packetChecks (newValue a b c a) (sourceMod a b c a) 0
      (marked (size a b c a) front e bs)) :
    ∃ sigma : List (Fin (a+b+c+a)), ∃ j : ℕ, j≤a+b+c+a ∧
      OriginalOrder (a+b+c+a) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+a+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+a) sigma j) := by
  have he : e.val<bs.length := by omega
  have hear : 0≤newValue a b c a (size a b c a) := by
    have ht:=chain_values a b c a ha hb hc ha
    rw [ht.2.2.2]
    have hh:=(ht.1 0).1
    omega
  have hnewpos : ∀ pkt∈marked (size a b c a) front e bs, ∀ i∈pkt.1,
      0≤newValue a b c a i := by
    cases front
    · exact withEar_positive _ _ _ _ hear (fun p hp i hi => (hpos p hp i hi).2)
    · exact fresh_positive a b c a e.val bs ha hb hc ha (fun p hp i hi => (hpos p hp i hi).2)
  have hnewneg : ∀ pkt∈marked (size a b c a) front e bs,
      newValue a b c a pkt.2≤0 := by
    have hmap : (marked (size a b c a) front e bs).map Prod.snd=bs.map Prod.snd := by
      cases front
      · exact withEar_negatives _ _ _
      · exact front_negatives _ _ _
    intro pkt hpk
    have hh : pkt.2∈bs.map Prod.snd := by
      rw [←hmap]
      exact List.mem_map.mpr ⟨pkt,hpk,rfl⟩
    obtain ⟨p,hp,heq⟩:=List.mem_map.mp hh
    simpa only [←heq] using (hneg p hp).2
  have hold:=packets_strip a b c ha hb hc false bs
    (fun p hp i hi => (hpos p hp i hi).1) (fun p hp => (hneg p hp).1) ho
  have hnew:=packets_strip a b c ha hb hc true (marked (size a b c a) front e bs)
    hnewpos hnewneg hn
  apply (actual_nat_joint_iff a b c a ha hb hc ha).mpr
  cases front
  · obtain ⟨pre,post,hw,hm⟩:=withEar_split (size a b c a) e.val bs he
    have hcut : pre.length≤size a b c a := by
      have hh:=hp.length_eq
      rw [hw] at hh
      simp only [List.length_append,List.length_range] at hh
      omega
    refine ⟨blocksWord bs,hp,hold,pre.length,hcut,?_⟩
    rw [hw]
    simpa [marked,insertAt,hm] using hnew
  · have hcut : (blocksWord (bs.take e.val)).length≤size a b c a := by
      have hp' := hp.length_eq
      have happ : blocksWord (bs.take e.val)++blocksWord (bs.drop e.val)=blocksWord bs := by
        rw [←blocks_append,List.take_append_drop]
      have hh:=congrArg List.length happ
      simp only [List.length_append] at hh
      simp only [List.length_range] at hp'
      omega
    refine ⟨blocksWord bs,hp,hold,(blocksWord (bs.take e.val)).length,hcut,?_⟩
    simpa only [marked,ite_true,fresh_word (size a b c a) e.val bs he] using hnew

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
