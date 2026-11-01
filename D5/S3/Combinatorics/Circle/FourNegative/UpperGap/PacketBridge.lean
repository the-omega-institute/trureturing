/- GID: D5/S3/Combinatorics/Circle/FourNegative/UpperGap/PacketBridge
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-packet-integration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact actual-source transport for explicitly constructed boundary packets. -/
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.Rounding
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.SourceMasses

/-! Exact physical transport of constructed packet checks in both centered rows. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.UpperGap
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private size sourceMod base oldValue newValue negatives chain_values source_signs
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private blocksWord insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private packetChecks withEar strip_iff_packetChecks withEar_split
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private withEar_positive withEar_negatives
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Equivalence
open private actual_nat_joint_iff
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint

private theorem certificate_of_checks (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (bs : List (List ℕ × ℕ))
    (hinv : (blocksWord bs).Perm (List.range (size a b c d)))
    (hneg : (bs.map Prod.snd).Perm (negatives a b c d))
    (hpos : ∀ block∈bs, ∀ i∈block.1, i<size a b c d ∧ i∉negatives a b c d)
    (hold : packetChecks (oldValue a b c d) (sourceMod a b c d/2) 0 bs)
    (hnew : packetChecks (newValue a b c d) (sourceMod a b c d) 0
      (withEar (size a b c d) 3 bs)) : Nonempty (Certificate a b c d) := by
  have hframe := chain_values a b c d ha hb hc hd
  have hN : 0<sourceMod a b c d := by have := hframe.1 0; omega
  have hA : 0<base a b c d 0 := by have := hframe.1 0; omega
  have hlen : bs.length=4 := by
    have he := hneg.length_eq
    simpa [negatives] using he
  have hnegative (n : ℕ) (hn : n∈bs.map Prod.snd) :
      oldValue a b c d n≤0 ∧ newValue a b c d n≤0 := by
    have hn' := hneg.mem_iff.mp hn
    have hk : n<size a b c d := by
      simp only [negatives,size,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hn'
      dsimp [size]
      omega
    have hs := source_signs a b c d ha hb hc hd n hk
    rw [if_pos hn'] at hs
    exact ⟨hs.1.le,hs.2.le⟩
  have hpold : ∀ block∈bs, ∀ i∈block.1, 0≤oldValue a b c d i := by
    intro block hb' i hi
    have h := hpos block hb' i hi
    have hs := source_signs a b c d ha hb hc hd i h.1
    rw [if_neg h.2] at hs
    exact hs.1.le
  have hpnew : ∀ block∈bs, ∀ i∈block.1, 0≤newValue a b c d i := by
    intro block hb' i hi
    have h := hpos block hb' i hi
    have hs := source_signs a b c d ha hb hc hd i h.1
    rw [if_neg h.2] at hs
    exact hs.2.le
  have hsold := (strip_iff_packetChecks (oldValue a b c d) (sourceMod a b c d/2) 0 bs
    ⟨by omega,by omega⟩ hpold
    (fun block hb' => (hnegative block.2 (List.mem_map.mpr ⟨block,hb',rfl⟩)).1)).mpr hold
  have hear : 0≤newValue a b c d (size a b c d) := by
    rw [hframe.2.2.2]
    omega
  have hpn := withEar_positive (newValue a b c d) (size a b c d) 3 bs hear hpnew
  have hnn : ∀ block∈withEar (size a b c d) 3 bs, newValue a b c d block.2≤0 := by
    intro block hb'
    have hm : block.2∈(withEar (size a b c d) 3 bs).map Prod.snd :=
      List.mem_map.mpr ⟨block,hb',rfl⟩
    rw [withEar_negatives] at hm
    exact (hnegative block.2 hm).2
  have hsnew := (strip_iff_packetChecks (newValue a b c d) (sourceMod a b c d) 0
    (withEar (size a b c d) 3 bs) ⟨by omega,by omega⟩ hpn hnn).mpr hnew
  obtain ⟨pre,post,hword,hmarked⟩ := withEar_split (size a b c d) 3 bs (by omega)
  have hj : pre.length≤size a b c d := by
    have he := hinv.length_eq
    rw [hword] at he
    simp only [List.length_append,List.length_range] at he
    omega
  have hins : insertAt (size a b c d) (blocksWord bs) pre.length =
      pre ++ size a b c d :: post := by
    rw [hword]
    simp [insertAt]
  apply (actual_four_packet_iff a b c d ha hb hc hd).mp
  apply (actual_nat_joint_iff a b c d ha hb hc hd).mpr
  refine ⟨blocksWord bs,hinv,hsold,pre.length,hj,?_⟩
  rw [hins,←hmarked]
  exact hsnew

end D5.S3.Combinatorics.Circle.FourNegative.UpperGap
