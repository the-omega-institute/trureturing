/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/FirstEar
   generality: I
   mirror-B: none(waiver:owning-blueprint-scribe)
   mirror-E: none(waiver:private-consumed-first-positive-bank-transport)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Packet-strip consumption with the same physical word and literal first ear. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Certificate
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
open SourceWidth PeriodicShortening RunFirstEarTransport
open PacketNormalForm
open private Parameters Parameters.a Parameters.b Parameters.c Parameters.d
  Parameters.hc Parameters.hd Parameters.ha Parameters.hb from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Parameters
open private lengths offsets from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Supports
open private bank terminal blocks word physical_inventory positive_bank from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Physical
open private old_packet_checks new_packet_checks from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Certificate
open private size seed sourceMod base oldValue newValue negatives source_signs
  chain_values chain_signs chainLength from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private positive_block_strip from D5.S3.Combinatorics.Circle.ThreeBitSource
open private strip_append_iff from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Transport
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private packetChecks withEar strip_iff_packetChecks from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private label lift_order marked_word from
  D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

private theorem first_bank_ear_left {α : Type*} (f : α → ℤ) (C : ℤ)
    (ear : α) (P post : List α) (he : 0 ≤ f ear)
    (hp : ∀ i ∈ P, 0 ≤ f i)
    (h : InStrip f C 0 ((P++[ear])++post)) :
    InStrip f C 0 (ear::(P++post)) := by
  obtain ⟨hpos,hpost⟩ := (strip_append_iff f C 0 (P++[ear]) post).mp h
  have hpeak := (inStrip_prefix hpos (P++[ear]).length).2
  simp only [List.take_length,List.map_append,List.sum_append,List.map_singleton,
    List.sum_singleton,zero_add] at hpeak
  have hp' : ∀ i ∈ ear::P, 0 ≤ f i := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl|hi
    · exact he
    · exact hp i hi
  have hpos' : InStrip f C 0 (ear::P) :=
    positive_block_strip hp' (by omega) (by simpa [add_comm] using hpeak)
  have hpost' : InStrip f C (0+((ear::P).map f).sum) post := by
    simpa only [List.map_cons,List.sum_cons,List.map_append,List.sum_append,
      List.map_singleton,List.sum_singleton,zero_add,add_comm] using hpost
  simpa only [List.cons_append] using inStrip_append hpos' hpost'

private theorem certified_strips (p : Parameters) :
    InStrip (oldValue p.a p.b p.c p.d) (sourceMod p.a p.b p.c p.d/2) 0 (word p) ∧
    InStrip (newValue p.a p.b p.c p.d) (sourceMod p.a p.b p.c p.d) 0
      (size p.a p.b p.c p.d :: word p) := by
  have hc := p.hc; have hd := p.hd; have ha := p.ha; have hb := p.hb
  have hN : 0 ≤ sourceMod p.a p.b p.c p.d := by
    have h := (chain_values p.a p.b p.c p.d (by omega) (by omega) hc (by omega)).1 0
    omega
  have hear := (chain_values p.a p.b p.c p.d (by omega) (by omega) hc (by omega)).2.2.2
  have hE : 0 ≤ base p.a p.b p.c p.d 0 := by
    have h := (chain_values p.a p.b p.c p.d (by omega) (by omega) hc (by omega)).1 0
    omega
  have holdchecks := old_packet_checks p
  have hnewchecks := new_packet_checks p
  have hpos : ∀ b ∈ blocks p, ∀ i ∈ b.1,
      0 ≤ oldValue p.a p.b p.c p.d i ∧ 0 ≤ newValue p.a p.b p.c p.d i := by
    intro b hb i hi
    simp only [blocks,List.mem_cons,List.mem_singleton] at hb
    rcases hb with rfl|rfl|rfl|rfl
    all_goals
      have hp := positive_bank p _ i hi
      have hs := source_signs p.a p.b p.c p.d (by omega) (by omega) hc (by omega) i hp.1
      rw [if_neg hp.2] at hs
      exact ⟨hs.1.le,hs.2.le⟩
  have hneg (chain : Fin 4) :
      oldValue p.a p.b p.c p.d (terminal p chain) ≤ 0 ∧
      newValue p.a p.b p.c p.d (terminal p chain) ≤ 0 := by
    have hlen : lengths p chain+1 = chainLength p.a p.b p.c p.d chain := by
      fin_cases chain <;> dsimp [lengths,chainLength] <;> omega
    have hs := chain_signs p.a p.b p.c p.d (by omega) (by omega) hc (by omega)
      chain (lengths p chain) (by omega)
    rw [if_neg (by omega)] at hs
    exact ⟨hs.1.le,hs.2.le⟩
  have hnold : ∀ b ∈ blocks p, oldValue p.a p.b p.c p.d b.2 ≤ 0 := by
    intro b hb
    simp only [blocks,List.mem_cons,List.mem_singleton] at hb
    rcases hb with rfl|rfl|rfl|rfl
    all_goals exact (hneg _).1
  have hnnew : ∀ b ∈ withEar (size p.a p.b p.c p.d) 0 (blocks p),
      newValue p.a p.b p.c p.d b.2 ≤ 0 := by
    intro b hb
    simp only [blocks,withEar,List.mem_cons,List.mem_singleton] at hb
    rcases hb with rfl|rfl|rfl|rfl
    all_goals exact (hneg _).2
  have hpnew : ∀ b ∈ withEar (size p.a p.b p.c p.d) 0 (blocks p),
      ∀ i ∈ b.1, 0 ≤ newValue p.a p.b p.c p.d i := by
    intro b hb i hi
    simp only [blocks,withEar,List.mem_cons,List.mem_singleton] at hb
    rcases hb with rfl|rfl|rfl|rfl
    · rcases List.mem_append.mp hi with hi|hi
      · exact (hpos _ (by simp [blocks]) i hi).2
      · have he := List.mem_singleton.mp hi
        rw [he,hear]; exact hE
    all_goals exact (hpos _ (by simp [blocks]) i hi).2
  have hold := (strip_iff_packetChecks _ _ _ _ ⟨by omega,by omega⟩
    (fun b hb i hi => (hpos b hb i hi).1) hnold).mpr holdchecks
  have hnew := (strip_iff_packetChecks _ _ _ _ ⟨by omega,hN⟩ hpnew hnnew).mpr hnewchecks
  refine ⟨hold,?_⟩
  apply first_bank_ear_left (newValue p.a p.b p.c p.d) (sourceMod p.a p.b p.c p.d)
    (size p.a p.b p.c p.d) (bank p 0)
    (terminal p 0 :: blocksWord [(bank p 1,terminal p 3),(bank p 2,terminal p 2),(bank p 3,terminal p 1)])
    (by rw [hear]; exact hE) (fun i hi => (hpos _ (by simp [blocks]) i hi).2)
  simpa [blocks,withEar,blocksWord,List.append_assoc] using hnew

private theorem physical_first_ear (p : Parameters) :
    ∃ sigma : List (Fin (p.a+p.b+p.c+p.d)),
      OriginalOrder (p.a+p.b+p.c+p.d) (1+2^p.a+2^(p.a+p.b)+2^(p.a+p.b+p.c)) sigma ∧
      OriginalOrder (p.a+p.b+p.c+p.d+1) (2*(1+2^p.a+2^(p.a+p.b)+2^(p.a+p.b+p.c)))
        (earWord (p.a+p.b+p.c+p.d) sigma 0) := by
  have hc := p.hc; have hd := p.hd; have ha := p.ha; have hb := p.hb
  let k := size p.a p.b p.c p.d
  let A := seed p.a p.b p.c
  have hk : 0 < k := by dsimp [k,size]; omega
  have hmod : modulus k = sourceMod p.a p.b p.c p.d := by
    dsimp [k,size,modulus,sourceMod]; ring
  have hmod' : modulus (k+1) = 2*sourceMod p.a p.b p.c p.d+1 := by
    dsimp [k,size,modulus,sourceMod]; ring
  have hhalf : modulus (k+1)/2 = sourceMod p.a p.b p.c p.d := by rw [hmod']; omega
  have hseed : (A : ℤ) = base p.a p.b p.c p.d 0 := by
    dsimp [A,seed,base]; push_cast; ring
  have hseed' : ((2*A : ℕ) : ℤ) = 2*base p.a p.b p.c p.d 0 := by push_cast; rw [hseed]
  obtain ⟨hold,hnew⟩ := certified_strips p
  have hp := physical_inventory p
  have hp' : (k::word p).Perm (List.range (k+1)) := by
    apply (List.perm_append_singleton k (word p)).symm.trans
    simpa only [List.range_succ] using hp.append_right [k]
  have hzero := ThreeNegativeEqualOuterSourceBridge.source_zero k A (by dsimp [k,size]; omega)
  have hzero' := ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*A) (by dsimp [k,size]; omega)
  refine ⟨(word p).map (label k hk),?_,?_⟩
  · apply lift_order k A hk (word p) hp
    · simpa only [hmod,hseed,oldValue] using hold
    · exact hzero
  · have he := marked_word k 0 hk [] (word p) rfl (by simpa using hp)
    simp only [List.nil_append,List.map_nil] at he
    rw [he]
    apply lift_order (k+1) (2*A) (by omega) (k::word p) hp'
    · simpa only [hhalf,hmod',hseed',newValue] using hnew
    · exact hzero'

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
