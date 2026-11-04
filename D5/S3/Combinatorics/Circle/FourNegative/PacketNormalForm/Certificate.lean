/- GID: D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Certificate
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Certificate
   mirror-E: none(waiver:consumed-physical-certificate)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Finite physical partitions and four seam-peak pairs in each row. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets

/-! Certificate assumptions contain physical partitions and endpoint inequalities only. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open SourceWidth
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private packetChecks withEar from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets

private noncomputable def orderedPackets (bs : List (Finset ℕ × ℕ)) : List (List ℕ × ℕ) :=
  bs.map (fun b => (b.1.toList,b.2))

private def finiteChecks (mass : Finset ℕ → ℤ) (f : ℕ → ℤ) (C h : ℤ) :
    List (Finset ℕ × ℕ) → Prop
  | [] => True
  | (P,n) :: bs => 0 ≤ h + mass P + f n ∧ h + mass P ≤ C ∧
      finiteChecks mass f C (h + mass P + f n) bs

private def finiteEarChecks (mass : Finset ℕ → ℤ) (f : ℕ → ℤ) (C E h : ℤ) :
    ℕ → List (Finset ℕ × ℕ) → Prop
  | _, [] => True
  | 0, (P,n) :: bs => 0 ≤ h + (mass P + E) + f n ∧ h + (mass P + E) ≤ C ∧
      finiteChecks mass f C (h + (mass P + E) + f n) bs
  | e+1, (P,n) :: bs => 0 ≤ h + mass P + f n ∧ h + mass P ≤ C ∧
      finiteEarChecks mass f C E (h + mass P + f n) e bs

private structure DataCertificate (k : ℕ) (f g : ℕ → ℤ) (C D E : ℤ)
    (ng : List ℕ) (mass mass' : Finset ℕ → ℤ) where
  packets : List (Finset ℕ × ℕ)
  negativeOrder : (packets.map Prod.snd).Perm ng
  earSlot : Fin 4
  positiveLabels : ∀ b ∈ packets, ∀ i ∈ b.1, i < k ∧ i ∉ ng
  partition : (blocksWord (orderedPackets packets) : Multiset ℕ) = (List.range k : Multiset ℕ)
  oldEndpoints : finiteChecks mass f C 0 packets
  newEndpoints : finiteEarChecks mass' g D E 0 earSlot.val packets

private theorem finiteChecks_equiv (mass : Finset ℕ → ℤ) (f : ℕ → ℤ) (C h : ℤ)
    (bs : List (Finset ℕ × ℕ))
    (hm : ∀ b ∈ bs, mass b.1 = ∑ i ∈ b.1, f i) :
    finiteChecks mass f C h bs ↔ packetChecks f C h (orderedPackets bs) := by
  induction bs generalizing h with
  | nil => simp [finiteChecks,packetChecks,orderedPackets]
  | cons b bs ih =>
    rcases b with ⟨P,n⟩
    have hmass : mass P = (P.toList.map f).sum := by
      rw [hm (P,n) (by simp)]
      simpa using List.sum_toFinset f P.nodup_toList
    have hms : ∀ b ∈ bs, mass b.1 = ∑ i ∈ b.1, f i := fun b hb => hm b (by simp [hb])
    simp only [finiteChecks,orderedPackets,List.map_cons,packetChecks]
    rw [hmass]
    exact and_congr Iff.rfl (and_congr Iff.rfl (ih _ hms))

private theorem finiteEarChecks_equiv (mass : Finset ℕ → ℤ) (f : ℕ → ℤ)
    (C E h : ℤ) (ear e : ℕ) (hE : f ear = E)
    (bs : List (Finset ℕ × ℕ))
    (hm : ∀ b ∈ bs, mass b.1 = ∑ i ∈ b.1, f i) :
    finiteEarChecks mass f C E h e bs ↔
      packetChecks f C h (withEar ear e (orderedPackets bs)) := by
  induction bs generalizing h e with
  | nil => simp [finiteEarChecks,packetChecks,orderedPackets,withEar]
  | cons b bs ih =>
    rcases b with ⟨P,n⟩
    have hmass : mass P = (P.toList.map f).sum := by
      rw [hm (P,n) (by simp)]
      simpa using List.sum_toFinset f P.nodup_toList
    have hms : ∀ b ∈ bs, mass b.1 = ∑ i ∈ b.1, f i := fun b hb => hm b (by simp [hb])
    cases e with
    | zero =>
      simp only [finiteEarChecks,orderedPackets,List.map_cons,withEar,packetChecks,
        List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero,hE]
      rw [hmass]
      exact and_congr Iff.rfl (and_congr Iff.rfl (finiteChecks_equiv mass f C _ bs hms))
    | succ e =>
      simp only [finiteEarChecks,orderedPackets,List.map_cons,withEar,packetChecks]
      rw [hmass]
      exact and_congr Iff.rfl (and_congr Iff.rfl (ih _ e hms))

end D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
