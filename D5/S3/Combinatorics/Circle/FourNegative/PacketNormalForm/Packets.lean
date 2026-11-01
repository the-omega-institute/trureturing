/- GID: D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Packets
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Packets
   mirror-E: none(waiver:consumed-packet-endpoints)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Endpoint checks and right-normalization for physical packets. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure

/-! Each packet contributes one seam and one peak, independently of its internal order. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open SourceWidth
open private positive_block_strip from D5.S3.Combinatorics.Circle.ThreeBitSource
open private strip_append_iff from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Transport
open private blocksWord insertAt insertAt_add slide_packet
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure

private def packetChecks (f : ℕ → ℤ) (C h : ℤ) : List (List ℕ × ℕ) → Prop
  | [] => True
  | (P,n) :: bs =>
      0 ≤ h + (P.map f).sum + f n ∧ h + (P.map f).sum ≤ C ∧
      packetChecks f C (h + (P.map f).sum + f n) bs

private theorem strip_iff_packetChecks (f : ℕ → ℤ) (C h : ℤ)
    (bs : List (List ℕ × ℕ)) (hh : 0 ≤ h ∧ h ≤ C)
    (hp : ∀ b ∈ bs, ∀ i ∈ b.1, 0 ≤ f i)
    (hn : ∀ b ∈ bs, f b.2 ≤ 0) :
    InStrip f C h (blocksWord bs) ↔ packetChecks f C h bs := by
  induction bs generalizing h with
  | nil => simp [blocksWord, packetChecks, InStrip, hh]
  | cons b bs ih =>
    rcases b with ⟨P,n⟩
    have hP : ∀ i ∈ P, 0 ≤ f i := hp (P,n) (by simp)
    have hneg : f n ≤ 0 := hn (P,n) (by simp)
    have hps : ∀ b ∈ bs, ∀ i ∈ b.1, 0 ≤ f i := fun b hb => hp b (by simp [hb])
    have hns : ∀ b ∈ bs, f b.2 ≤ 0 := fun b hb => hn b (by simp [hb])
    have hsum : 0 ≤ (P.map f).sum := by simpa using List.sum_le_sum hP
    change InStrip f C h (P ++ n :: blocksWord bs) ↔ _
    constructor
    · intro hw
      obtain ⟨hPstrip, hstep⟩ := (strip_append_iff f C h P _).mp hw
      have hpeak := (inStrip_prefix hPstrip P.length).2
      simp only [List.take_length] at hpeak
      have hpost := inStrip_prefix hstep.2.2 0
      simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero] at hpost
      exact ⟨hpost.1, hpeak, (ih _ hpost hps hns).mp hstep.2.2⟩
    · rintro ⟨hpost, hpeak, hchecks⟩
      have hnext : 0 ≤ h + (P.map f).sum + f n ∧
          h + (P.map f).sum + f n ≤ C := ⟨hpost, by omega⟩
      apply inStrip_append (positive_block_strip (l := P) hP hh.1 hpeak)
      exact ⟨by omega, hpeak, (ih _ hnext hps hns).mpr hchecks⟩

private def withEar (ear : ℕ) : ℕ → List (List ℕ × ℕ) → List (List ℕ × ℕ)
  | _, [] => []
  | 0, (P,n) :: bs => (P ++ [ear],n) :: bs
  | e+1, b :: bs => b :: withEar ear e bs

private theorem normalize_blocks (f : ℕ → ℤ) (C h : ℤ) (ear : ℕ)
    (bs : List (List ℕ × ℕ)) (j : ℕ) (hj : j < (blocksWord bs).length)
    (he : 0 ≤ f ear) (hp : ∀ b ∈ bs, ∀ i ∈ b.1, 0 ≤ f i)
    (hw : InStrip f C h (insertAt ear (blocksWord bs) j)) :
    ∃ e : ℕ, e < bs.length ∧ InStrip f C h (blocksWord (withEar ear e bs)) := by
  induction bs generalizing h j with
  | nil => simp [blocksWord] at hj
  | cons b bs ih =>
    rcases b with ⟨P,n⟩
    have hP : ∀ i ∈ P, 0 ≤ f i := hp (P,n) (by simp)
    have hps : ∀ b ∈ bs, ∀ i ∈ b.1, 0 ≤ f i := fun b hb => hp b (by simp [hb])
    have heword : blocksWord ((P,n) :: bs) = P ++ n :: blocksWord bs := by
      simp [blocksWord]
    rw [heword] at hw hj
    by_cases hcut : j ≤ P.length
    · have ht := slide_packet f C h ear [] P (n :: blocksWord bs) j hcut he hP
        (by simpa using hw)
      refine ⟨0, by simp, ?_⟩
      simpa [withEar, blocksWord, insertAt, List.take_append_of_le_length (le_refl P.length),
        List.drop_append_of_le_length (le_refl P.length), List.append_assoc] using ht
    · let pre := P ++ [n]
      let r := j - pre.length
      have hjrel : j = pre.length + r := by simp [r,pre]; omega
      have hjr : r < (blocksWord bs).length := by
        simp only [List.length_append, List.length_cons] at hj
        dsimp [r,pre]; simp; omega
      have hw' : InStrip f C h (pre ++ insertAt ear (blocksWord bs) r) := by
        have heq : P ++ n :: blocksWord bs = pre ++ blocksWord bs := by simp [pre]
        rw [heq, hjrel, insertAt_add] at hw
        exact hw
      obtain ⟨hpre, hrest⟩ := (strip_append_iff f C h pre _).mp hw'
      obtain ⟨e, he', hnew⟩ := ih _ r hjr hps hrest
      refine ⟨e+1, by simp; omega, ?_⟩
      have hh := inStrip_append hpre hnew
      simpa [withEar, blocksWord, pre, List.append_assoc] using hh

private theorem withEar_split (ear e : ℕ) (bs : List (List ℕ × ℕ))
    (he : e < bs.length) :
    ∃ pre post, blocksWord bs = pre ++ post ∧
      blocksWord (withEar ear e bs) = pre ++ ear :: post := by
  induction bs generalizing e with
  | nil => simp at he
  | cons b bs ih =>
    rcases b with ⟨P,n⟩
    cases e with
    | zero => exact ⟨P,n :: blocksWord bs,by simp [blocksWord],by simp [blocksWord,withEar]⟩
    | succ e =>
      obtain ⟨pre,post,hword,hmarked⟩ := ih e (by simpa using he)
      refine ⟨P ++ n :: pre,post,?_,?_⟩
      · change P ++ n :: blocksWord bs = (P ++ n :: pre) ++ post
        rw [hword]
        simp only [List.append_assoc,List.cons_append]
      · change P ++ n :: blocksWord (withEar ear e bs) = (P ++ n :: pre) ++ ear :: post
        rw [hmarked]
        simp only [List.append_assoc,List.cons_append]

end D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
