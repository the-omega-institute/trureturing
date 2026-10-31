/- GID: D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Structure
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Structure
   mirror-E: none(waiver:consumed-packet-structure)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Decomposition at negative physical labels without a positive tail. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Transport

/-! Physical decomposition and literal packet-end insertion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open SourceWidth
open private slide_ear_right from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Transport

private def blocksWord : List (List ℕ × ℕ) → List ℕ
  | [] => []
  | (P,n) :: bs => P ++ n :: blocksWord bs

private theorem blocksWord_flatMap (bs : List (List ℕ × ℕ)) :
    blocksWord bs = bs.flatMap (fun b => b.1 ++ [b.2]) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [blocksWord,List.flatMap_cons,ih,List.append_assoc]

private theorem split_packets (bad : ℕ → Prop) [DecidablePred bad] (l : List ℕ)
    (hlast : ∀ pre x, l = pre ++ [x] → bad x) :
    ∃ bs : List (List ℕ × ℕ), blocksWord bs = l ∧
      (∀ b ∈ bs, ∀ x ∈ b.1, ¬ bad x) ∧
      bs.map Prod.snd = l.filter (fun x => decide (bad x)) := by
  induction l with
  | nil => exact ⟨[], rfl, by simp, rfl⟩
  | cons x xs ih =>
    by_cases hxs : xs = []
    · subst xs
      have hx := hlast [] x rfl
      refine ⟨[([],x)], rfl, by simp, ?_⟩
      simp [hx]
    · have htail : ∀ pre y, xs = pre ++ [y] → bad y := by
        intro pre y he
        apply hlast (x :: pre) y
        simp [he]
      obtain ⟨bs, hb, hp, hn⟩ := ih htail
      by_cases hx : bad x
      · refine ⟨([],x) :: bs, by change x :: blocksWord bs = x :: xs; rw [hb], ?_, ?_⟩
        · intro b hb'
          rcases List.mem_cons.mp hb' with h | h
          · subst b; simp
          · exact hp b h
        · simp [hn, hx]
      · cases bs with
        | nil => simp [blocksWord] at hb; exact (hxs hb).elim
        | cons b bs =>
          rcases b with ⟨P,n⟩
          refine ⟨(x :: P,n) :: bs, ?_, ?_, ?_⟩
          · simpa [blocksWord] using congrArg (x :: ·) hb
          · intro b hb' y hy
            rcases List.mem_cons.mp hb' with h | h
            · subst b
              rcases List.mem_cons.mp hy with h | h
              · simpa [h] using hx
              · exact hp (P,n) (by simp) y h
            · exact hp b (by simp [h]) y hy
          · simpa [hx] using hn

private def insertAt (ear : ℕ) (l : List ℕ) (j : ℕ) : List ℕ :=
  l.take j ++ ear :: l.drop j

private theorem insertAt_add (ear : ℕ) (pre post : List ℕ) (j : ℕ) :
    insertAt ear (pre ++ post) (pre.length + j) = pre ++ insertAt ear post j := by
  unfold insertAt
  rw [List.take_length_add_append, List.drop_length_add_append]
  rw [List.append_assoc]

private theorem slide_packet (f : ℕ → ℤ) (B h : ℤ) (ear : ℕ)
    (pre P post : List ℕ) (j : ℕ) (hj : j ≤ P.length)
    (he : 0 ≤ f ear) (hp : ∀ i ∈ P, 0 ≤ f i)
    (hw : InStrip f B h (insertAt ear (pre ++ P ++ post) (pre.length+j))) :
    InStrip f B h (insertAt ear (pre ++ P ++ post) (pre.length+P.length)) := by
  have hleft : insertAt ear (pre ++ P ++ post) (pre.length+j) =
      (pre ++ P.take j) ++ ear :: (P.drop j ++ post) := by
    rw [List.append_assoc, insertAt_add]
    simp only [insertAt, List.take_append_of_le_length hj,
      List.drop_append_of_le_length hj, List.append_assoc]
  have hright : insertAt ear (pre ++ P ++ post) (pre.length+P.length) =
      pre ++ P ++ ear :: post := by
    rw [List.append_assoc, insertAt_add]
    simp [insertAt, List.take_append_of_le_length (le_refl P.length),
      List.drop_append_of_le_length (le_refl P.length), List.append_assoc]
  rw [hleft] at hw
  rw [hright]
  have hpos : ∀ i ∈ P.drop j, 0 ≤ f i :=
    fun i hi => hp i (List.mem_of_mem_drop hi)
  have hh := slide_ear_right f B h ear (pre ++ P.take j) (P.drop j) post he hpos hw
  simpa only [List.append_assoc pre (P.take j) (P.drop j), List.take_append_drop] using hh

end D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
