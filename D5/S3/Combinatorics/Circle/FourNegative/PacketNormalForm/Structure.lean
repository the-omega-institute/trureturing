/- GID: D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Structure
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Structure
   mirror-E: none(waiver:consumed-packet-structure)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Decomposition at negative physical labels without a positive tail. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Transport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm

private def blocksWord (bs : List (List ℕ × ℕ)) : List ℕ :=
  bs.flatMap (fun b => b.1 ++ [b.2])

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
      · refine ⟨([],x) :: bs, by simp [blocksWord, hb], ?_, ?_⟩
        · intro b hb'
          rcases List.mem_cons.mp hb' with h | h
          · subst b; simp
          · exact hp b h
        · simp [hn, hx]
      · cases bs with
        | nil => simp [blocksWord] at hb; exact (hxs hb.symm).elim
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
  induction pre with
  | nil => simp [insertAt]
  | cons x xs ih =>
    simpa [insertAt, Nat.add_assoc, List.take_succ_cons, List.drop_succ_cons] using
      congrArg (x :: ·) ih

end D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
