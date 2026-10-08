/- GID: D5/S3/Combinatorics/DyckValleys/ValleyBargraphBijection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DyckValleys/ValleyBargraphBijection
   mirror-E: none(waiver:recursive-statistic-preserving-bijection)
   anchors: []
   utility: none
   digest: A common five-case code gives unique Dyck and bargraph representations. -/

import D5.S3.Combinatorics.DyckValleys.ValleyBargraphDyck

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DyckValleys.ValleyBargraph

/-- The five cases of the first-return and first-height-one decompositions. -/
inductive Code where
  | atom : Code
  | left : Code → Code
  | elevate : Code → Code
  | right : Code → Code
  | join : Code → Code → Code

namespace Code

/-- Render the first-return construction as an actual Mathlib Dyck word. -/
def word : Code → DyckWord
  | atom => (0 : DyckWord).nest + (0 : DyckWord).nest
  | left q => (0 : DyckWord).nest + word q
  | elevate p => (word p).nest
  | right p => (word p).nest + (0 : DyckWord).nest
  | join p q => (word p).nest + word q

/-- Render the corresponding first-height-one construction. -/
def height : Code → List ℕ
  | atom => [1]
  | left q => 1 :: height q
  | elevate p => (height p).map Nat.succ
  | right p => (height p).map Nat.succ ++ [1]
  | join p q => (height p).map Nat.succ ++ [1] ++ height q

/-- Every recursive Dyck rendering has semilength at least two. -/
theorem word_semilength (c : Code) : 2 ≤ (word c).semilength := by
  induction c with
  | atom => simp [word]
  | left q ih => simp only [word, DyckWord.semilength_add,
      DyckWord.semilength_nest, DyckWord.semilength_zero]; omega
  | elevate p ih => simp only [word, DyckWord.semilength_nest]; omega
  | right p ih => simp only [word, DyckWord.semilength_add,
      DyckWord.semilength_nest, DyckWord.semilength_zero]; omega
  | join p q ip iq => simp only [word, DyckWord.semilength_add,
      DyckWord.semilength_nest]; omega

end Code
end D5.S3.Combinatorics.DyckValleys.ValleyBargraph

namespace D5.S3.Combinatorics.DyckValleys.ValleyBargraph

open ValleyBargraphDefs

namespace Code

/-- Unique first returns recover all five constructor choices and their children. -/
theorem words_injective : Function.Injective word := by
  have nonzero (c : Code) : word c ≠ 0 := by
    intro h
    have hs := word_semilength c
    have he := congrArg DyckWord.semilength h
    simp only [DyckWord.semilength_zero] at he
    omega
  have nonsingle (c : Code) : word c ≠ (0 : DyckWord).nest := by
    intro h
    have hs := word_semilength c
    have he := congrArg DyckWord.semilength h
    simp only [DyckWord.semilength_nest, DyckWord.semilength_zero] at he
    omega
  intro c
  induction c with
  | atom =>
    intro d h
    have hp := congrArg DyckWord.insidePart h
    have hq := congrArg DyckWord.outsidePart h
    cases d <;> simp only [word, DyckWord.insidePart_add DyckWord.nest_ne_zero,
      DyckWord.outsidePart_add DyckWord.nest_ne_zero, DyckWord.insidePart_nest,
      DyckWord.outsidePart_nest, zero_add] at hp hq
    all_goals first
      | rfl
      | exact (nonzero _ hp.symm).elim
      | exact (nonsingle _ hq.symm).elim
  | left q iq =>
    intro d h
    have hp := congrArg DyckWord.insidePart h
    have hq := congrArg DyckWord.outsidePart h
    cases d <;> simp only [word, DyckWord.insidePart_add DyckWord.nest_ne_zero,
      DyckWord.outsidePart_add DyckWord.nest_ne_zero, DyckWord.insidePart_nest,
      DyckWord.outsidePart_nest, zero_add] at hp hq
    all_goals first
      | exact congrArg left (iq hq)
      | exact (nonzero _ hp.symm).elim
      | exact (nonzero _ hq).elim
      | exact (nonsingle _ hq).elim
  | elevate p ip =>
    intro d h
    have hp := congrArg DyckWord.insidePart h
    have hq := congrArg DyckWord.outsidePart h
    cases d <;> simp only [word, DyckWord.insidePart_add DyckWord.nest_ne_zero,
      DyckWord.outsidePart_add DyckWord.nest_ne_zero, DyckWord.insidePart_nest,
      DyckWord.outsidePart_nest, zero_add] at hp hq
    all_goals first
      | exact congrArg elevate (ip hp)
      | exact (nonzero _ hp).elim
      | exact (nonzero _ hq.symm).elim
      | exact (DyckWord.nest_ne_zero hq.symm).elim
  | right p ip =>
    intro d h
    have hp := congrArg DyckWord.insidePart h
    have hq := congrArg DyckWord.outsidePart h
    cases d <;> simp only [word, DyckWord.insidePart_add DyckWord.nest_ne_zero,
      DyckWord.outsidePart_add DyckWord.nest_ne_zero, DyckWord.insidePart_nest,
      DyckWord.outsidePart_nest, zero_add] at hp hq
    all_goals first
      | exact congrArg right (ip hp)
      | exact (nonzero _ hp).elim
      | exact (nonsingle _ hq.symm).elim
      | exact (DyckWord.nest_ne_zero hq).elim
  | join p q ip iq =>
    intro d h
    have hp := congrArg DyckWord.insidePart h
    have hq := congrArg DyckWord.outsidePart h
    cases d <;> simp only [word, DyckWord.insidePart_add DyckWord.nest_ne_zero,
      DyckWord.outsidePart_add DyckWord.nest_ne_zero, DyckWord.insidePart_nest,
      DyckWord.outsidePart_nest, zero_add] at hp hq
    all_goals first
      | exact congrArg₂ join (ip hp) (iq hq)
      | exact (nonzero _ hp).elim
      | exact (nonzero _ hq).elim
      | exact (nonsingle _ hq).elim

/-- Structural induction verifies avoidance in all five constructors. -/
theorem words_sound (c : Code) : AvoidsUUDD (word c) := by
  have nonsingle (c : Code) : word c ≠ (0 : DyckWord).nest := by
    intro h
    have hs := word_semilength c
    have he := congrArg DyckWord.semilength h
    simp only [DyckWord.semilength_nest, DyckWord.semilength_zero] at he
    omega
  have hzero : AvoidsUUDD (0 : DyckWord) := by
    intro h
    have hl := h.length_le
    change 4 ≤ 0 at hl
    omega
  have hone : AvoidsUUDD (0 : DyckWord).nest := by
    intro h
    have hl := h.length_le
    change 4 ≤ 2 at hl
    omega
  induction c with
  | atom =>
    exact (avoids_nest_add _ _).mpr ⟨hzero, hone, Ne.symm DyckWord.nest_ne_zero⟩
  | left q iq =>
    exact (avoids_nest_add _ _).mpr ⟨hzero, iq, Ne.symm DyckWord.nest_ne_zero⟩
  | elevate p ip =>
    simpa [word] using (avoids_nest_add (word p) 0).mpr ⟨ip, hzero, nonsingle p⟩
  | right p ip =>
    exact (avoids_nest_add _ _).mpr ⟨ip, hone, nonsingle p⟩
  | join p q ip iq =>
    exact (avoids_nest_add _ _).mpr ⟨ip, iq, nonsingle p⟩

/-- Strong induction on semilength constructs the unique five-case representation. -/
theorem words_surjective (w : DyckWord) (hn : 2 ≤ w.semilength)
    (ha : AvoidsUUDD w) : ∃ c, word c = w := by
  have zero_of_size (v : DyckWord) (hv : v.semilength = 0) : v = 0 := by
    apply DyckWord.toList_eq_nil.mp
    apply List.eq_nil_of_length_eq_zero
    have h := v.two_mul_semilength_eq_length
    omega
  have short (v : DyckWord) (hv : v.semilength < 2) :
      v = 0 ∨ v = (0 : DyckWord).nest := by
    by_cases hz : v = 0
    · exact Or.inl hz
    · have hs := DyckWord.semilength_insidePart_add_semilength_outsidePart_add_one hz
      have hp : v.insidePart = 0 := zero_of_size _ (by omega)
      have hq : v.outsidePart = 0 := zero_of_size _ (by omega)
      exact Or.inr (by
        simpa [hp, hq] using (DyckWord.nest_insidePart_add_outsidePart hz).symm)
  generalize he : w.semilength = n at hn
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    have hz : w ≠ 0 := by intro h; subst w; simp at he; omega
    have hw := DyckWord.nest_insidePart_add_outsidePart hz
    have hd : AvoidsUUDD w.insidePart ∧ AvoidsUUDD w.outsidePart ∧
        w.insidePart ≠ (0 : DyckWord).nest :=
      (avoids_nest_add _ _).mp (hw.symm ▸ ha)
    have hp_lt : w.insidePart.semilength < n := by
      simpa [he] using DyckWord.semilength_insidePart_lt hz
    have hq_lt : w.outsidePart.semilength < n := by
      simpa [he] using DyckWord.semilength_outsidePart_lt hz
    by_cases hp : w.insidePart = 0
    · by_cases hq : w.outsidePart = (0 : DyckWord).nest
      · exact ⟨atom, by simpa [word, hp, hq] using hw⟩
      · have hq_size : 2 ≤ w.outsidePart.semilength := by
          by_contra h
          rcases short w.outsidePart (by omega) with hh | hh
          · have hs := DyckWord.semilength_insidePart_add_semilength_outsidePart_add_one hz
            simp only [hp, hh, DyckWord.semilength_zero] at hs
            omega
          · exact hq hh
        obtain ⟨cq, hcq⟩ := ih _ hq_lt _ hd.2.1 rfl hq_size
        exact ⟨left cq, by simpa [word, hcq, hp] using hw⟩
    · have hp_size : 2 ≤ w.insidePart.semilength := by
        by_contra h
        rcases short w.insidePart (by omega) with hh | hh
        · exact hp hh
        · exact hd.2.2 hh
      obtain ⟨cp, hcp⟩ := ih _ hp_lt _ hd.1 rfl hp_size
      by_cases hq : w.outsidePart = 0
      · exact ⟨elevate cp, by simpa [word, hcp, hq] using hw⟩
      · by_cases hq_one : w.outsidePart = (0 : DyckWord).nest
        · exact ⟨right cp, by simpa [word, hcp, hq_one] using hw⟩
        · have hq_size : 2 ≤ w.outsidePart.semilength := by
            by_contra h
            rcases short w.outsidePart (by omega) with hh | hh
            · exact hq hh
            · exact hq_one hh
          obtain ⟨cq, hcq⟩ := ih _ hq_lt _ hd.2.1 rfl hq_size
          exact ⟨join cp cq, by simpa [word, hcp, hcq] using hw⟩

end Code
end D5.S3.Combinatorics.DyckValleys.ValleyBargraph

namespace D5.S3.Combinatorics.DyckValleys.ValleyBargraph

open ValleyBargraphDefs
open Code

/-- The five constructions preserve positive heights and the two required statistics. -/
theorem heights_sound (c : Code) :
    IsBargraph (height c) ∧ semiperimeter (height c) = (word c).semilength ∧
      (height c).length = valleys (word c) := by
  have nonzero (c : Code) : word c ≠ 0 := by
    intro h
    have hs := word_semilength c
    have he := congrArg DyckWord.semilength h
    simp only [DyckWord.semilength_zero] at he
    omega
  have vzero : valleys (0 : DyckWord) = 0 := rfl
  have vone : valleys (0 : DyckWord).nest = 0 := rfl
  have wrapped (p : DyckWord) : valleys p.nest = valleys p := by
    simpa [vzero] using valleys_nest_add p 0
  have liftRise : ∀ A : List ℕ, ascent (A.map Nat.succ) = ascent A := by
    intro A
    induction A with
    | nil => rfl
    | cons a t ih =>
      cases t with
      | nil => rfl
      | cons b t => simpa [ascent, Nat.succ_sub_succ_eq_sub] using ih
  have separator : ∀ A B : List ℕ, A ≠ [] →
      ascent (A.map Nat.succ ++ 1 :: B) = ascent A + ascent (1 :: B) := by
    intro A
    induction A with
    | nil => simp
    | cons a t ih =>
      intro B _
      cases t with
      | nil => simp [ascent]
      | cons b t =>
        simpa [ascent, Nat.succ_sub_succ_eq_sub, Nat.add_assoc] using
          congrArg (fun x => (b - a) + x) (ih B (by simp))
  have leading : ∀ B : List ℕ, IsBargraph B →
      semiperimeter (1 :: B) = 1 + semiperimeter B := by
    intro B hB
    cases B with
    | nil => exact (hB.1 rfl).elim
    | cons b t =>
      have hb := hB.2 b (by simp)
      simp only [semiperimeter, List.length_cons, List.headD_cons, ascent]
      omega
  have lifted : ∀ A : List ℕ, A ≠ [] →
      semiperimeter (A.map Nat.succ) = 1 + semiperimeter A := by
    intro A hA
    cases A with
    | nil => exact (hA rfl).elim
    | cons a t =>
      simp only [semiperimeter, List.length_map]
      rw [liftRise]
      simp
      omega
  have separated : ∀ A B : List ℕ, A ≠ [] →
      semiperimeter (A.map Nat.succ ++ 1 :: B) =
        semiperimeter A + semiperimeter (1 :: B) := by
    intro A B hA
    cases A with
    | nil => exact (hA rfl).elim
    | cons a t =>
      simp only [semiperimeter, List.length_append, List.length_map,
        List.length_cons, List.headD_cons, List.map_cons, List.cons_append]
      have hs := separator (a :: t) B (by simp)
      simp only [List.map_cons, List.cons_append] at hs
      rw [hs]
      omega
  induction c with
  | atom => simp [height, word, IsBargraph, semiperimeter, ascent, valleys_nest_add,
      vzero, vone]
  | left q ih =>
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨by simp [height], ?_⟩
      intro h hh
      simp only [height, List.mem_cons] at hh
      rcases hh with rfl | hh
      · omega
      · exact ih.1.2 h hh
    · rw [height, leading _ ih.1, ih.2.1]; simp [word]
    · simp [height, word, valleys_nest_add, vzero, ih.2.2, nonzero, Nat.add_comm]
  | elevate p ih =>
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨by simpa [height] using ih.1.1, ?_⟩
      intro h hh
      rcases List.mem_map.mp hh with ⟨a, _, rfl⟩
      omega
    · rw [height, lifted _ ih.1.1, ih.2.1]; simp [word, Nat.add_comm]
    · simp [height, word, wrapped, ih.2.2]
  | right p ih =>
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · simp [height]
      · intro h hh
        simp only [height, List.mem_append, List.mem_map, List.mem_singleton] at hh
        rcases hh with ⟨a, _, rfl⟩ | rfl <;> omega
    · change semiperimeter ((height p).map Nat.succ ++ 1 :: []) = _
      rw [separated _ [] ih.1.1, ih.2.1]
      simp [semiperimeter, ascent, word]
    · simp [height, word, valleys_nest_add, vone, ih.2.2, Nat.add_comm]
  | join p q ip iq =>
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · simp [height]
      · intro h hh
        simp only [height, List.mem_append, List.mem_map, List.mem_singleton] at hh
        rcases hh with (⟨a, _, rfl⟩ | rfl) | hh
        · omega
        · omega
        · exact iq.1.2 h hh
    · simp only [height, List.append_assoc, List.singleton_append]
      rw [separated _ _ ip.1.1, leading _ iq.1, ip.2.1, iq.2.1]
      simp [word]; omega
    · simp [height, word, valleys_nest_add, ip.2.2, iq.2.2, nonzero,
        Nat.add_comm, Nat.add_left_comm]

/-- The first height-one separator recovers the constructor and both recursive children. -/
theorem heights_injective : Function.Injective height := by
  let pred : ℕ → Bool := fun h => h != 1
  have ne (c : Code) : height c ≠ [] := (heights_sound c).1.1
  have pos (c : Code) : ∀ h ∈ (height c).map Nat.succ, pred h = true := by
    intro h hh
    rcases List.mem_map.mp hh with ⟨a, ha, rfl⟩
    have hp := (heights_sound c).1.2 a ha
    simp only [pred, bne_iff_ne]
    omega
  have take (c : Code) :
      ((height c).map Nat.succ).takeWhile pred = (height c).map Nat.succ := by
    simpa using List.takeWhile_append_of_pos (l₂ := []) (pos c)
  have drop (c : Code) : ((height c).map Nat.succ).dropWhile pred = [] := by
    simpa using List.dropWhile_append_of_pos (l₂ := []) (pos c)
  have ft (c : Code) (B : List ℕ) :
      ((height c).map Nat.succ ++ 1 :: B).takeWhile pred =
        (height c).map Nat.succ := by
    rw [List.takeWhile_append_of_pos (pos c)]
    simp [pred]
  have bt (c : Code) (B : List ℕ) :
      ((height c).map Nat.succ ++ 1 :: B).dropWhile pred = 1 :: B := by
    rw [List.dropWhile_append_of_pos (pos c)]
    simp [pred]
  have hm (A B : List ℕ) : A.map Nat.succ = B.map Nat.succ ↔ A = B :=
    ⟨fun h => (List.map_injective_iff.mpr Nat.succ_injective) h,
      congrArg (List.map Nat.succ)⟩
  intro a
  induction a <;> intro b h <;> cases b <;>
    have hf := congrArg (List.takeWhile pred) h <;>
    have hb := congrArg (List.dropWhile pred) h <;>
    simp only [height, List.append_assoc, List.singleton_append] at hf hb <;>
    (try simp [ft, bt, take, drop, pred, hm, ne] at hf hb) <;>
    simp_all [height] <;> aesop

/-- Splitting at the first height-one column constructs a code for every bargraph. -/
theorem heights_surjective (H : List ℕ) (hH : IsBargraph H) :
    ∃ c : Code, height c = H := by
  have split : ∀ H : List ℕ, (∀ h ∈ H, 0 < h) →
      (∃ A : List ℕ, H = A.map Nat.succ ∧ ∀ a ∈ A, 0 < a) ∨
      (∃ A B : List ℕ, H = A.map Nat.succ ++ 1 :: B ∧
        (∀ a ∈ A, 0 < a) ∧ ∀ b ∈ B, 0 < b) := by
    intro H
    induction H with
    | nil => intro _; exact Or.inl ⟨[], rfl, by simp⟩
    | cons h t ih =>
      intro hp
      have hh := hp h (by simp)
      have ht : ∀ a ∈ t, 0 < a := fun a ha => hp a (by simp [ha])
      by_cases h1 : h = 1
      · exact Or.inr ⟨[], t, by simp [h1], by simp, ht⟩
      · have h2 : 0 < h - 1 := by omega
        rcases ih ht with ⟨A, hA, pA⟩ | ⟨A, B, hAB, pA, pB⟩
        · refine Or.inl ⟨(h - 1) :: A, ?_, ?_⟩
          · simp [hA]; omega
          · simpa using And.intro h2 pA
        · refine Or.inr ⟨(h - 1) :: A, B, ?_, ?_, pB⟩
          · simp [hAB]; omega
          · simpa using And.intro h2 pA
  have liftSum : ∀ A : List ℕ, (A.map Nat.succ).sum = A.sum + A.length := by
    intro A
    induction A with
    | nil => simp
    | cons a t ih => simp [ih]; omega
  have complete : ∀ s : ℕ, ∀ H : List ℕ, H.sum = s → IsBargraph H →
      ∃ c : Code, height c = H := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro H hs hp
      rcases split H hp.2 with ⟨A, hA, pA⟩ | ⟨A, B, hAB, pA, pB⟩
      · have hne : A ≠ [] := by
          intro he
          apply hp.1
          simpa only [he, List.map_nil] using hA
        have hl : 0 < A.length := List.length_pos_iff.mpr hne
        have hm : A.sum < s := by rw [hA, liftSum] at hs; omega
        obtain ⟨c, hc⟩ := ih A.sum hm A rfl ⟨hne, pA⟩
        exact ⟨.elevate c, by simp [height, hc, hA]⟩
      · have hs' : A.sum + A.length + 1 + B.sum = s := by
          simpa [hAB, List.sum_append, liftSum, Nat.add_assoc] using hs
        cases A with
        | nil =>
          cases B with
          | nil => exact ⟨.atom, by simpa [height] using hAB.symm⟩
          | cons b t =>
            have hm : (b :: t).sum < s := by simp only [List.sum_nil,
              List.length_nil, zero_add] at hs'; omega
            obtain ⟨c, hc⟩ := ih (b :: t).sum hm (b :: t) rfl ⟨by simp, pB⟩
            exact ⟨.left c, by simpa [height, hc] using hAB.symm⟩
        | cons a t =>
          have hm : (a :: t).sum < s := by
            simp only [List.length_cons] at hs'; omega
          obtain ⟨c, hc⟩ := ih (a :: t).sum hm (a :: t) rfl ⟨by simp, pA⟩
          cases B with
          | nil => exact ⟨.right c, by simpa [height, hc] using hAB.symm⟩
          | cons b u =>
            have hm' : (b :: u).sum < s := by omega
            obtain ⟨d, hd⟩ := ih (b :: u).sum hm' (b :: u) rfl ⟨by simp, pB⟩
            exact ⟨.join c d, by simpa [height, hc, hd, List.append_assoc] using
              hAB.symm⟩
  exact complete H.sum H rfl hH

end D5.S3.Combinatorics.DyckValleys.ValleyBargraph
