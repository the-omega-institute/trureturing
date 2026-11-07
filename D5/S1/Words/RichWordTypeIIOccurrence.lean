/- GID: D5/S1/Words/RichWordTypeIIOccurrence
   generality: I
   mirror - B: D5/B/S1/Words/RichWordTypeIIOccurrence
   mirror - E: none(waiver:source - word - combinatorics)
   anchors: []
   utility: none
   digest: Positive - cut Type - II factors and actual overlapping returns. -/
import D5.S1.Words.RichWordTypeIOccurrence

/-! Native Type - II factors, positive substitution cuts and overlapping return intervals. -/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RichWordTypeIIOccurrence

open RichWordTypeIOccurrence
open RankOneMorphismIterationBound (subst image subst_append image_add)
open AbelianBorders.AbelianBorderQuestionDefs (factor letterCount)
open MBonacciSentinelDesubstitution (factor_len factor_add factor_get)

/-- Auxiliary sentinel prefixes, before the first terminal wrap. -/
def F : ℕ → Word
  | 0 => []
  | k + 1 => sentinel (F k)

/-- Actual iterated substitution cuts. -/
def cut : ℕ → ℕ → ℕ
  | 0, i => i
  | k + 1, i => boundary (cut k i)

/-- The exact source recurrence, including both terminal letters. -/
def typeII : ℕ → Word
  | 0 => []
  | n + 1 => if n % 6 = 5 then terminal (typeII n) else sentinel (typeII n)

/-- The source vector recurrence; indices below six are auxiliary. -/
def f : ℕ → (Letter → ℕ)
  | 0 => 0
  | n + 1 => M.mulVec (f n) + increment n

/-- Positive occurrence starts, indexed by the positive source cuts. -/
def position : ℕ → ℕ → ℕ
  | 0, i => cut 6 i - 1
  | k + 1, i => occurrenceMap (k + 6) (position k i)

private theorem bstrict : StrictMono boundary := actual_fixed_point.2.1
private theorem bzero : boundary 0 = 0 := actual_fixed_point.2.2.1

private theorem bpos {i : ℕ} (hi : 0 < i) : 0 < boundary i := by
  simpa only [bzero] using bstrict hi

private theorem cut_strict (k : ℕ) : StrictMono (cut k) := by
  induction k with
  | zero => exact strictMono_id
  | succ k ih => exact bstrict.comp ih

private theorem cut_zero (k : ℕ) : cut k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [cut, ih] using bzero

private theorem cut_pos (k : ℕ) {i : ℕ} (hi : 0 < i) : 0 < cut k i := by
  simpa only [cut_zero] using cut_strict k hi

private theorem aux_occ (k q : ℕ) : Occ (F k) q ↔ ∃ i, q = cut k i := by
  induction k generalizing q with
  | zero => simp [F, cut, Occ, factor]
  | succ k ih =>
    rw [F, ordinary_occurrence_iff]
    constructor
    · rintro ⟨a,rfl,ha⟩
      obtain ⟨i,rfl⟩ := (ih a).mp ha
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨cut k i,rfl,(ih _).mpr ⟨i,rfl⟩⟩

private theorem aux_at (k i : ℕ) : Occ (F k) (cut k i) :=
  (aux_occ _ _).mpr ⟨i,rfl⟩

private theorem aux_context (k i : ℕ) (hi : 0 < i) :
    word (cut k i - 1) = (next^[k]) (word (i - 1)) ∧
    word (cut k i + (F k).length) = (next^[k]) (word i) := by
  induction k with
  | zero => simp [cut, F]
  | succ k ih =>
    have hlen := boundary_occ (aux_at k i)
    constructor
    · rw [cut, before_boundary (cut_pos k hi), ih.1, Function.iterate_succ_apply']
    · have he : cut (k + 1) i + (F (k + 1)).length =
          boundary (cut k i + (F k).length) + 1 := by
        simp only [cut, F, sentinel, List.length_append, List.length_singleton]
        omega
      rw [he,after_boundary,ih.2,Function.iterate_succ_apply']

private theorem next_five (a : Letter) :
    (next^[5]) a = if a = 0 then 5 else 6 := by
  fin_cases a <;> decide

private theorem next_five_context (a : Letter) :
    (next^[5]) a = 5 ∨ (next^[5]) a = 6 := by
  rw [next_five]; split <;> simp

private theorem wrap_five (a : Letter) :
    wrap ((next^[5]) a) = if a = 0 then 0 else 6 := by
  rw [next_five]; split <;> simp [wrap]

private theorem seed_eq : typeII 6 = terminal (F 5) := by rfl

private theorem seed_occ (q : ℕ) :
    Occ (typeII 6) q ↔ ∃ i, 0 < i ∧ q = cut 6 i - 1 := by
  rw [seed_eq,terminal_occurrence_iff]
  constructor
  · rintro ⟨a,ha,hq,ho,_,_⟩
    obtain ⟨i,he⟩ := (aux_occ 5 a).mp ho
    have hi : 0 < i := by
      by_contra h
      have hz : i = 0 := by omega
      rw [hz,cut_zero] at he
      omega
    refine ⟨i,hi,?_⟩
    change q = boundary (cut 5 i) - 1
    rw [hq,he]
  · rintro ⟨i,hi,rfl⟩
    have hc := aux_context 5 i hi
    exact ⟨cut 5 i,cut_pos 5 hi,rfl,aux_at 5 i,
      by rw [hc.1]; exact next_five_context _,
      by rw [hc.2]; exact next_five_context _⟩

private theorem seed_context (i : ℕ) (hi : 0 < i) :
    word (position 0 i - 1) = (if word (i - 1) = 0 then 0 else 6) ∧
    word (position 0 i + (typeII 6).length) = (if word i = 0 then 0 else 6) := by
  have hc := aux_context 5 i hi
  have hleft : word (cut 5 i - 1) = 5 ∨ word (cut 5 i - 1) = 6 :=
    by rw [hc.1]; exact next_five_context _
  have hright : word (cut 5 i + (F 5).length) = 5 ∨
      word (cut 5 i + (F 5).length) = 6 :=
    by rw [hc.2]; exact next_five_context _
  have hb := bpos (cut_pos 5 hi)
  have hlen := boundary_occ (aux_at 5 i)
  constructor
  · change word (boundary (cut 5 i) - 1 - 1) = _
    rw [show boundary (cut 5 i) - 1 - 1 = boundary (cut 5 i) - 2 by omega,
      two_before_boundary (cut_pos 5 hi) hleft,hc.1,wrap_five]
  · have he : position 0 i + (typeII 6).length =
        boundary (cut 5 i + (F 5).length) + 2 := by
      change boundary (cut 5 i) - 1 + (terminal (F 5)).length = _
      simp only [terminal,List.length_append,List.length_cons,List.length_nil]
      omega
    rw [he,two_after_boundary hright,hc.2,wrap_five]

private theorem position_strict (k : ℕ) : StrictMono (position k) := by
  induction k with
  | zero =>
    apply strictMono_nat_of_lt_succ
    intro i
    have hb := boundary_succ (cut 5 i)
    have hl : 2 ≤ (phi (word (cut 5 i))).length := by unfold phi; split <;> simp
    have hc := cut_strict 5 (show i < i + 1 by omega)
    have h := bstrict.monotone (show cut 5 i + 1 ≤ cut 5 (i + 1) by omega)
    change boundary (cut 5 i) - 1 < boundary (cut 5 (i + 1)) - 1
    omega
  | succ k ih => exact (occurrenceMap_strict (k + 6)).comp ih

private theorem position_pos (k i : ℕ) (hi : 0 < i) : 0 < position k i := by
  induction k with
  | zero =>
    have h := boundary_succ (cut 5 i - 1)
    have hl : 2 ≤ (phi (word (cut 5 i - 1))).length := by unfold phi; split <;> simp
    have hc := cut_pos 5 hi
    rw [show cut 5 i - 1 + 1 = cut 5 i by omega] at h
    change 0 < boundary (cut 5 i) - 1
    omega
  | succ k ih =>
    have hb := boundary_succ (position k i - 1)
    have hl : 2 ≤ (phi (word (position k i - 1))).length := by unfold phi; split <;> simp
    rw [show position k i - 1 + 1 = position k i by omega] at hb
    dsimp only [position,occurrenceMap]
    split <;> omega

private theorem phase_step (k : ℕ) (a : Letter) :
    (if (k + 6) % 6 = 5 then wrap else next)
        (if a = 0 then phase (k + 6) else 6) =
      (if a = 0 then phase (k + 1 + 6) else 6) := by
  have hk : (k + 6) % 6 < 6 := Nat.mod_lt _ (by omega)
  have he : (k + 1 + 6) % 6 = ((k + 6) % 6 + 1) % 6 := by omega
  by_cases ha : a = 0
  · simp only [ha,ite_true]
    by_cases h : (k + 6) % 6 = 5
    · rw [if_pos h]
      have hp : phase (k + 6) = 5 := by apply Fin.ext; exact h
      rw [hp]
      apply Fin.ext
      simp only [wrap,show (5:Letter)≠6 by decide,ite_false,Fin.val_zero,phase]
      omega
    · rw [if_neg h]
      apply Fin.ext
      have hp : (phase (k + 6)).val < 6 := hk
      change (if (k + 6) % 6 < 6 then ((k + 6) % 6 + 1) else 6) = (k + 1 + 6) % 6
      simp only [hk,ite_true]
      omega
  · simp only [ha,ite_false]
    split <;> decide

private theorem typeII_step (n : ℕ) : typeII (n + 1)=
    if n % 6 = 5 then terminal (typeII n) else sentinel (typeII n) := rfl

private theorem native_induction (k : ℕ) :
    (∀ q, Occ (typeII (k + 6)) q ↔ ∃ i, 0 < i ∧ q = position k i) ∧
    (∀ i, 0 < i →
      word (position k i - 1) = (if word (i - 1) = 0 then phase (k + 6) else 6) ∧
      word (position k i + (typeII (k + 6)).length) =
        (if word i = 0 then phase (k + 6) else 6)) := by
  induction k with
  | zero => exact ⟨seed_occ,by simpa [phase] using seed_context⟩
  | succ k ih =>
    have transport (q : ℕ) : Occ (typeII (k + 1 + 6)) q ↔
        ∃ a, q = occurrenceMap (k + 6) a ∧ Occ (typeII (k + 6)) a := by
      by_cases h : (k + 6) % 6 = 5
      · rw [show k + 1 + 6 = k + 6 + 1 by omega,typeII_step,if_pos h,terminal_occurrence_iff]
        constructor
        · rintro ⟨a,ha,hq,ho,_,_⟩; exact ⟨a,by simpa [occurrenceMap,h] using hq,ho⟩
        · rintro ⟨a,hq,ho⟩
          obtain ⟨i,hi,rfl⟩ := (ih.1 a).mp ho
          have hc := ih.2 i hi
          have hp : phase (k + 6) = 5 := by apply Fin.ext; simpa [phase] using h
          refine ⟨position k i,position_pos k i hi,by simpa [occurrenceMap,h] using hq,
            ho,?_,?_⟩
          · rw [hc.1,hp]; split <;> simp
          · rw [hc.2,hp]; split <;> simp
      · rw [show k + 1 + 6 = k + 6 + 1 by omega,typeII_step,if_neg h]
        simpa only [occurrenceMap,if_neg h] using ordinary_occurrence_iff (typeII (k + 6)) q
    refine ⟨?_,?_⟩
    · intro q
      rw [transport]
      constructor
      · rintro ⟨a,rfl,ha⟩
        obtain ⟨i,hi,rfl⟩ := (ih.1 a).mp ha
        exact ⟨i,hi,rfl⟩
      · rintro ⟨i,hi,rfl⟩
        exact ⟨position k i,rfl,(ih.1 _).mpr ⟨i,hi,rfl⟩⟩
    · intro i hi
      have hc := ih.2 i hi
      have ho := (ih.1 _).mpr ⟨i,hi,rfl⟩
      have hlen := boundary_occ ho
      by_cases h : (k + 6) % 6 = 5
      · have hp : phase (k + 6) = 5 := by apply Fin.ext; simpa [phase] using h
        have hl : word (position k i - 1) = 5 ∨ word (position k i - 1) = 6 := by
          rw [hc.1,hp]; split <;> simp
        have hr : word (position k i + (typeII (k + 6)).length) = 5 ∨
            word (position k i + (typeII (k + 6)).length) = 6 := by
          rw [hc.2,hp]; split <;> simp
        have hb := bpos (position_pos k i hi)
        constructor
        · have he : position (k + 1) i - 1 = boundary (position k i) - 2 := by
            simp only [position,occurrenceMap,if_pos h]; omega
          rw [he,two_before_boundary (position_pos k i hi) hl,hc.1]
          exact (by simpa only [if_pos h] using phase_step k (word (i - 1)))
        · have he : position (k + 1) i + (typeII (k + 1 + 6)).length =
              boundary (position k i + (typeII (k + 6)).length) + 2 := by
            rw [show k + 1 + 6 = k + 6 + 1 by omega,typeII_step (k + 6),if_pos h]
            change boundary (position k i) - 1 + (terminal (typeII (k + 6))).length = _
            simp only [terminal,List.length_append,List.length_cons,List.length_nil]
            omega
          rw [he,two_after_boundary hr,hc.2]
          exact (by simpa only [if_pos h] using phase_step k (word i))
      · constructor
        · change word (occurrenceMap (k + 6) (position k i) - 1) = _
          rw [occurrenceMap,if_neg h,before_boundary (position_pos k i hi),hc.1]
          exact (by simpa only [if_neg h] using phase_step k (word (i - 1)))
        · have he : position (k + 1) i + (typeII (k + 1 + 6)).length =
              boundary (position k i + (typeII (k + 6)).length) + 1 := by
            rw [show k + 1 + 6 = k + 6 + 1 by omega,typeII_step (k + 6),if_neg h]
            change boundary (position k i) + (sentinel (typeII (k + 6))).length = _
            simp only [sentinel,List.length_append,List.length_singleton]
            omega
          rw [he,after_boundary,hc.2]
          exact (by simpa only [if_neg h] using phase_step k (word i))


private theorem aux_return (k i : ℕ) :
    returnWord (cut k i) (cut k (i + 1)) = image phi k (word i) := by
  induction k with
  | zero => simp [cut,returnWord,factor,image]
  | succ k ih =>
    change returnWord (boundary (cut k i)) (boundary (cut k (i + 1))) = _
    rw [ordinary_return_word (cut_strict k (show i < i + 1 by omega)), ih,
      RankOneMorphismIterationBound.image_succ]

private theorem image_counts (n : ℕ) (a : Letter) :
    parikh (image phi n a) = (M^n).mulVec (unit a) :=
  typeI_parikh_formula.2.2 n a

private theorem seed_return (i : ℕ) (hi : 0 < i) :
    returnWord (position 0 i) (position 0 (i + 1)) =
      [6] ++ (image phi 6 (word i)).dropLast ∧
    parikh (returnWord (position 0 i) (position 0 (i + 1))) =
      (M^6).mulVec (unit (word i)) := by
  have hc := (aux_context 5 i hi).1
  have hd := (aux_context 5 (i + 1) (by omega)).1
  have hl : word (cut 5 i - 1) = 5 ∨ word (cut 5 i - 1) = 6 := by
    rw [hc]; exact next_five_context _
  have hr : word (cut 5 (i + 1) - 1) = 5 ∨ word (cut 5 (i + 1) - 1) = 6 := by
    rw [hd]; exact next_five_context _
  have hab := cut_strict 5 (show i < i + 1 by omega)
  constructor
  · simpa only [position,cut,aux_return,← RankOneMorphismIterationBound.image_succ] using
      terminal_interval_cancellation (cut_pos 5 hi) hab hl hr
  · change parikh (returnWord (boundary (cut 5 i) - 1) (boundary (cut 5 (i + 1)) - 1)) = _
    rw [terminal_return_parikh (cut_pos 5 hi) hab hl hr,aux_return,
      ← parikh_subst,← RankOneMorphismIterationBound.image_succ,image_counts]

private theorem consecutive_indices (k a b : ℕ) :
    Consecutive (typeII (k + 6)) a b ↔
      ∃ i, 0 < i ∧ a = position k i ∧ b = position k (i + 1) := by
  constructor
  · rintro ⟨hab,ha,hb,hgap⟩
    obtain ⟨i,hi,rfl⟩ := (native_induction k).1 a |>.mp ha
    obtain ⟨j,hj,rfl⟩ := (native_induction k).1 b |>.mp hb
    have hij := (position_strict k).lt_iff_lt.mp hab
    have he : j = i + 1 := by
      by_contra hne
      have hlt : i + 1 < j := by omega
      exact hgap (position k (i + 1)) (position_strict k (by omega))
        (position_strict k hlt) ((native_induction k).1 _ |>.mpr ⟨i + 1,by omega,rfl⟩)
    exact ⟨i,hi,rfl,by rw [he]⟩
  · rintro ⟨i,hi,rfl,rfl⟩
    refine ⟨position_strict k (by omega),
      (native_induction k).1 _ |>.mpr ⟨i,hi,rfl⟩,
      (native_induction k).1 _ |>.mpr ⟨i + 1,by omega,rfl⟩,?_⟩
    intro q haq hqb hq
    obtain ⟨j,hj,rfl⟩ := (native_induction k).1 q |>.mp hq
    have := (position_strict k).lt_iff_lt.mp haq
    have := (position_strict k).lt_iff_lt.mp hqb
    omega

private theorem return_update (k i : ℕ) (hi : 0 < i) :
    returnWord (position (k + 1) i) (position (k + 1) (i + 1)) =
      if (k + 6) % 6 = 5 then
        [6] ++ (subst phi (returnWord (position k i) (position k (i + 1)))).dropLast
      else subst phi (returnWord (position k i) (position k (i + 1))) := by
  have hab := position_strict k (show i < i + 1 by omega)
  by_cases h : (k + 6) % 6 = 5
  · have hp : phase (k + 6) = 5 := by apply Fin.ext; simpa [phase] using h
    have hl : word (position k i - 1) = 5 ∨ word (position k i - 1) = 6 := by
      rw [(native_induction k).2 i hi |>.1,hp]; split <;> simp
    have hr : word (position k (i + 1) - 1) = 5 ∨ word (position k (i + 1) - 1) = 6 := by
      rw [(native_induction k).2 (i + 1) (by omega) |>.1,hp]; split <;> simp
    simpa [position,occurrenceMap,h] using
      terminal_interval_cancellation (position_pos k i hi) hab hl hr
  · simpa [position,occurrenceMap,h] using ordinary_return_word hab

private theorem return_counts (k i : ℕ) (hi : 0 < i) :
    parikh (returnWord (position k i) (position k (i + 1))) =
      (M^(k + 6)).mulVec (unit (word i)) := by
  induction k with
  | zero => exact (seed_return i hi).2
  | succ k ih =>
    have hab := position_strict k (show i < i + 1 by omega)
    have step : parikh (returnWord (position (k + 1) i) (position (k + 1) (i + 1))) =
        M.mulVec (parikh (returnWord (position k i) (position k (i + 1)))) := by
      by_cases h : (k + 6) % 6 = 5
      · have hp : phase (k + 6) = 5 := by apply Fin.ext; simpa [phase] using h
        have hl : word (position k i - 1) = 5 ∨ word (position k i - 1) = 6 := by
          rw [(native_induction k).2 i hi |>.1,hp]; split <;> simp
        have hr : word (position k (i + 1) - 1) = 5 ∨ word (position k (i + 1) - 1) = 6 := by
          rw [(native_induction k).2 (i + 1) (by omega) |>.1,hp]; split <;> simp
        simpa [position,occurrenceMap,h] using
          terminal_return_parikh (position_pos k i hi) hab hl hr
      · rw [return_update k i hi,if_neg h,parikh_subst]
    rw [step,ih,Matrix.mulVec_mulVec,← pow_succ']
    congr 2 <;> omega

private theorem all_image_prefix (k : ℕ) (a : Letter) :
    image phi (k + 6) 0 <+: image phi (k + 6) a := by
  induction k with
  | zero => fin_cases a <;> decide
  | succ k ih => exact ih.flatMap phi

private theorem return_domination (k a b : ℕ)
    (h : Consecutive (typeII (k + 6)) a b) :
    (M^(k + 6)).mulVec (unit 0) ≤ parikh (returnWord a b) := by
  obtain ⟨i,hi,rfl,rfl⟩ := (consecutive_indices k a b).mp h
  rw [return_counts k i hi,← image_counts,← image_counts]
  intro c
  exact (all_image_prefix k (word i)).count_le c

private theorem small_letters : word 0 = 0 ∧ word 1 = 1 ∧ word 2 = 0 := by
  have h0 := word_eq_iterate 2 0 (by decide)
  have h1 := word_eq_iterate 2 1 (by decide)
  have h2 := word_eq_iterate 2 2 (by decide)
  exact ⟨h0,h1,h2⟩

private theorem every_letter (a : Letter) : ∃ i, 0 < i ∧ word i = a := by
  fin_cases a
  · exact ⟨2,by omega,small_letters.2.2⟩
  · exact ⟨1,by omega,word_eq_iterate 6 1 (by decide)⟩
  · exact ⟨3,by omega,word_eq_iterate 6 3 (by decide)⟩
  · exact ⟨7,by omega,word_eq_iterate 6 7 (by decide)⟩
  · exact ⟨15,by omega,word_eq_iterate 6 15 (by decide)⟩
  · exact ⟨31,by omega,word_eq_iterate 6 31 (by decide)⟩
  · exact ⟨63,by omega,word_eq_iterate 6 63 (by decide)⟩

private theorem exact_extensions (k : ℕ) :
    Lext (typeII (k + 6))={phase (k + 6),6} ∧
    Rext (typeII (k + 6))={phase (k + 6),6} := by
  have h1 := (native_induction k).2 1 (by omega)
  have h2 := (native_induction k).2 2 (by omega)
  simp only [show 1 - 1 = 0 by omega,show 2 - 1 = 1 by omega,
    small_letters.1,small_letters.2.1,small_letters.2.2,ite_true,
    show (1:Letter)≠0 by decide,ite_false] at h1 h2
  constructor
  · ext c
    rw [lext_iff]
    constructor
    · rintro ⟨q,hq,ho,he⟩
      obtain ⟨i,hi,rfl⟩ := (native_induction k).1 q |>.mp ho
      rw [(native_induction k).2 i hi |>.1] at he
      split at he <;> simp_all
    · intro hc
      rcases Set.mem_insert_iff.mp hc with hc | hc
      · exact ⟨position k 1,position_pos k 1 (by omega),
          (native_induction k).1 _ |>.mpr ⟨1,by omega,rfl⟩,hc ▸ h1.1⟩
      · have he : c = 6 := Set.mem_singleton_iff.mp hc
        exact ⟨position k 2,position_pos k 2 (by omega),
          (native_induction k).1 _ |>.mpr ⟨2,by omega,rfl⟩,he ▸ h2.1⟩
  · ext c
    rw [rext_iff]
    constructor
    · rintro ⟨q,ho,he⟩
      obtain ⟨i,hi,rfl⟩ := (native_induction k).1 q |>.mp ho
      rw [(native_induction k).2 i hi |>.2] at he
      split at he <;> simp_all
    · intro hc
      rcases Set.mem_insert_iff.mp hc with hc | hc
      · exact ⟨position k 2,(native_induction k).1 _ |>.mpr ⟨2,by omega,rfl⟩,hc ▸ h2.2⟩
      · have he : c = 6 := Set.mem_singleton_iff.mp hc
        exact ⟨position k 1,(native_induction k).1 _ |>.mpr ⟨1,by omega,rfl⟩,he ▸ h1.2⟩

private theorem factor_counts (n : ℕ) : parikh (typeII n) = f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [typeII_step,f,increment]
    by_cases h : n % 6 = 5
    · simp only [if_pos h,terminal,parikh_append,parikh_subst,ih]
      rw [show parikh [0,6]=unit 0 + unit 6 by rw [parikh_cons,parikh_singleton],
        parikh_singleton]
      ext a
      simp [Pi.add_apply,Pi.smul_apply,two_smul]
      omega
    · simp only [if_neg h,sentinel,parikh_append,parikh_subst,ih,parikh_singleton]

private theorem sentinel_reverse (s : Word) :
    (sentinel s).reverse = sentinel s.reverse := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    have comm : [0]++(phi a).reverse = phi a++[0] := by fin_cases a <;> decide
    change (phi a++(subst phi s++[0])).reverse =
      subst phi (s.reverse++[a])++[0]
    rw [List.reverse_append,ih,subst_append]
    change (subst phi s.reverse++[0])++(phi a).reverse =
      (subst phi s.reverse++phi a)++[0]
    rw [List.append_assoc,comm,List.append_assoc]

private theorem factor_palindrome (n : ℕ) : (typeII n).reverse = typeII n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [typeII]
    split
    · simp only [terminal,show ∀s : Word, [6]++subst phi s++[0,6]=
          [6]++sentinel s++[6] from fun s => by simp [sentinel,List.append_assoc],
        List.reverse_append,List.reverse_singleton,sentinel_reverse,ih]
      simp [List.append_assoc]
    · rw [sentinel_reverse,ih]

private theorem cut_succ (k i : ℕ) :
    cut k (i + 1) = cut k i + (image phi k (word i)).length := by
  have h := congrArg List.length (aux_return k i)
  simp only [returnWord,factor_len] at h
  have := cut_strict k (show i < i + 1 by omega)
  omega

private theorem seed_numerics :
    typeII 6 = 6::(F 6++[6]) ∧ (typeII 6).length = 65 ∧
    parikh (typeII 6) = (fun a => ![32,16,8,4,2,1,2] a) ∧
    position 0 2 = 128 ∧ position 0 3 = 192 ∧
    returnWord (position 0 2) (position 0 3) = 6::F 6 := by
  have c1 : cut 6 1 = 64 := by
    have h := cut_succ 6 0
    simpa only [cut_zero,small_letters.1,show (image phi 6 0).length = 64 by decide] using h
  have c2 : cut 6 2 = 129 := by
    have h := cut_succ 6 1
    simpa only [c1,small_letters.2.1,show (image phi 6 1).length = 65 by decide] using h
  have c3 : cut 6 3 = 193 := by
    have h := cut_succ 6 2
    simpa only [c2,small_letters.2.2,show (image phi 6 0).length = 64 by decide] using h
  refine ⟨by decide,by decide,by decide,?_,?_,?_⟩
  · change cut 6 2 - 1 = 128; omega
  · change cut 6 3 - 1 = 192; omega
  · rw [(seed_return 2 (by omega)).1,small_letters.2.2]
    decide

/-- Native words and their complete positive - cut occurrence and return data.
The offset k denotes source index k + 6, including the first overlapping pair. -/
structure NativeData (k : ℕ) : Prop where
  nonempty : (typeII (k + 6)).length > 0
  palindrome : (typeII (k + 6)).reverse = typeII (k + 6)
  counts : parikh (typeII (k + 6)) = f (k + 6)
  strict : StrictMono (position k)
  positive : ∀ i, 0 < i → 0 < position k i
  occurrence : ∀ q, Occ (typeII (k + 6)) q ↔ ∃! i, 0 < i ∧ q = position k i
  contexts : ∀ i, 0 < i →
    word (position k i - 1) = (if word (i - 1) = 0 then phase (k + 6) else 6) ∧
    word (position k i + (typeII (k + 6)).length)=
      (if word i = 0 then phase (k + 6) else 6)
  extensions : Lext (typeII (k + 6))={phase (k + 6),6} ∧
    Rext (typeII (k + 6))={phase (k + 6),6}
  consecutive : ∀ a b, Consecutive (typeII (k + 6)) a b ↔
    ∃! i, 0 < i ∧ a = position k i ∧ b = position k (i + 1)
  returnWordStep : ∀ i, 0 < i →
    returnWord (position (k + 1) i) (position (k + 1) (i + 1)) =
      if (k + 6) % 6 = 5 then
        [6]++(subst phi (returnWord (position k i) (position k (i + 1)))).dropLast
      else subst phi (returnWord (position k i) (position k (i + 1)))
  returnCounts : ∀ i, 0 < i →
    parikh (returnWord (position k i) (position k (i + 1)))=
      (M^(k + 6)).mulVec (unit (word i))
  minimum : Consecutive (typeII (k + 6)) (position k 2) (position k 3) ∧
    parikh (returnWord (position k 2) (position k 3)) = (M^(k + 6)).mulVec (unit 0) ∧
    ∀ a b, Consecutive (typeII (k + 6)) a b →
      (M^(k + 6)).mulVec (unit 0) ≤ parikh (returnWord a b)
  vectors : {v | ∃ a b, Consecutive (typeII (k + 6)) a b ∧ parikh (returnWord a b) = v}=
    Set.range (fun a : Letter => (M^(k + 6)).mulVec (unit a))
  seed : typeII 6 = 6::(F 6++[6]) ∧ (typeII 6).length = 65 ∧
    parikh (typeII 6) = (fun a => ![32,16,8,4,2,1,2] a) ∧
    position 0 2 = 128 ∧ position 0 3 = 192 ∧
    returnWord (position 0 2) (position 0 3) = 6::F 6

/-- Every original source index n at least six has the actual Type - II factor,
all its natural - position occurrences, and all its consecutive return vectors. -/
theorem actual_typeII (n : ℕ) (hn : 6≤n) : NativeData (n - 6) := by
  generalize hk : n - 6 = k
  refine ⟨?_,factor_palindrome _,factor_counts _,position_strict k,
    position_pos k,?_,(native_induction k).2,exact_extensions k,?_,
    return_update k,return_counts k,?_,?_,seed_numerics⟩
  · cases k with
    | zero => exact seed_numerics.2.1 ▸ (by decide : 0 < 65)
    | succ k =>
      rw [show k + 1 + 6 = k + 6 + 1 by omega,typeII]
      split <;> simp [terminal,sentinel]
  · intro q
    rw [(native_induction k).1]
    constructor
    · rintro ⟨i,hi,hq⟩
      exact ⟨i,⟨hi,hq⟩,fun j hj => (position_strict k).injective (hj.2.symm.trans hq)⟩
    · rintro ⟨i,hi,_⟩; exact ⟨i,hi⟩
  · intro a b
    rw [consecutive_indices]
    constructor
    · rintro ⟨i,hi,ha,hb⟩
      exact ⟨i,⟨hi,ha,hb⟩,fun j hj =>
        (position_strict k).injective (hj.2.1.symm.trans ha)⟩
    · rintro ⟨i,hi,_⟩; exact ⟨i,hi⟩
  · refine ⟨(consecutive_indices k _ _).mpr ⟨2,by omega,rfl,rfl⟩,?_,return_domination k⟩
    rw [return_counts k 2 (by omega),small_letters.2.2]
  · ext v
    constructor
    · rintro ⟨a,b,h,he⟩
      obtain ⟨i,hi,rfl,rfl⟩ := (consecutive_indices k a b).mp h
      exact ⟨word i,(return_counts k i hi).symm.trans he⟩
    · rintro ⟨a,rfl⟩
      obtain ⟨i,hi,he⟩ := every_letter a
      exact ⟨position k i,position k (i + 1),
        (consecutive_indices k _ _).mpr ⟨i,hi,rfl,rfl⟩,by rw [return_counts k i hi,he]⟩

end D5.S1.Words.RichWordTypeIIOccurrence
