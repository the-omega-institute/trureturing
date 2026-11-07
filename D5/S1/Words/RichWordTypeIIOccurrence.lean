/- GID: D5/S1/Words/RichWordTypeIIOccurrence
   generality: I
   mirror-B: D5/B/S1/Words/RichWordTypeIIOccurrence
   mirror-E: none(waiver:source-word-combinatorics)
   anchors: []
   utility: none
   digest: Positive-cut Type-II factors and actual overlapping returns. -/
import D5.S1.Words.RichWordTypeIOccurrence

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
  | k+1 => sentinel (F k)

/-- Actual iterated substitution cuts. -/
def cut : ℕ → ℕ → ℕ
  | 0, i => i
  | k+1, i => boundary (cut k i)

/-- The exact source recurrence, including both terminal letters. -/
def typeII : ℕ → Word
  | 0 => []
  | n+1 => if n % 6 = 5 then terminal (typeII n) else sentinel (typeII n)

/-- The source vector recurrence; indices below six are auxiliary. -/
def f : ℕ → (Letter → ℕ)
  | 0 => 0
  | n+1 => M.mulVec (f n) + increment n

/-- Positive occurrence starts, indexed by the positive source cuts. -/
def position : ℕ → ℕ → ℕ
  | 0, i => cut 6 i - 1
  | k+1, i => occurrenceMap (k+6) (position k i)

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
    word (cut k i-1) = (next^[k]) (word (i-1)) ∧
    word (cut k i+(F k).length) = (next^[k]) (word i) := by
  induction k with
  | zero => simp [cut, F]
  | succ k ih =>
    have hlen := boundary_occ (aux_at k i)
    constructor
    · rw [cut, before_boundary (cut_pos k hi), ih.1, Function.iterate_succ_apply']
    · have he : cut (k+1) i+(F (k+1)).length =
          boundary (cut k i+(F k).length)+1 := by
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
    Occ (typeII 6) q ↔ ∃ i, 0 < i ∧ q = cut 6 i-1 := by
  rw [seed_eq,terminal_occurrence_iff]
  constructor
  · rintro ⟨a,ha,rfl,ho,_,_⟩
    obtain ⟨i,rfl⟩ := (aux_occ 5 a).mp ho
    have hi : 0 < i := by
      by_contra h
      have he : i = 0 := by omega
      simp [he,cut_zero] at ha
    exact ⟨i,hi,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    have hc := aux_context 5 i hi
    exact ⟨cut 5 i,cut_pos 5 hi,rfl,aux_at 5 i,
      hc.1 ▸ next_five_context (word (i-1)),
      hc.2 ▸ next_five_context (word i)⟩

private theorem seed_context (i : ℕ) (hi : 0 < i) :
    word (position 0 i-1) = (if word (i-1) = 0 then 0 else 6) ∧
    word (position 0 i+(typeII 6).length) = (if word i = 0 then 0 else 6) := by
  have hc := aux_context 5 i hi
  have hleft : word (cut 5 i-1) = 5 ∨ word (cut 5 i-1) = 6 :=
    hc.1 ▸ next_five_context (word (i-1))
  have hright : word (cut 5 i+(F 5).length) = 5 ∨
      word (cut 5 i+(F 5).length) = 6 :=
    hc.2 ▸ next_five_context (word i)
  have hb := bpos (cut_pos 5 hi)
  have hlen := boundary_occ (aux_at 5 i)
  constructor
  · change word (boundary (cut 5 i)-1-1) = _
    rw [show boundary (cut 5 i)-1-1 = boundary (cut 5 i)-2 by omega,
      two_before_boundary (cut_pos 5 hi) hleft,hc.1,wrap_five]
  · have he : position 0 i+(typeII 6).length =
        boundary (cut 5 i+(F 5).length)+2 := by
      simp only [position,cut,seed_eq,terminal,List.length_append,List.length_cons,
        List.length_nil]
      omega
    rw [he,two_after_boundary hright,hc.2,wrap_five]

private theorem position_strict (k : ℕ) : StrictMono (position k) := by
  induction k with
  | zero =>
    apply strictMono_nat_of_lt_succ
    intro i
    have hb := boundary_succ (cut 5 i)
    have hl : 2 ≤ (phi (word (cut 5 i))).length := by unfold phi; split <;> simp
    have hc := cut_strict 5 (show i < i+1 by omega)
    have h := bstrict.monotone (show cut 5 i+1 ≤ cut 5 (i+1) by omega)
    change boundary (cut 5 i)-1 < boundary (cut 5 (i+1))-1
    omega
  | succ k ih => exact (occurrenceMap_strict (k+6)).comp ih

private theorem position_pos (k i : ℕ) (hi : 0 < i) : 0 < position k i := by
  induction k with
  | zero =>
    have h := boundary_succ (cut 5 i-1)
    have hl : 2 ≤ (phi (word (cut 5 i-1))).length := by unfold phi; split <;> simp
    have hc := cut_pos 5 hi
    rw [show cut 5 i-1+1 = cut 5 i by omega] at h
    change 0 < boundary (cut 5 i)-1
    omega
  | succ k ih =>
    have hb := boundary_succ (position k i-1)
    have hl : 2 ≤ (phi (word (position k i-1))).length := by unfold phi; split <;> simp
    rw [show position k i-1+1 = position k i by omega] at hb
    dsimp only [position,occurrenceMap]
    split <;> omega

private theorem phase_step (k : ℕ) (a : Letter) :
    (if (k+6)%6 = 5 then wrap else next)
        (if a = 0 then phase (k+6) else 6) =
      (if a = 0 then phase (k+1+6) else 6) := by
  have hk : (k+6)%6 < 6 := Nat.mod_lt _ (by omega)
  have he : (k+1+6)%6 = ((k+6)%6+1)%6 := by omega
  by_cases ha : a=0
  · simp only [ha,ite_true,phase]
    interval_cases h : (k+6)%6 <;> simp [h,he,next,wrap] <;> decide
  · simp [ha,next,wrap]

private theorem native_induction (k : ℕ) :
    (∀ q, Occ (typeII (k+6)) q ↔ ∃ i, 0 < i ∧ q = position k i) ∧
    (∀ i, 0 < i →
      word (position k i-1) = (if word (i-1)=0 then phase (k+6) else 6) ∧
      word (position k i+(typeII (k+6)).length) =
        (if word i=0 then phase (k+6) else 6)) := by
  induction k with
  | zero => exact ⟨seed_occ,by simpa [phase] using seed_context⟩
  | succ k ih =>
    have transport (q : ℕ) : Occ (typeII (k+1+6)) q ↔
        ∃ a, q=occurrenceMap (k+6) a ∧ Occ (typeII (k+6)) a := by
      by_cases h : (k+6)%6=5
      · rw [show k+1+6=k+6+1 by omega,typeII,if_pos h,terminal_occurrence_iff]
        constructor
        · rintro ⟨a,ha,hq,ho,_,_⟩; exact ⟨a,by simpa [occurrenceMap,h] using hq,ho⟩
        · rintro ⟨a,hq,ho⟩
          obtain ⟨i,hi,rfl⟩ := (ih.1 a).mp ho
          have hc := ih.2 i hi
          have hp : phase (k+6)=5 := by apply Fin.ext; simpa [phase] using h
          refine ⟨position k i,position_pos k i hi,by simpa [occurrenceMap,h] using hq,
            ho,?_,?_⟩
          · rw [hc.1,hp]; split <;> simp
          · rw [hc.2,hp]; split <;> simp
      · simpa [show k+1+6=k+6+1 by omega,typeII,h,occurrenceMap,sentinel]
          using ordinary_occurrence_iff (typeII (k+6)) q
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
      by_cases h : (k+6)%6=5
      · have hp : phase (k+6)=5 := by apply Fin.ext; simpa [phase] using h
        have hl : word (position k i-1)=5 ∨ word (position k i-1)=6 := by
          rw [hc.1,hp]; split <;> simp
        have hr : word (position k i+(typeII (k+6)).length)=5 ∨
            word (position k i+(typeII (k+6)).length)=6 := by
          rw [hc.2,hp]; split <;> simp
        have hb := bpos (position_pos k i hi)
        constructor
        · have he : position (k+1) i-1=boundary (position k i)-2 := by
            simp only [position,occurrenceMap,if_pos h]; omega
          rw [he,two_before_boundary (position_pos k i hi) hl,hc.1]
          exact (by simpa [h] using phase_step k (word (i-1)))
        · have he : position (k+1) i+(typeII (k+1+6)).length =
              boundary (position k i+(typeII (k+6)).length)+2 := by
            simp only [position,occurrenceMap,if_pos h,
              show k+1+6=k+6+1 by omega,typeII,terminal,List.length_append,
              List.length_cons,List.length_nil]
            omega
          rw [he,two_after_boundary hr,hc.2]
          exact (by simpa [h] using phase_step k (word i))
      · constructor
        · change word (boundary (position k i)-1)=_
          rw [before_boundary (position_pos k i hi),hc.1]
          exact (by simpa [h] using phase_step k (word (i-1)))
        · have he : position (k+1) i+(typeII (k+1+6)).length =
              boundary (position k i+(typeII (k+6)).length)+1 := by
            simp only [position,occurrenceMap,if_neg h,
              show k+1+6=k+6+1 by omega,typeII,if_neg h,sentinel,
              List.length_append,List.length_singleton]
            omega
          rw [he,after_boundary,hc.2]
          exact (by simpa [h] using phase_step k (word i))

end D5.S1.Words.RichWordTypeIIOccurrence
