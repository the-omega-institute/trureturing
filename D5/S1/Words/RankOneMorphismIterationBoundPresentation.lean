/- GID: D5/S1/Words/RankOneMorphismIterationBoundPresentation
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundPresentation
   mirror-E: none(waiver:consumed-source-presentation)
   anchors: []
   digest: Actual indexed binary expansion and uniform height presentation. -/
import D5.S1.Words.RankOneMorphismIterationBoundArithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
namespace Parameters
variable {f : Morphism} (p : Parameters f)

/-- Every state names an actual position in one of the two image words. -/
abbrev State (f : Morphism) := Σ c : Letter, Fin (f c).length

/-- The expansion of a source letter into its indexed positions. -/
def indexed (c : Letter) : List (State f) := List.ofFn (fun i => ⟨c, i⟩)

def expand (w : Word) : List (State f) := w.flatMap indexed

@[simp] theorem indexed_length (c : Letter) : (indexed (f := f) c).length = (f c).length := by
  simp [indexed]

@[simp] theorem expand_nil : expand (f := f) [] = [] := rfl
@[simp] theorem expand_cons (c : Letter) (w : Word) :
    expand (f := f) (c :: w) = indexed c ++ expand w := rfl
@[simp] theorem expand_append (u v : Word) :
    expand (f := f) (u ++ v) = expand u ++ expand v := List.flatMap_append

theorem state_card : Fintype.card (State f) = (f 0).length + (f 1).length := by
  rw [Fintype.card_sigma]
  simp [Fin.sum_univ_two]

theorem expand_length (w : Word) : (expand (f := f) w).length = (subst f w).length := by
  induction w with
  | nil => rfl
  | cons c w ih => simp [ih]

theorem expand_image_length (c : Letter) :
    (expand (f := f) (f c)).length = p.lam * (f c).length := by
  rw [expand_length, ← image_one f c, ← image_succ, p.iterated_length]
  rw [image_one, p.image_length]
  simp only [pow_one]
  ring

/-- MSB digit transition, read at its actual position in E(f(c)). -/
def transition (q : State f) (j : Fin p.lam) : State f :=
  (expand (f := f) (f q.1))[p.lam * q.2.val + j.val]'(by
    rw [p.expand_image_length]
    have hi := q.2.isLt
    have hj := j.isLt
    nlinarith)

def uniform (q : State f) : List (State f) := List.ofFn (p.transition q)

def coding (q : State f) : ℤ := p.charge ((f q.1).take q.2.val)

@[simp] theorem uniform_length (q : State f) : (p.uniform q).length = p.lam := by
  simp [uniform]

/-- hE=Ef on the actual finite source letters. -/
theorem uniform_indexed (c : Letter) :
    subst p.uniform (indexed c) = expand (f := f) (f c) := by
  have hl := p.expand_image_length c
  have hoff := List.ofFn_mul' (m := p.lam) (n := (f c).length)
    (fun i => (expand (f := f) (f c))[i.val]'(by omega))
  have ho : List.ofFn (fun i : Fin (p.lam * (f c).length) =>
      (expand (f := f) (f c))[i.val]'(by omega)) = expand (f := f) (f c) := by
    apply List.ext_getElem
    · simp [hl]
    · intro i hi hj; simp
  rw [ho] at hoff
  rw [hoff]
  simp only [subst, indexed, uniform, List.flatMap, List.map_ofFn, Function.comp_def]
  rfl

/-- Commutation on arbitrary source words. -/
theorem uniform_expand (w : Word) :
    subst p.uniform (expand (f := f) w) = expand (f := f) (subst f w) := by
  induction w with
  | nil => simp
  | cons c w ih => simp [p.uniform_indexed, ih]

theorem iterated_expand (t : ℕ) (w : Word) :
    subst (image p.uniform t) (expand (f := f) w) =
      expand (f := f) (subst (image f t) w) := by
  induction t with
  | zero => simp [subst, image]
  | succ t ih =>
    have hm {α : Type} (h : α → List α) (v : List α) :
        subst (image h (t+1)) v = subst h (subst (image h t) v) := by
      induction v with
      | nil => simp
      | cons c v hv => simp [hv]
    rw [hm p.uniform (expand w), ih, p.uniform_expand, ← hm f w]

/-- The finite list of actual prefix charges at each letter position. -/
def heights (w : Word) : List ℤ :=
  (List.range w.length).map (fun i => p.charge (w.take i))

@[simp] theorem heights_length (w : Word) : (p.heights w).length = w.length := by
  simp [heights]

theorem heights_append {u v : Word} (h : p.charge u = 0) :
    p.heights (u ++ v) = p.heights u ++ p.heights v := by
  simp only [heights, List.length_append, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi' : i < u.length := List.mem_range.mp hi
    rw [List.take_append_of_le_length (by omega)]
  · apply List.map_congr_left
    intro i hi
    have hi' : i < v.length := List.mem_range.mp hi
    simp only [Function.comp_apply, List.take_append, List.take_of_length_le (by omega : u.length ≤ u.length + i),
      Nat.add_sub_cancel_left, charge_append, h, zero_add]

theorem coding_indexed (c : Letter) :
    (indexed (f := f) c).map p.coding = p.heights (f c) := by
  apply List.ext_getElem
  · simp [heights]
  · intro i hi hj
    simp [indexed, coding, heights]

/-- Coding E(w) gives prefix charges of the actual substituted source word. -/
theorem coding_expand (w : Word) :
    (expand (f := f) w).map p.coding = p.heights (subst f w) := by
  induction w with
  | nil => simp [heights]
  | cons c w ih =>
    rw [expand_cons, List.map_append, p.coding_indexed, ih, subst_cons,
      p.heights_append (p.charge_image c)]

theorem finite_height_identity (t : ℕ) (c : Letter) :
    (subst (image p.uniform t) (indexed (f := f) c)).map p.coding =
      p.heights (image f (t+1) c) := by
  have h := p.iterated_expand t [c]
  have he : subst (image p.uniform t) (indexed (f := f) c) = expand (f := f) (image f t c) := by
    simpa [subst] using h
  rw [he, p.coding_expand]
  rfl

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
