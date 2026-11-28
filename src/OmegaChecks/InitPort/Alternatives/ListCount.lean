module
public import Init.Data.List.Count

/-! Count elements by induction on a sublist or on the inputs of a traversal.

The full-function equality `List.countP_eq_length_filter'` is open. The public
`countP` reduces to `countP.go p xs 0` for a variable list. Its pointwise
agreement with the length of the filtered list is `List.countP_eq_length_filter`. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.Sublist.countP_le : type_of% @_root_.List.Sublist.countP_le := by
  intro α p xs ys sub
  induction sub with
  | slnil => exact Nat.le_refl _
  | cons a _ ih =>
    rw [_root_.List.countP_cons]
    exact Nat.le_trans ih (Nat.le_add_right ..)
  | cons_cons a _ ih =>
    rw [_root_.List.countP_cons, _root_.List.countP_cons]
    exact Nat.add_le_add_right ih _

public theorem List.countP_flatten : type_of% @_root_.List.countP_flatten := by
  intro α p xs
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change (a ++ as.flatten).countP p = a.countP p + _
    rw [_root_.List.countP_append, ih]
    rfl

public theorem List.countP_flatMap : type_of% @_root_.List.countP_flatMap := by
  intro α β p xs f
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change (f a ++ as.flatMap f).countP p = (f a).countP p + _
    rw [_root_.List.countP_append, ih]
    rfl

public theorem List.count_flatten : type_of% @_root_.List.count_flatten := by
  intros
  apply List.countP_flatten

public theorem List.count_flatMap : type_of% @_root_.List.count_flatMap := by
  intros
  apply List.countP_flatMap

public theorem List.countP_filterMap : type_of% @_root_.List.countP_filterMap := by
  intro α β p f xs
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [_root_.List.filterMap_cons, _root_.List.countP_cons]
    cases f a with
    | none => exact ih
    | some b =>
      rw [_root_.List.countP_cons, ih]
      rfl

public theorem List.count_filterMap : type_of% @_root_.List.count_filterMap := by
  intro β α inst b f xs
  rw [_root_.List.count_eq_countP, List.countP_filterMap]
  apply _root_.List.countP_congr
  intro a _
  cases f a <;> rfl

public theorem List.filter_eq : type_of% @_root_.List.filter_eq := by
  intro α inst lawful dec xs a
  apply Eq.trans (_root_.List.filter_congr _)
  · exact _root_.List.filter_beq a
  · intro x _
    exact (Bool.beq_eq_decide_eq x a).symm

public theorem List.length_eq_countP_add_countP : type_of% @_root_.List.length_eq_countP_add_countP := by
  intro α p xs
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [_root_.List.length_cons, _root_.List.countP_cons, _root_.List.countP_cons, ih]
    cases p a with
    | false => exact rfl
    | true => exact (Nat.succ_add ..).symm

public theorem List.countP_eq_zero : type_of% @_root_.List.countP_eq_zero := by
  intro α xs p
  constructor
  · intro eq a member yes
    have pos := _root_.List.countP_pos_iff.mpr ⟨a, member, yes⟩
    exact (Nat.lt_irrefl 0) (eq ▸ pos)
  · intro never
    apply Nat.eq_zero_of_not_pos
    intro pos
    obtain ⟨a, member, yes⟩ := _root_.List.countP_pos_iff.mp pos
    exact never a member yes

public theorem List.count_filter : type_of% @_root_.List.count_filter := by
  intro α inst lawful p a xs h
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    by_cases yes : p b = true
    · rw [_root_.List.filter_cons_of_pos yes, _root_.List.count_cons, _root_.List.count_cons, ih]
    · have ne : b ≠ a := fun eq => yes (eq ▸ h)
      rw [_root_.List.filter_cons_of_neg yes, _root_.List.count_cons_of_ne ne, ih]

private theorem eraseConsTail [BEq α] {a b : α} (xs : _root_.List α) (h : ¬(b == a)) :
    (b :: xs).erase a = b :: xs.erase a := by
  change (match b == a with | true => xs | false => b :: xs.erase a) = _
  cases eq : b == a with
  | false => rfl
  | true => exact (h eq).elim

public theorem List.count_erase : type_of% @_root_.List.count_erase := by
  intro α inst lawful a b xs
  letI : DecidableEq α := _root_.instDecidableEqOfLawfulBEq
  by_cases same : b = a
  · subst b
    rw [ite_eq_left (beq_self_eq_true a)]
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      by_cases eq : x = a
      · subst x
        rw [_root_.List.erase_cons, ite_eq_left (beq_self_eq_true a), _root_.List.count_cons_self, Nat.add_one_sub_one]
      · have diff : ¬(x == a) := fun h => eq (eq_of_beq h)
        rw [eraseConsTail xs diff, _root_.List.count_cons_of_ne eq,
          _root_.List.count_cons_of_ne eq, ih]
  · rw [ite_eq_right (fun h => same (eq_of_beq h)), Nat.sub_zero]
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      by_cases eq : x = b
      · subst x
        rw [_root_.List.erase_cons, ite_eq_left (beq_self_eq_true b), _root_.List.count_cons_of_ne same]
      · have diff : ¬(x == b) := fun h => eq (eq_of_beq h)
        rw [eraseConsTail xs diff, _root_.List.count_cons, _root_.List.count_cons, ih]

public theorem List.count_erase_self : type_of% @_root_.List.count_erase_self := by
  intro α inst lawful a xs
  rw [List.count_erase, ite_eq_left (beq_self_eq_true a)]

public theorem List.count_erase_of_ne : type_of% @_root_.List.count_erase_of_ne := by
  intro α inst lawful a b ne xs
  rw [List.count_erase, ite_eq_right (fun h => ne (eq_of_beq h).symm), Nat.sub_zero]

public theorem List.countP_replicate : type_of% @_root_.List.countP_replicate := by
  intro α p a n
  by_cases h : p a = true
  · rw [ite_eq_left h]
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [_root_.List.replicate_succ, _root_.List.countP_cons_of_pos h, ih]
  · rw [ite_eq_right h]
    exact List.countP_eq_zero.mpr (fun x mem => (_root_.List.eq_of_mem_replicate mem) ▸ h)

end OmegaChecks.InitPort.Alternatives
