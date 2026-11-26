module
public import Init.Data.List.Sort.Lemmas
import all Init.Data.List.Sort.Basic

/-! Length, membership and stability of the comparison used by merge sort. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.length_merge : type_of% @_root_.List.length_merge := by
  intros
  exact (_root_.List.merge_perm_append _).length_eq.trans _root_.List.length_append

public theorem List.mem_merge : type_of% @_root_.List.mem_merge := by
  intros
  exact (_root_.List.merge_perm_append _).mem_iff.trans _root_.List.mem_append

private theorem zipIdxSpec {α : Type u} {le : α → α → Bool} {a b : α × Nat} :
    _root_.List.zipIdxLE le a b ↔ le a.1 b.1 ∧ (le b.1 a.1 → a.2 ≤ b.2) := by
  unfold _root_.List.zipIdxLE
  by_cases ab : le a.1 b.1
  · rw [ite_eq_left ab]
    by_cases ba : le b.1 a.1
    · rw [ite_eq_left ba]
      exact ⟨fun yes => ⟨ab, fun _ => of_decide_eq_true yes⟩,
        fun ⟨_, order⟩ => decide_eq_true (order ba)⟩
    · rw [ite_eq_right ba]
      exact ⟨fun _ => ⟨ab, fun h => (ba h).elim⟩, fun _ => rfl⟩
  · rw [ite_eq_right ab]
    exact ⟨(fun h => nomatch h), fun h => (ab h.1).elim⟩

public theorem List.zipIdxLE_trans : type_of% @_root_.List.zipIdxLE_trans := by
  intro α le trans a b c hab hbc
  obtain ⟨ab, iab⟩ := zipIdxSpec.mp hab
  obtain ⟨bc, ibc⟩ := zipIdxSpec.mp hbc
  exact zipIdxSpec.mpr ⟨trans _ _ _ ab bc, fun ca =>
    Nat.le_trans (iab (trans _ _ _ bc ca)) (ibc (trans _ _ _ ca ab))⟩

public theorem List.zipIdxLE_total : type_of% @_root_.List.zipIdxLE_total := by
  intro α le total a b
  apply Bool.or_eq_true_iff.mpr
  by_cases ab : le a.1 b.1
  · by_cases ba : le b.1 a.1
    · obtain (h | h) := Nat.le_total a.2 b.2
      · exact .inl (zipIdxSpec.mpr ⟨ab, fun _ => h⟩)
      · exact .inr (zipIdxSpec.mpr ⟨ba, fun _ => h⟩)
    · exact .inl (zipIdxSpec.mpr ⟨ab, fun h => (ba h).elim⟩)
  · have ba := (Bool.or_eq_true_iff.mp (total a.1 b.1)).resolve_left ab
    exact .inr (zipIdxSpec.mpr ⟨ba, fun h => (ab h).elim⟩)

public theorem List.pairwise_merge : type_of% @_root_.List.pairwise_merge := by
  intro α le trans total xs ys px py
  induction xs generalizing ys with
  | nil => rw [_root_.List.nil_merge]; exact py
  | cons x xs ih =>
    induction ys with
    | nil => rw [_root_.List.merge_right]; exact px
    | cons y ys iy =>
      obtain ⟨headX, tailX⟩ := _root_.List.pairwise_cons.mp px
      obtain ⟨headY, tailY⟩ := _root_.List.pairwise_cons.mp py
      by_cases h : le x y
      · rw [_root_.List.cons_merge_cons_pos le _ _ h]
        refine .cons ?_ (ih _ tailX py)
        intro z mem
        obtain (m | m) := List.mem_merge.mp mem
        · exact headX z m
        · cases m with
          | head => exact h
          | tail _ m => exact trans _ _ _ h (headY z m)
      · rw [_root_.List.cons_merge_cons_neg le _ _ h]
        have yx := (Bool.or_eq_true_iff.mp (total x y)).resolve_left h
        refine .cons ?_ (iy tailY)
        intro z mem
        obtain (m | m) := List.mem_merge.mp mem
        · cases m with
          | head => exact yx
          | tail _ m => exact trans _ _ _ yx (headX z m)
        · exact headY z m

end OmegaChecks.InitPort.Alternatives
