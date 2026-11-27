module

public import Init.Data.List.Erase
public import Init.Data.List.Perm

/-! First-match erasure and permutation laws proved by structural recursion. -/
namespace OmegaChecks.InitPort.Alternatives
namespace List
open _root_.List

public theorem erase_eq_eraseP : type_of% @_root_.List.erase_eq_eraseP := by
  intro α inst lawful a xs
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rw [erase_cons, eraseP_cons, ih, BEq.comm (a := b) (b := a)]

public theorem length_erase : type_of% @_root_.List.length_erase := by
  intro α inst lawful a xs
  by_cases h : a ∈ xs
  · rw [ite_eq_left h, length_erase_of_mem h]
  · rw [ite_eq_right h, erase_of_not_mem h]

public theorem erase_append : type_of% @_root_.List.erase_append := by
  intro α inst lawful a xs ys
  by_cases h : a ∈ xs
  · rw [ite_eq_left h, erase_append_left _ h]
  · rw [ite_eq_right h, erase_append_right _ h]

public theorem eraseP_eq_nil_iff : type_of% @_root_.List.eraseP_eq_nil_iff := by
  intro α xs p
  constructor
  · intro empty
    cases xs with
    | nil => exact .inl rfl
    | cons x xs =>
      by_cases h : p x
      · rw [eraseP_cons_of_pos h] at empty
        exact .inr ⟨x, h, congrArg (x :: ·) empty⟩
      · rw [eraseP_cons_of_neg h] at empty
        exact nomatch empty
  · rintro (rfl | ⟨x, h, rfl⟩)
    · rfl
    · exact eraseP_cons_of_pos h

public theorem erase_eq_nil_iff : type_of% @_root_.List.erase_eq_nil_iff := by
  intro α inst lawful xs a
  rw [erase_eq_eraseP, eraseP_eq_nil_iff]
  exact ⟨fun h => h.elim Or.inl (fun ⟨x, hit, eq⟩ => .inr ((eq_of_beq hit) ▸ eq)),
    fun h => h.elim Or.inl (fun eq => .inr ⟨a, beq_self_eq_true _, eq⟩)⟩

public theorem Perm.filter : type_of% @_root_.List.Perm.filter := by
  intro α p xs ys perm
  induction perm with
  | nil => exact .nil
  | cons x _ ih =>
    cases h : p x with
    | false => simpa only [filter_cons_of_neg (Bool.eq_false_iff.mp h)] using ih
    | true => simpa only [filter_cons_of_pos h] using ih.cons x
  | swap x y xs =>
    cases hx : p x <;> cases hy : p y <;>
      simp only [filter_cons, hx, hy] <;> first | exact .refl _ | exact .swap _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

public theorem Pairwise.perm : type_of% @_root_.List.Pairwise.perm := by
  intro α R xs ys sorted perm symm
  induction perm with
  | nil => exact sorted
  | cons x hp ih =>
    obtain ⟨rel, tail⟩ := pairwise_cons.mp sorted
    exact .cons (fun y m => rel y (hp.mem_iff.mpr m)) (ih tail)
  | swap x y xs =>
    obtain ⟨hy, hxs⟩ := pairwise_cons.mp sorted
    obtain ⟨hx, tail⟩ := pairwise_cons.mp hxs
    refine .cons ?_ (.cons (fun z hz => hy z (.tail _ hz)) tail)
    intro z m
    cases m with
    | head => exact symm (hy _ mem_cons_self)
    | tail _ mz => exact hx z mz
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ sorted)

public theorem Perm.pairwise_iff : type_of% @_root_.List.Perm.pairwise_iff := by
  intro α r symm xs ys perm
  exact ⟨fun h => Pairwise.perm h perm symm, fun h => Pairwise.perm h perm.symm symm⟩

public theorem Nodup.perm : type_of% @_root_.List.Nodup.perm := by
  intro α xs ys nodup perm
  exact Pairwise.perm nodup perm (fun h => Ne.symm h)

public theorem Perm.any_eq : type_of% @_root_.List.Perm.any_eq := by
  intro α xs ys f perm
  apply Bool.eq_iff_iff.mpr
  rw [any_eq_true, any_eq_true]
  exact ⟨fun ⟨x, mem, h⟩ => ⟨x, perm.subset mem, h⟩,
    fun ⟨x, mem, h⟩ => ⟨x, perm.symm.subset mem, h⟩⟩

public theorem Perm.all_eq : type_of% @_root_.List.Perm.all_eq := by
  intro α xs ys f perm
  apply Bool.eq_iff_iff.mpr
  rw [all_eq_true, all_eq_true]
  exact ⟨fun h x m => h x (perm.symm.subset m), fun h x m => h x (perm.subset m)⟩

public theorem eraseIdx_eq_self : type_of% @_root_.List.eraseIdx_eq_self := by
  intro α xs k
  induction xs generalizing k with
  | nil => exact ⟨fun _ => Nat.zero_le _, fun _ => rfl⟩
  | cons a xs ih =>
    cases k with
    | zero => exact ⟨fun h => (cons_ne_self a xs h.symm).elim, fun le => (Nat.not_succ_le_zero _ le).elim⟩
    | succ k =>
      rw [eraseIdx_cons_succ]
      exact ⟨fun h => Nat.succ_le_succ (ih.mp (cons.inj h).2),
        fun le => congrArg (a :: ·) (ih.mpr (Nat.le_of_succ_le_succ le))⟩

public theorem Nodup.erase_eq_filter : type_of% @_root_.List.Nodup.erase_eq_filter := by
  intro α inst lawful xs nodup a
  induction nodup with
  | nil => rfl
  | @cons b xs unique tail ih =>
    by_cases hit : b == a
    · cases eq_of_beq hit
      rw [erase_cons_head, filter_cons_of_neg (p := (· != a)) (fun hit => (bne_iff_ne.mp hit) rfl)]
      exact (filter_eq_self.mpr (fun x mem => bne_iff_ne.mpr (unique x mem).symm)).symm
    · have ne : b ≠ a := fun eq => hit (beq_iff_eq.mpr eq)
      rw [erase_cons_tail hit, filter_cons_of_pos (p := (· != a)) (bne_iff_ne.mpr ne), ih]

public theorem Nodup.mem_erase_iff : type_of% @_root_.List.Nodup.mem_erase_iff := by
  intro α inst xs b lawful a nodup
  rw [Nodup.erase_eq_filter nodup, mem_filter]
  exact ⟨fun ⟨mem, hit⟩ => ⟨bne_iff_ne.mp hit, mem⟩, fun ⟨ne, mem⟩ => ⟨mem, bne_iff_ne.mpr ne⟩⟩

public theorem Nodup.not_mem_erase : type_of% @_root_.List.Nodup.not_mem_erase := by
  intros
  exact fun mem => (Nodup.mem_erase_iff ‹_› |>.mp mem).1 rfl

public theorem Perm.take : type_of% @_root_.List.Perm.take := by
  intro α xs ys perm i tails
  apply (perm_append_right_iff (xs.drop i)).mp
  rw [take_append_drop]
  have suffix := tails.symm.append_left (ys.take i)
  rw [take_append_drop] at suffix
  exact perm.trans suffix

public theorem Perm.drop : type_of% @_root_.List.Perm.drop := by
  intro α xs ys perm i heads
  apply (perm_append_left_iff (xs.take i)).mp
  rw [take_append_drop]
  have permutedHead := heads.symm.append_right (ys.drop i)
  rw [take_append_drop] at permutedHead
  exact perm.trans permutedHead

public theorem Perm.pmap : type_of% @_root_.List.Perm.pmap := by
  intro α β p f xs ys perm
  induction perm with
  | nil => intros; exact .nil
  | cons x perm ih => intros; exact (ih).cons _
  | swap x y xs => intros; exact .swap _ _ _
  | trans p₁ p₂ ih₁ ih₂ =>
    intro onFirst onLast
    exact (ih₁ (H₂ := fun a h => onLast a (p₂.subset h))).trans ih₂

public theorem eraseP_filter : type_of% @_root_.List.eraseP_filter := by
  intro α p f xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases keep : f x
    · rw [filter_cons_of_pos keep]
      by_cases hit : p x
      · rw [eraseP_cons_of_pos hit, eraseP_cons_of_pos (p := fun y => p y && f y) (Bool.and_eq_true_iff.mpr ⟨hit, keep⟩)]
      · have no : ¬(p x && f x) = true := fun h => hit (Bool.and_eq_true_iff.mp h).1
        rw [eraseP_cons_of_neg hit, eraseP_cons_of_neg (p := fun y => p y && f y) no, filter_cons_of_pos keep, ih]
    · have no : ¬(p x && f x) = true := fun h => keep (Bool.and_eq_true_iff.mp h).2
      rw [filter_cons_of_neg keep, eraseP_cons_of_neg (p := fun y => p y && f y) no, filter_cons_of_neg keep, ih]

/-- Removing the unique head from the target of a subset preserves all tail members. -/
private theorem subsetTailOfNodup {a : α} {xs ys : _root_.List α}
    (fresh : a ∉ xs) (sub : a :: xs ⊆ a :: ys) : xs ⊆ ys := by
  intro x member
  cases sub (.tail _ member) with
  | head => exact (fresh member).elim
  | tail _ found => exact found

public theorem Nodup.length_le_of_subset : type_of% @_root_.List.Nodup.length_le_of_subset := by
  intro α xs ys nodup sub
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
    obtain ⟨fresh, tail⟩ := nodup_cons.mp nodup
    obtain ⟨before, after, rfl⟩ := append_of_mem (sub mem_cons_self)
    have move := @perm_middle _ a before after
    have shorter := ih tail (subsetTailOfNodup fresh (fun {_} m => move.subset (sub m)))
    rw [move.length_eq]
    exact Nat.succ_le_succ shorter

public theorem perm_ext_iff_of_nodup : type_of% @_root_.List.perm_ext_iff_of_nodup := by
  intro α xs ys distinct unique
  refine ⟨fun perm _ => perm.mem_iff, ?_⟩
  intro same
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact .nil
    | cons y ys => exact nomatch (same y).mpr mem_cons_self
  | cons x xs ih =>
    obtain ⟨left, right, rfl⟩ := append_of_mem ((same x).mp mem_cons_self)
    have move := @perm_middle _ x left right
    have same' := fun a => (same a).trans move.mem_iff
    obtain ⟨fresh, tail⟩ := nodup_cons.mp distinct
    obtain ⟨outside, rem⟩ := nodup_cons.mp (Nodup.perm unique move)
    have forward := subsetTailOfNodup fresh (fun {a} m => (same' a).mp m)
    have backward := subsetTailOfNodup outside (fun {a} m => (same' a).mpr m)
    exact ((ih tail rem (fun _ => ⟨fun m => forward m, fun m => backward m⟩)).cons x).trans move.symm

public theorem perm_iff_count : type_of% @_root_.List.perm_iff_count := by
  intro α inst lawful xs ys
  refine ⟨fun perm => perm.count_eq, ?_⟩
  intro counts
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact .nil
    | cons y ys =>
      have bad := counts y
      rw [count_nil, count_cons_self] at bad
      exact (Nat.noConfusion bad)
  | cons a xs ih =>
    have mem : a ∈ ys := count_pos_iff.mp ((counts a) ▸ count_pos_iff.mpr mem_cons_self)
    have move := perm_cons_erase mem
    apply _root_.List.Perm.trans _ move.symm
    apply _root_.List.Perm.cons
    apply ih
    intro b
    have total := (counts b).trans (move.count_eq b)
    rw [count_cons, count_cons] at total
    exact Nat.add_right_cancel total

public theorem erase_filter : type_of% @_root_.List.erase_filter := by
  intro α inst a lawful f xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hit : x == a
    · cases eq_of_beq hit
      rw [erase_cons_head]
      by_cases yes : f a
      · rw [filter_cons_of_pos yes, erase_cons_head]
      · rw [filter_cons_of_neg yes]
        exact erase_of_not_mem (fun mem => yes (mem_filter.mp mem).2)
    · rw [erase_cons_tail hit]
      by_cases yes : f x
      · rw [filter_cons_of_pos yes, filter_cons_of_pos yes, erase_cons_tail hit, ih]
      · rw [filter_cons_of_neg yes, filter_cons_of_neg yes, ih]

public theorem erase_eq_eraseIdx_of_idxOf : type_of% @_root_.List.erase_eq_eraseIdx_of_idxOf := by
  intro α inst lawful xs a i eq
  cases eq
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [idxOf_cons, erase_cons]
    by_cases h : x == a
    · rw [ite_eq_left h, ite_eq_left h, eraseIdx_cons_zero]
    · rw [ite_eq_right h, ite_eq_right h, eraseIdx_cons_succ, ih]

public theorem eraseIdx_ne_nil_iff : type_of% @_root_.List.eraseIdx_ne_nil_iff := by
  intro α xs i
  cases xs with
  | nil =>
    exact ⟨fun h => (h rfl).elim, fun h => h.elim (fun le => (Nat.not_succ_le_zero _ le).elim)
      (fun ⟨eq, _⟩ => nomatch eq)⟩
  | cons x xs =>
    cases xs with
    | nil =>
      cases i with
      | zero =>
        exact ⟨fun h => (h rfl).elim, fun h => h.elim (fun le => (Nat.not_succ_le_self 1 le).elim)
          (fun ⟨_, ne⟩ => (ne rfl).elim)⟩
      | succ j =>
        exact ⟨fun _ => .inr ⟨rfl, Nat.succ_ne_zero _⟩, fun _ => cons_ne_nil _ _⟩
    | cons y ys =>
      have large : 2 ≤ (x :: y :: ys).length := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
      exact ⟨fun _ => .inl large, fun _ h =>
        match eraseIdx_eq_nil_iff.mp h with
        | .inl eq => nomatch eq
        | .inr ⟨eq, _⟩ => Nat.not_succ_le_self 1 (Nat.le_trans large (Nat.le_of_eq eq))⟩

public theorem perm_insert_swap : type_of% @_root_.List.perm_insert_swap := by
  intro α inst lawful x y xs
  by_cases hx : x ∈ xs
  · rw [insert_of_mem hx, insert_of_mem (mem_insert_iff.mpr (.inr hx))]
  · by_cases hy : y ∈ xs
    · rw [insert_of_mem hy, insert_of_mem (mem_insert_iff.mpr (.inr hy))]
    · by_cases hit : x == y
      · cases eq_of_beq hit
        exact .refl _
      · have ne := fun eq => hit (beq_iff_eq.mpr eq)
        rw [insert_of_not_mem hy, insert_of_not_mem hx,
          insert_of_not_mem (fun h => (mem_cons.mp h).elim ne hx),
          insert_of_not_mem (fun h => (mem_cons.mp h).elim (Ne.symm ne) hy)]
        exact .swap _ _ _

end List
end OmegaChecks.InitPort.Alternatives
