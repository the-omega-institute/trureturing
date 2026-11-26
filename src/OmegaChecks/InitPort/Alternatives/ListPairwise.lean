module
public import Init.Data.List.Pairwise

/-! Pairwise relations and equality of indices in lists without duplicates. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.pairwise_iff_getElem : type_of% @_root_.List.pairwise_iff_getElem := by
  intro α R xs
  induction xs with
  | nil => exact ⟨fun _ i _ hi => (Nat.not_lt_zero i hi).elim, fun _ => .nil⟩
  | cons x xs ih =>
    constructor
    · intro h i j hi hj lt
      obtain ⟨head, tail⟩ := _root_.List.pairwise_cons.mp h
      cases j with
      | zero => exact (Nat.not_lt_zero _ lt).elim
      | succ j =>
        cases i with
        | zero => exact head _ (_root_.List.getElem_mem (Nat.lt_of_succ_lt_succ hj))
        | succ i =>
          exact ih.mp tail i j (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj)
            (Nat.lt_of_succ_lt_succ lt)
    · intro h
      apply _root_.List.Pairwise.cons
      · intro y mem
        obtain ⟨j, hj, rfl⟩ := _root_.List.mem_iff_getElem.mp mem
        exact h 0 (j+1) (Nat.zero_lt_succ _) (Nat.succ_lt_succ hj) (Nat.zero_lt_succ j)
      · exact ih.mpr fun i j hi hj lt =>
          h (i+1) (j+1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj) (Nat.succ_lt_succ lt)

public theorem List.pairwise_append_comm : type_of% @_root_.List.pairwise_append_comm := by
  intro α R sym xs ys
  have swap {xs ys : _root_.List α} (h : _root_.List.Pairwise R (xs ++ ys)) :
      _root_.List.Pairwise R (ys ++ xs) := by
    obtain ⟨px, py, cross⟩ := _root_.List.pairwise_append.mp h
    exact _root_.List.pairwise_append.mpr ⟨py, px, fun y hy x hx => sym (cross x hx y hy)⟩
  exact ⟨swap, swap⟩


public theorem List.pairwise_of_forall : type_of% @_root_.List.pairwise_of_forall := by
  intro α R xs rel
  exact List.pairwise_iff_getElem.mpr fun _ _ _ _ _ => rel _ _

public theorem List.nodup_iff_eq_of_getElem_eq : type_of% @_root_.List.nodup_iff_eq_of_getElem_eq := by
  intro α xs
  constructor
  · intro h i j hi hj eq
    obtain (lt | rfl | gt) := Nat.lt_trichotomy i j
    · exact ((List.pairwise_iff_getElem.mp h) i j hi hj lt eq).elim
    · rfl
    · exact ((List.pairwise_iff_getElem.mp h) j i hj hi gt eq.symm).elim
  · intro h
    exact List.pairwise_iff_getElem.mpr fun i j hi hj lt eq => Nat.ne_of_lt lt (h i j hi hj eq)

public theorem List.Nodup.eq_of_getElem?_eq : type_of% @_root_.List.Nodup.eq_of_getElem?_eq := by
  intro α i j xs nodup hi eq
  have atJ := eq.symm.trans (getElem?_pos xs i hi)
  obtain ⟨hj, same⟩ := getElem?_eq_some_iff.mp atJ
  exact (List.nodup_iff_eq_of_getElem_eq.mp nodup) i j hi hj same.symm

public theorem List.Nodup.getElem?_inj : type_of% @_root_.List.Nodup.getElem?_inj := by
  intros
  exact ⟨List.Nodup.eq_of_getElem?_eq ‹_› ‹_›, fun h => h ▸ rfl⟩

public theorem List.Nodup.getD_inj : type_of% @_root_.List.Nodup.getD_inj := by
  intro α i j fallback xs hi hj nodup
  rw [_root_.List.getD_eq_getElem?_getD, _root_.List.getD_eq_getElem?_getD,
    getElem?_pos xs i hi, getElem?_pos xs j hj]
  exact _root_.List.Nodup.getElem_inj nodup

public theorem List.Nodup.getElem!_inj : type_of% @_root_.List.Nodup.getElem!_inj := by
  intro α i j inh xs hi hj nodup
  rw [getElem!_pos xs i hi, getElem!_pos xs j hj]
  exact _root_.List.Nodup.getElem_inj nodup


public theorem List.pairwise_replicate : type_of% @_root_.List.pairwise_replicate := by
  intro α R n a
  constructor
  · intro h
    by_cases short : n ≤ 1
    · exact .inl short
    · have h1 : 1 < n := Nat.lt_of_not_ge short
      have b1 : 1 < (_root_.List.replicate n a).length := _root_.List.length_replicate.symm ▸ h1
      have b0 := Nat.lt_trans (Nat.zero_lt_succ 0) b1
      have rel := List.pairwise_iff_getElem.mp h 0 1 b0 b1 (Nat.zero_lt_succ 0)
      rw [_root_.List.getElem_replicate b0, _root_.List.getElem_replicate b1] at rel
      exact .inr rel
  · rintro (short | rel) <;> apply List.pairwise_iff_getElem.mpr <;> intro i j hi hj lt
    · rw [_root_.List.length_replicate] at hj
      exact (Nat.not_lt_of_ge short (Nat.lt_of_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le i) lt) hj)).elim
    · rw [_root_.List.getElem_replicate hi, _root_.List.getElem_replicate hj]
      exact rel

public theorem List.nodup_replicate : type_of% @_root_.List.nodup_replicate := by
  intros
  exact ⟨fun h => (List.pairwise_replicate.mp h).elim id (fun ne => (ne rfl).elim),
    fun h => List.pairwise_replicate.mpr (.inl h)⟩

public theorem List.pairwise_filterMap : type_of% @_root_.List.pairwise_filterMap := by
  intro α R β f xs
  induction xs with
  | nil => exact ⟨fun _ => .nil, fun _ => .nil⟩
  | cons a xs ih =>
    cases fa : f a with
    | none =>
      rw [_root_.List.filterMap_cons_none fa]
      constructor
      · intro h
        exact .cons (fun _ _ _ eq => nomatch fa.symm.trans eq) (ih.mp h)
      · intro h
        exact ih.mpr h.of_cons
    | some b =>
      rw [_root_.List.filterMap_cons_some fa]
      constructor
      · intro h
        obtain ⟨head, tail⟩ := _root_.List.pairwise_cons.mp h
        refine .cons ?_ (ih.mp tail)
        intro a' mem c eq d fd
        cases Option.some.inj (fa.symm.trans eq)
        exact head d (_root_.List.mem_filterMap.mpr ⟨a', mem, fd⟩)
      · intro h
        obtain ⟨head, tail⟩ := _root_.List.pairwise_cons.mp h
        refine .cons ?_ (ih.mpr tail)
        intro d mem
        obtain ⟨a', mem', fd⟩ := _root_.List.mem_filterMap.mp mem
        exact head a' mem' b fa d fd

public theorem List.pairwise_filter : type_of% @_root_.List.pairwise_filter := by
  intro α R p xs
  induction xs with
  | nil => exact ⟨fun _ => .nil, fun _ => .nil⟩
  | cons a xs ih =>
    by_cases pa : p a
    · rw [_root_.List.filter_cons_of_pos pa]
      constructor
      · intro h
        obtain ⟨head, tail⟩ := _root_.List.pairwise_cons.mp h
        exact .cons (fun b mem _ pb => head b (_root_.List.mem_filter.mpr ⟨mem, pb⟩)) (ih.mp tail)
      · intro h
        obtain ⟨head, tail⟩ := _root_.List.pairwise_cons.mp h
        exact .cons (fun b mem => let ⟨hx, pb⟩ := _root_.List.mem_filter.mp mem; head b hx pa pb) (ih.mpr tail)
    · rw [_root_.List.filter_cons_of_neg pa]
      exact ⟨fun h => .cons (fun _ _ bad => (pa bad).elim) (ih.mp h),
        fun h => ih.mpr h.of_cons⟩

public theorem List.pairwise_flatten : type_of% @_root_.List.pairwise_flatten := by
  intro α R xss
  induction xss with
  | nil => exact ⟨fun _ => ⟨(fun _ m => nomatch m), .nil⟩, fun _ => .nil⟩
  | cons xs xss ih =>
    constructor
    · intro h
      obtain ⟨first, tail, cross⟩ := _root_.List.pairwise_append.mp h
      obtain ⟨inside, between⟩ := ih.mp tail
      refine ⟨?_, .cons (fun ys hy x hx y mem =>
        cross x hx y (_root_.List.mem_flatten.mpr ⟨ys, hy, mem⟩)) between⟩
      intro ys mem
      cases mem with
      | head => exact first
      | tail _ hy => exact inside ys hy
    · rintro ⟨inside, between⟩
      obtain ⟨first, tail⟩ := _root_.List.pairwise_cons.mp between
      refine _root_.List.pairwise_append.mpr ⟨inside xs (.head _),
        ih.mpr ⟨fun ys mem => inside ys (.tail _ mem), tail⟩, ?_⟩
      intro x hx y hy
      obtain ⟨ys, mem, hy⟩ := _root_.List.mem_flatten.mp hy
      exact first ys mem x hx y hy

public theorem List.pairwise_flatMap : type_of% @_root_.List.pairwise_flatMap := by
  intro β α R xs f
  change _root_.List.Pairwise R (xs.map f).flatten ↔ _
  exact List.pairwise_flatten.trans (and_congr _root_.List.forall_mem_map _root_.List.pairwise_map)

public theorem List.pairwise_middle : type_of% @_root_.List.pairwise_middle := by
  intro α R sym a xs ys
  constructor
  · intro h
    obtain ⟨px, py, cross⟩ := _root_.List.pairwise_append.mp h
    obtain ⟨head, py⟩ := _root_.List.pairwise_cons.mp py
    refine .cons ?_ (_root_.List.pairwise_append.mpr ⟨px, py, fun x hx y hy => cross x hx y (.tail _ hy)⟩)
    intro z mem
    exact (_root_.List.mem_append.mp mem).elim (fun hx => sym (cross z hx a (.head _))) (head z)
  · intro h
    obtain ⟨head, tail⟩ := _root_.List.pairwise_cons.mp h
    obtain ⟨px, py, cross⟩ := _root_.List.pairwise_append.mp tail
    refine _root_.List.pairwise_append.mpr ⟨px, .cons (fun z hz => head z (_root_.List.mem_append.mpr (.inr hz))) py, ?_⟩
    intro x hx z hz
    cases hz with
    | head => exact sym (head x (_root_.List.mem_append.mpr (.inl hx)))
    | tail _ hz => exact cross x hx z hz

end OmegaChecks.InitPort.Alternatives
