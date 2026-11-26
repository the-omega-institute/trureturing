module
public import Init.Data.Order.Lemmas
public import OmegaChecks.InitPort.Alternatives.Compare

namespace OmegaChecks.InitPort.Alternatives

public theorem Std.lt_of_le_of_ne : type_of% @_root_.Std.lt_of_le_of_ne := by
  intro α le lt antisymm lawful a b forward different
  exact Std.lt_iff_le_and_not_ge.mpr
    ⟨forward, fun reverse => different (Std.Antisymm.antisymm a b forward reverse)⟩

public theorem Std.lt_iff_le_and_ne : type_of% @_root_.Std.lt_iff_le_and_ne := by
  intro α le lt lawful order a b
  exact ⟨fun strict => ⟨(Std.lt_iff_le_and_not_ge.mp strict).1, Std.ne_of_lt strict⟩,
    fun h => Std.lt_of_le_of_ne h.1 h.2⟩

public theorem Std.lt_min_iff : type_of% @_root_.Std.lt_min_iff := by
  intro α min le lt order inf lawful a b c
  refine ⟨fun h => ⟨Std.lt_of_lt_of_le h Std.min_le_left, Std.lt_of_lt_of_le h Std.min_le_right⟩, ?_⟩
  intro ⟨left, right⟩
  exact (Std.min_eq_or (a := b) (b := c)).elim (fun h => h.symm ▸ left) (fun h => h.symm ▸ right)

public theorem Std.max_lt_iff : type_of% @_root_.Std.max_lt_iff := by
  intro α max le lt order sup lawful a b c
  refine ⟨fun h => ⟨Std.lt_of_le_of_lt Std.left_le_max h, Std.lt_of_le_of_lt Std.right_le_max h⟩, ?_⟩
  intro ⟨left, right⟩
  exact (Std.max_eq_or (a := a) (b := b)).elim (fun h => h.symm ▸ left) (fun h => h.symm ▸ right)

end OmegaChecks.InitPort.Alternatives
