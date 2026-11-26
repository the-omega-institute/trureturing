module
public import Init.Data.Order.Lemmas
import all Init.Data.Order.PackageFactories
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

public theorem Std.LinearOrderPackage.ofLE._proof_1 : type_of% @_root_.Std.LinearOrderPackage.ofLE._proof_1 := by
  intro α args
  letI := args.le
  letI := args.decidableLE
  letI := args.min
  refine { min_eq_or := ?_, le_min_iff := ?_ }
  · intro a b
    rw [args.min_eq]
    split <;> first | exact Or.inl rfl | exact Or.inr rfl
  · intro a b c
    rw [args.min_eq]
    split
    · rename_i bc
      exact ⟨fun ab => ⟨ab, args.le_trans a b c ab bc⟩, And.left⟩
    · rename_i notBC
      exact ⟨fun ac => ⟨args.le_trans a c b ac ((args.le_total b c).resolve_left notBC), ac⟩, And.right⟩

public theorem Std.LinearOrderPackage.ofLE._proof_2 : type_of% @_root_.Std.LinearOrderPackage.ofLE._proof_2 := by
  intro α args
  letI := args.le
  letI := args.decidableLE
  letI := args.max
  refine { max_eq_or := ?_, max_le_iff := ?_ }
  · intro a b
    rw [args.max_eq]
    split <;> first | exact Or.inl rfl | exact Or.inr rfl
  · intro a b c
    rw [args.max_eq]
    split
    · rename_i ba
      exact ⟨fun ac => ⟨ac, args.le_trans b a c ba ac⟩, And.left⟩
    · rename_i notBA
      exact ⟨fun bc => ⟨args.le_trans a b c ((args.le_total b a).resolve_left notBA) bc, bc⟩, And.right⟩

end OmegaChecks.InitPort.Alternatives
