module
import all Init.Data.Order.Opposite
public import Init.Data.Order.Lemmas
import all Init.Data.Order.PackageFactories
public import OmegaChecks.InitPort.Alternatives.Compare

namespace OmegaChecks.InitPort.Alternatives

public theorem Std.OppositeOrderInstances.instLawfulOrderBEqOpposite :
    type_of% @_root_.Std.OppositeOrderInstances.instLawfulOrderBEqOpposite := by
  intro α le beq law
  apply @_root_.Std.LawfulOrderBEq.mk α beq le.opposite
  intro a b
  unfold LE.opposite
  exact (@_root_.Std.LawfulOrderBEq.beq_iff_le_and_ge α beq le law a b).trans and_comm


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

public theorem Std.OrientedCmp.of_gt_iff_lt : type_of% @_root_.Std.OrientedCmp.of_gt_iff_lt := by
  intro α cmp compatible
  constructor
  intro a b
  cases ab : cmp a b with
  | gt => rw [(compatible a b).mp ab]; rfl
  | lt => rw [(compatible b a).mpr ab]; rfl
  | eq =>
    cases ba : cmp b a with
    | eq => rfl
    | lt => exact Ordering.noConfusion (ab.symm.trans ((compatible a b).mpr ba))
    | gt => exact Ordering.noConfusion (ab.symm.trans ((compatible b a).mp ba))

public theorem Std.LinearPreorderPackage.ofOrd._proof_1 :
    type_of% @_root_.Std.LinearPreorderPackage.ofOrd._proof_1 := by
  intro α args a b
  letI := args.ord
  have isLT (o : Ordering) : o = .lt ↔ o.isLE = true ∧ ¬o.isGE = true := by
    cases o <;> decide
  exact (args.lt_iff a b).trans ((isLT (compare a b)).trans
    (and_congr (args.lawfulOrderOrd.isLE_compare a b) (not_congr (args.lawfulOrderOrd.isGE_compare a b))))

public theorem Std.LinearPreorderPackage.ofOrd._proof_3 :
    type_of% @_root_.Std.LinearPreorderPackage.ofOrd._proof_3 := by
  intro α args
  letI := args.le
  letI := args.beq
  refine { beq_iff_le_and_ge := ?_ }
  intro a b
  exact (args.beq_iff a b).trans (Ordering.eq_eq_iff_isLE_and_isGE.trans
    (and_congr (args.lawfulOrderOrd.isLE_compare a b) (args.lawfulOrderOrd.isGE_compare a b)))

public theorem Std.LinearPreorderPackage.ofOrd._proof_9 :
    type_of% @_root_.Std.LinearPreorderPackage.ofOrd._proof_9 := by
  intro α args law a b
  letI := args.ord
  have total (o : Ordering) : o.isLE = true ∨ o.isGE = true := by cases o <;> decide
  exact (total (compare a b)).elim (fun h => Or.inl ((law.isLE_compare a b).mp h))
    (fun h => Or.inr ((law.isGE_compare a b).mp h))

public theorem Std.LinearOrderPackage.ofOrd._proof_3 :
    type_of% @_root_.Std.LinearOrderPackage.ofOrd._proof_3 := by
  intro α args a b ab ba
  apply args.eq_of_compare a b
  exact Ordering.eq_eq_of_isLE_of_isGE ((args.lawfulOrderOrd.isLE_compare a b).mpr ab)
    ((args.lawfulOrderOrd.isGE_compare a b).mpr ba)

public theorem Std.LinearOrderPackage.ofOrd._proof_1 :
    type_of% @_root_.Std.LinearOrderPackage.ofOrd._proof_1 := by
  intro α args
  letI := _root_.Std.LinearPreorderPackage.ofOrd α args.toLinearPreorderOfOrdArgs
  letI := args.min
  refine { min_eq_or := ?_, le_min_iff := ?_ }
  · intro a b
    rw [args.min_eq]
    split <;> first | exact Or.inl rfl | exact Or.inr rfl
  · intro a b c
    rw [args.min_eq]
    split
    · rename_i bc
      exact ⟨fun ab => ⟨ab, _root_.Std.le_trans ab ((args.lawfulOrderOrd.isLE_compare b c).mp bc)⟩, And.left⟩
    · rename_i notBC
      have cb := _root_.Std.le_of_not_ge (fun bc => notBC ((args.lawfulOrderOrd.isLE_compare b c).mpr bc))
      exact ⟨fun ac => ⟨_root_.Std.le_trans ac cb, ac⟩, And.right⟩

public theorem Std.LinearOrderPackage.ofOrd._proof_2 :
    type_of% @_root_.Std.LinearOrderPackage.ofOrd._proof_2 := by
  intro α args
  letI := _root_.Std.LinearPreorderPackage.ofOrd α args.toLinearPreorderOfOrdArgs
  letI := args.max
  refine { max_eq_or := ?_, max_le_iff := ?_ }
  · intro a b
    rw [args.max_eq]
    split <;> first | exact Or.inl rfl | exact Or.inr rfl
  · intro a b c
    rw [args.max_eq]
    split
    · rename_i ba
      exact ⟨fun ac => ⟨ac, _root_.Std.le_trans ((args.lawfulOrderOrd.isGE_compare a b).mp ba) ac⟩, And.left⟩
    · rename_i notBA
      have ab := _root_.Std.le_of_not_ge (fun ba => notBA ((args.lawfulOrderOrd.isGE_compare a b).mpr ba))
      exact ⟨fun bc => ⟨_root_.Std.le_trans ab bc, bc⟩, And.right⟩

public theorem Std.instTransNotLtOfLawfulOrderLTOfTotalOfLe._proof_1 :
    type_of% @_root_.Std.instTransNotLtOfLawfulOrderLTOfTotalOfLe._proof_1 := by
  intro α lt le lawful total transitive
  have reverse {a b : α} (notLT : ¬ a < b) : ¬ ¬ b ≤ a := by
    intro notLE
    exact notLT (_root_.Std.lt_iff_le_and_not_ge.mpr ⟨(total.total a b).resolve_right notLE, notLE⟩)
  intro a b c ab bc ac
  exact reverse ab (fun ba => reverse bc (fun cb =>
    (_root_.Std.lt_iff_le_and_not_ge.mp ac).2 (transitive.trans cb ba)))

end OmegaChecks.InitPort.Alternatives
