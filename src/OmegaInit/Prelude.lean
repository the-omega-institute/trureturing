module
public import Init.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (And Bool Empty Eq False HEq List List.brecOn.go Nat Nonempty Not Option Or PEmpty PProd PUnit ReaderT ReaderT.adapt ReaderT.mk ReaderT.run True Unit Unit.unit absurd cast cond congr congrArg congrFun congrFun' eq_of_heq heq_of_eq id id_eq inferInstance namedPattern optParam outParam rfl semiOutParam «inferInstanceAs»)
end Omega
namespace Omega.And
export _root_.And (casesOn intro left rec recOn right)
end Omega.And
namespace Omega.Bool
export _root_.Bool (Reflects and and_eq_internalAnd beq dcond eq_false_of_ne_true eq_true_of_ne_false false ne_false_of_eq_true ne_true_of_eq_false not not_eq_internalNot or or_eq_internalOr rec recOn true)
end Omega.Bool
namespace Omega.Bool.Internal
export _root_.Bool.Internal (and not or)
end Omega.Bool.Internal
namespace Omega.Empty
export _root_.Empty (casesOn noConfusion noConfusionType rec recOn)
end Omega.Empty
namespace Omega.Eq
export _root_.Eq (casesOn ndrec ndrec_symm rec recOn refl subst symm trans)
end Omega.Eq
namespace Omega.False
export _root_.False (elim rec recOn)
end Omega.False
namespace Omega.Function
export _root_.Function (comp const)
end Omega.Function
namespace Omega.HEq
export _root_.HEq (casesOn rec recOn refl rfl)
end Omega.HEq
namespace Omega.List
export _root_.List (append below brecOn casesOn cons length nil rec recOn)
end Omega.List
namespace Omega.Nat
export _root_.Nat (add beq ble div le le_antisymm le_of_succ_le_succ le_refl le_trans lt mod mod_lt mul not_succ_le_zero pow pred rec recOn sub succ succ_le_succ succ_sub_succ_eq_sub zero zero_le)
end Omega.Nat
namespace Omega.Nat.le
export _root_.Nat.le (casesOn rec recOn refl step)
end Omega.Nat.le
namespace Omega.Nonempty
export _root_.Nonempty (casesOn elim intro rec recOn)
end Omega.Nonempty
namespace Omega.Option
export _root_.Option (casesOn getD map none rec recOn some)
end Omega.Option
namespace Omega.Or
export _root_.Or (casesOn elim inl inr intro_left intro_right neg_resolve_left neg_resolve_right rec recOn resolve_left resolve_right)
end Omega.Or
namespace Omega.PEmpty
export _root_.PEmpty (casesOn noConfusion noConfusionType rec recOn)
end Omega.PEmpty
namespace Omega.PProd
export _root_.PProd (casesOn fst mk rec recOn snd)
end Omega.PProd
namespace Omega.PUnit
export _root_.PUnit (casesOn rec recOn unit)
end Omega.PUnit
namespace Omega.True
export _root_.True (intro rec recOn)
end Omega.True
