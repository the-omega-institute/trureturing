module
public import Init.Internal.Order.Basic
public import OmegaInit.Core
public import OmegaInit.System.IO

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Lean.Order.CCPO.mk.noConfusion Lean.Order.CompleteLattice.mk.noConfusion Lean.Order.FlatOrder.inner Lean.Order.FlatOrder.inner_mk Lean.Order.FlatOrder.instOrder Lean.Order.FlatOrder.mk Lean.Order.FlatOrder.mk_inj Lean.Order.FlatOrder.mk_inner Lean.Order.FlatOrder.rel Lean.Order.PartialOrder.mk.noConfusion)
end Omega
namespace Omega.Lean.Order
export _root_.Lean.Order (CCPO CompleteLattice FlatOrder PartialOrder chain chain_conj chain_empty empty_chain instCCPOUnit instCompleteLatticeUnit instPartialOrderUnit is_meet is_sup is_sup_unique monotone monotone_compose monotone_const monotone_id)
end Omega.Lean.Order
namespace Omega.Lean.Order.CCPO
export _root_.Lean.Order.CCPO (casesOn ctorIdx has_csup mk noConfusion noConfusionType rec recOn toPartialOrder)
end Omega.Lean.Order.CCPO
namespace Omega.Lean.Order.CompleteLattice
export _root_.Lean.Order.CompleteLattice (casesOn ctorIdx has_sup mk noConfusion noConfusionType rec recOn toPartialOrder)
end Omega.Lean.Order.CompleteLattice
namespace Omega.Lean.Order.FlatOrder.rel
export _root_.Lean.Order.FlatOrder.rel (bot casesOn rec recOn refl)
end Omega.Lean.Order.FlatOrder.rel
namespace Omega.Lean.Order.PartialOrder
export _root_.Lean.Order.PartialOrder (casesOn ctorIdx mk noConfusion noConfusionType rec recOn rel rel_antisymm rel_of_eq rel_refl rel_trans)
end Omega.Lean.Order.PartialOrder
namespace Omega.Lean.Order.Unit
export _root_.Lean.Order.Unit (unit_le)
end Omega.Lean.Order.Unit
