module
public import Init.Coe
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Coe Coe.mk.noConfusion CoeDep CoeDep.mk.noConfusion CoeFun CoeFun.mk.noConfusion CoeHTC CoeHTC.mk.noConfusion CoeHTCT CoeHTCT.mk.noConfusion CoeHead CoeHead.mk.noConfusion CoeOTC CoeOTC.mk.noConfusion CoeOut CoeOut.mk.noConfusion CoeSort CoeSort.mk.noConfusion CoeT CoeT.mk.noConfusion CoeTC CoeTC.mk.noConfusion CoeTail CoeTail.mk.noConfusion boolToProp boolToSort coeFunNotation coeNotation coeSortNotation decPropToBool instCoeHTC instCoeHTCOfCoeHeadOfCoeOTC instCoeHTCOfCoeOTC instCoeHTCT instCoeHTCTOfCoeHTC instCoeHTCTOfCoeTailOfCoeHTC instCoeOTC instCoeOTCOfCoeOut instCoeOTCOfCoeTC instCoeOutOfCoeFun instCoeOutOfCoeSort instCoeT instCoeTC instCoeTCOfCoe instCoeTCOfCoe_1 instCoeTOfCoeDep instCoeTOfCoeHTCT subtypeCoe)
end Omega
namespace Omega.Coe
export _root_.Coe (casesOn coe ctorIdx mk noConfusion noConfusionType rec recOn)
end Omega.Coe
namespace Omega.CoeDep
export _root_.CoeDep (casesOn coe ctorIdx mk noConfusion noConfusionType rec recOn)
end Omega.CoeDep
namespace Omega.CoeFun
export _root_.CoeFun (casesOn coe ctorIdx mk noConfusion noConfusionType rec recOn)
end Omega.CoeFun
namespace Omega.CoeHTC
export _root_.CoeHTC (casesOn coe ctorIdx mk noConfusion noConfusionType rec recOn)
end Omega.CoeHTC
namespace Omega.CoeHTCT
export _root_.CoeHTCT (casesOn coe ctorIdx mk noConfusion noConfusionType rec recOn)
end Omega.CoeHTCT
namespace Omega.CoeHead
export _root_.CoeHead (casesOn coe ctorIdx mk noConfusion noConfusionType rec recOn)
end Omega.CoeHead
namespace Omega.CoeOTC
export _root_.CoeOTC (casesOn coe ctorIdx mk noConfusion noConfusionType rec recOn)
end Omega.CoeOTC
namespace Omega.CoeOut
export _root_.CoeOut (casesOn coe ctorIdx mk noConfusion noConfusionType rec recOn)
end Omega.CoeOut
namespace Omega.CoeSort
export _root_.CoeSort (casesOn coe ctorIdx mk noConfusion noConfusionType rec recOn)
end Omega.CoeSort
namespace Omega.CoeT
export _root_.CoeT (casesOn coe ctorIdx mk noConfusion noConfusionType rec recOn)
end Omega.CoeT
namespace Omega.CoeTC
export _root_.CoeTC (casesOn coe ctorIdx mk noConfusion noConfusionType rec recOn)
end Omega.CoeTC
namespace Omega.CoeTail
export _root_.CoeTail (casesOn coe ctorIdx mk noConfusion noConfusionType rec recOn)
end Omega.CoeTail
namespace Omega.Lean.Internal
export _root_.Lean.Internal (coeM liftCoeM)
end Omega.Lean.Internal
