module
public import Init.System.ST

namespace OmegaChecks.InitPort.Alternatives

/-- A supplied payload inhabits the sealed result of the external swap operation. -/
public def ST.Prim.Ref.swap {σ α : Type} (_ : @& _root_.ST.Ref σ α) (value : α) : _root_.ST σ α :=
  _root_.ST.pure value

end OmegaChecks.InitPort.Alternatives
