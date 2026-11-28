module
public import Init.System.ST

namespace OmegaChecks.InitPort.Alternatives

/-- Keep the carrier and its distinguished value together behind the region-indexed opaque function. -/
private def statePackage : Type → (Σ α : Type, α) :=
  Lean.opaqueId (fun _ => ⟨PUnit, PUnit.unit⟩)

public def Void.nonemptyType (σ : Type) : NonemptyType :=
  ⟨(statePackage σ).1, ⟨(statePackage σ).2⟩⟩

public def Void.mk {σ : Type} (_ : σ) : (Void.nonemptyType σ).type :=
  (statePackage σ).2

end OmegaChecks.InitPort.Alternatives
