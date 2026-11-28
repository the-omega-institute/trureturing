module
public import Init.Prelude

namespace OmegaChecks.InitPort.Alternatives

public def Lean.TSyntaxArray.rawImpl {ks : _root_.Lean.SyntaxNodeKinds} (xs : _root_.Lean.TSyntaxArray ks) :
    Array _root_.Lean.Syntax :=
  ⟨xs.toList.map _root_.Lean.TSyntax.raw⟩

public def Lean.TSyntaxArray.mkImpl {ks : _root_.Lean.SyntaxNodeKinds} (xs : Array _root_.Lean.Syntax) :
    _root_.Lean.TSyntaxArray ks :=
  ⟨xs.toList.map _root_.Lean.TSyntax.mk⟩

end OmegaChecks.InitPort.Alternatives
