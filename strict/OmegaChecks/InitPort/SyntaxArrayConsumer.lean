module
prelude
public import OmegaInit.Prelude

@[noinline] public unsafe def omegaTestMakeSyntaxArray (ks : @& Omega.Lean.SyntaxNodeKinds) (xs : @& Omega.Array Omega.Lean.Syntax) :
    Omega.Lean.TSyntaxArray ks := Omega.Lean.TSyntaxArray.mkImpl xs

@[noinline] public unsafe def omegaTestReadSyntaxArray (ks : @& Omega.Lean.SyntaxNodeKinds) (xs : @& Omega.Lean.TSyntaxArray ks) :
    Omega.Array Omega.Lean.Syntax := Omega.Lean.TSyntaxArray.rawImpl xs
