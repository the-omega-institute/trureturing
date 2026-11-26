module
public import Init.MetaTypes

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Lean.Meta
export _root_.Lean.Meta (EtaStructMode TransparencyMode)
end Omega.Lean.Meta
namespace Omega.Lean.Meta.EtaStructMode
export _root_.Lean.Meta.EtaStructMode (all none notClasses rec recOn)
end Omega.Lean.Meta.EtaStructMode
namespace Omega.Lean.Meta.TransparencyMode
export _root_.Lean.Meta.TransparencyMode (all default implicit instances none rec recOn reducible)
end Omega.Lean.Meta.TransparencyMode
