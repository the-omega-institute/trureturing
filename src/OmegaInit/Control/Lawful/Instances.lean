module
public import Init.Control.Lawful.Instances
public import OmegaInit.Data.Option.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Option.elim.eq_1 Option.elim.eq_2 Option.map.eq_1 Option.map.eq_2 ReaderT.run_mk)
end Omega
