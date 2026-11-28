module
public import Init.Data.Option.Instances
public import OmegaInit.Data.Option.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (
  Option.forM.match_1 Option.instForIn'InferInstanceMembershipOfMonad.match_1
  Option.instForIn'InferInstanceMembershipOfMonad.match_3 Option.pbind.match_1
  Option.pelim.match_1 Option.pfilter.match_1 Option.pmap.match_1)
end Omega
namespace Omega.Option
export _root_.Option (
  eq_none_of_isNone eq_of_eq_some forM instDecidableMemOfDecidableEq
  instForIn'InferInstanceMembershipOfMonad instForMOfMonad instMembership isNone_iff_eq_none
  mem_def pbind pelim pfilter pmap some_inj)
end Omega.Option
