import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedProperLimit

/-! Complete source telescope for the proper-limit constructor. This source
bridge is an audit attempt; it does not assert validated four-slot binding. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped Ordinal

namespace Reg.D5.S3.Topology.InverseLimit.SignedProperLimit

open _root_.D5.S3.Topology.InverseLimit.SignedProperLimit

structure SourceInputs where
  l : Ordinal.{0}
  history : Prefix l
  limit : Order.IsSuccLimit l
  countable : l < ω₁
  above : ω < l
  data : history.Data
  laws : history.Laws data

def conclusion (P : SourceInputs) : Prop := Nonempty (P.history.Extension P.data)

abbrev sourceScope := type_of% (@Prefix.exists_joint_proper_limit_extension)

/-- The source map retains all prefix, signed, eligible-domain and limit hypotheses. -/
theorem source_bridge : sourceScope ↔ ∀ P : SourceInputs, conclusion P := by
  constructor
  · intro h P
    exact h P.history P.limit P.countable P.above P.data P.laws
  · intro h l H hl hc hw D L
    exact h ⟨l, H, hl, hc, hw, D, L⟩

/-- This uses the actual constructor, and supplies no independent validation verdict. -/
theorem actual_positive : ∀ P : SourceInputs, conclusion P :=
  source_bridge.mp @Prefix.exists_joint_proper_limit_extension

end Reg.D5.S3.Topology.InverseLimit.SignedProperLimit
