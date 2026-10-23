import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Shadowing.UniformTracing

namespace Reg.D5.S1.Dynamics.Shadowing.UniformTracing

universe u v w t

/- Full original theorem telescopes are retained below as compiler expressions.
The unfinished four-slot obligations are tracked by the existing issue
https://github.com/the-omega-institute/trureturing/issues/5214.

Cover observations depend on an arbitrary compact uniform space; SR and OL
quantify over every entourage, then every sequence and prescribed source.
A faithful intervention must change a genuine observation in these full
contracts while fixing the original systems and hypotheses. No validated
realization/reconstruction, whole-family sensitivity or enrolled readout
binding has been supplied; the target proofs below do not substitute for them.
-/

abbrev cover_shadowing_iff_uniform_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.cover_shadowing_iff_uniform.{u})
def cover_shadowing_iff_uniform_actual : cover_shadowing_iff_uniform_scope.{u} := @_root_.D5.S1.Dynamics.Shadowing.cover_shadowing_iff_uniform.{u}
abbrev source_relative_iff_orbit_lifting_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.source_relative_iff_orbit_lifting.{u,v})
def source_relative_iff_orbit_lifting_actual : source_relative_iff_orbit_lifting_scope.{u,v} := @_root_.D5.S1.Dynamics.Shadowing.source_relative_iff_orbit_lifting.{u,v}
abbrev positive_expansivity_source_relative_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.positive_expansivity_source_relative.{u,v})
def positive_expansivity_source_relative_actual : positive_expansivity_source_relative_scope.{u,v} := @_root_.D5.S1.Dynamics.Shadowing.positive_expansivity_source_relative.{u,v}

end Reg.D5.S1.Dynamics.Shadowing.UniformTracing
