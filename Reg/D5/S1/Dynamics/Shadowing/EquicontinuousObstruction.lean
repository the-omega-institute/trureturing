import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Shadowing.EquicontinuousObstruction

namespace Reg.D5.S1.Dynamics.Shadowing.EquicontinuousObstruction

universe u v w t

/- Full original theorem telescopes are retained below as compiler expressions.
The unfinished four-slot obligations are tracked by the existing issue
https://github.com/the-omega-institute/trureturing/issues/5214.

The observations are arbitrary clopens and all forward iterates K → X;
K-invariance is absent. The fixed-orbit obstruction chooses E and a before
all D,V. The contraction tolerance includes q=0 and n=0. A faithful dependent
realization needs an enrolled observation preserving these nested scopes,
plus a counterrealization, all-role sensitivity, observational dependence and
exact source reconstruction. None is replaced by a finite or invariant-K
specialization. These exact positive-law checks are partial audit attempts,
not Contract.Registration records or declared_validated claims.
-/

abbrev orbit_lifting_clopen_image_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.orbit_lifting_clopen_image.{u,v})
def orbit_lifting_clopen_image_actual : orbit_lifting_clopen_image_scope.{u,v} := @_root_.D5.S1.Dynamics.Shadowing.orbit_lifting_clopen_image.{u,v}
abbrev orbit_lifting_clopen_basis_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.orbit_lifting_clopen_basis.{u,v})
def orbit_lifting_clopen_basis_actual : orbit_lifting_clopen_basis_scope.{u,v} := @_root_.D5.S1.Dynamics.Shadowing.orbit_lifting_clopen_basis.{u,v}
abbrev connected_subset_not_source_relative_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.connected_subset_not_source_relative.{u,v})
def connected_subset_not_source_relative_actual : connected_subset_not_source_relative_scope.{u,v} := @_root_.D5.S1.Dynamics.Shadowing.connected_subset_not_source_relative.{u,v}
abbrev expansive_factor_locally_constant_on_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.expansive_factor_locally_constant_on.{u,v})
def expansive_factor_locally_constant_on_actual : expansive_factor_locally_constant_on_scope.{u,v} := @_root_.D5.S1.Dynamics.Shadowing.expansive_factor_locally_constant_on.{u,v}
abbrev expansive_factor_constant_on_connected_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.expansive_factor_constant_on_connected.{u,v})
def expansive_factor_constant_on_connected_actual : expansive_factor_constant_on_connected_scope.{u,v} := @_root_.D5.S1.Dynamics.Shadowing.expansive_factor_constant_on_connected.{u,v}
abbrev connected_fixed_orbit_obstruction_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.connected_fixed_orbit_obstruction.{u,v})
def connected_fixed_orbit_obstruction_actual : connected_fixed_orbit_obstruction_scope.{u,v} := @_root_.D5.S1.Dynamics.Shadowing.connected_fixed_orbit_obstruction.{u,v}
abbrev contraction_pseudo_orbit_estimate_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.contraction_pseudo_orbit_estimate.{u})
def contraction_pseudo_orbit_estimate_actual : contraction_pseudo_orbit_estimate_scope.{u} := @_root_.D5.S1.Dynamics.Shadowing.contraction_pseudo_orbit_estimate.{u}
abbrev contraction_hasShadowing_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.contraction_hasShadowing.{u})
def contraction_hasShadowing_actual : contraction_hasShadowing_scope.{u} := @_root_.D5.S1.Dynamics.Shadowing.contraction_hasShadowing.{u}
abbrev connected_contraction_shadowing_obstruction_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.connected_contraction_shadowing_obstruction.{u,v})
def connected_contraction_shadowing_obstruction_actual : connected_contraction_shadowing_obstruction_scope.{u,v} := @_root_.D5.S1.Dynamics.Shadowing.connected_contraction_shadowing_obstruction.{u,v}

end Reg.D5.S1.Dynamics.Shadowing.EquicontinuousObstruction
