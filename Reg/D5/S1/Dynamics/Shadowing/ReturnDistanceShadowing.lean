import D5.S1.Dynamics.Shadowing.ReturnDistanceShadowing

namespace Reg.D5.S1.Dynamics.Shadowing.ReturnDistanceShadowing

universe u

/- The full original telescopes below are typed positive-law attempts.
A faithful four-slot registration remains unfinished: source reconstruction,
whole-family variation and sensitivity, observational dependence, and enrolled
readout binding have not been supplied. These checks are neither
Contract.Registration values nor declared_validated evidence.
The nested natural-time and integer-coordinate domains are preserved.
Coordination: https://github.com/the-omega-institute/trureturing/issues/5214. -/

abbrev neighborhood_two_of_pair_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.neighborhood_two_of_pair.{u})
def neighborhood_two_of_pair_actual : neighborhood_two_of_pair_scope.{u} := @_root_.D5.S1.Dynamics.Shadowing.neighborhood_two_of_pair.{u}

abbrev finite_integer_window_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.finite_integer_window)
def finite_integer_window_actual : finite_integer_window_scope := @_root_.D5.S1.Dynamics.Shadowing.finite_integer_window

abbrev return_metric_window_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.return_metric_window)
def return_metric_window_actual : return_metric_window_scope := @_root_.D5.S1.Dynamics.Shadowing.return_metric_window

abbrev return_window_control_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.return_window_control)
def return_window_control_actual : return_window_control_scope := @_root_.D5.S1.Dynamics.Shadowing.return_window_control

abbrev past_extension_overlap_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.past_extension_overlap.{u})
def past_extension_overlap_actual : past_extension_overlap_scope.{u} := @_root_.D5.S1.Dynamics.Shadowing.past_extension_overlap.{u}

abbrev signed_diagonal_overlap_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.signed_diagonal_overlap.{u})
def signed_diagonal_overlap_actual : signed_diagonal_overlap_scope.{u} := @_root_.D5.S1.Dynamics.Shadowing.signed_diagonal_overlap.{u}

abbrev return_shift_iterate_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.return_shift_iterate)
def return_shift_iterate_actual : return_shift_iterate_scope := @_root_.D5.S1.Dynamics.Shadowing.return_shift_iterate

abbrev return_bit_ext_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.return_bit_ext)
def return_bit_ext_actual : return_bit_ext_scope := @_root_.D5.S1.Dynamics.Shadowing.return_bit_ext

abbrev unbounded_return_neighborhood_two_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.unbounded_return_neighborhood_two)
def unbounded_return_neighborhood_two_actual : unbounded_return_neighborhood_two_scope := @_root_.D5.S1.Dynamics.Shadowing.unbounded_return_neighborhood_two

end Reg.D5.S1.Dynamics.Shadowing.ReturnDistanceShadowing
