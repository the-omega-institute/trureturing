import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetIntertwiner

/-! Exact original source telescopes and typed proof bridges.
Four-slot registration evidence remains incomplete. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeDualCosetIntertwiner

open _root_.D5.S3.VertexAlgebra.LatticeDualCosetIntertwiner

/- Exact original telescopes and proof terms are source evidence.
   They are not four-slot registrations or validated audit certificates. -/
abbrev sourceScope_mode_smul_source :=
  type_of% (@mode_smul_source)
theorem source_actual_mode_smul_source : sourceScope_mode_smul_source :=
  @mode_smul_source

abbrev sourceScope_mode_add_source :=
  type_of% (@mode_add_source)
theorem source_actual_mode_add_source : sourceScope_mode_add_source :=
  @mode_add_source

abbrev sourceScope_ward :=
  type_of% (@ward)
theorem source_actual_ward : sourceScope_ward :=
  @ward

abbrev sourceScope_current_ground :=
  type_of% (@current_ground)
theorem source_actual_current_ground : sourceScope_current_ground :=
  @current_ground

abbrev sourceScope_ground_current_ward :=
  type_of% (@ground_current_ward)
theorem source_actual_ground_current_ward : sourceScope_ground_current_ward :=
  @ground_current_ward

abbrev sourceScope_energy_ward :=
  type_of% (@energy_ward)
theorem source_actual_energy_ward : sourceScope_energy_ward :=
  @energy_ward

abbrev sourceScope_current_component :=
  type_of% (@current_component)
theorem source_actual_current_component : sourceScope_current_component :=
  @current_component

abbrev sourceScope_coefficient_charge :=
  type_of% (@coefficient_charge)
theorem source_actual_coefficient_charge : sourceScope_coefficient_charge :=
  @coefficient_charge

abbrev sourceScope_ground_charge :=
  type_of% (@ground_charge)
theorem source_actual_ground_charge : sourceScope_ground_charge :=
  @ground_charge

abbrev sourceScope_ground_charge_projection :=
  type_of% (@ground_charge_projection)
theorem source_actual_ground_charge_projection : sourceScope_ground_charge_projection :=
  @ground_charge_projection

abbrev sourceScope_ground_energy_difference :=
  type_of% (@ground_energy_difference)
theorem source_actual_ground_energy_difference : sourceScope_ground_energy_difference :=
  @ground_energy_difference

abbrev sourceScope_ground_L0 :=
  type_of% (@ground_L0)
theorem source_actual_ground_L0 : sourceScope_ground_L0 :=
  @ground_L0

abbrev sourceScope_dual_add :=
  type_of% (@dual_add)
theorem source_actual_dual_add : sourceScope_dual_add :=
  @dual_add

abbrev sourceScope_ground_eigen :=
  type_of% (@ground_eigen)
theorem source_actual_ground_eigen : sourceScope_ground_eigen :=
  @ground_eigen

abbrev sourceScope_ground_spectrum :=
  type_of% (@ground_spectrum)
theorem source_actual_ground_spectrum : sourceScope_ground_spectrum :=
  @ground_spectrum

abbrev sourceScope_ground_below :=
  type_of% (@ground_below)
theorem source_actual_ground_below : sourceScope_ground_below :=
  @ground_below

abbrev sourceScope_ground_leading :=
  type_of% (@ground_leading)
theorem source_actual_ground_leading : sourceScope_ground_leading :=
  @ground_leading

abbrev sourceScope_charged_ground_leading :=
  type_of% (@charged_ground_leading)
theorem source_actual_charged_ground_leading : sourceScope_charged_ground_leading :=
  @charged_ground_leading

abbrev sourceScope_charged_ground_above :=
  type_of% (@charged_ground_above)
theorem source_actual_charged_ground_above : sourceScope_charged_ground_above :=
  @charged_ground_above

abbrev sourceScope_chargedPower_add :=
  type_of% (@chargedPower_add)
theorem source_actual_chargedPower_add : sourceScope_chargedPower_add :=
  @chargedPower_add

abbrev sourceScope_groundPower_source_shift :=
  type_of% (@groundPower_source_shift)
theorem source_actual_groundPower_source_shift : sourceScope_groundPower_source_shift :=
  @groundPower_source_shift

abbrev sourceScope_groundPower_input_shift :=
  type_of% (@groundPower_input_shift)
theorem source_actual_groundPower_input_shift : sourceScope_groundPower_input_shift :=
  @groundPower_input_shift

end Reg.D5.S3.VertexAlgebra.LatticeDualCosetIntertwiner
