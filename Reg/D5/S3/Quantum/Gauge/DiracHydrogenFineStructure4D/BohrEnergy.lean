import D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
import Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.Common

open _root_.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter MeasureTheory Set
open scoped Topology

namespace Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace BohrEnergy

abbrev signature : Signature := operandSignature (ℕ) (ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {jLeft jRight : ℝ} (hjLeft : 0 ≤ jLeft) (hjRight : 0 ≤ jRight) (n : ℕ)
      (hn : (n : ℝ) = 2 * jLeft + 1)
      (horth : jLeft * (jLeft + 1) - jRight * (jRight + 1) = 0) (m α : ℝ),
    let C := 2 * (jLeft * (jLeft + 1) + jRight * (jRight + 1))
    jLeft = jRight ∧ C = 4 * jLeft * (jLeft + 1) ∧ C = R.readout () () n - 1 ∧
      -m * α ^ 2 / (2 * (C + 1)) = -m * α ^ 2 / (2 * (n : ℝ) ^ 2)

def actual : Realization signature := diracObserve% (fun n : ℕ => (n : ℝ) ^ 2)

def family : Registration arena (type_of% (@bohr_energy_from_casimir)) :=
  diracFamily% arena (@bohr_energy_from_casimir) actual
    (diracObserve% (fun _ => 0))
    (by
      intro h
      have e := (h (jLeft := 0) (jRight := 0) (by norm_num) (by norm_num) 1
        (by norm_num) (by norm_num) 1 1).2.2.1
      norm_num [realize] at e)
    (by
      refine ⟨(), 1, 2, ?_⟩
      norm_num [actual, realize])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bohr_energy_from_casimir) (Realization signature) Unit Unit :=
  diracBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.bohr_energy_from_casimir.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.BohrEnergy.family
    arena family (diracObserve% (fun n : ℕ => (n : ℝ) ^ 2))
    #[]
    #[{ path := diracPath% bohr_energy_from_casimir HPow.hPow 6 0
        stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }]

end BohrEnergy


end

end Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
