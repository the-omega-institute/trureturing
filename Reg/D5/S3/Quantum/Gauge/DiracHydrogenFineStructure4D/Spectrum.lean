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

namespace CircularEnergy

abbrev signature : Signature := operandSignature (ℝ) (ℕ → ℕ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℝ) (n : ℕ) {ζ : ℝ} (hζ : 0 < ζ) (hζn : ζ < (n : ℝ)),
    R.readout () () m n n ζ = circularEnergy m n ζ

def actual : Realization signature := diracObserve% (sommerfeldEnergy)

def family : Registration arena (type_of% (@sommerfeld_circular_matches_ode)) :=
  diracFamily% arena (@sommerfeld_circular_matches_ode) actual
    (diracObserve% (fun _ _ _ _ => 0))
    (by
      intro h
      have e := h 1 1 (ζ := 1 / 2) (by norm_num) (by norm_num)
      have hp : 0 < circularEnergy 1 1 (1 / 2) := by
        unfold circularEnergy circularGamma
        positivity
      exact hp.ne' e.symm)
    (by
      refine ⟨(), 0, 1, ?_⟩
      intro h
      have e := congrArg (fun f : ℕ → ℕ → ℝ → ℝ => f 1 1 0) h
      norm_num [actual, realize, sommerfeldEnergy, sommerfeldEnergySq] at e)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sommerfeld_circular_matches_ode) (Realization signature) Unit Unit :=
  diracBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.sommerfeld_circular_matches_ode.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.CircularEnergy.family
    arena family (diracObserve% (sommerfeldEnergy))
    #[]
    #[{ path := diracPath% sommerfeld_circular_matches_ode sommerfeldEnergy 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end CircularEnergy

namespace EnergyWindow

abbrev signature : Signature := operandSignature (ℝ) (ℕ → ℕ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m ζ : ℝ} {n k : ℕ} (hm : 0 < m) (hζ : 0 < ζ) (hζk : ζ < (k : ℝ)),
    0 < R.readout () () m n k ζ ∧ sommerfeldEnergy m n k ζ < m

def actual : Realization signature := diracObserve% (sommerfeldEnergy)

def family : Registration arena (type_of% (@sommerfeld_bound_state_window)) :=
  diracFamily% arena (@sommerfeld_bound_state_window) actual
    (diracObserve% (fun _ _ _ _ => 0))
    (by
      intro h
      exact (lt_irrefl (0 : ℝ)) (h (m := 1) (n := 1) (k := 1) (ζ := 1 / 2)
        (by norm_num) (by norm_num) (by norm_num)).1)
    (by
      refine ⟨(), 0, 1, ?_⟩
      intro h
      have e := congrArg (fun f : ℕ → ℕ → ℝ → ℝ => f 1 1 0) h
      norm_num [actual, realize, sommerfeldEnergy, sommerfeldEnergySq] at e)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sommerfeld_bound_state_window) (Realization signature) Unit Unit :=
  diracBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.sommerfeld_bound_state_window.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.EnergyWindow.family
    arena family (diracObserve% (sommerfeldEnergy))
    #[]
    #[{ path := diracPath% sommerfeld_bound_state_window sommerfeldEnergy 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end EnergyWindow

namespace CriticalEnergy

abbrev signature : Signature := operandSignature (ℝ) (ℕ → ℕ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℝ, Tendsto (R.readout () () m 1 1) (𝓝[<] 1) (𝓝 0)

def actual : Realization signature := diracObserve% (sommerfeldEnergy)

def family : Registration arena (type_of% (@sommerfeld_ground_critical_limit)) :=
  diracFamily% arena (@sommerfeld_ground_critical_limit) actual
    (diracObserve% (fun _ _ _ _ => 1))
    (by
      intro h
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[<] 1) (𝓝 1) := tendsto_const_nhds
      have hzero : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[<] 1) (𝓝 0) := h 1
      have e := tendsto_nhds_unique hzero hconst
      norm_num at e)
    (by
      refine ⟨(), 0, 1, ?_⟩
      intro h
      have e := congrArg (fun f : ℕ → ℕ → ℝ → ℝ => f 1 1 0) h
      norm_num [actual, realize, sommerfeldEnergy, sommerfeldEnergySq] at e)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sommerfeld_ground_critical_limit) (Realization signature) Unit Unit :=
  diracBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.sommerfeld_ground_critical_limit.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.CriticalEnergy.family
    arena family (diracObserve% (sommerfeldEnergy))
    #[]
    #[{ path := diracPath% sommerfeld_ground_critical_limit sommerfeldEnergy 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end CriticalEnergy

namespace EnergyOrdering

abbrev signature : Signature := operandSignature (ℝ) (ℕ → ℕ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m ζ : ℝ} {n k₁ k₂ : ℕ} (hm : 0 < m)
      (hk : k₁ < k₂) (hk₂ : k₂ ≤ n) (hζ : 0 < ζ) (hζk : ζ < (k₁ : ℝ)),
    R.readout () () m n k₁ ζ < sommerfeldEnergy m n k₂ ζ

def actual : Realization signature := diracObserve% (sommerfeldEnergy)

def family : Registration arena (type_of% (@sommerfeld_strictly_increasing_in_k)) :=
  diracFamily% arena (@sommerfeld_strictly_increasing_in_k) actual
    (diracObserve% (fun _ _ _ _ => 1))
    (by
      intro h
      have e := h (m := 1) (ζ := 1 / 2) (n := 2) (k₁ := 1) (k₂ := 2)
        (by norm_num) (by decide) (by decide) (by norm_num) (by norm_num)
      have hlt := (sommerfeld_bound_state_window (m := 1) (ζ := 1 / 2) (n := 2) (k := 2)
        (by norm_num) (by norm_num) (by norm_num)).2
      exact lt_asymm e hlt)
    (by
      refine ⟨(), 0, 1, ?_⟩
      intro h
      have e := congrArg (fun f : ℕ → ℕ → ℝ → ℝ => f 1 1 0) h
      norm_num [actual, realize, sommerfeldEnergy, sommerfeldEnergySq] at e)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sommerfeld_strictly_increasing_in_k) (Realization signature) Unit Unit :=
  diracBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.sommerfeld_strictly_increasing_in_k.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.EnergyOrdering.family
    arena family (diracObserve% (sommerfeldEnergy))
    #[]
    #[{ path := diracPath% sommerfeld_strictly_increasing_in_k sommerfeldEnergy 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end EnergyOrdering

namespace EnergyExpansion

abbrev signature : Signature := operandSignature (ℝ) (ℕ → ℕ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℝ) (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n),
    let g := R.readout () () m n k
    g 0 = m ∧ HasDerivAt g (-m / (2 * (n : ℝ) ^ 2)) 0 ∧
      HasDerivAt (deriv g)
        (-m / (n : ℝ) ^ 3 * (1 / (k : ℝ) - 3 / (4 * (n : ℝ)))) 0

def actual : Realization signature := diracObserve% (sommerfeldEnergySq)

def family : Registration arena (type_of% (@sommerfeld_fourth_order_expansion)) :=
  diracFamily% arena (@sommerfeld_fourth_order_expansion) actual
    (diracObserve% (fun _ _ _ _ => 0))
    (by
      intro h
      have e := (h 1 1 1 (by decide) (by decide)).1
      norm_num [realize] at e)
    (by
      refine ⟨(), 0, 1, ?_⟩
      intro h
      have e := congrArg (fun f : ℕ → ℕ → ℝ → ℝ => f 1 1 0) h
      norm_num [actual, realize, sommerfeldEnergy, sommerfeldEnergySq] at e)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sommerfeld_fourth_order_expansion) (Realization signature) Unit Unit :=
  diracBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.sommerfeld_fourth_order_expansion.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.EnergyExpansion.family
    arena family (diracObserve% (sommerfeldEnergySq))
    #[]
    #[{ path := diracPath% sommerfeld_fourth_order_expansion sommerfeldEnergySq 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end EnergyExpansion

namespace SplittingCoefficient

abbrev signature : Signature := operandSignature (ℝ) (ℕ → ℕ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℝ,
    (1 / 2 : ℝ) * (deriv (deriv (R.readout () () m 2 2)) 0 -
      deriv (deriv (sommerfeldEnergySq m 2 1)) 0) = m / 32

def actual : Realization signature := diracObserve% (sommerfeldEnergySq)

def family : Registration arena (type_of% (@sommerfeld_2p_splitting_coefficient)) :=
  diracFamily% arena (@sommerfeld_2p_splitting_coefficient) actual
    (diracObserve% (fun _ _ _ _ => 0))
    (by
      intro h
      have e := h 1
      have h₁ := (sommerfeld_fourth_order_expansion 1 2 1 (by decide) (by decide)).2.2.deriv
      simp only [realize, deriv_const] at e
      rw [h₁] at e
      norm_num at e)
    (by
      refine ⟨(), 0, 1, ?_⟩
      intro h
      have e := congrArg (fun f : ℕ → ℕ → ℝ → ℝ => f 1 1 0) h
      norm_num [actual, realize, sommerfeldEnergy, sommerfeldEnergySq] at e)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sommerfeld_2p_splitting_coefficient) (Realization signature) Unit Unit :=
  diracBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.sommerfeld_2p_splitting_coefficient.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.SplittingCoefficient.family
    arena family (diracObserve% (sommerfeldEnergySq))
    #[]
    #[{ path := diracPath% sommerfeld_2p_splitting_coefficient sommerfeldEnergySq 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end SplittingCoefficient


end

end Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
