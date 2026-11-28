import D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the orbital, spin and Dirac shell counts. -/

open _root_.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

private abbrev shellSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

private abbrev observeShell (f : ℕ → ℕ) : Realization shellSignature :=
  realize shellSignature (fun _ _ n => f n) (fun e => nomatch e)

macro "shellBind% " unit:term:max familyName:term:max arena:term:max family:term:max
    actual:term:max path:term:max : term =>
  `({ unitName := $unit
      realizationName := $familyName
      realizationSource := none
      generated := false
      arena := .source ⟨$arena⟩
      objectArena := .source ⟨$arena⟩
      catalog := Lean.Name.anonymous
      localNames := false
      realization := .source $arena ⟨$family⟩
      correspondence := ⟨.evidence, .evidence⟩
      bundleNonempty := .absent
      readout := some $actual
      variation := .absent
      sensitivity := .absent
      partialSensitivity := none
      escapeFrom := none
      sourceSelection := some {
        owner := `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
        definition := none
        coordinates := #[]
        readouts := #[⟨$path, 0, false, none, false⟩] }
      continuation := .unknown
      familyRecord := none
      options := #[] })

namespace OrbitalShell

private abbrev actual : Realization shellSignature :=
  observeShell (fun n => ∑ l ∈ Finset.range n, (2 * l + 1))

private abbrev erased : Realization shellSignature := observeShell (fun _ => 0)

abbrev arena : Arena where
  signature := shellSignature
  Law r := ∀ n : ℕ, r.readout () () n = n ^ 2

private theorem erased_rejected : ¬ arena.Law erased := by
  intro h
  have hOne := h 1
  change 0 = (1 : ℕ) ^ 2 at hOne
  norm_num at hOne

def family : Registration arena (type_of% (@bohr_shell_degeneracy)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bohr_shell_degeneracy, erased, erased_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased erased_rejected
  dependence := by
    intro _
    refine ⟨(), 1, 2, ?_⟩
    change (∑ l ∈ Finset.range 1, (2 * l + 1)) ≠ (∑ l ∈ Finset.range 2, (2 * l + 1))
    rw [bohr_shell_degeneracy, bohr_shell_degeneracy]
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bohr_shell_degeneracy) (Realization shellSignature) Unit Unit :=
  shellBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.bohr_shell_degeneracy.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.OrbitalShell.family
    arena family (realize shellSignature (fun _ _ n => (fun n => ∑ l ∈ Finset.range n, (2 * l + 1)) n) (fun e => nomatch e))
    #["body", "fn", "arg"]

end OrbitalShell

namespace SpinShell

private abbrev actual : Realization shellSignature :=
  observeShell (fun n => ∑ l ∈ Finset.range n, 2 * (2 * l + 1))

private abbrev erased : Realization shellSignature := observeShell (fun _ => 0)

abbrev arena : Arena where
  signature := shellSignature
  Law r := ∀ n : ℕ, r.readout () () n = 2 * n ^ 2

private theorem erased_rejected : ¬ arena.Law erased := by
  intro h
  have hOne := h 1
  change 0 = 2 * (1 : ℕ) ^ 2 at hOne
  norm_num at hOne

def family : Registration arena (type_of% (@bohr_spin_shell_capacity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bohr_spin_shell_capacity, erased, erased_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased erased_rejected
  dependence := by
    intro _
    refine ⟨(), 1, 2, ?_⟩
    change (∑ l ∈ Finset.range 1, 2 * (2 * l + 1)) ≠ (∑ l ∈ Finset.range 2, 2 * (2 * l + 1))
    rw [bohr_spin_shell_capacity, bohr_spin_shell_capacity]
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bohr_spin_shell_capacity) (Realization shellSignature) Unit Unit :=
  shellBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.bohr_spin_shell_capacity.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.SpinShell.family
    arena family (realize shellSignature (fun _ _ n => (fun n => ∑ l ∈ Finset.range n, 2 * (2 * l + 1)) n) (fun e => nomatch e))
    #["body", "fn", "arg"]

end SpinShell

namespace DiracSubshell

private abbrev actual : Realization shellSignature :=
  observeShell (fun n => ∑ k ∈ Finset.range n, (if k + 1 = n then 2 * k + 2 else 4 * k + 4))

private abbrev erased : Realization shellSignature := observeShell (fun _ => 0)

abbrev arena : Arena where
  signature := shellSignature
  Law r := ∀ n : ℕ, 1 ≤ n → r.readout () () n = 2 * n ^ 2

private theorem erased_rejected : ¬ arena.Law erased := by
  intro h
  have hOne := h 1 (by norm_num)
  change 0 = 2 * (1 : ℕ) ^ 2 at hOne
  norm_num at hOne

def family : Registration arena (type_of% (@dirac_subshell_degeneracy)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dirac_subshell_degeneracy, erased, erased_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased erased_rejected
  dependence := by
    intro _
    refine ⟨(), 1, 2, ?_⟩
    change (∑ k ∈ Finset.range 1, (if k + 1 = 1 then 2 * k + 2 else 4 * k + 4)) ≠
      (∑ k ∈ Finset.range 2, (if k + 1 = 2 then 2 * k + 2 else 4 * k + 4))
    rw [dirac_subshell_degeneracy 1 (by norm_num), dirac_subshell_degeneracy 2 (by norm_num)]
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dirac_subshell_degeneracy) (Realization shellSignature) Unit Unit :=
  shellBind% `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.dirac_subshell_degeneracy.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.DiracSubshell.family
    arena family (realize shellSignature (fun _ _ n => (fun n => ∑ k ∈ Finset.range n, (if k + 1 = n then 2 * k + 2 else 4 * k + 4)) n) (fun e => nomatch e))
    #["body", "body", "fn", "arg"]

end DiracSubshell
end Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
