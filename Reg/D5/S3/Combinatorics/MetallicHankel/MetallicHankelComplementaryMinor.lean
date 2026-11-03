import D5.S3.Combinatorics.MetallicHankel.MetallicHankelComplementaryMinor
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Dependent-family evidence for the exact complementary boundary determinant. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelComplementaryMinor
open _root_.D5.S3.Combinatorics.MetallicHankel.MetallicHankelComplementaryMinor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset
open _root_.D5.S3.Combinatorics.MetallicHankel.MetallicHankelDefs

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℤ) (fun _ => ℤ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (Φ : PowerSeries ℤ) (base a j u : ℕ) (_hN : 0 < j + (a + u)) (c d : ℕ → ℤ),
    c (j + (a + u)) = 1 →
    (∀ k, j + (a + u) < k → c k = 0) →
    (∀ k, j + (a + u) ≤ k → d k = 0) →
    (∀ t < j + (a + u),
      ∑ v ∈ range (j + (a + u) + 1), c v * PowerSeries.coeff (base + v + t) Φ = 0) →
    (∀ t < j + (a + u),
      ∑ v ∈ range (j + (a + u)), d v * PowerSeries.coeff (base + v + t) Φ =
        if t = j + (a + u) - 1 then -1 else 0) →
    IsUnit (shiftedHankel Φ base (j + (a + u))) →
    r.readout () () (shiftedHankel Φ (base + a) j)
      ((-1 : ℤ) ^ (a * j) * shiftedHankel Φ base (j + (a + u)) *
        (boundaryMatrix a j u c d).det)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let Φ : PowerSeries ℤ := PowerSeries.mk fun _ => 1
  let c : ℕ → ℤ := fun k => if k = 0 then -1 else if k = 1 then 1 else 0
  let d : ℕ → ℤ := fun k => if k = 0 then -1 else 0
  have hc : c 1 = 1 := by norm_num [c]
  have cs : ∀ k, 1 < k → c k = 0 := by
    intro k hk; simp [c, show k ≠ 0 by omega, show k ≠ 1 by omega]
  have ds : ∀ k, 1 ≤ k → d k = 0 := by
    intro k hk; simp [d, show k ≠ 0 by omega]
  have ho : ∀ t < 1, ∑ v ∈ range 2, c v * PowerSeries.coeff (0 + v + t) Φ = 0 := by
    intro t ht
    norm_num [Φ, c, sum_range_succ]
  have hp : ∀ t < 1, ∑ v ∈ range 1, d v * PowerSeries.coeff (0 + v + t) Φ =
      if t = 0 then -1 else 0 := by
    intro t ht
    have hh : t = 0 := by omega
    simp [Φ, d, hh]
  have hu : IsUnit (shiftedHankel Φ 0 1) := by
    simp [shiftedHankel, Φ, Matrix.det_fin_one]
  exact h Φ 0 1 0 0 (by omega) c d hc cs ds ho hp hu

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℤ) = 0 := Eq.mp (congrFun h 0) rfl
  norm_num at hh

def family : Registration arena (type_of% (@shifted_hankel_boundary)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@shifted_hankel_boundary, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@shifted_hankel_boundary) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Combinatorics.MetallicHankel.MetallicHankelComplementaryMinor.shifted_hankel_boundary.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelComplementaryMinor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelComplementaryMinor
