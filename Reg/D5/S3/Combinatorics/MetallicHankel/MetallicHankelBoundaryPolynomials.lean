import D5.S3.Combinatorics.MetallicHankel.MetallicHankelBoundaryPolynomials
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelBoundaryPolynomials
open _root_.D5.S3.Combinatorics.MetallicHankel.MetallicHankelBoundaryPolynomials
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℤ) (fun _ => ℤ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (μ : ℕ → ℤ) (n : ℕ) (c d : ℕ → ℤ),
    c (n + 1) = 1 →
    (∀ k, n + 1 < k → c k = 0) →
    (∀ k, n + 1 ≤ k → d k = 0) →
    (∀ t < n + 1, ∑ a ∈ range (n + 2), c a * μ (a + t) = 0) →
    (∀ t < n + 1, ∑ a ∈ range (n + 1), d a * μ (a + t) =
      if t = n then -1 else 0) →
    IsUnit (Matrix.of fun i j : Fin (n + 1) => μ (i.val + j.val)).det →
    ∀ i j : Fin (n + 1), r.readout () ()
      ((Matrix.of fun a b : Fin (n + 1) => μ (a.val + b.val))⁻¹ i j)
      (-∑ a ∈ range (j.val + 1),
        (c (i.val + j.val + 1 - a) * d a - d (i.val + j.val + 1 - a) * c a))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let c : ℕ → ℤ := fun k => if k = 0 then -1 else if k = 1 then 1 else 0
  let d : ℕ → ℤ := fun k => if k = 0 then -1 else 0
  have hc : c 1 = 1 := by norm_num [c]
  have cs : ∀ k, 1 < k → c k = 0 := by
    intro k hk
    simp [c, show k ≠ 0 by omega, show k ≠ 1 by omega]
  have ds : ∀ k, 1 ≤ k → d k = 0 := by
    intro k hk
    simp [d, show k ≠ 0 by omega]
  have ho : ∀ t < 1, ∑ a ∈ range 2, c a * (1 : ℤ) = 0 := by
    intro t ht
    norm_num [c, sum_range_succ]
  have hp : ∀ t < 1, ∑ a ∈ range 1, d a * (1 : ℤ) =
      if t = 0 then -1 else 0 := by
    intro t ht
    have : t = 0 := by omega
    simp [d, this]
  have hu : IsUnit (Matrix.of fun _ _ : Fin 1 => (1 : ℤ)).det := by
    simp [Matrix.det_fin_one]
  exact h (fun _ => 1) 0 c d hc cs ds ho hp hu 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℤ) = 0 := Eq.mp (congrFun h 0) rfl
  norm_num at hh

def family : Registration arena (type_of% (@hankel_inverse_bezout)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hankel_inverse_bezout, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hankel_inverse_bezout) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Combinatorics.MetallicHankel.MetallicHankelBoundaryPolynomials.hankel_inverse_bezout.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelBoundaryPolynomials.family
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
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MetallicHankel.MetallicHankelBoundaryPolynomials
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelBoundaryPolynomials
