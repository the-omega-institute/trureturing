import D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionLocalSharpness
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The two observations are the largest triangle defect as a function of the rim gains
and its dependence on an axial chart angle. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Real
open scoped Quaternion InnerProductSpace

noncomputable section

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionLocalSharpness

open _root_.RoundQuaternionLocalSharpness _root_.RoundQuaternionK4Bounds
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel (unitI inner_eq_components)

local notation "U" => unitary ℍ[ℝ]

private theorem defect_nonneg (g : Fin 4 → Fin 4 → U) (e : ℝ) (h : DefectLE g e) : 0 ≤ e :=
  (arccos_nonneg _).trans (h.2.2 0 1 2 (by decide) (by decide) (by decide))

private theorem dist_id : roundDist (1 : U) 1 = 0 := by
  simp [roundDist, real_inner_self_eq_norm_sq]

private theorem dist_axis : roundDist (1 : U) unitI = π/2 := by
  simp [roundDist, inner_eq_components, unitI]

namespace Local

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => Fin 3 → U) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ A => hubMaxDefect A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law observer := ∀ (A : Fin 3 → U) (p q : ℂ) (η γ : Fin 3 → ℝ),
    (∀ j, (A j : ℍ[ℝ]) = quatPair ⟨-η j, γ j⟩ (transverse p q j)) →
    (∀ j, γ j = √(1-(η j)^2-‖transverse p q j‖^2)) →
    (∀ j, 0 < γ j) → ‖p‖ ≤ localR → ‖q‖ ≤ localR → etaMax η ≤ localR →
    let g := hubGaugedGains A
    let e := observer.readout () () A
    let φ := quarterLocalPotential p q
    DefectLE g e ∧
    (∃ i j k : Fin 4, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ roundDist (g i j * g j k) (g i k) = e) ∧
    (∀ i j, i ≠ j → cos (cStar * e) + ‖q‖ / 200 + (3/100) * (‖p‖^2 + etaMax η) ≤
      ⟪(g i j : ℍ[ℝ]), (↑((φ i)⁻¹ * φ j) : ℍ[ℝ])⟫_ℝ) ∧
    Fits g φ (cStar * e) ∧
    (¬ (p = 0 ∧ q = 0 ∧ η = 0) → ∃ R < cStar * e, Fits g φ R) ∧
    (p = 0 ∧ q = 0 ∧ η = 0 → ∀ ψ R, R < cStar * e → ¬ Fits g ψ R)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc (j : Fin 3) :
      (unitI : ℍ[ℝ]) = quatPair ⟨-(0 : ℝ), 1⟩ (transverse 0 0 j) := by
    simp [transverse, quatPair, unitI]
  have hd := (h (fun _ => unitI) 0 0 0 (fun _ => 1) hc
    (by intro j; norm_num [transverse]) (by intro j; norm_num)
    (by norm_num [localR]) (by norm_num [localR]) (by norm_num [etaMax, localR])).1
  exact (by norm_num : ¬ 0 ≤ (-1 : ℝ)) (defect_nonneg _ (-1) hd)

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), fun _ => 1, fun _ => unitI, ?_⟩
  change hubMaxDefect (fun _ => 1) ≠ hubMaxDefect (fun _ => unitI)
  have h := (le_max_left (roundDist 1 unitI) (max (roundDist 1 unitI) (roundDist 1 unitI))).trans
    (le_max_left _ (roundDist (unitI * unitI * unitI) 1))
  have h₀ : hubMaxDefect (fun _ => 1) = 0 := by simp [hubMaxDefect, dist_id]
  rw [h₀, dist_axis] at *
  exact ne_of_lt (Real.pi_div_two_pos.trans_le h)

def family : Registration arena (type_of% @quarterLocal_strictFit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quarterLocal_strictFit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quarterLocal_strictFit) (Realization signature) Unit Unit where
  unitName := `RoundQuaternionLocalSharpness.quarterLocal_strictFit.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionLocalSharpness.Local.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionLocalSharpness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Local

namespace Angular

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature (ℝ × ℝ × ℝ × ℝ × ℝ)
  (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p a => chartMaxDefect a p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law observer := ∀ (a b c u v w : ℝ),
    |a - π/2| ≤ 17*π/900 → |b - π/2| ≤ 17*π/900 → |c - π/2| ≤ 17*π/900 →
    0 ≤ u → 0 ≤ v → u + v < π/2 →
    u^2 + v^2 + (u+v)^2 ≤ (4497/500) * localR^2 →
    let g := chartGains a b c u v w
    let e := observer.readout () (b,c,u,v,w) a
    let center := a = π/2 ∧ b = π/2 ∧ c = π/2 ∧ u = 0 ∧ v = 0
    DefectLE g e ∧
    (∃ i j k : Fin 4, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ roundDist (g i j * g j k) (g i k) = e) ∧
    (∃ φ, Fits g φ (cStar * e) ∧ (¬ center → ∃ R < cStar * e, Fits g φ R)) ∧
    (center → ∀ ψ R, R < cStar * e → ¬ Fits g ψ R)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : |π/2 - π/2| ≤ 17*π/900 := by simp; positivity
  have hd := (h (π/2) (π/2) (π/2) 0 0 0 hc hc hc le_rfl le_rfl
    (by simpa using Real.pi_div_two_pos) (by norm_num [localR])).1
  exact (by norm_num : ¬ 0 ≤ (-1 : ℝ)) (defect_nonneg _ (-1) hd)

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(0,0,0,0,0), 0, π/2, ?_⟩
  change chartMaxDefect 0 0 0 0 0 0 ≠ chartMaxDefect (π/2) 0 0 0 0 0
  let rim (a : ℝ) : Fin 3 → U := fun j =>
    chartGains a 0 0 0 0 0 j.succ (j + 1).succ
  have hdef (a : ℝ) : chartMaxDefect a 0 0 0 0 0 = hubMaxDefect (rim a) := by
    unfold chartMaxDefect
    congr 1
    funext j
    fin_cases j <;> rfl
  have hzero : rim 0 = fun _ => 1 := by
    funext j
    fin_cases j <;> apply Subtype.ext
    · change (⟨cos 0, 0, 0, 0⟩ : ℍ[ℝ]) + sin 0 • (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) = 1
      ext <;> simp
    · change (⟨cos 0, 0, 0, 0⟩ : ℍ[ℝ]) + sin 0 • (⟨0, cos 0, sin 0, 0⟩ : ℍ[ℝ]) = 1
      ext <;> simp
    · change (⟨cos 0, 0, 0, 0⟩ : ℍ[ℝ]) +
        sin 0 • (⟨0, cos 0, sin 0 * cos 0, sin 0 * sin 0⟩ : ℍ[ℝ]) = 1
      ext <;> simp
  have hquarter : rim (π/2) 0 = unitI := by
    apply Subtype.ext
    change (⟨cos (π/2), 0, 0, 0⟩ : ℍ[ℝ]) +
      sin (π/2) • (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) = (unitI : ℍ[ℝ])
    ext <;> simp [unitI]
  have hleft : hubMaxDefect (fun _ => 1) = 0 := by simp [hubMaxDefect, dist_id]
  rw [hdef 0, hdef (π/2), hzero, hleft]
  apply ne_of_lt
  calc
    0 < π/2 := Real.pi_div_two_pos
    _ = roundDist 1 (rim (π/2) 0) := by rw [hquarter, dist_axis]
    _ ≤ hubMaxDefect (rim (π/2)) := (le_max_left _ _).trans (le_max_left _ _)

def family : Registration arena (type_of% @quarterLocal_angularRegion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quarterLocal_angularRegion, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quarterLocal_angularRegion) (Realization signature) Unit Unit where
  unitName := `RoundQuaternionLocalSharpness.quarterLocal_angularRegion.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionLocalSharpness.Angular.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionLocalSharpness
    definition := none
    coordinates := #[1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Angular
example (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hu' : u ≤ 7 * π / 300) (hv' : v ≤ 7 * π / 300) :
    u + v < π / 2 ∧ u^2 + v^2 + (u+v)^2 ≤ (4497/500) * localR^2 := by
  have hU : u ≤ (734/10000 : ℝ) := by linarith [Real.pi_lt_d6]
  have hV : v ≤ (734/10000 : ℝ) := by linarith [Real.pi_lt_d6]
  refine ⟨by linarith [Real.pi_pos], ?_⟩
  norm_num [localR]
  nlinarith only [pow_le_pow_left₀ hu hU 2, pow_le_pow_left₀ hv hV 2,
    pow_le_pow_left₀ (add_nonneg hu hv) (add_le_add hU hV) 2]

example :
    ∃ a b c u v : ℝ, |a - π/2| ≤ 17*π/900 ∧ |b - π/2| ≤ 17*π/900 ∧
      |c - π/2| ≤ 17*π/900 ∧ 0 ≤ u ∧ 0 ≤ v ∧ u+v < π/2 ∧
      u^2 + v^2 + (u+v)^2 ≤ (4497/500) * localR^2 := by
  refine ⟨π/2, π/2, π/2, 0, 0, ?_⟩
  simp only [sub_self, abs_zero, pow_succ, pow_zero, one_mul, mul_zero, add_zero]
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  exact ⟨le_rfl, le_rfl, by positivity, by positivity⟩

end Reg.D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionLocalSharpness
