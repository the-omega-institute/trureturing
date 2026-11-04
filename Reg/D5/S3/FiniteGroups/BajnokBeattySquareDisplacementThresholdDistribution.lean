/- Full signed odd two-parameter family registration: four actual count roles,
all natural states, both analytic bounds, original-SC uniqueness in each fiber,
and every integer histogram value. Source selection and occurrence binding
remain unfinished: https://github.com/the-omega-institute/trureturing/issues/25856 . -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdDistribution
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdDistribution

open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdDistribution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Filter
open scoped Classical Topology

abbrev signature : Signature where
  Params := {p : ℤ // 5 ≤ p ∧ Odd p} × {r : ℤ // 5 ≤ r ∧ Odd r}
  State _ := ℕ × ℕ
  Role := Fin 4
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature
    (fun i pr kt =>
      if i = 0 then (square_return_pair pr.1.1 (qAt kt.1) kt.2).1
      else if i = 1 then (square_return_pair pr.1.1 (qAt kt.1) kt.2).2
      else if i = 2 then (square_return_pair pr.2.1 (qAt kt.1) kt.2).1
      else (square_return_pair pr.2.1 (qAt kt.1) kt.2).2)
    (fun e => nomatch e)

noncomputable def killed (i : Fin 4) : Realization signature :=
  realize signature
    (fun j pr kt => if j = i then 0 else actual.readout j pr kt)
    (fun e => nomatch e)

private abbrev params (p r : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p)
    (hr5 : 5 ≤ r) (hro : Odd r) : signature.Params :=
  ⟨⟨p, hp5, hpo⟩, ⟨r, hr5, hro⟩⟩

private def crossingSC (R : Realization signature) (pr : signature.Params)
    (c : ℤ) (i j : Fin 4) (k V : ℕ) : Prop :=
  let q := qAt k
  let tmin := ((q + 1) / 2).toNat
  tmin < V ∧
    (∀ t : ℕ, tmin ≤ t → t < V → R.readout j pr (k, t) < R.readout i pr (k, t)) ∧
    R.readout i pr (k, V) ≤ R.readout j pr (k, V) ∧
    (∀ t : ℕ, V < t → R.readout i pr (k, t) < R.readout j pr (k, t)) ∧
    V ≤ ((q * c + 1) / 2).toNat

private def crossingLaw (R : Realization signature) (pr : signature.Params)
    (c : ℤ) (i j : Fin 4) (T : ℕ → ℕ) : Prop :=
  ∀ k : ℕ,
    (crossingSC R pr c i j k (T k) ∧
      ((qAt k : ℝ)^2 - 1) * (c : ℝ) / (4 * (qAt k : ℝ) * Real.log 2) +
        1 / (2 * (qAt k : ℝ)) - 1 / (2 * (qAt k : ℝ) * (c : ℝ)) < (T k : ℝ) ∧
      (T k : ℤ) ≤ ⌈(c : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉) ∧
    ∀ v : ℕ, crossingSC R pr c i j k v → v = T k

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p r : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p) (hr5 : 5 ≤ r) (hro : Odd r),
    let pr := params p r hp5 hpo hr5 hro
    ∃ T U : ℕ → ℕ,
      crossingLaw R pr p 0 1 T ∧ crossingLaw R pr r 2 3 U ∧
      (∀ z : ℤ, Tendsto (fun N : ℕ =>
        (((Finset.range N).filter (fun k =>
          r * (T k : ℤ) - p * (U k : ℤ) = z)).card : ℝ) / (N : ℝ)) atTop
          (𝓝 (mass p r z)))

private theorem actual_bridge : (type_of% actual_square_displacement_threshold_distribution) ↔
    arena.Law actual := by
  constructor
  · intro h p r hp5 hpo hr5 hro
    obtain ⟨T, U, hT, hU, hhist⟩ := h p r hp5 hpo hr5 hro
    refine ⟨T, U, ?_, ?_, hhist⟩
    · intro k
      rcases hT k with ⟨⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩, huniq⟩
      refine ⟨⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩, ?_⟩
      intro v hv
      rcases hv with ⟨hvmin, hvbefore, hvat, hvafter, hvlate⟩
      exact huniq v ⟨hvmin, hvbefore, hvat, hvafter, hvlate⟩
    · intro k
      rcases hU k with ⟨⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩, huniq⟩
      refine ⟨⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩, ?_⟩
      intro v hv
      rcases hv with ⟨hvmin, hvbefore, hvat, hvafter, hvlate⟩
      exact huniq v ⟨hvmin, hvbefore, hvat, hvafter, hvlate⟩
  · intro h p r hp5 hpo hr5 hro
    obtain ⟨T, U, hT, hU, hhist⟩ := h p r hp5 hpo hr5 hro
    refine ⟨T, U, ?_, ?_, hhist⟩
    · intro k
      rcases hT k with ⟨⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩, huniq⟩
      refine ⟨⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩, ?_⟩
      intro v hv
      rcases hv with ⟨hvmin, hvbefore, hvat, hvafter, hvlate⟩
      exact huniq v ⟨hvmin, hvbefore, hvat, hvafter, hvlate⟩
    · intro k
      rcases hU k with ⟨⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩, huniq⟩
      refine ⟨⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩, ?_⟩
      intro v hv
      rcases hv with ⟨hvmin, hvbefore, hvat, hvafter, hvlate⟩
      exact huniq v ⟨hvmin, hvbefore, hvat, hvafter, hvlate⟩

private theorem actual_law : arena.Law actual :=
  actual_bridge.mp actual_square_displacement_threshold_distribution

private theorem killed_law (i : Fin 4) : ¬ arena.Law (killed i) := by
  intro h
  obtain ⟨T, U, hT, hU, _⟩ := h 5 5 (by norm_num) (by decide) (by norm_num) (by decide)
  fin_cases i
  · have hh := (hT 0).1.1
    have hz := hh.2.1 2 (by norm_num) hh.1
    change (square_return_pair 5 3 2).2 < 0 at hz
    omega
  · have hh := (hT 0).1.1
    have hz := hh.2.2.2.1 (T 0 + 1) (by omega)
    change (square_return_pair 5 3 (T 0 + 1)).1 < 0 at hz
    omega
  · have hh := (hU 0).1.1
    have hz := hh.2.1 2 (by norm_num) hh.1
    change (square_return_pair 5 3 2).2 < 0 at hz
    omega
  · have hh := (hU 0).1.1
    have hz := hh.2.2.2.1 (U 0 + 1) (by omega)
    change (square_return_pair 5 3 (U 0 + 1)).1 < 0 at hz
    omega

private theorem actual_samples :
    (square_return_pair 5 3 2).1 = 2 * (Nat.choose 55 30 + Nat.choose 55 50) ∧
    (square_return_pair 5 3 2).2 = 4 * Nat.choose 55 35 ∧
    (square_return_pair 5 3 3).1 = 2 * (Nat.choose 85 45 + Nat.choose 85 65) ∧
    (square_return_pair 5 3 3).2 = 4 * Nat.choose 85 50 := by
  have h2 := actual_counts 2 1 2 (by norm_num) (by norm_num) (by norm_num)
  have h3 := actual_counts 2 1 3 (by norm_num) (by norm_num) (by norm_num)
  change (square_return_pair 5 3 2).1 = 2 * (Nat.choose 55 30 + Nat.choose 55 50) ∧
    (square_return_pair 5 3 2).2 = 4 * Nat.choose 55 35 at h2
  change (square_return_pair 5 3 3).1 = 2 * (Nat.choose 85 45 + Nat.choose 85 65) ∧
    (square_return_pair 5 3 3).2 = 4 * Nat.choose 85 50 at h3
  exact ⟨h2.1, h2.2, h3.1, h3.2⟩

set_option maxRecDepth 10000 in
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let pr := params 5 5 (by norm_num) (by decide) (by norm_num) (by decide)
  refine ⟨pr, (0, 2), (0, 3), ?_⟩
  obtain ⟨hA, hB, hA', hB'⟩ := actual_samples
  fin_cases i
  · change (square_return_pair 5 3 2).1 ≠ (square_return_pair 5 3 3).1
    rw [hA, hA']
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 30 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 50 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 45 ≤ 85),
      Nat.choose_eq_factorial_div_factorial (by decide : 65 ≤ 85), Nat.factorial]
  · change (square_return_pair 5 3 2).2 ≠ (square_return_pair 5 3 3).2
    rw [hB, hB']
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 35 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 50 ≤ 85), Nat.factorial]
  · change (square_return_pair 5 3 2).1 ≠ (square_return_pair 5 3 3).1
    rw [hA, hA']
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 30 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 50 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 45 ≤ 85),
      Nat.choose_eq_factorial_div_factorial (by decide : 65 ≤ 85), Nat.factorial]
  · change (square_return_pair 5 3 2).2 ≠ (square_return_pair 5 3 3).2
    rw [hB, hB']
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 35 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 50 ≤ 85), Nat.factorial]

noncomputable def source_registration : Registration arena
    (type_of% actual_square_displacement_threshold_distribution) where
  actual := actual
  bridge := actual_bridge
  variation := ⟨actual_law, killed 0, killed_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨killed i, ?_, rfl, killed_law i⟩
      intro j hj
      funext pr kt
      simp [killed, realize, hj]
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@actual_square_displacement_threshold_distribution)
      (Realization signature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdDistribution.actual_square_displacement_threshold_distribution.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdDistribution.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun i pr kt =>
      if i = 0 then (square_return_pair pr.1.1 (qAt kt.1) kt.2).1
      else if i = 1 then (square_return_pair pr.1.1 (qAt kt.1) kt.2).2
      else if i = 2 then (square_return_pair pr.2.1 (qAt kt.1) kt.2).1
      else (square_return_pair pr.2.1 (qAt kt.1) kt.2).2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdDistribution
