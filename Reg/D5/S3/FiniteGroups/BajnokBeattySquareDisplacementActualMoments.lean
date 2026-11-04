/- Whole signed odd parameter family: two actual finite-group count roles,
all natural (k,t) states, one global threshold family, the original five crossing
clauses with both brackets and original-crossing uniqueness, and every marginal,
mixed-moment and empirical covariance limit. Source selection and occurrence
binding remain unfinished: https://github.com/the-omega-institute/trureturing/issues/25856 . -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementActualMoments
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementActualMoments

open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdDistribution
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementActualMoments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter
open scoped Classical Topology

abbrev signature : Signature where
  Params := _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementActualMoments.Params
  State _ := ℕ × ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature
    (fun i p kt => if i = 0 then (square_return_pair p.val (qAt kt.1) kt.2).1
      else (square_return_pair p.val (qAt kt.1) kt.2).2)
    (fun e => nomatch e)

noncomputable def killed (i : Fin 2) : Realization signature :=
  realize signature
    (fun j p kt => if j = i then 0 else actual.readout j p kt)
    (fun e => nomatch e)

private def crossingSC (R : Realization signature) (p : signature.Params) (k V : ℕ) : Prop :=
  let q := qAt k
  let tmin := ((q + 1) / 2).toNat
  tmin < V ∧
    (∀ t : ℕ, tmin ≤ t → t < V → R.readout 1 p (k, t) < R.readout 0 p (k, t)) ∧
    R.readout 0 p (k, V) ≤ R.readout 1 p (k, V) ∧
    (∀ t : ℕ, V < t → R.readout 0 p (k, t) < R.readout 1 p (k, t)) ∧
    V ≤ ((q * p.val + 1) / 2).toNat

private def crossingLaw (R : Realization signature) (T : signature.Params → ℕ → ℕ) : Prop :=
  ∀ (p : signature.Params) (k : ℕ),
    (crossingSC R p k (T p k) ∧
      ((qAt k : ℝ)^2 - 1) * (p.val : ℝ) / (4 * (qAt k : ℝ) * Real.log 2) +
        1 / (2 * (qAt k : ℝ)) - 1 / (2 * (qAt k : ℝ) * (p.val : ℝ)) < (T p k : ℝ) ∧
      (T p k : ℤ) ≤ ⌈(p.val : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉) ∧
    ∀ v : ℕ, crossingSC R p k v → v = T p k

abbrev arena : Arena where
  signature := signature
  Law R := ∃ T : signature.Params → ℕ → ℕ,
    crossingLaw R T ∧
    (∀ p : signature.Params,
      Tendsto (avg (D T p)) atTop (𝓝 (1 / 2)) ∧
      Tendsto (avg (fun k => D T p k ^ 2)) atTop (𝓝 (1 / 3))) ∧
    (∀ p r : signature.Params,
      Tendsto (avg (fun k => D T p k * D T r k)) atTop
        (𝓝 (1 / 4 + (Int.gcd p.val r.val : ℝ)^2 /
          (12 * (p.val : ℝ) * (r.val : ℝ)))) ∧
      Tendsto (fun N : ℕ => avg (fun k => D T p k * D T r k) N -
        avg (D T p) N * avg (D T r) N) atTop
        (𝓝 ((Int.gcd p.val r.val : ℝ)^2 / (12 * (p.val : ℝ) * (r.val : ℝ)))))

private theorem actual_bridge : (type_of% actual_square_displacement_actual_moments) ↔
    arena.Law actual := by
  constructor
  · intro h
    obtain ⟨T, hT, hmarg, hpair⟩ := h
    refine ⟨T, ?_, hmarg, hpair⟩
    intro p k
    rcases hT p k with ⟨⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩, huniq⟩
    refine ⟨⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩, ?_⟩
    intro v hv
    rcases hv with ⟨hvmin, hvbefore, hvat, hvafter, hvlate⟩
    exact huniq v ⟨hvmin, hvbefore, hvat, hvafter, hvlate⟩
  · intro h
    obtain ⟨T, hT, hmarg, hpair⟩ := h
    refine ⟨T, ?_, hmarg, hpair⟩
    intro p k
    rcases hT p k with ⟨⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩, huniq⟩
    refine ⟨⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩, ?_⟩
    intro v hv
    rcases hv with ⟨hvmin, hvbefore, hvat, hvafter, hvlate⟩
    exact huniq v ⟨hvmin, hvbefore, hvat, hvafter, hvlate⟩

private theorem actual_law : arena.Law actual :=
  actual_bridge.mp actual_square_displacement_actual_moments

/-- Wa is required before crossing; Wq is required after crossing. -/
private theorem killed_law (i : Fin 2) : ¬ arena.Law (killed i) := by
  intro h
  obtain ⟨T, hT, _, _⟩ := h
  let p : signature.Params := ⟨5, by norm_num, by decide⟩
  have hh := (hT p 0).1.1
  fin_cases i
  · have hmin : 2 < T p 0 := hh.1
    have hz := hh.2.1 2 (by norm_num) hmin
    change (square_return_pair 5 3 2).2 < 0 at hz
    omega
  · have hz := hh.2.2.2.1 (T p 0 + 1) (by omega)
    change (square_return_pair 5 3 (T p 0 + 1)).1 < 0 at hz
    omega

/-- The concrete binomial readouts are the same public actual_counts instances
    used in the supplied two-level-carry registration. -/
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
  let p : signature.Params := ⟨5, by norm_num, by decide⟩
  refine ⟨p, (0, 2), (0, 3), ?_⟩
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

noncomputable def source_registration : Registration arena
    (type_of% actual_square_displacement_actual_moments) where
  actual := actual
  bridge := actual_bridge
  variation := ⟨actual_law, killed 0, killed_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨killed i, ?_, rfl, killed_law i⟩
      intro j hj
      funext p kt
      simp [killed, realize, hj]
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@actual_square_displacement_actual_moments)
      (Realization signature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySquareDisplacementActualMoments.actual_square_displacement_actual_moments.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementActualMoments.source_registration
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
    (fun i p kt => if i = 0 then (square_return_pair p.val (qAt kt.1) kt.2).1
      else (square_return_pair p.val (qAt kt.1) kt.2).2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementActualMoments
