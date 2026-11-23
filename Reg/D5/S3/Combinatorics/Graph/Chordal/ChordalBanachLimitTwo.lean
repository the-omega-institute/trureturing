import D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Realization of the reconstruction radius, obstruction threshold and limiting radius. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph SimpleGraph.BanachPathPower Filter Topology
open _root_.Reg.Support

noncomputable section

universe u

namespace Upper

abbrev signature := SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ k ε => (2 - 2 / (k : ℝ)) * ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (n k : ℕ) (_hk : 0 < k) (g : Fin n → Fin n → E)
    (ε : ℝ) (_hε : 0 ≤ ε) (_hskew : ∀ i j, g j i = -g i j)
    (_htri : ∀ i j l, (pathPower n k).Adj i j → (pathPower n k).Adj j l →
      (pathPower n k).Adj i l → ‖g i j + g j l - g i l‖ ≤ ε),
    ∃ φ : Fin n → E, ∀ i j, (pathPower n k).Adj i j →
      ‖g i j - (φ j - φ i)‖ ≤ R.readout () k ε

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨φ, hφ⟩ := h (E := ULift.{u} ℝ) 2 1 (by decide) (fun _ _ => 0) 0
    le_rfl (by simp) (by simp)
  have he : (pathPower 2 1).Adj (0 : Fin 2) 1 := by
    change (0 : Fin 2) ≠ 1 ∧ (0 : ℕ) ≤ 1 + 1 ∧ (1 : ℕ) ≤ 0 + 1
    decide
  have hh := hφ 0 1 he
  change ‖(0 : ULift.{u} ℝ) - (φ 1 - φ 0)‖ ≤ -1 at hh
  linarith [norm_nonneg ((0 : ULift.{u} ℝ) - (φ 1 - φ 0))]

def family : Registration arena.{u} (type_of% (@pathPower_banach_upper_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pathPower_banach_upper_bound.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨2, 0, 1, ?_⟩
    norm_num [actual, realize]


def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pathPower_banach_upper_bound.{u}) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.BanachPathPower.pathPower_banach_upper_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo.Upper.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "body", "body", "body",
        "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Upper

namespace Lower

abbrev signature := SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n k => ((n : ℝ) - k) / ((n : ℝ) + k - 2) * (2 - 2 / (k : ℝ)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ) (_hk : 1 ≤ k) (_hn : k + 1 ≤ n),
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E)
      (_ : CompleteSpace E) (_ : FiniteDimensional ℝ E) (g : Fin n → Fin n → E),
      (∀ i j, g j i = -g i j) ∧
      (∀ i j l, (pathPower n k).Adj i j → (pathPower n k).Adj j l →
        (pathPower n k).Adj i l → ‖g i j + g j l - g i l‖ ≤ 1) ∧
      ∀ φ : Fin n → E, ∃ i j, (pathPower n k).Adj i j ∧
        R.readout () n k ≤ ‖g i j - (φ j - φ i)‖

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨E, hE, hSpace, _, _, g, hg, hf, hL⟩ := h 2 1 (by decide) (by decide)
  letI := hE
  letI := hSpace
  obtain ⟨φ, hφ⟩ := pathPower_banach_upper_bound 2 1 (by decide) g 1 zero_le_one hg hf
  obtain ⟨i, j, hij, hR⟩ := hL φ
  change 1 ≤ ‖g i j - (φ j - φ i)‖ at hR
  have hu := hφ i j hij
  norm_num at hu
  norm_num [hu] at hR

def family : Registration arena (type_of% (@pathPower_banach_lower_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pathPower_banach_lower_bound, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨3, 1, 2, ?_⟩
    norm_num [actual, realize]


def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pathPower_banach_lower_bound) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.BanachPathPower.pathPower_banach_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo.Lower.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "body", "arg", "body", "arg", "body", "arg",
        "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Lower

namespace Limit

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ k => 2 - 2 / (k : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (_hk : 1 ≤ k),
    Tendsto (fun n => banachCoefficient n k) atTop (𝓝 (R.readout () () k))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := tendsto_nhds_unique (pathPower_banach_limit_tendsto 1 le_rfl) (h 1 le_rfl)
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% (@pathPower_banach_limit_tendsto)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pathPower_banach_limit_tendsto, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]


def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pathPower_banach_limit_tendsto) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.BanachPathPower.pathPower_banach_limit_tendsto.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo.Limit.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Limit

end
end Reg.D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo
