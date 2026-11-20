import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance

/-! Source-bound observations of the universal-clique cograph family. -/

namespace Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance

open LeanInformationAudit SimpleGraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.SpectralGraph.UniversalCliqueCographDistance
open _root_.D5.S3.Combinatorics.SpectralGraph.MandalMannaDQDilworthRefutation
  (vicinal HasChainCover dilworthNumber)
open Reg.Support.SingleDependentReadout (signature sensitivity)

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private abbrev NatPair := Σ _ : ℕ, ℕ
private abbrev Sizes := Σ _ : ℕ, NatPair

abbrev widthSignature := signature NatPair (fun _ => ℕ) (fun _ => ℕ∞)
abbrev widthArena : Arena where
  signature := widthSignature
  Law R := ∀ {r s b : ℕ}, 2 ≤ s → R.readout () ⟨r, s⟩ b = 2

private def widthActual : Realization widthSignature :=
  realize widthSignature (fun _ p b => dilworthNumber (graph p.1 p.2 b))
    (fun e => nomatch e)

private def widthRejected : Realization widthSignature :=
  realize widthSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem widthRejectedLaw : ¬ widthArena.Law widthRejected := by
  intro h
  have htwo : (0 : ℕ∞) = 2 := h (r := 0) (b := 0) (s := 2) (by decide)
  exact (by decide : (0 : ℕ∞) ≠ 2) htwo

def widthFamily : Registration widthArena (type_of% @width) where
  actual := widthActual
  bridge := Iff.rfl
  variation := ⟨@width, widthRejected, widthRejectedLaw⟩
  sensitivity := sensitivity widthArena.Law widthActual widthRejected widthRejectedLaw
  dependence := by
    intro _
    refine ⟨⟨0, 0⟩, 1, 0, ?_⟩
    change dilworthNumber (graph 0 0 1) ≠ dilworthNumber (graph 0 0 0)
    have hpos : 1 ≤ dilworthNumber (graph 0 0 1) := by
      apply le_sInf
      rintro _ ⟨k, rfl, c, _⟩
      exact_mod_cast Nat.succ_le_of_lt ((Nat.zero_le _).trans_lt (c (.inr (.inr 0))).isLt)
    have hz : dilworthNumber (graph 0 0 0) = 0 := by
      apply le_antisymm _ bot_le
      exact sInf_le ⟨0, rfl, ⟨isEmptyElim, fun u => isEmptyElim u⟩⟩
    rw [hz]
    intro h
    rw [h] at hpos
    exact (by decide : ¬ (1 : ℕ∞) ≤ 0) hpos

abbrev rankSignature := signature NatPair (fun _ => ℕ) (fun _ => ℕ)
abbrev rankArena : Arena where
  signature := rankSignature
  Law R := ∀ {r s b : ℕ}, 0 < r → 2 ≤ s → 0 < b →
    R.readout () ⟨r, s⟩ b =
      if (b : ℤ) * ((r : ℤ) - 2 * ((s : ℤ) - 1)) = (s : ℤ) * ((s : ℤ) - 1)
      then 2 else 1

private def rankActual : Realization rankSignature :=
  realize rankSignature
  (fun _ p b => Module.finrank ℝ (shiftedKernel p.1 p.2 b)) (fun e => nomatch e)

private def rankRejected : Realization rankSignature :=
  realize rankSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rankRejectedLaw : ¬ rankArena.Law rankRejected := by
  intro h
  have hb := h (r := 3) (s := 2) (b := 2) (by decide) (by decide) (by decide)
  norm_num [rankRejected, realize] at hb

def rankFamily : Registration rankArena (type_of% @shiftedKernel_finrank) where
  actual := rankActual
  bridge := Iff.rfl
  variation := ⟨@shiftedKernel_finrank, rankRejected, rankRejectedLaw⟩
  sensitivity := sensitivity rankArena.Law rankActual rankRejected rankRejectedLaw
  dependence := by
    intro _
    refine ⟨⟨3, 2⟩, 2, 1, ?_⟩
    change Module.finrank ℝ (shiftedKernel 3 2 2) ≠ Module.finrank ℝ (shiftedKernel 3 2 1)
    rw [shiftedKernel_finrank (b := 2) (by decide) (by decide) (by decide),
      shiftedKernel_finrank (b := 1) (by decide) (by decide) (by decide)]
    decide

abbrev divisorSignature := signature NatPair (fun _ => ℕ) (fun _ => ℤ)
abbrev divisorArena : Arena where
  signature := divisorSignature
  Law R := ∀ {r s b : ℕ}, 2 ≤ s → 0 < b →
    (R.readout () ⟨r, s⟩ b = (s : ℤ) * ((s : ℤ) - 1) ↔
      ∃ d : ℕ, 0 < d ∧ d ∣ s * (s - 1) ∧ r = 2 * (s - 1) + d ∧ b = s * (s - 1) / d)

private def divisorActual : Realization divisorSignature :=
  realize divisorSignature
  (fun _ p b => (b : ℤ) * ((p.1 : ℤ) - 2 * ((p.2 : ℤ) - 1))) (fun e => nomatch e)

private def divisorRejected : Realization divisorSignature :=
  realize divisorSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem divisorRejectedLaw : ¬ divisorArena.Law divisorRejected := by
  intro h
  have hb := (h (r := 3) (s := 2) (b := 2) (by decide) (by decide)).mpr
    ⟨1, by decide, by decide, by decide, by decide⟩
  norm_num [divisorRejected, realize] at hb

def divisorFamily : Registration divisorArena (type_of% @parameter_iff_divisor) where
  actual := divisorActual
  bridge := Iff.rfl
  variation := ⟨@parameter_iff_divisor, divisorRejected, divisorRejectedLaw⟩
  sensitivity := sensitivity divisorArena.Law divisorActual divisorRejected divisorRejectedLaw
  dependence := by
    intro _
    refine ⟨⟨3, 2⟩, 2, 1, ?_⟩
    change (2 : ℤ) * (3 - 2 * (2 - 1)) ≠ 1 * (3 - 2 * (2 - 1))
    decide

private abbrev OrderVertex (s : ℕ) := Vertex (3 * (s - 1)) s s

private abbrev Attains (s : ℕ) : Prop :=
  (graph (3 * (s - 1)) s s).Connected ∧
    ¬ (pathGraph 4).IsIndContained (graph (3 * (s - 1)) s s) ∧
    dilworthNumber (graph (3 * (s - 1)) s s) = 2 ∧
    ((s : ℝ) - 2 ≠ -1 ∧ (s : ℝ) - 2 ≠ -2) ∧
    (s : ℝ) - 2 ∈ spectrum ℝ (distanceMatrix (3 * (s - 1)) s s) ∧
    Module.finrank ℝ (shiftedKernel (3 * (s - 1)) s s) = 2

abbrev orderSignature := signature Unit (fun _ => ℕ) (fun _ => ℕ)
abbrev orderArena : Arena where
  signature := orderSignature
  Law R := ∀ {s : ℕ}, 2 ≤ s → R.readout () () s = 6 * s - 3 ∧ Attains s

abbrev unboundedArena : Arena where
  signature := orderSignature
  Law R := ∀ n : ℕ, ∃ s : ℕ, 2 ≤ s ∧ n < R.readout () () s ∧ Attains s

private theorem orderDependence :
    ObservationalDependence orderSignature
      (realize orderSignature (fun _ _ s => Fintype.card (OrderVertex s))
        (fun e => nomatch e)) := by
  intro _
  refine ⟨(), 2, 3, ?_⟩
  change Fintype.card (OrderVertex 2) ≠ Fintype.card (OrderVertex 3)
  rw [(family (show 2 ≤ 2 by decide)).1, (family (show 2 ≤ 3 by decide)).1]
  decide

private def orderActual : Realization orderSignature :=
  realize orderSignature (fun _ _ s => Fintype.card (OrderVertex s))
    (fun e => nomatch e)

private def orderRejected : Realization orderSignature :=
  realize orderSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem orderRejectedLaw : ¬ orderArena.Law orderRejected := by
  intro h
  exact (by decide : (0 : ℕ) ≠ 6 * 2 - 3) (h (s := 2) (by decide)).1

def orderFamily : Registration orderArena (type_of% @family) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@family, orderRejected, orderRejectedLaw⟩
  sensitivity := sensitivity orderArena.Law orderActual orderRejected orderRejectedLaw
  dependence := orderDependence

private theorem unboundedRejectedLaw : ¬ unboundedArena.Law orderRejected := by
  intro h
  obtain ⟨_, _, hn, _⟩ := h 0
  exact (Nat.lt_irrefl 0) hn

def unboundedFamily : Registration unboundedArena (type_of% @unbounded_family) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨unbounded_family, orderRejected, unboundedRejectedLaw⟩
  sensitivity := sensitivity unboundedArena.Law orderActual
    orderRejected unboundedRejectedLaw
  dependence := orderDependence

abbrev distanceSignature := signature (Σ r : ℕ, Σ s : ℕ, Σ b : ℕ, Vertex r s b)
  (fun p => Vertex p.1 p.2.1 p.2.2.1) (fun _ => ℕ)

open scoped Classical in
abbrev distanceArena : Arena where
  signature := distanceSignature
  Law R := ∀ {r s b : ℕ}, 0 < r → ∀ u v : Vertex r s b,
    R.readout () ⟨r, s, b, u⟩ v =
      if u = v then 0 else if (graph r s b).Adj u v then 1 else 2

private def distanceActual : Realization distanceSignature :=
  realize distanceSignature (fun _ p v => (graph p.1 p.2.1 p.2.2.1).dist p.2.2.2 v)
    (fun e => nomatch e)

private def distanceRejected : Realization distanceSignature :=
  realize distanceSignature (fun _ _ _ => 3) (fun e => nomatch e)

private theorem distanceRejectedLaw : ¬ distanceArena.Law distanceRejected := by
  intro h
  let u : Vertex 1 0 0 := .inl 0
  have h3 := h (by decide) u u
  simp [distanceRejected, realize] at h3

def distanceFamily : Registration distanceArena (type_of% @distance) where
  actual := distanceActual
  bridge := Iff.rfl
  variation := ⟨@distance, distanceRejected, distanceRejectedLaw⟩
  sensitivity := sensitivity distanceArena.Law distanceActual distanceRejected distanceRejectedLaw
  dependence := by
    intro _
    let u : Vertex 2 0 0 := .inl 0
    let v : Vertex 2 0 0 := .inl 1
    refine ⟨⟨2, 0, 0, u⟩, u, v, ?_⟩
    change (graph 2 0 0).dist u u ≠ (graph 2 0 0).dist u v
    rw [dist_self, dist_eq_one_iff_adj.mpr (by simp [graph, u, v])]
    decide

private abbrev leftVertex {r s b : ℕ} (i : Fin s) : Vertex r s b := .inr (.inl (.inl i))
private abbrev rightVertex {r s b : ℕ} (j : Fin s) : Vertex r s b := .inr (.inl (.inr j))

abbrev incomparableSignature :=
  signature Sizes (fun p => Fin p.2.1) (fun p => Vertex p.1 p.2.1 p.2.2)

abbrev incomparableArena : Arena where
  signature := incomparableSignature
  Law R := ∀ {r s b : ℕ}, 2 ≤ s → ∀ i j : Fin s,
    ¬ vicinal (graph r s b) (leftVertex i) (R.readout () ⟨r, s, b⟩ j) ∧
      ¬ vicinal (graph r s b) (rightVertex j) (leftVertex i)

private def incomparableActual : Realization incomparableSignature :=
  realize incomparableSignature (fun _ _ j => rightVertex j) (fun e => nomatch e)

private def incomparableRejected : Realization incomparableSignature :=
  realize incomparableSignature (fun _ _ j => leftVertex j) (fun e => nomatch e)

private theorem incomparableRejectedLaw : ¬ incomparableArena.Law incomparableRejected := by
  intro h
  exact (h (r := 0) (b := 0) (s := 2) (by decide) 0 0).1 (fun _ hv => Or.inr hv)

def incomparableFamily : Registration incomparableArena (type_of% @incomparable_parts) where
  actual := incomparableActual
  bridge := Iff.rfl
  variation := ⟨@incomparable_parts, incomparableRejected, incomparableRejectedLaw⟩
  sensitivity := sensitivity incomparableArena.Law incomparableActual
    incomparableRejected incomparableRejectedLaw
  dependence := by
    intro _
    refine ⟨⟨0, 2, 0⟩, 0, 1, ?_⟩
    change (rightVertex 0 : Vertex 0 2 0) ≠ rightVertex 1
    decide

def widthRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@width) (Realization widthSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance.widthUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance.widthFamily
  realizationSource := none
  generated := false
  arena := .source ⟨widthArena⟩
  objectArena := .source ⟨widthArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source widthArena ⟨widthFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize widthSignature
    (fun _ p b => dilworthNumber (graph p.1 p.2 b))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def rankRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@shiftedKernel_finrank) (Realization rankSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance.rankUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance.rankFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rankArena⟩
  objectArena := .source ⟨rankArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source rankArena ⟨rankFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rankSignature
    (fun _ p b => Module.finrank ℝ (shiftedKernel p.1 p.2 b))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def divisorRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@parameter_iff_divisor) (Realization divisorSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance.divisorUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance.divisorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨divisorArena⟩
  objectArena := .source ⟨divisorArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source divisorArena ⟨divisorFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize divisorSignature
    (fun _ p b => (b : ℤ) * ((p.1 : ℤ) - 2 * ((p.2 : ℤ) - 1)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def orderRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@family) (Realization orderSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance.orderUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance.orderFamily
  realizationSource := none
  generated := false
  arena := .source ⟨orderArena⟩
  objectArena := .source ⟨orderArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source orderArena ⟨orderFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize orderSignature
    (fun _ _ s => Fintype.card (OrderVertex s))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def unboundedRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@unbounded_family) (Realization orderSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance.unboundedUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance.unboundedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨unboundedArena⟩
  objectArena := .source ⟨unboundedArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source unboundedArena ⟨unboundedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize orderSignature
    (fun _ _ s => Fintype.card (OrderVertex s))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def distanceRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@distance) (Realization distanceSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance.distanceUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance.distanceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨distanceArena⟩
  objectArena := .source ⟨distanceArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source distanceArena ⟨distanceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize distanceSignature
    (fun _ p v => (graph p.1 p.2.1 p.2.2.1).dist p.2.2.2 v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def incomparableRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@incomparable_parts) (Realization incomparableSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance.incomparableUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance.incomparableFamily
  realizationSource := none
  generated := false
  arena := .source ⟨incomparableArena⟩
  objectArena := .source ⟨incomparableArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source incomparableArena ⟨incomparableFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize incomparableSignature (fun _ _ j => rightVertex j)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance
