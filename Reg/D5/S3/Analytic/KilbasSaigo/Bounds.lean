import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.KilbasSaigo.Bounds
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.KilbasSaigo.Bounds
open _root_.D5.S3.Analytic.KilbasSaigo.Defs
open _root_.D5.S3.Analytic.KilbasSaigo.Series
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Analytic.KilbasSaigo.Bounds

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => g 1 p.1 p.2 0 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun i p x => if i then g 1 p.1 p.2 0 x else 0) (fun e => nomatch e)

def rejectedUpper : Realization signature :=
  realize signature (fun i p x => if i then 2 else g 1 p.1 p.2 0 x) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {m l x : ℝ}, 0 < m → m - 1 < l → 0 ≤ x →
    phi 1 m l 0 / (phi 1 m l 0 + x) ≤ R.readout false ⟨m, l⟩ x ∧
      R.readout true ⟨m, l⟩ x ≤ phi 1 m l 1 / (phi 1 m l 1 + x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := phi_pos (α := 1) (m := 1) (l := 1) (s := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hh := (h (m := 1) (l := 1) (x := 0) (by norm_num) (by norm_num) le_rfl).1
  change phi 1 1 1 0 / (phi 1 1 1 0 + 0) ≤ 0 at hh
  rw [add_zero, div_self hp.ne'] at hh
  norm_num at hh

private theorem rejected_upper_law : ¬ arena.Law rejectedUpper := by
  intro h
  have hp := phi_pos (α := 1) (m := 1) (l := 1) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hh := (h (m := 1) (l := 1) (x := 0) (by norm_num) (by norm_num) le_rfl).2
  change 2 ≤ phi 1 1 1 1 / (phi 1 1 1 1 + 0) at hh
  rw [add_zero, div_self hp.ne'] at hh
  norm_num at hh

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    cases i
    · refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        cases j
        · exact (hj rfl).elim
        · rfl
      · funext e
        exact nomatch e
    · refine ⟨rejectedUpper, ?_, ?_, rejected_upper_law⟩
      · intro j hj
        cases j
        · rfl
        · exact (hj rfl).elim
      · funext e
        exact nomatch e
  · intro e
    exact nomatch e

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  change g 1 1 1 0 0 ≠ g 1 1 1 0 1
  have hz : g 1 1 1 0 0 = 1 := by simp [g_zero, ksCoeff]
  rw [hz]
  have hb := (bounds_one (m := 1) (l := 1) (x := 1) (by norm_num) (by norm_num) (by norm_num)).2
  have hp := phi_pos (α := 1) (m := 1) (l := 1) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlt : phi 1 1 1 1 / (phi 1 1 1 1 + 1) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  exact ne_of_gt (hb.trans_lt hlt)

def family : Registration arena (type_of% @bounds_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bounds_one, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounds_one) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Bounds.unit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Bounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => g 1 p.1 p.2 0 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Bounds
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.KilbasSaigo.Bounds

namespace Reg.D5.S3.Analytic.KilbasSaigo.Bounds.Full

abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => kilbasSaigo p.1 p.2.1 p.2.2 (-x)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun i p x => if i then kilbasSaigo p.1 p.2.1 p.2.2 (-x) else 0)
    (fun e => nomatch e)

def rejectedUpper : Realization signature :=
  realize signature (fun i p x => if i then 2 else kilbasSaigo p.1 p.2.1 p.2.2 (-x))
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {α m l x : ℝ}, 0 < α → α ≤ 1 → 0 < m → m - 1 / α < l → 0 ≤ x →
    1 / (1 + Real.Gamma (1 + α * (l - m)) /
      Real.Gamma (1 + α * (l - m + 1)) * x) ≤ R.readout false ⟨α, m, l⟩ x ∧
    R.readout true ⟨α, m, l⟩ x ≤ 1 / (1 + Real.Gamma (1 + α * l) /
      Real.Gamma (1 + α * (1 + l)) * x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (α := 1) (m := 1) (l := 1) (x := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl).1
  norm_num [rejected, realize] at hh

private theorem rejected_upper_law : ¬ arena.Law rejectedUpper := by
  intro h
  have hh := (h (α := 1) (m := 1) (l := 1) (x := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl).2
  norm_num [rejectedUpper, realize] at hh

private theorem sensitivity : Sensitivity arena actual := by
  classical
  constructor
  · intro i
    cases i
    · refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        cases j
        · exact (hj rfl).elim
        · rfl
      · funext e
        exact nomatch e
    · refine ⟨rejectedUpper, ?_, ?_, rejected_upper_law⟩
      · intro j hj
        cases j
        · rfl
        · exact (hj rfl).elim
      · funext e
        exact nomatch e
  · intro e
    exact nomatch e

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1, 1⟩, 0, 1, ?_⟩
  change kilbasSaigo 1 1 1 (-0) ≠ kilbasSaigo 1 1 1 (-1)
  rw [kilbasSaigo_neg_eq_g0, kilbasSaigo_neg_eq_g0]
  have hz : g 1 1 1 0 0 = 1 := by simp [g_zero, ksCoeff]
  rw [hz]
  have hb := (bounds_one (m := 1) (l := 1) (x := 1)
    (by norm_num) (by norm_num) (by norm_num)).2
  have hp := phi_pos (α := 1) (m := 1) (l := 1) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlt : phi 1 1 1 1 / (phi 1 1 1 1 + 1) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  exact ne_of_gt (hb.trans_lt hlt)

def family : Registration arena (type_of% @bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bounds, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounds) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Bounds.Full.unit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Bounds.Full.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p x => kilbasSaigo p.1 p.2.1 p.2.2 (-x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Bounds
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.KilbasSaigo.Bounds.Full

namespace Reg.D5.S3.Analytic.KilbasSaigo.Bounds.Sign

abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun i p x => g p.1 p.2.1 p.2.2 i.val x) (fun e => nomatch e)

def rejected (i : Fin 3) : Realization signature :=
  realize signature (fun j p x => if j = i then 0 else g p.1 p.2.1 p.2.2 j.val x)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {α m l x : ℝ}, 0 < α → α ≤ 1 → 0 < m → m - 1 / α < l → 0 ≤ x →
    0 < R.readout ⟨0, by decide⟩ ⟨α, m, l⟩ x ∧
      0 < R.readout ⟨1, by decide⟩ ⟨α, m, l⟩ x ∧ 0 < R.readout ⟨2, by decide⟩ ⟨α, m, l⟩ x

private theorem rejected_law (i : Fin 3) : ¬ arena.Law (rejected i) := by
  intro h
  have hh := h (α := 1) (m := 1) (l := 1) (x := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl
  fin_cases i
  · have h0 := hh.1
    norm_num [rejected, realize] at h0
  · have h1 := hh.2.1
    norm_num [rejected, realize] at h1
  · have h2 := hh.2.2
    norm_num [rejected, realize] at h2

private theorem sensitivity : Sensitivity arena actual := by
  classical
  constructor
  · intro i
    refine ⟨rejected i, ?_, ?_, rejected_law i⟩
    · intro j hj
      funext p x
      change (j : Fin 3) ≠ i at hj
      simp only [actual, rejected, realize]
      split_ifs with hij
      · exact (hj hij).elim
      · rfl
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hn : ∃ x : ℝ, g 1 1 1 i.val x ≠ g 1 1 1 i.val 0 := by
    by_contra h
    push_neg at h
    have he : g 1 1 1 i.val = fun _ => g 1 1 1 i.val 0 := funext h
    have hd := hasDerivAt_g (α := 1) (m := 1) (l := 1)
      (by norm_num) (by norm_num) (by norm_num) i.val 0
    have hp := g_zero_pos (α := 1) (m := 1) (l := 1)
      (by norm_num) (by norm_num) (by norm_num) (i.val + 1)
    rw [he] at hd
    have hz := hd.unique (hasDerivAt_const 0 (g 1 1 1 i.val 0))
    linarith
  obtain ⟨x, hx⟩ := hn
  exact ⟨⟨1, 1, 1⟩, x, 0, hx⟩

def family : Registration arena (type_of% @pos_decreasing_convex) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pos_decreasing_convex, rejected 0, rejected_law 0⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pos_decreasing_convex) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KilbasSaigo.Bounds.Sign.unit
  realizationName := `Reg.D5.S3.Analytic.KilbasSaigo.Bounds.Sign.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun i p x => g p.1 p.2.1 p.2.2 i.val x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KilbasSaigo.Bounds
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.KilbasSaigo.Bounds.Sign
