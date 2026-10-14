import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Resolution.OpenPullbackObstruction
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff

/-!
# Obstruction source families

The original resolution type, topology, compactness, Hausdorffness, total
disconnectedness, map and its two hypotheses remain parameters. The state is
an actual Cantor-to-interval section and the readout is the complete original
construction certificate. These kernel family proofs do not certify an absent
raw source-selection reconstruction.
-/

namespace Reg.D5.S3.Topology.Resolution.OpenPullbackObstruction

open Set Filter _root_.Topology TopologicalSpace
open _root_.D5.S3.Topology.Resolution.OpenPullbackObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape
open scoped unitInterval

universe u v

structure Inputs where
  E : Type u
  top : TopologicalSpace E
  compact : @CompactSpace E top
  hausdorff : @T2Space E top
  disconnected : @TotallyDisconnectedSpace E top
  a : E → Square
  continuous : @Continuous E Square top inferInstance a
  surjective : Function.Surjective a

def certificate (P : Inputs.{u}) (s : Cantor → I) : Prop :=
  letI := P.top
  Construction.{u, v} P.a s

def signature : DependentFamily.Signature where
  Params := Inputs.{u}
  State := fun _ => Cantor → I
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ P s => certificate.{u, v} P s)
    (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature.{u}
  Law := fun R => ∀ P, ∃ s, R.readout () P s

abbrev sourceScope := type_of% (@exists_obstruction.{u, v})

theorem source_bridge : sourceScope.{u, v} ↔ arena.{u}.Law actual.{u, v} := by
  constructor
  · intro h P
    let := P.top
    let := P.compact
    let := P.hausdorff
    let := P.disconnected
    exact h P.a P.continuous P.surjective
  · intro h E tE hcE hhE hdE a ha hao
    exact h ⟨E, tE, hcE, hhE, hdE, a, ha, hao⟩

theorem actual_positive : arena.{u}.Law actual.{u, v} :=
  source_bridge.mp (@exists_obstruction.{u, v})

noncomputable def sampleInputs : Inputs.{u} := by
  let : MetricSpace Cantor := PiNat.metricSpace
  let hex := exists_nat_bool_continuous_surjective_of_compact Square
  let a := hex.choose
  have ha := hex.choose_spec.1
  have hao := hex.choose_spec.2
  let : TotallyDisconnectedSpace (ULift.{u} Cantor) :=
    (Homeomorph.ulift.symm).totallyDisconnectedSpace
  refine ⟨ULift.{u} Cantor, inferInstance, inferInstance, inferInstance,
    inferInstance, a ∘ ULift.down, ha.comp continuous_uliftDown, ?_⟩
  intro z
  obtain ⟨b, hb⟩ := hao z
  exact ⟨ULift.up b, hb⟩

noncomputable def badSection : Cantor → I := by
  classical
  exact fun b => if b = D5.S3.Topology.Resolution.OpenPullbackObstruction.star then 1 else 0

theorem badSection_discontinuous : ¬ Continuous badSection := by
  classical
  let b : ℕ → Cantor := fun n => Function.update star n true
  have hb : ∀ n, b n ≠ star := by
    intro n he
    have hh := congrFun he n
    simp [b, _root_.D5.S3.Topology.Resolution.OpenPullbackObstruction.star] at hh
  have hlim : Tendsto b atTop (𝓝 star) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_def.mpr
    intro U hU
    have hf : false ∈ U := mem_of_mem_nhds hU
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    simpa [b, Function.update_of_ne (show i ≠ n by omega),
      _root_.D5.S3.Topology.Resolution.OpenPullbackObstruction.star] using hf
  intro hs
  have h : Tendsto (fun _ : ℕ => (0 : I)) atTop (𝓝 (1 : I)) := by
    have hh := (hs.tendsto star).comp hlim
    have hf : badSection ∘ b = fun _ => (0 : I) := by
      funext n
      simp only [Function.comp_apply, badSection, if_neg (hb n)]
    rw [hf] at hh
    have hstar : badSection _root_.D5.S3.Topology.Resolution.OpenPullbackObstruction.star = 1 := by
      simp [badSection]
    rw [hstar] at hh
    exact hh
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds h)

def rejected : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun e => nomatch e)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨s, hs⟩ := h sampleInputs
  exact hs

noncomputable def familyRegistration :
    DependentFamily.Registration arena.{u} sourceScope.{u, v} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨s, hs⟩ := actual_positive.{u, v} sampleInputs
    refine ⟨sampleInputs, s, badSection, ?_⟩
    intro heq
    have hc : certificate.{u, v} sampleInputs s := hs
    have hbad : certificate.{u, v} sampleInputs badSection := by
      change certificate.{u, v} sampleInputs s = certificate.{u, v} sampleInputs badSection at heq
      exact heq ▸ hc
    let := sampleInputs.top
    exact badSection_discontinuous hbad.sectionContinuous

/- Raw coordinates and occurrence reconstruction are not asserted. This is an
honest incomplete source binding, with the full family obligations proved. -/
noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@exists_obstruction.{u, v})
      (DependentFamily.Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Topology.Resolution.OpenPullbackObstruction.exists_obstruction.__information_unit
  realizationName := `Reg.D5.S3.Topology.Resolution.OpenPullbackObstruction.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature.{u}
    (fun _ P s => certificate.{u, v} P s) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


namespace Section

structure Inputs where
  K : Set Square
  closed : IsClosed K
  lower : (D5.S3.Topology.Resolution.OpenPullbackObstruction.star, (0 : I)) ∈ K
  upper : (D5.S3.Topology.Resolution.OpenPullbackObstruction.star, (1 : I)) ∉ K

def certificate (P : Inputs) (s : Cantor → I) : Prop :=
  Continuous s ∧ IsClosed {b | (b, s b) ∈ P.K} ∧ ¬ IsOpen {b | (b, s b) ∈ P.K}

def signature : DependentFamily.Signature where
  Params := Inputs
  State := fun _ => Cantor → I
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ P s => certificate P s) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ P, ∃ s, R.readout () P s

abbrev sourceScope := type_of% (@exists_nonopen_section)

theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h P
    exact h P.K P.closed P.lower P.upper
  · intro h K hK hzero hone
    exact h ⟨K, hK, hzero, hone⟩

theorem actual_positive : arena.Law actual := source_bridge.mp exists_nonopen_section

def sampleInputs : Inputs where
  K := {z | z.2 = 0}
  closed := isClosed_singleton.preimage continuous_snd
  lower := rfl
  upper := one_ne_zero

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨s, hs⟩ := h sampleInputs
  exact hs

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨s, hs⟩ := actual_positive sampleInputs
    refine ⟨sampleInputs, s, (fun _ => (0 : I)), ?_⟩
    intro heq
    have hc : certificate sampleInputs s := hs
    have hbad : certificate sampleInputs (fun _ => 0) := by
      change certificate sampleInputs s = certificate sampleInputs (fun _ => 0) at heq
      exact heq ▸ hc
    exact hbad.2.2 (by simpa [sampleInputs] using (isOpen_univ : IsOpen (univ : Set Cantor)))

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@exists_nonopen_section) (DependentFamily.Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Topology.Resolution.OpenPullbackObstruction.exists_nonopen_section.__information_unit
  realizationName :=
    `Reg.D5.S3.Topology.Resolution.OpenPullbackObstruction.Section.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ P s => certificate P s) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Section

end Reg.D5.S3.Topology.Resolution.OpenPullbackObstruction
