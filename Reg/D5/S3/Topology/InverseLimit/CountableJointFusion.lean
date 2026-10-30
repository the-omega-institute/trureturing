import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.CountableJointFusion

/-!
Source family for the countable joint finite-block fusion theorem.  The
parameter structure retains the complete active-domain, inheritance, and
reservoir hypotheses.  The registration below is a faithful source attempt;
raw occurrence selection remains open until the current compiler binding is
supplied.
-/

namespace Reg.D5.S3.Topology.InverseLimit.CountableJointFusion

open Set Filter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Topology.InverseLimit.CountableJointFusion

set_option autoImplicit false
set_option relaxedAutoImplicit false

structure SourceInputs where
  active : ℕ → ℕ → Prop
  hactive_finite : ∀ j, {k | active k j}.Finite
  hactive_eventually : ∀ k, ∃ j₀, ∀ j, j₀ ≤ j → active k j
  I : ℕ → Set ℕ
  J : ℕ → ℕ → Set ℕ
  N : ℕ → Bool → Set ℕ
  hJsubI : ∀ k j, active k j → J k j ⊆ I j
  hI_mono : ∀ ⦃h j : ℕ⦄, h ≤ j → I j ≤ᶠ[Filter.cofinite] I h
  hJ_mono : ∀ (k : ℕ) ⦃h j : ℕ⦄, active k h → active k j →
    h ≤ j → J k j ≤ᶠ[Filter.cofinite] J k h
  hpool : ∀ k j e, active k j → (J k j ∩ N k e).Infinite

structure SourceState (P : SourceInputs) where
  v : ℕ → ℕ → Bool → ℕ
  Ilim : Set ℕ
  Jlim : ℕ → Set ℕ

def certificate (P : SourceInputs) (s : SourceState P) : Prop :=
  (∀ j k e, P.active k j →
    j < s.v j k e ∧ s.v j k e ∈ P.J k j ∧ s.v j k e ∈ P.N k e ∧
      (∀ h ≤ j, s.v j k e ∈ P.I h) ∧
      (∀ h ≤ j, P.active k h → s.v j k e ∈ P.J k h)) ∧
    (∀ k, s.Jlim k = {n | ∃ j e, P.active k j ∧ n = s.v j k e}) ∧
    s.Ilim = ⋃ k, s.Jlim k ∧
    (∀ k e, (s.Jlim k ∩ P.N k e).Infinite) ∧
    (∀ h, s.Ilim ≤ᶠ[Filter.cofinite] P.I h) ∧
    (∀ k h, P.active k h → s.Jlim k ≤ᶠ[Filter.cofinite] P.J k h)

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := SourceInputs
  State := SourceState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ P s => certificate P s) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ P, ∃ s, r.readout () P s

abbrev sourceScope :=
  type_of% (@exists_countable_joint_finite_block_fusion)

theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h P
    obtain ⟨v, Ilim, Jlim, hs⟩ := h P.active P.hactive_finite P.hactive_eventually
      P.I P.J P.N P.hJsubI P.hI_mono P.hJ_mono P.hpool
    exact ⟨⟨v, Ilim, Jlim⟩, hs⟩
  · intro h active hactive_finite hactive_eventually I J N hJsubI hI_mono hJ_mono hpool
    let P : SourceInputs :=
      { active := active
        hactive_finite := hactive_finite
        hactive_eventually := hactive_eventually
        I := I
        J := J
        N := N
        hJsubI := hJsubI
        hI_mono := hI_mono
        hJ_mono := hJ_mono
        hpool := hpool }
    obtain ⟨s, hs⟩ := h P
    exact ⟨s.v, s.Ilim, s.Jlim, hs⟩

theorem actual_positive : arena.Law actual :=
  source_bridge.mp @exists_countable_joint_finite_block_fusion

def unitInputs : SourceInputs :=
  { active := fun k j => k ≤ j
    hactive_finite := by
      intro j
      simpa [Set.mem_ofPred_eq] using (Set.finite_le_nat j)
    hactive_eventually := by
      intro k
      exact ⟨k, fun j hj => hj⟩
    I := fun _ => Set.univ
    J := fun _ _ => Set.univ
    N := fun _ _ => Set.univ
    hJsubI := by
      intro k j hkj
      exact subset_rfl
    hI_mono := by
      intro h j hj
      exact Filter.Eventually.of_forall (fun _ hn => hn)
    hJ_mono := by
      intro k h j hkh hkj hj
      exact Filter.Eventually.of_forall (fun _ hn => hn)
    hpool := by
      intro k j e hkj
      simpa using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) }

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨s, hs⟩ := h unitInputs
  exact hs

def familyRegistration : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim j i))
    · intro a
      exact Empty.elim a
  dependence := by
    intro i
    obtain ⟨s, hs⟩ := actual_positive unitInputs
    let P := unitInputs
    let bad : SourceState P := ⟨fun _ _ _ => 0, ∅, fun _ => ∅⟩
    refine ⟨P, s, bad, ?_⟩
    intro heq
    have hbad := hs
    rw [heq] at hbad
    have hinf : (bad.Jlim 0 ∩ P.N 0 false).Infinite := hbad.2.2.2.1 0 false
    rcases hinf.nonempty with ⟨x, hx⟩
    have hxempty : x ∈ (∅ : Set ℕ) := by simpa [bad] using hx.1
    exact hxempty

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@exists_countable_joint_finite_block_fusion)
      (Realization signature) Unit True where
  unitName := `D5.S3.Topology.InverseLimit.CountableJointFusion.exists_countable_joint_finite_block_fusion.__information_unit
  realizationName := `Reg.D5.S3.Topology.InverseLimit.CountableJointFusion.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature (fun _ P s => certificate P s) (fun e => nomatch e))
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.InverseLimit.CountableJointFusion
