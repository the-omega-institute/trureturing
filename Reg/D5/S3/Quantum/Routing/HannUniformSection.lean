import D5.S3.Quantum.Routing.HannUniformSection
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Complete-family source-owner audits for original Hann probability sections. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Reg.D5.S3.Quantum.Routing.HannUniformSection

open _root_.D5.S3.Quantum.Routing
open ReversibleQram (Address)
open HannRouterProfiles (Router)
open HannSpatialQram (Qutrit)
open HannSignedCertificate HannExactForest HannUniformSection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev leafSignature : Signature := Reg.Support.SingleDependentReadout.signature ℕ
  (fun n => Address n → ℝ) (fun n => Address n → ℝ)

def actualLeaf : Realization leafSignature :=
  realize leafSignature (fun _ _ x => x) (fun e => nomatch e)

def rejectedLeaf : Realization leafSignature :=
  realize leafSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem leaf_dependence : ObservationalDependence leafSignature actualLeaf := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  exact zero_ne_one (congrFun h ())

namespace Binary

def law (R : Realization leafSignature) : Prop :=
  ∀ (n : ℕ) (q : Router n → ℝ) (x : Address n → ℝ) (c : Node n → ℝ)
    (hx : ∀ a, 0 ≤ x a) (hxn : x ≠ 0)
    (hk : (matrix n q).mulVec (Sum.elim x c) = 0),
    ∃ (u : Address n → ℝ) (d : Node n → ℝ),
      (matrix n q).mulVec (Sum.elim u d) = 0 ∧ u ≠ 0 ∧
      (∀ a, u a = 0 ∨ u a = 1) ∧ (∀ a, u a ≠ 0 → 0 < R.readout () n x a) ∧
      (∀ v, d v = 0 ∨ d v = -1 ∨ d v = 1) ∧
      (∀ v, d v ≠ 0 → SignType.sign (d v) = SignType.sign (c v)) ∧
      SignType.sign (d (root n)) = SignType.sign (c (root n))

abbrev arena : Arena := ⟨leafSignature, law⟩

private theorem rejected_law : ¬ law rejectedLeaf := by
  intro h
  let q : Router 0 → ℝ := fun v => v.elim
  have hk : (matrix 0 q).mulVec (Sum.elim (fun _ => (1 : ℝ)) (fun _ => 1)) = 0 := by
    ext i
    simp [matrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  obtain ⟨u, d, _, hu, _, hs, _⟩ := h 0 q (fun _ => 1) (fun _ => 1)
    (by norm_num) (by intro hz; exact one_ne_zero (congrFun hz ())) hk
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hu
  exact (lt_irrefl (0 : ℝ)) (hs a ha)

def family : Registration arena (type_of% binary_conformal_kernel) where
  actual := actualLeaf
  bridge := Iff.rfl
  variation := ⟨binary_conformal_kernel, rejectedLeaf, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity law actualLeaf rejectedLeaf rejected_law
  dependence := leaf_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    binary_conformal_kernel (Realization leafSignature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannUniformSection.Binary.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannUniformSection.Binary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize leafSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Routing.HannUniformSection
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","arg","body","arg","body","arg","arg","arg","fn","arg","body","body","arg","fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Binary

namespace Zero

def law (R : Realization leafSignature) : Prop :=
  ∀ (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v ∧ q v ≤ 1)
    (p : Address n → ℝ) (hp : ∀ a, 0 ≤ p a) (hm : (∑ a, p a) = 1)
    (hz : synthesis n q bus (fun a => (p a : ℂ)) = 0),
    ∃ S : Finset (Address n), S.Nonempty ∧ (∀ a ∈ S, 0 < R.readout () n p a) ∧
      (∑ a ∈ S, record n q bus a) = 0

abbrev arena : Arena := ⟨leafSignature, law⟩

private def rates : Router 2 → ℝ
  | none => 1
  | some (false, _) => -(1 / 2)
  | some (true, _) => 1

private def masses (a : Address 2) : ℝ := if a.1 then if a.2.1 then 0 else 1 / 3 else 1 / 3

private def nodes : Node 2 → ℂ
  | none => 0
  | some (false, none) => -(1 / 3)
  | some (true, none) => 1 / 3
  | some (b, some (d, _)) => (masses (b, (d, ())) : ℂ)

private theorem zero_relation : synthesis 2 rates Qutrit.wait (fun a => (masses a : ℂ)) = 0 := by
  have hq : ∀ v, -(1 / 2 : ℝ) ≤ rates v ∧ rates v ≤ 1 := by
    intro v; cases v with
    | none => norm_num [rates]
    | some v => obtain ⟨b,v⟩ := v; cases b <;> norm_num [rates]
  suffices hh : synthesis 2 rates Qutrit.wait (fun a => (masses a : ℂ)) =
      (0 : ℂ) • vacuumRecord 2 rates by simpa using hh
  apply (relation_iff_matrix_kernel 2 rates Qutrit.wait hq _ 0).mpr
  refine ⟨nodes, rfl, (kernel_iff_equations 2 rates _ _).mpr ?_⟩
  norm_num [Equations, Local, nodes, masses, rates, root, restrict, childCoeff,
    childValues, Bool.forall_bool]

private theorem rejected_law : ¬ law rejectedLeaf := by
  intro h
  have hq : ∀ v, -(1 / 2 : ℝ) ≤ rates v ∧ rates v ≤ 1 := by
    intro v; cases v with
    | none => norm_num [rates]
    | some v => obtain ⟨b,v⟩ := v; cases b <;> norm_num [rates]
  have hp : ∀ a, 0 ≤ masses a := by intro a; unfold masses; split_ifs <;> norm_num
  have hm : (∑ a, masses a) = 1 := by
    norm_num [masses, Fintype.sum_prod_type, Fintype.sum_bool]
  obtain ⟨S, hs, hpos, _⟩ := h 2 rates Qutrit.wait hq masses hp hm zero_relation
  obtain ⟨a, ha⟩ := hs
  exact (lt_irrefl (0 : ℝ)) (hpos a ha)

def family : Registration arena (type_of% zero_certificate) where
  actual := actualLeaf
  bridge := Iff.rfl
  variation := ⟨zero_certificate, rejectedLeaf, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity law actualLeaf rejectedLeaf rejected_law
  dependence := leaf_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    zero_certificate (Realization leafSignature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannUniformSection.Zero.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannUniformSection.Zero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize leafSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Routing.HannUniformSection
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg","body","arg","fn","arg","body","body","arg","fn"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Zero

namespace Interval

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature ℕ
  (fun n => Router n → ℝ) (fun _ => Qutrit → Set ℝ)

def actual : Realization signature :=
  realize signature (fun _ n q => Section n q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => Set.univ) (fun e => nomatch e)

def law (R : Realization signature) : Prop :=
  ∀ (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v ∧ q v ≤ 1),
    (Section n q bus = ∅ ∨ ∃ l r : ℝ, l ≤ r ∧ R.readout () n q bus = Set.Icc l r ∧
      UniformEndpoint n q bus l ∧ UniformEndpoint n q bus r) ∧
    (0 ∈ Section n q bus → ∃ S : Finset (Address n), S.Nonempty ∧
      (∑ a ∈ S, record n q bus a) = 0)

abbrev arena : Arena := ⟨signature, law⟩

private theorem upper_one : (1 : ℝ) ∈ Section 1 (fun _ => 1) Qutrit.wait := by
  refine ⟨fun a => if a.1 then 0 else 1, ?_, ?_, ?_⟩
  · intro a; dsimp; split_ifs <;> norm_num
  · simp [Fintype.sum_prod_type, Fintype.sum_bool]
  · ext e
    simp [synthesis, record, vacuumRecord, Fintype.sum_prod_type, Fintype.sum_bool,
      Fintype.prod_option, local_upper]

private theorem interior_not_one : (1 : ℝ) ∉ Section 1 (fun _ => 0) Qutrit.wait := by
  rintro ⟨p, hp, hm, he⟩
  have h := below_upper_relation 0 (fun _ => 0) Qutrit.wait (by norm_num)
    (by norm_num) (fun a => (p a : ℂ)) 1 he
  have hz := h.2.2 (by norm_num)
  exact one_ne_zero hz

private theorem rejected_law : ¬ law rejected := by
  intro h
  let q : Router 0 → ℝ := fun v => v.elim
  have hm : (1 : ℝ) ∈ Section 0 q Qutrit.wait := by
    refine ⟨fun _ => 1, by norm_num, by simp, ?_⟩
    ext e; simp [synthesis, record, vacuumRecord]
  obtain ⟨hf, _⟩ := h 0 q Qutrit.wait (by intro v; exact v.elim)
  rcases hf with hempty | ⟨l,r,hle,heq,_⟩
  · simpa [hempty] using hm
  · have hx : r + 1 ∈ (Set.univ : Set ℝ) := Set.mem_univ _
    change (Set.univ : Set ℝ) = Set.Icc l r at heq
    rw [heq] at hx
    linarith [hx.2]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 1), (fun _ => 0), ?_⟩
  intro heq
  apply interior_not_one
  have heq := congrFun heq Qutrit.wait
  change Section 1 (fun _ => 1) Qutrit.wait = Section 1 (fun _ => 0) Qutrit.wait at heq
  rw [← heq]
  exact upper_one

def family : Registration arena (type_of% uniform_section) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_section, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    uniform_section (Realization signature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannUniformSection.Interval.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannUniformSection.Interval.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n q => Section n q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Routing.HannUniformSection
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","arg","arg","body","arg","body","arg","fn","arg","fn","arg","fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Interval

#print axioms Binary.family
#print axioms Zero.family
#print axioms Interval.family

end Reg.D5.S3.Quantum.Routing.HannUniformSection
