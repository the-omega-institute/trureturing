import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws
import Reg.Support.DependentFamily
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal BigOperators
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private theorem single_sensitivity (A : Arena) (actual bad : Realization A.signature)
    [Subsingleton A.signature.Role] [IsEmpty A.signature.Anchor] (h : ¬ A.Law bad) :
    Sensitivity A actual := by
  constructor
  · intro i
    refine ⟨bad,?_,?_,h⟩
    · intro j hj; exact (hj (Subsingleton.elim j i)).elim
    · funext e; exact isEmptyElim e
  · intro i; exact isEmptyElim i

structure PrimitiveFamily where
  S : Type
  O : Type
  d : S → Instruction (S × Option O)
  s : S
abbrev primitiveSignature : Signature where
  Params := PrimitiveFamily
  State _ := ℕ → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ C := ℕ → C.S ⊕ C.O
  Anchor := Empty
  finiteAnchor := inferInstance

def primitiveActual : Realization primitiveSignature :=
  realize primitiveSignature (fun _ C ω => path (cut C.d) (.inl C.s) ω) (fun e => nomatch e)
def primitiveBad : Realization primitiveSignature :=
  realize primitiveSignature (fun _ C _ _ => .inl C.s) (fun e => nomatch e)
def primitiveArena : Arena where
  signature := primitiveSignature
  Law R := ∀ {S O : Type} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    (d : S → Instruction (S × Option O)) (s : S) (ω : ℕ → Bool) (n : ℕ) (o : O),
    R.readout () ⟨S,O,d,s⟩ ω n = .inr o ↔
      ∃ k < n, edgeEvent d s ω k = some o ∧ ∀ j < k, edgeEvent d s ω j = none
private theorem primitive_bad : ¬ primitiveArena.Law primitiveBad := by
  intro h
  let d : Unit → Instruction (Unit × Option Bool) := fun _ => .deterministic ((),some true)
  have hh := (h d () (fun _ => false) 1 true).mpr
    ⟨0,by omega,rfl,by simp⟩
  cases hh

def primitiveRecord : Registration primitiveArena (type_of% (@primitive_event_cut)) where
  actual := primitiveActual
  bridge := Iff.rfl
  variation := ⟨primitive_event_cut,primitiveBad,primitive_bad⟩
  sensitivity := by
    letI : Subsingleton primitiveArena.signature.Role := by change Subsingleton Unit; infer_instance
    letI : IsEmpty primitiveArena.signature.Anchor := by change IsEmpty Empty; infer_instance
    exact single_sensitivity primitiveArena _ _ primitive_bad
  dependence := by
    intro i; cases i
    let d : Unit → Instruction (Unit × Option Bool) :=
      fun _ => .fair ((),some false) ((),some true)
    refine ⟨⟨Unit,Bool,d,()⟩,(fun _ => false),(fun _ => true),?_⟩
    intro h
    have hh := congrFun h 1
    simp [primitiveActual,realize,path,run,stopped,cut,mapInstruction,cutTarget,successor,d] at hh

structure Family where
  S : Type
  O : Type
  d : S → Instruction (S ⊕ O)
abbrev massSignature : Signature where
  Params := Family
  State C := C.S × C.O
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def massActual : Realization massSignature :=
  realize massSignature (fun _ C z => Z C.d z.1 z.2) (fun e => nomatch e)
def massBad : Realization massSignature :=
  realize massSignature (fun _ _ _ => 0) (fun e => nomatch e)
def renewalArena : Arena where
  signature := massSignature
  Law Q := ∀ {S O : Type} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    (d : S → Instruction (S ⊕ O)),
    let f : Matrix S O ℝ≥0∞ := fun s o => Q.readout () ⟨S,O,d⟩ (s,o)
    f = R d + T d * f
private theorem renewal_bad : ¬ renewalArena.Law massBad := by
  intro h
  let d : Unit → Instruction (Unit ⊕ Bool) := fun _ => .deterministic (.inr true)
  have hh := congrFun (congrFun (h d) ()) true
  norm_num [massBad,realize,R,T,row,stopped,d,PMF.pure_apply,Matrix.add_apply,Matrix.mul_apply] at hh
  change (0 : ℝ≥0∞) = 1 + ((T d) * (0 : Matrix Unit Bool ℝ≥0∞)) () true at hh
  simp only [Matrix.mul_zero,Matrix.zero_apply,add_zero] at hh
  exact zero_ne_one hh

private theorem immediate_mass (p o : Bool) :
    Z (fun (_ : Bool) => Instruction.deterministic (.inr p)) false o = if p=o then 1 else 0 := by
  let d : Bool → Instruction (Bool ⊕ Bool) := fun _ => .deterministic (.inr p)
  have hh := congrFun (congrFun (actual_renewal d) false) o
  simpa [R,T,row,stopped,d,PMF.pure_apply,Matrix.add_apply,Matrix.mul_apply,eq_comm] using hh

def renewalRecord : Registration renewalArena (type_of% (@actual_renewal)) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨actual_renewal,massBad,renewal_bad⟩
  sensitivity := by
    letI : Subsingleton renewalArena.signature.Role := by change Subsingleton Unit; infer_instance
    letI : IsEmpty renewalArena.signature.Anchor := by change IsEmpty Empty; infer_instance
    exact single_sensitivity renewalArena _ _ renewal_bad
  dependence := by
    intro i; cases i
    refine ⟨⟨Bool,Bool,fun _ => .deterministic (.inr true)⟩,(false,false),(false,true),?_⟩
    change Z (fun (_ : Bool) => Instruction.deterministic (.inr true)) false false ≠
      Z (fun (_ : Bool) => Instruction.deterministic (.inr true)) false true
    rw [immediate_mass,immediate_mass]
    norm_num


private def branching (s : Bool) : Instruction (Bool ⊕ Bool) :=
  if s then .deterministic (.inl true) else .deterministic (.inr true)
private theorem branching_false : never branching (.inl false) = ∅ := by
  ext ω
  simp only [never,Set.mem_iInter,Set.mem_empty_iff_false,iff_false]
  intro h
  obtain ⟨s,hs⟩ := h 1
  simp [path,run,stopped,branching,successor] at hs
private theorem branching_true : never branching (.inl true) = univ := by
  have hr (ω : ℕ → Bool) (n : ℕ) : path branching (.inl true) ω n = .inl true := by
    induction n with
    | zero => rfl
    | succ n ih => simpa [path,run,stopped,branching,successor] using ih
  ext ω; simp [never,live,hr]
private theorem branching_entry : ∀ a ∈ ({Sum.inl false} : Set (Bool ⊕ Bool)),
    tapeLaw (never branching a) = 0 := by
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  subst a
  rw [branching_false,measure_empty]

abbrev neverSignature : Signature where
  Params := Family
  State C := C.S
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set (ℕ → Bool)
  Anchor := Empty
  finiteAnchor := inferInstance
def neverActual : Realization neverSignature :=
  realize neverSignature (fun _ C s => never C.d (.inl s)) (fun e => nomatch e)
def neverBad : Realization neverSignature :=
  realize neverSignature (fun _ _ _ => univ) (fun e => nomatch e)
def reachableArena : Arena where
  signature := neverSignature
  Law Q := ∀ {S O : Type} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (hE : ∀ a ∈ E, tapeLaw (never d a) = 0) (s : S) (hs : Reachable d E s),
    tapeLaw (Q.readout () ⟨S,O,d⟩ s) = 0
private theorem reachable_bad : ¬ reachableArena.Law neverBad := by
  intro h
  have hh := h branching {Sum.inl false} branching_entry false (.entrance false rfl)
  change tapeLaw univ = 0 at hh
  rw [measure_univ] at hh
  exact one_ne_zero hh

def reachableRecord : Registration reachableArena (type_of% (@reachable_as_exit)) where
  actual := neverActual
  bridge := Iff.rfl
  variation := ⟨reachable_as_exit,neverBad,reachable_bad⟩
  sensitivity := by
    letI : Subsingleton reachableArena.signature.Role := by change Subsingleton Unit; infer_instance
    letI : IsEmpty reachableArena.signature.Anchor := by change IsEmpty Empty; infer_instance
    exact single_sensitivity reachableArena _ _ reachable_bad
  dependence := by
    intro i; cases i
    refine ⟨⟨Bool,Bool,branching⟩,false,true,?_⟩
    change never branching (.inl false) ≠ never branching (.inl true)
    rw [branching_false,branching_true]
    intro h
    have hh : (fun _ => false) ∈ (∅ : Set (ℕ → Bool)) := h.symm ▸ Set.mem_univ _
    exact hh

abbrev survivalSignature : Signature where
  Params := Family
  State C := C.S × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance
def survivalActual : Realization survivalSignature :=
  realize survivalSignature (fun _ C z => survival C.d z.1 z.2) (fun e => nomatch e)
def survivalBad : Realization survivalSignature :=
  realize survivalSignature (fun _ _ _ => 1) (fun e => nomatch e)
def escapeArena : Arena where
  signature := survivalSignature
  Law Q := ∀ {S O : Type} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (hE : ∀ a ∈ E, tapeLaw (never d a) = 0),
    ∃ L : ℕ, 0 < L ∧
      (∀ s, Reachable d E s → Q.readout () ⟨S,O,d⟩ (s,L) ≤ (1/2 : ℝ≥0∞)) ∧
      (∀ s, Reachable d E s → ∀ n, Q.readout () ⟨S,O,d⟩ (s,n*L) ≤ (1/2 : ℝ≥0∞)^n) ∧
      (∀ s, Reachable d E s → Filter.Tendsto (fun n => Q.readout () ⟨S,O,d⟩ (s,n)) Filter.atTop (nhds 0)) ∧
      (∀ s t, Reachable d E s → ¬ Reachable d E t → ∀ n, (T d ^ n) s t = 0)
private theorem escape_bad : ¬ escapeArena.Law survivalBad := by
  intro h
  obtain ⟨L,hL,hblock,_,_,_⟩ := h branching {Sum.inl false} branching_entry
  have hh := hblock false (.entrance false rfl)
  change (1 : ℝ≥0∞) ≤ 1/2 at hh
  have hn : (1/2 : ℝ≥0∞) < 1 := by norm_num [ENNReal.inv_lt_one]
  exact (not_le_of_gt hn) hh

def escapeRecord : Registration escapeArena (type_of% (@reachable_escape)) where
  actual := survivalActual
  bridge := Iff.rfl
  variation := ⟨reachable_escape,survivalBad,escape_bad⟩
  sensitivity := by
    letI : Subsingleton escapeArena.signature.Role := by change Subsingleton Unit; infer_instance
    letI : IsEmpty escapeArena.signature.Anchor := by change IsEmpty Empty; infer_instance
    exact single_sensitivity escapeArena _ _ escape_bad
  dependence := by
    intro i; cases i
    refine ⟨⟨Bool,Bool,branching⟩,(false,0),(false,1),?_⟩
    have he : live branching (.inl false) 1 = ∅ := by
      ext ω; simp [live,path,run,stopped,branching,successor]
    change survival branching false 0 ≠ survival branching false 1
    simp only [survival,he,measure_empty]
    have h0 : live branching (.inl false) 0 = univ := by ext ω; simp [live,path,run]
    rw [h0,measure_univ]
    exact one_ne_zero

def normalizationArena : Arena where
  signature := massSignature
  Law Q := ∀ {S O : Type} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (hE : ∀ a ∈ E, tapeLaw (never d a) = 0),
    (∀ a ∈ E, (∑ o, tapeLaw (exits d a o)) = 1) ∧
    (∀ s, Reachable d E s → (∑ o, Q.readout () ⟨S,O,d⟩ (s,o)) = 1)
private theorem normalization_bad : ¬ normalizationArena.Law massBad := by
  intro h
  have hh := (h branching {Sum.inl false} branching_entry).2 false (.entrance false rfl)
  have hz : (0 : ℝ≥0∞) = 1 := by simpa [massBad,realize] using hh
  exact zero_ne_one hz

def normalizationRecord : Registration normalizationArena (type_of% (@normalized_reachable_exits)) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨normalized_reachable_exits,massBad,normalization_bad⟩
  sensitivity := by
    letI : Subsingleton normalizationArena.signature.Role := by change Subsingleton Unit; infer_instance
    letI : IsEmpty normalizationArena.signature.Anchor := by change IsEmpty Empty; infer_instance
    exact single_sensitivity normalizationArena _ _ normalization_bad
  dependence := by simpa only [renewalRecord,renewalArena,normalizationArena] using renewalRecord.dependence

structure PathFamily where
  S : Type
  O : Type
  d : S → Instruction (S ⊕ O)
  a : S ⊕ O
abbrev pathSignature : Signature where
  Params := PathFamily
  State _ := ℕ → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ C := ℕ → C.S ⊕ C.O
  Anchor := Empty
  finiteAnchor := inferInstance
def pathActual : Realization pathSignature :=
  realize pathSignature (fun _ C ω => path C.d C.a ω) (fun e => nomatch e)
def pathBad : Realization pathSignature :=
  realize pathSignature (fun _ C _ _ => C.a) (fun e => nomatch e)
def finiteArena : Arena where
  signature := pathSignature
  Law Q := ∀ {S O : Type} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    (d : S → Instruction (S ⊕ O)) (a : S ⊕ O),
    tapeLaw.map (Q.readout () ⟨S,O,d,a⟩) = instructionLaw (stopped d) a ∧
    (∀ n o, MeasurableSet (trajectoryHit (S := S) n o) ∧
      instructionLaw (stopped d) a (trajectoryHit n o) = tapeLaw (hit d a n o)) ∧
    (∀ n o, MeasurableSet (hit d a n o)) ∧
    Pairwise (fun i j : ℕ × O => Disjoint (hit d a i.1 i.2) (hit d a j.1 j.2)) ∧
    (∀ s t n, tapeLaw {ω | path d (.inl s) ω n = .inl t} = (T d ^ n) s t) ∧
    (∀ s n, survival d s n = ∑ t, (T d ^ n) s t) ∧
    (∀ s o n, tapeLaw (hit d (.inl s) (n+1) o) = ((T d ^ n) * R d) s o) ∧
    (∀ o, tapeLaw (hit d a 0 o) = if a = .inr o then 1 else 0)
private theorem finite_bad : ¬ finiteArena.Law pathBad := by
  intro h
  let d : Unit → Instruction (Unit ⊕ Bool) := fun _ => .deterministic (.inr true)
  have hh := (h d (.inl ())).1
  rw [← (finite_exit_laws d (.inl ())).1] at hh
  have hm : MeasurableSet {x : ℕ → Unit ⊕ Bool | x 1 = .inr true} := by measurability
  have hx := congrArg (fun μ : Measure (ℕ → Unit ⊕ Bool) => μ {x | x 1 = .inr true}) hh
  rw [Measure.map_apply (by fun_prop) hm,
    Measure.map_apply (by exact Measurable.of_eval (fun n => measurable_run (stopped d) (.inl ()) n)) hm] at hx
  simp [pathBad,realize,path,run,stopped,successor,d] at hx

def finiteRecord : Registration finiteArena (type_of% (@finite_exit_laws)) where
  actual := pathActual
  bridge := Iff.rfl
  variation := ⟨finite_exit_laws,pathBad,finite_bad⟩
  sensitivity := by
    letI : Subsingleton finiteArena.signature.Role := by change Subsingleton Unit; infer_instance
    letI : IsEmpty finiteArena.signature.Anchor := by change IsEmpty Empty; infer_instance
    exact single_sensitivity finiteArena _ _ finite_bad
  dependence := by
    intro i; cases i
    let d : Unit → Instruction (Unit ⊕ Bool) := fun _ => .fair (.inr false) (.inr true)
    refine ⟨⟨Unit,Bool,d,.inl ()⟩,(fun _ => false),(fun _ => true),?_⟩
    intro h
    have hh := congrFun h 1
    simp [pathActual,realize,path,run,stopped,successor,d] at hh

def primitiveRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@primitive_event_cut) (type_of% (realize primitiveSignature (fun _ C ω => path (cut C.d) (.inl C.s) ω) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws.primitive_event_cut.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws.primitiveRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨primitiveArena⟩, objectArena := .source ⟨primitiveArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source primitiveArena ⟨primitiveRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize primitiveSignature (fun _ C ω => path (cut C.d) (.inl C.s) ω) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

def finiteRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_exit_laws) (type_of% (realize pathSignature (fun _ C ω => path C.d C.a ω) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws.finite_exit_laws.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws.finiteRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨finiteArena⟩, objectArena := .source ⟨finiteArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source finiteArena ⟨finiteRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize pathSignature (fun _ C ω => path C.d C.a ω) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

def reachableRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reachable_as_exit) (type_of% (realize neverSignature (fun _ C s => never C.d (.inl s)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws.reachable_as_exit.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws.reachableRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨reachableArena⟩, objectArena := .source ⟨reachableArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source reachableArena ⟨reachableRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize neverSignature (fun _ C s => never C.d (.inl s)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

def escapeRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reachable_escape) (type_of% (realize survivalSignature (fun _ C z => survival C.d z.1 z.2) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws.reachable_escape.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws.escapeRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨escapeArena⟩, objectArena := .source ⟨escapeArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source escapeArena ⟨escapeRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize survivalSignature (fun _ C z => survival C.d z.1 z.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

def normalizationRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normalized_reachable_exits) (type_of% (realize massSignature (fun _ C z => Z C.d z.1 z.2) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws.normalized_reachable_exits.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws.normalizationRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨normalizationArena⟩, objectArena := .source ⟨normalizationArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source normalizationArena ⟨normalizationRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize massSignature (fun _ C z => Z C.d z.1 z.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

def renewalRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_renewal) (type_of% (realize massSignature (fun _ C z => Z C.d z.1 z.2) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws.actual_renewal.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws.renewalRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨renewalArena⟩, objectArena := .source ⟨renewalArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source renewalArena ⟨renewalRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize massSignature (fun _ C z => Z C.d z.1 z.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws
