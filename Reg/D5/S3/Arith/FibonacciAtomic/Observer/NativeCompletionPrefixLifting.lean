import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
import Reg.Support.DependentFamily
import Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns (Frontier fill)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization (RankedExpr)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation (fixedEval)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting

abbrev cylinderSignature : Signature where
  Params := Σ _h : Nat, Σ _T : CompletionTree, Address
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def cylinderActual : Realization cylinderSignature :=
  realize cylinderSignature (fun _ p t => readout p.2.2 t) (fun e => nomatch e)

def cylinderBad : Realization cylinderSignature :=
  realize cylinderSignature (fun _ _ _ => .absent) (fun e => nomatch e)

abbrev cylinderArena : Arena where
  signature := cylinderSignature
  Law R := ∀ (h : Nat) (T : CompletionTree) (t : Source),
    (∀ a : Address, a.length ≤ h → R.readout () ⟨h,T,a⟩ t = completionReadout a T) ↔
      ∃ f : Frontier (cutoff (h+1) T) → Source, t = fill (cutoff (h+1) T) f

private theorem cylinder_bad : ¬ cylinderArena.Law cylinderBad := by
  intro h
  have eq := (h 0 (leaf true) (.of true)).mpr ⟨PEmpty.elim, rfl⟩ [] (by simp)
  change Reply.absent = Reply.alpha at eq
  cases eq

def cylinderProof : Registration cylinderArena (type_of% (@prefix_cylinder)) where
  actual := cylinderActual
  bridge := Iff.rfl
  variation := ⟨prefix_cylinder, cylinderBad, cylinder_bad⟩
  sensitivity := ⟨fun i => ⟨cylinderBad,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, cylinder_bad⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨0,leaf true,[]⟩, .of true, .of false, ?_⟩
    intro eq
    cases eq

abbrev signature : Signature where
  Params := Σ k : Nat, Σ r : Nat, Σ m : Nat,
    Σ _pairs : List (RankedExpr k (r + m) × RankedExpr k (r + m)),
    Σ _n : Fin k → Nat, Fin r → Source
  State p := Fin p.2.2.1 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := RankedExpr p.1 (p.2.1 + p.2.2.1) → Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p z => fixedEval p.2.2.2.2.1 p.2.2.2.2.2 z) (fun e => nomatch e)

def bad : Realization signature := realize signature
  (fun _ p z => NativeSimultaneousPrefixSeparation.bad.readout ()
    ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,(fun _ => True),
      p.2.2.2.2.1,p.2.2.2.2.2,(fun _ => 1),
      (fun _ => cutoff 1 (node (leaf true) (leaf true)))⟩ z)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k r m : Nat)
    (pairs : List (RankedExpr k (r + m) × RankedExpr k (r + m)))
    (n : Fin k → Nat) (f : Fin r → Source),
    (∃ z : Fin m → Source, ∀ e ∈ pairs,
      R.readout () ⟨k,r,m,pairs,n,f⟩ z e.1 ≠
        R.readout () ⟨k,r,m,pairs,n,f⟩ z e.2) →
    ∀ (T : Fin m → CompletionTree), (∀ i, HasInfiniteBranch (T i)) →
    ∀ (h : Fin m → Nat), ∃ z : Fin m → Source,
      (∀ (i : Fin m) (a : Address), a.length ≤ h i →
        readout a (z i) = completionReadout a (T i)) ∧ ∀ e ∈ pairs,
      R.readout () ⟨k,r,m,pairs,n,f⟩ z e.1 ≠ R.readout () ⟨k,r,m,pairs,n,f⟩ z e.2

private def fullBranch : CompletionTree :=
  PFunctor.M.corec (fun _ : Unit =>
    (⟨.inr (), fun _ : Bool => ()⟩ : completionFunctor Unit)) ()

private theorem fullBranch_dest : PFunctor.M.dest fullBranch =
    (⟨.inr (), fun _ : Bool => fullBranch⟩ : completionFunctor CompletionTree) := by
  exact PFunctor.M.dest_corec _ ()

private theorem fullBranch_readout (a : Address) : completionReadout a fullBranch = .branch := by
  induction a with
  | nil => simp only [completionReadout, fullBranch_dest]
  | cons b a ih => simpa only [completionReadout, fullBranch_dest] using ih

private theorem fullBranch_infinite : HasInfiniteBranch fullBranch := by
  refine ⟨fun _ => false, fun d => ?_⟩
  rw [fullBranch_readout]
  intro h; cases h

private def n : Fin 0 → Nat := fun x => nomatch x
private def f : Fin 0 → Source := fun x => nomatch x
private def A : RankedExpr 0 (0 + 1) := .residual 0 (.inr 0)
private def B : RankedExpr 0 (0 + 1) := .ground (.mul (.of true) (.of true))

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have witness : ∃ z : Fin 1 → Source, ∀ e ∈ [(A,B)],
      bad.readout () ⟨0,0,1,[(A,B)],n,f⟩ z e.1 ≠
        bad.readout () ⟨0,0,1,[(A,B)],n,f⟩ z e.2 := by
    refine ⟨fun _ => .of true, ?_⟩
    intro e he
    have ep : e = (A,B) := by simpa using he
    subst e
    intro no
    change FreeMagma.of true = FreeMagma.mul (.of true) (.of true) at no
    cases no
  obtain ⟨z, pref, neq⟩ := h 0 0 1 [(A,B)] n f witness (fun _ => fullBranch)
    (fun _ => fullBranch_infinite) (fun _ => 0)
  have root := pref 0 [] (by simp)
  rw [fullBranch_readout] at root
  have no := neq (A,B) (by simp)
  cases hz : z 0 with
  | of b => rw [hz] at root; cases b <;> cases root
  | mul l r =>
    apply no
    simp only [bad, NativeSimultaneousPrefixSeparation.bad, realize]
    rw [show fixedEval n f z A = .mul l r by
      change z 0 = .mul l r
      exact hz]
    rfl

def proof : Registration arena (type_of% (@simultaneous_prefix_disequality)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@simultaneous_prefix_disequality, bad, bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, bad_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨0,0,1,[],n,f⟩,
      (fun _ => .of true),(fun _ => .of false),?_⟩
    intro eq
    have no := congrFun eq A
    cases no

noncomputable def prefix_cylinder_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting.prefix_cylinder)
    (Realization cylinderSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting.prefix_cylinder
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting.cylinderProof
  realizationSource := none
  generated := false
  arena := .source ⟨cylinderArena⟩
  objectArena := .source ⟨cylinderArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cylinderArena ⟨cylinderProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cylinderSignature (fun _ p t => readout p.2.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
    definition := none
    coordinates := #[0,1,3]
    readouts := #[{
      path := #["body","body","body","fn","arg","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting.simultaneous_prefix_disequality)
    (Realization signature) (Nat → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting.simultaneous_prefix_disequality
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p z => fixedEval p.2.2.2.2.1 p.2.2.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
    definition := none
    coordinates := #[0,1,2,3,4,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","domain",
        "arg","body","body","body","fn","arg","fn"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms cylinderProof
#print axioms proof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting.EmbedReadout

abbrev signature : Signature where
  Params := Address
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ a t => readout a t) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => .absent) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : Address) (t : Source), completionReadout a (embed t) = R.readout () a t

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have h := law [] (.of true)
  change Reply.alpha = Reply.absent at h
  cases h

def proof : Registration arena (type_of% (@embed_readout)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨embed_readout,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,bad_law⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨[],.of true,.of false,?_⟩
    intro h
    cases h

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@embed_readout) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting.EmbedReadout.embed_readout
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting.EmbedReadout.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a t => readout a t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting.EmbedReadout

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting.TreeCases

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ b => leaf b) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => leaf false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P : CompletionTree → Prop} (T : CompletionTree),
    (∀ b, P (R.readout () () b)) → (∀ l r, P (node l r)) → P T

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have h := law (P := fun t => completionReadout [] t ≠ .alpha) (leaf true)
    (fun _ => by intro h; cases h) (fun _ _ => by intro h; cases h)
  apply h
  rfl

def proof : Registration arena (type_of% (@tree_cases)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tree_cases,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,bad_law⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(),true,false,?_⟩
    intro h
    have no := congrArg (completionReadout []) h
    change Reply.alpha = Reply.beta at no
    cases no

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@tree_cases) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting.TreeCases.tree_cases
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting.TreeCases.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => leaf b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
    definition := none
    coordinates := #[ ]
    readouts := #[{
      path := #["body","body","domain","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting.TreeCases
