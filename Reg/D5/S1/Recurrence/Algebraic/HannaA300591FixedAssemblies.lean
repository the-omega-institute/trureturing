import D5.S1.Recurrence.Algebraic.HannaA300591FixedAssemblies
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The exact family of invariant assembly sums, including all finite carriers. -/

namespace Reg.D5.S1.Recurrence.Algebraic.HannaA300591FixedAssemblies

open _root_.D5.S1.Recurrence.Algebraic.HannaA300591FixedAssemblies
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
open scoped BigOperators

noncomputable section

structure Input where
  V : Type
  C : Type
  finiteV : Fintype V
  finiteC : Fintype C
  decV : DecidableEq V
  allowed : ℕ → C → Prop
  S : Finset V
  T : Finset V
  g : Equiv.Perm V
  sign : C → ℤ

def total (I : Input) : ℤ := by
  letI := I.finiteV
  letI := I.finiteC
  exact ∑ E : FixedAssembly I.allowed I.S I.T I.g, weight I.sign E.val

def factored (I : Input) : ℤ := by
  letI := I.finiteV
  letI := I.finiteC
  letI := I.decV
  exact (∑ A : Assembly I.allowed (fixedVertices I.g I.S) (fixedVertices I.g I.T),
      weight I.sign A.val) *
    (∑ B : FixedAssembly I.allowed (movedVertices I.g I.S) I.T I.g, weight I.sign B.val)

abbrev signature : Signature where
  Params := Unit
  State _ := Input
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ I => total I) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ I => total I + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ I : Input, R.readout () () I = factored I

private theorem actual_law : arena.Law actual := by
  intro I
  letI := I.finiteV
  letI := I.finiteC
  letI := I.decV
  exact fixed_assembly_weight_factorization I.allowed I.S I.T I.g I.sign

private def emptyInput : Input where
  V := Unit
  C := Empty
  finiteV := inferInstance
  finiteC := inferInstance
  decV := inferInstance
  allowed _ _ := False
  S := ∅
  T := ∅
  g := Equiv.refl _
  sign e := nomatch e

private def blockedInput : Input where
  V := Unit
  C := Empty
  finiteV := inferInstance
  finiteC := inferInstance
  decV := inferInstance
  allowed _ _ := False
  S := (univ : Finset Unit)
  T := ∅
  g := Equiv.refl _
  sign e := nomatch e

private theorem empty_law : AssemblyLaw emptyInput.allowed emptyInput.S emptyInput.T
    (∅ : Finset (Block Unit Empty)) := by
  constructor <;> intro b hb <;> exact False.elim (notMem_empty b hb)

private theorem empty_stable : Stable emptyInput.g (∅ : Finset (Block Unit Empty)) := by
  intro b hb
  exact False.elim (notMem_empty b hb)

private theorem total_empty : total emptyInput = 1 := by
  let e : FixedAssembly emptyInput.allowed emptyInput.S emptyInput.T emptyInput.g :=
    ⟨∅, empty_law, empty_stable⟩
  have heq (E : FixedAssembly emptyInput.allowed emptyInput.S emptyInput.T emptyInput.g) :
      E = e := by
    apply Subtype.ext
    ext b
    exact False.elim b.2.1.elim
  unfold total
  rw [sum_eq_single e]
  · exact prod_empty
  · intro E _ hne
    exact False.elim (hne (heq E))
  · simp

private theorem total_blocked : total blockedInput = 0 := by
  unfold total
  apply sum_eq_zero
  intro E _
  obtain ⟨b, _, _⟩ := E.property.1.cover () (mem_univ ())
  exact b.2.1.elim

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h emptyInput
  have hgood := actual_law emptyInput
  change total emptyInput + 1 = factored emptyInput at hbad
  change total emptyInput = factored emptyInput at hgood
  omega

def family : Registration arena (type_of% @fixed_assembly_weight_factorization) where
  actual := actual
  bridge := by
    constructor
    · intro h I
      letI := I.finiteV
      letI := I.finiteC
      letI := I.decV
      exact h I.allowed I.S I.T I.g I.sign
    · intro h V C fV fC dV allowed S T g sign
      exact h ⟨V, C, fV, fC, dV, allowed, S, T, g, sign⟩
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact False.elim (hj (Subsingleton.elim _ _))
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), emptyInput, blockedInput, ?_⟩
    change total emptyInput ≠ total blockedInput
    rw [total_empty, total_blocked]
    norm_num

/-- The full typed bridge is retained; scoped source-occurrence reconstruction is unresolved. -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 1, 0, 0, 0, 0}
    (@fixed_assembly_weight_factorization) (Realization signature) Unit Unit where
  unitName := `D5.S1.Recurrence.Algebraic.HannaA300591FixedAssemblies.fixed_assembly_weight_factorization.audit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA300591FixedAssemblies.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ I => total I) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def allTotal (I : Input) : ℤ := by
  letI := I.finiteV
  letI := I.finiteC
  exact ∑ E : Assembly I.allowed I.S I.T, weight I.sign E.val

def rootTotal (I : Input) (x : I.V) : ℤ := by
  letI := I.finiteV
  letI := I.finiteC
  letI := I.decV
  exact ∑ b : RootBlock I.allowed I.S I.T x, I.sign (color b.val) *
    ∑ E : Assembly I.allowed (I.S \ (vertices b.val).toFinset) I.T, weight I.sign E.val

def rootActual : Realization signature :=
  realize signature (fun _ _ I => allTotal I) (fun e => nomatch e)

def rootRejected : Realization signature :=
  realize signature (fun _ _ I => allTotal I + 1) (fun e => nomatch e)

abbrev rootArena : Arena where
  signature := signature
  Law R := ∀ I : Input, ∀ x : I.V, x ∈ I.S → R.readout () () I = rootTotal I x

private theorem root_actual_law : rootArena.Law rootActual := by
  intro I x hx
  letI := I.finiteV
  letI := I.finiteC
  letI := I.decV
  exact assembly_weight_point_recursion I.allowed I.S I.T x hx I.sign

private theorem allTotal_empty : allTotal emptyInput = 1 := by
  let e : Assembly emptyInput.allowed emptyInput.S emptyInput.T := ⟨∅, empty_law⟩
  have heq (E : Assembly emptyInput.allowed emptyInput.S emptyInput.T) : E = e := by
    apply Subtype.ext
    ext b
    exact False.elim b.2.1.elim
  unfold allTotal
  rw [sum_eq_single e]
  · exact prod_empty
  · intro E _ hne
    exact False.elim (hne (heq E))
  · simp

private theorem allTotal_blocked : allTotal blockedInput = 0 := by
  unfold allTotal
  apply sum_eq_zero
  intro E _
  obtain ⟨b, _, _⟩ := E.property.cover () (mem_univ ())
  exact b.2.1.elim

private theorem root_rejected_law : ¬ rootArena.Law rootRejected := by
  intro h
  have hbad := h blockedInput () (mem_univ ())
  have hgood := root_actual_law blockedInput () (mem_univ ())
  change allTotal blockedInput + 1 = rootTotal blockedInput () at hbad
  change allTotal blockedInput = rootTotal blockedInput () at hgood
  omega

def rootFamily : Registration rootArena (type_of% @assembly_weight_point_recursion) where
  actual := rootActual
  bridge := by
    constructor
    · intro h I x hx
      letI := I.finiteV
      letI := I.finiteC
      letI := I.decV
      exact h I.allowed I.S I.T x hx I.sign
    · intro h V C fV fC dV allowed S T x hx sign
      exact h ⟨V, C, fV, fC, dV, allowed, S, T, Equiv.refl V, sign⟩ x hx
  variation := ⟨root_actual_law, rootRejected, root_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rootRejected, ?_, ?_, root_rejected_law⟩
      · intro j hj
        exact False.elim (hj (Subsingleton.elim _ _))
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), emptyInput, blockedInput, ?_⟩
    change allTotal emptyInput ≠ allTotal blockedInput
    rw [allTotal_empty, allTotal_blocked]
    norm_num

/-- Whole-claim evidence; tying the aggregate sum to a scoped source occurrence is unresolved. -/
def rootAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 1, 0, 0, 0, 0}
    (@assembly_weight_point_recursion) (Realization signature) Unit Unit where
  unitName := `D5.S1.Recurrence.Algebraic.HannaA300591FixedAssemblies.assembly_weight_point_recursion.audit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA300591FixedAssemblies.rootFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rootArena⟩
  objectArena := .source ⟨rootArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rootArena ⟨rootFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ I => allTotal I) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Recurrence.Algebraic.HannaA300591FixedAssemblies
