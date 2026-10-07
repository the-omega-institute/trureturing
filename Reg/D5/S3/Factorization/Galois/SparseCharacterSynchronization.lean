import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.Galois.SparseCharacterSynchronization
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ZMod

namespace Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization

open _root_.D5.S3.Factorization.Galois.SparseCharacterSynchronization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v

/-- Keep the source vertex type, graph, coefficient type and group instance.
The observed state is its additive homomorphism; the readout is the actual kernel. -/
def signature : Signature where
  Params := Σ (V : Type u), Σ (_ : SimpleGraph V), Σ (A : Type v), AddCommGroup A
  State p := by
    letI : AddCommGroup p.2.2.1 := p.2.2.2
    exact (p.1 → p.2.2.1) →+
      ({e : p.1 × p.1 // p.2.1.Adj e.1 e.2} → p.2.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := by
    letI : AddCommGroup p.2.2.1 := p.2.2.2
    exact AddSubgroup (p.1 → p.2.2.1)
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Replace only the selected kernel application. The entire original telescope,
constant subgroup and graph preconnectedness remain in the law. -/
def arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {V : Type u} (G : SimpleGraph V) (A : Type v)
    [inst : AddCommGroup A] [Nontrivial A],
    r.readout () ⟨V, G, A, inst⟩ (edgeDifference G A) =
      (Pi.constAddMonoidHom V A).range ↔ G.Preconnected

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p f => by
    letI : AddCommGroup p.2.2.1 := p.2.2.2
    exact f.ker) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ p _ => by
    letI : AddCommGroup p.2.2.1 := p.2.2.2
    exact (⊤ : AddSubgroup (p.1 → p.2.2.1))) (fun e => nomatch e)

/-- The intervention admits a nonconstant labeling on a connected two-vertex graph. -/
theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let A := ULift.{v} (ZMod 2)
  let x : ULift.{u} Bool → A := fun i => if i.down then 1 else 0
  have heq := (h (⊤ : SimpleGraph (ULift.{u} Bool)) A).mpr
    SimpleGraph.preconnected_top
  have hx : x ∈ (Pi.constAddMonoidHom (ULift.{u} Bool) A).range :=
    heq ▸ (show x ∈ (⊤ : AddSubgroup (ULift.{u} Bool → A)) from trivial)
  obtain ⟨a, ha⟩ := hx
  have hzero : a = 0 := by
    have : a = x ⟨false⟩ := congrFun ha ⟨false⟩
    simpa [x] using this
  have hone : a = 1 := by
    have : a = x ⟨true⟩ := congrFun ha ⟨true⟩
    simpa [x] using this
  exact zero_ne_one (hzero.symm.trans hone)

def registration : Registration arena.{u,v}
    (∀ {V : Type u} (G : SimpleGraph V) (A : Type v)
      [AddCommGroup A] [Nontrivial A],
      (edgeDifference G A).ker = (Pi.constAddMonoidHom V A).range ↔ G.Preconnected) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro V G A _ _; exact edge_difference_kernel_eq_constants_iff G A,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    let V := ULift.{u} Bool
    let A := ULift.{v} (ZMod 2)
    let G : SimpleGraph V := ⊤
    let x : V → A := fun j => if j.down then 1 else 0
    refine ⟨⟨V, G, A, inferInstance⟩, edgeDifference G A,
      (0 : (V → A) →+ ({e : V × V // G.Adj e.1 e.2} → A)), ?_⟩
    change (edgeDifference G A).ker ≠ (0 : (V → A) →+ _).ker
    intro h
    have hx : x ∈ (edgeDifference G A).ker := by
      rw [h, AddMonoidHom.mem_ker]
      rfl
    have he := congrFun (AddMonoidHom.mem_ker.mp hx)
      ⟨(⟨false⟩, ⟨true⟩), by
        change (⟨false⟩ : V) ≠ ⟨true⟩
        intro heq
        cases congrArg ULift.down heq⟩
    have hbad : (0 : A) = 1 := by
      apply sub_eq_zero.mp
      simpa [edgeDifference, x] using he
    exact zero_ne_one hbad

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.Galois.SparseCharacterSynchronization.edge_difference_kernel_eq_constants_iff.{u, v}) (type_of% (realize.{max (u + 1) (v + 1), max u v, 0, max u v, 0} signature.{u, v}
    (fun (_ : Unit) (p : signature.Params) (f : signature.State p) => by
      letI : AddCommGroup.{v} p.2.2.1 := p.2.2.2
      exact f.ker)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "Galois") "SparseCharacterSynchronization") "edge_difference_kernel_eq_constants_iff") "Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization/Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u, v})⟩,
  objectArena := .source ⟨(arena.{u, v})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u, v}) ⟨(registration.{u, v})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u + 1) (v + 1), max u v, 0, max u v, 0} signature.{u, v}
    (fun (_ : Unit) (p : signature.Params) (f : signature.State p) => by
      letI : AddCommGroup.{v} p.2.2.1 := p.2.2.2
      exact f.ker)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Galois.SparseCharacterSynchronization, definition := none, coordinates := #[0, 1, 2, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `D5.S3.Factorization.Galois.SparseCharacterSynchronization.edge_difference_kernel_eq_constants_iff, part := .type, path := [], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u, .param `v] }], facts := [`Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.canonicalArenaFact, `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.sourceBridgeFact, `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.observationFact0, `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization


noncomputable def Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.canonicalArenaOperand.{u, v} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u + 1) (v + 1), max u v, 0, max u v, 0} :=
  Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.arena.{u, v}
noncomputable def Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.canonicalArenaFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"SparseCharacterSynchronization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"SparseCharacterSynchronization\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.canonicalObjectArenaOperand.{u, v} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u + 1) (v + 1), max u v, 0, max u v, 0} :=
  Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.arena.{u, v}
noncomputable def Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.canonicalObjectArenaFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"SparseCharacterSynchronization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"SparseCharacterSynchronization\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  .evidence


noncomputable def Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.sourceLaw.{u, v} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u + 1) (v + 1), max u v, 0, max u v, 0}
  Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.arena.{u, v}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{max (u + 1) (v + 1), max u v, 0,
        max u v, 0}
    Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.arena.{u, v}
    (∀ {V : Type u} (G : SimpleGraph.{u} V) (A : Type v) [inst : AddCommGroup.{v} A] [Nontrivial.{v} A],
      Iff
        (@Eq.{max (u + 1) (v + 1)}
          (@AddSubgroup.{max u v} (V → A)
            (@Pi.addGroup.{u, v} V (fun (a : V) => A) fun (i : V) => @AddCommGroup.toAddGroup.{v} A inst))
          (@AddMonoidHom.ker.{max u v, max u v} (V → A)
            (@Pi.addGroup.{u, v} V (fun (a : V) => A) fun (i : V) => @AddCommGroup.toAddGroup.{v} A inst)
            ((@Subtype.{u + 1} (Prod.{u, u} V V) fun (e : Prod.{u, u} V V) =>
                @SimpleGraph.Adj.{u} V G (@Prod.fst.{u, u} V V e) (@Prod.snd.{u, u} V V e)) →
              A)
            (@Pi.addZeroClass.{u, v}
              (@Subtype.{u + 1} (Prod.{u, u} V V) fun (e : Prod.{u, u} V V) =>
                @SimpleGraph.Adj.{u} V G (@Prod.fst.{u, u} V V e) (@Prod.snd.{u, u} V V e))
              (fun
                  (a :
                    @Subtype.{u + 1} (Prod.{u, u} V V) fun (e : Prod.{u, u} V V) =>
                      @SimpleGraph.Adj.{u} V G (@Prod.fst.{u, u} V V e) (@Prod.snd.{u, u} V V e)) =>
                A)
              fun
                (i :
                  @Subtype.{u + 1} (Prod.{u, u} V V) fun (e : Prod.{u, u} V V) =>
                    @SimpleGraph.Adj.{u} V G (@Prod.fst.{u, u} V V e) (@Prod.snd.{u, u} V V e)) =>
              @AddMonoid.toAddZeroClass.{v} A
                (@SubNegMonoid.toAddMonoid.{v} A
                  (@AddGroup.toSubNegMonoid.{v} A (@AddCommGroup.toAddGroup.{v} A inst))))
            (@D5.S3.Factorization.Galois.SparseCharacterSynchronization.edgeDifference.{u, v} V G A inst))
          (@AddMonoidHom.range.{v, max u v} A (@AddCommGroup.toAddGroup.{v} A inst) (V → A)
            (@Pi.addGroup.{u, v} V (fun (a : V) => A) fun (i : V) => @AddCommGroup.toAddGroup.{v} A inst)
            (@Pi.constAddMonoidHom.{u, v} V A
              (@AddMonoid.toAddZeroClass.{v} A
                (@SubNegMonoid.toAddMonoid.{v} A
                  (@AddGroup.toSubNegMonoid.{v} A (@AddCommGroup.toAddGroup.{v} A inst)))))))
        (@SimpleGraph.Preconnected.{u} V G))
    Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration.{u, v})

noncomputable def Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.sourceBridgeFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Galois\",\"SparseCharacterSynchronization\",\"edge_difference_kernel_eq_constants_iff\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"SparseCharacterSynchronization\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `D5.S3.Factorization.Galois.SparseCharacterSynchronization.edge_difference_kernel_eq_constants_iff, part := .type, path := [], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{max (u + 1) (v + 1), max u v, 0, max u v,
      0}
  Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.arena.{u, v}
  (∀ {V : Type u} (G : SimpleGraph.{u} V) (A : Type v) [inst : AddCommGroup.{v} A] [Nontrivial.{v} A],
    Iff
      (@Eq.{max (u + 1) (v + 1)}
        (@AddSubgroup.{max u v} (V → A)
          (@Pi.addGroup.{u, v} V (fun (a : V) => A) fun (i : V) => @AddCommGroup.toAddGroup.{v} A inst))
        (@AddMonoidHom.ker.{max u v, max u v} (V → A)
          (@Pi.addGroup.{u, v} V (fun (a : V) => A) fun (i : V) => @AddCommGroup.toAddGroup.{v} A inst)
          ((@Subtype.{u + 1} (Prod.{u, u} V V) fun (e : Prod.{u, u} V V) =>
              @SimpleGraph.Adj.{u} V G (@Prod.fst.{u, u} V V e) (@Prod.snd.{u, u} V V e)) →
            A)
          (@Pi.addZeroClass.{u, v}
            (@Subtype.{u + 1} (Prod.{u, u} V V) fun (e : Prod.{u, u} V V) =>
              @SimpleGraph.Adj.{u} V G (@Prod.fst.{u, u} V V e) (@Prod.snd.{u, u} V V e))
            (fun
                (a :
                  @Subtype.{u + 1} (Prod.{u, u} V V) fun (e : Prod.{u, u} V V) =>
                    @SimpleGraph.Adj.{u} V G (@Prod.fst.{u, u} V V e) (@Prod.snd.{u, u} V V e)) =>
              A)
            fun
              (i :
                @Subtype.{u + 1} (Prod.{u, u} V V) fun (e : Prod.{u, u} V V) =>
                  @SimpleGraph.Adj.{u} V G (@Prod.fst.{u, u} V V e) (@Prod.snd.{u, u} V V e)) =>
            @AddMonoid.toAddZeroClass.{v} A
              (@SubNegMonoid.toAddMonoid.{v} A (@AddGroup.toSubNegMonoid.{v} A (@AddCommGroup.toAddGroup.{v} A inst))))
          (@D5.S3.Factorization.Galois.SparseCharacterSynchronization.edgeDifference.{u, v} V G A inst))
        (@AddMonoidHom.range.{v, max u v} A (@AddCommGroup.toAddGroup.{v} A inst) (V → A)
          (@Pi.addGroup.{u, v} V (fun (a : V) => A) fun (i : V) => @AddCommGroup.toAddGroup.{v} A inst)
          (@Pi.constAddMonoidHom.{u, v} V A
            (@AddMonoid.toAddZeroClass.{v} A
              (@SubNegMonoid.toAddMonoid.{v} A
                (@AddGroup.toSubNegMonoid.{v} A (@AddCommGroup.toAddGroup.{v} A inst)))))))
      (@SimpleGraph.Preconnected.{u} V G))
  Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration.{u, v})

noncomputable def Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.observation0.{u, v} : {V : Type u} →
  (G : SimpleGraph.{u} V) →
    (A : Type v) →
      [inst : AddCommGroup.{v} A] →
        [Nontrivial.{v} A] →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max (u + 1) (v + 1), max u v, 0,
              max u v, 0}
            Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.signature.{u, v} PUnit.unit.{1}
            (@Sigma.mk.{u + 1, max (v + 1) u} (Type u)
              (fun (V : Type u) =>
                @Sigma.{u, v + 1} (SimpleGraph.{u} V) fun (x : SimpleGraph.{u} V) =>
                  @Sigma.{v + 1, v} (Type v) fun (A : Type v) => AddCommGroup.{v} A)
              V
              (@Sigma.mk.{u, v + 1} (SimpleGraph.{u} V)
                (fun (x : SimpleGraph.{u} V) => @Sigma.{v + 1, v} (Type v) fun (A : Type v) => AddCommGroup.{v} A) G
                (@Sigma.mk.{v + 1, v} (Type v) (fun (A : Type v) => AddCommGroup.{v} A) A inst))) :=
  fun {V : Type u} (G : SimpleGraph.{u} V) (A : Type v) [inst : AddCommGroup.{v} A] [Nontrivial.{v} A] =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (u + 1) (v + 1), max u v, 0,
        max u v, 0}
    Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.signature.{u, v}
    Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.actual.{u, v} PUnit.unit.{1}
    (@Sigma.mk.{u + 1, max (v + 1) u} (Type u)
      (fun (V : Type u) =>
        @Sigma.{u, v + 1} (SimpleGraph.{u} V) fun (x : SimpleGraph.{u} V) =>
          @Sigma.{v + 1, v} (Type v) fun (A : Type v) => AddCommGroup.{v} A)
      V
      (@Sigma.mk.{u, v + 1} (SimpleGraph.{u} V)
        (fun (x : SimpleGraph.{u} V) => @Sigma.{v + 1, v} (Type v) fun (A : Type v) => AddCommGroup.{v} A) G
        (@Sigma.mk.{v + 1, v} (Type v) (fun (A : Type v) => AddCommGroup.{v} A) A inst)))
    (@D5.S3.Factorization.Galois.SparseCharacterSynchronization.edgeDifference.{u, v} V G A inst)

noncomputable def Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.observationFact0.{u, v} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Galois\",\"SparseCharacterSynchronization\",\"edge_difference_kernel_eq_constants_iff\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"SparseCharacterSynchronization\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `D5.S3.Factorization.Galois.SparseCharacterSynchronization.edge_difference_kernel_eq_constants_iff, part := .type, path := [.body, .body, .body, .body, .body, .function, .argument, .function, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.observation0, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.varyingLawInput.{u, v} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.canonicalArenaOperand.{u, v})
noncomputable def Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.varyingLaw.{u, v}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"SparseCharacterSynchronization\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"

noncomputable def Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.statementExclusion.{u, v} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"SparseCharacterSynchronization\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Galois\",\"SparseCharacterSynchronization\",\"edge_difference_kernel_eq_constants_iff\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  statementLocation := { owner := `D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `D5.S3.Factorization.Galois.SparseCharacterSynchronization.edge_difference_kernel_eq_constants_iff, part := .type, path := [], levels := [(.param `u), (.param `v)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration.{u, v}).actual (Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration.{u, v}).variation.2.choose (Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration.{u, v}).variation.1 (Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration.{u, v}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1.descriptorFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"SparseCharacterSynchronization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"SparseCharacterSynchronization\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization, declaration := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u), (.param `v)] }
  (by first | rfl | (ext <;> rfl))
