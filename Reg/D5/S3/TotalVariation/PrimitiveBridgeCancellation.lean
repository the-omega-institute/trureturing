import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.TotalVariation.PrimitiveBridgeCancellation
import Reg.Support.DependentFamily

open _root_.D5.S3.TotalVariation.PrimitiveBridgeCancellation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
open Quiver Quiver.Path

noncomputable section
namespace Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation
universe u

abbrev signature : Signature where
  Params := Σ q : ℕ, Finset (Fin q → ℤ)
  State p := Fin p.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Energy of the very same finite generating set selected by the source existential. -/
def actual : Realization signature :=
  realize signature (fun _ p x => energy p.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Only the energy occurrence in the cancellation inequality is selected. All other
clauses retain the common bridge length, generators, coefficient and actual paths. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hstoch : P ∈ Matrix.rowStochastic ℝ V)
    (hprim : Matrix.IsPrimitive P) {q : ℕ} (g : V → V → (Fin q → ℤ))
    (iStar jStar : V),
    letI : Quiver V := Matrix.toQuiver P
    ∃ L : ℕ, 0 < L ∧ ∃ F : Finset (Fin q → ℤ), ∃ c : ℝ, 0 < c ∧
      Submodule.span ℤ (F : Set (Fin q → ℤ)) = lattice P g ∧
      (∀ lam ∈ F, ∃ a b : Gamma P L iStar jStar,
        a.val.addWeightOfEPs g - b.val.addWeightOfEPs g = lam ∧
        c ≤ a.val.weightOfEPs (fun i j => P i j) * b.val.weightOfEPs (fun i j => P i j)) ∧
      0 < (P ^ L) iStar jStar ∧
      (∀ x : Fin q → ℝ, c * r.readout () ⟨q, F⟩ x ≤
        ((P ^ L) iStar jStar)^2 - ‖(twisted P g x ^ L) iStar jStar‖^2) ∧
      (∀ x : Fin q → ℝ, energy F x = 0 ↔ x ∈ annihilator P g)

/-- A one-state primitive stochastic chain with zero charges has zero deficit at
all lengths, so no positive coefficient can support the constant-one intervention. -/
theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} Unit
  let P : Matrix V V ℝ := 1
  have hp : Matrix.IsPrimitive P := by
    constructor
    · intro i j
      simp [P, Matrix.one_apply, Subsingleton.elim i j]
    · exact ⟨1, by omega, by intro i j; simp [P, Matrix.one_apply, Subsingleton.elim i j]⟩
  obtain ⟨L, hL, F, c, hc, hspan, hpaths, hpos, hcancel, hann⟩ :=
    h P (Matrix.rowStochastic ℝ V).one_mem hp (q := 1) (fun _ _ _ => 0) ⟨()⟩ ⟨()⟩
  have ht : twisted P (fun _ _ => fun _ : Fin 1 => (0 : ℤ)) (fun _ => 0) =
      (1 : Matrix V V ℂ) := by
    ext i j
    simp [twisted, dot, P, Matrix.one_apply, Subsingleton.elim i j]
  have hh := hcancel (fun _ => 0)
  simp only [ht, P, one_pow, Matrix.one_apply_eq, norm_one,
    one_pow, sub_self] at hh
  have : c ≤ 0 := by simpa [rejected, realize] using hh
  exact (not_le_of_gt hc) this

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, {fun _ : Fin 1 => (1 : ℤ)}⟩, (fun _ => 0), (fun _ => Real.pi), ?_⟩
  norm_num [actual, realize, energy, dot, Fin.sum_univ_one]

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.TotalVariation.PrimitiveBridgeCancellation.primitive_bridge_cancellation.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.TotalVariation.PrimitiveBridgeCancellation.primitive_bridge_cancellation.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p x => energy p.2 x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "TotalVariation") "PrimitiveBridgeCancellation") "primitive_bridge_cancellation") "Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation/Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p x => energy p.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.TotalVariation.PrimitiveBridgeCancellation, definition := none, coordinates := #[7, 12], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg", "body", "fn", "arg", "arg"], stateBinder := 14, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `D5.S3.TotalVariation.PrimitiveBridgeCancellation.primitive_bridge_cancellation, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.canonicalArenaFact, `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.sourceBridgeFact, `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.observationFact0, `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation


noncomputable def Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.arena.{u_1}
noncomputable def Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"PrimitiveBridgeCancellation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"PrimitiveBridgeCancellation\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.arena.{u_1}
noncomputable def Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"PrimitiveBridgeCancellation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"PrimitiveBridgeCancellation\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.arena.{u_1}
      Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.actual)
    Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration.{u_1})

noncomputable def Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"TotalVariation\",\"PrimitiveBridgeCancellation\",\"primitive_bridge_cancellation\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"PrimitiveBridgeCancellation\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `D5.S3.TotalVariation.PrimitiveBridgeCancellation.primitive_bridge_cancellation, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.arena.{u_1}
    Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.actual)
  Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration.{u_1})

noncomputable def Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.observation0.{u_1} : {V : Type u_1} →
  [inst : Fintype.{u_1} V] →
    [inst_1 : DecidableEq.{u_1 + 1} V] →
      [Nonempty.{u_1 + 1} V] →
        (P : Matrix.{u_1, u_1, 0} V V Real) →
          (hstoch :
              @Membership.mem.{u_1, u_1} (Matrix.{u_1, u_1, 0} V V Real)
                (@Submonoid.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
                  (@MulZeroOneClass.toMulOneClass.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
                    (@instMulZeroOneClassOfSemiring.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
                      (@Matrix.semiring.{0, u_1} V Real Real.semiring inst inst_1))))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Submonoid.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
                    (@MulZeroOneClass.toMulOneClass.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
                      (@instMulZeroOneClassOfSemiring.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
                        (@Matrix.semiring.{0, u_1} V Real Real.semiring inst inst_1))))
                  (Matrix.{u_1, u_1, 0} V V Real)
                  (@Submonoid.instSetLike.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
                    (@MulZeroOneClass.toMulOneClass.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
                      (@instMulZeroOneClassOfSemiring.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
                        (@Matrix.semiring.{0, u_1} V Real Real.semiring inst inst_1)))))
                (@Matrix.rowStochastic.{0, u_1} Real V inst inst_1 Real.semiring Real.partialOrder
                  Real.instIsOrderedRing)
                P) →
            (hprim : @Matrix.IsPrimitive.{u_1, 0} V Real Real.instRing Real.linearOrder inst inst_1 P) →
              {q : Nat} →
                (g : V → V → Fin q → Int) →
                  (iStar jStar : V) →
                    (L : Nat) →
                      (F : Finset.{0} (Fin q → Int)) →
                        (c : Real) →
                          (x : Fin q → Real) →
                            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                              Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.signature PUnit.unit.{1}
                              (@Sigma.mk.{0, 0} Nat (fun (q : Nat) => Finset.{0} (Fin q → Int)) q F) :=
  fun {V : Type u_1} [Fintype.{u_1} V] [DecidableEq.{u_1 + 1} V] [Nonempty.{u_1 + 1} V]
    (P : Matrix.{u_1, u_1, 0} V V Real)
    (hstoch :
      @Membership.mem.{u_1, u_1} (Matrix.{u_1, u_1, 0} V V Real)
        (@Submonoid.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
          (@MulZeroOneClass.toMulOneClass.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
            (@instMulZeroOneClassOfSemiring.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
              (@Matrix.semiring.{0, u_1} V Real Real.semiring inst inst_1))))
        (@SetLike.instMembership.{u_1, u_1}
          (@Submonoid.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
            (@MulZeroOneClass.toMulOneClass.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
              (@instMulZeroOneClassOfSemiring.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
                (@Matrix.semiring.{0, u_1} V Real Real.semiring inst inst_1))))
          (Matrix.{u_1, u_1, 0} V V Real)
          (@Submonoid.instSetLike.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
            (@MulZeroOneClass.toMulOneClass.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
              (@instMulZeroOneClassOfSemiring.{u_1} (Matrix.{u_1, u_1, 0} V V Real)
                (@Matrix.semiring.{0, u_1} V Real Real.semiring inst inst_1)))))
        (@Matrix.rowStochastic.{0, u_1} Real V inst inst_1 Real.semiring Real.partialOrder Real.instIsOrderedRing) P)
    (hprim : @Matrix.IsPrimitive.{u_1, 0} V Real Real.instRing Real.linearOrder inst inst_1 P) {q : Nat}
    (g : V → V → Fin q → Int) (iStar jStar : V) (L : Nat) (F : Finset.{0} (Fin q → Int)) (c : Real)
    (x : Fin q → Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.signature
    Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (q : Nat) => Finset.{0} (Fin q → Int)) q F) x

noncomputable def Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"TotalVariation\",\"PrimitiveBridgeCancellation\",\"primitive_bridge_cancellation\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"PrimitiveBridgeCancellation\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `D5.S3.TotalVariation.PrimitiveBridgeCancellation.primitive_bridge_cancellation, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .argument, .argument, .body, .argument, .body, .argument, .argument, .argument, .argument, .function, .argument, .body, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"PrimitiveBridgeCancellation\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"PrimitiveBridgeCancellation\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"TotalVariation\",\"PrimitiveBridgeCancellation\",\"primitive_bridge_cancellation\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `D5.S3.TotalVariation.PrimitiveBridgeCancellation.primitive_bridge_cancellation, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration.{u_1}).actual (Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration.{u_1}).variation.2.choose (Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration.{u_1}).variation.1 (Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"PrimitiveBridgeCancellation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"PrimitiveBridgeCancellation\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation, declaration := `Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
