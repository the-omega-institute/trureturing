import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

open _root_.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization
universe u v w

abbrev signature : Signature where
  Params := ℕ
  State d := EuclideanSpace ℝ (Fin d)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete original law, varying only the final distance measurement. -/
def arena : Arena where
  signature := signature
  Law obs := ∀
    {S : Type u} {A : Type v} {Y : Type w} [Finite S] [Nonempty S] {d : ℕ}
    (δ : A → S → S) (y : S → Y) (c : S → EuclideanSpace ℝ (Fin d))
    (Δ ν r R : ℝ)
    (_hsep : ∀ i j, i ≠ j → Δ ≤ ‖c i - c j‖)
    (_hν : 0 ≤ ν) (_hνr : ν < r) (_hrR : r < R) (_hRΔ : R < Δ / 2),
    ∃ (T : A → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (decode : EuclideanSpace ℝ (Fin d) → S)
      (readout : EuclideanSpace ℝ (Fin d) → Y),
      (∀ a, ContDiff ℝ 1 (T a)) ∧
      (∀ a i h, ‖h - c i‖ ≤ r → T a h = c (δ a i)) ∧
      (∀ i h, ‖h - c i‖ ≤ r → decode h = i ∧ readout h = y i) ∧
      ∀ (w : List (A × EuclideanSpace ℝ (Fin d))),
        (∀ step ∈ w, ‖step.2‖ ≤ ν) →
        ∀ i h, ‖h - c i‖ ≤ r → ∀ n : ℕ,
          let pre := w.take n
          let s := symbolicRun δ i (pre.map Prod.fst)
          let x := noisyRun T h pre
          obs.readout () d (x - c s) ≤ r ∧ decode x = s ∧ readout x = y s

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  obtain ⟨T, dec, out, hsmooth, hplateau, hdecode, hrun⟩ :=
    h (S := ULift.{u} Bool) (A := ULift.{v} Unit) (Y := ULift.{w} Unit)
      (d := 1) (fun _ s => s) (fun _ => ⟨()⟩)
      (fun s => if s.down then EuclideanSpace.single 0 4 else 0)
      4 0 (1/2) 1 (by
        rintro ⟨i⟩ ⟨j⟩ hij
        cases i <;> cases j <;> simp_all)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have bad := (hrun [] (by simp) ⟨false⟩ 0 (by simp) 0).1
  change (1 : ℝ) ≤ 1/2 at bad
  norm_num at bad

theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨1, 0, EuclideanSpace.single 0 (1 : ℝ), ?_⟩
  change ‖(0 : EuclideanSpace ℝ (Fin 1))‖ ≠ ‖EuclideanSpace.single 0 (1 : ℝ)‖
  simp

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@smooth_finite_machine_realization.{u,v,w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration_1.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.smooth_finite_machine_realization.{u_1, u_2, u_3}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => ‖x‖) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "SymbolicStability") "SmoothFiniteMachineRealization") "smooth_finite_machine_realization") "Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization/Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => ‖x‖) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, definition := none, coordinates := #[5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.smooth_finite_machine_realization, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.observationFact0, `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization


noncomputable def Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"SymbolicStability\",\"SmoothFiniteMachineRealization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"SymbolicStability\",\"SmoothFiniteMachineRealization\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"SymbolicStability\",\"SmoothFiniteMachineRealization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"SymbolicStability\",\"SmoothFiniteMachineRealization\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence


noncomputable def Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.arena.{u_1, u_2, u_3}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.arena.{u_1, u_2, u_3}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.arena.{u_1, u_2, u_3}
      Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.actual)
    Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration.{u_1, u_2, u_3})

noncomputable def Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"SymbolicStability\",\"SmoothFiniteMachineRealization\",\"smooth_finite_machine_realization\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"SymbolicStability\",\"SmoothFiniteMachineRealization\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.smooth_finite_machine_realization, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.arena.{u_1, u_2, u_3}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.arena.{u_1, u_2, u_3}
    Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.actual)
  Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration.{u_1, u_2, u_3})

noncomputable def Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.observation0.{u_1, u_2, u_3} : {S : Type u_1} →
  {A : Type u_2} →
    {Y : Type u_3} →
      [Finite.{u_1 + 1} S] →
        [Nonempty.{u_1 + 1} S] →
          {d : Nat} →
            (δ : A → S → S) →
              (y : S → Y) →
                (c : S → EuclideanSpace.{0, 0} Real (Fin d)) →
                  (Δ ν r R : Real) →
                    (hsep :
                        ∀ (i j : S),
                          @Ne.{u_1 + 1} S i j →
                            @LE.le.{0} Real Real.instLE Δ
                              (@Norm.norm.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                                (@PiLp.instNorm.{0, 0}
                                  (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                    (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                          ENNReal.instAddCommMonoidWithOne))
                                      PiLp.innerProductSpace._proof_1))
                                  (Fin d) (fun (x : Fin d) => Real) (Fin.fintype d) fun (i : Fin d) => Real.norm)
                                (@HSub.hSub.{0, 0, 0} (EuclideanSpace.{0, 0} Real (Fin d))
                                  (EuclideanSpace.{0, 0} Real (Fin d)) (EuclideanSpace.{0, 0} Real (Fin d))
                                  (@instHSub.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                                    (@SubNegMonoid.toSub.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                                      (@AddGroup.toSubNegMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                                        (@AddCommGroup.toAddGroup.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                                          (@WithLp.instAddCommGroup.{0}
                                            (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                              (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                                    ENNReal.instAddCommMonoidWithOne))
                                                PiLp.innerProductSpace._proof_1))
                                            ((i : Fin d) → (fun (x : Fin d) => Real) i)
                                            (@Pi.addCommGroup.{0, 0} (Fin d) (fun (x : Fin d) => Real)
                                              fun (i : Fin d) => Real.instAddCommGroup))))))
                                  (c i) (c j)))) →
                      (hν :
                          @LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ν) →
                        (hνr : @LT.lt.{0} Real Real.instLT ν r) →
                          (hrR : @LT.lt.{0} Real Real.instLT r R) →
                            (hRΔ :
                                @LT.lt.{0} Real Real.instLT R
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Δ
                                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
                              (T : A → EuclideanSpace.{0, 0} Real (Fin d) → EuclideanSpace.{0, 0} Real (Fin d)) →
                                (decode : EuclideanSpace.{0, 0} Real (Fin d) → S) →
                                  (readout : EuclideanSpace.{0, 0} Real (Fin d) → Y) →
                                    (w : List.{u_2} (Prod.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d)))) →
                                      (∀ (step : Prod.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d))),
                                          @Membership.mem.{u_2, u_2}
                                              (Prod.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d)))
                                              (List.{u_2} (Prod.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d))))
                                              (@List.instMembership.{u_2}
                                                (Prod.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d))))
                                              w step →
                                            @LE.le.{0} Real Real.instLE
                                              (@Norm.norm.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                                                (@PiLp.instNorm.{0, 0}
                                                  (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                                    (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                                          ENNReal.instAddCommMonoidWithOne))
                                                      PiLp.innerProductSpace._proof_1))
                                                  (Fin d) (fun (x : Fin d) => Real) (Fin.fintype d) fun (i : Fin d) =>
                                                  Real.norm)
                                                (@Prod.snd.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d)) step))
                                              ν) →
                                        (i : S) →
                                          (h : EuclideanSpace.{0, 0} Real (Fin d)) →
                                            @LE.le.{0} Real Real.instLE
                                                (@Norm.norm.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                                                  (@PiLp.instNorm.{0, 0}
                                                    (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                                      (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                                            ENNReal.instAddCommMonoidWithOne))
                                                        PiLp.innerProductSpace._proof_1))
                                                    (Fin d) (fun (x : Fin d) => Real) (Fin.fintype d) fun (i : Fin d) =>
                                                    Real.norm)
                                                  (@HSub.hSub.{0, 0, 0} (EuclideanSpace.{0, 0} Real (Fin d))
                                                    (EuclideanSpace.{0, 0} Real (Fin d))
                                                    (EuclideanSpace.{0, 0} Real (Fin d))
                                                    (@instHSub.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                                                      (@SubNegMonoid.toSub.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                                                        (@AddGroup.toSubNegMonoid.{0}
                                                          (EuclideanSpace.{0, 0} Real (Fin d))
                                                          (@AddCommGroup.toAddGroup.{0}
                                                            (EuclideanSpace.{0, 0} Real (Fin d))
                                                            (@WithLp.instAddCommGroup.{0}
                                                              (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                                                (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                                                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                                                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0}
                                                                      ENNReal ENNReal.instAddCommMonoidWithOne))
                                                                  PiLp.innerProductSpace._proof_1))
                                                              ((i : Fin d) → (fun (x : Fin d) => Real) i)
                                                              (@Pi.addCommGroup.{0, 0} (Fin d) (fun (x : Fin d) => Real)
                                                                fun (i : Fin d) => Real.instAddCommGroup))))))
                                                    h (c i)))
                                                r →
                                              (n : Nat) →
                                                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0,
                                                    0, 0, 0, 0}
                                                  Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.signature
                                                  PUnit.unit.{1} d :=
  fun {S : Type u_1} {A : Type u_2} {Y : Type u_3} [Finite.{u_1 + 1} S] [Nonempty.{u_1 + 1} S] {d : Nat} (δ : A → S → S)
    (y : S → Y) (c : S → EuclideanSpace.{0, 0} Real (Fin d)) (Δ ν r R : Real)
    (hsep :
      ∀ (i j : S),
        @Ne.{u_1 + 1} S i j →
          @LE.le.{0} Real Real.instLE Δ
            (@Norm.norm.{0} (EuclideanSpace.{0, 0} Real (Fin d))
              (@PiLp.instNorm.{0, 0}
                (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    PiLp.innerProductSpace._proof_1))
                (Fin d) (fun (x : Fin d) => Real) (Fin.fintype d) fun (i : Fin d) => Real.norm)
              (@HSub.hSub.{0, 0, 0} (EuclideanSpace.{0, 0} Real (Fin d)) (EuclideanSpace.{0, 0} Real (Fin d))
                (EuclideanSpace.{0, 0} Real (Fin d))
                (@instHSub.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                  (@SubNegMonoid.toSub.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                    (@AddGroup.toSubNegMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                      (@AddCommGroup.toAddGroup.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                        (@WithLp.instAddCommGroup.{0}
                          (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                              PiLp.innerProductSpace._proof_1))
                          ((i : Fin d) → (fun (x : Fin d) => Real) i)
                          (@Pi.addCommGroup.{0, 0} (Fin d) (fun (x : Fin d) => Real) fun (i : Fin d) =>
                            Real.instAddCommGroup))))))
                (c i) (c j))))
    (hν : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ν)
    (hνr : @LT.lt.{0} Real Real.instLT ν r) (hrR : @LT.lt.{0} Real Real.instLT r R)
    (hRΔ :
      @LT.lt.{0} Real Real.instLT R
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Δ
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    (T : A → EuclideanSpace.{0, 0} Real (Fin d) → EuclideanSpace.{0, 0} Real (Fin d))
    (decode : EuclideanSpace.{0, 0} Real (Fin d) → S) (readout : EuclideanSpace.{0, 0} Real (Fin d) → Y)
    (w : List.{u_2} (Prod.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d))))
    (a :
      ∀ (step : Prod.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d))),
        @Membership.mem.{u_2, u_2} (Prod.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d)))
            (List.{u_2} (Prod.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d))))
            (@List.instMembership.{u_2} (Prod.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d)))) w step →
          @LE.le.{0} Real Real.instLE
            (@Norm.norm.{0} (EuclideanSpace.{0, 0} Real (Fin d))
              (@PiLp.instNorm.{0, 0}
                (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    PiLp.innerProductSpace._proof_1))
                (Fin d) (fun (x : Fin d) => Real) (Fin.fintype d) fun (i : Fin d) => Real.norm)
              (@Prod.snd.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d)) step))
            ν)
    (i : S) (h : EuclideanSpace.{0, 0} Real (Fin d))
    (a_1 :
      @LE.le.{0} Real Real.instLE
        (@Norm.norm.{0} (EuclideanSpace.{0, 0} Real (Fin d))
          (@PiLp.instNorm.{0, 0}
            (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                PiLp.innerProductSpace._proof_1))
            (Fin d) (fun (x : Fin d) => Real) (Fin.fintype d) fun (i : Fin d) => Real.norm)
          (@HSub.hSub.{0, 0, 0} (EuclideanSpace.{0, 0} Real (Fin d)) (EuclideanSpace.{0, 0} Real (Fin d))
            (EuclideanSpace.{0, 0} Real (Fin d))
            (@instHSub.{0} (EuclideanSpace.{0, 0} Real (Fin d))
              (@SubNegMonoid.toSub.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                (@AddGroup.toSubNegMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                  (@AddCommGroup.toAddGroup.{0} (EuclideanSpace.{0, 0} Real (Fin d))
                    (@WithLp.instAddCommGroup.{0}
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          PiLp.innerProductSpace._proof_1))
                      ((i : Fin d) → (fun (x : Fin d) => Real) i)
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun (x : Fin d) => Real) fun (i : Fin d) =>
                        Real.instAddCommGroup))))))
            h (c i)))
        r)
    (n : Nat) =>
  have pre : List.{u_2} (Prod.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d))) :=
    @List.take.{u_2} (Prod.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d))) n w;
  have s : S :=
    @D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.symbolicRun.{u_1, u_2} S A δ i
      (@List.map.{u_2, u_2} (Prod.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d))) A
        (@Prod.fst.{u_2, 0} A (EuclideanSpace.{0, 0} Real (Fin d))) pre);
  have x : EuclideanSpace.{0, 0} Real (Fin d) :=
    @D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.noisyRun.{u_2, 0} A
      (EuclideanSpace.{0, 0} Real (Fin d))
      (@AddCommMagma.toAdd.{0} (EuclideanSpace.{0, 0} Real (Fin d))
        (@AddCommSemigroup.toAddCommMagma.{0} (EuclideanSpace.{0, 0} Real (Fin d))
          (@AddCommMonoid.toAddCommSemigroup.{0} (EuclideanSpace.{0, 0} Real (Fin d))
            (@AddCommGroup.toAddCommMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin d))
              (@WithLp.instAddCommGroup.{0}
                (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    PiLp.innerProductSpace._proof_1))
                ((i : Fin d) → (fun (x : Fin d) => Real) i)
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun (x : Fin d) => Real) fun (i : Fin d) =>
                  Real.instAddCommGroup))))))
      T h pre;
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.signature
    Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.actual PUnit.unit.{1} d
    (@HSub.hSub.{0, 0, 0} (EuclideanSpace.{0, 0} Real (Fin d)) (EuclideanSpace.{0, 0} Real (Fin d))
      (EuclideanSpace.{0, 0} Real (Fin d))
      (@instHSub.{0} (EuclideanSpace.{0, 0} Real (Fin d))
        (@SubNegMonoid.toSub.{0} (EuclideanSpace.{0, 0} Real (Fin d))
          (@AddGroup.toSubNegMonoid.{0} (EuclideanSpace.{0, 0} Real (Fin d))
            (@AddCommGroup.toAddGroup.{0} (EuclideanSpace.{0, 0} Real (Fin d))
              (@WithLp.instAddCommGroup.{0}
                (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    PiLp.innerProductSpace._proof_1))
                ((i : Fin d) → (fun (x : Fin d) => Real) i)
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun (x : Fin d) => Real) fun (i : Fin d) =>
                  Real.instAddCommGroup))))))
      x (c s))

noncomputable def Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"SymbolicStability\",\"SmoothFiniteMachineRealization\",\"smooth_finite_machine_realization\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"SymbolicStability\",\"SmoothFiniteMachineRealization\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.smooth_finite_machine_realization, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .argument, .body, .argument, .body, .argument, .argument, .argument, .body, .body, .body, .body, .body, .body, .letBody, .letBody, .letBody, .function, .argument, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"SymbolicStability\",\"SmoothFiniteMachineRealization\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"SymbolicStability\",\"SmoothFiniteMachineRealization\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"SymbolicStability\",\"SmoothFiniteMachineRealization\",\"smooth_finite_machine_realization\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.smooth_finite_machine_realization, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"SymbolicStability\",\"SmoothFiniteMachineRealization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"SymbolicStability\",\"SmoothFiniteMachineRealization\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization, declaration := `Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))
