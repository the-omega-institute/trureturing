import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.FiniteSectorPassivePair
import Reg.Support.DependentFamily
import Reg.Support.FiniteSectorSingleton

open _root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open _root_.D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker InnerProductSpace

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair
universe u

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℂ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output := fun _ _ => ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => star x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Sector : Type u} {EX : Type u} {EY : Type u} [Fintype Sector] [DecidableEq Sector]
    [Fintype EX] [DecidableEq EX] [Fintype EY] [DecidableEq EY]
    {J : ℕ} (M : Model Sector J)
    (VX : Matrix (EX × TargetLocal M.d) (SourceLocal (Coord := Fin J) M.d) ℂ)
    (VY : Matrix (EY × TargetLocal M.d) (SourceLocal (Coord := Fin J) M.d) ℂ)
    (hVX : VXᴴ * VX = 1) (hVY : VYᴴ * VY = 1),
    let C : Sector → Matrix (SourceLocal (Coord := Fin J) M.d)
        (SourceLocal (Coord := Fin J) M.d) ℂ := fun s => Matrix.diagonal fun u =>
      if u.1 = s then (Real.sqrt (M.spectrum s u.2.2 / (M.d s : ℝ)) : ℂ) else 0
    let Q := fun s => VX * C s * VY.transpose
    let Z : Sector → Matrix EX EY ℂ := fun s ex ey =>
      (((Real.sqrt (M.d s : ℝ))⁻¹ : ℝ) : ℂ) *
        ∑ a : Fin (M.d s), Q s (ex, ⟨s, a⟩) (ey, ⟨s, a⟩)
    ∀ s t, (∑ ex, ∑ ey, R.readout ⟨()⟩ () (Z s ex ey) * Z t ex ey).re ≤ kernel M s t

theorem actual_law : arena.{u}.Law actual := by
  intro Sector EX EY _ _ _ _ _ _ J M VX VY hVX hVY
  exact sector_pair M VX VY hVX hVY

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let M := Reg.Support.FiniteSectorSingleton.model (ULift.{u} Unit)
  let V : Matrix (ULift.{u} Unit × TargetLocal M.d)
      (SourceLocal (Coord := Fin 1) M.d) ℂ := fun _ _ => 1
  have index_eq : ∀ i j : SourceLocal (Coord := Fin 1) M.d, i = j := by
    change ∀ i j : (Σ _ : ULift.{u} Unit, Fin 1 × Fin 1), i = j
    intro ⟨s, a, b⟩ ⟨t, c, d⟩
    have hs : s = t := Subsingleton.elim _ _
    subst t
    have ha : a = c := Subsingleton.elim _ _
    have hb : b = d := Subsingleton.elim _ _
    subst c
    subst d
    rfl
  have hV : Vᴴ * V = 1 := by
    ext i j
    change (∑ _ : ULift.{u} Unit × TargetLocal M.d, star (1 : ℂ) * 1) =
      (1 : Matrix (SourceLocal (Coord := Fin 1) M.d) _ ℂ) i j
    rw [Matrix.one_apply, if_pos (index_eq i j)]
    simp only [star_one, mul_one]
    simp [M, Fintype.sum_sigma, Fintype.sum_prod_type]
  have hb := h M V V hV hV (⟨()⟩ : ULift.{u} Unit) (⟨()⟩ : ULift.{u} Unit)
  dsimp only [rejected, realize] at hb
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at hb
  norm_num [V, M, kernel, Matrix.diagonal_apply, Fintype.sum_sigma,
    Fintype.sum_prod_type] at hb


theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim (ULift.{u} Unit) _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

#print axioms registration

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.sector_pair.{u}) (type_of% (realize.{0, 0, u, 0, 0} signature.{u} (fun _ _ x => star.{0} x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Entanglement") "FiniteSectorChannelOptimality") "sector_pair") "Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair/Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u})⟩,
  objectArena := .source ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, u, 0, 0} signature.{u} (fun _ _ x => star.{0} x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "body", "arg", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.sector_pair, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.observationFact0, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.anchorEnumeration }



end Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair


noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.arena.{u}
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPassivePair\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPassivePair\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.arena.{u}
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPassivePair\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPassivePair\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.arena.{u}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, u, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.arena.{u}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
      Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.arena.{u}
      Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.actual.{u})
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration.{u})

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"sector_pair\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPassivePair\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.sector_pair, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, u, 0, 0}
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.arena.{u}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.arena.{u}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.actual.{u})
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration.{u})

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.roleEnumeration.{u} : LeanInformationAudit.Contract.FiniteEnumeration (ULift.{u, 0} Unit) where
  values := [@ULift.up.{u, 0} Unit Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.observation0.{u} : {Sector EX EY : Type u} →
  [inst : Fintype.{u} Sector] →
    [inst_1 : DecidableEq.{u + 1} Sector] →
      [inst_2 : Fintype.{u} EX] →
        [DecidableEq.{u + 1} EX] →
          [inst_4 : Fintype.{u} EY] →
            [DecidableEq.{u + 1} EY] →
              {J : Nat} →
                (M : @D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.{u} Sector inst J) →
                  (VX :
                      Matrix.{u, u, 0}
                        (Prod.{u, u} EX
                          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
                        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
                        Complex) →
                    (VY :
                        Matrix.{u, u, 0}
                          (Prod.{u, u} EY
                            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
                          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
                          Complex) →
                      (hVX :
                          @Eq.{u + 1}
                            (Matrix.{u, u, 0}
                              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
                              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
                              Complex)
                            (@HMul.hMul.{u, u, u}
                              (Matrix.{u, u, 0}
                                (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                    M))
                                (Prod.{u, u} EX
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M)))
                                Complex)
                              (Matrix.{u, u, 0}
                                (Prod.{u, u} EX
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M)))
                                (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                    M))
                                Complex)
                              (Matrix.{u, u, 0}
                                (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                    M))
                                (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                    M))
                                Complex)
                              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u, u, u}
                                (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                    M))
                                (Prod.{u, u} EX
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M)))
                                (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                    M))
                                Complex
                                (@instFintypeProd.{u, u} EX
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M))
                                  inst_2
                                  (@Sigma.instFintype.{u, 0} Sector
                                    (fun (s : Sector) =>
                                      Fin
                                        (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector
                                          inst J M s))
                                    (fun (i : Sector) =>
                                      Fin.fintype
                                        (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector
                                          inst J M i))
                                    inst))
                                Complex.instMul Complex.instAddCommMonoid)
                              (@Matrix.conjTranspose.{0, u, u}
                                (Prod.{u, u} EX
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M)))
                                (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                    M))
                                Complex
                                (@InvolutiveStar.toStar.{0} Complex
                                  (@StarAddMonoid.toInvolutiveStar.{0} Complex
                                    (@AddCommMonoid.toAddMonoid.{0} Complex
                                      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                              Complex.instNonUnitalCommRing)))))
                                    (@StarRing.toStarAddMonoid.{0} Complex
                                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                            Complex.instNonUnitalCommRing)))
                                      Complex.instStarRing)))
                                VX)
                              VX)
                            (@OfNat.ofNat.{u}
                              (Matrix.{u, u, 0}
                                (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                    M))
                                (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                    M))
                                Complex)
                              (nat_lit 1)
                              (@One.toOfNat1.{u}
                                (Matrix.{u, u, 0}
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M))
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M))
                                  Complex)
                                (@Matrix.one.{0, u}
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M))
                                  Complex
                                  (fun
                                      (a b :
                                        @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector
                                          (Fin J)
                                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector
                                            inst J M)) =>
                                    @Sigma.instDecidableEqSigma.{u, 0} Sector
                                      (fun (s : Sector) =>
                                        Prod.{0, 0}
                                          (Fin
                                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u}
                                              Sector inst J M s))
                                          (Fin J))
                                      inst_1
                                      (fun (a : Sector)
                                          (a_1 b :
                                            Prod.{0, 0}
                                              (Fin
                                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u}
                                                  Sector inst J M a))
                                              (Fin J)) =>
                                        @instDecidableEqProd.{0, 0}
                                          (Fin
                                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u}
                                              Sector inst J M a))
                                          (Fin J)
                                          ((fun (a : Sector) =>
                                              instDecidableEqFin
                                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u}
                                                  Sector inst J M a))
                                            a)
                                          (instDecidableEqFin J) a_1 b)
                                      a b)
                                  Complex.instZero Complex.instOne)))) →
                        (hVY :
                            @Eq.{u + 1}
                              (Matrix.{u, u, 0}
                                (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                    M))
                                (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                    M))
                                Complex)
                              (@HMul.hMul.{u, u, u}
                                (Matrix.{u, u, 0}
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M))
                                  (Prod.{u, u} EY
                                    (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                        J M)))
                                  Complex)
                                (Matrix.{u, u, 0}
                                  (Prod.{u, u} EY
                                    (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                        J M)))
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M))
                                  Complex)
                                (Matrix.{u, u, 0}
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M))
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M))
                                  Complex)
                                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u, u, u}
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M))
                                  (Prod.{u, u} EY
                                    (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                        J M)))
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M))
                                  Complex
                                  (@instFintypeProd.{u, u} EY
                                    (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                        J M))
                                    inst_4
                                    (@Sigma.instFintype.{u, 0} Sector
                                      (fun (s : Sector) =>
                                        Fin
                                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector
                                            inst J M s))
                                      (fun (i : Sector) =>
                                        Fin.fintype
                                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector
                                            inst J M i))
                                      inst))
                                  Complex.instMul Complex.instAddCommMonoid)
                                (@Matrix.conjTranspose.{0, u, u}
                                  (Prod.{u, u} EY
                                    (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                        J M)))
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M))
                                  Complex
                                  (@InvolutiveStar.toStar.{0} Complex
                                    (@StarAddMonoid.toInvolutiveStar.{0} Complex
                                      (@AddCommMonoid.toAddMonoid.{0} Complex
                                        (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                                          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                                Complex.instNonUnitalCommRing)))))
                                      (@StarRing.toStarAddMonoid.{0} Complex
                                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                              Complex.instNonUnitalCommRing)))
                                        Complex.instStarRing)))
                                  VY)
                                VY)
                              (@OfNat.ofNat.{u}
                                (Matrix.{u, u, 0}
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M))
                                  (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J
                                      M))
                                  Complex)
                                (nat_lit 1)
                                (@One.toOfNat1.{u}
                                  (Matrix.{u, u, 0}
                                    (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                        J M))
                                    (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                        J M))
                                    Complex)
                                  (@Matrix.one.{0, u}
                                    (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                        J M))
                                    Complex
                                    (fun
                                        (a b :
                                          @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector
                                            (Fin J)
                                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u}
                                              Sector inst J M)) =>
                                      @Sigma.instDecidableEqSigma.{u, 0} Sector
                                        (fun (s : Sector) =>
                                          Prod.{0, 0}
                                            (Fin
                                              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u}
                                                Sector inst J M s))
                                            (Fin J))
                                        inst_1
                                        (fun (a : Sector)
                                            (a_1 b :
                                              Prod.{0, 0}
                                                (Fin
                                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u}
                                                    Sector inst J M a))
                                                (Fin J)) =>
                                          @instDecidableEqProd.{0, 0}
                                            (Fin
                                              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u}
                                                Sector inst J M a))
                                            (Fin J)
                                            ((fun (a : Sector) =>
                                                instDecidableEqFin
                                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u}
                                                    Sector inst J M a))
                                              a)
                                            (instDecidableEqFin J) a_1 b)
                                        a b)
                                    Complex.instZero Complex.instOne)))) →
                          (s t : Sector) →
                            (ex : EX) →
                              (ey : EY) →
                                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, u, 0, 0}
                                  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.signature.{u}
                                  (@ULift.up.{u, 0} Unit Unit.unit) PUnit.unit.{1} :=
  fun {Sector EX EY : Type u} [inst : Fintype.{u} Sector] [inst_1 : DecidableEq.{u + 1} Sector] [Fintype.{u} EX]
    [DecidableEq.{u + 1} EX] [Fintype.{u} EY] [DecidableEq.{u + 1} EY] {J : Nat}
    (M : @D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.{u} Sector inst J)
    (VX :
      Matrix.{u, u, 0}
        (Prod.{u, u} EX
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
        Complex)
    (VY :
      Matrix.{u, u, 0}
        (Prod.{u, u} EY
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
        Complex)
    (hVX :
      @Eq.{u + 1}
        (Matrix.{u, u, 0}
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
          Complex)
        (@HMul.hMul.{u, u, u}
          (Matrix.{u, u, 0}
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            (Prod.{u, u} EX
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
            Complex)
          (Matrix.{u, u, 0}
            (Prod.{u, u} EX
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            Complex)
          (Matrix.{u, u, 0}
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u, u, u}
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            (Prod.{u, u} EX
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            Complex
            (@instFintypeProd.{u, u} EX
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
              inst_2
              (@Sigma.instFintype.{u, 0} Sector
                (fun (s : Sector) =>
                  Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s))
                (fun (i : Sector) =>
                  Fin.fintype (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M i))
                inst))
            Complex.instMul Complex.instAddCommMonoid)
          (@Matrix.conjTranspose.{0, u, u}
            (Prod.{u, u} EX
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            Complex
            (@InvolutiveStar.toStar.{0} Complex
              (@StarAddMonoid.toInvolutiveStar.{0} Complex
                (@AddCommMonoid.toAddMonoid.{0} Complex
                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
                (@StarRing.toStarAddMonoid.{0} Complex
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                  Complex.instStarRing)))
            VX)
          VX)
        (@OfNat.ofNat.{u}
          (Matrix.{u, u, 0}
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            Complex)
          (nat_lit 1)
          (@One.toOfNat1.{u}
            (Matrix.{u, u, 0}
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
              Complex)
            (@Matrix.one.{0, u}
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
              Complex
              (fun
                  (a b :
                    @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)) =>
                @Sigma.instDecidableEqSigma.{u, 0} Sector
                  (fun (s : Sector) =>
                    Prod.{0, 0}
                      (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s))
                      (Fin J))
                  inst_1
                  (fun (a : Sector)
                      (a_1 b :
                        Prod.{0, 0}
                          (Fin
                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M a))
                          (Fin J)) =>
                    @instDecidableEqProd.{0, 0}
                      (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M a))
                      (Fin J)
                      ((fun (a : Sector) =>
                          instDecidableEqFin
                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M a))
                        a)
                      (instDecidableEqFin J) a_1 b)
                  a b)
              Complex.instZero Complex.instOne))))
    (hVY :
      @Eq.{u + 1}
        (Matrix.{u, u, 0}
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
          Complex)
        (@HMul.hMul.{u, u, u}
          (Matrix.{u, u, 0}
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            (Prod.{u, u} EY
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
            Complex)
          (Matrix.{u, u, 0}
            (Prod.{u, u} EY
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            Complex)
          (Matrix.{u, u, 0}
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u, u, u}
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            (Prod.{u, u} EY
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            Complex
            (@instFintypeProd.{u, u} EY
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
              inst_4
              (@Sigma.instFintype.{u, 0} Sector
                (fun (s : Sector) =>
                  Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s))
                (fun (i : Sector) =>
                  Fin.fintype (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M i))
                inst))
            Complex.instMul Complex.instAddCommMonoid)
          (@Matrix.conjTranspose.{0, u, u}
            (Prod.{u, u} EY
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            Complex
            (@InvolutiveStar.toStar.{0} Complex
              (@StarAddMonoid.toInvolutiveStar.{0} Complex
                (@AddCommMonoid.toAddMonoid.{0} Complex
                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
                (@StarRing.toStarAddMonoid.{0} Complex
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                  Complex.instStarRing)))
            VY)
          VY)
        (@OfNat.ofNat.{u}
          (Matrix.{u, u, 0}
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            Complex)
          (nat_lit 1)
          (@One.toOfNat1.{u}
            (Matrix.{u, u, 0}
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
              Complex)
            (@Matrix.one.{0, u}
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
              Complex
              (fun
                  (a b :
                    @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)) =>
                @Sigma.instDecidableEqSigma.{u, 0} Sector
                  (fun (s : Sector) =>
                    Prod.{0, 0}
                      (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s))
                      (Fin J))
                  inst_1
                  (fun (a : Sector)
                      (a_1 b :
                        Prod.{0, 0}
                          (Fin
                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M a))
                          (Fin J)) =>
                    @instDecidableEqProd.{0, 0}
                      (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M a))
                      (Fin J)
                      ((fun (a : Sector) =>
                          instDecidableEqFin
                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M a))
                        a)
                      (instDecidableEqFin J) a_1 b)
                  a b)
              Complex.instZero Complex.instOne)))) =>
  have C :
    Sector →
      Matrix.{u, u, 0}
        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
        Complex :=
    fun (s : Sector) =>
    @Matrix.diagonal.{0, u}
      (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
        (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
      Complex
      (fun
          (a b :
            @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)) =>
        @Sigma.instDecidableEqSigma.{u, 0} Sector
          (fun (s : Sector) =>
            Prod.{0, 0} (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s))
              (Fin J))
          inst_1
          (fun (a : Sector)
              (a_1 b :
                Prod.{0, 0}
                  (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M a))
                  (Fin J)) =>
            @instDecidableEqProd.{0, 0}
              (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M a)) (Fin J)
              ((fun (a : Sector) =>
                  instDecidableEqFin
                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M a))
                a)
              (instDecidableEqFin J) a_1 b)
          a b)
      Complex.instZero
      fun
        (u :
          @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)) =>
      @ite.{1} Complex
        (@Eq.{u + 1} Sector
          (@Sigma.fst.{u, 0} Sector
            (fun (s : Sector) =>
              Prod.{0, 0}
                (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s)) (Fin J))
            u)
          s)
        (inst_1
          (@Sigma.fst.{u, 0} Sector
            (fun (s : Sector) =>
              Prod.{0, 0}
                (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s)) (Fin J))
            u)
          s)
        (Complex.ofReal
          (Real.sqrt
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.spectrum.{u} Sector inst J M s
                (@Prod.snd.{0, 0}
                  (Fin
                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M
                      (@Sigma.fst.{u, 0} Sector
                        (fun (s : Sector) =>
                          Prod.{0, 0}
                            (Fin
                              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s))
                            (Fin J))
                        u)))
                  (Fin J)
                  (@Sigma.snd.{u, 0} Sector
                    (fun (s : Sector) =>
                      Prod.{0, 0}
                        (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s))
                        (Fin J))
                    u)))
              (@Nat.cast.{0} Real Real.instNatCast
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s)))))
        (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero));
  have Q :
    (s : Sector) →
      Matrix.{u, u, 0}
        (Prod.{u, u} EX
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
        (Prod.{u, u} EY
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
        Complex :=
    fun (s : Sector) =>
    @HMul.hMul.{u, u, u}
      (Matrix.{u, u, 0}
        (Prod.{u, u} EX
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
        Complex)
      (Matrix.{u, u, 0}
        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
        (Prod.{u, u} EY
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
        Complex)
      (Matrix.{u, u, 0}
        (Prod.{u, u} EX
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
        (Prod.{u, u} EY
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
        Complex)
      (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u, u, u}
        (Prod.{u, u} EX
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
        (Prod.{u, u} EY
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
        Complex
        (@Sigma.instFintype.{u, 0} Sector
          (fun (s : Sector) =>
            Prod.{0, 0} (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s))
              (Fin J))
          (fun (i : Sector) =>
            @instFintypeProd.{0, 0}
              (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M i)) (Fin J)
              (Fin.fintype (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M i))
              (Fin.fintype J))
          inst)
        Complex.instMul Complex.instAddCommMonoid)
      (@HMul.hMul.{u, u, u}
        (Matrix.{u, u, 0}
          (Prod.{u, u} EX
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
          Complex)
        (Matrix.{u, u, 0}
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
          Complex)
        (Matrix.{u, u, 0}
          (Prod.{u, u} EX
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
          Complex)
        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u, u, u}
          (Prod.{u, u} EX
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
          Complex
          (@Sigma.instFintype.{u, 0} Sector
            (fun (s : Sector) =>
              Prod.{0, 0}
                (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s)) (Fin J))
            (fun (i : Sector) =>
              @instFintypeProd.{0, 0}
                (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M i)) (Fin J)
                (Fin.fintype (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M i))
                (Fin.fintype J))
            inst)
          Complex.instMul Complex.instAddCommMonoid)
        VX (C s))
      (@Matrix.transpose.{0, u, u}
        (Prod.{u, u} EY
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M)))
        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin J)
          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
        Complex VY);
  have Z : Sector → Matrix.{u, u, 0} EX EY Complex := fun (s : Sector) (ex : EX) (ey : EY) =>
    @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
      (Complex.ofReal
        (@Inv.inv.{0} Real Real.instInv
          (Real.sqrt
            (@Nat.cast.{0} Real Real.instNatCast
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s)))))
      (@Finset.sum.{0, 0}
        (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s)) Complex
        Complex.instAddCommMonoid
        (@Finset.univ.{0}
          (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s))
          (Fin.fintype (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s)))
        fun (a : Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s)) =>
        Q s
          (@Prod.mk.{u, u} EX
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            ex
            (@Sigma.mk.{u, 0} Sector
              (fun (s : Sector) =>
                Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s))
              s a))
          (@Prod.mk.{u, u} EY
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M))
            ey
            (@Sigma.mk.{u, 0} Sector
              (fun (s : Sector) =>
                Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst J M s))
              s a)));
  fun (s t : Sector) (ex : EX) (ey : EY) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, u, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.signature.{u}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.actual.{u} (@ULift.up.{u, 0} Unit Unit.unit) PUnit.unit.{1}
    (Z s ex ey)

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"sector_pair\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"body\",\"body\",\"function\",\"argument\",\"argument\",\"argument\",\"body\",\"argument\",\"body\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPassivePair\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.sector_pair, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .letBody, .letBody, .letBody, .body, .body, .function, .argument, .argument, .argument, .body, .argument, .body, .function, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPassivePair\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPassivePair\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"sector_pair\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.sector_pair, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration.{u}).actual (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration.{u}).variation.2.choose (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration.{u}).variation.1 (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1.descriptorFact.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPassivePair\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPassivePair\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))
