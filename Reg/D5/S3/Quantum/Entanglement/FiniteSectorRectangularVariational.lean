import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Module (finrank)
open scoped BigOperators InnerProductSpace

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational
universe u

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ k => k) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {𝕜 : Type} {E F : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {A : E →ₗ[𝕜] F} {k : ℕ} (hk : k ≤ finrank 𝕜 E)
    {u : Fin k → F} {v : Fin k → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v),
    RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) ≤ kyFanSum (R.readout ⟨()⟩ () k) A

theorem actual_law : arena.{u}.Law actual := by
  intro 𝕜 E F _ _ _ _ _ _ _ A k hk u v hu hv
  exact re_sum_inner_map_le_ky_fan_sum hk hu hv

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let E := EuclideanSpace ℝ (ULift.{u} (Fin 1))
  let v : Fin 1 → E := fun i => EuclideanSpace.basisFun (ULift.{u} (Fin 1)) ℝ ⟨i⟩
  have hv : Orthonormal ℝ v := by
    exact (EuclideanSpace.basisFun (ULift.{u} (Fin 1)) ℝ).orthonormal.comp
      (fun i : Fin 1 => ULift.up i) ULift.up_injective
  have hk : 1 ≤ finrank ℝ E := by simp [E]
  have hb := h (A := LinearMap.id (R := ℝ) (M := E)) hk hv hv
  have hinner : ∀ i : Fin 1, inner ℝ (v i) (v i) = 1 := by
    intro i
    exact (orthonormal_iff_ite.mp hv i i).trans (if_pos rfl)
  change (∑ i : Fin 1, inner ℝ (v i) (v i)) ≤ 0 at hb
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    one_smul] at hb
  exact (not_le_of_gt (by norm_num : (0 : ℝ) < 1)) hb

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  exact ⟨(), 0, 1, Nat.zero_ne_one⟩

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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{u + 2, u + 2, u, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, u, 0, 0, 0} (@_root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.re_sum_inner_map_le_ky_fan_sum.{u}) (type_of% (arena.{u})) (type_of% (arena.{u})) (type_of% (realize.{0, 0, u, 0, 0} signature.{u} (fun _ _ k => k) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Entanglement") "FiniteSectorChannelOptimality") "re_sum_inner_map_le_ky_fan_sum") "Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational/Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena.{u})⟩,
  objectArena := ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  readout := some (realize.{0, 0, u, 0, 0} signature.{u} (fun _ _ k => k) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 11, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
end Reg.D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational
