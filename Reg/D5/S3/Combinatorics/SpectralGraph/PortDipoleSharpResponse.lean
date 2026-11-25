import D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Batteries.Tactic.OpenPrivate

/-! Source-bound readouts for the voltage response and its prescribed-moment fibers. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix LeanInformationAudit
open scoped Matrix
open _root_.D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)
open private endpoint_response_mem from D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse

namespace Reg.D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse

universe u

private abbrev responseSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

private def responseActual : Realization responseSignature :=
  realize responseSignature (fun _ _ voltage => voltage / 2) (fun e => nomatch e)

private def responseRejected : Realization responseSignature :=
  realize responseSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem responseDependence : ObservationalDependence responseSignature responseActual := by
  intro role
  refine ⟨(), 0, 2, ?_⟩
  change (0 : ℝ) / 2 ≠ 2 / 2
  norm_num

private theorem unitMomentResponse : (1 : ℝ) ∈ responses 1 1 := by
  simpa using endpoint_response_mem (p := 1) (by norm_num)

private theorem liftedUnitMomentResponse :
    ∃ (n : ℕ) (L : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) ℝ)
      (hL : IsWeightedLaplacian L) (i j : ULift.{u} (Fin n)) (x : ULift.{u} (Fin n) → ℝ),
      hL.supportGraph.Connected ∧ i ≠ j ∧ L *ᵥ x = dipole i j ∧
      dipole i j ⬝ᵥ (L *ᵥ dipole i j) = 2 ∧
      (∑ k, ((L *ᵥ dipole i j) k) ^ 2) = 2 ∧ (x i - x j) / 2 = 1 := by
  obtain ⟨n, L, hL, i, j, x, hc, hij, hx, hm₁, hm₂, hdrop⟩ := unitMomentResponse
  let e : ULift.{u} (Fin n) ≃ Fin n := Equiv.ulift
  let M := L.submatrix e e
  have hM : IsWeightedLaplacian M := by
    refine ⟨Matrix.IsSymm.ext (fun a b => hL.symm.apply (e a) (e b)), ?_, ?_⟩
    · intro a
      exact (e.sum_comp (L (e a))).trans (hL.row_sum (e a))
    · intro a b hab
      exact hL.offdiag_nonpos _ _ (e.injective.ne hab)
  let graphIso : hM.supportGraph ≃g hL.supportGraph :=
    { toEquiv := e
      map_rel_iff' := by
        intro a b
        change (e a ≠ e b ∧ L (e a) (e b) < 0) ↔ (a ≠ b ∧ L (e a) (e b) < 0)
        simp }
  have hd : dipole (e.symm i) (e.symm j) = dipole i j ∘ e := by
    funext a
    simp [dipole, Pi.single_apply, Pi.sub_apply, e.eq_symm_apply]
  have mul_comp (v : Fin n → ℝ) : M *ᵥ (v ∘ e) = (L *ᵥ v) ∘ e := by
    ext a
    exact e.sum_comp (fun b => L (e a) b * v b)
  refine ⟨n, M, hM, e.symm i, e.symm j, x ∘ e, graphIso.connected_iff.mpr hc,
    e.symm.injective.ne hij, ?_, ?_, ?_, ?_⟩
  · rw [mul_comp, hx, hd]
  · rw [hd, mul_comp, comp_equiv_dotProduct_comp_equiv]
    simpa using hm₁
  · rw [hd, mul_comp]
    exact (e.sum_comp (fun k => ((L *ᵥ dipole i j) k) ^ 2)).trans (by simpa using hm₂)
  · simpa using hdrop.symm

namespace LowerBound

private abbrev arena : Arena where
  signature := responseSignature
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {L : Matrix V V ℝ} (_hL : IsWeightedLaplacian L)
    {i j : V} (_hij : i ≠ j) {x : V → ℝ} (_hx : L *ᵥ x = dipole i j)
    {p q : ℝ} (_hp : 0 < p) (_hq : q < 4 * p ^ 2)
    (_hm₁ : dipole i j ⬝ᵥ (L *ᵥ dipole i j) = 2 * p)
    (_hm₂ : (∑ k, ((L *ᵥ dipole i j) k) ^ 2) = 2 * q),
    max (1 / p) (2 * p / (4 * p ^ 2 - q)) ≤ R.readout () () (x i - x j) ∧
      (p ^ 2 < q → max (1 / p) (2 * p / (4 * p ^ 2 - q)) < (x i - x j) / 2)

private theorem rejected_law : ¬ arena.{u}.Law responseRejected := by
  intro h
  obtain ⟨n, L, hL, i, j, x, _, hij, hx, hm₁, hm₂, _⟩ := liftedUnitMomentResponse.{u}
  have assertion := (h hL hij hx (p := 1) (q := 1) (by norm_num) (by norm_num)
    (by norm_num at hm₁ ⊢; exact hm₁) (by norm_num at hm₂ ⊢; exact hm₂)).1
  change max ((1 : ℝ) / 1) (2 * 1 / (4 * 1 ^ 2 - 1)) ≤ 0 at assertion
  exact (by norm_num : ¬ ((1 : ℝ) / 1 ≤ 0)) ((le_max_left _ _).trans assertion)

def family : Registration arena.{u} (type_of% @response_lower_bound.{u}) where
  actual := responseActual
  bridge := Iff.rfl
  variation := ⟨@response_lower_bound, responseRejected, rejected_law⟩
  sensitivity := sensitivity arena.Law responseActual responseRejected rejected_law
  dependence := responseDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@response_lower_bound.{u}) (Realization responseSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse.response_lower_bound.audit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse.LowerBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize responseSignature (fun _ _ voltage => voltage / 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LowerBound

namespace CurrentSolution

private abbrev arena : Arena where
  signature := responseSignature
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {L : Matrix V V ℝ} (hL : IsWeightedLaplacian L)
    (_hc : hL.supportGraph.Connected) (i j : V),
    ∃ x : V → ℝ, L *ᵥ x = dipole i j ∧
      ∀ w : V → ℝ, L *ᵥ w = (Real.sqrt 2)⁻¹ • dipole i j →
        ((Real.sqrt 2)⁻¹ • dipole i j) ⬝ᵥ w = R.readout () () (x i - x j)

private theorem rejected_law : ¬ arena.{u}.Law responseRejected := by
  intro h
  obtain ⟨n, L, hL, i, j, x, hc, _, hx, _, _, hdrop⟩ := liftedUnitMomentResponse.{u}
  obtain ⟨_, _, hw⟩ := h hL hc i j
  let c := (Real.sqrt 2)⁻¹
  have hw' := hw (c • x) (by rw [mulVec_smul, hx])
  change (c • dipole i j) ⬝ᵥ (c • x) = 0 at hw'
  have hd : dipole i j ⬝ᵥ x = 2 := by
    simp [dipole, sub_dotProduct]
    linarith
  rw [smul_dotProduct, dotProduct_smul, hd] at hw'
  have hcpos : 0 < c := inv_pos.mpr (Real.sqrt_pos.2 (by norm_num))
  have hpositive : 0 < c * (c * 2) := mul_pos hcpos (mul_pos hcpos (by norm_num))
  exact hpositive.ne' hw'

def family : Registration arena.{u} (type_of% @exists_current_solution.{u}) where
  actual := responseActual
  bridge := Iff.rfl
  variation := ⟨@exists_current_solution, responseRejected, rejected_law⟩
  sensitivity := sensitivity arena.Law responseActual responseRejected rejected_law
  dependence := responseDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_current_solution.{u}) (Realization responseSignature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse.exists_current_solution.audit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse.CurrentSolution.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize responseSignature (fun _ _ voltage => voltage / 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CurrentSolution

private abbrev fiberSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => Set ℝ)

private def fiberActual : Realization fiberSignature :=
  realize fiberSignature (fun _ p q => responses p q) (fun e => nomatch e)

private def fiberRejected : Realization fiberSignature :=
  realize fiberSignature (fun _ _ _ => ∅) (fun e => nomatch e)

private theorem fiberDependence : ObservationalDependence fiberSignature fiberActual := by
  intro role
  refine ⟨1, 1, 2, ?_⟩
  change responses 1 1 ≠ responses 1 2
  intro he
  have hmem : (1 : ℝ) ∈ responses 1 2 := he ▸ unitMomentResponse
  have hiff := infimum_mem_responses_iff (p := 1) (q := 2)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at hiff
  exact hiff hmem

namespace Infimum

private abbrev arena : Arena where
  signature := fiberSignature
  Law R := ∀ {p q : ℝ}, 0 < p → p ^ 2 ≤ q → q < 4 * p ^ 2 →
    IsGLB (R.readout () p q) (max (1 / p) (2 * p / (4 * p ^ 2 - q)))

private theorem rejected_law : ¬ arena.Law fiberRejected := by
  intro h
  have hglb := h (p := 1) (q := 1) (by norm_num) (by norm_num) (by norm_num)
  change IsGLB (∅ : Set ℝ) _ at hglb
  have hle := hglb.2 (show (2 : ℝ) ∈ lowerBounds (∅ : Set ℝ) from fun _ hr => hr.elim)
  change (2 : ℝ) ≤ max (1 / 1) (2 * 1 / (4 * 1 ^ 2 - 1)) at hle
  norm_num [le_max_iff] at hle

def family : Registration arena (type_of% @isGLB_responses) where
  actual := fiberActual
  bridge := Iff.rfl
  variation := ⟨@isGLB_responses, fiberRejected, rejected_law⟩
  sensitivity := sensitivity arena.Law fiberActual fiberRejected rejected_law
  dependence := fiberDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@isGLB_responses) (Realization fiberSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse.isGLB_responses.audit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse.Infimum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fiberSignature (fun _ p q => responses p q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Infimum

namespace Attainment

private abbrev arena : Arena where
  signature := fiberSignature
  Law R := ∀ {p q : ℝ}, 0 < p → p ^ 2 ≤ q → q < 4 * p ^ 2 →
    (max (1 / p) (2 * p / (4 * p ^ 2 - q)) ∈ R.readout () p q ↔ q = p ^ 2)

private theorem rejected_law : ¬ arena.Law fiberRejected := by
  intro h
  have hmem := (h (p := 1) (q := 1) (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
  exact hmem.elim

def family : Registration arena (type_of% @infimum_mem_responses_iff) where
  actual := fiberActual
  bridge := Iff.rfl
  variation := ⟨@infimum_mem_responses_iff, fiberRejected, rejected_law⟩
  sensitivity := sensitivity arena.Law fiberActual fiberRejected rejected_law
  dependence := fiberDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@infimum_mem_responses_iff) (Realization fiberSignature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse.infimum_mem_responses_iff.audit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse.Attainment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fiberSignature (fun _ p q => responses p q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Attainment

end Reg.D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse
