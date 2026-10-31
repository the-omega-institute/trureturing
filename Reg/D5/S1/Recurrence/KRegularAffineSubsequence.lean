import D5.S1.Recurrence.KRegularAffineSubsequence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-!
# Source-family audits for affine subsequences

The observed integer value is s(an+b), with the complete infinite sequence,
step, and offset retained as parameters. The two laws replace only that
sampled sequence in the corresponding original theorem. Constant-one output
refutes uniform transport of the zero source. The period-doubling
prefix-palindromic-length sequence refutes unrestricted output substitution
in regularity closure, by the existing infinite rational kernel-rank theorem.
-/

noncomputable section

namespace Reg.D5.S1.Recurrence.KRegularAffineSubsequence

open _root_.D5.S1.Recurrence.KRegularAffineSubsequence
open _root_.D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions (kKernel IsKRegular)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev Params := Σ _ : ℕ, Σ _ : ℕ, (ℕ → ℤ)

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Params (fun _ => ℕ) (fun _ => ℤ)

abbrev actual : Realization signature :=
  realize signature (fun _ p n => p.2.2 (p.1 * n + p.2.1)) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0, fun n : ℕ => (n : ℤ)⟩, 0, 1, ?_⟩
  change (0 : ℤ) ≠ 1
  decide

namespace Transport

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k a b : ℕ) (s : ℕ → ℤ) (_hk : 2 ≤ k) (_ha : 1 ≤ a)
    (G : Finset (ℕ → ℤ))
    (_hG : Submodule.span ℤ (G : Set (ℕ → ℤ)) = Submodule.span ℤ (kKernel k s)),
    Submodule.span ℤ (kKernel k (R.readout () ⟨a, b, s⟩)) ≤
      Submodule.span ℤ {f | ∃ g ∈ G, ∃ c : ℕ, c < a + b ∧ f = fun n => g (a * n + c)}

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℤ)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : Submodule.span ℤ (kKernel 2 (fun _ => (0 : ℤ))) = ⊥ := by
    apply le_antisymm _ bot_le
    apply Submodule.span_le.mpr
    rintro f ⟨e, r, hr, rfl⟩
    exact Submodule.zero_mem _
  have hG : Submodule.span ℤ ((∅ : Finset (ℕ → ℤ)) : Set (ℕ → ℤ)) =
      Submodule.span ℤ (kKernel 2 (fun _ => (0 : ℤ))) := by simp [hzero]
  have hh := h 2 1 0 (fun _ => 0) (by decide) (by decide) ∅ hG
  have hm : (fun _ : ℕ => (1 : ℤ)) ∈
      Submodule.span ℤ (kKernel 2 (rejected.readout () ⟨1, 0, fun _ => 0⟩)) :=
    Submodule.subset_span ⟨0, 0, by decide, rfl⟩
  have heq : (fun _ : ℕ => (1 : ℤ)) = 0 := by simpa using hh hm
  have hz := congrFun heq 0
  norm_num at hz

def family : Registration arena (type_of% (@affine_kernel_span_le)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨affine_kernel_span_le, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@affine_kernel_span_le) (Realization signature) (Type) Unit where
  unitName := `D5.S1.Recurrence.KRegularAffineSubsequence.affine_kernel_span_le.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.KRegularAffineSubsequence.Transport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p n => p.2.2 (p.1 * n + p.2.1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.KRegularAffineSubsequence
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Transport

namespace Closure

private def ppl : ℕ → ℤ := fun n =>
  (_root_.D5.S1.Words.FridPrefix.PL
    (List.ofFn (fun i : Fin n => _root_.D5.S1.Words.Palindromes.PeriodDoubling.u_pd i)) : ℤ)

private theorem ppl_not_regular : ¬ IsKRegular 2 ppl := by
  intro hs
  obtain ⟨G, _, hG⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (kKernel 2 ppl)).1 hs
  let C : (ℕ → ℤ) →ₗ[ℤ] (ℕ → ℚ) := {
    toFun := fun f n => (f n : ℚ)
    map_add' := by intro f g; funext n; simp
    map_smul' := by intro z f; funext n; simp [zsmul_eq_mul] }
  let W : Submodule ℚ (ℕ → ℚ) := Submodule.span ℚ (C '' (G : Set (ℕ → ℤ)))
  letI : FiniteDimensional ℚ W :=
    FiniteDimensional.span_of_finite ℚ (G.finite_toSet.image C)
  have hle : Submodule.span ℚ
      (_root_.D5.S1.Words.Palindromes.PeriodDoubling.twoKernel (fun n =>
        (_root_.D5.S1.Words.FridPrefix.PL
          (List.ofFn (fun i : Fin n =>
            _root_.D5.S1.Words.Palindromes.PeriodDoubling.u_pd i)) : ℚ))) ≤ W := by
    apply Submodule.span_le.mpr
    rintro f ⟨e, r, hr, rfl⟩
    have hv : (fun n => ppl (2 ^ e * n + r)) ∈ Submodule.span ℤ (G : Set (ℕ → ℤ)) := by
      rw [← hG]
      exact Submodule.subset_span ⟨e, r, hr, rfl⟩
    have hx := Submodule.apply_mem_span_image_of_mem_span C hv
    have hsp : Submodule.span ℤ (C '' (G : Set (ℕ → ℤ))) ≤ W.restrictScalars ℤ :=
      Submodule.span_le.mpr (fun _ hf => Submodule.subset_span hf)
    simpa [C, ppl] using hsp hx
  exact _root_.D5.S1.Words.Palindromes.PeriodDoubling.stronger_PPL_kernel_span
    (Submodule.finiteDimensional_of_le hle)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k a b : ℕ) (s : ℕ → ℤ) (_hk : 2 ≤ k) (_ha : 1 ≤ a)
    (_hs : IsKRegular k s), IsKRegular k (R.readout () ⟨a, b, s⟩)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ n => ppl n) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : IsKRegular 2 (fun _ => (0 : ℤ)) := by
    apply Submodule.fg_span
    apply (Set.finite_singleton (fun _ : ℕ => (0 : ℤ))).subset
    rintro f ⟨e, r, hr, rfl⟩
    rfl
  exact ppl_not_regular (h 2 1 0 (fun _ => 0) (by decide) (by decide) hz)

def family : Registration arena (type_of% (@is_k_regular_affine_subsequence)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨is_k_regular_affine_subsequence, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@is_k_regular_affine_subsequence) (Realization signature) (Type) Unit where
  unitName :=
    `D5.S1.Recurrence.KRegularAffineSubsequence.is_k_regular_affine_subsequence.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.KRegularAffineSubsequence.Closure.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p n => p.2.2 (p.1 * n + p.2.1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.KRegularAffineSubsequence
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Closure
end Reg.D5.S1.Recurrence.KRegularAffineSubsequence

end
