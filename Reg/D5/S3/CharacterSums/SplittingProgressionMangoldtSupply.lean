import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.SplittingProgressionMangoldtSupply
import Reg.Support.SingleDependentReadout

/-! The audit observes the allowed exceptional count as the progression length changes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Real Filter Finset
open ArithmeticFunction hiding log
open _root_.D5.S3.CharacterSums.SplittingProgressionMangoldtSupply
open _root_.D5.S3.CharacterSums.DyadicMangoldtPrimeSupply (cutoff)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.SplittingProgressionMangoldtSupply

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p L => 8*(L:ℝ)/p.2^p.1) (fun e => nomatch e)

def negativeBound : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ q b m A L : ℕ,
    b%4=3 → 4 ∣ m → (∀ p : ℕ, p.Prime → p ∣ m → (p:ℝ) ≤ x^(ε/5) ∨ cutoff x < p) →
    exp (x^(ε/5)/2) ≤ 2*(L:ℝ) → ((failures x ε q b m A L).card:ℝ) ≤ V.readout () ⟨ε,x⟩ L

private theorem negative_fails : ¬ arena.Law negativeBound := by
  intro h
  obtain ⟨x,hx,hl⟩ := (((tendsto_rpow_atTop (show 0 < (1:ℝ)/5 by norm_num)).eventually_ge_atTop 2).and (h 1 one_pos)).exists
  let L := ⌈exp (x^((1:ℝ)/5)/2)⌉₊
  have hL : exp (x^((1:ℝ)/5)/2) ≤ 2*(L:ℝ) := by
    have he := Nat.le_ceil (exp (x^((1:ℝ)/5)/2))
    dsimp [L]; linarith [exp_pos (x^((1:ℝ)/5)/2)]
  have hf : ∀ p : ℕ, p.Prime → p ∣ 4 → (p:ℝ) ≤ x^((1:ℝ)/5) ∨ cutoff x < p := by
    intro p hp hd
    have hp2 : p=2 := by
      have h4 : p ≤ 4 := Nat.le_of_dvd (by decide) hd
      interval_cases p <;> norm_num at *
    subst p
    exact Or.inl hx
  have hz := hl 3 3 4 0 L (by decide) (by decide) hf hL
  change ((failures x 1 3 3 4 0 L).card:ℝ) ≤ -1 at hz
  linarith [Nat.cast_nonneg (α:=ℝ) (failures x 1 3 3 4 0 L).card]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨1,1⟩,0,1,?_⟩
  change 8*(0:ℕ)/((1:ℝ)^(1:ℝ)) ≠ 8*(1:ℕ)/((1:ℝ)^(1:ℝ))
  norm_num

def family : Registration arena (type_of% @simultaneous_splitting_progression) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@simultaneous_splitting_progression, negativeBound, negative_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual negativeBound negative_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@simultaneous_splitting_progression) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.SplittingProgressionMangoldtSupply.simultaneous_splitting_progression
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.SplittingProgressionMangoldtSupply "family"
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
    (fun _ p L => 8*(L:ℝ)/p.2^p.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.SplittingProgressionMangoldtSupply
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Discarded

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ y => Chebyshev.theta y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ y => -y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∃ K : ℝ, 0 ≤ K ∧ ∀ (x y : ℝ) (N m d : ℕ) (v : ℕ → ℝ), 0 < x →
      (∀ n, |v n| ≤ 1) → (∀ p : ℕ, p.Prime → p ∣ m → (p:ℝ) ≤ y ∨ N < p) →
      |(∑ n ∈ Finset.Icc 1 N, vonMangoldt n * min 1 (x/n) * v n * (jacobiSym (n:ℤ) d : ℝ)) -
        ∑ p ∈ (Finset.Icc 1 N).filter (fun p => p.Prime ∧ p ≠ 2 ∧ p.Coprime m),
          Real.log p * min 1 (x/p) * v p * (jacobiSym (p:ℤ) d : ℝ)| ≤
          K*Real.sqrt x+Real.log 2+V.readout () () y

private theorem reject_fails : ¬ arena.Law rejected := by
  rintro ⟨K, _, h⟩
  have hf : ∀ p : ℕ, p.Prime → p ∣ 1 → (p:ℝ) ≤ K+log 2+1 ∨ 0 < p :=
    fun _ hp _ => Or.inr hp.pos
  have hz := h 1 (K+log 2+1) 0 1 1 (fun _ => 0) one_pos (by simp) hf
  simp [rejected,realize] at hz
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 2, ?_⟩
  change Chebyshev.theta 0 ≠ Chebyshev.theta 2
  rw [Chebyshev.theta_zero]
  exact (Chebyshev.theta_pos (le_refl 2)).ne

def family : Registration arena (type_of% @clipped_coprime_prime_error) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@clipped_coprime_prime_error, rejected, reject_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected reject_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@clipped_coprime_prime_error) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.SplittingProgressionMangoldtSupply.clipped_coprime_prime_error
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.SplittingProgressionMangoldtSupply.Discarded "family"
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
    (fun _ _ y => Chebyshev.theta y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.SplittingProgressionMangoldtSupply
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Discarded

namespace Finite

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ t => t) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∃ K : ℝ, 0 ≤ K ∧ ∀ (x y t : ℝ) (N b m A L : ℕ) (v : ℕ → ℝ), 0 < x →
      b%4=3 → 4 ∣ m → (∀ p : ℕ, p.Prime → p ∣ m → (p:ℝ) ≤ y ∨ N < p) →
      (∀ n, |v n| ≤ 1) →
      let E := K*sqrt x+log 2+Chebyshev.theta y
      let P := (Icc 1 N).filter (fun p => Nat.Prime p ∧ p ≠ 2 ∧ m.Coprime p)
      let a := fun p : ℕ => log p*min 1 (x/p)*v p
      let F := fun i : ℕ => twistedBy x N (b+m*(A+i)) v
      (∑ i ∈ range L, (F i)^2) ≤ (sqrt (primeMomentBound P a L) + sqrt L * E)^2 ∧
      (∑ i ∈ range L, (max 0 (|F i| -E))^2) ≤ primeMomentBound P a L ∧
        (((range L).filter (fun i => V.readout () () t < |F i|)).card:ℝ)*(max 0 (t-E))^2 ≤
          primeMomentBound P a L

private theorem reject_fails : ¬ arena.Law rejected := by
  rintro ⟨K, _, h⟩
  have hz := (h 1 0 (K+log 2+1) 0 3 4 0 1 (fun _ => 0) one_pos
    (by decide) (by decide) (fun _ hp _ => Or.inr hp.pos) (by simp)).2.2
  simp [rejected,realize,twistedBy,primeMomentBound,Chebyshev.theta_zero] at hz
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual,realize]

def family : Registration arena (type_of% @finite_clipped_progression) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_clipped_progression, rejected, reject_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected reject_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_clipped_progression) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.SplittingProgressionMangoldtSupply.finite_clipped_progression
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.SplittingProgressionMangoldtSupply.Finite "family"
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
    (fun _ _ t => t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.SplittingProgressionMangoldtSupply
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "arg", "arg", "fn", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Finite

end Reg.D5.S3.CharacterSums.SplittingProgressionMangoldtSupply
