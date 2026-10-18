import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy
open _root_.D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
open LeanInformationAudit
open scoped BigOperators

namespace Reg.D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure
noncomputable section
set_option autoImplicit false

abbrev MassParams := Σ M : ℕ, Fin M → ℝ
abbrev massSignature := Reg.Support.SingleDependentReadout.signature
  MassParams (fun _ => ℕ) (fun _ => ℝ)

def massActual : Realization massSignature :=
  realize massSignature (fun _ p k => pb p.2 k) (fun e => nomatch e)

theorem mass_dependence : ObservationalDependence massSignature massActual := by
  intro i
  refine ⟨⟨1, fun _ => 1⟩, 0, 1, ?_⟩
  norm_num [massActual, realize, pb, Finset.univ_unique, Finset.powersetCard_one, Finset.filter_eq', Finset.card_compl]

namespace pb_nonneg
abbrev signature := massSignature
def actual : Realization signature := massActual
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {M : ℕ} {c : Fin M → ℝ} (hc : ∀ i, c i ∈ Set.Icc 0 1) (k : ℕ), 0 ≤ R.readout () ⟨M,c⟩ k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (M := 0) (c := fun i => Fin.elim0 i) (by intro i; exact Fin.elim0 i) 0
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_nonneg, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := mass_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_nonneg) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure.pb_nonneg.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => pb p.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end pb_nonneg

namespace pb_sum_one
abbrev signature := massSignature
def actual : Realization signature := massActual
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {M : ℕ} (c : Fin M → ℝ), ∑ k ∈ Finset.range (M+1), R.readout () ⟨M,c⟩ k = 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (M := 0) (fun i => Fin.elim0 i)
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_sum_one)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_sum_one, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := mass_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_sum_one) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_sum_one.__information_unit
  realizationName := `Reg.D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure.pb_sum_one.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => pb p.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end pb_sum_one

namespace pb_perm
abbrev signature := massSignature
def actual : Realization signature := massActual
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {M : ℕ} (c : Fin M → ℝ) (σ : Equiv.Perm (Fin M)) (k : ℕ), pb (c ∘ σ) k = R.readout () ⟨M,c⟩ k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (M := 0) (fun i => Fin.elim0 i) (Equiv.refl _) 0
  norm_num [rejected, realize, pb, Finset.filter_eq'] at hh

def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_perm)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_perm, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := mass_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_perm) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_perm.__information_unit
  realizationName := `Reg.D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure.pb_perm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => pb p.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end pb_perm

namespace pb_remove_two
attribute [local instance 100000] Classical.propDecidable
abbrev signature := massSignature
def actual : Realization signature := massActual
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {M : ℕ} (c : Fin M → ℝ) {i j : Fin M} (hij : i ≠ j) (k : ℕ),
    R.readout () ⟨M,c⟩ k = (1-c i)*(1-c j)*pbRest c i j k +
      (c i*(1-c j)+c j*(1-c i))*(if 1≤k then pbRest c i j (k-1) else 0) +
      c i*c j*(if 2≤k then pbRest c i j (k-2) else 0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (M := 2) (fun _ => 0) (i := 0) (j := 1) (by
    intro he; have hv := congrArg Fin.val he; norm_num at hv) 0
  have hg := _root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_remove_two
    (M := 2) (fun _ => 0) (i := 0) (j := 1)
    (by intro he; have hv := congrArg Fin.val he; norm_num at hv) 0
  have he : (0:ℝ) = pb (fun _ : Fin 2 => 0) 0 := hh.trans hg.symm
  have hp : 0 < pb (fun _ : Fin 2 => (0:ℝ)) 0 := by
    unfold pb
    apply Finset.sum_pos'
    · intro A hA
      positivity
    · exact ⟨∅, by simp, by simp⟩
  exact hp.ne' he.symm

def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_remove_two)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_remove_two, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := mass_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_remove_two) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.pb_remove_two.__information_unit
  realizationName := `Reg.D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure.pb_remove_two.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => pb p.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end pb_remove_two

namespace le_of_interior_ttransform
abbrev Params := Σ M : ℕ, (Fin M → ℝ) → ℝ
abbrev signature := Reg.Support.SingleDependentReadout.signature
  Params (fun p => Fin p.1 → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p x => p.2 x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {M : ℕ} (G : (Fin M → ℝ) → ℝ)
    (hstep : ∀ x y, InteriorT x y → G x ≤ G y)
    (c d : Fin M → ℝ) (hc : ∀ i, c i ∈ Set.Ioo 0 1)
    (hd : ∀ i, d i ∈ Set.Ioo 0 1) (hm : moreMixed d c),
    R.readout () ⟨M,G⟩ c ≤ G d
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (M := 0) (fun _ => 0) (by intros; exact le_rfl)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i) ⟨by simp [moreMixed,desc,prefixSum], by simp [moreMixed,desc,prefixSum]⟩
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.le_of_interior_ttransform)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.le_of_interior_ttransform, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    refine ⟨⟨1, fun x => x 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    norm_num [actual, realize]

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.le_of_interior_ttransform) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.le_of_interior_ttransform.__information_unit
  realizationName := `Reg.D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure.le_of_interior_ttransform.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end le_of_interior_ttransform

end
end Reg.D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure
