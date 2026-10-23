import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.OrliczCommonEnergy
import Reg.Support.SingleDependentReadout

open Filter Set Topology
open scoped BigOperators ENNReal NNReal Topology
open _root_.D5.S3.Quantum.Analysis.OrliczCommonEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy

private lemma psi_zero {p : ℝ} (hp : 0 < p) : conjugate p 0 = 0 := by
  apply le_antisymm
  · simpa using conjugate_le_majorant hp (le_refl (0 : ℝ))
  · exact conjugate_nonneg hp (le_refl (0 : ℝ))

namespace Supremum
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Set ℝ) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ _ S => BddAbove S) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {p u : ℝ}, 0 < p → 0 ≤ u →
    let S := (fun t : Set.Ici (0 : ℝ) => u * (t : ℝ) - phi p t) '' Set.univ
    S.Nonempty ∧ R.readout () () S
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (p := 1) (u := 0) (by norm_num) (by norm_num)).2
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), {0}, Set.univ, ?_⟩
  change BddAbove ({0} : Set ℝ) ≠ BddAbove (Set.univ : Set ℝ)
  intro h
  exact not_bddAbove_univ (h ▸ bddAbove_singleton)

def family : Registration arena (type_of% (@conjugate_nonempty_bddAbove)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conjugate_nonempty_bddAbove, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@conjugate_nonempty_bddAbove) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.Supremum.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.Supremum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => BddAbove S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Supremum
namespace Nonnegative
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p u => conjugate p u) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {p u : ℝ}, 0 < p → 0 ≤ u → 0 ≤ R.readout () p u
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (p := 1) (u := 0) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change conjugate 1 0 ≠ conjugate 1 1
  rw [psi_zero (by norm_num : (0 : ℝ) < 1)]
  have h := fenchel_young (p := 1) (u := 1) (t := 1)
    (by norm_num) (by norm_num) (by norm_num)
  have h1 : 1 ≤ conjugate 1 1 := by simpa [phi] using h
  linarith

def family : Registration arena (type_of% (@conjugate_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conjugate_nonneg, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@conjugate_nonneg) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.Nonnegative.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.Nonnegative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p u => conjugate p u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Nonnegative
namespace Majorant
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p u => u * Real.exp (u ^ p⁻¹)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {p u : ℝ}, 0 < p → 0 ≤ u → conjugate p u ≤ R.readout () p u
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (p := 1) (u := 0) (by norm_num) (by norm_num)
  rw [psi_zero (by norm_num)] at hb
  norm_num [rejected, realize] at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  simp only [actual, realize, zero_mul, one_mul]
  exact (Real.exp_ne_zero _).symm

def family : Registration arena (type_of% (@conjugate_le_majorant)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conjugate_le_majorant, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@conjugate_le_majorant) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.Majorant.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.Majorant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p u => u * Real.exp (u ^ p⁻¹)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Majorant
namespace Young
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ × ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ z => z.1 * z.2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {p u t : ℝ}, 0 < p → 0 ≤ u → 0 ≤ t →
    R.readout () () (u, t) ≤ phi p t + conjugate p u
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (p := 1) (u := 0) (t := 0) (by norm_num) (by norm_num) (by norm_num)
  rw [psi_zero (by norm_num)] at hb
  norm_num [phi, rejected, realize] at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 1), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@fenchel_young)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fenchel_young, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fenchel_young) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.Young.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.Young.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.1 * z.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Young

universe u

namespace YoungTail
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ → ℝ≥0∞) (fun _ => ℕ → ℝ≥0∞)
def actual : Realization signature :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => ∞) (fun e => nomatch e)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hb := congrFun h 0
  norm_num [actual, realize] at hb

def arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} (f A : X → ℕ → ℝ≥0∞)
    (B : ℝ≥0 → ℕ → ℝ≥0∞) (M : ℝ≥0∞),
    (∀ x, (∑' n, A x n) ≤ M) → M ≠ ∞ →
    (∀ (a : ℝ≥0), 0 < a → ∀ x n, (a : ℝ≥0∞) * f x n ≤ A x n + B a n) →
    (∀ a : ℝ≥0, 0 < a → (∑' n, B a n) ≠ ∞) →
    ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ x,
      (∑' k, (R.readout () () (f x)) (N + k)) ≤ (ε : ℝ≥0∞)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨N, hN⟩ := @h PUnit.{u+1} (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) 0 (by simp) (by simp) (by simp) (by simp) 1 (by norm_num)
  have hb := hN PUnit.unit
  simp [rejected, realize] at hb

def family : Registration arena.{u} (type_of% (@uniform_tail_from_young.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@uniform_tail_from_young.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_tail_from_young.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.YoungTail.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.YoungTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end YoungTail
namespace OrliczTail
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ → ℝ≥0∞) (fun _ => ℕ → ℝ≥0∞)
def actual : Realization signature :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => ∞) (fun e => nomatch e)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hb := congrFun h 0
  norm_num [actual, realize] at hb

def arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} {p : ℝ}, 0 < p →
    ∀ (s h : ℕ → ℝ) (d : X → ℕ → ℝ),
    (∀ n, 0 < s n) → (∀ n, 0 ≤ h n) → (∀ x n, 0 ≤ d x n) →
    ∀ M : ℝ≥0∞, (∀ x, (∑' n, baseTerm p s (d x) n) ≤ M) → M ≠ ∞ →
    (∀ a : ℝ≥0, 0 < a → (∑' n, dualTerm p s h a n) ≠ ∞) →
    ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ x,
      (∑' k, (R.readout () () (energyTerm h (d x))) (N + k)) ≤ (ε : ℝ≥0∞)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨N, hN⟩ := @h PUnit.{u+1} 1 (by norm_num) (fun _ => 1)
    (fun _ => 0) (fun _ _ => 0) (by simp) (by simp) (by simp) 0
    (by simp [baseTerm, phi]) (by simp)
    (by simp [dualTerm, psi_zero (by norm_num : (0 : ℝ) < 1)]) 1 (by norm_num)
  have hb := hN PUnit.unit
  simp [rejected, realize] at hb

def family : Registration arena.{u} (type_of% (@orlicz_uniform_energy_tail.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@orlicz_uniform_energy_tail.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@orlicz_uniform_energy_tail.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.OrliczTail.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.OrliczTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end OrliczTail
namespace Amplification
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℕ) (fun _ => ℕ → ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ w => w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hb := congrFun h 0
  norm_num [actual, realize] at hb

def arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} {p : ℝ}, 0 < p →
    ∀ (s h : ℕ → ℝ) (d : X → ℕ → ℝ),
    (∀ n, 0 < s n) → (∀ n, 0 ≤ h n) → (∀ x n, 0 ≤ d x n) →
    ∀ (M : ℝ≥0∞) (δ : ℝ≥0), 0 < δ →
    (∀ x, (∑' n, baseTerm p s (d x) n) ≤ M) → M ≠ ∞ →
    (∀ a : ℝ≥0, 0 < a → (∑' n, dualTerm p s h a n) ≠ ∞) →
    ∃ w : ℕ → ℕ,
      (∀ n, 1 ≤ (R.readout () () w) n) ∧ Monotone w ∧ Tendsto w atTop atTop ∧
      (∀ x, (∑' n, amplifiedEnergy w h (d x) n) ≤
        (∑' n, energyTerm h (d x) n) + (δ : ℝ≥0∞)) ∧
      (∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ x,
        (∑' k, amplifiedEnergy w h (d x) (N + k)) ≤ (ε : ℝ≥0∞))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨w, hw, _⟩ := @h PUnit.{u+1} 1 (by norm_num) (fun _ => 1)
    (fun _ => 0) (fun _ _ => 0) (by simp) (by simp) (by simp) 0 1 (by norm_num)
    (by simp [baseTerm, phi]) (by simp)
    (by simp [dualTerm, psi_zero (by norm_num : (0 : ℝ) < 1)])
  have hb := hw 0
  norm_num [rejected, realize] at hb

def family : Registration arena.{u} (type_of% (@exists_amplified_orlicz_energy.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_amplified_orlicz_energy.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_amplified_orlicz_energy.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.Amplification.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.Amplification.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Amplification

namespace CommonEnergy
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℕ) (fun _ => ℕ → ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ w => w) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} [TopologicalSpace X] {p : ℝ}, 0 < p →
    ∀ (s : ℕ → ℝ) (d : X → ℕ → ℝ),
    (∀ n, 0 < s n) → HasSum s 1 → (∀ x n, 0 ≤ d x n) →
    (∀ x, HasSum (d x) 1) → (∀ n, Continuous (fun x => d x n)) →
    ∀ M : ℝ≥0∞, (∀ x, (∑' n, baseTerm p s (d x) n) ≤ M) → M ≠ ∞ →
    (∀ a : ℝ≥0, 0 < a →
      (∑' n, dualTerm p s (logarithmicLevel s) a n) ≠ ∞) →
    ∀ δ : ℝ≥0, 0 < δ → ∃ w : ℕ → ℕ,
      (∀ n, 1 ≤ (R.readout () () w) n) ∧ Monotone w ∧ Tendsto w atTop atTop ∧
      (∀ n, logarithmicLevel s n ≤ commonLevel w s n) ∧
      Tendsto (commonLevel w s) atTop atTop ∧
      (∀ β : ℝ, 0 < β → Summable (fun n => Real.exp (-β * commonLevel w s n))) ∧
      (∀ x, Summable (fun n => logarithmicLevel s n * d x n)) ∧
      (∀ x, Summable (fun n => commonLevel w s n * d x n)) ∧
      Continuous (fun x => scalarEnergy (commonLevel w s) (d x)) ∧
      (∀ x, scalarEnergy (commonLevel w s) (d x) ≤
        scalarEnergy (logarithmicLevel s) (d x) + (δ : ℝ)) ∧
      (∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ x,
        (∑' k, ENNReal.ofReal (commonLevel w s (N + k) * d x (N + k))) ≤ (ε : ℝ≥0∞))

theorem actual_law : arena.{u}.Law actual := @exists_continuous_common_energy.{u}

-- The positive law retains the normalized reference, its actual logarithm,
-- every positive dual scale, arbitrary topological X and every conclusion.
-- A rejected realization respecting these hypotheses and raw source selection
-- are not supplied by this partial registration.
end CommonEnergy

#print axioms CommonEnergy.actual_law
namespace GenericSummability
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} (f : X → ℕ → ℝ)
    (hf : ∀ x n, 0 ≤ f x n) (hUT : ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ x,
      (∑' k, ENNReal.ofReal (f x (N + k))) ≤ (ε : ℝ≥0∞)),
    ∀ x, R.readout () () (Summable (f x))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro q
  have ht : ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ _x : ULift.{u} Unit,
      (∑' _k : ℕ, ENNReal.ofReal (0 : ℝ)) ≤ (ε : ℝ≥0∞) := by
    intro ε hε
    exact ⟨0, fun _ => by simp⟩
  have hx := q (X := ULift.{u} Unit) (fun _ _ => 0) (fun _ _ => le_rfl) ht ⟨()⟩
  exact hx

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  change True ≠ False
  simp

def family : Registration arena.{u} (type_of% (@summable_of_uniform_ennreal_tails.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@summable_of_uniform_ennreal_tails.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@summable_of_uniform_ennreal_tails.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.GenericSummability.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.GenericSummability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end GenericSummability

namespace GenericContinuity
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} [TopologicalSpace X] (f : X → ℕ → ℝ)
    (hf : ∀ x n, 0 ≤ f x n) (hc : ∀ n, Continuous (fun x => f x n))
    (hUT : ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ x,
      (∑' k, ENNReal.ofReal (f x (N + k))) ≤ (ε : ℝ≥0∞)),
    R.readout () () (Continuous (fun x => ∑' n, f x n))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro q
  have ht : ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ _x : ULift.{u} Unit,
      (∑' _k : ℕ, ENNReal.ofReal (0 : ℝ)) ≤ (ε : ℝ≥0∞) := by
    intro ε hε
    exact ⟨0, fun _ => by simp⟩
  have hx := q (X := ULift.{u} Unit) (fun _ _ => 0) (fun _ _ => le_rfl) (fun _ => continuous_const) ht
  exact hx

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  change True ≠ False
  simp

def family : Registration arena.{u} (type_of% (@continuous_of_uniform_ennreal_tails.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@continuous_of_uniform_ennreal_tails.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuous_of_uniform_ennreal_tails.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.GenericContinuity.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy.GenericContinuity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end GenericContinuity

end Reg.D5.S3.Quantum.Analysis.OrliczCommonEnergy
