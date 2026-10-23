import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSpectralBound.SharedSpectral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators Matrix
noncomputable section

namespace structural_fixed_good
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ) (fun _ => Fin 16 → ℝ) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ p x => spectralGood (Real.sqrt (target p.1)) (synth (d := p.1) (positions p.1 p.2) x)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N j : ℕ) (_hN : 67 ≤ N) (_hj : 6 ≤ j) (_hj' : j ≤ N-10)
    (x : Fin 16 → ℝ) (_hx : ∀ q, 0 ≤ x q) (_hAx : ∀ r, 0 ≤ (A *ᵥ x) r),
    O.readout () (N,j) x
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 67 6 (by norm_num) (by norm_num) (by norm_num) 0
    (by intro q; simp) (by intro r; simp)
  exact hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let bad : Fin 16 → ℝ := fun q => if q = 15 then -1 else 0
  refine ⟨(67,6), 0, bad, ?_⟩
  change spectralGood (Real.sqrt (target 67)) (synth (d := 67) (positions 67 6) 0) ≠
    spectralGood (Real.sqrt (target 67)) (synth (d := 67) (positions 67 6) bad)
  have hzero : spectralGood (Real.sqrt (target 67)) (synth (d := 67) (positions 67 6) 0) := by
    rw [map_zero]
    exact spectralGood_zero _ _
  have hp : ∀ q, positions 67 6 q ≤ 67 := by
    intro q; fin_cases q <;> norm_num [positions]
  have hm : (∑ k : Fin 67, synth (d := 67) (positions 67 6) bad k) = -67 := by
    rw [mass_synth (d := 67) (positions 67 6) hp]
    rw [Finset.sum_eq_single (15 : Fin 16)]
    · norm_num [bad, positions]
    · intro q _ hq
      simp [bad, hq]
    · simp
  have ht : 0 < Real.sqrt (target 67) := Real.sqrt_pos.2 (by norm_num [target])
  intro heq
  have hb := Eq.mp heq hzero
  unfold spectralGood at hb
  rw [hm] at hb
  have hn := norm_nonneg (WithLp.toLp 2 (synth (d := 67) (positions 67 6) bad))
  nlinarith
def family : Registration arena (type_of% (@structural_fixed_good)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@structural_fixed_good, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@structural_fixed_good) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.structural_fixed_good.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone.structural_fixed_good.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => spectralGood (Real.sqrt (target p.1)) (synth (d := p.1) (positions p.1 p.2) x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end structural_fixed_good

namespace quadratic_interval_le_fun
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ → ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ f x => f x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ f x => f x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (f : ℝ → ℝ) (a b c l r x M : ℝ)
    (hf : ∀ y, f y = a*y^2+b*y+c) (ha : 0 ≤ a)
    (hl : l ≤ x) (hr : x ≤ r) (hleft : f l ≤ M) (hright : f r ≤ M),
    O.readout () f x ≤ M
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (fun _ => 0) 0 0 0 0 0 0 0
    (by intro y; ring) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨id, 0, 1, zero_ne_one⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.quadratic_interval_le_fun)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.quadratic_interval_le_fun, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.quadratic_interval_le_fun) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone.quadratic_interval_le_fun.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone.quadratic_interval_le_fun.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f x => f x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end quadratic_interval_le_fun

namespace ordered_block_energy
universe u v
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ s => s ^ 2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ s => s ^ 2 - 1) (fun e => nomatch e)
/-- The original implicit types, instances, bounds and cardinality premises are unchanged. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (upper : ι → ℝ) (lower : κ → ℝ) (m : ℝ)
    (hm : 0 ≤ m) (hu : ∀ i, m ≤ upper i)
    (hl0 : ∀ i, 0 ≤ lower i) (hl1 : ∀ i, lower i ≤ m)
    (hk : 1 ≤ (Fintype.card ι : ℝ))
    (hcard : (Fintype.card κ : ℝ) ≤
      (Fintype.card ι : ℝ)*((Fintype.card ι : ℝ)-1)),
    (∑ i, (upper i)^2)+(∑ i, (lower i)^2) ≤ O.readout () () (∑ i, upper i)
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hb := h (ι := ULift.{u} (Fin 1)) (κ := ULift.{v} (Fin 0))
    0 0 0 (by norm_num) (by intro i; simp) (by intro i; simp)
    (by intro i; simp) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena.{u,v} (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.ordered_block_energy.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.ordered_block_energy.{u,v}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.ordered_block_energy.{u,v}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone.ordered_block_energy.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone.ordered_block_energy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ordered_block_energy

namespace boundary_mass
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ) (fun _ => Fin 16 → ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ p x => ∑ k : Fin p.1, synth (positions p.1 p.2) x k) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N j : ℕ) (hN : 16 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ),
    O.readout () (N,j) x = low x*(N : ℝ)+x 5*(j : ℝ)+H (head x)-D (tail x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 16 6 (by norm_num) (by norm_num) (by norm_num) 0
  norm_num [rejected, realize, low, head, tail, H, D, H2, D2, E, Fin.sum_univ_succ] at hf
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(16,6), 0, Pi.single (15 : Fin 16) 1, ?_⟩
  change (∑ k : Fin 16, (synth (positions 16 6) (0 : Fin 16 → ℝ) k)) ≠
    ∑ k : Fin 16, (synth (positions 16 6) (Pi.single (15 : Fin 16) 1) k)
  rw [boundary_mass 16 6 (by norm_num) (by norm_num) (by norm_num) 0,
    boundary_mass 16 6 (by norm_num) (by norm_num) (by norm_num) (Pi.single 15 1)]
  norm_num [low, head, tail, H, D, H2, D2, E, Fin.sum_univ_succ,
    Pi.single_apply, Pi.zero_apply]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_mass)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_mass, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_mass) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone.boundary_mass.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone.boundary_mass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => ∑ k : Fin p.1, synth (positions p.1 p.2) x k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone
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
end boundary_mass

namespace boundary_square
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ) (fun _ => Fin 16 → ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ p x => ∑ k : Fin p.1, (synth (positions p.1 p.2) x k)^2) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N j : ℕ) (hN : 16 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ),
    O.readout () (N,j) x = (2*low x+x 5)*(low x*(N : ℝ)+x 5*(j : ℝ)+H (head x)-D (tail x))-low x*(low x+x 5)*(N : ℝ)+E (x 5) (head x) (tail x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 16 6 (by norm_num) (by norm_num) (by norm_num) 0
  norm_num [rejected, realize, low, head, tail, H, D, H2, D2, E, Fin.sum_univ_succ] at hf
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(16,6), 0, Pi.single (15 : Fin 16) 1, ?_⟩
  change (∑ k : Fin 16, (synth (positions 16 6) (0 : Fin 16 → ℝ) k)^2) ≠
    ∑ k : Fin 16, (synth (positions 16 6) (Pi.single (15 : Fin 16) 1) k)^2
  rw [boundary_square 16 6 (by norm_num) (by norm_num) (by norm_num) 0,
    boundary_square 16 6 (by norm_num) (by norm_num) (by norm_num) (Pi.single 15 1)]
  norm_num [low, head, tail, H, D, H2, D2, E, Fin.sum_univ_succ,
    Pi.single_apply, Pi.zero_apply]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_square)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_square, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_square) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone.boundary_square.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone.boundary_square.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => ∑ k : Fin p.1, (synth (positions p.1 p.2) x k)^2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone
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
end boundary_square

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone
