import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound comparison audits retain the complete matrix-family statements. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Finset
open scoped BigOperators

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment
noncomputable section
universe u

/-- Observe the actual real comparison in the conclusion, retaining every premise. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def orderActual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def equalityActual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem order_dependence : ObservationalDependence signature orderActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hzero : (0 : ℝ) ≤ 0 := le_rfl
  have hone : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) hzero
  norm_num at hone

private theorem equality_dependence : ObservationalDependence signature equalityActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hone : (1 : ℝ) = 0 := Eq.mp (congrFun h 0) rfl
  norm_num at hone

private theorem sensitivity (law : Realization signature → Prop)
    (actual : Realization signature) (hbad : ¬ law rejected) :
    Sensitivity ⟨signature, law⟩ actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, hbad⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

namespace centered_row_moment
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [Nonempty ι] (K : Matrix ι ι ℝ) (hK : K.PosSemidef),
    R.readout () ()
      (centeredRowEnergy K)
      (uniformCharge K *
      (K.trace - uniformCharge K / Fintype.card ι))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hf := @h PUnit inferInstance inferInstance 0 Matrix.PosSemidef.zero
  exact hf

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.centered_row_moment.{u})) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.centered_row_moment.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law orderActual rejected_law
  dependence := order_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.centered_row_moment.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.centered_row_moment.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.centered_row_moment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end centered_row_moment

namespace centered_row_moment_of_nonpositive_offDiag
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [Nonempty ι]
    (K : Matrix ι ι ℝ) (hK : K.PosSemidef) (γ : ℝ)
    (hz : ∀ i j, i ≠ j → K i j ≤ 0) (hd : ∀ i, K i i ≤ 2 * γ),
    R.readout () ()
      (centeredRowEnergy K)
      (4 * γ * uniformCharge K -
      (uniformCharge K)^2 / Fintype.card ι)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hf := @h PUnit inferInstance inferInstance 0 Matrix.PosSemidef.zero 0
    (by intro i j hij; simp) (by intro i; simp)
  exact hf

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.centered_row_moment_of_nonpositive_offDiag.{u})) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.centered_row_moment_of_nonpositive_offDiag.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law orderActual rejected_law
  dependence := order_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.centered_row_moment_of_nonpositive_offDiag.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.centered_row_moment_of_nonpositive_offDiag.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.centered_row_moment_of_nonpositive_offDiag.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end centered_row_moment_of_nonpositive_offDiag

namespace permutation_weighted_second_moment
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] (z w : ι → ℝ)
    (hk : 2 ≤ Fintype.card ι) (hz : ∑ i, z i = 0),
    R.readout () ()
      (permutationAverage (fun π => (∑ i, w i * z (π i))^2))
      ((∑ i, (z i)^2) /
        ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)) *
        ((Fintype.card ι : ℝ) * (∑ i, (w i)^2) - (∑ i, w i)^2))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hf := @h (ULift.{u} (Fin 2)) inferInstance 0 0
    (by simp) (by simp)
  exact hf

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.permutation_weighted_second_moment.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.permutation_weighted_second_moment.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law equalityActual rejected_law
  dependence := equality_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.permutation_weighted_second_moment.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.permutation_weighted_second_moment.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.permutation_weighted_second_moment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end permutation_weighted_second_moment

namespace general_r_assignment_moment
abbrev arena : Arena where
  signature := signature
  Law R := ∀
    {r a b : ℕ} (hr : 3 ≤ r) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (top : Fin a → ℝ) (bottom : Fin b → ℝ)
    (K : Equiv.Perm (Fin a) → Equiv.Perm (Fin b) → Matrix (Fin r) (Fin r) ℝ)
    (topWeight : Fin r → Fin a → ℝ)
    (bottomWeight : Fin r → Fin b → ℝ)
    (diagSlot : Fin r → Fin b) (s γ : ℝ)
    (hacard : (a : ℝ) = (r : ℝ) * ((r : ℝ) - 1) / 2)
    (hbcard : (b : ℝ) = (r : ℝ) * ((r : ℝ) + 1) / 2)
    (hA : 0 < (a : ℝ)) (hB : 0 < (b : ℝ))
    (ha1 : (a : ℝ) - 1 ≠ 0) (hb1 : (b : ℝ) - 1 ≠ 0)
    (hTopFactor : ∀ i,
      ((a : ℝ) * ∑ k, (topWeight i k)^2 - (∑ k, topWeight i k)^2) /
          ((a : ℝ) * ((a : ℝ) - 1)) =
        2 * (r - 1 : ℝ) / ((r : ℝ) * ((r : ℝ) + 1)))
    (hBottomFactor : ∀ i,
      ((b : ℝ) * ∑ k, (bottomWeight i k)^2 - (∑ k, bottomWeight i k)^2) /
          ((b : ℝ) * ((b : ℝ) - 1)) = 2 / (r : ℝ))
    (hTopSum : ∀ i, ∑ k, topWeight i k = -(r - 1 : ℝ))
    (hBottomSum : ∀ i, ∑ k, bottomWeight i k = (r + 1 : ℝ))
    (hrow : ∀ π σ i,
      rowSum (K π σ) i =
        (∑ k, topWeight i k * top (π k)) +
        (∑ k, bottomWeight i k * bottom (σ k)))
    (hcharge : ∀ π σ, uniformCharge (K π σ) = 2 * s)
    (htrace : ∀ π σ, Matrix.trace (K π σ) =
      2 * ∑ i, bottom (σ (diagSlot i)))
    (hK : ∀ π σ, (K π σ).PosSemidef)
    (hoff : ∀ π σ i j, i ≠ j → K π σ i j ≤ 0)
    (hdiag : ∀ π σ i, K π σ i i ≤ 2 * γ)
    (hs : ∑ i, bottom i - ∑ i, top i = s)
    (hmean0 :
      -(r - 1 : ℝ) * ((∑ i, top i) / (a : ℝ)) +
        (r + 1 : ℝ) * ((∑ i, bottom i) / (b : ℝ)) = 2 * s / (r : ℝ)),
    R.readout () ()
      (((r - 1 : ℝ) / ((r : ℝ) + 1)) *
          (∑ i, (top i - (∑ j, top j) / (a : ℝ))^2) +
        (∑ i, (bottom i - (∑ j, bottom j) / (b : ℝ))^2))
      (4 * s * min ((∑ i, bottom i) / ((r : ℝ) + 1)) γ -
        2 * s^2 / (r : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let tw : Fin 3 → Fin 3 → ℝ := fun _ => ![-1, -1, 0]
  let bw : Fin 3 → Fin 6 → ℝ := fun _ => ![2, 1, 1, 0, 0, 0]
  have hf := @h 3 3 6 (by norm_num) (by norm_num) (by norm_num)
    0 0 (fun _ _ => 0) tw bw (fun _ => 0) 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by intro i; norm_num [tw, Fin.sum_univ_succ])
    (by intro i; norm_num [bw, Fin.sum_univ_succ])
    (by intro i; norm_num [tw, Fin.sum_univ_succ])
    (by intro i; norm_num [bw, Fin.sum_univ_succ])
    (by intro π σ i; simp [rowSum])
    (by intro π σ; simp [uniformCharge, rowSum])
    (by intro π σ; simp)
    (by intro π σ; exact Matrix.PosSemidef.zero)
    (by intro π σ i j hij; simp)
    (by intro π σ i; simp)
    (by simp) (by simp)
  exact hf

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.general_r_assignment_moment)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.general_r_assignment_moment, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law orderActual rejected_law
  dependence := order_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.general_r_assignment_moment) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.general_r_assignment_moment.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment.general_r_assignment_moment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end general_r_assignment_moment

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment
