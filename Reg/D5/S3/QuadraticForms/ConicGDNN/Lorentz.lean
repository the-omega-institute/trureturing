import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.ConicGDNN.Lorentz
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.QuadraticForms.ConicGDNN.Lorentz
open _root_.D5.S3.QuadraticForms.ConicGDNN.Defs
open _root_.D5.S3.QuadraticForms.ConicGDNN.Lorentz
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix MvPolynomial
open scoped BigOperators
noncomputable section
abbrev Dimensions := Σ _p : ℕ, Σ r : ℕ, Fin r → ℕ
abbrev Vector (d : Dimensions) := Idx d.1 d.2.1 d.2.2 → ℝ
abbrev Polynomial (d : Dimensions) := MvPolynomial (Idx d.1 d.2.1 d.2.2) ℝ
abbrev coneSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Dimensions
    (fun d => Set (Vector d)) (fun d => Set (Vector d))
def coneActual : Realization coneSignature :=
  realize coneSignature (fun _ _ S => dualCone S) (fun e => nomatch e)
def coneRejected : Realization coneSignature :=
  realize coneSignature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev coneArena : Arena where
  signature := coneSignature
  Law R := ∀ (p r : ℕ) (k : Fin r → ℕ),
    R.readout () ⟨p, r, k⟩ (cone p r k) = cone p r k
private theorem coneRejected_law : ¬ coneArena.Law coneRejected := by
  intro h
  let k : Fin 0 → ℕ := fun i => Fin.elim0 i
  have hz : (0 : Idx 0 0 k → ℝ) ∈ cone 0 0 k := by
    constructor
    · intro i; exact Fin.elim0 i
    · intro j; exact Fin.elim0 j
  have h0 := h 0 0 k
  change (∅ : Set (Idx 0 0 k → ℝ)) = cone 0 0 k at h0
  rw [← h0] at hz
  exact hz
private theorem coneDependence : ObservationalDependence coneSignature coneActual := by
  intro i
  let k : Fin 0 → ℕ := fun i => Fin.elim0 i
  let d : Dimensions := ⟨1, 0, k⟩
  refine ⟨d, ∅, Set.univ, ?_⟩
  intro he
  have hm : (fun _ => (1 : ℝ)) ∈ (dualCone (∅ : Set (Vector d))) := by
    intro y hy
    exact hy.elim
  change dualCone (∅ : Set (Vector d)) = dualCone Set.univ at he
  rw [he] at hm
  have hn := hm (fun _ => -1) (Set.mem_univ _)
  norm_num [dotProduct, d, k, Fintype.sum_sum_type, Fintype.sum_sigma,
    Fin.sum_univ_one] at hn
def coneSource : Registration coneArena (type_of% @dualCone_cone) where
  actual := coneActual
  bridge := Iff.rfl
  variation := ⟨dualCone_cone, coneRejected, coneRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity coneArena.Law
    coneActual coneRejected coneRejected_law
  dependence := coneDependence
abbrev squareSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Dimensions Vector Polynomial
def squareActual : Realization squareSignature :=
  realize squareSignature (fun _ _ u => ∑ a, C (u a) * jsq a)
    (fun e => nomatch e)
def squareRejected : Realization squareSignature :=
  realize squareSignature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev squareArena : Arena where
  signature := squareSignature
  Law R := ∀ {p r : ℕ} {k : Fin r → ℕ} (u : Idx p r k → ℝ),
    u ∈ cone p r k → ∃ L : List (MvPolynomial (Idx p r k) ℝ),
      (∀ ℓ ∈ L, ℓ.IsHomogeneous 1) ∧
      R.readout () ⟨p, r, k⟩ u = (L.map (· ^ 2)).sum
private theorem squareRejected_law : ¬ squareArena.Law squareRejected := by
  intro h
  let k : Fin 0 → ℕ := fun i => Fin.elim0 i
  let u : Idx 1 0 k → ℝ := fun _ => 1
  have hu : u ∈ cone 1 0 k := ⟨by intro i; exact zero_le_one, by intro j; exact Fin.elim0 j⟩
  obtain ⟨L, hL, he⟩ := h u hu
  have hv := congrArg (MvPolynomial.eval (fun _ => (0 : ℝ))) he
  have hnon : 0 ≤ MvPolynomial.eval (fun _ => (0 : ℝ)) ((L.map (· ^ 2)).sum) := by
    clear hL he hv
    induction L with
    | nil => simp
    | cons f L ih =>
      simpa using add_nonneg (sq_nonneg (MvPolynomial.eval (fun _ => (0 : ℝ)) f)) ih
  have hv1 : (-1 : ℝ) = MvPolynomial.eval (fun _ => (0 : ℝ)) ((L.map (· ^ 2)).sum) := by
    simpa only [squareRejected, realize, map_neg, map_one] using hv
  have hn : 0 ≤ (-1 : ℝ) := by
    rw [← hv1] at hnon
    exact hnon
  norm_num at hn
private theorem squareDependence : ObservationalDependence squareSignature squareActual := by
  intro i
  let k : Fin 0 → ℕ := fun i => Fin.elim0 i
  let d : Dimensions := ⟨1, 0, k⟩
  refine ⟨d, 0, (fun _ => 1), ?_⟩
  intro he
  have hv := congrArg (MvPolynomial.eval (fun _ => (1 : ℝ))) he
  norm_num [squareActual, realize, d, k, jsq, Fintype.sum_sum_type,
    Fintype.sum_sigma, Fin.sum_univ_one, Pi.zero_apply] at hv
  change (0 : ℝ) = 1 at hv
  norm_num at hv

def squareSource : Registration squareArena (type_of% @pullback_eq_sum_sq) where
  actual := squareActual
  bridge := Iff.rfl
  variation := ⟨pullback_eq_sum_sq, squareRejected, squareRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity squareArena.Law
    squareActual squareRejected squareRejected_law
  dependence := squareDependence

def coneAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@dualCone_cone) (Realization coneSignature) Unit Unit where
  unitName := `Reg.D5.S3.QuadraticForms.ConicGDNN.Lorentz.coneUnit
  realizationName := `Reg.D5.S3.QuadraticForms.ConicGDNN.Lorentz.coneSource
  realizationSource := none
  generated := false
  arena := .source ⟨coneArena⟩
  objectArena := .source ⟨coneArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coneArena ⟨coneSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coneSignature (fun _ _ S => dualCone S)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.ConicGDNN.Lorentz
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def squareAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pullback_eq_sum_sq) (Realization squareSignature) Unit Unit where
  unitName := `Reg.D5.S3.QuadraticForms.ConicGDNN.Lorentz.squareUnit
  realizationName := `Reg.D5.S3.QuadraticForms.ConicGDNN.Lorentz.squareSource
  realizationSource := none
  generated := false
  arena := .source ⟨squareArena⟩
  objectArena := .source ⟨squareArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source squareArena ⟨squareSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize squareSignature (fun _ _ u => ∑ a, C (u a) * jsq a)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.ConicGDNN.Lorentz
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms coneAudit
#print axioms squareAudit
end
end Reg.D5.S3.QuadraticForms.ConicGDNN.Lorentz
