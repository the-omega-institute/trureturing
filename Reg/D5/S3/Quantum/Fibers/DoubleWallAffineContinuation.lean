import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.DoubleWallAffineContinuation
import Reg.Support.DependentFamily
open D5.S3.Quantum.Fibers.FiniteRectangleTransport
open D5.S3.Quantum.Fibers.OriginalControlComposition
open D5.S3.Quantum.Fibers.DoubleWallAffineContinuation
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set
namespace Reg.D5.S3.Quantum.Fibers.DoubleWallAffineContinuation
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

def signature : Signature where
  Params := ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ → ℝ → Response
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ (Z : ℝ) (k : ℝ) => response (1-Z) Z k) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => (0 : ℝ → ℝ → Response)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀
    (Z s a b : ℝ) (hZ : 0 < Z) (hZ1 : Z < 1) (hs : s ≠ 0) (hab : a < b)
    (legal : ∀ k ∈ Ioo a b,
      0 < k ∧ k < (1-Z)/2 ∧ 0 < k+s ∧ k+s < (1-Z)/2),
    ValidBase ((1-Z)/2,(1-Z)/2,Z) ∧
    (∀ k ∈ Ioo a b, ∀ (chi0 : ℝ) (theta : Vec),
      OriginalControl ((1-Z)/2,(1-Z)/2,Z) 1
        (fun t => k+s*t) (fun _ => chi0) ∧
      Admissible ((1-Z)/2,(1-Z)/2,Z) 1
        (polygon [(k,chi0,theta),(k+s,chi0,theta)]) ∧
      (∀ t ∈ Icc (0:ℝ) 1,
        polygon [(k,chi0,theta),(k+s,chi0,theta)] t = (k+s*t,chi0,theta)) ∧
      (∀ t : ℝ, HasDerivAt (fun x : ℝ => k+s*x) s t ∧
        HasDerivAt (fun _ : ℝ => chi0) 0 t)) ∧
    ¬ (∃ (D : Response →ₗ[ℝ] Response) (c : Response),
      ∀ k ∈ Ioo a b, ∀ alpha beta : ℝ,
        R.readout () Z (k+s) alpha beta =
          c+D (R.readout () Z k alpha beta))

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hn := (h (1/2) (1/32) (1/16) (1/8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro k hk; constructor; linarith [hk.1]; constructor; linarith [hk.2];
        constructor <;> linarith [hk.1,hk.2])).2.2
  apply hn
  refine ⟨0,0,?_⟩
  intro k hk alpha beta
  simp [rejected,realize] <;> rfl

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lawful_probability_continuation_not_affine,rejected,rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(1/2:ℝ),(1/8:ℝ),(1/16:ℝ),?_⟩
    intro he
    have hx := congrFun (congrFun (congrFun he 0) 0) 2
    change 2*Real.sqrt ((1/8:ℝ)*(1/2))*Real.cos 0 =
      2*Real.sqrt ((1/16:ℝ)*(1/2))*Real.cos 0 at hx
    norm_num only [Real.cos_zero, mul_one,
      show (1/8:ℝ)*(1/2)=1/16 by norm_num,
      show (1/16:ℝ)*(1/2)=1/32 by norm_num] at hx
    have h2 : Real.sqrt (1/32:ℝ) ≠ 1/4 := by
      intro he
      have hh := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/32)
      rw [he] at hh
      norm_num at hh
    exact h2 (by linarith [hx])

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@D5.S3.Quantum.Fibers.DoubleWallAffineContinuation.lawful_probability_continuation_not_affine)
    (type_of% (realize signature (fun _ (Z : ℝ) (k : ℝ) => response (1-Z) Z k)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.DoubleWallAffineContinuation.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.DoubleWallAffineContinuation.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ (Z : ℝ) (k : ℝ) => response (1-Z) Z k)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.DoubleWallAffineContinuation,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body",
        "arg","arg","arg","arg","body","arg","body","body","body","body","body",
        "arg","arg","arg","fn","fn"],
      stateBinder := 11,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
end
end Reg.D5.S3.Quantum.Fibers.DoubleWallAffineContinuation
