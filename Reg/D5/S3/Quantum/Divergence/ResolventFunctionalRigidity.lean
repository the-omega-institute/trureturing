import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.ResolventFunctionalRigidity
import Reg.Support.DependentFamily

noncomputable section
universe u v w
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Divergence.ResolventFunctionalRigidity
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.ResolventFunctionalRigidity.FiniteSamples

abbrev signature : Signature where
  Params := Type u
  State n := n → ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ n := n → ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; cases e⟩

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete original telescope is retained, including independent matrix
and sampling universes. Only the final actual output vector is observed. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {n : Type u} {m : Type v}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {κ : Type w} [Fintype κ]
    (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (V : Matrix n m ℂ) (hV : Vᴴ * V ≤ 1) (hAB : Vᴴ * A * V ≤ B)
    (b : m → ℂ)
    (hb : (star (V *ᵥ b) ⬝ᵥ (V *ᵥ b)).re = (star b ⬝ᵥ b).re)
    (samples : κ → ℝ) (hpositive : ∀ k, 0 < samples k)
    (hinjective : Function.Injective samples)
    (hcard : (Finset.univ.image
      (Sum.elim hA.isHermitian.eigenvalues hB.isHermitian.eigenvalues)).card ≤
        Fintype.card κ)
    (hzero : ∀ k,
      (star (V *ᵥ b) ⬝ᵥ ((A + samples k • (1 : Matrix n n ℂ))⁻¹ *ᵥ (V *ᵥ b))).re -
      (star b ⬝ᵥ ((B + samples k • (1 : Matrix m m ℂ))⁻¹ *ᵥ b)).re = 0)
    (f : ℝ → ℝ), cfc f A *ᵥ (V *ᵥ b) = r.readout () n (V *ᵥ (cfc f B *ᵥ b))

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro n m _ _ _ _ κ _ A B hA hB V hV hAB b hb samples hp hi hc hz f
  exact finite_resolvent_defects_force_functional_intertwining
    A B hA hB V hV hAB b hb samples hp hi hc hz f

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  classical
  intro h
  let n := ULift.{u} (Fin 1)
  let m := ULift.{v} (Fin 1)
  let κ := ULift.{w} (Fin 2)
  let A : Matrix n n ℂ := 0
  let B : Matrix m m ℂ := 0
  let V : Matrix n m ℂ := fun _ _ => 1
  let b : m → ℂ := fun _ => 1
  let samples : κ → ℝ := fun k => (k.down.val : ℝ) + 1
  have hV : Vᴴ * V = 1 := by
    ext i j
    change (∑ k : n, star (V k i) * V k j) = (1 : Matrix m m ℂ) i j
    simp [V, n, Matrix.one_apply, Subsingleton.elim i j]
  have hAB : Vᴴ * A * V ≤ B := by simp [A, B]
  have hvec : V *ᵥ b = fun _ => (1 : ℂ) := by
    ext i
    simp [V, b, Matrix.mulVec, dotProduct]
  have hb : (star (V *ᵥ b) ⬝ᵥ (V *ᵥ b)).re = (star b ⬝ᵥ b).re := by
    rw [hvec]
    simp [b, dotProduct]
  have hp : ∀ k, 0 < samples k := by intro k; dsimp [samples]; positivity
  have hi : Function.Injective samples := by
    intro i j hij
    apply ULift.ext
    apply Fin.ext
    have hval : (i.down.val : ℝ) = (j.down.val : ℝ) := add_right_cancel hij
    exact_mod_cast hval
  have hc : (Finset.univ.image
      (Sum.elim (Matrix.PosSemidef.zero : A.PosSemidef).isHermitian.eigenvalues
        (Matrix.PosSemidef.zero : B.PosSemidef).isHermitian.eigenvalues)).card ≤
        Fintype.card κ := by
    have hbound := Finset.card_image_le
      (s := (Finset.univ : Finset (n ⊕ m)))
      (f := Sum.elim (Matrix.PosSemidef.zero : A.PosSemidef).isHermitian.eigenvalues
        (Matrix.PosSemidef.zero : B.PosSemidef).isHermitian.eigenvalues)
    simpa [n, m, κ] using hbound
  have hz : ∀ k,
      (star (V *ᵥ b) ⬝ᵥ ((A + samples k • (1 : Matrix n n ℂ))⁻¹ *ᵥ (V *ᵥ b))).re -
      (star b ⬝ᵥ ((B + samples k • (1 : Matrix m m ℂ))⁻¹ *ᵥ b)).re = 0 := by
    intro k
    rw [← cfc_shift_inverse A Matrix.PosSemidef.zero (samples k) (hp k),
      ← cfc_shift_inverse B Matrix.PosSemidef.zero (samples k) (hp k), hvec]
    simp [A, B, b, cfc_apply_zero, Algebra.algebraMap_eq_smul_one,
      Matrix.mulVec, dotProduct]
  have heq := h A B Matrix.PosSemidef.zero Matrix.PosSemidef.zero V
    (le_of_eq hV) hAB b hb samples hp hi hc hz (fun _ => 1)
  change cfc (fun _ : ℝ => 1) A *ᵥ (V *ᵥ b) = 0 at heq
  rw [cfc_const_one ℝ A, Matrix.one_mulVec, hvec] at heq
  have hone := congrFun heq (ULift.up 0)
  exact one_ne_zero hone

def family : Registration arena.{u,v,w}
    (type_of% (@finite_resolvent_defects_force_functional_intertwining.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      cases role; cases other
      exact (hne rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    refine ⟨ULift.{u} (Fin 1), 0, (fun _ => (1 : ℂ)), ?_⟩
    intro h
    exact zero_ne_one (congrFun h (ULift.up 0))

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_resolvent_defects_force_functional_intertwining.{u,v,w})
    (Realization signature.{u}) (Type (u+1)) Unit where
  unitName := `Reg.D5.S3.Quantum.Divergence.ResolventFunctionalRigidity.finiteSamplesUnit
  realizationName := `Reg.D5.S3.Quantum.Divergence.ResolventFunctionalRigidity.FiniteSamples.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨family.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (Type u)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ResolventFunctionalRigidity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Quantum.Divergence.ResolventFunctionalRigidity.FiniteSamples
