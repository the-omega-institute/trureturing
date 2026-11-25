import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing

/-! Extension of marked HHBB scalar identities to arbitrary actual twisted states. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockGradedTrace (actual_basis_apply oddWeight)
open Orbifold.NativeOddTwistedIntertwiner (Twisted TwistedEven TwistedOdd leechUnit)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open NativeFourHHomogeneousExtension (occupation_monomials_have_marked_words)

open private BasisIndex ambientBasis from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
open private component component_eq_zero project_basis_val expand from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing

local notation "ℒ" => leechData

/-- An HHBB scalar defect that vanishes on every valid marked tensor quadruple
vanishes on arbitrary actual twisted states in the same slot order.
The proof instantiates the finite mark type with `Fin m`. -/
theorem hhbb_defect_eq_zero_of_marked
    (F : TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedOdd →ₗ[ℂ] TwistedOdd →ₗ[ℂ] ℂ)
    (hmarked : ∀ {X : Type} [Finite X]
      (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X),
      l.Nodup → MixedParity slot n l →
      ∀ (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit),
        u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p →
        v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q →
        w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r →
        b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d →
        F u v w b = 0)
    (u v : TwistedEven) (w b : TwistedOdd) : F u v w b = 0 := by
  classical
  rw [expand u v w b F]
  refine Finset.sum_eq_zero fun i _ => ?_
  let u' := component false u i.1
  let v' := component false v i.2.1
  let w' := component true w i.2.2.1
  let b' := component true b i.2.2.2
  change F u' v' w' b' = 0
  let index : Puncture → BasisIndex
    | .P => i.1
    | .Q => i.2.1
    | .R => i.2.2.1
    | .S => i.2.2.2
  let odd : Puncture → Bool
    | .P => false
    | .Q => false
    | .R => true
    | .S => true
  by_cases h : ∀ t, oddWeight ℒ (index t).1 % 2 = (if odd t then 1 else 0)
  · -- The marked data used in component_sewing are local to that proof.
    obtain ⟨m, slot, colour, n, hmarks⟩ :=
      occupation_monomials_have_marked_words (fun t => (index t).1)
    let l := List.finRange m
    have hweight (t : Puncture) :
        doubledOccupation slot n l t % 2 = ((if odd t then 1 else 0 : ℕ) : ℤ) := by
      rw [(hmarks t).2]
      exact_mod_cast h t
    have hpar : MixedParity slot n l := ⟨hweight .P, hweight .Q, hweight .R, hweight .S⟩
    let ground (s : Bool) (a : Twisted ℒ leechUnit s) (t : Puncture) :
        ActualGround ℒ leechUnit :=
      ambientBasis.repr a.val (index t) • Pi.single (index t).2 (1 : ℂ)
    have hword (s : Bool) (a : Twisted ℒ leechUnit s) (t : Puncture) (ht : odd t = s) :
        (component s a (index t)).val = wordAt ℒ slot colour n l t ⊗ₜ[ℂ] ground s a t := by
      have hp := h t
      rw [ht] at hp
      rw [component, Submodule.coe_smul, project_basis_val, ite_eq_left hp,
        actual_basis_apply ℒ leechUnit (index t).1 (index t).2, (hmarks t).1,
        TensorProduct.tmul_smul]
    exact hmarked slot colour n l (List.nodup_finRange m) hpar u' v' w' b'
      (ground false u .P) (ground false v .Q) (ground true w .R) (ground true b .S)
      (hword false u .P rfl) (hword false v .Q rfl)
      (hword true w .R rfl) (hword true b .S rfl)
  · obtain ⟨t, ht⟩ := not_forall.mp h
    cases t with
    | P => simp [show u' = 0 from component_eq_zero false u i.1 ht]
    | Q => simp [show v' = 0 from component_eq_zero false v i.2.1 ht]
    | R => simp [show w' = 0 from component_eq_zero true w i.2.2.1 ht]
    | S => simp [show b' = 0 from component_eq_zero true b i.2.2.2 ht]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing
