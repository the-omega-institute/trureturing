/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalLiftSplitting
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/UniversalLiftSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform product splitting of every complete binary bipermutative lift. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.FactorialCoboundary
import D5.S1.Dynamics.Symbolic.PermutativeLifts.FactorialMinimal
import D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativeLift

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts

noncomputable def permutationTransfer {Q : Type*} [Finite Q]
    (π : Bool → Equiv.Perm Q) : FactorialPoint → Equiv.Perm Q :=
  transfer π (Nat.card (Equiv.Perm Q) + 1)

theorem permutationTransfer_shift {Q : Type*} [Finite Q]
    (π : Bool → Equiv.Perm Q) (y : FactorialPoint) :
    permutationTransfer π (shiftFactorial 1 y) = π (y.1 0) * permutationTransfer π y := by
  apply transfer_shift
  exact fun a => word_holonomy_eq_one π (by omega) (by omega) a

/-- The original finite fibre is retained throughout the conjugacy. -/
noncomputable def trivializingHomeomorph {Q : Type*} [Finite Q]
    [TopologicalSpace Q] [DiscreteTopology Q] (π : Bool → Equiv.Perm Q) :
    (FactorialPoint × Q) ≃ₜ (FactorialPoint × Q) where
  toFun z := (z.1, (permutationTransfer π z.1).symm z.2)
  invFun z := (z.1, permutationTransfer π z.1 z.2)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := by
    letI : TopologicalSpace (Equiv.Perm Q) := ⊥
    letI : DiscreteTopology (Equiv.Perm Q) := discreteTopology_bot _
    have hβ : Continuous (permutationTransfer π) := continuous_transfer π _
    have he : Continuous (fun z : Equiv.Perm Q × Q => z.1.symm z.2) :=
      continuous_of_discreteTopology
    exact continuous_fst.prodMk (he.comp ((hβ.comp continuous_fst).prodMk continuous_snd))
  continuous_invFun := by
    letI : TopologicalSpace (Equiv.Perm Q) := ⊥
    letI : DiscreteTopology (Equiv.Perm Q) := discreteTopology_bot _
    have hβ : Continuous (permutationTransfer π) := continuous_transfer π _
    have he : Continuous (fun z : Equiv.Perm Q × Q => z.1 z.2) :=
      continuous_of_discreteTopology
    exact continuous_fst.prodMk (he.comp ((hβ.comp continuous_fst).prodMk continuous_snd))

theorem trivializing_conjugacy {Q : Type*} [Finite Q]
    [TopologicalSpace Q] [DiscreteTopology Q] (π : Bool → Equiv.Perm Q)
    (y : FactorialPoint) (q : Q) :
    trivializingHomeomorph π (shiftFactorial 1 y, π (y.1 0) q) =
      (shiftFactorial 1 y, (trivializingHomeomorph π (y, q)).2) := by
  apply Prod.ext rfl
  change (permutationTransfer π (shiftFactorial 1 y)).symm (π (y.1 0) q) =
    (permutationTransfer π y).symm q
  apply (permutationTransfer π (shiftFactorial 1 y)).injective
  rw [Equiv.apply_symm_apply, permutationTransfer_shift, Equiv.Perm.mul_apply,
    Equiv.apply_symm_apply]

namespace UniversalLift

open BipermutativeLift
open SymbolicDynamics.FullShift

def shiftLift {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool} (g : ℤ)
    (x : LiftPoint h factorialSubshift) : LiftPoint h factorialSubshift :=
  ⟨shift g x.1, by
    have he : code h (shift g x.1) = shift g (code h x.1) := by
      funext i
      change h (window (shift g x.1) i) = h (window x.1 (g + i))
      apply congrArg h
      funext j
      simp only [window, shift_apply, add_assoc]
    rw [he]
    exact factorialSubshift.mapsTo g x.2⟩

private theorem shiftLift_add {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (g j : ℤ) (x : LiftPoint h factorialSubshift) :
    shiftLift (g + j) x = shiftLift g (shiftLift j x) := by
  apply Subtype.ext
  funext i
  simp [shiftLift, shift, add_assoc, add_comm g j]

instance liftShiftAction {k : ℕ} (h : (Fin (k + 2) → Bool) → Bool) :
    AddAction ℤ (LiftPoint h factorialSubshift) where
  vadd := shiftLift
  zero_vadd x := by
    change shiftLift 0 x = x
    apply Subtype.ext
    funext i
    change x.1 (0 + i) = x.1 i
    rw [zero_add]
  add_vadd := shiftLift_add

/-- Every length at least two is represented by `k+2`; the fibre is exactly
the set of binary prefixes of length `k+1`. -/
noncomputable def splitting {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) :
    LiftPoint h factorialSubshift ≃ₜ (FactorialPoint × Prefix Bool k) :=
  (fullLiftHomeomorph bh factorialSubshift).trans
    (trivializingHomeomorph (prefixPerm bh))

theorem splitting_conjugacy {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (x : LiftPoint h factorialSubshift) :
    splitting bh (liftShift factorialSubshift x) =
      (shiftFactorial 1 (splitting bh x).1, (splitting bh x).2) := by
  change trivializingHomeomorph (prefixPerm bh)
      (fullLiftHomeomorph bh factorialSubshift (liftShift factorialSubshift x)) = _
  rw [full_lift_conjugacy]
  exact trivializing_conjugacy (prefixPerm bh)
    (fullLiftHomeomorph bh factorialSubshift x).1
    (fullLiftHomeomorph bh factorialSubshift x).2

private theorem splitting_fibre_invariant {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (g : ℤ) (x : LiftPoint h factorialSubshift) :
    (splitting bh (shiftLift g x)).2 = (splitting bh x).2 := by
  have hstep (z : LiftPoint h factorialSubshift) :
      (splitting bh (shiftLift 1 z)).2 = (splitting bh z).2 := by
    exact congrArg Prod.snd (splitting_conjugacy bh z)
  have hnat (n : ℕ) (z : LiftPoint h factorialSubshift) :
      (splitting bh (shiftLift (n : ℤ) z)).2 = (splitting bh z).2 := by
    induction n with
    | zero =>
      have hz : shiftLift 0 z = z := zero_vadd ℤ z
      rw [hz]
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) by omega, shiftLift_add,
        hstep, ih]
  cases g with
  | ofNat n => exact hnat n x
  | negSucc n =>
    have he := hnat (n + 1) (shiftLift (Int.negSucc n) x)
    rw [← shiftLift_add] at he
    have hz : ((n + 1 : ℕ) : ℤ) + Int.negSucc n = 0 := by omega
    rw [hz, show shiftLift 0 x = x from zero_vadd ℤ x] at he
    exact he.symm

/-- For every allowed code length and every bipermutative binary code, its
entire inverse image over this same infinite minimal base is nonminimal. -/
theorem full_lift_not_minimal {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) : ¬ AddAction.IsMinimal ℤ (LiftPoint h factorialSubshift) := by
  intro hminimal
  letI := hminimal
  obtain ⟨y⟩ := (inferInstance : Nonempty FactorialPoint)
  let q₀ : Prefix Bool k := fun _ => false
  let q₁ : Prefix Bool k := fun _ => true
  let x₀ := (splitting bh).symm (y, q₀)
  let x₁ := (splitting bh).symm (y, q₁)
  let C : Set (LiftPoint h factorialSubshift) := {x | (splitting bh x).2 = q₀}
  have hC : IsClosed C := isClosed_singleton.preimage
    (continuous_snd.comp (splitting bh).continuous)
  have hsub : AddAction.orbit ℤ x₀ ⊆ C := by
    rintro z ⟨g, rfl⟩
    change (splitting bh (shiftLift g x₀)).2 = q₀
    rw [splitting_fibre_invariant]
    exact congrArg Prod.snd ((splitting bh).apply_symm_apply (y, q₀))
  have hdense := AddAction.dense_orbit ℤ x₀
  have hx₁ : x₁ ∈ C := by
    apply hC.closure_subset_iff.mpr hsub
    rw [hdense.closure_eq]
    trivial
  have he : q₁ = q₀ := by
    change (splitting bh x₁).2 = q₀ at hx₁
    simpa [x₁] using hx₁
  have he₀ := congrFun he (0 : Fin (k + 1))
  simp [q₀, q₁] at he₀

end UniversalLift
end D5.S1.Dynamics.Symbolic.PermutativeLifts
