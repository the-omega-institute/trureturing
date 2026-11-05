/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every actual prefix fibre of the full balanced lift is conjugate to its minimal base. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedLiftSplitting

/-! Actual prefix fibres are clopen and minimal.
Their orbit closures and exact cardinal are identified. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedLift

open BipermutativeLift Balanced

theorem splitting_integer_conjugacy {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (g : ℤ) (x : LiftPoint h balancedSubshift) :
    splitting bh (shiftLift g x) =
      (shiftBalanced g (splitting bh x).1, (splitting bh x).2) := by
  apply Prod.ext
  · apply Subtype.ext
    change code h (SymbolicDynamics.FullShift.shift g x.1) =
      SymbolicDynamics.FullShift.shift g (code h x.1)
    exact code_shift x.1 g
  · exact splitting_fibre_invariant bh g x

/-- The actual fibre inside the entire inverse image. -/
abbrev Component {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (q : Prefix Bool k) :=
  {x : LiftPoint h balancedSubshift // (splitting bh x).2 = q}

noncomputable def componentHomeomorph {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (q : Prefix Bool k) : Component bh q ≃ₜ BalancedPoint where
  toFun x := (splitting bh x.1).1
  invFun y := ⟨(splitting bh).symm (y, q), by
    exact congrArg Prod.snd ((splitting bh).apply_symm_apply (y, q))⟩
  left_inv x := by
    apply Subtype.ext
    apply (splitting bh).injective
    change splitting bh ((splitting bh).symm ((splitting bh x.1).1, q)) = splitting bh x.1
    rw [Homeomorph.apply_symm_apply]
    exact Prod.ext rfl x.2.symm
  right_inv y := by
    exact congrArg Prod.fst ((splitting bh).apply_symm_apply (y, q))
  continuous_toFun := continuous_fst.comp ((splitting bh).continuous.comp continuous_subtype_val)
  continuous_invFun :=
    ((splitting bh).symm.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _

instance componentNonempty {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (q : Prefix Bool k) : Nonempty (Component bh q) := by
  obtain ⟨y⟩ := (inferInstance : Nonempty BalancedPoint)
  exact ⟨(componentHomeomorph bh q).symm y⟩

def componentShift {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (q : Prefix Bool k) (g : ℤ) (x : Component bh q) :
    Component bh q :=
  ⟨shiftLift g x.1, (splitting_fibre_invariant bh g x.1).trans x.2⟩

instance componentShiftAction {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (q : Prefix Bool k) : AddAction ℤ (Component bh q) where
  vadd := componentShift bh q
  zero_vadd x := Subtype.ext (zero_vadd ℤ x.1)
  add_vadd g j x := Subtype.ext (integerShift_add balancedSubshift g j x.1)

theorem componentHomeomorph_conjugacy {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (q : Prefix Bool k) (g : ℤ) (x : Component bh q) :
    componentHomeomorph bh q (g +ᵥ x) = shiftBalanced g (componentHomeomorph bh q x) := by
  have he := congrArg (fun p : BalancedPoint × Prefix Bool k => p.1)
    (splitting_integer_conjugacy bh g x.1)
  exact he

/-- Every nonempty clopen fibre is minimal for its inherited integer shift. -/
instance componentMinimal {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (q : Prefix Bool k) : AddAction.IsMinimal ℤ (Component bh q) where
  dense_orbit x := by
    let e := componentHomeomorph bh q
    apply e.isInducing.dense_iff.mpr
    intro z
    have himage : e '' AddAction.orbit ℤ x = AddAction.orbit ℤ (e x) := by
      ext y
      constructor
      · rintro ⟨w, ⟨g, rfl⟩, rfl⟩
        exact ⟨g, (componentHomeomorph_conjugacy bh q g x).symm⟩
      · rintro ⟨g, rfl⟩
        exact ⟨g +ᵥ x, ⟨g, rfl⟩, componentHomeomorph_conjugacy bh q g x⟩
    rw [himage]
    exact AddAction.dense_orbit ℤ (e x) (e z)

/-- Every orbit closure is precisely its clopen minimal prefix fibre. -/
theorem orbit_closure_eq_fibre {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (x : LiftPoint h balancedSubshift) :
    closure (AddAction.orbit ℤ x) =
      {z : LiftPoint h balancedSubshift | (splitting bh z).2 = (splitting bh x).2} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro z ⟨g, rfl⟩
      exact splitting_fibre_invariant bh g x
    · exact (splitting_fibre_clopen bh _).isClosed
  · intro z hz
    let q := (splitting bh x).2
    let x' : Component bh q := ⟨x, rfl⟩
    let z' : Component bh q := ⟨z, hz⟩
    have hzdense := AddAction.dense_orbit ℤ x' z'
    have himage : (Subtype.val : Component bh q → LiftPoint h balancedSubshift) ''
        AddAction.orbit ℤ x' = AddAction.orbit ℤ x := by
      ext w
      constructor
      · rintro ⟨v, ⟨g, rfl⟩, rfl⟩
        exact ⟨g, rfl⟩
      · rintro ⟨g, rfl⟩
        exact ⟨g +ᵥ x', ⟨g, rfl⟩, rfl⟩
    have he := mem_closure_image
      (continuous_subtype_val : Continuous
        (Subtype.val : Component bh q → LiftPoint h balancedSubshift)).continuousAt hzdense
    rw [himage] at he
    exact he

theorem fibre_set_injective {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) : Function.Injective
      (fun q : Prefix Bool k => {x : LiftPoint h balancedSubshift | (splitting bh x).2 = q}) := by
  intro p q hpq
  obtain ⟨x⟩ := (inferInstance : Nonempty (Component bh p))
  have hmem := congrArg (fun C : Set (LiftPoint h balancedSubshift) => x.1 ∈ C) hpq
  exact x.2.symm.trans (Eq.mp hmem x.2)

/-- There are exactly 2^(k+1) distinct nonempty clopen minimal prefix fibres. -/
theorem fibre_family_card {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) :
    Nat.card (Set.range (fun q : Prefix Bool k =>
      {x : LiftPoint h balancedSubshift | (splitting bh x).2 = q})) = 2 ^ (k + 1) := by
  calc
    _ = Nat.card (Prefix Bool k) :=
      (Nat.card_congr (Equiv.ofInjective _ (fibre_set_injective bh))).symm
    _ = _ := by simp [Nat.card_eq_fintype_card, Prefix]

/-- The entire inverse image has exactly 2^(k+1) distinct orbit closures. -/
theorem orbit_closure_family_card {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) :
    Nat.card (Set.range (fun x : LiftPoint h balancedSubshift =>
      closure (AddAction.orbit ℤ x))) = 2 ^ (k + 1) := by
  have hset : Set.range (fun x : LiftPoint h balancedSubshift =>
      closure (AddAction.orbit ℤ x)) =
      Set.range (fun q : Prefix Bool k =>
        {x : LiftPoint h balancedSubshift | (splitting bh x).2 = q}) := by
    ext C
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(splitting bh x).2, (orbit_closure_eq_fibre bh x).symm⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨y⟩ := (inferInstance : Nonempty BalancedPoint)
      refine ⟨(splitting bh).symm (y, q), ?_⟩
      change closure (AddAction.orbit ℤ ((splitting bh).symm (y, q))) =
        {x : LiftPoint h balancedSubshift | (splitting bh x).2 = q}
      rw [orbit_closure_eq_fibre bh]
      simp
  rw [hset]
  exact fibre_family_card bh

end D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedLift
