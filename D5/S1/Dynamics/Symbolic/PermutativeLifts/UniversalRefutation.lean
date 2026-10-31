/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalRefutation
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/UniversalRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalRefutation.claim; result=D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalRefutation.result; claim=D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalRefutation.claim
   digest: Exact general-minimal-branch refutation for all lengths and entire permutative lifts. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.UniversalLiftSplitting

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.UniversalRefutation

open SymbolicDynamics.FullShift BipermutativeLift

def translateBase {A : Type*} [TopologicalSpace A] (Y : Subshift A ℤ)
    (g : ℤ) (y : Y.carrier) : Y.carrier :=
  ⟨shift g y.1, Y.mapsTo g y.2⟩

def translateLift {A : Type*} [TopologicalSpace A] {k : ℕ}
    {h : (Fin (k + 2) → A) → A} (Y : Subshift A ℤ) (g : ℤ)
    (x : LiftPoint h Y) : LiftPoint h Y :=
  ⟨shift g x.1, by
    have he : code h (shift g x.1) = shift g (code h x.1) := by
      funext i
      change h (window (shift g x.1) i) = h (window x.1 (g + i))
      apply congrArg h
      funext j
      simp only [window, shift_apply, add_assoc]
    rw [he]
    exact Y.mapsTo g x.2⟩

/-- Kang--Jaeger's general minimal branch. All finite alphabets of size at
least two, every nonempty minimal two-sided subshift, every permitted length
`k+2`, both endpoint bijections, and the whole inverse image are literal.
Minimality is the ordinary density of every integer shift orbit. -/
def claim : Prop :=
  ∀ (A : Type) [Fintype A] [TopologicalSpace A] [DiscreteTopology A],
    2 ≤ Fintype.card A → ∀ Y : Subshift A ℤ,
      Nonempty Y.carrier →
      (∀ y : Y.carrier, DenseRange (fun g : ℤ => translateBase Y g y)) →
      ∃ (k : ℕ) (h : (Fin (k + 2) → A) → A),
        Bipermutative h ∧
          ∀ x : LiftPoint h Y, DenseRange (fun g : ℤ => translateLift Y g x)

/-- The single explicit infinite binary base disproves the universal
existence assertion; neither the length nor the code is fixed in advance. -/
theorem result : Not claim := by
  intro hclaim
  obtain ⟨k, h, bh, hminimal⟩ := hclaim Bool (by decide) factorialSubshift
    (inferInstance : Nonempty FactorialPoint) factorial_orbit_dense
  apply UniversalLift.full_lift_not_minimal bh
  constructor
  intro x
  exact hminimal x

end D5.S1.Dynamics.Symbolic.PermutativeLifts.UniversalRefutation
