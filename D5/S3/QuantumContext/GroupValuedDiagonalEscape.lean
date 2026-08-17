/- GID: D5/S3/QuantumContext/GroupValuedDiagonalEscape
   generality: G
   mirror-B: D5/B/S3/QuantumContext/GroupValuedDiagonalEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A free group action shifts diagonal coordinates and forces pointwise escape. -/

import Mathlib.GroupTheory.GroupAction.Quotient

/- Library-search audit trail (2026-08-17):
   * Repository searches for group-valued diagonal escape, free-action orbit
     coordinates, `Gamma_A`, and `groupCoordinate` found no equivalent theorem.
   * Pinned Mathlib has the exact free-action normal form
     `MulAction.selfEquivOrbitsQuotientProd'`; it is applied below to the chosen
     orbit representative, rather than reconstructing the coordinate equivalence.
   * Searches in `Mathlib.GroupTheory.GroupAction.Quotient` found no theorem
     packaging all three diagonal conclusions. `IsCancelSMul.eq_one_of_smul`
     is the exact freeness lemma used for the escape conclusion. -/

namespace D5.S3.QuantumContext.GroupValuedDiagonalEscape

universe u v w

/-- Left translation of every diagonal value preserves its orbit, multiplies
its chosen free-action coordinate on the left, and escapes pointwise when the
translating group element is nontrivial. -/
theorem group_valued_diagonal_escape {G : Type u} {X : Type v} {A : Type w}
    [Group G] [MulAction G X] [IsCancelSMul G X]
    (representative : MulAction.orbitRel.Quotient G X -> X)
    (hrepresentative : Function.LeftInverse Quotient.mk'' representative)
    (h : G) (E : A -> A -> X) :
    let coordinates := MulAction.selfEquivOrbitsQuotientProd' hrepresentative
      (fun x => IsCancelSMul.stabilizer_eq_bot x)
    (forall a,
        (Quotient.mk'' (h • E a a) : MulAction.orbitRel.Quotient G X) =
          Quotient.mk'' (E a a)) /\
      (forall a, (coordinates (h • E a a)).2 = h * (coordinates (E a a)).2) /\
      (h ≠ 1 -> forall a, h • E a a ≠ E a a) := by
  dsimp only
  let coordinates := MulAction.selfEquivOrbitsQuotientProd' hrepresentative
    (fun x => IsCancelSMul.stabilizer_eq_bot x)
  constructor
  · intro a
    apply Quotient.sound
    exact ⟨h, rfl⟩
  constructor
  · intro a
    let x := E a a
    apply_fun fun g => g • representative (Quotient.mk'' x)
    · change (coordinates (h • x)).2 • representative (Quotient.mk'' x) =
        (h * (coordinates x).2) • representative (Quotient.mk'' x)
      have hfirst : (coordinates (h • x)).1 = Quotient.mk'' x := by
        change Quotient.mk'' (h • x) = Quotient.mk'' x
        apply Quotient.sound
        exact ⟨h, rfl⟩
      have hreconstruct (y : X) :
          (coordinates y).2 • representative ((coordinates y).1) = y := by
        change coordinates.symm (coordinates y) = y
        exact coordinates.symm_apply_apply y
      calc
        (coordinates (h • x)).2 • representative (Quotient.mk'' x) =
            (coordinates (h • x)).2 • representative ((coordinates (h • x)).1) := by
              rw [hfirst]
        _ = h • x := hreconstruct (h • x)
        _ = h • ((coordinates x).2 • representative ((coordinates x).1)) := by
          rw [hreconstruct x]
        _ = h • ((coordinates x).2 • representative (Quotient.mk'' x)) := by rfl
        _ = (h * (coordinates x).2) • representative (Quotient.mk'' x) := by
          rw [mul_smul]
    · exact fun g k hgk =>
        IsCancelSMul.right_cancel g k (representative (Quotient.mk'' x)) hgk
  · intro hne a heq
    exact hne (IsCancelSMul.eq_one_of_smul heq)

example : IsCancelSMul (Multiplicative ℤ) (Multiplicative ℤ) := by infer_instance

example :
    ∃ representative :
        MulAction.orbitRel.Quotient (Multiplicative ℤ) (Multiplicative ℤ) -> Multiplicative ℤ,
      Function.LeftInverse Quotient.mk'' representative := by
  refine ⟨fun _ => 1, ?_⟩
  intro orbit
  refine Quotient.inductionOn' orbit (fun x => ?_)
  apply Quotient.sound
  exact ⟨x⁻¹, by simp⟩

example : Nonempty Unit /\ Nonempty (Unit -> Unit -> Unit) :=
  ⟨⟨()⟩, ⟨fun _ _ => ()⟩⟩

example {G : Type u} {X : Type v} {A : Type w}
    [Group G] [MulAction G X] [IsCancelSMul G X]
    (representative : MulAction.orbitRel.Quotient G X -> X)
    (hrepresentative : Function.LeftInverse Quotient.mk'' representative)
    (h : G) (E : A -> A -> X) :
    let coordinates := MulAction.selfEquivOrbitsQuotientProd' hrepresentative
      (fun x => IsCancelSMul.stabilizer_eq_bot x)
    (forall a,
        (Quotient.mk'' (h • E a a) : MulAction.orbitRel.Quotient G X) =
          Quotient.mk'' (E a a)) /\
      (forall a, (coordinates (h • E a a)).2 = h * (coordinates (E a a)).2) /\
      (h ≠ 1 -> forall a, h • E a a ≠ E a a) := by
  fail_if_success rfl
  exact group_valued_diagonal_escape representative hrepresentative h E

#print axioms group_valued_diagonal_escape

end D5.S3.QuantumContext.GroupValuedDiagonalEscape
