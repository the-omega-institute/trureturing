/- GID: D5/S1/Deficit/Cocycles/ExtensionSectionCoboundary
   generality: G
   mirror-B: D5/B/S1/Deficit/Cocycles/ExtensionSectionCoboundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An additive section exists exactly when the canonical kernel carry is an additive coboundary. -/

import D5.S1.Deficit.Cocycles.AdditiveCarryCocycle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Deficit.Cocycles.ExtensionSectionCoboundary

open D5.S1.Deficit.Cocycles.AdditiveCarryCocycle

/- The coboundary is formed in the canonical kernel carrier of the quotient map. -/
def additiveCoboundary {X B : Type*} [AddCommGroup X] [AddCommGroup B]
    (quotient : AddMonoidHom X B) (beta : B -> quotient.ker) (a b : B) : quotient.ker :=
  beta a + beta b - beta (a + b)

theorem extension_section_iff_coboundary
    {X B : Type*} [AddCommGroup X] [AddCommGroup B]
    (quotient : AddMonoidHom X B) (representative : B -> X)
    (hsection : Function.RightInverse representative quotient)
    (hzero : representative 0 = 0) :
    ((∃ s' : B →+ X, Function.RightInverse s' quotient) ↔
      ∃ beta : B → quotient.ker, ∀ a b : B,
        kernelCarry quotient representative hsection a b +
            additiveCoboundary quotient beta a b = 0) ∧
    ((¬ (∃ beta : B → quotient.ker, ∀ a b : B,
        kernelCarry quotient representative hsection a b +
            additiveCoboundary quotient beta a b = 0)) ->
      ¬ (∃ s' : B →+ X, Function.RightInverse s' quotient)) := by
  have hcarry_zero : kernelCarry quotient representative hsection 0 0 = 0 := by
    apply Subtype.ext
    simp [kernelCarry, sectionCarry, hzero]
  have hforward :
      (∃ s' : B →+ X, Function.RightInverse s' quotient) →
        ∃ beta : B → quotient.ker, ∀ a b : B,
          kernelCarry quotient representative hsection a b +
              additiveCoboundary quotient beta a b = 0 := by
    rintro ⟨s', hs'⟩
    let beta : B → quotient.ker := fun a =>
      ⟨s' a - representative a, by
        change quotient (s' a - representative a) = 0
        rw [map_sub, hs' a, hsection a]
        simp⟩
    refine ⟨beta, ?_⟩
    intro a b
    apply Subtype.ext
    change (representative a + representative b - representative (a + b)) +
      ((s' a - representative a) + (s' b - representative b) -
        (s' (a + b) - representative (a + b))) = 0
    rw [s'.map_add]
    abel
  have hbackward :
      (∃ beta : B → quotient.ker, ∀ a b : B,
        kernelCarry quotient representative hsection a b +
            additiveCoboundary quotient beta a b = 0) →
      ∃ s' : B →+ X, Function.RightInverse s' quotient := by
    rintro ⟨beta, hbeta⟩
    have hbeta_zero : beta 0 = 0 := by
      have h := congrArg Subtype.val (hbeta 0 0)
      simpa [additiveCoboundary, kernelCarry, sectionCarry, hzero] using h
    let candidate : B → X := fun a => representative a + beta a
    let sectionHom : B →+ X :=
      { toFun := candidate
        map_zero' := by simp [candidate, hzero, hbeta_zero]
        map_add' := by
          intro a b
          have h := congrArg Subtype.val (hbeta a b)
          have hraw :
              (representative a + representative b - representative (a + b)) +
                (beta a + beta b - beta (a + b) : X) = 0 := by
            simpa [additiveCoboundary, kernelCarry, sectionCarry] using h
          apply (sub_eq_zero.mp ?_).symm
          calc
            (candidate a + candidate b) - candidate (a + b) =
                (representative a + representative b - representative (a + b)) +
                  (beta a + beta b - beta (a + b) : X) := by
              dsimp [candidate]
              abel
            _ = 0 := hraw }
    refine ⟨sectionHom, ?_⟩
    intro a
    change quotient (representative a + beta a) = a
    rw [map_add, hsection a]
    have hker : quotient (beta a) = 0 := by
      simpa only [AddMonoidHom.mem_ker] using (beta a).property
    simp [hker]
  refine ⟨⟨hforward, hbackward⟩, ?_⟩
  intro hnonzero hs'
  exact hnonzero (hforward hs')

/- The identity quotient supplies a concrete split extension and zero carry. -/
example :
    ∃ s' : Int →+ Int, Function.RightInverse s' (AddMonoidHom.id Int) := by
  refine ⟨AddMonoidHom.id Int, ?_⟩
  intro z
  rfl

#print axioms extension_section_iff_coboundary

end D5.S1.Deficit.Cocycles.ExtensionSectionCoboundary
