/- GID: D5/S3/FiniteGroups/NikolovSegal/InvariantBlockReduction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/InvariantBlockReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equivariant products combine ordered commutator-value coverage with the same q and m. -/

import D5.S3.FiniteGroups.NikolovSegal.CosetPowerBridge
import Mathlib.Algebra.Group.Pi.Lemmas

set_option autoImplicit false

namespace NikolovSegal

universe u v w

/-- Actual ordered value-set coverage combines across invariant product blocks.
`e` may identify a group with its orbit blocks; `equivariant` requires the
prescribed automorphisms to preserve each block and have the displayed action.
The same `q,m` work in every block and in the full product. This theorem does
not assume or conclude mere subgroup generation. -/
theorem prescribed_coverage_of_equivariant_product
    {A : Type u} [Group A] {ι : Type v} {S : ι → Type w} [∀ r, Group (S r)]
    (q m : ℕ) (k : Fin m → MulAut A) (l : ∀ r, Fin m → MulAut (S r))
    (e : A ≃* (∀ r, S r))
    (equivariant : ∀ i x r, e (k i x) r = l r i (e x r))
    (blocks : ∀ r, PrescribedCommutatorCoverage (S r) q m (l r)) :
    PrescribedCommutatorCoverage A q m k := by
  classical
  choose y hy using blocks
  let yA : Fin m → A := fun i => e.symm (fun r => y r i)
  refine ⟨yA, ?_⟩
  intro t
  choose c hc using fun r => hy r (e t r)
  let cA : Fin m → A := fun i => e.symm (fun r => c r i)
  refine ⟨cA, ?_⟩
  apply e.injective
  funext r
  let π : A →* S r := (Pi.evalMonoidHom S r).comp e.toMonoidHom
  have hα (i : Fin m) (x : A) :
      π ((k i * MulAut.conj (yA i)⁻¹) x) =
        (l r i * MulAut.conj (y r i)⁻¹) (π x) := by
    simp only [MulAut.mul_apply]
    change e (k i (MulAut.conj (yA i)⁻¹ x)) r = _
    rw [equivariant]
    simp [π, yA]
  have hpow (i : Fin m) (n : ℕ) (x : A) :
      π (((k i * MulAut.conj (yA i)⁻¹) ^ n) x) =
        ((l r i * MulAut.conj (y r i)⁻¹) ^ n) (π x) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change π ((k i * MulAut.conj (yA i)⁻¹)
        (((k i * MulAut.conj (yA i)⁻¹) ^ n) x)) =
        (l r i * MulAut.conj (y r i)⁻¹)
          (((l r i * MulAut.conj (y r i)⁻¹) ^ n) (π x))
      rw [hα, ih]
  change π (orderedProduct (fun i => (cA i)⁻¹ *
    ((k i * MulAut.conj (yA i)⁻¹) ^ q) (cA i))) = π t
  have hmap (f : Fin m → A) :
      π (orderedProduct f) = orderedProduct (fun i => π (f i)) := by
    simp [orderedProduct, map_list_prod, List.map_ofFn, Function.comp_def]
  rw [hmap]
  have hval (i : Fin m) :
      π ((cA i)⁻¹ * ((k i * MulAut.conj (yA i)⁻¹) ^ q) (cA i)) =
        (c r i)⁻¹ * ((l r i * MulAut.conj (y r i)⁻¹) ^ q) (c r i) := by
    rw [map_mul, map_inv, hpow]
    have hcA : π (cA i) = c r i := by simp [π, cA]
    rw [hcA]
  simp_rw [hval]
  exact hc r

end NikolovSegal
