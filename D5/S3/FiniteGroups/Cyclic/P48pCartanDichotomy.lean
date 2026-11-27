/- GID: D5/S3/FiniteGroups/Cyclic/P48pCartanDichotomy
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/P48pCartanDichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The real Cartan representation for P48p is reducible or has a pure cubic. -/

import D5.S3.FiniteGroups.Cyclic.P48pNormalFactorReducibility
import D5.S3.FiniteGroups.Cyclic.RealIrreducibleDegreeBound
import OmegaBuild.Commands

/-!
Nebe (arXiv:1212.0865, Theorem 3.6) gives the group structure for P48p.
Theorem 4.4 and Proposition 4.8 describe prime-order fixed spaces.
The pure cubic rank condition is an explicit hypothesis here, and the ambient
size constraint is expressed as divisibility of the normal factor's index.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace ExtremalC48

local notation "SL23" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 23)

/-- In the irreducible real Cartan case, the image of the normal factor contains
the negative identity and the factor contains an element of order three with
fixed space of real dimension sixteen. -/
theorem p48p_real_cartan_dichotomy
    {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (K : Subgroup H) [K.Normal] (ρ : Representation ℝ H V)
    (hdim : Module.finrank ℝ V = 48)
    (hcard : Nat.card K ∣ 2 ^ 4 * 3 * 11 * 23) (hindex : K.index ∣ 12)
    (φ : K →* SL23) (hφ : Function.Injective φ)
    (hfix : ∀ x : K, (orderOf x = 3 ∨ orderOf x = 11 ∨ orderOf x = 23) →
      LinearMap.ker (ρ (x : H) - 1) ≠ ⊥ ∧ LinearMap.ker (ρ (x : H) - 1) ≠ ⊤)
    (hcubic : ∀ x : K, orderOf x = 3 →
      Module.finrank ℝ (LinearMap.ker (ρ (x : H) - 1)) = 16) :
    (∃ W : Submodule ℝ V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g, W ≤ W.comap (ρ g)) ∨
      (-(1 : SL23) ∈ φ.range ∧
        ∃ x : K, orderOf x = 3 ∧ Module.finrank ℝ (LinearMap.ker (ρ (x : H) - 1)) = 16) := by
  classical
  by_cases hred : ∃ W : Submodule ℝ V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g, W ≤ W.comap (ρ g)
  · exact Or.inl hred
  refine Or.inr ⟨?_, ?_⟩
  · by_contra hneg
    have hodd := p48p_factor_odd_of_sl23_embedding_avoids_neg_one K φ hφ hneg
    exact hred (p48p_odd_normal_factor_exists_invariant_subspace
      K ρ hdim hcard hindex hodd hfix)
  · by_contra hno
    obtain ⟨n, hn, hK⟩ := p48p_irreducible_normal_factor_card_power_of_two
      K ρ hcard (fun x hx => hfix x (Or.inr hx)) hcubic hno hred
    have hsmall : Nat.card K ≤ 16 := by
      rw [hK]
      exact Nat.pow_le_pow_right (by decide) hn
    exact hred (p48p_small_factor_exists_real_invariant_subspace K ρ hdim hsmall hindex)

#print axioms p48p_real_cartan_dichotomy

end ExtremalC48
