/- GID: D5/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.OrderOfElement, mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: A cyclic product of an ambient associator detects nonzero carry type and obstructs membership in a subgroup trivializing that associator. -/

import D5.S3.FiniteGroups.Cyclic.CyclicCarryThreeCocycle
import Mathlib.GroupTheory.OrderOfElement
import OmegaBuild.Commands

/-!
For trivial multiplicative coefficients, evaluation on the cyclic generator
and its successive powers cancels every two-cochain coboundary.

Evans–Gannon, arXiv:1804.11145, equation (2.13), give the carry representative
of parameter q with phase exp(2πi q a floor((b+c)/n)/n).
Their equation (2.14) gives generator-flux conformal weight congruent to
q/n² modulo 1/n (with the central charge term removed).
Corollary 2 requires the restriction of the ambient cocycle to the
extension subgroup to be a coboundary.

For P48q, `P48qFiniteActionObstruction.p48q_finite_action_obstruction`
supplies an actual order-three element with twisted weight residue
9ρ ≡ 1 (mod 3), or two independent fixed weight-two states.
In particular ρ = 16/9 gives q = 1 in the above convention.
Application requires the actual ambient associator's pullback to the
generator to be cohomologous to that representative, with the comparison
of the twisted spectrum and cyclic class supplied by the orbifold theory.
-/

compile_only_with_mathlib

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.FiniteGroups.Cyclic.CyclicAssociatorObstruction

open CyclicCarryThreeCocycle (w sum_w)

variable {G C : Type*} [Group G] [CommGroup C]

/-- The inhomogeneous two-cochain differential for trivial coefficient action. -/
def twoCoboundary (β : G → G → C) (a b c : G) : C :=
  (β b c / β (a * b) c) * (β a (b * c) / β a b)

/-- Evaluation of a three-cochain around the cyclic subgroup of a finite-order generator. -/
noncomputable def cyclicProduct (α : G → G → G → C) (g : G) : C :=
  ∏ i ∈ Finset.range (orderOf g), α g (g ^ i) g

/-- Cyclically rotating the middle argument by the generator preserves the product. -/
theorem prod_pow_rotate (g : G) (f : G → C) :
    (∏ i ∈ Finset.range (orderOf g), f (g ^ (i + 1))) =
      ∏ i ∈ Finset.range (orderOf g), f (g ^ i) := by
  have h := Finset.prod_range_div (fun i => f (g ^ i)) (orderOf g)
  simp only [pow_orderOf_eq_one, pow_zero, Finset.prod_div_distrib] at h
  exact div_eq_one.mp (h.trans (div_self' _))

/-- No normalization or cocycle condition on the two-cochain is needed. -/
theorem cyclicProduct_coboundary (β : G → G → C) (g : G) :
    cyclicProduct (twoCoboundary β) g = 1 := by
  simp only [cyclicProduct, twoCoboundary, ← pow_succ', ← pow_succ,
    Finset.prod_mul_distrib, Finset.prod_div_distrib]
  rw [prod_pow_rotate g (fun x => β x g), prod_pow_rotate g (fun x => β g x)]
  simp

/-- Multiplying a three-cochain by an arbitrary two-coboundary leaves its cyclic
product unchanged. -/
theorem cyclicProduct_mul_coboundary (α : G → G → G → C) (β : G → G → C) (g : G) :
    cyclicProduct (fun a b c => α a b c * twoCoboundary β a b c) g =
      cyclicProduct α g := by
  unfold cyclicProduct
  rw [Finset.prod_mul_distrib, show
    (∏ i ∈ Finset.range (orderOf g), twoCoboundary β g (g ^ i) g) = 1
    from cyclicProduct_coboundary β g, mul_one]

/-- The cyclic product is one at every element of a subgroup on which the
ambient cochain is trivialized by a two-cochain. -/
theorem cyclicProduct_eq_one_of_mem (α : G → G → G → C) (H : Subgroup G)
    (β : H → H → C)
    (hβ : ∀ a b c : H, α a.val b.val c.val = twoCoboundary β a b c)
    {g : G} (hg : g ∈ H) : cyclicProduct α g = 1 := by
  let s : H := ⟨g, hg⟩
  calc
    cyclicProduct α g = cyclicProduct (twoCoboundary β) s := by
      unfold cyclicProduct
      rw [Subgroup.orderOf_mk]
      apply Finset.prod_congr rfl
      intro i _
      exact hβ s (s ^ i) s
    _ = 1 := cyclicProduct_coboundary β s

variable {n : ℕ} [NeZero n]

/-- The canonical pullback map from cyclic coordinates to the ambient group. -/
def cyclicPowerHom (g : G) (hg : orderOf g = n) : Multiplicative (ZMod n) →* G where
  toFun a := g ^ a.toAdd.val
  map_one' := by change g ^ (0 : ZMod n).val = 1; simp
  map_mul' a b := by
    change g ^ (a.toAdd + b.toAdd).val = g ^ a.toAdd.val * g ^ b.toAdd.val
    rw [ZMod.val_add]
    have h := pow_mod_orderOf g (a.toAdd.val + b.toAdd.val)
    rw [hg] at h
    rw [h, pow_add]

private theorem cyclicPowerHom_generator (hn : 1 < n) (g : G) (hg : orderOf g = n) :
    cyclicPowerHom g hg (Multiplicative.ofAdd (1 : ZMod n)) = g := by
  change g ^ (1 : ZMod n).val = g
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hn, pow_one]

/-- The multiplicative carry representative obtained from the additive
representative by applying the phase homomorphism. -/
def carryPhase (ζ : C) (hζ : orderOf ζ = n) (t : ZMod n)
    (a b c : Multiplicative (ZMod n)) : C :=
  cyclicPowerHom ζ hζ (Multiplicative.ofAdd (w t a.toAdd b.toAdd c.toAdd))

private theorem cyclicProduct_carryPhase (hn : 1 < n)
    (ζ : C) (hζ : orderOf ζ = n) (t : ZMod n) :
    cyclicProduct (carryPhase ζ hζ t) (Multiplicative.ofAdd (1 : ZMod n)) =
      ζ ^ t.val := by
  have hreindex : (∑ i ∈ Finset.range n, w t 1 (i : ZMod n) 1) =
      ∑ b : ZMod n, w t 1 b 1 := by
    refine Finset.sum_bij (s := Finset.range n) (t := Finset.univ)
      (f := fun i : ℕ => w t 1 (i : ZMod n) 1) (g := fun b : ZMod n => w t 1 b 1)
      (fun i _ => (i : ZMod n)) ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_univ _
    · intro i hi j hj hij
      have h := congrArg ZMod.val hij
      rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hi),
        ZMod.val_natCast_of_lt (Finset.mem_range.mp hj)] at h
      exact h
    · intro b _
      exact ⟨b.val, Finset.mem_range.mpr (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩
    · intro i _
      rfl
  have hsum := hreindex.trans (sum_w hn t)
  unfold cyclicProduct
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  calc
    _ = ∏ i ∈ Finset.range n,
        cyclicPowerHom ζ hζ (Multiplicative.ofAdd (w t 1 (i : ZMod n) 1)) := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [carryPhase, toAdd_pow, toAdd_ofAdd, Nat.smul_one_eq_cast]
    _ = cyclicPowerHom ζ hζ (Multiplicative.ofAdd t) := by
      rw [← map_prod, ← ofAdd_sum, hsum]
    _ = ζ ^ t.val := rfl

/-- An explicit cohomology comparison for the pullback of the actual ambient
three-cochain computes its generator product as the type phase. -/
theorem cyclicProduct_eq_type_phase (hn : 1 < n) (α : G → G → G → C)
    (g : G) (hg : orderOf g = n) (ζ : C) (hζ : orderOf ζ = n) (t : ZMod n)
    (β : Multiplicative (ZMod n) → Multiplicative (ZMod n) → C)
    (hcompare : ∀ a b c, α (cyclicPowerHom g hg a) (cyclicPowerHom g hg b)
        (cyclicPowerHom g hg c) = carryPhase ζ hζ t a b c * twoCoboundary β a b c) :
    cyclicProduct α g = ζ ^ t.val := by
  let x := Multiplicative.ofAdd (1 : ZMod n)
  have hx : orderOf x = n := ZMod.addOrderOf_one n
  have hgen : cyclicPowerHom g hg x = g := cyclicPowerHom_generator hn g hg
  calc
    cyclicProduct α g =
        cyclicProduct (fun a b c => carryPhase ζ hζ t a b c * twoCoboundary β a b c) x := by
      unfold cyclicProduct
      rw [hg, hx]
      apply Finset.prod_congr rfl
      intro i _
      simpa only [map_pow, hgen] using hcompare x (x ^ i) x
    _ = cyclicProduct (carryPhase ζ hζ t) x :=
      cyclicProduct_mul_coboundary (carryPhase ζ hζ t) β x
    _ = ζ ^ t.val := cyclicProduct_carryPhase hn ζ hζ t

/-- An element of nonzero type cannot belong to any subgroup trivializing
the actual ambient associator. The root phase has exact order n. -/
theorem not_mem_of_nonzero_type (hn : 1 < n) (α : G → G → G → C)
    (g : G) (hg : orderOf g = n) (ζ : C) (hζ : orderOf ζ = n)
    (t : ZMod n) (ht : t ≠ 0)
    (β : Multiplicative (ZMod n) → Multiplicative (ZMod n) → C)
    (hcompare : ∀ a b c, α (cyclicPowerHom g hg a) (cyclicPowerHom g hg b)
        (cyclicPowerHom g hg c) = carryPhase ζ hζ t a b c * twoCoboundary β a b c)
    (H : Subgroup G) (γ : H → H → C)
    (hγ : ∀ a b c : H, α a.val b.val c.val = twoCoboundary γ a b c) :
    g ∉ H := by
  intro hmem
  have hphase := cyclicProduct_eq_type_phase hn α g hg ζ hζ t β hcompare
  have htriv := cyclicProduct_eq_one_of_mem α H γ hγ hmem
  have hdvd : n ∣ t.val := by
    have h := orderOf_dvd_iff_pow_eq_one.mpr (hphase.symm.trans htriv)
    simpa only [hζ] using h
  have hz : t.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt t)
  apply ht
  apply ZMod.val_injective n
  simpa using hz

#print axioms prod_pow_rotate
#print axioms cyclicProduct_coboundary
#print axioms cyclicProduct_mul_coboundary
#print axioms cyclicProduct_eq_one_of_mem
#print axioms cyclicProduct_eq_type_phase
#print axioms not_mem_of_nonzero_type

end D5.S3.FiniteGroups.Cyclic.CyclicAssociatorObstruction
