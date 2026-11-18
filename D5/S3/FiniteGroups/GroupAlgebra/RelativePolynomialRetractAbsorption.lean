/- GID: D5/S3/FiniteGroups/GroupAlgebra/RelativePolynomialRetractAbsorption
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/RelativePolynomialRetractAbsorption
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Intertwining]
   utility: none
   digest: A split polynomial copy absorbs all remaining relative stable summands. -/

import D5.S3.FiniteGroups.GroupAlgebra.EmbeddedPolynomialCancellation

/-!
The polynomial scalar and automorphism arguments are reused from
EmbeddedPolynomialCancellation. The new inference concerns a chosen actual
split copy inside an arbitrary representation already relatively stably
isomorphic to that polynomial module. The complementary projector factors
through an original relatively projective module, without any finiteness
restriction on the ambient representation or the factorization witnesses.

Intended consumer: the symmetric-power complement after Elmer--Kadr Lemma 3.9,
DOI 10.1007/s13366-026-00855-9 / arXiv:2510.07939v1. This source alone does not
assert that symmetric-power application or a new external open-problem solution.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.RelativePolynomialRetractAbsorption

open ElmerKadrTensorCounterexample
open EmbeddedPolynomialCancellation
open ElmerKadrPolynomialCancellation (factors_sandwich)
open Representation (IntertwiningMap)

universe uK uE

variable {K : Type uK} [Field K]
  {E : Type uE} [AddGroup E] [Fintype E] [Nontrivial E]
  (α : E →+ K) (hα : Function.Injective α)
  {p : ℕ} [Fact p.Prime] [CharP K p]
  (s N : ℕ)
  {A : Type uK} [AddCommGroup A] [Module K A]

local notation "V" => (MonoidHom.comp (dualAction K (N + 1)) α.toMultiplicative)
local notation "M" =>
  (MonoidHom.comp (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
    α.toMultiplicative)

include hα in
theorem split_polynomial_retract_absorption
    (hsize : N + 2 ≤ Fintype.card E) (hdim : ((N + 1 : ℕ) : K) ≠ 0)
    (ρ : Representation K (Multiplicative E) A)
    (i : Representation.IntertwiningMap V ρ) (r : ρ.IntertwiningMap V)
    (hri : r.comp i = .id V) (hs : RelativeStableIso M ρ V) :
    RelativeFactors M (.id ρ - i.comp r) := by
  obtain ⟨f, g, hgf, _hfg⟩ := hs
  let D : ρ.IntertwiningMap ρ := g.comp f - .id ρ
  let a : Representation.IntertwiningMap V V := r.comp g
  let b : Representation.IntertwiningMap V V := f.comp i
  have hri_apply (x : DualPower K (N + 1)) : r (i x) = x :=
    congrArg (fun t : Representation.IntertwiningMap V V => t x) hri
  have herror : RelativeFactors M (a.comp b - .id V) := by
    have hf := factors_sandwich M hgf r i
    convert hf using 1
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change r (g (f (i x))) - x = r (g (f (i x)) - i x)
    rw [map_sub, hri_apply]
  have hz := topScalar_relativeFactors_zero α hα s N hsize hdim
    (a.comp b - .id V) herror
  have hid : topScalar α (K := K) N (.id V) = 1 := by
    simp [topScalar, dualBasis]
  have hab : topScalar α N (a.comp b) = 1 := by
    change topScalar α N (a.comp b) - topScalar α N (.id V) = 0 at hz
    rw [hid] at hz
    exact sub_eq_zero.mp hz
  have hb : topScalar α N b ≠ 0 := by
    intro hb
    rw [topScalar_comp α hα N hsize, hb, mul_zero] at hab
    exact zero_ne_one hab
  obtain ⟨e, he⟩ := endomorphism_equiv_of_top_ne_zero α hα N hsize b hb
  let u : Representation.IntertwiningMap V V := e.symm.toIntertwiningMap
  have hbu (x : DualPower K (N + 1)) : f (i (u x)) = x := by
    change b (u x) = x
    rw [← he]
    exact e.apply_symm_apply x
  let Q : ρ.IntertwiningMap ρ := .id ρ - i.comp r
  let B : ρ.IntertwiningMap ρ := i.comp (u.comp f) - .id ρ
  have hDB (x : A) : D (B x) = x - i (u (f x)) := by
    change g (f (i (u (f x)) - x)) - (i (u (f x)) - x) = _
    rw [map_sub, hbu, map_sub]
    abel
  have hQi (x : DualPower K (N + 1)) : Q (i x) = 0 := by
    change i x - i (r (i x)) = 0
    rw [hri_apply, sub_self]
  have hQ : (Q.comp D).comp B = Q := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change Q (D (B x)) = Q x
    rw [hDB, map_sub, hQi, sub_zero]
  have hf := factors_sandwich M hgf Q B
  change RelativeFactors M ((Q.comp D).comp B) at hf
  rw [hQ] at hf
  exact hf

variable {B : Type uK} [AddCommGroup B] [Module K B]

include hα in
/-- Every intermediate retract containing a split polynomial copy has exactly
that polynomial module's relative stable class. All displayed splittings are
actual equivariant splittings, and all relative witnesses remain unrestricted. -/
theorem intermediate_retract_stable
    (hsize : N + 2 ≤ Fintype.card E) (hdim : ((N + 1 : ℕ) : K) ≠ 0)
    (ρ : Representation K (Multiplicative E) A)
    (σ : Representation K (Multiplicative E) B)
    (j : σ.IntertwiningMap ρ) (q : ρ.IntertwiningMap σ)
    (hqj : q.comp j = .id σ)
    (i : Representation.IntertwiningMap V σ) (r : σ.IntertwiningMap V)
    (hri : r.comp i = .id V) (hs : RelativeStableIso M ρ V) :
    RelativeStableIso M σ V := by
  have hqj_apply (x : B) : q (j x) = x :=
    congrArg (fun t : σ.IntertwiningMap σ => t x) hqj
  have hri_apply (x : DualPower K (N + 1)) : r (i x) = x :=
    congrArg (fun t : Representation.IntertwiningMap V V => t x) hri
  have hleft : (r.comp q).comp (j.comp i) = .id V := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change r (q (j (i x))) = x
    rw [hqj_apply, hri_apply]
  have hT := split_polynomial_retract_absorption α hα s N hsize hdim
    ρ (j.comp i) (r.comp q) hleft hs
  have hS : RelativeFactors M (.id σ - i.comp r) := by
    have hf := factors_sandwich M hT q j
    convert hf using 1
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change x - i (r x) = q (j x - j (i (r (q (j x)))))
    simp only [map_sub, hqj_apply]
  refine ⟨r, i, ?_, ?_⟩
  · have hf := factors_sandwich M hS (-.id σ) (.id σ)
    convert hf using 1
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change i (r x) - x = -(x - i (r x))
    abel
  · rw [hri, sub_self]
    exact ElmerKadrPositiveCriterion.relativeFactors_zero M V V

end D5.S3.FiniteGroups.GroupAlgebra.RelativePolynomialRetractAbsorption
