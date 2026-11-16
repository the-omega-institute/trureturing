/- GID: D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer
   generality: G
   mirror-B: none(waiver:no-separate-boolean-mirror-claimed)
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Subgroup, mathlib/module/Mathlib.GroupTheory.Subgroup.Centralizer]
   utility: none
   digest: The ambient normalizer of diagonal left translations has unique permutation, common automorphism and source-indexed right-translation coordinates over arbitrary nonempty label types and groups. -/

import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Logic.Equiv.Prod

/-!
# Coordinates of the diagonal regular normalizer

For arbitrary types `K` and `H` with `[Group H]`, `diagonal K H` is the range
of the simultaneous left translations `(i, x) ↦ (i, h * x)` in
`Equiv.Perm (K × H)`. Its normalizer is taken in this actual ambient group.

When `K` is nonempty, every normalizing permutation has unique coordinates
`(sigma, alpha, b) : Equiv.Perm K × MulAut H × (K → H)` and acts by
`(i, x) ↦ (sigma i, alpha x * b i)`. The automorphism is common to all labels;
`b i` is a right translation indexed by the source label. `normalizerEquiv`
is an equivalence of types, with evaluation in `normalizerEquiv_eval` and full
membership classification in `mem_normalizer_iff_existsUnique_coordinates`.
There are no finiteness or nontriviality hypotheses.

The proof uses `Equiv.Perm.subgroupOfMulAction` for the faithful diagonal
range equivalence, `Subgroup.normalizerMonoidHom` and `MulAut.congr` for
conjugation, and `Equiv.prodCongrRight` for the coordinate permutations.
The coordinate reconstruction proves the label map bijective without a
finiteness argument. Nonempty labels recover the common automorphism in the
uniqueness proof; no multiplication on the coordinate type is specified.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.DiagonalRegularNormalizer

universe u v

variable (K : Type u) (H : Type v) [Group H]

-- Kept as a definition, never a global instance: the H-action on H stays regular.
private def labelAction : MulAction H K where
  smul _ i := i
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def diagonalHom : H →* Equiv.Perm (K × H) := by
  letI : MulAction H K := labelAction K H
  exact MulAction.toPermHom H (K × H)

private theorem diagonalHom_apply (h : H) (z : K × H) :
    diagonalHom K H h z = (z.1, h * z.2) := rfl

def diagonal : Subgroup (Equiv.Perm (K × H)) :=
  (diagonalHom K H).range

abbrev diagonalNormalizer : Subgroup (Equiv.Perm (K × H)) :=
  Subgroup.normalizer (diagonal K H : Set (Equiv.Perm (K × H)))

-- This is only a parameter TYPE. No multiplication on triples is proposed.
abbrev Parameters := Equiv.Perm K × MulAut H × (K → H)

def coordinatePerm (t : Parameters K H) : Equiv.Perm (K × H) :=
  (Equiv.prodCongrRight fun i : K =>
    t.2.1.toEquiv.trans (Equiv.mulRight (t.2.2 i))).trans
      (Equiv.prodCongr t.1 (Equiv.refl H))

private theorem coordinatePerm_apply (t : Parameters K H) (z : K × H) :
    coordinatePerm K H t z = (t.1 z.1, t.2.1 z.2 * t.2.2 z.1) := rfl

/- Twisted equivariance determines a label map and right translations. Its
first-coordinate map is proved bijective from the ambient permutation.
This reconstruction does not require Nonempty K. -/
private theorem coordinates_of_twisted
    (p : Equiv.Perm (K × H)) (alpha : MulAut H)
    (ht : ∀ (h : H) (i : K) (x : H),
      p (i, h * x) = ((p (i, x)).1, alpha h * (p (i, x)).2)) :
    ∃ (sigma : Equiv.Perm K) (b : K → H),
      ∀ (i : K) (x : H), p (i, x) = (sigma i, alpha x * b i) := by
  let k : K → K := fun i => (p (i, 1)).1
  let b : K → H := fun i => (p (i, 1)).2
  have hcoord (i : K) (x : H) : p (i, x) = (k i, alpha x * b i) := by
    simpa [k, b] using ht x i 1
  have hkinj : Function.Injective k := by
    intro i j hij
    let x : H := alpha.symm (b i * (b j)⁻¹)
    have hx : alpha x * b j = b i := by
      simp [x, mul_assoc]
    have hp : p (j, x) = p (i, 1) := by
      rw [hcoord j x, hcoord i 1]
      apply Prod.ext
      · exact hij.symm
      · simpa using hx
    exact (congrArg Prod.fst (p.injective hp)).symm
  have hksurj : Function.Surjective k := by
    intro j
    obtain ⟨⟨i, x⟩, hi⟩ := p.surjective (j, 1)
    exact ⟨i, congrArg Prod.fst ((hcoord i x).symm.trans hi)⟩
  refine ⟨Equiv.ofBijective k ⟨hkinj, hksurj⟩, b, ?_⟩
  intro i x
  exact hcoord i x

-- An actual ambient permutation, with its conjugation computed in that group.
private theorem coordinatePerm_conj (t : Parameters K H) (h : H) :
    coordinatePerm K H t * diagonalHom K H h * (coordinatePerm K H t)⁻¹ =
      diagonalHom K H (t.2.1 h) := by
  have ht : coordinatePerm K H t * diagonalHom K H h =
      diagonalHom K H (t.2.1 h) * coordinatePerm K H t := by
    apply Equiv.ext
    rintro ⟨i, x⟩
    simp only [Equiv.Perm.mul_apply, diagonalHom_apply, coordinatePerm_apply,
      map_mul, mul_assoc]
  calc
    coordinatePerm K H t * diagonalHom K H h * (coordinatePerm K H t)⁻¹ =
        (diagonalHom K H (t.2.1 h) * coordinatePerm K H t) *
          (coordinatePerm K H t)⁻¹ :=
      congrArg (fun q => q * (coordinatePerm K H t)⁻¹) ht
    _ = diagonalHom K H (t.2.1 h) := by
      rw [mul_assoc, mul_inv_cancel, mul_one]

private theorem coordinatePerm_mem_normalizer (t : Parameters K H) :
    coordinatePerm K H t ∈ diagonalNormalizer K H := by
  apply Subgroup.mem_set_normalizer_iff.mpr
  intro q
  change (∃ h : H, diagonalHom K H h = q) ↔
    (∃ h : H, diagonalHom K H h =
      coordinatePerm K H t * q * (coordinatePerm K H t)⁻¹)
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨t.2.1 h, (coordinatePerm_conj K H t h).symm⟩
  · rintro ⟨h, hh⟩
    have he :
        coordinatePerm K H t * diagonalHom K H (t.2.1.symm h) *
            (coordinatePerm K H t)⁻¹ =
          coordinatePerm K H t * q * (coordinatePerm K H t)⁻¹ := by
      calc
        coordinatePerm K H t * diagonalHom K H (t.2.1.symm h) *
            (coordinatePerm K H t)⁻¹ = diagonalHom K H h := by
          simpa only [MulEquiv.apply_symm_apply] using
            coordinatePerm_conj K H t (t.2.1.symm h)
        _ = coordinatePerm K H t * q * (coordinatePerm K H t)⁻¹ := hh
    exact ⟨t.2.1.symm h, mul_left_cancel (mul_right_cancel he)⟩

section NonemptyLabels

variable [Nonempty K]

-- The faithful diagonal action identifies H with its actual range.
private def diagonalEquiv : H ≃* diagonal K H := by
  letI : MulAction H K := labelAction K H
  exact Equiv.Perm.subgroupOfMulAction H (K × H)

private theorem diagonalEquiv_coe (h : H) :
    ((diagonalEquiv K H h : diagonal K H) : Equiv.Perm (K × H)) =
      diagonalHom K H h := rfl

-- Transport the normalizer conjugation automorphism from the diagonal range.
-- The resulting alpha is fixed before any label is chosen.
private def normalizerAlpha (p : diagonalNormalizer K H) : MulAut H :=
  (MulAut.congr (diagonalEquiv K H).symm)
    ((diagonal K H).normalizerMonoidHom p)

/- The normalizer action is conjugation in the ambient permutation group;
subgroupOfMulAction has diagonalHom as its forward map. Transporting this
action gives L_(alpha h) = p * L_h * p^-1. -/
private theorem normalizerAlpha_conj
    (p : diagonalNormalizer K H) (h : H) :
    diagonalHom K H (normalizerAlpha K H p h) =
      (p : Equiv.Perm (K × H)) * diagonalHom K H h *
        (p : Equiv.Perm (K × H))⁻¹ := by
  have htransport :
      diagonalEquiv K H (normalizerAlpha K H p h) =
        (diagonal K H).normalizerMonoidHom p (diagonalEquiv K H h) := by
    change diagonalEquiv K H
      ((diagonalEquiv K H).symm
        ((diagonal K H).normalizerMonoidHom p (diagonalEquiv K H h))) = _
    exact (diagonalEquiv K H).apply_symm_apply _
  have hval := congrArg
    (fun d : diagonal K H => (d : Equiv.Perm (K × H))) htransport
  change
    ((diagonalEquiv K H (normalizerAlpha K H p h) : diagonal K H) :
      Equiv.Perm (K × H)) =
    (p : Equiv.Perm (K × H)) *
      ((diagonalEquiv K H h : diagonal K H) : Equiv.Perm (K × H)) *
      (p : Equiv.Perm (K × H))⁻¹ at hval
  simpa only [diagonalEquiv_coe] using hval

private theorem normalizer_twisted
    (p : diagonalNormalizer K H) (h : H) (i : K) (x : H) :
    (p : Equiv.Perm (K × H)) (i, h * x) =
      (((p : Equiv.Perm (K × H)) (i, x)).1,
        normalizerAlpha K H p h * ((p : Equiv.Perm (K × H)) (i, x)).2) := by
  have he : (p : Equiv.Perm (K × H)) * diagonalHom K H h =
      diagonalHom K H (normalizerAlpha K H p h) *
        (p : Equiv.Perm (K × H)) := by
    calc
      (p : Equiv.Perm (K × H)) * diagonalHom K H h =
          ((p : Equiv.Perm (K × H)) * diagonalHom K H h *
              (p : Equiv.Perm (K × H))⁻¹) *
            (p : Equiv.Perm (K × H)) := by
        simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = diagonalHom K H (normalizerAlpha K H p h) *
          (p : Equiv.Perm (K × H)) := by
        rw [← normalizerAlpha_conj K H p h]
  have hv := congrArg (fun q : Equiv.Perm (K × H) => q (i, x)) he
  simpa only [Equiv.Perm.mul_apply, diagonalHom_apply] using hv

private theorem normalizer_has_coordinates (p : diagonalNormalizer K H) :
    ∃ t : Parameters K H, coordinatePerm K H t = (p : Equiv.Perm (K × H)) := by
  obtain ⟨sigma, b, hcoord⟩ := coordinates_of_twisted K H
    (p : Equiv.Perm (K × H)) (normalizerAlpha K H p)
      (normalizer_twisted K H p)
  refine ⟨(sigma, normalizerAlpha K H p, b), ?_⟩
  apply Equiv.ext
  rintro ⟨i, x⟩
  exact (hcoord i x).symm

/- Parameter uniqueness, including trivial H. Nonempty K is used only after
recovering sigma and b: right cancellation at one label recovers all of alpha.
With empty K this uniform uniqueness statement is false for general H. -/
private theorem coordinatePerm_injective :
    Function.Injective (coordinatePerm K H) := by
  rintro ⟨sigma, alpha, b⟩ ⟨tau, beta, c⟩ hp
  have h (i : K) (x : H) :
      (sigma i, alpha x * b i) = (tau i, beta x * c i) :=
    congrArg (fun q : Equiv.Perm (K × H) => q (i, x)) hp
  have hs : sigma = tau := by
    apply Equiv.ext
    intro i
    exact congrArg Prod.fst (h i 1)
  have hb : b = c := by
    funext i
    simpa only [map_one, one_mul] using congrArg Prod.snd (h i 1)
  have ha : alpha = beta := by
    apply MulEquiv.ext
    intro x
    let i : K := Classical.choice (inferInstance : Nonempty K)
    have hx := congrArg Prod.snd (h i x)
    rw [hb] at hx
    exact mul_right_cancel hx
  exact Prod.ext hs (Prod.ext ha hb)

private def toNormalizer (t : Parameters K H) : diagonalNormalizer K H :=
  ⟨coordinatePerm K H t, coordinatePerm_mem_normalizer K H t⟩

private theorem toNormalizer_bijective :
    Function.Bijective (toNormalizer K H) := by
  constructor
  · intro s t hst
    exact coordinatePerm_injective K H
      (congrArg (fun p : diagonalNormalizer K H =>
        (p : Equiv.Perm (K × H))) hst)
  · intro p
    obtain ⟨t, ht⟩ := normalizer_has_coordinates K H p
    exact ⟨t, Subtype.ext ht⟩

/-- The actual diagonal normalizer is equivalent as a type to its unique coordinates. -/
def normalizerEquiv : diagonalNormalizer K H ≃ Parameters K H :=
  (Equiv.ofBijective (toNormalizer K H) (toNormalizer_bijective K H)).symm

/-- Evaluation of an ambient normalizer element in its permutation, automorphism and right-translation coordinates. -/
theorem normalizerEquiv_eval
    (p : diagonalNormalizer K H) (i : K) (x : H) :
    (p : Equiv.Perm (K × H)) (i, x) =
      ((normalizerEquiv K H p).1 i,
        (normalizerEquiv K H p).2.1 x * (normalizerEquiv K H p).2.2 i) := by
  have hp : toNormalizer K H (normalizerEquiv K H p) = p :=
    (Equiv.ofBijective (toNormalizer K H) (toNormalizer_bijective K H)).apply_symm_apply p
  exact congrArg (fun q : diagonalNormalizer K H =>
    (q : Equiv.Perm (K × H)) (i, x)) hp.symm

/-- Ambient diagonal-normalizer membership is equivalent to unique coordinates
with one common automorphism and source-indexed right translations. -/
theorem mem_normalizer_iff_existsUnique_coordinates
    (p : Equiv.Perm (K × H)) :
    p ∈ Subgroup.normalizer (diagonal K H : Set (Equiv.Perm (K × H))) ↔
      ∃! t : Parameters K H, ∀ (i : K) (x : H),
        p (i, x) = (t.1 i, t.2.1 x * t.2.2 i) := by
  constructor
  · intro hp
    let pn : diagonalNormalizer K H := ⟨p, hp⟩
    refine ⟨normalizerEquiv K H pn, ?_, ?_⟩
    · intro i x
      exact normalizerEquiv_eval K H pn i x
    · intro t ht
      apply coordinatePerm_injective K H
      apply Equiv.ext
      rintro ⟨i, x⟩
      calc
        coordinatePerm K H t (i, x) = p (i, x) := (ht i x).symm
        _ = coordinatePerm K H (normalizerEquiv K H pn) (i, x) :=
          normalizerEquiv_eval K H pn i x
  · rintro ⟨t, ht, _⟩
    have hp : p = coordinatePerm K H t := by
      apply Equiv.ext
      rintro ⟨i, x⟩
      exact ht i x
    rw [hp]
    exact coordinatePerm_mem_normalizer K H t

end NonemptyLabels

end D5.S3.FiniteGroups.DiagonalRegularNormalizer
