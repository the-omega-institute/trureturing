/- GID: D5/S3/Factorization/Collinear/AffineGraphTranslationStabilizer
   generality: G
   mirror-B: D5/B/S3/Factorization/Collinear/AffineGraphTranslationStabilizer
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: An affine graph stabilizer is the slope lift of its abscissa stabilizer. -/

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Tactic

namespace D5.S3.Factorization.Collinear.AffineGraphTranslationStabilizer

open scoped Pointwise

/-- The graph of an affine map restricted to a finite set. -/
def affineGraph {R : Type*} [CommRing R] [DecidableEq R]
    (a b : R) (X : Finset R) : Finset (R × R) :=
  X.image (fun x => (x, a * x + b))

/-- The slope graph as an additive homomorphism. -/
def slopeHom {R : Type*} [CommRing R] (a : R) : R →+ R × R where
  toFun h := (h, a * h)
  map_zero' := by simp
  map_add' h k := by ext <;> simp [mul_add]

private theorem affineGraph_fst {R : Type*} [CommRing R] [DecidableEq R]
    (a b : R) (X : Finset R) :
    (affineGraph a b X).image Prod.fst = X := by
  simp [affineGraph, Finset.image_image, Function.comp_def]

private theorem affineGraph_vadd {R : Type*} [CommRing R] [DecidableEq R]
    (a b h k : R) (X : Finset R) :
    (h, k) +ᵥ affineGraph a b X =
      affineGraph a (b + k - a * h) (X.image (h + ·)) := by
  rw [Finset.vadd_finset_def]
  ext z
  simp only [affineGraph, Finset.mem_image]
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨h + x, ⟨x, hx, rfl⟩, ?_⟩
    apply Prod.ext
    · rfl
    · dsimp
      ring
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(x, a * x + b), ⟨x, hx, rfl⟩, ?_⟩
    apply Prod.ext
    · rfl
    · dsimp
      ring

private theorem affineGraph_vadd_eq_iff {R : Type*} [CommRing R] [DecidableEq R]
    (a b h k : R) (X : Finset R) (hX : X.Nonempty) :
    (h, k) +ᵥ affineGraph a b X = affineGraph a b X ↔
      X.image (h + ·) = X ∧ k = a * h := by
  constructor
  · intro hfixed
    have hshift : X.image (h + ·) = X := by
      have hp := congrArg (Finset.image Prod.fst) hfixed
      rw [affineGraph_vadd, affineGraph_fst, affineGraph_fst] at hp
      exact hp
    have hgraph : affineGraph a (b + k - a * h) X = affineGraph a b X := by
      simpa only [affineGraph_vadd, hshift] using hfixed
    obtain ⟨x, hx⟩ := hX
    have hmem : (x, a * x + (b + k - a * h)) ∈ affineGraph a b X := by
      rw [← hgraph]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hmem with ⟨y, _, hxy⟩
    have hy : y = x := by simpa using congrArg Prod.fst hxy
    have hsecond : a * x + (b + k - a * h) = a * x + b := by
      simpa only [hy] using (congrArg Prod.snd hxy).symm
    refine ⟨hshift, ?_⟩
    linear_combination hsecond
  · rintro ⟨hshift, hk⟩
    rw [affineGraph_vadd, hshift]
    have hb : b + k - a * h = b := by rw [hk]; ring
    rw [hb]

/-- An affine graph has exactly the translation symmetries obtained by lifting
the translation symmetries of its nonempty abscissa set along its slope. -/
theorem affineGraph_stabilizer_eq_map {R : Type*} [CommRing R] [DecidableEq R]
    (a b : R) (X : Finset R) (hX : X.Nonempty) :
    AddAction.stabilizer (R × R) (affineGraph a b X) =
      (AddAction.stabilizer R X).map (slopeHom a) := by
  ext t
  constructor
  · intro ht
    have hcriterion := (affineGraph_vadd_eq_iff a b t.1 t.2 X hX).mp ht
    apply AddSubgroup.mem_map.mpr
    refine ⟨t.1, hcriterion.1, ?_⟩
    exact Prod.ext rfl hcriterion.2.symm
  · intro ht
    rcases AddSubgroup.mem_map.mp ht with ⟨h, hh, rfl⟩
    apply (affineGraph_vadd_eq_iff a b h (a * h) X hX).mpr
    exact ⟨hh, rfl⟩

end D5.S3.Factorization.Collinear.AffineGraphTranslationStabilizer
