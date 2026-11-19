import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

/-! Cube symmetries transport regularity and Huang-balanced switching signs. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.HuangBalancedSymmetry

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip_adj)
open scoped Classical
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

local notation "flip" => BalancedCriticalSpectrum.flip

/-- A cube symmetry that permutes edge directions preserves induced
regularity and Huang-balanced supports. -/
theorem cube_action_regular_balanced {n d : ℕ} {C : Finset (Q n)}
    (g : Q n ≃ Q n) (p : Fin n ≃ Fin n)
    (hg : ∀ x i, g (BalancedCriticalSpectrum.flip x i) =
      BalancedCriticalSpectrum.flip (g x) (p i))
    (hreg : ((hypercube n).induce (C : Set (Q n))).IsRegularOfDegree d)
    (hb : IsBalanced C) :
    ((hypercube n).induce (C.image g : Set (Q n))).IsRegularOfDegree d ∧
      IsBalanced (C.image g) := by
  classical
  have hm (y : Q n) : y ∈ C.image g ↔ g.symm y ∈ C := by
    constructor
    · rintro hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      simpa using hx
    · intro hy
      exact mem_image.mpr ⟨g.symm y, hy, g.apply_symm_apply y⟩
  let e : (C : Set (Q n)) ≃ (C.image g : Set (Q n)) :=
    { toFun := fun x => ⟨g x, mem_image.mpr ⟨x, x.property, rfl⟩⟩
      invFun := fun y => ⟨g.symm y, (hm y).mp y.property⟩
      left_inv := fun x => Subtype.ext (g.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (g.apply_symm_apply y) }
  let f : ((hypercube n).induce (C : Set (Q n))) ≃g
      ((hypercube n).induce (C.image g : Set (Q n))) :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        change (hypercube n).Adj (g x.val) (g y.val) ↔ (hypercube n).Adj x.val y.val
        constructor
        · intro h
          obtain ⟨i, hi⟩ := adjacent_exists_flip h
          have he : y.val = flip x.val (p.symm i) := g.injective (by
            rw [hi, hg, p.apply_symm_apply])
          rw [he]
          exact flip_adj _ _
        · intro h
          obtain ⟨i, hi⟩ := adjacent_exists_flip h
          rw [hi, hg]
          exact flip_adj _ _ }
  constructor
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact (f.degree_eq x).trans (hreg.degree_eq x)
  · obtain ⟨theta, ht, he, _⟩ := HuangCubeCovariance.exists_signed_covariance g p hg
    obtain ⟨sigma, hs⟩ := hb
    refine ⟨fun y => theta (g.symm y) * sigma (g.symm y), ?_, ?_⟩
    · intro y hy
      rcases ht (g.symm y) with h | h <;>
        rcases hs.1 _ ((hm y).mp hy) with h' | h' <;> simp [h, h']
    · intro x hx y hy hxy
      obtain ⟨j, hj⟩ := adjacent_exists_flip hxy
      let i := p.symm j
      have hy' : y = g (flip (g.symm x) i) := by
        rw [hg, g.apply_symm_apply]
        simpa [i] using hj
      have he' := he (g.symm x) i
      rw [g.apply_symm_apply] at he'
      have hyC : flip (g.symm x) i ∈ C := by
        simpa [hy'] using (hm y).mp hy
      rw [hy']
      simp only [g.symm_apply_apply]
      rw [he', hs.2 _ ((hm x).mp hx) _ hyC (flip_adj _ _)]
      ring

end D5.S3.Combinatorics.Graph.HypercubeCritical.HuangBalancedSymmetry
