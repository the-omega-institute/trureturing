/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorBraiding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sector skew symmetry and the finite braiding convolution. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorBorcherds
import D5.S3.VertexAlgebra.StateField.SkewSymmetry
import D5.S3.VertexAlgebra.Sectors.LatticeSectorGround

/-! The all-state skew-symmetry supplier descends to every charge sector.
The finite convolution is retained explicitly, so the result is a genuine
mode identity rather than an informal exponential notation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open LatticeActualVertexAlgebra
open scoped BigOperators VertexOperator
noncomputable section

def reverseTerm (D : LatticeData) (α β : Charge D)
    (u : Sector D α) (v : Sector D β) (n : ℤ) (j : ℕ) :
    Sector D (α + β) :=
  (((-1 : ℂ) ^ (n + (j : ℤ) + 1)) / (j.factorial : ℂ)) •
    (sectorT D (α + β) ^ j)
      (canonical D β α v (n + j) u)

private theorem translation_pow_single (D : LatticeData) (δ : Charge D)
    (x : Sector D δ) (j : ℕ) :
    (translation D ^ j) (Finsupp.single δ x) =
      Finsupp.single δ ((sectorT D δ ^ j) x) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, ← single_sectorT]
      congr 1
      rw [pow_succ' (sectorT D δ) j, Module.End.mul_apply]

theorem canonical_skew
    (D : LatticeData) (α β : Charge D)
    (u : Sector D α) (v : Sector D β) (n : ℤ) :
    Function.HasFiniteSupport (reverseTerm D α β u v n) ∧
      canonical D α β u n v =
        ∑ᶠ j : ℕ, reverseTerm D α β u v n j := by
  classical
  let P : Carrier D →ₗ[ℂ] Sector D (α + β) := projection D (α + β)
  let A := Finsupp.single α u
  let B := Finsupp.single β v
  have h := StateField.SkewSymmetry.skew_symmetry
    (actualVertexAlgebra D) A B
  have hn := h.1 n
  let allTerm : ℕ → Carrier D := fun j =>
    (((-1 : ℂ) ^ (n + (j : ℤ) + 1)) / (j.factorial : ℂ)) •
      (translation D ^ j) (((Y D B)[[n + j]]) A)
  have hmode (j : ℕ) :
      ((Y D B)[[n + j]]) A =
        Finsupp.single (α + β) (canonical D β α v (n + j) u) := by
    simpa only [A, B, add_comm] using
      (single_canonical D β α v u (n + j)).symm
  have hterm (j : ℕ) :
      allTerm j = Finsupp.single (α + β) (reverseTerm D α β u v n j) := by
    dsimp only [allTerm]
    rw [hmode, translation_pow_single]
    simp only [← Finsupp.smul_single, reverseTerm]
  have hproj (j : ℕ) : P (allTerm j) = reverseTerm D α β u v n j := by
    simpa only [P, projection, Finsupp.lapply_apply, Finsupp.single_eq_same] using
      congrArg P (hterm j)
  have hfinite : Function.HasFiniteSupport (fun j : ℕ => P (allTerm j)) :=
    hn.1.fun_comp (map_zero P)
  have hfinite' : Function.HasFiniteSupport (reverseTerm D α β u v n) := by
    simpa only [hproj] using hfinite
  have hleft : canonical D α β u n v =
      P (((Y D A)[[n]]) B) := by
    simpa only [P, projection, Finsupp.lapply_apply, Finsupp.single_eq_same, A, B] using
      congrArg P (single_canonical D α β u v n)
  refine ⟨hfinite', ?_⟩
  calc
    canonical D α β u n v = P (((Y D A)[[n]]) B) := hleft
    _ = P (∑ᶠ j : ℕ, allTerm j) := by
      dsimp only [allTerm]
      simpa only [actualVertexAlgebra] using congrArg P hn.2
    _ = ∑ᶠ j : ℕ, P (allTerm j) := map_finsum P hn.1
    _ = ∑ᶠ j : ℕ, reverseTerm D α β u v n j := by
      apply finsum_congr
      intro j
      exact hproj j

end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
