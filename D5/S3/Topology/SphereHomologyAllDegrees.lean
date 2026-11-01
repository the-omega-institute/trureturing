/- GID: D5/S3/Topology/SphereHomologyAllDegrees
   generality: G
   mirror-B: D5/B/S3/Topology/SphereHomologyAllDegrees
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual sphere singular homology in every positive degree over torsion-free coefficients. -/
import D5.S3.Topology.TauCeti.AlgebraicTopology.Singular.Sphere
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Tactic.NormNum

noncomputable section
open CategoryTheory Limits AlgebraicTopology Metric Module

universe w v u
namespace D5.S3.Topology.SphereHomologyAllDegrees

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- In every degree other than its dimension, an actual Euclidean sphere has
zero reduced singular homology. No assertion of vanishing is an input. -/
theorem isZero_reducedHomology_sphere
    {d : ℕ} {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin (d + 1)) ℝ E) (q : ℕ) (hq : q ≠ d) :
    IsZero ((TauCeti.reducedSingularHomologyFunctor R q).obj
      (TopCat.of (sphere (0 : E) 1))) := by
  induction d generalizing E q with
  | zero =>
      have hd : Module.finrank ℝ E = 1 := by
        simpa using finrank_eq_card_basis b.toBasis
      letI : DiscreteTopology (sphere (0 : E) 1) :=
        TauCeti.discreteTopology_sphere_of_finrank_eq_one hd 0 1
      cases q with
      | zero => exact (hq rfl).elim
      | succ q =>
          exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C
            (q + 1) R (TopCat.of (sphere (0 : E) 1)) (Nat.succ_ne_zero q)).of_iso
              ((TauCeti.reducedSingularHomologySuccIso R q).app _)
  | succ d ih =>
      cases q with
      | zero =>
          have hr : (1 : Cardinal) < Module.rank ℝ E := by
            rw [rank_eq_card_basis b.toBasis, Fintype.card_fin]
            exact_mod_cast (by omega : 1 < d + 1 + 1)
          letI : PathConnectedSpace (sphere (0 : E) 1) :=
            isPathConnected_iff_pathConnectedSpace.mp
              (isPathConnected_sphere hr 0 (by norm_num : (0 : ℝ) ≤ 1))
          exact TauCeti.isZero_reducedSingularHomologyFunctor_zero R _
      | succ q =>
          have hqd : q ≠ d := by omega
          exact (ih (E := _) b.orthogonalLast q hqd).of_iso
            (TauCeti.reducedSingularHomologySphereSuccIso R
              (⟨b (Fin.last (d + 1)), by simp⟩ : sphere (0 : E) 1) q)

section Modules
variable {k : Type w} [Ring k]
    (M : ModuleCat.{w} k) [Module.IsTorsionFree k M]

/-- Actual sphere homology is torsion-free in all positive degrees, including
all off-dimensional degrees. The coefficient module may be any torsion-free
module over a ring. -/
theorem isTorsionFree_singularHomology_sphere
    {d : ℕ} {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin (d + 1)) ℝ E) (q : ℕ) (hq : 0 < q) :
    Module.IsTorsionFree k
      (((singularHomologyFunctor (ModuleCat.{w} k) q).obj M).obj
        (TopCat.of (sphere (0 : E) 1))) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  by_cases hd : r + 1 = d
  · subst d
    let e := ((TauCeti.reducedSingularHomologySuccIso M r).app
        (TopCat.of (sphere (0 : E) 1))).symm ≪≫
        TauCeti.reducedSingularHomologySphereIso M b
    let f := e.toLinearEquiv
    exact Function.Injective.moduleIsTorsionFree f f.injective
      (fun a z => f.map_smul a z)
  · letI : Subsingleton ((TauCeti.reducedSingularHomologyFunctor M (r + 1)).obj
        (TopCat.of (sphere (0 : E) 1))) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (isZero_reducedHomology_sphere M b (r + 1) hd)
    change Module.IsTorsionFree k
      ((TauCeti.reducedSingularHomologyFunctor M (r + 1)).obj
        (TopCat.of (sphere (0 : E) 1)))
    infer_instance

end Modules
end D5.S3.Topology.SphereHomologyAllDegrees
