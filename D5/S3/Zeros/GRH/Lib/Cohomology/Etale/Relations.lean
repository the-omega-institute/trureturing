/- GID: D5/S3/Zeros/GRH/Lib/Cohomology/Etale/Relations
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Cohomology/Etale/Relations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Cohomology.Etale.Relations. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cohomology/Etale/Relations.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.Partitions
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: A relation among maps on a locus with the same cohomology gives a relation among
pull-backs. -/


open CategoryTheory Preadditive Subfunctor
variable {C} [Category C] {Y W : C ⥤ Type 1} {F n ι} [Fintype ι] (c) (f : ι → (W ⟶ Y))

/-- For finitely many f_i: W → Y and integers c_i, the subfunctor of W of points x with ∑ c_i
[f_i(x)] = 0 in Z[Y(A)], expressed by `Cancels`. -/
def relationLocus := mk ({x | Cancels c fun i ↦ f i · x}) fun _ _ ↦ (·.mono fun _ ↦ by simp_all)

lemma relationLocus_sum_eq_zero : freeAb.map (relationLocus c f).ι ≫ ∑ i,
  c i • freeAb.map (f i) = 0 := freeAb.hom_ext fun _ ↦ (sum_app_apply.trans ·.2)

/-- For finitely many f_i: W → Y and integers c_i, if the inclusion into W of the locus where ∑
c_i [f_i(w)] = 0 is an equivalence for F, then ∑ c_i f_i^* x = 0 for every x in H^n(Y,F). -/
lemma H.sum_map_eq_zero_of_relationLocus (h : IsCohomEquiv F (freeAb.map (relationLocus c f).ι)) x :
  ∑ i, c i • map F (freeAb.map (f i)) n x = 0 := (h n).1
  (by simpa [comp_sum, ← map_comp] using! congr((mapHom ..) $(relationLocus_sum_eq_zero ..) x))
