/- GID: D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed acyclic data count actual cross-polytope sum faces by affine dimension. -/

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Order.Extension.Linear
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Sort
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Analysis.Convex.Topology
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Pointwise
open D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder
namespace D5.S3.Combinatorics.Geometry.CrossPolytopeFaceCounts
/-- The real coordinate space with `n` coordinates. -/
abbrev Ambient (n : ℕ) := Fin n → ℝ
/-- A zero block and a selected-coordinate set for each summand. -/
abbrev RawData (n m : ℕ) := Finset (Fin m) × (Fin m → Finset (Fin n))
/-- The convex hull of the positive and negative coordinate vectors indexed by `I`. -/
def crossHull {n : ℕ} (I : Finset (Fin n)) : Set (Ambient n) :=
  convexHull ℝ {x | ∃ j ∈ I, x = Pi.single j 1 ∨ x = -Pi.single j 1}

/-- The actual weighted Minkowski sum, including zero-weight summands. -/
def actualQ {n m : ℕ} (I : Fin m → Finset (Fin n)) (weights : Fin m → ℝ) : Set (Ambient n) := ∑ i : Fin m, weights i • crossHull (I i)

/-- The indices of strictly positive weights. -/
noncomputable def active {m : ℕ} (weights : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => 0 < weights i)

/-- The union of the coordinate supports of the indicated summands. -/
def support {n m : ℕ} (I : Fin m → Finset (Fin n)) (A : Finset (Fin m)) : Finset (Fin n) := A.biUnion I

/-- Coordinates belonging to at least one summand in the zero block. -/
def zeroSet {n m : ℕ} (I : Fin m → Finset (Fin n)) (q : RawData n m) : Finset (Fin n) := support I q.1

/-- Active summands outside the zero block. -/
def remaining {n m : ℕ} (A : Finset (Fin m)) (q : RawData n m) : Finset (Fin m) := A \ q.1

/-- Every active coordinate outside the zero set, including unselected coordinates. -/
def vertexSet {n m : ℕ} (I : Fin m → Finset (Fin n)) (A : Finset (Fin m)) (q : RawData n m) : Finset (Fin n) :=
  support I A \ zeroSet I q

/-- The union of all selected-coordinate sets of remaining summands. -/
def selected {n m : ℕ} (A : Finset (Fin m)) (q : RawData n m) : Finset (Fin n) := (remaining A q).biUnion q.2

/-- The vertex type retaining every coordinate of `vertexSet`. -/
abbrev Vertex {n m : ℕ} (I : Fin m → Finset (Fin n)) (A : Finset (Fin m)) (q : RawData n m) := {j // j ∈ vertexSet I A q}

/-- Distinct coordinates are adjacent when some remaining summand selects both. -/
def equalityGraph {n m : ℕ} (I : Fin m → Finset (Fin n)) (A : Finset (Fin m)) (q : RawData n m) : SimpleGraph (Vertex I A q) where
  Adj a b := a ≠ b ∧ ∃ i ∈ remaining A q, a.val ∈ q.2 i ∧ b.val ∈ q.2 i
  symm := ⟨by
    rintro a b ⟨hne, i, hi, ha, hb⟩; exact ⟨hne.symm, i, hi, hb, ha⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

/-- Equality components, including all isolated vertices. -/
abbrev Component {n m : ℕ} (I : Fin m → Finset (Fin n)) (A : Finset (Fin m)) (q : RawData n m) := (equalityGraph I A q).ConnectedComponent

/-- A nonselected coordinate points to a selected coordinate of the same summand. -/
def strictRel {n m : ℕ} (I : Fin m → Finset (Fin n)) (A : Finset (Fin m)) (q : RawData n m) (C D : Component I A q) : Prop :=
  ∃ i ∈ remaining A q, ∃ a b : Vertex I A q, a.val ∈ I i ∧ a.val ∉ q.2 i ∧ b.val ∈ q.2 i ∧ (equalityGraph I A q).connectedComponentMk a = C ∧
      (equalityGraph I A q).connectedComponentMk b = D

/-- The zero block is active; selections are empty elsewhere and nonempty
    in the remaining supports. -/
def validChoice {n m : ℕ} (I : Fin m → Finset (Fin n)) (A : Finset (Fin m)) (q : RawData n m) : Prop :=
  q.1 ⊆ A ∧
  (∀ i, i ∉ remaining A q → q.2 i = ∅) ∧
  (∀ i ∈ remaining A q, (q.2 i).Nonempty ∧ q.2 i ⊆ I i \ zeroSet I q)

/-- Valid choices whose strict component relation has no nonempty directed cycle,
    including self-loops. -/
def feasible {n m : ℕ} (I : Fin m → Finset (Fin n)) (A : Finset (Fin m)) (q : RawData n m) : Prop :=
  validChoice I A q ∧ ∀ C, ¬ Relation.TransGen (strictRel I A q) C C

/-- Actual nonempty exposed subsets counted by the finrank of their affine-span direction. -/
noncomputable def geometricFaceCount {n m : ℕ} (I : Fin m → Finset (Fin n)) (weights : Fin m → ℝ) (r : ℕ) : ℕ :=
  Nat.card {F : Set (Ambient n) // F.Nonempty ∧ IsExposed ℝ (actualQ I weights) F ∧ Module.finrank ℝ (affineSpan ℝ F).direction = r}

/-- The finite sum of global sign counts over feasible data of the specified dimension. -/
noncomputable def combinatorialSum {n m : ℕ} (I : Fin m → Finset (Fin n)) (weights : Fin m → ℝ) (r : ℕ) : ℕ := by
  classical
  exact ∑ q : RawData n m, if feasible I (active weights) q ∧ (support I (active weights)).card - Nat.card (Component I (active weights) q) = r
    then 2 ^ (selected (active weights) q).card else 0

/-- The component convex set specified by the zero block and signed selected vertices. -/
def chosenHull {n m : ℕ} (I : Fin m → Finset (Fin n)) (q : RawData n m) (sign : Fin n → ℝ) (i : Fin m) : Set (Ambient n) :=
  if i ∈ q.1 then crossHull (I i)
  else convexHull ℝ {x | ∃ j ∈ q.2 i, x = sign j • Pi.single j 1}

/-- The actual Minkowski sum of the signed component faces over positive-weight summands. -/
noncomputable def signedFace {n m : ℕ} (I : Fin m → Finset (Fin n)) (weights : Fin m → ℝ) (q : RawData n m) (sign : Fin n → ℝ) : Set (Ambient n) :=
  ∑ i ∈ active weights, weights i • chosenHull I q sign i

/-- For arbitrary nonempty coordinate supports and nonnegative real weights, the number
    of actual nonempty exposed faces of dimension `r` is the signed acyclic-data sum.
    Zero weights, repeated supports, disconnected configurations and empty active sets
    are included. The face dimension is the dimension of its actual affine span. -/
theorem full_cross_polytope_face_count (n m : ℕ) (I : Fin m → Finset (Fin n)) (weights : Fin m → ℝ) (hI : ∀ i, (I i).Nonempty) (hw : ∀ i, 0 ≤ weights i)
    (r : ℕ) (_hr : r ≤ (support I (active weights)).card) :
    geometricFaceCount I weights r = combinatorialSum I weights r := by
  classical
  have feasible_realizes_actual_sum_face {n m : ℕ} (I : Fin m → Finset (Fin n)) (weights : Fin m → ℝ) (hI : ∀ i, (I i).Nonempty) (hw : ∀ i, 0 ≤ weights i)
      (q : RawData n m) (hq : feasible I (active weights) q) (sign : Fin n → ℝ)
      (hsign : ∀ j ∈ selected (active weights) q, sign j = 1 ∨ sign j = -1) :
      ∃ l : StrongDual ℝ (Ambient n), l.toExposed (actualQ I weights) = signedFace I weights q sign ∧ (signedFace I weights q sign).Nonempty ∧
        (∀ i ∈ active weights, l.toExposed (crossHull (I i)) = chosenHull I q sign i) := by
    classical
    have common_normal_realizes {n m : ℕ} (I : Fin m → Finset (Fin n)) (A : Finset (Fin m)) (q : RawData n m) (hq : feasible I A q) (sign : Fin n → ℝ)
        (hsign : ∀ j ∈ selected A q, sign j = 1 ∨ sign j = -1) :
        ∃ u : Ambient n, (∀ j ∈ zeroSet I q, u j = 0) ∧ (∀ j, j ∉ support I A → u j = 0) ∧ (∀ i ∈ remaining A q, ∃ h : ℝ, 0 < h ∧
            (∀ j ∈ q.2 i, u j = sign j * h) ∧
            (∀ j ∈ I i \ q.2 i, |u j| < h)) := by
      classical
      let C := Component I A q
      let edge : C → C → Prop := strictRel I A q
      let _ : PartialOrder C := {
        le := Relation.ReflTransGen edge
        le_refl := fun _ => Relation.ReflTransGen.refl
        le_trans := fun _ _ _ => Relation.ReflTransGen.trans
        le_antisymm := fun _ _ =>
          reachable_antisymm_of_acyclic hq.2 }
      let _ : Fintype C := Fintype.ofFinite C
      let _ : Fintype (LinearExtension C) := Fintype.ofEquiv C
        { toFun := fun x => x, invFun := fun x => x,
          left_inv := fun _ => rfl, right_inv := fun _ => rfl }
      let e := monoEquivOfFin (LinearExtension C) rfl
      let height : C → ℝ := fun c => ((e.symm (toLinearExtension c)).val : ℝ) + 1
      have hheight (c : C) : 0 < height c := by
        dsimp [height]; positivity
      have hstrict {c d : C} (hcd : edge c d) : height c < height d := by
        have hle : c ≤ d := Relation.ReflTransGen.single hcd
        have hne : c ≠ d := by
          intro heq; subst d
          exact hq.2 c (Relation.TransGen.single hcd)
        have hlinear : toLinearExtension c < toLinearExtension d :=
          lt_of_le_of_ne (toLinearExtension.monotone hle) hne
        have hfin := e.symm.strictMono hlinear
        dsimp [height]; have hreal : ((e.symm (toLinearExtension c)).val : ℝ) < ((e.symm (toLinearExtension d)).val : ℝ) := by exact_mod_cast hfin
        linarith
      let block : Vertex I A q → C := (equalityGraph I A q).connectedComponentMk
      let u : Ambient n := fun j =>
        if hj : j ∈ vertexSet I A q then (if j ∈ selected A q then sign j else 1) * height (block ⟨j, hj⟩)
        else 0
      have hzero {j : Fin n} (hj : j ∈ zeroSet I q) : u j = 0 := by
        have hn : j ∉ vertexSet I A q := by
          simp only [vertexSet, Finset.mem_sdiff]; exact fun h => h.2 hj
        simp only [u, dif_neg hn]
      have habs (j : Vertex I A q) : |u j.val| = height (block j) := by
        simp only [u, dif_pos j.property, abs_mul]; have hsignabs : |if j.val ∈ selected A q then sign j.val else 1| = 1 := by
          split_ifs with hj
          · rcases hsign j.val hj with h | h <;> simp [h]
          · norm_num
        rw [hsignabs, one_mul, abs_of_pos (hheight _)]
      have hselected {i : Fin m} (hi : i ∈ remaining A q) {j : Fin n} (hj : j ∈ q.2 i) : j ∈ selected A q :=
        Finset.mem_biUnion.mpr ⟨i, hi, hj⟩
      have hvertex {i : Fin m} (hi : i ∈ remaining A q) {j : Fin n} (hj : j ∈ q.2 i) : j ∈ vertexSet I A q := by
        have hsub := (hq.1.2.2 i hi).2 hj
        refine Finset.mem_sdiff.mpr ⟨?_, (Finset.mem_sdiff.mp hsub).2⟩
        exact Finset.mem_biUnion.mpr ⟨i, (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hsub).1⟩
      refine ⟨u, fun _ hj => hzero hj, ?_, ?_⟩
      · intro j hj; have hn : j ∉ vertexSet I A q := by
          intro h; exact hj (Finset.mem_sdiff.mp h).1
        simp only [u, dif_neg hn]
      · intro i hi; obtain ⟨b, hb⟩ := (hq.1.2.2 i hi).1
        let vb : Vertex I A q := ⟨b, hvertex hi hb⟩
        refine ⟨height (block vb), hheight _, ?_, ?_⟩
        · intro j hj; let vj : Vertex I A q := ⟨j, hvertex hi hj⟩
          have hblocks : block vj = block vb := by
            by_cases h : vj = vb
            · exact congrArg block h
            · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj (show (equalityGraph I A q).Adj vj vb from ⟨h, i, hi, hj, hb⟩)
          simp only [u, dif_pos (hvertex hi hj), if_pos (hselected hi hj)]; change sign j * height (block vj) = _
          rw [hblocks]
        · intro j hj; by_cases hz : j ∈ zeroSet I q
          · rw [hzero hz, abs_zero]; exact hheight _
          · have hjV : j ∈ vertexSet I A q := by
              refine Finset.mem_sdiff.mpr ⟨?_, hz⟩
              exact Finset.mem_biUnion.mpr ⟨i, (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hj).1⟩
            let vj : Vertex I A q := ⟨j, hjV⟩
            rw [show |u j| = height (block vj) from habs vj]
            exact hstrict ⟨i, hi, vj, vb, (Finset.mem_sdiff.mp hj).1, (Finset.mem_sdiff.mp hj).2, hb, rfl, rfl⟩
    have feasible_realizes_component_faces {n m : ℕ} (I : Fin m → Finset (Fin n)) (A : Finset (Fin m)) (q : RawData n m)
        (hq : feasible I A q) (sign : Fin n → ℝ)
        (hsign : ∀ j ∈ selected A q, sign j = 1 ∨ sign j = -1) :
        ∃ l : StrongDual ℝ (Ambient n), ∀ i ∈ A, l.toExposed (crossHull (I i)) = chosenHull I q sign i := by
      classical
      obtain ⟨u, huZ, huU, hu⟩ := common_normal_realizes I A q hq sign hsign
      let l : StrongDual ℝ (Ambient n) := ∑ j, u j • ContinuousLinearMap.proj j
      have hl (x : Ambient n) : l x = ∑ j, u j * x j := by simp [l, ContinuousLinearMap.proj_apply, smul_eq_mul]
      have hsingle (j : Fin n) : l (Pi.single j 1) = u j := by simp [hl, Pi.single_apply, mul_ite, eq_comm]
      refine ⟨l, ?_⟩
      intro i hiA; by_cases hi0 : i ∈ q.1
      · have hvalues : ∀ x ∈ crossHull (I i), l x = 0 := by
          apply convexHull_min ?_ (convex_hyperplane l.toLinearMap.isLinear 0)
          rintro x ⟨j, hj, rfl | rfl⟩
          · change l (Pi.single j 1) = 0; rw [hsingle, huZ j (Finset.mem_biUnion.mpr ⟨i, hi0, hj⟩)]
          · change l (-Pi.single j 1) = 0; rw [map_neg, hsingle, huZ j (Finset.mem_biUnion.mpr ⟨i, hi0, hj⟩), neg_zero]
        simp only [chosenHull, if_pos hi0]; ext x
        constructor
        · exact fun hx => hx.1
        · intro hx; exact ⟨hx, fun y hy => by rw [hvalues y hy, hvalues x hx]⟩
      · have hirest : i ∈ remaining A q := Finset.mem_sdiff.mpr ⟨hiA, hi0⟩
        obtain ⟨h, hpos, hsel, hnon⟩ := hu i hirest
        let vertices : Set (Ambient n) :=
          {x | ∃ j ∈ I i, x = Pi.single j 1 ∨ x = -Pi.single j 1}
        let B : Set (Ambient n) := {x | ∃ j ∈ q.2 i, x = sign j • Pi.single j 1}
        have hs (j : Fin n) (hj : j ∈ q.2 i) : sign j = 1 ∨ sign j = -1 :=
          hsign j (Finset.mem_biUnion.mpr ⟨i, hirest, hj⟩)
        have hsub (j : Fin n) (hj : j ∈ q.2 i) : j ∈ I i :=
          (Finset.mem_sdiff.mp ((hq.1.2.2 i hirest).2 hj)).1
        have hBsub : B ⊆ vertices := by
          rintro x ⟨j, hj, rfl⟩; refine ⟨j, hsub j hj, ?_⟩
          rcases hs j hj with hsg | hsg
          · exact Or.inl (by simp [hsg])
          · exact Or.inr (by simp [hsg])
        have hbound : ∀ x ∈ vertices, l x ≤ h := by
          rintro x ⟨j, hj, hx⟩; have habs : |u j| ≤ h := by
            by_cases hjS : j ∈ q.2 i
            · rw [hsel j hjS]; rcases hs j hjS with hsg | hsg <;> simp [hsg, abs_of_pos hpos]
            · exact (hnon j (Finset.mem_sdiff.mpr ⟨hj, hjS⟩)).le
          rcases hx with rfl | rfl
          · exact (hsingle j).symm ▸ (le_abs_self (u j)).trans habs
          · rw [map_neg, hsingle]; exact (neg_le_abs (u j)).trans habs
        have hBmax : ∀ x ∈ B, l x = h := by
          rintro x ⟨j, hj, rfl⟩; rw [map_smul, smul_eq_mul, hsingle, hsel j hj]
          rcases hs j hj with hsg | hsg <;> simp [hsg]
        have hmaxB : ∀ x ∈ vertices, l x = h → x ∈ B := by
          rintro x ⟨j, hj, hx⟩ hmax; have hjS : j ∈ q.2 i := by
            by_contra hn
            have hlt := hnon j (Finset.mem_sdiff.mpr ⟨hj, hn⟩)
            rcases hx with rfl | rfl
            · rw [hsingle] at hmax; exact (not_lt_of_ge (le_abs_self (u j))) (hmax ▸ hlt)
            · rw [map_neg, hsingle] at hmax; exact (not_lt_of_ge (neg_le_abs (u j))) (hmax ▸ hlt)
          refine ⟨j, hjS, ?_⟩
          rcases hx with rfl | rfl
          · rw [hsingle, hsel j hjS] at hmax; rcases hs j hjS with hsg | hsg
            · simp [hsg]
            · rw [hsg] at hmax; nlinarith
          · rw [map_neg, hsingle, hsel j hjS] at hmax; rcases hs j hjS with hsg | hsg
            · rw [hsg] at hmax; nlinarith
            · simp [hsg]
        have hCHbound : ∀ x ∈ convexHull ℝ vertices, l x ≤ h :=
          convexHull_min hbound (convex_halfSpace_le l.toLinearMap.isLinear h)
        have hCHBmax : ∀ x ∈ convexHull ℝ B, l x = h :=
          convexHull_min hBmax (convex_hyperplane l.toLinearMap.isLinear h)
        obtain ⟨b, hb⟩ := (hq.1.2.2 i hirest).1
        let bpoint : Ambient n := sign b • Pi.single b 1
        have hbB : bpoint ∈ B := ⟨b, hb, rfl⟩
        simp only [chosenHull, if_neg hi0]; change l.toExposed (convexHull ℝ vertices) = convexHull ℝ B
        ext x
        constructor
        · intro hx; have hxmax : l x = h := le_antisymm (hCHbound x hx.1) (by
            have hbCH := subset_convexHull ℝ vertices (hBsub hbB)
            simpa only [hBmax bpoint hbB] using hx.2 bpoint hbCH)
          obtain ⟨κ, inst, w, z, hw0, hw1, hz, hcombo⟩ :=
            mem_convexHull_iff_exists_fintype.mp hx.1
          let _ : Fintype κ := inst
          have hsumval : (∑ k, w k * l (z k)) = h := by
            calc
              _ = l (∑ k, w k • z k) := by simp [map_sum, map_smul, smul_eq_mul]
              _ = h := hcombo ▸ hxmax
          have hdeficit : (∑ k, w k * (h - l (z k))) = 0 := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, hsumval, sub_self]
          have hweight (k : κ) : w k = 0 ∨ l (z k) = h := by
            have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
              mul_nonneg (hw0 k) (sub_nonneg.mpr (hbound _ (hz k))))).mp hdeficit k (Finset.mem_univ _)
            rcases mul_eq_zero.mp hk with hk | hk
            · exact Or.inl hk
            · exact Or.inr (sub_eq_zero.mp hk).symm
          let z' : κ → Ambient n := fun k => if w k = 0 then bpoint else z k
          apply mem_convexHull_of_exists_fintype w z' hw0 hw1
          · intro k; dsimp [z']
            split_ifs with hk
            · exact hbB
            · exact hmaxB _ (hz k) ((hweight k).resolve_left hk)
          · calc
              _ = ∑ k, w k • z k := by
                apply Finset.sum_congr rfl
                intro k hk; dsimp [z']
                split_ifs with hwk <;> simp [hwk]
              _ = x := hcombo
        · intro hx; refine ⟨convexHull_mono hBsub hx, ?_⟩
          intro y hy; rw [hCHBmax x hx]
          exact hCHbound y hy
    obtain ⟨l, hl⟩ := feasible_realizes_component_faces I (active weights) q hq sign hsign
    have hcompact (i : Fin m) : IsCompact (crossHull (I i)) := by
      apply Set.Finite.isCompact_convexHull
      apply (Set.finite_range (fun p : Fin n × Bool =>
        if p.2 then (Pi.single p.1 1 : Ambient n) else -Pi.single p.1 1)).subset
      rintro x ⟨j, hj, hx | hx⟩
      · exact ⟨(j, true), by simpa using hx.symm⟩
      · exact ⟨(j, false), by simpa using hx.symm⟩
    have hnonempty (i : Fin m) : (crossHull (I i)).Nonempty := by
      obtain ⟨j, hj⟩ := hI i
      exact ⟨Pi.single j 1, subset_convexHull ℝ _ ⟨j, hj, Or.inl rfl⟩⟩
    have hmax (i : Fin m) : ∃ x ∈ crossHull (I i), ∀ y ∈ crossHull (I i), l y ≤ l x :=
      (hcompact i).exists_isMaxOn (hnonempty i) l.continuous.continuousOn
    choose a ha hamax using hmax
    let E : Fin m → Set (Ambient n) := fun i => l.toExposed (crossHull (I i))
    have haE (i : Fin m) : a i ∈ E i := ⟨ha i, hamax i⟩
    have hEnonempty (i : Fin m) : (E i).Nonempty := ⟨a i, haE i⟩
    have haQ : (∑ i, weights i • a i) ∈ actualQ I weights := by
      apply Set.finsetSum_mem_finsetSum
      intro i hi; exact Set.smul_mem_smul_set (ha i)
    have hface_sum : l.toExposed (actualQ I weights) = ∑ i, weights i • E i := by
      ext x
      constructor
      · intro hx; obtain ⟨b, hb, hbx⟩ := (Set.mem_fintype_sum _ _).mp hx.1; choose t ht htb using (fun i => Set.mem_smul_set.mp (hb i))
        have htx : (∑ i, weights i • t i) = x :=
          (Finset.sum_congr rfl (fun i _ => htb i)).trans hbx
        have hle (i : Fin m) : weights i * l (t i) ≤ weights i * l (a i) :=
          mul_le_mul_of_nonneg_left (hamax i _ (ht i)) (hw i)
        have hsum : (∑ i, weights i * l (t i)) = ∑ i, weights i * l (a i) := by
          refine le_antisymm (Finset.sum_le_sum fun i _ => hle i) ?_
          have h := hx.2 _ haQ
          rw [← htx] at h; simpa only [map_sum, map_smul, smul_eq_mul] using h
        apply (Set.mem_fintype_sum _ _).mpr
        refine ⟨fun i => weights i • t i, ?_, htx⟩
        intro i; change weights i • t i ∈ weights i • E i
        by_cases hwi : weights i = 0
        · rw [hwi, Set.zero_smul_set (hEnonempty i), zero_smul]; exact Set.zero_mem_zero
        · have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hsum i (Finset.mem_univ _)
          have hval : l (t i) = l (a i) := mul_left_cancel₀ hwi heq
          apply Set.smul_mem_smul_set
          refine ⟨ht i, ?_⟩
          intro y hy; rw [hval]
          exact hamax i y hy
      · intro hx; obtain ⟨b, hb, rfl⟩ := (Set.mem_fintype_sum _ _).mp hx; choose t ht htb using (fun i => Set.mem_smul_set.mp (hb i))
        have hxQ : (∑ i, b i) ∈ actualQ I weights := by
          apply (Set.mem_fintype_sum _ _).mpr
          exact ⟨b, fun i => htb i ▸ Set.smul_mem_smul_set (ht i).1, rfl⟩
        refine ⟨hxQ, ?_⟩
        intro z hz; obtain ⟨c, hc, rfl⟩ := (Set.mem_fintype_sum _ _).mp hz
        simp only [map_sum]; apply Finset.sum_le_sum
        intro i hi; obtain ⟨s, hs, hsc⟩ := Set.mem_smul_set.mp (hc i)
        rw [← hsc, ← htb i]; simpa only [map_smul, smul_eq_mul] using mul_le_mul_of_nonneg_left ((ht i).2 s hs) (hw i)
    have hdrop : (∑ i, weights i • E i) = ∑ i ∈ active weights, weights i • E i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i hi hnot; have hwi : weights i = 0 := by
        have hn : ¬ 0 < weights i := by simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hnot
        exact le_antisymm (not_lt.mp hn) (hw i)
      rw [hwi]; exact Set.zero_smul_set (hEnonempty i)
    have hdata : (∑ i ∈ active weights, weights i • E i) = signedFace I weights q sign := by
      apply Finset.sum_congr rfl
      intro i hi; exact congrArg (fun S : Set (Ambient n) => weights i • S) (hl i hi)
    refine ⟨l, hface_sum.trans (hdrop.trans hdata), ?_, hl⟩
    rw [← hdata, ← hdrop]; refine ⟨∑ i, weights i • a i, ?_⟩
    apply Set.finsetSum_mem_finsetSum
    intro i hi; exact Set.smul_mem_smul_set (haE i)
  have actual_exposed_face_has_feasible_data {n m : ℕ} (I : Fin m → Finset (Fin n)) (weights : Fin m → ℝ) (hI : ∀ i, (I i).Nonempty) (hw : ∀ i, 0 ≤ weights i)
      (F : Set (Ambient n)) (hFne : F.Nonempty) (hF : IsExposed ℝ (actualQ I weights) F) :
      ∃ q : RawData n m, ∃ sign : Fin n → ℝ, feasible I (active weights) q ∧ (∀ j ∈ selected (active weights) q, sign j = 1 ∨ sign j = -1) ∧
        F = signedFace I weights q sign := by
    classical
    obtain ⟨l, hFl⟩ := hF hFne
    have normal_data : ∃ q : RawData n m, ∃ sign : Fin n → ℝ, feasible I (active weights) q ∧ (∀ j ∈ selected (active weights) q, sign j = 1 ∨ sign j = -1) ∧
        (∀ i ∈ active weights, l.toExposed (crossHull (I i)) = chosenHull I q sign i) := by
      classical
      let A := active weights
      let u : Ambient n := fun j => l (Pi.single j 1)
      let h : Fin m → ℝ := fun i => (I i).sup' (hI i) (fun j => |u j|)
      have hbound (i : Fin m) (j : Fin n) (hj : j ∈ I i) : |u j| ≤ h i :=
        Finset.le_sup' (fun j => |u j|) hj
      have hmax (i : Fin m) : ∃ j ∈ I i, |u j| = h i := by
        obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' (hI i) (fun j => |u j|)
        exact ⟨j, hj, heq.symm⟩
      have hnonneg (i : Fin m) : 0 ≤ h i := by
        obtain ⟨j, hj⟩ := hI i
        exact (abs_nonneg _).trans (hbound i j hj)
      let J0 := A.filter (fun i => h i = 0)
      let S : Fin m → Finset (Fin n) := fun i =>
        if i ∈ A ∧ h i ≠ 0 then (I i).filter (fun j => |u j| = h i) else ∅
      let q : RawData n m := (J0, S)
      let sign : Fin n → ℝ := fun j => if 0 ≤ u j then 1 else -1
      have hJ (i : Fin m) : i ∈ q.1 ↔ i ∈ A ∧ h i = 0 := by simp [q, J0]
      have hrest (i : Fin m) : i ∈ remaining A q ↔ i ∈ A ∧ h i ≠ 0 := by
        simp only [remaining, Finset.mem_sdiff, hJ]; tauto
      have hS (i : Fin m) (hi : i ∈ remaining A q) (j : Fin n) : j ∈ q.2 i ↔ j ∈ I i ∧ |u j| = h i := by simp [q, S, (hrest i).mp hi]
      have hzero (j : Fin n) (hj : j ∈ zeroSet I q) : u j = 0 := by
        obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
        have hh := (hJ i).mp hi
        have hz : |u j| = 0 := le_antisymm (hh.2 ▸ hbound i j hji) (abs_nonneg _)
        exact abs_eq_zero.mp hz
      have hvalid : validChoice I A q := by
        refine ⟨?_, ?_, ?_⟩
        · intro i hi; exact ((hJ i).mp hi).1
        · intro i hi; have hn : ¬ (i ∈ A ∧ h i ≠ 0) := mt (hrest i).mpr hi
          simp [q, S, hn]
        · intro i hi; have hp : 0 < h i := lt_of_le_of_ne (hnonneg i) (Ne.symm ((hrest i).mp hi).2)
          refine ⟨?_, ?_⟩
          · obtain ⟨j, hj, heq⟩ := hmax i
            exact ⟨j, (hS i hi j).mpr ⟨hj, heq⟩⟩
          · intro j hj; have hs := (hS i hi j).mp hj
            refine Finset.mem_sdiff.mpr ⟨hs.1, ?_⟩
            intro hjZ; have hz := hzero j hjZ
            rw [hz, abs_zero] at hs; exact (ne_of_gt hp) hs.2.symm
      let G := equalityGraph I A q
      have hadj {a b : Vertex I A q} (hab : G.Adj a b) : |u a.val| = |u b.val| := by
        obtain ⟨hne, i, hi, ha, hb⟩ := hab
        exact ((hS i hi a.val).mp ha).2.trans ((hS i hi b.val).mp hb).2.symm
      have hwalk {a b : Vertex I A q} (p : G.Walk a b) : |u a.val| = |u b.val| := by
        induction p with
        | nil => rfl
        | cons hab p ih => exact (hadj hab).trans ih
      let value : Component I A q → ℝ := Quot.lift (fun a : Vertex I A q => |u a.val|) (by intro a b hab; obtain ⟨p⟩ := hab; exact hwalk p)
      have hstrict {C D : Component I A q} (hCD : strictRel I A q C D) : value C < value D := by
        obtain ⟨i, hi, a, b, ha, hna, hb, rfl, rfl⟩ := hCD
        change |u a.val| < |u b.val|
        have hsb := ((hS i hi b.val).mp hb).2
        rw [hsb]; apply lt_of_le_of_ne (hbound i a.val ha)
        intro heq; exact hna ((hS i hi a.val).mpr ⟨ha, heq⟩)
      have hchain {C D : Component I A q} (hc : Relation.TransGen (strictRel I A q) C D) : value C < value D := by
        induction hc with
        | single hCD => exact hstrict hCD
        | tail hCD hDE ih => exact ih.trans (hstrict hDE)
      have hfeasible : feasible I A q := by
        refine ⟨hvalid, ?_⟩
        intro C hcycle; exact (lt_irrefl _) (hchain hcycle)
      have hsign (j : Fin n) : sign j = 1 ∨ sign j = -1 := by
        dsimp [sign]; split_ifs <;> simp
      have husign (j : Fin n) : u j = sign j * |u j| := by
        by_cases hj : 0 ≤ u j
        · simp [sign, hj, abs_of_nonneg hj]
        · simp [sign, hj, abs_of_neg (not_le.mp hj)]
      refine ⟨q, sign, hfeasible, fun j _ => hsign j, ?_⟩
      intro i hiA; by_cases hi0 : i ∈ q.1
      · have hvalues : ∀ x ∈ crossHull (I i), l x = 0 := by
          apply convexHull_min ?_ (convex_hyperplane l.toLinearMap.isLinear 0)
          rintro x ⟨j, hj, rfl | rfl⟩
          · change u j = 0; exact hzero j (Finset.mem_biUnion.mpr ⟨i, hi0, hj⟩)
          · change l (-Pi.single j 1) = 0; rw [map_neg]
            change -u j = 0; rw [hzero j (Finset.mem_biUnion.mpr ⟨i, hi0, hj⟩), neg_zero]
        simp only [chosenHull, if_pos hi0]; ext x
        constructor
        · exact fun hx => hx.1
        · intro hx; exact ⟨hx, fun y hy => by rw [hvalues y hy, hvalues x hx]⟩
      · have hirest : i ∈ remaining A q := Finset.mem_sdiff.mpr ⟨hiA, hi0⟩
        have hpos : 0 < h i := lt_of_le_of_ne (hnonneg i) (Ne.symm ((hrest i).mp hirest).2)
        have hsel (j : Fin n) (hj : j ∈ q.2 i) : u j = sign j * h i := by rw [husign j, ((hS i hirest j).mp hj).2]
        have hnon (j : Fin n) (hj : j ∈ I i \ q.2 i) : |u j| < h i := by
          apply lt_of_le_of_ne (hbound i j (Finset.mem_sdiff.mp hj).1)
          intro heq; exact (Finset.mem_sdiff.mp hj).2 ((hS i hirest j).mpr ⟨(Finset.mem_sdiff.mp hj).1, heq⟩)
        let vertices : Set (Ambient n) :=
          {x | ∃ j ∈ I i, x = Pi.single j 1 ∨ x = -Pi.single j 1}
        let B : Set (Ambient n) := {x | ∃ j ∈ q.2 i, x = sign j • Pi.single j 1}
        have hs (j : Fin n) (hj : j ∈ q.2 i) : sign j = 1 ∨ sign j = -1 :=
          hsign j
        have hsub (j : Fin n) (hj : j ∈ q.2 i) : j ∈ I i :=
          (Finset.mem_sdiff.mp ((hvalid.2.2 i hirest).2 hj)).1
        have hBsub : B ⊆ vertices := by
          rintro x ⟨j, hj, rfl⟩; refine ⟨j, hsub j hj, ?_⟩
          rcases hs j hj with hsg | hsg
          · exact Or.inl (by simp [hsg])
          · exact Or.inr (by simp [hsg])
        have hbound : ∀ x ∈ vertices, l x ≤ h i := by
          rintro x ⟨j, hj, hx⟩; have habs : |u j| ≤ h i := by
            by_cases hjS : j ∈ q.2 i
            · rw [hsel j hjS]; rcases hs j hjS with hsg | hsg <;> simp [hsg, abs_of_pos hpos]
            · exact (hnon j (Finset.mem_sdiff.mpr ⟨hj, hjS⟩)).le
          rcases hx with rfl | rfl
          · exact (show l (Pi.single j 1) = u j from rfl).symm ▸ (le_abs_self (u j)).trans habs
          · rw [map_neg, show l (Pi.single j 1) = u j from rfl]; exact (neg_le_abs (u j)).trans habs
        have hBmax : ∀ x ∈ B, l x = h i := by
          rintro x ⟨j, hj, rfl⟩; rw [map_smul, smul_eq_mul, show l (Pi.single j 1) = u j from rfl, hsel j hj]
          rcases hs j hj with hsg | hsg <;> simp [hsg]
        have hmaxB : ∀ x ∈ vertices, l x = h i → x ∈ B := by
          rintro x ⟨j, hj, hx⟩ hmax; have hjS : j ∈ q.2 i := by
            by_contra hn
            have hlt := hnon j (Finset.mem_sdiff.mpr ⟨hj, hn⟩)
            rcases hx with rfl | rfl
            · rw [show l (Pi.single j 1) = u j from rfl] at hmax; exact (not_lt_of_ge (le_abs_self (u j))) (hmax ▸ hlt)
            · rw [map_neg, show l (Pi.single j 1) = u j from rfl] at hmax; exact (not_lt_of_ge (neg_le_abs (u j))) (hmax ▸ hlt)
          refine ⟨j, hjS, ?_⟩
          rcases hx with rfl | rfl
          · rw [show l (Pi.single j 1) = u j from rfl, hsel j hjS] at hmax; rcases hs j hjS with hsg | hsg
            · simp [hsg]
            · rw [hsg] at hmax; nlinarith
          · rw [map_neg, show l (Pi.single j 1) = u j from rfl, hsel j hjS] at hmax; rcases hs j hjS with hsg | hsg
            · rw [hsg] at hmax; nlinarith
            · simp [hsg]
        have hCHbound : ∀ x ∈ convexHull ℝ vertices, l x ≤ h i :=
          convexHull_min hbound (convex_halfSpace_le l.toLinearMap.isLinear (h i))
        have hCHBmax : ∀ x ∈ convexHull ℝ B, l x = h i :=
          convexHull_min hBmax (convex_hyperplane l.toLinearMap.isLinear (h i))
        obtain ⟨b, hb⟩ := (hvalid.2.2 i hirest).1
        let bpoint : Ambient n := sign b • Pi.single b 1
        have hbB : bpoint ∈ B := ⟨b, hb, rfl⟩
        simp only [chosenHull, if_neg hi0]; change l.toExposed (convexHull ℝ vertices) = convexHull ℝ B
        ext x
        constructor
        · intro hx; have hxmax : l x = h i := le_antisymm (hCHbound x hx.1) (by
            have hbCH := subset_convexHull ℝ vertices (hBsub hbB)
            simpa only [hBmax bpoint hbB] using hx.2 bpoint hbCH)
          obtain ⟨κ, inst, w, z, hw0, hw1, hz, hcombo⟩ :=
            mem_convexHull_iff_exists_fintype.mp hx.1
          let _ : Fintype κ := inst
          have hsumval : (∑ k, w k * l (z k)) = h i := by
            calc
              _ = l (∑ k, w k • z k) := by simp [map_sum, map_smul, smul_eq_mul]
              _ = h i := hcombo ▸ hxmax
          have hdeficit : (∑ k, w k * (h i - l (z k))) = 0 := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, hsumval, sub_self]
          have hweight (k : κ) : w k = 0 ∨ l (z k) = h i := by
            have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
              mul_nonneg (hw0 k) (sub_nonneg.mpr (hbound _ (hz k))))).mp hdeficit k (Finset.mem_univ _)
            rcases mul_eq_zero.mp hk with hk | hk
            · exact Or.inl hk
            · exact Or.inr (sub_eq_zero.mp hk).symm
          let z' : κ → Ambient n := fun k => if w k = 0 then bpoint else z k
          apply mem_convexHull_of_exists_fintype w z' hw0 hw1
          · intro k; dsimp [z']
            split_ifs with hk
            · exact hbB
            · exact hmaxB _ (hz k) ((hweight k).resolve_left hk)
          · calc
              _ = ∑ k, w k • z k := by
                apply Finset.sum_congr rfl
                intro k hk; dsimp [z']
                split_ifs with hwk <;> simp [hwk]
              _ = x := hcombo
        · intro hx; refine ⟨convexHull_mono hBsub hx, ?_⟩
          intro y hy; rw [hCHBmax x hx]
          exact hCHbound y hy
    obtain ⟨q, sign, hq, hsign, hl⟩ := normal_data
    have hcompact (i : Fin m) : IsCompact (crossHull (I i)) := by
      apply Set.Finite.isCompact_convexHull
      apply (Set.finite_range (fun p : Fin n × Bool =>
        if p.2 then (Pi.single p.1 1 : Ambient n) else -Pi.single p.1 1)).subset
      rintro x ⟨j, hj, hx | hx⟩
      · exact ⟨(j, true), by simpa using hx.symm⟩
      · exact ⟨(j, false), by simpa using hx.symm⟩
    have hnonempty (i : Fin m) : (crossHull (I i)).Nonempty := by
      obtain ⟨j, hj⟩ := hI i
      exact ⟨Pi.single j 1, subset_convexHull ℝ _ ⟨j, hj, Or.inl rfl⟩⟩
    have hmax (i : Fin m) : ∃ x ∈ crossHull (I i), ∀ y ∈ crossHull (I i), l y ≤ l x :=
      (hcompact i).exists_isMaxOn (hnonempty i) l.continuous.continuousOn
    choose a ha hamax using hmax
    let E : Fin m → Set (Ambient n) := fun i => l.toExposed (crossHull (I i))
    have haE (i : Fin m) : a i ∈ E i := ⟨ha i, hamax i⟩
    have hEnonempty (i : Fin m) : (E i).Nonempty := ⟨a i, haE i⟩
    have haQ : (∑ i, weights i • a i) ∈ actualQ I weights := by
      apply Set.finsetSum_mem_finsetSum
      intro i hi; exact Set.smul_mem_smul_set (ha i)
    have hface_sum : l.toExposed (actualQ I weights) = ∑ i, weights i • E i := by
      ext x
      constructor
      · intro hx; obtain ⟨b, hb, hbx⟩ := (Set.mem_fintype_sum _ _).mp hx.1; choose t ht htb using (fun i => Set.mem_smul_set.mp (hb i))
        have htx : (∑ i, weights i • t i) = x :=
          (Finset.sum_congr rfl (fun i _ => htb i)).trans hbx
        have hle (i : Fin m) : weights i * l (t i) ≤ weights i * l (a i) :=
          mul_le_mul_of_nonneg_left (hamax i _ (ht i)) (hw i)
        have hsum : (∑ i, weights i * l (t i)) = ∑ i, weights i * l (a i) := by
          refine le_antisymm (Finset.sum_le_sum fun i _ => hle i) ?_
          have h := hx.2 _ haQ
          rw [← htx] at h; simpa only [map_sum, map_smul, smul_eq_mul] using h
        apply (Set.mem_fintype_sum _ _).mpr
        refine ⟨fun i => weights i • t i, ?_, htx⟩
        intro i; change weights i • t i ∈ weights i • E i
        by_cases hwi : weights i = 0
        · rw [hwi, Set.zero_smul_set (hEnonempty i), zero_smul]; exact Set.zero_mem_zero
        · have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hsum i (Finset.mem_univ _)
          have hval : l (t i) = l (a i) := mul_left_cancel₀ hwi heq
          apply Set.smul_mem_smul_set
          refine ⟨ht i, ?_⟩
          intro y hy; rw [hval]
          exact hamax i y hy
      · intro hx; obtain ⟨b, hb, rfl⟩ := (Set.mem_fintype_sum _ _).mp hx; choose t ht htb using (fun i => Set.mem_smul_set.mp (hb i))
        have hxQ : (∑ i, b i) ∈ actualQ I weights := by
          apply (Set.mem_fintype_sum _ _).mpr
          exact ⟨b, fun i => htb i ▸ Set.smul_mem_smul_set (ht i).1, rfl⟩
        refine ⟨hxQ, ?_⟩
        intro z hz; obtain ⟨c, hc, rfl⟩ := (Set.mem_fintype_sum _ _).mp hz
        simp only [map_sum]; apply Finset.sum_le_sum
        intro i hi; obtain ⟨s, hs, hsc⟩ := Set.mem_smul_set.mp (hc i)
        rw [← hsc, ← htb i]; simpa only [map_smul, smul_eq_mul] using mul_le_mul_of_nonneg_left ((ht i).2 s hs) (hw i)
    have hdrop : (∑ i, weights i • E i) = ∑ i ∈ active weights, weights i • E i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i hi hnot; have hwi : weights i = 0 := by
        have hn : ¬ 0 < weights i := by simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hnot
        exact le_antisymm (not_lt.mp hn) (hw i)
      rw [hwi]; exact Set.zero_smul_set (hEnonempty i)
    have hdata : (∑ i ∈ active weights, weights i • E i) = signedFace I weights q sign := by
      apply Finset.sum_congr rfl
      intro i hi; exact congrArg (fun S : Set (Ambient n) => weights i • S) (hl i hi)
    exact ⟨q, sign, hq, hsign, hFl.trans (hface_sum.trans (hdrop.trans hdata))⟩
  have equal_actual_signed_faces_recover_data_and_signs {n m : ℕ} (I : Fin m → Finset (Fin n)) (weights : Fin m → ℝ)
      (hI : ∀ i, (I i).Nonempty) (hw : ∀ i, 0 ≤ weights i)
      (q p : RawData n m) (hq : feasible I (active weights) q)
      (hp : feasible I (active weights) p) (s t : Fin n → ℝ)
      (hs : ∀ j ∈ selected (active weights) q, s j = 1 ∨ s j = -1)
      (ht : ∀ j ∈ selected (active weights) p, t j = 1 ∨ t j = -1)
      (heq : signedFace I weights q s = signedFace I weights p t) :
      q = p ∧ ∀ j ∈ selected (active weights) q, s j = t j := by
    classical
    have component_hulls_recover_data_and_signs {n m : ℕ} (I : Fin m → Finset (Fin n)) (A : Finset (Fin m))
        (q p : RawData n m) (hq : validChoice I A q) (hp : validChoice I A p)
        (s t : Fin n → ℝ)
        (hs : ∀ j ∈ selected A q, s j = 1 ∨ s j = -1)
        (ht : ∀ j ∈ selected A p, t j = 1 ∨ t j = -1)
        (heq : ∀ i ∈ A, chosenHull I q s i = chosenHull I p t i) :
        q = p ∧ ∀ j ∈ selected A q, s j = t j := by
      classical
      have coord_nonneg (B : Finset (Fin n)) (t : Fin n → ℝ) (j : Fin n) (htj : t j = 1 ∨ t j = -1) :
          ∀ x ∈ convexHull ℝ {x : Ambient n | ∃ k ∈ B, x = t k • Pi.single k 1}, 0 ≤ t j * x j := by
        let f : StrongDual ℝ (Ambient n) := t j • ContinuousLinearMap.proj j
        change convexHull ℝ _ ⊆ {x : Ambient n | 0 ≤ t j * x j}
        apply convexHull_min ?_ (by simpa [f, smul_eq_mul] using convex_halfSpace_ge f.toLinearMap.isLinear 0)
        rintro x ⟨k, hk, rfl⟩; by_cases hkj : k = j
        · subst k; rcases htj with h | h <;> simp [h]
        · simp [Ne.symm hkj]
      have zero_coord (B : Finset (Fin n)) (s : Fin n → ℝ) (j : Fin n) (hj : j ∉ B) :
          ∀ x ∈ convexHull ℝ {x : Ambient n | ∃ k ∈ B, x = s k • Pi.single k 1}, x j = 0 := by
        let f : StrongDual ℝ (Ambient n) := ContinuousLinearMap.proj j
        apply convexHull_min ?_ (convex_hyperplane f.toLinearMap.isLinear 0)
        rintro x ⟨k, hk, rfl⟩; have hkj : k ≠ j := fun h => hj (h ▸ hk)
        simp [f, Ne.symm hkj]
      have zero_subset (q p : RawData n m) (hq : validChoice I A q) (hp : validChoice I A p) (s t : Fin n → ℝ) (ht : ∀ j ∈ selected A p, t j = 1 ∨ t j = -1)
          (heq : ∀ i ∈ A, chosenHull I q s i = chosenHull I p t i) : q.1 ⊆ p.1 := by
        intro i hiq; have hiA := hq.1 hiq
        by_contra hip
        have hiR : i ∈ remaining A p := Finset.mem_sdiff.mpr ⟨hiA, hip⟩
        obtain ⟨j, hj⟩ := (hp.2.2 i hiR).1
        have htj := ht j (Finset.mem_biUnion.mpr ⟨i, hiR, hj⟩)
        have hjI := (Finset.mem_sdiff.mp ((hp.2.2 i hiR).2 hj)).1
        have hx : (-t j • Pi.single j 1 : Ambient n) ∈ crossHull (I i) := by
          apply subset_convexHull ℝ _
          refine ⟨j, hjI, ?_⟩
          rcases htj with h | h
          · exact Or.inr (by simp [h])
          · exact Or.inl (by simp [h])
        have hxq : (-t j • Pi.single j 1 : Ambient n) ∈ chosenHull I q s i := by simpa only [chosenHull, if_pos hiq] using hx
        have hxp : (-t j • Pi.single j 1 : Ambient n) ∈ convexHull ℝ {x : Ambient n | ∃ k ∈ p.2 i, x = t k • Pi.single k 1} := by
          simpa only [chosenHull, if_neg hip] using (heq i hiA).subset hxq
        have hn := coord_nonneg (p.2 i) t j htj _ hxp
        rcases htj with h | h <;> norm_num [h] at hn
      have hJ : q.1 = p.1 :=
        Finset.Subset.antisymm (zero_subset q p hq hp s t ht heq) (zero_subset p q hp hq t s hs (fun i hi => (heq i hi).symm))
      have selected_subset (q p : RawData n m) (hq : validChoice I A q) (hp : validChoice I A p) (s t : Fin n → ℝ) (hs : ∀ j ∈ selected A q, s j = 1 ∨ s j = -1)
          (hJ : q.1 = p.1) (heq : ∀ i ∈ A, chosenHull I q s i = chosenHull I p t i)
          (i : Fin m) : q.2 i ⊆ p.2 i := by
        by_cases hi : i ∈ remaining A q
        · have hiA := (Finset.mem_sdiff.mp hi).1
          have hiq := (Finset.mem_sdiff.mp hi).2
          have hip : i ∉ p.1 := hJ ▸ hiq
          intro j hj; by_contra hjp
          have hxq : (s j • Pi.single j 1 : Ambient n) ∈ chosenHull I q s i := by
            rw [chosenHull, if_neg hiq]; exact subset_convexHull ℝ _ ⟨j, hj, rfl⟩
          have hxp : (s j • Pi.single j 1 : Ambient n) ∈ convexHull ℝ {x : Ambient n | ∃ k ∈ p.2 i, x = t k • Pi.single k 1} := by
            simpa only [chosenHull, if_neg hip] using (heq i hiA).subset hxq
          have hz := zero_coord (p.2 i) t j hjp _ hxp
          have hsj := hs j (Finset.mem_biUnion.mpr ⟨i, hi, hj⟩)
          rcases hsj with h | h <;> norm_num [h] at hz
        · rw [hq.2.1 i hi]; exact Finset.empty_subset _
      have hS : q.2 = p.2 := by
        funext i; exact Finset.Subset.antisymm (selected_subset q p hq hp s t hs hJ heq i)
          (selected_subset p q hp hq t s ht hJ.symm (fun i hi => (heq i hi).symm) i)
      refine ⟨Prod.ext hJ hS, ?_⟩
      intro j hj; obtain ⟨i, hiR, hji⟩ := Finset.mem_biUnion.mp hj
      have hiA := (Finset.mem_sdiff.mp hiR).1
      have hiq := (Finset.mem_sdiff.mp hiR).2
      have hip : i ∉ p.1 := hJ ▸ hiq
      have hiRp : i ∈ remaining A p := Finset.mem_sdiff.mpr ⟨hiA, hip⟩
      have hjp : j ∈ p.2 i := hS ▸ hji
      have htj := ht j (Finset.mem_biUnion.mpr ⟨i, hiRp, hjp⟩)
      have hsj := hs j (Finset.mem_biUnion.mpr ⟨i, hiR, hji⟩)
      have hxq : (s j • Pi.single j 1 : Ambient n) ∈ chosenHull I q s i := by
        rw [chosenHull, if_neg hiq]; exact subset_convexHull ℝ _ ⟨j, hji, rfl⟩
      have hxp : (s j • Pi.single j 1 : Ambient n) ∈ convexHull ℝ {x : Ambient n | ∃ k ∈ p.2 i, x = t k • Pi.single k 1} := by
        simpa only [chosenHull, if_neg hip] using (heq i hiA).subset hxq
      have hn := coord_nonneg (p.2 i) t j htj _ hxp
      rcases hsj with hs1 | hs1 <;> rcases htj with ht1 | ht1
      · exact hs1.trans ht1.symm
      · exfalso; norm_num [hs1, ht1] at hn
      · exfalso; norm_num [hs1, ht1] at hn
      · exact hs1.trans ht1.symm
    have actual_component_recovery {n m : ℕ} (I : Fin m → Finset (Fin n)) (weights : Fin m → ℝ) (hI : ∀ i, (I i).Nonempty) (hw : ∀ i, 0 ≤ weights i)
        (l v : StrongDual ℝ (Ambient n))
        (heq : l.toExposed (actualQ I weights) = v.toExposed (actualQ I weights)) :
        ∀ i, 0 < weights i → l.toExposed (crossHull (I i)) = v.toExposed (crossHull (I i)) := by
      classical
      have hcompact (i : Fin m) : IsCompact (crossHull (I i)) := by
        apply Set.Finite.isCompact_convexHull
        apply (Set.finite_range (fun p : Fin n × Bool =>
          if p.2 then (Pi.single p.1 1 : Ambient n) else -Pi.single p.1 1)).subset
        rintro x ⟨j, hj, hx | hx⟩
        · exact ⟨(j, true), by simpa using hx.symm⟩
        · exact ⟨(j, false), by simpa using hx.symm⟩
      have hnonempty (i : Fin m) : (crossHull (I i)).Nonempty := by
        obtain ⟨j, hj⟩ := hI i
        exact ⟨Pi.single j 1, subset_convexHull ℝ _ ⟨j, hj, Or.inl rfl⟩⟩
      have hmax (f : StrongDual ℝ (Ambient n)) (i : Fin m) : ∃ x ∈ crossHull (I i), ∀ y ∈ crossHull (I i), f y ≤ f x := by
        exact (hcompact i).exists_isMaxOn (hnonempty i) f.continuous.continuousOn
      have hsub (f g : StrongDual ℝ (Ambient n)) (hfg : g.toExposed (actualQ I weights) ⊆ f.toExposed (actualQ I weights)) (i : Fin m) (hi : 0 < weights i) :
          g.toExposed (crossHull (I i)) ⊆ f.toExposed (crossHull (I i)) := by
        intro y hy; choose a ha hamax using hmax g
        let p : Fin m → Ambient n := Function.update a i y
        have hp (j : Fin m) : p j ∈ g.toExposed (crossHull (I j)) := by
          by_cases hji : j = i
          · subst j; simpa [p] using hy
          · simpa [p, hji, ContinuousLinearMap.toExposed] using And.intro (ha j) (hamax j)
        let x : Ambient n := ∑ j, weights j • p j
        have hx : x ∈ actualQ I weights := by
          apply Set.finsetSum_mem_finsetSum
          intro j hj; exact Set.smul_mem_smul_set (hp j).1
        have hxg : x ∈ g.toExposed (actualQ I weights) := by
          refine ⟨hx, ?_⟩
          intro z hz; obtain ⟨b, hb, rfl⟩ := (Set.mem_fintype_sum _ _).mp hz
          simp only [x, map_sum]; apply Finset.sum_le_sum
          intro j hj; obtain ⟨t, ht, ht_eq⟩ := (Set.mem_smul_set).mp (hb j)
          rw [← ht_eq]; simpa only [map_smul, smul_eq_mul] using mul_le_mul_of_nonneg_left ((hp j).2 t ht) (hw j)
        have hxf := hfg hxg
        choose b hb hbmax using hmax f
        have hbQ : (∑ j, weights j • b j) ∈ actualQ I weights := by
          apply Set.finsetSum_mem_finsetSum
          intro j hj; exact Set.smul_mem_smul_set (hb j)
        have hle (j : Fin m) : weights j * f (p j) ≤ weights j * f (b j) :=
          mul_le_mul_of_nonneg_left (hbmax j _ (hp j).1) (hw j)
        have hsum : (∑ j, weights j * f (p j)) = ∑ j, weights j * f (b j) := by
          apply le_antisymm (Finset.sum_le_sum fun j _ => hle j)
          simpa only [x, map_sum, map_smul, smul_eq_mul] using hxf.2 _ hbQ
        have hiEq : weights i * f (p i) = weights i * f (b i) :=
          (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hsum i (Finset.mem_univ _)
        have hyEq : f y = f (b i) := by
          have h := mul_left_cancel₀ (ne_of_gt hi) hiEq
          simpa [p] using h
        refine ⟨hy.1, ?_⟩
        intro z hz; rw [hyEq]
        exact hbmax i z hz
      intro i hi; exact Set.Subset.antisymm (hsub v l heq.subset i hi) (hsub l v heq.symm.subset i hi)
    obtain ⟨l, hl, hne, hlC⟩ := feasible_realizes_actual_sum_face I weights hI hw q hq s hs
    obtain ⟨v, hv, hpne, hvC⟩ := feasible_realizes_actual_sum_face I weights hI hw p hp t ht
    have hactual : l.toExposed (actualQ I weights) = v.toExposed (actualQ I weights) :=
      hl.trans (heq.trans hv.symm)
    have hcomponents : ∀ i ∈ active weights, chosenHull I q s i = chosenHull I p t i := by
      intro i hi; have hwi : 0 < weights i := by simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hi
      exact (hlC i hi).symm.trans ((actual_component_recovery I weights hI hw l v hactual i hwi).trans (hvC i hi))
    exact component_hulls_recover_data_and_signs I (active weights) q p hq.1 hp.1 s t hs ht hcomponents
  have actual_signed_face_annihilator {n m : ℕ} (I : Fin m → Finset (Fin n)) (weights : Fin m → ℝ) (hI : ∀ i, (I i).Nonempty) (q : RawData n m)
      (hq : validChoice I (active weights) q) (sign : Fin n → ℝ)
      (ell : Module.Dual ℝ (Ambient n)) :
      ell ∈ (affineSpan ℝ (signedFace I weights q sign)).direction.dualAnnihilator ↔ (∀ j ∈ zeroSet I q, ell (Pi.single j 1) = 0) ∧
        (∀ a b : Vertex I (active weights) q, (equalityGraph I (active weights) q).Adj a b →
          sign a.val * ell (Pi.single a.val 1) = sign b.val * ell (Pi.single b.val 1)) := by
    classical
    have ann (X : Set (Ambient n)) : ell ∈ (vectorSpan ℝ X).dualAnnihilator ↔ ∀ x ∈ X, ∀ y ∈ X, ell x = ell y := by
      constructor
      · intro h x hx y hy; have hz := (Submodule.mem_dualAnnihilator ell).mp h _ (vsub_mem_vectorSpan ℝ hx hy)
        simpa only [vsub_eq_sub, map_sub, sub_eq_zero] using hz
      · intro h; have hle : vectorSpan ℝ X ≤ LinearMap.ker ell := by
          rw [vectorSpan_def, Submodule.span_le]; rintro v ⟨x, hx, y, hy, rfl⟩
          change ell (x - y) = 0; rw [map_sub, h x hx y hy, sub_self]
        exact (Submodule.mem_dualAnnihilator ell).mpr (fun v hv => hle hv)
    have hullann (X : Set (Ambient n)) : (∀ x ∈ convexHull ℝ X, ∀ y ∈ convexHull ℝ X, ell x = ell y) ↔ (∀ x ∈ X, ∀ y ∈ X, ell x = ell y) := by
      rw [← ann, ← ann]; rw [← direction_affineSpan ℝ (convexHull ℝ X), affineSpan_convexHull, direction_affineSpan]
    have hn (i : Fin m) (hi : i ∈ active weights) : (chosenHull I q sign i).Nonempty := by
      by_cases hiq : i ∈ q.1
      · obtain ⟨j, hj⟩ := hI i
        refine ⟨Pi.single j 1, ?_⟩
        simp only [chosenHull, if_pos hiq, crossHull]; exact subset_convexHull ℝ _ ⟨j, hj, Or.inl rfl⟩
      · have hir : i ∈ remaining (active weights) q := Finset.mem_sdiff.mpr ⟨hi, hiq⟩
        obtain ⟨j, hj⟩ := (hq.2.2 i hir).1
        refine ⟨sign j • Pi.single j 1, ?_⟩
        simp only [chosenHull, if_neg hiq]; exact subset_convexHull ℝ _ ⟨j, hj, rfl⟩
    have hsum : (∀ x ∈ signedFace I weights q sign, ∀ y ∈ signedFace I weights q sign, ell x = ell y) ↔ ∀ i ∈ active weights, ∀ x ∈ chosenHull I q sign i,
          ∀ y ∈ chosenHull I q sign i, ell x = ell y := by
      constructor
      · intro h i hi x hx y hy; have hp : ∀ k : Fin m, ∃ p : Ambient n, k ∈ active weights → p ∈ chosenHull I q sign k := by
          intro k; by_cases hk : k ∈ active weights
          · obtain ⟨p, hp⟩ := hn k hk
            exact ⟨p, fun _ => hp⟩
          · exact ⟨0, fun h => False.elim (hk h)⟩
        choose p hp using hp
        let sx (z : Ambient n) := ∑ k ∈ active weights, weights k • Function.update p i z k
        have hs (z : Ambient n) (hz : z ∈ chosenHull I q sign i) : sx z ∈ signedFace I weights q sign := by
          apply Set.finsetSum_mem_finsetSum
          intro k hk; apply Set.smul_mem_smul_set
          by_cases hki : k = i
          · subst k; simpa using hz
          · simpa [Function.update, hki] using hp k hk
        have heval (z : Ambient n) : ell (sx z) = (∑ k ∈ (active weights).erase i, weights k * ell (p k)) + weights i * ell z := by
          simp only [sx, map_sum, map_smul, smul_eq_mul]; rw [← Finset.sum_erase_add _ _ hi]
          simp only [Function.update_self]; congr 1
          apply Finset.sum_congr rfl
          intro k hk; rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
        have he := h _ (hs x hx) _ (hs y hy)
        rw [heval, heval] at he; have hnw : weights i ≠ 0 := ne_of_gt (by simpa [active] using hi)
        exact mul_left_cancel₀ hnw (add_left_cancel he)
      · intro h x hx y hy; obtain ⟨a, ha, rfl⟩ := (Set.mem_finsetSum _ _ _).mp hx
        obtain ⟨b, hb, rfl⟩ := (Set.mem_finsetSum _ _ _).mp hy
        simp only [map_sum]; apply Finset.sum_congr rfl
        intro i hi; obtain ⟨u, hu, hue⟩ := Set.mem_smul_set.mp (ha hi)
        obtain ⟨v, hv, hve⟩ := Set.mem_smul_set.mp (hb hi)
        rw [← hue, ← hve]; simp only [map_smul, smul_eq_mul]
        rw [h i hi u hu v hv]
    rw [direction_affineSpan, ann, hsum]; constructor
    · intro h; constructor
      · intro j hj; obtain ⟨i, hiq, hji⟩ := Finset.mem_biUnion.mp hj
        have hi := hq.1 hiq
        have hp : (Pi.single j 1 : Ambient n) ∈ chosenHull I q sign i := by
          simp only [chosenHull, if_pos hiq, crossHull]; exact subset_convexHull ℝ _ ⟨j, hji, Or.inl rfl⟩
        have hm : (-Pi.single j 1 : Ambient n) ∈ chosenHull I q sign i := by
          simp only [chosenHull, if_pos hiq, crossHull]; exact subset_convexHull ℝ _ ⟨j, hji, Or.inr rfl⟩
        have he := h i hi _ hp _ hm
        rw [map_neg] at he; linarith
      · intro a b hab; obtain ⟨hne, i, hi, ha, hb⟩ := hab
        have hin : i ∉ q.1 := (Finset.mem_sdiff.mp hi).2
        have hm (j : Fin n) (hj : j ∈ q.2 i) : sign j • Pi.single j 1 ∈ chosenHull I q sign i := by
          simp only [chosenHull, if_neg hin]; exact subset_convexHull ℝ _ ⟨j, hj, rfl⟩
        have he := h i (Finset.mem_sdiff.mp hi).1 _ (hm _ ha) _ (hm _ hb)
        simpa only [map_smul, smul_eq_mul] using he
    · rintro ⟨hz, he⟩ i hi; by_cases hiq : i ∈ q.1
      · simp only [chosenHull, if_pos hiq, crossHull]; apply hullann _ |>.mpr
        rintro x ⟨a, ha, rfl | rfl⟩ y ⟨b, hb, rfl | rfl⟩ <;>
          have hza := hz a (Finset.mem_biUnion.mpr ⟨i, hiq, ha⟩) <;>
          have hzb := hz b (Finset.mem_biUnion.mpr ⟨i, hiq, hb⟩) <;>
          simp [hza, hzb]
      · simp only [chosenHull, if_neg hiq]; apply hullann _ |>.mpr
        rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩; have hir : i ∈ remaining (active weights) q := Finset.mem_sdiff.mpr ⟨hi, hiq⟩
        have hvertex (j : Fin n) (hj : j ∈ q.2 i) : j ∈ vertexSet I (active weights) q := by
          have hsub := (hq.2.2 i hir).2 hj
          refine Finset.mem_sdiff.mpr ⟨?_, (Finset.mem_sdiff.mp hsub).2⟩
          exact Finset.mem_biUnion.mpr ⟨i, hi, (Finset.mem_sdiff.mp hsub).1⟩
        by_cases hab : a = b
        · subst b; rfl
        · have hv := he ⟨a, hvertex a ha⟩ ⟨b, hvertex b hb⟩ ⟨fun h => hab (congrArg Subtype.val h), i, hir, ha, hb⟩
          simpa only [map_smul, smul_eq_mul] using hv
  have actual_signed_face_finrank {n m : ℕ} (I : Fin m → Finset (Fin n)) (weights : Fin m → ℝ) (hI : ∀ i, (I i).Nonempty) (q : RawData n m)
      (hq : validChoice I (active weights) q) (sign : Fin n → ℝ)
      (hsign : ∀ j ∈ selected (active weights) q, sign j = 1 ∨ sign j = -1) :
      Module.finrank ℝ (affineSpan ℝ (signedFace I weights q sign)).direction =
        (support I (active weights)).card - Nat.card (Component I (active weights) q) := by
    classical
    let U := support I (active weights)
    let Z := zeroSet I q
    let V := Vertex I (active weights) q
    let H := equalityGraph I (active weights) q
    let O := {j : Fin n // j ∉ U}
    let W := (affineSpan ℝ (signedFace I weights q sign)).direction
    let K := (H.lapMatrix ℝ).toLin'.ker
    let eta : V → ℝ := fun v => if v.val ∈ selected (active weights) q then sign v.val else 1
    have hetasq (v : V) : eta v * eta v = 1 := by
      dsimp [eta]; split_ifs with hv
      · rcases hsign v.val hv with h | h <;> norm_num [h]
      · norm_num
    have hetane (v : V) : eta v ≠ 0 := by intro h; have hh := hetasq v; rw [h, zero_mul] at hh; norm_num at hh
    have hetaedge (a b : V) (hab : H.Adj a b) : eta a = sign a.val ∧ eta b = sign b.val := by
      obtain ⟨hne, i, hi, ha, hb⟩ := hab
      have hsa : a.val ∈ selected (active weights) q := Finset.mem_biUnion.mpr ⟨i, hi, ha⟩
      have hsb : b.val ∈ selected (active weights) q := Finset.mem_biUnion.mpr ⟨i, hi, hb⟩
      exact ⟨if_pos hsa, if_pos hsb⟩
    have hchar (ell : Module.Dual ℝ (Ambient n)) : ell ∈ W.dualAnnihilator ↔ (∀ j ∈ Z, ell (Pi.single j 1) = 0) ∧ (∀ a b : V, H.Adj a b →
          eta a * ell (Pi.single a.val 1) = eta b * ell (Pi.single b.val 1)) := by
      rw [actual_signed_face_annihilator I weights hI q hq sign ell]; constructor
      · rintro ⟨hz, he⟩; refine ⟨hz, ?_⟩
        intro a b hab; rw [(hetaedge a b hab).1, (hetaedge a b hab).2]
        exact he a b hab
      · rintro ⟨hz, he⟩; refine ⟨hz, ?_⟩
        intro a b hab; have hh := he a b hab
        rwa [(hetaedge a b hab).1, (hetaedge a b hab).2] at hh
    have hkernel (ell : W.dualAnnihilator) : (fun v : V => eta v * ell.val (Pi.single v.val 1)) ∈ K := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply]; exact H.lapMatrix_mulVec_eq_zero_iff_forall_adj.mpr ((hchar ell.val).mp ell.property).2
    let f : W.dualAnnihilator →ₗ[ℝ] (O → ℝ) × K := {
      toFun := fun ell => (fun j => ell.val (Pi.single j.val 1),
        ⟨fun v => eta v * ell.val (Pi.single v.val 1), hkernel ell⟩)
      map_add' := by
        intro a b; apply Prod.ext
        · funext j; simp
        · apply Subtype.ext; funext v; simp [mul_add]
      map_smul' := by
        intro r a; apply Prod.ext
        · funext j; simp
        · apply Subtype.ext; funext v; simp [mul_left_comm] }
    have hfinj : Function.Injective f := by
      intro a b hab; apply Subtype.ext
      apply (Pi.basisFun ℝ (Fin n)).ext
      intro j; simp only [Pi.basisFun_apply]
      by_cases hjz : j ∈ Z
      · rw [((hchar a.val).mp a.property).1 j hjz, ((hchar b.val).mp b.property).1 j hjz]
      · by_cases hjv : j ∈ vertexSet I (active weights) q
        · have he := congrArg (fun p : (O → ℝ) × K => p.2.val ⟨j, hjv⟩) hab
          exact mul_left_cancel₀ (hetane ⟨j, hjv⟩) he
        · have hjo : j ∉ U := fun hu => hjv (Finset.mem_sdiff.mpr ⟨hu, hjz⟩)
          exact congrArg (fun p : (O → ℝ) × K => p.1 ⟨j, hjo⟩) hab
    have hfsurj : Function.Surjective f := by
      intro p; let coeff : Fin n → ℝ := fun j =>
        if hjz : j ∈ Z then 0 else
        if hjv : j ∈ vertexSet I (active weights) q then eta ⟨j, hjv⟩ * p.2.val ⟨j, hjv⟩
        else p.1 ⟨j, fun hu => hjv (Finset.mem_sdiff.mpr ⟨hu, hjz⟩)⟩
      let ell : Module.Dual ℝ (Ambient n) := (Pi.basisFun ℝ (Fin n)).constr ℝ coeff
      have hel (j : Fin n) : ell (Pi.single j 1) = coeff j := by
        simpa only [ell, Pi.basisFun_apply] using (Pi.basisFun ℝ (Fin n)).constr_basis ℝ coeff j
      have hvz (v : V) : v.val ∉ Z := (Finset.mem_sdiff.mp v.property).2
      have hev (v : V) : eta v * ell (Pi.single v.val 1) = p.2.val v := by
        rw [hel]; simp only [coeff, dif_neg (hvz v), dif_pos v.property]
        rw [← mul_assoc, hetasq, one_mul]
      have hell : ell ∈ W.dualAnnihilator := by
        apply (hchar ell).mpr
        constructor
        · intro j hj; rw [hel]; simp only [coeff, dif_pos hj]
        · intro a b hab; rw [hev, hev]
          have hp : (H.lapMatrix ℝ).mulVec p.2.val = 0 := by simpa only [K, LinearMap.mem_ker, Matrix.toLin'_apply] using p.2.property
          exact H.lapMatrix_mulVec_eq_zero_iff_forall_adj.mp hp a b hab
      refine ⟨⟨ell, hell⟩, ?_⟩
      apply Prod.ext
      · funext j; change ell (Pi.single j.val 1) = p.1 j
        rw [hel]; have hjz : j.val ∉ Z := by
          intro hz; obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hz
          exact j.property (Finset.mem_biUnion.mpr ⟨i, hq.1 hi, hji⟩)
        have hjv : j.val ∉ vertexSet I (active weights) q :=
          fun hv => j.property (Finset.mem_sdiff.mp hv).1
        simp only [coeff, dif_neg hjz, dif_neg hjv]; rfl
      · apply Subtype.ext; funext v; exact hev v
    let equiv := LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
    have hdim : Module.finrank ℝ W.dualAnnihilator = Fintype.card O + Nat.card (Component I (active weights) q) := by
      rw [equiv.finrank_eq, Module.finrank_prod, Module.finrank_pi]; have hgraph := H.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix
      simpa only [K, H, Nat.card_eq_fintype_card] using congrArg (fun x => Fintype.card O + x) hgraph.symm
    have hpartition : Fintype.card O + U.card = n := by
      have ho : Fintype.card O = n - U.card := by
        dsimp [O]; rw [Fintype.card_subtype_compl]
        simp only [Fintype.card_fin, Fintype.card_coe]
      have hu : U.card ≤ n := by simpa using Finset.card_le_univ U
      omega
    have hdual := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    rw [hdim, Module.finrank_pi] at hdual; have htotal : Module.finrank ℝ W + Nat.card (Component I (active weights) q) = U.card := by
      simp only [Fintype.card_fin] at hdual; omega
    dsimp [W, U] at htotal ⊢; omega
  let admissible : RawData n m → Prop := fun q =>
    feasible I (active weights) q ∧ (support I (active weights)).card - Nat.card (Component I (active weights) q) = r
  let Good := {q : RawData n m // admissible q}
  let Signed := Σ q : Good, ({j // j ∈ selected (active weights) q.val} → Bool)
  let Faces := {F : Set (Ambient n) // F.Nonempty ∧ IsExposed ℝ (actualQ I weights) F ∧ Module.finrank ℝ (affineSpan ℝ F).direction = r}
  let sg (p : Signed) : Fin n → ℝ := fun j =>
    if hj : j ∈ selected (active weights) p.1.val then if p.2 ⟨j, hj⟩ then 1 else -1
    else 1
  have hsg (p : Signed) : ∀ j ∈ selected (active weights) p.1.val, sg p j = 1 ∨ sg p j = -1 := by intro j hj; dsimp [sg]; rw [dif_pos hj]; split <;> simp
  have sameface (q : RawData n m) (s t : Fin n → ℝ) (he : ∀ j ∈ selected (active weights) q, s j = t j) :
      signedFace I weights q s = signedFace I weights q t := by
    unfold signedFace; apply Finset.sum_congr rfl
    intro i hi; congr 1
    unfold chosenHull; split_ifs with hiq
    · rfl
    · congr 1; ext x
      have hsel {j : Fin n} (hj : j ∈ q.2 i) : j ∈ selected (active weights) q :=
        Finset.mem_biUnion.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hi, hiq⟩, hj⟩
      constructor
      · rintro ⟨j, hj, hx⟩; exact ⟨j, hj, by rwa [← he j (hsel hj)]⟩
      · rintro ⟨j, hj, hx⟩; exact ⟨j, hj, by rwa [he j (hsel hj)]⟩
  have hface (p : Signed) : (signedFace I weights p.1.val (sg p)).Nonempty ∧ IsExposed ℝ (actualQ I weights) (signedFace I weights p.1.val (sg p)) ∧
      Module.finrank ℝ (affineSpan ℝ (signedFace I weights p.1.val (sg p))).direction = r := by
    obtain ⟨l, hl, hne, hC⟩ := feasible_realizes_actual_sum_face I weights hI hw p.1.val p.1.property.1 (sg p) (hsg p)
    refine ⟨hne, ?_, ?_⟩
    · rw [← hl]; exact ContinuousLinearMap.toExposed.isExposed
    · exact (actual_signed_face_finrank I weights hI p.1.val p.1.property.1.1 (sg p) (hsg p)).trans p.1.property.2
  let toFace : Signed → Faces := fun p => ⟨signedFace I weights p.1.val (sg p), hface p⟩
  have hinj : Function.Injective toFace := by
    rintro ⟨q, s⟩ ⟨p, t⟩ heq; have he := equal_actual_signed_faces_recover_data_and_signs I weights hI hw
      q.val p.val q.property.1 p.property.1 (sg ⟨q,s⟩) (sg ⟨p,t⟩)
      (hsg ⟨q,s⟩) (hsg ⟨p,t⟩) (congrArg Subtype.val heq)
    have hqp : q = p := Subtype.ext he.1
    subst p; congr 1
    funext j; have hsj := he.2 j.val j.property
    cases hs : s j <;> cases ht : t j <;>
      first | rfl | (exfalso; norm_num [sg, j.property, hs, ht] at hsj)
  have hsurj : Function.Surjective toFace := by
    intro F; obtain ⟨q, s, hq, hs, hF⟩ := actual_exposed_face_has_feasible_data I weights hI hw F.val F.property.1 F.property.2.1
    have hdim : (support I (active weights)).card - Nat.card (Component I (active weights) q) = r := by
      rw [← actual_signed_face_finrank I weights hI q hq.1 s hs, ← hF]; exact F.property.2.2
    let qg : Good := ⟨q, hq, hdim⟩
    let b : {j // j ∈ selected (active weights) q} → Bool := fun j => decide (s j.val = 1)
    have hsge : ∀ j ∈ selected (active weights) q, sg ⟨qg, b⟩ j = s j := by
      intro j hj; dsimp [sg, qg]
      rw [dif_pos hj]; rcases hs j hj with h | h <;> norm_num [b, h]
    refine ⟨⟨qg,b⟩, Subtype.ext ?_⟩
    change signedFace I weights q (sg ⟨qg,b⟩) = F.val; exact (sameface q _ _ hsge).trans hF.symm
  let _ : Fintype Good := Fintype.ofFinite Good
  have hcard : Nat.card Signed = combinatorialSum I weights r := by
    rw [Nat.card_sigma]; simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    unfold combinatorialSum; change (∑ q : Good, 2 ^ (selected (active weights) q.val).card) =
      ∑ q : RawData n m, if admissible q then 2 ^ (selected (active weights) q).card else 0
    rw [← Finset.sum_filter]; exact (Finset.sum_subtype (Finset.univ.filter admissible) (by simp) (fun q => 2 ^ (selected (active weights) q).card)).symm
  exact (Nat.card_congr (Equiv.ofBijective toFace ⟨hinj, hsurj⟩)).symm.trans hcard
end D5.S3.Combinatorics.Geometry.CrossPolytopeFaceCounts
