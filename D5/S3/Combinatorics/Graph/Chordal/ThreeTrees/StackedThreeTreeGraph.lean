/- GID: D5/S3/Combinatorics/Graph/Chordal/ThreeTrees/StackedThreeTreeGraph
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The simple graph and oriented triangle enumeration of a three-tree stacking history. -/

import OmegaBuild.Commands
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import D5.S3.Combinatorics.Graph.Chordal.ThreeTrees.StackedTriangleCurvature

compile_only_with_mathlib

/-! The simple graph and oriented triangle enumeration of a three-tree stacking history. -/

namespace StackedTriangleCurvature

/-- The three vertices of an oriented face, viewed as an unordered set. -/
def Build.faceVertices {n : ℕ} (b : Build n) (i : Face n) : Set (Vertex n) :=
  let t := b.triangle i
  {t.1, t.2.1, t.2.2}

/-- The graph obtained by joining each new vertex to the three vertices of its parent face. -/
def Build.graph : {n : ℕ} → Build n → SimpleGraph (Vertex n)
  | _, .root => ⊤
  | _, .attach b p => {
      Adj := fun
        | .inl u, .inl v => b.graph.Adj u v
        | .inl u, .inr _ => u ∈ b.faceVertices p
        | .inr _, .inl v => v ∈ b.faceVertices p
        | .inr _, .inr _ => False
      symm := by
        constructor
        rintro (u | ⟨⟩) (v | ⟨⟩) h
        · exact h.symm
        · exact h
        · exact h
        · exact h
      loopless := by
        constructor
        rintro (u | ⟨⟩)
        · exact b.graph.irrefl
        · exact id
    }

private theorem faceVertices_inl {n : ℕ} (b : Build n) (p i : Face n) :
    (b.attach p).faceVertices (Sum.inl i) = Sum.inl '' b.faceVertices i := by
  simp [Build.faceVertices, Build.triangle, Set.image_insert_eq]

private theorem faceVertices_inr {n : ℕ} (b : Build n) (p : Face n) :
    let t := b.triangle p
    (b.attach p).faceVertices (Sum.inr 0) = {Sum.inl t.1, Sum.inl t.2.1, Sum.inr ()} ∧
    (b.attach p).faceVertices (Sum.inr 1) = {Sum.inl t.2.1, Sum.inl t.2.2, Sum.inr ()} ∧
    (b.attach p).faceVertices (Sum.inr 2) = {Sum.inl t.2.2, Sum.inl t.1, Sum.inr ()} :=
  ⟨rfl, rfl, rfl⟩

/-- Each listed face is a clique in the actual stacking graph. -/
theorem Build.faceVertices_isClique {n : ℕ} (b : Build n) (i : Face n) :
    b.graph.IsClique (b.faceVertices i) := by
  induction b with
  | root =>
    intro u hu v hv hne
    exact hne
  | @attach n b p ih =>
    rcases i with i | i
    · rw [faceVertices_inl]
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ h
      exact ih i hu hv fun e => h (congrArg Sum.inl e)
    · let t := b.triangle p
      have hm : ∀ {u v : Vertex n}, u ∈ b.faceVertices p → v ∈ b.faceVertices p →
          (b.attach p).graph.IsClique {Sum.inl u, Sum.inl v, Sum.inr ()} := by
        intro u v hu hv x hx y hy hxy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        all_goals first
          | exact (hxy rfl).elim
          | exact hu
          | exact hv
          | exact (ih p) hu hv (fun e => hxy (congrArg Sum.inl e))
          | exact (ih p) hv hu (fun e => hxy (congrArg Sum.inl e))
      have h0 : t.1 ∈ b.faceVertices p := by simp [Build.faceVertices, t]
      have h1 : t.2.1 ∈ b.faceVertices p := by simp [Build.faceVertices, t]
      have h2 : t.2.2 ∈ b.faceVertices p := by simp [Build.faceVertices, t]
      fin_cases i
      · exact hm h0 h1
      · exact hm h1 h2
      · exact hm h2 h0

private theorem exists_new_face {n : ℕ} (b : Build n) (p : Face n) (u v : Vertex n)
    (hu : u ∈ b.faceVertices p) (hv : v ∈ b.faceVertices p) (h : u ≠ v) :
    ∃ i : Face (n + 1), (b.attach p).faceVertices i = {Sum.inl u, Sum.inl v, Sum.inr ()} := by
  let t := b.triangle p
  have hs := faceVertices_inr b p
  change u ∈ ({t.1, t.2.1, t.2.2} : Set (Vertex n)) at hu
  change v ∈ ({t.1, t.2.1, t.2.2} : Set (Vertex n)) at hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  all_goals try exact (h rfl).elim
  · exact ⟨Sum.inr 0, hs.1⟩
  · exact ⟨Sum.inr 2, hs.2.2.trans (Set.insert_comm _ _ _)⟩
  · exact ⟨Sum.inr 0, hs.1.trans (Set.insert_comm _ _ _)⟩
  · exact ⟨Sum.inr 1, hs.2.1⟩
  · exact ⟨Sum.inr 2, hs.2.2⟩
  · exact ⟨Sum.inr 1, hs.2.1.trans (Set.insert_comm _ _ _)⟩

/-- Every triangle of the actual stacking graph appears in the oriented enumeration. -/
theorem Build.exists_face_of_triangle {n : ℕ} (b : Build n) {u v w : Vertex n}
    (huv : b.graph.Adj u v) (hvw : b.graph.Adj v w) (hwu : b.graph.Adj w u) :
    ∃ i : Face n, b.faceVertices i = {u, v, w} := by
  induction b with
  | root =>
    have h : ∀ i : Fin 3, i = u ∨ i = v ∨ i = w := by
      intro i
      fin_cases u <;> fin_cases v <;> fin_cases w <;> fin_cases i <;>
        simp_all [Build.graph, SimpleGraph.top_adj]
    refine ⟨(), Set.eq_univ_of_forall ?_ |>.trans (Set.eq_univ_of_forall ?_).symm⟩
    · intro i
      fin_cases i <;> simp [Build.faceVertices, Build.triangle]
    · intro i
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h i
  | @attach n b p ih =>
    rcases u with u | ⟨⟩ <;> rcases v with v | ⟨⟩ <;> rcases w with w | ⟨⟩
    · obtain ⟨i, hi⟩ := ih huv hvw hwu
      refine ⟨Sum.inl i, ?_⟩
      rw [faceVertices_inl, hi]
      simp [Set.image_insert_eq]
    · exact exists_new_face b p u v hwu hvw (fun e => huv.ne (congrArg Sum.inl e))
    · obtain ⟨i, hi⟩ := exists_new_face b p u w huv hvw (fun e => hwu.ne (congrArg Sum.inl e.symm))
      refine ⟨i, hi.trans ?_⟩
      ext j
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop
    · exact False.elim hvw
    · obtain ⟨i, hi⟩ := exists_new_face b p v w huv hwu (fun e => hvw.ne (congrArg Sum.inl e))
      refine ⟨i, hi.trans ?_⟩
      ext j
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop
    · exact False.elim hwu
    · exact False.elim huv
    · exact False.elim huv

private theorem exists_flat_potential {n : ℕ} (b : Build n) (g : Vertex n → Vertex n → ℝ)
    (hr : ∀ u v, g v u = -g u v) (hz : b.curvature g = 0) :
    ∃ p : Vertex n → ℝ, ∀ u v, b.graph.Adj u v → g u v = p v - p u := by
  induction b with
  | root =>
    refine ⟨fun v => g 0 v, fun u v huv => ?_⟩
    have h := congrFun hz ()
    change g 0 1 + g 1 2 + g 2 0 = 0 at h
    have h00 : g 0 0 = 0 := by linarith [hr 0 0]
    fin_cases u <;> fin_cases v
    all_goals try exact (huv.ne rfl).elim
    · change g 0 1 = g 0 1 - g 0 0
      rw [h00, sub_zero]
    · change g 0 2 = g 0 2 - g 0 0
      rw [h00, sub_zero]
    · change g 1 0 = g 0 0 - g 0 1
      linarith [hr 0 1]
    · change g 1 2 = g 0 2 - g 0 1
      linarith [hr 0 2]
    · change g 2 0 = g 0 0 - g 0 2
      linarith [hr 0 2]
    · change g 2 1 = g 0 1 - g 0 2
      linarith [hr 0 2, hr 1 2]
  | @attach n b t ih =>
    let old (u v : Vertex n) := g (Sum.inl u) (Sum.inl v)
    have hold : b.curvature old = 0 := by
      funext i
      simpa [Build.curvature, Build.triangle, old] using congrFun hz (Sum.inl i)
    obtain ⟨p, hp⟩ := ih old (fun u v => hr _ _) hold
    let a := (b.triangle t).1
    let u := (b.triangle t).2.1
    let v := (b.triangle t).2.2
    have ha : a ∈ b.faceVertices t := by simp [Build.faceVertices, a]
    have hu : u ∈ b.faceVertices t := by simp [Build.faceVertices, u]
    have hv : v ∈ b.faceVertices t := by simp [Build.faceVertices, v]
    have hn := b.triangle_distinct t
    have hab := hp a u (b.faceVertices_isClique t ha hu hn.1)
    have hca := hp v a (b.faceVertices_isClique t hv ha hn.2.2)
    let fresh : Vertex (n + 1) := Sum.inr ()
    let q : Vertex (n + 1) → ℝ := Sum.elim p (fun _ => p a + g (Sum.inl a) fresh)
    have ha' : ∀ j : Vertex n, j ∈ b.faceVertices t →
        g (Sum.inl j) fresh = q fresh - q (Sum.inl j) := by
      intro j hj
      have h₀ := congrFun hz (Sum.inr 0)
      change old a u + g (Sum.inl u) fresh + g fresh (Sum.inl a) = 0 at h₀
      have h₂ := congrFun hz (Sum.inr 2)
      change old v a + g (Sum.inl a) fresh + g fresh (Sum.inl v) = 0 at h₂
      change j ∈ ({a, u, v} : Set (Vertex n)) at hj
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
      rcases hj with rfl | rfl | rfl <;>
        change g (Sum.inl _) fresh = p a + g (Sum.inl a) fresh - p _
      · ring
      · linarith [hr (Sum.inl a) fresh]
      · linarith [hr (Sum.inl v) fresh]
    refine ⟨q, ?_⟩
    rintro (i | ⟨⟩) (j | ⟨⟩) hij
    · exact hp i j hij
    · exact ha' i hij
    · change g fresh (Sum.inl j) = q (Sum.inl j) - q fresh
      rw [hr (Sum.inl j) fresh, ha' j hij]
      ring
    · exact False.elim hij

/-- Scalar gains alternate on ordered edges and vanish on nonedges. -/
def Build.EdgeGains {n : ℕ} (b : Build n) : Submodule ℝ (Vertex n → Vertex n → ℝ) where
  carrier := {g | (∀ u v, g v u = -g u v) ∧ (∀ u v, ¬ b.graph.Adj u v → g u v = 0)}
  zero_mem' := by simp
  add_mem' := by
    rintro g h ⟨hgr, hg⟩ ⟨hhr, hh⟩
    exact ⟨fun u v => by simp [hgr u v, hhr u v, add_comm], fun u v e => by simp [hg u v e, hh u v e]⟩
  smul_mem' := by
    rintro k g ⟨hr, hg⟩
    exact ⟨fun u v => by simp [hr u v, mul_neg], fun u v e => by simp [hg u v e]⟩

/-- Differences of a vertex potential, supported on the graph edges. -/
noncomputable def Build.edgeGradient {n : ℕ} (b : Build n) (p : Vertex n → ℝ) : b.EdgeGains := by
  classical
  refine ⟨fun u v => if b.graph.Adj u v then p v - p u else 0, ?_⟩
  refine ⟨fun u v => ?_, fun u v h => ite_eq_right h⟩
  by_cases h : b.graph.Adj u v
  · simp only [h, h.symm, ite_true, neg_sub]
  · have hr : ¬ b.graph.Adj v u := fun he => h he.symm
    simp only [h, hr, ite_false, neg_zero]

private def curvatureMap {n : ℕ} (b : Build n) : b.EdgeGains →ₗ[ℝ] (Face n → ℝ) where
  toFun g := b.curvature g.val
  map_add' g h := by
    funext i
    simp [Build.curvature]
    ring
  map_smul' k g := by
    funext i
    simp [Build.curvature]
    ring

/-- Every linear functional on skew edge gains that vanishes on gradients is the
boundary pairing of an oriented triangle filling. -/
theorem Build.exists_faceChain_of_cycle {n : ℕ} (b : Build n)
    (z : b.EdgeGains →ₗ[ℝ] ℝ) (hz : ∀ p, z (b.edgeGradient p) = 0) :
    ∃ a : FaceChain n, ∀ g : b.EdgeGains, z g = a.pair (b.curvature g.val) := by
  classical
  let d := curvatureMap b
  have hker : d.ker ≤ z.ker := by
    intro g hg
    have hg' : b.curvature g.val = 0 := hg
    obtain ⟨p, hp⟩ := exists_flat_potential b g.val g.prop.1 hg'
    have he : g = b.edgeGradient p := by
      apply Subtype.ext
      funext u v
      by_cases h : b.graph.Adj u v
      · simpa [Build.edgeGradient, h] using hp u v h
      · simpa [Build.edgeGradient, h] using g.prop.2 u v h
    rw [he]
    exact hz p
  let z' := d.ker.liftQ z hker
  let zR := z'.comp d.quotKerEquivRange.symm.toLinearMap
  obtain ⟨f, hf⟩ := zR.exists_extend
  let a : FaceChain n := WithLp.toLp 1 (fun i => f (Pi.single i 1))
  refine ⟨a, fun g => ?_⟩
  have hfg : f (d g) = z g := by
    have he := LinearMap.congr_fun hf (d.quotKerEquivRange (Submodule.Quotient.mk g))
    simpa [zR, z'] using he
  rw [← hfg]
  calc
    f (d g) = f (∑ i, Pi.single i (d g i)) := by rw [Finset.univ_sum_single]
    _ = ∑ i, f (d g i • Pi.single i 1) := by simp [← Pi.single_smul]
    _ = a.pair (b.curvature g.val) := by simp [FaceChain.pair, a, d, curvatureMap, mul_comm]

/-- Edge arrays are paired by summing over both orientations and dividing by two. -/
noncomputable def Build.edgePairing {n : ℕ} (b : Build n) (z : b.EdgeGains) :
    b.EdgeGains →ₗ[ℝ] ℝ where
  toFun g := (∑ u, ∑ v, z.val u v * g.val u v) / 2
  map_add' g h := by
    change (∑ u, ∑ v, z.val u v * (g.val u v + h.val u v)) / 2 = _
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  map_smul' k g := by
    change (∑ u, ∑ v, z.val u v * (k * g.val u v)) / 2 =
      k * ((∑ u, ∑ v, z.val u v * g.val u v) / 2)
    simp only [mul_left_comm (z.val _ _), ← Finset.mul_sum]
    ring

/-- Every divergence-free alternating edge array is the boundary of an oriented
triangle filling. Equality is tested on skew edge gains using the edge pairing. -/
theorem Build.exists_faceChain_of_divergence_free {n : ℕ} (b : Build n)
    (z : b.EdgeGains) (hz : ∀ u, ∑ v, z.val u v = 0) :
    ∃ a : FaceChain n, ∀ g : b.EdgeGains, b.edgePairing z g = a.pair (b.curvature g.val) := by
  apply b.exists_faceChain_of_cycle (b.edgePairing z)
  intro p
  have ha (u v : Vertex n) : z.val u v * (b.edgeGradient p).val u v =
      z.val u v * (p v - p u) := by
    by_cases h : b.graph.Adj u v
    · simp [Build.edgeGradient, h]
    · simp [z.prop.2 u v h]
  have hin (u : Vertex n) : ∑ v, z.val v u = 0 := by
    simp_rw [z.prop.1 u]
    rw [Finset.sum_neg_distrib, hz u, neg_zero]
  change (∑ u, ∑ v, z.val u v * (b.edgeGradient p).val u v) / 2 = 0
  simp only [ha, mul_sub, Finset.sum_sub_distrib]
  have h₁ : (∑ u, ∑ v, z.val u v * p v) = 0 := by
    rw [Finset.sum_comm]
    simp [← Finset.sum_mul, hin]
  have h₂ : (∑ u, ∑ v, z.val u v * p u) = 0 := by
    simp [← Finset.sum_mul, hz]
  rw [h₁, h₂]
  norm_num

private noncomputable def restrictGain {n : ℕ} (b : Build n)
    (g : Vertex n → Vertex n → ℝ) (hg : ∀ u v, g v u = -g u v) : b.EdgeGains := by
  classical
  refine ⟨fun u v => if b.graph.Adj u v then g u v else 0, ?_⟩
  refine ⟨fun u v => ?_, fun u v h => ite_eq_right h⟩
  by_cases h : b.graph.Adj u v
  · simp only [h, h.symm, ite_true, hg u v]
  · have hr : ¬ b.graph.Adj v u := fun he => h he.symm
    simp only [h, hr, ite_false, neg_zero]

private theorem curvature_restrictGain {n : ℕ} (b : Build n)
    (g : Vertex n → Vertex n → ℝ) (hg : ∀ u v, g v u = -g u v) :
    b.curvature (restrictGain b g hg).val = b.curvature g := by
  funext i
  let t := b.triangle i
  have ht : t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.2.2 ≠ t.1 := b.triangle_distinct i
  have h0 : t.1 ∈ b.faceVertices i := by simp [Build.faceVertices, t]
  have h1 : t.2.1 ∈ b.faceVertices i := by simp [Build.faceVertices, t]
  have h2 : t.2.2 ∈ b.faceVertices i := by simp [Build.faceVertices, t]
  have hc := b.faceVertices_isClique i
  have h01 := hc h0 h1 ht.1
  have h12 := hc h1 h2 ht.2.1
  have h20 := hc h2 h0 ht.2.2
  change (restrictGain b g hg).val t.1 t.2.1 + (restrictGain b g hg).val t.2.1 t.2.2 +
    (restrictGain b g hg).val t.2.2 t.1 = g t.1 t.2.1 + g t.2.1 t.2.2 + g t.2.2 t.1
  simp [restrictGain, h01, h12, h20]

/-- Unit gains on edges oriented by a strict ranking. -/
noncomputable def Build.orderGain {n : ℕ} (b : Build n) (r : Vertex n ↪ ℝ) : b.EdgeGains := by
  classical
  let g (u v : Vertex n) : ℝ := if u = v then 0 else if r u < r v then 1 else -1
  refine restrictGain b g ?_
  intro u v
  by_cases h : u = v
  · subst v
    simp [g]
  · have hne : r u ≠ r v := fun e => h (r.injective e)
    rcases lt_or_gt_of_ne hne with hr | hr <;> simp [g, h, Ne.symm h, hr, hr.not_gt]

private theorem curvature_orderGain {n : ℕ} (b : Build n) (r : Vertex n ↪ ℝ) :
    b.curvature (b.orderGain r).val = b.orderCurvature r := by
  classical
  unfold Build.orderGain
  rw [curvature_restrictGain]
  funext i
  let t := b.triangle i
  let rankSign (u v : Vertex n) : ℝ := if r u < r v then 1 else -1
  have h : t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.2.2 ≠ t.1 := b.triangle_distinct i
  change ((if t.1 = t.2.1 then 0 else rankSign t.1 t.2.1) +
    (if t.2.1 = t.2.2 then 0 else rankSign t.2.1 t.2.2) +
    (if t.2.2 = t.1 then 0 else rankSign t.2.2 t.1)) =
    rankSign t.1 t.2.1 + rankSign t.2.1 t.2.2 + rankSign t.2.2 t.1
  simp only [h.1, h.2.1, h.2.2, ite_false]

private theorem same_boundary_iff {n : ℕ} (b : Build n) (a c : FaceChain n) :
    (Submodule.Quotient.mk a : b.TriangleCycles) = Submodule.Quotient.mk c ↔
    ∀ g : b.EdgeGains, a.pair (b.curvature g.val) = c.pair (b.curvature g.val) := by
  rw [Submodule.Quotient.eq b.zeroBoundary]
  have hd (x : Face n → ℝ) : (a - c).pair x = a.pair x - c.pair x := by
    simp [FaceChain.pair, sub_mul, Finset.sum_sub_distrib]
  constructor
  · intro ha g
    exact sub_eq_zero.mp ((hd _).symm.trans (ha g.val g.prop.1))
  · intro h g hg
    rw [hd, ← curvature_restrictGain b g hg, h (restrictGain b g hg), sub_self]

/-- The triangle-filling norm is the infimum of ℓ¹ costs of fillings of the edge array. -/
noncomputable def Build.triangleFillingNorm {n : ℕ} (b : Build n) (z : b.EdgeGains) : ℝ :=
  sInf {t | ∃ a : FaceChain n,
    (∀ g : b.EdgeGains, b.edgePairing z g = a.pair (b.curvature g.val)) ∧
      (∑ i, |a i|) = t}

/-- The triangle-filling norm of any divergence-free edge array is the maximum of its
pairings with total-order gains on the actual stacking graph. -/
theorem Build.triangleFillingNorm_eq_orderMaximum {n : ℕ} (b : Build n)
    (z : b.EdgeGains) (hz : ∀ u, ∑ v, z.val u v = 0) :
    ∃ r : Vertex n ↪ ℝ, b.triangleFillingNorm z = b.edgePairing z (b.orderGain r) ∧
      ∀ s : Vertex n ↪ ℝ, b.edgePairing z (b.orderGain s) ≤ b.edgePairing z (b.orderGain r) := by
  obtain ⟨a, ha⟩ := b.exists_faceChain_of_divergence_free z hz
  have hn : b.triangleFillingNorm z = ‖(Submodule.Quotient.mk a : b.TriangleCycles)‖ := by
    rw [b.triangleNorm_eq_inf, Build.triangleFillingNorm]
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq, same_boundary_iff]
    constructor <;> rintro ⟨c, hc, he⟩
    · refine ⟨c, fun g => ?_, he⟩
      exact (hc g).symm.trans (ha g)
    · exact ⟨c, fun g => (ha g).trans (hc g).symm, he⟩
  obtain ⟨r, hr, hm⟩ := b.triangleNorm_eq_orderMaximum a
  have hscore (r : Vertex n ↪ ℝ) : b.edgePairing z (b.orderGain r) = a.pair (b.orderCurvature r) :=
    (ha (b.orderGain r)).trans (congrArg a.pair (curvature_orderGain b r))
  exact ⟨r, hn.trans (hr.trans (hscore r).symm),
    fun s => (hscore s).le.trans ((hm s).trans_eq (hscore r).symm)⟩

end StackedTriangleCurvature
