/- GID: D5/S3/Combinatorics/Graph/QuadraticLoad/NativeTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/QuadraticLoad/NativeTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Sion, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Prod]
   utility: none
   digest: Native quadratic allocations transport along graph injections and tensorize on Cartesian products. -/

import D5.S3.Combinatorics.Graph.QuadraticEdgeLoad
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Mul
import Mathlib.Topology.Sion

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Finset Set
open D5.S3.Combinatorics.Graph.QuadraticEdgeLoad

namespace D5.S3.Combinatorics.Graph.QuadraticLoad.NativeTransport

variable {V W : Type*} [Fintype V] [Fintype W] [Nonempty V] [Nonempty W]
variable (G : SimpleGraph V) (H : SimpleGraph W)
variable [DecidableRel G.Adj] [DecidableRel H.Adj]

private theorem pullback_load_le (f : V → W) (hi : Function.Injective f)
    (hf : ∀ v w, G.Adj v w → H.Adj (f v) (f w))
    (a : W → W → ℝ) (v : V) :
    load G (fun v w => a (f v) (f w)) v ≤ load H a (f v) := by
  classical
  unfold load
  change (∑ c ∈ G.neighborFinset v, (a (f v) (f c)) ^ 2) ≤ _
  calc
    _ = ∑ c ∈ (G.neighborFinset v).image f, (a (f v) c) ^ 2 :=
      (sum_image (fun x _ y _ h => hi h)).symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro w hw
        obtain ⟨u, hu, rfl⟩ := mem_image.mp hw
        exact (H.mem_neighborFinset _ _).mpr (hf _ _ ((G.mem_neighborFinset _ _).mp hu))
      · intro w hw hn
        exact sq_nonneg _

/-- Every ambient allocation restricts to the injectively embedded native graph. -/
theorem kappa_le_of_injective_hom (f : V → W) (hi : Function.Injective f)
    (hf : ∀ v w, G.Adj v w → H.Adj (f v) (f w)) : kappa G ≤ kappa H := by
  classical
  obtain ⟨a, ha, hmin⟩ := minimum_attained H
  let b : V → V → ℝ := fun v w => a (f v) (f w)
  have hb : Feasible G b := ⟨fun v w => ha.1 _ _, fun v w hvw => ha.2 _ _ (hf _ _ hvw)⟩
  apply (kappa_le G b hb).trans
  rw [← hmin]
  apply sup'_le
  intro v hv
  exact (pullback_load_le G H f hi hf a v).trans (load_le_maxLoad H a (f v))

private def boxAllocation (a : V → V → ℝ) (b : W → W → ℝ)
    (x y : V × W) : ℝ := if x.1 = y.1 then b x.2 y.2 else a x.1 y.1

private theorem box_feasible (a : V → V → ℝ) (b : W → W → ℝ)
    (ha : Feasible G a) (hb : Feasible H b) :
    Feasible (G □ H) (boxAllocation a b) := by
  classical
  constructor
  · intro x y
    unfold boxAllocation
    split_ifs <;> [exact hb.1 _ _; exact ha.1 _ _]
  · intro x y hxy
    rcases hxy with ⟨hg, he⟩ | ⟨hh, he⟩
    · have hn := hg.ne
      simp only [boxAllocation, if_neg hn, if_neg hn.symm]
      exact ha.2 _ _ hg
    · simp only [boxAllocation, if_pos he, if_pos he.symm]
      exact hb.2 _ _ hh

private theorem box_load (a : V → V → ℝ) (b : W → W → ℝ) (x : V × W) :
    load (G □ H) (boxAllocation a b) x = load G a x.1 + load H b x.2 := by
  classical
  rw [load, SimpleGraph.neighborFinset_boxProd, sum_disjUnion]
  simp only [sum_product, sum_singleton, boxAllocation, ite_true]
  congr 1
  apply sum_congr rfl
  intro v hv
  rw [if_neg ((G.mem_neighborFinset _ _).mp hv).ne]

private theorem feasible_compact : IsCompact {a : V → V → ℝ | Feasible G a} := by
  have he : IsClosed {a : V → V → ℝ | ∀ b c, G.Adj b c → a b c + a c b = 1} := by
    simp_rw [Set.ofPred_forall]
    exact isClosed_iInter fun b => isClosed_iInter fun c =>
      isClosed_iInter fun _ => isClosed_eq (by fun_prop) continuous_const
  have hi := (isCompact_Icc : IsCompact
    (Set.Icc (fun _ _ : V => (0 : ℝ)) (fun _ _ : V => (1 : ℝ))))
  convert hi.inter_right he using 1
  ext a
  simp only [Set.mem_inter_iff, Set.mem_Icc, Pi.le_def, Set.mem_ofPred_eq, Feasible]
  aesop

private theorem feasible_convex : Convex ℝ {a : V → V → ℝ | Feasible G a} := by
  intro a ha b hb s t hs ht hst
  constructor
  · intro v w
    change 0 ≤ s * a v w + t * b v w ∧ s * a v w + t * b v w ≤ 1
    constructor
    · exact add_nonneg (mul_nonneg hs (ha.1 _ _).1) (mul_nonneg ht (hb.1 _ _).1)
    · calc
        _ ≤ s * 1 + t * 1 := add_le_add
          (mul_le_mul_of_nonneg_left (ha.1 _ _).2 hs)
          (mul_le_mul_of_nonneg_left (hb.1 _ _).2 ht)
        _ = 1 := by nlinarith
  · intro v w hvw
    change (s * a v w + t * b v w) + (s * a w v + t * b w v) = 1
    have h1 := ha.2 _ _ hvw
    have h2 := hb.2 _ _ hvw
    nlinarith

private def payoff (a : V → V → ℝ) (p : V → ℝ) : ℝ := ∑ v, p v * load G a v

private theorem payoff_convex (p : V → ℝ) (hp : p ∈ stdSimplex ℝ V) :
    ConvexOn ℝ {a | Feasible G a} (fun a => payoff G a p) := by
  refine ⟨feasible_convex G, ?_⟩
  intro a ha b hb s t hs ht hst
  simp only [payoff, smul_eq_mul, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro v hv
  have hsq : load G (s • a + t • b) v ≤ s * load G a v + t * load G b v := by
    simp only [load, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro w hw
    change (s * a v w + t * b v w) ^ 2 ≤ s * (a v w) ^ 2 + t * (b v w) ^ 2
    exact (even_two.convexOn_pow (𝕜 := ℝ)).2 (Set.mem_univ _) (Set.mem_univ _) hs ht hst
  calc
    p v * load G (s • a + t • b) v ≤ p v * (s * load G a v + t * load G b v) :=
      mul_le_mul_of_nonneg_left hsq (hp.1 v)
    _ = _ := by ring

private theorem payoff_concave (a : V → V → ℝ) :
    ConcaveOn ℝ (stdSimplex ℝ V) (payoff G a) := by
  refine ⟨convex_stdSimplex ℝ V, ?_⟩
  intro p hp q hq s t hs ht hst
  simp only [payoff, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, mul_sum, ← sum_add_distrib]
  apply le_of_eq
  apply sum_congr rfl
  intro v hv
  ring

private theorem exists_lower_law : ∃ p ∈ stdSimplex ℝ V,
    ∀ a, Feasible G a → kappa G ≤ ∑ v, p v * load G a v := by
  classical
  have hc (p : V → ℝ) : Continuous (fun a : V → V → ℝ => payoff G a p) := by
    unfold payoff load
    fun_prop
  have hd (a : V → V → ℝ) : Continuous (payoff G a) := by unfold payoff; fun_prop
  obtain ⟨a, ha, p, hp, hsp⟩ := Sion.exists_isSaddlePointOn
    (X := {a : V → V → ℝ | Feasible G a}) (Y := stdSimplex ℝ V) (f := payoff G)
    ⟨_, half_feasible G⟩ (feasible_convex G) (feasible_compact G)
    (fun p hp => (hc p).continuousOn.lowerSemicontinuousOn)
    (fun p hp => (payoff_convex G p hp).quasiconvexOn)
    (convex_stdSimplex ℝ V) ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary V)⟩
    (isCompact_stdSimplex ℝ V)
    (fun a ha => (hd a).continuousOn.upperSemicontinuousOn)
    (fun a ha => (payoff_concave G a).quasiconcaveOn)
  refine ⟨p, hp, fun b hb => (kappa_le G a ha).trans ?_⟩
  apply sup'_le
  intro v hv
  have he := hsp b hb (Pi.single v 1) (single_mem_stdSimplex ℝ v)
  simpa [payoff, Pi.single_apply] using he

/-- The native infimum tensorizes without excluding zero probability masses. -/
theorem kappa_box : kappa (G □ H) = kappa G + kappa H := by
  classical
  apply le_antisymm
  · obtain ⟨a, ha, hma⟩ := minimum_attained G
    obtain ⟨b, hb, hmb⟩ := minimum_attained H
    apply (kappa_le (G □ H) _ (box_feasible G H a b ha hb)).trans
    apply sup'_le
    intro x hx
    rw [box_load]
    exact add_le_add (by simpa [hma] using load_le_maxLoad G a x.1)
      (by simpa [hmb] using load_le_maxLoad H b x.2)
  · obtain ⟨p, hp, hpL⟩ := exists_lower_law G
    obtain ⟨q, hq, hqL⟩ := exists_lower_law H
    obtain ⟨A, hA, hmA⟩ := minimum_attained (G □ H)
    have hleft (w : W) : Feasible G (fun v v' => A (v,w) (v',w)) := by
      refine ⟨fun v v' => hA.1 _ _, fun v v' he => hA.2 _ _ ?_⟩
      exact Or.inl ⟨he, rfl⟩
    have hright (v : V) : Feasible H (fun w w' => A (v,w) (v,w')) := by
      refine ⟨fun w w' => hA.1 _ _, fun w w' he => hA.2 _ _ ?_⟩
      exact Or.inr ⟨he, rfl⟩
    have hsplit (v : V) (w : W) : load (G □ H) A (v,w) =
        load G (fun v v' => A (v,w) (v',w)) v +
        load H (fun w w' => A (v,w) (v,w')) w := by
      simp only [load, SimpleGraph.neighborFinset_boxProd, sum_disjUnion,
        sum_product, sum_singleton]
    have hL : kappa G ≤ ∑ w, q w * ∑ v, p v * load G (fun v v' => A (v,w) (v',w)) v := by
      calc
        _ = ∑ w, q w * kappa G := by rw [← sum_mul, hq.2, one_mul]
        _ ≤ _ := sum_le_sum fun w _ => mul_le_mul_of_nonneg_left
          (hpL _ (hleft w)) (hq.1 w)
    have hR : kappa H ≤ ∑ v, p v * ∑ w, q w * load H (fun w w' => A (v,w) (v,w')) w := by
      calc
        _ = ∑ v, p v * kappa H := by rw [← sum_mul, hp.2, one_mul]
        _ ≤ _ := sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
          (hqL _ (hright v)) (hp.1 v)
    have htotal : (∑ w, q w * ∑ v, p v * load G (fun v v' => A (v,w) (v',w)) v) +
        (∑ v, p v * ∑ w, q w * load H (fun w w' => A (v,w) (v,w')) w) =
        ∑ v, ∑ w, (p v * q w) * load (G □ H) A (v,w) := by
      simp_rw [mul_sum]
      rw [sum_comm (f := fun w v => q w * (p v * load G (fun v v' => A (v,w) (v',w)) v))]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro v hv
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro w hw
      rw [hsplit]
      ring
    calc
      kappa G + kappa H ≤ _ := add_le_add hL hR
      _ = _ := htotal
      _ ≤ ∑ v, ∑ w, (p v * q w) * kappa (G □ H) := by
        apply sum_le_sum; intro v hv
        apply sum_le_sum; intro w hw
        exact mul_le_mul_of_nonneg_left (by simpa [hmA] using load_le_maxLoad (G □ H) A (v,w))
          (mul_nonneg (hp.1 v) (hq.1 w))
      _ = kappa (G □ H) := by
        simp_rw [mul_assoc, ← mul_sum, ← sum_mul]
        rw [hq.2, hp.2]
        ring

end D5.S3.Combinatorics.Graph.QuadraticLoad.NativeTransport
