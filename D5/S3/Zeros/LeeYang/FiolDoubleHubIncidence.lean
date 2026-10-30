/- GID: D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/FiolDoubleHubIncidence
   mirror-E: none(waiver:analytic-family-proof)
   anchors: []
   utility: none
   digest: All-parameter physical double-hub incidence identities. -/
import D5.S3.Zeros.LeeYang.FiolDoubleHubGrid
import D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Fin.InsertNth

open scoped BigOperators
open Polynomial Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Zeros.LeeYang
open FiolDoubleHubEndpoint
open scoped BigOperators
open Polynomial Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
open FiolDoubleHubEndpoint
namespace FiolDoubleHub

noncomputable local instance (m : ℕ) (v : Vertex m) :
    Fintype ((graph m).neighborSet v) := Fintype.ofFinite _

private theorem adjacency_named (m : ℕ) (u v : Vertex m) :
    (graph m).Adj u v ↔
      (∃ e : Edge m, src e = u ∧ tgt e = v) ∨
      (∃ e : Edge m, tgt e = u ∧ src e = v) := by
  classical
  rw [graph,D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport.treeSupport,
    SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨e,he⟩,hne⟩
    rcases Sym2.eq_iff.mp he with h | h
    · exact Or.inl ⟨e.1,h⟩
    · exact Or.inr ⟨e.1,h.2,h.1⟩
  · rintro (⟨e,he,ht⟩ | ⟨e,ht,he⟩)
    · exact ⟨⟨⟨e,Set.mem_univ e⟩,by simp [he,ht]⟩,by
        intro h; exact nonloop m e (he.trans (h.trans ht.symm))⟩
    · exact ⟨⟨⟨e,Set.mem_univ e⟩,by simp [he,ht,Sym2.eq_swap]⟩,by
        intro h; exact nonloop m e (he.trans (h.symm.trans ht.symm))⟩

private theorem center_adj (m : ℕ) (v : Vertex m) :
    (graph m).Adj none v ↔ ∃ b : Bool, v = some (b,none) := by
  rw [adjacency_named]
  constructor
  · rintro (⟨⟨b,o⟩,h,_⟩ | ⟨⟨b,o⟩,h,hv⟩)
    · simp [src] at h
    · cases o with
      | none => exact ⟨b,hv.symm⟩
      | some i => simp [tgt] at h
  · rintro ⟨b,rfl⟩
    exact Or.inr ⟨(b,none),rfl,rfl⟩

private theorem hub_adj (m : ℕ) (b : Bool) (v : Vertex m) :
    (graph m).Adj (some (b,none)) v ↔ v = none ∨ ∃ i : Fin m, v = some (b,some i) := by
  rw [adjacency_named]
  constructor
  · rintro (⟨⟨c,o⟩,h,hv⟩ | ⟨⟨c,o⟩,h,hv⟩)
    · have he : c=b ∧ o=none := by simpa [src] using h
      rcases he with ⟨rfl,rfl⟩
      exact Or.inl hv.symm
    · cases o with
      | none => simp [tgt] at h
      | some i =>
        have he : c=b := by simpa [tgt] using h
        subst c
        exact Or.inr ⟨i,hv.symm⟩
  · rintro (rfl | ⟨i,rfl⟩)
    · exact Or.inl ⟨(b,none),rfl,rfl⟩
    · exact Or.inr ⟨(b,some i),rfl,rfl⟩

private theorem leaf_adj (m : ℕ) (b : Bool) (i : Fin m) (v : Vertex m) :
    (graph m).Adj (some (b,some i)) v ↔ v = some (b,none) := by
  rw [adjacency_named]
  constructor
  · rintro (⟨⟨c,o⟩,h,hv⟩ | ⟨⟨c,o⟩,h,_⟩)
    · have he : c=b ∧ o=some i := by simpa [src] using h
      rcases he with ⟨rfl,rfl⟩
      exact hv.symm
    · cases o <;> simp [tgt] at h
  · intro hv
    subst v
    exact Or.inl ⟨(b,some i),rfl,rfl⟩

private theorem graph_degree_center (m : ℕ) : (graph m).degree none = 2 := by
  classical
  have hn : (graph m).neighborFinset none =
      Finset.univ.image (fun b : Bool => (some (b,none) : Vertex m)) := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset,center_adj,Finset.mem_image,Finset.mem_univ,
      true_and]
    aesop
  rw [←SimpleGraph.card_neighborFinset_eq_degree,hn,Finset.card_image_of_injective]
  · simp
  · intro b c h
    simpa using h

private theorem graph_degree_hub (m : ℕ) (b : Bool) :
    (graph m).degree (some (b,none)) = m+1 := by
  classical
  have hn : (graph m).neighborFinset (some (b,none)) =
      insert none (Finset.univ.image (fun i : Fin m => (some (b,some i) : Vertex m))) := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset,hub_adj,Finset.mem_insert,Finset.mem_image,
      Finset.mem_univ,true_and]
    aesop
  rw [←SimpleGraph.card_neighborFinset_eq_degree,hn,Finset.card_insert_of_notMem,Finset.card_image_of_injective]
  · simp
  · intro i j h
    simpa using h
  · simp

private theorem graph_degree_leaf (m : ℕ) (b : Bool) (i : Fin m) :
    (graph m).degree (some (b,some i)) = 1 := by
  classical
  have hn : (graph m).neighborFinset (some (b,some i)) = {some (b,none)} := by
    ext v
    simp [leaf_adj]
  rw [←SimpleGraph.card_neighborFinset_eq_degree,hn,Finset.card_singleton]

theorem incidence_degree (m : ℕ) (v : Vertex m) :
    degree v = (graph m).degree v := by
  cases v with
  | none => rw [center_degree,graph_degree_center]
  | some e =>
    rcases e with ⟨b,o⟩
    cases o with
    | none => rw [hub_degree,graph_degree_hub]
    | some i => rw [leaf_degree,graph_degree_leaf]

private theorem unique_center (m : ℕ) (hm : 1 ≤ m) (v : Vertex m) :
    ((graph m).degree v = 2 ∧
      ∀ u : Vertex m, (graph m).Adj v u → (graph m).degree u ≠ 1) ↔ v = none := by
  constructor
  · rintro ⟨hd,hn⟩
    cases v with
    | none => rfl
    | some e =>
      rcases e with ⟨b,o⟩
      cases o with
      | none =>
        have hh := hn (some (b,some (⟨0,hm⟩ : Fin m)))
          ((hub_adj m b _).mpr (Or.inr ⟨⟨0,hm⟩,rfl⟩))
        apply False.elim
        apply hh
        rw [←incidence_degree,leaf_degree]
      | some i => rw [graph_degree_leaf] at hd; omega
  · rintro rfl
    refine ⟨graph_degree_center m,?_⟩
    intro u hu
    obtain ⟨b,rfl⟩ := (center_adj m u).mp hu
    rw [graph_degree_hub]
    omega

private theorem automorphism_fixes_center (m : ℕ) (hm : 1 ≤ m)
    (f : (graph m) ≃g graph m) : f none = none := by
  classical
  apply (unique_center m hm _).mp
  refine ⟨?_,?_⟩
  · rw [f.degree_eq,graph_degree_center]
  · intro u hu
    obtain ⟨w,rfl⟩ := f.surjective u
    rw [f.degree_eq]
    have hw : (graph m).Adj none w := f.map_rel_iff.mp hu
    obtain ⟨b,rfl⟩ := (center_adj m w).mp hw
    rw [graph_degree_hub]
    omega

end FiolDoubleHub
namespace FiolDoubleHub

private theorem automorphism_hub_exists (m : ℕ) (hm : 1 ≤ m)
    (f : (graph m) ≃g graph m) (b : Bool) :
    ∃ c : Bool, f (some (b,none)) = some (c,none) := by
  have hh := f.map_rel_iff.mpr ((center_adj m _).mpr ⟨b,rfl⟩)
  rw [automorphism_fixes_center m hm f] at hh
  exact (center_adj m _).mp hh

private noncomputable def branchOf (m : ℕ) (hm : 1 ≤ m)
    (f : (graph m) ≃g graph m) (b : Bool) : Bool :=
  (automorphism_hub_exists m hm f b).choose

private theorem branch_spec (m : ℕ) (hm : 1 ≤ m)
    (f : (graph m) ≃g graph m) (b : Bool) :
    f (some (b,none)) = some (branchOf m hm f b,none) :=
  (automorphism_hub_exists m hm f b).choose_spec

private theorem branch_inv (m : ℕ) (hm : 1 ≤ m)
    (f : (graph m) ≃g graph m) (b : Bool) :
    branchOf m hm f.symm (branchOf m hm f b) = b := by
  have he := congrArg f.symm (branch_spec m hm f b)
  rw [branch_spec m hm f.symm] at he
  simpa using he.symm

private noncomputable def branchPerm (m : ℕ) (hm : 1 ≤ m)
    (f : (graph m) ≃g graph m) : Equiv.Perm Bool where
  toFun := branchOf m hm f
  invFun := branchOf m hm f.symm
  left_inv := branch_inv m hm f
  right_inv := by
    intro b
    simpa using branch_inv m hm f.symm b

private theorem automorphism_leaf_exists (m : ℕ) (hm : 1 ≤ m)
    (f : (graph m) ≃g graph m) (b : Bool) (i : Fin m) :
    ∃ j : Fin m, f (some (b,some i)) = some (branchPerm m hm f b,some j) := by
  have hh := f.map_rel_iff.mpr ((hub_adj m b _).mpr (Or.inr ⟨i,rfl⟩))
  rw [branch_spec m hm f b] at hh
  rcases (hub_adj m (branchOf m hm f b) _).mp hh with hz | hj
  · have he : f (some (b,some i)) = f none :=
      hz.trans (automorphism_fixes_center m hm f).symm
    have he' := f.injective he
    simp at he'
  · exact hj

private noncomputable def leafOf (m : ℕ) (hm : 1 ≤ m)
    (f : (graph m) ≃g graph m) (b : Bool) (i : Fin m) : Fin m :=
  (automorphism_leaf_exists m hm f b i).choose

private theorem leaf_spec (m : ℕ) (hm : 1 ≤ m)
    (f : (graph m) ≃g graph m) (b : Bool) (i : Fin m) :
    f (some (b,some i)) = some (branchPerm m hm f b,some (leafOf m hm f b i)) :=
  (automorphism_leaf_exists m hm f b i).choose_spec

private theorem leaf_bijective (m : ℕ) (hm : 1 ≤ m)
    (f : (graph m) ≃g graph m) (b : Bool) :
    Function.Bijective (leafOf m hm f b) := by
  refine ⟨?_,?_⟩
  · intro i j he
    have hh : f (some (b,some i)) = f (some (b,some j)) := by
      rw [leaf_spec m hm f b i,leaf_spec m hm f b j,he]
    simpa using f.injective hh
  · intro j
    let c := branchPerm m hm f b
    let i := leafOf m hm f.symm c j
    have hh := leaf_spec m hm f.symm c j
    have hc : branchPerm m hm f.symm c = b := branch_inv m hm f b
    rw [hc] at hh
    have he := congrArg f hh
    rw [leaf_spec m hm f b i] at he
    have he' : j = leafOf m hm f b i := by simpa [i,c] using he
    exact ⟨i,he'.symm⟩

private noncomputable def leafPerm (m : ℕ) (hm : 1 ≤ m)
    (f : (graph m) ≃g graph m) (b : Bool) : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (leafOf m hm f b) (leaf_bijective m hm f b)

private def vertexPerm (m : ℕ) (p : Equiv.Perm Bool)
    (q : Bool → Equiv.Perm (Fin m)) : Equiv.Perm (Vertex m) where
  toFun
    | none => none
    | some (b,none) => some (p b,none)
    | some (b,some i) => some (p b,some (q b i))
  invFun
    | none => none
    | some (b,none) => some (p.symm b,none)
    | some (b,some i) => some (p.symm b,some ((q (p.symm b)).symm i))
  left_inv := by
    rintro (_ | ⟨b,_ | i⟩) <;> simp
  right_inv := by
    rintro (_ | ⟨b,_ | i⟩) <;> simp

private def constructAutomorphism (m : ℕ) (p : Equiv.Perm Bool)
    (q : Bool → Equiv.Perm (Fin m)) : (graph m) ≃g graph m where
  toEquiv := vertexPerm m p q
  map_rel_iff' := by
    rintro (_ | ⟨b,_ | i⟩) (_ | ⟨c,_ | j⟩)
    all_goals simp only [vertexPerm,Equiv.coe_fn_mk]
    all_goals first
      | simp [center_adj]
      | simp [hub_adj]
      | simp [leaf_adj]
      | simp [SimpleGraph.irrefl]

private noncomputable def automorphismEquiv (m : ℕ) (hm : 1 ≤ m) :
    ((graph m) ≃g graph m) ≃
      (Equiv.Perm Bool × (Bool → Equiv.Perm (Fin m))) where
  toFun f := (branchPerm m hm f,leafPerm m hm f)
  invFun pq := constructAutomorphism m pq.1 pq.2
  left_inv := by
    intro f
    apply DFunLike.ext
    rintro (_ | ⟨b,_ | i⟩)
    · exact (automorphism_fixes_center m hm f).symm
    · exact (branch_spec m hm f b).symm
    · exact (leaf_spec m hm f b i).symm
  right_inv := by
    rintro ⟨p,q⟩
    apply Prod.ext
    · apply Equiv.ext
      intro b
      have hh := branch_spec m hm (constructAutomorphism m p q) b
      simpa [constructAutomorphism,vertexPerm,branchPerm] using hh.symm
    · funext b
      apply Equiv.ext
      intro i
      have hh := leaf_spec m hm (constructAutomorphism m p q) b i
      have he : q b i = leafOf m hm (constructAutomorphism m p q) b i := by
        simpa [constructAutomorphism,vertexPerm] using congrArg
          (fun v : Vertex m => v.bind (fun e => e.2)) hh
      exact he.symm

theorem actual_automorphism_order (m : ℕ) (hm : 1 ≤ m) :
    automorphismOrder m = 2*(Nat.factorial m)^2 := by
  rw [automorphismOrder,Nat.card_congr (automorphismEquiv m hm)]
  simp [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fun]

end FiolDoubleHub
namespace FiolDoubleHub

private theorem endpointRatio_pos (a r : ℕ) (ha : 1 ≤ a) : 0 < endpointRatio a r := by
  unfold endpointRatio
  split_ifs <;> positivity

private theorem selected_weight_pos (m : ℕ) (A S : Finset (Edge m))
    (hA : A.card = 2) (hSA : S ⊆ A) :
    0 < physicalWeight (totals A) (shares S) := by
  rw [actual_weight_normalized m A S hA hSA]
  apply mul_pos
  · positivity
  · apply Finset.prod_pos
    intro v hv
    exact endpointRatio_pos _ _ (actual_degree_positive m v)

private theorem actual_eval_zero_pos (m cutoff : ℕ) (hm : 1 ≤ m) (hc : 3 ≤ cutoff) :
    0 < (sourceCoefficient m cutoff).eval 0 := by
  classical
  rw [all_endpoint_coefficient m cutoff hc]
  simp only [Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_C]
  apply Finset.sum_pos
  · intro A hA
    have hcard := (Finset.mem_powersetCard.mp hA).2
    apply mul_pos
    · change 0 < sourcePrefactor (fun e => if e ∈ A then 3 else 2)
      rw [actual_prefactor m A hcard,actual_automorphism_order m hm]
      positivity
    · simp only [Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_C,
        Polynomial.eval_prod,Polynomial.eval_add,Polynomial.eval_one,
        Polynomial.eval_pow,Polynomial.eval_X]
      apply Finset.sum_pos
      · intro S hS
        have hs := Finset.mem_powerset.mp hS
        have hp : (∏ v : Vertex m,
            (1 + (-1:ℝ)^degree v * (0:ℝ)^(degree v+increments A S v))) = 1 := by
          apply Finset.prod_eq_one
          intro v hv
          have hd : degree v+increments A S v ≠ 0 := by
            have := actual_degree_positive m v
            omega
          simp [zero_pow hd]
        rw [hp,mul_one]
        exact selected_weight_pos m A S hcard hs
      · exact ⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset A)⟩
  · refine ⟨{(false,none),(true,none)},?_⟩
    simp [Finset.mem_powersetCard]

private theorem total_incidence_degree (m : ℕ) :
    (∑ v : Vertex m, degree v) = 4*m+4 := by
  change (∑ v : Option (Bool × Option (Fin m)),degree v) = _
  simp only [Fintype.sum_option,Fintype.sum_prod_type,center_degree,hub_degree,leaf_degree]
  simp [Fintype.sum_bool]
  omega

private theorem homogeneousSplit_symmetric (m : ℕ) (n k : Edge m → ℕ)
    (a b : ℂ) : homogeneousSplitSource n k a b = homogeneousSplitSource n k b a := by
  classical
  have hf (v : Vertex m) :
      a^mass n k v + (-1:ℂ)^degree v * b^mass n k v =
      (-1:ℂ)^degree v * (b^mass n k v + (-1:ℂ)^degree v * a^mass n k v) := by
    have hs : (-1:ℂ)^degree v * (-1:ℂ)^degree v = 1 := by
      rw [←pow_add,←two_mul,pow_mul]
      norm_num
    linear_combination -(a^mass n k v)*hs
  unfold homogeneousSplitSource
  simp_rw [hf]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,total_incidence_degree]
  have he : (-1:ℂ)^(4*m+4)=1 := by
    have hh : 4*m+4 = 2*(2*m+2) := by omega
    rw [hh,pow_mul]
    norm_num
  rw [he,one_mul]

private theorem homogeneousCoefficient_symmetric (m cutoff : ℕ) (a b : ℂ) :
    homogeneousCoefficient m cutoff a b = homogeneousCoefficient m cutoff b a := by
  unfold homogeneousCoefficient homogeneousTruncation
  simp_rw [homogeneousSplit_symmetric m _ _ a b]

private theorem actual_boundary_right (m cutoff : ℕ) (hc : 3 ≤ cutoff)
    (a : ℂ) (ha : a ≠ 0) :
    homogeneousCoefficient m cutoff a 0 = a^(4*m+6) *
      ((sourceCoefficient m cutoff).eval 0 : ℝ) := by
  rw [actual_homogeneous_ratio m cutoff hc a 0 ha]
  simp [Polynomial.coeff_zero_eq_eval_zero]

theorem actual_zero_coupling_boundaries (m cutoff : ℕ)
    (hm : 1 ≤ m) (hc : 3 ≤ cutoff) :
    (∀ a : ℂ, a ≠ 0 → homogeneousCoefficient m cutoff a 0 ≠ 0) ∧
    (∀ b : ℂ, b ≠ 0 → homogeneousCoefficient m cutoff 0 b ≠ 0) ∧
    homogeneousCoefficient m cutoff 0 0 = 0 := by
  classical
  have hp : (sourceCoefficient m cutoff).eval 0 ≠ 0 := ne_of_gt (actual_eval_zero_pos m cutoff hm hc)
  have hr : ∀ a : ℂ, a ≠ 0 → homogeneousCoefficient m cutoff a 0 ≠ 0 := by
    intro a ha
    rw [actual_boundary_right m cutoff hc a ha]
    exact mul_ne_zero (pow_ne_zero _ ha) (by exact_mod_cast hp)
  refine ⟨hr,?_,?_⟩
  · intro b hb
    rw [homogeneousCoefficient_symmetric]
    exact hr b hb
  · have hE : Fintype.card (Edge m) = 2*m+2 := by simp [Edge]; omega
    unfold homogeneousCoefficient homogeneousTruncation targetMonomial
    rw [coefficient_extract m cutoff hE,pair_sum cutoff hc]
    apply Finset.sum_eq_zero
    intro A hA
    change (sourcePrefactor (totals A) : ℂ) *
      (∑ k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits (totals A),
        homogeneousSplitSource (totals A) k 0 0) = 0
    apply mul_eq_zero_of_right
    rw [split_sum]
    apply Finset.sum_eq_zero
    intro S hS
    unfold homogeneousSplitSource
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ (none : Vertex m))
    have hm' : mass (totals A) (shares S) (none : Vertex m) ≠ 0 := by
      change D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass src tgt
        (totals A) (shares S) none ≠ 0
      rw [actual_mass src tgt A S (Finset.mem_powerset.mp hS) none]
      have hd := actual_degree_positive m (none : Vertex m)
      dsimp [degree] at hd
      omega
    simp [zero_pow hm']

end FiolDoubleHub
namespace FiolDoubleHub

theorem actual_source_normalization (m cutoff : ℕ)
    (hm : 1 ≤ m) (hc : 3 ≤ cutoff) :
    sourceCoefficient m cutoff = Polynomial.C (200*(12:ℝ)^(2*m)) *
      ∑ A ∈ (Finset.univ : Finset (Edge m)).powersetCard 2,
        ∑ S ∈ A.powerset,
          Polynomial.C (18 * ∏ v : Vertex m, endpointRatio (degree v) (increments A S v)) *
            ∏ v : Vertex m, (1 + Polynomial.C ((-1:ℝ)^degree v) *
              Polynomial.X^(degree v+increments A S v)) := by
  classical
  rw [all_endpoint_coefficient m cutoff hc,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have ha := (Finset.mem_powersetCard.mp hA).2
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hs := Finset.mem_powerset.mp hS
  have hp : sourcePrefactor (totals A) = 4/(9*(automorphismOrder m:ℝ)) := by
    change sourcePrefactor (fun e => if e ∈ A then 3 else 2) = _
    exact actual_prefactor m A ha
  rw [hp,actual_automorphism_order m hm,actual_weight_normalized m A S ha hs]
  have hf : (Nat.factorial m : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have he (t : ℝ) :
      (4/(9*(2*(Nat.factorial m)^2:ℕ):ℝ)) *
        (16200*(Nat.factorial m:ℝ)^2*(12:ℝ)^(2*m)*t) =
      (200*(12:ℝ)^(2*m))*(18*t) := by
    push_cast
    field_simp
    <;> ring
  rw [←mul_assoc,←mul_assoc,←Polynomial.C_mul,←Polynomial.C_mul]
  congr 1
  exact congrArg Polynomial.C (he _)

end FiolDoubleHub
namespace FiolDoubleHub

def placementsCC (m : ℕ) : Finset (Finset (Edge m)) :=
  {{(false,none),(true,none)}}
def placementsCPsame (m : ℕ) : Finset (Finset (Edge m)) :=
  (Finset.univ : Finset (Bool × Fin m)).image
    (fun bi => {(bi.1,none),(bi.1,some bi.2)})
def placementsCPopp (m : ℕ) : Finset (Finset (Edge m)) :=
  (Finset.univ : Finset (Bool × Fin m)).image
    (fun bi => {(bi.1,none),(!bi.1,some bi.2)})
def placementsPPsame (m : ℕ) : Finset (Finset (Edge m)) :=
  ((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset (Fin m)).powersetCard 2).image
    (fun bs => bs.2.image (fun i => (bs.1,some i)))
def placementsPPopp (m : ℕ) : Finset (Finset (Edge m)) :=
  (Finset.univ : Finset (Fin m × Fin m)).image
    (fun ij => {(false,some ij.1),(true,some ij.2)})

theorem placement_exhaustive (m : ℕ) (A : Finset (Edge m)) (hA : A.card = 2) :
    A ∈ placementsCC m ∨ A ∈ placementsCPsame m ∨ A ∈ placementsCPopp m ∨
      A ∈ placementsPPsame m ∨ A ∈ placementsPPopp m := by
  classical
  obtain ⟨⟨b,o⟩,⟨c,p⟩,hne,rfl⟩ := Finset.card_eq_two.mp hA
  cases o with
  | none =>
    cases p with
    | none =>
      left
      cases b <;> cases c <;> simp_all [placementsCC,Finset.pair_comm]
    | some j =>
      by_cases hbc : b=c
      · subst c
        exact Or.inr (Or.inl (Finset.mem_image.mpr ⟨(b,j),Finset.mem_univ _,rfl⟩))
      · right;right;left
        have hc : c = !b := by cases b <;> cases c <;> simp_all
        subst c
        exact Finset.mem_image.mpr ⟨(b,j),Finset.mem_univ _,rfl⟩
  | some i =>
    cases p with
    | none =>
      by_cases hbc : b=c
      · subst c
        right;left
        exact Finset.mem_image.mpr ⟨(b,i),Finset.mem_univ _,Finset.pair_comm _ _⟩
      · right;right;left
        have hb : b = !c := by cases b <;> cases c <;> simp_all
        subst b
        exact Finset.mem_image.mpr ⟨(c,i),Finset.mem_univ _,Finset.pair_comm _ _⟩
    | some j =>
      by_cases hbc : b=c
      · subst c
        have hij : i≠j := by intro h; subst j; exact hne rfl
        right;right;right;left
        apply Finset.mem_image.mpr
        refine ⟨(b,{i,j}),?_,?_⟩
        · simp [Finset.mem_powersetCard,hij]
        · simp
      · right;right;right;right
        cases b <;> cases c <;> simp_all [placementsPPopp,Finset.mem_image]
        all_goals first
          | exact ⟨i,j,rfl⟩
          | exact ⟨j,i,Finset.pair_comm _ _⟩

theorem placement_counts (m : ℕ) :
    (placementsCC m).card = 1 ∧
    (placementsCPsame m).card = 2*m ∧
    (placementsCPopp m).card = 2*m ∧
    (placementsPPsame m).card = m*(m-1) ∧
    (placementsPPopp m).card = m^2 := by
  classical
  have hs : Function.Injective (fun bi : Bool × Fin m =>
      ({(bi.1,none),(bi.1,some bi.2)} : Finset (Edge m))) := by
    rintro ⟨b,i⟩ ⟨c,j⟩ he
    dsimp only at he
    have hb : b=c := by
      have hh : (b,none) ∈ ({(c,none),(c,some j)} : Finset (Edge m)) := by
        rw [←he]; simp
      simpa using hh
    subst c
    have hi : i=j := by
      have hh : (b,some i) ∈ ({(b,none),(b,some j)} : Finset (Edge m)) := by
        rw [←he]; simp
      simpa using hh
    subst j
    rfl
  have ho : Function.Injective (fun bi : Bool × Fin m =>
      ({(bi.1,none),(!bi.1,some bi.2)} : Finset (Edge m))) := by
    rintro ⟨b,i⟩ ⟨c,j⟩ he
    dsimp only at he
    have hb : b=c := by
      have hh : (b,none) ∈ ({(c,none),(!c,some j)} : Finset (Edge m)) := by
        rw [←he]; simp
      simpa using hh
    subst c
    have hi : i=j := by
      have hh : (!b,some i) ∈ ({(b,none),(!b,some j)} : Finset (Edge m)) := by
        rw [←he]; simp
      simpa using hh
    subst j
    rfl
  have hp : Function.Injective (fun ij : Fin m × Fin m =>
      ({(false,some ij.1),(true,some ij.2)} : Finset (Edge m))) := by
    rintro ⟨i,j⟩ ⟨k,l⟩ he
    dsimp only at he
    have hi : i=k := by
      have hh : (false,some i) ∈ ({(false,some k),(true,some l)} : Finset (Edge m)) := by
        rw [←he]; simp
      simpa using hh
    have hj : j=l := by
      have hh : (true,some j) ∈ ({(false,some k),(true,some l)} : Finset (Edge m)) := by
        rw [←he]; simp
      simpa using hh
    subst k
    subst l
    rfl
  have hsame : Set.InjOn
      (fun bs : Bool × Finset (Fin m) => bs.2.image (fun i => (bs.1,some i)))
      ↑((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset (Fin m)).powersetCard 2) := by
    rintro ⟨b,A⟩ hA ⟨c,B⟩ hB he
    have ha := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hA).2).2
    have hb := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hB).2).2
    dsimp only at ha hb he
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    have hi' : (b,some i) ∈ B.image (fun j => (c,some j)) := by
      rw [←he]
      exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
    obtain ⟨j,hj,hij⟩ := Finset.mem_image.mp hi'
    have hbc : b=c := by simpa using (congrArg Prod.fst hij).symm
    subst c
    have hab : A=B := by
      apply Finset.image_injective (f := fun i : Fin m => (b,some i))
        (by intro i j h; simpa using h)
      exact he
    subst B
    rfl
  refine ⟨by simp [placementsCC],?_,?_,?_,?_⟩
  · rw [placementsCPsame,Finset.card_image_of_injective _ hs]
    simp
  · rw [placementsCPopp,Finset.card_image_of_injective _ ho]
    simp
  · rw [placementsPPsame,Finset.card_image_of_injOn hsame,
      Finset.card_product,Finset.card_powersetCard]
    simp only [Finset.card_univ,Fintype.card_bool,Fintype.card_fin]
    have he := (Nat.descFactorial_eq_factorial_mul_choose m 2).symm
    simpa [Nat.descFactorial,Nat.factorial,Nat.mul_comm] using he
  · rw [placementsPPopp,Finset.card_image_of_injective _ hp]
    simp [pow_two]

end FiolDoubleHub
namespace FiolDoubleHub

private theorem leaf_increments (m : ℕ) (A S : Finset (Edge m)) (b : Bool) (i : Fin m) :
    increments A S (some (b,some i)) = if (b,some i) ∈ S then 1 else 0 := by
  classical
  have hs : (Finset.univ.filter (fun e : Edge m => src e=some (b,some i) ∧ e∈S)) =
      if (b,some i)∈S then {(b,some i)} else ∅ := by
    ext e
    by_cases hi : (b,some i)∈S
    · simp [src,hi]
      aesop
    · simp [src,hi]
      aesop
  have ht : (Finset.univ.filter (fun e : Edge m => tgt e=some (b,some i) ∧ e∈A \ S)) = ∅ := by
    ext e
    rcases e with ⟨c,o⟩
    cases o <;> simp [tgt]
  simp only [increments,hs,ht,Finset.card_empty,add_zero]
  split_ifs <;> simp

noncomputable def selectedLeaves (m : ℕ) (S : Finset (Edge m)) : Finset (Bool × Fin m) :=
  Finset.univ.filter (fun bi => (bi.1,some bi.2) ∈ S)

theorem leaf_vertex_product (m : ℕ) (A S : Finset (Edge m)) :
    (∏ bi : Bool × Fin m,
      Polynomial.C (endpointRatio (degree (some (bi.1,some bi.2)))
        (increments A S (some (bi.1,some bi.2)))) *
      (1+Polynomial.C ((-1:ℝ)^degree (some (bi.1,some bi.2))) *
        Polynomial.X^(degree (some (bi.1,some bi.2))+
          increments A S (some (bi.1,some bi.2))))) =
    (1-Polynomial.X)^(2*m) *
      (Polynomial.C (1/3:ℝ)*(1+Polynomial.X))^(selectedLeaves m S).card := by
  classical
  have hf (bi : Bool × Fin m) :
      Polynomial.C (endpointRatio (degree (some (bi.1,some bi.2)))
        (increments A S (some (bi.1,some bi.2)))) *
      (1+Polynomial.C ((-1:ℝ)^degree (some (bi.1,some bi.2))) *
        Polynomial.X^(degree (some (bi.1,some bi.2))+
          increments A S (some (bi.1,some bi.2)))) =
      (1-Polynomial.X) *
        (if (bi.1,some bi.2) ∈ S then Polynomial.C (1/3:ℝ)*(1+Polynomial.X) else 1) := by
    rw [leaf_degree,leaf_increments]
    by_cases hi : (bi.1,some bi.2) ∈ S <;>
      norm_num [hi,endpointRatio] <;> ring
  simp_rw [hf]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  have hc : Fintype.card (Bool × Fin m) = 2*m := by simp
  rw [hc]
  congr 1
  rw [Finset.prod_ite]
  simp [selectedLeaves]

end FiolDoubleHub

end D5.S3.Zeros.LeeYang
