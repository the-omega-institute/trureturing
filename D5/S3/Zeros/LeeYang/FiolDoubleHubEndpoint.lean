/- GID: D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/FiolDoubleHubEndpoint
   mirror-E: none(waiver:analytic-family-proof)
   anchors: []
   utility: none
   digest: All-parameter physical double-hub endpoint identities. -/
import D5.S3.Zeros.LeeYang.FiolDoubleHubGraph
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
namespace FiolDoubleHubEndpoint
def totals {E : Type} [DecidableEq E] (A : Finset E) (e : E) : ℕ :=
  if e ∈ A then 3 else 2
def shares {E : Type} [DecidableEq E] (S : Finset E) (e : E) : ℕ :=
  if e ∈ S then 2 else 1

theorem split_iff {E : Type} [Fintype E] [DecidableEq E]
    (A : Finset E) (k : E → ℕ) :
    k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits (totals A) ↔
      ∀ e, (e ∈ A → k e = 1 ∨ k e = 2) ∧ (e ∉ A → k e = 1) := by
  simp only [D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits,
    Fintype.mem_piFinset,Finset.mem_Icc]
  constructor
  · intro h e
    have he := h e
    by_cases ha : e ∈ A <;> simp [totals,ha] at he ⊢ <;> omega
  · intro h e
    have he := h e
    by_cases ha : e ∈ A <;> simp [totals,ha] at he ⊢ <;> omega

theorem split_sum {E : Type} [Fintype E] [DecidableEq E]
    {R : Type} [AddCommMonoid R] (A : Finset E) (a : (E → ℕ) → R) :
    (∑ k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits (totals A), a k) =
      ∑ S ∈ A.powerset, a (shares S) := by
  classical
  let pick (k : E → ℕ) := Finset.univ.filter (fun e => k e = 2)
  have hleft (k : E → ℕ)
      (hk : k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits (totals A)) :
      shares (pick k) = k := by
    funext e
    have he := (split_iff A k).mp hk e
    by_cases ha : e ∈ A
    · rcases he.1 ha with h | h <;> simp [shares,pick,h]
    · simp [shares,pick,he.2 ha]
  have hright (S : Finset E) : pick (shares S) = S := by
    ext e
    simp [pick,shares]
  refine Finset.sum_bij (fun k _ => pick k) ?_ ?_ ?_ ?_
  · intro k hk
    apply Finset.mem_powerset.mpr
    intro e he
    have hk2 : k e = 2 := (Finset.mem_filter.mp he).2
    by_contra hnot
    have hk1 := ((split_iff A k).mp hk e).2 hnot
    omega
  · intro k hk k' hk' heq
    rw [← hleft k hk, ← hleft k' hk', heq]
  · intro S hS
    have hSA := Finset.mem_powerset.mp hS
    refine ⟨shares S, (split_iff A (shares S)).mpr ?_, hright S⟩
    intro e
    constructor
    · intro he
      by_cases hs : e ∈ S <;> simp [shares,hs]
    · intro he
      have hs : e ∉ S := fun hs => he (hSA hs)
      simp [shares,hs]
  · intro k hk
    rw [hleft k hk]

-- Exactly four complementary splits for each actual two-edge placement.
theorem actual_mass {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (src tgt : E → V)
    (A S : Finset E) (hSA : S ⊆ A) (v : V) :
    D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass src tgt (totals A) (shares S) v =
    ((Finset.univ.filter (fun e : E => src e = v)).card +
      (Finset.univ.filter (fun e : E => tgt e = v)).card) +
    (Finset.univ.filter (fun e : E => src e = v ∧ e ∈ S)).card +
    (Finset.univ.filter (fun e : E => tgt e = v ∧ e ∈ A \ S)).card := by
  have hs (e : E) : shares S e = 1 + if e ∈ S then 1 else 0 := by
    by_cases h : e ∈ S <;> simp [shares,h]
  have ht (e : E) : totals A e-shares S e = 1 + if e ∈ A \ S then 1 else 0 := by
    by_cases h : e ∈ S
    · have ha := hSA h
      simp [totals,shares,h,ha]
    · by_cases ha : e ∈ A <;> simp [totals,shares,h,ha]
  unfold D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass
  simp_rw [ht,hs]
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one,
    Finset.sum_boole,Finset.filter_filter,Nat.cast_id]
  omega

end FiolDoubleHubEndpoint


namespace FiolDoubleHub
open FiolDoubleHubEndpoint

noncomputable def increments {m : ℕ} (A S : Finset (Edge m)) (v : Vertex m) : ℕ :=
  (Finset.univ.filter (fun e : Edge m => src e = v ∧ e ∈ S)).card +
  (Finset.univ.filter (fun e : Edge m => tgt e = v ∧ e ∈ A \ S)).card

private theorem split_endpoint_value (m : ℕ) (A S : Finset (Edge m)) (hSA : S ⊆ A) :
    splitSource (totals A) (shares S) =
      Polynomial.C (physicalWeight (totals A) (shares S)) *
      ∏ v : Vertex m, (1+Polynomial.C ((-1:ℝ)^degree v) *
        Polynomial.X^(degree v+increments A S v)) := by
  unfold splitSource
  apply congrArg (fun p : Polynomial ℝ => Polynomial.C (physicalWeight (totals A) (shares S)) * p)
  apply Finset.prod_congr rfl
  intro v hv
  have h := actual_mass (src (m:=m)) tgt A S hSA v
  have he : mass (totals A) (shares S) v = degree v+increments A S v := by
    change D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass src tgt
      (totals A) (shares S) v = _
    rw [h]
    dsimp [degree,increments]
    omega
  rw [he]

theorem all_endpoint_coefficient (m cutoff : ℕ) (hc : 3 ≤ cutoff) :
    sourceCoefficient m cutoff =
      ∑ A ∈ (Finset.univ : Finset (Edge m)).powersetCard 2,
        Polynomial.C (sourcePrefactor (totals A)) *
        ∑ S ∈ A.powerset,
          Polynomial.C (physicalWeight (totals A) (shares S)) *
          ∏ v : Vertex m, (1+Polynomial.C ((-1:ℝ)^degree v) *
            Polynomial.X^(degree v+increments A S v)) := by
  rw [source_pair_formula m cutoff hc]
  apply Finset.sum_congr rfl
  intro A hA
  change Polynomial.C (sourcePrefactor (totals A)) *
    allVertexSource (totals A) = _
  apply congrArg (fun p : Polynomial ℝ => Polynomial.C (sourcePrefactor (totals A)) * p)
  unfold allVertexSource
  rw [split_sum]
  apply Finset.sum_congr rfl
  intro S hS
  exact split_endpoint_value m A S (Finset.mem_powerset.mp hS)

end FiolDoubleHub


-- The source masses count every edge exactly twice, with complementary shares.
theorem mass_total {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (src tgt : E → V) (n k : E → ℕ)
    (hk : k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits n) :
    (∑ v : V, D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass src tgt n k v) =
      ∑ e : E, n e := by
  classical
  unfold D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass
  rw [Finset.sum_add_distrib, Finset.sum_fiberwise, Finset.sum_fiberwise,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hke := Fintype.mem_piFinset.mp hk e
  have hle : k e ≤ n e := by
    change k e ∈ Finset.Icc 1 (n e - 1) at hke
    have := (Finset.mem_Icc.mp hke).2
    omega
  exact Nat.add_sub_of_le hle

-- Exactly two total-3 edges and 2m total-2 edges give full degree 4m+6.
theorem total_degree {E : Type} [Fintype E] [DecidableEq E] (m : ℕ)
    (hE : Fintype.card E = 2*m+2) (n : E → ℕ)
    (hrange : ∀ e : E, n e = 2 ∨ n e = 3)
    (hcount : (Finset.univ.filter (fun e : E => n e = 3)).card = 2) :
    (∑ e : E, n e) = 4*m+6 := by
  calc
    _ = ∑ e : E, (2 + if n e = 3 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      rcases hrange e with h | h <;> simp [h]
    _ = 2*Fintype.card E + (Finset.univ.filter (fun e : E => n e = 3)).card := by
      simp [Finset.sum_add_distrib, mul_comm]
    _ = _ := by rw [hE, hcount]; ring





namespace FiolDoubleHub
private theorem allVertex_ratio (m D : ℕ) (n : Edge m → ℕ)
    (hm : ∀ k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits n,
      (∑ v : Vertex m, mass n k v) = D)
    (lambda1 lambda2 : ℂ) (h1 : lambda1 ≠ 0) :
    (∑ k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits n,
      homogeneousSplitSource n k lambda1 lambda2) =
    lambda1^D * (Polynomial.eval₂RingHom Complex.ofRealHom (lambda2/lambda1))
      (allVertexSource n) := by
  classical
  have hprod (k : Edge m → ℕ) :
      (∏ v : Vertex m, (lambda1 ^ mass n k v +
        ((-1:ℂ)^degree v)*lambda2 ^ mass n k v)) =
      lambda1^(∑ v : Vertex m, mass n k v) *
        ∏ v : Vertex m, (1+((-1:ℂ)^degree v)*(lambda2/lambda1)^mass n k v) := by
    calc
      _ = ∏ v : Vertex m, lambda1 ^ mass n k v *
          (1+((-1:ℂ)^degree v)*(lambda2/lambda1)^mass n k v) := by
        apply Finset.prod_congr rfl
        intro v hv
        rw [div_pow]
        field_simp <;> ring
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [allVertexSource,map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold homogeneousSplitSource splitSource
  rw [hprod,hm k hk]
  simp only [map_mul, Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
    Polynomial.eval₂_finsetProd,Polynomial.eval₂_add,Polynomial.eval₂_one,
    Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_neg,
    map_pow,map_neg,map_one,Complex.ofRealHom_eq_coe]
  ring

theorem actual_homogeneous_ratio (m cutoff : ℕ) (hc : 3 ≤ cutoff)
    (lambda1 lambda2 : ℂ) (h1 : lambda1 ≠ 0) :
    homogeneousCoefficient m cutoff lambda1 lambda2 =
      lambda1^(4*m+6) *
        (Polynomial.eval₂RingHom Complex.ofRealHom (lambda2/lambda1))
          (sourceCoefficient m cutoff) := by
  classical
  have hE : Fintype.card (Edge m) = 2*m+2 := by simp [Edge]; omega
  unfold homogeneousCoefficient homogeneousTruncation targetMonomial
  rw [coefficient_extract m cutoff hE, pair_sum cutoff hc,source_pair_formula m cutoff hc]
  simp only [map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  let n : Edge m → ℕ := fun e => if e ∈ A then 3 else 2
  have hr : ∀ e : Edge m, n e = 2 ∨ n e = 3 := by
    intro e; dsimp [n]; split_ifs <;> omega
  have hfilter : (Finset.univ.filter (fun e : Edge m => n e = 3)) = A := by
    ext e; simp [n]
  have hn : (∑ e : Edge m, n e) = 4*m+6 := by
    apply total_degree m hE n hr
    rw [hfilter]
    exact (Finset.mem_powersetCard.mp hA).2
  have hm : ∀ k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits n,
      (∑ v : Vertex m, mass n k v) = 4*m+6 := by
    intro k hk
    rw [mass_total src tgt n k hk,hn]
  rw [← Finset.mul_sum]
  change (sourcePrefactor n : ℂ) *
    (∑ k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits n,
      homogeneousSplitSource n k lambda1 lambda2) = _
  rw [allVertex_ratio m (4*m+6) n hm lambda1 lambda2 h1]
  simp only [map_mul,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,Complex.ofRealHom_eq_coe]
  dsimp only [n]
  ring

end FiolDoubleHub


namespace FiolDoubleHub
theorem actual_prefactor (m : ℕ) (A : Finset (Edge m)) (hA : A.card = 2) :
    sourcePrefactor (fun e => if e ∈ A then 3 else 2) =
      4 / (9*(automorphismOrder m : ℝ)) := by
  classical
  have hE : Fintype.card (Edge m) = 2*m+2 := by simp [Edge]; omega
  have hf : (Finset.univ.filter (fun e : Edge m => e ∈ A)) = A := by ext e; simp
  have hfn : (Finset.univ.filter (fun e : Edge m => e ∉ A)) = Finset.univ \ A := by
    ext e; simp
  have hcard : (Finset.univ \ A).card = 2*m := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A),Finset.card_univ,hE,hA]
    omega
  have hp : (∏ e : Edge m, ((if e ∈ A then 3 else 2 : ℕ):ℝ)) =
      9*(2:ℝ)^(2*m) := by
    simp only [apply_ite,Nat.cast_ofNat]
    rw [Finset.prod_ite,hf,hfn]
    norm_num [hA,hcard]
  have hs : (∑ e : Edge m, (if e ∈ A then 3 else 2 : ℕ)) = 4*m+6 := by
    calc
      _ = ∑ e : Edge m, (2 + if e ∈ A then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> norm_num
      _ = _ := by simp [Finset.sum_add_distrib,hE,hA]; omega
  have hpow : (-2:ℝ)^(2*m+2) = 4*(2:ℝ)^(2*m) := by
    rw [pow_add,pow_mul,pow_mul]
    norm_num
    ring
  have hsign : (-1:ℝ)^(4*m+6) = 1 := by
    rw [pow_add,pow_mul]
    norm_num
  unfold sourcePrefactor
  rw [hE,hp,hs,hpow,hsign]
  simp only [mul_one]
  calc
    _ = (4*(2:ℝ)^(2*m)) / ((9*(automorphismOrder m : ℝ))*(2:ℝ)^(2*m)) := by
      congr 1
      ring
    _ = _ := mul_div_mul_right 4 (9*(automorphismOrder m : ℝ)) (by positivity)

end FiolDoubleHub


namespace FiolDoubleHub
theorem center_degree (m : ℕ) : degree (none : Vertex m) = 2 := by
  simp only [degree,Finset.card_filter,Fintype.sum_prod_type,
    Fintype.sum_option,Fintype.sum_bool]
  simp [src,tgt] <;> omega
theorem hub_degree (m : ℕ) (b : Bool) :
    degree (some (b,none) : Vertex m) = m+1 := by
  cases b <;> simp only [degree,Finset.card_filter,Fintype.sum_prod_type,
    Fintype.sum_option,Fintype.sum_bool] <;> simp [src,tgt] <;> omega
theorem leaf_degree (m : ℕ) (b : Bool) (i : Fin m) :
    degree (some (b,some i) : Vertex m) = 1 := by
  cases b <;> simp only [degree,Finset.card_filter,Fintype.sum_prod_type,
    Fintype.sum_option,Fintype.sum_bool] <;> simp [src,tgt] <;> omega

private noncomputable def baseline (a : ℕ) : ℝ := (Nat.factorial (a-1) : ℝ)/2
private theorem baseline_product (m : ℕ) :
    (∏ v : Vertex m, baseline (degree v)) =
      (Nat.factorial m : ℝ)^2 / (2:ℝ)^(2*m+3) := by
  change (∏ v : Option (Bool × Option (Fin m)), baseline (degree v)) = _
  rw [Fintype.prod_option]
  simp only [Fintype.prod_prod_type,Fintype.prod_option,center_degree,hub_degree,leaf_degree]
  simp [baseline,Fintype.prod_bool,div_pow,pow_add,pow_mul]
  ring_nf
  norm_num [pow_mul']

end FiolDoubleHub
namespace FiolDoubleHub
open FiolDoubleHubEndpoint

theorem physicalWeight_by_edges {m : ℕ} (n k : Edge m → ℕ) :
    physicalWeight n k =
      (∏ e : Edge m, (Nat.choose (2*n e) (2*k e) : ℝ) * J (k e) * J (n e-k e)) *
      ∏ v : Vertex m, (Nat.factorial (mass n k v-1) : ℝ) /
        (Nat.factorial (mass n k v-degree v+2) : ℝ) := by
  classical
  unfold physicalWeight edgeBinom vertexWeight
  simp_rw [Finset.prod_mul_distrib]
  rw [Finset.prod_fiberwise,Finset.prod_fiberwise]
  ring

private theorem chosen_edge_weight (m : ℕ) (A S : Finset (Edge m))
    (hSA : S ⊆ A) (e : Edge m) :
    (Nat.choose (2*totals A e) (2*shares S e) : ℝ) *
      J (shares S e) * J (totals A e-shares S e) =
      if e ∈ A then 360 else 24 := by
  by_cases hs : e ∈ S
  · have ha := hSA hs
    norm_num [totals,shares,hs,ha,J,Nat.choose]
  · by_cases ha : e ∈ A <;> norm_num [totals,shares,hs,ha,J,Nat.choose]

private theorem chosen_edge_product (m : ℕ) (A S : Finset (Edge m))
    (hA : A.card = 2) (hSA : S ⊆ A) :
    (∏ e : Edge m, (Nat.choose (2*totals A e) (2*shares S e) : ℝ) *
      J (shares S e) * J (totals A e-shares S e)) =
      (24:ℝ)^(2*m)*360^2 := by
  classical
  simp_rw [chosen_edge_weight m A S hSA]
  rw [Finset.prod_ite]
  have hfilter : (Finset.univ.filter (fun e : Edge m => e ∈ A)) = A := by ext e; simp
  have hfilter' : (Finset.univ.filter (fun e : Edge m => ¬ e ∈ A)) = Finset.univ \ A := by
    ext e; simp
  simp only [Finset.prod_const,hfilter,hfilter',hA]
  have hc : (Finset.univ \ A).card = 2*m := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,hA]
    simp [Edge]
    omega
  rw [hc]
  ring

private theorem actual_common_edge_factor (m : ℕ) (A S : Finset (Edge m))
    (hA : A.card = 2) (hSA : S ⊆ A) :
    physicalWeight (totals A) (shares S) =
      ((24:ℝ)^(2*m)*360^2) *
      ∏ v : Vertex m,
        (Nat.factorial (degree v+increments A S v-1) : ℝ) /
          (Nat.factorial (increments A S v+2) : ℝ) := by
  rw [physicalWeight_by_edges,chosen_edge_product m A S hA hSA]
  apply congrArg (fun z : ℝ => ((24:ℝ)^(2*m)*360^2)*z)
  apply Finset.prod_congr rfl
  intro v hv
  have he : mass (totals A) (shares S) v = degree v+increments A S v := by
    change D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass src tgt
      (totals A) (shares S) v = _
    rw [actual_mass src tgt A S hSA v]
    dsimp [degree,increments]
    omega
  rw [he]
  simp

noncomputable def endpointRatio (a r : ℕ) : ℝ :=
  if r = 0 then 1 else if r = 1 then (a:ℝ)/3 else (a:ℝ)*((a:ℝ)+1)/12

private theorem local_factorial_ratio (a r : ℕ) (ha : 1 ≤ a) (hr : r ≤ 2) :
    (Nat.factorial (a+r-1) : ℝ) / (Nat.factorial (r+2) : ℝ) =
      baseline a * endpointRatio a r := by
  interval_cases r
  · simp [endpointRatio,baseline]
  · simp only [Nat.add_sub_cancel,Nat.reduceAdd,endpointRatio,ite_false,ite_true]
    norm_num [baseline]
    rw [← Nat.mul_factorial_pred (by omega : a ≠ 0)]
    push_cast
    ring
  · have he : a+2-1 = a+1 := by omega
    rw [he,Nat.factorial_succ,← Nat.mul_factorial_pred (by omega : a ≠ 0)]
    norm_num [endpointRatio,baseline]
    push_cast
    ring

theorem actual_degree_positive (m : ℕ) (v : Vertex m) : 1 ≤ degree v := by
  cases v with
  | none => rw [center_degree]; omega
  | some e =>
    rcases e with ⟨b,o⟩
    cases o with
    | none => rw [hub_degree]; omega
    | some i => rw [leaf_degree]

private theorem increments_le_two (m : ℕ) (A S : Finset (Edge m))
    (hA : A.card = 2) (hSA : S ⊆ A) (v : Vertex m) : increments A S v ≤ 2 := by
  classical
  have hs : (Finset.univ.filter (fun e : Edge m => src e=v ∧ e ∈ S)).card ≤ S.card :=
    Finset.card_le_card (by intro e he; exact (Finset.mem_filter.mp he).2.2)
  have ht : (Finset.univ.filter (fun e : Edge m => tgt e=v ∧ e ∈ A \ S)).card ≤
      (A \ S).card :=
    Finset.card_le_card (by intro e he; exact (Finset.mem_filter.mp he).2.2)
  have hh := Finset.card_sdiff_add_card_eq_card hSA
  dsimp [increments]
  omega

private theorem actual_weight_ratios (m : ℕ) (A S : Finset (Edge m))
    (hA : A.card = 2) (hSA : S ⊆ A) :
    physicalWeight (totals A) (shares S) =
      (((24:ℝ)^(2*m)*360^2) * ((Nat.factorial m:ℝ)^2/(2:ℝ)^(2*m+3))) *
        ∏ v : Vertex m, endpointRatio (degree v) (increments A S v) := by
  rw [actual_common_edge_factor m A S hA hSA]
  have hp :
      (∏ v : Vertex m, (Nat.factorial (degree v+increments A S v-1) : ℝ) /
        (Nat.factorial (increments A S v+2) : ℝ)) =
        (∏ v : Vertex m, baseline (degree v)) *
        ∏ v : Vertex m, endpointRatio (degree v) (increments A S v) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    exact local_factorial_ratio (degree v) (increments A S v)
      (actual_degree_positive m v) (increments_le_two m A S hA hSA v)
  rw [hp,baseline_product]
  ring

private theorem common_numeric_factor (m : ℕ) :
    ((24:ℝ)^(2*m)*360^2) * ((Nat.factorial m:ℝ)^2/(2:ℝ)^(2*m+3)) =
      16200*(Nat.factorial m:ℝ)^2*(12:ℝ)^(2*m) := by
  have hp : (24:ℝ)^(2*m) = (2:ℝ)^(2*m)*(12:ℝ)^(2*m) := by
    rw [← mul_pow]
    norm_num
  rw [hp,pow_add]
  field_simp
  ring

theorem actual_weight_normalized (m : ℕ) (A S : Finset (Edge m))
    (hA : A.card = 2) (hSA : S ⊆ A) :
    physicalWeight (totals A) (shares S) =
      (16200*(Nat.factorial m:ℝ)^2*(12:ℝ)^(2*m)) *
        ∏ v : Vertex m, endpointRatio (degree v) (increments A S v) := by
  rw [actual_weight_ratios m A S hA hSA,common_numeric_factor]

end FiolDoubleHub


end D5.S3.Zeros.LeeYang
