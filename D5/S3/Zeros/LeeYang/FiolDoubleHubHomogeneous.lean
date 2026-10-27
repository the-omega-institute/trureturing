/- GID: D5/S3/Zeros/LeeYang/FiolDoubleHubHomogeneous
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/FiolDoubleHubHomogeneous
   mirror-E: none(waiver:analytic-family-proof)
   anchors: []
   utility: none
   digest: All-parameter physical double-hub homogeneous identities. -/
import D5.S3.Zeros.LeeYang.FiolDoubleHubCoefficient
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
namespace FiolDoubleHub

private theorem selected_total_mass (m : ℕ) (A S : Finset (Edge m))
    (hA : A.card=2) (hS : S⊆A) :
    (∑ v : Vertex m,(degree v+increments A S v))=4*m+6 := by
  classical
  have hE : Fintype.card (Edge m)=2*m+2 := by simp [Edge];omega
  have hr (e : Edge m) : totals A e=2 ∨ totals A e=3 := by
    unfold totals
    split_ifs <;> omega
  have hfilter : (Finset.univ.filter (fun e : Edge m => totals A e=3))=A := by
    ext e
    simp [totals]
  have hn : (∑ e : Edge m,totals A e)=4*m+6 := by
    apply total_degree m hE (totals A) hr
    rw [hfilter]
    exact hA
  have hk : shares S ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits (totals A) := by
    apply (split_iff A (shares S)).mpr
    intro e
    constructor
    · intro he
      by_cases hs : e∈S <;> simp [shares,hs]
    · intro he
      have hs : e∉S := fun h => he (hS h)
      simp [shares,hs]
  have hm := mass_total src tgt (totals A) (shares S) hk
  rw [hn] at hm
  calc
    _ = ∑ v : Vertex m,mass (totals A) (shares S) v := by
      apply Finset.sum_congr rfl
      intro v hv
      change _ = D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass src tgt (totals A) (shares S) v
      rw [actual_mass src tgt A S hS v]
      dsimp [degree,increments]
      omega
    _ = _ := hm

private theorem constant_mul_degree_bound (c : ℝ) (p : Polynomial ℝ) (D : ℕ)
    (hp : p.natDegree≤D) : (Polynomial.C c*p).natDegree≤D := by
  exact Polynomial.natDegree_mul_le.trans (by simpa using hp)

private theorem actual_source_degree_le (m cutoff : ℕ) (hc : 3≤cutoff) :
    (sourceCoefficient m cutoff).natDegree≤4*m+6 := by
  classical
  rw [all_endpoint_coefficient m cutoff hc]
  apply Polynomial.natDegree_sum_le_of_forall_le _
  intro A hA
  apply constant_mul_degree_bound
  apply Polynomial.natDegree_sum_le_of_forall_le _
  intro S hS
  apply constant_mul_degree_bound
  have ha := (Finset.mem_powersetCard.mp hA).2
  have hs := Finset.mem_powerset.mp hS
  calc
    _ ≤ ∑ v : Vertex m,
        (1+Polynomial.C ((-1:ℝ)^degree v)*Polynomial.X^(degree v+increments A S v)).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ v : Vertex m,(degree v+increments A S v) := by
      apply Finset.sum_le_sum
      intro v hv
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · simp
      · exact Polynomial.natDegree_mul_le.trans (by simp)
    _ = _ := selected_total_mass m A S ha hs

private theorem candidate_degree_le (m : ℕ) (hm : 1≤m) : (R m).natDegree≤4*m+6 := by
  have hb := actual_source_degree_le m 3 (by omega)
  rw [actual_coefficient_identity m 3 hm (by omega)] at hb
  have hs : 200*(12:ℝ)^(2*m)≠0 := by positivity
  rwa [Polynomial.natDegree_C_mul hs] at hb

theorem actual_closed_ratio (m cutoff : ℕ) (hm : 1≤m) (hc : 3≤cutoff)
    (a b : ℂ) (ha : a≠0) :
    homogeneousCoefficient m cutoff a b = (200*(12:ℂ)^(2*m))*a^(4*m+6)*
      ((R m).map Complex.ofRealHom).eval (b/a) := by
  rw [actual_homogeneous_ratio m cutoff hc a b ha,actual_coefficient_identity m cutoff hm hc]
  simp only [map_mul,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
    Polynomial.eval₂_eq_eval_map,Complex.ofRealHom_eq_coe,map_mul,map_ofNat,map_pow]
  ring

private theorem expected_ratio (m : ℕ) (hm : 1≤m) (a b : ℂ) (ha : a≠0) :
    expectedHomogeneousCoefficient m a b = (200*(12:ℂ)^(2*m))*a^(4*m+6)*
      ((R m).map Complex.ofRealHom).eval (b/a) := by
  have hd : ((R m).map Complex.ofRealHom).natDegree<4*m+7 :=
    lt_of_le_of_lt Polynomial.natDegree_map_le (by have := candidate_degree_le m hm;omega)
  rw [Polynomial.eval_eq_sum_range' hd]
  unfold expectedHomogeneousCoefficient
  rw [mul_assoc (200*(12:ℂ)^(2*m)) (a^(4*m+6))]
  apply congrArg (fun z : ℂ => (200*(12:ℂ)^(2*m))*z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hle : j≤4*m+6 := by have := Finset.mem_range.mp hj;omega
  simp only [Polynomial.coeff_map,Complex.ofRealHom_eq_coe]
  have hp : a^(4*m+6)=a^(4*m+6-j)*a^j := by
    rw [←pow_add,Nat.sub_add_cancel hle]
  rw [hp,div_pow]
  field_simp [ha]
  <;> ring

private theorem homogeneous_pair_formula (m cutoff : ℕ) (hc : 3≤cutoff) (a b : ℂ) :
    homogeneousCoefficient m cutoff a b =
      ∑ A ∈ (Finset.univ : Finset (Edge m)).powersetCard 2,
        (sourcePrefactor (totals A) : ℂ)*
          ∑ k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits (totals A),
            homogeneousSplitSource (totals A) k a b := by
  classical
  have hE : Fintype.card (Edge m)=2*m+2 := by simp [Edge];omega
  unfold homogeneousCoefficient homogeneousTruncation targetMonomial
  rw [coefficient_extract m cutoff hE,pair_sum cutoff hc]
  rfl

private theorem actual_homogeneous_continuous (m cutoff : ℕ) (hc : 3≤cutoff) (b : ℂ) :
    Continuous (fun a : ℂ => homogeneousCoefficient m cutoff a b) := by
  classical
  simp_rw [homogeneous_pair_formula m cutoff hc]
  unfold homogeneousSplitSource
  fun_prop

private theorem expected_homogeneous_continuous (m : ℕ) (b : ℂ) :
    Continuous (fun a : ℂ => expectedHomogeneousCoefficient m a b) := by
  unfold expectedHomogeneousCoefficient
  fun_prop

theorem actual_homogeneous_identity (m cutoff : ℕ) (hm : 1≤m) (hc : 3≤cutoff)
    (a b : ℂ) : homogeneousCoefficient m cutoff a b=expectedHomogeneousCoefficient m a b := by
  have hd : Dense ({0}ᶜ : Set ℂ) := by
    rw [←interior_eq_empty_iff_dense_compl]
    simp
  have heq := Continuous.ext_on hd (actual_homogeneous_continuous m cutoff hc b)
    (expected_homogeneous_continuous m b) (by
      intro x hx
      have hx0 : x≠0 := by simpa using hx
      change homogeneousCoefficient m cutoff x b=expectedHomogeneousCoefficient m x b
      rw [actual_closed_ratio m cutoff hm hc x b hx0,expected_ratio m hm x b hx0])
  exact congrFun heq a

end FiolDoubleHub

end D5.S3.Zeros.LeeYang
