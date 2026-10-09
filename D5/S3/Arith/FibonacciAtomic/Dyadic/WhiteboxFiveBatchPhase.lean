/- GID: D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxFiveBatchPhase
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxFiveBatchPhase
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: All fair-prefix total controllers have the sharp five-tree batch phase. -/

import D5.S3.Arith.FibonacciAtomic.DyadicSupportLines
import D5.S3.Arith.FibonacciAtomic.MersenneDyadicSupportLines
import D5.S3.Arith.FibonacciAtomic.Scale36ActualEndpointAcquisition
import D5.S3.Arith.FibonacciAtomic.Scale38NestedCompensation
import D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase
import Mathlib.Logic.Equiv.Fin.Rotate
local notation "Source" => D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.Source
local notation "Nonconflict" => D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation.Nonconflict
local notation "kappa_hist" => D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory.kappa_hist
local notation "minimumMass" => (fun p : Fin 5 → ℝ => Finset.univ.inf' (by simp) p)
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase
open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic

def sharp (N l : ℝ) : ℝ := min (22*N) (min (349*N/16+3*l) (109*N/5+18*l/5))


private theorem support (p : Fin 5 → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    0 ≤ minimumMass p ∧ minimumMass p ≤ 1/5 ∧
      16*minimumMass p ≤ DyadicSupportLines.cost p ∧
      48*minimumMass p-6 ≤ DyadicSupportLines.cost p := by
  exact (DyadicSupportLines.result p hp hs).2

private theorem affine_lower (N l t e : ℝ) (hl : 0 ≤ l) (ht0 : 0 ≤ t) (ht3 : t ≤ 1/5)
    (h6 : 16*t ≤ e) (h14 : 48*t-6 ≤ e) :
    sharp N l ≤ 22*N-N*t+l*e := by
  unfold sharp
  by_cases low : N ≤ 16*l
  · apply le_trans (min_le_left _ _)
    have H1 := mul_nonneg hl (sub_nonneg.mpr h6)
    have H2 := mul_nonneg (sub_nonneg.mpr low) ht0
    nlinarith only [H1,H2]
  · by_cases high : 48*l ≤ N
    · apply le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
      have H1 := mul_nonneg hl (sub_nonneg.mpr h14)
      have H2 := mul_nonneg (sub_nonneg.mpr high) (sub_nonneg.mpr ht3)
      nlinarith only [H1,H2]
    · apply le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
      by_cases small : t ≤ 3/16
      · have H1 := mul_nonneg hl (sub_nonneg.mpr h6)
        have H2 := mul_nonneg (by linarith : 0 ≤ N-16*l) (sub_nonneg.mpr small)
        nlinarith only [H1,H2]
      · have H1 := mul_nonneg hl (sub_nonneg.mpr h14)
        have H2 := mul_nonneg (by linarith : 0 ≤ 48*l-N) (by linarith : 0 ≤ t-3/16)
        nlinarith only [H1,H2]

private theorem phase_switches (N l : ℝ) (hl : 0 ≤ l) :
    (N ≤ 16*l → sharp N l = 22*N) ∧
    (16*l ≤ N → N ≤ 48*l → sharp N l = 349*N/16+3*l) ∧
    (48*l ≤ N → sharp N l = 109*N/5+18*l/5) := by
  unfold sharp
  constructor
  · intro H
    rw [min_eq_left (le_min (by linarith) (by linarith))]
  · constructor
    · intro H1 H2
      rw [min_eq_left (show 349*N/16+3*l ≤ 109*N/5+18*l/5 by linarith),
        min_eq_right (show 349*N/16+3*l ≤ 22*N by linarith)]
    · intro H
      rw [min_eq_right (show 109*N/5+18*l/5 ≤ 349*N/16+3*l by linarith),
        min_eq_right (show 109*N/5+18*l/5 ≤ 22*N by linarith)]

end D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Codes
open scoped BigOperators ENNReal Classical
open MeasureTheory
open D5.S3.Arith.FibonacciAtomic.CarryGraphEmbedding
open D5.S3.Arith.FibonacciAtomic.CarryGraphRealization
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)

def biasedFive : Path :=
  ⟨fun d => if d=0 then ⟨1,5⟩ else if d=1 then ⟨2,5⟩ else if d=2 then ⟨3,4⟩
      else if d=3 then ⟨2,4⟩ else ⟨0,4⟩,
    fun d => if d=1 then ⟨0,1,0⟩ else if d=2 ∨ d=3 then ⟨1,0,0⟩ else ⟨0,0,0⟩⟩

def uniformFive : Path :=
  ⟨fun d => ⟨if d%4=0 then 1 else if d%4=1 then 2 else if d%4=2 then 4 else 3,5⟩,
    fun d => ⟨if d%4=2 ∨ d%4=3 then 1 else 0,0,0⟩⟩

private theorem biased_legal : IsRootPath 5 biasedFive := by
  constructor
  · rfl
  · intro d
    by_cases hd : d<4
    · interval_cases d <;> norm_num [biasedFive,IsState,Legal,successor,ones]
    · have h0 : d≠0 := by omega
      have h1 : d≠1 := by omega
      have h2 : d≠2 := by omega
      have h3 : d≠3 := by omega
      have hn0 : d+1≠0 := by omega
      have hn1 : d+1≠1 := by omega
      have hn2 : d+1≠2 := by omega
      have hn3 : d+1≠3 := by omega
      norm_num [biasedFive,IsState,Legal,successor,ones,h0,h1,h2,h3,hn0,hn1,hn2,hn3]

private theorem uniform_legal : IsRootPath 5 uniformFive := by
  constructor
  · rfl
  · intro d
    have bound : d%4<4 := Nat.mod_lt _ (by omega)
    interval_cases h : d%4 <;>
      have hn : (d+1)%4 = (d%4+1)%4 := by omega
    all_goals norm_num [uniformFive,IsState,Legal,successor,ones,h,hn]

private theorem biased_cost : pathCost biasedFive = 3 := by
  unfold pathCost
  have support : (fun d : ℕ => ((biasedFive.state d).r : ℝ)/(2:ℝ)^d) =
      (fun d => if d=0 then (1:ℝ) else if d=1 then 1 else if d=2 then 3/4 else if d=3 then 1/4 else 0) := by
    funext d
    by_cases hd : d<4
    · interval_cases d <;> norm_num [biasedFive]
    · have h0 : d≠0 := by omega
      have h1 : d≠1 := by omega
      have h2 : d≠2 := by omega
      have h3 : d≠3 := by omega
      norm_num [biasedFive,h0,h1,h2,h3]

  rw [support,tsum_eq_sum (s := Finset.range 4) (fun d hd => by
    have h : 4≤d := by simpa using hd
    have h0 : d≠0 := by omega
    have h1 : d≠1 := by omega
    have h2 : d≠2 := by omega
    have h3 : d≠3 := by omega
    simp [h0,h1,h2,h3])]
  norm_num [Finset.sum_range_succ]

private theorem biased_law (i : Fin 5) :
    Real.ofDigits (labelDigit biasedFive i) = if i=4 then (1/4:ℝ) else 3/16 := by
  have dig : labelDigit biasedFive i = fun d =>
      if d=1 then (if i=4 then (1:Fin 2) else 0) else
        if d=2 ∨ d=3 then (if i=4 then 0 else 1) else 0 := by
    funext d
    by_cases hd : d<4
    · fin_cases i <;> interval_cases d <;> norm_num [labelDigit,labelSet,biasedFive,Fin.ext_iff]
    · have h0 : d≠0 := by omega
      have h1 : d≠1 := by omega
      have h2 : d≠2 := by omega
      have h3 : d≠3 := by omega
      fin_cases i <;> norm_num [labelDigit,labelSet,biasedFive,Fin.ext_iff,h0,h1,h2,h3]

  rw [dig,Real.ofDigits_eq_sum_add_ofDigits _ 4]
  have tail : (fun d => if d+4=1 then (if i=4 then (1:Fin 2) else 0) else
      if d+4=2 ∨ d+4=3 then (if i=4 then 0 else 1) else 0) = fun _ => (0:Fin 2) := by
    funext d; simp
  rw [tail]
  have zero : Real.ofDigits (fun _ => (0:Fin 2)) = 0 := by simp [Real.ofDigits,Real.ofDigitsTerm]
  rw [zero]
  fin_cases i <;> norm_num [Finset.sum_range_succ,Real.ofDigitsTerm,Fin.ext_iff]

private theorem uniform_law (i : Fin 5) : Real.ofDigits (labelDigit uniformFive i) = (1/5:ℝ) := by
  have same (i j : Fin 5) : labelDigit uniformFive i = labelDigit uniformFive j := by
    funext d
    have hi : (i.val:ℤ)<5 := by exact_mod_cast i.isLt
    have hj : (j.val:ℤ)<5 := by exact_mod_cast j.isLt
    by_cases hd : d%4=2 ∨ d%4=3 <;>
      simp [labelDigit,labelSet,uniformFive,hd,hi,hj,not_le_of_gt hi,not_le_of_gt hj,Nat.not_le_of_lt i.isLt,Nat.not_le_of_lt j.isLt]
  have H := (D5.S3.Arith.FibonacciAtomic.CarryGraphRealization.result 5 (by omega) uniformFive uniform_legal).2.1
  have equal (j : Fin 5) : Real.ofDigits (labelDigit uniformFive j) =
      Real.ofDigits (labelDigit uniformFive i) := congrArg Real.ofDigits (same j i)
  simp_rw [equal] at H
  norm_num at H
  linarith

private theorem uniform_cost : pathCost uniformFive = 18/5 := by
  let f := fun d : ℕ => ((uniformFive.state d).r:ℝ)/(2:ℝ)^d
  have hn (d : ℕ) : 0≤f d := by dsimp [f,uniformFive]; split_ifs <;> positivity
  have upper (d : ℕ) : f d ≤ 4*(1/2:ℝ)^d := by
    have H : (((uniformFive.state d).r:ℤ):ℝ)≤4 := by
      dsimp [uniformFive]; split_ifs <;> norm_num
    simpa [f,div_eq_mul_inv,inv_pow] using div_le_div_of_nonneg_right H (by positivity : (0:ℝ)≤2^d)
  have summable : Summable f := Summable.of_nonneg_of_le hn upper
    ((summable_geometric_of_abs_lt_one (r := (1/2:ℝ)) (by norm_num)).mul_left 4)
  have shift (d : ℕ) : f (d+4)=f d/16 := by
    dsimp [f,uniformFive]
    simp only [Nat.add_mod,Nat.add_zero,Nat.mod_self,Nat.mod_mod,Int.cast_ite,pow_add]
    split_ifs <;> push_cast <;> field_simp <;> ring
  have H := summable.sum_add_tsum_nat_add 4
  simp_rw [shift] at H
  rw [tsum_div_const] at H
  have head : ∑ d ∈ Finset.range 4, f d = 27/8 := by
    norm_num [f,uniformFive,Finset.sum_range_succ]
  rw [head] at H
  change (∑' d, f d)=18/5
  linarith only [H]

end D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Codes
set_option autoImplicit false
namespace D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase
open scoped BigOperators ENNReal Classical
open MeasureTheory
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition
open D5.S3.Arith.FibonacciAtomic
open D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail

def row5 (i : Fin 5) : Unit ⊕ (Fin 2 × Fin 2) :=
  if i.val = 0 then .inl () else if i.val = 1 then .inr (0,0)
    else if i.val = 2 then .inr (0,1) else if i.val = 3 then .inr (1,0) else .inr (1,1)

local notation "prototypes" => (fun i : Fin 5 => Scale36ActualEndpointAcquisition.family 2 (row5 i))

local notation "selected" => D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase.selected
local notation "Coarse" => D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase.Coarse
local notation "Tuple" => (fun N : ℕ => Fin N → Fin 5)

def paidTuple (s : PrefixSampler Strategy) (N : ℕ) (l : ℝ) (q : Tuple N) (t : Tape) : ℝ≥0∞ :=
  ENNReal.ofReal l * bill s t + ∑ r : Fin N, (cost (selected s t) (prototypes (q r)) : ℝ≥0∞)

def G (s : PrefixSampler Strategy) (N : ℕ) (l : ℝ) : ℝ≥0∞ :=
  Finset.univ.sup (fun q : Tuple N => ∫⁻ t, paidTuple s N l q t ∂fairTape)

def H (s : PrefixSampler Strategy) (N : ℕ) (l : ℝ) : ℝ≥0∞ :=
  ∫⁻ t, Finset.univ.sup (fun q : Tuple N => paidTuple s N l q t) ∂fairTape

def rawGamma (N : ℕ) (l : ℝ) : ℝ≥0∞ := ⨅ s : PrefixSampler Strategy, G s N l

def coarseGamma (N : ℕ) (l : ℝ) : ℝ≥0∞ := ⨅ s : {s : PrefixSampler Strategy // Coarse s}, G s.val N l

def rawH (N : ℕ) (l : ℝ) : ℝ≥0∞ := ⨅ s : PrefixSampler Strategy, H s N l

def coarseH (N : ℕ) (l : ℝ) : ℝ≥0∞ := ⨅ s : {s : PrefixSampler Strategy // Coarse s}, H s.val N l

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Classical
open D5.S3.Arith.FibonacciAtomic
open ActualTreeReadoutAcquisition
open ActualJointResponseCostCore

private theorem row5_injective : Function.Injective row5 := by decide

private theorem prototype_facts : Function.Injective prototypes ∧
    (∀ i, Positive (prototypes i) ∧ (leaves (prototypes i)).length = 21) ∧
    ∀ i j, Nonconflict (prototypes i) (prototypes j) := by
  have S := Scale36ActualEndpointAcquisition.family_structure 2 (by omega)
  refine ⟨S.1.comp row5_injective, ?_,fun i j => S.2.2 _ _⟩
  intro i
  refine ⟨(S.2.1 _).2.1, ?_⟩
  fin_cases i <;> rfl

private theorem profile_domination (pi : Strategy) :
    ∃ a : Fin 5, ∀ i, 22-(if a=i then 1 else 0) ≤ cost pi (prototypes i) := by
  have core := ActualJointResponseCostCore.result 5 (by omega) prototypes
    (fun i => (prototype_facts.2.1 i).1) prototype_facts.1
  obtain ⟨v,hv,dom⟩ := core.2.2.2.1 pi
  obtain ⟨r,hr⟩ := hv
  by_cases zero : ∃ a, gain r a = 0
  · obtain ⟨a,ha⟩ := zero
    refine ⟨a,fun i => ?_⟩
    have bound := dom i
    rw [hr i,(prototype_facts.2.1 i).2] at bound
    by_cases same : a=i
    · simp [same]; omega
    · have hpos : 1 ≤ gain r i := by
        have hn : gain r i ≠ 0 := by
          intro h
          exact same (D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase.zero_gain_unique prototypes prototype_facts.2.2 r a i
            (Finset.mem_univ _) (Finset.mem_univ _) ha h)
        omega
      simp [same]; omega
  · refine ⟨0,fun i => ?_⟩
    have hpos : 1 ≤ gain r i := by
      have hn : gain r i ≠ 0 := by intro h; exact zero ⟨i,h⟩
      omega
    have bound := dom i
    rw [hr i,(prototype_facts.2.1 i).2] at bound
    dsimp only at bound ⊢
    split_ifs <;> omega

private theorem actual_endpoints (a : Fin 5) : ∃ pi : Strategy,
    Function.FactorsThrough pi.policy kappa_hist ∧
      ∀ i, cost pi (prototypes i) = 22-(if a=i then 1 else 0) := by
  have S := Scale36ActualEndpointAcquisition.result 2 (by omega)
  obtain ⟨pi,hcoarse,hcost⟩ := S.2.2.2.2 (row5 a)
  refine ⟨pi,hcoarse,fun i => ?_⟩
  have H := (hcost (row5 i)).2
  simpa only [Nat.reduceMul,Nat.reduceAdd,row5_injective.eq_iff] using H

open scoped BigOperators ENNReal Classical
open MeasureTheory
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition
open D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail

def endpointIndex (pi : Strategy) : Fin 5 := Classical.choose (profile_domination pi)

local notation "labelSampler" => (fun s : PrefixSampler Strategy => relabel endpointIndex s)

private theorem endpointIndex_bound (pi : Strategy) (i : Fin 5) :
    22-(if endpointIndex pi=i then 1 else 0) ≤ cost pi (prototypes i) :=
  Classical.choose_spec (profile_domination pi) i

open D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase (selected_emitted)

def profileCost (a i : Fin 5) : ℝ≥0∞ := ((22-(if a=i then 1 else 0) : ℕ) : ℝ≥0∞)

def profileRead (s : PrefixSampler (Fin 5)) (i : Fin 5) (t : Tape) : ℝ≥0∞ :=
  ∑ a : Fin 5, (emitted s a).indicator (fun _ => profileCost a i) t

private theorem profileRead_le (s : PrefixSampler Strategy) (i : Fin 5) :
    profileRead (labelSampler s) i ≤ᵐ[fairTape]
      (fun t => (cost (selected s t) (prototypes i) : ℝ≥0∞)) := by
  filter_upwards [s.terminates] with t ht
  obtain ⟨d,pi,hpi⟩ := ht
  have hem : t ∈ emitted s pi := ⟨d,hpi⟩
  have hm : t ∈ emitted (labelSampler s) (endpointIndex pi) :=
    (relabel_emitted endpointIndex s _ t).mpr ⟨pi,hem,rfl⟩
  have other (a : Fin 5) (ha : a ≠ endpointIndex pi) :
      t ∉ emitted (labelSampler s) a := by
    intro h
    exact Set.disjoint_left.mp (emitted_disjoint (labelSampler s) ha) h hm
  have exactSum : profileRead (labelSampler s) i t = profileCost (endpointIndex pi) i := by
    unfold profileRead
    rw [Finset.sum_eq_single (endpointIndex pi)]
    · simp [Set.indicator_of_mem hm]
    · intro a ha hn; simp [Set.indicator_of_notMem (other a hn)]
    · simp
  rw [exactSum,selected_emitted s t pi hem]
  have H := endpointIndex_bound pi i
  unfold profileCost
  by_cases hh : endpointIndex pi=i <;> simp [hh] at H ⊢ <;> exact_mod_cast H


set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators ENNReal Classical
open MeasureTheory
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)
open D5.S3.Arith.FibonacciAtomic
open ActualTreeReadoutAcquisition
open D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail

private theorem profileRead_measurable (s : PrefixSampler (Fin 5)) (i : Fin 5) :
    Measurable (profileRead s i) := Finset.measurable_sum _
  (fun a _ => measurable_const.indicator (emitted_measurable s a))

private theorem profile_expectation (s : PrefixSampler (Fin 5)) (i : Fin 5) :
    (∫⁻ t, profileRead s i t ∂fairTape) = ENNReal.ofReal (22-law s i) := by
  unfold profileRead
  rw [lintegral_finsetSum Finset.univ (fun a _ => measurable_const.indicator (emitted_measurable s a))]
  simp_rw [lintegral_indicator_const (emitted_measurable s _)]
  have mass (a : Fin 5) : fairTape (emitted s a) = ENNReal.ofReal (law s a) :=
    (ENNReal.ofReal_toReal (measure_ne_top fairTape _)).symm
  have scale (a : Fin 5) : profileCost a i * fairTape (emitted s a) =
      ENNReal.ofReal ((22-(if a=i then (1 : ℝ) else 0))*law s a) := by
    rw [mass,ENNReal.ofReal_mul (by split_ifs <;> norm_num)]
    unfold profileCost
    split_ifs <;> norm_num
  simp_rw [scale]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg
    (by split_ifs <;> norm_num) ((law_simplex s).1 a))]
  have eqn : (∑ a : Fin 5, (22-(if a=i then (1 : ℝ) else 0))*law s a) = 22-law s i := by
    simp only [sub_mul,ite_mul,one_mul,zero_mul,Finset.sum_sub_distrib,
      ← Finset.mul_sum,(law_simplex s).2,Finset.sum_ite_eq',Finset.mem_univ,
      if_pos, mul_one]
  rw [eqn]

private theorem fixed_tuple_lower (s : PrefixSampler Strategy) (N : ℕ) (l : ℝ) (i : Fin 5) :
    ENNReal.ofReal l * (∫⁻ t, bill s t ∂fairTape) +
      (N : ℝ≥0∞)*ENNReal.ofReal (22-law (labelSampler s) i) ≤ G s N l := by
  let q : Tuple N := fun _ => i
  have small (t : Tape) : ENNReal.ofReal l * bill s t +
      (N : ℝ≥0∞)*profileRead (labelSampler s) i t =
      ENNReal.ofReal l * bill s t + ∑ _r : Fin N, profileRead (labelSampler s) i t := by simp
  have dom : (fun t => ENNReal.ofReal l * bill s t +
      (N : ℝ≥0∞)*profileRead (labelSampler s) i t) ≤ᵐ[fairTape] paidTuple s N l q := by
    filter_upwards [profileRead_le s i] with t ht
    rw [small]
    have HH := add_le_add_right
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun r _ => ht))
      (ENNReal.ofReal l * bill s t)
    simpa [paidTuple,q,add_comm] using HH
  have integral := lintegral_mono_ae dom
  have hm : Measurable (fun t : Tape => ENNReal.ofReal l * bill s t) :=
    measurable_const.mul (bill_measurable s)
  rw [lintegral_add_left hm,
    lintegral_const_mul _ (bill_measurable s),
    lintegral_const_mul _ (profileRead_measurable _ _), profile_expectation] at integral
  exact integral.trans (Finset.le_sup (s := Finset.univ)
    (f := fun q : Tuple N => ∫⁻ t, paidTuple s N l q t ∂fairTape) (Finset.mem_univ q))

private theorem all_controller_lower (s : PrefixSampler Strategy) (N : ℕ) (l : ℝ) (hl : 0 ≤ l) :
    ENNReal.ofReal (D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.sharp N l) ≤ G s N l := by
  let p := law (labelSampler s)
  let t := minimumMass p
  have hp := law_simplex (labelSampler s)
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' (by simp : (Finset.univ : Finset (Fin 5)).Nonempty) p
  have ht : t = p i := he
  have H := DyadicSupportLines.result p hp.1 hp.2
  have costpos : 0 ≤ DyadicSupportLines.cost p := by
    have bounds := Phase.support p hp.1 hp.2
    linarith [bounds.1, bounds.2.2.1]
  have ht22 : 0 ≤ 22-t := by have hh := (D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.support p hp.1 hp.2).2.1; dsimp [t]; linarith
  have real_lower := D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.affine_lower N l t (DyadicSupportLines.cost p) hl
    (D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.support p hp.1 hp.2).1 (D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.support p hp.1 hp.2).2.1
    (D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.support p hp.1 hp.2).2.2.1 (D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.support p hp.1 hp.2).2.2.2
  have paid := ddg_lower (labelSampler s) H.1
  simp only [relabel_bill] at paid
  calc
    ENNReal.ofReal (D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.sharp N l) ≤
        ENNReal.ofReal ((N : ℝ)*(22-t)+l*DyadicSupportLines.cost p) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith only [real_lower]
    _ = ENNReal.ofReal l*ENNReal.ofReal (DyadicSupportLines.cost p) +
        (N : ℝ≥0∞)*ENNReal.ofReal (22-t) := by
      rw [ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) ht22) (mul_nonneg hl costpos),
        ENNReal.ofReal_mul (Nat.cast_nonneg N),ENNReal.ofReal_mul hl]
      simp [add_comm]
    _ ≤ ENNReal.ofReal l*(∫⁻ x, bill s x ∂fairTape)+(N : ℝ≥0∞)*ENNReal.ofReal (22-t) := by
      have mult := mul_le_mul_right paid (ENNReal.ofReal l)
      exact add_le_add mult le_rfl
    _ ≤ G s N l := by simpa only [ht,p] using fixed_tuple_lower s N l i

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators ENNReal Classical
open MeasureTheory
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition
open D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail

def endpoint (a : Fin 5) : Strategy := Classical.choose (actual_endpoints a)

private theorem endpoint_coarse (a : Fin 5) : Function.FactorsThrough (endpoint a).policy kappa_hist :=
  (Classical.choose_spec (actual_endpoints a)).1

private theorem endpoint_cost (a i : Fin 5) : cost (endpoint a) (prototypes i) =
    22-(if a=i then 1 else 0) := (Classical.choose_spec (actual_endpoints a)).2 i

local notation "endpointSampler" => (fun s : PrefixSampler (Fin 5) => relabel endpoint s)

private theorem endpointSampler_coarse (s : PrefixSampler (Fin 5)) : Coarse (endpointSampler s) := by
  intro d w pi hpi
  obtain ⟨a,_,ha⟩ := Option.map_eq_some_iff.mp hpi
  rw [← ha]
  exact endpoint_coarse a

private theorem profileRead_single (s : PrefixSampler (Fin 5)) (i a : Fin 5) (t : Tape)
    (ha : t ∈ emitted s a) : profileRead s i t = profileCost a i := by
  unfold profileRead
  rw [Finset.sum_eq_single a]
  · exact Set.indicator_of_mem ha _
  · intro b hb hba
    have hno : t ∉ emitted s b := fun h =>
      Set.disjoint_left.mp (emitted_disjoint s hba) h ha
    exact Set.indicator_of_notMem hno _
  · simp

private theorem endpointTuple_expectation (s : PrefixSampler (Fin 5)) (N : ℕ) (l : ℝ) (q : Tuple N) :
    (∫⁻ t, paidTuple (endpointSampler s) N l q t ∂fairTape) =
      ENNReal.ofReal l*(∫⁻ t, bill s t ∂fairTape)+
        ∑ r : Fin N, ENNReal.ofReal (22-law s (q r)) := by
  have point : paidTuple (endpointSampler s) N l q =ᵐ[fairTape]
      (fun t => ENNReal.ofReal l*bill s t+∑ r : Fin N, profileRead s (q r) t) := by
    filter_upwards [s.terminates] with t ht
    obtain ⟨d,a,ha⟩ := ht
    have emitted_a : t ∈ emitted s a := ⟨d,ha⟩
    have hem : t ∈ emitted (endpointSampler s) (endpoint a) :=
      (relabel_emitted endpoint s _ t).mpr ⟨a,emitted_a,rfl⟩
    unfold paidTuple
    rw [selected_emitted _ t (endpoint a) hem]
    simp only [relabel_bill]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [profileRead_single s _ a t emitted_a]
    unfold profileCost
    rw [endpoint_cost]
  rw [lintegral_congr_ae point]
  have hm : Measurable (fun t : Tape => ENNReal.ofReal l*bill s t) :=
    measurable_const.mul (bill_measurable s)
  rw [lintegral_add_left hm,lintegral_const_mul _ (bill_measurable s),
    lintegral_finsetSum Finset.univ (fun r _ => profileRead_measurable s (q r))]
  simp_rw [profile_expectation]

private theorem endpointG_exact (s : PrefixSampler (Fin 5)) (N : ℕ) (l : ℝ) :
    G (endpointSampler s) N l = ENNReal.ofReal l*(∫⁻ t, bill s t ∂fairTape)+
      (N : ℝ≥0∞)*ENNReal.ofReal (22-minimumMass (law s)) := by
  let t := minimumMass (law s)
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' (by simp : (Finset.univ : Finset (Fin 5)).Nonempty) (law s)
  have ht : t=law s i := he
  apply le_antisymm
  · unfold G
    apply Finset.sup_le
    intro q hq
    rw [endpointTuple_expectation]
    have term (r : Fin N) : ENNReal.ofReal (22-law s (q r)) ≤ ENNReal.ofReal (22-t) := by
      apply ENNReal.ofReal_le_ofReal
      have hmin : t ≤ law s (q r) := Finset.inf'_le _ (Finset.mem_univ _)
      linarith
    have sums := Finset.sum_le_sum (s := Finset.univ) (fun r _ => term r)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      add_le_add le_rfl sums
  · have H := Finset.le_sup (s := Finset.univ)
      (f := fun q : Tuple N => ∫⁻ t, paidTuple (endpointSampler s) N l q t ∂fairTape)
      (Finset.mem_univ (fun _ => i))
    rw [endpointTuple_expectation] at H
    change t=law s i at ht
    change ENNReal.ofReal l*(∫⁻ t, bill s t ∂fairTape)+(N : ℝ≥0∞)*ENNReal.ofReal (22-t) ≤ _
    simpa [G,ht] using H

def point : PrefixSampler (Fin 5) where
  observe _ _ := some 0
  persistent _ _ _ _ i h := h
  terminates := Filter.Eventually.of_forall (fun _ => ⟨0,0,rfl⟩)

private theorem point_bill : bill point = (fun _ => 0) := by
  funext t
  simp [bill,active,point]

private theorem point_law (i : Fin 5) : law point i = if i=0 then 1 else 0 := by
  have evt : emitted point i = if i=0 then Set.univ else ∅ := by
    ext t
    by_cases h : i=0 <;> simp [emitted,point,h,eq_comm]
  unfold law
  rw [evt]
  split_ifs <;> simp

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators ENNReal Classical
open MeasureTheory
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition
open D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail

local notation "biasedBase" => D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail.Paths.fromPath 5 D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Codes.biasedFive (by omega) D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Codes.biased_legal

local notation "rotate" => finRotate 5

local notation "biased" => relabel rotate biasedBase

local notation "uniform" => D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail.Paths.fromPath 5 D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Codes.uniformFive (by omega) D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Codes.uniform_legal

private theorem biased_law (i : Fin 5) : law biased i = if i=0 then (1/4 : ℝ) else 3/16 := by
  rw [relabel_law_equiv,D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail.Paths.path_law,D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Codes.biased_law]
  fin_cases i <;> norm_num [finRotate_symm_apply,Fin.ext_iff,Fin.sub_def]

private theorem uniform_law (i : Fin 5) : law uniform i = (1/5 : ℝ) := by
  rw [D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail.Paths.path_law,D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Codes.uniform_law]

private theorem code_bills :
    (∫⁻ t, bill biased t ∂fairTape) = ENNReal.ofReal 3 ∧
    (∫⁻ t, bill uniform t ∂fairTape) = ENNReal.ofReal (18/5) := by
  simp only [relabel_bill,D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail.Paths.path_expectation]
  exact ⟨by rw [Codes.biased_cost], by rw [Codes.uniform_cost]⟩

private theorem minMass_eq (p : Fin 5 → ℝ) (t : ℝ) (lower : ∀ i, t ≤ p i)
    (hit : ∃ i, p i=t) : minimumMass p=t := by
  obtain ⟨i,hi⟩ := hit
  exact le_antisymm ((Finset.inf'_le _ (Finset.mem_univ i)).trans_eq hi)
    (Finset.le_inf' (by simp) p (fun j _ => lower j))

private theorem code_minMass :
    minimumMass (law point) = 0 ∧
    minimumMass (law biased) = 3/16 ∧
    minimumMass (law uniform) = 1/5 := by
  refine ⟨minMass_eq _ _ (fun i => (law_simplex point).1 i) ⟨1,by simp [point_law]⟩,?_,?_⟩
  · apply minMass_eq
    · intro i; rw [biased_law]; split_ifs <;> norm_num
    · exact ⟨1,by norm_num [biased_law,Fin.ext_iff]⟩
  · exact minMass_eq _ _ (fun i => by rw [uniform_law]) ⟨0,uniform_law 0⟩

private theorem three_lines (N : ℕ) (l : ℝ) (hl : 0 ≤ l) :
    G (endpointSampler point) N l = ENNReal.ofReal (22*N) ∧
    G (endpointSampler biased) N l = ENNReal.ofReal (349*N/16+3*l) ∧
    G (endpointSampler uniform) N l = ENNReal.ofReal (109*N/5+18*l/5) := by
  have convert (t e : ℝ) (ht : 0 ≤ 22-t) (he : 0 ≤ e) :
      ENNReal.ofReal l*ENNReal.ofReal e+(N : ℝ≥0∞)*ENNReal.ofReal (22-t) =
        ENNReal.ofReal ((N : ℝ)*(22-t)+l*e) := by
    rw [ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) ht) (mul_nonneg hl he),
      ENNReal.ofReal_mul (Nat.cast_nonneg N),ENNReal.ofReal_mul hl]
    simp [add_comm]
  constructor
  · rw [endpointG_exact,point_bill]
    simp only [lintegral_zero,code_minMass.1,mul_zero,zero_add,sub_zero]
    simpa [mul_comm] using (ENNReal.ofReal_mul (Nat.cast_nonneg N) (22 : ℝ)).symm
  · constructor
    · rw [endpointG_exact,code_minMass.2.1,code_bills.1,convert (3/16) 3 (by norm_num) (by norm_num)]
      congr 1; ring
    · rw [endpointG_exact,code_minMass.2.2,code_bills.2,convert (1/5) (18/5) (by norm_num) (by norm_num)]
      congr 1; ring

private theorem phase_attainment (N : ℕ) (l : ℝ) (hl : 0 ≤ l) :
    ∃ s : PrefixSampler Strategy, Coarse s ∧ G s N l = ENNReal.ofReal (D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.sharp N l) := by
  have P := D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.phase_switches N l hl
  have L := three_lines N l hl
  by_cases low : (N : ℝ) ≤ 16*l
  · exact ⟨endpointSampler point,endpointSampler_coarse _,by rw [L.1,P.1 low]⟩
  · by_cases high : 48*l ≤ (N : ℝ)
    · exact ⟨endpointSampler uniform,endpointSampler_coarse _,by rw [L.2.2,P.2.2 high]⟩
    · exact ⟨endpointSampler biased,endpointSampler_coarse _,by rw [L.2.1,P.2.1 (by linarith) (by linarith)]⟩

private theorem gamma_exact (N : ℕ) (l : ℝ) (hl : 0 ≤ l) :
    rawGamma N l = ENNReal.ofReal (D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.sharp N l) ∧
    coarseGamma N l = ENNReal.ofReal (D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.sharp N l) := by
  obtain ⟨s,hcoarse,he⟩ := phase_attainment N l hl
  constructor
  · apply le_antisymm
    · exact (iInf_le (fun s => G s N l) s).trans_eq he
    · exact le_iInf (fun s => all_controller_lower s N l hl)
  · apply le_antisymm
    · exact (iInf_le (fun s : {s : PrefixSampler Strategy // Coarse s} => G s.val N l)
        ⟨s,hcoarse⟩).trans_eq he
    · exact le_iInf (fun s => all_controller_lower s.val N l hl)

private theorem some_cost_22 (pi : Strategy) : ∃ i : Fin 5, 22 ≤ cost pi (prototypes i) := by
  obtain ⟨a,ha⟩ := profile_domination pi
  have distinct : ∃ i : Fin 5, a ≠ i := by
    by_cases h : a=0
    · exact ⟨1,by rw [h]; decide⟩
    · exact ⟨0,h⟩
  obtain ⟨i,hi⟩ := distinct
  exact ⟨i,by simpa [hi] using ha i⟩

private theorem all_H_lower (s : PrefixSampler Strategy) (N : ℕ) (l : ℝ) :
    ENNReal.ofReal (22*N) ≤ H s N l := by
  have point (t : Tape) : (22*N : ℝ≥0∞) ≤
      Finset.univ.sup (fun q : Tuple N => paidTuple s N l q t) := by
    obtain ⟨i,hi⟩ := some_cost_22 (selected s t)
    have bound : (22*N : ℝ≥0∞) ≤ paidTuple s N l (fun _ => i) t := by
      have sums := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
        (fun _ _ => show (22 : ℝ≥0∞) ≤ (cost (selected s t) (prototypes i) : ℝ≥0∞) by exact_mod_cast hi)
      have noBits : (∑ _ : Fin N, (cost (selected s t) (prototypes i) : ℝ≥0∞)) ≤
          paidTuple s N l (fun _ => i) t := le_add_of_nonneg_left (by positivity)
      simpa [mul_comm] using sums.trans noBits
    exact bound.trans (Finset.le_sup (s := Finset.univ)
      (f := fun q : Tuple N => paidTuple s N l q t) (Finset.mem_univ (fun _ : Fin N => i)))
  have HH := lintegral_mono (μ := fairTape)
    (f := fun _ : Tape => (22*N : ℝ≥0∞))
    (g := fun t : Tape => Finset.univ.sup (fun q : Tuple N => paidTuple s N l q t)) point
  simpa [H,lintegral_const,ENNReal.ofReal_mul] using HH

private theorem point_selected (t : Tape) : selected (endpointSampler point) t = endpoint 0 :=
  selected_emitted _ t _ ((relabel_emitted endpoint point _ t).mpr ⟨0,⟨0,rfl⟩,rfl⟩)

private theorem H_attainment (N : ℕ) (l : ℝ) : H (endpointSampler point) N l = ENNReal.ofReal (22*N) := by
  apply le_antisymm
  · have upper (t : Tape) : Finset.univ.sup (fun q : Tuple N => paidTuple (endpointSampler point) N l q t) ≤
        (22*N : ℝ≥0∞) := by
      apply Finset.sup_le
      intro q hq
      unfold paidTuple
      rw [point_selected]
      simp only [relabel_bill,point_bill,mul_zero,zero_add]
      have sums := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
        (fun r _ => show (cost (endpoint 0) (prototypes (q r)) : ℝ≥0∞) ≤ 22 by
          rw [endpoint_cost]; split_ifs <;> norm_num)
      simpa [mul_comm] using sums
    have HH := lintegral_mono (μ := fairTape)
      (f := fun t : Tape => Finset.univ.sup (fun q : Tuple N => paidTuple (endpointSampler point) N l q t))
      (g := fun _ : Tape => (22*N : ℝ≥0∞)) upper
    simpa [H,lintegral_const,ENNReal.ofReal_mul] using HH
  · exact all_H_lower _ N l

private theorem H_exact (N : ℕ) (l : ℝ) :
    rawH N l = ENNReal.ofReal (22*N) ∧ coarseH N l = ENNReal.ofReal (22*N) := by
  constructor
  · apply le_antisymm
    · exact (iInf_le (fun s => H s N l) (endpointSampler point)).trans_eq (H_attainment N l)
    · exact le_iInf (fun s => all_H_lower s N l)
  · apply le_antisymm
    · exact (iInf_le (fun s : {s : PrefixSampler Strategy // Coarse s} => H s.val N l)
        ⟨endpointSampler point,endpointSampler_coarse _⟩).trans_eq (H_attainment N l)
    · exact le_iInf (fun s => all_H_lower s.val N l)

open D5.S3.Arith.FibonacciAtomic.CarryGraphRealization

private theorem sorted4 :
    ({0,1,2,3} : Finset (Fin 5)).sort (fun i j => i≤j) = [0,1,2,3] := by
  rw [Finset.sort_insert (s := ({1,2,3}:Finset (Fin 5))) (a := 0) (fun i j => i≤j) (by decide) (by decide)]
  rw [Finset.sort_insert (s := ({2,3}:Finset (Fin 5))) (a := 1) (fun i j => i≤j) (by decide) (by decide)]
  rw [Finset.sort_insert (s := ({3}:Finset (Fin 5))) (a := 2) (fun i j => i≤j) (by decide) (by decide)]
  simp

private theorem b0 : labelSet 5 Codes.biasedFive 0 = ∅ := by
  ext i; fin_cases i <;> norm_num [labelSet,Codes.biasedFive,Fin.ext_iff]
private theorem b1 : labelSet 5 Codes.biasedFive 1 = {4} := by
  ext i; fin_cases i <;> norm_num [labelSet,Codes.biasedFive,Fin.ext_iff]
private theorem b2 : labelSet 5 Codes.biasedFive 2 = {0,1,2,3} := by
  ext i; fin_cases i <;> norm_num [labelSet,Codes.biasedFive,Fin.ext_iff]
private theorem b3 : labelSet 5 Codes.biasedFive 3 = {0,1,2,3} := by
  ext i; fin_cases i <;> norm_num [labelSet,Codes.biasedFive,Fin.ext_iff]
private theorem u0 : labelSet 5 Codes.uniformFive 0 = ∅ := by
  ext i; fin_cases i <;> norm_num [labelSet,Codes.uniformFive]
private theorem u1 : labelSet 5 Codes.uniformFive 1 = ∅ := by
  ext i; fin_cases i <;> norm_num [labelSet,Codes.uniformFive]
private theorem u2 : labelSet 5 Codes.uniformFive 2 = Finset.univ := by
  ext i; fin_cases i <;> norm_num [labelSet,Codes.uniformFive]
private theorem u3 : labelSet 5 Codes.uniformFive 3 = Finset.univ := by
  ext i; fin_cases i <;> norm_num [labelSet,Codes.uniformFive]

private theorem literal_quarter_code :
    (stopping 5 Codes.biasedFive 1).map (fun v => (v.1,rotate v.2)) =
      [([false,false],(0:Fin 5))] ∧
    (stopping 5 Codes.biasedFive 2).map (fun v => (v.1,rotate v.2)) =
      [([false,true,false],(1:Fin 5)),([false,true,true],2),
       ([true,false,false],3),([true,false,true],4)] ∧
    (stopping 5 Codes.biasedFive 3).map (fun v => (v.1,rotate v.2)) =
      [([true,true,false,false],(1:Fin 5)),([true,true,false,true],2),
       ([true,true,true,false],3),([true,true,true,true],4)] ∧
    continuing 5 Codes.biasedFive 4 = [] := by norm_num [stopping,continuing,children,b0,b1,b2,b3,u0,u1,u2,u3,sorted4,Fin.sort_univ,finRotate_apply,List.finRange,Fin.add_def,Fin.ext_iff]

private theorem literal_uniform_code :
    stopping 5 Codes.uniformFive 2 =
      [([false,false,false],(0:Fin 5)),([false,false,true],1),
       ([false,true,false],2),([false,true,true],3),([true,false,false],4)] ∧
    stopping 5 Codes.uniformFive 3 =
      [([true,false,true,false],(0:Fin 5)),([true,false,true,true],1),
       ([true,true,false,false],2),([true,true,false,true],3),
       ([true,true,true,false],4)] ∧
    continuing 5 Codes.uniformFive 4 = [[true,true,true,true]] := by norm_num [stopping,continuing,children,b0,b1,b2,b3,u0,u1,u2,u3,sorted4,Fin.sort_univ,finRotate_apply,List.finRange,Fin.add_def,Fin.ext_iff]

private theorem uniform_period (d : ℕ) :
    Codes.uniformFive.state (d+4) = Codes.uniformFive.state d ∧
    Codes.uniformFive.action (d+4) = Codes.uniformFive.action d := by
  simp [Codes.uniformFive,Nat.add_mod]

/-- Literal quarter and uniform codes, their laws and their paid bit expectations. -/
def CodeClaim : Prop :=
    (stopping 5 Codes.biasedFive 1).map (fun v => (v.1,rotate v.2)) =
      [([false,false],(0:Fin 5))] ∧
    (stopping 5 Codes.biasedFive 2).map (fun v => (v.1,rotate v.2)) =
      [([false,true,false],(1:Fin 5)),([false,true,true],2),
       ([true,false,false],3),([true,false,true],4)] ∧
    (stopping 5 Codes.biasedFive 3).map (fun v => (v.1,rotate v.2)) =
      [([true,true,false,false],(1:Fin 5)),([true,true,false,true],2),
       ([true,true,true,false],3),([true,true,true,true],4)] ∧
    continuing 5 Codes.biasedFive 4 = [] ∧
    stopping 5 Codes.uniformFive 2 =
      [([false,false,false],(0:Fin 5)),([false,false,true],1),
       ([false,true,false],2),([false,true,true],3),([true,false,false],4)] ∧
    stopping 5 Codes.uniformFive 3 =
      [([true,false,true,false],(0:Fin 5)),([true,false,true,true],1),
       ([true,true,false,false],2),([true,true,false,true],3),
       ([true,true,true,false],4)] ∧
    continuing 5 Codes.uniformFive 4 = [[true,true,true,true]] ∧
    (∀ d, Codes.uniformFive.state (d+4) = Codes.uniformFive.state d ∧
      Codes.uniformFive.action (d+4) = Codes.uniformFive.action d) ∧
    (∀ i, law biased i = if i=0 then (1/4 : ℝ) else 3/16) ∧
    (∀ i, law uniform i = (1/5 : ℝ)) ∧
    (∫⁻ t, bill biased t ∂fairTape) = ENNReal.ofReal 3 ∧
    (∫⁻ t, bill uniform t ∂fairTape) = ENNReal.ofReal (18/5)

private theorem codes_exact : CodeClaim :=
  ⟨literal_quarter_code.1, literal_quarter_code.2.1,
    literal_quarter_code.2.2.1, literal_quarter_code.2.2.2,
    literal_uniform_code.1, literal_uniform_code.2.1, literal_uniform_code.2.2,
    uniform_period, biased_law, uniform_law, code_bills.1, code_bills.2⟩

/-- Exact all-sampler/controller target. No conclusion is included among its assumptions. -/
def Claim : Prop := CodeClaim ∧ ∀ N : ℕ, 1 ≤ N → ∀ l : ℝ, 0 < l →
  rawGamma N l = ENNReal.ofReal (D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.sharp N l) ∧
  coarseGamma N l = ENNReal.ofReal (D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.sharp N l) ∧
  (∃ s : PrefixSampler Strategy, Coarse s ∧ G s N l = ENNReal.ofReal (D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.sharp N l)) ∧
  (N ≤ 16*l → rawGamma N l = ENNReal.ofReal (22*N)) ∧
  (16*l ≤ N → N ≤ 48*l → rawGamma N l = ENNReal.ofReal (349*N/16+3*l)) ∧
  (48*l ≤ N → rawGamma N l = ENNReal.ofReal (109*N/5+18*l/5)) ∧
  rawH N l = ENNReal.ofReal (22*N) ∧
  coarseH N l = ENNReal.ofReal (22*N) ∧
  (∃ s : PrefixSampler Strategy, Coarse s ∧ H s N l = ENNReal.ofReal (22*N))

/-- The sharp raw and coarse five-tree contracts, with literal attaining codes. -/
theorem result : Claim := by
  refine ⟨codes_exact, ?_⟩
  intro N hN l hl
  have gamma := gamma_exact N l hl.le
  have phases := D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase.Phase.phase_switches N l hl.le
  exact ⟨gamma.1,gamma.2,phase_attainment N l hl.le,
    fun h => by rw [gamma.1,phases.1 h],
    fun h1 h2 => by rw [gamma.1,phases.2.1 h1 h2],
    fun h => by rw [gamma.1,phases.2.2 h],
    (H_exact N l).1,(H_exact N l).2,
    ⟨endpointSampler point,endpointSampler_coarse _,H_attainment N l⟩⟩

end D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxFiveBatchPhase
