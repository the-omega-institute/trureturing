/- GID: D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxThreeBatchPhase
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxThreeBatchPhase
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: All fair-prefix total controllers have the sharp three-tree batch phase. -/

import D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail
import D5.S3.Arith.FibonacciAtomic.Scale36ActualEndpointAcquisition
import D5.S3.Arith.FibonacciAtomic.Scale38NestedCompensation

set_option autoImplicit false
set_option maxHeartbeats 500000
local notation "minimumMass" => (fun p : Fin 3 → ℝ => Finset.univ.inf' (by simp) p)

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase.Codes
open scoped BigOperators ENNReal Classical
open MeasureTheory
open D5.S3.Arith.FibonacciAtomic.CarryGraphEmbedding
open D5.S3.Arith.FibonacciAtomic.CarryGraphRealization
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)

def biasedThree : Path :=
  ⟨fun d => if d = 0 then ⟨1,3⟩ else if d = 1 then ⟨1,2⟩ else ⟨0,2⟩,
   fun d => if d = 0 then ⟨0,1,0⟩ else if d = 1 then ⟨1,0,0⟩ else ⟨0,0,0⟩⟩

def uniformThree : Path :=
  ⟨fun d => ⟨if d % 2 = 0 then 1 else 2, 3⟩,
   fun d => ⟨if d % 2 = 0 then 0 else 1, 0, 0⟩⟩

private theorem biased_legal : IsRootPath 3 biasedThree := by
  constructor
  · rfl
  · intro d
    rcases d with _ | _ | d <;>
      norm_num [biasedThree, IsState, Legal, successor, ones]

private theorem uniform_legal : IsRootPath 3 uniformThree := by
  constructor
  · rfl
  · intro d
    by_cases hd : d % 2 = 0
    · have hn : (d + 1) % 2 ≠ 0 := by omega
      norm_num [uniformThree, IsState, Legal, successor, ones,hd,hn]
    · have hn : (d + 1) % 2 = 0 := by omega
      norm_num [uniformThree, IsState, Legal, successor, ones,hd,hn]

private theorem biased_cost : pathCost biasedThree = 3/2 := by
  unfold pathCost
  have support : (fun d : ℕ => ((biasedThree.state d).r : ℝ) / (2 : ℝ)^d) =
      (fun d => if d = 0 then (1 : ℝ) else if d = 1 then 1/2 else 0) := by
    funext d
    rcases d with _ | _ | d <;> norm_num [biasedThree]
  rw [support, tsum_eq_sum (s := ({0,1} : Finset ℕ)) (fun d hd => by
    have hn : d ≠ 0 ∧ d ≠ 1 := by simpa using hd
    simp [hn.1,hn.2])]
  norm_num

private theorem biased_law (i : Fin 3) :
    Real.ofDigits (labelDigit biasedThree i) = if i = 2 then (1/2 : ℝ) else 1/4 := by
  have dig : labelDigit biasedThree i = fun d =>
      if d = 0 then (if i = 2 then (1 : Fin 2) else 0) else
        if d = 1 then (if i = 2 then 0 else 1) else 0 := by
    funext d
    fin_cases i <;> rcases d with _ | _ | d <;>
      norm_num [labelDigit, labelSet, biasedThree, Fin.ext_iff]
  rw [dig, Real.ofDigits_eq_sum_add_ofDigits _ 2]
  have tail : (fun d => (if d+2 = 0 then (if i = 2 then (1 : Fin 2) else 0) else
      if d+2 = 1 then (if i = 2 then 0 else 1) else 0)) = (fun _ => (0 : Fin 2)) := by
    funext d; simp
  rw [tail]
  have zero : Real.ofDigits (fun _ => (0 : Fin 2)) = 0 := by
    simp [Real.ofDigits,Real.ofDigitsTerm]
  rw [zero]
  fin_cases i <;> norm_num [Finset.sum_range_succ,Real.ofDigitsTerm,Fin.ext_iff]

private theorem uniform_law (i : Fin 3) : Real.ofDigits (labelDigit uniformThree i) = (1/3 : ℝ) := by
  have same (i j : Fin 3) : labelDigit uniformThree i = labelDigit uniformThree j := by
    funext d
    have hi : (i.val : ℤ) < 3 := by exact_mod_cast i.isLt
    have hj : (j.val : ℤ) < 3 := by exact_mod_cast j.isLt
    by_cases hd : d%2=0 <;> simp [labelDigit,labelSet,uniformThree,hd,hi,hj,not_le_of_gt hi,not_le_of_gt hj,
      Nat.not_le_of_lt i.isLt,Nat.not_le_of_lt j.isLt]
  have H := (D5.S3.Arith.FibonacciAtomic.CarryGraphRealization.result 3 (by omega)
    uniformThree uniform_legal).2.1
  have equal (j : Fin 3) : Real.ofDigits (labelDigit uniformThree j) =
      Real.ofDigits (labelDigit uniformThree i) := congrArg Real.ofDigits (same j i)
  simp_rw [equal] at H
  norm_num at H
  linarith

private theorem uniform_cost : pathCost uniformThree = 8/3 := by
  let f := fun d : ℕ => ((uniformThree.state d).r : ℝ) / (2 : ℝ)^d
  have hn (d : ℕ) : 0 ≤ f d := by dsimp [f,uniformThree]; split_ifs <;> positivity
  have upper (d : ℕ) : f d ≤ 2*(1/2 : ℝ)^d := by
    have H : (((uniformThree.state d).r : ℤ) : ℝ) ≤ 2 := by
      dsimp [uniformThree]; split_ifs <;> norm_num
    simpa [f,div_eq_mul_inv,inv_pow] using
      div_le_div_of_nonneg_right H (by positivity : (0 : ℝ)≤2^d)
  have summable : Summable f := Summable.of_nonneg_of_le hn upper
    ((summable_geometric_of_abs_lt_one (r := (1/2 : ℝ)) (by norm_num)).mul_left 2)
  have shift (d : ℕ) : f (d+2) = f d /4 := by
    dsimp [f,uniformThree]
    simp only [Nat.add_mod, Nat.add_zero, Nat.mod_self, Nat.mod_mod, Int.cast_ite, pow_add]
    split_ifs <;> push_cast <;> field_simp <;> ring
  have H := summable.sum_add_tsum_nat_add 2
  simp_rw [shift] at H
  rw [tsum_div_const] at H
  have head : ∑ d ∈ Finset.range 2, f d = 2 := by
    norm_num [f,uniformThree,Finset.sum_range_succ]
  rw [head] at H
  change pathCost uniformThree = 8/3
  change (∑' d, f d) = 8/3
  linarith only [H]

end D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase.Codes

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase.Phase
open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic

def sharp (N l : ℝ) : ℝ := min (17*N) (min (67*N/4+3*l/2) (50*N/3+8*l/3))

private theorem support (p : Fin 3 → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    0 ≤ minimumMass p ∧ minimumMass p ≤ 1/3 ∧
      6*minimumMass p ≤ DyadicSupportLines.cost p ∧
      14*minimumMass p-2 ≤ DyadicSupportLines.cost p := by
  have H := MersenneDyadicSupportLines.mersenne_support_lines 2 (by omega) p hp hs
  norm_num only [Nat.reducePow, Nat.reduceSub, Nat.cast_ofNat] at H
  dsimp only
  exact ⟨H.2.1,H.2.2.1,by norm_num at H ⊢; exact H.2.2.2.1,
    by norm_num at H ⊢; exact H.2.2.2.2⟩

private theorem affine_lower (N l t e : ℝ) (hl : 0 ≤ l) (ht0 : 0 ≤ t) (ht3 : t ≤ 1/3)
    (h6 : 6*t ≤ e) (h14 : 14*t-2 ≤ e) :
    sharp N l ≤ 17*N-N*t+l*e := by
  unfold sharp
  by_cases low : N ≤ 6*l
  · apply le_trans (min_le_left _ _)
    have H1 := mul_nonneg hl (sub_nonneg.mpr h6)
    have H2 := mul_nonneg (sub_nonneg.mpr low) ht0
    nlinarith only [H1,H2]
  · by_cases high : 14*l ≤ N
    · apply le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
      have H1 := mul_nonneg hl (sub_nonneg.mpr h14)
      have H2 := mul_nonneg (sub_nonneg.mpr high) (sub_nonneg.mpr ht3)
      nlinarith only [H1,H2]
    · apply le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
      by_cases small : t ≤ 1/4
      · have H1 := mul_nonneg hl (sub_nonneg.mpr h6)
        have H2 := mul_nonneg (by linarith : 0 ≤ N-6*l) (sub_nonneg.mpr small)
        nlinarith only [H1,H2]
      · have H1 := mul_nonneg hl (sub_nonneg.mpr h14)
        have H2 := mul_nonneg (by linarith : 0 ≤ 14*l-N) (by linarith : 0 ≤ t-1/4)
        nlinarith only [H1,H2]

private theorem phase_switches (N l : ℝ) (hl : 0 ≤ l) :
    (N ≤ 6*l → sharp N l = 17*N) ∧
    (6*l ≤ N → N ≤ 14*l → sharp N l = 67*N/4+3*l/2) ∧
    (14*l ≤ N → sharp N l = 50*N/3+8*l/3) := by
  unfold sharp
  constructor
  · intro H
    rw [min_eq_left (le_min (by linarith) (by linarith))]
  · constructor
    · intro H1 H2
      rw [min_eq_left (show 67*N/4+3*l/2 ≤ 50*N/3+8*l/3 by linarith),
        min_eq_right (show 67*N/4+3*l/2 ≤ 17*N by linarith)]
    · intro H
      rw [min_eq_right (show 50*N/3+8*l/3 ≤ 67*N/4+3*l/2 by linarith),
        min_eq_right (show 50*N/3+8*l/3 ≤ 17*N by linarith)]

end D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase.Phase

set_option autoImplicit false
namespace D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase
open scoped BigOperators ENNReal Classical
open MeasureTheory
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition
open D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation (Nonconflict)
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory (kappa_hist)
open D5.S3.Arith.FibonacciAtomic
open D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail

def row3 (i : Fin 3) : Unit ⊕ (Fin 1 × Fin 2) :=
  if i.val = 0 then .inl () else if i.val = 1 then .inr (0,0) else .inr (0,1)

local notation "prototypes" => (fun i : Fin 3 => Scale36ActualEndpointAcquisition.family 1 (row3 i))

def selected (s : PrefixSampler Strategy) (t : Tape) : Strategy :=
  if h : ∃ pi, t ∈ emitted s pi then Classical.choose h else fallback

def Coarse (s : PrefixSampler Strategy) : Prop :=
  ∀ d w pi, s.observe d w = some pi → Function.FactorsThrough pi.policy kappa_hist

local notation "Tuple" N => (Fin N → Fin 3)

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
open ActualTreeReadoutAcquisition
open ActualJointResponseCostCore

private theorem row3_injective : Function.Injective row3 := by decide

private theorem prototype_facts : Function.Injective prototypes ∧
    (∀ i, Positive (prototypes i) ∧ (leaves (prototypes i)).length = 16) ∧
    ∀ i j, Nonconflict (prototypes i) (prototypes j) := by
  have S := Scale36ActualEndpointAcquisition.family_structure 1 (by omega)
  refine ⟨S.1.comp row3_injective, ?_,fun i j => S.2.2 _ _⟩
  intro i
  refine ⟨(S.2.1 _).2.1, ?_⟩
  fin_cases i <;> rfl


/-- Restricting the evaluated family admits a recipe with no greater excess. -/
theorem restrict_recipe {m : ℕ} {F : Fin m → Source} {S : Finset (Fin m)}
    (r : Recipe F S) : ∀ (T : Finset (Fin m)), T ⊆ S → T.Nonempty →
      ∃ q : Recipe F T, ∀ i ∈ T, gain q i ≤ gain r i := by
  classical
  induction r with
  | singleton a =>
    intro T hT hn
    have eqn : T = {a} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨by obtain ⟨i,hi⟩ := hn; have he := Finset.mem_singleton.mp (hT hi); simpa [he] using hi,
        fun i hi => Finset.mem_singleton.mp (hT hi)⟩
    subst T
    exact ⟨.singleton a,fun i hi => le_rfl⟩
  | split S a hs next ih =>
    intro T hT hn
    have child_subset (y : Reply) : survivors T a.val y ⊆ survivors S a.val y := by
      intro i hi
      simp only [survivors,Finset.mem_filter] at hi ⊢
      exact ⟨hT hi.1,hi.2⟩
    by_cases splits : 2 ≤ (T.image a.val).card
    · let children (y : Reply) (hy : (survivors T a.val y).Nonempty) :
          Recipe F (survivors T a.val y) := Classical.choose
            (ih y (hy.mono (child_subset y)) _ (child_subset y) hy)
      refine ⟨.split T a splits children,?_⟩
      intro i hi
      have hy : (survivors T a.val (a.val i)).Nonempty := ⟨i,by simp [survivors,hi]⟩
      have hbound := Classical.choose_spec
        (ih (a.val i) (hy.mono (child_subset _)) _ (child_subset _) hy) i
          (by simp [survivors,hi])
      simpa only [gain, dif_pos hi, dif_pos (hT hi),children] using
        Nat.add_le_add_left hbound (chi (a.val i))
    · obtain ⟨i0,hi0⟩ := hn
      have hn : T.Nonempty := ⟨i0,hi0⟩
      have card : (T.image a.val).card ≤ 1 := by omega
      have same (i : Fin m) (hi : i ∈ T) : a.val i = a.val i0 :=
        Finset.card_le_one.mp card _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
          _ (Finset.mem_image.mpr ⟨i0,hi0,rfl⟩)
      have hchild : T ⊆ survivors S a.val (a.val i0) := by
        intro i hi
        simp only [survivors,Finset.mem_filter]
        exact ⟨hT hi,same i hi⟩
      obtain ⟨q,hq⟩ := ih (a.val i0) (hn.mono hchild) T hchild hn
      refine ⟨q,?_⟩
      intro i hi
      have lower := hq i hi
      have transport (u v : Reply) (hu : (survivors S a.val u).Nonempty)
          (hv : (survivors S a.val v).Nonempty) (he : u = v) :
          gain (next u hu) i = gain (next v hv) i := by
        subst v
        rfl
      have child_same : gain (next (a.val i0) (hn.mono hchild)) i =
          gain (next (a.val i) ⟨i,by simp [survivors,hT hi]⟩) i := by
        exact transport _ _ _ _ (same i hi).symm
      rw [child_same] at lower
      exact lower.trans (by simp only [gain,dif_pos (hT hi)]; omega)


/-- In a nonconflicting family, a recipe has at most one zero-excess member. -/
theorem zero_gain_unique {m : ℕ} (F : Fin m → Source)
    (nc : ∀ i j, Nonconflict (F i) (F j)) {S : Finset (Fin m)}
    (r : Recipe F S) (i j : Fin m) (hi : i ∈ S) (hj : j ∈ S)
    (hgi : gain r i = 0) (hgj : gain r j = 0) : i = j := by
  by_contra different
  have card : 2 ≤ ({i,j} : Finset (Fin m)).card := by simp [different]
  obtain ⟨q,hq⟩ := restrict_recipe r {i,j} (by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · simpa [hx] using hi
    · simpa [Finset.mem_singleton.mp hx] using hj) (by simp)
  obtain ⟨x,hx,hgain⟩ := Scale38NestedCompensation.root_excess F nc {i,j} q card
  have bound := hq x hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · subst x; omega
  · have hx' := Finset.mem_singleton.mp hx; subst x; omega

private theorem profile_domination (pi : Strategy) :
    ∃ a : Fin 3, ∀ i, 17-(if a=i then 1 else 0) ≤ cost pi (prototypes i) := by
  have core := ActualJointResponseCostCore.result 3 (by omega) prototypes
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
          exact same (zero_gain_unique prototypes prototype_facts.2.2 r a i
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

private theorem actual_endpoints (a : Fin 3) : ∃ pi : Strategy,
    Function.FactorsThrough pi.policy kappa_hist ∧
      ∀ i, cost pi (prototypes i) = 17-(if a=i then 1 else 0) := by
  have S := Scale36ActualEndpointAcquisition.result 1 (by omega)
  obtain ⟨pi,hcoarse,hcost⟩ := S.2.2.2.2 (row3 a)
  refine ⟨pi,hcoarse,fun i => ?_⟩
  have H := (hcost (row3 i)).2
  simpa only [Nat.reduceMul,Nat.reduceAdd,row3_injective.eq_iff] using H

def endpointIndex (pi : Strategy) : Fin 3 := Classical.choose (profile_domination pi)

local notation "labelSampler" => (fun s : PrefixSampler Strategy => relabel endpointIndex s)

private theorem endpointIndex_bound (pi : Strategy) (i : Fin 3) :
    17-(if endpointIndex pi=i then 1 else 0) ≤ cost pi (prototypes i) :=
  Classical.choose_spec (profile_domination pi) i

theorem selected_emitted (s : PrefixSampler Strategy) (t : Tape) (pi : Strategy)
    (hpi : t ∈ emitted s pi) : selected s t = pi := by
  have hs : ∃ pi, t ∈ emitted s pi := ⟨pi,hpi⟩
  simp only [selected,dif_pos hs]
  have hchoose := Classical.choose_spec hs
  by_contra hn
  exact Set.disjoint_left.mp (emitted_disjoint s hn) hchoose hpi

def profileCost (a i : Fin 3) : ℝ≥0∞ := ((17-(if a=i then 1 else 0) : ℕ) : ℝ≥0∞)

def profileRead (s : PrefixSampler (Fin 3)) (i : Fin 3) (t : Tape) : ℝ≥0∞ :=
  ∑ a : Fin 3, (emitted s a).indicator (fun _ => profileCost a i) t

private theorem profileRead_le (s : PrefixSampler Strategy) (i : Fin 3) :
    profileRead (labelSampler s) i ≤ᵐ[fairTape]
      (fun t => (cost (selected s t) (prototypes i) : ℝ≥0∞)) := by
  filter_upwards [s.terminates] with t ht
  obtain ⟨d,pi,hpi⟩ := ht
  have hem : t ∈ emitted s pi := ⟨d,hpi⟩
  have hm : t ∈ emitted (labelSampler s) (endpointIndex pi) :=
    (relabel_emitted endpointIndex s _ t).mpr ⟨pi,hem,rfl⟩
  have other (a : Fin 3) (ha : a ≠ endpointIndex pi) :
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

private theorem profileRead_measurable (s : PrefixSampler (Fin 3)) (i : Fin 3) :
    Measurable (profileRead s i) := Finset.measurable_sum _
  (fun a _ => measurable_const.indicator (emitted_measurable s a))

private theorem profile_expectation (s : PrefixSampler (Fin 3)) (i : Fin 3) :
    (∫⁻ t, profileRead s i t ∂fairTape) = ENNReal.ofReal (17-law s i) := by
  unfold profileRead
  rw [lintegral_finsetSum Finset.univ (fun a _ => measurable_const.indicator (emitted_measurable s a))]
  simp_rw [lintegral_indicator_const (emitted_measurable s _)]
  have mass (a : Fin 3) : fairTape (emitted s a) = ENNReal.ofReal (law s a) :=
    (ENNReal.ofReal_toReal (measure_ne_top fairTape _)).symm
  have scale (a : Fin 3) : profileCost a i * fairTape (emitted s a) =
      ENNReal.ofReal ((17-(if a=i then (1 : ℝ) else 0))*law s a) := by
    rw [mass,ENNReal.ofReal_mul (by split_ifs <;> norm_num)]
    unfold profileCost
    split_ifs <;> norm_num
  simp_rw [scale]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg
    (by split_ifs <;> norm_num) ((law_simplex s).1 a))]
  have eqn : (∑ a : Fin 3, (17-(if a=i then (1 : ℝ) else 0))*law s a) = 17-law s i := by
    simp only [sub_mul,ite_mul,one_mul,zero_mul,Finset.sum_sub_distrib,
      ← Finset.mul_sum,(law_simplex s).2,Finset.sum_ite_eq',Finset.mem_univ,
      if_pos, mul_one]
  rw [eqn]

private theorem fixed_tuple_lower (s : PrefixSampler Strategy) (N : ℕ) (l : ℝ) (i : Fin 3) :
    ENNReal.ofReal l * (∫⁻ t, bill s t ∂fairTape) +
      (N : ℝ≥0∞)*ENNReal.ofReal (17-law (labelSampler s) i) ≤ G s N l := by
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
    ENNReal.ofReal (Phase.sharp N l) ≤ G s N l := by
  let p := law (labelSampler s)
  let t := minimumMass p
  have hp := law_simplex (labelSampler s)
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' (by simp : (Finset.univ : Finset (Fin 3)).Nonempty) p
  have ht : t = p i := he
  have H := MersenneDyadicSupportLines.mersenne_support_lines 2 (by omega) p hp.1 hp.2
  norm_num only [Nat.reducePow,Nat.reduceSub,Nat.cast_ofNat] at H
  have costpos : 0 ≤ DyadicSupportLines.cost p :=
    (MersenneDyadicSupportLines.simplex_data 2 p hp.2).2.2
  have ht17 : 0 ≤ 17-t := by have hh := (Phase.support p hp.1 hp.2).2.1; dsimp [t]; linarith
  have real_lower := Phase.affine_lower N l t (DyadicSupportLines.cost p) hl
    (Phase.support p hp.1 hp.2).1 (Phase.support p hp.1 hp.2).2.1
    (Phase.support p hp.1 hp.2).2.2.1 (Phase.support p hp.1 hp.2).2.2.2
  have paid := ddg_lower (labelSampler s) H.1
  simp only [relabel_bill] at paid
  calc
    ENNReal.ofReal (Phase.sharp N l) ≤
        ENNReal.ofReal ((N : ℝ)*(17-t)+l*DyadicSupportLines.cost p) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith only [real_lower]
    _ = ENNReal.ofReal l*ENNReal.ofReal (DyadicSupportLines.cost p) +
        (N : ℝ≥0∞)*ENNReal.ofReal (17-t) := by
      rw [ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) ht17) (mul_nonneg hl costpos),
        ENNReal.ofReal_mul (Nat.cast_nonneg N),ENNReal.ofReal_mul hl]
      simp [add_comm]
    _ ≤ ENNReal.ofReal l*(∫⁻ x, bill s x ∂fairTape)+(N : ℝ≥0∞)*ENNReal.ofReal (17-t) := by
      have mult : ENNReal.ofReal l*ENNReal.ofReal (DyadicSupportLines.cost p) ≤
          ENNReal.ofReal l*(∫⁻ x, bill s x ∂fairTape) := by
        gcongr
      exact add_le_add mult le_rfl
    _ ≤ G s N l := by simpa only [ht,p] using fixed_tuple_lower s N l i

def endpoint (a : Fin 3) : Strategy := Classical.choose (actual_endpoints a)

private theorem endpoint_coarse (a : Fin 3) : Function.FactorsThrough (endpoint a).policy kappa_hist :=
  (Classical.choose_spec (actual_endpoints a)).1

private theorem endpoint_cost (a i : Fin 3) : cost (endpoint a) (prototypes i) =
    17-(if a=i then 1 else 0) := (Classical.choose_spec (actual_endpoints a)).2 i

local notation "endpointSampler" => (fun s : PrefixSampler (Fin 3) => relabel endpoint s)

private theorem endpointSampler_coarse (s : PrefixSampler (Fin 3)) : Coarse (endpointSampler s) := by
  intro d w pi hpi
  obtain ⟨a,_,ha⟩ := Option.map_eq_some_iff.mp hpi
  rw [← ha]
  exact endpoint_coarse a

private theorem profileRead_single (s : PrefixSampler (Fin 3)) (i a : Fin 3) (t : Tape)
    (ha : t ∈ emitted s a) : profileRead s i t = profileCost a i := by
  unfold profileRead
  rw [Finset.sum_eq_single a]
  · exact Set.indicator_of_mem ha _
  · intro b hb hba
    have hno : t ∉ emitted s b := fun h =>
      Set.disjoint_left.mp (emitted_disjoint s hba) h ha
    exact Set.indicator_of_notMem hno _
  · simp

private theorem endpointTuple_expectation (s : PrefixSampler (Fin 3)) (N : ℕ) (l : ℝ) (q : Tuple N) :
    (∫⁻ t, paidTuple (endpointSampler s) N l q t ∂fairTape) =
      ENNReal.ofReal l*(∫⁻ t, bill s t ∂fairTape)+
        ∑ r : Fin N, ENNReal.ofReal (17-law s (q r)) := by
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

private theorem endpointG_exact (s : PrefixSampler (Fin 3)) (N : ℕ) (l : ℝ) :
    G (endpointSampler s) N l = ENNReal.ofReal l*(∫⁻ t, bill s t ∂fairTape)+
      (N : ℝ≥0∞)*ENNReal.ofReal (17-minimumMass (law s)) := by
  let t := minimumMass (law s)
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' (by simp : (Finset.univ : Finset (Fin 3)).Nonempty) (law s)
  have ht : t=law s i := he
  apply le_antisymm
  · unfold G
    apply Finset.sup_le
    intro q hq
    rw [endpointTuple_expectation]
    have term (r : Fin N) : ENNReal.ofReal (17-law s (q r)) ≤ ENNReal.ofReal (17-t) := by
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
    change ENNReal.ofReal l*(∫⁻ t, bill s t ∂fairTape)+(N : ℝ≥0∞)*ENNReal.ofReal (17-t) ≤ _
    simpa [G,ht] using H

def point : PrefixSampler (Fin 3) where
  observe _ _ := some 0
  persistent _ _ _ _ i h := h
  terminates := Filter.Eventually.of_forall (fun _ => ⟨0,0,rfl⟩)

private theorem point_bill : bill point = (fun _ => 0) := by
  funext t
  simp [bill,active,point]

private theorem point_law (i : Fin 3) : law point i = if i=0 then 1 else 0 := by
  have evt : emitted point i = if i=0 then Set.univ else ∅ := by
    ext t
    by_cases h : i=0 <;> simp [emitted,point,h,eq_comm]
  unfold law
  rw [evt]
  split_ifs <;> simp

local notation "biasedBase" => Paths.fromPath 3 Codes.biasedThree (by omega) Codes.biased_legal
local notation "rotate" => finRotate 3
local notation "biased" => relabel rotate biasedBase

local notation "uniform" => Paths.fromPath 3 Codes.uniformThree (by omega) Codes.uniform_legal

private theorem biased_law (i : Fin 3) : law biased i = if i=0 then (1/2 : ℝ) else 1/4 := by
  rw [relabel_law_equiv,Paths.path_law,Codes.biased_law]
  fin_cases i <;> norm_num [finRotate_symm_apply,Fin.ext_iff,Fin.sub_def]

private theorem uniform_law (i : Fin 3) : law uniform i = (1/3 : ℝ) := by
  rw [Paths.path_law,Codes.uniform_law]

private theorem code_bills :
    (∫⁻ t, bill biased t ∂fairTape) = ENNReal.ofReal (3/2) ∧
    (∫⁻ t, bill uniform t ∂fairTape) = ENNReal.ofReal (8/3) := by
  constructor
  · rw [relabel_bill, Paths.path_expectation, Codes.biased_cost]
  · rw [Paths.path_expectation, Codes.uniform_cost]

private theorem minMass_eq (p : Fin 3 → ℝ) (t : ℝ) (lower : ∀ i, t ≤ p i)
    (hit : ∃ i, p i=t) : minimumMass p=t := by
  obtain ⟨i,hi⟩ := hit
  exact le_antisymm ((Finset.inf'_le _ (Finset.mem_univ i)).trans_eq hi)
    (Finset.le_inf' (by simp) p (fun j _ => lower j))

private theorem code_minMass :
    minimumMass (law point) = 0 ∧
    minimumMass (law biased) = 1/4 ∧
    minimumMass (law uniform) = 1/3 := by
  refine ⟨minMass_eq _ _ (fun i => (law_simplex point).1 i) ⟨1,by simp [point_law]⟩,?_,?_⟩
  · apply minMass_eq
    · intro i; rw [biased_law]; split_ifs <;> norm_num
    · exact ⟨1,by norm_num [biased_law,Fin.ext_iff]⟩
  · exact minMass_eq _ _ (fun i => by rw [uniform_law]) ⟨0,uniform_law 0⟩

private theorem three_lines (N : ℕ) (l : ℝ) (hl : 0 ≤ l) :
    G (endpointSampler point) N l = ENNReal.ofReal (17*N) ∧
    G (endpointSampler biased) N l = ENNReal.ofReal (67*N/4+3*l/2) ∧
    G (endpointSampler uniform) N l = ENNReal.ofReal (50*N/3+8*l/3) := by
  have convert (t e : ℝ) (ht : 0 ≤ 17-t) (he : 0 ≤ e) :
      ENNReal.ofReal l*ENNReal.ofReal e+(N : ℝ≥0∞)*ENNReal.ofReal (17-t) =
        ENNReal.ofReal ((N : ℝ)*(17-t)+l*e) := by
    rw [ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) ht) (mul_nonneg hl he),
      ENNReal.ofReal_mul (Nat.cast_nonneg N),ENNReal.ofReal_mul hl]
    simp [add_comm]
  constructor
  · rw [endpointG_exact,point_bill]
    simp only [lintegral_zero,code_minMass.1,mul_zero,zero_add,sub_zero]
    simpa [mul_comm] using (ENNReal.ofReal_mul (Nat.cast_nonneg N) (17 : ℝ)).symm
  · constructor
    · rw [endpointG_exact,code_minMass.2.1,code_bills.1,convert (1/4) (3/2) (by norm_num) (by norm_num)]
      congr 1; ring
    · rw [endpointG_exact,code_minMass.2.2,code_bills.2,convert (1/3) (8/3) (by norm_num) (by norm_num)]
      congr 1; ring

private theorem phase_attainment (N : ℕ) (l : ℝ) (hl : 0 ≤ l) :
    ∃ s : PrefixSampler Strategy, Coarse s ∧ G s N l = ENNReal.ofReal (Phase.sharp N l) := by
  have P := Phase.phase_switches N l hl
  have L := three_lines N l hl
  by_cases low : (N : ℝ) ≤ 6*l
  · exact ⟨endpointSampler point,endpointSampler_coarse _,by rw [L.1,P.1 low]⟩
  · by_cases high : 14*l ≤ (N : ℝ)
    · exact ⟨endpointSampler uniform,endpointSampler_coarse _,by rw [L.2.2,P.2.2 high]⟩
    · exact ⟨endpointSampler biased,endpointSampler_coarse _,by rw [L.2.1,P.2.1 (by linarith) (by linarith)]⟩

private theorem gamma_exact (N : ℕ) (l : ℝ) (hl : 0 ≤ l) :
    rawGamma N l = ENNReal.ofReal (Phase.sharp N l) ∧
    coarseGamma N l = ENNReal.ofReal (Phase.sharp N l) := by
  obtain ⟨s,hcoarse,he⟩ := phase_attainment N l hl
  constructor
  · apply le_antisymm
    · exact (iInf_le (fun s => G s N l) s).trans_eq he
    · exact le_iInf (fun s => all_controller_lower s N l hl)
  · apply le_antisymm
    · exact (iInf_le (fun s : {s : PrefixSampler Strategy // Coarse s} => G s.val N l)
        ⟨s,hcoarse⟩).trans_eq he
    · exact le_iInf (fun s => all_controller_lower s.val N l hl)

private theorem some_cost_17 (pi : Strategy) : ∃ i : Fin 3, 17 ≤ cost pi (prototypes i) := by
  have core := ActualJointResponseCostCore.result 3 (by omega) prototypes
    (fun i => (prototype_facts.2.1 i).1) prototype_facts.1
  obtain ⟨v,hv,dom⟩ := core.2.2.2.1 pi
  obtain ⟨r,hr⟩ := hv
  obtain ⟨i,_,hgain⟩ := Scale38NestedCompensation.root_excess prototypes
    prototype_facts.2.2 Finset.univ r (by simp)
  refine ⟨i,?_⟩
  have bound := dom i
  rw [hr i,(prototype_facts.2.1 i).2] at bound
  dsimp only at bound ⊢
  omega

private theorem all_H_lower (s : PrefixSampler Strategy) (N : ℕ) (l : ℝ) :
    ENNReal.ofReal (17*N) ≤ H s N l := by
  have point (t : Tape) : (17*N : ℝ≥0∞) ≤
      Finset.univ.sup (fun q : Tuple N => paidTuple s N l q t) := by
    obtain ⟨i,hi⟩ := some_cost_17 (selected s t)
    have bound : (17*N : ℝ≥0∞) ≤ paidTuple s N l (fun _ => i) t := by
      have sums := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
        (fun _ _ => show (17 : ℝ≥0∞) ≤ (cost (selected s t) (prototypes i) : ℝ≥0∞) by exact_mod_cast hi)
      have noBits : (∑ _ : Fin N, (cost (selected s t) (prototypes i) : ℝ≥0∞)) ≤
          paidTuple s N l (fun _ => i) t := le_add_of_nonneg_left (by positivity)
      simpa [mul_comm] using sums.trans noBits
    exact bound.trans (Finset.le_sup (s := Finset.univ)
      (f := fun q : Tuple N => paidTuple s N l q t) (Finset.mem_univ (fun _ : Fin N => i)))
  have HH := lintegral_mono (μ := fairTape)
    (f := fun _ : Tape => (17*N : ℝ≥0∞))
    (g := fun t : Tape => Finset.univ.sup (fun q : Tuple N => paidTuple s N l q t)) point
  simpa [H,lintegral_const,ENNReal.ofReal_mul] using HH

private theorem point_selected (t : Tape) : selected (endpointSampler point) t = endpoint 0 :=
  selected_emitted _ t _ ((relabel_emitted endpoint point _ t).mpr ⟨0,⟨0,rfl⟩,rfl⟩)

private theorem H_attainment (N : ℕ) (l : ℝ) : H (endpointSampler point) N l = ENNReal.ofReal (17*N) := by
  apply le_antisymm
  · have upper (t : Tape) : Finset.univ.sup (fun q : Tuple N => paidTuple (endpointSampler point) N l q t) ≤
        (17*N : ℝ≥0∞) := by
      apply Finset.sup_le
      intro q hq
      unfold paidTuple
      rw [point_selected]
      simp only [relabel_bill,point_bill,mul_zero,zero_add]
      have sums := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
        (fun r _ => show (cost (endpoint 0) (prototypes (q r)) : ℝ≥0∞) ≤ 17 by
          rw [endpoint_cost]; split_ifs <;> norm_num)
      simpa [mul_comm] using sums
    have HH := lintegral_mono (μ := fairTape)
      (f := fun t : Tape => Finset.univ.sup (fun q : Tuple N => paidTuple (endpointSampler point) N l q t))
      (g := fun _ : Tape => (17*N : ℝ≥0∞)) upper
    simpa [H,lintegral_const,ENNReal.ofReal_mul] using HH
  · exact all_H_lower _ N l

private theorem H_exact (N : ℕ) (l : ℝ) :
    rawH N l = ENNReal.ofReal (17*N) ∧ coarseH N l = ENNReal.ofReal (17*N) := by
  constructor
  · apply le_antisymm
    · exact (iInf_le (fun s => H s N l) (endpointSampler point)).trans_eq (H_attainment N l)
    · exact le_iInf (fun s => all_H_lower s N l)
  · apply le_antisymm
    · exact (iInf_le (fun s : {s : PrefixSampler Strategy // Coarse s} => H s.val N l)
        ⟨endpointSampler point,endpointSampler_coarse _⟩).trans_eq (H_attainment N l)
    · exact le_iInf (fun s => all_H_lower s.val N l)

open D5.S3.Arith.FibonacciAtomic.CarryGraphRealization

/-- Fixed endpoint labels for the finite biased code and the repeating uniform code. -/
def CodeClaim : Prop :=
    (∀ d w, point.observe d w = some 0) ∧
    bill point = (fun _ => 0) ∧
    (stopping 3 Codes.biasedThree 0).map (fun v => (v.1,rotate v.2)) =
      [([false],(0:Fin 3))] ∧
    (stopping 3 Codes.biasedThree 1).map (fun v => (v.1,rotate v.2)) =
      [([true,false],(1:Fin 3)),([true,true],2)] ∧
    continuing 3 Codes.biasedThree 2 = [] ∧
    stopping 3 Codes.uniformThree 1 =
      [([false,false],(0:Fin 3)),([false,true],1),([true,false],2)] ∧
    continuing 3 Codes.uniformThree 2 = [[true,true]] ∧
    (∀ d, Codes.uniformThree.state (d+2) = Codes.uniformThree.state d ∧
      Codes.uniformThree.action (d+2) = Codes.uniformThree.action d) ∧
    (∀ i, law biased i = if i=0 then (1/2 : ℝ) else 1/4) ∧
    (∀ i, law uniform i = (1/3 : ℝ)) ∧
    (∫⁻ t, bill biased t ∂fairTape) = ENNReal.ofReal (3/2) ∧
    (∫⁻ t, bill uniform t ∂fairTape) = ENNReal.ofReal (8/3)

private theorem codes_exact : CodeClaim := by
  have b0 : labelSet 3 Codes.biasedThree 0 = {2} := by
    ext i; fin_cases i <;> norm_num [labelSet,Codes.biasedThree,Fin.ext_iff]
  have b1 : labelSet 3 Codes.biasedThree 1 = {0,1} := by
    ext i; fin_cases i <;> norm_num [labelSet,Codes.biasedThree,Fin.ext_iff]
  have u0 : labelSet 3 Codes.uniformThree 0 = ∅ := by
    ext i; fin_cases i <;> norm_num [labelSet,Codes.uniformThree]
  have u1 : labelSet 3 Codes.uniformThree 1 = Finset.univ := by
    ext i; fin_cases i <;> norm_num [labelSet,Codes.uniformThree]
  have sorted : ({0,1} : Finset (Fin 3)).sort (fun i j => i≤j) = [0,1] := by
    rw [Finset.sort_insert (s := ({1}:Finset (Fin 3))) (a := 0)
      (fun i j => i≤j) (by decide) (by decide)]
    simp
  refine ⟨fun _ _ => rfl, point_bill, ?_, ?_, ?_, ?_, ?_, ?_,
    biased_law, uniform_law, code_bills.1, code_bills.2⟩
  · norm_num [stopping, continuing, children, b0, b1, sorted,
      Fin.sort_univ, finRotate_apply, List.finRange, Fin.add_def, Fin.ext_iff]
  · norm_num [stopping, continuing, children, b0, b1, sorted,
      Fin.sort_univ, finRotate_apply, List.finRange, Fin.add_def, Fin.ext_iff]
  · norm_num [continuing, children, b0, b1, sorted,
      Fin.sort_univ, List.finRange, Fin.ext_iff]
  · norm_num [stopping, continuing, children, u0, u1,
      Fin.sort_univ, List.finRange, Fin.ext_iff]
  · norm_num [continuing, children, u0, u1,
      Fin.sort_univ, List.finRange, Fin.ext_iff]
  · intro d
    simp [Codes.uniformThree,Nat.add_mod]

/-- Exact all-sampler/controller target. No conclusion is included among its assumptions. -/
def Claim : Prop := CodeClaim ∧ ∀ N : ℕ, 1 ≤ N → ∀ l : ℝ, 0 < l →
  rawGamma N l = ENNReal.ofReal (Phase.sharp N l) ∧
  coarseGamma N l = ENNReal.ofReal (Phase.sharp N l) ∧
  (∃ s : PrefixSampler Strategy, Coarse s ∧ G s N l = ENNReal.ofReal (Phase.sharp N l)) ∧
  (N ≤ 6*l → rawGamma N l = ENNReal.ofReal (17*N)) ∧
  (6*l ≤ N → N ≤ 14*l → rawGamma N l = ENNReal.ofReal (67*N/4+3*l/2)) ∧
  (14*l ≤ N → rawGamma N l = ENNReal.ofReal (50*N/3+8*l/3)) ∧
  rawH N l = ENNReal.ofReal (17*N) ∧
  coarseH N l = ENNReal.ofReal (17*N) ∧
  (∃ s : PrefixSampler Strategy, Coarse s ∧ H s N l = ENNReal.ofReal (17*N))


/-- Sharp raw/coarse batch infima, literal codes, phase thresholds, and coarse attainment. -/
theorem result : Claim := by
  refine ⟨codes_exact, ?_⟩
  intro N hN l hl
  have gamma := gamma_exact N l hl.le
  have phases := Phase.phase_switches N l hl.le
  exact ⟨gamma.1,gamma.2,phase_attainment N l hl.le,
    fun h => by rw [gamma.1,phases.1 h],
    fun h1 h2 => by rw [gamma.1,phases.2.1 h1 h2],
    fun h => by rw [gamma.1,phases.2.2 h],
    (H_exact N l).1,(H_exact N l).2,
    ⟨endpointSampler point,endpointSampler_coarse _,H_attainment N l⟩⟩

end D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase
