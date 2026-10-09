/- GID: D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Fair-bit prefix samplers obey the common-law dyadic survival bound. -/

import D5.S3.Arith.FibonacciAtomic.MersenneDyadicSupportLines
import D5.S3.Arith.FibonacciAtomic.CarryGraphRealization
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail
open MeasureTheory
open scoped BigOperators ENNReal Classical
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape fairBit)
open D5.S3.Arith.FibonacciAtomic.DyadicSupportLines

def readPrefix (d : ℕ) (t : Tape) : Fin d → Bool := fun i => t i.val

def cylinder (d : ℕ) (w : Fin d → Bool) : Set Tape := {t | readPrefix d t = w}

private theorem cylinder_data (d : ℕ) (w : Fin d → Bool) :
    MeasurableSet (cylinder d w) ∧ fairTape (cylinder d w) = (2 : ℝ≥0∞)⁻¹ ^ d := by
  have eqn : cylinder d w = Set.pi (↑(Finset.range d) : Set ℕ)
      (fun n => {if h : n < d then w ⟨n,h⟩ else false}) := by
    ext t
    simp only [cylinder, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe,
      Finset.mem_range, Set.mem_singleton_iff]
    constructor
    · intro h n hn
      rw [dif_pos hn]
      exact congrFun h ⟨n,hn⟩
    · intro h
      funext i
      exact (h i.val i.isLt).trans (dif_pos i.isLt)
  rw [eqn]
  constructor
  · exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton _)
  · rw [fairTape, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
    have mass (x : Bool) : fairBit {x} = (2 : ℝ≥0∞)⁻¹ := by
      cases x <;> simp [fairBit]
    simp_rw [mass]
    simp

def layerCount {α : Type*} (d : ℕ) (f : (Fin d → Bool) → α) (a : α) : ℕ :=
  (Finset.univ.filter fun w => f w = a).card

private theorem finite_event {α : Type*} (d : ℕ) (f : (Fin d → Bool) → α) (a : α) :
    MeasurableSet {t : Tape | f (readPrefix d t) = a} ∧
      fairTape {t : Tape | f (readPrefix d t) = a} =
        (layerCount d f a : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ d := by
  classical
  let W := {w : Fin d → Bool // f w = a}
  have event : {t : Tape | f (readPrefix d t) = a} = ⋃ w : W, cylinder d w.val := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, cylinder]
    exact ⟨fun h => ⟨⟨readPrefix d t,h⟩,rfl⟩, fun ⟨w,h⟩ => h ▸ w.property⟩
  have disj : Pairwise fun u v : W => Disjoint (cylinder d u.val) (cylinder d v.val) := by
    intro u v huv
    apply Set.disjoint_left.mpr
    intro t hu hv
    exact huv (Subtype.ext (hu.symm.trans hv))
  rw [event]
  refine ⟨MeasurableSet.iUnion (fun w => (cylinder_data d w.val).1), ?_⟩
  rw [measure_iUnion disj (fun w => (cylinder_data d w.val).1)]
  simp_rw [(fun w : W => (cylinder_data d w.val).2)]
  rw [tsum_fintype]
  simp [W, Fintype.card_subtype, layerCount]

structure PrefixSampler (α : Type*) where
  observe : (d : ℕ) → (Fin d → Bool) → Option α
  persistent : ∀ (d e : ℕ) (hde : d ≤ e) (w : Fin e → Bool) (i : α),
    observe d (fun j => w ⟨j.val,lt_of_lt_of_le j.isLt hde⟩) = some i → observe e w = some i
  terminates : ∀ᵐ t ∂fairTape, ∃ d i, observe d (readPrefix d t) = some i

def emitted {α : Type*} (s : PrefixSampler α) (i : α) : Set Tape :=
  {t | ∃ d, s.observe d (readPrefix d t) = some i}

def law {m : ℕ} (s : PrefixSampler (Fin m)) (i : Fin m) : ℝ := (fairTape (emitted s i)).toReal

def active {α : Type*} (s : PrefixSampler α) (d : ℕ) : Set Tape :=
  {t | s.observe d (readPrefix d t) = none}

def bill {α : Type*} (s : PrefixSampler α) (t : Tape) : ℝ≥0∞ :=
  ∑' d : ℕ, (active s d).indicator (fun _ => 1) t

theorem emitted_measurable {α : Type*} (s : PrefixSampler α) (i : α) :
    MeasurableSet (emitted s i) := by
  have ev : emitted s i = ⋃ d, {t : Tape | s.observe d (readPrefix d t) = some i} := by
    ext t; simp [emitted]
  rw [ev]
  exact MeasurableSet.iUnion fun d => (finite_event d (s.observe d) (some i)).1

private theorem expected_bill {α : Type*} (s : PrefixSampler α) :
    (∫⁻ t, bill s t ∂fairTape) = ∑' d, fairTape (active s d) := by
  have meas (d : ℕ) : MeasurableSet (active s d) := (finite_event d (s.observe d) none).1
  unfold bill
  rw [lintegral_tsum (fun d => (measurable_const.indicator (meas d)).aemeasurable)]
  congr 1
  funext d
  exact lintegral_indicator_one (meas d)

end D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail

namespace D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail
open MeasureTheory
open scoped BigOperators ENNReal Classical
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)
open D5.S3.Arith.FibonacciAtomic.DyadicSupportLines

theorem emitted_disjoint {α : Type*} (s : PrefixSampler α) :
    Pairwise fun i j => Disjoint (emitted s i) (emitted s j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro t ⟨d,hd⟩ ⟨e,he⟩
  have h1 : s.observe (max d e) (readPrefix (max d e) t) = some i :=
    s.persistent d (max d e) (le_max_left _ _) (readPrefix (max d e) t) i hd
  have h2 : s.observe (max d e) (readPrefix (max d e) t) = some j :=
    s.persistent e (max d e) (le_max_right _ _) (readPrefix (max d e) t) j he
  exact hij (Option.some.inj (h1.symm.trans h2))

theorem law_simplex {m : ℕ} (s : PrefixSampler (Fin m)) :
    (∀ i, 0 ≤ law s i) ∧ ∑ i, law s i = 1 := by
  have all : (⋃ i, emitted s i) =ᵐ[fairTape] Set.univ := by
    filter_upwards [s.terminates] with t ht
    obtain ⟨d,i,h⟩ := ht
    have member : t ∈ ⋃ i, emitted s i := Set.mem_iUnion.mpr ⟨i,d,h⟩
    apply propext
    exact ⟨fun _ => trivial, fun _ => member⟩
  have total : ∑ i, fairTape (emitted s i) = 1 := by
    rw [← tsum_fintype (L := SummationFilter.unconditional (Fin m)), ← measure_iUnion (emitted_disjoint s) (emitted_measurable s)]
    rw [measure_congr all]
    exact measure_univ
  refine ⟨fun i => ENNReal.toReal_nonneg, ?_⟩
  unfold law
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top fairTape _), total]
  rfl

private theorem layer_le_law {m : ℕ} (s : PrefixSampler (Fin m)) (d : ℕ) (i : Fin m) :
    ((layerCount d (s.observe d) (some i) : ℕ) : ℝ) /
      (2 : ℝ)^d ≤ law s i := by
  have H : fairTape {t : Tape | s.observe d (readPrefix d t) = some i} ≤
      fairTape (emitted s i) := measure_mono (fun t h => ⟨d,h⟩)
  rw [(finite_event d (s.observe d) (some i)).2] at H
  have HH := ENNReal.toReal_mono (measure_ne_top fairTape _) H
  convert HH using 1 <;> simp [law, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_inv, div_eq_mul_inv]

private theorem layer_floor {m : ℕ} (s : PrefixSampler (Fin m)) (d : ℕ) (i : Fin m) :
    (layerCount d (s.observe d) (some i) : ℤ) ≤
      ⌊(2 : ℝ)^d * law s i⌋ := by
  apply Int.le_floor.mpr
  have H := (div_le_iff₀ (by positivity : (0 : ℝ)<2^d)).mp (layer_le_law s d i)
  simpa [mul_comm] using H

end D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail

namespace D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail
open MeasureTheory
open scoped BigOperators ENNReal Classical
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)
open D5.S3.Arith.FibonacciAtomic.DyadicSupportLines

private theorem layer_partition {m : ℕ} (s : PrefixSampler (Fin m)) (d : ℕ) :
    layerCount d (s.observe d) none +
      ∑ i : Fin m, layerCount d (s.observe d) (some i) = 2^d := by
  have H := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin d → Bool)) (Finset.univ : Finset (Option (Fin m))) (s.observe d)
  simp [univ_option, Finset.mem_insertNone, Fintype.card_fun] at H
  unfold layerCount
  convert H using 1
  congr 1
  · congr 1; ext w; simp
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1; ext w; simp

theorem cylinder_tail_lower {m : ℕ} (s : PrefixSampler (Fin m)) (d : ℕ) :
    ENNReal.ofReal (D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual (law s) d / (2 : ℝ)^d) ≤ fairTape (active s d) := by
  have part : ((layerCount d (s.observe d) none : ℕ) : ℤ) +
      ∑ i : Fin m, (layerCount d (s.observe d) (some i) : ℤ) =
        (2 : ℤ)^d := by exact_mod_cast layer_partition s d
  have floors := Finset.sum_le_sum (s := Finset.univ) (fun i _ => layer_floor s d i)
  have gap : (2 : ℤ)^d - ∑ i, ⌊(2 : ℝ)^d * law s i⌋ ≤
      (layerCount d (s.observe d) none : ℤ) := by omega
  have gapR : D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual (law s) d ≤
      (layerCount d (s.observe d) none : ℝ) := by
    have HH : (((2 : ℤ)^d - ∑ i, ⌊(2 : ℝ)^d * law s i⌋ : ℤ) : ℝ) ≤
        (layerCount d (s.observe d) none : ℝ) := by exact_mod_cast gap
    simpa [D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual] using HH
  apply ENNReal.ofReal_le_of_le_toReal
  rw [show fairTape (active s d) =
      (layerCount d (s.observe d) none : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹^d
    from (finite_event d (s.observe d) none).2]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  simpa [div_eq_mul_inv, inv_pow] using
    div_le_div_of_nonneg_right gapR (by positivity : (0 : ℝ) ≤ 2^d)

private theorem residual_nonnegative {m : ℕ} (s : PrefixSampler (Fin m)) (d : ℕ) :
    0 ≤ D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual (law s) d := by
  have H := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Int.floor_le ((2 : ℝ)^d * law s i))
  rw [← Finset.mul_sum, (law_simplex s).2, mul_one] at H
  simpa [D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual, Int.cast_sum] using sub_nonneg.mpr H

theorem ddg_lower {m : ℕ} (s : PrefixSampler (Fin m))
    (hs : Summable (fun d : ℕ => D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual (law s) d / (2 : ℝ)^d)) :
    ENNReal.ofReal (cost (law s)) ≤ ∫⁻ t, bill s t ∂fairTape := by
  rw [expected_bill, cost, ENNReal.ofReal_tsum_of_nonneg
    (fun d => div_nonneg (residual_nonnegative s d) (by positivity)) hs]
  exact ENNReal.tsum_le_tsum (cylinder_tail_lower s)

end D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail
open scoped BigOperators ENNReal Classical
open MeasureTheory
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)

def relabel {α β : Type*} (f : α → β) (s : PrefixSampler α) : PrefixSampler β where
  observe d w := (s.observe d w).map f
  persistent d e hde w i h := by
    cases ho : s.observe d (fun j => w ⟨j.val,lt_of_lt_of_le j.isLt hde⟩) with
    | none => simp [ho] at h
    | some a =>
      have hi : f a = i := by simpa [ho] using h
      rw [s.persistent d e hde w a ho,Option.map_some,hi]
  terminates := by
    filter_upwards [s.terminates] with t ht
    obtain ⟨d,a,ha⟩ := ht
    exact ⟨d,f a,by simp [ha]⟩

theorem relabel_emitted {α β : Type*} (f : α → β) (s : PrefixSampler α) (i : β) (t : Tape) :
    t ∈ emitted (relabel f s) i ↔ ∃ a, t ∈ emitted s a ∧ f a = i := by
  constructor
  · rintro ⟨d,hd⟩
    obtain ⟨a,ha,hi⟩ := Option.map_eq_some_iff.mp hd
    exact ⟨a,⟨d,ha⟩,hi⟩
  · rintro ⟨a,⟨d,ha⟩,hi⟩
    exact ⟨d,by simp [relabel,ha,hi]⟩

theorem relabel_bill {α β : Type*} (f : α → β) (s : PrefixSampler α) :
    bill (relabel f s) = bill s := by
  funext t
  unfold bill
  congr 1
  funext d
  simp [active,relabel]

theorem bill_measurable {α : Type*} (s : PrefixSampler α) : Measurable (bill s) :=
  Measurable.ennreal_tsum fun d => measurable_const.indicator
    ((finite_event d (s.observe d) none).1)

end D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail
open scoped BigOperators ENNReal Classical
open MeasureTheory
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)

private theorem bill_at_stop {α : Type*} (s : PrefixSampler α) (t : Tape) (n : ℕ)
    (ht : ∃ i, s.observe n (readPrefix n t) = some i)
    (before : ∀ d < n, s.observe d (readPrefix d t) = none) : bill s t = (n : ℝ≥0∞) := by
  have survival (d : ℕ) : t ∈ active s d ↔ d < n := by
    constructor
    · intro hd
      by_contra h
      have le : n ≤ d := Nat.le_of_not_gt h
      obtain ⟨i,hi⟩ := ht
      have stop := s.persistent n d le (readPrefix d t) i hi
      simpa [active,stop] using hd
    · intro hd
      exact before d hd
  unfold bill
  have eqn : (fun d => (active s d).indicator (fun _ => (1 : ℝ≥0∞)) t) =
      (fun d => if d ∈ Finset.range (n) then (1 : ℝ≥0∞) else 0) := by
    funext d
    simp only [Set.indicator_apply,survival,Finset.mem_range]
  rw [eqn,tsum_eq_sum (s := Finset.range (n)) (fun d hd => by simp [hd])]
  calc
    (∑ d ∈ Finset.range (n), if d ∈ Finset.range (n) then (1 : ℝ≥0∞) else 0) =
        ∑ _d ∈ Finset.range (n), (1 : ℝ≥0∞) :=
      Finset.sum_congr rfl (fun d hd => if_pos hd)
    _ = (n : ℝ≥0∞) := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]

end D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail

namespace D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail.Paths
open scoped BigOperators ENNReal Classical
open MeasureTheory
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)
open D5.S3.Arith.FibonacciAtomic.CarryGraphEmbedding
open D5.S3.Arith.FibonacciAtomic.CarryGraphRealization
open D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail

/-- A labelled stopping word already contained in a finite observed prefix. -/
def FiniteReturn (m : ℕ) (g : Path) (d : ℕ) (w : Fin d → Bool) (i : Fin m) : Prop :=
  ∃ n, ∃ hn : n < d,
    (List.ofFn (fun j : Fin (n+1) => w ⟨j.val, by omega⟩), i) ∈ stopping m g n

private theorem finite_return_iff (m : ℕ) (g : Path) (hm : 2 ≤ m)
    (hg : IsRootPath m g) (d : ℕ) (t : Tape) (i : Fin m) :
    FiniteReturn m g d (readPrefix d t) i ↔
      ∃ n, n < d ∧ sample m g t = some (i,n+1) := by
  have H := D5.S3.Arith.FibonacciAtomic.CarryGraphRealization.result m hm g hg
  obtain ⟨_,_,_,_,_,_,_,first,_⟩ := H
  constructor
  · rintro ⟨n,hn,hw⟩
    exact ⟨n,hn,(first t i n).mpr hw⟩
  · rintro ⟨n,hn,hs⟩
    exact ⟨n,hn,(first t i n).mp hs⟩

private theorem prefix_return_unique (m : ℕ) (g : Path) (hm : 2 ≤ m)
    (hg : IsRootPath m g) (d : ℕ) (w : Fin d → Bool) (i j : Fin m)
    (hi : FiniteReturn m g d w i) (hj : FiniteReturn m g d w j) : i=j := by
  let t : Tape := fun n => if h : n < d then w ⟨n,h⟩ else false
  have ht : readPrefix d t = w := by funext a; simp [readPrefix,t,a.isLt]
  obtain ⟨a,_,ha⟩ := (finite_return_iff m g hm hg d t i).mp (ht ▸ hi)
  obtain ⟨b,_,hb⟩ := (finite_return_iff m g hm hg d t j).mp (ht ▸ hj)
  exact congrArg Prod.fst (Option.some.inj (ha.symm.trans hb))

private theorem finite_return_extend (m : ℕ) (g : Path) (d e : ℕ) (hde : d ≤ e)
    (w : Fin e → Bool) (i : Fin m)
    (h : FiniteReturn m g d (fun j => w ⟨j.val,by omega⟩) i) :
    FiniteReturn m g e w i := by
  obtain ⟨n,hn,hw⟩ := h
  exact ⟨n,lt_of_lt_of_le hn hde,hw⟩

/-- Stop at the unique labelled leaf visible in the current finite prefix. -/
def fromPath (m : ℕ) (g : Path) (hm : 2 ≤ m) (hg : IsRootPath m g) :
    PrefixSampler (Fin m) where
  observe d w := if h : ∃ i, FiniteReturn m g d w i then some (Classical.choose h) else none
  persistent d e hde w i h := by
    split at h
    next hx =>
      have hi : Classical.choose hx = i := Option.some.inj h
      have hr := finite_return_extend m g d e hde w i (hi ▸ Classical.choose_spec hx)
      rw [dif_pos ⟨i,hr⟩]
      congr 1
      exact prefix_return_unique m g hm hg e w _ i (Classical.choose_spec _) hr
    next hx => cases h
  terminates := by
    have H := D5.S3.Arith.FibonacciAtomic.CarryGraphRealization.result m hm g hg
    obtain ⟨_,_,_,_,_,_,_,_,charged,_,_,returns,_⟩ := H
    filter_upwards [returns] with t ht
    obtain ⟨i,n,hs⟩ := ht
    have positive : 0 < n := by
      have initial : (1 : ℝ≥0∞) ≤
          D5.S3.Arith.FibonacciAtomic.CarryGraphRealization.bill m g t := by
        unfold D5.S3.Arith.FibonacciAtomic.CarryGraphRealization.bill
        simpa [scan] using ENNReal.le_tsum (f := fun d =>
          if (scan m g t d).isRight then (1 : ℝ≥0∞) else 0) 0
      rw [charged t i n hs] at initial
      by_contra hn
      have hz : n=0 := by omega
      simp [hz] at initial
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hr := (finite_return_iff m g hm hg (a+1) t i).mpr ⟨a,by omega,hs⟩
    refine ⟨a+1,i,?_⟩
    rw [dif_pos ⟨i,hr⟩]
    congr 1
    exact prefix_return_unique m g hm hg _ _ _ i (Classical.choose_spec _) hr

private theorem observation (m : ℕ) (g : Path) (hm : 2 ≤ m) (hg : IsRootPath m g)
    (d : ℕ) (t : Tape) (i : Fin m) :
    (fromPath m g hm hg).observe d (readPrefix d t) = some i ↔
      ∃ n, n < d ∧ sample m g t = some (i,n+1) := by
  rw [← finite_return_iff m g hm hg d t i]
  change (if h : ∃ j, FiniteReturn m g d (readPrefix d t) j then
    some (Classical.choose h) else none) = some i ↔ _
  constructor
  · intro h
    split at h
    next hx => exact Option.some.inj h ▸ Classical.choose_spec hx
    next hx => cases h
  · intro h
    rw [dif_pos ⟨i,h⟩]
    congr 1
    exact prefix_return_unique m g hm hg _ _ _ i (Classical.choose_spec _) h

/-- The finite-prefix observer preserves the expected charge of the realized code. -/
theorem path_expectation (m : ℕ) (g : Path) (hm : 2 ≤ m) (hg : IsRootPath m g) :
    (∫⁻ t, bill (fromPath m g hm hg) t ∂fairTape) = ENNReal.ofReal (pathCost g) := by
  have H := D5.S3.Arith.FibonacciAtomic.CarryGraphRealization.result m hm g hg
  obtain ⟨_,_,_,_,_,_,_,_,charged,_,_,returns,expectation,_⟩ := H
  rw [← expectation]
  apply lintegral_congr_ae
  filter_upwards [returns] with t ht
  obtain ⟨i,n,hs⟩ := ht
  have initial : (1 : ℝ≥0∞) ≤
      D5.S3.Arith.FibonacciAtomic.CarryGraphRealization.bill m g t := by
    unfold D5.S3.Arith.FibonacciAtomic.CarryGraphRealization.bill
    simpa [scan] using ENNReal.le_tsum (f := fun d =>
      if (scan m g t d).isRight then (1 : ℝ≥0∞) else 0) 0
  have positive : 0 < n := by
    rw [charged t i n hs] at initial
    by_contra hn
    have hz : n=0 := by omega
    simp [hz] at initial
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let s := fromPath m g hm hg
  have stop : s.observe (a+1) (readPrefix (a+1) t) = some i :=
    (observation m g hm hg (a+1) t i).mpr ⟨a,by omega,hs⟩
  have exists_stop : ∃ d j, s.observe d (readPrefix d t) = some j := ⟨a+1,i,stop⟩
  have before (d : ℕ) (hd : d < a+1) : s.observe d (readPrefix d t) = none := by
    cases hh : s.observe d (readPrefix d t) with
    | none => rfl
    | some j =>
      obtain ⟨b,hb,hbs⟩ := (observation m g hm hg d t j).mp hh
      have eqn := congrArg Prod.snd (Option.some.inj (hs.symm.trans hbs))
      omega
  rw [bill_at_stop s t (a+1) ⟨i,stop⟩ before,charged t i (a+1) hs]

/-- The output law of the finite-prefix observer is the fixed-label digit law. -/
theorem path_law (m : ℕ) (g : Path) (hm : 2 ≤ m) (hg : IsRootPath m g) (i : Fin m) :
    law (fromPath m g hm hg) i = Real.ofDigits (labelDigit g i) := by
  have H := D5.S3.Arith.FibonacciAtomic.CarryGraphRealization.result m hm g hg
  obtain ⟨nonneg,_,_,_,_,_,_,_,charged,returned,_⟩ := H
  have event : emitted (fromPath m g hm hg) i = {t : Tape | ∃ n, sample m g t=some (i,n)} := by
    ext t
    constructor
    · rintro ⟨d,hd⟩
      obtain ⟨n,_,hn⟩ := (observation m g hm hg d t i).mp hd
      exact ⟨n+1,hn⟩
    · rintro ⟨n,hn⟩
      have initial : (1 : ℝ≥0∞) ≤
          D5.S3.Arith.FibonacciAtomic.CarryGraphRealization.bill m g t := by
        unfold D5.S3.Arith.FibonacciAtomic.CarryGraphRealization.bill
        simpa [scan] using ENNReal.le_tsum (f := fun d =>
          if (scan m g t d).isRight then (1 : ℝ≥0∞) else 0) 0
      have positive : 0 < n := by
        rw [charged t i n hn] at initial
        by_contra hh
        have hz : n=0 := by omega
        simp [hz] at initial
      obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact ⟨a+1,(observation m g hm hg (a+1) t i).mpr ⟨a,by omega,hn⟩⟩
  unfold law
  rw [event,(returned i).2,ENNReal.toReal_ofReal (nonneg i)]
end D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail.Paths
