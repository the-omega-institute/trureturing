/- GID: D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The attained local optimum equals the three short max-plus traces for all heterogeneous real tests. -/

import D5.S3.Combinatorics.Graph.LayeredCirculation.LayeredFlow
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Order.WithBot
import Mathlib.Algebra.Tropical.BigOperators
import Mathlib.LinearAlgebra.Matrix.Trace

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum
open scoped BigOperators
open Maths Maths.AdditiveTransport
noncomputable section

/-- The max-plus semiring uses the dual real order and one absorbing bottom. -/
abbrev MaxPlus := MinTropical (WithTop (OrderDual ℝ))

/-- This is the actual extended real score, with bottom denoting no path. -/
def maxScore (x : MaxPlus) : WithBot ℝ := MinTropical.untrop x

def realEntry (x : ℝ) : MaxPlus := MinTropical.trop ((OrderDual.toDual x : OrderDual ℝ) : WithTop (OrderDual ℝ))

private theorem maxScore_injective : Function.Injective maxScore := MinTropical.untrop_injective
private theorem maxScore_zero : maxScore (0 : MaxPlus) = ⊥ := rfl
private theorem maxScore_real (x : ℝ) : maxScore (realEntry x) = (x : WithBot ℝ) := rfl
private theorem realEntry_mul (x y : ℝ) : realEntry x * realEntry y = realEntry (x+y) := rfl

/-- The original row-to-column transition matrix, with its five legal entries. -/
def transition {n : ℕ} (f : ZMod n → Fin 5 → ℝ) (i : ZMod n) : Matrix (Fin 3) (Fin 3) MaxPlus :=
  ![![realEntry (f i 0), realEntry (f i 3), 0],
    ![0, 0, realEntry (f i 2)],
    ![realEntry (f i 1), realEntry (f i 4), 0]]

/-- Multiplication preserves the temporal order of the position-dependent tests. -/
def orderedProduct {n : ℕ} (f : ZMod n → Fin 5 → ℝ) (i : ZMod n) :
    ℕ → Matrix (Fin 3) (Fin 3) MaxPlus
  | 0 => 1
  | k+1 => orderedProduct f i k * transition f (i+k)

def monodromy {n : ℕ} (f : ZMod n → Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) MaxPlus :=
  orderedProduct f 0 n

/-- The tropical matrix trace is a maximum of diagonal scores. -/
def maxTrace (M : Matrix (Fin 3) (Fin 3) MaxPlus) : WithBot ℝ := maxScore (Matrix.trace M)

def traceValue (M : Matrix (Fin 3) (Fin 3) MaxPlus) : ℝ := (maxTrace M).unbotD 0

def shortCycleOptimum {n : ℕ} (f : ZMod n → Fin 5 → ℝ) : ℝ :=
  max (traceValue (monodromy f))
    (max (traceValue (monodromy f ^ 2) / 2) (traceValue (monodromy f ^ 3) / 3))

private theorem transition_edge {n : ℕ} (f : ZMod n → Fin 5 → ℝ)
    (i : ZMod n) (σ : Fin 5) :
    transition f i (sourceState σ) (targetState σ) = realEntry (f i σ) := by
  fin_cases σ <;> rfl

private theorem transition_witness {n : ℕ} (f : ZMod n → Fin 5 → ℝ)
    (i : ZMod n) (s t : Fin 3) (h : transition f i s t ≠ 0) :
    ∃ σ : Fin 5, sourceState σ = s ∧ targetState σ = t ∧
      transition f i s t = realEntry (f i σ) := by
  fin_cases s <;> fin_cases t
  all_goals first
    | exact ⟨0,rfl,rfl,rfl⟩
    | exact ⟨1,rfl,rfl,rfl⟩
    | exact ⟨2,rfl,rfl,rfl⟩
    | exact ⟨3,rfl,rfl,rfl⟩
    | exact ⟨4,rfl,rfl,rfl⟩
    | exact (h rfl).elim

private theorem sum_eq_term (g : Fin 3 → MaxPlus) : ∃ r : Fin 3, (∑ s, g s) = g r := by
  rw [Fin.sum_univ_three]
  rcases le_total (g 0) (g 1) with h | h
  · rw [MinTropical.add_eq_left h]
    rcases le_total (g 0) (g 2) with h2 | h2
    · exact ⟨0,MinTropical.add_eq_left h2⟩
    · exact ⟨2,MinTropical.add_eq_right h2⟩
  · rw [MinTropical.add_eq_right h]
    rcases le_total (g 1) (g 2) with h2 | h2
    · exact ⟨1,MinTropical.add_eq_left h2⟩
    · exact ⟨2,MinTropical.add_eq_right h2⟩

private theorem mul_entry_term_le (A B : Matrix (Fin 3) (Fin 3) MaxPlus) (s r t : Fin 3) :
    maxScore (A s r) + maxScore (B r t) ≤ maxScore ((A*B) s t) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  change maxScore (A s r) + maxScore (B r t) ≤
    max (max (maxScore (A s 0) + maxScore (B 0 t))
      (maxScore (A s 1) + maxScore (B 1 t))) (maxScore (A s 2) + maxScore (B 2 t))
  fin_cases r
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

private theorem mul_entry_witness (A B : Matrix (Fin 3) (Fin 3) MaxPlus) (s t : Fin 3) :
    ∃ r : Fin 3, (A*B) s t = A s r * B r t :=
  sum_eq_term (fun r => A s r * B r t)

private theorem end_layer {n : ℕ} {a b : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a b) : b.1 = a.1 + (w.length : ZMod n) := by
  induction w with
  | nil => simp
  | @concat middle w e h ih =>
    have he : e.1 = middle.1 := congrArg Prod.fst h
    change e.1+1 = a.1 + ((w.length+1 : ℕ) : ZMod n)
    rw [he, ih, Nat.cast_add, Nat.cast_one, add_assoc]

private theorem walk_product_le {n : ℕ} (f : ZMod n → Fin 5 → ℝ)
    {a b : ZMod n × Fin 3} (w : (layeredGraph n).Walk a b) :
    ((Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w : ℝ) : WithBot ℝ) ≤
      maxScore (orderedProduct f a.1 w.length a.2 b.2) := by
  induction w with
  | nil =>
    simp only [EdgeGraph.Walk.length,Maths.MaxPlusPotential.walkWeight,
      EdgeGraph.Walk.edges,List.map_nil,List.sum_nil,orderedProduct,Matrix.one_apply,if_pos rfl]
    exact le_rfl
  | @concat middle w e h ih =>
    have he : e.1 = middle.1 := congrArg Prod.fst h
    have hs : sourceState e.2 = middle.2 := congrArg Prod.snd h
    have hi := end_layer w
    rw [Maths.MaxPlusPotential.walkWeight_concat, EdgeGraph.Walk.length_concat]
    change ((Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w + f e.1 e.2 : ℝ) : WithBot ℝ) ≤
      maxScore ((orderedProduct f a.1 w.length * transition f (a.1+w.length)) a.2 (targetState e.2))
    rw [WithBot.coe_add]
    calc
      _ ≤ maxScore (orderedProduct f a.1 w.length a.2 middle.2) + (f e.1 e.2 : WithBot ℝ) :=
        add_le_add ih le_rfl
      _ = maxScore (orderedProduct f a.1 w.length a.2 middle.2) +
          maxScore (transition f (a.1+w.length) middle.2 (targetState e.2)) := by
        rw [← hs, ← hi, ← he, transition_edge, maxScore_real]
      _ ≤ _ := mul_entry_term_le _ _ _ middle.2 _

private theorem orderedProduct_append {n : ℕ} (f : ZMod n → Fin 5 → ℝ)
    (i : ZMod n) (k l : ℕ) :
    orderedProduct f i (k+l) = orderedProduct f i k * orderedProduct f (i+k) l := by
  induction l with
  | zero => simp [orderedProduct]
  | succ l ih =>
    change orderedProduct f i (k+l) * transition f (i+((k+l:ℕ):ZMod n)) =
      orderedProduct f i k * (orderedProduct f (i+k) l * transition f ((i+k)+l))
    rw [ih, Matrix.mul_assoc, Nat.cast_add, add_assoc]

private theorem orderedProduct_periods {n : ℕ} (f : ZMod n → Fin 5 → ℝ) (m : ℕ) :
    orderedProduct f 0 (m*n) = monodromy f ^ m := by
  induction m with
  | zero => simp [orderedProduct]
  | succ m ih =>
    rw [Nat.succ_mul, orderedProduct_append, ih, pow_succ]
    simp only [Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add, monodromy]


private theorem product_path_exists {n : ℕ} (f : ZMod n → Fin 5 → ℝ)
    (i : ZMod n) (k : ℕ) (s t : Fin 3)
    (h : orderedProduct f i k s t ≠ 0) :
    ∃ w : (layeredGraph n).Walk (i,s) (i+(k:ZMod n),t),
      w.length = k ∧ realEntry (Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w) =
        orderedProduct f i k s t := by
  induction k generalizing s t with
  | zero =>
    by_cases hst : s=t
    · subst t
      let w : (layeredGraph n).Walk (i,s) (i+((0:ℕ):ZMod n),s) :=
        (EdgeGraph.Walk.nil : (layeredGraph n).Walk (i,s) (i,s)).castFinish (by simp)
      refine ⟨w, by simp [w], ?_⟩
      simp only [w, Maths.MaxPlusPotential.walkWeight,EdgeGraph.Walk.edges_castFinish,
        EdgeGraph.Walk.edges,List.map_nil,List.sum_nil,orderedProduct,Matrix.one_apply,if_pos rfl]
      rfl
    · exact (h (by simp [orderedProduct, Matrix.one_apply, hst])).elim
  | succ k ih =>
    obtain ⟨r,hr⟩ := mul_entry_witness (orderedProduct f i k) (transition f (i+k)) s t
    have hP : orderedProduct f i k s r ≠ 0 := by
      intro hz
      apply h
      rw [orderedProduct, hr, hz, zero_mul]
    have hT : transition f (i+k) r t ≠ 0 := by
      intro hz
      apply h
      rw [orderedProduct, hr, hz, mul_zero]
    obtain ⟨q,hq,hweight⟩ := ih s r hP
    obtain ⟨σ,hsource,htarget,hentry⟩ := transition_witness f (i+k) r t hT
    let extended := q.concat (i+k,σ) (by simp only [layeredGraph, hsource])
    have hfinish : (layeredGraph n).target (i+k,σ) = (i+((k+1:ℕ):ZMod n),t) := by
      simp only [layeredGraph, htarget, Nat.cast_add, Nat.cast_one, add_assoc]
    let w := extended.castFinish hfinish
    refine ⟨w, ?_, ?_⟩
    · simp only [w, extended, EdgeGraph.Walk.length_castFinish, EdgeGraph.Walk.length_concat, hq]
    · simp only [w, extended, Maths.MaxPlusPotential.walkWeight_castFinish,
        Maths.MaxPlusPotential.walkWeight_concat]
      rw [← realEntry_mul, hweight, ← hentry]
      exact hr.symm

private theorem exists_zero_seam_path {n : ℕ} (i : ZMod n) (k : ℕ) :
    ∃ w : (layeredGraph n).Walk (i,0) (i+(k:ZMod n),0), w.length = k := by
  induction k with
  | zero =>
    exact ⟨(EdgeGraph.Walk.nil : (layeredGraph n).Walk (i,0) (i,0)).castFinish (by simp),
      by simp⟩
  | succ k ih =>
    obtain ⟨q,hq⟩ := ih
    let extended := q.concat (i+k,0) rfl
    have hfinish : (layeredGraph n).target (i+k,0) = (i+((k+1:ℕ):ZMod n),0) := by
      simp [layeredGraph, targetState, Nat.cast_add, Nat.cast_one, add_assoc]
    exact ⟨extended.castFinish hfinish, by simp [extended,hq]⟩

private theorem sum_term_score_le (g : Fin 3 → MaxPlus) (r : Fin 3) :
    maxScore (g r) ≤ maxScore (∑ s, g s) := by
  simp only [Fin.sum_univ_three]
  change maxScore (g r) ≤ max (max (maxScore (g 0)) (maxScore (g 1))) (maxScore (g 2))
  fin_cases r
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

private theorem trace_nonzero {n : ℕ} (f : ZMod n → Fin 5 → ℝ) (m : ℕ) :
    Matrix.trace (monodromy f ^ m) ≠ 0 := by
  obtain ⟨w,hw⟩ := exists_zero_seam_path (0 : ZMod n) (m*n)
  have hl := walk_product_le f w
  rw [hw, orderedProduct_periods] at hl
  have htr := sum_term_score_le (fun s => (monodromy f ^ m) s s) 0
  intro hz
  change maxScore ((monodromy f ^ m) 0 0) ≤ maxScore (Matrix.trace (monodromy f ^ m)) at htr
  rw [hz, maxScore_zero] at htr
  have hh := hl.trans htr
  exact (WithBot.not_coe_le_bot _) hh

private theorem trace_attaining_walk {n : ℕ} [NeZero n]
    (f : ZMod n → Fin 5 → ℝ) (m : ℕ) :
    ∃ (s : Fin 3) (w : (layeredGraph n).Walk (0,s) (0,s)),
      w.length = m*n ∧
      Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w =
        traceValue (monodromy f ^ m) := by
  obtain ⟨s,hs⟩ := sum_eq_term (fun s => (monodromy f ^ m) s s)
  have hn : orderedProduct f 0 (m*n) s s ≠ 0 := by
    rw [orderedProduct_periods]
    intro hz
    exact trace_nonzero f m (hs.trans hz)
  obtain ⟨q,hq,hweight⟩ := product_path_exists f 0 (m*n) s s hn
  have hfinish : ((0 : ZMod n)+((m*n:ℕ):ZMod n),s) = (0,s) := by
    simp [Nat.cast_mul, ZMod.natCast_self]
  let w := q.castFinish hfinish
  refine ⟨s,w,by simpa only [w,EdgeGraph.Walk.length_castFinish,EdgeGraph.Walk.length_castStart] using hq, ?_⟩
  have he : realEntry (Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w) =
      Matrix.trace (monodromy f ^ m) := by
    simp only [w,Maths.MaxPlusPotential.walkWeight_castFinish]
    rw [hweight,orderedProduct_periods]
    exact hs.symm
  have heScore := congrArg maxScore he
  simp only [maxScore_real] at heScore
  unfold traceValue maxTrace
  rw [← heScore]
  rfl

private theorem rotate_to_zero_layer {n : ℕ} [NeZero n]
    (f : ZMod n → Fin 5 → ℝ) {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) (hw : 0 < w.length) :
    ∃ (s : Fin 3) (r : (layeredGraph n).Walk (0,s) (0,s)),
      r.length = w.length ∧
      Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) r =
        Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w := by
  have hm : 0 < layerCount w 0 := by
    by_contra h
    have hz : layerCount w 0=0 := by omega
    rw [length_eq_layer_count,hz,mul_zero] at hw
    omega
  have hpos : 0 < ∑ σ, w.edgeMultiplicity (-1,σ) := by
    change 0 < layerCount w (-1)
    rwa [layer_count_uniform]
  have hex : ∃ σ, 0 < w.edgeMultiplicity (-1,σ) := by
    by_contra h
    push_neg at h
    have hz (σ : Fin 5) : w.edgeMultiplicity (-1,σ)=0 := by have := h σ; omega
    simp only [hz,Finset.sum_const_zero,lt_self_iff_false] at hpos
  obtain ⟨σ,hcount⟩ := hex
  have hmem := (w.edgeMultiplicity_pos_iff_mem_edges (-1,σ)).mp hcount
  have hv := w.mem_visited_of_mem_edges hmem
  change ((-1:ZMod n)+1,targetState σ) ∈ w.visited at hv
  simp only [neg_add_cancel] at hv
  obtain ⟨before,after,hedges⟩ := w.exists_split_of_mem_visited hv
  refine ⟨targetState σ,after.append before, ?_, ?_⟩
  · rw [EdgeGraph.Walk.length_append, ← w.edges_length, hedges, List.length_append,
      before.edges_length,after.edges_length]
    omega
  · simp only [Maths.MaxPlusPotential.walkWeight, EdgeGraph.Walk.edges_append,
      hedges,List.map_append,List.sum_append,add_comm]

private theorem closed_walk_trace_bound {n : ℕ} [NeZero n]
    (f : ZMod n → Fin 5 → ℝ) {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) (hw : 0 < w.length) :
    Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w ≤
      traceValue (monodromy f ^ layerCount w 0) := by
  obtain ⟨s,r,hlen,hweight⟩ := rotate_to_zero_layer f w hw
  have hl := walk_product_le f r
  rw [hlen,length_eq_layer_count w,Nat.mul_comm n,orderedProduct_periods] at hl
  have he : maxScore ((monodromy f ^ layerCount w 0) s s) ≤
      maxTrace (monodromy f ^ layerCount w 0) := by
    change maxScore ((monodromy f ^ layerCount w 0) s s) ≤
      maxScore (∑ t, (monodromy f ^ layerCount w 0) t t)
    exact sum_term_score_le (fun t => (monodromy f ^ layerCount w 0) t t) s
  have hb := hl.trans he
  rw [hweight] at hb
  have hn : maxTrace (monodromy f ^ layerCount w 0) ≠ ⊥ := by
    intro hz
    apply trace_nonzero f (layerCount w 0)
    exact maxScore_injective (hz.trans maxScore_zero.symm)
  exact (WithBot.le_unbotD_iff hn).mpr hb

private theorem short_candidate_le {n : ℕ} (f : ZMod n → Fin 5 → ℝ)
    (m : ℕ) (hm1 : 1 ≤ m) (hm3 : m ≤ 3) :
    traceValue (monodromy f ^ m) / m ≤ shortCycleOptimum f := by
  have hm : m=1 ∨ m=2 ∨ m=3 := by omega
  rcases hm with hm | hm | hm
  · simpa only [hm,pow_one,Nat.cast_one,div_one,shortCycleOptimum] using
      le_max_left (traceValue (monodromy f))
        (max (traceValue (monodromy f ^ 2)/2) (traceValue (monodromy f ^ 3)/3))
  · simpa only [hm,Nat.cast_ofNat,shortCycleOptimum] using
      (le_max_left (traceValue (monodromy f ^ 2)/2) (traceValue (monodromy f ^ 3)/3)).trans
        (le_max_right (traceValue (monodromy f))
          (max (traceValue (monodromy f ^ 2)/2) (traceValue (monodromy f ^ 3)/3)))
  · simpa only [hm,Nat.cast_ofNat,shortCycleOptimum] using
      (le_max_right (traceValue (monodromy f ^ 2)/2) (traceValue (monodromy f ^ 3)/3)).trans
        (le_max_right (traceValue (monodromy f))
          (max (traceValue (monodromy f ^ 2)/2) (traceValue (monodromy f ^ 3)/3)))

private theorem simple_law_score_le {n : ℕ} [NeZero n]
    (f : ZMod n → Fin 5 → ℝ) {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) (hw : IsSimpleCycle w) :
    localScore f (walkLaw w) ≤ shortCycleOptimum f := by
  obtain ⟨hm1,hm3,_⟩ := simple_cycle_winding w hw
  rw [walk_law_score]
  exact (div_le_div_of_nonneg_right (closed_walk_trace_bound f w hw.1)
    (Nat.cast_nonneg _)).trans (short_candidate_le f _ hm1 hm3)

private theorem local_score_upper {n : ℕ} [NeZero n]
    (f p : ZMod n → Fin 5 → ℝ) (hp : IsLocalLaw p) :
    localScore f p ≤ shortCycleOptimum f := by
  obtain ⟨ι,inst,weight,base,cycle,hnonneg,hsum,hsimple,_,_,hrec,_⟩ :=
    local_simple_cycle_decomposition p hp
  have heq : localScore f p = ∑ i, weight i * localScore f (walkLaw (cycle i)) := by
    simp only [localScore]
    simp_rw [hrec,Finset.mul_sum]
    conv_lhs =>
      arg 2
      ext j
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [heq]
  calc
    _ ≤ ∑ i, weight i * shortCycleOptimum f := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : 0 < weight i
      · exact mul_le_mul_of_nonneg_left
          (simple_law_score_le f (cycle i) (hsimple i hi)) (hnonneg i)
      · have hz : weight i=0 := le_antisymm (le_of_not_gt hi) (hnonneg i)
        simp only [hz,zero_mul,le_refl]
    _ = (∑ i, weight i) * shortCycleOptimum f := (Finset.sum_mul _ _ _).symm
    _ = shortCycleOptimum f := by rw [hsum,one_mul]

private theorem layer_count_of_length {n : ℕ} [NeZero n] {a : ZMod n × Fin 3}
    (m : ℕ) (w : (layeredGraph n).Walk a a) (hw : w.length=m*n) :
    layerCount w 0 = m := by
  have hh := length_eq_layer_count w
  rw [hw,Nat.mul_comm m] at hh
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne n)) hh.symm

private theorem trace_candidate_attained {n : ℕ} [NeZero n]
    (f : ZMod n → Fin 5 → ℝ) (m : ℕ) (hm : 0 < m) :
    ∃ p : ZMod n → Fin 5 → ℝ, IsLocalLaw p ∧
      localScore f p = traceValue (monodromy f ^ m) / m := by
  obtain ⟨s,w,hlen,hscore⟩ := trace_attaining_walk f m
  refine ⟨walkLaw w,walk_law_local w ?_,?_⟩
  · rw [hlen]
    exact Nat.mul_pos hm (Nat.pos_of_ne_zero (NeZero.ne n))
  · rw [walk_law_score,hscore,layer_count_of_length m w hlen]

private theorem local_optimum_attained {n : ℕ} [NeZero n]
    (f : ZMod n → Fin 5 → ℝ) :
    ∃ p : ZMod n → Fin 5 → ℝ, IsLocalLaw p ∧ localScore f p = shortCycleOptimum f := by
  obtain ⟨p1,hp1,h1⟩ := trace_candidate_attained f 1 (by omega)
  obtain ⟨p2,hp2,h2⟩ := trace_candidate_attained f 2 (by omega)
  obtain ⟨p3,hp3,h3⟩ := trace_candidate_attained f 3 (by omega)
  simp only [pow_one,Nat.cast_one,div_one] at h1
  simp only [Nat.cast_ofNat] at h2 h3
  unfold shortCycleOptimum
  rcases max_choice (traceValue (monodromy f))
    (max (traceValue (monodromy f ^ 2)/2) (traceValue (monodromy f ^ 3)/3)) with h | h
  · exact ⟨p1,hp1,h1.trans h.symm⟩
  · rcases max_choice (traceValue (monodromy f ^ 2)/2) (traceValue (monodromy f ^ 3)/3) with hh | hh
    · exact ⟨p2,hp2,h2.trans (h.trans hh).symm⟩
    · exact ⟨p3,hp3,h3.trans (h.trans hh).symm⟩

/-- For every original ring length and arbitrary real heterogeneous tests, the
attained local maximum is the maximum of the one-, two-, and three-turn max-plus
traces. Every repeated longer closed walk gives a lawful local law and obeys the
same bound after division by its winding number. -/
private theorem local_optimum_exact (n : ℕ) (hn : 5 ≤ n)
    (f : ZMod n → Fin 5 → ℝ) :
    letI : NeZero n := ⟨by omega⟩
    IsGreatest {v : ℝ | ∃ p : ZMod n → Fin 5 → ℝ, IsLocalLaw p ∧ localScore f p = v}
      (shortCycleOptimum f) ∧
    ∀ (m : ℕ), 1 ≤ m → ∀ (a : ZMod n × Fin 3)
      (w : (layeredGraph n).Walk a a), w.length=m*n →
      IsLocalLaw (walkLaw w) ∧
      localScore f (walkLaw w) =
        Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w / m ∧
      localScore f (walkLaw w) ≤ shortCycleOptimum f := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨p,hp,hscore⟩ := local_optimum_attained f
  refine ⟨⟨⟨p,hp,hscore⟩,?_⟩,?_⟩
  · rintro v ⟨q,hq,hvalue⟩
    rw [← hvalue]
    exact local_score_upper f q hq
  · intro m hm a w hlen
    have hlaw : IsLocalLaw (walkLaw w) := walk_law_local w (by
      rw [hlen]
      exact Nat.mul_pos (by omega) (by omega))
    refine ⟨hlaw,?_,local_score_upper f (walkLaw w) hlaw⟩
    rw [walk_law_score,layer_count_of_length m w hlen]

def LegalCyclicWord {L : ℕ} (u : ZMod L → Bool) : Prop :=
  ∀ j, ¬(u j=true ∧ u (j+1)=true)

def patternCode : Bool × Bool × Bool → Fin 5
  | (false,false,false) => 0
  | (true,false,false) => 1
  | (false,true,false) => 2
  | (false,false,true) => 3
  | (true,false,true) => 4
  | _ => 0

private theorem patternCode_pattern (σ : Fin 5) : patternCode (pattern σ) = σ := by
  fin_cases σ <;> rfl

def window {L : ℕ} (u : ZMod L → Bool) (j : ZMod L) : Bool × Bool × Bool :=
  (u j,u (j+1),u (j+2))

def wordScore {n L : ℕ} (f : ZMod n → Fin 5 → ℝ) (u : ZMod L → Bool) : ℝ :=
  ∑ j : Fin L, f (j.val : ZMod n) (patternCode (window u (j.val : ZMod L)))

private def cyclicEdge {n : ℕ} {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) [NeZero w.edges.length] (j : ZMod w.edges.length) : ZMod n × Fin 5 :=
  w.edges[j.val]'j.val_lt

private def closedWord {n : ℕ} {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) [NeZero w.edges.length] : ZMod w.edges.length → Bool :=
  fun j => (pattern (cyclicEdge w j).2).1

private theorem cyclic_edge_match {n : ℕ} {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) [NeZero w.edges.length] (j : ZMod w.edges.length) :
    (layeredGraph n).target (cyclicEdge w j) = (layeredGraph n).source (cyclicEdge w (j+1)) := by
  have hne : w.edges ≠ [] := by
    intro h
    have hh := NeZero.ne w.edges.length
    exact hh (by rw [h];rfl)
  have hJ : j+1 = ((j.val+1 : ℕ) : ZMod w.edges.length) := by simp
  by_cases hnext : j.val+1 < w.edges.length
  · have hval : (j+1).val = j.val+1 := by
      rw [hJ,ZMod.val_natCast,Nat.mod_eq_of_lt hnext]
    have hh := List.isChain_iff_getElem.mp w.edges_isChain j.val hnext
    simpa only [cyclicEdge,hval] using hh
  · have hlast : j.val = w.edges.length-1 := by have := j.val_lt; omega
    have hval : (j+1).val=0 := by
      rw [hJ,ZMod.val_natCast]
      have hh : j.val+1=w.edges.length := by have := j.val_lt;omega
      rw [hh,Nat.mod_self]
    have ht : (layeredGraph n).target (cyclicEdge w j) = a := by
      unfold cyclicEdge
      simpa only [List.getLast_eq_getElem hne,hlast] using w.target_getLast hne
    have hs : (layeredGraph n).source (cyclicEdge w (j+1)) = a := by
      unfold cyclicEdge
      simpa only [List.head_eq_getElem_zero hne,hval] using w.source_head hne
    exact ht.trans hs.symm

private theorem cyclic_edge_bits {n : ℕ} {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) [NeZero w.edges.length] (j : ZMod w.edges.length) :
    (pattern (cyclicEdge w j).2).2.1 = (pattern (cyclicEdge w (j+1)).2).1 ∧
    (pattern (cyclicEdge w j).2).2.2 = (pattern (cyclicEdge w (j+1)).2).2.1 := by
  have hh := congrArg Prod.snd (cyclic_edge_match w j)
  change targetState (cyclicEdge w j).2 = sourceState (cyclicEdge w (j+1)).2 at hh
  have hb := congrArg seam hh
  rw [(labels _).2,(labels _).1] at hb
  exact ⟨congrArg Prod.fst hb,congrArg Prod.snd hb⟩

private theorem closed_word_window {n : ℕ} {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) [NeZero w.edges.length] (j : ZMod w.edges.length) :
    window (closedWord w) j = pattern (cyclicEdge w j).2 := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact (cyclic_edge_bits w j).1.symm
    · have hh := (cyclic_edge_bits w j).2.trans (cyclic_edge_bits w (j+1)).1
      have he : j+1+1=j+2 := by ring
      simpa only [window,closedWord,he] using hh.symm

private theorem closed_word_legal {n : ℕ} {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) [NeZero w.edges.length] : LegalCyclicWord (closedWord w) := by
  intro j
  have hh := closed_word_window w j
  have hf := congrArg Prod.fst hh
  have hm := congrArg (fun p : Bool × Bool × Bool => p.2.1) hh
  change closedWord w j = (pattern (cyclicEdge w j).2).1 at hf
  change closedWord w (j+1) = (pattern (cyclicEdge w j).2).2.1 at hm
  rw [hf,hm]
  generalize (cyclicEdge w j).2 = σ
  fin_cases σ <;> decide

private theorem edge_layer_at {n : ℕ} {a b : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a b) (j : Fin w.edges.length) :
    (w.edges.get j).1 = a.1 + (j.val : ZMod n) := by
  have hall : ∀ k, ∀ hk : k < w.edges.length, (w.edges[k]).1 = a.1 + (k : ZMod n) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hne : w.edges ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hh := congrArg Prod.fst (w.source_head hne)
      simpa only [layeredGraph,List.head_eq_getElem_zero hne,Nat.cast_zero,add_zero] using hh
    | succ k ih =>
      intro hk
      have hstep := List.isChain_iff_getElem.mp w.edges_isChain k hk
      have hstep := congrArg Prod.fst hstep
      change (w.edges[k]).1+1 = (w.edges[k+1]).1 at hstep
      rw [← hstep,ih (by omega),Nat.cast_add,Nat.cast_one,add_assoc]
  exact hall j.val j.isLt

private theorem walk_weight_indexed {V E : Type*} {G : EdgeGraph V E}
    (f : E → ℝ) {a b : V} (w : G.Walk a b) :
    Maths.MaxPlusPotential.walkWeight f w = ∑ j : Fin w.edges.length, f (w.edges.get j) := by
  have hh := List.sum_ofFn (f := fun j : Fin w.edges.length => f w.edges[j.val])
  rw [List.ofFn_getElem_eq_map] at hh
  exact hh

private theorem closed_word_score {n : ℕ} (f : ZMod n → Fin 5 → ℝ) {s : Fin 3}
    (w : (layeredGraph n).Walk (0,s) (0,s)) [NeZero w.edges.length] :
    wordScore f (closedWord w) = Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w := by
  rw [walk_weight_indexed]
  unfold wordScore
  apply Finset.sum_congr rfl
  intro j _
  rw [closed_word_window,patternCode_pattern]
  have hj : (j.val : ZMod w.edges.length).val=j.val := ZMod.val_natCast_of_lt j.isLt
  simp only [cyclicEdge,hj]
  have hp := edge_layer_at w j
  simp only [zero_add] at hp
  change f (j.val : ZMod n) (w.edges.get j).2 = f (w.edges.get j).1 (w.edges.get j).2
  rw [hp]

private def seamCode : Bool × Bool → Fin 3
  | (false,false) => 0
  | (false,true) => 1
  | (true,false) => 2
  | _ => 0

private theorem legal_window_labels {L : ℕ} (u : ZMod L → Bool)
    (hu : LegalCyclicWord u) (j : ZMod L) :
    sourceState (patternCode (window u j)) = seamCode (u j,u (j+1)) ∧
    targetState (patternCode (window u j)) = seamCode (u (j+1),u (j+2)) := by
  have h₁ := hu j
  have h₂ := hu (j+1)
  have he : j+1+1=j+2 := by ring
  rw [he] at h₂
  unfold window
  generalize u j = a at *
  generalize u (j+1) = b at *
  generalize u (j+2) = c at *
  cases a <;> cases b <;> cases c <;>
    simp_all [patternCode,sourceState,targetState,seamCode]

private def wordVertex {n L : ℕ} (u : ZMod L → Bool) (k : ℕ) : ZMod n × Fin 3 :=
  ((k:ZMod n),seamCode (u (k:ZMod L),u ((k:ZMod L)+1)))

private def wordEdge {n L : ℕ} (u : ZMod L → Bool) (k : ℕ) : ZMod n × Fin 5 :=
  ((k:ZMod n),patternCode (window u (k:ZMod L)))

private theorem word_edge_source {n L : ℕ} (u : ZMod L → Bool)
    (hu : LegalCyclicWord u) (k : ℕ) :
    (layeredGraph n).source (wordEdge u k) = wordVertex u k := by
  exact Prod.ext rfl (legal_window_labels u hu k).1

private theorem word_edge_target {n L : ℕ} (u : ZMod L → Bool)
    (hu : LegalCyclicWord u) (k : ℕ) :
    (layeredGraph n).target (wordEdge u k) = wordVertex u (k+1) := by
  apply Prod.ext
  · simp [wordEdge,wordVertex,layeredGraph]
  · simpa [wordVertex,wordEdge,layeredGraph,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
      (legal_window_labels u hu k).2

private def wordWalk {n L : ℕ} (u : ZMod L → Bool) (hu : LegalCyclicWord u) :
    (k : ℕ) → (layeredGraph n).Walk (wordVertex u 0) (wordVertex u k)
  | 0 => .nil
  | k+1 => ((wordWalk u hu k).concat (wordEdge u k) (word_edge_source u hu k)).castFinish
      (word_edge_target u hu k)

private theorem word_walk_length {n L : ℕ} (u : ZMod L → Bool)
    (hu : LegalCyclicWord u) (k : ℕ) : (wordWalk (n:=n) u hu k).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [wordWalk] using congrArg Nat.succ ih

private theorem word_walk_weight {n L : ℕ} (f : ZMod n → Fin 5 → ℝ)
    (u : ZMod L → Bool) (hu : LegalCyclicWord u) (k : ℕ) :
    Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) (wordWalk u hu k) =
      ∑ j ∈ Finset.range k, f (j:ZMod n) (patternCode (window u (j:ZMod L))) := by
  induction k with
  | zero => simp [wordWalk,Maths.MaxPlusPotential.walkWeight]
  | succ k ih => simp [wordWalk,Maths.MaxPlusPotential.walkWeight_concat,
      Finset.sum_range_succ,ih,wordEdge]

private theorem legal_word_walk {n : ℕ} [NeZero n] (m : ℕ)
    (f : ZMod n → Fin 5 → ℝ) (u : ZMod (m*n) → Bool) (hu : LegalCyclicWord u) :
    ∃ (s : Fin 3) (w : (layeredGraph n).Walk (0,s) (0,s)),
      w.length=m*n ∧ Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w=wordScore f u := by
  have hv : wordVertex (n:=n) u (m*n) = wordVertex u 0 := by
    simp [wordVertex,Nat.cast_mul]
  have h0 : wordVertex (n:=n) u 0 = (0,seamCode (u 0,u 1)) := by simp [wordVertex]
  let w := (((wordWalk (n:=n) u hu (m*n)).castFinish hv).castStart h0).castFinish h0
  refine ⟨seamCode (u 0,u 1),w,?_,?_⟩
  · simpa only [w,EdgeGraph.Walk.length_castFinish,EdgeGraph.Walk.length_castStart] using word_walk_length (n:=n) u hu (m*n)
  · simp only [w,Maths.MaxPlusPotential.walkWeight_castFinish,wordScore]
    simp only [Maths.MaxPlusPotential.walkWeight,EdgeGraph.Walk.edges_castStart,
      EdgeGraph.Walk.edges_castFinish]
    change Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) (wordWalk u hu (m*n)) = _
    rw [word_walk_weight]
    exact (Fin.sum_univ_eq_sum_range _ _).symm

private theorem periodic_word_trace_exact {n : ℕ} [NeZero n]
    (f : ZMod n → Fin 5 → ℝ) (m : ℕ) (hm : 0 < m) :
    IsGreatest {v : ℝ | ∃ u : ZMod (m*n) → Bool, LegalCyclicWord u ∧ wordScore f u=v}
      (traceValue (monodromy f ^ m)) := by
  have hL : 0 < m*n := Nat.mul_pos hm (Nat.pos_of_ne_zero (NeZero.ne n))
  obtain ⟨s,w,hlen,hscore⟩ := trace_attaining_walk f m
  have hedges : w.edges.length=m*n := by simpa using hlen
  letI : NeZero w.edges.length := ⟨by omega⟩
  have hv : ∃ u : ZMod (m*n) → Bool, LegalCyclicWord u ∧
      wordScore f u=traceValue (monodromy f ^ m) := by
    have H : ∃ u : ZMod w.edges.length → Bool, LegalCyclicWord u ∧
        wordScore f u=traceValue (monodromy f ^ m) :=
      ⟨closedWord w,closed_word_legal w,(closed_word_score f w).trans hscore⟩
    exact Eq.mp (congrArg (fun L => ∃ u : ZMod L → Bool, LegalCyclicWord u ∧
      wordScore f u=traceValue (monodromy f ^ m)) hedges) H
  refine ⟨hv,?_⟩
  rintro v ⟨u,hu,rfl⟩
  obtain ⟨s,w,hlen,hweight⟩ := legal_word_walk m f u hu
  have hb := closed_walk_trace_bound f w (by omega)
  rwa [layer_count_of_length m w hlen,hweight] at hb

/-- The complete layered local-law optimum, with its positive real cycle
certificates and exact legal periodic-word interpretation. -/
theorem whole_theorem18_1 (n : ℕ) (hn : 5 ≤ n) (f : ZMod n → Fin 5 → ℝ) :
    letI : NeZero n := ⟨by omega⟩
    IsGreatest {v : ℝ | ∃ p : ZMod n → Fin 5 → ℝ, IsLocalLaw p ∧ localScore f p=v}
      (max (traceValue (monodromy f))
        (max (traceValue (monodromy f ^ 2)/2) (traceValue (monodromy f ^ 3)/3))) ∧
    IsCompact {p : ZMod n → Fin 5 → ℝ | IsLocalLaw p} ∧
    {p : ZMod n → Fin 5 → ℝ | IsLocalLaw p}.Nonempty ∧
    (∀ p : ZMod n → Fin 5 → ℝ,
      (IsLocalLaw p ↔ (∀ i σ, 0 ≤ p i σ) ∧ (∀ i, ∑ σ, p i σ=1) ∧ IsCirculation p)) ∧
    (∀ p : ZMod n → Fin 5 → ℝ, IsLocalLaw p → HasPositiveCycleDecomposition p) ∧
    (∀ p : ZMod n → Fin 5 → ℝ, (∀ i σ, 0 ≤ p i σ) → IsCirculation p → p ≠ 0 →
      HasPositiveCycleErasure p) ∧
    (∀ m : ℕ, 1 ≤ m →
      IsGreatest {v : ℝ | ∃ u : ZMod (m*n) → Bool, LegalCyclicWord u ∧ wordScore f u=v}
        (traceValue (monodromy f ^ m))) ∧
    ∀ (m : ℕ), 1 ≤ m → ∀ (a : ZMod n × Fin 3) (w : (layeredGraph n).Walk a a),
      w.length=m*n → IsLocalLaw (walkLaw w) ∧
      localScore f (walkLaw w)=Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w/m ∧
      localScore f (walkLaw w) ≤ shortCycleOptimum f := by
  letI : NeZero n := ⟨by omega⟩
  refine ⟨(local_optimum_exact n hn f).1,local_law_compact,?_,local_law_iff,
    positive_cycle_decomposition,positive_cycle_erasure,?_,(local_optimum_exact n hn f).2⟩
  · obtain ⟨p,hp,_⟩ := local_optimum_attained f
    exact ⟨p,hp⟩
  · intro m hm
    exact periodic_word_trace_exact f m (by omega)

end
end D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum
