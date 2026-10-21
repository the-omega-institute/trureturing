/- GID: D5/S3/Entropy/TwoDeletionRunEntropyBounds
   generality: G
   mirror-B: D5/B/S3/Entropy/TwoDeletionRunEntropyBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact binary run counts and entropy comparisons for two deletions. -/

/-
admission_basis: escape-witness
Module escape_witness: deletion_abstract_bridge_gap.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19498.
convex_increment_mono: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: f_increment_lower.
nonadjLinear: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: nonadj_phi_ge_linear.
list_sum_add_const: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: nonadjLinear_formula.
f: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: same_run_phi_formula.
logb_three_bounds: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: h_step_pos.
sum_cast_list: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: jensen_list_nat.
longRuns: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: bridgeWeights_constraints.
bridgeWeightsAux: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: bridgeWeights_constraints.
logb_nat_add_one_le: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: run_fine_insertion_bound.
runDefect: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: component_length_le.
component_aux_sum: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: component_sum.
component_aux_nonempty: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: component_nonempty.
adjacent_sum_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: component_jensen_bound.
nat_square_le_two_pow_sub_two: proof_shape: content; frozen: none; escape_witness: none; consumer: logb_nat_ge_eight_upper.
nonadjLinear_formula: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: nonadj_phi_lower_sum.
f_zero: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: same_run_phi_formula.
f_one: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: f_real_lower.
f_two: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: f_increment_lower.
f_mul: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: first_pair_phi.
f_convex: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: f_increment_lower.
f_nonneg_nat: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: run_fine_insertion_bound.
deletion_two_coefficient_pos: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: short_run_jensen_gap.
pair_nonadjacent_decomposition: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: run_grouping_lower.
Hrun: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: Hrun_lower.
bridgeWeightsAux_length: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: bridgeWeights_constraints.
positive_filter_long: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: bridgeWeights_constraints.
bridgeWeightsAux_sum: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: bridgeWeights_constraints.
longRuns_bounds: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.deletion_counting_lower_of_run_score.
longRuns_nonempty_of_defect: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.deletion_counting_lower_of_run_score.
jensen_sum_f: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: jensen_list_nat.
component_sum: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: component_jensen_bound.
runDefect_eq: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: run_fine_insertion_bound.
component_aux_length_le: proof_shape: content; frozen: none; escape_witness: none; consumer: component_length_le.
component_nonempty: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: component_jensen_bound.
runPhiInsertion: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: run_fine_insertion_bound.
logb_nat_ge_eight_upper: proof_shape: content; frozen: none; escape_witness: none; consumer: large_insertion_comparison.
f_increment_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: h_step_lower.
f_merge_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: h_step_lower.
f_product_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: nonadj_phi_ge_linear.
f_real_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: f_choose_two_lower.
Hrun_two: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: Hrun_lower.
jensen_list_nat: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: jensen_nat_list_at_least.
short_run_jensen_gap: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: deletion_abstract_bridge_gap.
first_pair_phi: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: pair_phi_formula.
same_run_phi_formula: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: run_coarse_insertion_bound.
bridgeWeights_constraints: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.deletion_counting_lower_of_run_score.
component_length_le: proof_shape: content; frozen: none; escape_witness: none; consumer: component_jensen_bound.
deletionRunScore: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.deletion_counting_lower_of_run_score.
large_insertion_comparison: proof_shape: content; frozen: none; escape_witness: none; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.large_insertion_strict.
h_step_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: h_step_pos.
nonadj_phi_ge_linear: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: nonadj_phi_lower_sum.
f_nat_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: sum_f_run_lower.
f_choose_two_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: run_term_coarse.
f_add_super_nat: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: component_aux_lower.
jensen_nat_list_at_least: proof_shape: content; frozen: none; escape_witness: none; consumer: deletion_abstract_bridge_gap.
component_jensen_bound: proof_shape: content; frozen: none; escape_witness: none; consumer: run_fine_insertion_bound.
pair_phi_formula: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: run_coarse_insertion_bound.
h_step_pos: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: Hrun_step.
nonadj_phi_lower_sum: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: nonadj_defect_lower.
sum_f_run_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: nonadj_defect_lower.
component_aux_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: component_lower.
run_term_coarse: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: run_coarse_insertion_bound.
nonadj_defect_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: run_fine_insertion_bound.
component_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: run_grouping_lower.
Hrun_step: proof_shape: content; frozen: none; escape_witness: none; consumer: Hrun_lower.
run_grouping_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: run_coarse_insertion_bound.
Hrun_lower: proof_shape: content; frozen: none; escape_witness: none; consumer: deletion_abstract_bridge_gap.
run_fine_insertion_bound: proof_shape: content; frozen: none; escape_witness: none; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.large_insertion_strict.
deletion_abstract_bridge_gap: proof_shape: content; frozen: none; escape_witness: deletion_abstract_bridge_gap; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.deletion_strict_of_count_lower.
run_coarse_insertion_bound: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.large_insertion_strict.
-/

import D5.S1.Words.TwoDeletionRunDecks
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace D5.S3.Entropy.TwoDeletionRunEntropyBounds

open D5.S1.Words.TwoDeletionRunDecks

private lemma convex_increment_mono (F : ℝ → ℝ) (hF : ConvexOn ℝ (Set.Ici 0) F)
    {x y t : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (ht : 0 < t) :
    F (x+t)-F x ≤ F (y+t)-F y := by
  have hD : 0 < y-x+t := by linarith
  have h1 := hF.2 hx (show 0 ≤ y+t by linarith)
    (show 0 ≤ (y-x)/(y-x+t) by positivity)
    (show 0 ≤ t/(y-x+t) by positivity)
    (show (y-x)/(y-x+t)+t/(y-x+t)=1 by field_simp [hD.ne'] <;> ring)
  have h2 := hF.2 hx (show 0 ≤ y+t by linarith)
    (show 0 ≤ t/(y-x+t) by positivity)
    (show 0 ≤ (y-x)/(y-x+t) by positivity)
    (show t/(y-x+t)+(y-x)/(y-x+t)=1 by field_simp [hD.ne'] <;> ring)
  simp only [smul_eq_mul] at h1 h2
  have he1 : (y-x)/(y-x+t)*x+t/(y-x+t)*(y+t)=x+t := by field_simp [hD.ne'] <;> ring
  have he2 : t/(y-x+t)*x+(y-x)/(y-x+t)*(y+t)=y := by field_simp [hD.ne'] <;> ring
  rw [he1] at h1
  rw [he2] at h2
  have hs : (y-x)/(y-x+t)+t/(y-x+t)=1 := by field_simp [hD.ne'] <;> ring
  have hadd := add_le_add h1 h2
  have he : (y-x)/(y-x+t)*F x+t/(y-x+t)*F (y+t) +
      (t/(y-x+t)*F x+(y-x)/(y-x+t)*F (y+t)) = F x+F (y+t) := by
    field_simp [hD.ne']
    ring
  rw [he] at hadd
  linarith

private noncomputable def nonadjLinear (F : ℕ → ℝ) : List ℕ → ℝ
  | [] => 0
  | a::rs => ((rs.drop 1).map (fun b : ℕ => F a+F b)).sum+nonadjLinear F rs

private lemma list_sum_add_const (F : ℕ → ℝ) (a : ℝ) (rs : List ℕ) :
    (rs.map (fun b : ℕ => a+F b)).sum=(rs.length:ℝ)*a+(rs.map F).sum := by
  simp only [List.sum_map_add, List.map_const', List.sum_replicate, nsmul_eq_mul]

noncomputable def f (x : ℝ) : ℝ := x * Real.logb 2 x

private lemma logb_three_bounds : (3:ℝ)/2 < Real.logb 2 3 ∧ Real.logb 2 3 < 5/3 := by
  have hlow := Real.logb_lt_logb (b:=2) (x:=8) (y:=9) (by norm_num) (by norm_num) (by norm_num)
  have hupp := Real.logb_lt_logb (b:=2) (x:=27) (y:=32) (by norm_num) (by norm_num) (by norm_num)
  have h8 : Real.logb 2 8 = 3 := by
    calc Real.logb 2 8 = Real.logb 2 ((2:ℝ)^3) := by norm_num
         _ = 3 := by rw [Real.logb_pow]; norm_num
  have h9 : Real.logb 2 9 = 2 * Real.logb 2 3 := by
    calc Real.logb 2 9 = Real.logb 2 ((3:ℝ)^2) := by norm_num
         _ = _ := by rw [Real.logb_pow]; norm_num
  have h27 : Real.logb 2 27 = 3 * Real.logb 2 3 := by
    calc Real.logb 2 27 = Real.logb 2 ((3:ℝ)^3) := by norm_num
         _ = _ := by rw [Real.logb_pow]; norm_num
  have h32 : Real.logb 2 32 = 5 := by
    calc Real.logb 2 32 = Real.logb 2 ((2:ℝ)^5) := by norm_num
         _ = _ := by rw [Real.logb_pow]; norm_num
  rw [h8,h9] at hlow
  rw [h27,h32] at hupp
  constructor <;> linarith

private lemma sum_cast_list (ws : List ℕ) : (ws.map (fun n : ℕ => (n:ℝ))).sum=(ws.sum:ℝ) := by
  exact (Nat.cast_list_sum ws).symm

def longRuns (rs : List ℕ) : List ℕ := rs.filter (fun r => 2 ≤ r)

def bridgeWeightsAux (prev singles : ℕ) : List ℕ → List ℕ
  | [] => [prev+singles+1]
  | r::rs => if r=1 then bridgeWeightsAux prev (singles+1) rs
      else (prev+r+singles+1)::bridgeWeightsAux r 0 rs

private lemma logb_nat_add_one_le (d : ℕ) : Real.logb 2 ((d : ℝ)+1) ≤ d := by
  have hp : d+1 ≤ 2^d := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hpR : (d : ℝ)+1 ≤ (2:ℝ)^d := by exact_mod_cast hp
  have h := Real.logb_le_logb_of_le (b:=2) (by norm_num)
    (show 0 < (d:ℝ)+1 by positivity) hpR
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ)<2), mul_one] using h

def runDefect (rs : List ℕ) : ℕ := (rs.map (fun r => r-1)).sum

private lemma component_aux_sum (acc prev : ℕ) (rs : List ℕ) :
    (componentWeightsAux acc prev rs).sum = acc+(adjacentWeights (prev::rs)).sum := by
  induction rs generalizing acc prev with
  | nil => simp [componentWeightsAux,adjacentWeights]
  | cons r rs ih =>
    by_cases hp : prev=1 <;>
      simp [componentWeightsAux,adjacentWeights,hp,ih,Nat.add_assoc]

private lemma component_aux_nonempty (acc prev : ℕ) (rs : List ℕ) :
    componentWeightsAux acc prev rs ≠ [] := by
  induction rs generalizing acc prev with
  | nil => simp [componentWeightsAux]
  | cons r rs ih =>
    by_cases he : prev=1 <;> simp [componentWeightsAux,he,ih]

private lemma adjacent_sum_lower (rs : List ℕ) (hp : ∀ r ∈ rs,0<r) (hlen : 2≤rs.length) :
    rs.sum-1 ≤ (adjacentWeights rs).sum := by
  induction rs with
  | nil => simp at hlen
  | cons a rs ih =>
    cases rs with
    | nil => simp at hlen
    | cons b rs =>
      have ha := hp a (by simp)
      have hb := hp b (by simp)
      have hab : a+b-1≤a*b := Nat.add_sub_one_le_mul (Nat.ne_of_gt ha) (Nat.ne_of_gt hb)
      cases rs with
      | nil => simpa [adjacentWeights] using hab
      | cons c rs =>
        have hi := ih (fun r hr => hp r (by simp [hr])) (by simp)
        simp only [List.sum_cons,adjacentWeights] at hi ⊢
        omega

private lemma nat_square_le_two_pow_sub_two (n : ℕ) (hn : 8 ≤ n) : n^2 ≤ 2^(n-2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have he : n+1-2 = (n-2)+1 := by omega
    rw [he,pow_succ 2 (n-2)]
    nlinarith

private lemma nonadjLinear_formula (F : ℕ → ℝ) (a b : ℕ) (ts : List ℕ) :
    nonadjLinear F (a::(ts++[b])) =
      ((ts.length:ℝ)-1)*(F a+(ts.map F).sum+F b)+F a+F b := by
  induction ts generalizing a with
  | nil => simp [nonadjLinear] <;> ring
  | cons c ts ih =>
    change ((ts++[b]).map (fun r : ℕ => F a+F r)).sum+
      nonadjLinear F (c::(ts++[b])) = _
    rw [ih c,list_sum_add_const]
    simp only [List.length_append,List.length_singleton,List.map_append,List.map_singleton,
      List.sum_append,List.sum_singleton,List.length_cons,Nat.cast_add,Nat.cast_one,
      List.map_cons,List.sum_cons,List.length_nil,List.map_nil,List.sum_nil,Nat.cast_zero,zero_add,add_zero,zero_mul,mul_zero]
    ring

lemma f_zero : f 0 = 0 := by simp [f]

lemma f_one : f 1 = 0 := by simp [f]

lemma f_two : f 2 = 2 := by norm_num [f, Real.logb_self_eq_one]

lemma f_mul (a b : ℝ) : f (a*b) = b*f a + a*f b := by
  unfold f
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [Real.logb_mul ha hb]
  ring

private lemma f_convex : ConvexOn ℝ (Set.Ici 0) f := by
  have hi : 0 ≤ (Real.log 2)⁻¹ := le_of_lt (inv_pos.mpr (Real.log_pos (by norm_num)))
  have hc := ConvexOn.smul hi Real.convexOn_mul_log
  convert hc using 1
  ext x
  simp only [f, Real.logb, smul_eq_mul]
  ring

private lemma f_nonneg_nat (n : ℕ) : 0 ≤ f n := by
  cases n with
  | zero => simp [f]
  | succ n =>
    unfold f Real.logb
    have h1 : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact mul_nonneg (by positivity) (div_nonneg (Real.log_nonneg h1) (Real.log_nonneg (by norm_num)))

private lemma deletion_two_coefficient_pos (m : ℕ) :
    0 < (6 * Real.logb 2 3 - 9) * m + 5 - 3 * Real.logb 2 3 := by
  have h := logb_three_bounds
  have hm : (0 : ℝ) ≤ m := by positivity
  have : 0 < 6*Real.logb 2 3-9 := by linarith
  nlinarith

private lemma pair_nonadjacent_decomposition (rs : List ℕ) :
    ((pairWeights rs).map (fun n : ℕ => f n)).sum =
      ((nonadjacentWeights rs).map (fun n : ℕ => f n)).sum +
      ((adjacentWeights rs).map (fun n : ℕ => f n)).sum := by
  induction rs with
  | nil => simp [pairWeights,nonadjacentWeights,adjacentWeights]
  | cons a rs ih =>
    cases rs with
    | nil => simp [pairWeights,nonadjacentWeights,adjacentWeights]
    | cons b rs =>
      simp only [pairWeights,nonadjacentWeights,adjacentWeights,List.drop_succ_cons,List.drop_zero,
        List.map_cons,List.map_append,List.sum_append,List.sum_cons] at ih ⊢
      linarith

noncomputable def Hrun (m r : ℝ) : ℝ :=
  f ((r+1)*(r+2)/2)+(2*m-r)*f (r+1)

private lemma bridgeWeightsAux_length (rs : List ℕ) (prev singles : ℕ) :
    (bridgeWeightsAux prev singles rs).length=(rs.filter (fun r => r≠1)).length+1 := by
  induction rs generalizing prev singles with
  | nil => rfl
  | cons r rs ih =>
    by_cases hr : r=1
    · subst r; simp [bridgeWeightsAux,ih]
    · simp [bridgeWeightsAux,hr,ih]

private lemma positive_filter_long (rs : List ℕ) (hp : ∀ r∈rs,0<r) :
    rs.filter (fun r => r≠1)=longRuns rs := by
  apply List.filter_congr
  intro r hr
  have h := hp r hr
  simp only [decide_eq_decide]
  omega

private lemma bridgeWeightsAux_sum (rs : List ℕ) (prev singles : ℕ) (hp : ∀ r∈rs,0<r) :
    (bridgeWeightsAux prev singles rs).sum=
      rs.sum+(longRuns rs).sum+(longRuns rs).length+prev+singles+1 := by
  induction rs generalizing prev singles with
  | nil => simp [bridgeWeightsAux,longRuns]
  | cons r rs ih =>
    have hr := hp r (by simp)
    have ht : ∀ a∈rs,0<a := fun a ha => hp a (by simp [ha])
    by_cases he : r=1
    · subst r
      simp only [bridgeWeightsAux,ite_true]
      rw [ih _ _ ht]
      simp [longRuns]
      omega
    · have hl : 2 ≤ r := by omega
      simp only [bridgeWeightsAux,if_neg he,List.sum_cons]
      rw [ih _ _ ht]
      simp [longRuns,hl]
      omega

lemma longRuns_bounds (rs : List ℕ) (hp : ∀ r∈rs,0<r) :
    (∀ r∈longRuns rs,2 ≤ r ∧ r ≤ rs.sum) ∧ (longRuns rs).sum ≤ rs.sum := by
  constructor
  · intro r hr
    have h : r∈rs ∧ 2 ≤ r := by simpa [longRuns] using hr
    exact ⟨h.2,List.single_le_sum (fun a _ => Nat.zero_le a) r h.1⟩
  · have hsub : (longRuns rs).Sublist rs := List.filter_sublist
    exact hsub.sum_le_sum (fun a _ => Nat.zero_le a)

lemma longRuns_nonempty_of_defect (rs : List ℕ) (hp : ∀ r∈rs,0<r)
    (hd : 0<runDefect rs) : longRuns rs ≠ [] := by
  intro he
  have hones : ∀ r∈rs,r=1 := by
    intro r hr
    have hpos := hp r hr
    have hn : ¬2 ≤ r := by
      intro h
      have hm : r∈longRuns rs := by simp [longRuns,hr,h]
      rw [he] at hm
      simp at hm
    omega
  have hz : runDefect rs=0 := by
    unfold runDefect
    have hmap : rs.map (fun r => r-1)=rs.map (fun _ => 0) := by
      apply List.map_congr_left
      intro r hr
      rw [hones r hr]
    rw [hmap]
    simp
  omega

private lemma jensen_sum_f {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hs : s.Nonempty) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i) * Real.logb 2 ((∑ i ∈ s, w i) / s.card) ≤ ∑ i ∈ s, f (w i) := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hsum : (∑ _i ∈ s, (s.card : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hc.ne'
  have h := f_convex.map_sum_le (t:=s) (w:=fun _ => (s.card:ℝ)⁻¹) (p:=w)
    (fun _ _ => inv_nonneg.mpr hc.le) hsum hw
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  have hm := mul_le_mul_of_nonneg_left h hc.le
  unfold f at hm
  simp only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at hm
  simpa only [f,div_eq_mul_inv, mul_comm (∑ i ∈ s, w i)] using hm

private lemma component_sum (rs : List ℕ) :
    (componentWeights rs).sum = (adjacentWeights rs).sum := by
  cases rs with
  | nil => simp [componentWeights,adjacentWeights]
  | cons a rs =>
    cases rs with
    | nil => simp [componentWeights,adjacentWeights]
    | cons b rs => simp [componentWeights,adjacentWeights,component_aux_sum]

lemma runDefect_eq (rs : List ℕ) (hp : ∀ r ∈ rs, 0<r) :
    runDefect rs + rs.length = rs.sum := by
  induction rs with
  | nil => simp [runDefect]
  | cons r rs ih =>
    have hr := hp r (by simp)
    have ht := ih (fun a ha => hp a (by simp [ha]))
    simp only [runDefect,List.map_cons,List.sum_cons,List.length_cons] at ht ⊢
    omega

private lemma component_aux_length_le (acc prev : ℕ) (rs : List ℕ)
    (hp : 0<prev) (hr : ∀ r ∈ rs,0<r) :
    (componentWeightsAux acc prev rs).length ≤ 1+(prev-1)+runDefect rs := by
  induction rs generalizing acc prev with
  | nil => simp [componentWeightsAux,runDefect]
  | cons r rs ih =>
    have hr0 := hr r (by simp)
    have ht : ∀ s ∈ rs,0<s := fun s hs => hr s (by simp [hs])
    by_cases he : prev=1
    · simp only [componentWeightsAux,if_pos he,runDefect,List.map_cons,List.sum_cons]
      have hi := ih (acc+prev*r) r hr0 ht
      simp only [runDefect] at hi
      omega
    · simp only [componentWeightsAux,if_neg he,List.length_cons,runDefect,List.map_cons,List.sum_cons]
      have hi := ih (prev*r) r hr0 ht
      simp only [runDefect] at hi
      omega

private lemma component_nonempty (rs : List ℕ) (hlen : 2≤rs.length) : componentWeights rs ≠ [] := by
  cases rs with
  | nil => simp at hlen
  | cons a rs =>
    cases rs with
    | nil => simp at hlen
    | cons b rs => exact component_aux_nonempty (a*b) b rs

noncomputable def runPhiInsertion (rs : List ℕ) : ℝ :=
  ((collisionWeights rs).map (fun n : ℕ => f n)).sum

private lemma logb_nat_ge_eight_upper (n : ℕ) (hn : 8 ≤ n) :
    Real.logb 2 n ≤ (n:ℝ)/2-1 := by
  have hs : (n:ℝ)^2 ≤ (2:ℝ)^(n-2) := by exact_mod_cast nat_square_le_two_pow_sub_two n hn
  have h := Real.logb_le_logb_of_le (b:=2) (by norm_num)
    (show (0:ℝ)<(n:ℝ)^2 by positivity) hs
  rw [Real.logb_pow,Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] at h
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast (show 2≤n by omega)
  rw [Nat.cast_sub (show 2≤n by omega)] at h
  norm_num at h
  linarith

private lemma f_increment_lower {r : ℝ} (hr : 2 ≤ r) :
    3*Real.logb 2 3-2 ≤ f (r+1)-f r := by
  have h := convex_increment_mono f f_convex (x:=2) (y:=r) (t:=1) (by norm_num) hr (by norm_num)
  norm_num [f_two, show f 3 = 3*Real.logb 2 3 from rfl] at h
  linarith

private lemma f_merge_lower {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    f a + f b + 2*b ≤ f (a+b) := by
  have h := convex_increment_mono f f_convex (x:=b) (y:=a) (t:=b) hb.le hab hb
  have he : b+b=2*b := by ring
  rw [he, f_mul, f_two] at h
  linarith



private lemma f_product_lower (a b : ℕ) (ha : 1≤a) (hb : 1≤b) : f a+f b ≤ f (a*b:ℕ) := by
  rw [Nat.cast_mul,f_mul]
  have haR : (1:ℝ)≤a := by exact_mod_cast ha
  have hbR : (1:ℝ)≤b := by exact_mod_cast hb
  have h1 := mul_le_mul_of_nonneg_right haR (f_nonneg_nat b)
  have h2 := mul_le_mul_of_nonneg_right hbR (f_nonneg_nat a)
  nlinarith

private lemma f_real_lower {r : ℝ} (hr : 2 ≤ r) : 2*(r-1) ≤ f r := by
  have h := f_convex.secant_mono (a:=1) (x:=2) (y:=r)
    (by norm_num) (by norm_num) (by linarith : 0 ≤ r)
    (by norm_num) (by linarith : r ≠ 1) hr
  norm_num [f_one, f_two] at h
  have hr1 : 0 < r-1 := by linarith
  have hm := (le_div_iff₀ hr1).mp h
  linarith

private lemma Hrun_two (m : ℝ) :
    Hrun m 2=2*(f 3+4*m)+((6*Real.logb 2 3-8)*m+6-6*Real.logb 2 3) := by
  have h6 := f_mul 2 3
  norm_num [f_two] at h6
  have hf3 : f 3=3*Real.logb 2 3 := rfl
  unfold Hrun
  norm_num
  rw [h6,hf3]
  ring

private lemma jensen_list_nat (ws : List ℕ) (hw : ws≠[]) :
    (ws.sum:ℝ)*Real.logb 2 ((ws.sum:ℝ)/ws.length) ≤ (ws.map (fun n : ℕ => f n)).sum := by
  let w : Fin ws.length → ℝ := fun i => ws[i]
  have hn : 0<ws.length := List.length_pos_iff_ne_nil.mpr hw
  have hu : (Finset.univ : Finset (Fin ws.length)).Nonempty := ⟨⟨0,hn⟩,by simp⟩
  have hj := jensen_sum_f Finset.univ w hu (fun _ _ => by dsimp [w]; positivity)
  have hs : (∑ i : Fin ws.length, w i)=(ws.sum:ℝ) := by
    dsimp only [w]
    rw [←List.sum_ofFn]
    change (List.ofFn (fun i : Fin ws.length => (ws[i.val] : ℝ))).sum = _
    rw [List.ofFn_getElem_eq_map ws (fun n : ℕ => (n : ℝ))]
    exact sum_cast_list ws
  have hf : (∑ i : Fin ws.length, f (w i))=(ws.map (fun n : ℕ => f n)).sum := by
    dsimp only [w]
    rw [←List.sum_ofFn]
    change (List.ofFn (fun i : Fin ws.length => f ws[i.val])).sum = _
    rw [List.ofFn_getElem_eq_map ws (fun n : ℕ => f n)]
  simpa only [hs,hf,Finset.card_univ,Fintype.card_fin] using hj

private lemma short_run_jensen_gap (m q : ℕ) (hm : 2 ≤ m) (hq : 1 ≤ q) :
    f (m+1) < (q:ℝ)*((6*Real.logb 2 3-8)*m+6-6*Real.logb 2 3) +
      ((m:ℝ)+3*q+1)*Real.logb 2 (((m:ℝ)+3*q+1)/((q:ℝ)+1)) := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hx : (0:ℝ) < (m:ℝ)+1 := by positivity
  have hc : (0:ℝ) < (q:ℝ)+1 := by positivity
  have hS : (0:ℝ) < (m:ℝ)+3*q+1 := by positivity
  have hL := logb_three_bounds
  have hqlog := logb_nat_add_one_le q
  have hratio : (3:ℝ) ≤ ((m:ℝ)+3*q+1)/((q:ℝ)+1) := by
    apply (le_div_iff₀ hc).mpr
    linarith
  have hrl := Real.logb_le_logb_of_le (b:=2) (by norm_num)
    (by norm_num : (0:ℝ)<3) hratio
  have hstrict := Real.logb_lt_logb (b:=2) (by norm_num) hx
    (show (m:ℝ)+1 < (m:ℝ)+3*q+1 by linarith)
  have hdiv : Real.logb 2 (((m:ℝ)+3*q+1)/((q:ℝ)+1)) =
      Real.logb 2 ((m:ℝ)+3*q+1)-Real.logb 2 ((q:ℝ)+1) :=
    Real.logb_div hS.ne' hc.ne'
  have hprod := mul_lt_mul_of_pos_left hstrict hx
  have hqprod := mul_le_mul_of_nonneg_left hqlog hx.le
  have hLprod := mul_le_mul_of_nonneg_left hrl (show (0:ℝ)≤3*q by positivity)
  have hcoef := deletion_two_coefficient_pos m
  have hpositive := mul_pos (show (0:ℝ)<q by linarith) hcoef
  have he : ((m:ℝ)+3*q+1)*Real.logb 2 (((m:ℝ)+3*q+1)/((q:ℝ)+1)) =
      ((m:ℝ)+1)*(Real.logb 2 ((m:ℝ)+3*q+1)-Real.logb 2 ((q:ℝ)+1)) +
      3*q*Real.logb 2 (((m:ℝ)+3*q+1)/((q:ℝ)+1)) := by rw [hdiv]; ring
  rw [he]
  unfold f
  nlinarith

private lemma first_pair_phi (a : ℕ) (rs : List ℕ) :
    ((rs.map (fun b => a*b)).map (fun n : ℕ => f n)).sum =
      (rs.sum:ℝ)*f a + (a:ℝ)*(rs.map (fun r : ℕ => f r)).sum := by
  induction rs with
  | nil => simp
  | cons b rs ih =>
    simp only [List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_mul,f_mul,ih]
    ring

lemma same_run_phi_formula (rs : List ℕ) :
    ((sameRunWeights rs).map (fun n : ℕ => f n)).sum =
      (rs.map (fun r => f (r.choose 2))).sum := by
  induction rs with
  | nil => simp [sameRunWeights]
  | cons a rs ih =>
    by_cases ha : 2≤a
    · simpa [sameRunWeights,ha] using congrArg (fun t => f (a.choose 2)+t) ih
    · have ha' : a=0 ∨ a=1 := by omega
      rcases ha' with rfl | rfl <;> simpa [sameRunWeights,f_zero] using ih

lemma bridgeWeights_constraints (rs : List ℕ) (hp : ∀ r∈rs,0<r) :
    (bridgeWeightsAux 0 0 rs).length=(longRuns rs).length+1 ∧
    (bridgeWeightsAux 0 0 rs).sum=rs.sum+(longRuns rs).sum+(longRuns rs).length+1 := by
  constructor
  · rw [bridgeWeightsAux_length,positive_filter_long rs hp]
  · simpa  using bridgeWeightsAux_sum rs 0 0 hp

private lemma component_length_le (rs : List ℕ) (hp : ∀ r ∈ rs,0<r) :
    (componentWeights rs).length ≤ 1+runDefect rs := by
  cases rs with
  | nil => simp [componentWeights,runDefect]
  | cons a rs =>
    cases rs with
    | nil => simp [componentWeights,runDefect]
    | cons b rs =>
      have hb := hp b (by simp)
      have ht : ∀ r ∈ rs,0<r := fun r hr => hp r (by simp [hr])
      have h := component_aux_length_le (a*b) b rs hb ht
      simp only [componentWeights,runDefect,List.map_cons,List.sum_cons] at h ⊢
      omega

noncomputable def deletionRunScore (rs : List ℕ) : ℝ :=
  ((rs.sum-(longRuns rs).sum:ℕ):ℝ)*(f 3+4*rs.sum)+
    ((longRuns rs).map (fun r : ℕ => Hrun (rs.sum:ℝ) (r:ℝ))).sum+
    ((bridgeWeightsAux 0 0 rs).map (fun r : ℕ => f r)).sum

lemma large_insertion_comparison (n d : ℕ) (P : ℝ) (hn : 9 ≤ n) (hd : 1 ≤ d)
    (hcoarse : 2*((n:ℝ)-2)*d ≤ P)
    (hfine : 2*d < n-5 → f (n-1:ℕ) + (d:ℝ)*((n:ℝ)-2*d-5) ≤ P) :
    f (n-1:ℕ) < P := by
  have hnR : (9:ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  by_cases hcase : 2*d < n-5
  · have h := hfine hcase
    have ht : (0:ℝ) < (n:ℝ)-2*d-5 := by
      have hh : (2:ℝ)*d+5 < n := by
        exact_mod_cast (show 2*d+5 < n by omega)
      linarith
    have hp := mul_pos (show (0:ℝ)<d by linarith) ht
    linarith
  · have hdhigh : (n:ℝ)-5 ≤ 2*d := by
      have hh : (n:ℝ) ≤ 2*d+5 := by exact_mod_cast (show n ≤ 2*d+5 by omega)
      linarith
    have hpow := logb_nat_ge_eight_upper (n-1) (by omega)
    rw [Nat.cast_sub (show 1≤n by omega)] at hpow
    norm_num at hpow
    have hn1R : (0:ℝ) ≤ (n:ℝ)-1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hpow hn1R
    have hco := mul_le_mul_of_nonneg_left hdhigh (show 0≤(n:ℝ)-2 by linarith)
    unfold f
    rw [Nat.cast_sub (show 1≤n by omega)]
    norm_num
    nlinarith [sq_nonneg ((n:ℝ)-9)]

private lemma h_step_lower {m r : ℝ} (hr : 2 ≤ r) (hrm : r ≤ m) :
    (6*Real.logb 2 3-8)*m+(4-3*Real.logb 2 3)*r ≤
      f ((r+1)*(r+2)/2)-f (r*(r+1)/2) +
        (2*m-r)*(f (r+1)-f r)-f r-(f 3+4*m) := by
  have hb : 0 < r+1 := by linarith
  have hab : r+1 ≤ r*(r+1)/2 := by nlinarith
  have hmerge := f_merge_lower hb hab
  have htri : r*(r+1)/2+(r+1)=(r+1)*(r+2)/2 := by ring
  rw [htri] at hmerge
  have hinc := f_increment_lower hr
  have hcoef : 0 ≤ 2*m-r+1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hinc hcoef
  change _ ≤ _ + _ - _ - (3*Real.logb 2 3+4*m)
  nlinarith

private lemma nonadj_phi_ge_linear (rs : List ℕ) (hp : ∀ r ∈ rs,0<r) :
    nonadjLinear (fun n : ℕ => f n) rs ≤
      ((nonadjacentWeights rs).map (fun n : ℕ => f n)).sum := by
  induction rs with
  | nil => simp [nonadjLinear,nonadjacentWeights]
  | cons a rs ih =>
    have ha := hp a (by simp)
    have ht : ∀ r ∈ rs,0<r := fun r hr => hp r (by simp [hr])
    have hs : ((rs.drop 1).map (fun b : ℕ => f a+f b)).sum ≤
        ((rs.drop 1).map (fun b : ℕ => f (a*b:ℕ))).sum := by
      apply List.sum_le_sum
      intro b hb
      exact f_product_lower a b ha (ht b (List.mem_of_mem_drop hb))
    change ((rs.drop 1).map (fun b : ℕ => f a+f b)).sum+nonadjLinear (fun n : ℕ => f n) rs ≤ _
    simpa only [nonadjacentWeights,List.map_append,List.sum_append,List.map_map,
      Function.comp_def] using add_le_add hs (ih ht)

private lemma f_nat_lower (r : ℕ) (hr : 1 ≤ r) : 2*((r : ℝ)-1) ≤ f r := by
  by_cases he : r=1
  · simp [he, f_one]
  · apply f_real_lower
    exact_mod_cast (show 2 ≤ r by omega)

private lemma f_choose_two_lower (r : ℕ) (hr : 2 ≤ r) :
    2*((r : ℝ)-1)*((r : ℝ)-2) ≤ f (r.choose 2) := by
  by_cases he : r=2
  · norm_num [he, f_one]
  by_cases he3 : r=3
  · subst r
    norm_num [f]
    have h := logb_three_bounds
    linarith
  have hr4 : (4 : ℝ) ≤ r := by exact_mod_cast (show 4 ≤ r by omega)
  have ha := f_real_lower (r:=r/2) (by linarith)
  have hb := f_real_lower (r:=(r:ℝ)-1) (by linarith)
  rw [Nat.cast_choose_two, show (r:ℝ)*((r:ℝ)-1)/2=((r:ℝ)/2)*((r:ℝ)-1) by ring, f_mul]
  have hma := mul_le_mul_of_nonneg_left ha (show 0 ≤ (r:ℝ)-1 by linarith)
  have hmb := mul_le_mul_of_nonneg_left hb (show 0 ≤ (r:ℝ)/2 by positivity)
  nlinarith

lemma f_add_super_nat (a b : ℕ) : f a + f b ≤ f ((a+b : ℕ)) := by
  by_cases ha : a=0
  · simp [ha,f_zero]
  by_cases hb : b=0
  · simp [hb,f_zero]
  have haR : (0:ℝ)<a := by exact_mod_cast Nat.pos_of_ne_zero ha
  have hbR : (0:ℝ)<b := by exact_mod_cast Nat.pos_of_ne_zero hb
  rcases le_total (a:ℝ) b with hab | hba
  · have h := f_merge_lower haR hab
    rw [add_comm (b:ℝ) (a:ℝ)] at h
    simp only [Nat.cast_add]
    linarith
  · have h := f_merge_lower hbR hba
    simp only [Nat.cast_add]
    linarith

private lemma jensen_nat_list_at_least (ws : List ℕ) (A : ℝ) (hw : ws ≠ [])
    (hA : (ws.length:ℝ) ≤ A) (hAE : A ≤ ws.sum) :
    A*Real.logb 2 (A/ws.length) ≤ (ws.map (fun n : ℕ => f n)).sum := by
  have hc : (0:ℝ)<ws.length := by exact_mod_cast List.length_pos_iff_ne_nil.mpr hw
  have hA0 : 0<A := hc.trans_le hA
  have hratio : 1 ≤ A/ws.length := (le_div_iff₀ hc).mpr (by simpa using hA)
  have hlog0 := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hratio
  have hratio2 := div_le_div_of_nonneg_right hAE hc.le
  have hlog := Real.logb_le_logb_of_le (b:=2) (by norm_num) (div_pos hA0 hc) hratio2
  have hmul1 := mul_le_mul_of_nonneg_left hlog hA0.le
  have hmul2 := mul_le_mul_of_nonneg_right hAE (hlog0.trans hlog)
  exact (hmul1.trans hmul2).trans (jensen_list_nat ws hw)

private lemma component_jensen_bound (rs : List ℕ) (hp : ∀ r ∈ rs,0<r) (hlen : 3≤rs.length) :
    ((rs.sum-1:ℕ):ℝ)*Real.logb 2 (((rs.sum-1:ℕ):ℝ)/((runDefect rs:ℝ)+1)) ≤
      ((componentWeights rs).map (fun n : ℕ => f n)).sum := by
  have hdef := runDefect_eq rs hp
  have hm : 3≤rs.sum := by omega
  have hc0 := component_nonempty rs (by omega)
  have hcn := List.length_pos_iff_ne_nil.mpr hc0
  have hcle := component_length_le rs hp
  have he := adjacent_sum_lower rs hp (by omega)
  rw [←component_sum] at he
  let E : ℝ := ((componentWeights rs).sum:ℝ)
  let c : ℝ := ((componentWeights rs).length:ℝ)
  let A : ℝ := ((rs.sum-1:ℕ):ℝ)
  let D : ℝ := (runDefect rs:ℝ)+1
  have hc : 0<c := by dsimp [c]; exact_mod_cast hcn
  have hA : 0<A := by dsimp [A]; exact_mod_cast (show 0<rs.sum-1 by omega)
  have hD : 0<D := by dsimp [D]; positivity
  have hcD : c≤D := by
    dsimp [c,D]
    exact_mod_cast (show (componentWeights rs).length≤runDefect rs+1 by omega)
  have hDA : D≤A := by
    dsimp [D,A]
    exact_mod_cast (show runDefect rs+1≤rs.sum-1 by omega)
  have hAE : A≤E := by dsimp [A,E]; exact_mod_cast he
  have hratio : A/D≤E/c := by
    apply (div_le_div_iff₀ hD hc).mpr
    exact (mul_le_mul_of_nonneg_left hcD hA.le).trans (mul_le_mul_of_nonneg_right hAE hD.le)
  have hbase : 1≤A/D := (le_div_iff₀ hD).mpr (by simpa using hDA)
  have hlog0 : 0≤Real.logb 2 (A/D) := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hbase
  have hlog := Real.logb_le_logb_of_le (b:=2) (by norm_num) (div_pos hA hD) hratio
  have hmul1 := mul_le_mul_of_nonneg_left hlog hA.le
  have hmul2 := mul_le_mul_of_nonneg_right hAE (hlog0.trans hlog)
  have hj := jensen_list_nat (componentWeights rs) hc0
  change E*Real.logb 2 (E/c) ≤ _ at hj
  exact (hmul1.trans hmul2).trans hj

private lemma pair_phi_formula (rs : List ℕ) :
    ((pairWeights rs).map (fun n : ℕ => f n)).sum =
      (rs.map (fun r : ℕ => ((rs.sum:ℝ)-r)*f r)).sum := by
  induction rs with
  | nil => simp [pairWeights]
  | cons a rs ih =>
    simp only [pairWeights,List.map_append,List.sum_append,first_pair_phi,ih,
      List.sum_cons,List.map_cons,Nat.cast_add,add_sub_cancel_left]
    have he : (fun r : ℕ => (((a:ℝ)+rs.sum)-r)*f r) =
        (fun r : ℕ => (a:ℝ)*f r+((rs.sum:ℝ)-r)*f r) := by
      funext r
      ring
    rw [he,List.sum_map_add,List.sum_map_mul_left]
    ring

private lemma h_step_pos {m r : ℝ} (hr : 2 ≤ r) (hrm : r ≤ m) :
    0 < f ((r+1)*(r+2)/2)-f (r*(r+1)/2) +
      (2*m-r)*(f (r+1)-f r)-f r-(f 3+4*m) := by
  have hlower := h_step_lower hr hrm
  have hlog := logb_three_bounds
  have hm : 0 < m := by linarith
  have hcoef : 0 < 3*Real.logb 2 3-4 := by linarith
  have hc : 4-3*Real.logb 2 3 < 0 := by linarith
  have hcomp := mul_le_mul_of_nonpos_left hrm hc.le
  nlinarith [mul_pos hm hcoef]

private lemma nonadj_phi_lower_sum (rs : List ℕ) (hp : ∀ r ∈ rs,0<r) (hlen : 2≤rs.length) :
    ((rs.length:ℝ)-3)*(rs.map (fun r : ℕ => f r)).sum ≤
      ((nonadjacentWeights rs).map (fun n : ℕ => f n)).sum := by
  cases rs with
  | nil => simp at hlen
  | cons a rs =>
    rcases List.eq_nil_or_concat' rs with h | ⟨ts,b,h⟩
    · subst rs
      simp at hlen
    · subst rs
      have hlin := nonadj_phi_ge_linear (a::(ts++[b])) hp
      rw [nonadjLinear_formula] at hlin
      have ha := f_nonneg_nat a
      have hb := f_nonneg_nat b
      simp only [List.length_cons,List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one,
        List.map_cons,List.map_append,List.map_singleton,List.sum_cons,List.sum_append,
        List.sum_singleton,List.length_nil,List.map_nil,List.sum_nil,Nat.cast_zero,zero_add,add_zero,zero_mul,mul_zero]
      nlinarith

private lemma sum_f_run_lower (rs : List ℕ) (hp : ∀ r ∈ rs,0<r) :
    2*((rs.sum:ℝ)-rs.length) ≤ (rs.map (fun r : ℕ => f r)).sum := by
  have hlin : ∀ ts : List ℕ, (ts.map (fun r : ℕ => 2*((r:ℝ)-1))).sum =
      2*((ts.sum:ℝ)-ts.length) := by
    intro ts
    simp only [mul_sub, mul_one, sub_eq_add_neg, List.sum_map_add,
      List.sum_map_mul_left, List.map_const', List.sum_replicate, nsmul_eq_mul,
      ← Nat.cast_list_sum]
    ring
  rw [←hlin]
  apply List.sum_le_sum
  intro r hr
  exact f_nat_lower r (hp r hr)

private lemma component_aux_lower (acc prev : ℕ) (rs : List ℕ) :
    f acc + ((adjacentWeights (prev::rs)).map (fun n : ℕ => f n)).sum ≤
      ((componentWeightsAux acc prev rs).map (fun n : ℕ => f n)).sum := by
  induction rs generalizing acc prev with
  | nil => simp [componentWeightsAux,adjacentWeights]
  | cons r rs ih =>
    simp only [adjacentWeights,List.map_cons,List.sum_cons]
    by_cases hp : prev=1
    · rw [componentWeightsAux,if_pos hp]
      have h := ih (acc+prev*r) r
      have hadd := f_add_super_nat acc (prev*r)
      linarith
    · rw [componentWeightsAux,if_neg hp]
      simp only [List.map_cons,List.sum_cons]
      have h := ih (prev*r) r
      linarith

private lemma run_term_coarse (m r : ℕ) (hr : 1 ≤ r) (hrm : r ≤ m) :
    2*((m:ℝ)-2)*((r:ℝ)-1) ≤ f (r.choose 2)+((m:ℝ)-r)*f r := by
  by_cases he : r=1
  · simp [he,f_one,f_zero]
  have hr2 : 2≤r := by omega
  have h1 := f_choose_two_lower r hr2
  have h2 := f_nat_lower r hr
  have hrmR : (r:ℝ)≤m := by exact_mod_cast hrm
  have hh := mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hrmR)
  nlinarith

private lemma nonadj_defect_lower (rs : List ℕ) (hp : ∀ r ∈ rs,0<r) (hlen : 3≤rs.length) :
    2*((rs.sum:ℝ)-rs.length)*((rs.length:ℝ)-3) ≤
      ((nonadjacentWeights rs).map (fun n : ℕ => f n)).sum := by
  have h1 := nonadj_phi_lower_sum rs hp (by omega)
  have h2 := sum_f_run_lower rs hp
  have hlenR : (3:ℝ)≤rs.length := by exact_mod_cast hlen
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0≤(rs.length:ℝ)-3 by linarith)
  nlinarith

private lemma component_lower (rs : List ℕ) :
    ((adjacentWeights rs).map (fun n : ℕ => f n)).sum ≤
      ((componentWeights rs).map (fun n : ℕ => f n)).sum := by
  cases rs with
  | nil => simp [adjacentWeights,componentWeights]
  | cons a rs =>
    cases rs with
    | nil => simp [adjacentWeights,componentWeights]
    | cons b rs =>
      simpa [adjacentWeights,componentWeights] using component_aux_lower (a*b) b rs

private lemma Hrun_step {m r : ℝ} (hr : 2 ≤ r) (hrm : r ≤ m) :
    0<Hrun m r-Hrun m (r-1)-(f 3+4*m) := by
  have h := h_step_pos hr hrm
  unfold Hrun
  rw [show r-1+1=r by ring,show r-1+2=r+1 by ring]
  nlinarith

private lemma run_grouping_lower (rs : List ℕ) :
    ((sameRunWeights rs).map (fun n : ℕ => f n)).sum +
      ((pairWeights rs).map (fun n : ℕ => f n)).sum ≤ runPhiInsertion rs := by
  rw [pair_nonadjacent_decomposition]
  unfold runPhiInsertion collisionWeights
  simp only [List.map_append,List.sum_append]
  have h := component_lower rs
  linarith

private lemma Hrun_lower (m r : ℕ) (hr : 2 ≤ r) (hrm : r ≤ m) :
    (r:ℝ)*(f 3+4*m)+((6*Real.logb 2 3-8)*m+6-6*Real.logb 2 3) ≤ Hrun m r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases he : r=2
    · subst r; norm_num only [Nat.cast_ofNat]; rw [Hrun_two]
    have hr3 : 3 ≤ r := by omega
    have hi := ih (r-1) (by omega) (by omega) (by omega)
    have hs := Hrun_step (m:=(m:ℝ)) (r:=(r:ℝ)) (by exact_mod_cast hr) (by exact_mod_cast hrm)
    rw [Nat.cast_sub (by omega : 1 ≤ r),Nat.cast_one] at hi
    nlinarith

lemma run_fine_insertion_bound (rs : List ℕ) (hp : ∀ r ∈ rs,0<r) (hlen : 3≤rs.length) :
    f (rs.sum-1:ℕ)+(runDefect rs:ℝ)*((rs.sum:ℝ)-2*runDefect rs-5) ≤ runPhiInsertion rs := by
  have hdef := runDefect_eq rs hp
  have hdefR : (runDefect rs:ℝ)+(rs.length:ℝ)=(rs.sum:ℝ) := by exact_mod_cast hdef
  have hdEq : (rs.sum:ℝ)-rs.length=(runDefect rs:ℝ) := by exact Eq.symm (eq_sub_of_add_eq hdefR)
  have hnon := nonadj_defect_lower rs hp hlen
  rw [hdEq] at hnon
  have hcomp := component_jensen_bound rs hp hlen
  have hpos : (0:ℝ)<(rs.sum-1:ℕ) := by exact_mod_cast (show 0<rs.sum-1 by omega)
  have hdpos : (0:ℝ)<(runDefect rs:ℝ)+1 := by positivity
  rw [Real.logb_div hpos.ne' hdpos.ne'] at hcomp
  have hlog := logb_nat_add_one_le (runDefect rs)
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  have hf : f (rs.sum-1:ℕ)-((rs.sum-1:ℕ):ℝ)*runDefect rs ≤
      ((componentWeights rs).map (fun n : ℕ => f n)).sum := by
    change ((rs.sum-1:ℕ):ℝ)*Real.logb 2 ((rs.sum-1:ℕ):ℝ)-
      ((rs.sum-1:ℕ):ℝ)*runDefect rs ≤ _
    nlinarith
  have hs : 0≤((sameRunWeights rs).map (fun n : ℕ => f n)).sum := by
    apply List.sum_nonneg
    intro t ht
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp ht
    exact f_nonneg_nat n
  have hm : 1≤rs.sum := by omega
  rw [Nat.cast_sub hm,Nat.cast_one] at hf
  have hprod := congrArg (fun t : ℝ => (runDefect rs:ℝ)*t) hdefR
  rw [Nat.cast_sub hm,Nat.cast_one]
  unfold runPhiInsertion collisionWeights
  simp only [List.map_append,List.sum_append]
  nlinarith

lemma deletion_abstract_bridge_gap (m : ℕ) (us ws : List ℕ) (hm : 2 ≤ m)
    (hu : us ≠ []) (hp : ∀ u ∈ us,2 ≤ u ∧ u ≤ m) (hU : us.sum ≤ m)
    (hc : ws.length=us.length+1) (hS : m+us.sum+us.length+1 ≤ ws.sum) :
    4*(m:ℝ)^2+3*m*Real.logb 2 3+f ((m:ℝ)+1) <
      ((m-us.sum:ℕ):ℝ)*(f 3+4*m)+(us.map (fun u : ℕ => Hrun (m:ℝ) (u:ℝ))).sum+
        (ws.map (fun n : ℕ => f n)).sum := by
  have hq : 1 ≤ us.length := List.length_pos_iff_ne_nil.mpr hu
  have hU2 : 2*us.length ≤ us.sum := by
    have h : ∀ vs : List ℕ,(∀ u∈vs,2 ≤ u)→2*vs.length ≤ vs.sum := by
      intro vs hv
      induction vs with
      | nil => simp
      | cons u vs ih =>
        have hu2 := hv u (by simp)
        have ht : ∀ v∈vs,2 ≤ v := fun v hv' => hv v (by simp [hv'])
        simp only [List.length_cons,List.sum_cons]
        have hi := ih ht
        omega
    exact h us (fun u hu' => (hp u hu').1)
  have hw : ws ≠ [] := by intro he; rw [he] at hc; simp at hc
  have hlen : (ws.length:ℝ) ≤ (m:ℝ)+3*us.length+1 := by
    exact_mod_cast (show ws.length ≤ m+3*us.length+1 by omega)
  have hsum : (m:ℝ)+3*us.length+1 ≤ ws.sum := by
    exact_mod_cast (show m+3*us.length+1 ≤ ws.sum by omega)
  have hj := jensen_nat_list_at_least ws ((m:ℝ)+3*us.length+1) hw hlen hsum
  rw [hc,Nat.cast_add,Nat.cast_one] at hj
  have hgap := short_run_jensen_gap m us.length hm hq
  have hsumH : (us.sum:ℝ)*(f 3+4*m)+(us.length:ℝ)*
      ((6*Real.logb 2 3-8)*m+6-6*Real.logb 2 3) ≤ (us.map (fun u : ℕ => Hrun (m:ℝ) (u:ℝ))).sum := by
    have hh : ∀ vs : List ℕ,(∀ u∈vs,2 ≤ u ∧ u ≤ m)→
        (vs.sum:ℝ)*(f 3+4*m)+(vs.length:ℝ)*
          ((6*Real.logb 2 3-8)*m+6-6*Real.logb 2 3) ≤ (vs.map (fun u : ℕ => Hrun (m:ℝ) (u:ℝ))).sum := by
      intro vs hv
      induction vs with
      | nil => simp
      | cons u vs ih =>
        have ht : ∀ v∈vs,2 ≤ v ∧ v ≤ m := fun v hv' => hv v (by simp [hv'])
        have hhead := Hrun_lower m u (hv u (by simp)).1 (hv u (by simp)).2
        have hi := ih ht
        simp only [List.sum_cons,List.length_cons,List.map_cons,Nat.cast_add,Nat.cast_one,List.sum_cons]
        nlinarith
    exact hh us hp
  rw [Nat.cast_sub hU]
  have hf3 : f 3=3*Real.logb 2 3 := rfl
  rw [hf3] at hsumH ⊢
  nlinarith

lemma run_coarse_insertion_bound (rs : List ℕ) (hp : ∀ r ∈ rs, 0<r) :
    2*((rs.sum:ℝ)-2)*((rs.sum:ℝ)-rs.length) ≤ runPhiInsertion rs := by
  have hgroup := run_grouping_lower rs
  rw [same_run_phi_formula,pair_phi_formula] at hgroup
  have hsum : (rs.map (fun r : ℕ => 2*((rs.sum:ℝ)-2)*((r:ℝ)-1))).sum ≤
      (rs.map (fun r : ℕ => f (r.choose 2)+((rs.sum:ℝ)-r)*f r)).sum := by
    apply List.sum_le_sum
    intro i hi
    exact run_term_coarse rs.sum i (hp i hi) (List.single_le_sum (fun a _ => Nat.zero_le a) i hi)
  rw [List.sum_map_add] at hsum
  have hlin : ∀ (ts : List ℕ) (M:ℝ),
      (ts.map (fun r : ℕ => M*((r:ℝ)-1))).sum = M*((ts.sum:ℝ)-ts.length) := by
    intro ts M
    simp only [mul_sub, mul_one, sub_eq_add_neg, List.sum_map_add,
      List.sum_map_mul_left, List.map_const', List.sum_replicate, nsmul_eq_mul,
      ← Nat.cast_list_sum]
    ring
  rw [hlin] at hsum
  exact hsum.trans hgroup

end D5.S3.Entropy.TwoDeletionRunEntropyBounds
