/- GID: D5/S1/Digit/Infinite/ResetCodebookFinite
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/ResetCodebookFinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite reset families retain actual sources and a common strict margin. -/

import D5.S1.Digit.Infinite.ResetCodebookGrowth
import Mathlib.Analysis.SpecificLimits.Basic
local notation "g_bounds" => And.intro (And.left (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra)) (And.left (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra)))
local notation "g_relation" => (And.left D5.S1.Digit.Infinite.SixWindowForcing.algebra)
local notation "g_eq" => (And.left (And.right (And.right (And.right D5.S1.Digit.Infinite.OddColorThreeSource.golden_relations))))
local notation "t_sq" => (And.right (And.right (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra))))
local notation "t_linear" => (And.left (And.right (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra))))
local notation "Vertex" => fun (lang : Set (ℤ → Bool)) (n : ℕ) =>
  {v : Fin n → Bool // ∃ w∈lang, ∃ i : ℤ, D5.S1.Digit.Infinite.ResetCodebook.Transfer.history n w i=v}
local notation "resetFloor" => D5.S1.Digit.Infinite.ResetCodebook.Statement.B
local notation "totalWeight" => D5.S1.Digit.Infinite.ResetCodebook.Statement.weight
set_option autoImplicit false
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open scoped Topology
namespace D5.S1.Digit.Infinite.ResetCodebook
-- This conditional finite-memory bound does not construct an auxiliary state system.
theorem common_memory_cutoff (K : ℕ) (height eps : ℝ)
    (hh : 0 < height) (heps : 0 < eps) :
    ∃ n : ℕ, K ≤ n ∧ height*rho^n < eps := by
  have hr0 : 0 ≤ rho := pow_nonneg (by have := g_bounds; linarith) 6
  have hr1 : rho < 1 := pow_lt_one₀ (by have := g_bounds; linarith)
    (by have := g_bounds; linarith) (by decide)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul height
  have hev : ∀ᶠ n : ℕ in Filter.atTop, height*rho^n < eps :=
    (tendsto_order.mp ht).2 eps (by simpa using heps)
  obtain ⟨m,hm⟩ := Filter.eventually_atTop.mp hev
  exact ⟨max K m,le_max_left _ _,hm _ (le_max_right _ _)⟩
end D5.S1.Digit.Infinite.ResetCodebook
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Words.Powers (wordPower wordPower_succ length_wordPower)
namespace D5.S1.Digit.Infinite.ResetCodebook
noncomputable def step (low : Bool) (D : ℝ) := A low+rho*D
noncomputable def run (low : Bool) (a : Return) (D : ℝ) :=
  (step low)^[a.val.1] (chi^a.val.2*D)
theorem parameters (low : Bool) :
    0 < rho ∧ rho < 1 ∧ 0 < chi ∧ chi < 1 ∧
    0 < h low ∧ h low < E low ∧ E low ≤ 1/4 := by
  have hg := g_bounds
  have hg0 : 0 < g := by linarith
  have hg1 : g < 1 := by linarith
  have hr : 0 < rho ∧ rho < 1 := ⟨pow_pos hg0 _,pow_lt_one₀ hg0.le hg1 (by decide)⟩
  have hc : 0 < chi ∧ chi < 1 := ⟨pow_pos hg0 _,pow_lt_one₀ hg0.le hg1 (by decide)⟩
  refine ⟨hr.1,hr.2,hc.1,hc.2,?_,?_,?_⟩
  all_goals cases low <;> simp only [h,E,coord,if_true,if_false,Bool.false_eq_true,t_sq,center] <;> linarith
private theorem side_map (low : Bool) (D : ℝ) : wordScalar (sideWord low) (coord low D)=coord low (step low D) := by
  cases low
  · exact U_map D
  · exact V_map D
private theorem step_interval (low : Bool) (D : ℝ) (hD : 0 ≤ D) (hh : D ≤ h low) :
    D ≤ step low D ∧ step low D ≤ h low := by
  have hp := parameters low
  unfold step A
  constructor <;> nlinarith [hp.1,hp.2.1]
private theorem step_iterate_bounds (low : Bool) (m : ℕ) (D : ℝ) (hD : 0 ≤ D) (hh : D ≤ h low) :
    D ≤ (step low)^[m] D ∧ (step low)^[m] D ≤ h low := by
  induction m with
  | zero => exact ⟨le_rfl,hh⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have hb := step_interval low _ (hD.trans ih.1) ih.2
    exact ⟨ih.1.trans hb.1,hb.2⟩
private theorem side_power_scalar (low : Bool) (m : ℕ) (D : ℝ) :
    wordScalar (wordPower m (sideWord low)) (coord low D)=coord low ((step low)^[m] D) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [wordPower_succ,wordScalar_append,ih,side_map,Function.iterate_succ_apply']
private theorem C_power_scalar (low : Bool) (r : ℕ) (D : ℝ) :
    wordScalar (wordPower r C) (coord low D)=coord low (chi^r*D) := by
  induction r with
  | zero => simp [wordPower,wordScalar]
  | succ r ih =>
    rw [wordPower_succ,wordScalar_append,ih,C_map,pow_succ]
    congr 1
    ring
private theorem return_scalar (low : Bool) (a : Return) (D : ℝ) :
    wordScalar (returnWord low a) (coord low D)=coord low (run low a D) := by
  unfold returnWord run
  rw [wordScalar_append,C_power_scalar,side_power_scalar]
private theorem coord_bound (low : Bool) (D : ℝ) (hD : 0 ≤ D) (hD1 : D ≤ 1/4) :
    |coord low D-c0| ≤ 1/4 := by
  cases low <;> simp only [coord,if_true,if_false,Bool.false_eq_true,abs_le] <;> constructor <;> linarith
private theorem side_cost (low : Bool) (D : ℝ) (hD : 0 ≤ D) (hD1 : D ≤ 1/4) :
    wordCost (sideWord low) sixColor (coord low D) ≤ max (lambda-g^2*D) (lambda-rho) := by
  cases low
  · exact U_cost D hD hD1
  · exact V_cost D hD hD1
private theorem side_power_cost (low : Bool) (m : ℕ) (D : ℝ)
    (hD : 0 ≤ D) (hh : D ≤ h low) :
    wordCost (wordPower m (sideWord low)) (wordPower m sixColor) (coord low D)
      ≤ max (lambda-g^2*D) (lambda-rho) := by
  induction m with
  | zero => exact auto_positive.le.trans (le_max_right _ _)
  | succ m ih =>
    rw [wordPower_succ,wordPower_succ,cost_append _ _ _ _ (by cases low <;> rfl),side_power_scalar]
    apply max_le _ ih
    have hi := step_iterate_bounds low m D hD hh
    have hp := parameters low
    apply (side_cost low _ (hD.trans hi.1) (hi.2.trans (hp.2.2.2.2.2.1.le.trans hp.2.2.2.2.2.2))).trans
    apply max_le_max _ le_rfl
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hi.1 (sq_nonneg g)) _
private theorem C_power_cost (low : Bool) (r : ℕ) (D : ℝ)
    (hD : 0 ≤ D) (hh : D ≤ h low) :
    wordCost (wordPower r C) (wordPower r twentyColor) (coord low D) ≤ lambda-rho := by
  induction r with
  | zero => exact auto_positive.le
  | succ r ih =>
    rw [wordPower_succ,wordPower_succ,cost_append _ _ _ _ (by rfl),C_power_scalar]
    apply max_le _ ih
    have hp:=parameters low
    have hpw : 0 ≤ chi^r ∧ chi^r ≤ 1 := ⟨pow_nonneg hp.2.2.1.le r,pow_le_one₀ hp.2.2.1.le hp.2.2.2.1.le⟩
    apply C_cost _ (coord_bound low _ (mul_nonneg hpw.1 hD) _)
    calc
      chi^r*D ≤ D := mul_le_of_le_one_left hD hpw.2
      _ ≤ h low := hh
      _ ≤ E low := hp.2.2.2.2.2.1.le
      _ ≤ 1/4 := hp.2.2.2.2.2.2
private theorem return_cost (low : Bool) (a : Return) (D : ℝ)
    (hD : 0 ≤ D) (hh : D ≤ h low) :
    wordCost (returnWord low a) (returnColors a) (coord low D)
      ≤ max (lambda-g^2*chi^a.val.2*D) (lambda-rho) := by
  unfold returnWord returnColors
  rw [cost_append _ _ _ _ (by rw [length_wordPower,length_wordPower]; cases low <;> rfl),C_power_scalar]
  have hp:=parameters low
  have hpw : 0 ≤ chi^a.val.2 ∧ chi^a.val.2 ≤ 1 :=
    ⟨pow_nonneg hp.2.2.1.le _,pow_le_one₀ hp.2.2.1.le hp.2.2.2.1.le⟩
  apply max_le
  · have hi := side_power_cost low a.val.1 (chi^a.val.2*D) (mul_nonneg hpw.1 hD)
      ((mul_le_of_le_one_left hD hpw.2).trans hh)
    simpa only [mul_assoc] using hi
  · exact (C_power_cost low a.val.2 D hD hh).trans (le_max_right _ _)
end D5.S1.Digit.Infinite.ResetCodebook
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Words.Powers (wordPower wordPower_succ length_wordPower)
namespace D5.S1.Digit.Infinite.ResetCodebook
noncomputable def execute (low : Bool) (as : List Return) (D : ℝ) := as.foldl (fun x a => run low a x) D
private noncomputable def controls (low : Bool) : List Return → ℝ → ℝ
  | [], _ => 0
  | a::as, D => max (lambda-g^2*chi^a.val.2*D) (controls low as (run low a D))
private theorem listWord_append (low : Bool) (as bs : List Return) :
    listWord low (as++bs)=listWord low as++listWord low bs := List.flatMap_append
private theorem listColors_append (as bs : List Return) :
    listColors (as++bs)=listColors as++listColors bs := List.flatMap_append
theorem run_bounds (low : Bool) (a : Return) (D : ℝ) (hD : 0 ≤ D) (hh : D ≤ h low) :
    0 ≤ run low a D ∧ run low a D ≤ h low := by
  have hp := parameters low
  have hpow : 0 ≤ chi^a.val.2 ∧ chi^a.val.2 ≤ 1 :=
    ⟨pow_nonneg hp.2.2.1.le _,pow_le_one₀ hp.2.2.1.le hp.2.2.2.1.le⟩
  have hi:=step_iterate_bounds low a.val.1 (chi^a.val.2*D)
    (mul_nonneg hpow.1 hD) ((mul_le_of_le_one_left hD hpow.2).trans hh)
  exact ⟨(mul_nonneg hpow.1 hD).trans hi.1,hi.2⟩
theorem execute_bounds (low : Bool) (as : List Return) (D : ℝ) (hD : 0 ≤ D) (hh : D ≤ h low) :
    0 ≤ execute low as D ∧ execute low as D ≤ h low := by
  induction as generalizing D with
  | nil => exact ⟨hD,hh⟩
  | cons a as ih => exact ih _ (run_bounds low a D hD hh).1 (run_bounds low a D hD hh).2
private theorem list_scalar (low : Bool) (as : List Return) (D : ℝ) :
    wordScalar (listWord low as.reverse) (coord low D)=coord low (execute low as D) := by
  induction as generalizing D with
  | nil => rfl
  | cons a as ih =>
    rw [List.reverse_cons,listWord_append,wordScalar_append]
    simp only [listWord,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    change wordScalar (listWord low as.reverse) (wordScalar (returnWord low a) (coord low D))=_
    rw [return_scalar,ih]
    rfl
private theorem list_lengths (low : Bool) (as : List Return) : (listWord low as).length=(listColors as).length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    change (returnWord low a++listWord low as).length=(returnColors a++listColors as).length
    simp only [List.length_append,ih]
    unfold returnWord returnColors
    simp only [List.length_append,length_wordPower]
    cases low <;> rfl
private theorem all_departure_cost (low : Bool) (as : List Return) (D : ℝ)
    (hD : 0 ≤ D) (hh : D ≤ h low) :
    wordCost (listWord low as.reverse) (listColors as.reverse) (coord low D)
      ≤ max (controls low as D) (lambda-rho) := by
  induction as generalizing D with
  | nil => exact auto_positive.le.trans (le_max_right _ _)
  | cons a as ih =>
    rw [List.reverse_cons,listWord_append,listColors_append,cost_append _ _ _ _ (list_lengths _ _)]
    simp only [listWord,listColors,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    change max (wordCost (listWord low as.reverse) (listColors as.reverse)
      (wordScalar (returnWord low a) (coord low D)))
      (wordCost (returnWord low a) (returnColors a) (coord low D))≤_
    rw [return_scalar]
    have hr:=run_bounds low a D hD hh
    have ht:=return_cost low a D hD hh
    have hi:=ih _ hr.1 hr.2
    change max _ _ ≤ max (max _ _) _
    apply max_le
    · exact hi.trans (max_le_max (le_max_right _ _) le_rfl)
    · exact ht.trans (max_le_max (le_max_left _ _) le_rfl)
end D5.S1.Digit.Infinite.ResetCodebook
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Words.Powers (wordPower wordPower_succ length_wordPower)
namespace D5.S1.Digit.Infinite.ResetCodebook
private def anchorReturn : Return := ⟨(1,1),by decide,by decide⟩
private theorem anchor_word (low : Bool) : returnWord low anchorReturn=sideWord low++C := by
  simp [returnWord,anchorReturn]
private theorem anchor_color : returnColors anchorReturn=sixColor++twentyColor := by
  simp [returnColors,anchorReturn]
private theorem tail_scalar (low : Bool) : kappa (literalTail low)=coord low (X low) := by
  rw [(literal_tail_spec low).2.2.2]
  unfold tailWord
  rw [wordScalar_append,wordScalar_append]
  have he : wordScalar (if low then [] else [fiveLabel]) 0=coord low (E low) := by
    cases low <;> norm_num [wordScalar,branch,offset,fiveLabel,coord,E,List.foldr] <;> ring
  rw [he,C_power_scalar,side_map]
  congr 1
  unfold step X
  ring
private theorem h_small (low : Bool) : 1/16<h low := by
  have hg:=g_bounds
  cases low <;> simp only [h,if_true,if_false,Bool.false_eq_true] <;> linarith
private theorem X_bounds (low : Bool) : 0<X low ∧ A low<X low ∧ X low<h low := by
  obtain ⟨hr,hr1,hc,hc1,hh,hhE,hE⟩:=parameters low
  have ha : 0<A low := by unfold A; exact mul_pos (by linarith) hh
  have hE0 : 0<E low := hh.trans hhE
  have hcsmall := (small_powers 20).2
  have hhsmall := h_small low
  have hcp : chi^3 ≤ chi := by
    simpa using pow_le_pow_of_le_one hc.le hc1.le (show 1 ≤ 3 by decide)
  have hce : chi^3*E low < h low := by
    have hm:=mul_le_mul_of_nonneg_right hcp hE0.le
    have hm2:=mul_le_mul_of_nonneg_left hE hc.le
    have hcsmall2 : chi ≤ 1 / 1099511627776 := by
      norm_num [chi] at hcsmall ⊢
      exact hcsmall
    have hcquarter : chi ≤ 1 / 4 := hcsmall2.trans (by norm_num)
    nlinarith
  have hp:=mul_pos hr (mul_pos (pow_pos hc 3) hE0)
  unfold X
  refine ⟨by linarith,by linarith,?_⟩
  unfold A
  nlinarith
noncomputable def initial (low anchor : Bool) := if anchor then Y low else X low
private theorem anchor_scalar (low : Bool) :
    wordScalar (sideWord low++C) (coord low (X low))=coord low (Y low) := by
  rw [wordScalar_append,C_map,side_map]
  congr 1
  unfold step Y
  ring
private theorem initial_bounds (low anchor : Bool) : 0 ≤ initial low anchor ∧ initial low anchor ≤ h low := by
  cases anchor
  · exact ⟨(X_bounds low).1.le,(X_bounds low).2.2.le⟩
  · have hr:=run_bounds low anchorReturn (X low) (X_bounds low).1.le (X_bounds low).2.2.le
    have he : run low anchorReturn (X low)=Y low := by simp [run,anchorReturn,Function.iterate_one,step,Y,mul_assoc]
    simpa [initial,he] using hr
private theorem full_scalar (low anchor : Bool) (exec : List Return) :
    wordScalar (sourcePrefix low anchor exec) (kappa (literalTail low))=
      coord low (run low anchorReturn (execute low exec (initial low anchor))) := by
  rw [tail_scalar]
  unfold sourcePrefix
  rw [wordScalar_append,wordScalar_append]
  have he : wordScalar (if anchor then sideWord low++C else []) (coord low (X low))=coord low (initial low anchor) := by
    cases anchor
    · rfl
    · exact anchor_scalar low
  rw [he,list_scalar,←anchor_word,return_scalar]
private noncomputable def fullBudget (low anchor : Bool) (exec : List Return) :=
  max (max (lambda-g^2*chi*execute low exec (initial low anchor)) (lambda-rho))
    (max (max (controls low exec (initial low anchor)) (lambda-rho))
      (if anchor then max (lambda-g^2*chi*X low) (lambda-rho) else 0))
private theorem full_length (low anchor : Bool) (exec : List Return) :
    (sourcePrefix low anchor exec).length=(colors anchor exec).length := by
  unfold sourcePrefix colors
  simp only [List.length_append,list_lengths]
  cases anchor <;> cases low <;> rfl
private theorem full_departure_cost (low anchor : Bool) (exec : List Return) :
    wordCost (sourcePrefix low anchor exec) (colors anchor exec) (kappa (literalTail low))
      ≤ fullBudget low anchor exec := by
  have ht:=X_bounds low
  have hi:=initial_bounds low anchor
  have hr:=execute_bounds low exec _ hi.1 hi.2
  have hs:=(return_cost low anchorReturn _ hr.1 hr.2)
  simp only [anchorReturn,returnWord,returnColors,D5.S1.Words.Powers.wordPower_one,pow_one] at hs
  have hm:=all_departure_cost low exec _ hi.1 hi.2
  have ha : wordCost (if anchor then sideWord low++C else [])
      (if anchor then sixColor++twentyColor else []) (kappa (literalTail low)) ≤
      (if anchor then max (lambda-g^2*chi*X low) (lambda-rho) else 0) := by
    cases anchor
    · exact le_rfl
    · rw [tail_scalar,←anchor_word,←anchor_color]
      simpa only [anchorReturn,pow_one,if_true] using return_cost low anchorReturn _ ht.1.le ht.2.2.le
  have hl : (sideWord low++C).length=(sixColor++twentyColor).length := by cases low <;> rfl
  have hall : (sideWord low++C++listWord low exec.reverse).length=
      (sixColor++twentyColor++listColors exec.reverse).length := by simp only [List.length_append,hl,list_lengths]
  unfold sourcePrefix colors
  rw [cost_append _ _ _ _ hall,cost_append _ _ _ _ hl]
  have he : wordScalar (if anchor then sideWord low++C else []) (kappa (literalTail low))=
      coord low (initial low anchor) := by
    rw [tail_scalar]
    cases anchor
    · rfl
    · exact anchor_scalar low
  rw [he,list_scalar]
  unfold fullBudget
  exact (max_le_max (max_le_max hs hm) ha).trans (le_of_eq (max_assoc _ _ _))
-- One literal address per side supplies every departure coordinate and all the
-- same terminal futures. The bound here is not yet the single high-side budget.
private theorem actual_all_slots (anchor : Bool) (exec : List Return) :
    ∃ src : Bool → LegalDigits, ∀ low,
      stateAddress false (src low) ∧ finiteTail (src low) ∧
      addressPrefix (sourcePrefix low anchor exec) (src low) (literalTail low) ∧
      kappa (src low)=coord low (run low anchorReturn (execute low exec (initial low anchor))) ∧
      wordCost (sourcePrefix low anchor exec) (colors anchor exec) (kappa (literalTail low))
        ≤ fullBudget low anchor exec := by
  obtain ⟨src,hs⟩:=actual_pair anchor exec
  exact ⟨src,fun low => ⟨(hs low).1,(hs low).2.1,(hs low).2.2.1,
    (hs low).2.2.2.trans (full_scalar low anchor exec),full_departure_cost low anchor exec⟩⟩
end D5.S1.Digit.Infinite.ResetCodebook
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Words.Powers (wordPower wordPower_succ length_wordPower)
namespace D5.S1.Digit.Infinite.ResetCodebook
noncomputable def closedRun (low : Bool) (m r : ℕ) (D : ℝ) := h low-rho^m*(h low-chi^r*D)
private theorem step_iterate (low : Bool) (m : ℕ) (D : ℝ) :
    (step low)^[m] D=h low-rho^m*(h low-D) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply',ih]; unfold step A; rw [pow_succ]; ring
theorem run_closed (low : Bool) (a : Return) (D : ℝ) : run low a D=closedRun low a.val.1 a.val.2 D :=
  step_iterate low a.val.1 (chi^a.val.2*D)
theorem reset_lifts (M : ℕ) (z : ℝ) (hz : A false ≤ z) :
    resetFloor M ≤ closedRun false M 1 z := by
  have hp:=parameters false
  have ha:=mul_nonneg (pow_nonneg hp.1.le M) hp.2.2.1.le
  unfold Statement.B closedRun
  simp only [pow_one]
  nlinarith
private theorem return_difference (low : Bool) (a : Return) (x y : ℝ) :
    run low a x-run low a y=rho^a.val.1*chi^a.val.2*(x-y) := by
  rw [run_closed,run_closed]; unfold closedRun; ring
private def actualWeight (a : Return) := 6*a.val.1+20*a.val.2
private theorem return_slope (a : Return) : rho^a.val.1*chi^a.val.2=g^(actualWeight a) := by
  unfold rho chi actualWeight
  rw [←pow_mul,←pow_mul,←pow_add]
end D5.S1.Digit.Infinite.ResetCodebook
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
namespace D5.S1.Digit.Infinite.ResetCodebook
private theorem side_order : h false ≤ h true ∧ E false ≤ E true := by
  have hg := g_bounds
  constructor
  · simp only [h, Bool.false_eq_true, if_false, if_true]
    linarith
  · simp only [E, Bool.false_eq_true, if_false, if_true, center, t_sq]
    linarith
private theorem A_order : A false ≤ A true := by
  have hp := parameters false
  unfold A
  exact mul_le_mul_of_nonneg_left side_order.1 (by linarith [hp.2.1])
private theorem X_order : X false ≤ X true := by
  have hp := parameters false
  have hc := mul_nonneg hp.1.le (pow_nonneg hp.2.2.1.le 3)
  have he := mul_le_mul_of_nonneg_left side_order.2 hc
  unfold X
  nlinarith [A_order]
private theorem run_order (a : Return) (x y : ℝ) (hxy : x ≤ y) :
    run false a x ≤ run true a y := by
  have hp := parameters false
  have hr : 0 ≤ rho^a.val.1 ∧ rho^a.val.1 ≤ 1 :=
    ⟨pow_nonneg hp.1.le _,pow_le_one₀ hp.1.le hp.2.1.le⟩
  have hh := mul_nonneg (sub_nonneg.mpr hr.2) (sub_nonneg.mpr side_order.1)
  have hc := mul_nonneg hr.1 (pow_nonneg hp.2.2.1.le a.val.2)
  have hd := mul_nonneg hc (sub_nonneg.mpr hxy)
  rw [run_closed,run_closed]
  unfold closedRun
  nlinarith
private theorem initial_order (anchor : Bool) : initial false anchor ≤ initial true anchor := by
  cases anchor
  · exact X_order
  · have hh := run_order anchorReturn _ _ X_order
    simpa [initial,run,anchorReturn,step,Y,mul_assoc] using hh
private theorem execute_order (as : List Return) (x y : ℝ) (hxy : x ≤ y) :
    execute false as x ≤ execute true as y := by
  induction as generalizing x y with
  | nil => exact hxy
  | cons a as ih => exact ih _ _ (run_order a x y hxy)
private theorem controls_order (as : List Return) (x y : ℝ) (hxy : x ≤ y) :
    controls true as y ≤ controls false as x := by
  induction as generalizing x y with
  | nil => exact le_rfl
  | cons a as ih =>
    change max _ _ ≤ max _ _
    apply max_le_max
    · apply sub_le_sub_left
      exact mul_le_mul_of_nonneg_left hxy
        (mul_nonneg (sq_nonneg g) (pow_nonneg (parameters false).2.2.1.le _))
    · exact ih _ _ (run_order a x y hxy)
private theorem fullBudget_order (anchor : Bool) (exec : List Return) :
    fullBudget true anchor exec ≤ fullBudget false anchor exec := by
  have he := execute_order exec _ _ (initial_order anchor)
  have hc := controls_order exec _ _ (initial_order anchor)
  have hs := mul_nonneg (sq_nonneg g) (parameters false).2.2.1.le
  unfold fullBudget
  apply max_le_max
  · exact max_le_max (sub_le_sub_left (mul_le_mul_of_nonneg_left he hs) _) le_rfl
  · apply max_le_max (max_le_max hc le_rfl)
    cases anchor
    · exact le_rfl
    · exact max_le_max (sub_le_sub_left (mul_le_mul_of_nonneg_left X_order hs) _) le_rfl
private theorem run_floor (low : Bool) (a : Return) (D : ℝ) (hD : 0 ≤ D) (hh : D ≤ h low) :
    A low ≤ run low a D := by
  have hm : a.val.1 ≠ 0 := by have := a.property.1; omega
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hp := parameters low
  have hi := step_iterate_bounds low m (chi^a.val.2*D)
    (mul_nonneg (pow_nonneg hp.2.2.1.le _) hD)
    ((mul_le_of_le_one_left hD (pow_le_one₀ hp.2.2.1.le hp.2.2.2.1.le)).trans hh)
  unfold run
  rw [hm,Function.iterate_succ_apply']
  change A low ≤ A low+rho*((step low)^[m] (chi^a.val.2*D))
  have hm0 := mul_nonneg hp.1.le ((mul_nonneg (pow_nonneg hp.2.2.1.le _) hD).trans hi.1)
  exact le_add_of_nonneg_right hm0
private theorem initial_floor (low anchor : Bool) : A low ≤ initial low anchor := by
  cases anchor
  · exact (X_bounds low).2.1.le
  · have hp := initial_bounds low false
    have hf := run_floor low anchorReturn (X low) hp.1 hp.2
    simpa [initial,run,anchorReturn,step,Y,mul_assoc] using hf
theorem execute_floor (low : Bool) (as : List Return) (D : ℝ)
    (hD : A low ≤ D) (hh : D ≤ h low) : A low ≤ execute low as D := by
  have hA : 0 ≤ A low := by
    unfold A
    exact mul_nonneg (by linarith [(parameters low).2.1]) (parameters low).2.2.2.2.1.le
  induction as generalizing D with
  | nil => exact hD
  | cons a as ih =>
    exact ih _ (run_floor low a D (hA.trans hD) hh)
      (run_bounds low a D (hA.trans hD) hh).2
end D5.S1.Digit.Infinite.ResetCodebook
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
namespace D5.S1.Digit.Infinite.ResetCodebook
theorem weak_run (K : ℕ) (d : ℝ) (a : Return) (as : List Return) (D : ℝ) :
    Statement.weak K d (a::as) D ↔
      a.val.2 ≤ K ∧ (a.val.2=K → d ≤ D) ∧ Statement.weak K d as (run false a D) := by
  change (a.val.2 ≤ K ∧ (a.val.2 = K → d ≤ D) ∧
    Statement.weak K d as (closedRun false a.val.1 a.val.2 D)) ↔
    (a.val.2 ≤ K ∧ (a.val.2 = K → d ≤ D) ∧ Statement.weak K d as (run false a D))
  rw [run_closed]
theorem weak_gain (K : ℕ) (d delta x y : ℝ) (as : List Return)
    (hd : 0 < delta) (hxy : x+delta ≤ y) (hw : Statement.weak K d as x) :
    Statement.weak K (d+delta*g^(totalWeight as)) as y := by
  have hg := g_bounds
  have hg0 : 0 ≤ g := by linarith
  have hg1 : g ≤ 1 := by linarith
  induction as generalizing x y delta with
  | nil => trivial
  | cons a as ih =>
    rw [weak_run] at hw ⊢
    refine ⟨hw.1,?_,?_⟩
    · intro hk
      have hx := hw.2.1 hk
      have hpow := pow_le_one₀ hg0 hg1 (n := totalWeight (a::as))
      nlinarith [mul_le_mul_of_nonneg_left hpow hd.le]
    · have hda : 0 < delta*g^(actualWeight a) := mul_pos hd (pow_pos (by linarith) _)
      have hdiff := return_difference false a y x
      rw [return_slope] at hdiff
      have hmul := mul_le_mul_of_nonneg_left hxy (pow_nonneg hg0 (actualWeight a))
      have hnext : run false a x+delta*g^(actualWeight a) ≤ run false a y := by
        nlinarith
      have ht := ih _ _ _ hda hnext hw.2.2
      have he : d+(delta*g^(actualWeight a))*g^(totalWeight as)=d+delta*g^(totalWeight (a::as)) := by
        simp only [Statement.weight,actualWeight,List.map_cons,List.sum_cons,pow_add]
        ring
      exact he ▸ ht
theorem weak_append (K : ℕ) (q : ℝ) (as bs : List Return) (z : ℝ)
    (ha : Statement.weak K q as z)
    (hb : Statement.weak K q bs (execute false as z)) :
    Statement.weak K q (as++bs) z := by
  induction as generalizing z with
  | nil => exact hb
  | cons a as ih =>
      rw [weak_run] at ha
      rw [List.cons_append,weak_run]
      exact ⟨ha.1,ha.2.1,ih _ ha.2.2 hb⟩
theorem finite_reset_weak_state
    (anchor : Bool) (K M N : ℕ) (d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M)
    (hreset : initial false anchor < Statement.B M)
    (vs : List (List Return))
    (hvs : ∀ v∈vs, Statement.weight v=N ∧ Statement.weak K d v (initial false anchor))
    (z : ℝ) (hz : A false ≤ z) (hh : z ≤ h false) :
    Statement.weak K (d+(Statement.B M-initial false anchor)*g^N)
      ((vs.map (fun v => Statement.reset M hM::v)).flatten) z := by
  have hp := parameters false
  have hA : 0 ≤ A false := by
    unfold A
    exact mul_nonneg (by linarith [hp.2.1]) hp.2.2.2.2.1.le
  induction vs generalizing z with
  | nil => trivial
  | cons v vs ih =>
      have hv := hvs v (by simp)
      have hr := run_bounds false (Statement.reset M hM) z (hA.trans hz) hh
      have hresetz : Statement.B M ≤ run false (Statement.reset M hM) z := by
        rw [run_closed]
        exact reset_lifts M z hz
      have hweak := weak_gain K d (Statement.B M-initial false anchor)
        (initial false anchor) (run false (Statement.reset M hM) z) v
        (sub_pos.mpr hreset) (by linarith) hv.2
      have hweight : Statement.weight v=N := hv.1
      rw [hweight] at hweak
      have hw : Statement.weak K (d+(Statement.B M-initial false anchor)*g^N)
          (Statement.reset M hM::v) z := by
        rw [weak_run]
        refine ⟨by change 1 ≤ K; omega,?_,hweak⟩
        intro heq
        change 1=K at heq
        omega
      have hexf := execute_floor false (Statement.reset M hM::v) z hz hh
      have hexh := (execute_bounds false (Statement.reset M hM::v) z (hA.trans hz) hh).2
      have htail := ih (fun x hx => hvs x (by simp [hx])) _ hexf hexh
      simp only [List.map_cons,List.flatten_cons]
      exact weak_append K _ _ _ z hw htail
private theorem reset_concatenation_guard (anchor : Bool) (K M N : ℕ) (d : ℝ) (hK : 2 ≤ K)
    (hM : 1 ≤ M) (hreset : initial false anchor < resetFloor M)
    (vs : List (List Return)) (hvs : ∀ v∈vs, Statement.weight v=N ∧ Statement.weak K d v (initial false anchor)) :
    Statement.weak K (d+(resetFloor M-initial false anchor)*g^N)
      ((vs.map (fun v => Statement.reset M hM::v)).flatten) (initial false anchor) := by
  exact finite_reset_weak_state anchor K M N d hK hM hreset vs hvs
    (initial false anchor) (initial_floor false anchor) (initial_bounds false anchor).2
theorem A_nonneg : 0 ≤ A false := by
  have hp := parameters false
  unfold A
  exact mul_nonneg (by linarith [hp.2.1]) hp.2.2.2.2.1.le
private theorem auto_nonneg (K : ℕ) : 0 ≤ Statement.autoCost K :=
  auto_positive.le.trans ((le_max_right _ _).trans (le_max_right _ _))
private theorem controls_budget (K : ℕ) (d gain b : ℝ) (as : List Return) (D : ℝ)
    (hK : 2 ≤ K) (hb : b=lambda-g^2*chi^K*d)
    (hD : A false ≤ D) (hh : D ≤ h false)
    (hw : Statement.weak K (d+gain) as D) :
    controls false as D ≤ max (Statement.autoCost K) (b-g^2*chi^K*gain) := by
  have hp := parameters false
  induction as generalizing D with
  | nil => exact (auto_nonneg K).trans (le_max_left _ _)
  | cons a as ih =>
    rw [weak_run] at hw
    change max _ _ ≤ _
    apply max_le
    · by_cases hk : a.val.2=K
      · have hc := hw.2.1 hk
        have hm := mul_le_mul_of_nonneg_left hc
          (mul_nonneg (sq_nonneg g) (pow_nonneg hp.2.2.1.le K))
        apply le_trans _ (le_max_right _ _)
        rw [hk,hb]
        nlinarith
      · have har : a.val.2 ≤ K-1 := by omega
        have hpow := pow_le_pow_of_le_one hp.2.2.1.le hp.2.2.2.1.le har
        have hpa := mul_le_mul_of_nonneg_right hpow A_nonneg
        have hpd := mul_le_mul_of_nonneg_left hD (pow_nonneg hp.2.2.1.le a.val.2)
        have hm := mul_le_mul_of_nonneg_left (hpa.trans hpd) (sq_nonneg g)
        have hc : lambda-g^2*chi^a.val.2*D ≤ lambda-g^2*chi^(K-1)*A false := by
          nlinarith
        exact hc.trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
    · exact ih _ (run_floor false a D (A_nonneg.trans hD) hh)
        (run_bounds false a D (A_nonneg.trans hD) hh).2 hw.2.2
private theorem fullBudget_guard (anchor : Bool) (K : ℕ) (d gain b : ℝ) (as : List Return)
    (hK : 2 ≤ K) (hb : b=lambda-g^2*chi^K*d)
    (hw : Statement.weak K (d+gain) as (initial false anchor)) :
    ∀ low, fullBudget low anchor as ≤ max (Statement.autoCost K) (b-g^2*chi^K*gain) := by
  have hp := parameters false
  have hf := execute_floor false as _ (initial_floor false anchor) (initial_bounds false anchor).2
  have hc := controls_budget K d gain b as _ hK hb
    (initial_floor false anchor) (initial_bounds false anchor).2 hw
  have hpow : chi^(K-1) ≤ chi := by
    simpa using pow_le_pow_of_le_one hp.2.2.1.le hp.2.2.2.1.le (show 1 ≤ K-1 by omega)
  have hs : lambda-g^2*chi*execute false as (initial false anchor) ≤ Statement.autoCost K := by
    have hm1 := mul_le_mul_of_nonneg_right hpow A_nonneg
    have hm2 := mul_le_mul_of_nonneg_left hf hp.2.2.1.le
    have hm3 := mul_le_mul_of_nonneg_left (hm1.trans hm2) (sq_nonneg g)
    have hst : lambda-g^2*chi*execute false as (initial false anchor) ≤
        lambda-g^2*chi^(K-1)*A false := by nlinarith
    exact hst.trans ((le_max_left _ _).trans (le_max_right _ _))
  have ha : lambda-rho ≤ Statement.autoCost K := (le_max_right _ _).trans (le_max_right _ _)
  have hbs : fullBudget false anchor as ≤ max (Statement.autoCost K) (b-g^2*chi^K*gain) := by
    unfold fullBudget
    apply max_le
    · exact (max_le hs ha).trans (le_max_left _ _)
    · apply max_le
      · exact max_le hc (ha.trans (le_max_left _ _))
      · cases anchor
        · exact (auto_nonneg K).trans (le_max_left _ _)
        · apply le_trans _ (le_max_left _ _)
          exact max_le (le_max_left _ _) ha
  intro low
  cases low
  · exact hbs
  · exact (fullBudget_order anchor as).trans hbs
-- The source pair is fully actual. The only supplied hypotheses here are the
-- strengthened scalar guard and automatic slack; no per-side budget is assumed.
end D5.S1.Digit.Infinite.ResetCodebook
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
namespace D5.S1.Digit.Infinite.ResetCodebook
private theorem rho_chi_small : rho ≤ 1/4096 ∧ chi ≤ 1/1099511627776 := by
  constructor
  · have hh := (small_powers 6).2
    norm_num [rho] at hh ⊢
    exact hh
  · have hh := (small_powers 20).2
    norm_num [chi] at hh ⊢
    exact hh
private theorem A_gt_chi_h : chi*h false < A false := by
  have hp := parameters false
  have hsum : rho+chi < 1 := by linarith [rho_chi_small.1,rho_chi_small.2]
  have hm := mul_pos (by linarith : 0 < 1-rho-chi) hp.2.2.2.2.1
  unfold A
  nlinarith
private theorem automatic_strict (K : ℕ) (hK : 2 ≤ K) :
    Statement.autoCost K < lambda-g^2*chi^K*h false := by
  have hp := parameters false
  have hg := g_bounds
  have hg0 : 0 < g := by linarith
  have hg1 : g < 1 := by linarith
  have hfactor : 0 < g^2 := pow_pos hg0 _
  have hchie : chi^K ≤ chi^2 := pow_le_pow_of_le_one hp.2.2.1.le hp.2.2.2.1.le hK
  have hx := (X_bounds false).2.1
  have hcx : chi^2*h false < chi*X false := by
    have hh := mul_lt_mul_of_pos_left (A_gt_chi_h.trans hx) hp.2.2.1
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hchie hp.2.2.2.2.1.le
  have htop := mul_lt_mul_of_pos_left (hh.trans_lt hcx) hfactor
  have hlow : chi^K*h false < chi^(K-1)*A false := by
    have hm := mul_lt_mul_of_pos_left A_gt_chi_h (pow_pos hp.2.2.1 (K-1))
    have he : chi^K=chi^(K-1)*chi := by
      rw [←pow_succ]
      congr 1
      omega
    rw [he]
    nlinarith
  have hmid := mul_lt_mul_of_pos_left hlow hfactor
  have hchirho : chi ≤ rho := by
    simpa [chi,rho] using pow_le_pow_of_le_one hg0.le hg1.le (show 6 ≤ 20 by decide)
  have hkp : chi^K ≤ chi := by
    simpa using pow_le_pow_of_le_one hp.2.2.1.le hp.2.2.2.1.le (show 1 ≤ K by omega)
  have hh1 : h false < 1 := hp.2.2.2.2.2.1.trans_le (hp.2.2.2.2.2.2.trans (by norm_num))
  have hh0 : 0 ≤ h false := hp.2.2.2.2.1.le
  have hsq1 : g^2 < 1 := pow_lt_one₀ hg0.le hg1 (by decide)
  have hm1 := mul_lt_mul_of_pos_left hh1 (pow_pos hp.2.2.1 K)
  have hm2 := mul_le_mul_of_nonneg_left hm1.le hfactor.le
  have hm3 := mul_lt_mul_of_pos_right hsq1 (pow_pos hp.2.2.1 K)
  have hfinal : g^2*chi^K*h false < rho := by
    nlinarith
  unfold Statement.autoCost
  apply max_lt
  · nlinarith
  · apply max_lt <;> nlinarith
end D5.S1.Digit.Infinite.ResetCodebook

namespace D5.S1.Digit.Infinite.ResetCodebook
theorem reset_actual_family (anchor : Bool) (K M N : ℕ) (b d : ℝ)
    (hK : 2 ≤ K) (hM : 1 ≤ M)
    (hb : lambda-g^2*chi^K*h false < b)
    (hd : d=(lambda-b)/(g^2*chi^K))
    (hreset : max (X false) (Y false) < Statement.B M) :
    0 < Statement.actualEps anchor K M N b ∧ Statement.finiteActual anchor K M N b d hM := by
  have hp := parameters false
  have hg : 0 < g := by have := g_bounds; linarith
  have hfac : 0 < g^2*chi^K := mul_pos (pow_pos hg _) (pow_pos hp.2.2.1 _)
  have hbeq : b=lambda-g^2*chi^K*d := by
    have hdeq := (eq_div_iff (ne_of_gt hfac)).mp hd
    nlinarith
  have hinit : initial false anchor < resetFloor M := by
    cases anchor
    · exact (le_max_left _ _).trans_lt hreset
    · exact (le_max_right _ _).trans_lt hreset
  let gain := (resetFloor M-initial false anchor)*g^N
  have hgain : 0 < gain := mul_pos (sub_pos.mpr hinit) (pow_pos hg _)
  have hauto : Statement.autoCost K < b := (automatic_strict K hK).trans hb
  let eps := Statement.actualEps anchor K M N b
  have hepsEq : eps=min (b-Statement.autoCost K) (g^2*chi^K*gain)/2 := by
    simp only [eps,Statement.actualEps,gain,initial]
    ring
  have hgp : 0 < g^2*chi^K*gain := mul_pos hfac hgain
  have he : 0 < eps := by rw [hepsEq]; exact div_pos (lt_min (sub_pos.mpr hauto) hgp) (by norm_num)
  have heleft : 2*eps ≤ b-Statement.autoCost K := by
    rw [hepsEq]
    linarith [min_le_left (b-Statement.autoCost K) (g^2*chi^K*gain)]
  have heright : 2*eps ≤ g^2*chi^K*gain := by
    rw [hepsEq]
    linarith [min_le_right (b-Statement.autoCost K) (g^2*chi^K*gain)]
  have hbe : 0 < b-eps := by have := auto_nonneg K; linarith
  refine ⟨he,?_⟩
  intro vs hvs
  let exec := (vs.map (fun v => Statement.reset M hM::v)).flatten
  have hw : Statement.weak K (d+gain) exec (initial false anchor) :=
    reset_concatenation_guard anchor K M N d hK hM hinit vs (fun v hv => hvs v hv)
  have hbud : ∀ low, fullBudget low anchor exec ≤ b-2*eps := by
    intro low
    apply (fullBudget_guard anchor K d gain b exec hK hbeq hw low).trans
    apply max_le <;> linarith
  obtain ⟨src,hs⟩ := actual_all_slots anchor exec
  have hw' : Statement.weak K (d+(Statement.B M-initial false anchor)*g^N) exec (initial false anchor) := by
    simpa only [gain] using hw
  refine ⟨hw',src,?_⟩
  intro low
  have hc := ((hs low).2.2.2.2).trans (hbud low)
  refine ⟨(hs low).1,(hs low).2.1,(hs low).2.2.1,hc,?_⟩
  intro Q hQ
  obtain ⟨es,hlen,herr⟩ := actual_errors _ _ _ _ (hs low).2.2.1
    (full_length low anchor exec) b eps he hbe hc Q hQ
  exact ⟨fun p => es[p]?.getD 0,herr⟩
end D5.S1.Digit.Infinite.ResetCodebook
