/- GID: D5/S1/Digit/Infinite/ResetCodebookIndexed
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/ResetCodebookIndexed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bilateral reset concatenations satisfy caps and guarded high margins. -/

import D5.S1.Digit.Infinite.ResetCodebookFinite
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Set.Finite.List
import Mathlib.Topology.Order.MonotoneConvergence
local notation "g_bounds" => And.intro (And.left (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra)) (And.left (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra)))
local notation "g_relation" => (And.left D5.S1.Digit.Infinite.SixWindowForcing.algebra)
local notation "g_eq" => (And.left (And.right (And.right (And.right D5.S1.Digit.Infinite.OddColorThreeSource.golden_relations))))
local notation "t_sq" => (And.right (And.right (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra))))
local notation "t_linear" => (And.left (And.right (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra))))
local notation "Vertex" => fun (lang : Set (ℤ → Bool)) (n : ℕ) =>
  {v : Fin n → Bool // ∃ w∈lang, ∃ i : ℤ, D5.S1.Digit.Infinite.ResetCodebook.Transfer.history n w i=v}
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
namespace D5.S1.Digit.Infinite.ResetCodebook
end D5.S1.Digit.Infinite.ResetCodebook
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open scoped Topology
namespace D5.S1.Digit.Infinite.ResetCodebook
noncomputable def pastRec (w : ℤ→Bool) (i : ℤ) : ℕ→ℝ→ℝ
  | 0,z => z
  | n+1,z => Statement.f (w (i-1)) (pastRec w (i-1) n z)
noncomputable def stateRec (w : ℤ→Bool) (i : ℤ) := ⨆ n, pastRec w i n 0
private theorem f_mono (a : Bool) : Monotone (Statement.f a) := by
  have hp := parameters false
  cases a
  · intro x y hxy
    change A false+rho*x ≤ A false+rho*y
    linarith [mul_le_mul_of_nonneg_left hxy hp.1.le]
  · intro x y hxy
    exact mul_le_mul_of_nonneg_left hxy hp.2.2.1.le
private theorem f_interval (a : Bool) (z : ℝ) (hz : 0 ≤ z) (hh : z ≤ h false) :
    0 ≤ Statement.f a z ∧ Statement.f a z ≤ h false := by
  have hp := parameters false
  cases a
  · have hm := mul_nonneg hp.1.le hz
    change 0 ≤ A false+rho*z ∧ A false+rho*z ≤ h false
    refine ⟨by linarith [A_nonneg],?_⟩
    have hm2 := mul_le_mul_of_nonneg_left hh hp.1.le
    unfold A
    nlinarith
  · change 0 ≤ chi*z ∧ chi*z ≤ h false
    exact ⟨mul_nonneg hp.2.2.1.le hz,(mul_le_of_le_one_left hz hp.2.2.2.1.le).trans hh⟩
private theorem pastRec_interval (w : ℤ→Bool) (i : ℤ) (n : ℕ) (z : ℝ)
    (hz : 0 ≤ z) (hh : z ≤ h false) : 0 ≤ pastRec w i n z ∧ pastRec w i n z ≤ h false := by
  induction n generalizing i with
  | zero => exact ⟨hz,hh⟩
  | succ n ih => exact f_interval _ _ (ih (i-1)).1 (ih (i-1)).2
private theorem pastRec_increasing (w : ℤ→Bool) (i : ℤ) : Monotone (fun n => pastRec w i n 0) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing i with
  | zero => exact (f_interval _ 0 le_rfl (parameters false).2.2.2.2.1.le).1
  | succ n ih => exact f_mono _ (ih (i-1))
private theorem pastRec_bdd (w : ℤ→Bool) (i : ℤ) : BddAbove (Set.range (fun n => pastRec w i n 0)) := by
  refine ⟨h false,?_⟩
  rintro x ⟨n,rfl⟩
  exact (pastRec_interval w i n 0 le_rfl (parameters false).2.2.2.2.1.le).2
theorem stateRec_limit (w : ℤ→Bool) (i : ℤ) :
    Filter.Tendsto (fun n => pastRec w i n 0) Filter.atTop (nhds (stateRec w i)) :=
  tendsto_atTop_ciSup (pastRec_increasing w i) (pastRec_bdd w i)
theorem stateRec_interval (w : ℤ→Bool) (i : ℤ) : 0 ≤ stateRec w i ∧ stateRec w i ≤ h false := by
  constructor
  · exact le_ciSup (pastRec_bdd w i) 0
  · apply ciSup_le
    intro n
    exact (pastRec_interval w i n 0 le_rfl (parameters false).2.2.2.2.1.le).2
theorem stateRec_next (w : ℤ→Bool) (i : ℤ) : stateRec w (i+1)=Statement.f (w i) (stateRec w i) := by
  have hc : Continuous (Statement.f (w i)) := by
    cases hw : w i
    · change Continuous (fun z : ℝ => A false+rho*z)
      fun_prop
    · change Continuous (fun z : ℝ => chi*z)
      fun_prop
  have hleft := (stateRec_limit w (i+1)).comp (Filter.tendsto_add_atTop_nat 1)
  have hright := hc.continuousAt.tendsto.comp (stateRec_limit w i)
  have he : (fun n => pastRec w (i+1) (n+1) 0) = (fun n => Statement.f (w i) (pastRec w i n 0)) := by
    funext n
    simp only [pastRec,add_sub_cancel_right]
  change Filter.Tendsto (fun n => pastRec w (i+1) (n+1) 0) Filter.atTop (nhds (stateRec w (i+1))) at hleft
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright
end D5.S1.Digit.Infinite.ResetCodebook
set_option autoImplicit false
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
namespace D5.S1.Digit.Infinite.ResetCodebook
private theorem reset_family_cutoff (anchor : Bool) (K M N : ℕ) (b d : ℝ)
    (hK : 2 ≤ K) (hM : 1 ≤ M)
    (hb : lambda-g^2*chi^K*h false < b)
    (hd : d=(lambda-b)/(g^2*chi^K))
    (hreset : max (X false) (Y false) < Statement.B M) :
    0 < Statement.actualEps anchor K M N b ∧ Statement.finiteActual anchor K M N b d hM ∧
    ∃ n : ℕ, K ≤ n ∧ h false*rho^n < chi^(K-1)*(Statement.B M-initial false anchor)*g^N := by
  have hδ : 0 < Statement.B M-initial false anchor := by
    apply sub_pos.mpr
    cases anchor
    · exact (le_max_left _ _).trans_lt hreset
    · exact (le_max_right _ _).trans_lt hreset
  have hg : 0 < g := by have := g_bounds; linarith
  have hp := parameters false
  have he : 0 < chi^(K-1)*(Statement.B M-initial false anchor)*g^N :=
    mul_pos (mul_pos (pow_pos hp.2.2.1 _) hδ) (pow_pos hg _)
  have ha := reset_actual_family anchor K M N b d hK hM hb hd hreset
  exact ⟨ha.1,ha.2,common_memory_cutoff K (h false) _ hp.2.2.2.2.1 he⟩
end D5.S1.Digit.Infinite.ResetCodebook
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open scoped Topology
namespace D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ResetCodebook
/-- The index-explicit two-sided lower-memory graph used for the auxiliary language. -/
noncomputable def XMinus (K n : ℕ) (tau : ℝ) : Set (ℤ → Bool) :=
  {w | Statement.cap K w ∧
    ∀ i, Statement.high K w i → tau < D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n 0}
private lemma f_difference (a : Bool) (x y : ℝ) :
    Statement.f a x - Statement.f a y = (if a then chi else rho) * (x - y) := by
  cases a <;> simp [Statement.f] <;> ring
private lemma f_lipschitz (a : Bool) (x y : ℝ) :
    |Statement.f a x - Statement.f a y| ≤ rho * |x-y| := by
  have hr : 0 ≤ rho := by unfold rho; positivity
  have hc : 0 ≤ chi := by unfold chi; positivity
  rw [f_difference]
  cases a
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [abs_mul, abs_of_nonneg hr]
  · simp only [↓reduceIte]
    rw [abs_mul, abs_of_nonneg hc]
    have hχ : chi ≤ rho := by
      unfold chi rho
      have hg := g_bounds
      have h0 : 0 ≤ g := by linarith
      have h1 : g ≤ 1 := by linarith
      exact pow_le_pow_of_le_one h0 h1 (by decide)
    exact mul_le_mul_of_nonneg_right hχ (abs_nonneg (x-y))
private lemma pastRec_mono_z (w : ℤ → Bool) (i : ℤ) (n : ℕ) :
    Monotone (fun z : ℝ => D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n z) := by
  induction n generalizing i with
  | zero => exact monotone_id
  | succ n ih =>
      intro x y hxy
      change Statement.f (w (i - 1)) (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i - 1) n x) ≤
        Statement.f (w (i - 1)) (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i - 1) n y)
      exact D5.S1.Digit.Infinite.ResetCodebook.f_mono _ ((ih (i-1)) hxy)
private lemma pastRec_lipschitz (w : ℤ → Bool) (i : ℤ) (n : ℕ) (x y : ℝ) :
    |D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n x - D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n y| ≤ rho^n * |x-y| := by
  induction n generalizing i x y with
  | zero => simp [D5.S1.Digit.Infinite.ResetCodebook.pastRec]
  | succ n ih =>
      change |Statement.f (w (i - 1)) (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i - 1) n x) -
          Statement.f (w (i - 1)) (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i - 1) n y)| ≤ rho^(n+1) * |x-y|
      have hf := f_lipschitz (w (i - 1))
        (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i - 1) n x) (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i - 1) n y)
      have hh := ih (i-1) x y
      have hr : 0 ≤ rho := by unfold rho; positivity
      calc
        |Statement.f (w (i - 1)) (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i - 1) n x) -
            Statement.f (w (i - 1)) (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i - 1) n y)| ≤
            rho * |D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i - 1) n x - D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i - 1) n y| := hf
        _ ≤ rho * (rho^n * |x-y|) := mul_le_mul_of_nonneg_left hh hr
        _ = rho^(n+1) * |x-y| := by rw [pow_succ]; ring
private lemma pastRec_zero (w : ℤ → Bool) (i : ℤ) (z : ℝ) :
    D5.S1.Digit.Infinite.ResetCodebook.pastRec w i 0 z = z := by
  rw [D5.S1.Digit.Infinite.ResetCodebook.pastRec.eq_def]
private lemma pastRec_succ (w : ℤ → Bool) (i : ℤ) (n : ℕ) (z : ℝ) :
    D5.S1.Digit.Infinite.ResetCodebook.pastRec w i (n+1) z =
      Statement.f (w (i-1)) (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i-1) n z) := by
  rw [show n+1 = Nat.succ n by omega, D5.S1.Digit.Infinite.ResetCodebook.pastRec.eq_def]
private lemma pastRec_split (w : ℤ → Bool) (i : ℤ) (n k : ℕ) (z : ℝ) :
    D5.S1.Digit.Infinite.ResetCodebook.pastRec w i (n+k) z =
      D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i-(n:ℤ)) k z) := by
  induction n generalizing i k z with
  | zero =>
      simp only [Nat.zero_add]
      rw [pastRec_zero]
      simpa only [Int.ofNat_zero, sub_zero]
  | succ n ih =>
      calc
        D5.S1.Digit.Infinite.ResetCodebook.pastRec w i (n.succ+k) z =
            D5.S1.Digit.Infinite.ResetCodebook.pastRec w i ((n+k)+1) z := by congr 1 <;> omega
        _ = Statement.f (w (i-1)) (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i-1) (n+k) z) :=
          pastRec_succ w i (n+k) z
        _ = Statement.f (w (i-1))
            (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i-1) n (D5.S1.Digit.Infinite.ResetCodebook.pastRec w ((i-1)-(n:ℤ)) k z)) := by
          rw [ih (i-1) k z]
        _ = D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n.succ
            (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i-(n.succ:ℤ)) k z) := by
          rw [pastRec_succ]
          congr 2
          rw [Int.natCast_succ]
          ring
private lemma pastRec_interval_state (w : ℤ → Bool) (i : ℤ) (n : ℕ) :
    0 ≤ D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n 0 ∧ D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n 0 ≤ h false :=
  D5.S1.Digit.Infinite.ResetCodebook.pastRec_interval w i n 0 le_rfl (D5.S1.Digit.Infinite.ResetCodebook.parameters false).2.2.2.2.1.le
private lemma pastRec_le_stateRec (w : ℤ → Bool) (i : ℤ) (n : ℕ) :
    D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n 0 ≤ D5.S1.Digit.Infinite.ResetCodebook.stateRec w i := by
  exact le_ciSup (D5.S1.Digit.Infinite.ResetCodebook.pastRec_bdd w i) n
private lemma pastRec_state_gap (w : ℤ → Bool) (i : ℤ) (n : ℕ) :
    D5.S1.Digit.Infinite.ResetCodebook.stateRec w i - D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n 0 ≤ h false * rho^n := by
  have hupper : D5.S1.Digit.Infinite.ResetCodebook.stateRec w i ≤ D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n 0 + h false * rho^n := by
    unfold D5.S1.Digit.Infinite.ResetCodebook.stateRec
    apply ciSup_le
    intro m
    by_cases hmn : m ≤ n
    · have hmono := D5.S1.Digit.Infinite.ResetCodebook.pastRec_increasing w i hmn
      have hrho : 0 ≤ rho := by unfold rho; positivity
      have hnon : 0 ≤ h false * rho^n :=
        mul_nonneg (D5.S1.Digit.Infinite.ResetCodebook.parameters false).2.2.2.2.1.le (pow_nonneg hrho n)
      exact hmono.trans (le_add_of_nonneg_right hnon)
    · have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnm
      subst m
      rw [pastRec_split]
      have hx := pastRec_interval_state w (i - (n : ℤ)) k
      have hL := pastRec_lipschitz w i n
        (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i - (n : ℤ)) k 0) 0
      have hrho : 0 ≤ rho := by unfold rho; positivity
      have hr : 0 ≤ rho^n := pow_nonneg hrho n
      have hdiff : |D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i - (n : ℤ)) k 0 - 0| ≤ h false := by
        simpa [sub_zero, abs_of_nonneg hx.1] using hx.2
      have habs : |D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n
          (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i - (n : ℤ)) k 0) - D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n 0| ≤
          rho^n * h false := by
        apply hL.trans
        exact mul_le_mul_of_nonneg_left hdiff hr
      have horder : D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n 0 ≤
          D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n (D5.S1.Digit.Infinite.ResetCodebook.pastRec w (i - (n : ℤ)) k 0) := by
        apply pastRec_mono_z w i n
        exact hx.1
      rw [abs_of_nonneg (sub_nonneg.mpr horder)] at habs
      nlinarith [habs]
  linarith
/-- A common positive state margin survives a single indexed finite-memory cutoff. -/
theorem aux_mem_XMinus
    (K n : ℕ) (tau eps : ℝ) (w : ℤ → Bool)
    (hcap : Statement.cap K w)
    (hmargin : ∀ i, Statement.high K w i → tau + eps ≤ D5.S1.Digit.Infinite.ResetCodebook.stateRec w i)
    (heps : 0 < eps) (hcut : h false * rho^n < eps) :
    w ∈ XMinus K n tau := by
  refine ⟨hcap, fun i hi => ?_⟩
  have hg := pastRec_state_gap w i n
  have hstate := hmargin i hi
  have hnon : D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n 0 ≤ D5.S1.Digit.Infinite.ResetCodebook.stateRec w i := pastRec_le_stateRec w i n
  nlinarith
end D5.S1.Digit.Infinite.ResetCodebook.Coding
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open scoped Topology
namespace D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ResetCodebook
lemma past_eq_pastRec (w : ℤ → Bool) (i : ℤ) (n : ℕ) (z : ℝ) :
    Statement.past w i n z = pastRec w i n z := by
  induction n generalizing i z with
  | zero => simp [Statement.past, pastRec]
  | succ n ih =>
      unfold Statement.past
      have hcoerce : ∀ m : ℕ,
          (do let a ← List.range m; pure (a:ℤ)) =
            (List.range m).map (fun a : ℕ => (a:ℤ)) := by
        intro m
        induction (List.range m) with
        | nil => rfl
        | cons a l ih =>
            change [(a:ℤ)] ++ (do let b ← l; pure (b:ℤ)) =
              [(a:ℤ)] ++ l.map (fun b : ℕ => (b:ℤ))
            rw [ih]
      rw [hcoerce (n+1)]
      simp only [List.map_map]
      change ((List.range (n+1)).map
          (fun j : ℕ => w (i-(n+1:ℤ)+(j:ℤ)))).foldl
          (fun D a => Statement.f a D) z = _
      rw [show n+1=n.succ by omega, List.range_succ, List.map_append,
        List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      have hp : (fun j : ℕ => w (i - ((n+1 : ℕ) : ℤ) + (j : ℤ))) =
          (fun j : ℕ => w ((i-1) - (n : ℤ) + (j : ℤ))) := by
        funext j
        congr 1
        rw [Int.natCast_add, Int.natCast_one]
        ring
      have hl : i - ((n+1 : ℕ) : ℤ) + (n : ℤ) = i - 1 := by
        rw [Int.natCast_add, Int.natCast_one]
        ring
      have hmap :
          List.map (fun j : ℕ => w (i - ((n:ℤ)+1) + (j:ℤ))) (List.range n) =
            List.map (fun j : ℕ => w ((i-1) - (n:ℤ) + (j:ℤ))) (List.range n) := by
        apply List.map_congr_left
        intro j hj
        congr 1
        ring
      have hl' : i - ((n:ℤ)+1) + (n:ℤ) = i - 1 := by ring
      rw [hl', hmap]
      rw [pastRec_succ, ← ih]
      have hpast :
          List.foldl (fun D a => Statement.f a D) z
              (List.map (fun j : ℕ => w ((i-1) - (n:ℤ) + (j:ℤ))) (List.range n)) =
            Statement.past w (i-1) n z := by
        unfold Statement.past
        rw [hcoerce n]
        simp only [List.map_map]
        congr 1
      exact congrArg (Statement.f (w (i-1))) hpast
lemma state_eq_stateRec (w : ℤ → Bool) (i : ℤ) :
    Statement.state w i = stateRec w i := by
  simp only [Statement.state, past_eq_pastRec, stateRec]
  rfl
lemma lowerLanguage_eq_XMinus (K n : ℕ) (d : ℝ) :
    Statement.lowerLanguage K n d = XMinus K n (chi^(K-1)*d) := by
  ext w
  simp only [Statement.lowerLanguage, XMinus, Set.mem_setOf_eq, past_eq_pastRec]
/-- Indexed forward intervals keep the start and end in the same realization. -/
private def slice (w : ℤ → Bool) (p : ℤ) (n : ℕ) : List Bool :=
  (List.range n).map (fun j : ℕ => w (p + (j : ℤ)))
private lemma slice_succ (w : ℤ → Bool) (p : ℤ) (n : ℕ) :
    slice w p (n+1) = slice w p n ++ [w (p+(n:ℤ))] := by
  simp [slice, List.range_succ]
private lemma stateRec_fold_slice (w : ℤ → Bool) (p : ℤ) (n : ℕ) :
    stateRec w (p+(n:ℤ)) =
      (slice w p n).foldl (fun z a => Statement.f a z) (stateRec w p) := by
  induction n with
  | zero => simp [slice]
  | succ n ih =>
      rw [Int.natCast_succ, ← add_assoc, stateRec_next, ih, slice_succ]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
private lemma slice_of_word (w : ℤ → Bool) (p : ℤ) (u : List Bool)
    (hu : ∀ j : Fin u.length, w (p+(j.val:ℤ)) = u[j.val]) :
    slice w p u.length = u := by
  apply List.ext_getElem
  · simp [slice]
  · intro j hj hj'
    unfold slice at hj
    unfold slice
    rw [List.getElem_map, List.getElem_range]
    exact hu ⟨j,hj'⟩
private lemma stateRec_fold_word (w : ℤ → Bool) (p : ℤ) (u : List Bool)
    (hu : ∀ j : Fin u.length, w (p+(j.val:ℤ)) = u[j.val]) :
    stateRec w (p+(u.length:ℤ)) =
      u.foldl (fun z a => Statement.f a z) (stateRec w p) := by
  rw [stateRec_fold_slice, slice_of_word w p u hu]
private lemma fold_true (n : ℕ) (z : ℝ) :
    (List.replicate n true).foldl (fun z a => Statement.f a z) z = chi^n*z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ]
      change (List.replicate n true).foldl _ (chi*z) = _
      rw [ih, pow_succ]
      ring
private lemma fold_false (n : ℕ) (z : ℝ) :
    (List.replicate n false).foldl (fun z a => Statement.f a z) z =
      (step false)^[n] z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ]
      change (List.replicate n false).foldl _ (step false z) = _
      rw [ih, Function.iterate_succ_apply]
private lemma fold_letters (as : List Return) (z : ℝ) :
    (Statement.letters as).foldl (fun z a => Statement.f a z) z =
      execute false as z := by
  induction as generalizing z with
  | nil => rfl
  | cons a as ih =>
      simp only [Statement.letters, List.flatMap_cons, List.foldl_append]
      rw [fold_true, fold_false]
      change (Statement.letters as).foldl _ (run false a z) = _
      rw [ih]
      rfl
private lemma cut_execution (w : ℤ → Bool) (p q : ℤ) (as : List Return)
    (hlen : q-p = (Statement.letters as).length)
    (hu : ∀ j : Fin (Statement.letters as).length,
      w (p+(j.val:ℤ)) = (Statement.letters as)[j.val]) :
    stateRec w q = execute false as (stateRec w p) := by
  have hq : q = p + ((Statement.letters as).length:ℤ) := by omega
  rw [hq, stateRec_fold_word w p (Statement.letters as) hu, fold_letters]
lemma letters_end_false (a : Return) (as : List Return) :
    ∃ u : List Bool, Statement.letters (a::as) = u ++ [false] := by
  induction as generalizing a with
  | nil =>
      obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero
        (show a.val.1 ≠ 0 by have := a.property.1; omega)
      refine ⟨List.replicate a.val.2 true ++ List.replicate m false, ?_⟩
      simp only [Statement.letters, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, hm]
      rw [show Nat.succ m = m+1 by omega, List.replicate_add]
      simp [List.append_assoc]
  | cons b as ih =>
      obtain ⟨u,hu⟩ := ih b
      refine ⟨(List.replicate a.val.2 true ++ List.replicate a.val.1 false) ++ u, ?_⟩
      change _ ++ Statement.letters (b::as) = _
      rw [hu]
      simp only [List.append_assoc]
private lemma cut_floor (w : ℤ → Bool) (p q : ℤ) (a : Return) (as : List Return)
    (hlen : q-p = (Statement.letters (a::as)).length)
    (hu : ∀ j : Fin (Statement.letters (a::as)).length,
      w (p+(j.val:ℤ)) = (Statement.letters (a::as))[j.val]) :
    A false ≤ stateRec w q := by
  obtain ⟨u,he⟩ := letters_end_false a as
  have hlen' : (Statement.letters (a::as)).length = u.length+1 := by
    rw [he, List.length_append]; simp
  have hw : w (q-1) = false := by
    have hlast := hu ⟨u.length, by omega⟩
    have hidx : p+(u.length:ℤ) = q-1 := by omega
    rw [hidx] at hlast
    simpa [he] using hlast
  have hstate := stateRec_next w (q-1)
  have hnon := (stateRec_interval w (q-1)).1
  have hp := parameters false
  simp only [sub_add_cancel, hw, Statement.f, Bool.false_eq_true, ↓reduceIte] at hstate
  rw [hstate]
  have hm := mul_nonneg hp.1.le hnon
  linarith
/-- Both the predecessor and current cut are obtained from the supplied typed segmentation. -/
private theorem concatenation_cut_guard
    (anchor : Bool) (K M N : ℕ) (d : ℝ) (hM : 1 ≤ M)
    (w : ℤ → Bool) (cuts : ℤ → ℤ) (v : ℤ → List Return)
    (hseg : ∀ i, v i ∈ Statement.codebook anchor K N d ∧
      cuts (i+1)-cuts i=(Statement.letters (Statement.reset M hM::v i)).length ∧
      ∀ j : Fin (Statement.letters (Statement.reset M hM::v i)).length,
        w (cuts i+(j.val:ℤ))=(Statement.letters (Statement.reset M hM::v i))[j.val]) :
    ∀ i, A false ≤ stateRec w (cuts i) ∧
      stateRec w (cuts (i+1)) = execute false (Statement.reset M hM::v i)
        (stateRec w (cuts i)) := by
  intro i
  have hprev := hseg (i-1)
  have hc := cut_floor w (cuts (i-1)) (cuts i) (Statement.reset M hM) (v (i-1))
    (by simpa using hprev.2.1) (by simpa using hprev.2.2)
  exact ⟨hc, cut_execution w (cuts i) (cuts (i+1)) _ (hseg i).2.1 (hseg i).2.2⟩
end D5.S1.Digit.Infinite.ResetCodebook.Coding
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
namespace D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ResetCodebook
private theorem reset_weak_at_cut
    (anchor : Bool) (K M N : ℕ) (d : ℝ) (hM : 1 ≤ M)
    (hreset : initial false anchor < Statement.B M)
    (w : ℤ → Bool) (p : ℤ) (v : List Return)
    (hv : v ∈ Statement.codebook anchor K N d)
    (hfloor : A false ≤ stateRec w p) :
    Statement.weak K (d+(Statement.B M-initial false anchor)*g^N)
      v (run false (Statement.reset M hM) (stateRec w p)) := by
  have hh := (stateRec_interval w p).2
  have hz : Statement.B M ≤ run false (Statement.reset M hM) (stateRec w p) := by
    rw [run_closed]
    exact reset_lifts M _ hfloor
  have hg := weak_gain K d (Statement.B M-initial false anchor)
    (initial false anchor) (run false (Statement.reset M hM) (stateRec w p)) v
    (sub_pos.mpr hreset) (by linarith) hv.2
  have hweight : Statement.weight v = N := hv.1
  simpa only [hweight] using hg
end D5.S1.Digit.Infinite.ResetCodebook.Coding
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open scoped Topology
namespace D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ResetCodebook
private lemma covering_cut (cuts : ℤ → ℤ) (hm : StrictMono cuts)
    (ht : Filter.Tendsto cuts Filter.atTop Filter.atTop)
    (hb : Filter.Tendsto cuts Filter.atBot Filter.atBot) (p : ℤ) :
    ∃ c : ℤ, cuts c  ≤  p ∧ p  <  cuts (c+1) := by
  let S : Set ℤ := {i | cuts i  ≤  p}
  have hev : ∀ᶠ a in Filter.atBot, cuts a ≤ p := hb.eventually (Filter.eventually_le_atBot p)
  obtain ⟨a,ha'⟩ := hev.exists
  obtain ⟨b,hb,hb'⟩ := Filter.exists_lt_of_tendsto_atTop ht 0 p
  have hne : S.Nonempty := ⟨a,ha'⟩
  have hbd : BddAbove S := by
    refine ⟨b,?_⟩
    intro i hi
    have hi' : cuts i  <  cuts b := hi.trans_lt hb'
    exact (hm.lt_iff_lt.mp hi').le
  let c : ℤ := sSup S
  have hc : c∈S := Int.csSup_mem hne hbd
  refine ⟨c,hc,?_⟩
  by_contra hn
  have hnext : c+1∈S := le_of_not_gt hn
  have hle := le_csSup hbd hnext
  change c+1  ≤  c at hle
  omega
private lemma word_prefix_realization (w : ℤ → Bool) (p : ℤ) (u v : List Bool)
    (hu : ∀ j : Fin (u++v).length, w (p+(j.val:ℤ))=(u++v)[j.val]) :
    (∀ j : Fin u.length, w (p+(j.val:ℤ))=u[j.val]) ∧
    (∀ j : Fin v.length, w (p+(u.length:ℤ)+(j.val:ℤ))=v[j.val]) := by
  constructor
  · intro j
    have hj : j.val  <  (u++v).length := by simp; omega
    simpa [List.getElem_append_left j.isLt] using hu ⟨j.val,hj⟩
  · intro j
    have hj : u.length+j.val  <  (u++v).length := by simp
    have hh := hu ⟨u.length+j.val,hj⟩
    have he : p+((u.length+j.val:ℕ):ℤ) = p+(u.length:ℤ)+(j.val:ℤ) := by
      simp only [Int.natCast_add]; ring
    rw [he] at hh
    simpa using hh
private lemma high_start_bound (w : ℤ → Bool) (p i : ℤ) (K : ℕ)
    (hprev : w (p-1)=false) (hpi : p ≤ i) (hi : Statement.high K w i) :
    (K:ℤ)  ≤  i-p+1 := by
  by_contra hn
  have hj : (i-p+1).toNat  <  K := by omega
  have hh := hi ((i-p+1).toNat) hj
  have he : i-(((i-p+1).toNat:ℕ):ℤ) = p-1 := by omega
  rw [he,hprev] at hh
  contradiction
private lemma state_at_high_prefix (w : ℤ → Bool) (p : ℤ) (r : ℕ)
    (hu : ∀ j : Fin r, w (p+(j.val:ℤ))=true) :
    stateRec w (p+(r:ℤ)) = chi^r * stateRec w p := by
  have hh := stateRec_fold_word w p (List.replicate r true) (by
    intro j
    simpa using hu ⟨j.val, by simpa using j.isLt⟩)
  simpa only [List.length_replicate,fold_true] using hh
/-- Each high run is identified inside the same actual word, with its predecessor seam. -/
theorem weak_word_local_guard
    (w : ℤ → Bool) (p : ℤ) (K : ℕ) (q : ℝ) (as : List Return)
    (hw : Statement.weak K q as (stateRec w p))
    (hprev : w (p-1)=false)
    (hu : ∀ j : Fin (Statement.letters as).length,
      w (p+(j.val:ℤ))=(Statement.letters as)[j.val]) :
    ∀ i : ℤ, p ≤ i → i < p+((Statement.letters as).length:ℤ) →
      ¬Statement.high (K+1) w i ∧
        (Statement.high K w i → chi^(K-1)*q  ≤  stateRec w i) := by
  induction as generalizing p with
  | nil => simp only [Statement.letters,List.flatMap_nil,List.length_nil,Int.natCast_zero,add_zero]; omega
  | cons a as ih =>
      rw [weak_run] at hw
      have hword : Statement.letters (a::as) =
          (List.replicate a.val.2 true ++ List.replicate a.val.1 false) ++ Statement.letters as := rfl
      have hu' : ∀ j : Fin
          (((List.replicate a.val.2 true ++ List.replicate a.val.1 false) ++ Statement.letters as).length),
          w (p+(j.val:ℤ)) =
            ((List.replicate a.val.2 true ++ List.replicate a.val.1 false) ++ Statement.letters as)[j.val] := by
        exact Eq.mp (congrArg (fun u : List Bool =>
          ∀ j : Fin u.length, w (p+(j.val:ℤ)) = u.get j) hword) hu
      have hpref := word_prefix_realization w p _ _ hu'
      have hparts := word_prefix_realization w p _ _ hpref.1
      intro i hpi hi
      by_cases hhigh : i  <  p+(a.val.2:ℤ)
      · have jnon : 0 ≤ i-p := by omega
        have jlt : (i-p).toNat  <  a.val.2 := by omega
        have hmargin (hin : Statement.high K w i) :
            chi^(K-1)*q  ≤  stateRec w i := by
          have hKbound := high_start_bound w p i K hprev hpi hin
          have hr : a.val.2=K := by omega
          have hj : (i-p).toNat=K-1 := by omega
          have hq := hw.2.1 hr
          have hs := state_at_high_prefix w p (K-1) (by
            intro j
            have hjr : j.val < a.val.2 := by omega
            have hh := hparts.1 ⟨j.val,by simpa using hjr⟩
            simpa using hh)
          have he : i=p+((K-1:ℕ):ℤ) := by omega
          rw [he,hs]
          exact mul_le_mul_of_nonneg_left hq (pow_nonneg (parameters false).2.2.1.le _)
        refine ⟨?_,hmargin⟩
        intro hh
        have hKbound := high_start_bound w p i (K+1) hprev hpi hh
        omega
      · by_cases hlow : i  <  p+(a.val.2:ℤ)+(a.val.1:ℤ)
        · have hj : (i-p-(a.val.2:ℤ)).toNat  <  a.val.1 := by omega
          have hh := hparts.2 ⟨(i-p-(a.val.2:ℤ)).toNat,by simpa using hj⟩
          have he : p+(List.replicate a.val.2 true).length+
              (((i-p-(a.val.2:ℤ)).toNat:ℕ):ℤ)=i := by simp; omega
          rw [he] at hh
          have hfalse : w i=false := by simpa using hh
          constructor
          · intro hH
            have hz := hH 0 (by omega)
            simp [hfalse] at hz
          · intro hH
            have hK : 1 ≤ K := a.property.2.trans hw.1
            have hz := hH 0 (by omega)
            simp [hfalse] at hz
        · let p' := p+(a.val.2:ℤ)+(a.val.1:ℤ)
          have hprefix := stateRec_fold_word w p
            (List.replicate a.val.2 true ++ List.replicate a.val.1 false) hpref.1
          rw [List.foldl_append,fold_true,fold_false] at hprefix
          have hstate : stateRec w p'=run false a (stateRec w p) := by
            simpa [p',run,List.length_append,List.length_replicate,Int.natCast_add,add_assoc] using hprefix
          have hpr : w (p'-1)=false := by
            have hm1 : a.val.1-1 < a.val.1 := by have := a.property.1; omega
            have hh := hparts.2 ⟨a.val.1-1,by simpa using hm1⟩
            have he : p+(List.replicate a.val.2 true).length+
                ((a.val.1-1:ℕ):ℤ)=p'-1 := by simp [p']; have := a.property.1; omega
            rw [he] at hh
            simpa using hh
          have htail : ∀ j : Fin (Statement.letters as).length,
              w (p'+(j.val:ℤ))=(Statement.letters as)[j.val] := by
            intro j
            simpa [p',List.length_append,List.length_replicate,Int.natCast_add,add_assoc] using hpref.2 j
          apply ih p' (hstate ▸ hw.2.2) hpr htail i
          · dsimp [p']; omega
          · simp only [hword,List.length_append,List.length_replicate,Int.natCast_add] at hi
            dsimp [p']; omega
private lemma word_terminal_false (w : ℤ → Bool) (p q : ℤ) (a : Return) (as : List Return)
    (hlen : q-p = (Statement.letters (a::as)).length)
    (hu : ∀ j : Fin (Statement.letters (a::as)).length,
      w (p+(j.val:ℤ)) = (Statement.letters (a::as))[j.val]) :
    w (q-1) = false := by
  obtain ⟨u,he⟩ := letters_end_false a as
  have hlen' : (Statement.letters (a::as)).length = u.length+1 := by
    rw [he, List.length_append]; simp
  have hlast := hu ⟨u.length, by omega⟩
  have hidx : p+(u.length:ℤ) = q-1 := by omega
  rw [hidx] at hlast
  simpa [he] using hlast
/-- The reset gain, run cap, and all high-edge margins belong to the same bi-infinite word. -/
theorem concatenation_cap_margin
    (anchor : Bool) (K M N : ℕ) (d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M)
    (hreset : initial false anchor < Statement.B M)
    (w : ℤ → Bool) (hc : Statement.concatenation anchor K M N d hM w) :
    Statement.cap K w ∧ ∀ i, Statement.high K w i →
      chi^(K-1)*d + chi^(K-1)*(Statement.B M-initial false anchor)*g^N ≤ stateRec w i := by
  obtain ⟨cuts,hm,ht,hb,v,hseg⟩ := hc
  have hcuts := concatenation_cut_guard anchor K M N d hM w cuts v hseg
  have hlocal (c : ℤ) : ∀ i : ℤ, cuts c ≤ i → i < cuts (c+1) →
      ¬Statement.high (K+1) w i ∧ (Statement.high K w i →
        chi^(K-1)*(d+(Statement.B M-initial false anchor)*g^N) ≤ stateRec w i) := by
    have hw := reset_weak_at_cut anchor K M N d hM hreset w (cuts c) (v c)
      (hseg c).1 (hcuts c).1
    have hw' : Statement.weak K (d+(Statement.B M-initial false anchor)*g^N)
        (Statement.reset M hM::v c) (stateRec w (cuts c)) := by
      rw [weak_run]
      refine ⟨by change 1 ≤ K; omega, ?_, hw⟩
      intro he
      change 1 = K at he
      omega
    have hp := hseg (c-1)
    have hprev := word_terminal_false w (cuts (c-1)) (cuts c) (Statement.reset M hM)
      (v (c-1)) (by simpa using hp.2.1) (by simpa using hp.2.2)
    have hg := weak_word_local_guard w (cuts c) K _ _ hw' hprev (hseg c).2.2
    intro i hi hi'
    apply hg i hi
    have hlen := (hseg c).2.1
    omega
  constructor
  · intro i
    obtain ⟨c,hci,hic⟩ := covering_cut cuts hm ht hb i
    exact (hlocal c i hci hic).1
  · intro i hi
    obtain ⟨c,hci,hic⟩ := covering_cut cuts hm ht hb i
    have hh := (hlocal c i hci hic).2 hi
    nlinarith [hh]
/-- One finite memory, selected by the previous finite-actual family theorem, covers every
auxiliary concatenation of the complete weak book. -/
theorem reset_complete_family_membership
    (anchor : Bool) (K M N : ℕ) (b d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M)
    (hb : lambda-g^2*chi^K*h false < b)
    (hd : d = (lambda-b)/(g^2*chi^K))
    (hreset : max (X false) (Y false) < Statement.B M) :
    0 < Statement.actualEps anchor K M N b ∧ Statement.finiteActual anchor K M N b d hM ∧
      ∃ n : ℕ, K ≤ n ∧ h false*rho^n < chi^(K-1)*(Statement.B M-initial false anchor)*g^N ∧
        ∀ w, Statement.concatenation anchor K M N d hM w → w ∈ Statement.lowerLanguage K n d := by
  obtain ⟨he,hactual,n,hKn,hcut⟩ := reset_family_cutoff anchor K M N b d hK hM hb hd hreset
  have hr : initial false anchor < Statement.B M := by
    cases anchor
    · exact (le_max_left _ _).trans_lt hreset
    · exact (le_max_right _ _).trans_lt hreset
  refine ⟨he,hactual,n,hKn,hcut,?_⟩
  intro w hw
  have hcm := concatenation_cap_margin anchor K M N d hK hM hr w hw
  rw [lowerLanguage_eq_XMinus]
  apply aux_mem_XMinus K n (chi^(K-1)*d) _ w hcm.1 hcm.2 _ hcut
  have hp := parameters false
  have hg : 0 < g := by have := g_bounds; linarith
  exact mul_pos (mul_pos (pow_pos hp.2.2.1 _) (sub_pos.mpr hr)) (pow_pos hg _)
end D5.S1.Digit.Infinite.ResetCodebook.Coding
