/- GID: D5/S3/Combinatorics/Graph/LegalWords/InhomogeneousMarkovCompletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LegalWords/InhomogeneousMarkovCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strictly interior site means determine a unique first-order legal binary chain. -/

import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LegalWords.InhomogeneousMarkovCompletion

open scoped BigOperators
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (adm_iff_no_adjacent_true)

noncomputable section

/-- The one-site Bernoulli table, in the order false, true. -/
def site (u : ℝ) (a : Bool) : ℝ := if a then u else 1 - u

/-- The unique adjacent table compatible with exclusion and the two means. -/
def pair (u v : ℝ) (a b : Bool) : ℝ :=
  if a then (if b then 0 else u) else (if b then v else 1 - u - v)

/-- Conditional transition obtained from the adjacent table. -/
def step (u v : ℝ) (a b : Bool) : ℝ := pair u v a b / site u a

/-- A finite first-order path mass, with arbitrary initial table and transitions. -/
def chain (q : Bool → ℝ) (K : ℕ → Bool → Bool → ℝ)
    (n : ℕ) (w : Fin (n + 1) → Bool) : ℝ :=
  q (w 0) * ∏ i : Fin n, K i.val (w i.castSucc) (w i.succ)

/-- The overlapping-table expression on a path with n+2 sites. -/
def completion (u : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → Bool) : ℝ :=
  (∏ i : Fin (n + 1), pair (u i.val) (u (i.val + 1)) (w i.castSucc) (w i.succ)) /
    ∏ i : Fin n, site (u (i.val + 1)) (w i.succ.castSucc)

/-- Strictly positive sites and strictly positive empty-empty seams. -/
def Interior (u : ℕ → ℝ) (N : ℕ) : Prop :=
  (∀ i < N, 0 < u i ∧ u i < 1) ∧ (∀ i, i + 1 < N → 0 < 1 - u i - u (i + 1))

/-- A probability mass supported on the repository's admissible binary words. -/
def LegalLaw (n : ℕ) (P : (Fin (n + 1) → Bool) → ℝ) : Prop :=
  (∀ w, 0 ≤ P w) ∧ (∑ w, P w) = 1 ∧ (∀ w, ¬ Adm (n + 1) w → P w = 0)

/-- The occupied-state marginal is the site mean. -/
def Means (u : ℕ → ℝ) (n : ℕ) (P : (Fin (n + 1) → Bool) → ℝ) : Prop :=
  ∀ i : Fin (n + 1), (∑ w, P w * if w i then 1 else 0) = u i.val

/-- First-order factorization with stochastic rows; transitions may vary with the site. -/
private def Factorized (n : ℕ) (P : (Fin (n + 1) → Bool) → ℝ) : Prop :=
  ∃ (q : Bool → ℝ) (K : ℕ → Bool → Bool → ℝ),
    (∀ a, 0 ≤ q a) ∧ (∑ a, q a) = 1 ∧
    (∀ i < n, ∀ a b, 0 ≤ K i a b) ∧
    (∀ i < n, ∀ a, (∑ b, K i a b) = 1) ∧ P = chain q K n

private theorem sum_snoc (n : ℕ) (F : (Fin (n + 1) → Bool) → ℝ) :
    (∑ w, F w) = ∑ v : Fin n → Bool, ∑ b : Bool, F (Fin.snoc v b) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (n + 1) => Bool),
    Fintype.sum_prod_type, Finset.sum_comm]
  rfl

private theorem chain_snoc (q : Bool → ℝ) (K : ℕ → Bool → Bool → ℝ)
    (n : ℕ) (v : Fin (n + 1) → Bool) (b : Bool) :
    chain q K (n + 1) (Fin.snoc v b) = chain q K n v * K n (v (Fin.last n)) b := by
  simp only [chain, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.val_castSucc, Fin.val_last, Fin.succ_last, ← Fin.castSucc_succ, Fin.snoc_apply_zero]
  ring

private theorem sum_one (F : (Fin 1 → Bool) → ℝ) :
    (∑ w, F w) = ∑ a : Bool, F (fun _ => a) := by
  rw [sum_snoc 0]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro a _
  congr 1

private theorem site_pos {u : ℝ} (hu : 0 < u ∧ u < 1) (a : Bool) :
    0 < site u a := by
  cases a <;> simp [site] <;> linarith [hu.1, hu.2]

private theorem step_rows {u v : ℝ} (hu : 0 < u ∧ u < 1) (a : Bool) :
    (∑ b : Bool, step u v a b) = 1 := by
  have h : 1 - u ≠ 0 := ne_of_gt (sub_pos.mpr hu.2)
  have h0 : u ≠ 0 := ne_of_gt hu.1
  cases a <;> simp [step, pair, site]
  · field_simp
    ; ring
  · simp [h0]

private theorem step_transfer {u v : ℝ} (hu : 0 < u ∧ u < 1) (b : Bool) :
    (∑ a : Bool, site u a * step u v a b) = site v b := by
  have h0 := ne_of_gt hu.1
  have h1 := ne_of_gt (sub_pos.mpr hu.2)
  cases b <;> simp [step, pair, site, h0]
  <;> field_simp
  all_goals ring

/-- Restrict a path to its initial m+1 sites. -/
def initialSegment {n : ℕ} (m : ℕ) (h : m ≤ n) (w : Fin (n + 1) → Bool) :
    Fin (m + 1) → Bool := fun i => w ⟨i.val, by omega⟩

/-- The probability of an exact initial segment of a full path. -/
def cylinder (n : ℕ) (P : (Fin (n + 1) → Bool) → ℝ)
    (m : ℕ) (hm : m ≤ n) (v : Fin (m + 1) → Bool) : ℝ :=
  ∑ w, P w * if initialSegment m hm w = v then 1 else 0

/-- Conditional extension of any history depends only on its last bit. -/
def Markov (n : ℕ) (P : (Fin (n + 1) → Bool) → ℝ) : Prop :=
  ∃ K : ℕ → Bool → Bool → ℝ,
    (∀ i < n, ∀ a b, 0 ≤ K i a b) ∧
    (∀ i < n, ∀ a, (∑ b, K i a b) = 1) ∧
    ∀ (m : ℕ) (hm : m < n) (v : Fin (m + 1) → Bool) (b : Bool),
      cylinder n P (m + 1) (by omega) (Fin.snoc v b) =
        cylinder n P m (by omega) v * K m (v (Fin.last m)) b

private theorem prefix_expect (q : Bool → ℝ) (K : ℕ → Bool → Bool → ℝ)
    (n : ℕ) (hK : ∀ i < n, ∀ a, (∑ b, K i a b) = 1)
    (m : ℕ) (hm : m ≤ n) (F : (Fin (m + 1) → Bool) → ℝ) :
    (∑ w, chain q K n w * F (initialSegment m hm w)) = ∑ v, chain q K m v * F v := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst m
    rfl
  | succ n ih =>
    by_cases he : m = n + 1
    · subst m
      rfl
    · have hm' : m ≤ n := by omega
      rw [sum_snoc (n + 1)]
      have hp (v : Fin (n + 1) → Bool) (b : Bool) :
          initialSegment m hm (Fin.snoc v b) = initialSegment m hm' v := by
        funext i
        simp [initialSegment, Fin.snoc, show i.val < n + 1 by omega]
      simp_rw [chain_snoc, hp, mul_assoc, mul_comm (K n _ _),
        ← mul_assoc, ← Finset.mul_sum, hK n (by omega), mul_one]
      exact ih (fun i hi => hK i (by omega)) hm'

private theorem cylinder_full (n : ℕ) (P : (Fin (n + 1) → Bool) → ℝ)
    (v : Fin (n + 1) → Bool) : cylinder n P n le_rfl v = P v := by
  change (∑ w, P w * if w = v then 1 else 0) = P v
  simp

private theorem cylinder_total (n : ℕ) (P : (Fin (n + 1) → Bool) → ℝ)
    (m : ℕ) (hm : m ≤ n) : (∑ v, cylinder n P m hm v) = ∑ w, P w := by
  unfold cylinder
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp [mul_ite]

private theorem chain_cylinder (q : Bool → ℝ) (K : ℕ → Bool → Bool → ℝ)
    (n : ℕ) (hK : ∀ i < n, ∀ a, (∑ b, K i a b) = 1)
    (m : ℕ) (hm : m ≤ n) (v : Fin (m + 1) → Bool) :
    cylinder n (chain q K n) m hm v = chain q K m v := by
  unfold cylinder
  rw [prefix_expect q K n hK m hm (fun x => if x = v then 1 else 0)]
  simp

private theorem factorized_markov (n : ℕ) (P : (Fin (n + 1) → Bool) → ℝ)
    (h : Factorized n P) : Markov n P := by
  obtain ⟨q, K, _, _, hpos, hrows, rfl⟩ := h
  refine ⟨K, hpos, hrows, ?_⟩
  intro m hm v b
  rw [chain_cylinder q K n hrows, chain_cylinder q K n hrows, chain_snoc]

private theorem markov_factorized (n : ℕ) (P : (Fin (n + 1) → Bool) → ℝ)
    (hP : LegalLaw n P) (h : Markov n P) : Factorized n P := by
  obtain ⟨K, hpos, hrows, hrec⟩ := h
  let q : Bool → ℝ := fun a => cylinder n P 0 (Nat.zero_le _) (fun _ => a)
  have hqpos (a : Bool) : 0 ≤ q a := by
    unfold q cylinder
    apply Finset.sum_nonneg
    intro w _
    apply mul_nonneg (hP.1 w)
    split_ifs <;> norm_num
  have hqsum : (∑ a, q a) = 1 := by
    change (∑ a : Bool, cylinder n P 0 (Nat.zero_le _) (fun _ => a)) = 1
    rw [← sum_one, cylinder_total]
    exact hP.2.1
  have hc (m : ℕ) (hm : m ≤ n) (v : Fin (m + 1) → Bool) :
      cylinder n P m hm v = chain q K m v := by
    induction m with
    | zero =>
      simp only [chain, Fin.prod_univ_zero, mul_one]
      change cylinder n P 0 hm v = cylinder n P 0 hm (fun _ => v 0)
      congr 1
      funext i
      have hi : i = 0 := Fin.ext (by omega)
      rw [hi]
    | succ m ih =>
      rw [← Fin.snoc_init_self v, hrec m (by omega), chain_snoc, ih (by omega)]
  refine ⟨q, K, hqpos, hqsum, hpos, hrows, ?_⟩
  funext w
  rw [← cylinder_full n P w]
  exact hc n le_rfl w

private theorem endpoint_split (q : Bool → ℝ) (K : ℕ → Bool → Bool → ℝ)
    (n : ℕ) (f : Bool → ℝ) :
    (∑ w, chain q K n w * f (w (Fin.last n))) =
      ∑ a : Bool, (∑ w, chain q K n w * if w (Fin.last n) = a then 1 else 0) * f a := by
  simp only [Finset.sum_mul, Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  cases w (Fin.last n) <;> simp

private theorem endpoint_recursion (q : Bool → ℝ) (K : ℕ → Bool → Bool → ℝ)
    (n : ℕ) (f : Bool → ℝ) :
    (∑ w, chain q K (n + 1) w * f (w (Fin.last (n + 1)))) =
      ∑ a : Bool, (∑ v, chain q K n v * if v (Fin.last n) = a then 1 else 0) *
        (∑ b : Bool, K n a b * f b) := by
  rw [sum_snoc (n + 1)]
  simp_rw [chain_snoc, Fin.snoc_last, mul_assoc, ← Finset.mul_sum]
  exact endpoint_split q K n (fun a => ∑ b : Bool, K n a b * f b)

private theorem endpoint_canonical (u : ℕ → ℝ) (n : ℕ)
    (hu : ∀ i < n + 1, 0 < u i ∧ u i < 1) (f : Bool → ℝ) :
    (∑ w, chain (site (u 0)) (fun i => step (u i) (u (i + 1))) n w *
      f (w (Fin.last n))) = ∑ a : Bool, site (u n) a * f a := by
  induction n generalizing f with
  | zero =>
    rw [sum_one]
    simp [chain]
  | succ n ih =>
    rw [endpoint_recursion]
    have he (a : Bool) :
        (∑ v, chain (site (u 0)) (fun i => step (u i) (u (i + 1))) n v *
          if v (Fin.last n) = a then 1 else 0) = site (u n) a := by
      rw [ih (fun i hi => hu i (by omega)) (fun b : Bool => if b = a then 1 else 0)]
      cases a <;> simp
    simp_rw [he, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, step_transfer (hu n (by omega))]

private theorem marginal_prefix (q : Bool → ℝ) (K : ℕ → Bool → Bool → ℝ)
    (n : ℕ) (hK : ∀ i < n, ∀ a, (∑ b, K i a b) = 1)
    (i : Fin (n + 1)) (f : Bool → ℝ) :
    (∑ w, chain q K n w * f (w i)) =
      ∑ v, chain q K i.val v * f (v (Fin.last i.val)) := by
  exact prefix_expect q K n hK i.val (by omega) (fun v => f (v (Fin.last i.val)))

private theorem prescribed_marginals (u : ℕ → ℝ) (n : ℕ)
    (P : (Fin (n + 1) → Bool) → ℝ) (hP : (∑ w, P w) = 1)
    (hmean : Means u n P) (i : Fin (n + 1)) (a : Bool) :
    (∑ w, P w * if w i = a then 1 else 0) = site (u i.val) a := by
  cases a with
  | true => simpa [site] using hmean i
  | false =>
    have he : (∑ w, P w * if w i = false then 1 else 0) +
        (∑ w, P w * if w i then 1 else 0) = 1 := by
      calc
        _ = ∑ w, P w := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro w _
          cases w i <;> simp
        _ = 1 := hP
    have hm := hmean i
    simp only [site, Bool.false_eq_true, ite_false]
    linarith

private theorem chain_normalized (q : Bool → ℝ) (K : ℕ → Bool → Bool → ℝ)
    (n : ℕ) (hq : (∑ a, q a) = 1)
    (hK : ∀ i < n, ∀ a, (∑ b, K i a b) = 1) :
    (∑ w, chain q K n w) = 1 := by
  have h := prefix_expect q K n hK 0 (Nat.zero_le _) (fun _ => 1)
  simp only [mul_one] at h
  rw [h, sum_one]
  simpa [chain] using hq

private theorem completion_chain (u : ℕ → ℝ) (n : ℕ)
    (hu : ∀ i < n + 2, 0 < u i ∧ u i < 1) (w : Fin (n + 2) → Bool) :
    completion u n w = chain (site (u 0)) (fun i => step (u i) (u (i + 1))) (n + 1) w := by
  have h0 : site (u 0) (w 0) ≠ 0 := ne_of_gt (site_pos (hu 0 (by omega)) _)
  have hd : (∏ i : Fin n, site (u (i.val + 1)) (w i.succ.castSucc)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (site_pos (hu _ (by omega)) _))
  unfold completion chain
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.val_zero, zero_add, Fin.castSucc_zero, Fin.val_succ, step,
    Finset.prod_div_distrib]
  field_simp

private theorem identify_markov (u : ℕ → ℝ) (n : ℕ)
    (hu : ∀ i < n + 1, 0 < u i ∧ u i < 1)
    (P : (Fin (n + 1) → Bool) → ℝ) (hP : LegalLaw n P)
    (hm : Means u n P) (hM : Factorized n P) :
    P = chain (site (u 0)) (fun i => step (u i) (u (i + 1))) n := by
  obtain ⟨q, K, _hqpos, hqsum, _hKpos, hKsum, rfl⟩ := hM
  have hend (i : ℕ) (hi : i ≤ n) (a : Bool) :
      (∑ v, chain q K i v * if v (Fin.last i) = a then 1 else 0) = site (u i) a := by
    exact (marginal_prefix q K n hKsum ⟨i, by omega⟩
      (fun b => if b = a then 1 else 0)).symm.trans
      (prescribed_marginals u n _ hP.2.1 hm ⟨i, by omega⟩ a)
  have hq (a : Bool) : q a = site (u 0) a := by
    have he := hend 0 (Nat.zero_le _) a
    rw [sum_one] at he
    cases a <;> simpa [chain, Fintype.sum_bool] using he
  have hK (i : ℕ) (hi : i < n) (a b : Bool) : K i a b = step (u i) (u (i + 1)) a b := by
    let I : Fin (n + 1) := ⟨i, by omega⟩
    let J : Fin (n + 1) := ⟨i + 1, by omega⟩
    have hzero : (∑ w, chain q K n w * if w I = true ∧ w J = true then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      by_cases hw : w I = true ∧ w J = true
      · have hn : ¬ Adm (n + 1) w := by
          intro ha
          have hh := (adm_iff_no_adjacent_true _ w).mp ha I J (by rfl)
          simp [hw.1, hw.2] at hh
        simp [hw, hP.2.2 w hn]
      · simp [hw]
    have hprefix : (∑ v, chain q K (i + 1) v *
        if v (Fin.last i).castSucc = true ∧ v (Fin.last (i + 1)) = true then 1 else 0) = 0 := by
      have he := prefix_expect q K n hKsum (i + 1) (by omega)
        (fun v => if v (Fin.last i).castSucc = true ∧
          v (Fin.last (i + 1)) = true then 1 else 0)
      exact he.symm.trans hzero
    have hpair : (∑ v, chain q K (i + 1) v *
        if v (Fin.last i).castSucc = true ∧ v (Fin.last (i + 1)) = true then 1 else 0) =
        (∑ v, chain q K i v * if v (Fin.last i) = true then 1 else 0) * K i true true := by
      rw [sum_snoc (i + 1), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v _
      simp only [chain_snoc, Fin.snoc_last, Fin.snoc_castSucc, Fintype.sum_bool]
      cases v (Fin.last i) <;> simp
    rw [hpair, hend i (by omega) true] at hprefix
    have h11 : K i true true = 0 := by
      simpa [site, ne_of_gt (hu i (by omega)).1] using hprefix
    have h10 : K i true false = 1 := by
      have hr := hKsum i hi true
      simpa [Fintype.sum_bool, h11] using hr
    have hnext := endpoint_recursion q K i (fun b => if b = true then 1 else 0)
    simp only [hend (i + 1) (by omega) true, hend i (by omega), Fintype.sum_bool,
      site, Bool.false_eq_true, ite_false, ite_true, h11, mul_zero, zero_add,
      mul_one, add_zero] at hnext
    have hz : 1 - u i ≠ 0 := ne_of_gt (sub_pos.mpr (hu i (by omega)).2)
    have h01 : K i false true = u (i + 1) / (1 - u i) := by
      apply (eq_div_iff hz).2
      linarith [hnext]
    have h00 : K i false false = (1 - u i - u (i + 1)) / (1 - u i) := by
      have hr := hKsum i hi false
      simp only [Fintype.sum_bool] at hr
      rw [h01] at hr
      apply (eq_div_iff hz).2
      field_simp at hr
      nlinarith [hr]
    cases a <;> cases b <;>
      simp [step, pair, site, h00, h01, h10, h11, ne_of_gt (hu i (by omega)).1]
  funext w
  unfold chain
  rw [hq]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact hK i.val i.isLt _ _

private theorem canonical_legal (u : ℕ → ℝ) (n : ℕ)
    (hu : Interior u (n + 1)) :
    LegalLaw n (chain (site (u 0)) (fun i => step (u i) (u (i + 1))) n) := by
  have hnonneg (i : ℕ) (hi : i < n) (a b : Bool) : 0 ≤ step (u i) (u (i + 1)) a b := by
    apply div_nonneg _ (site_pos (hu.1 i (by omega)) a).le
    cases a <;> cases b <;> simp only [pair, ite_true]
    · exact (hu.2 i (by omega)).le
    · exact (hu.1 (i + 1) (by omega)).1.le
    · exact (hu.1 i (by omega)).1.le
    · rfl
  refine ⟨?_, ?_, ?_⟩
  · intro w
    apply mul_nonneg (site_pos (hu.1 0 (by omega)) _).le
    exact Finset.prod_nonneg (fun i _ => hnonneg i.val i.isLt _ _)
  · apply chain_normalized
    · simp [site]
    · intro i hi a
      exact step_rows (hu.1 i (by omega)) a
  · intro w hw
    rw [adm_iff_no_adjacent_true] at hw
    push Not at hw
    obtain ⟨i, j, hij, hi, hj⟩ := hw
    let k : Fin n := ⟨i.val, by have := j.isLt; omega⟩
    have hi' : w k.castSucc = true := by
      have he : k.castSucc = i := Fin.ext rfl
      simpa [he] using hi
    have hj' : w k.succ = true := by
      have he : k.succ = j := Fin.ext (by simpa [k] using hij)
      simpa [he] using hj
    unfold chain
    have hp : (∏ l : Fin n, step (u l.val) (u (l.val + 1)) (w l.castSucc) (w l.succ)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      simp [step, pair, hi', hj']
    rw [hp, mul_zero]

/-- The local-table quotient is the unique first-order legal law with the prescribed means. -/
theorem unique_markov_completion (u : ℕ → ℝ) (n : ℕ) (hu : Interior u (n + 2)) :
    LegalLaw (n + 1) (completion u n) ∧
    Means u (n + 1) (completion u n) ∧
    Markov (n + 1) (completion u n) ∧
    ∀ P : (Fin (n + 2) → Bool) → ℝ,
      LegalLaw (n + 1) P → Means u (n + 1) P → Markov (n + 1) P → P = completion u n := by
  have he : completion u n = chain (site (u 0)) (fun i => step (u i) (u (i + 1))) (n + 1) :=
    funext (completion_chain u n hu.1)
  rw [he]
  refine ⟨canonical_legal u (n + 1) hu, ?_, ?_, ?_⟩
  · intro i
    rw [marginal_prefix (site (u 0)) (fun j => step (u j) (u (j + 1)))
      (n + 1) (fun j hj a => step_rows (hu.1 j (by omega)) a) i
      (fun b : Bool => if b then 1 else 0),
      endpoint_canonical u i.val (fun j hj => hu.1 j (by have := i.isLt; omega))
        (fun b : Bool => if b then 1 else 0)]
    simp [site]
  · apply factorized_markov
    refine ⟨site (u 0), (fun i => step (u i) (u (i + 1))), ?_, ?_, ?_, ?_, rfl⟩
    · intro a
      exact (site_pos (hu.1 0 (by omega)) a).le
    · simp [site]
    · intro i hi a b
      apply div_nonneg _ (site_pos (hu.1 i (by omega)) a).le
      cases a <;> cases b <;> simp only [pair, ite_true]
      · exact (hu.2 i (by omega)).le
      · exact (hu.1 (i + 1) (by omega)).1.le
      · exact (hu.1 i (by omega)).1.le
      · rfl
    · intro i hi a
      exact step_rows (hu.1 i (by omega)) a
  · intro P hP hm hM
    exact identify_markov u (n + 1) hu.1 P hP hm (markov_factorized _ P hP hM)

#print axioms unique_markov_completion

end
end D5.S3.Combinatorics.Graph.LegalWords.InhomogeneousMarkovCompletion
