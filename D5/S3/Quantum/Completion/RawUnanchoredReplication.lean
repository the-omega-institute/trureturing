/- GID: D5/S3/Quantum/Completion/RawUnanchoredReplication
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/RawUnanchoredReplication
   mirror-E: none(waiver:raw-unital-magma)
   anchors: []
   utility: none
   digest: Synchronous arrays retain ordered comparisons and control costs to the actual unit. -/

import D5.S3.QuadraticForms.ThreeWayBalance
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Mathlib.Tactic.DeriveCountable
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

/-! Raw unanchored costs, common phases and literal coordinate arrays. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

namespace D5.S3.Quantum.Completion.RawUnanchoredReplication

/-- Finite real costs and the full four-variable law, with an arbitrary marker. -/
structure RawCost {M : Type*} [MulOneClass M] (U : M → M) (c : M → M → ℝ) : Prop where
  nonneg : ∀ a b, 0 ≤ c a b
  diagonal : ∀ a, c a a = 0
  balance : ∀ a b u v,
    c (a * u) (b * v) + c (a * U u) (b * U v) +
      c (a * U (U u)) (b * U (U v)) = 3 * c a b + 3 * c u v

variable {M : Type*} [MulOneClass M] {U : M → M} {c : M → M → ℝ}

def omega (U : M → M) (c : M → M → ℝ) : ℝ :=
  c (U 1) 1 + c (U (U 1)) 1 + c 1 (U 1) + c 1 (U (U 1))

private lemma sync (h : RawCost U c) (x y : M) : c (U x) (U y) = c x y := by
  let s : ℕ → ℝ := fun n => c (U^[n] x) (U^[n] y)
  have hr (n : ℕ) : s (n + 2) + s (n + 1) = 2 * s n := by
    have hh := h.balance 1 1 (U^[n] x) (U^[n] y)
    simp only [one_mul, h.diagonal, mul_zero, zero_add] at hh
    change c (U^[n+2] x) (U^[n+2] y) + c (U^[n+1] x) (U^[n+1] y) = 2*c (U^[n] x) (U^[n] y)
    simp only [show n+2 = (n+1)+1 by omega, Function.iterate_succ_apply']
    linarith
  exact D5.S3.QuadraticForms.ThreeWayBalance.nonneg_recurrence_constant s
    (fun n => h.nonneg _ _) hr

lemma sync_iter (h : RawCost U c) (n : ℕ) (x y : M) :
    c (U^[n] x) (U^[n] y) = c x y := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply', sync h] using ih

lemma single (h : RawCost U c) (a b u v : M) :
    c (a * u) (b * v) ≤ 3 * (c a b + c u v) := by
  have hh := h.balance a b u v
  linarith [h.nonneg (a * U u) (b * U v), h.nonneg (a * U (U u)) (b * U (U v))]

lemma unit_compare (h : RawCost U c) (x y : M) :
    c x y ≤ 3 * (c x 1 + c 1 y) := by
  simpa only [mul_one, one_mul] using single h x 1 1 y

private lemma transpose (h : RawCost U c) : RawCost U (fun a b => c b a) :=
  ⟨fun a b => h.nonneg b a, h.diagonal, fun a b u v => h.balance b a v u⟩

private lemma omega_nonneg (h : RawCost U c) : 0 ≤ omega U c := by
  unfold omega
  linarith [h.nonneg (U 1) 1, h.nonneg (U (U 1)) 1,
    h.nonneg 1 (U 1), h.nonneg 1 (U (U 1))]

private lemma orbit_budget (h : RawCost U c) (n : ℕ) :
    c (U^[n] 1) 1 + c 1 (U^[n] 1) ≤ omega U c := by
  let x := U^[n] (1 : M)
  have hzero := h.balance x 1 1 x
  have hfirst := h.balance x (U x) (U 1) 1
  have hsecond := h.balance x (U (U x)) (U (U 1)) 1
  simp only [one_mul, mul_one, h.diagonal, zero_add] at hzero hfirst hsecond
  have hc (z : M) : U^[n] (U z) = U (U^[n] z) :=
    (Function.iterate_succ_apply U n z).symm.trans (Function.iterate_succ_apply' U n z)
  have hi : c x (U x) = c 1 (U 1) := by
    simpa only [x, hc] using sync_iter h n 1 (U 1)
  have hii : c x (U (U x)) = c 1 (U (U 1)) := by
    simpa only [x, hc] using sync_iter h n 1 (U (U 1))
  have hn₁ := h.nonneg (x * U (U 1)) (U x * U 1)
  have hn₂ := h.nonneg (x * U (U (U 1))) (U x * U (U 1))
  have hn₃ := h.nonneg (x * U (U (U 1))) (U (U x) * U 1)
  have hn₄ := h.nonneg (x * U (U (U (U 1)))) (U (U x) * U (U 1))
  dsimp [omega]
  change c x 1 + c 1 x ≤ _
  linarith

private lemma right_three (h : RawCost U c) (a b : M) (j : ℕ) :
    c (a * U^[j + 3] 1) (b * U^[j + 3] 1) =
      c (a * U^[j] 1) (b * U^[j] 1) := by
  have h₀ := h.balance a b (U^[j] 1) (U^[j] 1)
  have h₁ := h.balance a b (U^[j+1] 1) (U^[j+1] 1)
  simp only [h.diagonal, mul_zero, add_zero] at h₀ h₁
  simp only [show j + 3 = (j + 1) + 1 + 1 by omega, Function.iterate_succ_apply']
  simp only [Function.iterate_succ_apply'] at h₁
  linarith

private lemma right_multiple (h : RawCost U c) (a b : M) (L : ℕ) (hL : 3 ∣ L) :
    c (a * U^[L] 1) (b * U^[L] 1) = c a b := by
  obtain ⟨k, rfl⟩ := hL
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 3 * (k+1) = 3*k+3 by omega, right_three h]
    exact ih

private lemma multiple_budget (h : RawCost U c) (y : M) (L : ℕ) (hL : 3 ∣ L) :
    c y 1 ≤ 3 * c y (U^[L] 1) + 3 * omega U c := by
  have he := right_multiple h y 1 L hL
  simp only [one_mul] at he
  have hb := single h y (U^[L] 1) (U^[L] 1) 1
  simp only [mul_one] at hb
  have ho := orbit_budget h L
  have hn := h.nonneg 1 (U^[L] 1)
  linarith

/-- A source-dependent phase is never used: the same phase works for every source. -/
def phase (j : ℕ) : Fin 3 := ⟨(3 - j % 3) % 3, Nat.mod_lt _ (by decide)⟩

private lemma phase_dvd (j : ℕ) : 3 ∣ j + (phase j).val := by
  apply Nat.dvd_of_mod_eq_zero
  have hm := Nat.mod_lt j (by decide : 0 < 3)
  dsimp [phase]
  omega

private lemma marker_budget (h : RawCost U c) (y : M) (j : ℕ) :
    c y 1 ≤ 9 * c y (U^[j] 1) + 12 * omega U c := by
  let e := (phase j).val
  have hb := multiple_budget h (U^[e] y) (j+e) (phase_dvd j)
  have hid : U^[j+e] (1 : M) = U^[e] (U^[j] 1) := by
    rw [Nat.add_comm, Function.iterate_add_apply]
  rw [hid, sync_iter h] at hb
  have hs := unit_compare h (U^[e] y) (U^[e] 1)
  rw [sync_iter h] at hs
  have ho := orbit_budget h e
  have hn := h.nonneg (U^[e] 1) 1
  linarith

private lemma iterate_budget (h : RawCost U c) (x : M) (n : ℕ) :
    c (U^[n] x) 1 ≤ 9 * c x 1 + 12 * omega U c := by
  simpa only [sync_iter h] using marker_budget h (U^[n] x) n

/-- The index is the actual array of N phase choices. -/
abbrev Sigma (N : ℕ) := Fin N → Fin 3

/-- The literal right comb retains both the bracketing and the order. -/
def history (U : M → M) (a z : M) : (N : ℕ) → Sigma N → M
  | 0, _ => z
  | N+1, σ => a * U^[(σ 0).val] (history U a z N (fun i => σ i.succ))

def phaseSum {N : ℕ} (σ : Sigma N) : ℕ := ∑ i, (σ i).val

private def splitSigma (N : ℕ) : Sigma (N+1) ≃ Fin 3 × Sigma N where
  toFun σ := (σ 0, fun i => σ i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv σ := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv p := by simp

private lemma sum_split (N : ℕ) (f : Sigma (N+1) → ℝ) :
    ∑ σ, f σ = ∑ τ : Sigma N, ∑ k : Fin 3, f (Fin.cons k τ) := by
  rw [Fintype.sum_equiv (splitSigma N) f (fun p => f (Fin.cons p.1 p.2))]
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
  · intro σ
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [splitSigma]

private lemma sigma_card (N : ℕ) : Fintype.card (Sigma N) = 3^N := by
  simp [Sigma, Fintype.card_fun]

private lemma history_sum (h : RawCost U c) (a b z w : M) (N : ℕ) :
    ∑ σ : Sigma N, c (history U a z N σ) (history U b w N σ) =
      (3 : ℝ)^N * ((N : ℝ) * c a b + c z w) := by
  induction N with
  | zero => simp [history, Sigma]
  | succ N ih =>
    rw [sum_split]
    have hb (τ : Sigma N) :
        (∑ k : Fin 3, c (history U a z (N+1) (Fin.cons k τ))
          (history U b w (N+1) (Fin.cons k τ))) =
          3*c a b + 3*c (history U a z N τ) (history U b w N τ) := by
      simpa [history, Fin.sum_univ_succ, add_assoc] using
        h.balance a b (history U a z N τ) (history U b w N τ)
    simp_rw [hb]
    rw [Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum]
    rw [ih]
    simp only [Finset.sum_const, Finset.card_univ, sigma_card, nsmul_eq_mul]
    push_cast
    rw [pow_succ]
    ring

private lemma history_unit (N : ℕ) (σ : Sigma N) :
    history U 1 1 N σ = U^[phaseSum σ] 1 := by
  induction N with
  | zero => simp [history, phaseSum]
  | succ N ih =>
    rw [history, one_mul, ih]
    unfold phaseSum
    rw [Fin.sum_univ_succ]
    exact (Function.iterate_add_apply U _ _ 1).symm

/-- All sources use the same coordinate phase, including the old unit source. -/
def gamma (U : M → M) (N : ℕ) (a : M) : Sigma N → M := fun σ =>
  U^[(phase (phaseSum σ)).val] (history U a 1 N σ)

/-- The new actual unit is the constant old-unit array. -/
def arrayMarker (U : M → M) {N : ℕ} (X : Sigma N → M) : Sigma N → M := U ∘ X

def arrayCost (c : M → M → ℝ) (N : ℕ) (X Y : Sigma N → M) : ℝ :=
  (∑ σ, c (X σ) (Y σ)) / ((N : ℝ) * 3^N)

private lemma array_raw (h : RawCost U c) (N : ℕ) :
    RawCost (arrayMarker U) (arrayCost c N) := by
  constructor
  · intro X Y
    exact div_nonneg (Finset.sum_nonneg (fun σ _ => h.nonneg _ _)) (by positivity)
  · intro X
    simp [arrayCost, h.diagonal]
  · intro A B X Y
    unfold arrayCost arrayMarker
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [← add_div, ← add_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp_rw [h.balance]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring

private lemma array_constant (N : ℕ) (hN : 0 < N) (a b : M) :
    arrayCost c N (fun _ => a) (fun _ => b) = c a b / N := by
  simp only [arrayCost, Finset.sum_const, Finset.card_univ, sigma_card, nsmul_eq_mul]
  push_cast
  field_simp

private lemma array_omega (N : ℕ) (hN : 0 < N) :
    omega (arrayMarker U (N := N)) (arrayCost c N) = omega U c / N := by
  unfold omega
  change arrayCost c N (fun _ => U 1) (fun _ => 1) +
    arrayCost c N (fun _ => U (U 1)) (fun _ => 1) +
    arrayCost c N (fun _ => 1) (fun _ => U 1) +
    arrayCost c N (fun _ => 1) (fun _ => U (U 1)) = _
  rw [array_constant N hN, array_constant N hN, array_constant N hN, array_constant N hN]
  ring

private lemma gamma_matrix (h : RawCost U c) (N : ℕ) (hN : 0 < N) (a b : M) :
    arrayCost c N (gamma U N a) (gamma U N b) = c a b := by
  unfold arrayCost gamma
  simp_rw [sync_iter h]
  rw [history_sum h]
  simp only [h.diagonal, add_zero]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have ht : (3 : ℝ)^N ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  <;> ring

private lemma gamma_unit (N : ℕ) (σ : Sigma N) :
    gamma U N 1 σ = U^[phaseSum σ + (phase (phaseSum σ)).val] 1 := by
  unfold gamma
  rw [history_unit, Nat.add_comm, Function.iterate_add_apply]

private lemma gamma_forward (h : RawCost U c) (N : ℕ) (hN : 0 < N) (a : M) :
    arrayCost c N (gamma U N a) 1 ≤ 3*c a 1 + 3*omega U c/N := by
  have hp : 0 ≤ (N : ℝ)*3^N := by positivity
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have ht : (3 : ℝ)^N ≠ 0 := pow_ne_zero _ (by norm_num)
  have hs : (∑ σ : Sigma N, c (gamma U N a σ) 1) ≤
      ∑ σ : Sigma N, (3*c (gamma U N a σ) (gamma U N 1 σ) + 3*omega U c) := by
    apply Finset.sum_le_sum
    intro σ _
    rw [gamma_unit]
    exact multiple_budget h _ _ (phase_dvd _)
  have hd := div_le_div_of_nonneg_right hs hp
  have hm := gamma_matrix h N hN a 1
  unfold arrayCost at hm ⊢
  change (∑ σ, c (gamma U N a σ) 1) / ((N : ℝ)*3^N) ≤ _
  apply hd.trans
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, sigma_card, nsmul_eq_mul]
  push_cast
  rw [add_div, mul_div_assoc, hm]
  apply le_of_eq
  field_simp
  <;> ring

/-- The actual array model preserves every ordered comparison and both true-unit budgets.
This finite-depth statement supplies no countable limiting model. -/
theorem raw_replication (h : RawCost U c) (N : ℕ) (hN : 0 < N) :
    RawCost (arrayMarker U (N := N)) (arrayCost c N) ∧
    omega (arrayMarker U (N := N)) (arrayCost c N) = omega U c/N ∧
    (∀ a b, arrayCost c N (gamma U N a) (gamma U N b) = c a b) ∧
    (∀ a, arrayCost c N (gamma U N a) 1 ≤ 3*c a 1 + 3*omega U c/N ∧
      arrayCost c N 1 (gamma U N a) ≤ 3*c 1 a + 3*omega U c/N) ∧
    (∀ x n, c (U^[n] x) 1 + c 1 (U^[n] x) ≤
      9*(c x 1+c 1 x)+24*omega U c) := by
  refine ⟨array_raw h N, array_omega N hN, gamma_matrix h N hN, ?_, ?_⟩
  · intro a
    refine ⟨gamma_forward h N hN a, ?_⟩
    have ht := gamma_forward (transpose h) N hN a
    have he : omega U (fun a b => c b a) = omega U c := by unfold omega; ring
    simpa only [arrayCost, he] using ht
  · intro x n
    have hf := iterate_budget h x n
    have hr := iterate_budget (transpose h) x n
    have he : omega U (fun a b => c b a) = omega U c := by unfold omega; ring
    rw [he] at hr
    linarith

/-- Raw ordered syntax. The normal subset removes only two-sided unit factors. -/
inductive Expr (α : Type*)
  | unit : Expr α
  | source : α → Expr α
  | mark : Expr α → Expr α
  | product : Expr α → Expr α → Expr α
  deriving Countable

@[reducible] def Normal {α : Type*} : Expr α → Prop
  | .unit => True
  | .source _ => True
  | .mark s => Normal s
  | .product s t => Normal s ∧ Normal t ∧ s ≠ .unit ∧ t ≠ .unit

/-- Canonical unit normal forms; the expression U(unit) remains a distinct form. -/
abbrev Term (α : Type*) := {s : Expr α // Normal s}

instance {α : Type*} [Countable α] : Countable (Term α) :=
  inferInstanceAs (Countable {s : Expr α // Normal s})

def termProduct {α : Type*} (s t : Term α) : Term α := by
  classical
  exact if hs : s.val = .unit then t else
    if ht : t.val = .unit then s else
      ⟨.product s.val t.val, s.property, t.property, hs, ht⟩

instance {α : Type*} : MulOneClass (Term α) where
  one := ⟨.unit, trivial⟩
  mul := termProduct
  one_mul s := by
    classical
    change termProduct ⟨.unit, trivial⟩ s = s
    simp [termProduct]
  mul_one s := by
    classical
    change termProduct s ⟨.unit, trivial⟩ = s
    by_cases hs : s.val = .unit
    · have he : s = (⟨.unit, trivial⟩ : Term α) := Subtype.ext hs
      simp [termProduct, hs, he]
    · simp [termProduct, hs]

def source {α : Type*} (a : α) : Term α := ⟨.source a, trivial⟩
def termMarker {α : Type*} (s : Term α) : Term α := ⟨.mark s.val, s.property⟩

private def evalExpr {α : Type*} (U : M → M) (f : α → M) : Expr α → M
  | .unit => 1
  | .source a => f a
  | .mark s => U (evalExpr U f s)
  | .product s t => evalExpr U f s * evalExpr U f t

def evaluate {α : Type*} (U : M → M) (f : α → M) (s : Term α) : M := evalExpr U f s.val

private lemma eval_one {α : Type*} (f : α → M) : evaluate U f (1 : Term α) = 1 := rfl
private lemma eval_mark {α : Type*} (f : α → M) (s : Term α) :
    evaluate U f (termMarker s) = U (evaluate U f s) := rfl
private lemma eval_product {α : Type*} (f : α → M) (s t : Term α) :
    evaluate U f (s*t) = evaluate U f s * evaluate U f t := by
  classical
  change evalExpr U f (termProduct s t).val = _
  unfold termProduct
  split_ifs with hs ht
  · simp [evaluate, hs, evalExpr]
  · simp [evaluate, ht, evalExpr]
  · rfl

private def exprBudget {α : Type*} (b : α → ℝ) (o : ℝ) : Expr α → ℝ
  | .unit => 0
  | .source a => b a
  | .mark s => 9*exprBudget b o s + 24*o
  | .product s t => 3*(exprBudget b o s+exprBudget b o t)

def budget {α : Type*} (f : α → M) (U : M → M) (c : M → M → ℝ) (s : Term α) : ℝ :=
  exprBudget (fun a => 3*(c (f a) 1+c 1 (f a))+6*omega U c) (omega U c) s.val

private lemma eval_budget {α : Type*} {V : Type*} [MulOneClass V]
    {v : V → V} {d : V → V → ℝ} (hd : RawCost v d)
    (g : α → V) (b : α → ℝ) (o : ℝ)
    (ho : omega v d ≤ o)
    (hg : ∀ a, d (g a) 1+d 1 (g a) ≤ b a)
    (s : Expr α) :
    d (evalExpr v g s) 1+d 1 (evalExpr v g s) ≤ exprBudget b o s := by
  induction s with
  | unit => simp [evalExpr, exprBudget, hd.diagonal]
  | source a => exact hg a
  | mark s ih =>
    have hf := iterate_budget hd (evalExpr v g s) 1
    have hr := iterate_budget (transpose hd) (evalExpr v g s) 1
    have he : omega v (fun a b => d b a) = omega v d := by unfold omega; ring
    rw [he] at hr
    simp only [Function.iterate_one] at hf hr
    dsimp [evalExpr, exprBudget]
    linarith
  | product s t ihs iht =>
    have hf := single hd (evalExpr v g s) 1 (evalExpr v g t) 1
    have hr := single hd 1 (evalExpr v g s) 1 (evalExpr v g t)
    simp only [one_mul, mul_one] at hf hr
    dsimp [evalExpr, exprBudget]
    linarith

private lemma array_term_budget {α : Type*} (h : RawCost U c) (f : α → M)
    (N : ℕ) (hN : 0 < N) (s : Term α) :
    arrayCost c N (evaluate (arrayMarker U) (fun a => gamma U N (f a)) s) 1 +
      arrayCost c N 1 (evaluate (arrayMarker U) (fun a => gamma U N (f a)) s) ≤
      budget f U c s := by
  have ho : omega U c/N ≤ omega U c := by
    apply div_le_self (omega_nonneg h)
    exact_mod_cast hN
  apply eval_budget (array_raw h N) _ _ _ _ _ s.val
  · rw [array_omega N hN]
    exact ho
  · intro a
    have hh := (raw_replication h N hN).2.2.2.1 (f a)
    rcases hh with ⟨hf, hr⟩
    simp only [mul_div_assoc] at hf hr
    linarith

private lemma pair_budget {α : Type*} (h : RawCost U c) (f : α → M)
    (N : ℕ) (hN : 0 < N) (s t : Term α) :
    arrayCost c N (evaluate (arrayMarker U) (fun a => gamma U N (f a)) s)
      (evaluate (arrayMarker U) (fun a => gamma U N (f a)) t) ≤
      3*(budget f U c s+budget f U c t) := by
  have hs := array_term_budget h f N hN s
  have ht := array_term_budget h f N hN t
  have hb := unit_compare (array_raw h N)
    (evaluate (arrayMarker U) (fun a => gamma U N (f a)) s)
    (evaluate (arrayMarker U) (fun a => gamma U N (f a)) t)
  have hn₁ := (array_raw h N).nonneg 1
    (evaluate (arrayMarker U) (fun a => gamma U N (f a)) s)
  have hn₂ := (array_raw h N).nonneg
    (evaluate (arrayMarker U) (fun a => gamma U N (f a)) t) 1
  linarith

private lemma term_induction {α : Type*} (P : Term α → Prop)
    (hunit : P 1) (hsource : ∀ a, P (source a))
    (hmark : ∀ s, P s → P (termMarker s))
    (hmul : ∀ s t, P s → P t → P (s*t)) (s : Term α) : P s := by
  classical
  have hall (e : Expr α) : ∀ he : Normal e, P ⟨e, he⟩ := by
    induction e with
    | unit => intro he; exact hunit
    | source a => intro he; exact hsource a
    | mark e ih => intro he; exact hmark ⟨e, he⟩ (ih he)
    | product e g ihe ihg =>
      intro he
      have hp := hmul ⟨e, he.1⟩ ⟨g, he.2.1⟩ (ihe he.1) (ihg he.2.1)
      simpa [HMul.hMul, Mul.mul, termProduct, he.2.2.1, he.2.2.2] using hp
  exact hall s.val s.property

def modelCost {α : Type*} (f : α → M) (U : M → M) (c : M → M → ℝ)
    (N : ℕ) (s t : Term α) : ℝ :=
  arrayCost c N (evaluate (arrayMarker U) (fun a => gamma U N (f a)) s)
    (evaluate (arrayMarker U) (fun a => gamma U N (f a)) t)

private lemma model_raw {α : Type*} (h : RawCost U c) (f : α → M) (N : ℕ) :
    RawCost (termMarker (α := α)) (modelCost f U c N) := by
  constructor
  · intro s t; exact (array_raw h N).nonneg _ _
  · intro s; exact (array_raw h N).diagonal _
  · intro a b u v
    simpa only [modelCost, eval_product, eval_mark] using
      (array_raw h N).balance
        (evaluate (arrayMarker U) (fun a => gamma U N (f a)) a)
        (evaluate (arrayMarker U) (fun a => gamma U N (f a)) b)
        (evaluate (arrayMarker U) (fun a => gamma U N (f a)) u)
        (evaluate (arrayMarker U) (fun a => gamma U N (f a)) v)

private lemma model_omega {α : Type*} (f : α → M) (N : ℕ) (hN : 0 < N) :
    omega (termMarker (α := α)) (modelCost f U c N) = omega U c/N := by
  simpa only [omega, modelCost, eval_mark, eval_one] using (array_omega (U := U) (c := c) N hN)

private lemma model_matrix {α : Type*} (h : RawCost U c) (f : α → M)
    (N : ℕ) (hN : 0 < N) (a b : α) :
    modelCost f U c N (source a) (source b) = c (f a) (f b) :=
  gamma_matrix h N hN (f a) (f b)

private lemma expr_nonneg {α : Type*} (b : α → ℝ) (o : ℝ)
    (hb : ∀ a, 0 ≤ b a) (ho : 0 ≤ o) (s : Expr α) : 0 ≤ exprBudget b o s := by
  induction s with
  | unit => exact le_rfl
  | source a => exact hb a
  | mark s ih => dsimp [exprBudget]; positivity
  | product s t ihs iht => dsimp [exprBudget]; positivity

/-- Finite budgets are uniform in depth and compatible with the actual unit reduction. -/
theorem normal_form_budgets {α : Type*} (h : RawCost U c) (f : α → M) :
    budget f U c 1 = 0 ∧
    (∀ a, budget f U c (source a) = 3*(c (f a) 1+c 1 (f a))+6*omega U c) ∧
    (∀ s, budget f U c (termMarker s) = 9*budget f U c s+24*omega U c) ∧
    (∀ s t, budget f U c (s*t) ≤ 3*(budget f U c s+budget f U c t)) ∧
    (∀ N, 0 < N → ∀ s t : Term α,
      modelCost f U c N s 1+modelCost f U c N 1 s ≤ budget f U c s ∧
      modelCost f U c N s t ≤ 3*(budget f U c s+budget f U c t)) := by
  classical
  have hn (s : Term α) : 0 ≤ budget f U c s := by
    apply expr_nonneg
    · intro a
      have ho := omega_nonneg h
      have hf := h.nonneg (f a) 1
      have hr := h.nonneg 1 (f a)
      positivity
    · exact omega_nonneg h
  refine ⟨rfl, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro s t
    change exprBudget _ _ (termProduct s t).val ≤ _
    unfold termProduct
    split_ifs with hs ht
    · have hz : budget f U c s = 0 := by simp [budget, hs, exprBudget]
      change budget f U c t ≤ _
      rw [hz]
      linarith [hn t]
    · have hz : budget f U c t = 0 := by simp [budget, ht, exprBudget]
      change budget f U c s ≤ _
      rw [hz]
      linarith [hn s]
    · exact le_rfl
  · intro N hN s t
    exact ⟨by simpa only [modelCost, eval_one] using array_term_budget h f N hN s,
      pair_budget h f N hN s t⟩

open Filter Topology

/-- One common subsequence of actual coordinate models yields a genuine zero-drift
model on all unit normal forms and retains every ordered source comparison. -/
theorem raw_zero_drift {α : Type*} [Finite α] (h : RawCost U c) (f : α → M) :
    ∃ (d : Term α → Term α → ℝ) (ρ : ℕ → ℕ),
      StrictMono ρ ∧
      (∀ s t, Tendsto (fun l => modelCost f U c (ρ l+1) s t) atTop (𝓝 (d s t))) ∧
      RawCost termMarker d ∧ omega termMarker d = 0 ∧
      (∀ a b, d (source a) (source b) = c (f a) (f b)) ∧
      (∀ a, (source a : Term α) ≠ 1) ∧
      termMarker (1 : Term α) ≠ 1 ∧
      (∀ P : Term α → Prop, P 1 → (∀ a, P (source a)) →
        (∀ s, P s → P (termMarker s)) →
        (∀ s t, P s → P t → P (s*t)) → ∀ s, P s) := by
  classical
  let C (p : Term α × Term α) := 3*(budget f U c p.1+budget f U c p.2)
  let K : Set ((Term α × Term α) → ℝ) := {d | ∀ p, d p ∈ Set.Icc 0 (C p)}
  have hk : IsCompact K := isCompact_pi_infinite (fun _ => isCompact_Icc)
  let seq (n : ℕ) (p : Term α × Term α) := modelCost f U c (n+1) p.1 p.2
  have hseq (n : ℕ) : seq n ∈ K := by
    intro p
    exact ⟨(model_raw h f (n+1)).nonneg p.1 p.2,
      ((normal_form_budgets h f).2.2.2.2 (n+1) (Nat.succ_pos n) p.1 p.2).2⟩
  obtain ⟨d, hd, ρ, hρ, hlim⟩ := hk.tendsto_subseq hseq
  have hl (s t : Term α) :
      Tendsto (fun l => modelCost f U c (ρ l+1) s t) atTop (𝓝 (d (s,t))) :=
    tendsto_pi_nhds.mp hlim (s,t)
  refine ⟨fun s t => d (s,t), ρ, hρ, hl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro s t; exact (hd (s,t)).1
    · intro s
      have hz : Tendsto (fun l => modelCost f U c (ρ l+1) s s) atTop (𝓝 0) := by
        simpa only [(model_raw h f _).diagonal] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
      exact tendsto_nhds_unique (hl s s) hz
    · intro a b u v
      have hleft := ((hl (a*u) (b*v)).add (hl (a*termMarker u) (b*termMarker v))).add
        (hl (a*termMarker (termMarker u)) (b*termMarker (termMarker v)))
      have hright := ((hl a b).const_mul 3).add ((hl u v).const_mul 3)
      apply tendsto_nhds_unique hleft
      exact hright.congr' (Eventually.of_forall fun l => ((model_raw h f (ρ l+1)).balance a b u v).symm)
  · have hh := (((hl (termMarker 1) 1).add (hl (termMarker (termMarker 1)) 1)).add
      (hl 1 (termMarker 1))).add (hl 1 (termMarker (termMarker 1)))
    have hzero : Tendsto (fun l => omega termMarker (modelCost f U c (ρ l+1))) atTop (𝓝 0) := by
      simp_rw [model_omega f _ (Nat.succ_pos _)]
      exact (tendsto_const_div_atTop_nhds_zero_nat (omega U c)).comp
        ((tendsto_add_atTop_nat 1).comp hρ.tendsto_atTop)
    exact tendsto_nhds_unique hh hzero
  · intro a b
    have he : Tendsto (fun l => modelCost f U c (ρ l+1) (source a) (source b))
        atTop (𝓝 (c (f a) (f b))) := by
      simpa only [model_matrix h f _ (Nat.succ_pos _)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => c (f a) (f b)) atTop (𝓝 (c (f a) (f b))))
    exact tendsto_nhds_unique (hl _ _) he
  · intro a he
    have hh := congrArg Subtype.val he
    cases hh
  · intro he
    have hh := congrArg Subtype.val he
    cases hh
  · intro P hunit hsource hmark hmul s
    exact term_induction P hunit hsource hmark hmul s

end D5.S3.Quantum.Completion.RawUnanchoredReplication
