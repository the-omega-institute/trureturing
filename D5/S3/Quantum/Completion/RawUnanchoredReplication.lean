/- GID: D5/S3/Quantum/Completion/RawUnanchoredReplication
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/RawUnanchoredReplication
   mirror-E: none(waiver:raw-unital-magma)
   anchors: []
   utility: none
   digest: Synchronous arrays retain ordered comparisons and control costs to the actual unit. -/

module

public import D5.S3.QuadraticForms.ThreeWayBalance
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Mathlib.Tactic.DeriveCountable
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sequences

/-! Raw unanchored costs, common phases and literal coordinate arrays. -/

public section
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

private lemma sync_iter (h : RawCost U c) (n : ℕ) (x y : M) :
    c (U^[n] x) (U^[n] y) = c x y := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply', sync h] using ih

private lemma single (h : RawCost U c) (a b u v : M) :
    c (a * u) (b * v) ≤ 3 * (c a b + c u v) := by
  have hh := h.balance a b u v
  linarith [h.nonneg (a * U u) (b * U v), h.nonneg (a * U (U u)) (b * U (U v))]

private lemma unit_compare (h : RawCost U c) (x y : M) :
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

end D5.S3.Quantum.Completion.RawUnanchoredReplication
