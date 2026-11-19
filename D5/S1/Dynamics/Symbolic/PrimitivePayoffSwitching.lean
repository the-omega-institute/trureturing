/- GID: D5/S1/Dynamics/Symbolic/PrimitivePayoffSwitching
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PrimitivePayoffSwitching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reweighted switching costs bound mechanical endpoint minima and force bounded discrepancy. -/

/- admission_basis: escape-witness
   reweightedStep_ge supplies a uniform lower bound of one at every switch.
   mechanical_cost_ge_boundary sums that bound after transferring the signed
   potential across each edge. It is used both to bound attained endpoint
   minima below by -1 and to prove constant paths minimize at equal endpoints.
   The independent endpoint-patched path in exists_endpoint_response_cost_le
   gives the complementary upper estimate used in strict four-entry improvement.
   The count conversion discrepancy_prefix_eq_sum_range is consumed by
   MeyerovitchYoungQ62.shift_has_no_positive_period. cost_constant is consumed
   by mechanical_endpointMinimum_diagonal and exists_endpoint_response_cost_le.
   Existing mechanical letters and their zero-or-one law come from
   D5/S1/Words/Mechanical/MechanicalBalance. -/

import D5.S1.Words.Mechanical.MechanicalBalance
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi

/-!
Finite-word core for Meyerovitch–Young, arXiv:2603.21449v1, Question 6.2.
Alice's two loops are indexed by Bool. For Bob there is one directed edge for
each ordered pair of Bool states. A walk of n edges thus has n + 1 states.
The strict comparison in §4 is at every Bob endpoint pair. The windows in
(19) have length at least two.
-/

open scoped BigOperators
open D5.S1.Words.Mechanical

set_option autoImplicit false

namespace PrimitivePayoffSwitching

noncomputable section

/-- Alice's loop label as a real number. -/
def bit (b : Bool) : ℝ := if b = true then 1 else 0

def sgn : Bool → ℝ
  | false => -1
  | true => 1

def switchCost (s t : Bool) : ℝ := if s = t then 0 else 2

def payoff (α : ℝ) (b s t : Bool) : ℝ :=
  sgn s * (bit b - α) + switchCost s t

abbrev Response (n : ℕ) := Fin (n + 1) → Bool

abbrev EndpointResponse (n : ℕ) (s t : Bool) :=
  {p : Response n // p 0 = s ∧ p (Fin.last n) = t}

def cost {n : ℕ} (α : ℝ) (w : Fin n → Bool) (p : Response n) : ℝ :=
  ∑ i : Fin n, payoff α (w i) (p i.castSucc) (p i.succ)

def discrepancy {n : ℕ} (α : ℝ) (w : Fin n → Bool) : ℝ :=
  ∑ i : Fin n, (bit (w i) - α)

private theorem bit_eq_toNat (b : Bool) : bit b = (b.toNat : ℝ) := by
  cases b <;> norm_num [bit, Bool.toNat]

/-- Count formula for a finite window supplied as a word on natural indices. -/
theorem discrepancy_prefix_eq_sum_range (α : ℝ) (w : ℕ → Bool) (n : ℕ) :
    discrepancy α (fun i : Fin n => w i.val) =
      (∑ j ∈ Finset.range n, ((w j).toNat : ℝ)) - (n : ℝ) * α := by
  rw [discrepancy, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => bit (w j)) n]
  simp [bit_eq_toNat, nsmul_eq_mul]

theorem cost_constant {n : ℕ} (α : ℝ) (w : Fin n → Bool) (s : Bool) :
    cost α w (fun _ => s) = sgn s * discrepancy α w := by
  rw [discrepancy, Finset.mul_sum]
  simp [cost, payoff, switchCost]

private theorem exists_endpoint_minimizer {n : ℕ} (α : ℝ) (w : Fin n → Bool)
    (hn : 0 < n) (s t : Bool) :
    ∃ p : EndpointResponse n s t, ∀ r : EndpointResponse n s t,
      cost α w p.val ≤ cost α w r.val := by
  classical
  let p : Response n := fun j => if j.val = 0 then s else t
  have hp : p 0 = s ∧ p (Fin.last n) = t := by
    constructor
    · simp [p]
    · simp [p, Nat.ne_of_gt hn]
  obtain ⟨q, _, hq⟩ := (Finset.univ : Finset (EndpointResponse n s t)).exists_min_image
    (fun r => cost α w r.val) ⟨⟨p, hp⟩, Finset.mem_univ _⟩
  exact ⟨q, fun r => hq r (Finset.mem_univ r)⟩

/-- The minimum over the finite, nonempty class of walks with the given endpoints. -/
def endpointMinimum {n : ℕ} (α : ℝ) (w : Fin n → Bool) (hn : 0 < n)
    (s t : Bool) : ℝ :=
  cost α w (Classical.choose (exists_endpoint_minimizer α w hn s t)).val

theorem endpointMinimum_spec {n : ℕ} (α : ℝ) (w : Fin n → Bool) (hn : 0 < n)
    (s t : Bool) :
    ∃ p : EndpointResponse n s t, cost α w p.val = endpointMinimum α w hn s t ∧
      ∀ r : EndpointResponse n s t, endpointMinimum α w hn s t ≤ cost α w r.val := by
  let h := exists_endpoint_minimizer α w hn s t
  exact ⟨Classical.choose h, rfl, Classical.choose_spec h⟩

def StrictlyImproves {n : ℕ} (α : ℝ) (hn : 0 < n) (w v : Fin n → Bool) : Prop :=
  ∀ s t : Bool, endpointMinimum α w hn s t < endpointMinimum α v hn s t

def Nonimprovable {n : ℕ} (α : ℝ) (hn : 0 < n) (w : Fin n → Bool) : Prop :=
  ∀ v : Fin n → Bool, ¬ StrictlyImproves α hn w v

def mechanicalWindow (α ρ : ℝ) (start n : ℕ) : Fin n → Bool :=
  fun i => lowerMechanicalWord α ρ (start + i.val)

/-- The centered fractional part at a boundary between mechanical letters. -/
def potential (α ρ : ℝ) (i : ℕ) : ℝ :=
  Int.fract (ρ + (i : ℝ) * α) - 1 / 2

private theorem potential_bounds (α ρ : ℝ) (i : ℕ) :
    -(1 / 2 : ℝ) ≤ potential α ρ i ∧ potential α ρ i ≤ 1 / 2 := by
  unfold potential
  constructor
  · linarith only [Int.fract_nonneg (ρ + (i : ℝ) * α)]
  · linarith only [Int.fract_lt_one (ρ + (i : ℝ) * α)]

private theorem mechanical_bit_sub_alpha {α ρ : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (i : ℕ) :
    bit (lowerMechanicalWord α ρ i) - α = potential α ρ i - potential α ρ (i + 1) := by
  have hbit : bit (lowerMechanicalWord α ρ i) = (lowerMechanicalLetter α ρ i : ℝ) := by
    rcases lowerMechanicalLetter_eq_zero_or_one (rho := ρ) hα₀ hα₁ i with hzero | hone
    · have hfalse : lowerMechanicalWord α ρ i ≠ true := by
        intro h
        have hletter := (lowerMechanicalWord_eq_true_iff α ρ i).mp h
        omega
      simp [bit, hfalse, hzero]
    · have htrue := (lowerMechanicalWord_eq_true_iff α ρ i).mpr hone
      simp [bit, htrue, hone]
  have harg : ρ + ((i + 1 : ℕ) : ℝ) * α = ρ + (i : ℝ) * α + α := by
    push_cast
    ring
  rw [hbit]
  simp only [potential, lowerMechanicalLetter, Int.cast_sub]
  linarith only [Int.floor_add_fract (ρ + (i : ℝ) * α),
    Int.floor_add_fract (ρ + ((i + 1 : ℕ) : ℝ) * α), harg]

/-- The cost after transferring the signed potential across an edge. -/
def reweightedStep (q : ℝ) (s t : Bool) : ℝ :=
  (sgn t - sgn s) * q + switchCost s t

theorem reweightedStep_ge {q : ℝ} (hq₀ : -(1 / 2 : ℝ) ≤ q) (hq₁ : q ≤ 1 / 2)
    (s t : Bool) : (if s = t then 0 else 1 : ℝ) ≤ reweightedStep q s t := by
  cases s <;> cases t <;> norm_num [reweightedStep, sgn, switchCost] <;> linarith

private theorem sum_state_differences {n : ℕ} (g : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (g i.succ - g i.castSucc)) = g (Fin.last n) - g 0 := by
  rw [Finset.sum_sub_distrib]
  linarith only [Fin.sum_univ_succ g, Fin.sum_univ_castSucc g]

theorem mechanical_cost_reweight {α ρ : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    {n : ℕ} (start : ℕ) (p : Response n) :
    cost α (mechanicalWindow α ρ start n) p +
        (sgn (p (Fin.last n)) * potential α ρ (start + n) -
          sgn (p 0) * potential α ρ start) =
      ∑ i : Fin n, reweightedStep (potential α ρ (start + i.val + 1))
        (p i.castSucc) (p i.succ) := by
  let g (j : Fin (n + 1)) := sgn (p j) * potential α ρ (start + j.val)
  have hsum :
      (∑ i : Fin n,
        (payoff α (mechanicalWindow α ρ start n i) (p i.castSucc) (p i.succ) +
          (g i.succ - g i.castSucc))) =
      ∑ i : Fin n, reweightedStep (potential α ρ (start + i.val + 1))
        (p i.castSucc) (p i.succ) := by
    apply Finset.sum_congr rfl
    intro i _
    let k := start + i.val
    let s := p i.castSucc
    let t := p i.succ
    change payoff α (lowerMechanicalWord α ρ k) s t +
        (sgn t * potential α ρ (k + 1) - sgn s * potential α ρ k) =
      reweightedStep (potential α ρ (k + 1)) s t
    rw [payoff, mechanical_bit_sub_alpha hα₀ hα₁, reweightedStep]
    ring
  rw [Finset.sum_add_distrib, sum_state_differences] at hsum
  change cost α (mechanicalWindow α ρ start n) p + (g (Fin.last n) - g 0) = _ at hsum
  simpa only [g, Fin.val_last, Fin.val_zero, Nat.add_zero] using hsum

theorem mechanical_cost_ge_boundary {α ρ : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    {n : ℕ} (start : ℕ) (p : Response n) :
    sgn (p 0) * potential α ρ start - sgn (p (Fin.last n)) * potential α ρ (start + n) ≤
      cost α (mechanicalWindow α ρ start n) p := by
  have hsum : 0 ≤ ∑ i : Fin n, reweightedStep (potential α ρ (start + i.val + 1))
      (p i.castSucc) (p i.succ) := by
    apply Finset.sum_nonneg
    intro i _
    obtain ⟨hl, hu⟩ := potential_bounds α ρ (start + i.val + 1)
    have hnonneg : (0 : ℝ) ≤ (if p i.castSucc = p i.succ then 0 else 1) := by
      split <;> norm_num
    exact hnonneg.trans (reweightedStep_ge hl hu _ _)
  linarith only [hsum, mechanical_cost_reweight (ρ := ρ) hα₀ hα₁ start p]

private theorem signed_potential_bounds (α ρ : ℝ) (i : ℕ) (s : Bool) :
    -(1 / 2 : ℝ) ≤ sgn s * potential α ρ i ∧
      sgn s * potential α ρ i ≤ 1 / 2 := by
  obtain ⟨hl, hu⟩ := potential_bounds α ρ i
  cases s <;> simp only [sgn, neg_one_mul, one_mul] <;> constructor <;> linarith

theorem mechanical_cost_ge_neg_one {α ρ : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    {n : ℕ} (start : ℕ) (p : Response n) :
    -1 ≤ cost α (mechanicalWindow α ρ start n) p := by
  linarith only [(signed_potential_bounds α ρ start (p 0)).1,
    (signed_potential_bounds α ρ (start + n) (p (Fin.last n))).2,
    mechanical_cost_ge_boundary (ρ := ρ) hα₀ hα₁ start p]

theorem mechanical_endpointMinimum_ge_neg_one {α ρ : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    {n : ℕ} (hn : 0 < n) (start : ℕ) (s t : Bool) :
    -1 ≤ endpointMinimum α (mechanicalWindow α ρ start n) hn s t := by
  obtain ⟨p, hp, _⟩ := endpointMinimum_spec α (mechanicalWindow α ρ start n) hn s t
  rw [← hp]
  exact mechanical_cost_ge_neg_one hα₀ hα₁ start p.val

theorem mechanical_constant_minimizes {α ρ : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    {n : ℕ} (start : ℕ) (s : Bool) (p : EndpointResponse n s s) :
    cost α (mechanicalWindow α ρ start n) (fun _ => s) ≤
      cost α (mechanicalWindow α ρ start n) p.val := by
  have hconstant := mechanical_cost_reweight (ρ := ρ) hα₀ hα₁ start
    (fun _ : Fin (n + 1) => s)
  have hbound := mechanical_cost_ge_boundary (ρ := ρ) hα₀ hα₁ start p.val
  simp [reweightedStep, switchCost] at hconstant
  rw [p.property.1, p.property.2] at hbound
  linarith only [hconstant, hbound]

theorem mechanical_endpointMinimum_diagonal {α ρ : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    {n : ℕ} (hn : 0 < n) (start : ℕ) (s : Bool) :
    endpointMinimum α (mechanicalWindow α ρ start n) hn s s =
      sgn s * discrepancy α (mechanicalWindow α ρ start n) := by
  let c : EndpointResponse n s s := ⟨fun _ => s, ⟨rfl, rfl⟩⟩
  obtain ⟨p, hp, hmin⟩ := endpointMinimum_spec α (mechanicalWindow α ρ start n) hn s s
  rw [← cost_constant α (mechanicalWindow α ρ start n) s]
  exact le_antisymm (hmin c)
    ((mechanical_constant_minimizes hα₀ hα₁ start s p).trans_eq hp)

theorem mechanical_nonimprovable {α ρ : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    {n : ℕ} (hn : 0 < n) (start : ℕ) :
    Nonimprovable α hn (mechanicalWindow α ρ start n) := by
  intro v h
  have hdiag (s : Bool) :
      sgn s * discrepancy α (mechanicalWindow α ρ start n) < sgn s * discrepancy α v := by
    let c : EndpointResponse n s s := ⟨fun _ => s, ⟨rfl, rfl⟩⟩
    obtain ⟨_, _, hmin⟩ := endpointMinimum_spec α v hn s s
    have hs := (h s s).trans_le (hmin c)
    simpa only [mechanical_endpointMinimum_diagonal (ρ := ρ) hα₀ hα₁ hn start s,
      c, cost_constant] using hs
  have hfalse := hdiag false
  have htrue := hdiag true
  simp only [sgn, neg_one_mul, one_mul] at hfalse htrue
  linarith only [hfalse, htrue]

private theorem first_edge_le {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1) (b s h : Bool) :
    payoff α b s h ≤ sgn h * (bit b - α) + 4 := by
  cases b <;> cases s <;> cases h <;> norm_num [payoff, bit, sgn, switchCost] <;> linarith

/-- A response with prescribed endpoints and all interior states equal to h
costs at most six more than the constant h response. -/
theorem exists_endpoint_response_cost_le {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    {n : ℕ} (hn : 2 ≤ n) (w : Fin n → Bool) (s h t : Bool) :
    ∃ p : EndpointResponse n s t, cost α w p.val ≤ sgn h * discrepancy α w + 6 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
  let p : Response (m + 2) := fun j =>
    if j.val = 0 then s else if j.val = m + 2 then t else h
  have hp₀ : p 0 = s := by simp [p]
  have hpₙ : p (Fin.last (m + 2)) = t := by
    simp [p]
  let edge (i : Fin (m + 2)) := payoff α (w i) (p i.castSucc) (p i.succ)
  let base (i : Fin (m + 2)) := payoff α (w i) h h
  have hfirst : edge 0 ≤ base 0 + 4 := by
    have hsource : p (0 : Fin (m + 2)).castSucc = s := by
      change p 0 = s
      exact hp₀
    have htarget : p (0 : Fin (m + 2)).succ = h := by
      change (if (1 : ℕ) = 0 then s else if (1 : ℕ) = m + 2 then t else h) = h
      simp
    dsimp only [edge, base]
    rw [hsource, htarget]
    simpa [payoff, switchCost] using first_edge_le hα₀ hα₁ (w 0) s h
  have hlast : edge (Fin.last m).succ ≤ base (Fin.last m).succ + 2 := by
    have hsource : p (Fin.last m).succ.castSucc = h := by
      have hne₀ : m + 1 ≠ 0 := by omega
      have hneₙ : m + 1 ≠ m + 2 := by omega
      change (if m + 1 = 0 then s else if m + 1 = m + 2 then t else h) = h
      simp only [ite_eq_right hne₀, ite_eq_right hneₙ]
    have htarget : p (Fin.last m).succ.succ = t := by
      exact hpₙ
    dsimp only [edge, base]
    rw [hsource, htarget]
    by_cases heq : h = t <;> simp [payoff, switchCost, heq]
  have hmiddle (i : Fin m) : edge i.castSucc.succ = base i.castSucc.succ := by
    have hi := i.isLt
    have hne₁ : i.val + 1 ≠ 0 := by omega
    have hne₂ : i.val + 1 ≠ m + 2 := by omega
    have hne₃ : i.val + 1 + 1 ≠ 0 := by omega
    have hne₄ : i.val + 1 + 1 ≠ m + 2 := by omega
    have hsource : p i.castSucc.succ.castSucc = h := by
      change (if i.val + 1 = 0 then s else if i.val + 1 = m + 2 then t else h) = h
      simp only [ite_eq_right hne₁, ite_eq_right hne₂]
    have htarget : p i.castSucc.succ.succ = h := by
      change (if i.val + 1 + 1 = 0 then s else
        if i.val + 1 + 1 = m + 2 then t else h) = h
      simp only [ite_eq_right hne₃, ite_eq_right hne₄]
    simp only [edge, base, hsource, htarget]
  have hsum : (∑ i, edge i) ≤ (∑ i, base i) + 6 := by
    rw [Fin.sum_univ_succ edge, Fin.sum_univ_succ base,
      Fin.sum_univ_castSucc (fun i : Fin (m + 1) => edge i.succ),
      Fin.sum_univ_castSucc (fun i : Fin (m + 1) => base i.succ)]
    have heq : (∑ i : Fin m, edge i.castSucc.succ) = ∑ i : Fin m, base i.castSucc.succ :=
      Finset.sum_congr rfl (fun i _ => hmiddle i)
    rw [heq]
    linarith only [hfirst, hlast]
  refine ⟨⟨p, ⟨hp₀, hpₙ⟩⟩, ?_⟩
  rw [← cost_constant α w h]
  exact hsum

theorem large_discrepancy_improved_by_mechanicalWindow {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    {n : ℕ} (hn : 2 ≤ n) (w : Fin n → Bool) (hlarge : 7 < |discrepancy α w|)
    (ρ : ℝ) (start : ℕ) :
    StrictlyImproves α (show 0 < n by omega) w (mechanicalWindow α ρ start n) := by
  have hn₀ : 0 < n := by omega
  have hfavorable : ∃ h : Bool, sgn h * discrepancy α w = -|discrepancy α w| := by
    by_cases hge : 0 ≤ discrepancy α w
    · exact ⟨false, by simp [sgn, abs_of_nonneg hge]⟩
    · exact ⟨true, by simp [sgn, abs_of_neg (lt_of_not_ge hge)]⟩
  obtain ⟨h, hh⟩ := hfavorable
  intro s t
  obtain ⟨p, hp⟩ := exists_endpoint_response_cost_le hα₀ hα₁ hn w s h t
  obtain ⟨_, _, hw⟩ := endpointMinimum_spec α w hn₀ s t
  have hupp : endpointMinimum α w hn₀ s t < -1 := by
    have hmin := hw p
    linarith only [hmin, hp, hh, hlarge]
  exact hupp.trans_le (mechanical_endpointMinimum_ge_neg_one hα₀ hα₁ hn₀ start s t)

theorem nonimprovable_abs_discrepancy_le_seven {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    {n : ℕ} (hn : 2 ≤ n) (w : Fin n → Bool)
    (hw : Nonimprovable α (show 0 < n by omega) w) : |discrepancy α w| ≤ 7 := by
  by_contra hlarge
  exact hw (mechanicalWindow α 0 0 n)
    (large_discrepancy_improved_by_mechanicalWindow hα₀ hα₁ hn w (lt_of_not_ge hlarge) 0 0)

end

end PrimitivePayoffSwitching
