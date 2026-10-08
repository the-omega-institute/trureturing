/- GID: D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A depth-free carry-slot machine preserves fair-tape labels and charges. -/

import D5.S3.Arith.FibonacciAtomic.CarryGraphRealization
import D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CarryGraphFiniteSampler

open scoped BigOperators ENNReal
open CarryGraphEmbedding MeasureTheory
open OptimalLawStrictSlope (alpha)
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)

local notation "S" => (fun m : ℕ => {s : State // IsState m s})
local notation "A" => (fun (m : ℕ) (s : State) => {a : Action // Legal m s a})
set_option quotPrecheck false in
local notation "P" => (fun m : ℕ => (s : S m) → A m s.val)
set_option quotPrecheck false in
local notation "labels" => (fun (m : ℕ) (s : State) (a : Action) =>
  Finset.sort (CarryGraphRealization.labelSet m ⟨fun _ => s, fun _ => a⟩ 0)
    (fun i j => i ≤ j))

/-- The state and action sequence of a legal stationary table, starting at a
specified legal carry state. -/
def policyPath (m : ℕ) (f : P m) (start : S m) : Path :=
  let step : S m → S m := fun s =>
    ⟨successor s.val (f s).val, (f s).property.2.2⟩
  ⟨fun d => (step^[d] start).val, fun d => (f (step^[d] start)).val⟩

/-- An active control stores a legal carry state and a slot strictly below its width. -/
def Active (m : ℕ) := {x : S m × ℕ // (x.2 : ℤ) < x.1.val.r}

/-- The initial control has width one, all labels equal, and slot zero. -/
def initial (m : ℕ) (hm : 2 ≤ m) : Sum (Active m) (Fin m) :=
  .inl ⟨(⟨root m, by dsimp [IsState, root]; omega⟩, 0), by simp [root]⟩

/-- Read one bit while active. The check on the continuing slot makes the function
 total; the simulation proves it always succeeds on the continuing branch. -/
def step (m : ℕ) (f : P m) (u : Bool) :
    Sum (Active m) (Fin m) → Sum (Active m) (Fin m)
  | .inr i => .inr i
  | .inl x =>
    let s := x.val.1
    let a := f s
    let L := labels m s.val a.val
    let z := 2 * x.val.2 + u.toNat
    if hz : z < L.length then .inr L[z]
    else
      let ns : S m := ⟨successor s.val a.val, a.property.2.2⟩
      if hj : ((z - L.length : ℕ) : ℤ) < ns.val.r then
        .inl ⟨(ns, z - L.length), hj⟩
      else .inl x

/-- Execution records the control and a separate invoice; the invoice is never
 supplied to the control transition. Returned controls consume no further bits. -/
def execute (m : ℕ) (f : P m) (start : Sum (Active m) (Fin m)) (tape : Tape) :
    ℕ → Sum (Active m) (Fin m) × ℕ
  | 0 => (start, 0)
  | d + 1 =>
    let prev := execute m f start tape d
    match prev.1 with
    | .inr _ => prev
    | .inl x => (step m f (tape d) (.inl x), prev.2 + 1)

/-- First output together with the invoice at that output, or no finite output. -/
noncomputable def sample (m : ℕ) (f : P m) (start : Sum (Active m) (Fin m))
    (tape : Tape) : Option (Fin m × ℕ) := by
  classical
  exact if h : ∃ d, (execute m f start tape d).1.isRight then
    ((execute m f start tape (Nat.find h)).1.getRight?).map
      (fun i => (i, (execute m f start tape (Nat.find h)).2))
  else none

/-- All active steps are charged, including every step on a divergent tape. -/
noncomputable def bill (m : ℕ) (f : P m) (start : Sum (Active m) (Fin m))
    (tape : Tape) : ℝ≥0∞ :=
  ∑' d : ℕ, if (execute m f start tape d).1.isLeft then 1 else 0


/-- On every tape, the bounded control follows the stationary path's scan,
including its returned label and invoice and every continuing carry slot. -/
theorem coupling (m : ℕ) (hm : 2 ≤ m) (f : P m) :
    let o : S m := ⟨root m, by dsimp [IsState, root]; omega⟩
    let γ := policyPath m f o
    ∀ tape d, match CarryGraphRealization.scan m γ tape d with
      | .inl returned => execute m f (initial m hm) tape d = (.inr returned.1, returned.2)
      | .inr j => ∃ x : Active m,
          execute m f (initial m hm) tape d = (.inl x, d) ∧
          x.val.1.val = γ.state d ∧ x.val.2 = j := by
  classical
  let o : S m := ⟨root m, by dsimp [IsState, root]; omega⟩
  let γ := policyPath m f o
  have hγ : IsRootPath m γ := by
    refine ⟨rfl, fun d => ⟨(f _).property, ?_⟩⟩
    exact congrArg Subtype.val (Function.iterate_succ_apply'
      (fun s : S m => ⟨successor s.val (f s).val, (f s).property.2.2⟩) d o)
  change ∀ tape d, match CarryGraphRealization.scan m γ tape d with
      | .inl returned => execute m f (initial m hm) tape d = (.inr returned.1, returned.2)
      | .inr j => ∃ x : Active m,
          execute m f (initial m hm) tape d = (.inl x, d) ∧
          x.val.1.val = γ.state d ∧ x.val.2 = j
  intro tape d
  induction d with
  | zero =>
    change ∃ x : Active m, (initial m hm, 0) = (.inl x, 0) ∧
      x.val.1.val = γ.state 0 ∧ x.val.2 = 0
    exact ⟨⟨(o, 0), by simp [o, root]⟩, rfl, rfl, rfl⟩
  | succ d ih =>
    cases hs : CarryGraphRealization.scan m γ tape d with
    | inl returned =>
      simp only [hs] at ih
      simp [CarryGraphRealization.scan, hs, execute, ih]
    | inr j =>
      simp only [hs] at ih
      obtain ⟨x, hx, hcore, hslot⟩ := ih
      have ha : (f x.val.1).val = γ.action d := by
        have hstate : x.val.1 =
            ((fun s : {s : State // IsState m s} =>
              ⟨successor s.val (f s).val, (f s).property.2.2⟩)^[d] o) :=
          Subtype.ext hcore
        exact congrArg (fun s : {s : State // IsState m s} => (f s).val) hstate
      have labels_eq :
          Finset.sort (CarryGraphRealization.labelSet m
            ⟨fun _ => x.val.1.val, fun _ => (f x.val.1).val⟩ 0) (fun i j => i ≤ j) =
          Finset.sort (CarryGraphRealization.labelSet m γ d) (fun i j => i ≤ j) := by
        congr 1
        ext i
        simp only [CarryGraphRealization.labelSet, hcore, ha]
      let L := Finset.sort (CarryGraphRealization.labelSet m γ d) (fun i j => i ≤ j)
      let z := 2 * j + (tape d).toNat
      have hc : (L.length : ℤ) = ones (γ.state d) (γ.action d) := by
        change ((Finset.sort (CarryGraphRealization.labelSet m γ d)
          (fun i j => i ≤ j)).length : ℤ) = _
        simpa only [Finset.length_sort] using (CarryGraphRealization.tree_layers m γ hγ).1 d
      have hnext : successor x.val.1.val (f x.val.1).val = γ.state (d + 1) := by
        rw [ha, hcore]
        exact (hγ.2 d).2.symm
      by_cases hz : z < L.length
      · have he : execute m f (initial m hm) tape (d + 1) = (.inr L[z], d + 1) := by
          have hz' := hz
          dsimp only [z, L] at hz'
          simp only [execute, hx, step, hslot, labels_eq,
            dif_pos hz']
          rfl
        simp only [CarryGraphRealization.scan, hs]
        change (match (if hz : z < L.length then
          Sum.inl (L[z], d + 1) else Sum.inr (z - L.length)) with
          | .inl returned => execute m f (initial m hm) tape (d + 1) =
              (.inr returned.1, returned.2)
          | .inr j => ∃ x : Active m,
              execute m f (initial m hm) tape (d + 1) = (.inl x, d + 1) ∧
              x.val.1.val = γ.state (d + 1) ∧ x.val.2 = j)
        rw [dif_pos hz]
        exact he
      · have hj : ((z - L.length : ℕ) : ℤ) <
            (successor x.val.1.val (f x.val.1).val).r := by
          have H := x.property
          have Hu : (tape d).toNat ≤ 1 := by cases tape d <;> decide
          have hn := congrArg State.r (hγ.2 d).2
          dsimp only [successor] at hn
          dsimp only [z]
          rw [hnext]
          rw [hslot, hcore] at H
          omega
        let y : Active m := ⟨(⟨successor x.val.1.val (f x.val.1).val,
          (f x.val.1).property.2.2⟩, z - L.length), hj⟩
        have he : execute m f (initial m hm) tape (d + 1) = (.inl y, d + 1) := by
          have hz' := hz
          have hj' := hj
          dsimp only [z, L] at hz' hj'
          simp only [execute, hx, step, hslot, labels_eq,
            dif_neg hz', dif_pos hj']
          rfl
        simp only [CarryGraphRealization.scan, hs]
        change (match (if hz : z < L.length then
          Sum.inl (L[z], d + 1) else Sum.inr (z - L.length)) with
          | .inl returned => execute m f (initial m hm) tape (d + 1) =
              (.inr returned.1, returned.2)
          | .inr j => ∃ x : Active m,
              execute m f (initial m hm) tape (d + 1) = (.inl x, d + 1) ∧
              x.val.1.val = γ.state (d + 1) ∧ x.val.2 = j)
        rw [dif_neg hz]
        exact ⟨y, he, hnext, rfl⟩

/-- A critical stationary carry table runs as a finite control, preserving every
 tape's labels, first-return invoice, tail events and optimal expected bit cost. -/
theorem result (m : ℕ) (hm : 2 ≤ m) :
    let o : S m := ⟨root m, by dsimp [IsState, root]; omega⟩
    ∀ f : P m,
      let γ := policyPath m f o
      let p : Fin m → ℝ := fun i => Real.ofDigits (CarryGraphRealization.labelDigit γ i)
      0 < anchorValue γ → pathCost γ = alpha m * anchorValue γ →
      IsRootPath m γ ∧
      Finite (Active m) ∧ Nat.card (Active m) ≤ m ^ 2 * (m - 1) / 2 ∧
      Nat.card (Fin m) = m ∧
      (∀ tape d, match CarryGraphRealization.scan m γ tape d with
        | .inl returned => execute m f (initial m hm) tape d = (.inr returned.1, returned.2)
        | .inr j => ∃ x : Active m,
            execute m f (initial m hm) tape d = (.inl x, d) ∧
            x.val.1.val = γ.state d ∧ x.val.2 = j) ∧
      (∀ tape, sample m f (initial m hm) tape = CarryGraphRealization.sample m γ tape ∧
        bill m f (initial m hm) tape = CarryGraphRealization.bill m γ tape) ∧
      (∀ i, 0 < p i) ∧ (∑ i, p i) = 1 ∧
      0 < anchorValue γ ∧ sInf (Set.range p) = anchorValue γ ∧
      (∀ i, ∃ q : ℚ, (q : ℝ) = p i) ∧
      (∀ i, p i = ∑' d : ℕ,
        (if i ∈ CarryGraphRealization.labelSet m γ d then (1 : ℝ) else 0) /
          (2 : ℝ) ^ (d + 1)) ∧
      (∀ tape (i : Fin m) d, sample m f (initial m hm) tape = some (i, d + 1) ↔
        (List.ofFn (fun j : Fin (d + 1) => tape j.val), i) ∈
          CarryGraphRealization.stopping m γ d) ∧
      (∀ tape (i : Fin m) n, sample m f (initial m hm) tape = some (i, n) →
        bill m f (initial m hm) tape = n) ∧
      (∀ i : Fin m, fairTape {tape | ∃ n, sample m f (initial m hm) tape = some (i, n)} =
        ENNReal.ofReal (p i)) ∧
      (∀ d, fairTape {tape | sample m f (initial m hm) tape = none ∨
        ∃ i n, sample m f (initial m hm) tape = some (i, n) ∧ d < n} =
          ENNReal.ofReal (((γ.state d).r : ℝ) / (2 : ℝ) ^ d)) ∧
      (∀ᵐ tape ∂fairTape, ∃ i n, sample m f (initial m hm) tape = some (i, n)) ∧
      (∫⁻ tape, bill m f (initial m hm) tape ∂fairTape) = ENNReal.ofReal (pathCost γ) ∧
      pathCost γ = DyadicSupportLines.cost p ∧
      DyadicSupportLines.cost p = alpha m * anchorValue γ := by
  classical
  let o : S m := ⟨root m, by dsimp [IsState, root]; omega⟩
  dsimp only
  intro f
  let γ := policyPath m f o
  let p : Fin m → ℝ := fun i => Real.ofDigits (CarryGraphRealization.labelDigit γ i)
  change 0 < anchorValue γ → pathCost γ = alpha m * anchorValue γ → _
  intro ht hC
  have hγ : IsRootPath m γ := by
    refine ⟨rfl, fun d => ⟨(f _).property, ?_⟩⟩
    exact congrArg Subtype.val (Function.iterate_succ_apply'
      (fun s : S m => ⟨successor s.val (f s).val, (f s).property.2.2⟩) d o)
  obtain ⟨_, hsum, ha, hminimum, hpositive, _, _, hleaf, hcharged,
    hlaw, htail, hterm, hbill, _, hlower, _⟩ :=
    CarryGraphRealization.result m hm γ hγ
  change p ⟨0, by omega⟩ = anchorValue γ at ha
  change (∑ i, p i) = 1 at hsum
  change ∀ i, anchorValue γ ≤ p i at hminimum
  change DyadicSupportLines.cost p ≤ pathCost γ at hlower
  let : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have hp : ∀ i, 0 < p i := hpositive ht
  have hcost_lower : alpha m * anchorValue γ ≤ DyadicSupportLines.cost p := by
    have H := OptimalLawStrictSlope.alpha_le m p hp hsum ⟨0, by omega⟩
      (fun i => by rw [ha]; exact hminimum i)
    rw [ha] at H
    exact (le_div_iff₀ ht).mp H
  have hratio : DyadicSupportLines.cost p = alpha m * anchorValue γ :=
    le_antisymm (hlower.trans_eq hC) hcost_lower
  have hcost : pathCost γ = DyadicSupportLines.cost p := hC.trans hratio.symm
  have hmin : sInf (Set.range p) = anchorValue γ := by
    apply le_antisymm
    · rw [← ha]
      exact csInf_le (Set.finite_range p).bddBelow ⟨⟨0, by omega⟩, rfl⟩
    · apply le_csInf (Set.range_nonempty p)
      rintro y ⟨i, rfl⟩
      exact hminimum i
  have finite_bound : Finite (Active m) ∧ Nat.card (Active m) ≤ m ^ 2 * (m - 1) / 2 := by
    let code : Active m → Fin m × (Σ r : Fin (m - 1), Fin (r.val + 1)) := fun x =>
      (⟨(x.val.1.val.e - 1).toNat, by
        have hs := x.val.1.property; dsimp [IsState] at hs; omega⟩,
       ⟨⟨(x.val.1.val.r - 1).toNat, by
           have hs := x.val.1.property; have hj := x.property
           dsimp [IsState] at hs; omega⟩,
         ⟨x.val.2, by
           have hj := x.property
           change x.val.2 < (x.val.1.val.r - 1).toNat + 1
           omega⟩⟩)
    have injective : Function.Injective code := by
      intro x y hxy
      have he := congrArg (fun x => x.1.val) hxy
      have hr := congrArg (fun x => x.2.1.val) hxy
      have hj := congrArg (fun x => x.2.2.val) hxy
      have hx := x.val.1.property
      have hy := y.val.1.property
      have hxs := x.property
      have hys := y.property
      dsimp [code, IsState] at he hr hj hx hy
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        have he' : x.val.1.val.e = y.val.1.val.e := by omega
        have hr' : x.val.1.val.r = y.val.1.val.r := by omega
        exact (show ∀ u v : State, u.r = v.r → u.e = v.e → u = v by
          intro u v hr he
          cases u
          cases v
          dsimp only at hr he
          cases hr
          cases he
          rfl) _ _ hr' he'
      · exact hj
    have sum : (∑ r : Fin (m - 1), (r.val + 1)) = m * (m - 1) / 2 := by
      rw [Fin.sum_univ_eq_sum_range (fun r => r + 1)]
      have H := Finset.sum_range_id_mul_two (m - 1)
      have hn : m - 1 - 1 + 2 = m := by omega
      have H' : 2 * (∑ r ∈ Finset.range (m - 1), (r + 1)) = m * (m - 1) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          smul_eq_mul, mul_one]
        nlinarith [H, hn]
      omega
    refine ⟨Finite.of_injective code injective, ?_⟩
    calc
      _ ≤ Nat.card (Fin m × (Σ r : Fin (m - 1), Fin (r.val + 1))) :=
        Nat.card_le_card_of_injective code injective
      _ = m * (∑ r : Fin (m - 1), (r.val + 1)) := by
        rw [Nat.card_prod, Nat.card_fin, Nat.card_sigma]
        simp only [Nat.card_fin]
      _ = m ^ 2 * (m - 1) / 2 := by
        rw [sum, ← Nat.mul_div_assoc _ (Nat.even_mul_pred_self m).two_dvd]
        congr 1
        ring
  have sim : ∀ tape d, match CarryGraphRealization.scan m γ tape d with
      | .inl returned => execute m f (initial m hm) tape d = (.inr returned.1, returned.2)
      | .inr j => ∃ x : Active m,
          execute m f (initial m hm) tape d = (.inl x, d) ∧
          x.val.1.val = γ.state d ∧ x.val.2 = j := coupling m hm f
  have observations : ∀ tape,
      sample m f (initial m hm) tape = CarryGraphRealization.sample m γ tape ∧
      bill m f (initial m hm) tape = CarryGraphRealization.bill m γ tape := by
    intro tape
    have stopped (d : ℕ) : (execute m f (initial m hm) tape d).1.isRight =
        (CarryGraphRealization.scan m γ tape d).isLeft := by
      have H := sim tape d
      cases hs : CarryGraphRealization.scan m γ tape d with
      | inl returned => simp only [hs] at H; simp [H]
      | inr j =>
        simp only [hs] at H
        obtain ⟨x, hx, _, _⟩ := H
        simp [hx]
    have active (d : ℕ) : (execute m f (initial m hm) tape d).1.isLeft =
        (CarryGraphRealization.scan m γ tape d).isRight := by
      have H := sim tape d
      cases hs : CarryGraphRealization.scan m γ tape d with
      | inl returned => simp only [hs] at H; simp [H]
      | inr j =>
        simp only [hs] at H
        obtain ⟨x, hx, _, _⟩ := H
        simp [hx]
    constructor
    · unfold sample CarryGraphRealization.sample
      split_ifs with hE hS hS
      · have findeq : Nat.find hE = Nat.find hS := by
          exact Nat.find_congr (Nat.find_spec hE) (fun n _ => by rw [stopped n])
        rw [findeq]
        have H := sim tape (Nat.find hS)
        have hs := Nat.find_spec hS
        cases he : CarryGraphRealization.scan m γ tape (Nat.find hS) with
        | inl returned =>
          simp only [he] at H
          simp [H]
        | inr j => simp [he] at hs
      · exact False.elim (hS (by simpa only [← stopped] using hE))
      · exact False.elim (hE (by simpa only [stopped] using hS))
      · rfl
    · unfold bill CarryGraphRealization.bill
      apply tsum_congr
      intro d
      rw [active]
  have rational : ∀ i, ∃ q : ℚ, (q : ℝ) = p i := by
    let next : {s : State // IsState m s} → {s : State // IsState m s} := fun s =>
      ⟨successor s.val (f s).val, (f s).property.2.2⟩
    change ∀ i : Fin m, ∃ q : ℚ, (q : ℝ) = Real.ofDigits (CarryGraphRealization.labelDigit γ i)
    let code : {s : State // IsState m s} →
        (Finset.Ico (0 : ℤ) m) × (Finset.Icc (1 : ℤ) m) := fun s =>
      (⟨s.val.r, by have hs := s.property; simp only [IsState] at hs
                    simp only [Finset.mem_Ico]; omega⟩,
       ⟨s.val.e, by have hs := s.property; simp only [IsState] at hs
                    simp only [Finset.mem_Icc]; omega⟩)
    have inj : Function.Injective code := by
      intro s t h
      have hr : s.val.r = t.val.r := congrArg (fun p => p.1.val) h
      have he : s.val.e = t.val.e := congrArg (fun p => p.2.val) h
      apply Subtype.ext
      exact (show ∀ u v : State, u.r = v.r → u.e = v.e → u = v by
        intro u v hr he
        cases u
        cases v
        dsimp only at hr he
        cases hr
        cases he
        rfl) _ _ hr he
    let : Finite {s : State // IsState m s} := Finite.of_injective code inj
    have collision : ∃ a b : ℕ, a < b ∧ next^[a] o = next^[b] o := by
      obtain ⟨a, b, hne, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun d : ℕ => next^[d] o)
      rcases lt_or_gt_of_ne hne with hab | hba
      · exact ⟨a, b, hab, he⟩
      · exact ⟨b, a, hba, he.symm⟩
    obtain ⟨a, b, hab, he⟩ := collision
    intro i
    let digits := CarryGraphRealization.labelDigit γ i
    have tails : (fun n => digits (n + a)) = (fun n => digits (n + b)) := by
      funext n
      have H : next^[n + a] o = next^[n + b] o := by
        rw [Function.iterate_add_apply, Function.iterate_add_apply, he]
      exact congrArg (fun s : {s : State // IsState m s} =>
        if i ∈ CarryGraphRealization.labelSet m ⟨fun _ => s.val, fun _ => (f s).val⟩ 0
        then (1 : Fin 2) else 0) H
    let qa : ℚ := ∑ j ∈ Finset.range a, (digits j).val / (2 : ℚ) ^ (j + 1)
    let qb : ℚ := ∑ j ∈ Finset.range b, (digits j).val / (2 : ℚ) ^ (j + 1)
    have castA : (qa : ℝ) = ∑ j ∈ Finset.range a, Real.ofDigitsTerm digits j := by
      dsimp only [qa]
      push_cast
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Real.ofDigitsTerm, Nat.cast_ofNat, div_eq_mul_inv]
    have castB : (qb : ℝ) = ∑ j ∈ Finset.range b, Real.ofDigitsTerm digits j := by
      dsimp only [qb]
      push_cast
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Real.ofDigitsTerm, Nat.cast_ofNat, div_eq_mul_inv]
    have denom : ((2 : ℝ) ^ a)⁻¹ - ((2 : ℝ) ^ b)⁻¹ ≠ 0 := by
      apply sub_ne_zero.mpr
      intro H
      have H' := inv_injective H
      exact (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hab).ne H'
    have headA := Real.ofDigits_eq_sum_add_ofDigits digits a
    have headB := Real.ofDigits_eq_sum_add_ofDigits digits b
    rw [← castA] at headA
    rw [← castB] at headB
    rw [tails] at headA
    refine ⟨(((2 : ℚ) ^ a)⁻¹ * qb - ((2 : ℚ) ^ b)⁻¹ * qa) /
      (((2 : ℚ) ^ a)⁻¹ - ((2 : ℚ) ^ b)⁻¹), ?_⟩
    push_cast
    apply (div_eq_iff denom).mpr
    change ((2 : ℝ) ^ a)⁻¹ * (qb : ℝ) - ((2 : ℝ) ^ b)⁻¹ * (qa : ℝ) =
      Real.ofDigits digits * (((2 : ℝ) ^ a)⁻¹ - ((2 : ℝ) ^ b)⁻¹)
    nlinarith [congrArg (fun y => ((2 : ℝ) ^ b)⁻¹ * y) headA,
      congrArg (fun y => ((2 : ℝ) ^ a)⁻¹ * y) headB]
  have samples : sample m f (initial m hm) = CarryGraphRealization.sample m γ :=
    funext fun tape => (observations tape).1
  have bills : bill m f (initial m hm) = CarryGraphRealization.bill m γ :=
    funext fun tape => (observations tape).2
  refine ⟨hγ, finite_bound.1, finite_bound.2, Nat.card_fin m, sim, observations,
    hp, hsum, ht, hmin, rational, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcost, hratio⟩
  · intro i
    change Real.ofDigits (CarryGraphRealization.labelDigit γ i) =
      ∑' d : ℕ, (if i ∈ CarryGraphRealization.labelSet m γ d then (1 : ℝ) else 0) /
        (2 : ℝ) ^ (d + 1)
    unfold Real.ofDigits
    apply tsum_congr
    intro d
    by_cases hi : i ∈ CarryGraphRealization.labelSet m γ d <;>
      simp [Real.ofDigitsTerm, CarryGraphRealization.labelDigit, hi, div_eq_mul_inv]
  · intro tape i d
    rw [samples]
    exact hleaf tape i d
  · intro tape i n h
    rw [bills]
    apply hcharged tape i n
    rwa [samples] at h
  · intro i
    rw [samples]
    exact (hlaw i).2
  · intro d
    rw [samples]
    exact (htail d).2
  · rw [samples]
    exact hterm
  · rw [bills]
    exact hbill

end D5.S3.Arith.FibonacciAtomic.CarryGraphFiniteSampler
