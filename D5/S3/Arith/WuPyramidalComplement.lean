/- GID: D5/S3/Arith/WuPyramidalComplement
   generality: G
   mirror-B: D5/B/S3/Arith/WuPyramidalComplement
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas, mathlib/module/Mathlib.Data.Nat.Nth]
   utility: none
   digest: Wu's exact formula for every positive non-k-gonal-pyramidal number when k is at least nine. -/

import D5.S3.ConceptDynamics.RegistrationWitnesses
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.WuPyramidalComplement

noncomputable section
local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

/-- The `m`-th `k`-gonal pyramidal number, extended to `m = 0` for counting. -/
def pyramidal (k m : Nat) : Nat :=
  (k - 2) * Nat.choose (m + 1) 3 + Nat.choose (m + 1) 2

/-- Positive integers outside the image of the positive-index pyramidal sequence. -/
def complement (k x : Nat) : Prop :=
  0 < x ∧ ∀ m, 0 < m → pyramidal k m ≠ x

/-- The exact integer cube-root index used internally. -/
private def rootIndex (k n : Nat) : Nat := Nat.nthRoot 3 ((6 * n) / (k - 2))

/-- The upper inclusive threshold in Equation (6). -/
def upperThreshold (k h : Nat) : Nat :=
  (k - 2) * h ^ 3 + 3 * (k - 1) * h ^ 2 + (2 * k - 1) * h + 6

/-- The lower inclusive threshold in Equation (6). -/
def lowerThreshold (k h : Nat) : Nat :=
  h * (h - 1) * (h * (k - 2) + k + 1)

/-- The source branch operation; its three supplied codes remain visible at call sites. -/
def branchSelector (upper lower middle : Option Bool) (k n h : Nat) : Option Bool :=
  if upperThreshold k h ≤ 6 * n then upper
  else if 6 * n ≤ lowerThreshold k h then lower
  else middle

/-- Interpret the source branch code as the `+1`, `-1`, or unchanged adjustment. -/
def evaluateBranch (branch : Option Bool) (n h : Nat) : Nat :=
  match branch with
  | some true => n + h + 1
  | some false => n + h - 1
  | none => n + h

private theorem pyramidal_cast (k m : Nat) (hk : 5 ≤ k) :
    (pyramidal k m : Rat) =
      (m : Rat) * (m + 1) * ((m : Rat) * (k - 2) - (k - 5)) / 6 := by
  induction m with
  | zero => simp [pyramidal, Nat.choose]
  | succ m ih =>
      have hsucc :
          pyramidal k (m + 1) =
            pyramidal k m + (k - 2) * Nat.choose (m + 1) 2 + (m + 1) := by
        simp only [pyramidal, Nat.choose_succ_succ']
        simp [Nat.choose_one_right]
        ring
      rw [hsucc]
      push_cast [Nat.cast_sub (by omega : 2 ≤ k)]
      rw [ih, Nat.choose_two_right]
      rw [Nat.cast_div_charZero (by
        simpa [Nat.mul_comm] using
          (even_iff_two_dvd.mp (Nat.even_mul_succ_self m)))]
      push_cast
      ring

private theorem upper_threshold_identity (k h : Nat) (hk : 9 ≤ k) :
    upperThreshold k h + 6 * h = 6 * pyramidal k (h + 1) := by
  have hr : (upperThreshold k h : Rat) + 6 * h = 6 * pyramidal k (h + 1) := by
    rw [pyramidal_cast k (h + 1) (by omega)]
    simp only [upperThreshold]
    push_cast [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_sub (by omega : 1 ≤ k),
      Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    ring
  exact_mod_cast hr

private theorem lower_threshold_identity (k h : Nat) (hk : 9 ≤ k) :
    lowerThreshold k h + 6 * h = 6 * pyramidal k h := by
  rcases h with _ | h
  · simp [lowerThreshold, pyramidal, Nat.choose]
  · have hr : (lowerThreshold k (h + 1) : Rat) + 6 * (h + 1) =
        6 * pyramidal k (h + 1) := by
      rw [pyramidal_cast k (h + 1) (by omega)]
      simp only [lowerThreshold]
      push_cast [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_sub (by omega : 5 ≤ k)]
      ring
    exact_mod_cast hr

private theorem previous_below_alpha (k h : Nat) (hk : 9 ≤ k) (hh : 1 ≤ h) :
    6 * pyramidal k (h - 1) ≤ (k - 2) * h ^ 3 := by
  have hr : ((6 * pyramidal k (h - 1) : Nat) : Rat) ≤
      (((k - 2) * h ^ 3 : Nat) : Rat) := by
    push_cast [Nat.cast_sub hh, Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_sub (by omega : 5 ≤ k)]
    rw [pyramidal_cast k (h - 1) (by omega)]
    push_cast [Nat.cast_sub hh, Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_sub (by omega : 5 ≤ k)]
    have hkR : (9 : Rat) ≤ k := by exact_mod_cast hk
    have hk2 : (0 : Rat) < (k : Rat) - 2 := by linarith
    have hk3 : (0 : Rat) < (k : Rat) - 3 := by linarith
    have hhR : (1 : Rat) ≤ h := by exact_mod_cast hh
    have hh0 : (0 : Rat) ≤ h := by linarith
    have hh1 : (0 : Rat) ≤ h - 1 := by linarith
    have hid : ((k : Rat) - 2) * h ^ 3 / 6 -
        (h - 1) * ((h - 1) + 1) * ((h - 1) * (k - 2) - (k - 5)) / 6 =
        h * ((k - 2) + 3 * (h - 1) * (k - 3)) / 6 := by ring
    have hn : (0 : Rat) ≤ h * ((k - 2) + 3 * (h - 1) * (k - 3)) / 6 := by positivity
    linarith
  exact_mod_cast hr

private theorem next_above_alpha (k m : Nat) (hk : 9 ≤ k) :
    (k - 2) * m ^ 3 + 6 * m < 6 * pyramidal k (m + 1) := by
  have hr : ((((k - 2) * m ^ 3 + 6 * m : Nat) : Rat) <
      ((6 * pyramidal k (m + 1) : Nat) : Rat)) := by
    push_cast [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_sub (by omega : 5 ≤ k)]
    rw [pyramidal_cast k (m + 1) (by omega)]
    push_cast [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_sub (by omega : 5 ≤ k)]
    have hkR : (9 : Rat) ≤ k := by exact_mod_cast hk
    have hk1 : (0 : Rat) < (k : Rat) - 1 := by linarith
    have hk2 : (0 : Rat) < 2 * k - 1 := by linarith
    have hm : (0 : Rat) ≤ m := by positivity
    have hid :
        ((m : Rat) + 1) * (((m : Rat) + 1) + 1) *
            (((m : Rat) + 1) * ((k : Rat) - 2) - ((k : Rat) - 5)) / 6 -
          ((k : Rat) - 2) * (m : Rat) ^ 3 / 6 - m =
        (3 * ((k : Rat) - 1) * (m : Rat) ^ 2 + (2 * (k : Rat) - 1) * m + 6) / 6 := by ring
    have hp : (0 : Rat) <
        (3 * ((k : Rat) - 1) * (m : Rat) ^ 2 + (2 * (k : Rat) - 1) * m + 6) / 6 := by
      positivity
    linarith
  exact_mod_cast hr

private theorem count_complement_at_gap (k t a : Nat)
    (hleft : pyramidal k t < a) (hright : a < pyramidal k (t + 1)) :
    Nat.count (complement k) a = a - 1 - t := by
  classical
  let f := pyramidal k
  have hf : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro m
    have hsucc :
        pyramidal k (m + 1) =
          pyramidal k m + (k - 2) * Nat.choose (m + 1) 2 + (m + 1) := by
      simp only [pyramidal, Nat.choose_succ_succ']
      simp [Nat.choose_one_right]
      ring
    dsimp only [f]
    rw [hsucc]
    omega
  have hf0 : f 0 = 0 := by simp [f, pyramidal, Nat.choose]
  have hleft' : f t < a := hleft
  have hright' : a < f (t + 1) := hright
  let good : Nat → Prop := complement k
  let bad := (Finset.range a).filter fun x => ¬ good x
  have hbad : bad = insert 0 ((Finset.Icc 1 t).image f) := by
    ext x
    constructor
    · intro hx
      have hxa : x < a := (Finset.mem_filter.mp hx).1 |> Finset.mem_range.mp
      have hxng : ¬ good x := (Finset.mem_filter.mp hx).2
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hxp : 0 < x := Nat.pos_of_ne_zero hx0
        have hex : ∃ m, 0 < m ∧ f m = x := by
          simpa [good, complement, f, hxp] using hxng
        obtain ⟨m, hm, rfl⟩ := hex
        have hmt : m ≤ t := by
          by_contra hnot
          have htm : t + 1 ≤ m := by omega
          have := hf.monotone htm
          omega
        exact Finset.mem_insert.mpr <| Or.inr <|
          Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨hm, hmt⟩, rfl⟩
    · intro hx
      have hx' : x = 0 ∨ x ∈ (Finset.Icc 1 t).image f := Finset.mem_insert.mp hx
      apply Finset.mem_filter.mpr
      rcases hx' with rfl | hx'
      · constructor
        · apply Finset.mem_range.mpr
          omega
        · simp [good, complement]
      · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx'
        have hm' := Finset.mem_Icc.mp hm
        constructor
        · exact Finset.mem_range.mpr ((hf.monotone hm'.2).trans_lt hleft')
        · intro hgood
          exact hgood.2 m hm'.1 rfl
  have hzero : 0 ∉ (Finset.Icc 1 t).image f := by
    rintro hx
    obtain ⟨m, hm, heq⟩ := Finset.mem_image.mp hx
    have hm' := (Finset.mem_Icc.mp hm).1
    have hp := hf (show 0 < m by omega)
    rw [hf0, heq] at hp
    omega
  have hbadcard : bad.card = t + 1 := by
    rw [hbad, Finset.card_insert_of_notMem hzero, Finset.card_image_of_injective _ hf.injective]
    simp
  have hpartition := Finset.card_filter_add_card_filter_not (s := Finset.range a) good
  change Nat.count good a = a - 1 - t
  rw [Nat.count_eq_card_filter_range]
  change ((Finset.range a).filter good).card = a - 1 - t
  change ((Finset.range a).filter good).card + bad.card = (Finset.range a).card at hpartition
  simp only [hbadcard, Finset.card_range] at hpartition
  omega

private theorem branch_gap (k n : Nat) (hk : 9 ≤ k) (hn : 1 ≤ n) :
    let h := rootIndex k n
    let branch := branchSelector (some true) (some false) none k n h
    let a := evaluateBranch branch n h
    ∃ t, pyramidal k t < a ∧ a < pyramidal k (t + 1) ∧ a = n + t := by
  let h := rootIndex k n
  change ∃ t, pyramidal k t <
      evaluateBranch (branchSelector (some true) (some false) none k n h) n h ∧
    evaluateBranch (branchSelector (some true) (some false) none k n h) n h <
      pyramidal k (t + 1) ∧
    evaluateBranch (branchSelector (some true) (some false) none k n h) n h = n + t
  have hb : (k - 2) * (rootIndex k n) ^ 3 ≤ 6 * n ∧
      6 * n < (k - 2) * (rootIndex k n + 1) ^ 3 := by
    have hd : 0 < k - 2 := by omega
    constructor
    · have hp := Nat.pow_nthRoot_le (n := 3) (a := (6 * n) / (k - 2)) (Or.inl (by decide))
      simpa [rootIndex, Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hp
    · have hp := Nat.lt_pow_nthRoot_add_one (n := 3) (by decide) ((6 * n) / (k - 2))
      simpa [rootIndex, Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd).mp hp
  have hb' : (k - 2) * h ^ 3 ≤ 6 * n ∧ 6 * n < (k - 2) * (h + 1) ^ 3 := by
    simpa [h] using hb
  have hnext := next_above_alpha k (h + 1) hk
  have hnext' : (k - 2) * (h + 1) ^ 3 + 6 * (h + 1) <
      6 * pyramidal k (h + 2) := by
    simpa [Nat.add_assoc] using hnext
  have hfar : 6 * (n + h + 1) < 6 * pyramidal k (h + 2) := by omega
  by_cases hu : upperThreshold k h ≤ 6 * n
  · refine ⟨h + 1, ?_, ?_, ?_⟩
    · have hid := upper_threshold_identity k h hk
      simp only [branchSelector, if_pos hu, evaluateBranch]
      omega
    · simp only [branchSelector, if_pos hu, evaluateBranch]
      simpa [Nat.add_assoc] using hfar
    · simp only [branchSelector, if_pos hu, evaluateBranch]
      omega
  · by_cases hl : 6 * n ≤ lowerThreshold k h
    · have hh : 2 ≤ h := by
        rcases h with _ | _ | h <;> simp_all [lowerThreshold]
      have hprev := previous_below_alpha k h hk (by omega)
      refine ⟨h - 1, ?_, ?_, ?_⟩
      · simp only [branchSelector, if_neg hu, if_pos hl, evaluateBranch]
        omega
      · have hid := lower_threshold_identity k h hk
        simp only [branchSelector, if_neg hu, if_pos hl, evaluateBranch]
        rw [show h - 1 + 1 = h by omega]
        omega
      · simp only [branchSelector, if_neg hu, if_pos hl, evaluateBranch]
        omega
    · refine ⟨h, ?_, ?_, ?_⟩
      · have hid := lower_threshold_identity k h hk
        simp only [branchSelector, if_neg hu, if_neg hl, evaluateBranch]
        omega
      · have hid := upper_threshold_identity k h hk
        simp only [branchSelector, if_neg hu, if_neg hl, evaluateBranch]
        omega
      · simp only [branchSelector, if_neg hu, if_neg hl, evaluateBranch]

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open LeanInformationAudit

private def branchSignature : PrimitiveSignature (Option Bool) where
  Index := Unit
  indexFintype := PUnit.fintype
  indexDecidableEq := instDecidableEqPUnit
  Output := fun _ => Option Bool
  outputDecidableEq := fun _ => @Option.instDecidableEq Bool instDecidableEqBool
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := Fin.fintype 0
  anchorDecidableEq := instDecidableEqFin 0

def branchArena : PrimitiveLawArena where
  toArena := Arena.ofFintype (Option Bool)
  signature := branchSignature
  Law realization := ∀ (k n : Nat), 9 ≤ k → 1 ≤ n →
    Nat.nth (complement k) (n - 1) =
      let h := Nat.floor
        ((((6 * n : Nat) : Real) / ((k - 2 : Nat) : Real)) ^ ((3 : Real)⁻¹))
      evaluateBranch
        (realization.readout ()
          (branchSelector (some true) (some false) none k n h)) n h

private instance : DecidableEq branchArena.State := branchArena.toArena.stateDecidableEq

def branchRealization (readBranch : Option Bool → Option Bool) :
    PrimitiveRealization branchSignature where
  readout := fun _ => readBranch
  anchor := Fin.elim0

def identityReadout : PrimitiveRealization branchSignature :=
  branchRealization (fun branch : Option Bool => branch)

private def constantLowerReadout : PrimitiveRealization branchSignature :=
  branchRealization (fun _ : Option Bool => some false)

theorem branchSensitivity : FiniteSlotSensitivity branchArena := by
  have identityLaw : branchArena.Law identityReadout := by
    intro k n hk hn
    have hroot :
        Nat.floor ((((6 * n : Nat) : Real) / ((k - 2 : Nat) : Real)) ^ ((3 : Real)⁻¹)) =
          rootIndex k n := by
      let h := rootIndex k n
      have hb : (k - 2) * (rootIndex k n) ^ 3 ≤ 6 * n ∧
          6 * n < (k - 2) * (rootIndex k n + 1) ^ 3 := by
        have hd : 0 < k - 2 := by omega
        constructor
        · have hp :=
            Nat.pow_nthRoot_le (n := 3) (a := (6 * n) / (k - 2)) (Or.inl (by decide))
          simpa [rootIndex, Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hp
        · have hp := Nat.lt_pow_nthRoot_add_one (n := 3) (by decide) ((6 * n) / (k - 2))
          simpa [rootIndex, Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd).mp hp
      have hd : (0 : Real) < (k - 2 : Nat) := by
        exact_mod_cast (show 0 < k - 2 by omega)
      have hx : (0 : Real) ≤ ((6 * n : Nat) : Real) / ((k - 2 : Nat) : Real) := by
        positivity
      apply (Nat.floor_eq_iff (Real.rpow_nonneg hx _)).mpr
      constructor
      · apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg h) hx
          (by norm_num : (0 : Real) < 3)).mpr
        change (h : Real) ^ ((3 : Nat) : Real) ≤
          ((6 * n : Nat) : Real) / ((k - 2 : Nat) : Real)
        rw [Real.rpow_natCast]
        apply (le_div_iff₀ hd).mpr
        exact_mod_cast (by simpa [h, Nat.mul_comm] using hb.1)
      · apply (Real.rpow_inv_lt_iff_of_pos hx (by positivity : (0 : Real) ≤ (h : Real) + 1)
            (by norm_num : (0 : Real) < 3)).mpr
        change ((6 * n : Nat) : Real) / ((k - 2 : Nat) : Real) <
          ((h : Real) + 1) ^ ((3 : Nat) : Real)
        rw [Real.rpow_natCast]
        apply (div_lt_iff₀ hd).mpr
        exact_mod_cast (by simpa [h, Nat.mul_comm] using hb.2)
    rw [hroot]
    obtain ⟨t, hleft, hright, ha⟩ := branch_gap k n hk hn
    let a := evaluateBranch
      (branchSelector (some true) (some false) none k n (rootIndex k n)) n (rootIndex k n)
    have hf : StrictMono (pyramidal k) := by
      apply strictMono_nat_of_lt_succ
      intro m
      have hsucc :
          pyramidal k (m + 1) =
            pyramidal k m + (k - 2) * Nat.choose (m + 1) 2 + (m + 1) := by
        simp only [pyramidal, Nat.choose_succ_succ']
        simp [Nat.choose_one_right]
        ring
      rw [hsucc]
      omega
    have hca : complement k a := by
      constructor
      · omega
      · intro m hm heq
        by_cases hmt : m ≤ t
        · have := hf.monotone hmt
          omega
        · have htm : t + 1 ≤ m := by omega
          have := hf.monotone htm
          omega
    have hcount : Nat.count (complement k) a = n - 1 := by
      calc
        Nat.count (complement k) a = a - 1 - t := by
          exact count_complement_at_gap k t a hleft hright
        _ = n - 1 := by omega
    rw [← hcount]
    exact Nat.nth_count hca
  have constantLower_not_law : ¬ branchArena.Law constantLowerReadout := by
    intro law
    have hbad := law 9 1 (by omega) (by omega)
    have hgood := identityLaw 9 1 (by omega) (by omega)
    have hroot :
        Nat.floor ((((6 * 1 : Nat) : Real) / ((9 - 2 : Nat) : Real)) ^ ((3 : Real)⁻¹)) =
          rootIndex 9 1 := by
      let h := rootIndex 9 1
      have hb : (9 - 2) * (rootIndex 9 1) ^ 3 ≤ 6 * 1 ∧
          6 * 1 < (9 - 2) * (rootIndex 9 1 + 1) ^ 3 := by
        have hd : 0 < 9 - 2 := by omega
        constructor
        · have hp :=
            Nat.pow_nthRoot_le (n := 3) (a := (6 * 1) / (9 - 2)) (Or.inl (by decide))
          simpa [rootIndex, Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hp
        · have hp := Nat.lt_pow_nthRoot_add_one (n := 3) (by decide) ((6 * 1) / (9 - 2))
          simpa [rootIndex, Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd).mp hp
      have hd : (0 : Real) < (9 - 2 : Nat) := by norm_num
      have hx : (0 : Real) ≤ ((6 * 1 : Nat) : Real) / ((9 - 2 : Nat) : Real) := by
        positivity
      apply (Nat.floor_eq_iff (Real.rpow_nonneg hx _)).mpr
      constructor
      · apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg h) hx
          (by norm_num : (0 : Real) < 3)).mpr
        change (h : Real) ^ ((3 : Nat) : Real) ≤
          ((6 * 1 : Nat) : Real) / ((9 - 2 : Nat) : Real)
        rw [Real.rpow_natCast]
        apply (le_div_iff₀ hd).mpr
        exact_mod_cast (by simpa [h, Nat.mul_comm] using hb.1)
      · apply (Real.rpow_inv_lt_iff_of_pos hx (by positivity : (0 : Real) ≤ (h : Real) + 1)
            (by norm_num : (0 : Real) < 3)).mpr
        change ((6 * 1 : Nat) : Real) / ((9 - 2 : Nat) : Real) <
          ((h : Real) + 1) ^ ((3 : Nat) : Real)
        rw [Real.rpow_natCast]
        apply (div_lt_iff₀ hd).mpr
        exact_mod_cast (by simpa [h, Nat.mul_comm] using hb.2)
    rw [hroot] at hbad hgood
    change Nat.nth (complement 9) 0 = 0 at hbad
    norm_num [branchArena, identityReadout, branchRealization, rootIndex, branchSelector,
      upperThreshold, lowerThreshold, evaluateBranch] at hbad hgood
    omega
  constructor
  · intro i
    refine ⟨identityReadout, constantLowerReadout, ?_, ?_, ?_⟩
    · intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => constantLower_not_law, fun _ => identityLaw⟩
  · intro i
    exact Fin.elim0 i

theorem branchVariation : FiniteLawVariation branchArena := by
  obtain ⟨r, r', _, _, hr⟩ := branchSensitivity.1 ()
  by_cases hp : branchArena.Law r
  · exact ⟨r, r', hp, hr.mp hp⟩
  · have hp' : branchArena.Law r' := Classical.byContradiction (fun hn => hp (hr.mpr hn))
    exact ⟨r', r, hp', hp⟩



/- Wu's Conjecture 1: Equation (6) gives the `n`-th positive integer outside the
positive `k`-gonal-pyramidal image for every `k ≥ 9` and `n ≥ 1`. -/
theorem wu_conjecture_one : ∀ (k n : Nat), 9 ≤ k → 1 ≤ n →
      Nat.nth (complement k) (n - 1) =
        let h := Nat.floor
          ((((6 * n : Nat) : Real) / ((k - 2 : Nat) : Real)) ^ ((3 : Real)⁻¹))
        evaluateBranch (branchSelector (some true) (some false) none k n h) n h := by
  intro k n hk hn
  have hroot :
      Nat.floor ((((6 * n : Nat) : Real) / ((k - 2 : Nat) : Real)) ^ ((3 : Real)⁻¹)) =
        rootIndex k n := by
    let h := rootIndex k n
    have hb : (k - 2) * (rootIndex k n) ^ 3 ≤ 6 * n ∧
        6 * n < (k - 2) * (rootIndex k n + 1) ^ 3 := by
      have hd : 0 < k - 2 := by omega
      constructor
      · have hp :=
          Nat.pow_nthRoot_le (n := 3) (a := (6 * n) / (k - 2)) (Or.inl (by decide))
        simpa [rootIndex, Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hp
      · have hp := Nat.lt_pow_nthRoot_add_one (n := 3) (by decide) ((6 * n) / (k - 2))
        simpa [rootIndex, Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd).mp hp
    have hd : (0 : Real) < (k - 2 : Nat) := by
      exact_mod_cast (show 0 < k - 2 by omega)
    have hx : (0 : Real) ≤ ((6 * n : Nat) : Real) / ((k - 2 : Nat) : Real) := by
      positivity
    apply (Nat.floor_eq_iff (Real.rpow_nonneg hx _)).mpr
    constructor
    · apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg h) hx
        (by norm_num : (0 : Real) < 3)).mpr
      change (h : Real) ^ ((3 : Nat) : Real) ≤
        ((6 * n : Nat) : Real) / ((k - 2 : Nat) : Real)
      rw [Real.rpow_natCast]
      apply (le_div_iff₀ hd).mpr
      exact_mod_cast (by simpa [h, Nat.mul_comm] using hb.1)
    · apply (Real.rpow_inv_lt_iff_of_pos hx (by positivity : (0 : Real) ≤ (h : Real) + 1)
          (by norm_num : (0 : Real) < 3)).mpr
      change ((6 * n : Nat) : Real) / ((k - 2 : Nat) : Real) <
        ((h : Real) + 1) ^ ((3 : Nat) : Real)
      rw [Real.rpow_natCast]
      apply (div_lt_iff₀ hd).mpr
      exact_mod_cast (by simpa [h, Nat.mul_comm] using hb.2)
  rw [hroot]
  obtain ⟨t, hleft, hright, ha⟩ := branch_gap k n hk hn
  let a := evaluateBranch
    (branchSelector (some true) (some false) none k n (rootIndex k n)) n (rootIndex k n)
  have hf : StrictMono (pyramidal k) := by
    apply strictMono_nat_of_lt_succ
    intro m
    have hsucc :
        pyramidal k (m + 1) =
          pyramidal k m + (k - 2) * Nat.choose (m + 1) 2 + (m + 1) := by
      simp only [pyramidal, Nat.choose_succ_succ']
      simp [Nat.choose_one_right]
      ring
    rw [hsucc]
    omega
  have hca : complement k a := by
    constructor
    · omega
    · intro m hm heq
      by_cases hmt : m ≤ t
      · have := hf.monotone hmt
        omega
      · have htm : t + 1 ≤ m := by omega
        have := hf.monotone htm
        omega
  have hcount : Nat.count (complement k) a = n - 1 := by
    calc
      Nat.count (complement k) a = a - 1 - t := by
        exact count_complement_at_gap k t a hleft hright
      _ = n - 1 := by omega
  rw [← hcount]
  exact Nat.nth_count hca



#print axioms wu_conjecture_one

end
end D5.S3.Arith.WuPyramidalComplement
