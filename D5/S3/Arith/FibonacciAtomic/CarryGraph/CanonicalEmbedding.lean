/- GID: D5/S3/Arith/FibonacciAtomic/CarryGraph/CanonicalEmbedding
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/CarryGraph/CanonicalEmbedding
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Positive real laws embed with exact anchors, costs and floor layers. -/

import D5.S3.Arith.FibonacciAtomic.CarryGraphEmbedding
import D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CarryGraph.CanonicalEmbedding
open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic CarryGraphEmbedding

local notation "pref" => (fun {m : ℕ} (p : Fin m → ℝ) (d : ℕ) (i : Fin m) =>
  ⌊(2 : ℝ) ^ d * p i⌋)
local notation "bit" => (fun {m : ℕ} (p : Fin m → ℝ) (d : ℕ) (i : Fin m) =>
  pref p (d + 1) i - 2 * pref p d i)
local notation "eqCount" => (fun {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (d : ℕ) =>
  ∑ i, ite (pref p d i = pref p d k) (1 : ℤ) 0)
local notation "resid" => (fun {m : ℕ} (p : Fin m → ℝ) (d : ℕ) =>
  (2 : ℤ) ^ d - ∑ i, pref p d i)
local notation "equalOnes" => (fun {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (d : ℕ) =>
  ∑ i, ite (pref p d i = pref p d k) (bit p d i) 0)
local notation "largerOnes" => (fun {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (d : ℕ) =>
  ∑ i, ite (pref p d i = pref p d k) 0 (bit p d i))

/-- The floor residual and the number of labels sharing the minimum prefix. -/
noncomputable def canonicalState {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (d : ℕ) : State :=
  ⟨resid p d, eqCount p k d⟩

/-- Canonical next digits count departures from the anchor group and larger one-labels. -/
noncomputable def canonicalAction {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (d : ℕ) : Action :=
  ⟨bit p d k, if bit p d k = 1 then 0 else equalOnes p k d, largerOnes p k d⟩

/-- The states and actions obtained from one common real input law. -/
noncomputable def canonicalPath {m : ℕ} (p : Fin m → ℝ) (k : Fin m) : Path :=
  ⟨canonicalState p k, canonicalAction p k⟩

/-- Floor division makes every next digit zero or one. -/
private theorem bit_bounds {m : ℕ} (p : Fin m → ℝ) (d : ℕ) (i : Fin m) :
    0 ≤ bit p d i ∧ bit p d i ≤ 1 := by
  have divs : pref p (d+1) i / 2 = pref p d i := by
    change ⌊(2 : ℝ)^(d+1) * p i⌋ / 2 = ⌊(2 : ℝ)^d * p i⌋
    convert Int.cast_mul_floor_div_cancel_of_pos (R := ℝ) (by norm_num : (0 : ℤ) < 2)
      ((2 : ℝ)^d * p i) using 1 <;> congr 1 <;> simp [pow_succ] <;> ring
  have rem := Int.emod_nonneg (pref p (d+1) i) (by norm_num : (2 : ℤ) ≠ 0)
  have rem' := Int.emod_lt_of_pos (pref p (d+1) i) (by norm_num : (0 : ℤ) < 2)
  dsimp only at *
  omega

/-- A least real coordinate remains least after each floor observation. -/
private theorem prefix_min {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hk : ∀ i, p k ≤ p i) (d : ℕ) (i : Fin m) : pref p d k ≤ pref p d i := by
  exact Int.floor_mono (mul_le_mul_of_nonneg_left (hk i) (by positivity))

/-- Every coordinate of a positive multi-label normalized law is below one. -/
private theorem coordinate_lt_one {m : ℕ} (hm : 2 ≤ m) (p : Fin m → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) (i : Fin m) : p i < 1 := by
  classical
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  obtain ⟨j, hji⟩ := exists_ne i
  rw [← hs]
  exact Finset.single_lt_sum hji (Finset.mem_univ i) (Finset.mem_univ j)
    (hp j) (fun k _ _ => (hp k).le)

/-- The integer residual lies in the original state interval. -/
private theorem residual_bounds {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hs : ∑ i, p i = 1) (d : ℕ) : 0 ≤ resid p d ∧ resid p d ≤ (m : ℤ)-1 := by
  have scaled : ∑ i, (2 : ℝ)^d * p i = (2 : ℝ)^d := by
    rw [← Finset.mul_sum, hs, mul_one]
  have hi := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) ⟨k, by simp⟩
    (fun i _ => Int.lt_floor_add_one ((2 : ℝ)^d * p i))
  rw [scaled] at hi
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hi
  have lo' : (0 : ℝ) ≤ (resid p d : ℝ) := by
    simpa only [DyadicSupportLines.residual, Int.cast_sum, Int.cast_sub,
      Int.cast_pow, Int.cast_ofNat] using (OptimalLawStrictSlope.law_data m p hs).1 d |>.1
  have hi' : (resid p d : ℝ) < (m : ℝ) := by
    simp only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat, Int.cast_sum]
    linarith
  have L : 0 ≤ resid p d := by exact_mod_cast lo'
  have H : resid p d < m := by exact_mod_cast hi'
  exact ⟨L, by omega⟩

/-- The equality group contains its anchor and at most all labels. -/
private theorem count_bounds {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (d : ℕ) :
    1 ≤ eqCount p k d ∧ eqCount p k d ≤ m := by
  classical
  have L := Finset.single_le_sum (s := Finset.univ)
    (f := fun i => ite (pref p d i = pref p d k) (1 : ℤ) 0)
    (by intro i _; split_ifs <;> norm_num) (Finset.mem_univ k)
  have H := Finset.sum_le_sum (s := Finset.univ)
    (f := fun i => ite (pref p d i = pref p d k) (1 : ℤ) 0)
    (g := fun _ => (1 : ℤ)) (by intro i _; split_ifs <;> norm_num)
  simpa [] using And.intro L H

/-- The floor state satisfies both carry-state bounds. -/
private theorem state_valid {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hs : ∑ i, p i = 1) (d : ℕ) : IsState m (canonicalState p k d) :=
  ⟨(residual_bounds p k hs d).1, (residual_bounds p k hs d).2,
    (count_bounds p k d).1, (count_bounds p k d).2⟩

/-- At depth zero all prefixes vanish, giving the original root. -/
private theorem root_eq {m : ℕ} (hm : 2 ≤ m) (p : Fin m → ℝ) (k : Fin m)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) : canonicalState p k 0 = root m := by
  have N (i : Fin m) : ⌊p i⌋ = 0 := by
    apply Int.floor_eq_iff.mpr
    simp only [Int.cast_zero, zero_add]
    exact ⟨(hp i).le, coordinate_lt_one hm p hp hs i⟩
  simp [canonicalState, N, root]

/-- The equality indicator drops exactly when an equal label departs. -/
private theorem indicator_step {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hk : ∀ i, p k ≤ p i) (d : ℕ) (i : Fin m) :
    (if pref p (d+1) i = pref p (d+1) k then (1 : ℤ) else 0) =
      (if pref p d i = pref p d k then 1 else 0) -
      (if bit p d k = 1 then 0 else ite (pref p d i = pref p d k) (bit p d i) 0) := by
  have B := bit_bounds p d i
  have K := bit_bounds p d k
  have M := prefix_min p k hk d i
  have M' := prefix_min p k hk (d+1) i
  dsimp only at *
  split_ifs <;> omega

/-- An anchor one forces every still-equal label to have digit one. -/
private theorem equal_digit {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hk : ∀ i, p k ≤ p i) (d : ℕ) (i : Fin m)
    (hi : pref p d i = pref p d k) (hb : bit p d k = 1) : bit p d i = 1 := by
  have B := bit_bounds p d i
  have M := prefix_min p k hk (d+1) i
  dsimp only at *
  omega

/-- The same-law equality count decreases by the departure coordinate. -/
private theorem equality_count_step {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hk : ∀ i, p k ≤ p i) (d : ℕ) :
    eqCount p k (d+1) = eqCount p k d - (canonicalAction p k d).h := by
  classical
  dsimp only
  simp_rw [indicator_step p k hk d]
  rw [Finset.sum_sub_distrib]
  by_cases hb : bit p d k = 1
  · simp [canonicalAction, hb]
  · simp [canonicalAction, hb]

/-- The complete next-digit column has the original action count. -/
private theorem column_total {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hk : ∀ i, p k ≤ p i) (d : ℕ) :
    (∑ i, bit p d i) = ones (canonicalState p k d) (canonicalAction p k d) := by
  classical
  have split : (∑ i, bit p d i) = equalOnes p k d + largerOnes p k d := by
    dsimp only
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [split]
  unfold ones canonicalAction canonicalState
  dsimp only
  by_cases hb : bit p d k = 1
  · simp only [hb, ite_true]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : pref p d i = pref p d k
    · simpa only [if_pos hi] using equal_digit p k hk d i hi hb
    · simp [hi]
  · simp [hb]

/-- The floor residual satisfies the doubled-column recurrence. -/
private theorem residual_step {m : ℕ} (p : Fin m → ℝ) (d : ℕ) :
    resid p (d+1) = 2*resid p d - ∑ i, bit p d i := by
  dsimp only
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, pow_succ]
  ring

/-- Both coordinates advance through the original successor. -/
private theorem canonical_successor {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hk : ∀ i, p k ≤ p i) (d : ℕ) :
    canonicalState p k (d+1) = successor (canonicalState p k d) (canonicalAction p k d) := by
  change State.mk _ _ = State.mk _ _
  congr 1
  · exact (residual_step p d).trans (by rw [column_total p k hk d]; rfl)
  · exact equality_count_step p k hk d

/-- The canonical digits satisfy exactly one of the two action rows. -/
private theorem action_rows {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hk : ∀ i, p k ≤ p i) (d : ℕ) :
    ((canonicalAction p k d).b = 1 ∧ (canonicalAction p k d).h = 0 ∧
        0 ≤ (canonicalAction p k d).c ∧
        (canonicalAction p k d).c ≤ (m : ℤ)-(canonicalState p k d).e) ∨
      ((canonicalAction p k d).b = 0 ∧ 0 ≤ (canonicalAction p k d).h ∧
        (canonicalAction p k d).h ≤ (canonicalState p k d).e - 1 ∧
        0 ≤ (canonicalAction p k d).c ∧
        (canonicalAction p k d).c ≤ (m : ℤ)-(canonicalState p k d).e) := by
  classical
  have C0 : 0 ≤ largerOnes p k d := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact le_rfl
    · exact (bit_bounds p d i).1
  have C1 : largerOnes p k d ≤ (m : ℤ) - eqCount p k d := by
    have H := Finset.sum_le_sum (s := Finset.univ)
      (f := fun i => if pref p d i = pref p d k then (0 : ℤ) else bit p d i)
      (g := fun i => 1 - (ite (pref p d i = pref p d k) (1 : ℤ) 0)) (by
        intro i _; split_ifs <;> have := bit_bounds p d i <;> omega)
    simpa [Finset.sum_sub_distrib] using H
  have H0 : 0 ≤ equalOnes p k d := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact (bit_bounds p d i).1
    · exact le_rfl
  have H1 := (count_bounds p k (d+1)).1
  rw [equality_count_step p k hk d] at H1
  have B := bit_bounds p d k
  by_cases hb : bit p d k = 1
  · exact Or.inl ⟨hb, by simp [canonicalAction, hb], C0, C1⟩
  · have hb0 : bit p d k = 0 := by omega
    have H1' : 1 ≤ eqCount p k d - equalOnes p k d := by
      simpa only [canonicalAction, hb0, Int.zero_ne_one, ite_false] using H1
    have Hbound : equalOnes p k d ≤ eqCount p k d - 1 := by omega
    exact Or.inr ⟨hb0, by simpa [canonicalAction, hb0] using H0,
      by simpa only [canonicalAction, canonicalState, hb0, Int.zero_ne_one, ite_false]
        using Hbound, C0, C1⟩

/-- The same-law action connects two legal carry states. -/
private theorem canonical_legal {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hs : ∑ i, p i = 1) (hk : ∀ i, p k ≤ p i) (d : ℕ) :
    Legal m (canonicalState p k d) (canonicalAction p k d) := by
  refine ⟨state_valid p k hs d, action_rows p k hk d, ?_⟩
  rw [← canonical_successor p k hk d]
  exact state_valid p k hs (d+1)

/-- A least label supplies a legal canonical path from the root. -/
private theorem canonical_root_path {m : ℕ} (hm : 2 ≤ m) (p : Fin m → ℝ) (k : Fin m)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) (hk : ∀ i, p k ≤ p i) :
    IsRootPath m (canonicalPath p k) :=
  ⟨root_eq hm p k hp hs, fun d => ⟨canonical_legal p k hs hk d, canonical_successor p k hk d⟩⟩

/-- For nonnegative coordinates the floor difference is the canonical binary digit. -/
private theorem bit_eq_digits {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i)
    (d : ℕ) (i : Fin m) : bit p d i = ((Real.digits (p i) 2 d).val : ℤ) := by
  have divs : pref p (d+1) i / 2 = pref p d i := by
    change ⌊(2 : ℝ)^(d+1) * p i⌋ / 2 = ⌊(2 : ℝ)^d * p i⌋
    convert Int.cast_mul_floor_div_cancel_of_pos (R := ℝ) (by norm_num : (0 : ℤ) < 2)
      ((2 : ℝ)^d * p i) using 1 <;> congr 1 <;> simp [pow_succ] <;> ring
  have H : (⌊p i * (2 : ℝ)^(d+1)⌋₊ : ℤ) = pref p (d+1) i := by
    rw [Int.natCast_floor_eq_floor (by exact mul_nonneg (hp i) (by positivity))]
    dsimp only
    congr 1
    ring
  have D : ((Real.digits (p i) 2 d).val : ℤ) = pref p (d+1) i % 2 := by
    change ((⌊p i * (2 : ℝ)^(d+1)⌋₊ % 2 : ℕ) : ℤ) = _
    rw [Int.natCast_mod, H]
    norm_num
  rw [D]
  dsimp only at *
  omega

/-- The anchor series is the original real coordinate. -/
private theorem canonical_anchor {m : ℕ} (hm : 2 ≤ m) (p : Fin m → ℝ) (k : Fin m)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    anchorValue (canonicalPath p k) = p k := by
  rw [← Real.ofDigits_digits (b := 2) (by norm_num)
    ⟨(hp k).le, coordinate_lt_one hm p hp hs k⟩]
  unfold anchorValue Real.ofDigits
  apply tsum_congr
  intro d
  change (bit p d k : ℝ) / (2 : ℝ)^(d+1) = _
  rw [bit_eq_digits p (fun i => (hp i).le)]
  simp [Real.ofDigitsTerm, div_eq_mul_inv]

/-- The path residual series equals the original dyadic cost term by term. -/
private theorem canonical_cost {m : ℕ} (p : Fin m → ℝ) (k : Fin m) :
    pathCost (canonicalPath p k) = DyadicSupportLines.cost p := by
  unfold pathCost DyadicSupportLines.cost
  apply tsum_congr
  intro d
  congr 1
  simp [canonicalPath, canonicalState, DyadicSupportLines.residual]

/-- Every carry state admits an action; the zero-residual boundary is absorbing,
and singleton equality groups never lose their anchor. Every strictly positive
normalized real law embeds with its exact minimum, cost and all floor layers. -/
theorem result (m : ℕ) (hm : 2 ≤ m) :
    (∀ s : State, IsState m s → ∃ a : Action, Legal m s a) ∧
    (∀ (s : State) (a : Action), Legal m s a → s.r = 0 →
      a.b = 0 ∧ a.h = 0 ∧ a.c = 0 ∧ successor s a = s) ∧
    (∀ (s : State) (a : Action), Legal m s a → s.e = 1 → a.h = 0) ∧
    (∀ p : Fin m → ℝ, (∀ i, 0 < p i) → (∑ i, p i = 1) →
      ∃ k : Fin m, (∀ i, p k ≤ p i) ∧ ∃ γ : Path,
        IsRootPath m γ ∧ anchorValue γ = p k ∧
        anchorValue γ = sInf (Set.range p) ∧ pathCost γ = DyadicSupportLines.cost p ∧
        (∀ d, (γ.state d).r = (2 : ℤ)^d - ∑ i, ⌊(2 : ℝ)^d*p i⌋) ∧
        (∀ d, (γ.state d).e = ((Finset.univ.filter
          (fun i => ⌊(2 : ℝ)^d*p i⌋ = ⌊(2 : ℝ)^d*p k⌋)).card : ℤ))) := by
  classical
  have totality (s : State) (hs : IsState m s) : ∃ a : Action, Legal m s a := by
    let q : ℤ := max 0 (2*s.r - ((m : ℤ)-1))
    let h : ℤ := min q (s.e-1)
    let c : ℤ := q-h
    refine ⟨⟨0,h,c⟩, hs, Or.inr ?_, ?_⟩
    · dsimp only
      rcases hs with ⟨hr0,hr1,he0,he1⟩
      dsimp [q,h,c]
      omega
    · rcases hs with ⟨hr0,hr1,he0,he1⟩
      simp only [IsState, successor, ones, Int.zero_ne_one, ite_false]
      dsimp [q,h,c]
      omega
  have zeroB (s : State) (a : Action) (ha : Legal m s a) (hr : s.r = 0) :
    a.b = 0 ∧ a.h = 0 ∧ a.c = 0 ∧ successor s a = s := by
    rcases ha with ⟨⟨_,_,he0,_⟩, ha, hs⟩
    rcases ha with ⟨hb,hh,hc0,hc1⟩ | ⟨hb,hh0,hh1,hc0,hc1⟩
    · have H := hs.1
      simp [successor, ones, hb, hr] at H
      omega
    · have H := hs.1
      simp [successor, ones, hb, hr] at H
      have hh : a.h = 0 := by omega
      have hc : a.c = 0 := by omega
      refine ⟨hb,hh,hc,?_⟩
      cases s
      simp_all [successor, ones]
  have oneB (s : State) (a : Action) (ha : Legal m s a) (he : s.e = 1) : a.h = 0 := by
    rcases ha.2.1 with ⟨_,hh,_,_⟩ | ⟨_,hh0,hh1,_,_⟩ <;> omega
  refine ⟨totality, zeroB, oneB, ?_⟩
  intro p hp hs
  have hn : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, by omega⟩, by simp⟩
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_inf' hn p
  have minp (i : Fin m) : p k ≤ p i := by
    rw [← he]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  have below : BddBelow (Set.range p) := ⟨0, by
    rintro x ⟨i, rfl⟩
    exact (hp i).le⟩
  have min_eq : sInf (Set.range p) = p k := le_antisymm
    (csInf_le below ⟨k, rfl⟩) (le_csInf ⟨p k, k, rfl⟩ (by
      rintro x ⟨i, rfl⟩
      exact minp i))
  refine ⟨k, minp, canonicalPath p k, canonical_root_path hm p k hp hs minp,
    canonical_anchor hm p k hp hs, (canonical_anchor hm p k hp hs).trans min_eq.symm,
    canonical_cost p k, fun d => rfl, ?_⟩
  intro d
  simp only [canonicalPath, canonicalState]
  rw [Finset.card_filter]
  push_cast
  rfl

end D5.S3.Arith.FibonacciAtomic.CarryGraph.CanonicalEmbedding
