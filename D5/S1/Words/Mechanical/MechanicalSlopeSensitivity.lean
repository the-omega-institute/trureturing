/- GID: D5/S1/Words/Mechanical/MechanicalSlopeSensitivity
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalSlopeSensitivity
   mirror-E: none(waiver:unbounded-symbolic-parameter-sensitivity)
   anchors: []
   utility: none
   digest: Actual mechanical readouts have a constructed local slope chamber with an exact quadratic-in-horizon disagreement law. -/

import D5.S1.Words.Mechanical.MechanicalBalance
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# Numerical slope precision and actual binary observations

The finite observation is the existing lowerMechanicalWord, not a supplied
partition. The proof constructs a positive perturbation radius from its
actual irrational rotation cuts. Inside that radius the disagreement set is
exactly a disjoint family of swept intervals. It also computes the signed
letter changes, so the local errors are adjacent exchanges, not independent
bit noise. Lebesgue length gives the exact n(n+1)/2 sensitivity coefficient.

No disjointness, stable floor pattern, mismatch region or measure certificate
is an input. The perturbation radius is sufficient, not claimed maximal.
The approximating slope may be rational. All endpoint conventions are exact.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S1.Words.Mechanical.MechanicalSlopeSensitivity

open Set MeasureTheory
open scoped BigOperators
open D5.S1.Words.Mechanical

/-- Phases at which the two actual n-bit mechanical observations disagree. -/
def slopeDisagreement (alpha beta : ℝ) (n : ℕ) : Set ℝ :=
  {x | x ∈ Ico 0 1 ∧ ∃ k : Fin n,
    lowerMechanicalWord beta x k.val ≠ lowerMechanicalWord alpha x k.val}

/-- Every irrational slope has a constructed local chamber in which the
complete observation disagreement, its measure, and every signed letter
change are exact. The geometric chamber is proved from irrationality. -/
theorem local_slope_disagreement_law
    (alpha : ℝ) (halpha : Irrational alpha) (h0 : 0 < alpha) (h1 : alpha < 1)
    (n : ℕ) :
    ∃ radius : ℝ, 0 < radius ∧ alpha + radius < 1 ∧
      ∀ delta : ℝ, 0 ≤ delta → delta ≤ radius →
      let c : Fin n → ℝ := fun i => 1 - Int.fract (((i.val + 1 : ℕ) : ℝ) * alpha)
      let swept : Fin n → Set ℝ := fun i =>
        Ico (c i - ((i.val + 1 : ℕ) : ℝ) * delta) (c i)
      slopeDisagreement alpha (alpha + delta) n = ⋃ i, swept i ∧
      Pairwise (fun i j => Disjoint (swept i) (swept j)) ∧
      volume (slopeDisagreement alpha (alpha + delta) n) =
        ENNReal.ofReal ((n : ℝ) * ((n : ℝ) + 1) / 2 * delta) ∧
      ∀ i x, x ∈ swept i → ∀ j : Fin n,
        lowerMechanicalLetter (alpha + delta) x j.val -
          lowerMechanicalLetter alpha x j.val =
          (if j.val = i.val then (1 : ℤ) else 0) -
            (if j.val = i.val + 1 then (1 : ℤ) else 0) := by
  classical
  let c : Fin n → ℝ := fun i => 1 - Int.fract (((i.val + 1 : ℕ) : ℝ) * alpha)
  have hc (i : Fin n) : c i ∈ Ioo (0 : ℝ) 1 := by
    have hnz : Int.fract (((i.val + 1 : ℕ) : ℝ) * alpha) ≠ 0 := by
      rw [Int.fract_ne_zero_iff]
      rintro ⟨z, hz⟩
      exact (halpha.natCast_mul (Nat.succ_ne_zero i.val)).ne_int z hz.symm
    have hp := lt_of_le_of_ne (Int.fract_nonneg
      (((i.val + 1 : ℕ) : ℝ) * alpha)) (Ne.symm hnz)
    dsimp [c]
    constructor <;> linarith [Int.fract_lt_one (((i.val + 1 : ℕ) : ℝ) * alpha)]
  have hc_inj : Function.Injective c := by
    intro i j hij
    by_contra hne
    have hfract : Int.fract (((i.val + 1 : ℕ) : ℝ) * alpha) =
        Int.fract (((j.val + 1 : ℕ) : ℝ) * alpha) := by
      dsimp [c] at hij
      linarith
    obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp hfract
    have hcoeff : ((i.val + 1 : ℕ) : ℤ) - ((j.val + 1 : ℕ) : ℤ) ≠ 0 := by
      intro he
      apply hne
      apply Fin.ext
      omega
    apply (halpha.intCast_mul hcoeff).ne_int z
    push_cast
    convert hz using 1 <;> ring
  let pairs : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  let gaps : Finset ℝ := insert (1 - alpha)
    (Finset.univ.image c ∪ pairs.image (fun p => |c p.1 - c p.2|))
  have hmem : 1 - alpha ∈ gaps := Finset.mem_insert_self _ _
  have hnonempty : gaps.Nonempty := ⟨1 - alpha, hmem⟩
  have hpos : ∀ z ∈ gaps, 0 < z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · linarith
    · rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
        exact (hc i).1
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
        apply abs_pos.mpr
        apply sub_ne_zero.mpr
        exact fun he => (Finset.mem_filter.mp hp).2 (hc_inj he)
  let g := gaps.min' hnonempty
  have hg : 0 < g := hpos g (Finset.min'_mem gaps hnonempty)
  have hga : g ≤ 1 - alpha := Finset.min'_le gaps _ hmem
  have hgc (i : Fin n) : g ≤ c i := Finset.min'_le gaps _
    (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, rfl⟩)))
  have hgap (i j : Fin n) (hij : i ≠ j) : g ≤ |c i - c j| :=
    Finset.min'_le gaps _ (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩)))
  let radius := g / (2 * ((n : ℝ) + 1))
  have hden : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have hr : 0 < radius := div_pos hg hden
  have hrlt : radius < g := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [mul_nonneg hg.le (Nat.cast_nonneg (R := ℝ) n)]
  refine ⟨radius, hr, by linarith, ?_⟩
  intro delta hd hdr
  let beta := alpha + delta
  let swept : Fin n → Set ℝ := fun i =>
    Ico (c i - ((i.val + 1 : ℕ) : ℝ) * delta) (c i)
  have hb0 : 0 ≤ beta := by dsimp [beta]; linarith
  have hb1 : beta < 1 := by dsimp [beta]; linarith
  have hmove (i : Fin n) : 0 ≤ ((i.val + 1 : ℕ) : ℝ) * delta ∧
      ((i.val + 1 : ℕ) : ℝ) * delta < g := by
    have hi : ((i.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt i.isLt)
    have hdelta : delta * (2 * ((n : ℝ) + 1)) ≤ g :=
      (le_div_iff₀ hden).mp hdr
    constructor
    · positivity
    · have hm := mul_le_mul_of_nonneg_right hi hd
      nlinarith
  have hsweep01 (i : Fin n) {x : ℝ} (hx : x ∈ swept i) : x ∈ Ico (0 : ℝ) 1 := by
    change c i - ((i.val + 1 : ℕ) : ℝ) * delta ≤ x ∧ x < c i at hx
    constructor
    · linarith [hgc i, (hmove i).2]
    · exact hx.2.trans (hc i).2
  have hdisj : Pairwise (fun i j => Disjoint (swept i) (swept j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    change c i - ((i.val + 1 : ℕ) : ℝ) * delta ≤ x ∧ x < c i at hxi
    change c j - ((j.val + 1 : ℕ) : ℝ) * delta ≤ x ∧ x < c j at hxj
    have hsep := hgap i j hij
    rcases lt_or_gt_of_ne (fun he => hij (hc_inj he)) with hcij | hcji
    · rw [abs_of_neg (sub_neg.mpr hcij)] at hsep
      linarith [(hmove j).2]
    · rw [abs_of_pos (sub_pos.mpr hcji)] at hsep
      linarith [(hmove i).2]
  -- Compute the cumulative floor change at every actual observation time.
  have hcarry (i : Fin n) (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
      ⌊x + ((i.val + 1 : ℕ) : ℝ) * beta⌋ -
        ⌊x + ((i.val + 1 : ℕ) : ℝ) * alpha⌋ =
        if x ∈ swept i then (1 : ℤ) else 0 := by
    let t : ℝ := ((i.val + 1 : ℕ) : ℝ) * alpha
    let e : ℝ := ((i.val + 1 : ℕ) : ℝ) * delta
    have he0 : 0 ≤ e := (hmove i).1
    have hec : e < 1 - Int.fract t := lt_of_lt_of_le (hmove i).2 (hgc i)
    have hf (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 - Int.fract t) :
        ⌊x + t + u⌋ = ⌊t⌋ + if 1 - Int.fract t - u ≤ x then 1 else 0 := by
      have hdecomp : (⌊t⌋ : ℝ) + (x + Int.fract t + u) = x + t + u := by
        have ht := Int.floor_add_fract t
        linarith
      rw [← hdecomp, Int.floor_intCast_add]
      congr 1
      by_cases h : 1 - Int.fract t - u ≤ x
      · rw [if_pos h, Int.floor_eq_iff]
        norm_num
        constructor <;> linarith [Int.fract_nonneg t, Int.fract_lt_one t]
      · rw [if_neg h, Int.floor_eq_iff]
        norm_num
        constructor
        · linarith [Int.fract_nonneg t]
        · linarith [lt_of_not_ge h]
    have heq : x + ((i.val + 1 : ℕ) : ℝ) * beta = x + t + e := by
      dsimp [beta, t, e]
      ring
    rw [heq, hf e he0 hec.le]
    have hbase := hf 0 (by norm_num) (by linarith [Int.fract_lt_one t])
    simp only [add_zero, sub_zero] at hbase
    change (_ + if c i - e ≤ x then (1 : ℤ) else 0) - ⌊x + t⌋ = _
    rw [hbase]
    change (_ + if c i - e ≤ x then (1 : ℤ) else 0) -
      (_ + if c i ≤ x then (1 : ℤ) else 0) = _
    by_cases hlo : c i - e ≤ x
    · by_cases hhi : x < c i
      · have hxC : x ∈ swept i := ⟨hlo, hhi⟩
        simp [hlo, not_le_of_gt hhi, hxC]
      · have hcx : c i ≤ x := le_of_not_gt hhi
        have hxC : x ∉ swept i := fun h => hhi h.2
        simp [hlo, hcx, hxC]
    · have hcx : ¬c i ≤ x := by intro h; apply hlo; linarith
      have hxC : x ∉ swept i := fun h => hlo h.1
      simp [hlo, hcx, hxC]
  have hpattern (i : Fin n) (x : ℝ) (hx : x ∈ swept i) (j : Fin n) :
      lowerMechanicalLetter beta x j.val - lowerMechanicalLetter alpha x j.val =
        (if j.val = i.val then (1 : ℤ) else 0) -
          (if j.val = i.val + 1 then (1 : ℤ) else 0) := by
    have hx01 := hsweep01 i hx
    have hF (k : ℕ) (hk : k ≤ n) :
        ⌊x + (k : ℝ) * beta⌋ - ⌊x + (k : ℝ) * alpha⌋ =
          if k = i.val + 1 then (1 : ℤ) else 0 := by
      cases k with
      | zero => simp
      | succ k =>
          let l : Fin n := ⟨k, by omega⟩
          have h := hcarry l x hx01
          by_cases heq : k = i.val
          · have hli : l = i := Fin.ext heq
            simpa [hli, hx, heq] using h
          · have hli : l ≠ i := fun he => heq (congrArg Fin.val he)
            have hxl : x ∉ swept l := fun hh => (Set.disjoint_left.mp (hdisj l i hli)) hh hx
            simpa [l, hxl, heq] using h
    have hnext := hF (j.val + 1) (by omega)
    have hprev := hF j.val j.isLt.le
    unfold lowerMechanicalLetter
    have hsum : (⌊x + ((j.val + 1 : ℕ) : ℝ) * beta⌋ - ⌊x + (j.val : ℝ) * beta⌋) -
        (⌊x + ((j.val + 1 : ℕ) : ℝ) * alpha⌋ - ⌊x + (j.val : ℝ) * alpha⌋) =
        (⌊x + ((j.val + 1 : ℕ) : ℝ) * beta⌋ - ⌊x + ((j.val + 1 : ℕ) : ℝ) * alpha⌋) -
        (⌊x + (j.val : ℝ) * beta⌋ - ⌊x + (j.val : ℝ) * alpha⌋) := by ring
    rw [hsum, hnext, hprev]
    simp only [Nat.add_right_cancel_iff]
  have hword (x : ℝ) (k : ℕ) :
      lowerMechanicalWord beta x k = lowerMechanicalWord alpha x k ↔
        lowerMechanicalLetter beta x k = lowerMechanicalLetter alpha x k := by
    rcases lowerMechanicalLetter_eq_zero_or_one (rho := x) hb0 hb1 k with hb | hb <;>
      rcases lowerMechanicalLetter_eq_zero_or_one (rho := x) h0.le h1 k with ha | ha <;>
      simp [lowerMechanicalWord, hb, ha]
  have hset : slopeDisagreement alpha beta n = ⋃ i, swept i := by
    ext x
    constructor
    · rintro ⟨hx01, k, hk⟩
      by_contra hnot
      have hnone (i : Fin n) : x ∉ swept i := fun hi => hnot (Set.mem_iUnion.mpr ⟨i, hi⟩)
      have hF (j : ℕ) (hj : j ≤ n) :
          ⌊x + (j : ℝ) * beta⌋ = ⌊x + (j : ℝ) * alpha⌋ := by
        cases j with
        | zero => simp
        | succ j =>
            have h := hcarry ⟨j, by omega⟩ x hx01
            rw [if_neg (hnone _)] at h
            exact sub_eq_zero.mp h
      apply hk
      apply (hword x k.val).mpr
      unfold lowerMechanicalLetter
      rw [hF (k.val + 1) (by omega), hF k.val k.isLt.le]
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      refine ⟨hsweep01 i hi, i, ?_⟩
      intro heq
      have hl := (hword x i.val).mp heq
      have hp := hpattern i x hi i
      rw [hl, sub_self] at hp
      simp at hp
  have hsum : ∀ N : ℕ, (∑ i : Fin N, ((i.val + 1 : ℕ) : ℝ)) =
      (N : ℝ) * ((N : ℝ) + 1) / 2 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one] at ih ⊢
        rw [ih]
        ring
  have hvol : volume (slopeDisagreement alpha beta n) =
      ENNReal.ofReal ((n : ℝ) * ((n : ℝ) + 1) / 2 * delta) := by
    rw [hset, measure_iUnion hdisj (fun _ => measurableSet_Ico), tsum_fintype]
    simp only [swept, Real.volume_Ico, sub_sub_cancel]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hmove i).1)]
    rw [← Finset.sum_mul, hsum n]
  exact ⟨hset, hdisj, hvol, hpattern⟩

#print axioms slopeDisagreement
#print axioms local_slope_disagreement_law

end D5.S1.Words.Mechanical.MechanicalSlopeSensitivity
