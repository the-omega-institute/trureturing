/- GID: D5/S3/Combinatorics/Circle/OriginalLowerFullBank
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/OriginalLowerFullBank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Original-source full-b LOWER selection and exact depleted w support. -/
module
public import D5.S3.Combinatorics.Circle.OriginalSourceRows
import all D5.S3.Combinatorics.Circle.OriginalSourceRows
import all D5.S3.Combinatorics.Circle.ZeroSumSubsets

/-! # A full retained bank for original LOWER sources

All words are mapped from the bounded actual physical occurrence inventory.
The least rounding coefficient preserves the entire positive b row; the
residual source recurrence determines literal retained w support.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace D5.S3.Combinatorics.Circle.OriginalLowerFullBank
open SourceWidth M5FullWordConsumer SourcePrefixInventory
open Fin.NatCast
open scoped BigOperators

private def fullKeep {D : PrefixArithmetic} (R : RowData naturalRows D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (Sz : Finset (Fin (R.len 0))) : Finset (Occ R.len) :=
  rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw ∪ fullRow R 1 ∪ rowMask R.len 0 Sz

private theorem fullKeep_available {D : PrefixArithmetic} (R : RowData naturalRows D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (Sz : Finset (Fin (R.len 0))) : fullKeep R Sn Sw Sz ⊆ bank R Sn Sw := by
  obtain ⟨hn, hw, hz, hb, hv⟩ := bank_parts R Sn Sw
  exact Finset.union_subset (Finset.union_subset (Finset.union_subset hn hw) hb)
    ((rowMask_mono R.len 0 (Finset.subset_univ Sz)).trans hz)

private theorem fullKeep_sum {D : PrefixArithmetic} (R : RowData naturalRows D) (A : ℤ) (c : ℕ)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (Sz : Finset (Fin (R.len 0)))
    (hn : weight Sn = A) (hw : weight Sw = D.H / 4 - A)
    (hz : weight Sz = (c : ℤ)) :
    -(∑ o ∈ fullKeep R Sn Sw Sz, R.f o) =
      A * D.n + (D.H / 4 - A) * D.w - (D.q - 1) * D.b + (c : ℤ) * D.z := by
  have hd1 : Disjoint (rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw) (fullRow R 1) := by
    simp only [fullRow, Finset.disjoint_union_left]
    constructor <;> apply rowMask_disjoint <;> decide
  have hd0 : Disjoint (rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw ∪ fullRow R 1)
      (rowMask R.len 0 Sz) := by
    simp only [fullRow, Finset.disjoint_union_left]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply rowMask_disjoint <;> decide
  rw [fullKeep, Finset.sum_union hd0, Finset.sum_union hd1,
    two_rows_sum R 2 4 Sn Sw (by decide), row_sum, fullRow_sum,
    hn, hw, hz, (show R.base 0 = -D.z from R.base0), (show R.base 1 = D.b from R.base1), (show R.base 2 = -D.n from R.base2), (show R.base 4 = -D.w from R.base4), (show (2 : ℤ) ^ R.len 1 = D.q from R.pow1)]
  ring

private theorem fullKeep_complement {D : PrefixArithmetic} (R : RowData naturalRows D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (Sz : Finset (Fin (R.len 0))) :
    bank R Sn Sw \ fullKeep R Sn Sw Sz = rowMask R.len 0 Szᶜ ∪ fullRow R 5 := by
  classical
  ext o
  rcases o with i | ⟨i, j⟩
  · simp [bank, fullKeep, fullRow]
  · by_cases hi0 : i = 0
    · subst i; simp [bank, fullKeep, fullRow]
    · by_cases hi1 : i = 1
      · subst i; simp [bank, fullKeep, fullRow]
      · by_cases hi2 : i = 2
        · subst i; simp [bank, fullKeep, fullRow]
        · by_cases hi4 : i = 4
          · subst i; simp [bank, fullKeep, fullRow]
          · by_cases hi5 : i = 5
            · subst i; simp [bank, fullKeep, fullRow]
            · simp (disch := omega) [bank, fullKeep, fullRow]

private theorem lower_above_two_b (D : PrefixArithmetic) (hF : D.F ≤ D.H / 4) :
    2 * D.b < D.u := by
  obtain ⟨hn, hz, hb, hw, hv, hu, hG, hq, hHw, hwb, hza⟩ := arithmetic_geometry D
  have h4 : 4 * D.F ≤ D.H := by have hH := D.H_four; omega
  have hm := mul_le_mul_of_nonneg_right h4 (le_of_lt hu)
  have hHu : 2 * (D.N + 1) ≤ D.H * D.u := by
    nlinarith only [hm, D.U_threshold]
  by_contra hbad
  have hm' := mul_le_mul_of_nonneg_left (le_of_not_gt hbad)
    (show 0 ≤ D.H by have hH := D.H_eight; omega)
  nlinarith only [hm', hHu, D.N_b, hn]

private theorem full_bank_selection {D : PrefixArithmetic} (R : RowData naturalRows D) (A f : ℤ)
    (hA : 1 ≤ A)
    (heq : 2 * f = D.n + D.w + D.Δ - 2 * A * (D.w - D.n))
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (hSn : weight Sn = A) (hSw : weight Sw = D.H / 4 - A)
    (hZ : 0 < wjHeight R f) (hF : D.F ≤ D.H / 4) :
    ∃ (c : ℕ) (Sz : Finset (Fin (R.len 0))) (K : TSelection R Sn Sw),
      (c : ℤ) ≤ D.q - 1 ∧ weight Sz = (c : ℤ) ∧
      K.keep = fullKeep R Sn Sw Sz ∧ K.pay = ∅ ∧
      (∀ j : ℕ, j < c →
        A * D.n + (D.H / 4 - A) * D.w - (D.q - 1) * D.b + (j : ℤ) * D.z <
          (D.u - D.z) / 2) ∧
      tSmall R K = rowMask R.len 0 Szᶜ ∪ fullRow R 5 := by
  classical
  obtain ⟨hn, hz, hb, hw, hv, hu, hG, hq, hHw, hwb, hza⟩ := arithmetic_geometry D
  obtain ⟨hell0, hW0, hell, hhi, hW, hwidth⟩ := gate_limits D
  let Dold := A * D.n + (D.H / 4 - A) * D.w - (D.q - 1) * D.b
  let ell := (D.u - D.z) / 2
  have hqb : (D.H / 4) * D.w < D.q * D.b := by
    have hw2b : D.w < 2 * D.b := by have hwa := D.w_bounds.2; have hab := D.ab; omega
    have hm := mul_pos (show 0 < D.H / 4 by omega) (sub_pos.mpr hw2b)
    have hqB := congrArg (fun q : ℤ => q * D.b) hq
    nlinarith only [hm, hqB]
  have hR : A * D.n + (D.H / 4 - A) * D.w ≤ (D.H / 4) * D.w := by
    have hm := mul_nonneg (show 0 ≤ A by omega) (show 0 ≤ D.w - D.n by have hwh := D.w_hard; have hd := D.delta_two; omega)
    nlinarith only [hm]
  have hD : Dold < D.b := by dsimp only [Dold]; nlinarith only [hR, hqb]
  have hsum : (∑ o ∈ bank R Sn Sw, R.f o) =
      -Dold - (D.q - 1) * D.z + (D.e - 1) * D.v := by
    have hd0 : Disjoint (rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw) (fullRow R 0) := by
      simp only [fullRow, Finset.disjoint_union_left]
      constructor <;> apply rowMask_disjoint <;> decide
    have hd1 : Disjoint (rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw ∪ fullRow R 0) (fullRow R 1) := by
      simp only [fullRow, Finset.disjoint_union_left]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply rowMask_disjoint <;> decide
    have hd5 : Disjoint (rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw ∪ fullRow R 0 ∪ fullRow R 1)
        (fullRow R 5) := by
      simp only [fullRow, Finset.disjoint_union_left]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> apply rowMask_disjoint <;> decide
    change (∑ o ∈ rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw ∪
      fullRow R 0 ∪ fullRow R 1 ∪ fullRow R 5, R.f o) =
      -Dold - (D.q - 1) * D.z + (D.e - 1) * D.v
    rw [Finset.sum_union hd5, Finset.sum_union hd1, Finset.sum_union hd0,
      two_rows_sum R 2 4 Sn Sw (by decide), fullRow_sum, fullRow_sum, fullRow_sum,
      hSn, hSw, (show (2 : ℤ) ^ R.len 0 = D.q from R.pow0), (show (2 : ℤ) ^ R.len 1 = D.q from R.pow1), (show (2 : ℤ) ^ R.len 5 = D.e from R.pow5), (show R.base 0 = -D.z from R.base0), (show R.base 1 = D.b from R.base1), (show R.base 2 = -D.n from R.base2), (show R.base 4 = -D.w from R.base4), (show R.base 5 = D.v from R.base5)]
    dsimp only [Dold]
    ring
  have hledger := bank_charge R A f heq Sn Sw hSn hSw
  have hcost := mul_nonneg (sub_nonneg.mpr D.e_one) (le_of_lt hv)
  have hreach : ell ≤ Dold + (D.q - 1) * D.z := by
    rw [hsum] at hledger
    dsimp only [ell]
    nlinarith only [hledger, hell, hZ, hcost]
  have hqc : (((D.q - 1).toNat : ℕ) : ℤ) = D.q - 1 := Int.toNat_of_nonneg (by omega)
  have hex : ∃ c : ℕ, ell ≤ Dold + (c : ℤ) * D.z := by
    refine ⟨(D.q - 1).toNat, ?_⟩
    simpa only [hqc] using hreach
  let c := Nat.find hex
  have hc : ell ≤ Dold + (c : ℤ) * D.z := Nat.find_spec hex
  have hcq : (c : ℤ) ≤ D.q - 1 := by
    have hh := Nat.find_min' hex (show ell ≤ Dold + ((D.q - 1).toNat : ℤ) * D.z by
      simpa only [hqc] using hreach)
    have hcast : (c : ℤ) ≤ ((D.q - 1).toNat : ℤ) := by
      exact_mod_cast (show c ≤ (D.q - 1).toNat from hh)
    omega
  have hminimal (j : ℕ) (hj : j < c) : Dold + (j : ℤ) * D.z < ell :=
    lt_of_not_ge (Nat.find_min hex hj)
  have hu2b := lower_above_two_b D hF
  have hu2z : 2 * D.z < D.u := by have hzb := D.nzb.2; omega
  have hupper : Dold + (c : ℤ) * D.z ≤ D.u - (D.z + 1) / 2 := by
    by_cases hc0 : c = 0
    · simp only [hc0, Nat.cast_zero, zero_mul, add_zero]
      have hoz := D.odd_z
      have hzb := D.nzb.2
      omega
    · have hprev := hminimal (c - 1) (by omega)
      have hcast : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
      rw [hcast] at hprev
      nlinarith only [hprev, hu2z, hell, hhi]
  obtain ⟨Sz, hSz⟩ := mask_exists (R.len 0) (c : ℤ) (by omega)
    (by rw [(show (2 : ℤ) ^ R.len 0 = D.q from R.pow0)]; omega)
  let K : TSelection R Sn Sw := {
    keep := fullKeep R Sn Sw Sz
    available := fullKeep_available R Sn Sw Sz
    pay := ∅
    gate := by
      rw [fullKeep_sum R A c Sn Sw Sz hSn hSw hSz]
      simp only [weight, Finset.sum_empty, zero_mul, sub_zero]
      exact ⟨hc, hupper⟩ }
  refine ⟨c, Sz, K, hcq, hSz, rfl, rfl, hminimal, ?_⟩
  simp only [tSmall, K, rowMask, Finset.map_empty, Finset.union_empty]
  exact fullKeep_complement R Sn Sw Sz

/- Exact finite complement; no saturated beyond-boundary parent is included. -/
private def fullBank {D : PrefixArithmetic} (R : RowData naturalRows D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (Sz : Finset (Fin (R.len 0))) : Finset (Occ R.len) :=
  fullKeep R Sn Sw Sz ∪ fullRow R 6

private theorem fullBank_partition {D : PrefixArithmetic} (R : RowData naturalRows D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (Sz : Finset (Fin (R.len 0))) (K : TSelection R Sn Sw)
    (hk : K.keep = fullKeep R Sn Sw Sz) (hp : K.pay = ∅) :
    Disjoint (tUsed R K) (fullBank R Sn Sw Sz) ∧
      tUsed R K ∪ fullBank R Sn Sw Sz = (occurrences 7 R.len).toFinset := by
  classical
  have hs : tSmall R K = rowMask R.len 0 Szᶜ ∪ fullRow R 5 := by
    simp only [tSmall, hk, hp, rowMask, Finset.map_empty, Finset.union_empty]
    exact fullKeep_complement R Sn Sw Sz
  constructor
  · apply Finset.disjoint_left.mpr
    intro o ho hb
    rcases o with i | ⟨i, j⟩
    · simpa [fullBank, fullKeep, fullRow] using hb
    · by_cases hi : i < 7
      · interval_cases i <;>
          simp [tUsed, hs, wjUsed, firstParents, initialSmall, fullBank, fullKeep, fullRow] at ho hb <;> tauto
      · simp (disch := omega) [fullBank, fullKeep, fullRow] at hb
  · ext o
    rcases o with i | ⟨i, j⟩
    · by_cases hi : i < 7
      · interval_cases i <;>
          simp [tUsed, hs, wjUsed, firstParents, initialSmall, fullBank, fullKeep, fullRow, mem_occurrences]
      · simp (disch := omega) [tUsed, hs, wjUsed, firstParents, initialSmall, fullBank,
          fullKeep, fullRow, mem_occurrences, hi] <;> omega
    · by_cases hi : i < 7
      · interval_cases i <;>
          simp [tUsed, hs, wjUsed, firstParents, initialSmall, fullBank, fullKeep, fullRow,
            mem_occurrences] <;> tauto
      · simp (disch := omega) [tUsed, hs, wjUsed, firstParents, initialSmall, fullBank,
          fullKeep, fullRow, mem_occurrences, hi]

private theorem fullBank_charge {D : PrefixArithmetic} (R : RowData naturalRows D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (Sz : Finset (Fin (R.len 0))) (K : TSelection R Sn Sw)
    (hk : K.keep = fullKeep R Sn Sw Sz) (hp : K.pay = ∅) :
    2 * (tHeight R K + ∑ o ∈ fullBank R Sn Sw Sz, R.f o) = D.z + D.y := by
  have hd := (bank_row6_disjoint R Sn Sw (Finset.univ : Finset (Fin (R.len 6)))).mono_left
    (fullKeep_available R Sn Sw Sz)
  change Disjoint (fullKeep R Sn Sw Sz) (fullRow R 6) at hd
  have hs : (∑ o ∈ fullBank R Sn Sw Sz, R.f o) =
      (∑ o ∈ K.keep, R.f o) - ((2 : ℤ) ^ R.len 6 - 1) * D.u := by
    rw [fullBank, Finset.sum_union hd, fullRow_sum, (show R.base 6 = -D.u from R.base6), ← hk]
    ring
  obtain ⟨he0, hw0, he, hhi, hw, hwidth⟩ := gate_limits D
  have hpu := congrArg (fun n : ℤ => n * D.u) (show 2 * (2 : ℤ) ^ R.len 6 = D.F from R.pow6)
  rw [hs]
  dsimp only [tHeight]
  rw [hp]
  simp only [weight, Finset.sum_empty, zero_mul, sub_zero]
  nlinarith only [he, hpu, R.large6, D.y_source]

/- G8: reuse the existing natural binary-mask injectivity theorem. The new
content is the source-forced range and literal retained support decomposition. -/
private theorem weight_injective {u : ℕ} : Function.Injective (weight (u := u)) := by
  intro S T h
  apply ZeroSumSubsets.mask_injective u
  change (∑ j ∈ S, (2 : ℕ) ^ j.val) = ∑ j ∈ T, (2 : ℕ) ^ j.val
  rw [weight_nat, weight_nat] at h
  exact_mod_cast h

def liftMask {r l : ℕ} (hr : r ≤ l) (S : Finset (Fin r)) : Finset (Fin l) :=
  S.map ⟨fun j => ⟨j.val, lt_of_lt_of_le j.isLt hr⟩,
    by intro i j he; exact Fin.ext (congrArg (Fin.val (n := l)) he)⟩

private theorem weight_liftMask {r l : ℕ} (hr : r ≤ l) (S : Finset (Fin r)) :
    weight (liftMask hr S) = weight S := by
  rw [weight, liftMask, Finset.sum_map]
  rfl

private theorem mem_lift_full {r l : ℕ} (hr : r ≤ l) (j : Fin l) :
    j ∈ liftMask hr (Finset.univ : Finset (Fin r)) ↔ j.val < r := by
  constructor
  · intro hj
    obtain ⟨i, hi, he⟩ := Finset.mem_map.mp hj
    have hv : i.val = j.val := congrArg (Fin.val (n := l)) he
    omega
  · intro hj
    exact Finset.mem_map.mpr ⟨⟨j.val, hj⟩, Finset.mem_univ _, Fin.ext rfl⟩

private theorem depleted_w_decomposition {l r : ℕ} (hr : r < l) (A : ℤ)
    (hA : 1 ≤ A) (hAt : A ≤ (2 : ℤ) ^ r)
    (Sw : Finset (Fin l)) (hSw : weight Sw = (2 : ℤ) ^ l - A) :
    ∃ Slow : Finset (Fin l),
      weight Slow = (2 : ℤ) ^ r - A ∧
      (∀ j ∈ Slow, j.val < r) ∧
      Disjoint Slow {⟨r, hr⟩} ∧
      Sw = (liftMask (Nat.succ_le_of_lt hr) (Finset.univ : Finset (Fin (r + 1))))ᶜ ∪
        {⟨r, hr⟩} ∪ Slow ∧
      Slow ⊆ Sw ∧ (⟨r, hr⟩ : Fin l) ∈ Sw ∧
      (2 ≤ A → Sw ≠ Finset.univ) := by
  classical
  obtain ⟨S, hS⟩ := mask_exists r ((2 : ℤ) ^ r - A) (by omega) (by omega)
  let Slow := liftMask (Nat.le_of_lt hr) S
  let High := (liftMask (Nat.succ_le_of_lt hr) (Finset.univ : Finset (Fin (r + 1))))ᶜ
  let top : Fin l := ⟨r, hr⟩
  have hlow : ∀ j ∈ Slow, j.val < r := by
    intro j hj
    obtain ⟨i, hi, he⟩ := Finset.mem_map.mp hj
    have hv : i.val = j.val := congrArg (Fin.val (n := l)) he
    omega
  have hHigh : ∀ j ∈ High, r + 1 ≤ j.val := by
    intro j hj
    have hh := Finset.mem_compl.mp hj
    rw [mem_lift_full] at hh
    omega
  have hdht : Disjoint High {top} := by
    apply Finset.disjoint_left.mpr
    intro j hj ht
    have he := Finset.mem_singleton.mp ht
    subst j
    have hh := hHigh top hj
    change r + 1 ≤ r at hh
    omega
  have hdtl : Disjoint ({top} : Finset (Fin l)) Slow := by
    apply Finset.disjoint_left.mpr
    intro j ht hj
    have he := Finset.mem_singleton.mp ht
    subst j
    have hh := hlow top hj
    change r < r at hh
    omega
  have hdhl : Disjoint High Slow := by
    apply Finset.disjoint_left.mpr
    intro j hj hl
    have h1 := hHigh j hj
    have h2 := hlow j hl
    omega
  have hwl : weight Slow = (2 : ℤ) ^ r - A := by
    rw [weight_liftMask]
    exact hS
  have hwh : weight High = (2 : ℤ) ^ l - 2 * (2 : ℤ) ^ r := by
    rw [weight_compl, weight_liftMask, weight_full, pow_succ]
    ring
  have he : Sw = High ∪ {top} ∪ Slow := by
    apply weight_injective
    rw [hSw]
    change (2 : ℤ) ^ l - A = ∑ j ∈ High ∪ {top} ∪ Slow, (2 : ℤ) ^ j.val
    rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdhl, hdtl⟩),
      Finset.sum_union hdht]
    simp only [Finset.sum_singleton]
    change (2 : ℤ) ^ l - A = weight High + (2 : ℤ) ^ r + weight Slow
    rw [hwh, hwl]
    ring
  refine ⟨Slow, hwl, hlow, hdtl.symm, he, ?_, ?_, ?_⟩
  · rw [he]
    exact Finset.subset_union_right
  · rw [he]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  · intro h2 hfull
    have hh := congrArg weight hfull
    rw [hSw, weight_full] at hh
    omega

private theorem source_A_le_tau {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x)
    (he : (sourcePrefixArithmetic h).e = 1) (hF : 4 ≤ (sourcePrefixArithmetic h).F)
    (hy : (sourcePrefixArithmetic h).y ≤ 2 * b - 3)
    (A : ℤ)
    (hprev : 2 * ((sourcePrefixArithmetic h).w - (sourcePrefixArithmetic h).n) * (A - 1) <
      (sourcePrefixArithmetic h).n + (sourcePrefixArithmetic h).Δ + 1) :
    A ≤ (2 : ℤ) ^ sourceLength t x 6 := by
  let D := sourcePrefixArithmetic h
  change D.e = 1 at he
  change 4 ≤ D.F at hF
  change D.y ≤ 2 * D.b - 3 at hy
  change 2 * (D.w - D.n) * (A - 1) < D.n + D.Δ + 1 at hprev
  obtain ⟨hn, hz, hb, hw, hv, hu, hG, hq, hHw, hwb, hza⟩ := arithmetic_geometry D
  let eta := D.F * D.w - (D.F + 1) * D.b
  have huEq : D.u = D.H * D.w - D.N := by
    have hh := congrArg (fun q : ℤ => q * D.w) D.H_q
    have hus := D.u_source
    rw [he] at hus
    nlinarith only [hus, D.v_source, hh]
  have heta : D.H * eta = (D.F + 1) * D.n - D.y := by
    have hys := D.y_source
    rw [huEq] at hys
    have hNb := congrArg (fun s : ℤ => (D.F + 1) * s) D.N_b
    dsimp only [eta]
    nlinarith only [hys, hNb]
  have hn2b : D.b < 2 * D.n := by have ha := D.n_minimum; have hab := D.ab.2; omega
  have heta0 : 0 < eta := by
    have hm := mul_nonneg (show 0 ≤ D.F - 4 by omega) (le_of_lt hn)
    by_contra hh
    have hm' := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ D.H by have hH := D.H_eight; omega)
      (show eta ≤ 0 by omega)
    change D.y ≤ 2 * D.b - 3 at hy
    nlinarith only [heta, hm, hm', hy, hn2b, hn]
  have hFK : D.n + D.Δ + 1 < D.F * (D.w - D.n) := by
    have hH := D.H_eight
    have hDel := D.delta_two
    have hpositive := mul_nonneg (show 0 ≤ D.F - 1 by omega)
      (show 0 ≤ D.H * D.Δ by positivity)
    have hid : D.F * (D.w - D.n) = D.b + eta + D.F * D.H * D.Δ := by
      dsimp only [eta]
      rw [D.b_n]
      ring
    have hHD := mul_nonneg (show 0 ≤ D.H - 1 by omega) (show 0 ≤ D.Δ by omega)
    nlinarith only [hid, D.b_n, heta0, hpositive, hHD, hDel]
  have hpow : D.F = 2 * (2 : ℤ) ^ sourceLength t x 6 := by
    change (2 : ℤ) ^ (sourceLength t x 6 + 1) = _
    rw [pow_succ]
    ring
  have hK : 0 < D.w - D.n := by have hh := D.w_hard; have hd := D.delta_two; omega
  by_contra hbad
  have hm := mul_nonneg (le_of_lt hK)
    (show 0 ≤ A - 1 - (2 : ℤ) ^ sourceLength t x 6 by omega)
  have hFKpow := congrArg (fun q : ℤ => q * (D.w - D.n)) hpow
  nlinarith only [hm, hprev, hFK, hFKpow]

/-- Literal physical positions in a computed source row. -/
def sourceMask {k : ℕ} (t : ℕ) (x : Fin k) (i : ℕ)
    (S : Finset (Fin (sourceLength t x i))) : Finset (Fin k) :=
  S.image (fun j => advance (sourceParent t x i) (j.val + 1))

/-- Chronological labels starting with row seven, including its parent U,
up to the actual boundary at 2m. The boundary x is excluded. -/
def futureLabels {k : ℕ} (m t : ℕ) (x : Fin k) : Finset (Fin k) :=
  (((List.range (2 * m)).filter (fun i => 7 ≤ i)).flatMap (fun i =>
    sourceParent t x i :: rowLabels (sourceParent t x i) (sourceLength t x i))).toFinset

private theorem physical_mask_image {k t : ℕ} (x : Fin k) (i : ℕ)
    (S : Finset (Fin (sourceLength t x i))) :
    (rowMask (fun j => sourceLength t x j) i S).image (physical x) = sourceMask t x i S := by
  classical
  ext z
  simp [rowMask, sourceMask, physical]

private theorem map_nodup_on {α β : Type*} (f : α → β) (l : List α)
    (hn : l.Nodup)
    (hi : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hh := List.nodup_cons.mp hn
    rw [List.map_cons, List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
      have heq := hi b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self) he
      subst b
      exact hh.1 hb
    · apply ih hh.2
      intro b hb c hc he
      exact hi b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc) he

private theorem word_finset_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : α → ℤ} {C h : ℤ} {first : α} {U : Finset α}
    (pre : Prefix s C first U h) (phi : α → β) :
    (pre.word.map phi).toFinset = U.image phi := by
  ext j
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨o, ho, he⟩
    exact ⟨o, Finset.mem_toList.mp (pre.perm.mem_iff.mp ho), he⟩
  · rintro ⟨o, ho, he⟩
    exact ⟨o, pre.perm.mem_iff.mpr (Finset.mem_toList.mpr ho), he⟩

private theorem physical_future_image {m k t : ℕ} (x : Fin k) :
    (((occurrences (2 * m) (fun i => sourceLength t x i)).toFinset) \
      (occurrences 7 (fun i => sourceLength t x i)).toFinset).image (physical x) =
      futureLabels m t x := by
  classical
  ext z
  simp only [Finset.mem_image, Finset.mem_sdiff, List.mem_toFinset,
    futureLabels, List.mem_flatMap, List.mem_filter, List.mem_range,
    List.mem_cons, rowLabels, List.mem_ofFn, decide_eq_true_eq]
  constructor
  · rintro ⟨o, ⟨ho, hn⟩, he⟩
    rcases o with i | ⟨i, j⟩
    · rw [mem_occurrences] at ho hn
      exact ⟨i, ⟨ho, by omega⟩, Or.inl he.symm⟩
    · rw [mem_occurrences] at ho hn
      change i < 2 * m at ho
      change ¬i < 7 at hn
      exact ⟨i, ⟨ho, by omega⟩, Or.inr ⟨j, he⟩⟩
  · rintro ⟨i, ⟨hi, hi7⟩, he | ⟨j, he⟩⟩
    · exact ⟨Sum.inl i, ⟨mem_occurrences.mpr hi, by rw [mem_occurrences]; omega⟩, he.symm⟩
    · exact ⟨Sum.inr ⟨i, j⟩, ⟨mem_occurrences.mpr hi, by rw [mem_occurrences]; change ¬i < 7; omega⟩, he⟩

set_option maxHeartbeats 2000000 in
/-- A source-attained canonical LOWER prefix retains the entire positive b row.
In the e=1 residual it also exposes the exact low-w mask and tau occurrence.
All source quantities, including row-eight a0, are the computed actual ones. -/
theorem canonical_lower_full_bank {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x)
    (hLower : (2 : ℤ) ^ (sourceLength t x 6 + 1) ≤ (2 : ℤ) ^ (L + 1) / 4) :
    let D := sourceCoordinates h
    let s := actualSource k t
    ∃ (A f : ℤ) (c : ℕ)
      (Sn : Finset (Fin (sourceLength t x 2)))
      (Sw : Finset (Fin (sourceLength t x 4)))
      (Sz : Finset (Fin (sourceLength t x 0))) (word : List (Fin k)),
      1 ≤ A ∧ A ≤ D.H / 4 ∧ 0 ≤ f ∧ f ≤ (D.w - 1) / 2 ∧
      2 * f = D.n + D.w + D.Δ - 2 * A * (D.w - D.n) ∧
      2 * (D.w - D.n) * (A - 1) < D.n + D.Δ + 1 ∧
      D.n + D.Δ + 1 ≤ 2 * (D.w - D.n) * A ∧
      (∑ j ∈ Sn, (2 : ℤ) ^ j.val) = A ∧ (∑ j ∈ Sw, (2 : ℤ) ^ j.val) = D.H / 4 - A ∧ (∑ j ∈ Sz, (2 : ℤ) ^ j.val) = (c : ℤ) ∧
      (c : ℤ) ≤ D.q - 1 ∧
      (∀ j : ℕ, j < c → A * D.n + (D.H / 4 - A) * D.w - (D.q - 1) * D.b +
        (j : ℤ) * D.z < (D.u - D.z) / 2) ∧
      (let Kfull := sourceMask t x 2 Sn ∪ sourceMask t x 4 Sw ∪
        sourceMask t x 1 Finset.univ ∪ sourceMask t x 0 Sz ∪ sourceMask t x 6 Finset.univ
       let Dold := A * D.n + (D.H / 4 - A) * D.w - (D.q - 1) * D.b
       (D.u - D.z) / 2 ≤ Dold + (c : ℤ) * D.z ∧
       Dold + (c : ℤ) * D.z ≤ D.u - (D.z + 1) / 2 ∧
       word.Nodup ∧ word.head? = some x ∧
       (∀ j : ℕ, 0 ≤ ((word.take j).map (s)).sum ∧
         ((word.take j).map (s)).sum ≤ halfCapacity k) ∧
       Disjoint word.toFinset Kfull ∧
       word.toFinsetᶜ = Kfull ∪ futureLabels m t x ∧
       Disjoint Kfull (futureLabels m t x) ∧
       2 * ((word.map (s)).sum + ∑ i ∈ Kfull, s i) = D.z + D.y ∧
       (D.e = 1 → 4 ≤ D.F → D.y ≤ 2 * b - 3 →
         ∃ (hr : sourceLength t x 6 < sourceLength t x 4)
           (Slow : Finset (Fin (sourceLength t x 4))),
           (∑ j ∈ Slow, (2 : ℤ) ^ j.val) = (2 : ℤ) ^ sourceLength t x 6 - A ∧
           (∀ j ∈ Slow, j.val < sourceLength t x 6) ∧
           Disjoint Slow {⟨sourceLength t x 6, hr⟩} ∧
           Sw = (liftMask (Nat.succ_le_of_lt hr) Finset.univ)ᶜ ∪
             {⟨sourceLength t x 6, hr⟩} ∪ Slow ∧
           sourceMask t x 4 Slow ⊆ Kfull ∧
           advance (sourceParent t x 4) (sourceLength t x 6 + 1) ∈ Kfull ∧
           (2 ≤ A → Sw ≠ Finset.univ))) := by
  classical
  let D := sourcePrefixArithmetic h
  let R := sourceData h
  have hm := h.pairs
  obtain ⟨A, f, hA, hAG, hf, hfg, heq, hprev, hnext⟩ := canonical_mask_height D
  obtain ⟨hn, hz, hb, hw, hv, hu, hG, hq, hHw, hwb, hza⟩ := arithmetic_geometry D
  have hpow2 : (2 : ℤ) ^ R.len 2 = D.q := (show (2 : ℤ) ^ R.len 2 = D.q from R.pow2)
  have hpow4 : (2 : ℤ) ^ R.len 4 = D.H / 4 := (show (2 : ℤ) ^ R.len 4 = D.H / 4 from R.pow4)
  obtain ⟨Sn, hSn⟩ := mask_exists (R.len 2) A (by omega) (by rw [hpow2]; omega)
  obtain ⟨Sw, hSw⟩ := mask_exists (R.len 4) (D.H / 4 - A) (by omega)
    (by rw [hpow4]; omega)
  obtain ⟨⟨preJ⟩, hZ, hZv⟩ := wj_prefix R A f hA hAG hf hfg heq Sn Sw hSn hSw
  obtain ⟨c, Sz, K, hcq, hSz, hk, hp, hmin, hsmall⟩ :=
    full_bank_selection R A f hA heq Sn Sw hSn hSw hZ hLower
  obtain ⟨preT⟩ := t_extension R A f heq Sn Sw hSn hSw preJ K
  obtain ⟨hd, hpart⟩ := fullBank_partition R Sn Sw Sz K hk hp
  let phi : Occ R.len → Fin k := physical (t := t) x
  let U := tUsed R K
  let B := fullBank R Sn Sw Sz
  let All := (occurrences (2 * m) R.len).toFinset
  let Future := All \ (occurrences 7 R.len).toFinset
  have hinj := physical_injective_on h
  have hvalid (o : Occ R.len) (ho : o ∈ U ∪ B) : o ∈ All := by
    change o ∈ tUsed R K ∪ fullBank R Sn Sw Sz at ho
    rw [hpart] at ho
    have hh := mem_occurrences.mp (List.mem_toFinset.mp ho)
    apply List.mem_toFinset.mpr
    apply mem_occurrences.mpr
    rcases o with i | ⟨i, j⟩ <;> change i < 7 at hh <;> change i < 2 * m <;> omega
  have huvalid (o : Occ R.len) (ho : o ∈ preT.word) :
      o ∈ occurrences (2 * m) R.len := by
    apply List.mem_toFinset.mp
    exact hvalid o (Finset.mem_union_left _ (Finset.mem_toList.mp (preT.perm.mem_iff.mp ho)))
  have hnd : (preT.word.map phi).Nodup := by
    apply map_nodup_on phi preT.word (preT.perm.nodup_iff.mpr U.nodup_toList)
    intro o ho o' ho' he
    exact hinj (huvalid o ho) (huvalid o' ho') he
  let word := preT.word.map phi
  have hwused : word.toFinset = U.image phi := word_finset_image preT phi
  let Kfull := sourceMask t x 2 Sn ∪ sourceMask t x 4 Sw ∪ sourceMask t x 1 Finset.univ ∪
    sourceMask t x 0 Sz ∪ sourceMask t x 6 Finset.univ
  have hrowimage (i : ℕ) (S : Finset (Fin (R.len i))) :
      (rowMask R.len i S).image phi = sourceMask t x i S := physical_mask_image x i S
  have hbimage : B.image phi = Kfull := by
    simp only [B, fullBank, fullKeep, Finset.image_union, fullRow, hrowimage, Kfull]
    rfl
  have htimage : Future.image phi = futureLabels m t x := physical_future_image x
  have hbd : Disjoint word.toFinset Kfull := by
    rw [hwused, ← hbimage]
    apply Finset.disjoint_left.mpr
    intro z hz1 hz2
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hz1
    obtain ⟨o', ho', he⟩ := Finset.mem_image.mp hz2
    have heq := hinj (List.mem_toFinset.mp (hvalid o' (Finset.mem_union_right _ ho')))
      (List.mem_toFinset.mp (hvalid o (Finset.mem_union_left _ ho))) he
    subst o'
    exact Finset.disjoint_left.mp hd ho ho'
  have hfuture (o : Occ R.len) : o ∈ Future ↔ o ∈ All ∧ o ∉ U ∪ B := by
    simp only [Future, Finset.mem_sdiff, ← hpart]
    rfl
  have hsurj (z : Fin k) : ∃ o ∈ All, phi o = z := by
    obtain ⟨o, ho, he⟩ := List.mem_map.mp ((physical_inventory h).mem_iff.mpr (List.mem_finRange z))
    exact ⟨o, List.mem_toFinset.mpr ho, he⟩
  have hcomp : word.toFinsetᶜ = Kfull ∪ futureLabels m t x := by
    rw [hwused, ← hbimage, ← htimage]
    ext z
    obtain ⟨o, ho, rfl⟩ := hsurj z
    have himg (S : Finset (Occ R.len)) (hS : S ⊆ All) : phi o ∈ S.image phi ↔ o ∈ S := by
      constructor
      · intro hz
        obtain ⟨o', ho', he⟩ := Finset.mem_image.mp hz
        have heq := hinj (List.mem_toFinset.mp (hS ho')) (List.mem_toFinset.mp ho) he
        simpa only [heq] using ho'
      · intro hs
        exact Finset.mem_image.mpr ⟨o, hs, rfl⟩
    rw [Finset.mem_compl, Finset.mem_union,
      himg U (fun o ho => hvalid o (Finset.mem_union_left _ ho)),
      himg B (fun o ho => hvalid o (Finset.mem_union_right _ ho)),
      himg Future Finset.sdiff_subset, hfuture]
    have hdis : o ∈ U → o ∈ B → False := fun hu hb => Finset.disjoint_left.mp hd hu hb
    simp only [Finset.mem_union]
    tauto
  have hbfuture : Disjoint Kfull (futureLabels m t x) := by
    rw [← hbimage, ← htimage]
    apply Finset.disjoint_left.mpr
    intro z hz1 hz2
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hz1
    obtain ⟨o', ho', he⟩ := Finset.mem_image.mp hz2
    have hs := (hfuture o').mp ho'
    have heq := hinj (List.mem_toFinset.mp hs.1)
      (List.mem_toFinset.mp (hvalid o (Finset.mem_union_right _ ho))) he
    subst o'
    exact hs.2 (Finset.mem_union_right _ ho)
  have hsum : (∑ z ∈ Kfull, actualSource k t z) = ∑ o ∈ B, R.f o := by
    rw [← hbimage, Finset.sum_image]
    · rfl
    · intro o ho o' ho' he
      exact hinj (List.mem_toFinset.mp (hvalid o (Finset.mem_union_right _ ho)))
        (List.mem_toFinset.mp (hvalid o' (Finset.mem_union_right _ ho'))) he
  have hwordSum : (word.map (actualSource k t)).sum = tHeight R K := by
    change ((preT.word.map phi).map (actualSource k t)).sum = tHeight R K
    rw [List.map_map]
    exact preT.height
  have hgate := K.gate
  rw [hp, hk, fullKeep_sum R A c Sn Sw Sz hSn hSw hSz] at hgate
  simp only [weight, Finset.sum_empty, zero_mul, sub_zero] at hgate
  refine ⟨A, f, c, Sn, Sw, Sz, word, hA, hAG, hf, hfg, heq, hprev, hnext,
    hSn, hSw, hSz, hcq, hmin, hgate.1, hgate.2, hnd, ?_, ?_, hbd,
    hcomp, hbfuture, ?_, ?_⟩
  · change (preT.word.map phi).head? = some x
    rw [List.head?_map, preT.head]
    change some (sourceParent t x 0) = some x
    rw [source_parent_zero h]
  · have hl : InStrip (actualSource k t) (halfCapacity k) 0 word :=
      (inStrip_map phi (actualSource k t) (halfCapacity k) 0 preT.word).mpr preT.legal
    intro j
    simpa only [zero_add] using inStrip_prefix hl j
  · rw [hsum, hwordSum]
    exact fullBank_charge R Sn Sw Sz K hk hp
  · intro he hF hy
    have hAt := source_A_le_tau h he hF hy A hprev
    have hr : sourceLength t x 6 < sourceLength t x 4 := by
      have hpow : (2 : ℤ) ^ (sourceLength t x 6 + 1) ≤ (2 : ℤ) ^ sourceLength t x 4 := by
        change D.F ≤ (2 : ℤ) ^ R.len 4
        rw [(show (2 : ℤ) ^ R.len 4 = D.H / 4 from R.pow4)]
        exact hLower
      by_contra hh
      have hm' := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show sourceLength t x 4 ≤ sourceLength t x 6 by omega)
      have hp' : (0 : ℤ) < 2 ^ sourceLength t x 6 := by positivity
      rw [pow_succ] at hpow
      nlinarith only [hpow, hm', hp']
    have hSw' : weight Sw = (2 : ℤ) ^ sourceLength t x 4 - A := by
      change weight Sw = (2 : ℤ) ^ R.len 4 - A
      rw [(show (2 : ℤ) ^ R.len 4 = D.H / 4 from R.pow4)]
      exact hSw
    obtain ⟨Slow, hwl, hlow, hdis, heqW, hsub, htop, hdeplete⟩ :=
      depleted_w_decomposition hr A hA hAt Sw hSw'
    refine ⟨hr, Slow, hwl, hlow, hdis, heqW, ?_, ?_, hdeplete⟩
    · intro z hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      have hjw : advance (sourceParent t x 4) (j.val + 1) ∈ sourceMask t x 4 Sw :=
        Finset.mem_image.mpr ⟨j, hsub hj, rfl⟩
      simp only [Kfull, Finset.mem_union]
      tauto
    · have hjw : advance (sourceParent t x 4) (sourceLength t x 6 + 1) ∈ sourceMask t x 4 Sw :=
        Finset.mem_image.mpr ⟨⟨sourceLength t x 6, hr⟩, htop, rfl⟩
      simp only [Kfull, Finset.mem_union]
      tauto

end D5.S3.Combinatorics.Circle.OriginalLowerFullBank
