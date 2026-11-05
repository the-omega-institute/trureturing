/- GID: D5/S3/Combinatorics/Circle/M5PhysicalInventory
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/M5PhysicalInventory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical row occurrences and exact legal prefix extensions. -/
module
import all D5.S3.Combinatorics.Circle.M5AttainedMesh
import all D5.S3.Combinatorics.Circle.TwoLargeOrdering
public import D5.S3.Combinatorics.Circle.SourcePrefixInventory
/-! # M5PhysicalInventory -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.M5FullWordConsumer

open SourceWidth SourcePrefixInventory
open Fin.NatCast
open scoped BigOperators

private def occurrences (len : Fin 10 → ℕ) : List (Occ len) :=
  (List.finRange 10).flatMap (fun i => Sum.inl i :: List.ofFn (fun j => Sum.inr ⟨i, j⟩))

private theorem mem_occurrences (len : Fin 10 → ℕ) (o : Occ len) : o ∈ occurrences len := by
  rcases o with i | ⟨i, j⟩
  · exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by simp⟩
  · exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
      List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨j, rfl⟩)⟩

private def physical {k t : ℕ} (x : Fin k) :
    Occ (fun i : Fin 10 => sourceLength t x i.val) → Fin k
  | .inl i => sourceParent t x i.val
  | .inr ⟨i, j⟩ => advance (sourceParent t x i.val) (j.val + 1)

private theorem physical_inventory {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) :
    ((occurrences (fun i : Fin 10 => sourceLength t x i.val)).map (physical x)).Perm
      (List.finRange k) := by
  have hp := source_partition h
  have he : (occurrences (fun i : Fin 10 => sourceLength t x i.val)).map (physical x) =
      (List.range 10).flatMap (fun i => sourceParent t x i ::
        rowLabels (sourceParent t x i) (sourceLength t x i)) := by
    simp only [occurrences, List.map_flatMap, List.map_cons, List.map_ofFn, physical,
      rowLabels, Function.comp_apply]
    rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
    apply List.flatMap_congr
    intro i _
    rfl
  rw [he]
  exact hp

private theorem physical_injective {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) : Function.Injective (physical (t := t) x) := by
  have hnd := (physical_inventory h).nodup_iff.mpr (List.nodup_finRange k)
  exact fun o o' he => List.inj_on_of_nodup_map hnd
    (mem_occurrences _ o) (mem_occurrences _ o') he

private structure RowData (D : Arithmetic) extends
    SourcePrefixInventory.RowData fivePairRows D.toPrefixArithmetic where
  base7 : base 7 = D.y
  large7 : 2 * f (Sum.inl 7) = -D.F * D.u
  large8 : 2 * f (Sum.inl 8) = D.N - D.a0
  last_negative : f (Sum.inl 9) < 0
  next7 : D.a0 = D.N - 2 * (2 : ℤ) ^ len 7 * D.y
  total : ∑ o : Occ len, f o = 0

private theorem selection_of_coeff {D : Arithmetic} (R : RowData D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (M : Finset (Occ R.len)) (hM : M ⊆ bank R.toRowData Sn Sw) (f : ℤ)
    (hf : 0 ≤ f) (hfu : f < (2 : ℤ) ^ R.len 6)
    (hgate : (D.u - D.z) / 2 ≤ -(∑ o ∈ M, R.f o) - f * D.u ∧
      -(∑ o ∈ M, R.f o) - f * D.u ≤ D.u - (D.z + 1) / 2) :
    Nonempty (TSelection R.toRowData Sn Sw) := by
  obtain ⟨S, hS⟩ := mask_exists (R.len 6) f hf hfu
  exact ⟨⟨M, hM, S, by simpa only [hS] using hgate⟩⟩

private theorem select_T {D : Arithmetic} (R : RowData D) (A : ℤ)
    (hA : 1 ≤ A) (hAP : A ≤ D.H / 4)
    (hprev : 2 * (D.w - D.n) * (A - 1) < D.n + D.Δ + 1)
    (hnext : D.n + D.Δ + 1 ≤ 2 * (D.w - D.n) * A)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (hSn : weight Sn = A) (hSw : weight Sw = D.H / 4 - A) :
    Nonempty (TSelection R.toRowData Sn Sw) := by
  classical
  obtain ⟨hn0, hz0, hb0, hw0, hv0, hu0, hP, hq, hHw, hwb, hzmax⟩ := arithmetic_geometry D.toPrefixArithmetic
  obtain ⟨hN, hW, hZ, hB, hV⟩ := bank_parts R.toRowData Sn Sw
  have hmissing : weight Swᶜ = A - 1 := by rw [weight_compl, (show (2 : ℤ) ^ R.len 4 = D.H / 4 from R.pow4), hSw]; ring
  have hrow0 (S : Finset (Fin (R.len 0))) : rowMask R.len 0 S ⊆ bank R.toRowData Sn Sw :=
    (rowMask_mono R.len 0 (Finset.subset_univ S)).trans hZ
  have hrow1 (S : Finset (Fin (R.len 1))) : rowMask R.len 1 S ⊆ bank R.toRowData Sn Sw :=
    (rowMask_mono R.len 1 (Finset.subset_univ S)).trans hB
  have hrow4 (S : Finset (Fin (R.len 4))) (hS : S ⊆ Sw) : rowMask R.len 4 S ⊆ bank R.toRowData Sn Sw :=
    (rowMask_mono R.len 4 hS).trans hW
  rcases D.branch with ⟨hF, hF4⟩ | hF
  · have hpow6 : (2 : ℤ) ^ R.len 6 = D.H / 4 := by
      have hh := (show 2 * (2 : ℤ) ^ R.len 6 = D.F from R.pow6)
      have hH := D.H_four
      omega
    have halfbounds := half_source_bounds D hF
    obtain ⟨hell0, hW0, hell, hhi, hWeq, hwidth⟩ := gate_limits D.toPrefixArithmetic
    by_cases he : D.e = 1
    · obtain ⟨hBsource, hKsource, hB2n⟩ := half_one_geometry D hF he
      obtain ⟨hAsmall, hAr, hD0⟩ := half_one_canonical_bounds D hF he A hA hprev hnext
      have hBpos : 0 < D.w - D.b := by omega
      have hAB : A * (D.w - D.b) ≤ (D.u - 1) / 2 := by
        have hm := mul_nonneg (show 0 ≤ D.H / 4 - A by omega) (le_of_lt hBpos)
        have hH4B := congrArg (fun H : ℤ => H * (D.w - D.b)) D.H_four
        have hnU : D.n < D.u := by have hnz := D.nzb.1; have hzu := D.u_above; omega
        nlinarith only [hm, hBsource, hH4B, hnU, hWeq]
      by_cases hspan : (D.u - D.z) / 2 ≤ (D.H / 4 - A) * (D.w - D.b)
      · obtain ⟨J, hJS, hlo, hhi'⟩ := supported_multiple_crossing (R.len 4) Sw
          ((D.u - D.z) / 2) (D.u - (D.z + 1) / 2) ((D.u - 1) / 2) (D.w - D.b) A
          hell0 hBpos hA hwidth (by rw [← weight_nat, hSw]; exact hspan)
          (by rw [← weight_nat, hmissing]) hAB
        have hc0 := weight_nonneg J
        have hcmax : weight J < (2 : ℤ) ^ R.len 1 := by
          have hm := weight_mono hJS
          rw [(show (2 : ℤ) ^ R.len 1 = D.q from R.pow1)]
          omega
        obtain ⟨Bmask, hBM⟩ := mask_exists (R.len 1) (weight J) hc0 hcmax
        apply selection_of_coeff R Sn Sw (rowMask R.len 4 J ∪ rowMask R.len 1 Bmask)
          (Finset.union_subset (hrow4 J hJS) (hrow1 Bmask)) 0 (le_refl _)
          (by positivity)
        rw [two_rows_sum R.toRowData 4 1 J Bmask (by decide), (show R.base 4 = -D.w from R.base4), (show R.base 1 = D.b from R.base1), hBM]
        rw [← weight_nat] at hlo hhi'
        constructor <;> nlinarith only [hlo, hhi']
      · have hend := half_one_borrow_endpoint D hF he A hA hAP hprev hnext (lt_of_not_ge hspan)
        let fm := min A (D.H / 4 - 1)
        have hfm : 0 ≤ fm := by dsimp only [fm]; omega
        have hfmcast : ((fm.toNat : ℕ) : ℤ) = fm := Int.toNat_of_nonneg hfm
        have hlo0 : (D.u - D.z) / 2 ≤ D.z - A * D.H * D.Δ := by
          have hu2z := halfbounds.1
          omega
        obtain ⟨f, hfm', hlo, hhi'⟩ := one_step_crossing (D.z - A * D.H * D.Δ)
          ((D.u - D.z) / 2) (D.u - (D.z + 1) / 2) ((D.u - 1) / 2) (D.u - D.b)
          fm.toNat hlo0 hwidth ⟨by omega, by omega⟩ (by simpa only [hfmcast] using hend)
        have hf : (f : ℤ) ≤ fm := by
          have hh : (f : ℤ) ≤ (fm.toNat : ℤ) := by exact_mod_cast hfm'
          omega
        have hfA : (f : ℤ) ≤ A := by dsimp only [fm] at hf; omega
        have hfP : (f : ℤ) ≤ D.H / 4 - 1 := by dsimp only [fm] at hf; omega
        obtain ⟨Zmask, hZM⟩ := mask_exists (R.len 0) 1 (by omega) (by rw [(show (2 : ℤ) ^ R.len 0 = D.q from R.pow0)]; omega)
        obtain ⟨Bmask, hBM⟩ := mask_exists (R.len 1) (A - (f : ℤ)) (by omega)
          (by rw [(show (2 : ℤ) ^ R.len 1 = D.q from R.pow1)]; omega)
        apply selection_of_coeff R Sn Sw
          (rowMask R.len 2 Sn ∪ rowMask R.len 0 Zmask ∪ rowMask R.len 1 Bmask)
          (Finset.union_subset (Finset.union_subset hN (hrow0 Zmask)) (hrow1 Bmask))
          (f : ℤ) (by omega) (by rw [hpow6]; omega)
        rw [three_rows_sum R.toRowData 2 0 1 Sn Zmask Bmask (by decide) (by decide) (by decide),
          hSn, hZM, hBM, (show R.base 2 = -D.n from R.base2), (show R.base 0 = -D.z from R.base0), (show R.base 1 = D.b from R.base1)]
        have hbA := congrArg (fun b : ℤ => A * b) D.b_n
        constructor <;> nlinarith only [hlo, hhi', hbA]
    · have he2 : 2 ≤ D.e := by have hh := D.e_one; omega
      obtain ⟨hA1, c, f, hcP, hfc, hcf, hlo, hhi'⟩ := half_many_T_coefficients D hF he2 A hA hprev
      have hzero : weight Swᶜ = 0 := by omega
      obtain ⟨Wmask, hWMsub, hWM⟩ := supported_mask_exists Sw hzero (c : ℤ) (by omega)
        (by rw [hSw]; omega)
      obtain ⟨Bmask, hBM⟩ := mask_exists (R.len 1) (2 * (c : ℤ) - (f : ℤ)) (by omega)
        (by rw [(show (2 : ℤ) ^ R.len 1 = D.q from R.pow1)]; omega)
      apply selection_of_coeff R Sn Sw
        (rowMask R.len 2 Sn ∪ rowMask R.len 4 Wmask ∪ rowMask R.len 1 Bmask)
        (Finset.union_subset (Finset.union_subset hN (hrow4 Wmask hWMsub)) (hrow1 Bmask))
        (f : ℤ) (by omega) (by rw [hpow6]; omega)
      rw [three_rows_sum R.toRowData 2 4 1 Sn Wmask Bmask (by decide) (by decide) (by decide),
        hSn, hWM, hBM, (show R.base 2 = -D.n from R.base2), (show R.base 4 = -D.w from R.base4), (show R.base 1 = D.b from R.base1), hA1]
      constructor <;> nlinarith only [hlo, hhi']
  · obtain ⟨hu2z, c, hcmax, hlo, hhi⟩ := lower_T_coefficient D hF
    obtain ⟨Zmask, hZM⟩ := mask_exists (R.len 0) (c : ℤ) (by omega)
      (by rw [(show (2 : ℤ) ^ R.len 0 = D.q from R.pow0)]; omega)
    apply selection_of_coeff R Sn Sw (rowMask R.len 0 Zmask) (hrow0 Zmask) 0 (le_refl _)
      (by positivity)
    rw [row_sum, hZM, (show R.base 0 = -D.z from R.base0)]
    constructor <;> nlinarith only [hlo, hhi]

end D5.S3.Combinatorics.Circle.M5FullWordConsumer
