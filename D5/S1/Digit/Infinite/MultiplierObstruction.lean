/- GID: D5/S1/Digit/Infinite/MultiplierObstruction
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/MultiplierObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Multiplication by every natural number at least two has no continuous extension to legal infinite digit streams. -/

import D5.S1.Digit.Infinite.SignedSeriesFibres
import D5.S1.Digit.GoldenZeckendorfLanguage
import D5.S1.Digit.Raw
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.MultiplierObstruction

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S1.Digit.Infinite.SignedSeriesFibres
open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S1.Digit
open scoped Topology
open Filter

/-- The Zeckendorf digit row of a natural number, indexed by Fibonacci weights starting at one. -/
def zRow (n : ℕ) : LegalDigits :=
  ⟨fun j => decide (zeckendorfBit n j = 1), by
    intro j h
    have gap := D5.S1.Digit.GoldenZeckendorfLanguage.canonical_indices_not_adjacent
      (Nat.zeckendorf n) (Nat.isZeckendorfRep_zeckendorf n) (j + 2)
    have h0 : zeckendorfBit n j = 1 := of_decide_eq_true h.1
    have h1 : zeckendorfBit n (j + 1) = 1 := of_decide_eq_true h.2
    apply gap
    constructor
    · by_contra hj
      simp [zeckendorfBit, D5.S0.Conventions.wdigits, hj] at h0
    · by_contra hj
      simp [zeckendorfBit, D5.S0.Conventions.wdigits, Nat.add_assoc] at h1
      exact hj h1⟩

/-- The signed value of a legal digit stream, taken modulo one. -/
noncomputable def phase (x : LegalDigits) : AddCircle (1 : ℝ) := signedValue x

set_option maxHeartbeats 800000 in
/-- No continuous self-map of the legal streams multiplies every natural digit row by m ≥ 2. -/
theorem multiplier_obstruction (m : ℕ) (hm : 2 ≤ m) :
    ¬ ∃ M : LegalDigits → LegalDigits, Continuous M ∧
      ∀ n, M (zRow n) = zRow (m * n) := by
  classical
  let gamma (n : ℕ) : AddCircle (1 : ℝ) := (n : ℝ) * Real.goldenRatio
  have coefficient (j : ℕ) :
      (-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2) =
      Real.goldenRatio * (Nat.fib (j + 2) : ℝ) - (Nat.fib (j + 3) : ℝ) := by
    have e := Real.fib_succ_sub_goldenRatio_mul_fib (j + 2)
    have hc : Real.goldenConj = -alpha := by
      dsimp [alpha]
      have hi := Real.inv_goldenRatio
      linarith [hi]
    have hsign : (-alpha) ^ (j + 2) =
        -((-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2)) := by
      rw [neg_eq_neg_one_mul, mul_pow]
      simp only [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      ring
    rw [hc, hsign] at e
    have hi : j + 2 + 1 = j + 3 := by omega
    rw [hi] at e
    linarith

  have value_row (n : ℕ) : ∃ k : ℤ,
      signedValue (zRow n) = (n : ℝ) * Real.goldenRatio - k := by
    classical
    let R := rawOfZeckendorf (Nat.zeckendorf n)
    have hc := canonicalRaw_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)
    have hm (i : ℕ) : i ∈ R.support ↔ i + 2 ∈ Nat.zeckendorf n := by
      dsimp [R]
      conv_rhs => rw [← rawToZeckendorf_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)]
      simp [rawToZeckendorf, Finsupp.mem_toMultiset]
    have bit (i : ℕ) : (if (zRow n).val i then (1 : ℝ) else 0) = R i := by
      have hb := hc.1 i
      change R i ≤ 1 at hb
      have hm' := hm i
      rw [Finsupp.mem_support_iff] at hm'
      by_cases hi : i + 2 ∈ Nat.zeckendorf n
      · have hr : R i = 1 := by have := hm'.mpr hi; omega
        simp [zRow, zeckendorfBit, D5.S0.Conventions.wdigits, hi, hr]
      · have hr : R i = 0 := by simpa using mt hm'.mp hi
        simp [zRow, zeckendorfBit, D5.S0.Conventions.wdigits, hi, hr]
    have hn : rawValue R = n := by
      rw [rawValue_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n), Nat.sum_zeckendorf_fib]
    refine ⟨(∑ j ∈ R.support, (R j : ℤ) * (Nat.fib (j + 3) : ℤ)), ?_⟩
    rw [signedValue]
    simp_rw [bit]
    rw [tsum_eq_sum (s := R.support) (fun j hj => by simp [Finsupp.notMem_support_iff.mp hj])]
    simp_rw [coefficient]
    rw [← hn]
    simp only [rawValue, Finsupp.sum, D5.S0.Conventions.wValue, Int.cast_natCast,
      Nat.cast_sum, Nat.cast_mul, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring

  have phase_row (n : ℕ) : phase (zRow n) = gamma n := by
    obtain ⟨k, hk⟩ := value_row n
    have zeroK : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k, by simp⟩
    simp only [phase, gamma, hk, AddCircle.coe_sub, zeroK, sub_zero]

  have value_continuous : Continuous signedValue := by
    have hp : 0 < alpha := inv_pos.mpr Real.goldenRatio_pos
    have hlt : alpha < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
    apply continuous_tsum
    · intro j
      apply continuous_const.mul
      exact (continuous_of_discreteTopology : Continuous (fun b : Bool => if b then (1 : ℝ) else 0)).comp
        ((continuous_apply j).comp continuous_subtype_val)
    · exact (summable_geometric_of_lt_one hp.le hlt).mul_right (alpha ^ 2)
    · intro j x
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow]
      simp only [abs_neg, abs_one, one_pow, one_mul, abs_of_pos hp]
      cases x.val j <;> simp [pow_add, mul_nonneg (pow_nonneg hp.le j) (sq_nonneg alpha)]

  have h_continuous : Continuous phase :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp value_continuous

  have seam_negative_phase (w : List Block) :
      ∃ k : ℕ, 2 ≤ k ∧ ((seam w : ℝ) : AddCircle (1 : ℝ)) =
        (((-(k : ℝ) * Real.goldenRatio) : ℝ) : AddCircle (1 : ℝ)) := by
    classical
    let N : ℕ := ∑ j ∈ Finset.range (len w),
      if (digitsOf w)[j]?.getD false then Nat.fib (j + 2) else 0
    let J : ℕ := ∑ j ∈ Finset.range (len w),
      if (digitsOf w)[j]?.getD false then Nat.fib (j + 3) else 0
    have hsum : (∑ j ∈ Finset.range (len w), Nat.fib (j + 2)) + 2 =
        Nat.fib (len w + 3) := by
      have ht := Nat.fib_succ_eq_succ_sum (len w + 2)
      have hs : (∑ j ∈ Finset.range (len w + 2), Nat.fib j) =
          1 + ∑ j ∈ Finset.range (len w), Nat.fib (j + 2) := by
        simpa [Finset.sum_range_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Finset.sum_range_add Nat.fib 2 (len w))
      rw [hs] at ht
      calc
        (∑ j ∈ Finset.range (len w), Nat.fib (j + 2)) + 2 =
            (1 + ∑ j ∈ Finset.range (len w), Nat.fib (j + 2)) + 1 := by omega
        _ = Nat.fib (len w + 2 + 1) := ht.symm
        _ = Nat.fib (len w + 3) := rfl
    have hN : N ≤ ∑ j ∈ Finset.range (len w), Nat.fib (j + 2) := by
      apply Finset.sum_le_sum
      intro j _
      split <;> omega
    have hNk : N + 2 ≤ Nat.fib (len w + 3) := by omega
    let k := Nat.fib (len w + 3) - N
    have hk : 2 ≤ k := by dsimp [k]; omega
    have hreal : (Nat.fib (len w + 3) : ℝ) = (N : ℝ) + (k : ℝ) := by
      exact_mod_cast (show Nat.fib (len w + 3) = N + k by dsimp [k]; omega)
    have hS : S w = Real.goldenRatio * (N : ℝ) - (J : ℝ) := by
      dsimp [S, N, J]
      simp_rw [coefficient]
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      cases h : (digitsOf w)[j]?.getD false <;> simp [h]
    have hq : r ^ len w * q =
        -(Real.goldenRatio * (Nat.fib (len w + 3) : ℝ) - (Nat.fib (len w + 4) : ℝ)) := by
      have h := coefficient (len w + 1)
      have he : r ^ len w * q =
          -((-1 : ℝ) ^ (len w + 1 + 1) * alpha ^ (len w + 1 + 2)) := by
        dsimp [r, q]
        rw [neg_eq_neg_one_mul alpha, mul_pow]
        simp only [pow_add, pow_one]
        ring
      simpa only [Nat.add_assoc] using he.trans (congrArg Neg.neg h)
    have hs : seam w = -(k : ℝ) * Real.goldenRatio +
        ((Nat.fib (len w + 4) : ℤ) - (J : ℤ) : ℤ) := by
      dsimp [seam, f]
      rw [hS, hq, hreal]
      push_cast
      ring
    refine ⟨k, hk, ?_⟩
    have hz : ((((Nat.fib (len w + 4) : ℤ) - (J : ℤ) : ℤ) : ℝ) :
        AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
        ⟨(Nat.fib (len w + 4) : ℤ) - (J : ℤ), by simp⟩
    rw [hs, AddCircle.coe_add, hz, add_zero]

  have divided_phase_avoids (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) :
      (((-Real.goldenRatio / (m : ℝ)) : ℝ) : AddCircle (1 : ℝ)) ≠
        (((-(k : ℝ) * Real.goldenRatio) : ℝ) : AddCircle (1 : ℝ)) := by
    intro he
    have hzero : (((-Real.goldenRatio / (m : ℝ) + (k : ℝ) * Real.goldenRatio) : ℝ) :
        AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_add, he]
      simp [neg_mul, AddCircle.coe_neg]
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
    simp only [zsmul_eq_mul, mul_one] at hz
    have hmk : 2 ≤ m * k := le_trans hm (Nat.le_mul_of_pos_right m hk)
    have hi := Real.goldenRatio_irrational.natCast_mul (show m * k - 1 ≠ 0 by omega)
    apply hi.ne_int (z * (m : ℤ))
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hh := congrArg (fun t : ℝ => t * (m : ℝ)) hz
    rw [add_mul, div_mul_cancel₀ _ hm0] at hh
    rw [Nat.cast_sub (by omega : 1 ≤ m * k)]
    push_cast
    nlinarith

  have phase_unique_of_avoids (c : AddCircle (1 : ℝ))
      (havoid : ∀ k : ℕ, 1 ≤ k → c ≠
        (((-(k : ℝ) * Real.goldenRatio) : ℝ) : AddCircle (1 : ℝ))) :
      ∃! x : LegalDigits, phase x = c := by
    have haid : a = 1 - Real.goldenRatio := by
      dsimp [a, alpha]
      rw [Real.inv_goldenRatio]
      linarith [Real.goldenRatio_add_goldenConj]
    have hba : b = a + 1 := by
      dsimp [b, a, alpha]
      rw [Real.inv_goldenRatio]
      nlinarith [Real.goldenConj_sq]
    have hone : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨1, by simp⟩
    have hap : (a : AddCircle (1 : ℝ)) = ((-Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) := by
      rw [haid, AddCircle.coe_sub, hone, zero_sub, AddCircle.coe_neg]
    have hbp : (b : AddCircle (1 : ℝ)) = ((-Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) := by
      rw [hba, AddCircle.coe_add, hone, add_zero, hap]
    have he : c ≠ ((-Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) := by
      simpa using havoid 1 (by omega)
    let t := AddCircle.equivIco (1 : ℝ) a c
    have htc : ((t.val : ℝ) : AddCircle (1 : ℝ)) = c := AddCircle.coe_equivIco
    have hti : t.val ∈ Set.Ioo a b := by
      refine ⟨lt_of_le_of_ne t.property.1 ?_, ?_⟩
      · intro ht
        exact he (htc.symm.trans (ht ▸ hap))
      · simpa [hba] using t.property.2
    have hns : t.val ∉ Set.range seam := by
      rintro ⟨w, hw⟩
      obtain ⟨k, hk, hphase⟩ := seam_negative_phase w
      exact havoid k (by omega) (htc.symm.trans (hw ▸ hphase))
    obtain ⟨x, hx, hunique⟩ := signed_series_fibres.2.2 t.val
      ⟨hti.1.le, hti.2.le⟩ hns
    refine ⟨x, ?_, ?_⟩
    · exact (congrArg (fun s : ℝ => (s : AddCircle (1 : ℝ))) hx).trans htc
    · intro y hy
      apply hunique y
      have hbounds : signedValue y ∈ Set.Icc a b := by
        rw [← signed_series_range.1]
        exact Set.mem_range_self y
      have hlt : signedValue y < b := by
        refine lt_of_le_of_ne hbounds.2 ?_
        intro hb
        exact he (hy.symm.trans ((congrArg (fun s : ℝ => (s : AddCircle (1 : ℝ))) hb).trans hbp))
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (show signedValue y ∈ Set.Ico a (a + 1) from ⟨hbounds.1, hba ▸ hlt⟩)
        t.property).mp (hy.trans htc.symm)

  have divided_phase_unique (m : ℕ) (hm : 2 ≤ m) :
      ∃! x : LegalDigits, phase x = (((-Real.goldenRatio / (m : ℝ)) : ℝ) : AddCircle (1 : ℝ)) :=
    phase_unique_of_avoids _ (fun k hk => divided_phase_avoids m k hm hk)

  have forward_visits (U : Set (AddCircle (1 : ℝ))) (hU : IsOpen U)
      (hne : U.Nonempty) (N : ℕ) :
      ∃ n : ℕ, N < n ∧ (((n : ℝ) * Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) ∈ U := by
    let step : AddCircle (1 : ℝ) := Real.goldenRatio
    have hz : DenseRange (fun z : ℤ => z • step) := by
      dsimp [step]
      rw [AddCircle.denseRange_zsmul_coe_iff]
      simpa using Real.goldenRatio_irrational
    have hn : DenseRange (fun n : ℕ => n • step) := denseRange_zsmul_iff_nsmul.mp hz
    let shift : AddCircle (1 : ℝ) → AddCircle (1 : ℝ) := fun x => (N + 1) • step + x
    have hs : Function.Surjective shift := fun y => ⟨y - (N + 1) • step, by simp [shift]⟩
    have hc : Continuous shift := by
      dsimp [shift]
      fun_prop
    have hd : DenseRange (fun n : ℕ => shift (n • step)) := hs.denseRange.comp hn hc
    obtain ⟨n, h⟩ := hd.exists_mem_open hU hne
    refine ⟨N + 1 + n, by omega, ?_⟩
    change (N + 1) • step + n • step ∈ U at h
    rw [← add_nsmul] at h
    have heq (j : ℕ) : j • step =
        (((j : ℝ) * Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) := by
      simpa only [step, nsmul_eq_mul] using
        (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := j) (x := Real.goldenRatio)).symm
    rwa [heq] at h

  have legal_compact : CompactSpace LegalDigits := by
    have hc : IsClosed {x : ℕ → Bool | ∀ j, ¬ (x j = true ∧ x (j + 1) = true)} := by
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro j
      have ho0 : IsOpen {x : ℕ → Bool | x j = true} :=
        (isOpen_discrete ({true} : Set Bool)).preimage
          (show Continuous (fun x : ℕ → Bool => x j) from continuous_apply j)
      have ho1 : IsOpen {x : ℕ → Bool | x (j + 1) = true} :=
        (isOpen_discrete ({true} : Set Bool)).preimage
          (show Continuous (fun x : ℕ → Bool => x (j + 1)) from continuous_apply (j + 1))
      have ho := ho0.inter ho1
      exact ho.isClosed_compl
    exact isCompact_iff_compactSpace.mp hc.isCompact

  have lift_convergence {Y : Type} [TopologicalSpace Y] [T2Space Y]
      (F : LegalDigits → Y) (hF : Continuous F) (x : LegalDigits)
      (hunique : ∀ y, F y = F x → y = x) (s : ℕ → LegalDigits)
      (hs : Tendsto (F ∘ s) atTop (𝓝 (F x))) : Tendsto s atTop (𝓝 x) := by
    letI : CompactSpace LegalDigits := legal_compact
    apply tendsto_nhds_of_unique_mapClusterPt
    intro y hy
    apply hunique y
    have hmap : ClusterPt (F y) (𝓝 (F x)) :=
      hy.map hF.continuousAt (by simpa only [Tendsto, Filter.map_map] using hs)
    exact eq_of_nhds_neBot hmap

  have obstruction_of_two_sided_limits (m : ℕ) (x : LegalDigits) (splus sminus : ℕ → ℕ)
      (hplus : Tendsto (zRow ∘ splus) atTop (𝓝 x))
      (hminus : Tendsto (zRow ∘ sminus) atTop (𝓝 x))
      (hvplus : Tendsto (fun j => signedValue (zRow (m * splus j))) atTop (𝓝 a))
      (hvminus : Tendsto (fun j => signedValue (zRow (m * sminus j))) atTop (𝓝 b)) :
      ¬ ∃ M : LegalDigits → LegalDigits, Continuous M ∧
        ∀ n, M (zRow n) = zRow (m * n) := by
    rintro ⟨M, hM, hrow⟩
    have hcont := value_continuous.comp hM
    have hp : Tendsto (fun j => signedValue (zRow (m * splus j))) atTop
        (𝓝 (signedValue (M x))) := by
      simpa only [Function.comp_def, hrow] using hcont.continuousAt.tendsto.comp hplus
    have hn : Tendsto (fun j => signedValue (zRow (m * sminus j))) atTop
        (𝓝 (signedValue (M x))) := by
      simpa only [Function.comp_def, hrow] using hcont.continuousAt.tendsto.comp hminus
    have he : a = b := (tendsto_nhds_unique hvplus hp).trans (tendsto_nhds_unique hvminus hn).symm
    have hba : b = a + 1 := by
      dsimp [b, a, alpha]
      rw [Real.inv_goldenRatio]
      nlinarith [Real.goldenConj_sq]
    linarith

  have haid : a = 1 - Real.goldenRatio := by
    dsimp [a, alpha]
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hba : b = a + 1 := by
    dsimp [b, a, alpha]
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  have hone : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨1, by simp⟩
  have hap : (a : AddCircle (1 : ℝ)) = ((-Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) := by
    rw [haid, AddCircle.coe_sub, hone, zero_sub, AddCircle.coe_neg]
  have hbp : (b : AddCircle (1 : ℝ)) = ((-Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) := by
    rw [hba, AddCircle.coe_add, hone, add_zero, hap]
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  let c₀ : ℝ := -Real.goldenRatio / (m : ℝ)
  obtain ⟨x, hx, huniq⟩ := divided_phase_unique m hm
  change phase x = (c₀ : AddCircle (1 : ℝ)) at hx
  have visits (l u : ℝ) (hlu : l < u) (N : ℕ) :
      ∃ p : ℕ × ℝ, N < p.1 ∧ p.2 ∈ Set.Ioo l u ∧
        gamma p.1 = ((c₀ + p.2 : ℝ) : AddCircle (1 : ℝ)) := by
    let U : Set (AddCircle (1 : ℝ)) :=
      (fun r : ℝ => (r : AddCircle (1 : ℝ))) '' Set.Ioo (c₀ + l) (c₀ + u)
    have hU : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
    have hne : U.Nonempty := (Set.nonempty_Ioo.mpr (by linarith)).image _
    obtain ⟨n, hn, r, hr, he⟩ := forward_visits U hU hne N
    refine ⟨(n, r - c₀), hn, ⟨by dsimp; linarith [hr.1], by dsimp; linarith [hr.2]⟩, ?_⟩
    simpa [gamma] using he.symm
  have sequences (l u : ℕ → ℝ) (hlu : ∀ j, l j < u j) :
      ∃ s : ℕ → ℕ, ∃ t : ℕ → ℝ, StrictMono s ∧
        ∀ j, t j ∈ Set.Ioo (l j) (u j) ∧
          gamma (s j) = ((c₀ + t j : ℝ) : AddCircle (1 : ℝ)) := by
    let pick (j N : ℕ) : ℕ × ℝ := Classical.choose (visits (l j) (u j) (hlu j) N)
    have hpick (j N : ℕ) := Classical.choose_spec (visits (l j) (u j) (hlu j) N)
    let p : ℕ → ℕ × ℝ := Nat.rec (pick 0 0) (fun j prev => pick (j + 1) prev.1)
    have hdata (j : ℕ) : (p j).2 ∈ Set.Ioo (l j) (u j) ∧
        gamma (p j).1 = ((c₀ + (p j).2 : ℝ) : AddCircle (1 : ℝ)) := by
      cases j with
      | zero => exact (hpick 0 0).2
      | succ j => exact (hpick (j + 1) (p j).1).2
    refine ⟨fun j => (p j).1, fun j => (p j).2, ?_, hdata⟩
    apply strictMono_nat_of_lt_succ
    intro j
    exact (hpick (j + 1) (p j).1).1
  let δ (j : ℕ) : ℝ := 1 / (8 * (m : ℝ) * ((j : ℝ) + 1))
  have hδpos (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδbound (j : ℕ) : (m : ℝ) * δ j ≤ 1 / 8 := by
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    dsimp [δ]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    have hd : 0 < 8 * (m : ℝ) * ((j : ℝ) + 1) := by positivity
    field_simp
    nlinarith
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (1 / (8 * (m : ℝ)))
    simpa only [mul_zero, div_mul_div_comm, one_mul] using h
  obtain ⟨sp, tp, hsp, hp⟩ := sequences (fun j => δ j / 2) δ (fun j => by
    have := hδpos j
    linarith)
  obtain ⟨sn, tn, hsn, hn⟩ := sequences (fun j => -δ j) (fun j => -δ j / 2) (fun j => by
    have := hδpos j
    linarith)
  have htp (j : ℕ) : 0 < tp j ∧ tp j < δ j := by
    exact ⟨lt_trans (half_pos (hδpos j)) (hp j).1.1, (hp j).1.2⟩
  have htn (j : ℕ) : -δ j < tn j ∧ tn j < 0 := by
    exact ⟨(hn j).1.1, lt_trans (hn j).1.2 (by have := hδpos j; linarith)⟩
  have htplim : Tendsto tp atTop (𝓝 0) :=
    squeeze_zero (fun j => (htp j).1.le) (fun j => (htp j).2.le) hδlim
  have htnlim : Tendsto tn atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hδlim.neg)
      tendsto_const_nhds (fun j => (htn j).1.le) (fun j => (htn j).2.le)
  have lift (s : ℕ → ℕ) (t : ℕ → ℝ)
      (ht : Tendsto t atTop (𝓝 0))
      (he : ∀ j, gamma (s j) = ((c₀ + t j : ℝ) : AddCircle (1 : ℝ))) :
      Tendsto (zRow ∘ s) atTop (𝓝 x) := by
    apply lift_convergence phase h_continuous x
      (fun y hy => huniq y (hy.trans hx)) (zRow ∘ s)
    have hc : Continuous (fun r : ℝ => (r : AddCircle (1 : ℝ))) :=
      AddCircle.continuous_mk' (1 : ℝ)
    have hl := hc.continuousAt.tendsto.comp ((tendsto_const_nhds (x := c₀)).add ht)
    simpa only [Function.comp_def, phase_row, he, add_zero, hx] using hl
  have hplus := lift sp tp htplim (fun j => (hp j).2)
  have hminus := lift sn tn htnlim (fun j => (hn j).2)
  have multiplied (n : ℕ) (t : ℝ)
      (he : gamma n = ((c₀ + t : ℝ) : AddCircle (1 : ℝ))) :
      phase (zRow (m * n)) = ((-Real.goldenRatio + (m : ℝ) * t : ℝ) :
        AddCircle (1 : ℝ)) := by
    rw [phase_row]
    calc
      gamma (m * n) = m • gamma n := by
        simp only [gamma, ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
      _ = m • ((c₀ + t : ℝ) : AddCircle (1 : ℝ)) := congrArg (fun y => m • y) he
      _ = _ := by
        rw [← AddCircle.coe_nsmul]
        congr 1
        simp only [nsmul_eq_mul]
        dsimp [c₀]
        field_simp
  have representative (y : LegalDigits) (r : ℝ) (hr : r ∈ Set.Ioo a b)
      (he : phase y = (r : AddCircle (1 : ℝ))) : signedValue y = r := by
    have hy : signedValue y ∈ Set.Icc a b := by
      rw [← signed_series_range.1]
      exact Set.mem_range_self y
    have hbne : signedValue y ≠ b := by
      intro hb
      have heq : (b : AddCircle (1 : ℝ)) = (r : AddCircle (1 : ℝ)) := by
        simpa only [phase, hb] using he
      have hbr : b = r := (AddCircle.coe_eq_coe_iff_of_mem_Ioc
        (show b ∈ Set.Ioc a (a + 1) from ⟨by linarith, by linarith⟩)
        (show r ∈ Set.Ioc a (a + 1) from ⟨hr.1, by linarith [hr.2]⟩)).mp heq
      linarith [hr.2]
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show signedValue y ∈ Set.Ico a (a + 1) from
        ⟨hy.1, by have := lt_of_le_of_ne hy.2 hbne; linarith⟩)
      (show r ∈ Set.Ico a (a + 1) from ⟨hr.1.le, by linarith [hr.2]⟩)).mp he
  have vp (j : ℕ) : signedValue (zRow (m * sp j)) = a + (m : ℝ) * tp j := by
    have htpos := mul_pos hmpos (htp j).1
    have htlt := (mul_lt_mul_of_pos_left (htp j).2 hmpos).trans_le (hδbound j)
    apply representative _ _ ⟨by linarith, by linarith⟩
    rw [multiplied (sp j) (tp j) (hp j).2, AddCircle.coe_add, AddCircle.coe_add, hap]
  have vn (j : ℕ) : signedValue (zRow (m * sn j)) = b + (m : ℝ) * tn j := by
    have htneg := mul_neg_of_pos_of_neg hmpos (htn j).2
    have htlt := mul_lt_mul_of_pos_left (htn j).1 hmpos
    have hbound := hδbound j
    rw [mul_neg] at htlt
    apply representative _ _ ⟨by linarith, by linarith⟩
    rw [multiplied (sn j) (tn j) (hn j).2, AddCircle.coe_add, AddCircle.coe_add, hbp]
  exact obstruction_of_two_sided_limits m x sp sn hplus hminus
    (by simpa only [vp, mul_zero, add_zero] using
          (tendsto_const_nhds (x := a)).add (htplim.const_mul (m : ℝ)))
    (by simpa only [vn, mul_zero, add_zero] using
          (tendsto_const_nhds (x := b)).add (htnlim.const_mul (m : ℝ)))

end D5.S1.Digit.Infinite.MultiplierObstruction
