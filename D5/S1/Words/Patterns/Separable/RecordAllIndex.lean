/- GID: D5/S1/Words/Patterns/Separable/RecordAllIndex
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/RecordAllIndex
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown]
   utility: none
   digest: Actual-carrier CKZ weighted quadratic, exact binomial coefficients, arbitrary-index decline and peak-three conclusion. -/

import D5.S1.Words.Patterns.Separable.RecordNewtonPositivity
import D5.S1.Words.Patterns.Separable.RecordFirstDecline
import Mathlib.RingTheory.PowerSeries.WellKnown

namespace D5.S1.Words.Patterns.Separable.RecordAllIndex
open D5.S1.Words.Patterns.Separable.RecordPeak
open D5.S1.Words.Patterns.Separable.RecordTransport
open D5.S1.Words.Patterns.Separable.RecordNewtonPositivity
open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open D5.S1.Words.Patterns.Separable.ActualCardinality
open D5.S1.Words.Patterns.Separable.EndpointHistoryKernel
open D5.S1.Words.Patterns.Separable.ProperCut
open scoped BigOperators
private noncomputable def positive (f : ℕ → ℕ → ℕ) : PowerSeries (PowerSeries ℚ) :=
  PowerSeries.mk fun k => PowerSeries.mk fun n => if n = 0 then 0 else (f n k : ℚ)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem actual_weighted_quadratic :
    D5.S1.Words.Patterns.Separable.RecordPeak.J =
      D5.S1.Words.Patterns.Separable.RecordPeak.z +
        D5.S1.Words.Patterns.Separable.RecordPeak.z *
          (1 + PowerSeries.C D5.S1.Words.Patterns.Separable.RecordPeak.q) *
          D5.S1.Words.Patterns.Separable.RecordPeak.J +
        PowerSeries.C D5.S1.Words.Patterns.Separable.RecordPeak.q *
          (1 + PowerSeries.C D5.S1.Words.Patterns.Separable.RecordPeak.q) *
          D5.S1.Words.Patterns.Separable.RecordPeak.J ^ 2 := by
  classical
  let U := positive allCount
  let J := positive (signedCount false)
  let R := positive (properCount false)

  have blockRecords {m k : ℕ} (α : Equiv.Perm (Fin m))
      (β : Equiv.Perm (Fin k)) :
      rmax (blockSum false α β) = (if k = 0 then rmax α else rmax β) ∧
      rmax (blockSum true α β) = rmax α + rmax β := by
    classical
    have leftval (sign : Bool) (i : Fin m) :
        (blockSum sign α β (Fin.castAdd k i)).val =
          (if sign then k else 0) + (α i).val := by
      cases sign <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm, Nat.add_comm]
    have rightval (sign : Bool) (i : Fin k) :
        (blockSum sign α β (Fin.natAdd m i)).val =
          (if sign then 0 else m) + (β i).val := by
      cases sign <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm]
    have suffix (sign : Bool) (i : Fin k) :
        IsRightMaximum (blockSum sign α β) (Fin.natAdd m i) ↔
          IsRightMaximum β i := by
      constructor
      · intro h j hj
        have comparison := h (Fin.natAdd m j) (by simpa using hj)
        simpa only [Fin.lt_def, rightval, Nat.add_lt_add_iff_left] using comparison
      · intro h j hj
        by_cases left : j.val < m
        · simp only [Fin.lt_def, Fin.val_natAdd] at hj
          omega
        · let last : Fin k := ⟨j.val - m, by omega⟩
          have eq : j = Fin.natAdd m last := Fin.ext (by simp [last]; omega)
          rw [eq] at hj ⊢
          have comparison := h last (by simpa using hj)
          simpa only [Fin.lt_def, rightval, Nat.add_lt_add_iff_left] using comparison
    have prefixLaw (sign : Bool) (allowed : sign = true ∨ k = 0) (i : Fin m) :
        IsRightMaximum (blockSum sign α β) (Fin.castAdd k i) ↔
          IsRightMaximum α i := by
      constructor
      · intro h j hj
        have comparison := h (Fin.castAdd k j) (by
          simpa only [Fin.lt_def, Fin.val_castAdd] using hj)
        simpa only [Fin.lt_def, leftval,
          Nat.add_lt_add_iff_left] using comparison
      · intro h j hj
        by_cases left : j.val < m
        · let first : Fin m := ⟨j.val, left⟩
          have eq : j = Fin.castAdd k first := Fin.ext rfl
          rw [eq] at hj ⊢
          have comparison := h first (by
            simpa only [Fin.lt_def, Fin.val_castAdd] using hj)
          simpa only [Fin.lt_def, leftval,
            Nat.add_lt_add_iff_left] using comparison
        · let last : Fin k := ⟨j.val - m, by omega⟩
          have eq : j = Fin.natAdd m last := Fin.ext (by simp [last]; omega)
          rw [eq]
          cases sign with
          | false =>
            have empty : k = 0 := allowed.resolve_left Bool.false_ne_true
            have bound := last.isLt
            omega
          | true =>
            simp only [Fin.lt_def, rightval, leftval, ↓reduceIte, Nat.zero_add]
            exact lt_of_lt_of_le (β last).isLt (Nat.le_add_right _ _)
    have directPrefix (hk : 0 < k) (i : Fin m) :
        ¬IsRightMaximum (blockSum false α β) (Fin.castAdd k i) := by
      intro h
      have comparison := h (Fin.natAdd m ⟨0, hk⟩) (by
        simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
        omega)
      simp only [Fin.lt_def, rightval, leftval, Bool.false_eq_true, ↓reduceIte,
        Nat.zero_add] at comparison
      have bound := (α i).isLt
      omega
    have count {n : ℕ} (π : Equiv.Perm (Fin n)) :
        rmax π = ∑ i : Fin n, if IsRightMaximum π i then 1 else 0 := by
      simp only [rmax, Finset.card_eq_sum_ones, Finset.sum_filter]
    constructor
    · by_cases hk : k = 0
      · subst k
        rw [if_pos rfl, count, Fin.sum_univ_add, count]
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
        apply Finset.sum_congr rfl
        intro i _
        simp only [prefixLaw false (Or.inr rfl)]
      · rw [if_neg hk, count, Fin.sum_univ_add, count]
        simp only [directPrefix (Nat.pos_of_ne_zero hk), ↓reduceIte,
          Finset.sum_const_zero, zero_add, suffix]
    · rw [count, Fin.sum_univ_add, count, count]
      simp only [prefixLaw true (Or.inl rfl), suffix]

  have cutRecords (sign : Bool) (n k : ℕ) :
      Nat.card {π : ProperSigned sign n // rmax π.val.val = k} =
        ∑ cut ∈ Finset.Ioo 0 n,
          if sign then
            ∑ b ∈ Finset.range (k + 1),
              Nat.card {α : Indecomposable sign cut // rmax α.val.val = b} *
                Nat.card {β : Avoider (n - cut) // rmax β.val = k - b}
          else
            Nat.card (Indecomposable sign cut) *
              Nat.card {β : Avoider (n - cut) // rmax β.val = k} := by
    classical
    obtain ⟨_, _, _, _, _, _, _, _, enumeration, _⟩ := actual_schroder_cardinality
    obtain ⟨e, reconstruction⟩ := enumeration sign n
    let Factors (cut : ↥(Finset.Ioo 0 n)) :=
      Indecomposable sign cut.val × Avoider (n - cut.val)
    let weight (cut : ↥(Finset.Ioo 0 n)) (factors : Factors cut) :=
      if sign then rmax factors.1.val.val + rmax factors.2.val else rmax factors.2.val
    have transported {a b : ℕ} (h : a = b) (π : Equiv.Perm (Fin a)) :
        rmax (h ▸ π : Equiv.Perm (Fin b)) = rmax π := by
      cases h
      rfl
    have exactWeight (π : ProperSigned sign n) :
        rmax π.val.val = weight (e π).1 (e π).2 := by
      have cutPositive := (Finset.mem_Ioo.mp (e π).1.property).1
      have cutBelow := (Finset.mem_Ioo.mp (e π).1.property).2
      have law := blockRecords (e π).2.1.val.val (e π).2.2.val
      have preserved := congrArg rmax (reconstruction π).2
      rw [transported] at preserved
      rw [← preserved]
      cases sign with
      | false =>
        dsimp [weight]
        exact law.1.trans (if_neg (by omega))
      | true => exact law.2
    let restricted : {π : ProperSigned sign n // rmax π.val.val = k} ≃
        {item : Σ cut, Factors cut // weight item.1 item.2 = k} :=
      Equiv.subtypeEquiv e (fun π => by rw [exactWeight])
    let split : {item : Σ cut, Factors cut // weight item.1 item.2 = k} ≃
        Σ cut, {factors : Factors cut // weight cut factors = k} :=
      { toFun := fun item => ⟨item.val.1, item.val.2, item.property⟩
        invFun := fun item => ⟨⟨item.1, item.2.val⟩, item.2.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have counts (cut : ↥(Finset.Ioo 0 n)) :
        Nat.card {factors : Factors cut // weight cut factors = k} =
          if sign then
            ∑ b ∈ Finset.range (k + 1),
              Nat.card {α : Indecomposable sign cut.val // rmax α.val.val = b} *
                Nat.card {β : Avoider (n - cut.val) // rmax β.val = k - b}
          else
            Nat.card (Indecomposable sign cut.val) *
              Nat.card {β : Avoider (n - cut.val) // rmax β.val = k} := by
      cases sign with
      | false =>
        let suffixOnly : {factors : Factors cut // weight cut factors = k} ≃
            Indecomposable false cut.val ×
              {β : Avoider (n - cut.val) // rmax β.val = k} :=
          { toFun := fun item => ⟨item.val.1, item.val.2, item.property⟩
            invFun := fun item => ⟨⟨item.1, item.2.val⟩, item.2.property⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        simpa only [Bool.false_eq_true, ↓reduceIte] using
          (Nat.card_congr suffixOnly).trans (Nat.card_prod _ _)
      | true =>
        let additive : {factors : Factors cut // weight cut factors = k} ≃
            Σ b : ↥(Finset.range (k + 1)),
              {α : Indecomposable true cut.val // rmax α.val.val = b.val} ×
                {β : Avoider (n - cut.val) // rmax β.val = k - b.val} :=
          { toFun := fun item =>
              ⟨⟨rmax item.val.1.val.val, Finset.mem_range.mpr (by
                  have sum := item.property
                  dsimp [weight] at sum
                  omega)⟩,
                ⟨item.val.1, rfl⟩, ⟨item.val.2, by
                  change rmax item.val.2.val = k - rmax item.val.1.val.val
                  have sum := item.property
                  dsimp [weight] at sum
                  omega⟩⟩
            invFun := fun item => ⟨⟨item.2.1.val, item.2.2.val⟩, by
              dsimp [weight]
              rw [item.2.1.property, item.2.2.property]
              have bound := Finset.mem_range.mp item.1.property
              omega⟩
            left_inv := fun _ => rfl
            right_inv := by
              rintro ⟨⟨b, hb⟩, ⟨α, hα⟩, ⟨β, hβ⟩⟩
              dsimp at hα
              cases hα
              rfl }
        rw [Nat.card_congr additive, Nat.card_sigma]
        simp only [↓reduceIte, Nat.card_prod]
        exact Finset.sum_coe_sort (Finset.range (k + 1))
          (fun b => Nat.card {α : Indecomposable true cut.val // rmax α.val.val = b} *
            Nat.card {β : Avoider (n - cut.val) // rmax β.val = k - b})
    calc
      _ = Nat.card (Σ cut, {factors : Factors cut // weight cut factors = k}) :=
        Nat.card_congr (restricted.trans split)
      _ = ∑ cut : ↥(Finset.Ioo 0 n),
          Nat.card {factors : Factors cut // weight cut factors = k} := Nat.card_sigma
      _ = ∑ cut : ↥(Finset.Ioo 0 n),
          if sign then
            ∑ b ∈ Finset.range (k + 1),
              Nat.card {α : Indecomposable sign cut.val // rmax α.val.val = b} *
                Nat.card {β : Avoider (n - cut.val) // rmax β.val = k - b}
          else
            Nat.card (Indecomposable sign cut.val) *
              Nat.card {β : Avoider (n - cut.val) // rmax β.val = k} := by
        apply Finset.sum_congr rfl
        intro cut _
        exact counts cut
      _ = _ := Finset.sum_coe_sort (Finset.Ioo 0 n)
        (fun cut => if sign then
          ∑ b ∈ Finset.range (k + 1),
            Nat.card {α : Indecomposable sign cut // rmax α.val.val = b} *
              Nat.card {β : Avoider (n - cut) // rmax β.val = k - b}
          else Nat.card (Indecomposable sign cut) *
            Nat.card {β : Avoider (n - cut) // rmax β.val = k})

  have support (n : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin n)) :
      1 ≤ rmax π ∧ rmax π ≤ n := by
    constructor
    · apply Nat.succ_le_iff.mpr
      apply Finset.card_pos.mpr
      refine ⟨⟨n - 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      intro j hj
      have bound := j.isLt
      simp only [Fin.lt_def] at hj
      omega
    · exact (Finset.card_filter_le _ _).trans_eq (by simp)
  have singletonRecord (π : Equiv.Perm (Fin 1)) : rmax π = 1 := by
    have h := support 1 (by omega) π
    omega
  obtain ⟨_, scalarCounts, _, halfCounts, _, _, singletonCount, tinyCounts, _, _⟩ :=
    actual_schroder_cardinality
  have properTiny (sign : Bool) (n k : ℕ) (hn : n ≤ 1) :
      properCount sign n k = 0 := by
    have : IsEmpty {π : ProperSigned sign n // rmax π.val.val = k} :=
      ⟨fun π => by obtain ⟨cut, hp, hc, _⟩ := π.val.property; omega⟩
    exact Nat.card_of_isEmpty
  have singleSigned (sign : Bool) (k : ℕ) :
      signedCount sign 1 k = if k = 1 then 1 else 0 := by
    by_cases hk : k = 1
    · subst k
      rw [if_pos rfl]
      exact (Nat.card_congr (Equiv.subtypeUnivEquiv
        (fun π : Indecomposable sign 1 => singletonRecord π.val.val))).trans
          (tinyCounts sign).2
    · rw [if_neg hk]
      have : IsEmpty {π : Indecomposable sign 1 // rmax π.val.val = k} :=
        ⟨fun π => hk (π.property.symm.trans (singletonRecord π.val.val.val))⟩
      exact Nat.card_of_isEmpty
  have partition (sign : Bool) (n k : ℕ) :
      allCount n k = signedCount sign n k + properCount sign n k := by
    let P (π : Avoider n) := HasProperCut sign π.val
    let F (π : Avoider n) := rmax π.val = k
    let e : {π : Avoider n // F π} ≃
        {π : Indecomposable sign n // rmax π.val.val = k} ⊕
        {π : ProperSigned sign n // rmax π.val.val = k} :=
      (Equiv.sumCompl (fun π : {π : Avoider n // F π} => ¬P π.val)).symm.trans
        (Equiv.sumCongr
          { toFun := fun π => ⟨⟨π.val.val, π.property⟩, π.val.property⟩
            invFun := fun π => ⟨⟨π.val.val, π.property⟩, π.val.property⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
          { toFun := fun π => ⟨⟨π.val.val, not_not.mp π.property⟩, π.val.property⟩
            invFun := fun π => ⟨⟨π.val.val, π.property⟩, not_not.mpr π.val.property⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl })
    exact (Nat.card_congr e).trans Nat.card_sum
  have opposite (sign : Bool) (n k : ℕ) (hn : 2 ≤ n) :
      signedCount (!sign) n k = properCount sign n k := by
    obtain ⟨_, _, _, _, _, _, _, _, signLaw⟩ :=
      endpoint_history_count_kernel (EndpointHistory.stop none n)
    let e : Indecomposable (!sign) n ≃ ProperSigned sign n :=
      Equiv.subtypeEquivRight (fun π => signLaw sign hn π)
    exact Nat.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))
  let S := positive (signedCount true)
  have positiveCoeff (f : ℕ → ℕ → ℕ) (k n : ℕ) :
      PowerSeries.coeff n (PowerSeries.coeff k (positive f)) =
        if n = 0 then 0 else (f n k : ℚ) := by
    simp [positive]
  have zCoeff (k n : ℕ) :
      PowerSeries.coeff n (PowerSeries.coeff k z) =
        if n = 1 ∧ k = 1 then 1 else 0 := by
    simp only [z, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
    by_cases hk : k = 1 <;> by_cases hn : n = 1 <;> simp [PowerSeries.coeff_X, hk, hn]
  have signedSeries (sign : Bool) :
      positive (signedCount (!sign)) = z + positive (properCount sign) := by
    apply PowerSeries.ext
    intro k
    apply PowerSeries.ext
    intro n
    simp only [map_add, positiveCoeff, zCoeff]
    rcases n with _ | n
    · simp
    rcases n with _ | n
    · simp [singleSigned, properTiny sign 1 k (by omega)]
    · simp only [Nat.succ_ne_zero, if_false,
        show ¬(n + 1 + 1 = 1 ∧ k = 1) by omega, zero_add]
      exact_mod_cast opposite sign (n + 1 + 1) k (by omega)
  have S_eq : S = z + R := by
    exact signedSeries false
  have J_eq_proper : J = z + positive (properCount true) := by
    exact signedSeries true
  have U_partition : U = J + R := by
    apply PowerSeries.ext
    intro k
    apply PowerSeries.ext
    intro n
    simp only [U, J, R, map_add, positiveCoeff]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [if_neg hn]
      exact_mod_cast partition false n k
  have lengthProduct (f g : PowerSeries ℚ) (n : ℕ)
      (hf : PowerSeries.coeff 0 f = 0) (hg : PowerSeries.coeff 0 g = 0) :
      PowerSeries.coeff n (f * g) =
        ∑ c ∈ Finset.Ioo 0 n, PowerSeries.coeff c f * PowerSeries.coeff (n-c) g := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a f * PowerSeries.coeff b g) n]
    apply (Finset.sum_subset (by
      intro c hc
      have h := Finset.mem_Ioo.mp hc
      exact Finset.mem_range.mpr (by omega)) ?_).symm
    intro c hc hnot
    have h := Finset.mem_range.mp hc
    have hn := hnot
    simp only [Finset.mem_Ioo, not_and, not_lt] at hn
    by_cases hzero : c = 0
    · simp [hzero, hf]
    · have heq : n = c := by have := hn (by omega); omega
      simp [heq, hg]
  have R_product : R = I * U := by
    apply PowerSeries.ext
    intro k
    apply PowerSeries.ext
    intro n
    rw [show I = PowerSeries.C I0 from rfl, PowerSeries.coeff_C_mul,
      lengthProduct I0 (PowerSeries.coeff k U) n (by simp [I0]) (by simp [U, positiveCoeff])]
    simp only [R, positiveCoeff]
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn]
      have h := cutRecords false n k
      simp only [Bool.false_eq_true, if_false] at h
      rw [show properCount false n k = _ from h]
      push_cast
      apply Finset.sum_congr rfl
      intro c hc
      have h := Finset.mem_Ioo.mp hc
      simp only [I0, U, positiveCoeff, PowerSeries.coeff_mk,
        if_neg (show c ≠ 0 by omega), if_neg (show n-c ≠ 0 by omega)]
      rfl
  have S_product : positive (properCount true) = S * U := by
    apply PowerSeries.ext
    intro k
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_mul, map_sum]
    simp only [positiveCoeff]
    have productTerm (b : ℕ) :
        PowerSeries.coeff n (PowerSeries.coeff b S * PowerSeries.coeff (k-b) U) =
          ∑ c ∈ Finset.Ioo 0 n,
            (signedCount true c b : ℚ) * (allCount (n-c) (k-b) : ℚ) := by
      rw [lengthProduct _ _ n (by simp [S, positiveCoeff]) (by simp [U, positiveCoeff])]
      apply Finset.sum_congr rfl
      intro c hc
      have h := Finset.mem_Ioo.mp hc
      simp [S, U, positiveCoeff, show c ≠ 0 by omega, show n-c ≠ 0 by omega]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff n (PowerSeries.coeff a S * PowerSeries.coeff b U)) k]
    simp_rw [productTerm]
    rw [Finset.sum_comm]
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn]
      have h := cutRecords true n k
      simp only [if_true] at h
      change ((Nat.card {π : ProperSigned true n // rmax π.val.val = k}) : ℚ) = _
      rw [h]
      push_cast
      rfl
  have J_product : J = z + (z + R) * U := by
    rw [J_eq_proper, S_product, S_eq]
  have qIdentify : q = PowerSeries.X *
      (PowerSeries.largeSchroderSeries.map (Nat.castRingHom ℚ)) := by
    apply PowerSeries.ext
    intro n
    rcases n with _ | n
    · simp [q, PowerSeries.coeff_zero_eq_constantCoeff]
    · simp only [q, PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_map,
        PowerSeries.coeff_largeSchroderSeries,
        Nat.coe_castRingHom]
      have hc := scalarCounts (n+1) (by omega)
      simpa only [Nat.add_sub_cancel] using congrArg (fun m : ℕ => (m : ℚ)) hc
  have qQuadratic : q = PowerSeries.X + PowerSeries.X * q + q ^ 2 := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      PowerSeries.largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
    simp only [map_add, map_one, map_mul, PowerSeries.map_X, map_pow] at h
    rw [qIdentify]
    linear_combination (PowerSeries.X : PowerSeries ℚ) * h
  have I_half : 2 * I0 = q + PowerSeries.X := by
    rw [show (2 : PowerSeries ℚ) * I0 = I0 + I0 by ring]
    apply PowerSeries.ext
    intro n
    simp only [map_add, I0, q, PowerSeries.coeff_mk, PowerSeries.coeff_X]
    rcases n with _ | n
    · norm_num
    rcases n with _ | n
    · simp only [if_true, (tinyCounts false).2, singletonCount]
      norm_num
    · simp only [Nat.succ_ne_zero, if_false, show n+1+1 ≠ 1 by omega, add_zero]
      have h := halfCounts false (n+1+1) (by omega)
      have hc : (2 : ℚ) * Nat.card (Indecomposable false (n+1+1)) =
          Nat.card (Avoider (n+1+1)) := by exact_mod_cast h
      linarith
  have I_q : I0 * (1 + q) = q := by
    have h : 2 * (I0 * (1 + q)) = 2 * q := by
      linear_combination (1 + q) * I_half - qQuadratic
    have htwo : (2 : PowerSeries ℚ) ≠ 0 := by
      intro hzero
      have hc := congrArg PowerSeries.constantCoeff hzero
      rw [show (2 : PowerSeries ℚ) = 1 + 1 by ring, map_add, map_one] at hc
      norm_num at hc
    exact mul_left_cancel₀ htwo h
  have lifted : I * (1 + PowerSeries.C q) = PowerSeries.C q := by
    have h := congrArg PowerSeries.C I_q
    simpa only [I, map_mul, map_add, map_one] using h
  have U_J : U = (1 + PowerSeries.C q) * J := by
    linear_combination (1 + PowerSeries.C q) * U_partition +
      (1 + PowerSeries.C q) * R_product + U * lifted
  have R_qJ : R = PowerSeries.C q * J := by
    rw [R_product, U_J]
    calc
      I * ((1 + PowerSeries.C q) * J) = (I * (1 + PowerSeries.C q)) * J := by ring
      _ = _ := by rw [lifted]
  have J_quadratic : J = z + z * (1 + PowerSeries.C q) * J +
      PowerSeries.C q * (1 + PowerSeries.C q) * J ^ 2 := by
    rw [R_qJ, U_J] at J_product
    linear_combination J_product
  exact J_quadratic

noncomputable section


def a : PowerSeries ℚ := PowerSeries.X * (3 + 2*PowerSeries.X)
def b : PowerSeries ℚ := PowerSeries.X * (1 + PowerSeries.X)^3
def h : PowerSeries ℚ := 1 + PowerSeries.X
def L : PowerSeries (PowerSeries ℚ) :=
  PowerSeries.invOfUnit (1-PowerSeries.C a*PowerSeries.X) 1
def w : PowerSeries (PowerSeries ℚ) := PowerSeries.C b*PowerSeries.X^2*L^2
def Cc : PowerSeries (PowerSeries ℚ) :=
  PowerSeries.catalanSeries.map (Nat.castRingHom (PowerSeries ℚ))
def M : PowerSeries (PowerSeries ℚ) :=
  L*PowerSeries.subst w Cc
def t (r : ℕ) : PowerSeries ℚ := PowerSeries.coeff r M

theorem M_eq : M = 1 + PowerSeries.C a*PowerSeries.X*M+
      PowerSeries.C b*PowerSeries.X^2*M^2 := by
  have L_inv : (1-PowerSeries.C a*PowerSeries.X)*L = 1 := by
    exact PowerSeries.mul_invOfUnit _ 1 (by simp [L])
  have w0 : PowerSeries.constantCoeff w = 0 := by simp [w]
  have hw : PowerSeries.HasSubst w := PowerSeries.HasSubst.of_constantCoeff_zero' w0
  have C_eq : Cc^2*PowerSeries.X+1 = Cc := by
    have h0 := congrArg (PowerSeries.map (Nat.castRingHom (PowerSeries ℚ)))
      PowerSeries.catalanSeries_sq_mul_X_add_one
    simpa only [Cc, map_add,map_mul,map_pow,map_one,PowerSeries.map_X] using h0
  have swC : (PowerSeries.subst w Cc)^2*w+1 = PowerSeries.subst w Cc := by
    have h0 := congrArg (PowerSeries.subst w) C_eq
    simpa only [PowerSeries.subst_add hw,PowerSeries.subst_mul hw,
      PowerSeries.subst_pow hw,PowerSeries.subst_X hw,
      show PowerSeries.subst w (1 : PowerSeries (PowerSeries ℚ)) = 1 by
        simpa only [map_one] using (PowerSeries.subst_C (1 : PowerSeries ℚ) (a := w))] using h0
  have H : (1-PowerSeries.C a*PowerSeries.X)*M =
      1+w*(PowerSeries.subst w Cc)^2 := by
    dsimp [M]
    calc
      (1-PowerSeries.C a*PowerSeries.X) * (L*PowerSeries.subst w Cc) =
          PowerSeries.subst w Cc := by rw [← mul_assoc,L_inv,one_mul]
      _ = 1+w*(PowerSeries.subst w Cc)^2 := by linear_combination -swC
  dsimp [M,w] at H ⊢
  linear_combination H

def V : PowerSeries (PowerSeries ℚ) := PowerSeries.mk 1
def wb : PowerSeries (PowerSeries ℚ) := PowerSeries.X * V
def B : PowerSeries (PowerSeries ℚ) := V * PowerSeries.subst wb M

lemma coeff_Vpow (d n : ℕ) :
    PowerSeries.coeff n (V^d) =
      if d = 0 then (if n = 0 then 1 else 0) else
        (Nat.choose (d + n - 1) (d - 1) : PowerSeries ℚ) := by
  cases d with
  | zero => simp [V]
  | succ d =>
      have h := PowerSeries.mk_one_pow_eq_mk_choose_add (PowerSeries ℚ) d
      have hn := congrArg (PowerSeries.coeff n) h
      simpa [V, Nat.succ_eq_add_one, Nat.add_sub_cancel] using hn

theorem coeff_B (n : ℕ) : PowerSeries.coeff n B =
    ∑ d ∈ Finset.range (n+1), (n.choose d : PowerSeries ℚ) * t d := by
  classical
  have hwb : PowerSeries.HasSubst wb :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [wb])
  have first : PowerSeries.coeff n B = ∑ᶠ d,
      t d * PowerSeries.coeff n (V * wb^d) := by
    rw [B, PowerSeries.coeff_mul]
    simp_rw [PowerSeries.coeff_subst' hwb, smul_eq_mul, mul_finsum]
    rw [sum_finsum_comm]
    · apply finsum_congr
      intro d
      rw [PowerSeries.coeff_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [t]
      ring
    · intro p hp
      have hs := PowerSeries.coeff_subst_finite' hwb M p.2
      simp only [smul_eq_mul] at hs
      exact Function.HasFiniteSupport.mul_right (fun _ => PowerSeries.coeff p.1 V) hs
  rw [first]
  have coeffterm (d : ℕ) : PowerSeries.coeff n (V * wb^d) =
      if d ≤ n then (n.choose d : PowerSeries ℚ) else 0 := by
    rw [show V * wb^d = PowerSeries.X^d * V^(d+1) by
      simp only [wb, mul_pow, pow_succ]; ring]
    rw [PowerSeries.coeff_X_pow_mul']
    by_cases hd : d ≤ n
    · rw [if_pos hd, coeff_Vpow]
      simp only [show d+1 ≠ 0 by omega, if_false]
      rw [show d+1+(n-d)-1=n by omega, show d+1-1=d by omega]
      rw [if_pos hd]
    · rw [if_neg hd, if_neg hd]
  simp_rw [coeffterm]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n+1)) (by
    intro d hd
    by_contra hout
    have hd' : ¬d ≤ n := by simpa only [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff] using hout
    simp only [Function.mem_support, if_neg hd', mul_zero, ne_eq, not_true_eq_false] at hd)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [if_pos (by have := Finset.mem_range.mp hd; omega), mul_comm]

theorem B_eq : B = 1 + (1 + PowerSeries.C a) * PowerSeries.X * B +
      PowerSeries.C b * PowerSeries.X^2 * B^2 := by
  have V_inv : (1 - PowerSeries.X) * V = 1 := by
    rw [mul_comm]
    simpa [V] using PowerSeries.mk_one_mul_one_sub_eq_one (PowerSeries ℚ)
  have wb0 : PowerSeries.constantCoeff wb = 0 := by simp [wb, V]
  have hwb : PowerSeries.HasSubst wb := PowerSeries.HasSubst.of_constantCoeff_zero' wb0
  have subM := congrArg (PowerSeries.subst wb) M_eq
  simp only [PowerSeries.subst_add hwb,PowerSeries.subst_mul hwb,
    PowerSeries.subst_pow hwb,PowerSeries.subst_C,PowerSeries.subst_X hwb] at subM
  have HB : (1-PowerSeries.X)*B = PowerSeries.subst wb M := by
    dsimp [B]
    rw [← mul_assoc,V_inv,one_mul]
  rw [← HB] at subM
  dsimp [wb] at subM
  have V_right : V * (1 - PowerSeries.X) = 1 := by
    rw [mul_comm, V_inv]
  have xV : PowerSeries.X * V * (1 - PowerSeries.X) = PowerSeries.X := by
    calc
      PowerSeries.X * V * (1 - PowerSeries.X) =
          PowerSeries.X * (V * (1 - PowerSeries.X)) := by ring
      _ = PowerSeries.X := by rw [V_right, mul_one]
  have xV2 : (PowerSeries.X * V)^2 * (1 - PowerSeries.X)^2 = PowerSeries.X^2 := by
    calc
      (PowerSeries.X * V)^2 * (1 - PowerSeries.X)^2 =
          (PowerSeries.X * V * (1 - PowerSeries.X))^2 := by ring
      _ = PowerSeries.X^2 := by rw [xV]
  have sub_one : PowerSeries.subst (PowerSeries.X * V)
      (1 : PowerSeries (PowerSeries ℚ)) = 1 := by
    change PowerSeries.subst (PowerSeries.X * V)
      (PowerSeries.C (1 : PowerSeries ℚ)) = 1
    rw [PowerSeries.subst_C]
    rfl
  rw [sub_one] at subM
  change (1 - PowerSeries.X) * B =
      1 + PowerSeries.C a * (PowerSeries.X * V) * ((1 - PowerSeries.X) * B) +
        PowerSeries.C b * (PowerSeries.X * V)^2 * ((1 - PowerSeries.X) * B)^2 at subM
  have term1 : PowerSeries.C a * (PowerSeries.X * V) *
      ((1 - PowerSeries.X) * B) = PowerSeries.C a * PowerSeries.X * B := by
    calc
      _ = PowerSeries.C a * (PowerSeries.X * V * (1 - PowerSeries.X)) * B := by ring
      _ = _ := by rw [xV]
  have term2 : PowerSeries.C b * (PowerSeries.X * V)^2 *
      ((1 - PowerSeries.X) * B)^2 = PowerSeries.C b * PowerSeries.X^2 * B^2 := by
    calc
      _ = PowerSeries.C b * ((PowerSeries.X * V)^2 * (1 - PowerSeries.X)^2) * B^2 := by ring
      _ = _ := by rw [xV2]
  have hmain : (1-PowerSeries.X)*B =
      1 + PowerSeries.C a*PowerSeries.X*B + PowerSeries.C b*PowerSeries.X^2*B^2 := by
    rw [term1, term2] at subM
    exact subM
  linear_combination hmain

theorem F_eq :
    let F : PowerSeries (PowerSeries ℚ) := PowerSeries.X +
      PowerSeries.X^2 * PowerSeries.C (h^2) * B
    F = PowerSeries.X + PowerSeries.C h * PowerSeries.X * F +
      PowerSeries.C (PowerSeries.X*h) * F^2 := by
  change (PowerSeries.X + PowerSeries.X^2 * PowerSeries.C (h^2) * B) =
    PowerSeries.X + PowerSeries.C h * PowerSeries.X *
      (PowerSeries.X + PowerSeries.X^2 * PowerSeries.C (h^2) * B) +
      PowerSeries.C (PowerSeries.X*h) *
        (PowerSeries.X + PowerSeries.X^2 * PowerSeries.C (h^2) * B)^2
  have hb := B_eq
  have Ch : PowerSeries.C h = 1 + PowerSeries.C PowerSeries.X := by simp [h]
  have Ch2 : PowerSeries.C (h^2) = (1 + PowerSeries.C PowerSeries.X)^2 := by simp [h]
  have Cuh : PowerSeries.C (PowerSeries.X*h) =
      PowerSeries.C PowerSeries.X * PowerSeries.C h := by simp [map_mul]
  have Ca : PowerSeries.C a = PowerSeries.C PowerSeries.X *
      (3 + 2 * PowerSeries.C PowerSeries.X) := by
    dsimp [a]
    simp only [map_mul, map_add, map_ofNat]
  have Cb : PowerSeries.C b = PowerSeries.C PowerSeries.X *
      (1 + PowerSeries.C PowerSeries.X)^3 := by
    simp [b, map_mul, map_add, map_ofNat]
  rw [Ch, Ch2, Cuh, Ch]
  rw [Ca, Cb] at hb
  -- expected universal identity, specialized coefficient ring
  linear_combination PowerSeries.X^2 * (1 + PowerSeries.C PowerSeries.X)^2 * hb

def F : PowerSeries (PowerSeries ℚ) := PowerSeries.X +
  PowerSeries.X^2 * PowerSeries.C (h^2) * B
def q0 : PowerSeries.constantCoeff q = 0 := by simp [q]
def hq : PowerSeries.HasSubst q := PowerSeries.HasSubst.of_constantCoeff_zero' q0

def substQ : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ :=
  PowerSeries.substAlgHom hq
lemma substQ_apply (f : PowerSeries ℚ) : substQ f = PowerSeries.subst q f := by
  exact congrFun (PowerSeries.coe_substAlgHom (R := ℚ) hq) f

lemma substQ_X : substQ PowerSeries.X = q := by
  exact PowerSeries.substAlgHom_X _

def actualF : PowerSeries (PowerSeries ℚ) :=
  PowerSeries.rescale (PowerSeries.X : PowerSeries ℚ)
    (PowerSeries.map substQ.toRingHom F)

set_option maxHeartbeats 2000000 in
lemma actualF_eq : actualF = z + z * (1+PowerSeries.C q) * actualF +
    PowerSeries.C q * (1+PowerSeries.C q) * actualF^2 := by
  have hF := F_eq
  change F = PowerSeries.X + PowerSeries.C h * PowerSeries.X * F +
    PowerSeries.C (PowerSeries.X*h) * F^2 at hF
  have hs := congrArg (PowerSeries.map substQ.toRingHom) hF
  simp only [map_add,map_mul,map_pow,PowerSeries.map_C,PowerSeries.map_X] at hs
  have sx : substQ.toRingHom PowerSeries.X = q := by
    change substQ PowerSeries.X = q
    exact substQ_X
  have sh : substQ.toRingHom h = 1 + q := by
    change substQ h = 1 + q
    simp [h, substQ_X]
  rw [sx, sh] at hs
  have hr := congrArg (PowerSeries.rescale (PowerSeries.X : PowerSeries ℚ)) hs
  have rc (c : PowerSeries ℚ) : PowerSeries.rescale (PowerSeries.X : PowerSeries ℚ)
      (PowerSeries.C c) = PowerSeries.C c := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_rescale,PowerSeries.coeff_C]
    split_ifs with hn
    · simp [hn]
    · simp
  simp only [map_add,map_mul,map_pow,PowerSeries.rescale_X,rc] at hr
  have C1 : PowerSeries.C (1 : PowerSeries ℚ) =
      (1 : PowerSeries (PowerSeries ℚ)) := rfl
  rw [C1] at hr
  have hr' : actualF = PowerSeries.C (PowerSeries.X : PowerSeries ℚ)*PowerSeries.X +
      (1+PowerSeries.C q) * (PowerSeries.C (PowerSeries.X : PowerSeries ℚ)*PowerSeries.X) * actualF +
      PowerSeries.C q * (1+PowerSeries.C q) * actualF^2 := by
    simpa [actualF] using hr
  dsimp [z]
  linear_combination hr'

lemma J0 : PowerSeries.constantCoeff J = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  change PowerSeries.coeff 0
      (PowerSeries.mk (fun k => PowerSeries.mk (fun n =>
        if n = 0 then 0 else
          (signedCount false n k : ℚ)))) = 0
  apply PowerSeries.ext
  intro n
  rcases n with _ | n
  · simp
  · simp only [PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false]
    change (signedCount false (n+1) 0 : ℚ) = 0
    have hz := (D5.S1.Words.Patterns.Separable.RecordTransport.actual_four_record_transports_and_rising.2.1
      (n+1) (by omega)).1
    simp only [D5.S1.Words.Patterns.Separable.RecordTransport.irreducibleCount,
      if_neg (by omega : n+1 ≠ 0)] at hz
    exact_mod_cast hz

theorem J_eq_actualF : J = actualF := by
  have jf := D5.S1.Words.Patterns.Separable.RecordAllIndex.actual_weighted_quadratic
  have ff := actualF_eq
  have F0 : PowerSeries.constantCoeff actualF = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [actualF, PowerSeries.coeff_rescale,pow_zero,one_mul,PowerSeries.coeff_map]
    simp [F,PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have prod : (1-z*(1+PowerSeries.C q)-PowerSeries.C q*(1+PowerSeries.C q)*(J+actualF)) *
      (J-actualF) = 0 := by
    linear_combination jf-ff
  have nz : (1-z*(1+PowerSeries.C q)-PowerSeries.C q*(1+PowerSeries.C q)*(J+actualF)) ≠ 0 := by
    intro he
    have hz := congrArg PowerSeries.constantCoeff he
    simp [z,J0,F0] at hz
  exact sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left nz)

theorem J_coeff (n : ℕ) : PowerSeries.coeff (n+2) J =
    (PowerSeries.X : PowerSeries ℚ)^(n+2) * (1+q)^2 *
      ∑ r ∈ Finset.range (n+1), (n.choose r : PowerSeries ℚ)*substQ (t r) := by
  rw [J_eq_actualF]
  simp only [actualF,PowerSeries.coeff_rescale,PowerSeries.coeff_map]
  have hcoeff : PowerSeries.coeff (n+2) F = h^2 * PowerSeries.coeff n B := by
    rw [F,map_add,PowerSeries.coeff_X,
      if_neg (show n+2 ≠ 1 by omega),zero_add]
    rw [mul_assoc,PowerSeries.coeff_X_pow_mul', if_pos (by omega : 2 ≤ n+2),
      show n+2-2=n by omega,PowerSeries.coeff_C_mul]
  rw [hcoeff,coeff_B]
  have sx : substQ.toRingHom PowerSeries.X = q := by
    change substQ PowerSeries.X = q
    exact substQ_X
  have sx' : substQ PowerSeries.X = q := substQ_X
  have map_t (f : PowerSeries ℚ) : substQ.toRingHom f = substQ f := rfl
  simp only [map_mul,map_pow,map_add,map_one, h,map_sum,map_natCast,sx,sx',map_t]
  ring
private lemma binomial_shift_one (v : ℕ → PowerSeries ℚ) (m : ℕ) :
    ∑ r ∈ Finset.range (m+2), (Nat.choose (m+1) r : PowerSeries ℚ) * v r =
      ∑ r ∈ Finset.range (m+1), (Nat.choose m r : PowerSeries ℚ) *
        (v r + v (r+1)) := by
  have shifted :
      (∑ r ∈ Finset.range (m+1), (Nat.choose m (r+1) : PowerSeries ℚ) * v (r+1)) + v 0 =
      ∑ r ∈ Finset.range (m+1), (Nat.choose m r : PowerSeries ℚ) * v r := by
    calc
      _ = (∑ r ∈ Finset.range m, (Nat.choose m (r+1) : PowerSeries ℚ) * v (r+1)) + v 0 := by
        rw [Finset.sum_range_succ]
        simp
      _ = _ := by
        rw [Finset.sum_range_succ']
        simp
  rw [Finset.sum_range_succ' (fun r =>
    (Nat.choose (m+1) r : PowerSeries ℚ) * v r) (m+1)]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul,
    Nat.choose_succ_succ', Nat.cast_add, add_mul, mul_add, Finset.sum_add_distrib]
  linear_combination shifted

private lemma binomial_shift_two (v : ℕ → PowerSeries ℚ) (m : ℕ) :
    ∑ r ∈ Finset.range (m+3), (Nat.choose (m+2) r : PowerSeries ℚ) * v r =
      ∑ r ∈ Finset.range (m+1), (Nat.choose m r : PowerSeries ℚ) *
        (v r + 2*v (r+1) + v (r+2)) := by
  rw [show m+3=(m+1)+2 by omega, show m+2=(m+1)+1 by omega,
    binomial_shift_one v (m+1), binomial_shift_one (fun r => v r+v (r+1)) m]
  apply Finset.sum_congr rfl
  intro r hr
  ring

lemma q_quadratic : q = PowerSeries.X + PowerSeries.X*q + q^2 := by
  obtain ⟨_, scalarCounts, _, _, _, _, _, _, _, _⟩ :=
    D5.S1.Words.Patterns.Separable.ActualCardinality.actual_schroder_cardinality
  have qIdentify : q = PowerSeries.X *
      (PowerSeries.largeSchroderSeries.map (Nat.castRingHom ℚ)) := by
    apply PowerSeries.ext
    intro n
    rcases n with _ | n
    · simp [q, PowerSeries.coeff_zero_eq_constantCoeff]
    · simp only [q, PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_map,
        PowerSeries.coeff_largeSchroderSeries, Nat.coe_castRingHom]
      have hc := scalarCounts (n+1) (by omega)
      simpa only [Nat.add_sub_cancel] using congrArg (fun z : ℕ => (z : ℚ)) hc
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
    PowerSeries.largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
  simp only [map_add,map_one,map_mul,PowerSeries.map_X,map_pow] at h
  rw [qIdentify]
  linear_combination (PowerSeries.X : PowerSeries ℚ) * h

lemma time_relation : PowerSeries.X * (1+q) = q*(1-q) := by
  linear_combination -q_quadratic

def G (r : ℕ) : PowerSeries ℚ :=
    (1+PowerSeries.X)^2 * (t r + t (r+1)) -
      PowerSeries.X*(1-PowerSeries.X)*(1+PowerSeries.X) *
        (t r + 2*t (r+1) + t (r+2))

lemma G_nonnegative (r n : ℕ) : 0 ≤ PowerSeries.coeff n (substQ (G r)) := by
  have h :=
    D5.S1.Words.Patterns.Separable.RecordNewtonPositivity.actual_q_record_newton_nonnegative r n
  simpa [G, t, M, L, w, Cc, a, b, substQ_apply] using h

lemma actual_adjacent_difference (m : ℕ) :
    PowerSeries.coeff (m+3) J - PowerSeries.coeff (m+4) J =
      (PowerSeries.X : PowerSeries ℚ)^(m+3) *
        ∑ r ∈ Finset.range (m+1), (Nat.choose m r : PowerSeries ℚ) * substQ (G r) := by
  rw [J_coeff (m+1), J_coeff (m+2),
    binomial_shift_one (fun r => substQ (t r)) m,
    binomial_shift_two (fun r => substQ (t r)) m]
  have hG (r : ℕ) : substQ (G r) =
      (1+q)^2 * (substQ (t r) + substQ (t (r+1))) -
        q*(1-q)*(1+q) *
          (substQ (t r) + 2*substQ (t (r+1)) + substQ (t (r+2))) := by
    simp only [G, map_sub, map_mul, map_pow, map_add, map_one, map_ofNat, substQ_X]
  simp_rw [hG]
  rw [show (PowerSeries.X : PowerSeries ℚ)^(m+4) =
      PowerSeries.X^(m+3) * PowerSeries.X by ring]
  have ht : q*(1-q)*(1+q) = PowerSeries.X*(1+q)^2 := by
    rw [← time_relation]
    ring
  rw [ht]
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp_rw [show ∀ (c v : PowerSeries ℚ), c*((1+q)^2*v) =
    (1+q)^2*(c*v) by intros; ring,
    show ∀ (c v : PowerSeries ℚ), c*(PowerSeries.X*(1+q)^2*v) =
    PowerSeries.X*(1+q)^2*(c*v) by intros; ring]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem actual_rmax_decline (n k : ℕ) (hk : 3 ≤ k) :
    irreducibleCount n rmax (k+1) ≤ irreducibleCount n rmax k := by
  by_cases hn : n = 0
  · simp [irreducibleCount, hn]
  have h := congrArg (PowerSeries.coeff n) (actual_adjacent_difference (k-3))
  rw [map_sub, PowerSeries.coeff_X_pow_mul'] at h
  rw [show k-3+3=k by omega, show k-3+4=k+1 by omega,
    show k-3+1=k-2 by omega] at h
  have hsum (d : ℕ) :
      0 ≤ PowerSeries.coeff d
        (∑ r ∈ Finset.range (k-2),
          (Nat.choose (k-3) r : PowerSeries ℚ) * substQ (G r)) := by
    simp only [map_sum]
    exact Finset.sum_nonneg (fun r hr => by
      have hg := G_nonnegative r d
      change 0 ≤ PowerSeries.coeff d
        (PowerSeries.C ((Nat.choose (k-3) r : ℕ) : ℚ) * substQ (G r))
      rw [PowerSeries.coeff_C_mul]
      exact mul_nonneg (Nat.cast_nonneg _) hg)
  have nonnegative : 0 ≤ (if k ≤ n then
      PowerSeries.coeff (n-k)
        (∑ r ∈ Finset.range (k-2),
          (Nat.choose (k-3) r : PowerSeries ℚ) * substQ (G r)) else 0) := by
    split_ifs with hkn
    · exact hsum _
    · rfl
  have coeff_J (j : ℕ) :
      PowerSeries.coeff n (PowerSeries.coeff j J) =
        if n = 0 then 0 else (signedCount false n j : ℚ) := by
    change PowerSeries.coeff n
      (PowerSeries.coeff j
        (PowerSeries.mk (fun k => PowerSeries.mk (fun d =>
          if d = 0 then 0 else (signedCount false d k : ℚ))))) = _
    simp
  rw [coeff_J k, coeff_J (k+1), if_neg hn, if_neg hn] at h
  simp only [irreducibleCount, if_neg hn]
  exact_mod_cast (show (signedCount false n (k+1) : ℚ) ≤
      signedCount false n k by linarith)

theorem actual_ckz_conjecture_two :
    ∀ n, 5 ≤ n →
      (∀ k, k < 3 →
        irreducibleCount n rmax k ≤ irreducibleCount n rmax (k+1) ∧
        irreducibleCount n lmin k ≤ irreducibleCount n lmin (k+1) ∧
        reducibleCount n lmax k ≤ reducibleCount n lmax (k+1) ∧
        reducibleCount n rmin k ≤ reducibleCount n rmin (k+1)) ∧
      (∀ k, 3 ≤ k →
        irreducibleCount n rmax (k+1) ≤ irreducibleCount n rmax k ∧
        irreducibleCount n lmin (k+1) ≤ irreducibleCount n lmin k ∧
        reducibleCount n lmax (k+1) ≤ reducibleCount n lmax k ∧
        reducibleCount n rmin (k+1) ≤ reducibleCount n rmin k) ∧
      (∀ k,
        irreducibleCount n rmax k ≤ irreducibleCount n rmax 3 ∧
        irreducibleCount n lmin k ≤ irreducibleCount n lmin 3 ∧
        reducibleCount n lmax k ≤ reducibleCount n lmax 3 ∧
        reducibleCount n rmin k ≤ reducibleCount n rmin 3) := by
  intro n hn
  obtain ⟨transports, _, _, rising⟩ :=
    actual_four_record_transports_and_rising
  have eqs (k : ℕ) :
      irreducibleCount n lmin k = irreducibleCount n rmax k ∧
      reducibleCount n lmax k = irreducibleCount n rmax k ∧
      reducibleCount n rmin k = irreducibleCount n rmax k := by
    have h := transports n k
    simpa [show ¬(n = 1 ∧ k = 1) by omega] using h
  have rmax_to_three : ∀ k, 3 ≤ k →
      irreducibleCount n rmax k ≤ irreducibleCount n rmax 3 := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases h3 : k = 3
      · subst k
        exact le_rfl
      · have hprev : 3 ≤ k - 1 := by omega
        have hs := (actual_rmax_decline n (k-1) hprev).trans
          (ih (k-1) (by omega) hprev)
        simpa only [show k-1+1=k by omega] using hs
  have rise_part : ∀ k, k < 3 →
      irreducibleCount n rmax k ≤ irreducibleCount n rmax (k+1) ∧
      irreducibleCount n lmin k ≤ irreducibleCount n lmin (k+1) ∧
      reducibleCount n lmax k ≤ reducibleCount n lmax (k+1) ∧
      reducibleCount n rmin k ≤ reducibleCount n rmin (k+1) := by
    intro k hk
    exact rising n (by omega) k hk
  have decline_part : ∀ k, 3 ≤ k →
      irreducibleCount n rmax (k+1) ≤ irreducibleCount n rmax k ∧
      irreducibleCount n lmin (k+1) ≤ irreducibleCount n lmin k ∧
      reducibleCount n lmax (k+1) ≤ reducibleCount n lmax k ∧
      reducibleCount n rmin (k+1) ≤ reducibleCount n rmin k := by
    intro k hk
    have hr := actual_rmax_decline n k hk
    have ek := eqs k
    have ek1 := eqs (k+1)
    rw [ek.1, ek.2.1, ek.2.2, ek1.1, ek1.2.1, ek1.2.2]
    exact ⟨hr, hr, hr, hr⟩
  have peak_part : ∀ k,
      irreducibleCount n rmax k ≤ irreducibleCount n rmax 3 ∧
      irreducibleCount n lmin k ≤ irreducibleCount n lmin 3 ∧
      reducibleCount n lmax k ≤ reducibleCount n lmax 3 ∧
      reducibleCount n rmin k ≤ reducibleCount n rmin 3 := by
    intro k
    by_cases hk : k < 3
    · interval_cases k
      · have h0 := rise_part 0 (by omega)
        have h1 := rise_part 1 (by omega)
        have h2 := rise_part 2 (by omega)
        exact ⟨h0.1.trans (h1.1.trans h2.1),
          h0.2.1.trans (h1.2.1.trans h2.2.1),
          h0.2.2.1.trans (h1.2.2.1.trans h2.2.2.1),
          h0.2.2.2.trans (h1.2.2.2.trans h2.2.2.2)⟩
      · have h1 := rise_part 1 (by omega)
        have h2 := rise_part 2 (by omega)
        exact ⟨h1.1.trans h2.1,
          h1.2.1.trans h2.2.1,
          h1.2.2.1.trans h2.2.2.1,
          h1.2.2.2.trans h2.2.2.2⟩
      · have h2 := rise_part 2 (by omega)
        exact ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩
    · have hk3 : 3 ≤ k := by omega
      have hr := rmax_to_three k hk3
      have ek := eqs k
      have e3 := eqs 3
      exact ⟨hr,
        (calc
          irreducibleCount n lmin k = irreducibleCount n rmax k := ek.1
          _ ≤ irreducibleCount n rmax 3 := hr
          _ = irreducibleCount n lmin 3 := e3.1.symm),
        (calc
          reducibleCount n lmax k = irreducibleCount n rmax k := ek.2.1
          _ ≤ irreducibleCount n rmax 3 := hr
          _ = reducibleCount n lmax 3 := e3.2.1.symm),
        (calc
          reducibleCount n rmin k = irreducibleCount n rmax k := ek.2.2
          _ ≤ irreducibleCount n rmax 3 := hr
          _ = reducibleCount n rmin 3 := e3.2.2.symm)⟩
  exact ⟨rise_part, decline_part, peak_part⟩

end
end D5.S1.Words.Patterns.Separable.RecordAllIndex
