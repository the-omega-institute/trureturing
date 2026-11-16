/- GID: D5/S1/Words/Patterns/Separable/RecordAllIndex
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/RecordAllIndex
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [D5/S1/Words/Patterns/Separable/RecordNewtonPositivity, D5/S1/Words/Patterns/Separable/RecordTransport]
   utility: none
   digest: Actual-carrier CKZ weighted record quadratic reconstructed from direct-cut enumeration; all-index coefficient normalization remains open. -/

import D5.S1.Words.Patterns.Separable.RecordNewtonPositivity
import D5.S1.Words.Patterns.Separable.RecordFirstDecline

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

end D5.S1.Words.Patterns.Separable.RecordAllIndex
