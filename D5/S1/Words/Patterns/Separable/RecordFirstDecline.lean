/- GID: D5/S1/Words/Patterns/Separable/RecordFirstDecline
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/RecordFirstDecline
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Schroder]
   utility: none
   digest: Actual four record fibers decline from three to four, strictly for n ≥ 3. -/

import D5.S1.Words.Patterns.Separable.RecordTransport

namespace D5.S1.Words.Patterns.Separable.RecordFirstDecline

open D5.S1.Words.Patterns.Separable.RecordPeak
open D5.S1.Words.Patterns.Separable.RecordTransport
open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open D5.S1.Words.Patterns.Separable.ActualCardinality
open D5.S1.Words.Patterns.Separable.EndpointHistoryKernel
open PowerSeries
  (largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq)
open scoped BigOperators

/-- The first declining comparison is weak at every length, and strict at
all lengths at least three, in all four actual CKZ record distributions. -/
theorem actual_four_record_first_decline :
    (∀ n,
      irreducibleCount n rmax 4 ≤ irreducibleCount n rmax 3 ∧
      irreducibleCount n lmin 4 ≤ irreducibleCount n lmin 3 ∧
      reducibleCount n lmax 4 ≤ reducibleCount n lmax 3 ∧
      reducibleCount n rmin 4 ≤ reducibleCount n rmin 3) ∧
    (∀ n, 3 ≤ n →
      irreducibleCount n rmax 4 < irreducibleCount n rmax 3 ∧
      irreducibleCount n lmin 4 < irreducibleCount n lmin 3 ∧
      reducibleCount n lmax 4 < reducibleCount n lmax 3 ∧
      reducibleCount n rmin 4 < reducibleCount n rmin 3) := by
  classical
  let positive (f : ℕ → ℕ → ℕ) : PowerSeries (PowerSeries ℚ) :=
    PowerSeries.mk fun k => PowerSeries.mk fun n => if n = 0 then 0 else (f n k : ℚ)
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
  -- Restrict the frozen least-cut reconstruction to actual record fibers.
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
  -- Positive length supplies a last position, and records are a subset of positions.
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
  have U_def : U = positive allCount := rfl
  have J_def : J = positive (signedCount false) := rfl
  have R_def : R = positive (properCount false) := rfl
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
    simp only [U_def, J_def, R_def, map_add, positiveCoeff]
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
      lengthProduct I0 (PowerSeries.coeff k U) n (by simp [I0]) (by simp [U_def, positiveCoeff])]
    simp only [R_def, positiveCoeff]
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
      simp only [I0, U_def, positiveCoeff, PowerSeries.coeff_mk,
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
      rw [lengthProduct _ _ n (by simp [S, positiveCoeff]) (by simp [U_def, positiveCoeff])]
      apply Finset.sum_congr rfl
      intro c hc
      have h := Finset.mem_Ioo.mp hc
      simp [S, U_def, positiveCoeff, show c ≠ 0 by omega, show n-c ≠ 0 by omega]
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
      largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
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
  have zeroSigned (n : ℕ) (hn : 0 < n) : signedCount false n 0 = 0 := by
    have h := (actual_four_record_transports_and_rising.2.1 n hn).1
    simpa only [irreducibleCount, signedCount, if_neg (by omega : n ≠ 0)] using h
  have J0 : PowerSeries.coeff 0 J = 0 := by
    apply PowerSeries.ext
    intro n
    simp only [J_def, positiveCoeff, map_zero]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [if_neg hn, zeroSigned n (by omega), Nat.cast_zero]
  have normalizedJ : J =
      PowerSeries.C (PowerSeries.X : PowerSeries ℚ) * PowerSeries.X +
      PowerSeries.C (PowerSeries.X * (1+q)) * (PowerSeries.X * J) +
      PowerSeries.C (q * (1+q)) * J^2 := by
    calc
      J = z + z * (1 + PowerSeries.C q) * J +
          PowerSeries.C q * (1 + PowerSeries.C q) * J ^ 2 := J_quadratic
      _ = _ := by simp only [map_mul, map_add, map_one, z]; ring
  have J1 : PowerSeries.coeff 1 J = PowerSeries.X := by
    apply PowerSeries.ext
    intro n
    simp only [J_def, positiveCoeff, PowerSeries.coeff_X]
    rcases n with _ | n
    · norm_num
    rcases n with _ | n
    · simp [singleSigned]
    · simp only [Nat.succ_ne_zero, if_false, show n+1+1 ≠ 1 by omega]
      have h := (actual_four_record_transports_and_rising.2.2.1 (n+1+1) (by omega)).1
      simp only [irreducibleCount, if_neg (by omega : n+1+1 ≠ 0)] at h
      exact_mod_cast h
  have J2 : PowerSeries.coeff 2 J = PowerSeries.X^2 * (1+q)^2 := by
    have h := congrArg (PowerSeries.coeff 2) normalizedJ
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
      show ¬(2 = 1) by omega,
      PowerSeries.coeff_succ_X_mul, J1] at h
    simp only [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Finset.sum_range_zero, Nat.sub_zero, Nat.sub_self, J0, J1,
      zero_mul, mul_zero, add_zero, zero_add] at h
    simp only [if_false, mul_zero, zero_add] at h
    linear_combination h
  have J3 : PowerSeries.coeff 3 J = PowerSeries.X^3 * (1+q)^3 * (1+2*q) := by
    have h := congrArg (PowerSeries.coeff 3) normalizedJ
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
      show ¬(3 = 1) by omega, if_false, mul_zero,
      PowerSeries.coeff_succ_X_mul, J2] at h
    norm_num only [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Finset.sum_range_zero, Nat.sub_zero, Nat.sub_self, J0, J1, J2,
      zero_mul, mul_zero, add_zero, zero_add] at h
    linear_combination h
  have timeRelation : PowerSeries.X * (1+q) = q * (1-q) := by
    linear_combination -qQuadratic
  -- The first declining comparison uses the next actual record coefficient.
  have J4 : PowerSeries.coeff 4 J =
      PowerSeries.X^4 * (1+q)^4 * (1+5*q+5*q^2) := by
    have h := congrArg (PowerSeries.coeff 4) normalizedJ
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
      show ¬(4 = 1) by omega, if_false, mul_zero,
      PowerSeries.coeff_succ_X_mul, J3] at h
    norm_num only [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Finset.sum_range_zero, Nat.zero_add, Nat.sub_zero, Nat.sub_self,
      J0, J1, J2, J3, zero_mul, mul_zero, add_zero, zero_add] at h
    linear_combination h
  let P : PowerSeries ℚ := 1+4*PowerSeries.X+2*PowerSeries.X^2-
    8*PowerSeries.X^3-6*PowerSeries.X^4+11*PowerSeries.X^5+
    15*PowerSeries.X^6+5*PowerSeries.X^7
  let K : PowerSeries ℚ := 1-2*PowerSeries.X-PowerSeries.X^2
  let N : PowerSeries ℚ := 4+12*PowerSeries.X-12*PowerSeries.X^2-
    68*PowerSeries.X^3-17*PowerSeries.X^4+176*PowerSeries.X^5+
    270*PowerSeries.X^6+160*PowerSeries.X^7+35*PowerSeries.X^8
  have q0 : PowerSeries.constantCoeff q = 0 := by
    simp only [q, PowerSeries.constantCoeff_mk, if_true]
  have hq : PowerSeries.HasSubst q := PowerSeries.HasSubst.of_constantCoeff_zero' q0
  let substQ : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := PowerSeries.substAlgHom hq
  have substApply (f : PowerSeries ℚ) : substQ f = PowerSeries.subst q f :=
    congrFun (PowerSeries.coe_substAlgHom (R := ℚ) hq) f
  have substX : substQ PowerSeries.X = q := by
    rw [substApply]
    exact PowerSeries.subst_X hq
  have difference : PowerSeries.coeff 3 J - PowerSeries.coeff 4 J =
      PowerSeries.X^3 * substQ P := by
    rw [J3, J4]
    dsimp [P]
    simp only [map_sub, map_add, map_one, map_mul, map_pow, map_ofNat, substX]
    linear_combination -PowerSeries.X^3 * (1+q)^3 * (1+5*q+5*q^2) * timeRelation
  let pair (n : ℕ) : ℕ × ℕ :=
    (fun p : ℕ × ℕ => (p.2, 2*p.2+p.1))^[n] (2224, 5372)
  let cert (n : ℕ) : ℕ := match n with
    | 0 => 4
    | 1 => 20
    | 2 => 32
    | 3 => 16
    | 4 => 47
    | 5 => 286
    | 6 => 889
    | 7 => 2224
    | n+8 => (pair n).2
  have certTail (n : ℕ) (hn : 7 ≤ n) : cert (n+2) = 2*cert (n+1)+cert n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rcases m with _ | m
    · norm_num [cert, pair, Function.iterate_succ_apply']
    · rw [show 7+(m+1)+2 = (m+2)+8 by omega,
        show 7+(m+1)+1 = (m+1)+8 by omega,
        show 7+(m+1) = m+8 by omega]
      simp [cert, pair, Function.iterate_succ_apply']
  let V : PowerSeries ℚ := PowerSeries.mk fun n => (cert n : ℚ)
  have coeffNumber (a : ℕ) [a.AtLeastTwo] (n : ℕ) (f : PowerSeries ℚ) :
      PowerSeries.coeff n ((OfNat.ofNat a : PowerSeries ℚ)*f) =
        (OfNat.ofNat a : ℚ)*PowerSeries.coeff n f := by
    exact PowerSeries.coeff_C_mul n f (OfNat.ofNat a)
  have coeffConstant (a : ℕ) [a.AtLeastTwo] (n : ℕ) :
      PowerSeries.coeff n (OfNat.ofNat a : PowerSeries ℚ) =
        if n = 0 then (OfNat.ofNat a : ℚ) else 0 := by
    exact PowerSeries.coeff_C n (OfNat.ofNat a : ℚ)
  have constantNumber (a : ℕ) [a.AtLeastTwo] :
      PowerSeries.constantCoeff (OfNat.ofNat a : PowerSeries ℚ) =
        (OfNat.ofNat a : ℚ) := by
    exact PowerSeries.constantCoeff_C (OfNat.ofNat a : ℚ)
  have certificate : K * V = N := by
    have hnorm : K * V = V - (PowerSeries.X * V + PowerSeries.X * V) -
        PowerSeries.X^2 * V := by dsimp [K]; ring
    rw [hnorm]
    apply PowerSeries.ext
    intro n
    rcases n with _ | n
    · norm_num [V, N, cert, pair, PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.constantCoeff_mk, constantNumber]
    rcases n with _ | n
    · norm_num [V, N, cert, pair, map_sub, map_add, coeffNumber,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul', coeffConstant]
    · simp only [map_sub, map_add, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_X_pow_mul', show 2 ≤ n+1+1 by omega, if_true,
        show n+1+1-2 = n by omega, V, PowerSeries.coeff_mk]
      by_cases hn : n ≤ 6
      · interval_cases n <;>
          norm_num [N, cert, pair, coeffNumber, coeffConstant,
            PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
      · have hv := certTail n (by omega)
        have hN : PowerSeries.coeff (n+1+1) N = 0 := by
          dsimp [N]
          simp only [map_sub, map_add, coeffNumber, PowerSeries.coeff_X_pow,
            coeffConstant, PowerSeries.coeff_X]
          norm_num [show n+1+1 ≠ 0 by omega, show n+1+1 ≠ 1 by omega,
            show n+1+1 ≠ 2 by omega, show n+1+1 ≠ 3 by omega,
            show n+1+1 ≠ 4 by omega, show n+1+1 ≠ 5 by omega,
            show n+1+1 ≠ 6 by omega, show n+1+1 ≠ 7 by omega,
            show n+1+1 ≠ 8 by omega]
        rw [hN, show n+1+1 = n+2 by omega, hv]
        push_cast
        ring
  have qDerivative : substQ K * PowerSeries.derivative ℚ q = (1+q)^2 := by
    have hd := congrArg (PowerSeries.derivative ℚ) qQuadratic
    simp only [map_add, Derivation.leibniz, PowerSeries.derivative_X,
      PowerSeries.derivative_pow, smul_eq_mul] at hd
    dsimp [K]
    simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, substX]
    linear_combination (1+q) * hd - PowerSeries.derivative ℚ q * qQuadratic
  have polyDerivative : PowerSeries.derivative ℚ P * (1+PowerSeries.X)^2 = N := by
    have dNum (a : ℕ) [a.AtLeastTwo] :
        PowerSeries.derivative ℚ (OfNat.ofNat a : PowerSeries ℚ) = 0 := by
      exact PowerSeries.derivative_C
    dsimp [P, N]
    simp only [map_sub, map_add, Derivation.leibniz, dNum,
      PowerSeries.derivative_one, PowerSeries.derivative_X, PowerSeries.derivative_pow,
      smul_eq_mul]
    norm_num
    ring
  have PDerivative : PowerSeries.derivative ℚ (substQ P) = substQ V := by
    have hp := congrArg substQ polyDerivative
    simp only [map_add, map_mul, map_pow, map_one, substX] at hp
    have hc := congrArg substQ certificate
    simp only [map_mul] at hc
    have chain : PowerSeries.derivative ℚ (substQ P) =
        substQ (PowerSeries.derivative ℚ P) * PowerSeries.derivative ℚ q := by
      rw [substApply, substApply]
      exact PowerSeries.derivative_subst hq
    have hcalc : substQ K * PowerSeries.derivative ℚ (substQ P) = substQ N := by
      rw [chain]
      linear_combination hp + substQ (PowerSeries.derivative ℚ P) * qDerivative
    have hK : substQ K ≠ 0 := by
      intro he
      have hc0 := congrArg PowerSeries.constantCoeff he
      dsimp [K] at hc0
      simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, substX, q0,
        mul_zero, sub_zero] at hc0
      norm_num at hc0
    exact mul_left_cancel₀ hK (hcalc.trans hc.symm)
  have positiveMul (f g : PowerSeries ℚ)
      (hf : ∀ n, 0 ≤ PowerSeries.coeff n f) (hg : ∀ n, 0 ≤ PowerSeries.coeff n g) :
      ∀ n, 0 ≤ PowerSeries.coeff n (f*g) := by
    intro n
    rw [PowerSeries.coeff_mul]
    exact Finset.sum_nonneg (fun _ _ => mul_nonneg (hf _) (hg _))
  have qPositive (n : ℕ) : 0 ≤ PowerSeries.coeff n q := by
    simp only [q, PowerSeries.coeff_mk]
    split_ifs <;> positivity
  have qPowerPositive (d n : ℕ) : 0 ≤ PowerSeries.coeff n (q^d) := by
    induction d generalizing n with
    | zero => simp only [pow_zero, PowerSeries.coeff_one]; split_ifs <;> norm_num
    | succ d ih => rw [pow_succ]; exact positiveMul _ _ ih qPositive n
  have composedPositive (f : PowerSeries ℚ) (hf : ∀ d, 0 ≤ PowerSeries.coeff d f)
      (n : ℕ) : 0 ≤ PowerSeries.coeff n (substQ f) := by
    rw [substApply, PowerSeries.coeff_subst' hq]
    apply finsum_nonneg
    intro d
    exact mul_nonneg (hf d) (qPowerPositive d n)
  have VMinusPositive (n : ℕ) : 0 ≤ PowerSeries.coeff n (V - 20*PowerSeries.X) := by
    by_cases hn : n = 1
    · subst n
      norm_num [V, cert, map_sub, coeffNumber, PowerSeries.coeff_X]
    · simp only [map_sub, coeffNumber, PowerSeries.coeff_X, if_neg hn, mul_zero,
        sub_zero, V, PowerSeries.coeff_mk]
      exact Nat.cast_nonneg _
  have qStrict (n : ℕ) (hn : 0 < n) : 0 < PowerSeries.coeff n q := by
    have schroderPos (m : ℕ) : 0 < Nat.largeSchroder m := by
      induction m with
      | zero => simp
      | succ m ih => rw [Nat.largeSchroder_succ]; omega
    simp only [q, PowerSeries.coeff_mk, if_neg (by omega : n ≠ 0)]
    rw [scalarCounts n hn]
    exact_mod_cast schroderPos (n-1)
  have derivativeStrict (n : ℕ) : 0 < PowerSeries.coeff n (substQ V) := by
    rcases n with _ | n
    · have hz : PowerSeries.constantCoeff (substQ (V-4)) = 0 := by
        rw [substApply, PowerSeries.constantCoeff_eq]
        exact PowerSeries.constantCoeff_subst_eq_zero q0 (V-4)
          (by norm_num [V, cert, PowerSeries.constantCoeff_mk, constantNumber])
      simp only [map_sub, map_ofNat] at hz
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      linarith
    · have h := composedPositive (V - 20*PowerSeries.X) VMinusPositive (n+1)
      simp only [map_sub, map_mul, map_ofNat, substX, coeffNumber] at h
      have hqpos := qStrict (n+1) (by omega)
      linarith
  have PStrict (n : ℕ) : 0 < PowerSeries.coeff n (substQ P) := by
    rcases n with _ | n
    · dsimp [P]
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one, substX,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, map_add, map_mul,
        map_pow, map_ofNat, map_one, q0]
      norm_num
    · have h := derivativeStrict n
      rw [← PDerivative, PowerSeries.coeff_derivative] at h
      have hn : (0 : ℚ) < n+1 := by positivity
      exact pos_of_mul_pos_left h (le_of_lt hn)
  have actualWeak (n : ℕ) : irreducibleCount n rmax 4 ≤ irreducibleCount n rmax 3 := by
    by_cases hn : n = 0
    · simp [hn, irreducibleCount]
    · have h := congrArg (PowerSeries.coeff n) difference
      rw [map_sub, PowerSeries.coeff_X_pow_mul'] at h
      simp only [J_def, positiveCoeff, if_neg hn] at h
      have nonnegative : 0 ≤ (if 3 ≤ n then PowerSeries.coeff (n-3) (substQ P) else 0) := by
        split_ifs
        · exact le_of_lt (PStrict _)
        · rfl
      simp only [irreducibleCount, if_neg hn]
      exact_mod_cast (show (signedCount false n 4 : ℚ) ≤ signedCount false n 3 by linarith)
  have actualStrict (n : ℕ) (hn : 3 ≤ n) :
      irreducibleCount n rmax 4 < irreducibleCount n rmax 3 := by
    have h := congrArg (PowerSeries.coeff n) difference
    rw [map_sub, PowerSeries.coeff_X_pow_mul', if_pos hn] at h
    simp only [J_def, positiveCoeff, if_neg (by omega : n ≠ 0)] at h
    have hp := PStrict (n-3)
    simp only [irreducibleCount, if_neg (by omega : n ≠ 0)]
    exact_mod_cast (show (signedCount false n 4 : ℚ) < signedCount false n 3 by linarith)
  obtain ⟨transports, _, _, _⟩ := actual_four_record_transports_and_rising
  have equalities (n : ℕ) :
      irreducibleCount n lmin 3 = irreducibleCount n rmax 3 ∧
      irreducibleCount n lmin 4 = irreducibleCount n rmax 4 ∧
      reducibleCount n lmax 3 = irreducibleCount n rmax 3 ∧
      reducibleCount n lmax 4 = irreducibleCount n rmax 4 ∧
      reducibleCount n rmin 3 = irreducibleCount n rmax 3 ∧
      reducibleCount n rmin 4 = irreducibleCount n rmax 4 := by
    have h3 := transports n 3
    have h4 := transports n 4
    norm_num at h3 h4
    exact ⟨h3.1, h4.1, h3.2.1, h4.2.1, h3.2.2, h4.2.2⟩
  constructor
  · intro n
    obtain ⟨h13, h14, h23, h24, h33, h34⟩ := equalities n
    rw [h13, h14, h23, h24, h33, h34]
    exact ⟨actualWeak n, actualWeak n, actualWeak n, actualWeak n⟩
  · intro n hn
    obtain ⟨h13, h14, h23, h24, h33, h34⟩ := equalities n
    rw [h13, h14, h23, h24, h33, h34]
    exact ⟨actualStrict n hn, actualStrict n hn, actualStrict n hn, actualStrict n hn⟩

#print axioms actual_four_record_first_decline

end D5.S1.Words.Patterns.Separable.RecordFirstDecline
