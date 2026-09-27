/- GID: D5/S3/Estimation/DecisionRisk/SignPairUStatisticMoments
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/SignPairUStatisticMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Product signs give exact moments for the second-order pair U-statistic. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments

open scoped BigOperators

/-- Product weight of a sign vector with common coordinate mean `mu`. -/
noncomputable def signPairWeight {k : ℕ} (mu : ℝ) (eta : Fin k → ℤˣ) : ℝ :=
  ∏ i, (1 + mu * (((eta i : ℤˣ) : ℤ) : ℝ)) / 2

/-- The normalized second-order sign U-statistic. -/
noncomputable def signPairUStatistic {k : ℕ} (eta : Fin k → ℤˣ) : ℝ :=
  ((∑ i, (((eta i : ℤˣ) : ℤ) : ℝ)) ^ 2 - (k : ℝ)) /
    ((k : ℝ) * ((k : ℝ) - 1))

/-- The pair representation, mean, and variance of the sign U-statistic under its product law. -/
theorem sign_pair_u_statistic_moments (k : ℕ) (mu : ℝ) (hk : 2 ≤ k)
    (_hmu_lower : -1 ≤ mu) (_hmu_upper : mu ≤ 1) :
    (∀ eta : Fin k → ℤˣ,
      signPairUStatistic eta =
        (∑ i : Fin k, ∑ j : Fin k,
          if i < j then
            (((eta i : ℤˣ) : ℤ) : ℝ) * (((eta j : ℤˣ) : ℤ) : ℝ)
          else 0) / (Nat.choose k 2 : ℝ)) ∧
    (∑ eta : Fin k → ℤˣ, signPairWeight mu eta * signPairUStatistic eta) =
      mu ^ 2 ∧
    (∑ eta : Fin k → ℤˣ, signPairWeight mu eta * signPairUStatistic eta ^ 2) -
        (∑ eta : Fin k → ℤˣ, signPairWeight mu eta * signPairUStatistic eta) ^ 2 =
      4 * mu ^ 2 * (1 - mu ^ 2) / k +
        2 * (1 - mu ^ 2) ^ 2 / ((k : ℝ) * ((k : ℝ) - 1)) := by
  classical
  let a : ℤˣ → ℝ := fun u => (1 + mu * (((u : ℤˣ) : ℤ) : ℝ)) / 2
  let x : (Fin k → ℤˣ) → Fin k → ℝ :=
    fun eta i => (((eta i : ℤˣ) : ℤ) : ℝ)
  let z : (Fin k → ℤˣ) → Fin k → ℝ := fun eta i => x eta i - mu
  let E : ((Fin k → ℤˣ) → ℝ) → ℝ :=
    fun f => ∑ eta : Fin k → ℤˣ, signPairWeight mu eta * f eta
  let pairSum : (Fin k → ℝ) → ℝ :=
    fun f => ∑ i : Fin k, ∑ j : Fin k, if i < j then f i * f j else 0

  have ha_zero : (∑ u : ℤˣ, a u) = 1 := by
    simp [a, UnitsInt.univ]
    ring
  have ha_sign : (∑ u : ℤˣ, a u * (((u : ℤˣ) : ℤ) : ℝ)) = mu := by
    simp [a, UnitsInt.univ]
    ring
  have ha_center : (∑ u : ℤˣ, a u * ((((u : ℤˣ) : ℤ) : ℝ) - mu)) = 0 := by
    simp [a, UnitsInt.univ]
    ring
  have ha_center_sq :
      (∑ u : ℤˣ, a u * ((((u : ℤˣ) : ℤ) : ℝ) - mu) ^ 2) = 1 - mu ^ 2 := by
    simp [a, UnitsInt.univ]
    ring

  have hfactor (g : Fin k → ℤˣ → ℝ) :
      E (fun eta => ∏ i, g i (eta i)) =
        ∏ i, ∑ u : ℤˣ, a u * g i u := by
    dsimp only [E]
    simp_rw [signPairWeight, a, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum fun i u =>
      (1 + mu * (((u : ℤˣ) : ℤ) : ℝ)) / 2 * g i u).symm

  have hE_sum {ι : Type} [Fintype ι] (f : ι → (Fin k → ℤˣ) → ℝ) :
      E (fun eta => ∑ i, f i eta) = ∑ i, E (f i) := by
    dsimp only [E]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]

  have hE_add (f g : (Fin k → ℤˣ) → ℝ) :
      E (fun eta => f eta + g eta) = E f + E g := by
    dsimp only [E]
    simp_rw [mul_add, Finset.sum_add_distrib]
  have hE_sub (f g : (Fin k → ℤˣ) → ℝ) :
      E (fun eta => f eta - g eta) = E f - E g := by
    dsimp only [E]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hE_const_mul (c : ℝ) (f : (Fin k → ℤˣ) → ℝ) :
      E (fun eta => c * f eta) = c * E f := by
    dsimp only [E]
    simp_rw [mul_left_comm (signPairWeight mu _) c, ← Finset.mul_sum]
  have hE_congr {f g : (Fin k → ℤˣ) → ℝ} (h : ∀ eta, f eta = g eta) : E f = E g := by
    dsimp only [E]
    exact Finset.sum_congr rfl fun eta _ => by rw [h eta]

  have hfactor_finset (S : Finset (Fin k)) (g : Fin k → ℤˣ → ℝ) :
      E (fun eta => ∏ i ∈ S, g i (eta i)) =
        ∏ i ∈ S, ∑ u : ℤˣ, a u * g i u := by
    calc
      E (fun eta => ∏ i ∈ S, g i (eta i)) =
          E (fun eta => ∏ i, if i ∈ S then g i (eta i) else 1) := by
            congr 1
            funext eta
            rw [Fintype.prod_ite_mem]
      _ = ∏ i, ∑ u : ℤˣ, a u * (if i ∈ S then g i u else 1) :=
        hfactor (fun i u => if i ∈ S then g i u else 1)
      _ = ∏ i, if i ∈ S then (∑ u : ℤˣ, a u * g i u) else 1 := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · simp [hi]
        · simp only [hi, if_false, mul_one]
          exact ha_zero
      _ = ∏ i ∈ S, ∑ u : ℤˣ, a u * g i u := by
        rw [Fintype.prod_ite_mem]

  have hcharacter (S : Finset (Fin k)) :
      E (fun eta => ∏ i ∈ S, x eta i) = mu ^ S.card := by
    rw [hfactor_finset S (fun _ u => (((u : ℤˣ) : ℤ) : ℝ))]
    simp_rw [ha_sign]
    simp

  have hsum_sq : ∀ n : ℕ, ∀ f : Fin n → ℝ,
      (∑ i, f i) ^ 2 =
        (∑ i, f i ^ 2) +
          2 * (∑ i : Fin n, ∑ j : Fin n, if i < j then f i * f j else 0) := by
    intro n
    induction n with
    | zero => intro f; simp
    | succ n ih =>
        intro f
        have hpairs :
            (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              if i < j then f i * f j else 0) =
              f 0 * (∑ j : Fin n, f j.succ) +
                ∑ i : Fin n, ∑ j : Fin n,
                  if i < j then f i.succ * f j.succ else 0 := by
          simp only [Fin.sum_univ_succ]
          simp only [lt_self_iff_false, reduceIte, Fin.succ_pos, zero_add, not_lt_zero,
            Fin.succ_lt_succ_iff, add_left_inj]
          rw [← Finset.mul_sum]
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hpairs]
        nlinarith [ih (fun i => f i.succ)]

  have hx_sq (eta : Fin k → ℤˣ) (i : Fin k) : x eta i ^ 2 = 1 := by
    dsimp only [x]
    exact_mod_cast Int.isUnit_sq (eta i).isUnit
  have hz_sq (eta : Fin k → ℤˣ) (i : Fin k) :
      z eta i ^ 2 = 1 - mu ^ 2 - 2 * mu * z eta i := by
    dsimp only [z]
    rw [sub_sq, hx_sq]
    ring

  have hpair_card :
      (Finset.filter (fun p : Fin k × Fin k => p.1 < p.2)
        (Finset.univ.product Finset.univ)).card = Nat.choose k 2 := by
    simpa using
      (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin k))))
  have hchoose_cast : (Nat.choose k 2 : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    rw [Nat.cast_choose_two]
  have hk_real : (1 : ℝ) < k := by exact_mod_cast hk
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt (lt_trans Real.zero_lt_one hk_real)
  have hk_sub_ne : (k : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hk_real)
  have hchoose_ne : (Nat.choose k 2 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hk

  have hpair_identity : ∀ eta : Fin k → ℤˣ,
      signPairUStatistic eta = pairSum (x eta) / (Nat.choose k 2 : ℝ) := by
    intro eta
    have hsquare := hsum_sq k (x eta)
    have hdiag : (∑ i : Fin k, x eta i ^ 2) = (k : ℝ) := by
      simp_rw [hx_sq]
      simp
    dsimp only [signPairUStatistic, pairSum]
    rw [hdiag] at hsquare
    rw [hchoose_cast]
    field_simp
    nlinarith

  have hpair_mean : E (fun eta => pairSum (x eta)) = (Nat.choose k 2 : ℝ) * mu ^ 2 := by
    dsimp only [pairSum]
    calc
      E (fun eta => ∑ i : Fin k, ∑ j : Fin k,
          if i < j then x eta i * x eta j else 0) =
          ∑ i : Fin k, E (fun eta => ∑ j : Fin k,
            if i < j then x eta i * x eta j else 0) :=
        hE_sum (fun i eta => ∑ j : Fin k,
          if i < j then x eta i * x eta j else 0)
      _ = ∑ i : Fin k, ∑ j : Fin k,
          E (fun eta => if i < j then x eta i * x eta j else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hE_sum (fun j eta => if i < j then x eta i * x eta j else 0)
      _ = ∑ i : Fin k, ∑ j : Fin k, if i < j then mu ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i < j
        · have hchar := hcharacter ({i, j} : Finset (Fin k))
          simpa [E, x, hij, hij.ne] using hchar
        · simp [hij, E]
      _ = (Nat.choose k 2 : ℝ) * mu ^ 2 := by
        rw [← Finset.sum_product', ← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hc :
            ((Finset.filter (fun p : Fin k × Fin k => p.1 < p.2)
              (Finset.univ ×ˢ Finset.univ)).card : ℝ) = (Nat.choose k 2 : ℝ) := by
          exact_mod_cast hpair_card
        rw [hc]

  have hmean : E signPairUStatistic = mu ^ 2 := by
    calc
      E signPairUStatistic =
          E (fun eta => (Nat.choose k 2 : ℝ)⁻¹ * pairSum (x eta)) := by
        congr 1
        funext eta
        rw [hpair_identity]
        ring
      _ = (Nat.choose k 2 : ℝ)⁻¹ * E (fun eta => pairSum (x eta)) :=
        hE_const_mul _ _
      _ = mu ^ 2 := by
        rw [hpair_mean]
        field_simp [hchoose_ne]

  have hcentered_decomposition : ∀ eta : Fin k → ℤˣ,
      signPairUStatistic eta = mu ^ 2 +
        (2 * mu / k) * (∑ i, z eta i) +
        (2 / ((k : ℝ) * ((k : ℝ) - 1))) * pairSum (z eta) := by
    intro eta
    have hsquare := hsum_sq k (z eta)
    have hzsum : (∑ i : Fin k, z eta i) =
        (∑ i : Fin k, x eta i) - (k : ℝ) * mu := by
      dsimp only [z]
      simp_rw [Finset.sum_sub_distrib]
      simp
    have hzdiag : (∑ i : Fin k, z eta i ^ 2) =
        (k : ℝ) * (1 - mu ^ 2) - 2 * mu * (∑ i, z eta i) := by
      simp_rw [hz_sq]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, Fintype.card_fin]
      rw [← Finset.mul_sum]
      ring
    have hxsum : (∑ i : Fin k, x eta i) =
        (∑ i : Fin k, z eta i) + (k : ℝ) * mu := by
      linarith [hzsum]
    dsimp only [signPairUStatistic, pairSum]
    rw [hzdiag] at hsquare
    rw [hxsum]
    field_simp [hk_ne, hk_sub_ne]
    nlinarith [hsquare]

  have hcenter_one (i : Fin k) : E (fun eta => z eta i) = 0 := by
    have hfi := hfactor_finset ({i} : Finset (Fin k))
      (fun _ u => (((u : ℤˣ) : ℤ) : ℝ) - mu)
    simp only [Finset.prod_singleton] at hfi
    rw [ha_center] at hfi
    simpa [z, x] using hfi

  have hcenter_sq_one (i : Fin k) : E (fun eta => z eta i ^ 2) = 1 - mu ^ 2 := by
    have hfi := hfactor_finset ({i} : Finset (Fin k))
      (fun _ u => ((((u : ℤˣ) : ℤ) : ℝ) - mu) ^ 2)
    simp only [Finset.prod_singleton] at hfi
    rw [ha_center_sq] at hfi
    simpa [z, x] using hfi

  have hcenter_two (i j : Fin k) (hij : i ≠ j) :
      E (fun eta => z eta i * z eta j) = 0 := by
    have hfi := hfactor_finset ({i, j} : Finset (Fin k))
      (fun _ u => (((u : ℤˣ) : ℤ) : ℝ) - mu)
    simp only [Finset.prod_insert, Finset.mem_singleton, hij, not_false_eq_true,
      Finset.prod_singleton] at hfi
    rw [ha_center] at hfi
    simpa [z, x] using hfi

  have hcenter_sq_center (i j : Fin k) (hij : i ≠ j) :
      E (fun eta => z eta i ^ 2 * z eta j) = 0 := by
    have hpoint : ∀ eta, z eta i ^ 2 * z eta j =
        (1 - mu ^ 2) * z eta j - 2 * mu * (z eta i * z eta j) := by
      intro eta
      rw [hz_sq]
      ring
    calc
      E (fun eta => z eta i ^ 2 * z eta j) =
          E (fun eta => (1 - mu ^ 2) * z eta j -
            2 * mu * (z eta i * z eta j)) := by
        congr 1
        funext eta
        exact hpoint eta
      _ = E (fun eta => (1 - mu ^ 2) * z eta j) -
          E (fun eta => 2 * mu * (z eta i * z eta j)) := hE_sub _ _
      _ = (1 - mu ^ 2) * E (fun eta => z eta j) -
          (2 * mu) * E (fun eta => z eta i * z eta j) := by
        rw [hE_const_mul, hE_const_mul]
      _ = 0 := by rw [hcenter_one, hcenter_two i j hij]; ring

  have hcenter_three (i j q : Fin k) (hij : i ≠ j) (hiq : i ≠ q) (hjq : j ≠ q) :
      E (fun eta => z eta i * z eta j * z eta q) = 0 := by
    have hfi := hfactor_finset ({i, j, q} : Finset (Fin k))
      (fun _ u => (((u : ℤˣ) : ℤ) : ℝ) - mu)
    simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton, hij, hiq,
      hjq, or_false, not_false_eq_true, Finset.prod_singleton] at hfi
    rw [ha_center] at hfi
    simpa [z, x, mul_assoc] using hfi

  have hcenter_sq_sq (i j : Fin k) (hij : i ≠ j) :
      E (fun eta => z eta i ^ 2 * z eta j ^ 2) = (1 - mu ^ 2) ^ 2 := by
    have hfi := hfactor_finset ({i, j} : Finset (Fin k))
      (fun _ u => ((((u : ℤˣ) : ℤ) : ℝ) - mu) ^ 2)
    simp only [Finset.prod_insert, Finset.mem_singleton, hij, not_false_eq_true,
      Finset.prod_singleton] at hfi
    rw [ha_center_sq] at hfi
    simpa [z, x, pow_two] using hfi

  have hcenter_sq_center_center (i j q : Fin k)
      (hij : i ≠ j) (hiq : i ≠ q) (hjq : j ≠ q) :
      E (fun eta => z eta i ^ 2 * (z eta j * z eta q)) = 0 := by
    have hpoint : ∀ eta, z eta i ^ 2 * (z eta j * z eta q) =
        (1 - mu ^ 2) * (z eta j * z eta q) -
          2 * mu * (z eta i * z eta j * z eta q) := by
      intro eta
      rw [hz_sq]
      ring
    calc
      E (fun eta => z eta i ^ 2 * (z eta j * z eta q)) =
          E (fun eta => (1 - mu ^ 2) * (z eta j * z eta q) -
            2 * mu * (z eta i * z eta j * z eta q)) := by
        congr 1
        funext eta
        exact hpoint eta
      _ = E (fun eta => (1 - mu ^ 2) * (z eta j * z eta q)) -
          E (fun eta => 2 * mu * (z eta i * z eta j * z eta q)) := hE_sub _ _
      _ = (1 - mu ^ 2) * E (fun eta => z eta j * z eta q) -
          (2 * mu) * E (fun eta => z eta i * z eta j * z eta q) := by
        rw [hE_const_mul, hE_const_mul]
      _ = 0 := by
        rw [hcenter_two j q hjq, hcenter_three i j q hij hiq hjq]
        ring

  have hcenter_four (i j p q : Fin k)
      (hij : i ≠ j) (hip : i ≠ p) (hiq : i ≠ q)
      (hjp : j ≠ p) (hjq : j ≠ q) (hpq : p ≠ q) :
      E (fun eta => z eta i * z eta j * (z eta p * z eta q)) = 0 := by
    have hfi := hfactor_finset ({i, j, p, q} : Finset (Fin k))
      (fun _ u => (((u : ℤˣ) : ℤ) : ℝ) - mu)
    simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton, hij, hip,
      hiq, hjp, hjq, hpq, or_false, not_false_eq_true, Finset.prod_singleton] at hfi
    rw [ha_center] at hfi
    simpa [z, x, mul_assoc] using hfi

  have hlinear_second : E (fun eta => (∑ i, z eta i) ^ 2) =
      (k : ℝ) * (1 - mu ^ 2) := by
    have hexpand : E (fun eta => (∑ i, z eta i) ^ 2) =
        E (fun eta => ∑ i : Fin k, ∑ j : Fin k, z eta i * z eta j) := by
      congr 1
      funext eta
      rw [pow_two, Finset.sum_mul_sum]
    rw [hexpand]
    calc
      E (fun eta => ∑ i : Fin k, ∑ j : Fin k, z eta i * z eta j) =
          ∑ i : Fin k, E (fun eta => ∑ j : Fin k, z eta i * z eta j) :=
        hE_sum (fun i eta => ∑ j : Fin k, z eta i * z eta j)
      _ = ∑ i : Fin k, ∑ j : Fin k, E (fun eta => z eta i * z eta j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hE_sum (fun j eta => z eta i * z eta j)
      _ = ∑ i : Fin k, ∑ j : Fin k,
          if i = j then 1 - mu ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j
        · subst j
          simpa [pow_two] using hcenter_sq_one i
        · simpa [hij] using hcenter_two i j hij
      _ = (k : ℝ) * (1 - mu ^ 2) := by simp; ring

  have hcross_term : E (fun eta =>
      (∑ i, z eta i) * pairSum (z eta)) = 0 := by
    have hpoint : ∀ eta : Fin k → ℤˣ,
        (∑ r : Fin k, z eta r) * pairSum (z eta) =
          ∑ r : Fin k, ∑ i : Fin k, ∑ j : Fin k,
            if i < j then z eta r * (z eta i * z eta j) else 0 := by
      intro eta
      dsimp only [pairSum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i < j <;> simp [hij]
    rw [show E (fun eta => (∑ i, z eta i) * pairSum (z eta)) =
        E (fun eta => ∑ r : Fin k, ∑ i : Fin k, ∑ j : Fin k,
          if i < j then z eta r * (z eta i * z eta j) else 0) by
      congr 1
      funext eta
      exact hpoint eta]
    rw [hE_sum (fun r eta => ∑ i : Fin k, ∑ j : Fin k,
      if i < j then z eta r * (z eta i * z eta j) else 0)]
    apply Finset.sum_eq_zero
    intro r _
    rw [hE_sum (fun i eta => ∑ j : Fin k,
      if i < j then z eta r * (z eta i * z eta j) else 0)]
    apply Finset.sum_eq_zero
    intro i _
    rw [hE_sum (fun j eta =>
      if i < j then z eta r * (z eta i * z eta j) else 0)]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hij : i < j
    · simp only [hij, if_true]
      by_cases hri : r = i
      · subst r
        calc
          E (fun eta => z eta i * (z eta i * z eta j)) =
              E (fun eta => z eta i ^ 2 * z eta j) := hE_congr (by intro eta; ring)
          _ = 0 := hcenter_sq_center i j hij.ne
      · by_cases hrj : r = j
        · subst r
          calc
            E (fun eta => z eta j * (z eta i * z eta j)) =
                E (fun eta => z eta j ^ 2 * z eta i) := hE_congr (by intro eta; ring)
            _ = 0 := hcenter_sq_center j i (Ne.symm hij.ne)
        · calc
            E (fun eta => z eta r * (z eta i * z eta j)) =
                E (fun eta => z eta r * z eta i * z eta j) :=
              hE_congr (by intro eta; ring)
            _ = 0 := hcenter_three r i j hri hrj hij.ne
    · simp [hij, E]

  have hpair_second : E (fun eta => pairSum (z eta) ^ 2) =
      (Nat.choose k 2 : ℝ) * (1 - mu ^ 2) ^ 2 := by
    dsimp only [pairSum]
    have hfour : ∀ i j p q : Fin k, i < j → p < q →
        E (fun eta => z eta i * z eta j * (z eta p * z eta q)) =
          if i = p ∧ j = q then (1 - mu ^ 2) ^ 2 else 0 := by
      intro i j p q hij hpq
      by_cases hip : i = p
      · subst p
        by_cases hjq : j = q
        · subst q
          rw [if_pos ⟨rfl, rfl⟩]
          calc
            E (fun eta => z eta i * z eta j * (z eta i * z eta j)) =
                E (fun eta => z eta i ^ 2 * z eta j ^ 2) :=
              hE_congr (by intro eta; ring)
            _ = (1 - mu ^ 2) ^ 2 := hcenter_sq_sq i j hij.ne
        · rw [if_neg (by simp [hjq])]
          have hiq : i ≠ q := hpq.ne
          calc
            E (fun eta => z eta i * z eta j * (z eta i * z eta q)) =
                E (fun eta => z eta i ^ 2 * (z eta j * z eta q)) :=
              hE_congr (by intro eta; ring)
            _ = 0 := hcenter_sq_center_center i j q hij.ne hiq hjq
      · by_cases hjp : j = p
        · subst p
          rw [if_neg (by simp [hip])]
          have hiq : i ≠ q := by omega
          have hjq : j ≠ q := hpq.ne
          calc
            E (fun eta => z eta i * z eta j * (z eta j * z eta q)) =
                E (fun eta => z eta j ^ 2 * (z eta i * z eta q)) :=
              hE_congr (by intro eta; ring)
            _ = 0 := hcenter_sq_center_center j i q (Ne.symm hij.ne) hjq hiq
        · by_cases hiq : i = q
          · subst q
            rw [if_neg (by simp [hip])]
            have hip' : i ≠ p := Ne.symm hpq.ne
            calc
              E (fun eta => z eta i * z eta j * (z eta p * z eta i)) =
                  E (fun eta => z eta i ^ 2 * (z eta j * z eta p)) :=
                hE_congr (by intro eta; ring)
              _ = 0 := hcenter_sq_center_center i j p hij.ne hip' hjp
          · by_cases hjq : j = q
            · subst q
              rw [if_neg (by simp [hip])]
              have hjp' : j ≠ p := Ne.symm hpq.ne
              calc
                E (fun eta => z eta i * z eta j * (z eta p * z eta j)) =
                    E (fun eta => z eta j ^ 2 * (z eta i * z eta p)) :=
                  hE_congr (by intro eta; ring)
                _ = 0 := hcenter_sq_center_center j i p (Ne.symm hij.ne) hjp' hip
            · rw [if_neg (by simp [hip])]
              exact hcenter_four i j p q hij.ne hip hiq hjp hjq hpq.ne
    have hpoint : ∀ eta,
        (∑ i : Fin k, ∑ j : Fin k,
          if i < j then z eta i * z eta j else 0) ^ 2 =
        ∑ i : Fin k, ∑ p : Fin k, ∑ j : Fin k, ∑ q : Fin k,
          if i < j ∧ p < q then z eta i * z eta j * (z eta p * z eta q) else 0 := by
      intro eta
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      by_cases hij : i < j <;> by_cases hpq : p < q <;> simp [hij, hpq]
    rw [show E (fun eta =>
        (∑ i : Fin k, ∑ j : Fin k, if i < j then z eta i * z eta j else 0) ^ 2) =
        E (fun eta => ∑ i : Fin k, ∑ p : Fin k, ∑ j : Fin k, ∑ q : Fin k,
          if i < j ∧ p < q then z eta i * z eta j * (z eta p * z eta q) else 0) by
      congr 1
      funext eta
      exact hpoint eta]
    rw [hE_sum (fun i eta => ∑ p : Fin k, ∑ j : Fin k, ∑ q : Fin k,
      if i < j ∧ p < q then z eta i * z eta j * (z eta p * z eta q) else 0)]
    apply Eq.trans ?_ (show
      (∑ i : Fin k, ∑ p : Fin k, ∑ j : Fin k, ∑ q : Fin k,
        if i < j ∧ p < q ∧ i = p ∧ j = q then (1 - mu ^ 2) ^ 2 else 0) =
        (Nat.choose k 2 : ℝ) * (1 - mu ^ 2) ^ 2 by
          calc
            (∑ i : Fin k, ∑ p : Fin k, ∑ j : Fin k, ∑ q : Fin k,
              if i < j ∧ p < q ∧ i = p ∧ j = q then
                (1 - mu ^ 2) ^ 2 else 0) =
                ∑ i : Fin k, ∑ j : Fin k,
                  if i < j then (1 - mu ^ 2) ^ 2 else 0 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro j _
              by_cases hij : i < j
              · have hcond : ∀ p q : Fin k,
                    (p < q ∧ i = p ∧ j = q) ↔ (p = i ∧ q = j) := by
                  intro p q
                  constructor
                  · rintro ⟨_, rfl, rfl⟩
                    exact ⟨rfl, rfl⟩
                  · rintro ⟨rfl, rfl⟩
                    exact ⟨hij, rfl, rfl⟩
                simp only [hij, true_and]
                simp_rw [hcond]
                rw [Finset.sum_eq_single i]
                · rw [Finset.sum_eq_single j]
                  · simp
                  · intro q _ hq
                    simp [hq]
                  · simp
                · intro p _ hp
                  simp [hp]
                · simp
              · simp [hij]
            _ = (Nat.choose k 2 : ℝ) * (1 - mu ^ 2) ^ 2 := by
              rw [← Finset.sum_product', ← Finset.sum_filter]
              simp only [Finset.sum_const, nsmul_eq_mul]
              have hc :
                  ((Finset.filter (fun p : Fin k × Fin k => p.1 < p.2)
                    (Finset.univ ×ˢ Finset.univ)).card : ℝ) =
                      (Nat.choose k 2 : ℝ) := by
                exact_mod_cast hpair_card
              rw [hc])
    apply Finset.sum_congr rfl
    intro i _
    rw [hE_sum (fun p eta => ∑ j : Fin k, ∑ q : Fin k,
      if i < j ∧ p < q then z eta i * z eta j * (z eta p * z eta q) else 0)]
    apply Finset.sum_congr rfl
    intro p _
    rw [hE_sum (fun j eta => ∑ q : Fin k,
      if i < j ∧ p < q then z eta i * z eta j * (z eta p * z eta q) else 0)]
    apply Finset.sum_congr rfl
    intro j _
    rw [hE_sum (fun q eta =>
      if i < j ∧ p < q then z eta i * z eta j * (z eta p * z eta q) else 0)]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hij : i < j
    · by_cases hpq : p < q
      · simpa [hij, hpq] using hfour i j p q hij hpq
      · simp [hpq, E]
    · simp [hij, E]

  have hvariance_centered :
      E (fun eta => (signPairUStatistic eta - mu ^ 2) ^ 2) =
        4 * mu ^ 2 * (1 - mu ^ 2) / k +
          2 * (1 - mu ^ 2) ^ 2 / ((k : ℝ) * ((k : ℝ) - 1)) := by
    have hpoint : ∀ eta,
        (signPairUStatistic eta - mu ^ 2) ^ 2 =
          (2 * mu / k) ^ 2 * (∑ i, z eta i) ^ 2 +
          2 * (2 * mu / k) * (2 / ((k : ℝ) * ((k : ℝ) - 1))) *
            ((∑ i, z eta i) * pairSum (z eta)) +
          (2 / ((k : ℝ) * ((k : ℝ) - 1))) ^ 2 * pairSum (z eta) ^ 2 := by
      intro eta
      rw [hcentered_decomposition]
      ring
    rw [show E (fun eta => (signPairUStatistic eta - mu ^ 2) ^ 2) =
        E (fun eta =>
          (2 * mu / k) ^ 2 * (∑ i, z eta i) ^ 2 +
          2 * (2 * mu / k) * (2 / ((k : ℝ) * ((k : ℝ) - 1))) *
            ((∑ i, z eta i) * pairSum (z eta)) +
          (2 / ((k : ℝ) * ((k : ℝ) - 1))) ^ 2 * pairSum (z eta) ^ 2) by
      congr 1
      funext eta
      exact hpoint eta]
    rw [hE_add, hE_add, hE_const_mul, hE_const_mul, hE_const_mul]
    rw [hlinear_second, hcross_term, hpair_second, mul_zero, add_zero, hchoose_cast]
    field_simp
    ring

  refine ⟨hpair_identity, hmean, ?_⟩
  change E (fun eta => signPairUStatistic eta ^ 2) - E signPairUStatistic ^ 2 = _
  rw [hmean]
  have hcentered := hvariance_centered
  have hnormalize : E (fun _ => (1 : ℝ)) = 1 := by
    calc
      E (fun _ => (1 : ℝ)) = ∏ _ : Fin k, ∑ u : ℤˣ, a u := by
        simpa using hfactor (fun _ _ => (1 : ℝ))
      _ = (∑ u : ℤˣ, a u) ^ k := by simp
      _ = 1 := by rw [ha_zero]; simp
  have hsecond_center : E (fun eta => (signPairUStatistic eta - mu ^ 2) ^ 2) =
      E (fun eta => signPairUStatistic eta ^ 2) - mu ^ 4 := by
    have hpoint : ∀ eta : Fin k → ℤˣ,
        (signPairUStatistic eta - mu ^ 2) ^ 2 =
          signPairUStatistic eta ^ 2 -
            (2 * mu ^ 2) * signPairUStatistic eta + mu ^ 4 * 1 := by
      intro eta
      ring
    rw [show E (fun eta => (signPairUStatistic eta - mu ^ 2) ^ 2) =
        E (fun eta => signPairUStatistic eta ^ 2 -
          (2 * mu ^ 2) * signPairUStatistic eta + mu ^ 4 * 1) by
      congr 1
      funext eta
      exact hpoint eta]
    rw [hE_add, hE_sub, hE_const_mul, hE_const_mul, hmean, hnormalize]
    ring
  rw [hsecond_center] at hcentered
  nlinarith

#print axioms sign_pair_u_statistic_moments

end D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments
