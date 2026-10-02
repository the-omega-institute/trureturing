/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalGroundSeries
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalGroundSeries
   mirror-E: none(waiver:royal-ground-series-bridge)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: Derives the Royal series bridge from weighted Dyck recurrences. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalAugCount
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalDownSeries
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalGroundSeries

open DyckStep NonnestingBasicRoyalGround NonnestingBasicRoyalDownRuns NonnestingBasicRoyalDownCount
  NonnestingBasicRoyalGroundCount NonnestingBasicRoyalAugCount PowerSeries
  NonnestingBasicRoyalDownSeries
theorem groundSeries_bridge :
    let groundSeries : PowerSeries ℤ :=
      PowerSeries.mk fun n => (groundWeight n : ℤ)
    let downSeries : PowerSeries ℤ :=
      PowerSeries.mk fun n => (downWeight n : ℤ)
    (1 - 2 * X * downSeries) * groundSeries = 1 - X := by
  classical
  let SplitPairs (n : ℕ) : Type :=
    {uv : DyckWord × DyckWord // uv.1.semilength + uv.2.semilength = n}
  let augmentedSeries : PowerSeries ℤ :=
    PowerSeries.mk fun n => (augmentedWeight n : ℤ)
  let groundSeries : PowerSeries ℤ :=
    PowerSeries.mk fun n => (groundWeight n : ℤ)
  let downSeries : PowerSeries ℤ :=
    PowerSeries.mk fun n => (downWeight n : ℤ)
  letI (n : ℕ) : Fintype (SplitPairs n) := by
    let T := Σ i : Fin (n + 1),
      {u : DyckWord // u.semilength = i.val} ×
        {v : DyckWord // v.semilength = n - i.val}
    let f : SplitPairs n → T := fun x => by
      have hi : x.1.1.semilength < n + 1 := by
        have h := x.2; omega
      exact ⟨⟨x.1.1.semilength, hi⟩,
        ⟨⟨x.1.1, rfl⟩, ⟨x.1.2, by
          change x.1.2.semilength = n - x.1.1.semilength; have h := x.2
          omega⟩⟩⟩
    have hf : Function.Injective f := by
      intro x y h; apply Subtype.ext; apply Prod.ext
      · exact congrArg (fun z : T => z.2.1.1) h
      · exact congrArg (fun z : T => z.2.2.1) h
    letI : Finite (SplitPairs n) := Finite.of_injective f hf
    exact Fintype.ofFinite (SplitPairs n)
  have downPairs_append (s t : List DyckStep) :
      downPairs (s ++ t) = downPairs s + downPairs t +
        if s.getLast? = some D ∧ t.head? = some D then 1 else 0 := by
    induction s with
    | nil => simp [downPairs]
    | cons a s ih =>
      cases s with
      | nil =>
        cases t with
        | nil => cases a <;> simp [downPairs]
        | cons b t =>
          cases a <;> cases b <;> simp [downPairs] <;> omega
      | cons b s =>
        change (if a = D ∧ b = D then 1 else 0) + downPairs ((b :: s) ++ t) =
          ((if a = D ∧ b = D then 1 else 0) + downPairs (b :: s)) + downPairs t +
            if (a :: b :: s).getLast? = some D ∧ t.head? = some D then 1 else 0
        rw [ih]; have hlast : (a :: b :: s).getLast? = (b :: s).getLast? := rfl; rw [hlast]; omega
  have downPairs_dyck_add (p q : DyckWord) :
      downPairs (p + q).toList = downPairs p.toList + downPairs q.toList := by
    rw [show (p + q).toList = p.toList ++ q.toList from rfl, downPairs_append]
    by_cases hp : p = 0
    · subst p
      simp [show (0 : DyckWord).toList = [] from rfl, downPairs]
    by_cases hq : q = 0
    · subst q
      simp [show (0 : DyckWord).toList = [] from rfl, downPairs]
    have hhead : q.toList.head? = some U := by
      rw [List.head?_eq_some_head (DyckWord.toList_ne_nil.mpr hq)]
      exact congrArg some (DyckWord.head_eq_U q (DyckWord.toList_ne_nil.mpr hq))
    simp [hhead]
  have downPairs_nest (p : DyckWord) :
      downPairs p.nest.toList = downPairs p.toList + if p = 0 then 0 else 1 := by
    rw [show p.nest.toList = [U] ++ p.toList ++ [D] from rfl]
    by_cases hp : p = 0
    · subst p
      simp [show (0 : DyckWord).toList = [] from rfl, downPairs]
    have hfirst : downPairs (U :: (p.toList ++ [D])) =
        downPairs (p.toList ++ [D]) := by
      cases hlist : p.toList with
      | nil => exact False.elim ((DyckWord.toList_ne_nil.mpr hp) hlist)
      | cons s t =>
        have hs : s = U := by
          simpa [hlist] using
            (DyckWord.head_eq_U p (DyckWord.toList_ne_nil.mpr hp))
        subst s; simp [downPairs]
    rw [show [U] ++ p.toList ++ [D] = U :: (p.toList ++ [D]) from rfl, hfirst]
    rw [downPairs_append]
    have hlast : p.toList.getLast? = some D := by
      rw [List.getLast?_eq_getLast_of_ne_nil (DyckWord.toList_ne_nil.mpr hp)]
      exact congrArg some (DyckWord.getLast_eq_D p (DyckWord.toList_ne_nil.mpr hp))
    simp [downPairs, hlast, hp]
  have groundSingletons_add (p q : DyckWord) (hp : p ≠ 0) :
      groundSingletons (p + q) = groundSingletons p + groundSingletons q +
        if q ≠ 0 ∧ q.insidePart = 0 then 1 else 0 := by
    suffices h : ∀ n (p q : DyckWord), p.semilength = n → p ≠ 0 →
        groundSingletons (p + q) = groundSingletons p + groundSingletons q +
          if q ≠ 0 ∧ q.insidePart = 0 then 1 else 0 from
      h p.semilength p q rfl hp
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p q hn hp
      have hpq : p + q ≠ 0 := by
        intro heq; have hl : p.toList ++ q.toList = [] := congrArg DyckWord.toList heq
        exact hp (DyckWord.toList_eq_nil.mp (List.append_eq_nil_iff.mp hl).1)
      have hleft : groundSingletons p = groundSingletons p.outsidePart +
          (if p.outsidePart ≠ 0 ∧ p.outsidePart.insidePart = 0 then 1 else 0) := by
        rw [groundSingletons, dif_neg hp]
      have hright : groundSingletons (p + q) =
          groundSingletons (p.outsidePart + q) +
            (if p.outsidePart + q ≠ 0 ∧ (p.outsidePart + q).insidePart = 0
              then 1 else 0) := by
        rw [groundSingletons, dif_neg hpq, p.outsidePart_add hp]
      by_cases ha : p.outsidePart = 0
      · have hq : p.outsidePart + q = q := by simp [ha]
        rw [hleft, hright]
        have hzero : groundSingletons 0 = 0 := by rw [groundSingletons]; simp
        simp [ha, hzero]
      · have hsmall : p.outsidePart.semilength < n := by
          rw [← hn]; exact p.semilength_outsidePart_lt hp
        have hrec := ih p.outsidePart.semilength hsmall p.outsidePart q rfl ha
        have haq : p.outsidePart + q ≠ 0 := by
          intro heq; have hl : p.outsidePart.toList ++ q.toList = [] :=
            congrArg DyckWord.toList heq
          exact ha (DyckWord.toList_eq_nil.mp (List.append_eq_nil_iff.mp hl).1)
        rw [hright, hleft, hrec, DyckWord.insidePart_add ha]
        simp only [ha, haq, ne_eq, not_false_eq_true, true_and]; omega
  have groundWeight_first_return (n : ℕ) :
      groundWeight (n + 1) =
        ∑ x : SplitPairs n,
          (if x.1.1 = 0 then 1 else 2) *
            2 ^ downPairs x.1.1.toList *
            2 ^ (downPairs x.1.2.toList + groundSingletons x.1.2) *
            (if x.1.2 ≠ 0 ∧ x.1.2.insidePart = 0 then 2 else 1) := by
    let S := {d : DyckWord // d.semilength = n + 1}; let e : S ≃ SplitPairs n :=
      { toFun := fun d => by
          have hd : d.1 ≠ 0 := by
            intro h; have hn := d.2; simp [h] at hn
          have hlen := d.1.semilength_insidePart_add_semilength_outsidePart_add_one hd
          exact ⟨(d.1.insidePart, d.1.outsidePart), by
            change d.1.insidePart.semilength + d.1.outsidePart.semilength = n; rw [d.2] at hlen
            omega⟩
        invFun := fun x =>
          ⟨x.1.1.nest + x.1.2, by
            simp only [DyckWord.semilength_add, DyckWord.semilength_nest]; have h := x.2
            omega⟩
        left_inv := by
          intro d; apply Subtype.ext
          have hd : d.1 ≠ 0 := by
            intro h; have hn := d.2; simp [h] at hn
          exact d.1.nest_insidePart_add_outsidePart hd
        right_inv := by
          intro x; apply Subtype.ext
          apply Prod.ext <;> simp }
    change (∑ d : S, 2 ^ (downPairs d.1.toList + groundSingletons d.1)) = _
    rw [← Equiv.sum_comp e.symm
      (fun d : S => 2 ^ (downPairs d.1.toList + groundSingletons d.1))]
    apply Fintype.sum_congr; intro x
    change 2 ^ (downPairs (x.1.1.nest + x.1.2).toList +
      groundSingletons (x.1.1.nest + x.1.2)) = _
    have hn : groundSingletons x.1.1.nest = 0 := by
      rw [groundSingletons, dif_neg (DyckWord.nest_ne_zero)]; simp [groundSingletons]
    rw [downPairs_dyck_add, downPairs_nest,
      groundSingletons_add _ _ (DyckWord.nest_ne_zero), hn]
    by_cases hu : x.1.1 = 0
    · by_cases hv : x.1.2 ≠ 0 ∧ x.1.2.insidePart = 0
      · simp [hu, hv, pow_add, pow_succ]; ring
      · simp [hu, hv, pow_add]; ring
    · by_cases hv : x.1.2 ≠ 0 ∧ x.1.2.insidePart = 0
      · simp [hu, hv, pow_add, pow_succ]; ring
      · simp [hu, hv, pow_add, pow_succ]; ring
  have groundWeight_convolution (n : ℕ) :
      groundWeight (n + 1) =
        ∑ i : Fin (n + 1), (if i.val = 0 then 1 else 2) *
          downWeight i.val * augmentedWeight (n - i.val) := by
    let f : SplitPairs n → Fin (n + 1) := fun x =>
      ⟨x.1.1.semilength, by have h := x.2; omega⟩
    let fiber (i : Fin (n + 1)) := {x : SplitPairs n // f x = i}
    letI (i : Fin (n + 1)) : Fintype (fiber i) := Fintype.ofFinite (fiber i)
    let weight : SplitPairs n → ℕ := fun x =>
      (if x.1.1 = 0 then 1 else 2) *
        2 ^ downPairs x.1.1.toList *
        2 ^ (downPairs x.1.2.toList + groundSingletons x.1.2) *
        (if x.1.2 ≠ 0 ∧ x.1.2.insidePart = 0 then 2 else 1)
    have hzero (p : DyckWord) : p = 0 ↔ p.semilength = 0 := by
      constructor
      · intro h
        simp [h]
      · intro h
        have hl := p.two_mul_semilength_eq_length
        rw [h] at hl; apply DyckWord.toList_eq_nil.mp; exact List.length_eq_zero_iff.mp (by omega)
    have hfiber (i : Fin (n + 1)) :
        (∑ x : fiber i, weight x.1) =
          (if i.val = 0 then 1 else 2) *
            downWeight i.val * augmentedWeight (n - i.val) := by
      let U := {u : DyckWord // u.semilength = i.val}
      let V := {v : DyckWord // v.semilength = n - i.val}; let e : fiber i ≃ U × V :=
        { toFun := fun x =>
            (⟨x.1.1.1, by
              have h := congrArg Fin.val x.2
              exact h⟩,
              ⟨x.1.1.2, by
                have h := congrArg Fin.val x.2; change x.1.1.1.semilength = i.val at h
                have hs := x.1.2; change x.1.1.1.semilength + x.1.1.2.semilength = n at hs
                omega⟩)
          invFun := fun uv =>
            ⟨⟨(uv.1.1, uv.2.1), by
              change uv.1.1.semilength + uv.2.1.semilength = n; have hu := uv.1.2; have hv := uv.2.2
              omega⟩, by
              apply Fin.ext; exact uv.1.2⟩
          left_inv := by
            intro x; apply Subtype.ext; apply Subtype.ext; rfl
          right_inv := by
            intro uv
            apply Prod.ext <;> apply Subtype.ext <;> rfl }
      rw [← Equiv.sum_comp e.symm (fun x : fiber i => weight x.1)]
      change (∑ uv : U × V,
        (if uv.1.1 = 0 then 1 else 2) *
          2 ^ downPairs uv.1.1.toList *
          2 ^ (downPairs uv.2.1.toList + groundSingletons uv.2.1) *
          (if uv.2.1 ≠ 0 ∧ uv.2.1.insidePart = 0 then 2 else 1)) = _
      rw [Fintype.sum_prod_type]
      have hiff (u : U) : u.1 = 0 ↔ i.val = 0 := by
        rw [hzero u.1, u.2]
      simp_rw [hiff]
      simp only [downWeight, augmentedWeight, Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
      simp only [mul_assoc]; rfl
    rw [groundWeight_first_return]; change (∑ x : SplitPairs n, weight x) = _
    rw [← Equiv.sum_comp (Equiv.sigmaFiberEquiv f)
      (fun x : SplitPairs n => weight x)]
    rw [Fintype.sum_sigma]; exact Fintype.sum_congr _ _ hfiber
  have augmentedWeight_succ (n : ℕ) :
      augmentedWeight (n + 1) = groundWeight (n + 1) + augmentedWeight n := by
    let S := {d : DyckWord // d.semilength = n + 1}; let T := {d : S // d.1.insidePart = 0}
    let U := {q : DyckWord // q.semilength = n}; let e : T ≃ U :=
      { toFun := fun d => ⟨d.1.1.outsidePart, by
            have hd : d.1.1 ≠ 0 := by
              intro h; have hn := d.1.2; simp [h] at hn
            have hlen := d.1.1.semilength_insidePart_add_semilength_outsidePart_add_one hd
            rw [d.2] at hlen
            simpa [d.1.2] using hlen⟩
        invFun := fun q =>
          ⟨⟨(0 : DyckWord).nest + q.1, by
            simp only [DyckWord.semilength_add, DyckWord.semilength_nest,
              DyckWord.semilength_zero]
            omega⟩, by simp⟩
        left_inv := by
          intro d; apply Subtype.ext; apply Subtype.ext
          have hd : d.1.1 ≠ 0 := by
            intro h; have hn := d.1.2; simp [h] at hn
          simpa [d.2] using d.1.1.nest_insidePart_add_outsidePart hd
        right_inv := by
          intro q; apply Subtype.ext
          simp }
    have hnonzero (d : S) : d.1 ≠ 0 := by
      intro h; have hn := d.2; simp [h] at hn
    have hsplit : augmentedWeight (n + 1) = groundWeight (n + 1) +
        ∑ d : S, if d.1.insidePart = 0 then
          2 ^ (downPairs d.1.toList + groundSingletons d.1) else 0 := by
      simp only [augmentedWeight, groundWeight]; rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro d hd
      by_cases h : d.1.insidePart = 0
      · simp [h, hnonzero d]; ring
      · simp [h]
    rw [hsplit]; congr 1
    have hsum : (∑ d : S, if d.1.insidePart = 0 then
          2 ^ (downPairs d.1.toList + groundSingletons d.1) else 0) =
        ∑ d : T, 2 ^ (downPairs d.1.1.toList + groundSingletons d.1.1) := by
      rw [← Finset.sum_filter]
      simpa only [Finset.subtype_univ] using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset S))
          (p := fun d : S => d.1.insidePart = 0)
          (fun d : S => 2 ^ (downPairs d.1.toList + groundSingletons d.1))).symm
    rw [hsum, ← Equiv.sum_comp e.symm
      (fun d : T => 2 ^ (downPairs d.1.1.toList + groundSingletons d.1.1))]
    apply Fintype.sum_congr; intro q
    change 2 ^ (downPairs ((0 : DyckWord).nest + q.1).toList +
        groundSingletons ((0 : DyckWord).nest + q.1)) = _
    have hground : groundSingletons (0 : DyckWord).nest = 0 := by
      rw [groundSingletons, dif_neg (DyckWord.nest_ne_zero)]; simp [groundSingletons]
    rw [downPairs_dyck_add, downPairs_nest,
      groundSingletons_add _ _ (DyckWord.nest_ne_zero), hground]
    simp only [downPairs, if_true, pow_add]
    by_cases h : q.1 ≠ 0 ∧ q.1.insidePart = 0
    · simp [h, pow_succ]; ring
    · simp [h]
  let A : PowerSeries ℤ := downSeries; let B : PowerSeries ℤ := groundSeries
  let C : PowerSeries ℤ := augmentedSeries; let Q : PowerSeries ℤ := 2 * A - 1
  have hzero : groundWeight 0 = 1 ∧ augmentedWeight 0 = 1 ∧ downWeight 0 = 1 := by
    haveI : Unique {d : DyckWord // d.semilength = 0} :=
      ⟨⟨0, rfl⟩, by
        intro d; apply Subtype.ext; have hl := d.1.two_mul_semilength_eq_length
        rw [d.2] at hl; apply DyckWord.toList_eq_nil.mp
        exact List.length_eq_zero_iff.mp (by omega)⟩
    have hd : (default : {d : DyckWord // d.semilength = 0}).1 = 0 := by
      have h := Subsingleton.elim
        (default : {d : DyckWord // d.semilength = 0})
        (⟨0, rfl⟩ : {d : DyckWord // d.semilength = 0})
      exact congrArg Subtype.val h
    have hgs0 : groundSingletons 0 = 0 := by rw [groundSingletons]; simp
    simp [groundWeight, augmentedWeight, downWeight, hd, downPairs, hgs0]
  have hcoeffQ (k : ℕ) : coeff k Q =
      (if k = 0 then (1 : ℤ) else 2 * (downWeight k : ℤ)) := by
    have htwo : (2 : PowerSeries ℤ) = PowerSeries.C 2 := by norm_num
    change coeff k ((2 : PowerSeries ℤ) * A - 1) = _; rw [htwo, map_sub, coeff_C_mul, coeff_one]
    simp only [A, downSeries, coeff_mk]
    by_cases hk : k = 0
    · subst k
      simp [hzero.2.2]
    · simp [hk]
  have hconv (k : ℕ) :
      coeff k (Q * C) =
        ∑ i : Fin (k + 1),
          (if i.val = 0 then (1 : ℤ) else 2) *
            (downWeight i.val : ℤ) *
            (augmentedWeight (k - i.val) : ℤ) := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Finset.sum_fin_eq_sum_range]; apply Finset.sum_congr rfl; intro i hi
    by_cases hz : i = 0
    · subst i
      simp [Q, C, A, augmentedSeries, hcoeffQ, hzero.2.2]
    · simp [Q, C, A, augmentedSeries, hcoeffQ, hz, Finset.mem_range.mp hi]
  have hB0 : coeff 0 B = 1 := by simp [B, groundSeries, hzero.1]
  have hC0 : coeff 0 C = 1 := by simp [C, augmentedSeries, hzero.2.1]
  have hBC : B = 1 + X * (Q * C) := by
    apply PowerSeries.ext; intro n
    cases n with
    | zero =>
      rw [map_add, coeff_one, coeff_zero_X_mul]; simp [hB0]
    | succ k =>
      have hz : (groundWeight (k + 1) : ℤ) =
          ∑ i : Fin (k + 1),
            (if i.val = 0 then (1 : ℤ) else 2) *
              (downWeight i.val : ℤ) *
              (augmentedWeight (k - i.val) : ℤ) := by
        exact_mod_cast groundWeight_convolution k
      simp only [map_add, PowerSeries.coeff_succ_X_mul, coeff_one,
        Nat.succ_ne_zero, if_false, zero_add]
      simp only [B, groundSeries, coeff_mk]; rw [hconv, hz]
  have hCB : C = B + X * C := by
    apply PowerSeries.ext; intro n
    cases n with
    | zero =>
      rw [map_add, coeff_zero_X_mul]; simp [hB0, hC0]
    | succ k =>
      simp only [map_add, PowerSeries.coeff_succ_X_mul]
      simp only [B, C, groundSeries, augmentedSeries, coeff_mk]
      exact_mod_cast augmentedWeight_succ k
  have hQ : Q = 2 * A - 1 := rfl
  have hA : B = 1 + X * (2 * A - 1) * C := by simpa [hQ, mul_assoc] using hBC
  have hC : C = B + X * C := hCB
  have hdiff : C - X * C = B := by
    calc
      C - X * C = (B + X * C) - X * C := by
        nth_rewrite 1 [hC]
        rfl
      _ = B := by ring
  have hbase : (1 - 2 * X * A) * C = 1 := by
    calc
      (1 - 2 * X * A) * C = C - X * (2 * A - 1) * C - X * C := by ring
      _ = B - X * (2 * A - 1) * C := by rw [← hdiff]; ring
      _ = 1 := by rw [hA]; ring
  have hB : B = (1 - X) * C := by
    calc
      B = C - X * C := hdiff.symm
      _ = (1 - X) * C := by ring
  have hfinish : (1 - 2 * X * A) * B = 1 - X := calc
    (1 - 2 * X * A) * B = (1 - X) * ((1 - 2 * X * A) * C) := by rw [hB]; ring
    _ = 1 - X := by rw [hbase]; ring
  simpa only [A, B] using hfinish
#print axioms groundSeries_bridge

end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalGroundSeries
