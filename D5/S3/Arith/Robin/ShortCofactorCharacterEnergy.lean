/- GID: D5/S3/Arith/Robin/ShortCofactorCharacterEnergy
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ShortCofactorCharacterEnergy
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Short cofactor character sums have fourth moment upper and first moment lower bounds. -/

import Mathlib.Combinatorics.Additive.Energy
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic

namespace D5.S3.Arith.Robin.ShortCofactorCharacterEnergy

open Finset

/-- The positive natural numbers strictly below a real cutoff. -/
noncomputable def shortInterval (H : ℝ) : Finset ℕ := Ico 1 ⌈H⌉₊

/-- The classical gcd parametrization gives a logarithmic energy bound. -/
theorem short_interval_energy (H : ℝ) (hH : 1 ≤ H) :
    ((shortInterval H).mulEnergy (shortInterval H) : ℝ) ≤
      2 * H ^ 2 * (1 + Real.log H) := by
  classical
  have integer_bound (N : ℕ) :
      ((Icc 1 N).mulEnergy (Icc 1 N) : ℝ) ≤
        2 * (N : ℝ) ^ 2 * (harmonic N : ℝ) := by
    let bucket (m : ℕ) : Finset (Bool × ℕ × ℕ × ℕ) :=
      univ ×ˢ (Icc 1 m) ×ˢ (Icc 1 (N / m)) ×ˢ (Icc 1 (N / m))
    let parameters := (Icc 1 N).sigma bucket
    let decode : (Σ _ : ℕ, Bool × ℕ × ℕ × ℕ) → (ℕ × ℕ) × ℕ × ℕ :=
      fun z => if z.2.1 then
        ((z.2.2.2.1 * z.1, z.2.2.2.1 * z.2.2.1),
          z.2.2.2.2 * z.2.2.1, z.2.2.2.2 * z.1)
      else
        ((z.2.2.2.1 * z.2.2.1, z.2.2.2.1 * z.1),
          z.2.2.2.2 * z.1, z.2.2.2.2 * z.2.2.1)
    have cover : Set.SurjOn decode (↑parameters)
        (↑(((Icc 1 N ×ˢ Icc 1 N) ×ˢ Icc 1 N ×ˢ Icc 1 N).filter
          fun x => x.1.1 * x.2.1 = x.1.2 * x.2.2)) := by
      intro x hx
      simp only [mem_coe, mem_filter, mem_product, mem_Icc] at hx
      obtain ⟨⟨⟨ha, hc⟩, hb, hd⟩, heq⟩ := hx
      let g := Nat.gcd x.1.1 x.1.2
      let u := x.1.1 / g
      let v := x.1.2 / g
      have hg : 0 < g := Nat.gcd_pos_of_pos_left _ ha.1
      have hu : g * u = x.1.1 := Nat.mul_div_cancel_left' (Nat.gcd_dvd_left _ _)
      have hv : g * v = x.1.2 := Nat.mul_div_cancel_left' (Nat.gcd_dvd_right _ _)
      have hu0 : 0 < u := by nlinarith [ha.1]
      have hv0 : 0 < v := by nlinarith [hc.1]
      have huv : Nat.Coprime u v := Nat.coprime_div_gcd_div_gcd hg
      have heq' : u * x.2.1 = v * x.2.2 := by
        apply Nat.eq_of_mul_eq_mul_left hg
        calc g * (u * x.2.1) = x.1.1 * x.2.1 := by rw [← mul_assoc, hu]
             _ = x.1.2 * x.2.2 := heq
             _ = g * (v * x.2.2) := by rw [← mul_assoc, hv]
      have hud : u ∣ x.2.2 := huv.dvd_of_dvd_mul_right
        (by rw [mul_comm x.2.2 v, ← heq']; exact dvd_mul_right u _)
      obtain ⟨j, hj⟩ := hud
      have hj0 : 0 < j := by nlinarith [hd.1]
      have hjv : j * v = x.2.1 := by
        apply Nat.eq_of_mul_eq_mul_left hu0
        calc u * (j * v) = (u * j) * v := by ring
             _ = x.2.2 * v := by rw [← hj]
             _ = v * x.2.2 := mul_comm _ _
             _ = u * x.2.1 := heq'.symm
      have hju : j * u = x.2.2 := by rw [mul_comm, ← hj]
      by_cases huvle : v ≤ u
      · have hum : u ≤ N := (Nat.div_le_self _ _).trans ha.2
        have hgu : g ≤ N / u := (Nat.le_div_iff_mul_le hu0).mpr (hu ▸ ha.2)
        have hjuN : j ≤ N / u := (Nat.le_div_iff_mul_le hu0).mpr (hju ▸ hd.2)
        refine ⟨⟨u, true, v, g, j⟩, ?_, ?_⟩
        · simp only [mem_coe, parameters, mem_sigma, bucket, mem_product, mem_univ,
            mem_Icc, true_and]
          exact ⟨⟨hu0, hum⟩, ⟨hv0, huvle⟩, ⟨hg, hgu⟩, ⟨hj0, hjuN⟩⟩
        · simp only [decode, ↓reduceIte]
          exact Prod.ext (Prod.ext hu hv) (Prod.ext hjv hju)
      · have huvle' : u ≤ v := by omega
        have hvm : v ≤ N := (Nat.div_le_self _ _).trans hc.2
        have hgv : g ≤ N / v := (Nat.le_div_iff_mul_le hv0).mpr (hv ▸ hc.2)
        have hjvN : j ≤ N / v := (Nat.le_div_iff_mul_le hv0).mpr (hjv ▸ hb.2)
        refine ⟨⟨v, false, u, g, j⟩, ?_, ?_⟩
        · simp only [mem_coe, parameters, mem_sigma, bucket, mem_product, mem_univ,
            mem_Icc, true_and]
          exact ⟨⟨hv0, hvm⟩, ⟨hu0, huvle'⟩, ⟨hg, hgv⟩, ⟨hj0, hjvN⟩⟩
        · simp only [decode, Bool.false_eq_true, ↓reduceIte]
          exact Prod.ext (Prod.ext hu hv) (Prod.ext hjv hju)
    have count : (Icc 1 N).mulEnergy (Icc 1 N) ≤
        ∑ m ∈ Icc 1 N, 2 * m * (N / m) ^ 2 := by
      have hc := card_le_card_of_surjOn decode cover
      simp only [parameters, card_sigma, bucket, card_product, card_univ,
        Fintype.card_bool, Nat.card_Icc, Nat.add_sub_cancel] at hc
      simpa only [Finset.mulEnergy, pow_two, mul_assoc] using hc
    have real_count : ((Icc 1 N).mulEnergy (Icc 1 N) : ℝ) ≤
        ∑ m ∈ Icc 1 N, 2 * (m : ℝ) * (N / m : ℕ) ^ 2 := by
      exact_mod_cast count
    calc
      ((Icc 1 N).mulEnergy (Icc 1 N) : ℝ)
          ≤ ∑ m ∈ Icc 1 N, 2 * (m : ℝ) * (N / m : ℕ) ^ 2 := real_count
      _ ≤ ∑ m ∈ Icc 1 N, 2 * (N : ℝ) ^ 2 * (m : ℝ)⁻¹ := by
        apply sum_le_sum
        intro m hm
        have hm0 : 0 < (m : ℝ) := by exact_mod_cast (mem_Icc.mp hm).1
        have hdiv : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
        calc
          2 * (m : ℝ) * (N / m : ℕ) ^ 2
              ≤ 2 * (m : ℝ) * ((N : ℝ) / m) ^ 2 := by gcongr
          _ = 2 * (N : ℝ) ^ 2 * (m : ℝ)⁻¹ := by field_simp
      _ = 2 * (N : ℝ) ^ 2 * (harmonic N : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, mul_sum]
  let N := ⌈H⌉₊ - 1
  have hceil : 1 ≤ ⌈H⌉₊ := (Nat.ceil_pos.mpr (by linarith : 0 < H))
  have hN : (N : ℝ) < H := by
    have hlt : N < ⌈H⌉₊ := by dsimp [N]; omega
    exact Nat.lt_ceil.mp hlt
  have interval_eq : shortInterval H = Icc 1 N := by
    ext n
    simp only [shortInterval, mem_Ico, mem_Icc]
    dsimp [N]
    omega
  rw [interval_eq]
  by_cases hN0 : N = 0
  · simp only [hN0, Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1),
      mulEnergy_empty_left, Nat.cast_zero]
    exact mul_nonneg (by positivity) (by linarith [Real.log_nonneg hH])
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN0
  calc
    ((Icc 1 N).mulEnergy (Icc 1 N) : ℝ)
        ≤ 2 * (N : ℝ) ^ 2 * (harmonic N : ℝ) := integer_bound N
    _ ≤ 2 * (N : ℝ) ^ 2 * (1 + Real.log N) := by
      gcongr
      exact harmonic_le_one_add_log N
    _ ≤ 2 * H ^ 2 * (1 + Real.log H) := by
      gcongr

/-- The short positive integers that are units modulo `V`. -/
noncomputable def cofactors (V : ℕ) (H : ℝ) : Finset ℕ :=
  (shortInterval H).filter (Nat.Coprime · V)

/-- The character sum over the short cofactors. -/
noncomputable def characterSum (V : ℕ) (H : ℝ) (χ : DirichletCharacter ℂ V) : ℂ :=
  ∑ h ∈ cofactors V H, χ h

/-- The moment with the principal coordinate set to zero and all characters used to normalize. -/
noncomputable def nonprincipalMoment (V : ℕ) (H : ℝ) (p : ℕ) : ℝ := by
  classical
  exact (V.totient : ℝ)⁻¹ *
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ V)).erase 1, ‖characterSum V H χ‖ ^ p

/-- The fourth moment bound and the first moment lower bound for an arbitrary modulus. -/
theorem character_bounds (V : ℕ) [NeZero V] (H : ℝ) (hH : 1 ≤ H) (hshort : H ^ 2 ≤ V) :
    nonprincipalMoment V H 4 ≤ 2 * H ^ 2 * (1 + Real.log H) ∧
      (2 * (cofactors V H).card ≤ V.totient →
        ((cofactors V H).card : ℝ) ^ (3 / 2 : ℝ) /
          (4 * H * Real.sqrt (1 + Real.log H)) ≤ nonprincipalMoment V H 1) := by
  classical
  have star_value (χ : DirichletCharacter ℂ V) (a : ZMod V) (ha : IsUnit a) :
      star (χ a) = χ a⁻¹ := by
    obtain ⟨u, rfl⟩ := ha
    rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  have orthogonal (a b : ZMod V) (ha : IsUnit a) :
      (∑ χ : DirichletCharacter ℂ V, star (χ a) * χ b) =
        if a = b then (V.totient : ℂ) else 0 := by
    simp_rw [star_value _ a ha]
    exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha b
  have square_moment {α : Type} [DecidableEq α] (T : Finset α) (f : α → ZMod V)
      (hf : ∀ t ∈ T, IsUnit (f t)) :
      (∑ χ : DirichletCharacter ℂ V, ‖∑ t ∈ T, χ (f t)‖ ^ 2) =
        (V.totient : ℝ) * ∑ a ∈ T, ∑ b ∈ T, if f a = f b then (1 : ℝ) else 0 := by
    apply Complex.ofReal_injective
    push_cast
    simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero]
    calc
      (∑ χ : DirichletCharacter ℂ V, (‖∑ t ∈ T, χ (f t)‖ : ℂ) ^ 2)
          = ∑ χ : DirichletCharacter ℂ V, ∑ a ∈ T, ∑ b ∈ T,
              star (χ (f a)) * χ (f b) := by
        apply sum_congr rfl
        intro χ _
        rw [← Complex.conj_mul']
        change star (∑ t ∈ T, χ (f t)) * (∑ t ∈ T, χ (f t)) = _
        rw [star_sum, sum_mul]
        simp_rw [mul_sum]
      _ = ∑ a ∈ T, ∑ b ∈ T, ∑ χ : DirichletCharacter ℂ V,
          star (χ (f a)) * χ (f b) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro a _
        rw [sum_comm]
      _ = (V.totient : ℂ) * ∑ a ∈ T, ∑ b ∈ T,
          if f a = f b then (1 : ℂ) else 0 := by
        simp only [mul_sum]
        apply sum_congr rfl
        intro a ha
        apply sum_congr rfl
        intro b _
        rw [orthogonal (f a) (f b) (hf a ha)]
        split_ifs <;> simp
  let S := cofactors V H
  have unit (h : ℕ) (hh : h ∈ S) : IsUnit (h : ZMod V) :=
    (ZMod.unitOfCoprime h (mem_filter.mp hh).2).isUnit
  have below (h : ℕ) (hh : h ∈ S) : (h : ℝ) < H :=
    Nat.lt_ceil.mp (mem_Ico.mp (mem_filter.mp hh).1).2
  have hHV : H ≤ (V : ℝ) := by nlinarith
  have small (h : ℕ) (hh : h ∈ S) : h < V := by
    exact_mod_cast (below h hh).trans_le hHV
  have cast_eq (a b : ℕ) (ha : a < V) (hb : b < V) :
      (a : ZMod V) = (b : ZMod V) ↔ a = b := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have second : (∑ χ : DirichletCharacter ℂ V, ‖characterSum V H χ‖ ^ 2) =
      (V.totient : ℝ) * S.card := by
    change (∑ χ : DirichletCharacter ℂ V, ‖∑ h ∈ S, χ (h : ZMod V)‖ ^ 2) = _
    rw [square_moment S (fun h => (h : ZMod V)) unit]
    congr 1
    calc
      (∑ a ∈ S, ∑ b ∈ S, if (a : ZMod V) = b then (1 : ℝ) else 0)
          = ∑ a ∈ S, ∑ b ∈ S, if a = b then (1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro a ha
        apply sum_congr rfl
        intro b hb
        simp only [cast_eq a b (small a ha) (small b hb)]
      _ = S.card := by simp
  have product_small (a b : ℕ) (ha : a ∈ S) (hb : b ∈ S) : a * b < V := by
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    have hap := below a ha
    have hbp := below b hb
    have hp : (a : ℝ) * b < H ^ 2 := by nlinarith
    exact_mod_cast hp.trans_le hshort
  have fourth : (∑ χ : DirichletCharacter ℂ V, ‖characterSum V H χ‖ ^ 4) =
      (V.totient : ℝ) * S.mulEnergy S := by
    have pair_sum (χ : DirichletCharacter ℂ V) :
        (characterSum V H χ) ^ 2 = ∑ t ∈ S ×ˢ S, χ ((t.1 * t.2 : ℕ) : ZMod V) := by
      simp only [characterSum, S, pow_two, sum_mul, mul_sum, sum_product,
        Nat.cast_mul, map_mul]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      ring
    calc
      (∑ χ : DirichletCharacter ℂ V, ‖characterSum V H χ‖ ^ 4)
          = ∑ χ : DirichletCharacter ℂ V,
              ‖∑ t ∈ S ×ˢ S, χ ((t.1 * t.2 : ℕ) : ZMod V)‖ ^ 2 := by
        apply sum_congr rfl
        intro χ _
        rw [← pair_sum, norm_pow]
        ring
      _ = (V.totient : ℝ) * ∑ a ∈ S ×ˢ S, ∑ b ∈ S ×ˢ S,
          if ((a.1 * a.2 : ℕ) : ZMod V) = ((b.1 * b.2 : ℕ) : ZMod V)
            then (1 : ℝ) else 0 :=
        square_moment (S ×ˢ S) (fun t => ((t.1 * t.2 : ℕ) : ZMod V))
          (fun t ht => by rw [Nat.cast_mul]; exact
            (unit t.1 (mem_product.mp ht).1).mul (unit t.2 (mem_product.mp ht).2))
      _ = (V.totient : ℝ) * S.mulEnergy S := by
        congr 1
        rw [mulEnergy_eq_card_filter, ← sum_boole]
        conv_rhs => rw [sum_product]
        apply sum_congr rfl
        intro a ha
        apply sum_congr rfl
        intro b hb
        simp only [cast_eq (a.1 * a.2) (b.1 * b.2)
          (product_small _ _ (mem_product.mp ha).1 (mem_product.mp ha).2)
          (product_small _ _ (mem_product.mp hb).1 (mem_product.mp hb).2)]
  let C := (univ : Finset (DirichletCharacter ℂ V)).erase 1
  let x (χ : DirichletCharacter ℂ V) := ‖characterSum V H χ‖
  let Q : ℝ := V.totient
  let k : ℝ := S.card
  have hQ : 0 < Q := by
    dsimp [Q]
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos V)
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hx (χ : DirichletCharacter ℂ V) : 0 ≤ x χ := norm_nonneg _
  have principal : characterSum V H 1 = (S.card : ℂ) := by
    change (∑ h ∈ S, (1 : DirichletCharacter ℂ V) h) = _
    calc
      (∑ h ∈ S, (1 : DirichletCharacter ℂ V) h) = ∑ _h ∈ S, (1 : ℂ) :=
        sum_congr rfl (fun h hh => MulChar.one_apply (unit h hh))
      _ = _ := by simp
  have principal_norm : x 1 = k := by
    simp only [x, principal, Complex.norm_natCast, k]
  have sum_two : (∑ χ ∈ C, x χ ^ 2) = Q * k - k ^ 2 := by
    have hsum := sum_erase_add (univ : Finset (DirichletCharacter ℂ V))
      (fun χ => x χ ^ 2) (mem_univ (1 : DirichletCharacter ℂ V))
    change (∑ χ ∈ C, x χ ^ 2) + x 1 ^ 2 = _ at hsum
    rw [principal_norm, second] at hsum
    dsimp [Q, k]
    linarith
  have sum_four : (∑ χ ∈ C, x χ ^ 4) ≤ Q * S.mulEnergy S := by
    calc
      (∑ χ ∈ C, x χ ^ 4) ≤ ∑ χ : DirichletCharacter ℂ V, x χ ^ 4 :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by positivity)
      _ = Q * S.mulEnergy S := fourth
  have energy_bound : (S.mulEnergy S : ℝ) ≤ 2 * H ^ 2 * (1 + Real.log H) := by
    calc
      (S.mulEnergy S : ℝ) ≤ (shortInterval H).mulEnergy (shortInterval H) := by
        exact_mod_cast mulEnergy_mono (filter_subset _ _) (filter_subset _ _)
      _ ≤ 2 * H ^ 2 * (1 + Real.log H) := short_interval_energy H hH
  have upper : nonprincipalMoment V H 4 ≤ 2 * H ^ 2 * (1 + Real.log H) := by
    change Q⁻¹ * (∑ χ ∈ C, x χ ^ 4) ≤ _
    calc
      Q⁻¹ * (∑ χ ∈ C, x χ ^ 4) ≤ Q⁻¹ * (Q * S.mulEnergy S) := by gcongr
      _ = (S.mulEnergy S : ℝ) := by field_simp
      _ ≤ 2 * H ^ 2 * (1 + Real.log H) := energy_bound
  refine ⟨upper, ?_⟩
  intro hbalance
  have hbalanceR : 2 * k ≤ Q := by
    dsimp [Q, k, S]
    exact_mod_cast hbalance
  let M (p : ℕ) := nonprincipalMoment V H p
  have hM (p : ℕ) : 0 ≤ M p := by
    dsimp [M, nonprincipalMoment]
    positivity
  have lower_two : k / 2 ≤ M 2 := by
    change k / 2 ≤ Q⁻¹ * (∑ χ ∈ C, x χ ^ 2)
    rw [sum_two]
    apply (le_of_mul_le_mul_left ?_ hQ)
    field_simp
    nlinarith [mul_nonneg hk (show 0 ≤ Q - 2 * k by linarith)]
  have cauchy_one : (∑ χ ∈ C, x χ ^ 2) ^ 2 ≤
      (∑ χ ∈ C, x χ) * ∑ χ ∈ C, x χ ^ 3 :=
    sum_sq_le_sum_mul_sum_of_sq_le_mul C
      (fun χ _ => hx χ) (fun χ _ => pow_nonneg (hx χ) _)
      (fun χ _ => le_of_eq (by ring))
  have cauchy_two : (∑ χ ∈ C, x χ ^ 3) ^ 2 ≤
      (∑ χ ∈ C, x χ ^ 2) * ∑ χ ∈ C, x χ ^ 4 := by
    have hprod (χ : DirichletCharacter ℂ V) : x χ * x χ ^ 2 = x χ ^ 3 := by ring
    have hpow (χ : DirichletCharacter ℂ V) : (x χ ^ 2) ^ 2 = x χ ^ 4 := by ring
    have h := sum_mul_sq_le_sq_mul_sq C x (fun χ => x χ ^ 2)
    change (∑ χ ∈ C, x χ * x χ ^ 2) ^ 2 ≤
      (∑ χ ∈ C, x χ ^ 2) * ∑ χ ∈ C, (x χ ^ 2) ^ 2 at h
    have hsum3 : (∑ χ ∈ C, x χ * x χ ^ 2) = ∑ χ ∈ C, x χ ^ 3 :=
      sum_congr rfl (fun χ _ => hprod χ)
    have hsum4 : (∑ χ ∈ C, (x χ ^ 2) ^ 2) = ∑ χ ∈ C, x χ ^ 4 :=
      sum_congr rfl (fun χ _ => hpow χ)
    rwa [hsum3, hsum4] at h
  have interpolation_sum : (∑ χ ∈ C, x χ ^ 2) ^ 3 ≤
      (∑ χ ∈ C, x χ) ^ 2 * ∑ χ ∈ C, x χ ^ 4 := by
    have h2 : 0 ≤ ∑ χ ∈ C, x χ ^ 2 := sum_nonneg (fun _ _ => by positivity)
    have h1 : 0 ≤ ∑ χ ∈ C, x χ := sum_nonneg (fun χ _ => hx χ)
    have h3 : 0 ≤ ∑ χ ∈ C, x χ ^ 3 := sum_nonneg (fun _ _ => by positivity)
    rcases h2.eq_or_lt with hz | hp
    · rw [← hz]
      norm_num only [zero_pow]
      exact mul_nonneg (sq_nonneg _) (sum_nonneg (fun _ _ => by positivity))
    have hfour : (∑ χ ∈ C, x χ ^ 2) ^ 4 ≤
        (∑ χ ∈ C, x χ) ^ 2 * (∑ χ ∈ C, x χ ^ 2) * ∑ χ ∈ C, x χ ^ 4 := by
      calc
        (∑ χ ∈ C, x χ ^ 2) ^ 4 = ((∑ χ ∈ C, x χ ^ 2) ^ 2) ^ 2 := by ring
        _ ≤ ((∑ χ ∈ C, x χ) * ∑ χ ∈ C, x χ ^ 3) ^ 2 := by gcongr
        _ = (∑ χ ∈ C, x χ) ^ 2 * (∑ χ ∈ C, x χ ^ 3) ^ 2 := by ring
        _ ≤ (∑ χ ∈ C, x χ) ^ 2 *
            ((∑ χ ∈ C, x χ ^ 2) * ∑ χ ∈ C, x χ ^ 4) := by gcongr
        _ = _ := by ring
    apply le_of_mul_le_mul_left (a := ∑ χ ∈ C, x χ ^ 2) _ hp
    nlinarith only [hfour]
  have interpolation : M 2 ^ 3 ≤ M 1 ^ 2 * M 4 := by
    have hscaled := mul_le_mul_of_nonneg_left interpolation_sum
      (pow_nonneg (inv_nonneg.mpr hQ.le) 3)
    dsimp only [M, nonprincipalMoment]
    simp only [pow_one]
    change (Q⁻¹ * (∑ χ ∈ C, x χ ^ 2)) ^ 3 ≤
      (Q⁻¹ * (∑ χ ∈ C, x χ)) ^ 2 * (Q⁻¹ * (∑ χ ∈ C, x χ ^ 4))
    calc
      _ = Q⁻¹ ^ 3 * (∑ χ ∈ C, x χ ^ 2) ^ 3 := by ring
      _ ≤ Q⁻¹ ^ 3 * ((∑ χ ∈ C, x χ) ^ 2 * ∑ χ ∈ C, x χ ^ 4) := hscaled
      _ = _ := by ring
  have kcube : k ^ 3 ≤ 16 * H ^ 2 * (1 + Real.log H) * M 1 ^ 2 := by
    have hc : (k / 2) ^ 3 ≤ M 1 ^ 2 * (2 * H ^ 2 * (1 + Real.log H)) := by
      calc
        (k / 2) ^ 3 ≤ M 2 ^ 3 := by gcongr
        _ ≤ M 1 ^ 2 * M 4 := interpolation
        _ ≤ M 1 ^ 2 * (2 * H ^ 2 * (1 + Real.log H)) := by gcongr
    nlinarith only [hc]
  have hlog : 0 < 1 + Real.log H := by linarith [Real.log_nonneg hH]
  have hHpos : 0 < H := by linarith
  have denominator_pos : 0 < 4 * H * Real.sqrt (1 + Real.log H) := by positivity
  have numerator_sq : (k ^ (3 / 2 : ℝ)) ^ 2 = k ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk]
    norm_num
  have denominator_sq : (4 * H * Real.sqrt (1 + Real.log H)) ^ 2 =
      16 * H ^ 2 * (1 + Real.log H) := by
    rw [mul_pow, Real.sq_sqrt hlog.le]
    ring
  apply (div_le_iff₀ denominator_pos).mpr
  have hsq : (k ^ (3 / 2 : ℝ)) ^ 2 ≤
      (M 1 * (4 * H * Real.sqrt (1 + Real.log H))) ^ 2 := by
    rw [numerator_sq, mul_pow, denominator_sq]
    nlinarith only [kcube]
  have hright : 0 ≤ M 1 * (4 * H * Real.sqrt (1 + Real.log H)) :=
    mul_nonneg (hM 1) denominator_pos.le
  nlinarith only [hsq, hright, Real.rpow_nonneg hk (3 / 2 : ℝ)]

/-- The reference scale `1 + V ceil(V/10)`. -/
noncomputable def referenceScale (V : ℕ) : ℕ := 1 + V * ⌈(V : ℝ) / 10⌉₊

/-- The short-cofactor cutoff at a positive budget coefficient. -/
noncomputable def cutoff (a : ℝ) (V : ℕ) : ℝ :=
  let y := Real.log (referenceScale V)
  Real.exp (a * (y / (Real.log y) ^ 2))

/-- All sufficiently large prime Fibonacci indices satisfy the short-cofactor bounds. -/
theorem result (a : ℝ) (ha : 0 < a) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → r.Prime →
      (cutoff a (Nat.fib r)) ^ 2 < Nat.fib r ∧
        nonprincipalMoment (Nat.fib r) (cutoff a (Nat.fib r)) 4 ≤
          2 * (cutoff a (Nat.fib r)) ^ 2 * (1 + Real.log (cutoff a (Nat.fib r))) ∧
        ((cofactors (Nat.fib r) (cutoff a (Nat.fib r))).card : ℝ) ^ (3 / 2 : ℝ) /
          (4 * cutoff a (Nat.fib r) * Real.sqrt (1 + Real.log (cutoff a (Nat.fib r)))) ≤
            nonprincipalMoment (Nat.fib r) (cutoff a (Nat.fib r)) 1 := by
  classical
  have totient_square (V : ℕ) (hV : 0 < V) : V ≤ 2 * V.totient ^ 2 := by
    let P := V.primeFactors
    let L := ∏ p ∈ P, p
    let R := ∏ p ∈ P, (p - 1)
    have hLpos : 0 < L := prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
    have hLdvd : L ∣ V := Nat.prod_primeFactors_dvd V
    have hrest : (∏ p ∈ P.erase 2, p) ≤ (∏ p ∈ P.erase 2, (p - 1)) ^ 2 := by
      rw [← prod_pow]
      apply prod_le_prod'
      intro p hp
      have hpP := (mem_erase.mp hp).2
      have hp2 := (mem_erase.mp hp).1
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hpP
      have hp3 : 3 ≤ p := by have := hprime.two_le; omega
      have hsub : p - 1 + 1 = p := Nat.sub_add_cancel hprime.one_le
      nlinarith
    have hLR : L ≤ 2 * R ^ 2 := by
      by_cases h2 : 2 ∈ P
      · dsimp [L, R]
        rw [← mul_prod_erase P (fun p : ℕ => p) h2, ← mul_prod_erase P (fun p => p - 1) h2]
        norm_num only [Nat.reduceSub, one_mul]
        nlinarith only [hrest]
      · simp only [erase_eq_of_notMem h2] at hrest
        dsimp [L, R]
        nlinarith only [hrest, sq_nonneg (∏ p ∈ P, (p - 1))]
    let d := V / L
    have hd : 1 ≤ d := Nat.div_pos (Nat.le_of_dvd hV hLdvd) hLpos
    have hVeq : V = d * L := (Nat.div_mul_cancel hLdvd).symm
    have hQeq : V.totient = d * R := Nat.totient_eq_div_primeFactors_mul V
    rw [hQeq, hVeq]
    calc
      d * L ≤ d * (2 * R ^ 2) := Nat.mul_le_mul_left _ hLR
      _ = 2 * d * R ^ 2 := by ring
      _ ≤ 2 * d ^ 2 * R ^ 2 := by
        have hd2 : d ≤ d ^ 2 := by nlinarith
        gcongr
      _ = 2 * (d * R) ^ 2 := by ring
  let t := Real.sqrt (8 * a) + 1
  let r₀ := max 65 ⌈Real.exp (Real.exp t)⌉₊
  refine ⟨r₀, ?_⟩
  intro r hr _hrprime
  let V := Nat.fib r
  have hr65 : 65 ≤ r := (le_max_left _ _).trans hr
  have hrceil : ⌈Real.exp (Real.exp t)⌉₊ ≤ r := (le_max_right _ _).trans hr
  have hrV : r ≤ V := Nat.le_fib_self (by omega)
  have hV65 : 65 ≤ V := hr65.trans hrV
  have hVpos : 0 < V := by omega
  have : NeZero V := ⟨by omega⟩
  have hVR : (64 : ℝ) < V := by exact_mod_cast (show 64 < V by omega)
  have hV2 : (2 : ℝ) ≤ V := by linarith
  have hV0 : (0 : ℝ) < V := by positivity
  have threshold : Real.exp (Real.exp t) ≤ (V : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hrceil.trans hrV)
  let g := ⌈(V : ℝ) / 10⌉₊
  let A : ℝ := referenceScale V
  let y := Real.log A
  let ell := Real.log y
  let H := cutoff a V
  have hg1 : 1 ≤ g := Nat.ceil_pos.mpr (by positivity : 0 < (V : ℝ) / 10)
  have hgR : (g : ℝ) < (V : ℝ) / 10 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hAeq : A = 1 + (V : ℝ) * g := by simp [A, referenceScale, g]
  have hVA : (V : ℝ) ≤ A := by
    have hgR1 : (1 : ℝ) ≤ g := by exact_mod_cast hg1
    rw [hAeq]
    nlinarith
  have hAupper : A ≤ (V : ℝ) ^ 2 := by
    rw [hAeq]
    nlinarith
  have hApos : 0 < A := hV0.trans_le hVA
  have hlogV : 0 < Real.log (V : ℝ) := Real.log_pos (by linarith)
  have hypos : 0 < y := hlogV.trans_le (Real.log_le_log hV0 hVA)
  have hyupper : y ≤ 2 * Real.log (V : ℝ) := by
    have hh := Real.log_le_log hApos hAupper
    simpa only [Real.log_pow, Nat.cast_ofNat, y] using hh
  have hylower : Real.exp t ≤ y := by
    have hh := Real.log_le_log (Real.exp_pos (Real.exp t)) threshold
    rw [Real.log_exp] at hh
    exact hh.trans (Real.log_le_log hV0 hVA)
  have hell : t ≤ ell := by
    have hh := Real.log_le_log (Real.exp_pos t) hylower
    simpa only [Real.log_exp, ell] using hh
  have hsqrt : (Real.sqrt (8 * a)) ^ 2 = 8 * a := Real.sq_sqrt (by positivity)
  have hsqrt0 := Real.sqrt_nonneg (8 * a)
  have hellpos : 0 < ell := by dsimp [t] at hell; linarith
  have hellsq : 8 * a < ell ^ 2 := by dsimp [t] at hell; nlinarith
  have hexponent : a * (y / ell ^ 2) ≤ Real.log (V : ℝ) / 4 := by
    calc
      a * (y / ell ^ 2) ≤ y / 8 := by
        rw [← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hellpos)]
        nlinarith
      _ ≤ Real.log (V : ℝ) / 4 := by linarith
  have hHexp : H = Real.exp (a * (y / ell ^ 2)) := rfl
  have hH1 : 1 ≤ H := by
    rw [hHexp]
    exact Real.one_le_exp (by positivity)
  have hloglarge : 2 * Real.log 8 < Real.log (V : ℝ) := by
    have hh := Real.log_lt_log (by norm_num : (0 : ℝ) < 64) hVR
    have heq : Real.log (64 : ℝ) = 2 * Real.log 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rwa [heq] at hh
  have h8 : 8 * H ^ 2 < (V : ℝ) := by
    calc
      8 * H ^ 2 = Real.exp (Real.log 8 + 2 * (a * (y / ell ^ 2))) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8),
          show 2 * (a * (y / ell ^ 2)) = (2 : ℕ) * (a * (y / ell ^ 2)) by norm_num,
          Real.exp_nat_mul, hHexp]
      _ < Real.exp (Real.log (V : ℝ)) := Real.exp_lt_exp.mpr (by linarith)
      _ = (V : ℝ) := Real.exp_log hV0
  have hshort : H ^ 2 < (V : ℝ) := by nlinarith [sq_nonneg H]
  have hcard : (cofactors V H).card ≤ ⌈H⌉₊ - 1 := by
    have hh := card_filter_le (shortInterval H) (Nat.Coprime · V)
    simpa only [cofactors, shortInterval, Nat.card_Ico] using hh
  have hceil : 0 < ⌈H⌉₊ := Nat.ceil_pos.mpr (by linarith : 0 < H)
  have hcardH : ((cofactors V H).card : ℝ) ≤ H := by
    have hn : ⌈H⌉₊ - 1 < ⌈H⌉₊ := by omega
    exact (Nat.cast_le.mpr hcard).trans (Nat.lt_ceil.mp hn).le
  have htotient : (V : ℝ) ≤ 2 * (V.totient : ℝ) ^ 2 := by
    exact_mod_cast totient_square V hVpos
  have hQ0 : (0 : ℝ) ≤ V.totient := Nat.cast_nonneg _
  have hH0 : 0 ≤ H := by linarith
  have h2H : 2 * H ≤ (V.totient : ℝ) := by nlinarith
  have hbalance : 2 * (cofactors V H).card ≤ V.totient := by
    have hh : 2 * ((cofactors V H).card : ℝ) ≤ (V.totient : ℝ) := by linarith
    exact_mod_cast hh
  have general := character_bounds V H hH1 hshort.le
  exact ⟨hshort, general.1, general.2 hbalance⟩

end D5.S3.Arith.Robin.ShortCofactorCharacterEnergy
