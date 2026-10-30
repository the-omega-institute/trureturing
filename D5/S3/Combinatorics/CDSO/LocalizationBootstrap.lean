/- GID: D5/S3/Combinatorics/CDSO/LocalizationBootstrap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CDSO/LocalizationBootstrap
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Order.BigOperators.Ring.Finset]
   utility: none
   digest: Uniform actual-array localization and two-stage bootstrap for fixed surplus hubs. -/

module

public import D5.S3.Combinatorics.CDSO.ArrayCore
import all D5.S3.Combinatorics.CDSO.ArrayCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

public section

open scoped BigOperators
open Filter Topology

namespace D5.S3.Combinatorics.CDSO.LocalizationBootstrap

noncomputable section

namespace JointArray

variable {a h : ℕ} (x : JointArray a h)

def tailV (D : TailChoice x) (T : NonemptyType a h) : ℝ :=
  ∑ j ∈ T.1 ∩ D.D, (y x j)⁻¹

def eventK2 (D : TailChoice x) : ℝ :=
  expect x (fun T => if 0 < tailCount x D T then (K T)^2 else 0)

private theorem tailV_zero (D : TailChoice x) (T : NonemptyType a h)
    (ht : ¬ 0 < tailCount x D T) : tailV x D T = 0 := by
  have he : T.1 ∩ D.D = ∅ := Finset.card_eq_zero.mp (by
    change tailCount x D T = 0
    omega)
  simp [tailV, he]

private theorem mean_tailV (D : TailChoice x) :
    expect x (tailV x D) = (h : ℝ) := by
  have hh := expect_incidence x D.D (fun i => (y x i)⁻¹)
  have he : (∑ i ∈ D.D, y x i * (y x i)⁻¹) = (h : ℝ) := by
    simp only [mul_inv_cancel₀ (ne_of_gt (y_pos x _)), Finset.sum_const,
      nsmul_eq_mul, mul_one, D.card_eq]
  exact hh.trans he

private theorem tailV_sq (D : TailChoice x) (T : NonemptyType a h) :
    (tailV x D T)^2 ≤ (K T)^2 * ∑ j ∈ T.1 ∩ D.D, (y x j)⁻¹^2 := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (T.1 ∩ D.D)
    (fun _ => (1 : ℝ)) (fun j => (y x j)⁻¹)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hh
  have hb : ((T.1 ∩ D.D).card : ℝ) ≤ K T := by
    dsimp [K, cardValue]
    exact_mod_cast (Finset.card_le_card Finset.inter_subset_left :
      (T.1 ∩ D.D).card ≤ T.1.card)
  have hk : 1 ≤ K T := by
    dsimp [K, cardValue]
    exact_mod_cast T.2.card_pos
  have hbk : ((T.1 ∩ D.D).card : ℝ) ≤ (K T)^2 := by nlinarith
  exact hh.trans (mul_le_mul_of_nonneg_right hbk
    (Finset.sum_nonneg fun j _ => sq_nonneg _))

private theorem tail_cauchy (D : TailChoice x) :
    0 < tailEventMass x D ∧ (h : ℝ)^2 / tailEventMass x D ≤ tailEnergy x D ∧
      eventK2 x D ≤ (delta x D)^2 * tailEnergy x D := by
  classical
  have hp := event_pos x D
  have hV : expect x (fun T => (tailV x D T)^2) ≤ tailEnergy x D := by
    rw [tailEnergy_eq]
    exact expect_mono x _ _ (tailV_sq x D)
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun T : NonemptyType a h => x.mass T * tailV x D T)
    (f := fun T => if 0 < tailCount x D T then x.mass T else 0)
    (g := fun T => x.mass T * (tailV x D T)^2)
    (fun T _ => by split_ifs <;> simp_all [x.mass_nonneg])
    (fun T _ => mul_nonneg (x.mass_nonneg T) (sq_nonneg _))
    (fun T _ => by
      split_ifs with ht
      · nlinarith
      · rw [tailV_zero x D T ht]
        simp)
  change (expect x (tailV x D))^2 ≤
    tailEventMass x D * expect x (fun T => (tailV x D T)^2) at hc
  rw [mean_tailV] at hc
  have hcp : (h : ℝ)^2 ≤ tailEnergy x D * tailEventMass x D := by
    nlinarith [mul_le_mul_of_nonneg_left hV hp.le]
  refine ⟨hp, (div_le_iff₀ hp).mpr hcp, ?_⟩
  rw [eventK2, tailEnergy_eq, ← expect_mul]
  apply expect_mono
  intro T
  split_ifs with ht
  · obtain ⟨j, hj⟩ := Finset.card_pos.mp ht
    have hy := y_pos x j
    have hyd : y x j ≤ delta x D :=
      Finset.le_sup' (fun j => y x j) (Finset.mem_inter.mp hj).2
    have hd : 0 ≤ delta x D := hy.le.trans hyd
    have hsq : (y x j)^2 ≤ (delta x D)^2 := by nlinarith
    have hterm : 1 ≤ (delta x D)^2 * (y x j)⁻¹^2 := by
      calc
        1 = (y x j)^2 * (y x j)⁻¹^2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have hsingle : (y x j)⁻¹^2 ≤ ∑ k ∈ T.1 ∩ D.D, (y x k)⁻¹^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg ((y x k)⁻¹)) hj
    have hall : 1 ≤ (delta x D)^2 * ∑ k ∈ T.1 ∩ D.D, (y x k)⁻¹^2 :=
      hterm.trans (mul_le_mul_of_nonneg_left hsingle (sq_nonneg _))
    nlinarith [mul_le_mul_of_nonneg_left hall (sq_nonneg (K T))]
  · positivity





def variance : ℝ := expect x (fun T => (K T - a)^2)

private theorem expect_K : expect x K = (a : ℝ) := x.mean_card_eq

private theorem expect_square (f : NonemptyType a h → ℝ) :
    (expect x f)^2 ≤ expect x (fun T => (f T)^2) := by
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun T => x.mass T * f T) (f := x.mass)
    (g := fun T => x.mass T * (f T)^2)
    (fun T _ => x.mass_nonneg T)
    (fun T _ => mul_nonneg (x.mass_nonneg T) (sq_nonneg _))
    (fun T _ => by nlinarith)
  simpa [expect, x.mass_sum] using hh

private theorem H_ge_third : expect x (fun T => (K T)^3) ≤ H x := by
  apply expect_mono
  intro T
  have hs : (K T : ℝ) ≤ ∑ i ∈ T.1, (y x i)⁻¹^2 := by
    have hh := Finset.sum_le_sum (s := T.1) (f := fun _ => (1 : ℝ))
      (g := fun i => (y x i)⁻¹^2) fun i _ => by
        have hi := (one_le_inv₀ (y_pos x i)).mpr (y_le_one x i)
        nlinarith
    simpa [K, cardValue] using hh
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (K T))]

private theorem cubic_variance :
    2 * (a : ℝ) * variance x ≤ expect x (fun T => (K T)^3) - (a : ℝ)^3 := by
  have hh : expect x (fun T => 2 * (a : ℝ) * (K T - a)^2) ≤
      expect x (fun T => (K T)^3 - (a : ℝ)^3 - 3 * (a : ℝ)^2 * (K T - a)) := by
    apply expect_mono
    intro T
    have hk : 0 ≤ K T := by dsimp [K, cardValue]; positivity
    nlinarith [mul_nonneg hk (sq_nonneg (K T - a))]
  rw [expect_mul, expect_sub, expect_sub, expect_const, expect_mul,
    expect_sub, expect_K, expect_const, sub_self, mul_zero, sub_zero] at hh
  exact hh

private theorem variance_bound (M : ℝ) (hM : 0 < M) (ha : 4 ≤ a)
    (hd : d x ≤ M * ((a : ℝ) * Real.sqrt a)) :
    variance x ≤ (M + 3) * (a : ℝ) := by
  have har : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have hs := Real.sq_sqrt (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  have hsn := Real.sqrt_nonneg (a : ℝ)
  have hsa : Real.sqrt (a : ℝ) ≤ a := by nlinarith
  have hv := (cubic_variance x).trans (sub_le_sub_right (H_ge_third x) _)
  have hmp := mul_le_mul_of_nonneg_left hsa (by positivity : 0 ≤ M * (a : ℝ))
  unfold d at hd
  nlinarith [sq_nonneg (a : ℝ), mul_nonneg (by linarith : 0 ≤ M + 3)
    (by nlinarith : 0 ≤ (a : ℝ)^2)]

private theorem absolute_deviation_bound (M : ℝ) (hM : 0 < M) (ha : 4 ≤ a)
    (hd : d x ≤ M * ((a : ℝ) * Real.sqrt a)) :
    expect x (fun T => |K T - a|) ≤ Real.sqrt (M + 3) * Real.sqrt a := by
  have hh := expect_square x (fun T => |K T - a|)
  simp only [sq_abs] at hh
  have hv := variance_bound x M hM ha hd
  have hM3 : 0 ≤ M + 3 := by linarith
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hsM := Real.sq_sqrt hM3
  have hsa := Real.sq_sqrt ha0
  have hn : 0 ≤ Real.sqrt (M + 3) * Real.sqrt (a : ℝ) := by positivity
  have hs : (Real.sqrt (M + 3) * Real.sqrt (a : ℝ))^2 = (M + 3) * a := by
    rw [mul_pow, hsM, hsa]
  change (expect x (fun T => |K T - a|))^2 ≤ variance x at hh
  nlinarith





def excess (S : Finset (Label a h)) (T : NonemptyType a h) : ℝ :=
  ∑ i ∈ T.1 ∩ S, ((y x i)⁻¹^2 - 1)

private theorem excess_term_nonneg (i : Label a h) : 0 ≤ (y x i)⁻¹^2 - 1 := by
  have hh := (one_le_inv₀ (y_pos x i)).mpr (y_le_one x i)
  nlinarith

private theorem excess_nonneg (S : Finset (Label a h)) (T : NonemptyType a h) :
    0 ≤ excess x S T := Finset.sum_nonneg fun i _ => excess_term_nonneg x i

private theorem deficit_sum : (∑ i, (1 - y x i)) = (h : ℝ) + 1 := by
  rw [Finset.sum_sub_distrib, sum_y]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, Nat.cast_add, Nat.cast_one]
  ring

private theorem cutoff_excess_bound (ε : ℝ) (hε : 0 < ε)
    (S : Finset (Label a h)) (hS : ∀ i ∈ S, ε ≤ y x i) (T : NonemptyType a h) :
    excess x S T ≤ 2 * ((h : ℝ) + 1) / ε^2 := by
  have ht (i : Label a h) (hi : i ∈ T.1 ∩ S) :
      (y x i)⁻¹^2 - 1 ≤ 2 / ε^2 * (1 - y x i) := by
    have hy := y_pos x i
    have hy1 := y_le_one x i
    have hye := hS i (Finset.mem_inter.mp hi).2
    have hid : (y x i)⁻¹^2 - 1 = (1 - y x i) * (1 + y x i) / (y x i)^2 := by
      field_simp
      <;> ring
    rw [hid]
    calc
      _ ≤ (1 - y x i) * 2 / ε^2 := by
        gcongr
        · linarith
      _ = _ := by ring
  have hsub : (∑ i ∈ T.1 ∩ S, (1 - y x i)) ≤ ∑ i, (1 - y x i) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ =>
      sub_nonneg.mpr (y_le_one x i)
  calc
    excess x S T ≤ ∑ i ∈ T.1 ∩ S, (2 / ε^2 * (1 - y x i)) :=
      Finset.sum_le_sum ht
    _ = 2 / ε^2 * ∑ i ∈ T.1 ∩ S, (1 - y x i) := (Finset.mul_sum ..).symm
    _ ≤ 2 / ε^2 * ((h : ℝ) + 1) := by
      rw [← deficit_sum x]
      exact mul_le_mul_of_nonneg_left hsub (by positivity)
    _ = _ := by ring

private theorem excess_mean_lower (S : Finset (Label a h)) :
    2 * ((S.card : ℝ) - ∑ i ∈ S, y x i) ≤ expect x (excess x S) := by
  have he := expect_incidence x S (fun i => (y x i)⁻¹^2 - 1)
  change expect x (excess x S) = _ at he
  rw [he]
  have ht (i : Label a h) :
      2 * (1 - y x i) ≤ y x i * ((y x i)⁻¹^2 - 1) := by
    have hy := y_pos x i
    have hid : y x i * ((y x i)⁻¹^2 - 1) - 2 * (1 - y x i) =
        (1 - y x i)^2 / y x i := by
      field_simp
      <;> ring
    have hp := div_nonneg (sq_nonneg (1 - y x i)) hy.le
    linarith
  have hh := Finset.sum_le_sum (s := S) (fun i _ => ht i)
  simpa only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, mul_one] using hh

private theorem energy_excess_lower (S : Finset (Label a h)) (V : ℝ)
    (hV : ∀ T, excess x S T ≤ V) :
    expect x (fun T => (K T)^3) + (a : ℝ)^2 * expect x (excess x S) -
      2 * a * V * expect x (fun T => |K T - a|) ≤ H x := by
  have hmain : expect x (fun T => (K T)^3 + (K T)^2 * excess x S T) ≤ H x := by
    apply expect_mono
    intro T
    have hsub : excess x S T ≤ ∑ i ∈ T.1, ((y x i)⁻¹^2 - 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
        (fun i _ _ => excess_term_nonneg x i)
    have he : (∑ i ∈ T.1, ((y x i)⁻¹^2 - 1)) =
        (∑ i ∈ T.1, (y x i)⁻¹^2) - K T := by
      simp [Finset.sum_sub_distrib, K, cardValue]
    rw [he] at hsub
    nlinarith [mul_le_mul_of_nonneg_left hsub (sq_nonneg (K T))]
  have hpt (T : NonemptyType a h) :
      (a : ℝ)^2 * excess x S T - 2 * a * V * |K T - a| ≤
        (K T)^2 * excess x S T := by
    have hnon := excess_nonneg x S T
    have hab := le_abs_self (-(K T - a))
    rw [abs_neg] at hab
    have hka : (a : ℝ)^2 - 2 * a * |K T - a| ≤ (K T)^2 := by
      nlinarith [sq_nonneg (K T - a)]
    have hh := mul_le_mul_of_nonneg_right hka hnon
    have hv := mul_le_mul_of_nonneg_right (hV T)
      (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * a) (abs_nonneg (K T - a)))
    nlinarith
  have hh := expect_mono x _ _ hpt
  rw [expect_sub, expect_mul, expect_mul] at hh
  rw [expect_add] at hmain
  linarith

private theorem rank_cutoff_localization (D : TailChoice x) (M ε : ℝ)
    (hM : 0 < M) (hε : 0 < ε) (ha : 4 ≤ a)
    (hd : d x ≤ M * ((a : ℝ) * Real.sqrt a))
    (hlarge : (M + 4 * ((h : ℝ) + 1) / ε^2 * Real.sqrt (M + 3) + 2)^2 ≤ (a : ℝ)) :
    delta x D < ε := by
  classical
  by_contra hbad
  have hde : ε ≤ delta x D := le_of_not_gt hbad
  let S := Finset.univ.filter (fun i => ε ≤ y x i)
  have hS : ∀ i ∈ S, ε ≤ y x i := fun i hi => (Finset.mem_filter.mp hi).2
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' D.nonempty (fun j => y x j)
  have hjε : ε ≤ y x j := by simpa [delta, heq] using hde
  have hsub : insert j (coreSet x D) ⊆ S := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjε⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hde.trans ((tail_bounds x D).2.2.2.1 i (Finset.mem_sdiff.mp hi).2)⟩
  have hjn : j ∉ coreSet x D := fun hc => (Finset.mem_sdiff.mp hc).2 hj
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hjn] at hc
  have hcore : (coreSet x D).card = a + 1 := core_card x D
  rw [hcore] at hc
  have hsum : (∑ i ∈ S, y x i) ≤ (a : ℝ) := by
    rw [← sum_y x]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ =>
      (y_pos x i).le
  have hmean := excess_mean_lower x S
  have hcard : (a : ℝ) + 2 ≤ (S.card : ℝ) := by exact_mod_cast hc
  have hfour : 4 ≤ expect x (excess x S) := by linarith
  let V := 2 * ((h : ℝ) + 1) / ε^2
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have henergy := energy_excess_lower x S V (cutoff_excess_bound x ε hε S hS)
  have had := absolute_deviation_bound x M hM ha hd
  have hthird : (a : ℝ)^3 ≤ expect x (fun T => (K T)^3) := by
    have hh := cubic_variance x
    have hv : 0 ≤ variance x := expect_nonneg x _ (fun T => sq_nonneg _)
    nlinarith [mul_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a) hv]
  have ha4 : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have hsn := Real.sqrt_nonneg (a : ℝ)
  have hs := Real.sq_sqrt (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  have hC : 0 ≤ M + 2 * V * Real.sqrt (M + 3) + 2 := by positivity
  have hroot : M + 2 * V * Real.sqrt (M + 3) + 2 ≤ Real.sqrt a := by
    have hl : (M + 2 * V * Real.sqrt (M + 3) + 2)^2 ≤ (a : ℝ) := by
      have hi : M + 2 * V * Real.sqrt (M + 3) + 2 =
          M + 4 * ((h : ℝ) + 1) / ε^2 * Real.sqrt (M + 3) + 2 := by
        dsimp [V]
        ring
      rwa [hi]
    nlinarith
  have herror := mul_le_mul_of_nonneg_left had
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * a) hV)
  have hmain : (a : ℝ)^3 + 4 * (a : ℝ)^2 -
      2 * a * V * (Real.sqrt (M + 3) * Real.sqrt a) ≤ H x := by
    nlinarith [mul_le_mul_of_nonneg_left hfour (sq_nonneg (a : ℝ))]
  have hscale := mul_le_mul_of_nonneg_left hroot
    (mul_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a) hsn)
  unfold d at hd
  nlinarith





def onTail (D : TailChoice x) (f : NonemptyType a h → ℝ) : ℝ :=
  expect x (fun T => if 0 < tailCount x D T then f T else 0)

private theorem onTail_nonneg (D : TailChoice x) (f : NonemptyType a h → ℝ)
    (hf : ∀ T, 0 ≤ f T) : 0 ≤ onTail x D f :=
  expect_nonneg x _ fun T => by split_ifs <;> simp_all

private theorem onTail_mono (D : TailChoice x) (f g : NonemptyType a h → ℝ)
    (hf : ∀ T, f T ≤ g T) : onTail x D f ≤ onTail x D g := by
  apply expect_mono
  intro T
  split_ifs <;> simp_all

private theorem onTail_const (D : TailChoice x) (c : ℝ) :
    onTail x D (fun _ => c) = c * tailEventMass x D := by
  rw [onTail, event_eq, ← expect_mul]
  congr 1
  funext T
  split_ifs <;> simp_all

private theorem onTail_mul (D : TailChoice x) (c : ℝ) (f : NonemptyType a h → ℝ) :
    onTail x D (fun T => c * f T) = c * onTail x D f := by
  unfold onTail
  rw [← expect_mul]
  congr 1
  funext T
  split_ifs <;> simp_all

private theorem onTail_sub (D : TailChoice x) (f g : NonemptyType a h → ℝ) :
    onTail x D (fun T => f T - g T) = onTail x D f - onTail x D g := by
  rw [onTail, onTail, onTail, ← expect_sub]
  congr 1
  funext T
  split_ifs <;> simp_all

private theorem onTail_square (D : TailChoice x) (f : NonemptyType a h → ℝ) :
    (onTail x D f)^2 ≤ tailEventMass x D * onTail x D (fun T => (f T)^2) := by
  classical
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun T => x.mass T * (if 0 < tailCount x D T then f T else 0))
    (f := fun T => if 0 < tailCount x D T then x.mass T else 0)
    (g := fun T => x.mass T * (if 0 < tailCount x D T then (f T)^2 else 0))
    (fun T _ => by split_ifs <;> simp_all [x.mass_nonneg])
    (fun T _ => mul_nonneg (x.mass_nonneg T) (by split_ifs <;> positivity))
    (fun T _ => by split_ifs <;> nlinarith)
  exact hh

private theorem onTail_core_square (D : TailChoice x) :
    (onTail x D (fun T => (coreCount x D T : ℝ)))^2 ≤
      tailEventMass x D * eventK2 x D := by
  have hh := onTail_square x D (fun T => (coreCount x D T : ℝ))
  have hmono : onTail x D (fun T => (coreCount x D T : ℝ)^2) ≤ eventK2 x D := by
    apply onTail_mono
    intro T
    have hk : (coreCount x D T : ℝ) ≤ K T := by
      dsimp [coreCount, K, cardValue]
      exact_mod_cast (Finset.card_le_card Finset.sdiff_subset : (T.1 \ D.D).card ≤ T.1.card)
    have hnon : 0 ≤ (coreCount x D T : ℝ) := by positivity
    nlinarith
  exact hh.trans (mul_le_mul_of_nonneg_left hmono (event_nonneg x D))

private theorem Q_tail_lower (D : TailChoice x) :
    (a : ℝ) * (a + 1) * (2 * a + 1) * tailEventMass x D -
      (3 * (a : ℝ)^2 + 3 * a + 1) *
        onTail x D (fun T => (coreCount x D T : ℝ)) ≤
      expect x (fun T => Q (a := a) (coreCount x D T)) := by
  have hh : onTail x D (fun T => (a : ℝ) * (a + 1) * (2 * a + 1) -
        (3 * (a : ℝ)^2 + 3 * a + 1) * coreCount x D T) ≤
      expect x (fun T => Q (a := a) (coreCount x D T)) := by
    apply expect_mono
    intro T
    split_ifs with ht
    · have hl : 0 ≤ (coreCount x D T : ℝ)^3 := by positivity
      unfold Q
      nlinarith
    · exact Q_nonneg x D T
  rw [onTail_sub, onTail_const, onTail_mul] at hh
  exact hh

private theorem correction_bounds (D : TailChoice x) (ha : 4 ≤ a)
    (hah : 2 * (h : ℝ) ≤ (a : ℝ)) :
    0 ≤ correction x D ∧ correction x D ≤ 64 * (a : ℝ)^2 := by
  have har : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have hu0 : 0 ≤ tailSum x D.D := Finset.sum_nonneg fun i _ => (y_pos x i).le
  have huh : tailSum x D.D ≤ (h : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ D.D, (1 : ℝ) := Finset.sum_le_sum fun i _ => y_le_one x i
      _ = _ := by simp [D.card_eq]
  have hp := core_sum_pos x D
  refine ⟨?_, ?_⟩
  · unfold correction
    positivity
  · unfold correction
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    have hr : ((a : ℝ) + 1)^2 ≤ 4 * (a : ℝ)^2 := by nlinarith
    have hn : (a : ℝ)^2 + 3 * a + 1 + a * tailSum x D.D ≤ 4 * (a : ℝ)^2 := by
      nlinarith [mul_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a) (sub_nonneg.mpr huh)]
    have hden : (a : ℝ)^2 ≤ 4 * ((a : ℝ) - tailSum x D.D)^2 := by
      nlinarith
    calc
      _ ≤ (4 * (a : ℝ)^2) * (4 * (a : ℝ)^2) :=
        mul_le_mul hr hn (by positivity) (by positivity)
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 16 * (a : ℝ)^2)]

private theorem tail_correction_bound (D : TailChoice x) (ha : 4 ≤ a)
    (hah : 2 * (h : ℝ) ≤ (a : ℝ)) :
    tailSum x D.D * correction x D ≤
      (64 * (h : ℝ)) * (a : ℝ)^2 * tailEventMass x D := by
  have hc := correction_bounds x D ha hah
  have hb := (tail_bounds x D).2.2.1
  have hp := event_nonneg x D
  calc
    _ ≤ ((h : ℝ) * tailEventMass x D) * (64 * (a : ℝ)^2) :=
      mul_le_mul hb hc.2 hc.1 (by positivity)
    _ = _ := by ring

private theorem energy_nonneg (D : TailChoice x) : 0 ≤ tailEnergy x D := by
  rw [tailEnergy_eq]
  exact expect_nonneg x _ fun T =>
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)





private theorem first_bootstrap (D : TailChoice x) (M : ℝ) (hM : 0 < M) (ha : 4 ≤ a)
    (hcond : 3 * (h : ℝ) * (2 * a + 1) ≤ (a : ℝ)^2)
    (hlarge : 100 * (64 * (h : ℝ) + 1) ≤ (a : ℝ))
    (hd : d x ≤ M * ((a : ℝ) * Real.sqrt a))
    (hsmall : delta x D ≤ 1 / (100 * (M + 64 * (h : ℝ) + 1))) :
    tailEnergy x D + (a : ℝ)^3 * tailEventMass x D ≤ d x := by
  let κ := 64 * (h : ℝ)
  let p := tailEventMass x D
  let δ := delta x D
  let E := tailEnergy x D
  let L := onTail x D (fun T => (coreCount x D T : ℝ))
  have hp : 0 < p := event_pos x D
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have har : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have hah : 2 * (h : ℝ) ≤ (a : ℝ) := by dsimp [κ] at *; linarith
  have hc := core_certificate x D hcond
  have ht := tail_correction_bound x D ha hah
  have hb := tail_bounds x D
  have he : E ≤ d x + κ * (a : ℝ)^2 * p := by
    dsimp [E, κ, p]
    linarith [hc.1, hc.2.1, hc.2.2, ht]
  have hδp : δ ≤ p := hb.1
  have hδ : 0 ≤ δ := by
    obtain ⟨j, hj⟩ := D.nonempty
    exact (y_pos x j).le.trans (Finset.le_sup' (fun j => y x j) hj)
  have hden : 0 < 100 * (M + κ + 1) := by positivity
  have hδsmall : (100 * (M + κ + 1)) * δ ≤ 1 := by
    simpa [δ, mul_comm] using (le_div_iff₀ hden).mp hsmall
  have hδ1 : δ ≤ 1 := by nlinarith only [hδsmall, hδ, mul_nonneg hM.le hδ, mul_nonneg hκ hδ]
  have hδprod : (M + κ) * δ ≤ 1 / 100 := by nlinarith only [hδsmall, hδ]
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  have hsnon := Real.sqrt_nonneg (a : ℝ)
  have hsqle : Real.sqrt (a : ℝ) ≤ a := by nlinarith
  have hde : d x ≤ M * (a : ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hsqle (by positivity : 0 ≤ M * (a : ℝ))
    nlinarith
  have hcs := tail_cauchy x D
  have hK : eventK2 x D ≤ (a : ℝ)^2 * p / 100 := by
    calc
      eventK2 x D ≤ δ^2 * E := hcs.2.2
      _ ≤ δ^2 * (M * (a : ℝ)^2 + κ * (a : ℝ)^2 * p) :=
        mul_le_mul_of_nonneg_left (by linarith : E ≤ M * (a : ℝ)^2 + κ * (a : ℝ)^2 * p)
          (sq_nonneg δ)
      _ = (a : ℝ)^2 * (M * δ^2 + κ * (δ^2 * p)) := by ring
      _ ≤ (a : ℝ)^2 * (M * (δ * p) + κ * (δ * p)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (by nlinarith : δ^2 ≤ δ * p) hM.le
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by nlinarith : δ^2 ≤ δ) hp.le) hκ
      _ = (a : ℝ)^2 * p * ((M + κ) * δ) := by ring
      _ ≤ (a : ℝ)^2 * p * (1 / 100) :=
        mul_le_mul_of_nonneg_left hδprod (by positivity)
      _ = _ := by ring
  have hL0 : 0 ≤ L := onTail_nonneg x D _ (fun T => by positivity)
  have hLsq : L^2 ≤ ((a : ℝ) * p / 10)^2 := by
    calc
      L^2 ≤ p * eventK2 x D := onTail_core_square x D
      _ ≤ p * ((a : ℝ)^2 * p / 100) := mul_le_mul_of_nonneg_left hK hp.le
      _ = _ := by ring
  have hL : L ≤ (a : ℝ) * p / 10 := by
    have hn : 0 ≤ (a : ℝ) * p / 10 := by positivity
    nlinarith only [hLsq, hL0, hn]
  have hβ : 3 * (a : ℝ)^2 + 3 * a + 1 ≤ 7 * (a : ℝ)^2 := by nlinarith only [har]
  have hβL : (3 * (a : ℝ)^2 + 3 * a + 1) * L ≤
      7 * (a : ℝ)^2 * ((a : ℝ) * p / 10) :=
    mul_le_mul hβ hL hL0 (by positivity)
  have hκa : κ ≤ (a : ℝ) / 100 := by dsimp [κ]; linarith only [hlarge]
  have hcost : κ * (a : ℝ)^2 * p ≤ (a : ℝ)^3 * p / 100 := by
    have hh := mul_le_mul_of_nonneg_right hκa (by positivity : 0 ≤ (a : ℝ)^2 * p)
    nlinarith only [hh]
  have hα : 2 * (a : ℝ)^3 * p ≤ (a : ℝ) * (a + 1) * (2 * a + 1) * p := by
    have hh := mul_le_mul_of_nonneg_right
      (show 2 * (a : ℝ)^3 ≤ (a : ℝ) * (a + 1) * (2 * a + 1) by nlinarith only [har, sq_nonneg (a : ℝ)]) hp.le
    exact hh
  have hQ := Q_tail_lower x D
  dsimp [L, p, κ, E] at *
  have hAp : 0 ≤ (a : ℝ)^3 * tailEventMass x D := by positivity
  nlinarith only [hc.2.2, hc.1, ht, hQ, hcost, hβL, hα, hAp]

private theorem refined_bootstrap (D : TailChoice x) (M : ℝ) (hM : 0 < M) (ha : 4 ≤ a)
    (hcond : 3 * (h : ℝ) * (2 * a + 1) ≤ (a : ℝ)^2)
    (hlarge : 100 * (64 * (h : ℝ) + 1) ≤ (a : ℝ))
    (hd : d x ≤ M * ((a : ℝ) * Real.sqrt a))
    (hsmall : delta x D ≤ 1 / (100 * (M + 64 * (h : ℝ) + 1))) :
    tailEventMass x D * ((a : ℝ) * Real.sqrt a) ≤ M ∧
    tailSum x D.D * ((a : ℝ) * Real.sqrt a) ≤ (h : ℝ) * M ∧
    tailEnergy x D ≤ M * ((a : ℝ) * Real.sqrt a) ∧
    tailEnergy x D +
      (2 * (a : ℝ)^3 - (64 * (h : ℝ) + 7 * (M^2 + 1)) * (a : ℝ)^2) *
        tailEventMass x D ≤ d x := by
  let p := tailEventMass x D
  let E := tailEnergy x D
  let q := (a : ℝ) * Real.sqrt a
  let L := onTail x D (fun T => (coreCount x D T : ℝ))
  have hp : 0 < p := event_pos x D
  have hE : 0 ≤ E := energy_nonneg x D
  have har : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have hq : 0 < q := mul_pos (by linarith) (Real.sqrt_pos.mpr (by linarith))
  have hq2 : q^2 = (a : ℝ)^3 := by
    dsimp [q]
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ a)]
    ring
  have hf := first_bootstrap x D M hM ha hcond hlarge hd hsmall
  have hqp : p * q ≤ M := by
    apply (mul_le_mul_iff_left₀ hq).mp
    calc
      (p * q) * q = (a : ℝ)^3 * p := by rw [← hq2]; ring
      _ ≤ d x := by linarith
      _ ≤ M * q := hd
  have huq : tailSum x D.D * q ≤ (h : ℝ) * M := by
    have hu := (tail_bounds x D).2.2.1
    calc
      _ ≤ ((h : ℝ) * p) * q := mul_le_mul_of_nonneg_right hu hq.le
      _ = (h : ℝ) * (p * q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hqp (Nat.cast_nonneg h)
  have hEq : E ≤ M * q := by
    have hnon : 0 ≤ (a : ℝ)^3 * p := by positivity
    linarith
  have hδ : 0 ≤ delta x D := by
    obtain ⟨j, hj⟩ := D.nonempty
    exact (y_pos x j).le.trans (Finset.le_sup' (fun j => y x j) hj)
  have hK : eventK2 x D ≤ M^2 * p := by
    calc
      _ ≤ (delta x D)^2 * E := (tail_cauchy x D).2.2
      _ ≤ p^2 * (M * q) := by
        apply mul_le_mul _ hEq hE (sq_nonneg _)
        nlinarith [(tail_bounds x D).1]
      _ = (M * p) * (p * q) := by ring
      _ ≤ (M * p) * M := mul_le_mul_of_nonneg_left hqp (by positivity)
      _ = _ := by ring
  have hL0 : 0 ≤ L := onTail_nonneg x D _ (fun T => by positivity)
  have hLsq : L^2 ≤ ((M^2 + 1) * p)^2 := by
    calc
      _ ≤ p * eventK2 x D := onTail_core_square x D
      _ ≤ p * (M^2 * p) := mul_le_mul_of_nonneg_left hK hp.le
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right
          (show M^2 ≤ (M^2 + 1)^2 by nlinarith only [sq_nonneg (M^2)]) (sq_nonneg p)
        nlinarith only [hh]
  have hL : L ≤ (M^2 + 1) * p := by
    have hn : 0 ≤ (M^2 + 1) * p := by positivity
    nlinarith only [hLsq, hn]
  have hβ : 3 * (a : ℝ)^2 + 3 * a + 1 ≤ 7 * (a : ℝ)^2 := by nlinarith only [har]
  have hβL := mul_le_mul hβ hL hL0 (by positivity : 0 ≤ 7 * (a : ℝ)^2)
  have hah : 2 * (h : ℝ) ≤ (a : ℝ) := by linarith
  have hc := core_certificate x D hcond
  have ht := tail_correction_bound x D ha hah
  have hQ := Q_tail_lower x D
  have hα : 2 * (a : ℝ)^3 * p ≤ (a : ℝ) * (a + 1) * (2 * a + 1) * p :=
    mul_le_mul_of_nonneg_right
      (show 2 * (a : ℝ)^3 ≤ (a : ℝ) * (a + 1) * (2 * a + 1) by nlinarith only [har, sq_nonneg (a : ℝ)]) hp.le
  refine ⟨hqp, huq, hEq, ?_⟩
  dsimp [p, E, L] at *
  nlinarith only [hc.2.2, hc.1, ht, hQ, hβL, hα]



end JointArray

abbrev IndexAtLeast4 := {a : ℕ // 4 ≤ a}

def scale (a : IndexAtLeast4) (q : ℝ) : ℝ := Real.rpow (a : ℝ) q

def EventuallyAtLeast (P : IndexAtLeast4 → Prop) : Prop := ∀ᶠ a in atTop, P a

def EventuallyAfter (N : ℝ) (P : IndexAtLeast4 → Prop) : Prop :=
  ∀ᶠ (a : IndexAtLeast4) in atTop, N ≤ (a : ℝ) → P a


def FullLowerChain (C : ℝ) {a h : ℕ} (x : JointArray a h) (D : x.TailChoice) : Prop :=
  JointArray.tailEnergy x D + (2 * (a : ℝ)^3 - C * (a : ℝ)^2) *
      JointArray.tailEventMass x D ≤ JointArray.d x ∧
  (h : ℝ)^2 / JointArray.tailEventMass x D +
      (2 * (a : ℝ)^3 - C * (a : ℝ)^2) * JointArray.tailEventMass x D ≤
    JointArray.tailEnergy x D +
      (2 * (a : ℝ)^3 - C * (a : ℝ)^2) * JointArray.tailEventMass x D

def UniformEstimate (Cp Cu CH C : ℝ) {a h : ℕ}
    (x : JointArray a h) (D : x.TailChoice) : Prop :=
  0 < JointArray.tailEventMass x D ∧
  JointArray.tailEventMass x D ≤ Cp * (a : ℝ)^(-3 / 2 : ℝ) ∧
  JointArray.tailSum x D.D ≤ Cu * (a : ℝ)^(-3 / 2 : ℝ) ∧
  JointArray.tailEnergy x D ≤ CH * (a : ℝ)^(3 / 2 : ℝ) ∧ FullLowerChain C x D

def UniformLocalization (h : ℕ) (M : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ a : ℕ, 4 ≤ a → N ≤ a →
    ∀ (x : JointArray a h) (D : x.TailChoice),
      JointArray.d x ≤ M * (a : ℝ)^(3 / 2 : ℝ) → JointArray.delta x D < ε

def Lemma135Statement (h : ℕ) (M : ℝ) : Prop :=
  2 ≤ h ∧ 0 < M →
  ∃ Cp Cu CH C : ℝ, 0 < Cp ∧ 0 < Cu ∧ 0 < CH ∧ 0 < C ∧ ∃ N : ℕ,
    (∀ a : ℕ, 4 ≤ a → N ≤ a → ∀ (x : JointArray a h) (D : x.TailChoice),
      JointArray.d x ≤ M * (a : ℝ)^(3 / 2 : ℝ) → UniformEstimate Cp Cu CH C x D) ∧
    UniformLocalization h M ∧
    (∀ (x : ∀ a : IndexAtLeast4, JointArray a h)
      (D : ∀ a : IndexAtLeast4, (x a).TailChoice),
      EventuallyAtLeast (fun a => JointArray.d (x a) ≤ M * scale a (3 / 2 : ℝ)) →
      Tendsto (fun a => JointArray.delta (x a) (D a)) atTop (𝓝 0) ∧
        EventuallyAtLeast (fun a => UniformEstimate Cp Cu CH C (x a) (D a)))

private theorem rpow_three_halves (a : ℕ) (ha : 0 < a) :
    (a : ℝ)^(3 / 2 : ℝ) = (a : ℝ) * Real.sqrt a := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add (Nat.cast_pos.mpr ha), Real.rpow_one, ← Real.sqrt_eq_rpow]

private theorem rpow_neg_three_halves (a : ℕ) (ha : 0 < a) :
    (a : ℝ)^(-3 / 2 : ℝ) = ((a : ℝ) * Real.sqrt a)⁻¹ := by
  rw [show (-3 / 2 : ℝ) = -(3 / 2) by ring,
    Real.rpow_neg (Nat.cast_nonneg a), rpow_three_halves a ha]

private theorem uniform_localization (h : ℕ) (M : ℝ) (hM : 0 < M) :
    UniformLocalization h M := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_ge
    ((M + 4 * ((h : ℝ) + 1) / ε^2 * Real.sqrt (M + 3) + 2)^2)
  refine ⟨N, ?_⟩
  intro a ha hNa x D hd
  apply JointArray.rank_cutoff_localization x D M ε hM hε ha
  · simpa [rpow_three_halves a (by omega)] using hd
  · exact hN.trans (Nat.cast_le.mpr hNa)

private theorem uniform_bootstrap (h : ℕ) (M : ℝ) (hM : 0 < M) :
    ∃ N : ℕ, ∀ a : ℕ, 4 ≤ a → N ≤ a → ∀ (x : JointArray a h) (D : x.TailChoice),
      JointArray.d x ≤ M * (a : ℝ)^(3 / 2 : ℝ) →
      UniformEstimate M ((h : ℝ) * M) M (64 * h + 7 * (M^2 + 1)) x D := by
  let ε := 1 / (100 * (M + 64 * (h : ℝ) + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨Nδ, hNδ⟩ := uniform_localization h M hM ε hε
  obtain ⟨Nb, hNb⟩ := exists_nat_ge (100 * (64 * (h : ℝ) + 1))
  refine ⟨max Nδ Nb, ?_⟩
  intro a ha hNa x D hd
  have hlarge : 100 * (64 * (h : ℝ) + 1) ≤ (a : ℝ) :=
    hNb.trans (Nat.cast_le.mpr ((le_max_right Nδ Nb).trans hNa))
  have har : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have h10 : 10 * ((h : ℝ) + 1) ≤ (a : ℝ) := by nlinarith only [hlarge, (Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
  have hcond : 3 * (h : ℝ) * (2 * a + 1) ≤ (a : ℝ)^2 := by
    nlinarith only [h10, (Nat.cast_nonneg h : (0 : ℝ) ≤ h),
      mul_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a) (sub_nonneg.mpr h10),
      mul_nonneg (Nat.cast_nonneg h : (0 : ℝ) ≤ h) (by linarith : 0 ≤ (a : ℝ) - 1)]
  have hsmall := (hNδ a ha ((le_max_left Nδ Nb).trans hNa) x D hd).le
  have hd' : JointArray.d x ≤ M * ((a : ℝ) * Real.sqrt a) := by
    simpa [rpow_three_halves a (by omega)] using hd
  have hb := JointArray.refined_bootstrap x D M hM ha hcond hlarge hd' hsmall
  have hq : 0 < (a : ℝ) * Real.sqrt a := by positivity
  have hp := JointArray.tail_cauchy x D
  refine ⟨hp.1, ?_, ?_, ?_, hb.2.2.2, ?_⟩
  · rw [rpow_neg_three_halves a (by omega), ← div_eq_mul_inv]
    exact (le_div_iff₀ hq).mpr hb.1
  · rw [rpow_neg_three_halves a (by omega), ← div_eq_mul_inv]
    exact (le_div_iff₀ hq).mpr hb.2.1
  · simpa [rpow_three_halves a (by omega)] using hb.2.2.1
  · linarith only [hp.2.1]

theorem lemma135 (h : ℕ) (M : ℝ) : Lemma135Statement h M := by
  rintro ⟨hh, hM⟩
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  obtain ⟨N, hN⟩ := uniform_bootstrap h M hM
  have hloc := uniform_localization h M hM
  refine ⟨M, (h : ℝ) * M, M, 64 * h + 7 * (M^2 + 1),
    hM, mul_pos hh0 hM, hM, by positivity, N, hN, hloc, ?_⟩
  intro x D hd
  have hthreshold (n : ℕ) : ∀ᶠ a : IndexAtLeast4 in atTop, n ≤ a.val := by
    refine (eventually_ge_atTop (⟨max n 4, le_max_right n 4⟩ : IndexAtLeast4)).mono ?_
    intro a ha
    exact (le_max_left n 4).trans ha
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := hloc ε hε
    filter_upwards [hd, hthreshold n] with a hda hna
    rw [Real.dist_eq, sub_zero, abs_of_nonneg]
    · exact hn a.val a.property hna (x a) (D a) hda
    · obtain ⟨j, hj⟩ := (D a).nonempty
      exact (JointArray.y_pos (x a) j).le.trans (Finset.le_sup' (fun j => JointArray.y (x a) j) hj)
  · filter_upwards [hd, hthreshold N] with a hda hna
    exact hN a.val a.property hna (x a) (D a) hda

#print axioms lemma135

end

end D5.S3.Combinatorics.CDSO.LocalizationBootstrap
