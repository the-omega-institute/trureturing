/- GID: D5/S3/Combinatorics/CDSO/ArrayCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CDSO/ArrayCore
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Order.BigOperators.Ring.Finset]
   utility: none
   digest: Actual incidence arrays and the common-tail core remainder certificate. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Filter Topology

namespace D5.S3.Combinatorics.CDSO.LocalizationBootstrap

noncomputable section

abbrev Label (a h : ℕ) := Fin (a + 1 + h)

abbrev NonemptyType (a h : ℕ) := {T : Finset (Label a h) // T.Nonempty}

instance nonemptyTypeFintype (a h : ℕ) : Fintype (NonemptyType a h) :=
  Fintype.ofFinite _

instance nonemptyTypeDecidableEq (a h : ℕ) : DecidableEq (NonemptyType a h) :=
  Classical.decEq _

def cardValue {a h : ℕ} (T : NonemptyType a h) : ℝ := T.1.card

def marginal {a h : ℕ} (mass : NonemptyType a h → ℝ) (i : Label a h) : ℝ :=
  ∑ T : NonemptyType a h, if i ∈ T.1 then mass T else 0

def meanCard {a h : ℕ} (mass : NonemptyType a h → ℝ) : ℝ :=
  ∑ T : NonemptyType a h, mass T * cardValue T

structure JointArray (a h : ℕ) where
  mass : NonemptyType a h → ℝ
  mass_nonneg : ∀ T, 0 ≤ mass T
  mass_sum : ∑ T, mass T = 1
  marginal_pos : ∀ i, 0 < marginal mass i
  mean_card_eq : meanCard mass = a

namespace JointArray

variable {a h : ℕ} (x : JointArray a h)

def y (i : Label a h) : ℝ := marginal x.mass i

structure TailChoice where
  D : Finset (Label a h)
  card_eq : D.card = h
  nonempty : D.Nonempty
  smallest : ∀ j ∈ D, ∀ i ∉ D, y x j ≤ y x i

def K (T : NonemptyType a h) : ℝ := cardValue T

def H : ℝ :=
  ∑ T : NonemptyType a h, x.mass T *
    ((K T) ^ 2 * ∑ i ∈ T.1, (y x i)⁻¹ ^ 2)

def d : ℝ := H x - a * (a + 1) ^ 2

def tailSum (D : Finset (Label a h)) : ℝ := ∑ j ∈ D, y x j

def delta (D : TailChoice x) : ℝ := D.D.sup' D.nonempty (fun j => y x j)

def tailCount (D : TailChoice x) (T : NonemptyType a h) : ℕ := (T.1 ∩ D.D).card

def coreCount (D : TailChoice x) (T : NonemptyType a h) : ℕ := (T.1 \ D.D).card

def tailEventMass (D : TailChoice x) : ℝ :=
  ∑ T : NonemptyType a h, if 0 < tailCount x D T then x.mass T else 0

def tailEnergy (D : TailChoice x) : ℝ :=
  ∑ T : NonemptyType a h, if 0 < tailCount x D T then
      x.mass T * ((K T) ^ 2 * ∑ j ∈ T.1 ∩ D.D, (y x j)⁻¹ ^ 2) else 0


def expect (f : NonemptyType a h → ℝ) : ℝ := ∑ T, x.mass T * f T

private theorem expect_nonneg (f : NonemptyType a h → ℝ) (hf : ∀ T, 0 ≤ f T) :
    0 ≤ expect x f :=
  Finset.sum_nonneg fun T _ => mul_nonneg (x.mass_nonneg T) (hf T)

private theorem expect_mono (f g : NonemptyType a h → ℝ) (hfg : ∀ T, f T ≤ g T) :
    expect x f ≤ expect x g :=
  Finset.sum_le_sum fun T _ => mul_le_mul_of_nonneg_left (hfg T) (x.mass_nonneg T)

private theorem expect_const (c : ℝ) : expect x (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, x.mass_sum]

private theorem expect_add (f g : NonemptyType a h → ℝ) :
    expect x (fun T => f T + g T) = expect x f + expect x g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

private theorem expect_sub (f g : NonemptyType a h → ℝ) :
    expect x (fun T => f T - g T) = expect x f - expect x g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

private theorem expect_mul (c : ℝ) (f : NonemptyType a h → ℝ) :
    expect x (fun T => c * f T) = c * expect x f := by
  simp [expect, Finset.mul_sum, mul_left_comm]

private theorem expect_incidence (S : Finset (Label a h)) (f : Label a h → ℝ) :
    expect x (fun T => ∑ i ∈ T.1 ∩ S, f i) = ∑ i ∈ S, y x i * f i := by
  classical
  simp only [expect, y, marginal]
  calc
    _ = ∑ T, ∑ i ∈ S, if i ∈ T.1 then x.mass T * f i else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      rw [Finset.mul_sum]
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro T _
      split_ifs <;> simp_all

private theorem y_pos (i : Label a h) : 0 < y x i := x.marginal_pos i

private theorem y_le_one (i : Label a h) : y x i ≤ 1 := by
  classical
  rw [y, marginal, ← x.mass_sum]
  exact Finset.sum_le_sum fun T _ => by
    split_ifs <;> simp_all [x.mass_nonneg]

private theorem sum_y : (∑ i, y x i) = (a : ℝ) := by
  have hi := expect_incidence x Finset.univ (fun _ => 1)
  have hm : expect x (fun T => (T.1.card : ℝ)) = (a : ℝ) := x.mean_card_eq
  have hi' : expect x (fun T => (T.1.card : ℝ)) = ∑ i, y x i := by simpa using hi
  exact hi'.symm.trans hm

private theorem tailCount_le (D : TailChoice x) (T : NonemptyType a h) :
    tailCount x D T ≤ h := by
  exact (Finset.card_le_card Finset.inter_subset_right).trans_eq D.card_eq

private theorem core_card (D : TailChoice x) :
    (Finset.univ \ D.D).card = a + 1 := by
  classical
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, D.card_eq]
  omega

private theorem coreCount_le (D : TailChoice x) (T : NonemptyType a h) :
    coreCount x D T ≤ a + 1 := by
  exact (Finset.card_le_card (show T.1 \ D.D ⊆ Finset.univ \ D.D by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩)).trans_eq (core_card x D)

private theorem tailSum_eq (D : TailChoice x) :
    tailSum x D.D = expect x (fun T => (tailCount x D T : ℝ)) := by
  simpa [tailSum, tailCount] using
    (expect_incidence x D.D (fun _ => 1)).symm

private theorem event_eq (D : TailChoice x) :
    tailEventMass x D = expect x (fun T => if 0 < tailCount x D T then 1 else 0) := by
  classical
  simp only [tailEventMass, expect]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp_all

private theorem event_nonneg (D : TailChoice x) : 0 ≤ tailEventMass x D := by
  rw [event_eq]
  exact expect_nonneg x _ fun T => by split_ifs <;> norm_num

private theorem y_le_event (D : TailChoice x) (j : Label a h) (hj : j ∈ D.D) :
    y x j ≤ tailEventMass x D := by
  classical
  unfold y marginal tailEventMass
  apply Finset.sum_le_sum
  intro T _
  by_cases ht : j ∈ T.1
  · have hb : 0 < tailCount x D T := by
      exact Finset.card_pos.mpr ⟨j, Finset.mem_inter.mpr ⟨ht, hj⟩⟩
    simp [ht, hb]
  · simp only [ht, if_false]
    split_ifs <;> simp_all [x.mass_nonneg]

private theorem tail_bounds (D : TailChoice x) :
    delta x D ≤ tailEventMass x D ∧
    tailEventMass x D ≤ tailSum x D.D ∧
    tailSum x D.D ≤ (h : ℝ) * tailEventMass x D ∧
    (∀ i ∉ D.D, delta x D ≤ y x i) ∧
    tailSum x D.D / (h : ℝ) ≤ delta x D := by
  classical
  have hh : 0 < h := by rw [← D.card_eq]; exact D.nonempty.card_pos
  have he : tailEventMass x D ≤ tailSum x D.D := by
    rw [tailSum_eq, event_eq]
    apply expect_mono
    intro T
    split_ifs with ht
    · exact_mod_cast ht
    · positivity
  have hu : tailSum x D.D ≤ (h : ℝ) * tailEventMass x D := by
    rw [tailSum_eq, event_eq, ← expect_mul]
    apply expect_mono
    intro T
    split_ifs with ht
    · simpa using (Nat.cast_le.mpr (tailCount_le x D T) : (tailCount x D T : ℝ) ≤ h)
    · have hz : tailCount x D T = 0 := by omega
      simp [hz]
  refine ⟨?_, he, hu, ?_, ?_⟩
  · exact Finset.sup'_le _ _ fun j hj => y_le_event x D j hj
  · intro i hi
    exact Finset.sup'_le _ _ fun j hj => D.smallest j hj i hi
  · apply (div_le_iff₀ (Nat.cast_pos.mpr hh)).mpr
    calc
      tailSum x D.D ≤ ∑ _j ∈ D.D, delta x D :=
        Finset.sum_le_sum fun j hj => Finset.le_sup' (fun j => y x j) hj
      _ = delta x D * (h : ℝ) := by simp [D.card_eq, mul_comm]

private theorem event_pos (D : TailChoice x) : 0 < tailEventMass x D := by
  obtain ⟨j, hj⟩ := D.nonempty
  exact (y_pos x j).trans_le (y_le_event x D j hj)

private theorem core_sum (D : TailChoice x) :
    (∑ i ∈ Finset.univ \ D.D, y x i) = (a : ℝ) - tailSum x D.D := by
  have hs := Finset.sum_sdiff (Finset.subset_univ D.D) (f := y x)
  rw [sum_y x] at hs
  exact eq_sub_iff_add_eq.mpr hs

private theorem expect_core (D : TailChoice x) :
    expect x (fun T => (coreCount x D T : ℝ)) = (a : ℝ) - tailSum x D.D := by
  have hi := expect_incidence x (Finset.univ \ D.D) (fun _ => 1)
  simp only [← Finset.inter_sdiff_assoc, Finset.inter_univ] at hi
  simpa [coreCount] using hi.trans (by simpa using core_sum x D)



def coreSet (D : TailChoice x) : Finset (Label a h) := Finset.univ \ D.D

def Q (l : ℝ) : ℝ := ((a : ℝ) + 1 - l) * ((a : ℝ) - l) * (2 * a + 1 + l)

def coreFunction (u y : ℝ) : ℝ := (a : ℝ)^2 / y - (2 * a + 1) * u / y^2

def correction (D : TailChoice x) : ℝ :=
  ((a : ℝ) + 1)^2 *
    ((a : ℝ)^2 + 3 * a + 1 + a * tailSum x D.D) / ((a : ℝ) - tailSum x D.D)^2

def jensenGap (D : TailChoice x) : ℝ :=
  (∑ i ∈ coreSet x D, coreFunction (a := a) (tailSum x D.D) (y x i)) -
    ((a : ℝ) + 1) *
      coreFunction (a := a) (tailSum x D.D) (((a : ℝ) - tailSum x D.D) / (a + 1))

def rho (D : TailChoice x) (i : Label a h) (T : NonemptyType a h) : ℝ :=
  if i ∈ T.1 then
    ((a : ℝ) + 1 - coreCount x D T) * ((a : ℝ) - coreCount x D T)
  else (2 * a + 1) * ((a : ℝ) - coreCount x D T)

private theorem rho_nonneg (D : TailChoice x) (i : Label a h) (hi : i ∈ coreSet x D)
    (T : NonemptyType a h) : 0 ≤ rho x D i T := by
  classical
  have hc := coreCount_le x D T
  have hid : i ∉ D.D := (Finset.mem_sdiff.mp hi).2
  unfold rho
  split_ifs with hit
  · by_cases hl : coreCount x D T ≤ a
    · have hlr : (coreCount x D T : ℝ) ≤ a := by exact_mod_cast hl
      exact mul_nonneg (by linarith) (by linarith)
    · have hl : coreCount x D T = a + 1 := by omega
      simp [hl]
  · have hsub : insert i (T.1 \ D.D) ⊆ coreSet x D := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hj).2⟩
    have hnot : i ∉ T.1 \ D.D := fun hm => hit (Finset.mem_sdiff.mp hm).1
    have hl := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot] at hl
    change coreCount x D T + 1 ≤ (Finset.univ \ D.D).card at hl
    rw [core_card x D] at hl
    have hlr : (coreCount x D T : ℝ) ≤ a := by exact_mod_cast (show coreCount x D T ≤ a by omega)
    exact mul_nonneg (by positivity) (by linarith)

private theorem rho_expansion (D : TailChoice x) (i : Label a h)
    (T : NonemptyType a h) :
    rho x D i T =
      (if i ∈ T.1 then (coreCount x D T : ℝ)^2 else 0) -
      (a : ℝ)^2 * (if i ∈ T.1 then 1 else 0) +
      (2 * a + 1) * ((a : ℝ) - coreCount x D T) := by
  classical
  unfold rho
  split_ifs <;> ring

private theorem sum_rho (D : TailChoice x) (T : NonemptyType a h) :
    (∑ i ∈ coreSet x D, rho x D i T) = Q (a := a) (coreCount x D T) := by
  classical
  have hind : (∑ i ∈ coreSet x D, if i ∈ T.1 then (1 : ℝ) else 0) =
      (coreCount x D T : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter]
    rw [Finset.inter_comm, coreSet, ← Finset.inter_sdiff_assoc, Finset.inter_univ]
    simp [coreCount]
  have hcard : ((coreSet x D).card : ℝ) = (a : ℝ) + 1 := by
    exact_mod_cast core_card x D
  simp_rw [rho_expansion]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsq : (∑ i ∈ coreSet x D, if i ∈ T.1 then (coreCount x D T : ℝ)^2 else 0) =
      (coreCount x D T : ℝ)^2 * coreCount x D T := by
    rw [← hind, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [hsq, hind]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  unfold Q
  ring

private theorem Q_nonneg (D : TailChoice x) (T : NonemptyType a h) :
    0 ≤ Q (a := a) (coreCount x D T) := by
  rw [← sum_rho x D T]
  exact Finset.sum_nonneg fun i hi => rho_nonneg x D i hi T

private theorem mean_rho (D : TailChoice x) (i : Label a h) :
    expect x (rho x D i) =
      expect x (fun T => if i ∈ T.1 then (coreCount x D T : ℝ)^2 else 0) -
      (a : ℝ)^2 * y x i + (2 * a + 1) * tailSum x D.D := by
  have hm : expect x (fun T => if i ∈ T.1 then 1 else 0) = y x i := by
    classical
    simp only [expect, y, marginal]
    apply Finset.sum_congr rfl
    intro T _
    split_ifs <;> simp
  change expect x (fun T => rho x D i T) = _
  simp_rw [rho_expansion]
  rw [expect_add, expect_sub, expect_mul, hm, expect_mul, expect_sub,
    expect_const, expect_core]
  ring



private theorem expect_weighted_incidence (S : Finset (Label a h))
    (f : Label a h → ℝ) (g : NonemptyType a h → ℝ) :
    expect x (fun T => g T * ∑ i ∈ T.1 ∩ S, f i) =
      ∑ i ∈ S, expect x (fun T => if i ∈ T.1 then g T else 0) * f i := by
  classical
  simp only [expect]
  calc
    _ = ∑ T, ∑ i ∈ S, if i ∈ T.1 then x.mass T * g T * f i else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      rw [← mul_assoc, Finset.mul_sum, Finset.inter_comm,
        ← Finset.filter_mem_eq_inter, Finset.sum_filter]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro T _
      split_ifs <;> simp_all

private theorem core_sum_pos (D : TailChoice x) :
    0 < (a : ℝ) - tailSum x D.D := by
  rw [← core_sum x D]
  apply Finset.sum_pos
  · intro i _
    exact y_pos x i
  · apply Finset.card_pos.mp
    rw [core_card x D]
    omega

private theorem core_tangent (u v z : ℝ) (hv : 0 < v) (hz : 0 < z)
    (huv : u ≤ (h : ℝ) * v) (huz : u ≤ (h : ℝ) * z)
    (ha : 3 * (h : ℝ) * (2 * a + 1) ≤ (a : ℝ)^2) :
    coreFunction (a := a) u z +
      (-(a : ℝ)^2 / z^2 + 2 * (2 * a + 1) * u / z^3) * (v - z) ≤
      coreFunction (a := a) u v := by
  have hc : 0 ≤ (2 * (a : ℝ) + 1) := by positivity
  have hnum : 0 ≤ (a : ℝ)^2 * v * z - (2 * a + 1) * u * (2 * v + z) := by
    have hh : 0 ≤ 3 * (h : ℝ) * v * z - u * (2 * v + z) := by
      nlinarith [mul_nonneg hv.le (sub_nonneg.mpr huz),
        mul_nonneg hz.le (sub_nonneg.mpr huv)]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (mul_nonneg hv.le hz.le),
      mul_nonneg hc hh]
  have hid :
      coreFunction (a := a) u v - coreFunction (a := a) u z -
        (-(a : ℝ)^2 / z^2 + 2 * (2 * a + 1) * u / z^3) * (v - z) =
      (v - z)^2 * ((a : ℝ)^2 * v * z - (2 * a + 1) * u * (2 * v + z)) /
        (v^2 * z^3) := by
    unfold coreFunction
    field_simp
    <;> ring
  have hn := div_nonneg (mul_nonneg (sq_nonneg (v - z)) hnum)
    (mul_nonneg (sq_nonneg v) (pow_nonneg hz.le 3))
  linarith

private theorem jensen_nonneg (D : TailChoice x)
    (ha : 3 * (h : ℝ) * (2 * a + 1) ≤ (a : ℝ)^2) :
    0 ≤ jensenGap x D := by
  classical
  let u := tailSum x D.D
  let z := ((a : ℝ) - u) / (a + 1)
  have hr : 0 < (a : ℝ) + 1 := by positivity
  have hz : 0 < z := div_pos (core_sum_pos x D) hr
  have hcard : ((coreSet x D).card : ℝ) = (a : ℝ) + 1 := by
    exact_mod_cast core_card x D
  have hv (i : Label a h) (hi : i ∈ coreSet x D) : u ≤ (h : ℝ) * y x i := by
    have hb := tail_bounds x D
    have hhi : 0 < (h : ℝ) := by
      exact_mod_cast (show 0 < h from D.nonempty.card_pos.trans_eq D.card_eq)
    have hdi := hb.2.2.2.1 i (Finset.mem_sdiff.mp hi).2
    have hu := (div_le_iff₀ hhi).mp hb.2.2.2.2
    nlinarith
  have huz : u ≤ (h : ℝ) * z := by
    have hh : (∑ _i ∈ coreSet x D, u) ≤
        ∑ i ∈ coreSet x D, (h : ℝ) * y x i :=
      Finset.sum_le_sum hv
    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hcard] at hh
    rw [coreSet, core_sum x D] at hh
    dsimp [z]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hr).mpr
    nlinarith
  have ht := Finset.sum_le_sum fun i hi =>
    core_tangent (a := a) (h := h) u (y x i) z (y_pos x i) hz (hv i hi) huz ha
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, Finset.sum_sub_distrib, hcard] at ht
  have hsum : (∑ i ∈ coreSet x D, y x i) - ((a : ℝ) + 1) * z = 0 := by
    rw [coreSet, core_sum x D]
    dsimp [z, u]
    field_simp
    <;> ring
  rw [hsum, mul_zero, add_zero] at ht
  exact sub_nonneg.mpr ht

private theorem core_scalar_identity (D : TailChoice x) :
    ((a : ℝ) + 1) * coreFunction (a := a) (tailSum x D.D)
      (((a : ℝ) - tailSum x D.D) / (a + 1)) =
      (a : ℝ) * (a + 1)^2 - tailSum x D.D * correction x D := by
  have hr : (a : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have hu := ne_of_gt (core_sum_pos x D)
  unfold coreFunction correction
  field_simp
  <;> ring

private theorem tailEnergy_eq (D : TailChoice x) :
    tailEnergy x D =
      expect x (fun T => (K T)^2 * ∑ j ∈ T.1 ∩ D.D, (y x j)⁻¹^2) := by
  classical
  unfold tailEnergy expect
  apply Finset.sum_congr rfl
  intro T _
  split_ifs with ht
  · rfl
  · have hem : T.1 ∩ D.D = ∅ := Finset.card_eq_zero.mp (by
      change tailCount x D T = 0
      omega)
    simp [hem]

private theorem energy_split (D : TailChoice x) :
    H x = tailEnergy x D +
      expect x (fun T => (K T)^2 * ∑ i ∈ T.1 \ D.D, (y x i)⁻¹^2) := by
  rw [tailEnergy_eq, ← expect_add]
  unfold H expect
  apply Finset.sum_congr rfl
  intro T _
  dsimp only
  rw [← mul_add, Finset.sum_inter_add_sum_sdiff]

private theorem core_energy_lower (D : TailChoice x) :
    (∑ i ∈ coreSet x D, coreFunction (a := a) (tailSum x D.D) (y x i)) +
      expect x (fun T => Q (a := a) (coreCount x D T)) ≤
      expect x (fun T => (K T)^2 * ∑ i ∈ T.1 \ D.D, (y x i)⁻¹^2) := by
  classical
  have hmono :
      expect x (fun T => (coreCount x D T : ℝ)^2 *
        ∑ i ∈ T.1 \ D.D, (y x i)⁻¹^2) ≤
      expect x (fun T => (K T)^2 * ∑ i ∈ T.1 \ D.D, (y x i)⁻¹^2) := by
    apply expect_mono
    intro T
    have hk : (coreCount x D T : ℝ) ≤ K T := by
      dsimp [coreCount, K, cardValue]
      exact_mod_cast (Finset.card_le_card Finset.sdiff_subset : (T.1 \ D.D).card ≤ T.1.card)
    have hc : 0 ≤ (coreCount x D T : ℝ) := by positivity
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun i _ => sq_nonneg _)
    nlinarith
  have hwi := expect_weighted_incidence x (coreSet x D)
    (fun i => (y x i)⁻¹^2) (fun T => (coreCount x D T : ℝ)^2)
  simp only [coreSet, ← Finset.inter_sdiff_assoc, Finset.inter_univ] at hwi
  have hR : (∑ i ∈ coreSet x D, expect x (rho x D i)) =
      expect x (fun T => Q (a := a) (coreCount x D T)) := by
    rw [← show (fun T => ∑ i ∈ coreSet x D, rho x D i T) =
      (fun T => Q (a := a) (coreCount x D T)) from funext (sum_rho x D)]
    simp only [expect, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hl :
      (∑ i ∈ coreSet x D, (coreFunction (a := a) (tailSum x D.D) (y x i) +
        expect x (rho x D i))) ≤
      ∑ i ∈ coreSet x D,
        expect x (fun T => if i ∈ T.1 then (coreCount x D T : ℝ)^2 else 0) *
          (y x i)⁻¹^2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hr : 0 ≤ expect x (rho x D i) :=
      expect_nonneg x _ (rho_nonneg x D i hi)
    have hy := y_pos x i
    have hy1 := y_le_one x i
    have hdiv : expect x (rho x D i) ≤ expect x (rho x D i) / (y x i)^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hy)).mpr
      nlinarith [mul_nonneg hr (by nlinarith : 0 ≤ 1 - (y x i)^2)]
    calc
      _ ≤ coreFunction (a := a) (tailSum x D.D) (y x i) +
          expect x (rho x D i) / (y x i)^2 := by linarith
      _ = _ := by
        rw [mean_rho]
        unfold coreFunction
        field_simp
        <;> ring
  rw [Finset.sum_add_distrib, hR] at hl
  exact hl.trans (hwi.symm.le.trans hmono)

private theorem core_certificate (D : TailChoice x)
    (ha : 3 * (h : ℝ) * (2 * a + 1) ≤ (a : ℝ)^2) :
    0 ≤ jensenGap x D ∧
    0 ≤ expect x (fun T => Q (a := a) (coreCount x D T)) ∧
    tailEnergy x D - tailSum x D.D * correction x D +
      expect x (fun T => Q (a := a) (coreCount x D T)) + jensenGap x D ≤ d x := by
  refine ⟨jensen_nonneg x D ha, expect_nonneg x _ (Q_nonneg x D), ?_⟩
  have he := energy_split x D
  have hl := core_energy_lower x D
  have hs := core_scalar_identity x D
  unfold jensenGap d
  linarith

end JointArray

def Lemma134ProducerStatement (a h : ℕ) : Prop :=
  4 ≤ a → 2 ≤ h → 3 * (h : ℝ) * (2 * a + 1) ≤ (a : ℝ)^2 →
    ∀ (x : JointArray a h) (D : x.TailChoice),
      let C := JointArray.coreSet x D
      let u := JointArray.tailSum x D.D
      let δ := JointArray.delta x D
      δ ≤ JointArray.tailEventMass x D ∧
      JointArray.tailEventMass x D ≤ u ∧ u ≤ h * JointArray.tailEventMass x D ∧
      (∀ i ∈ C, δ ≤ JointArray.y x i) ∧ u / (h : ℝ) ≤ δ ∧
      0 ≤ JointArray.jensenGap x D ∧
      0 ≤ JointArray.expect x (fun T => JointArray.Q (a := a) (JointArray.coreCount x D T)) ∧
      JointArray.tailEnergy x D - u * JointArray.correction x D +
        JointArray.expect x (fun T => JointArray.Q (a := a) (JointArray.coreCount x D T)) +
          JointArray.jensenGap x D ≤ JointArray.d x

#print axioms JointArray.core_certificate

end

end D5.S3.Combinatorics.CDSO.LocalizationBootstrap
