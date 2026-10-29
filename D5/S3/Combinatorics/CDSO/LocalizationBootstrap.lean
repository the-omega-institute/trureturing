/- GID: D5/S3/Combinatorics/CDSO/LocalizationBootstrap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CDSO/LocalizationBootstrap
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Order.BigOperators.Ring.Finset]
   utility: none
   digest: Actual-array definitions and the faithful full statement of CDSO Lemma 13.5.
-/

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

private theorem count_split (D : TailChoice x) (T : NonemptyType a h) :
    tailCount x D T + coreCount x D T = T.1.card := by
  exact Finset.card_inter_add_card_sdiff T.1 D.D

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

theorem core_certificate (D : TailChoice x)
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

theorem tail_cauchy (D : TailChoice x) :
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

theorem rank_cutoff_localization (D : TailChoice x) (M ε : ℝ)
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
    exact (le_div_iff₀ hden).mp hsmall
  have hδ1 : δ ≤ 1 := by nlinarith
  have hδprod : (M + κ) * δ ≤ 1 / 100 := by nlinarith
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
  have hL : L ≤ (a : ℝ) * p / 10 := by nlinarith
  have hβ : 3 * (a : ℝ)^2 + 3 * a + 1 ≤ 7 * (a : ℝ)^2 := by nlinarith
  have hβL : (3 * (a : ℝ)^2 + 3 * a + 1) * L ≤
      7 * (a : ℝ)^2 * ((a : ℝ) * p / 10) :=
    mul_le_mul hβ hL hL0 (by positivity)
  have hκa : κ ≤ (a : ℝ) / 100 := by dsimp [κ]; linarith
  have hcost : κ * (a : ℝ)^2 * p ≤ (a : ℝ)^3 * p / 100 := by
    have hh := mul_le_mul_of_nonneg_right hκa (by positivity : 0 ≤ (a : ℝ)^2 * p)
    nlinarith
  have hα : 2 * (a : ℝ)^3 * p ≤ (a : ℝ) * (a + 1) * (2 * a + 1) * p := by
    have hh := mul_le_mul_of_nonneg_right
      (show 2 * (a : ℝ)^3 ≤ (a : ℝ) * (a + 1) * (2 * a + 1) by nlinarith) hp.le
    exact hh
  have hQ := Q_tail_lower x D
  dsimp [L, p, κ, E] at *
  nlinarith [hc.2.2, hc.1, ht]

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
      q * (p * q) = (a : ℝ)^3 * p := by rw [← hq2]; ring
      _ ≤ d x := by linarith
      _ ≤ M * q := hd
      _ = q * M := mul_comm _ _
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
        nlinarith [mul_nonneg (sq_nonneg (M^2 + 1)) (sq_nonneg p),
          mul_nonneg (by nlinarith [sq_nonneg (M^2)] : 0 ≤ (M^2 + 1)^2 - M^2) (sq_nonneg p)]
  have hL : L ≤ (M^2 + 1) * p := by
    have hn : 0 ≤ (M^2 + 1) * p := by positivity
    nlinarith
  have hβ : 3 * (a : ℝ)^2 + 3 * a + 1 ≤ 7 * (a : ℝ)^2 := by nlinarith
  have hβL := mul_le_mul hβ hL hL0 (by positivity : 0 ≤ 7 * (a : ℝ)^2)
  have hah : 2 * (h : ℝ) ≤ (a : ℝ) := by linarith
  have hc := core_certificate x D hcond
  have ht := tail_correction_bound x D ha hah
  have hQ := Q_tail_lower x D
  have hα : 2 * (a : ℝ)^3 * p ≤ (a : ℝ) * (a + 1) * (2 * a + 1) * p :=
    mul_le_mul_of_nonneg_right
      (show 2 * (a : ℝ)^3 ≤ (a : ℝ) * (a + 1) * (2 * a + 1) by nlinarith) hp.le
  refine ⟨hqp, huq, hEq, ?_⟩
  dsimp [p, E, L] at *
  nlinarith [hc.2.2, hc.1, ht]

#print axioms core_certificate
#print axioms tail_cauchy
#print axioms rank_cutoff_localization
#print axioms refined_bootstrap


end JointArray

abbrev IndexAtLeast4 := {a : ℕ // 4 ≤ a}

def scale (a : IndexAtLeast4) (q : ℝ) : ℝ := Real.rpow (a : ℝ) q

def EventuallyAtLeast (P : IndexAtLeast4 → Prop) : Prop := ∀ᶠ a in atTop, P a

def EventuallyAfter (N : ℝ) (P : IndexAtLeast4 → Prop) : Prop :=
  ∀ᶠ (a : IndexAtLeast4) in atTop, N ≤ (a : ℝ) → P a

def FullLowerChain (h : ℕ) (M : ℝ)
    (x : ∀ a : IndexAtLeast4, JointArray a h)
    (D : ∀ a : IndexAtLeast4, (x a).TailChoice) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℝ, 0 < N ∧ EventuallyAfter N (fun a =>
    JointArray.d (x a) ≥
        JointArray.tailEnergy (x a) (D a) +
          (2 * (a : ℝ)^3 - C * (a : ℝ)^2) *
            JointArray.tailEventMass (x a) (D a) ∧
    JointArray.tailEnergy (x a) (D a) +
          (2 * (a : ℝ)^3 - C * (a : ℝ)^2) *
            JointArray.tailEventMass (x a) (D a) ≥
        ((h : ℝ)^2) / JointArray.tailEventMass (x a) (D a) +
          (2 * (a : ℝ)^3 - C * (a : ℝ)^2) *
            JointArray.tailEventMass (x a) (D a))

def Lemma135Statement (h : ℕ) (M : ℝ) : Prop :=
  2 ≤ h ∧ 0 < M →
  ∀ (x : ∀ a : IndexAtLeast4, JointArray a h)
    (D : ∀ a : IndexAtLeast4, (x a).TailChoice),
    EventuallyAtLeast (fun a => JointArray.d (x a) ≤ M * scale a (3 / 2 : ℝ)) →
      Tendsto (fun a => JointArray.delta (x a) (D a)) atTop (𝓝 0) ∧
      (∃ Cp Cu CH N : ℝ, 0 < Cp ∧ 0 < Cu ∧ 0 < CH ∧ 0 < N ∧
        EventuallyAfter N (fun a =>
          JointArray.tailEventMass (x a) (D a) ≤ Cp * scale a (-3 / 2 : ℝ) ∧
          JointArray.tailSum (x a) (D a).D ≤ Cu * scale a (-3 / 2 : ℝ) ∧
          JointArray.tailEnergy (x a) (D a) ≤ CH * scale a (3 / 2 : ℝ))) ∧
      FullLowerChain h M x D

def Lemma134ProducerStatement (a h : ℕ) : Prop :=
  4 ≤ a → 2 ≤ h → ∀ (x : JointArray a h)
    (D : (x).TailChoice),
      let C := Finset.univ \ D.D
      let u := JointArray.tailSum x D.D
      let δ := JointArray.delta x D
      δ ≤ JointArray.tailEventMass x D ∧
      JointArray.tailEventMass x D ≤ u ∧ u ≤ h * JointArray.tailEventMass x D ∧
      (∀ i ∈ C, δ ≤ JointArray.y x i) ∧ u / (h : ℝ) ≤ δ

end

end D5.S3.Combinatorics.CDSO.LocalizationBootstrap
