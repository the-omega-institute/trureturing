/- GID: D5/S3/Arith/Covering/FixedCollisionExceptions
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/FixedCollisionExceptions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed pairs meet ordinary-prime collisions in sum-minimal shallow odd covers. -/

import D5.S3.Arith.Congruence.ConditionalComparison.ArithmeticCoordinates
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos7.OddDistinctCoveringSystem

open scoped BigOperators

variable {L : ℕ}

/-- All positive five depths at one complete ternary word and first-five root. -/
def collisionTop (F : OddDistinctCoveringSystem L) (u omega : ℕ) (i : Fin L) : Prop :=
  45 ∣ F.modulus i ∧ F.residue i ≡ u [MOD 9] ∧ F.residue i ≡ omega [MOD 5]

/-- A literal collision at an ordinary prime of the original moduli. -/
def ordinaryPrimeCollision (F : OddDistinctCoveringSystem L) (i j : Fin L) : Prop :=
  i ≠ j ∧ ∃ p : ℕ, Nat.Prime p ∧ p ≠ 3 ∧ p ≠ 5 ∧
    p ∣ F.modulus i ∧ p ∣ F.modulus j ∧ F.residue i ≡ F.residue j [MOD p]

private theorem fresh_four_slot_descent
    (F : OddDistinctCoveringSystem L)
    (hsumMin : ∀ H : OddDistinctCoveringSystem L,
      (∑ i, F.modulus i) ≤ ∑ i, H.modulus i)
    (slot : Fin 4 ↪ Fin L) (m a : Fin 4 → ℕ)
    (hm : ∀ t, 1 < m t) (ho : ∀ t, Odd (m t))
    (hinj : Function.Injective m)
    (hfresh : ∀ t i, m t ≠ F.modulus i)
    (hcover : ∀ x t, x ≡ F.residue (slot t) [MOD F.modulus (slot t)] →
      ∃ s, x ≡ a s [MOD m s])
    (hcost : (∑ t, m t) < ∑ t, F.modulus (slot t)) : False := by
  classical
  let changed (i : Fin L) : Prop := ∃ t, slot t = i
  let newMod (i : Fin L) : ℕ :=
    if h : changed i then m (Classical.choose h) else F.modulus i
  let newRes (i : Fin L) : ℕ :=
    if h : changed i then a (Classical.choose h) else F.residue i
  have hat (t : Fin 4) : newMod (slot t) = m t ∧ newRes (slot t) = a t := by
    have hc : changed (slot t) := ⟨t, rfl⟩
    have ht : Classical.choose hc = t := slot.injective (Classical.choose_spec hc)
    constructor <;> simp only [newMod, newRes, dif_pos hc, ht]
  have hoff (i : Fin L) (hi : ¬ changed i) :
      newMod i = F.modulus i ∧ newRes i = F.residue i := by
    constructor <;> simp only [newMod, newRes, dif_neg hi]
  have hnewCover : ∀ x : ℕ, ∃ i, x ≡ newRes i [MOD newMod i] := by
    intro x
    obtain ⟨i, hxi⟩ := F.covers x
    by_cases hi : changed i
    · obtain ⟨t, rfl⟩ := hi
      obtain ⟨s, hs⟩ := hcover x t hxi
      exact ⟨slot s, by simpa only [(hat s).1, (hat s).2] using hs⟩
    · exact ⟨i, by simpa only [(hoff i hi).1, (hoff i hi).2] using hxi⟩
  have hnewInjective : Function.Injective newMod := by
    intro i j hij
    by_cases hi : changed i
    · obtain ⟨t, rfl⟩ := hi
      by_cases hj : changed j
      · obtain ⟨s, rfl⟩ := hj
        have hts : t = s := hinj (by simpa only [(hat t).1, (hat s).1] using hij)
        exact congrArg slot hts
      · exact False.elim (hfresh t j (by simpa only [(hat t).1, (hoff j hj).1] using hij))
    · by_cases hj : changed j
      · obtain ⟨s, rfl⟩ := hj
        exact False.elim (hfresh s i (by simpa only [(hoff i hi).1, (hat s).1] using hij.symm))
      · exact F.modulus_injective (by simpa only [(hoff i hi).1, (hoff j hj).1] using hij)
  let H : OddDistinctCoveringSystem L :=
    { modulus := newMod
      residue := newRes
      covers := hnewCover
      modulus_one_lt := by
        intro i
        by_cases hi : changed i
        · obtain ⟨t, rfl⟩ := hi
          simpa only [(hat t).1] using hm t
        · simpa only [(hoff i hi).1] using F.modulus_one_lt i
      modulus_odd := by
        intro i
        by_cases hi : changed i
        · obtain ⟨t, rfl⟩ := hi
          simpa only [(hat t).1] using ho t
        · simpa only [(hoff i hi).1] using F.modulus_odd i
      modulus_injective := hnewInjective }
  let K : Finset (Fin L) := Finset.univ.map slot
  have hKnew : (∑ i ∈ K, newMod i) = ∑ t, m t := by
    dsimp only [K]
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl (fun t _ => (hat t).1)
  have hKold : (∑ i ∈ K, F.modulus i) = ∑ t, F.modulus (slot t) := by
    simp only [K, Finset.sum_map]
  have hoffsum : (∑ i ∈ Kᶜ, newMod i) = ∑ i ∈ Kᶜ, F.modulus i := by
    apply Finset.sum_congr rfl
    intro i hi
    apply (hoff i _).1
    intro hc
    apply (Finset.mem_compl.mp hi)
    simpa only [K, Finset.mem_map, Finset.mem_univ, true_and] using hc
  have hn := Finset.sum_add_sum_compl K newMod
  have hF := Finset.sum_add_sum_compl K F.modulus
  rw [hKnew, hoffsum] at hn
  rw [hKold] at hF
  have hmin := hsumMin H
  change (∑ i, F.modulus i) ≤ ∑ i, newMod i at hmin
  omega

theorem collision_prime_arithmetic
    (F : OddDistinctCoveringSystem L) (i : Fin L)
    (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (hpd : p ∣ F.modulus i) :
    Odd p ∧ 5 ≤ p ∧ Nat.Coprime 27 p ∧ Nat.Coprime 45 p ∧ Nat.Coprime 5 p := by
  have hodd : Odd p := (F.modulus_odd i).of_dvd_nat hpd
  have hp2 : p ≠ 2 := by intro h; subst p; norm_num at hodd
  have hpge := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  have h3 : Nat.Coprime 3 p := by
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h
    · exact hp.ne_one h
    · exact hp3 h
  have h5 : Nat.Coprime 5 p := by
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
    · exact hp.ne_one h
    · exact hp5 h
  have h27 : Nat.Coprime 27 p := by simpa using h3.pow_left 3
  have h45 : Nat.Coprime 45 p := by
    have h := Nat.coprime_mul_iff_left.mpr ⟨h3.pow_left 2, h5⟩
    simpa using h
  exact ⟨hodd, hpge, h27, h45, h5⟩

private theorem ternary_third_digit (x u : ℕ) (h : x ≡ u [MOD 9]) :
    x ≡ u % 9 [MOD 27] ∨ x ≡ u % 9 + 9 [MOD 27] ∨
      x ≡ u % 9 + 18 [MOD 27] := by
  have hx : x % 9 = u % 9 := h
  have hu := Nat.mod_lt u (by decide : 0 < (9 : ℕ))
  have hx27 := Nat.mod_lt x (by decide : 0 < (27 : ℕ))
  have hxmod := Nat.mod_mod_of_dvd x (by decide : 9 ∣ 27)
  change x % 27 = (u % 9) % 27 ∨ x % 27 = (u % 9 + 9) % 27 ∨
    x % 27 = (u % 9 + 18) % 27
  rw [Nat.mod_eq_of_lt (by omega : u % 9 < 27),
    Nat.mod_eq_of_lt (by omega : u % 9 + 9 < 27),
    Nat.mod_eq_of_lt (by omega : u % 9 + 18 < 27)]
  omega

private theorem distinct_positive_multiples_pair
    (d a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hda : d ∣ a) (hdb : d ∣ b) (hne : a ≠ b) : 3 * d ≤ a + b := by
  obtain ⟨v, hv⟩ := hda
  obtain ⟨w, hw⟩ := hdb
  have hvpos : 0 < v := by
    by_contra h
    have : v = 0 := by omega
    simp only [this, mul_zero] at hv
    omega
  have hwpos : 0 < w := by
    by_contra h
    have : w = 0 := by omega
    simp only [this, mul_zero] at hw
    omega
  have hvw : v ≠ w := by intro h; apply hne; simp only [hv, hw, h]
  have hsum : 3 ≤ v + w := by omega
  calc
    3 * d ≤ (v + w) * d := Nat.mul_le_mul_right d hsum
    _ = a + b := by rw [hv, hw]; ring

-- The two four-slot CRT constructions need a local elaboration budget.
set_option maxHeartbeats 800000 in
/-- Two disjoint literal ordinary-prime collisions admit a strict four-slot descent. -/
theorem no_disjoint_ordinary_prime_collisions
    (F : OddDistinctCoveringSystem L)
    (hsumMin : ∀ H : OddDistinctCoveringSystem L,
      (∑ i, F.modulus i) ≤ ∑ i, H.modulus i)
    (hno27 : ∀ i, ¬ 27 ∣ F.modulus i)
    (u omega : ℕ) (slot : Fin 4 ↪ Fin L)
    (htop : ∀ t, collisionTop F u omega (slot t))
    (hedgeP : ordinaryPrimeCollision F (slot 0) (slot 1))
    (hedgeR : ordinaryPrimeCollision F (slot 2) (slot 3)) : False := by
  classical
  obtain ⟨_, p, hp, hp3, hp5, hp0, hp1, hpEq⟩ := hedgeP
  obtain ⟨_, r, hr, hr3, hr5, hr2, hr3d, hrEq⟩ := hedgeR
  obtain ⟨hpo, hpge, hp27, hp45, hpFive⟩ := collision_prime_arithmetic F (slot 0) p hp hp3 hp5 hp0
  obtain ⟨hro, hrge, hr27, hr45, hrFive⟩ := collision_prime_arithmetic F (slot 2) r hr hr3 hr5 hr2
  have hp0full : 45 * p ∣ F.modulus (slot 0) := hp45.mul_dvd_of_dvd_of_dvd (htop 0).1 hp0
  have hp1full : 45 * p ∣ F.modulus (slot 1) := hp45.mul_dvd_of_dvd_of_dvd (htop 1).1 hp1
  have hr2full : 45 * r ∣ F.modulus (slot 2) := hr45.mul_dvd_of_dvd_of_dvd (htop 2).1 hr2
  have hr3full : 45 * r ∣ F.modulus (slot 3) := hr45.mul_dvd_of_dvd_of_dvd (htop 3).1 hr3d
  have hp0le := Nat.le_of_dvd (Nat.zero_lt_of_lt (F.modulus_one_lt (slot 0))) hp0full
  have hp1le := Nat.le_of_dvd (Nat.zero_lt_of_lt (F.modulus_one_lt (slot 1))) hp1full
  have hr2le := Nat.le_of_dvd (Nat.zero_lt_of_lt (F.modulus_one_lt (slot 2))) hr2full
  have hr3le := Nat.le_of_dvd (Nat.zero_lt_of_lt (F.modulus_one_lt (slot 3))) hr3full
  let b := F.residue (slot 0)
  let c := F.residue (slot 2)
  let a5 := (Nat.chineseRemainder (by decide : Nat.Coprime 27 5) (u % 9 + 9) omega).val
  let ap := (Nat.chineseRemainder hp27 (u % 9 + 18) b).val
  have hx9 (x : ℕ) (t : Fin 4) (hx : x ≡ F.residue (slot t) [MOD F.modulus (slot t)]) :
      x ≡ u [MOD 9] :=
    (hx.of_dvd ((by decide : 9 ∣ 45).trans (htop t).1)).trans (htop t).2.1
  have hx5 (x : ℕ) (t : Fin 4) (hx : x ≡ F.residue (slot t) [MOD F.modulus (slot t)]) :
      x ≡ omega [MOD 5] :=
    (hx.of_dvd ((by decide : 5 ∣ 45).trans (htop t).1)).trans (htop t).2.2
  by_cases hpr : p = r
  · subst r
    let cp := (Nat.chineseRemainder hpFive omega c).val
    have h27fivep : Nat.Coprime 27 (5 * p) :=
      Nat.coprime_mul_iff_right.mpr ⟨by decide, hp27⟩
    let aqp := (Nat.chineseRemainder h27fivep (u % 9 + 18) cp).val
    let m : Fin 4 → ℕ := ![27, 135, 27 * p, 135 * p]
    let a : Fin 4 → ℕ := ![u % 9, a5, ap, aqp]
    apply fresh_four_slot_descent F hsumMin slot m a
    · intro t
      fin_cases t
      · change 1 < 27
        omega
      · change 1 < 135
        omega
      · change 1 < 27 * p
        omega
      · change 1 < 135 * p
        omega
    · intro t
      fin_cases t
      · exact (by decide : Odd 27)
      · exact (by decide : Odd 135)
      · exact (by decide : Odd 27).mul hpo
      · exact (by decide : Odd 135).mul hpo
    · intro s t h
      fin_cases s <;> fin_cases t
      all_goals first
        | rfl
        | (exfalso
           simp only [m, Matrix.cons_val_zero', Matrix.cons_val_succ'] at h <;> omega)
    · intro t i h
      apply hno27 i
      rw [← h]
      fin_cases t
      · exact dvd_refl 27
      · exact ⟨5, rfl⟩
      · exact ⟨p, rfl⟩
      · exact ⟨5 * p, by dsimp [m]; ring⟩
    · intro x t hx
      rcases ternary_third_digit x u (hx9 x t hx) with h0 | h1 | h2
      · exact ⟨0, by simpa only [a, m, Matrix.cons_val_zero] using h0⟩
      · refine ⟨1, ?_⟩
        simpa [a, m, a5] using Nat.chineseRemainder_modEq_unique
          (by decide : Nat.Coprime 27 5) h1 (hx5 x t hx)
      · fin_cases t
        · refine ⟨2, ?_⟩
          simpa [a, m, ap, b] using Nat.chineseRemainder_modEq_unique hp27 h2 (hx.of_dvd hp0)
        · refine ⟨2, ?_⟩
          simpa [a, m, ap, b] using Nat.chineseRemainder_modEq_unique hp27 h2
            ((hx.of_dvd hp1).trans hpEq.symm)
        · refine ⟨3, ?_⟩
          have hpC := Nat.chineseRemainder_modEq_unique hpFive (hx5 x 2 hx) (hx.of_dvd hr2)
          simpa [a, m, aqp, cp, c, ← Nat.mul_assoc] using
            Nat.chineseRemainder_modEq_unique h27fivep h2 hpC
        · refine ⟨3, ?_⟩
          have hpC := Nat.chineseRemainder_modEq_unique hpFive (hx5 x 3 hx)
            ((hx.of_dvd hr3d).trans hrEq.symm)
          simpa [a, m, aqp, cp, c, ← Nat.mul_assoc] using
            Nat.chineseRemainder_modEq_unique h27fivep h2 hpC
    · have hne : F.modulus (slot 0) ≠ F.modulus (slot 1) := by
        intro he
        have h := slot.injective (F.modulus_injective he)
        norm_num at h
      have hpair := distinct_positive_multiples_pair (45 * p)
        (F.modulus (slot 0)) (F.modulus (slot 1))
        (Nat.zero_lt_of_lt (F.modulus_one_lt (slot 0)))
        (Nat.zero_lt_of_lt (F.modulus_one_lt (slot 1))) hp0full hp1full hne
      rw [Fin.sum_univ_four, Fin.sum_univ_four]
      change 27 + 135 + 27 * p + 135 * p < _
      omega
  · let ar := (Nat.chineseRemainder hr27 (u % 9 + 18) c).val
    let m : Fin 4 → ℕ := ![27, 135, 27 * p, 27 * r]
    let a : Fin 4 → ℕ := ![u % 9, a5, ap, ar]
    apply fresh_four_slot_descent F hsumMin slot m a
    · intro t
      fin_cases t
      · change 1 < 27
        omega
      · change 1 < 135
        omega
      · change 1 < 27 * p
        omega
      · change 1 < 27 * r
        omega
    · intro t
      fin_cases t
      · exact (by decide : Odd 27)
      · exact (by decide : Odd 135)
      · exact (by decide : Odd 27).mul hpo
      · exact (by decide : Odd 27).mul hro
    · intro s t h
      fin_cases s <;> fin_cases t
      all_goals first
        | rfl
        | (exfalso
           simp only [m, Matrix.cons_val_zero', Matrix.cons_val_succ'] at h <;> omega)
    · intro t i h
      apply hno27 i
      rw [← h]
      fin_cases t
      · exact dvd_refl 27
      · exact ⟨5, rfl⟩
      · exact ⟨p, rfl⟩
      · exact ⟨r, rfl⟩
    · intro x t hx
      rcases ternary_third_digit x u (hx9 x t hx) with h0 | h1 | h2
      · exact ⟨0, by simpa only [a, m, Matrix.cons_val_zero] using h0⟩
      · refine ⟨1, ?_⟩
        simpa [a, m, a5] using Nat.chineseRemainder_modEq_unique
          (by decide : Nat.Coprime 27 5) h1 (hx5 x t hx)
      · fin_cases t
        · refine ⟨2, ?_⟩
          simpa [a, m, ap, b] using Nat.chineseRemainder_modEq_unique hp27 h2 (hx.of_dvd hp0)
        · refine ⟨2, ?_⟩
          simpa [a, m, ap, b] using Nat.chineseRemainder_modEq_unique hp27 h2
            ((hx.of_dvd hp1).trans hpEq.symm)
        · refine ⟨3, ?_⟩
          simpa [a, m, ar, c] using Nat.chineseRemainder_modEq_unique hr27 h2 (hx.of_dvd hr2)
        · refine ⟨3, ?_⟩
          simpa [a, m, ar, c] using Nat.chineseRemainder_modEq_unique hr27 h2
            ((hx.of_dvd hr3d).trans hrEq.symm)
    · rw [Fin.sum_univ_four, Fin.sum_univ_four]
      change 27 + 135 + 27 * p + 27 * r < _
      omega

/-- One fixed set of at most two originals meets every ordinary-prime collision,
independently of any cofactor point or source law. -/
theorem exists_fixed_collision_exceptions
    (F : OddDistinctCoveringSystem L)
    (hsumMin : ∀ H : OddDistinctCoveringSystem L,
      (∑ i, F.modulus i) ≤ ∑ i, H.modulus i)
    (hno27 : ∀ i, ¬ 27 ∣ F.modulus i) (u omega : ℕ) :
    ∃ X : Finset (Fin L),
      (∀ i ∈ X, collisionTop F u omega i) ∧ X.card ≤ 2 ∧
      ∀ i j, collisionTop F u omega i → collisionTop F u omega j →
        i ∉ X → j ∉ X → ¬ ordinaryPrimeCollision F i j := by
  classical
  by_cases hedge : ∃ i j, collisionTop F u omega i ∧ collisionTop F u omega j ∧
      ordinaryPrimeCollision F i j
  · obtain ⟨i, j, hTi, hTj, hE⟩ := hedge
    refine ⟨{i, j}, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hTi
      · exact hTj
    · have hij := hE.1
      simp [hij]
    · intro k l hTk hTl hk hl hEkl
      have hij : i ≠ j := hE.1
      have hkl : k ≠ l := hEkl.1
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk hl
      let slot : Fin 4 ↪ Fin L :=
        { toFun := ![i, j, k, l]
          inj' := by
            intro a b hab
            fin_cases a <;> fin_cases b <;> norm_num at hab ⊢ <;> simp_all }
      apply no_disjoint_ordinary_prime_collisions F hsumMin hno27 u omega slot
      · intro t
        fin_cases t
        · exact hTi
        · exact hTj
        · exact hTk
        · exact hTl
      · exact hE
      · exact hEkl
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro i j hi hj _ _ hE
    exact hedge ⟨i, j, hi, hj, hE⟩

end Erdos7.OddDistinctCoveringSystem
