/- GID: D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/PeriodicGridCoverLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Flat binary periodic grid labels have unique anchored twisted integer-grid lifts. -/

import D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift

open PeriodicGridHolonomy

private def index (n : ℕ) [NeZero n] (i : ℤ) : Fin n :=
  ⟨(i % n).toNat, by
    have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
    have hr := Int.emod_lt_of_pos i hn
    omega⟩

private theorem index_val (n : ℕ) [NeZero n] (i : ℤ) :
    ((index n i).val : ℤ) = i % n := by
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  simp [index, Int.toNat_of_nonneg (Int.emod_nonneg _ hn)]

private theorem index_zero (n : ℕ) [NeZero n] : index n 0 = 0 := by
  apply Fin.ext
  simp [index]

private theorem index_period (n : ℕ) [NeZero n] (i : ℤ) :
    index n (i + n) = index n i := by
  apply Fin.ext
  rw [← Int.ofNat_inj]
  simp only [index_val]
  simp

private theorem index_step (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (i : ℤ) :
    index n (i + 1) = index n i + 1 := by
  apply Fin.ext
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hstep : (i + 1) % n = (i % n + 1) % n := by
    simp only [Int.add_emod, Int.emod_emod]
  have hone : (1 : Fin n).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  apply Int.ofNat_inj.mp
  simp only [Fin.val_add, hone, Int.natCast_mod, Nat.cast_add, index_val]
  exact hstep

private def seamPrimitive (n : ℕ) (i : ℤ) : ZMod 2 := (i / n : ℤ)

private theorem seamPrimitive_period (n : ℕ) [NeZero n] (i : ℤ) :
    seamPrimitive n (i + n) = seamPrimitive n i + 1 := by
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simp only [seamPrimitive]
  rw [Int.add_ediv_of_dvd_right (dvd_refl (n : ℤ))]
  rw [Int.ediv_self hn]
  push_cast
  rfl

private theorem seamPrimitive_step (n : ℕ) [NeZero n] (i : ℤ) :
    seamPrimitive n (i + 1) + seamPrimitive n i =
      if (index n i).val + 1 = n then 1 else 0 := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hr0 : 0 ≤ i % n := Int.emod_nonneg _ (by omega)
  have hrn : i % n < n := Int.emod_lt_of_pos i hn
  have hdecomp := Int.emod_add_ediv_mul i (n : ℤ)
  have hdiv : (i + 1) / n = i / n + (i % n + 1) / n := by
    conv_lhs => lhs; arg 1; rw [← hdecomp]
    rw [show i % (n : ℤ) + i / n * n + 1 = i / n * n + (i % n + 1) by ring]
    rw [Int.add_ediv_of_dvd_left (show (n : ℤ) ∣ i / n * n from
      ⟨i / n, by ring⟩)]
    rw [Int.mul_ediv_cancel _ (by omega : (n : ℤ) ≠ 0)]
  by_cases h : (index n i).val + 1 = n
  · have hh : i % n + 1 = n := by
      rw [← index_val]
      exact_mod_cast h
    have hq : (i % n + 1) / n = 1 := by
      rw [hh]
      exact Int.ediv_self (by omega : (n : ℤ) ≠ 0)
    rw [hq] at hdiv
    simp only [seamPrimitive, if_pos h, hdiv, Int.cast_add, Int.cast_one]
    have ht (z : ZMod 2) : z + 1 + z = 1 := by
      calc
        z + 1 + z = (z + z) + 1 := by abel
        _ = 1 := by rw [ZModModule.add_self, zero_add]
    exact ht _
  · have hh : i % n + 1 < n := by
      have hv := index_val n i
      omega
    have hq : (i % n + 1) / n = 0 :=
      Int.ediv_eq_zero_of_lt (by omega) hh
    simp only [seamPrimitive, if_neg h, hdiv, hq, add_zero]
    exact ZModModule.add_self _

def pulledHorizontal {M N : ℕ} [NeZero M] [NeZero N]
    (y : EdgeLabel M N) (i j : ℤ) : ZMod 2 :=
  y.horizontal (index M i) (index N j)

def pulledVertical {M N : ℕ} [NeZero M] [NeZero N]
    (y : EdgeLabel M N) (i j : ℤ) : ZMod 2 :=
  y.vertical (index M i) (index N j)

def IsCoverLift {M N : ℕ} [NeZero M] [NeZero N]
    (y : EdgeLabel M N) (a : ZMod 2) (x : ℤ → ℤ → ZMod 2) : Prop :=
  x 0 0 = a ∧
    (∀ i j, x i (j + 1) + x i j = pulledHorizontal y i j) ∧
    (∀ i j, x (i + 1) j + x i j = pulledVertical y i j) ∧
    (∀ i j, x i (j + N) = x i j + rowHolonomy y 0) ∧
    (∀ i j, x (i + M) j = x i j + columnHolonomy y 0)

theorem flat_unique_cover_lift {M N : ℕ} [NeZero M] [NeZero N]
    (_hM : 3 ≤ M) (_hN : 3 ≤ N) (y : EdgeLabel M N) (hy : Flat y)
    (a : ZMod 2) : ∃! x : ℤ → ℤ → ZMod 2, IsCoverLift y a x := by
  obtain ⟨v, hv0, hs, hu⟩ := flat_decomposition y hy
  let h := rowHolonomy y 0
  let u := columnHolonomy y 0
  let x : ℤ → ℤ → ZMod 2 := fun i j =>
    a + v (index M i) (index N j) + seamPrimitive M i * u + seamPrimitive N j * h
  have hx0 : x 0 0 = a := by
    simp [x, index_zero, seamPrimitive, hv0]
  have hhorizontal : ∀ i j, x i (j + 1) + x i j = pulledHorizontal y i j := by
    intro i j
    have hq := seamPrimitive_step N j
    have hh := hs (index M i) (index N j)
    simp only [gradient, seam] at hh
    change _ = y.horizontal (index M i) (index N j)
    rw [hh]
    have hn2 : 2 ≤ N := by omega
    simp only [x, index_step N hn2]
    have ha := ZModModule.add_self a
    have hu' := ZModModule.add_self (seamPrimitive M i * u)
    calc
      _ = v (index M i) (index N j + 1) + v (index M i) (index N j) +
          (seamPrimitive N (j + 1) * h + seamPrimitive N j * h) := by
            calc
              _ = (v (index M i) (index N j + 1) + v (index M i) (index N j)) +
                  (a + a) + (seamPrimitive M i * u + seamPrimitive M i * u) +
                  (seamPrimitive N (j + 1) * h + seamPrimitive N j * h) := by abel_nf
              _ = _ := by rw [ha, hu']; simp
      _ = _ := by rw [← add_mul, hq]; split <;> simp [h]
  have hvertical : ∀ i j, x (i + 1) j + x i j = pulledVertical y i j := by
    intro i j
    have hq := seamPrimitive_step M i
    have hh := hu (index M i) (index N j)
    simp only [gradient, seam] at hh
    change _ = y.vertical (index M i) (index N j)
    rw [hh]
    have hm2 : 2 ≤ M := by omega
    simp only [x, index_step M hm2]
    have ha := ZModModule.add_self a
    have hh' := ZModModule.add_self (seamPrimitive N j * h)
    calc
      _ = v (index M i + 1) (index N j) + v (index M i) (index N j) +
          (seamPrimitive M (i + 1) * u + seamPrimitive M i * u) := by
            calc
              _ = (v (index M i + 1) (index N j) + v (index M i) (index N j)) +
                  (a + a) + (seamPrimitive N j * h + seamPrimitive N j * h) +
                  (seamPrimitive M (i + 1) * u + seamPrimitive M i * u) := by abel_nf
              _ = _ := by rw [ha, hh']; simp
      _ = _ := by rw [← add_mul, hq]; split <;> simp [u]
  have htwistH : ∀ i j, x i (j + N) = x i j + h := by
    intro i j
    simp only [x, index_period, seamPrimitive_period]
    ring
  have htwistV : ∀ i j, x (i + M) j = x i j + u := by
    intro i j
    simp only [x, index_period, seamPrimitive_period]
    ring
  refine ⟨x, ⟨hx0, hhorizontal, hvertical, htwistH, htwistV⟩, ?_⟩
  intro z hz
  have rearrange (p q r s : ZMod 2) (hp : p + q = r + s) : p + r = q + s := by
    have hq := ZModModule.add_self q
    have hs := ZModModule.add_self s
    calc
      p + r = p + r + (q + q) + (s + s) := by rw [hq, hs]; simp
      _ = (p + q) + (r + s) + (q + s) := by abel
      _ = q + s := by rw [hp, ZModModule.add_self, zero_add]
  have hstepH (i j : ℤ) :
      z i (j + 1) + x i (j + 1) = z i j + x i j := by
    exact rearrange _ _ _ _ ((hz.2.1 i j).trans (hhorizontal i j).symm)
  have hstepV (i j : ℤ) :
      z (i + 1) j + x (i + 1) j = z i j + x i j := by
    exact rearrange _ _ _ _ ((hz.2.2.1 i j).trans (hvertical i j).symm)
  have int_constant_of_step (f : ℤ → ZMod 2)
      (hf : ∀ i, f (i + 1) = f i) : ∀ i, f i = f 0 := by
    intro i
    induction i using Int.induction_on with
    | zero => rfl
    | succ i hi => exact (hf i).trans hi
    | pred i hi =>
        have h := hf (-(i : ℤ) - 1)
        have heq : -(i : ℤ) - 1 + 1 = -(i : ℤ) := by omega
        rw [heq] at h
        have hindex : Int.negSucc i = -(i : ℤ) - 1 := by omega
        simpa only [hindex] using h.symm.trans hi
  have hdiff : ∀ i j, z i j + x i j = 0 := by
    intro i j
    calc
      z i j + x i j = z i 0 + x i 0 :=
        int_constant_of_step (fun j => z i j + x i j) (hstepH i) j
      _ = z 0 0 + x 0 0 :=
        int_constant_of_step (fun i => z i 0 + x i 0) (fun i => hstepV i 0) i
      _ = 0 := by rw [hz.1, hx0]; exact ZModModule.add_self a
  funext i j
  have hh := hdiff i j
  exact add_right_cancel (hh.trans (ZModModule.add_self (x i j)).symm)

#print axioms flat_unique_cover_lift

end D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift
