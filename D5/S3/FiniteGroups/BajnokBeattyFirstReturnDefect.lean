/- GID: D5/S3/FiniteGroups/BajnokBeattyFirstReturnDefect
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyFirstReturnDefect
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The first signed word-return defect of the two actual Bajnok--Beatty quotients. -/

import D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth

/-!
proof_shape: kernel_at_n_19: content.
proof_shape: kernel_at_n_33: content.
proof_shape: word_fibers_from_kernels: content.
proof_shape: first_return_defect: content.
admission_basis: escape-witness.
escape_witness: the already compiled quotient equivalences reduce a short
word return to an integral divisibility problem.  The two coefficient rows
have no nonzero Lee relation below p * (m - 3); at that radius the second row has
exactly the two additional axial relations ±(p * (m - 3),0).  Equality in the
word endpoint norm forces the corresponding words to be constant.  The main
statement therefore compares actual endpoint fibers, rather than importing a
ball - cardinality identity.  No short - kernel or covering hypothesis is assumed.
No literature novelty or open - problem claim is made.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect

open D5.S3.FiniteGroups.NearSquareLatticeRigidity
open D5.S3.FiniteGroups.BajnokBeattyAsymmetricGrowth
open D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth

/-- The four signed coordinate steps in the integer plane. -/
def step : Fin 4 → Plane
  | 0 => ![(1 : ℤ), 0]
  | 1 => ![(-1 : ℤ), 0]
  | 2 => ![0, (1 : ℤ)]
  | 3 => ![0, (-1 : ℤ)]

/-- The endpoint of a length-`l` word. -/
def endpoint {l : ℕ} (w : Fin l → Fin 4) : Plane :=
  ∑ i : Fin l, step (w i)

/-- The actual signed word - return fiber of a quotient map. -/
def ReturnWords {G : Type*} [AddCommGroup G]
    (F : Plane →+ G) (l : ℕ) : Type :=
  {w : Fin l → Fin 4 // F (endpoint w) = 0}

/-- Its finite cardinality. -/
noncomputable def W {G : Type*} [AddCommGroup G]
    (F : Plane →+ G) (l : ℕ) : ℕ := Nat.card (ReturnWords F l)

private lemma scaled_lee_norm (p X Y : ℤ) (hp : 0 < p) :
    |(![p * X, p * Y] : Plane) 0| + |(![p * X, p * Y] : Plane) 1| =
      p * (|X| + |Y|) := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, abs_mul, abs_of_pos hp]
  ring

lemma endpoint_lee_bound {l : ℕ} (w : Fin l → Fin 4) :
    |endpoint w 0| + |endpoint w 1| ≤ (l : ℤ) := by
  have hx := Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin l)))
    (f := fun i => step (w i) 0)
  have hy := Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin l)))
    (f := fun i => step (w i) 1)
  have hunit : ∀ i : Fin l,
      |step (w i) 0| + |step (w i) 1| = (1 : ℤ) := by
    intro i
    generalize hw : w i = a
    fin_cases a <;> simp [step]
  calc
    |endpoint w 0| + |endpoint w 1| ≤
        (∑ i : Fin l, |step (w i) 0|) + (∑ i : Fin l, |step (w i) 1|) := by
            simpa only [endpoint, Finset.sum_apply] using add_le_add hx hy
    _ = ∑ i : Fin l, (|step (w i) 0| + |step (w i) 1|) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ _i : Fin l, (1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hunit i
    _ = (l : ℤ) := by simp

private lemma endpoint_const_pos (l : ℕ) :
    endpoint (fun _ : Fin l => (0 : Fin 4)) = ![(l : ℤ), 0] := by
  ext i
  fin_cases i
  · simp [endpoint, step]
  · simp [endpoint, step]

private lemma endpoint_const_neg (l : ℕ) :
    endpoint (fun _ : Fin l => (1 : Fin 4)) = ![-(l : ℤ), 0] := by
  ext i
  fin_cases i
  · simp [endpoint, step]
  · simp [endpoint, step]

private lemma positive_extremal_word {l : ℕ}
    (w : Fin l → Fin 4)
    (h : endpoint w = ![(l : ℤ), 0]) :
    w = fun _ : Fin l => (0 : Fin 4) := by
  have hx : (∑ i : Fin l, step (w i) 0) = (l : ℤ) := by
    simpa [endpoint] using congrFun h 0
  have hzero : ∑ i : Fin l, ((1 : ℤ) - step (w i) 0) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    omega
  have hnonneg : ∀ i : Fin l, 0 ≤ (1 : ℤ) - step (w i) 0 := by
    intro i
    generalize hw : w i = a
    fin_cases a <;> simp [step]
  have hterm : ∀ i : Fin l, (1 : ℤ) - step (w i) 0 = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hzero i (by simp)
  funext i
  have hcoord : step (w i) 0 = (1 : ℤ) := by have hi := hterm i; omega
  generalize hw : w i = a at hcoord ⊢
  fin_cases a <;> simp [step] at hcoord ⊢

private lemma negative_extremal_word {l : ℕ}
    (w : Fin l → Fin 4)
    (h : endpoint w = ![-(l : ℤ), 0]) :
    w = fun _ : Fin l => (1 : Fin 4) := by
  have hx : (∑ i : Fin l, step (w i) 0) = -(l : ℤ) := by
    simpa [endpoint] using congrFun h 0
  have hzero : ∑ i : Fin l, ((1 : ℤ) + step (w i) 0) = 0 := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    omega
  have hnonneg : ∀ i : Fin l, 0 ≤ (1 : ℤ) + step (w i) 0 := by
    intro i
    generalize hw : w i = a
    fin_cases a <;> simp [step]
  have hterm : ∀ i : Fin l, (1 : ℤ) + step (w i) 0 = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hzero i (by simp)
  funext i
  have hcoord : step (w i) 0 = (-1 : ℤ) := by have hi := hterm i; omega
  generalize hw : w i = a at hcoord ⊢
  fin_cases a <;> simp [step] at hcoord ⊢

private lemma kernel_characterization
    {G : Type*} [AddCommGroup G]
    (p D t : ℤ) (hp : 0 < p) (hD : 0 < D)
    (F : Plane →+ G) (e : G ≃+ (ZMod p.natAbs × ZMod (p * D).natAbs))
    (he : ∀ z : Plane, e (F z) =
      (((-z 0 + z 1 : ℤ) : ZMod p.natAbs),
        ((-3 * t * z 0 + (3 * t - 1) * z 1 : ℤ) : ZMod (p * D).natAbs))) :
    ∀ z : Plane, F z = 0 ↔
      ∃ X Y : ℤ, z = ![p * X, p * Y] ∧ D ∣ (-3 * t) * X + (3 * t - 1) * Y := by
  intro z
  constructor
  · intro hz
    have hcoord := congrArg Prod.snd (he z)
    have hfirst := congrArg Prod.fst (he z)
    rw [hz, map_zero] at hcoord hfirst
    have hfirst' : ((-z 0 + z 1 : ℤ) : ZMod p.natAbs) = 0 := by
      simpa using hfirst.symm
    have hsecond' : ((-3 * t * z 0 + (3 * t - 1) * z 1 : ℤ) : ZMod (p * D).natAbs) = 0 := by
      simpa using hcoord.symm
    have hpA : p ∣ -z 0 + z 1 := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (-z 0 + z 1) p.natAbs).mp hfirst'
      have hnat : (p.natAbs : ℤ) = p := by
        simp only [Int.natCast_natAbs, abs_of_pos hp]
      simpa [hnat] using h
    have hpB : p ∣ -3 * t * z 0 + (3 * t - 1) * z 1 := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
        (-3 * t * z 0 + (3 * t - 1) * z 1) (p * D).natAbs).mp hsecond'
      have hnat : ((p * D).natAbs : ℤ) = p * D := by
        simp only [Int.natCast_natAbs, abs_of_pos (mul_pos hp hD)]
      have hpd : (p * D) ∣ -3 * t * z 0 + (3 * t - 1) * z 1 := by simpa [hnat] using h
      exact dvd_trans (dvd_mul_right p D) hpd
    have hp0 : p ∣ z 0 := by
      have hcomb : (3 * t - 1) * (-z 0 + z 1) - (-3 * t * z 0 + (3 * t - 1) * z 1) = z 0 := by ring
      have h := dvd_sub (dvd_mul_of_dvd_right hpA (3 * t - 1)) hpB
      rw [hcomb] at h
      exact h
    have hp1 : p ∣ z 1 := by
      have hcomb : 3 * t * (-z 0 + z 1) - (-3 * t * z 0 + (3 * t - 1) * z 1) = z 1 := by ring
      have h := dvd_sub (dvd_mul_of_dvd_right hpA (3 * t)) hpB
      rw [hcomb] at h
      exact h
    obtain ⟨X, hX⟩ := hp0
    obtain ⟨Y, hY⟩ := hp1
    have hpd : (p * D) ∣ -3 * t * z 0 + (3 * t - 1) * z 1 := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
        (-3 * t * z 0 + (3 * t - 1) * z 1) (p * D).natAbs).mp hsecond'
      have hnat : ((p * D).natAbs : ℤ) = p * D := by
        simp only [Int.natCast_natAbs, abs_of_pos (mul_pos hp hD)]
      simpa [hnat] using h
    use X, Y
    constructor
    · ext i
      fin_cases i
      · exact hX
      · exact hY
    · obtain ⟨k, hk⟩ := hpd
      use k
      rw [hX, hY] at hk
      have hpne : p ≠ 0 := ne_of_gt hp
      apply (mul_left_cancel₀ hpne)
      calc
        p * ((-3 * t) * X + (3 * t - 1) * Y) =
            -3 * t * (p * X) + (3 * t - 1) * (p * Y) := by ring
        _ = p * (D * k) := by nlinarith only [hk]
  · rintro ⟨X, Y, rfl, hdiv⟩
    apply e.injective
    rw [he, map_zero]
    apply Prod.ext
    all_goals simp only [Prod.fst_zero, Prod.snd_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    · have hfirst : -p * X + p * Y = p * (-X + Y) := by ring
      rw [show - (p * X) + p * Y = p * (-X + Y) by ring, Int.cast_mul]
      have hnat : (p.natAbs : ℤ) = p := by
        simp only [Int.natCast_natAbs, abs_of_pos hp]
      have hpcast : (p : ZMod p.natAbs) = 0 := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd p p.natAbs).mpr
        simp [hnat]
      rw [hpcast, zero_mul]
    · have hsecond : -3 * t * (p * X) + (3 * t - 1) * (p * Y) =
          p * ((-3 * t) * X + (3 * t - 1) * Y) := by ring
      obtain ⟨k, hk⟩ := hdiv
      rw [hsecond, hk]
      have hfac : p * (D * k) = (p * D) * k := by ring
      rw [hfac, Int.cast_mul]
      have hnat : ((p * D).natAbs : ℤ) = p * D := by
        simp only [Int.natCast_natAbs, abs_of_pos (mul_pos hp hD)]
      have hpdcast : ((p * D : ℤ) : ZMod (p * D).natAbs) = 0 := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd (p * D) (p * D).natAbs).mpr
        simp [hnat]
      rw [hpdcast, zero_mul]

private lemma kernel_characterization_33
    {G : Type*} [AddCommGroup G]
    (p D t : ℤ) (hp : 0 < p) (hD : 0 < D)
    (F : Plane →+ G) (e : G ≃+ (ZMod p.natAbs × ZMod (p * D).natAbs))
    (he : ∀ z : Plane, e (F z) =
      (((t * z 0 + (1 - t) * z 1 : ℤ) : ZMod p.natAbs),
        ((-(3 * t + 1) * z 0 + (3 * t - 2) * z 1 : ℤ) : ZMod (p * D).natAbs))) :
    ∀ z : Plane, F z = 0 ↔
      ∃ X Y : ℤ, z = ![p * X, p * Y] ∧ D ∣ (-(3 * t + 1)) * X + (3 * t - 2) * Y := by
  intro z
  constructor
  · intro hz
    have hcoord := congrArg Prod.snd (he z)
    have hfirst := congrArg Prod.fst (he z)
    rw [hz, map_zero] at hcoord hfirst
    have hfirst' : ((t * z 0 + (1 - t) * z 1 : ℤ) : ZMod p.natAbs) = 0 := by
      simpa using hfirst.symm
    have hsecond' : ((-(3 * t + 1) * z 0 + (3 * t - 2) * z 1 : ℤ) : ZMod (p * D).natAbs) = 0 := by
      simpa using hcoord.symm
    have hpA : p ∣ t * z 0 + (1 - t) * z 1 := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
        (t * z 0 + (1 - t) * z 1) p.natAbs).mp hfirst'
      have hnat : (p.natAbs : ℤ) = p := by
        simp only [Int.natCast_natAbs, abs_of_pos hp]
      simpa [hnat] using h
    have hpB : p ∣ -(3 * t + 1) * z 0 + (3 * t - 2) * z 1 := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
        (-(3 * t + 1) * z 0 + (3 * t - 2) * z 1) (p * D).natAbs).mp hsecond'
      have hnat : ((p * D).natAbs : ℤ) = p * D := by
        simp only [Int.natCast_natAbs, abs_of_pos (mul_pos hp hD)]
      have hpd : (p * D) ∣ -(3 * t + 1) * z 0 + (3 * t - 2) * z 1 := by
        simpa [hnat] using h
      exact dvd_trans (dvd_mul_right p D) hpd
    have hp0 : p ∣ z 0 := by
      have hcomb : (3 * t - 2) * (t * z 0 + (1 - t) * z 1) - (1 - t) * (-(3 * t + 1) * z 0 + (3 * t - 2) * z 1) = z 0 := by ring
      have h := dvd_sub (dvd_mul_of_dvd_right hpA (3 * t - 2))
        (dvd_mul_of_dvd_right hpB (1 - t))
      rw [hcomb] at h
      exact h
    have hp1 : p ∣ z 1 := by
      have hcomb : (3 * t + 1) * (t * z 0 + (1 - t) * z 1) + t * (-(3 * t + 1) * z 0 + (3 * t - 2) * z 1) = z 1 := by ring
      have h := dvd_add (dvd_mul_of_dvd_right hpA (3 * t + 1))
        (dvd_mul_of_dvd_right hpB t)
      rw [hcomb] at h
      exact h
    obtain ⟨X, hX⟩ := hp0
    obtain ⟨Y, hY⟩ := hp1
    have hpd : (p * D) ∣ -(3 * t + 1) * z 0 + (3 * t - 2) * z 1 := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
        (-(3 * t + 1) * z 0 + (3 * t - 2) * z 1) (p * D).natAbs).mp hsecond'
      have hnat : ((p * D).natAbs : ℤ) = p * D := by
        simp only [Int.natCast_natAbs, abs_of_pos (mul_pos hp hD)]
      simpa [hnat] using h
    use X, Y
    constructor
    · ext i
      fin_cases i
      · exact hX
      · exact hY
    · obtain ⟨k, hk⟩ := hpd
      use k
      rw [hX, hY] at hk
      have hpne : p ≠ 0 := ne_of_gt hp
      apply (mul_left_cancel₀ hpne)
      calc
        p * ((-(3 * t + 1)) * X + (3 * t - 2) * Y) =
            -(3 * t + 1) * (p * X) + (3 * t - 2) * (p * Y) := by ring
        _ = p * (D * k) := by nlinarith only [hk]
  · rintro ⟨X, Y, rfl, hdiv⟩
    apply e.injective
    rw [he, map_zero]
    apply Prod.ext
    all_goals simp only [Prod.fst_zero, Prod.snd_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    · have hfirst : t * (p * X) + (1 - t) * (p * Y) =
          p * (t * X + (1 - t) * Y) := by ring
      rw [hfirst, Int.cast_mul]
      have hnat : (p.natAbs : ℤ) = p := by
        simp only [Int.natCast_natAbs, abs_of_pos hp]
      have hpcast : (p : ZMod p.natAbs) = 0 := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd p p.natAbs).mpr
        simp [hnat]
      rw [hpcast, zero_mul]
    · have hsecond : -(3 * t + 1) * (p * X) + (3 * t - 2) * (p * Y) =
          p * ((-(3 * t + 1)) * X + (3 * t - 2) * Y) := by ring
      obtain ⟨k, hk⟩ := hdiv
      rw [hsecond, hk]
      have hfac : p * (D * k) = (p * D) * k := by ring
      rw [hfac, Int.cast_mul]
      have hnat : ((p * D).natAbs : ℤ) = p * D := by
        simp only [Int.natCast_natAbs, abs_of_pos (mul_pos hp hD)]
      have hpdcast : ((p * D : ℤ) : ZMod (p * D).natAbs) = 0 := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd (p * D) (p * D).natAbs).mpr
        simp [hnat]
      rw [hpdcast, zero_mul]

private lemma dvd_abs_le_cases {D L : ℤ} (hD : 0 < D)
    (hdiv : D ∣ L) (hbound : |L| ≤ D) :
    L = 0 ∨ L = D ∨ L = -D := by
  obtain ⟨k, hk⟩ := hdiv
  by_cases hk0 : k = 0
  · left
    simpa [hk0] using hk
  · by_cases hkpos : 0 < k
    · have hkone : k = 1 := by
        have hle : D * k ≤ D := by
          rw [hk] at hbound
          simpa [abs_mul, abs_of_pos hD, abs_of_pos hkpos] using hbound
        nlinarith
      right
      left
      rw [hk, hkone]
      ring
    · have hkneg : k < 0 := by omega
      have hkminusone : k = -1 := by
        have hle : D * (-k) ≤ D := by
          rw [hk] at hbound
          simpa [abs_mul, abs_of_pos hD, abs_of_neg hkneg] using hbound
        nlinarith
      right
      right
      rw [hk, hkminusone]
      ring

private lemma kernel_at_n_19
    (p t m D : ℤ) (hp3 : 3 ≤ p) (ht : 2 ≤ t)
    (hm : m = 6 * t - 1) (hDfactor : D = (3 * t + 1) * (m - 3))
    (F : Plane →+ (Plane ⧸ Submodule.span ℤ (Set.range
      ![![p * (m - 1)/2, p * (m + 1)/2],
        ![p * (m - 9)/2, -(p * (m + 9)/2)]])))
    (e : (Plane ⧸ Submodule.span ℤ (Set.range
      ![![p * (m - 1)/2, p * (m + 1)/2],
        ![p * (m - 9)/2, -(p * (m + 9)/2)]])) ≃+
      (ZMod p.natAbs × ZMod (p * D).natAbs))
    (he : ∀ z : Plane, e (F z) =
      (((-z 0 + z 1 : ℤ) : ZMod p.natAbs),
        ((-3 * t * z 0 + (3 * t - 1) * z 1 : ℤ) : ZMod (p * D).natAbs)))
    {z : Plane} (hz : F z = 0)
    (hnorm : |z 0| + |z 1| ≤ p * (m - 3)) : z = 0 := by
  have hp : 0 < p := by omega
  have hm3 : 0 < m - 3 := by
    have : 11 ≤ m := by omega
    omega
  obtain ⟨X, Y, hxy, hdiv⟩ :=
    (kernel_characterization p D t hp (by nlinarith [hDfactor, hm3]) F e he z).mp hz
  have hnormXY : |X|+|Y| ≤ m - 3 := by
    rw [hxy, scaled_lee_norm p X Y hp] at hnorm
    nlinarith [abs_nonneg X, abs_nonneg Y]
  have hLbound : |(-3 * t) * X + (3 * t - 1) * Y| ≤ 3 * t * (m - 3) := by
    have htriangle := abs_add_le ((-3 * t) * X) ((3 * t - 1) * Y)
    have hcoeff : |(-3 * t) * X| + |(3 * t - 1) * Y| ≤
        3 * t * (|X|+|Y|) := by
      simp only [abs_mul, abs_neg, abs_of_nonneg (by omega : 0 ≤ t), abs_of_nonneg (by norm_num : (0:ℤ) ≤ 3),
        abs_of_nonneg (by omega : 0 ≤ 3 * t - 1)]
      nlinarith [abs_nonneg X, abs_nonneg Y]
    exact htriangle.trans (hcoeff.trans (by
      have ht0 : 0 ≤ 3 * t := by omega
      exact mul_le_mul_of_nonneg_left hnormXY ht0))
  have hstrict : |(-3 * t) * X + (3 * t - 1) * Y| < D := by
    rw [hDfactor]
    have ht0 : 0 < 3 * t := by omega
    nlinarith [hLbound, hm3]
  have hLzero : (-3 * t) * X + (3 * t - 1) * Y = 0 :=
    Int.eq_zero_of_abs_lt_dvd hdiv hstrict
  have hX : X = (3 * t - 1) * (Y - X) := by nlinarith only [hLzero]
  have hY : Y = 3 * t * (Y - X) := by nlinarith only [hLzero]
  let k : ℤ := Y - X
  have hnormk : |X|+|Y| = m*|k| := by
    calc
      _ = |(3 * t - 1) * k| + |3 * t * k| := congrArg₂ (fun a b : ℤ => |a|+|b|) hX hY
      _ = m*|k| := by
        rw [hm]
        simp only [abs_mul, abs_of_nonneg (by omega : 0 ≤ 3 * t - 1),
          abs_of_nonneg (by omega : 0 ≤ 3 * t)]
        ring
  have hkzero : k = 0 := by
    by_contra hk
    have hkabs : 1 ≤ |k| := Int.one_le_abs hk
    rw [hnormk] at hnormXY
    have hmpos : 0 < m := by omega
    nlinarith
  have hXYzero : X = 0 ∧ Y = 0 := by
    dsimp [k] at hkzero
    constructor <;> nlinarith [hX, hY]
  rw [hxy]
  rcases hXYzero with ⟨rfl, rfl⟩
  simp

private lemma kernel_at_n_33
    (p t m D : ℤ) (hp3 : 3 ≤ p) (ht : 2 ≤ t)
    (hm : m = 6 * t - 1) (hDfactor : D = (3 * t + 1) * (m - 3))
    (F : Plane →+ (Plane ⧸ Submodule.span ℤ (Set.range
      ![![p * (m - 3)/2, p * (m + 3)/2],
        ![p * (m - 3)/2, -(p * (m + 3)/2)]])))
    (e : (Plane ⧸ Submodule.span ℤ (Set.range
      ![![p * (m - 3)/2, p * (m + 3)/2],
        ![p * (m - 3)/2, -(p * (m + 3)/2)]])) ≃+
      (ZMod p.natAbs × ZMod (p * D).natAbs))
    (he : ∀ z : Plane, e (F z) =
      (((t * z 0 + (1 - t) * z 1 : ℤ) : ZMod p.natAbs),
        ((-(3 * t + 1) * z 0 + (3 * t - 2) * z 1 : ℤ) : ZMod (p * D).natAbs)))
    {z : Plane} (hz : F z = 0)
    (hnorm : |z 0| + |z 1| ≤ p * (m - 3)) :
    z = 0 ∨ z = ![p * (m - 3), 0] ∨ z = ![-(p * (m - 3)), 0] := by
  have hp : 0 < p := by omega
  have hm3 : 0 < m - 3 := by
    have : 11 ≤ m := by omega
    omega
  obtain ⟨X, Y, hxy, hdiv⟩ :=
    (kernel_characterization_33 p D t hp (by nlinarith [hDfactor, hm3]) F e he z).mp hz
  have hnormXY : |X|+|Y| ≤ m - 3 := by
    rw [hxy, scaled_lee_norm p X Y hp] at hnorm
    nlinarith [abs_nonneg X, abs_nonneg Y]
  have hLbound : |(-(3 * t + 1)) * X + (3 * t - 2) * Y| ≤
      D - 3*|Y| := by
    have htriangle := abs_add_le (-(3 * t + 1) * X) ((3 * t - 2) * Y)
    have hcoeff : |(-(3 * t + 1)) * X| + |(3 * t - 2) * Y| =
        (3 * t + 1)*|X| + (3 * t - 2)*|Y| := by
      simp only [abs_mul, abs_neg, abs_of_nonneg (by omega : 0 ≤ 3 * t + 1),
        abs_of_nonneg (by omega : 0 ≤ 3 * t - 2)]
    rw [hcoeff] at htriangle
    rw [hDfactor]
    nlinarith [htriangle, hnormXY, abs_nonneg Y]
  have hDpos : 0 < D := by nlinarith [hDfactor, hm3]
  have hLle : |(-(3 * t + 1)) * X + (3 * t - 2) * Y| ≤ D := by
    exact hLbound.trans (by nlinarith [abs_nonneg Y])
  obtain hzero | hplus | hminus := dvd_abs_le_cases hDpos hdiv hLle
  · have hX : X = (3 * t - 2) * (t * X + (1 - t) * Y) := by linear_combination (t - 1) * hzero
    have hY : Y = (3 * t + 1) * (t * X + (1 - t) * Y) := by linear_combination t * hzero
    let k : ℤ := t * X + (1 - t) * Y
    have hnormk : |X|+|Y| = m*|k| := by
      calc
        _ = |(3 * t - 2) * k| + |(3 * t + 1) * k| := congrArg₂ (fun a b : ℤ => |a|+|b|) hX hY
        _ = m*|k| := by
          rw [hm]
          simp only [abs_mul, abs_of_nonneg (by omega : 0 ≤ 3 * t - 2),
            abs_of_nonneg (by omega : 0 ≤ 3 * t + 1)]
          ring
    have hkzero : k = 0 := by
      by_contra hk
      have hkabs : 1 ≤ |k| := Int.one_le_abs hk
      rw [hnormk] at hnormXY
      have hmpos : 0 < m := by omega
      nlinarith
    have hXYzero : X = 0 ∧ Y = 0 := by
      dsimp [k] at hkzero
      constructor <;> nlinarith [hX, hY]
    left
    rw [hxy]
    rcases hXYzero with ⟨rfl, rfl⟩
    simp
  · right
    right
    have hYzero : Y = 0 := by
      have h := hLbound
      rw [hplus, abs_of_pos hDpos] at h
      have : |Y| = 0 := by nlinarith [abs_nonneg Y]
      exact abs_eq_zero.mp this
    have hX : X = -(m - 3) := by
      rw [hYzero] at hplus
      rw [hDfactor] at hplus
      nlinarith
    rw [hxy, hYzero, hX]
    ext i
    fin_cases i <;> simp <;> ring
  · right
    left
    have hYzero : Y = 0 := by
      have h := hLbound
      rw [hminus, abs_neg, abs_of_pos hDpos] at h
      have : |Y| = 0 := by nlinarith [abs_nonneg Y]
      exact abs_eq_zero.mp this
    have hX : X = m - 3 := by
      rw [hYzero] at hminus
      rw [hDfactor] at hminus
      nlinarith
    rw [hxy, hYzero, hX]
    ext i
    fin_cases i <;> simp <;> ring

private theorem word_fibers_from_kernels
    {G19 G33 : Type*} [AddCommGroup G19] [AddCommGroup G33]
    (F19 : Plane →+ G19) (F33 : Plane →+ G33) (n : ℕ) (hnpositive : 0 < n)
    (hkernel19n : ∀ z : Plane, F19 z = 0 → |z 0| + |z 1| ≤ (n : ℤ) → z = 0)
    (hkernel33n : ∀ z : Plane, F33 z = 0 → |z 0| + |z 1| ≤ (n : ℤ) →
      z = 0 ∨ z = ![(n : ℤ), 0] ∨ z = ![-(n : ℤ), 0])
    (hplus : F33 ![(n : ℤ), 0] = 0) (hminus : F33 ![-(n : ℤ), 0] = 0) :
    (∀ l : ℕ, l < n → W F19 l = W F33 l) ∧ W F33 n = W F19 n + 2 := by
  classical
  have hshort19 (l : ℕ) (hl : l < n) (w : Fin l → Fin 4)
      (hw : F19 (endpoint w) = 0) : endpoint w = 0 := by
    apply hkernel19n _ hw
    exact (endpoint_lee_bound w).trans (by exact_mod_cast Nat.le_of_lt hl)
  have hshort33 (l : ℕ) (hl : l < n) (w : Fin l → Fin 4)
      (hw : F33 (endpoint w) = 0) : endpoint w = 0 := by
    have hb := endpoint_lee_bound w
    have hln : (l : ℤ) < (n : ℤ) := by exact_mod_cast hl
    have hnp : (0 : ℤ) < n := by exact_mod_cast hnpositive
    rcases hkernel33n (endpoint w) hw (by omega) with hz | hz | hz
    · exact hz
    · have hlen : (n : ℤ) ≤ l := by
        simpa only [hz, Matrix.cons_val_zero, Matrix.cons_val_one, abs_of_pos hnp,
          abs_zero, add_zero] using hb
      omega
    · have hlen : (n : ℤ) ≤ l := by
        simpa only [hz, Matrix.cons_val_zero, Matrix.cons_val_one, abs_neg,
          abs_of_pos hnp, abs_zero, add_zero] using hb
      omega
  have hshort_equiv (l : ℕ) (hl : l < n) :
      ReturnWords F19 l ≃ ReturnWords F33 l := by
    let toFun : ReturnWords F19 l → ReturnWords F33 l := fun w =>
      ⟨w.1, by
        have hz : endpoint w.1 = 0 := hshort19 l hl w.1 w.2
        have hz' : F33 (endpoint w.1) = 0 := by simp [hz]
        exact hz'⟩
    let invFun : ReturnWords F33 l → ReturnWords F19 l := fun w =>
      ⟨w.1, by
        have hz : endpoint w.1 = 0 := hshort33 l hl w.1 w.2
        have hz' : F19 (endpoint w.1) = 0 := by simp [hz]
        exact hz'⟩
    exact
      { toFun := toFun
        invFun := invFun
        left_inv := by intro w; rfl
        right_inv := by intro w; rfl }
  have hshort_count (l : ℕ) (hl : l < n) : W F19 l = W F33 l := by
    exact Nat.card_congr (hshort_equiv l hl)
  have hnorm_n (w : Fin n → Fin 4) :
      |endpoint w 0| + |endpoint w 1| ≤ (n : ℤ) := endpoint_lee_bound w
  let wplus : Fin n → Fin 4 := fun _ => (0 : Fin 4)
  let wminus : Fin n → Fin 4 := fun _ => (1 : Fin 4)
  have hplus_endpoint : endpoint wplus = ![(n : ℤ), 0] := by
    simpa [wplus] using endpoint_const_pos n
  have hminus_endpoint : endpoint wminus = ![-(n : ℤ), 0] := by
    simpa [wminus] using endpoint_const_neg n
  have hplus33 : F33 (endpoint wplus) = 0 := by rwa [hplus_endpoint]
  have hminus33 : F33 (endpoint wminus) = 0 := by rwa [hminus_endpoint]
  let bplus : ReturnWords F33 n := ⟨wplus, hplus33⟩
  let bminus : ReturnWords F33 n := ⟨wminus, hminus33⟩
  have hsum_equiv : ReturnWords F33 n ≃
      (ReturnWords F19 n ⊕ Fin 2) := by
    have hzp : endpoint wplus ≠ 0 := by
      intro h
      have h0 := congrFun (hplus_endpoint.symm.trans h) 0
      simp only [Matrix.cons_val_zero, Pi.zero_apply] at h0
      omega
    have hzm : endpoint wminus ≠ 0 := by
      intro h
      have h0 := congrFun (hminus_endpoint.symm.trans h) 0
      simp only [Matrix.cons_val_zero, Pi.zero_apply] at h0
      omega
    have hmp : endpoint wminus ≠ ![(n : ℤ), 0] := by
      intro h
      have h0 := congrFun (hminus_endpoint.symm.trans h) 0
      simp only [Matrix.cons_val_zero] at h0
      omega
    let toFun : ReturnWords F33 n → ReturnWords F19 n ⊕ Fin 2 := fun w =>
      if hzero : endpoint w.1 = 0 then Sum.inl ⟨w.1, by simp [hzero]⟩
      else if endpoint w.1 = ![(n : ℤ), 0] then Sum.inr 0 else Sum.inr 1
    have hbp : toFun bplus = Sum.inr 0 := by
      dsimp only [toFun, bplus]
      rw [dite_eq_right hzp, ite_eq_left hplus_endpoint]
    have hbm : toFun bminus = Sum.inr 1 := by
      dsimp only [toFun, bminus]
      rw [dite_eq_right hzm, ite_eq_right hmp]
    let invFun : ReturnWords F19 n ⊕ Fin 2 → ReturnWords F33 n := fun s =>
      match s with
      | Sum.inl w => ⟨w.1, by
          have hz : endpoint w.1 = 0 := hkernel19n (endpoint w.1) w.2 (hnorm_n w.1)
          simpa [hz]⟩
      | Sum.inr j => if j = 0 then bplus else bminus
    exact
      { toFun := toFun
        invFun := invFun
        left_inv := by
          intro w
          by_cases hzero : endpoint w.1 = 0
          · dsimp only [toFun]
            rw [dite_eq_left hzero]
            rfl
          · rcases hkernel33n (endpoint w.1) w.2 (hnorm_n w.1) with h0 | hpv | hmv
            · exact (hzero h0).elim
            · have hw : w.1 = wplus := positive_extremal_word w.1 hpv
              have heq : w = bplus := Subtype.ext hw
              rw [heq, hbp]
              rfl
            · have hw : w.1 = wminus := negative_extremal_word w.1 hmv
              have heq : w = bminus := Subtype.ext hw
              rw [heq, hbm]
              rfl
        right_inv := by
          intro s
          rcases s with w | j
          · have hz : endpoint w.1 = 0 := hkernel19n (endpoint w.1) w.2 (hnorm_n w.1)
            dsimp only [invFun, toFun]
            rw [dite_eq_left hz]
            rfl
          · fin_cases j
            · simpa [invFun] using hbp
            · simpa [invFun] using hbm
          }
  have hcard_n : W F33 n = W F19 n + 2 := by
    have : Finite (ReturnWords F19 n) := by unfold ReturnWords; infer_instance
    have hc := Nat.card_congr hsum_equiv
    simpa [W, Nat.card_sum] using hc
  exact ⟨hshort_count, hcard_n⟩

/--
For the two actual lattice quotients with `m = 6 * t - 1`, the first length at
which their signed word - return fibers differ is `n = p * (m - 3)`.  Every
shorter fiber is identical, while the `(3,3)` quotient has precisely the two
additional constant horizontal words at length `n`.
-/
theorem first_return_defect (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t) :
    let m : ℤ := 6 * t - 1
    let D : ℤ := (m ^ 2 - 9)/2
    let H := ZMod p.natAbs × ZMod (p * D).natAbs
    let v119 : Plane := ![p * (m - 1)/2, p * (m + 1)/2]
    let v219 : Plane := ![p * (m - 9)/2, -(p * (m + 9)/2)]
    let v133 : Plane := ![p * (m - 3)/2, p * (m + 3)/2]
    let v233 : Plane := ![p * (m - 3)/2, -(p * (m + 3)/2)]
    let K19 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v133, v233])
    let G19 := Plane ⧸ K19
    let G33 := Plane ⧸ K33
    let F19 : Plane →+ G19 := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ G33 := K33.mkQ.toAddMonoidHom
    let n : ℕ := (p * (m - 3)).toNat
    ∃ (e19 : G19 ≃+ H) (e33 : G33 ≃+ H),
      (∀ z : Plane, e19 (F19 z) =
        (((-z 0 + z 1 : ℤ) : ZMod p.natAbs),
          ((-(3 * t) * z 0 + (3 * t - 1) * z 1 : ℤ) : ZMod (p * D).natAbs))) ∧
      (∀ z : Plane, e33 (F33 z) =
        (((t * z 0 + (1 - t) * z 1 : ℤ) : ZMod p.natAbs),
          ((-(3 * t + 1) * z 0 + (3 * t - 2) * z 1 : ℤ) : ZMod (p * D).natAbs))) ∧
      (∀ l : ℕ, l < n → W F19 l = W F33 l) ∧
      W F33 n = W F19 n + 2 := by
  classical
  let m : ℤ := 6 * t - 1
  let D : ℤ := (m ^ 2 - 9)/2
  let H := ZMod p.natAbs × ZMod (p * D).natAbs
  let v119 : Plane := ![p * (m - 1)/2, p * (m + 1)/2]
  let v219 : Plane := ![p * (m - 9)/2, -(p * (m + 9)/2)]
  let v133 : Plane := ![p * (m - 3)/2, p * (m + 3)/2]
  let v233 : Plane := ![p * (m - 3)/2, -(p * (m + 3)/2)]
  let K19 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v119, v219])
  let K33 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v133, v233])
  let G19 := Plane ⧸ K19
  let G33 := Plane ⧸ K33
  let F19 : Plane →+ G19 := K19.mkQ.toAddMonoidHom
  let F33 : Plane →+ G33 := K33.mkQ.toAddMonoidHom
  let n : ℕ := (p * (m - 3)).toNat
  change ∃ (e19 : G19 ≃+ H) (e33 : G33 ≃+ H),
      (∀ z : Plane, e19 (F19 z) =
        (((-z 0 + z 1 : ℤ) : ZMod p.natAbs),
          ((-(3 * t) * z 0 + (3 * t - 1) * z 1 : ℤ) : ZMod (p * D).natAbs))) ∧
      (∀ z : Plane, e33 (F33 z) =
        (((t * z 0 + (1 - t) * z 1 : ℤ) : ZMod p.natAbs),
          ((-(3 * t + 1) * z 0 + (3 * t - 2) * z 1 : ℤ) : ZMod (p * D).natAbs))) ∧
      (∀ l : ℕ, l < n → W F19 l = W F33 l) ∧
      W F33 n = W F19 n + 2
  have hp : 0 < p := by omega
  have hm11 : 11 ≤ m := by dsimp [m]; omega
  have hm3 : 0 < m - 3 := by omega
  have hDfactor : D = (3 * t + 1) * (m - 3) := by
    have half_exact (c d : ℤ) (h : c = 2 * d) : c/2 = d := by omega
    apply half_exact
    dsimp [D, m]
    ring
  have hDpos : 0 < D := by nlinarith [hDfactor, hm3]
  obtain ⟨e19, e33, he19, he33, hrest⟩ := same_group_different_growth p t hp3 hpo ht
  clear hrest
  have hnpos : 0 < p * (m - 3) := mul_pos hp hm3
  have hncast : (n : ℤ) = p * (m - 3) := by
    dsimp [n]
    exact Int.toNat_of_nonneg (le_of_lt hnpos)
  have hnpositive : 0 < n := by
    have : (0 : ℤ) < (n : ℤ) := by omega
    exact_mod_cast this
  have hkernel33n (z : Plane) (hz : F33 z = 0)
      (hnorm : |z 0|+|z 1| ≤ (n : ℤ)) :
      z = 0 ∨ z = ![(n : ℤ), 0] ∨ z = ![-(n : ℤ), 0] := by
    have h := kernel_at_n_33 p t m D hp3 ht rfl hDfactor F33 e33 he33 hz
      (by simpa [hncast] using hnorm)
    simpa [hncast] using h
  have hkernel19n (z : Plane) (hz : F19 z = 0)
      (hnorm : |z 0|+|z 1| ≤ (n : ℤ)) : z = 0 := by
    apply kernel_at_n_19 p t m D hp3 ht rfl hDfactor F19 e19 (by simpa only [neg_mul] using he19) hz
    simpa [hncast] using hnorm
  let wplus : Fin n → Fin 4 := fun _ => (0 : Fin 4)
  let wminus : Fin n → Fin 4 := fun _ => (1 : Fin 4)
  have hplus_endpoint : endpoint wplus = ![(n : ℤ), 0] := by
    simpa [wplus] using endpoint_const_pos n
  have hminus_endpoint : endpoint wminus = ![-(n : ℤ), 0] := by
    simpa [wminus] using endpoint_const_neg n
  have hplus33 : F33 (endpoint wplus) = 0 := by
    rw [hplus_endpoint]
    apply (kernel_characterization_33 p D t hp hDpos F33 e33 he33
      (![ (n : ℤ), 0] : Plane)).mpr
    use m - 3, 0
    constructor
    · rw [hncast]
      ext i
      fin_cases i <;> simp <;> ring
    · rw [hDfactor]
      use - 1
      ring
  have hminus33 : F33 (endpoint wminus) = 0 := by
    rw [hminus_endpoint]
    apply (kernel_characterization_33 p D t hp hDpos F33 e33 he33
      (![ -(n : ℤ), 0] : Plane)).mpr
    use - (m - 3), 0
    constructor
    · rw [hncast]
      ext i
      fin_cases i <;> simp <;> ring
    · rw [hDfactor]
      use 1
      ring
  obtain ⟨hshort_count, hcard_n⟩ := word_fibers_from_kernels F19 F33 n hnpositive
    hkernel19n hkernel33n (by rwa [← hplus_endpoint]) (by rwa [← hminus_endpoint])
  exact ⟨e19, e33, he19, he33, hshort_count, hcard_n⟩

end D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
