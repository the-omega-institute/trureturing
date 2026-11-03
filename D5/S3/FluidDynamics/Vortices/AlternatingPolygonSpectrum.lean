/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Barry–Kevrekidis alternating vortex polygon spectrum and distinct real pairs. -/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import D5.S3.Quantum.Matrix.CirculantCharpoly

/-! Alternating vortex polygon equilibrium, Jacobian and real spectrum. -/

noncomputable section
open scoped BigOperators
open Matrix Polynomial

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum

set_option autoImplicit false

/-- Alternating charge, with `j` the zero-based label corresponding to the source's `j+1`. -/
def charge (N : ℕ) (j : Fin N) : ℝ := (-1 : ℝ) ^ (j.val + 2)

/-- The Cartesian point-vortex field with `b = 2` and `Ω = 1/2`. -/
def field (N : ℕ) (z : Fin N ⊕ Fin N → ℝ) : Fin N ⊕ Fin N → ℝ := fun p =>
  match p with
  | Sum.inl j =>
      -charge N j * (1 / 2 : ℝ) * z (Sum.inr j) -
        ∑ k : Fin N, if k = j then 0 else
          charge N k * (z (Sum.inr j) - z (Sum.inr k)) /
            ((z (Sum.inl j) - z (Sum.inl k)) ^ 2 +
              (z (Sum.inr j) - z (Sum.inr k)) ^ 2)
  | Sum.inr j =>
      charge N j * (1 / 2 : ℝ) * z (Sum.inl j) +
        ∑ k : Fin N, if k = j then 0 else
          charge N k * (z (Sum.inl j) - z (Sum.inl k)) /
            ((z (Sum.inl j) - z (Sum.inl k)) ^ 2 +
              (z (Sum.inr j) - z (Sum.inr k)) ^ 2)

/-- The regular unit `N`-gon in the source's cyclic order. -/
def polygon (N : ℕ) : Fin N ⊕ Fin N → ℝ := fun p =>
  match p with
  | Sum.inl j => Real.cos (2 * Real.pi * (j.val + 1 : ℝ) / N)
  | Sum.inr j => Real.sin (2 * Real.pi * (j.val + 1 : ℝ) / N)

/-- Cartesian Jacobian, defined by the partial derivative in each coordinate direction. -/
def jacobian (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  fun p q => deriv (fun t : ℝ => field N (polygon N + t • Pi.single q 1) p) 0

private lemma distinctness_certificate (m k l : ℕ)
    (hk : 2 ≤ k) (hkl : k < l) (hlm : l < m) :
    ((m : ℝ) - k) ^ 2 * ((k : ℝ) ^ 2 - 2) ≠
      ((m : ℝ) - l) ^ 2 * ((l : ℝ) ^ 2 - 2) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hklR : (k : ℝ) < l := by exact_mod_cast hkl
  have hlmR : (l : ℝ) < m := by exact_mod_cast hlm
  let s : ℝ := k + l
  let Q : ℝ → ℝ := fun t =>
    s * t ^ 2 - 2 * ((k : ℝ)^2 + k*l + (l : ℝ)^2 - 2) * t +
      s * ((k : ℝ)^2 + (l : ℝ)^2 - 2)
  have hs : 0 < s := by dsimp [s]; linarith
  have hfactor :
      ((m : ℝ) - k)^2 * ((k : ℝ)^2 - 2) -
        ((m : ℝ) - l)^2 * ((l : ℝ)^2 - 2) = (k - (l : ℝ)) * Q m := by
    dsimp [Q, s]
    ring
  have hQ : Q m ≠ 0 := by
    by_cases hm : m < k + l
    · have hmR : (m : ℝ) ≤ s - 1 := by
        have hc : (m : ℝ) + 1 ≤ (k : ℝ) + l := by exact_mod_cast (show m + 1 ≤ k + l by omega)
        dsimp [s]
        linarith
      have hQl : Q l < 0 := by
        have hid : Q l = -((l : ℝ) - k) * ((k : ℝ)^2 - 2) := by dsimp [Q, s]; ring
        rw [hid]
        have : 0 < (k : ℝ)^2 - 2 := by nlinarith
        exact mul_neg_of_neg_of_pos (by linarith) this
      have hQb : Q (s - 1) < 0 := by
        let u : ℝ := k - 2
        let v : ℝ := l - k - 1
        have hu : 0 ≤ u := by dsimp [u]; linarith
        have hv : 0 ≤ v := by
          have hc : (k : ℝ) + 1 ≤ l := by exact_mod_cast (show k + 1 ≤ l by omega)
          dsimp [v]
          linarith
        have hid : Q (s - 1) = -(2*u^2 + 2*u*v + 4*u + v + 1) := by
          dsimp [Q, s, u, v]
          ring
        rw [hid]
        nlinarith [sq_nonneg u, mul_nonneg hu hv]
      have ht : 0 < (m : ℝ) - l := by linarith
      have hr : 0 ≤ s - 1 - m := by linarith
      have hwidth : 0 < (k : ℝ) - 1 := by linarith
      have hinterp : ((k : ℝ) - 1) * Q m =
          (s - 1 - m) * Q l + ((m : ℝ) - l) * Q (s - 1) -
            s * ((k : ℝ) - 1) * ((m : ℝ) - l) * (s - 1 - m) := by
        dsimp [Q, s]
        ring
      have hneg := mul_neg_of_pos_of_neg ht hQb
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos hr (le_of_lt hQl)
      have hnonneg : 0 ≤ s * ((k : ℝ) - 1) * ((m : ℝ) - l) * (s - 1 - m) :=
        mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hs) (le_of_lt hwidth)) (le_of_lt ht)) hr
      have : ((k : ℝ) - 1) * Q m < 0 := by linarith
      intro he
      rw [he, mul_zero] at this
      linarith
    · have hmR : s ≤ m := by dsimp [s]; exact_mod_cast (show k + l ≤ m by omega)
      let h : ℝ := m - s
      have hh : 0 ≤ h := by dsimp [h]; linarith
      have hid : Q m = 2*s + (2*(k : ℝ)*l + 4)*h + s*h^2 := by
        dsimp [Q, h, s]
        ring
      have hcoef : 0 ≤ 2*(k : ℝ)*l + 4 := by positivity
      have hpos : 0 < Q m := by
        rw [hid]
        have := mul_nonneg hcoef hh
        have := mul_nonneg (le_of_lt hs) (sq_nonneg h)
        linarith
      exact ne_of_gt hpos
  intro he
  have hz : (k - (l : ℝ)) * Q m = 0 := by rw [← hfactor, he, sub_self]
  exact (mul_ne_zero (by linarith) hQ) hz

private lemma chord_sq (N : ℕ) (j k : Fin N) :
    (polygon N (Sum.inl j) - polygon N (Sum.inl k))^2 +
      (polygon N (Sum.inr j) - polygon N (Sum.inr k))^2 =
        4 * Real.sin (Real.pi * ((j.val : ℝ) - k.val) / N)^2 := by
  let a := 2 * Real.pi * (j.val + 1 : ℝ) / N
  let b := 2 * Real.pi * (k.val + 1 : ℝ) / N
  have hab : (a - b) / 2 = Real.pi * ((j.val : ℝ) - k.val) / N := by
    dsimp [a, b]
    ring
  change (Real.cos a - Real.cos b)^2 + (Real.sin a - Real.sin b)^2 = _
  rw [← hab, Real.cos_sub_cos, Real.sin_sub_sin]
  have hunit := Real.sin_sq_add_cos_sq ((a + b) / 2)
  linear_combination 4 * Real.sin ((a - b) / 2)^2 * hunit

private lemma chord_sq_ne_zero (N : ℕ) (j k : Fin N) (hjk : j ≠ k) :
    (polygon N (Sum.inl j) - polygon N (Sum.inl k))^2 +
      (polygon N (Sum.inr j) - polygon N (Sum.inr k))^2 ≠ 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N from Nat.zero_lt_of_lt j.isLt)
  have hj : (j.val : ℝ) < N := by exact_mod_cast j.isLt
  have hk : (k.val : ℝ) < N := by exact_mod_cast k.isLt
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  have hlo : -Real.pi < Real.pi * ((j.val : ℝ) - k.val) / N := by
    apply (lt_div_iff₀ hN).mpr
    nlinarith [Real.pi_pos]
  have hhi : Real.pi * ((j.val : ℝ) - k.val) / N < Real.pi := by
    apply (div_lt_iff₀ hN).mpr
    nlinarith [Real.pi_pos]
  have hsin : Real.sin (Real.pi * ((j.val : ℝ) - k.val) / N) ≠ 0 := by
    intro hz
    have hz' := (Real.sin_eq_zero_iff_of_lt_of_lt hlo hhi).mp hz
    have hd : (j.val : ℝ) - k.val = 0 :=
      (mul_eq_zero.mp ((div_eq_zero_iff.mp hz').resolve_right (ne_of_gt hN))).resolve_left
        (ne_of_gt Real.pi_pos)
    have hv : j.val = k.val := by exact_mod_cast (sub_eq_zero.mp hd)
    exact hjk (Fin.ext hv)
  rw [chord_sq]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hsin)

private lemma entry_formula (N : ℕ) (p q : Fin N ⊕ Fin N) :
    let z := polygon N
    let v : Fin N ⊕ Fin N → ℝ := Pi.single q 1
    let d := fun j k : Fin N =>
      (z (Sum.inl j) - z (Sum.inl k))^2 + (z (Sum.inr j) - z (Sum.inr k))^2
    let e := fun j k : Fin N =>
      2*(z (Sum.inl j) - z (Sum.inl k))*(v (Sum.inl j) - v (Sum.inl k)) +
      2*(z (Sum.inr j) - z (Sum.inr k))*(v (Sum.inr j) - v (Sum.inr k))
    jacobian N p q = match p with
    | Sum.inl j => -charge N j * (1/2:ℝ) * v (Sum.inr j) -
        ∑ k : Fin N, if k = j then 0 else charge N k *
          ((v (Sum.inr j) - v (Sum.inr k))*d j k -
            (z (Sum.inr j) - z (Sum.inr k))*e j k) / (d j k)^2
    | Sum.inr j => charge N j * (1/2:ℝ) * v (Sum.inl j) +
        ∑ k : Fin N, if k = j then 0 else charge N k *
          ((v (Sum.inl j) - v (Sum.inl k))*d j k -
            (z (Sum.inl j) - z (Sum.inl k))*e j k) / (d j k)^2 := by
  let z := polygon N
  let v : Fin N ⊕ Fin N → ℝ := Pi.single q 1
  let F : ℝ → (Fin N ⊕ Fin N → ℝ) := fun t => z + t • v
  have hc (r : Fin N ⊕ Fin N) : HasDerivAt (fun t => F t r) (v r) 0 := by
    simpa only [F, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul] using
      ((hasDerivAt_id 0).mul_const (v r)).const_add (z r)
  have hd (j k : Fin N) : HasDerivAt
      (fun t => (F t (Sum.inl j) - F t (Sum.inl k))^2 +
        (F t (Sum.inr j) - F t (Sum.inr k))^2)
      (2*(z (Sum.inl j) - z (Sum.inl k))*(v (Sum.inl j) - v (Sum.inl k)) +
        2*(z (Sum.inr j) - z (Sum.inr k))*(v (Sum.inr j) - v (Sum.inr k))) 0 := by
    convert (((hc (Sum.inl j)).sub (hc (Sum.inl k))).pow 2).add
      (((hc (Sum.inr j)).sub (hc (Sum.inr k))).pow 2) using 1 <;> simp [F]
  have hi (r : Fin N → Fin N ⊕ Fin N) (j k : Fin N) (hkj : k ≠ j) :
      HasDerivAt
        (fun t => charge N k * (F t (r j) - F t (r k)) /
          ((F t (Sum.inl j) - F t (Sum.inl k))^2 +
            (F t (Sum.inr j) - F t (Sum.inr k))^2))
        (charge N k *
          ((v (r j) - v (r k))*
              ((z (Sum.inl j) - z (Sum.inl k))^2 + (z (Sum.inr j) - z (Sum.inr k))^2) -
            (z (r j) - z (r k))*
              (2*(z (Sum.inl j) - z (Sum.inl k))*(v (Sum.inl j) - v (Sum.inl k)) +
                2*(z (Sum.inr j) - z (Sum.inr k))*(v (Sum.inr j) - v (Sum.inr k)))) /
          ((z (Sum.inl j) - z (Sum.inl k))^2 + (z (Sum.inr j) - z (Sum.inr k))^2)^2) 0 := by
    convert (((hc (r j)).sub (hc (r k))).const_mul (charge N k)).div (hd j k)
      (by simpa [F, z] using chord_sq_ne_zero N j k hkj.symm) using 1 <;>
      simp [F] <;> ring
  cases p with
  | inl j =>
    apply HasDerivAt.deriv
    apply HasDerivAt.sub
    · simpa [F, z, v] using (hc (Sum.inr j)).const_mul (-charge N j * (1/2:ℝ))
    · apply HasDerivAt.fun_sum
      intro k hk
      by_cases hkj : k = j
      · simp only [hkj, ite_true]
        exact hasDerivAt_const _ _
      · simp only [hkj, ite_false]
        exact hi Sum.inr j k hkj
  | inr j =>
    apply HasDerivAt.deriv
    apply HasDerivAt.add
    · simpa [F, z, v] using (hc (Sum.inl j)).const_mul (charge N j * (1/2:ℝ))
    · apply HasDerivAt.fun_sum
      intro k hk
      by_cases hkj : k = j
      · simp only [hkj, ite_true]
        exact hasDerivAt_const _ _
      · simp only [hkj, ite_false]
        exact hi Sum.inl j k hkj

private lemma reflection_index (m : ℕ) (j k : Fin (2*m)) :
    ∃ t : ℤ, (((j+j-k).val : ℕ) : ℤ) = 2*(j.val : ℤ) - k.val + t*(2*m) := by
  have ha := Fin.val_add_eq_ite j j
  have hb := Fin.intCast_val_sub_eq_sub_add_ite (j+j) k
  split_ifs at ha with h
  · have ha' : (((j+j).val : ℕ) : ℤ) = 2*(j.val : ℤ) - (2*m : ℕ) := by
      rw [ha, Nat.cast_sub h]
      push_cast
      ring
    rw [ha'] at hb
    split_ifs at hb with h'
    · exact ⟨-1, by push_cast at *; linarith⟩
    · exact ⟨0, by push_cast at *; linarith⟩
  · have ha' : (((j+j).val : ℕ) : ℤ) = 2*(j.val : ℤ) := by
      rw [ha]
      push_cast
      ring
    rw [ha'] at hb
    split_ifs at hb with h'
    · exact ⟨0, by push_cast at *; linarith⟩
    · exact ⟨1, by push_cast at *; linarith⟩

private lemma reflection_charge (m : ℕ) (j k : Fin (2*m)) :
    charge (2*m) (j+j-k) = charge (2*m) k := by
  obtain ⟨t, ht⟩ := reflection_index m j k
  have he : Even ((j+j-k).val + k.val) := by
    apply (Int.even_coe_nat _).mp
    refine ⟨(j.val : ℤ) + t*m, ?_⟩
    push_cast
    linear_combination ht
  have hp : charge (2*m) (j+j-k) * charge (2*m) k = 1 := by
    simp only [charge, ← pow_add]
    apply Even.neg_one_pow
    convert he.add (by decide : Even 4) using 1 <;> omega
  have hs : charge (2*m) k * charge (2*m) k = 1 := by
    unfold charge
    rw [← pow_two, ← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  calc
    charge (2*m) (j+j-k) = charge (2*m) (j+j-k) * (charge (2*m) k * charge (2*m) k) := by rw [hs, mul_one]
    _ = charge (2*m) k := by rw [← mul_assoc, hp, one_mul]

private lemma reflection_pair (m : ℕ) (hm : 3 ≤ m) (j k : Fin (2*m)) (hkj : k ≠ j) :
    let z := polygon (2*m)
    let d := fun a b : Fin (2*m) =>
      (z (Sum.inl a)-z (Sum.inl b))^2 + (z (Sum.inr a)-z (Sum.inr b))^2
    (z (Sum.inl j)-z (Sum.inl k)) / d j k +
        (z (Sum.inl j)-z (Sum.inl (j+j-k))) / d j (j+j-k) = z (Sum.inl j) ∧
      (z (Sum.inr j)-z (Sum.inr k)) / d j k +
        (z (Sum.inr j)-z (Sum.inr (j+j-k))) / d j (j+j-k) = z (Sum.inr j) := by
  let a := 2*Real.pi*(j.val+1:ℝ)/((2*m:ℕ):ℝ)
  let b := 2*Real.pi*(k.val+1:ℝ)/((2*m:ℕ):ℝ)
  let c := 2*Real.pi*((j+j-k).val+1:ℝ)/((2*m:ℕ):ℝ)
  obtain ⟨t, ht⟩ := reflection_index m j k
  have htR := congrArg (fun n : ℤ => (n : ℝ)) ht
  push_cast at htR
  have hangle : c = (2*a-b) + (t:ℝ)*(2*Real.pi) := by
    dsimp [a, b, c]
    push_cast
    have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    field_simp
    nlinarith [htR]
  have hc : Real.cos c = Real.cos (2*a-b) := by rw [hangle, Real.cos_add_int_mul_two_pi]
  have hs : Real.sin c = Real.sin (2*a-b) := by rw [hangle, Real.sin_add_int_mul_two_pi]
  have hua := Real.sin_sq_add_cos_sq a
  have hub := Real.sin_sq_add_cos_sq b
  have huc := Real.sin_sq_add_cos_sq c
  have hdot : Real.cos a * Real.cos c + Real.sin a * Real.sin c =
      Real.cos a * Real.cos b + Real.sin a * Real.sin b := by
    rw [hc, hs, Real.cos_sub, Real.sin_sub, Real.cos_two_mul, Real.sin_two_mul]
    linear_combination (-2*Real.sin a*Real.sin b) * hua
  have hd : (Real.cos a-Real.cos c)^2 + (Real.sin a-Real.sin c)^2 =
      (Real.cos a-Real.cos b)^2 + (Real.sin a-Real.sin b)^2 := by nlinarith
  have hsimple : (Real.cos a-Real.cos b)^2 + (Real.sin a-Real.sin b)^2 =
      2-2*(Real.cos a*Real.cos b+Real.sin a*Real.sin b) := by nlinarith
  have hx : 2*Real.cos a-Real.cos b-Real.cos c =
      ((Real.cos a-Real.cos b)^2 + (Real.sin a-Real.sin b)^2)*Real.cos a := by
    rw [hsimple, hc, Real.cos_sub, Real.cos_two_mul, Real.sin_two_mul]
    ring
  have hy : 2*Real.sin a-Real.sin b-Real.sin c =
      ((Real.cos a-Real.cos b)^2 + (Real.sin a-Real.sin b)^2)*Real.sin a := by
    rw [hsimple, hs, Real.sin_sub, Real.cos_two_mul, Real.sin_two_mul]
    linear_combination (2*Real.sin b) * hua
  have hn : (Real.cos a-Real.cos b)^2 + (Real.sin a-Real.sin b)^2 ≠ 0 :=
    chord_sq_ne_zero (2*m) j k hkj.symm
  change (Real.cos a-Real.cos b) / _ + (Real.cos a-Real.cos c) / _ = _ ∧
    (Real.sin a-Real.sin b) / _ + (Real.sin a-Real.sin c) / _ = _
  rw [hd]
  constructor
  · rw [← add_div]
    apply (div_eq_iff hn).mpr
    linarith [hx]
  · rw [← add_div]
    apply (div_eq_iff hn).mpr
    linarith [hy]

private lemma equilibrium (m : ℕ) (hm : 3 ≤ m) :
    field (2 * m) (polygon (2 * m)) = 0 := by
  letI : NeZero (2*m) := ⟨by omega⟩
  let z := polygon (2*m)
  let d := fun j k : Fin (2*m) =>
    (z (Sum.inl j)-z (Sum.inl k))^2 + (z (Sum.inr j)-z (Sum.inr k))^2
  have htotal : (∑ k : Fin (2*m), charge (2*m) k) = 0 := by
    simp [charge, pow_add, Fin.sum_neg_one_pow, even_two_mul]
  have hsum (j : Fin (2*m)) (r : Fin (2*m) → Fin (2*m) ⊕ Fin (2*m))
      (hr : r = Sum.inl ∨ r = Sum.inr) :
      (∑ k : Fin (2*m), if k = j then 0 else
        charge (2*m) k * (z (r j)-z (r k)) / d j k) = -charge (2*m) j * z (r j) / 2 := by
    let f := fun k : Fin (2*m) => if k = j then 0 else
      charge (2*m) k * (z (r j)-z (r k)) / d j k
    let e : Equiv.Perm (Fin (2*m)) := { toFun := fun k => j+j-k
        invFun := fun k => j+j-k
        left_inv := by intro k; abel
        right_inv := by intro k; abel }
    have hperm : (∑ k, f (j+j-k)) = ∑ k, f k :=
      Fintype.sum_equiv e _ _ (by intro k; rfl)
    have hpair (k : Fin (2*m)) : f k + f (j+j-k) =
        if k = j then 0 else charge (2*m) k * z (r j) := by
      by_cases hkj : k = j
      · subst k; simp [f]
      · have hrj : j+j-k ≠ j := by
          intro h
          exact hkj (add_left_cancel (sub_eq_iff_eq_add.mp h)).symm
        simp only [f, hkj, hrj, ite_false, reflection_charge]
        rw [mul_div_assoc, mul_div_assoc, ← mul_add]
        congr 1
        rcases hr with rfl | rfl
        · exact (reflection_pair m hm j k hkj).1
        · exact (reflection_pair m hm j k hkj).2
    have hrem : (∑ k : Fin (2*m), if k = j then 0 else charge (2*m) k) = -charge (2*m) j := by
      have heach (k : Fin (2*m)) : charge (2*m) k =
          (if k = j then 0 else charge (2*m) k) + (if k = j then charge (2*m) k else 0) := by
        split_ifs <;> simp
      have he := congrArg (fun g : Fin (2*m) → ℝ => ∑ k, g k) (funext heach)
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, htotal] at he
      linarith
    have he : (∑ k, f k) + (∑ k, f k) = -charge (2*m) j * z (r j) := by
      calc
        _ = (∑ k, f k) + ∑ k, f (j+j-k) := by rw [hperm]
        _ = ∑ k, (f k + f (j+j-k)) := by rw [Finset.sum_add_distrib]
        _ = ∑ k : Fin (2*m), if k = j then 0 else charge (2*m) k * z (r j) :=
          Finset.sum_congr rfl (fun k _ => hpair k)
        _ = (∑ k : Fin (2*m), if k = j then 0 else charge (2*m) k) * z (r j) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          split_ifs <;> simp
        _ = _ := by rw [hrem]
    change (∑ k, f k) = _
    linarith
  funext p
  cases p with
  | inl j =>
    change -charge (2*m) j * (1/2:ℝ) * z (Sum.inr j) - _ = 0
    rw [hsum j Sum.inr (Or.inr rfl)]
    ring
  | inr j =>
    change charge (2*m) j * (1/2:ℝ) * z (Sum.inl j) + _ = 0
    rw [hsum j Sum.inl (Or.inl rfl)]
    ring

private def weights (m : ℕ) : Matrix (Fin (2*m)) (Fin (2*m)) ℝ :=
  fun j k => if j = k then 0 else
    1 / (4 * Real.sin (Real.pi * ((j.val : ℝ) - k.val) / (2*m))^2)

private def chargeMatrix (m : ℕ) : Matrix (Fin (2*m)) (Fin (2*m)) ℝ :=
  Matrix.diagonal (charge (2*m))

private def diagonalWeight (m : ℕ) : ℝ := (((2*m : ℕ) : ℝ)^2 - 1) / 12 - (m : ℝ)^2 / 2

private def blockB (m : ℕ) : Matrix (Fin (2*m)) (Fin (2*m)) ℝ :=
  (diagonalWeight m • 1 - weights m) * chargeMatrix m

private def blockC (m : ℕ) : Matrix (Fin (2*m)) (Fin (2*m)) ℝ :=
  ((diagonalWeight m + 1) • 1 - weights m) * chargeMatrix m

private def rotation (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks
    (Matrix.diagonal (fun j => polygon N (Sum.inl j)))
    (Matrix.diagonal (fun j => -polygon N (Sum.inr j)))
    (Matrix.diagonal (fun j => polygon N (Sum.inr j)))
    (Matrix.diagonal (fun j => polygon N (Sum.inl j)))

private lemma rotation_mul_transpose (N : ℕ) :
    rotation N * (rotation N).transpose = 1 := by
  unfold rotation
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_add]
  ext p q
  cases p with
  | inl j =>
    cases q with
    | inl k =>
      by_cases h : j = k
      · subst k
        simpa [Matrix.fromBlocks, polygon, pow_two, add_comm] using
          Real.sin_sq_add_cos_sq (2 * Real.pi * (j.val + 1 : ℝ) / N)
      · simp [Matrix.fromBlocks, Matrix.diagonal, h]
    | inr k =>
      by_cases h : j = k
      · subst k; simp [Matrix.fromBlocks, polygon]; ring
      · simp [Matrix.fromBlocks, Matrix.diagonal, h]
  | inr j =>
    cases q with
    | inl k =>
      by_cases h : j = k
      · subst k; simp [Matrix.fromBlocks, polygon]; ring
      · simp [Matrix.fromBlocks, Matrix.diagonal, h]
    | inr k =>
      by_cases h : j = k
      · subst k
        simpa [Matrix.fromBlocks, polygon, pow_two, add_comm] using
          Real.sin_sq_add_cos_sq (2 * Real.pi * (j.val + 1 : ℝ) / N)
      · simp [Matrix.fromBlocks, Matrix.diagonal, h]

private lemma rotated_jacobian (m : ℕ) (hm : 3 ≤ m) :
    (rotation (2*m)).transpose * jacobian (2*m) * rotation (2*m) =
      Matrix.fromBlocks 0 (blockB m) (blockC m) 0 := by sorry

private lemma nonzero_root_iff (m : ℕ) (hm : 3 ≤ m) (x : ℝ) (hx : x ≠ 0) :
    (jacobian (2*m)).charpoly.IsRoot x ↔
      (x^2 • 1 - blockC m * blockB m).det = 0 := by
  let B := blockB m
  let C := blockC m
  let I : Matrix (Fin (2*m)) (Fin (2*m)) ℝ := 1
  letI : Invertible (x • I) :=
    { invOf := x⁻¹ • I
      invOf_mul_self := by simp [I, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hx]
      mul_invOf_self := by simp [I, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hx] }
  have hchar : (jacobian (2*m)).charpoly =
      (Matrix.fromBlocks 0 B C 0).charpoly := by
    change _ = (Matrix.fromBlocks 0 (blockB m) (blockC m) 0).charpoly
    rw [← rotated_jacobian m hm, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      rotation_mul_transpose, Matrix.one_mul]
  have hmat : Matrix.scalar (Fin (2*m) ⊕ Fin (2*m)) x - Matrix.fromBlocks 0 B C 0 =
      Matrix.fromBlocks (x • I) (-B) (-C) (x • I) := by
    ext p q
    cases p <;> cases q <;>
      simp [Matrix.fromBlocks, Matrix.scalar, Matrix.diagonal, I, Matrix.one_apply]
  have hschur := Matrix.det_fromBlocks₁₁ (x • I) (-B) (-C) (x • I)
  change _ = (x • I).det * (x • I - (-C) * (x⁻¹ • I) * (-B)).det at hschur
  have hscale : x • (x • I - (-C) * (x⁻¹ • I) * (-B)) =
      x^2 • I - C * B := by
    simp [smul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul, I, hx, pow_two]
  have hd : (x • I).det ≠ 0 := by
    simp [I, Matrix.det_smul, hx]
  change Polynomial.eval x (jacobian (2*m)).charpoly = 0 ↔ _
  rw [hchar, Matrix.eval_charpoly, hmat, hschur]
  rw [mul_eq_zero, or_iff_right hd]
  change _ ↔ (x^2 • I - C*B).det = 0
  rw [← hscale, Matrix.det_smul]
  exact (mul_eq_zero.trans (or_iff_right (pow_ne_zero _ hx))).symm

private def gamma (m : ℕ) (k : ZMod (2*m)) : ℝ :=
  let r := min k.val (2*m - k.val)
  ((m : ℝ) - r)^2 * ((r : ℝ)^2 - 2) / 4

private lemma product_spectrum (m : ℕ) [NeZero (2*m)] (hm : 3 ≤ m) (y : ℝ) :
    (y • 1 - blockC m * blockB m).det =
      ∏ k : ZMod (2*m), (y - gamma m k) := by sorry

private lemma root_iff_mode (m : ℕ) (hm : 3 ≤ m) (x : ℝ) (hx : x ≠ 0) :
    (jacobian (2*m)).charpoly.IsRoot x ↔
      ∃ r : ℕ, 2 ≤ r ∧ r < m ∧
        x^2 = ((m : ℝ) - r)^2 * ((r : ℝ)^2 - 2) / 4 := by
  letI : NeZero (2*m) := ⟨by omega⟩
  rw [nonzero_root_iff m hm x hx, product_spectrum m hm]
  simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero]
  constructor
  · rintro ⟨k, hk⟩
    let r := min k.val (2*m - k.val)
    have hval := ZMod.val_lt k
    have hr : r ≤ m := by dsimp [r]; omega
    change x^2 = ((m : ℝ) - r)^2 * ((r : ℝ)^2 - 2) / 4 at hk
    have hxpos : 0 < x^2 := sq_pos_of_ne_zero hx
    have hr2 : 2 ≤ r := by
      by_contra h
      have : r = 0 ∨ r = 1 := by omega
      rcases this with h0 | h1
      · simp only [h0, Nat.cast_zero, sub_zero, zero_pow (by decide : (2:ℕ) ≠ 0), zero_sub] at hk
        nlinarith [sq_nonneg (m : ℝ)]
      · simp only [h1, Nat.cast_one, one_pow] at hk
        nlinarith [sq_nonneg ((m : ℝ) - 1)]
    have hrlt : r < m := by
      by_contra h
      have he : r = m := by omega
      rw [he] at hk
      simp at hk
      exact hx hk
    exact ⟨r, hr2, hrlt, hk⟩
  · rintro ⟨r, hr2, hrm, hr⟩
    refine ⟨(r : ZMod (2*m)), ?_⟩
    have hv : (r : ZMod (2*m)).val = r := ZMod.val_natCast_of_lt (by omega)
    have hf : min (r : ZMod (2*m)).val (2*m - (r : ZMod (2*m)).val) = r := by
      rw [hv]
      omega
    simpa only [gamma, hf] using hr

private def positiveRoot (m r : ℕ) : ℝ :=
  ((m : ℝ) - r) * Real.sqrt ((r : ℝ)^2 - 2) / 2

private lemma positiveRoot_pos (m r : ℕ) (hr : 2 ≤ r) (hrm : r < m) :
    0 < positiveRoot m r := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hmR : (r : ℝ) < m := by exact_mod_cast hrm
  unfold positiveRoot
  exact div_pos (mul_pos (by linarith) (Real.sqrt_pos.mpr (by nlinarith))) (by norm_num)

private lemma positiveRoot_sq (m r : ℕ) (hr : 2 ≤ r) :
    (positiveRoot m r)^2 = ((m : ℝ) - r)^2 * ((r : ℝ)^2 - 2) / 4 := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  unfold positiveRoot
  rw [div_pow, mul_pow, Real.sq_sqrt (by nlinarith : 0 ≤ (r : ℝ)^2 - 2)]
  norm_num

private lemma real_root_count (m : ℕ) (hm : 3 ≤ m) :
    (∀ x : ℝ, (jacobian (2 * m)).charpoly.IsRoot x →
      (jacobian (2 * m)).charpoly.IsRoot (-x)) ∧
      {x : ℝ | x ≠ 0 ∧ (jacobian (2 * m)).charpoly.IsRoot x}.ncard =
        2 * (m - 2) := by
  classical
  constructor
  · intro x hx
    by_cases hx0 : x = 0
    · simpa [hx0] using hx
    · apply (nonzero_root_iff m hm (-x) (neg_ne_zero.mpr hx0)).mpr
      simpa only [neg_sq] using (nonzero_root_iff m hm x hx0).mp hx
  · let s : Finset ℕ := Finset.Icc 2 (m-1)
    let p : ℕ → ℝ := positiveRoot m
    have hs (r : ℕ) : r ∈ s ↔ 2 ≤ r ∧ r < m := by
      simp only [s, Finset.mem_Icc]
      omega
    have hpos (r : ℕ) (hr : r ∈ s) : 0 < p r :=
      positiveRoot_pos m r ((hs r).mp hr).1 ((hs r).mp hr).2
    have hsq (r : ℕ) (hr : r ∈ s) :
        (p r)^2 = ((m : ℝ) - r)^2 * ((r : ℝ)^2 - 2) / 4 :=
      positiveRoot_sq m r ((hs r).mp hr).1
    have hinj : Set.InjOn p (s : Set ℕ) := by
      intro k hk l hl h
      by_contra hkl
      have heq : ((m : ℝ) - k)^2 * ((k : ℝ)^2 - 2) =
          ((m : ℝ) - l)^2 * ((l : ℝ)^2 - 2) := by
        have hpow := congrArg (fun t : ℝ => t^2) h
        rw [hsq k hk, hsq l hl] at hpow
        linarith
      rcases lt_or_gt_of_ne hkl with hlt | hgt
      · exact distinctness_certificate m k l ((hs k).mp hk).1 hlt ((hs l).mp hl).2 heq
      · exact distinctness_certificate m l k ((hs l).mp hl).1 hgt ((hs k).mp hk).2 heq.symm
    have hneginj : Set.InjOn (fun r => -p r) (s : Set ℕ) := by
      intro k hk l hl h
      exact hinj hk hl (neg_injective h)
    have hdisj : Disjoint (s.image p) (s.image (fun r => -p r)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨l, hl, heq⟩ := Finset.mem_image.mp hx'
      have := hpos k hk
      have := hpos l hl
      linarith
    have hset : {x : ℝ | x ≠ 0 ∧ (jacobian (2*m)).charpoly.IsRoot x} =
        ((s.image p ∪ s.image (fun r => -p r) : Finset ℝ) : Set ℝ) := by
      ext x
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨hx0, hx⟩
        obtain ⟨r, hr2, hrm, hr⟩ := (root_iff_mode m hm x hx0).mp hx
        have hrs : r ∈ s := (hs r).mpr ⟨hr2, hrm⟩
        have heq : x^2 = (p r)^2 := hr.trans (hsq r hrs).symm
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with hp | hn
        · exact Or.inl ⟨r, hrs, hp.symm⟩
        · exact Or.inr ⟨r, hrs, hn.symm⟩
      · rintro (⟨r, hrs, rfl⟩ | ⟨r, hrs, rfl⟩)
        · have hx0 := ne_of_gt (hpos r hrs)
          exact ⟨hx0, (root_iff_mode m hm (p r) hx0).mpr
            ⟨r, ((hs r).mp hrs).1, ((hs r).mp hrs).2, hsq r hrs⟩⟩
        · have hx0 := neg_ne_zero.mpr (ne_of_gt (hpos r hrs))
          refine ⟨hx0, (root_iff_mode m hm (-p r) hx0).mpr ?_⟩
          exact ⟨r, ((hs r).mp hrs).1, ((hs r).mp hrs).2, by simpa only [neg_sq] using hsq r hrs⟩
    rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_iff.mpr hinj, Finset.card_image_iff.mpr hneginj]
    have hcard : s.card = m-2 := by simp only [s, Nat.card_Icc]; omega
    rw [hcard]
    omega

def claim : Prop :=
  ∀ m : ℕ, 3 ≤ m →
    (∀ x : ℝ, (jacobian (2 * m)).charpoly.IsRoot x →
      (jacobian (2 * m)).charpoly.IsRoot (-x)) ∧
      {x : ℝ | x ≠ 0 ∧ (jacobian (2 * m)).charpoly.IsRoot x}.ncard =
        2 * (m - 2)

theorem result : claim := by
  intro m hm
  exact real_root_count m hm

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum
