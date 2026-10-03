/- GID: D5/S1/Recurrence/FiniteColumnGcdNormalization
   generality: G
   mirror-B: D5/B/S1/Recurrence/FiniteColumnGcdNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Bezout elimination constructs an integral column automorphism with prescribed gcd pivot. -/

import Mathlib

namespace D5.S1.Recurrence.FiniteColumnGcdNormalization

/-- An integral automorphism eliminates the selected finite coordinates into a nonnegative
pivot gcd. The formula includes negative inputs, zero gcd, and untouched outside coordinates. -/
theorem finite_column_gcd_normalization {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι) (hp : p ∉ s) (a : ℤ) (v : ι → ℤ) :
    ∃ e : (ι → ℤ) ≃ₗ[ℤ] (ι → ℤ),
      ∀ x : ι → ℤ, x p = a → (∀ i ∈ s, x i = v i) →
        e x = fun i => if i = p then
          (Nat.gcd a.natAbs (s.gcd (fun j => (v j).natAbs)) : ℤ)
          else if i ∈ s then 0 else x i := by
  classical
  have pair (p q : ι) (hpq : p ≠ q) (a b : ℤ) :
      ∃ e : (ι → ℤ) ≃ₗ[ℤ] (ι → ℤ), ∀ x : ι → ℤ,
        x p = a → x q = b →
        e x = fun i => if i = p then (Int.gcd a b : ℤ)
          else if i = q then 0 else x i := by
    by_cases hz : Int.gcd a b = 0
    · have ha : a = 0 := Int.eq_zero_of_gcd_eq_zero_left hz
      have hb : b = 0 := Int.eq_zero_of_gcd_eq_zero_right hz
      refine ⟨LinearEquiv.refl ℤ _, ?_⟩
      intro x hxp hxq
      ext i
      by_cases hip : i = p
      · subst i; simp [hxp, ha, hb]
      by_cases hiq : i = q
      · subst i; simp [hip, hxq, hb]
      simp [hip, hiq]
    let g : ℤ := Int.gcd a b
    let c := Int.gcdA a b
    let d := Int.gcdB a b
    let u := a / g
    let w := b / g
    have hg : g ≠ 0 := by dsimp [g]; exact_mod_cast hz
    have ha : g * u = a := by
      simpa [u, mul_comm] using Int.ediv_mul_cancel (Int.gcd_dvd_left a b)
    have hb : g * w = b := by
      simpa [w, mul_comm] using Int.ediv_mul_cancel (Int.gcd_dvd_right a b)
    have bez : a * c + b * d = g := (Int.gcd_eq_gcd_ab a b).symm
    have det : c * u + d * w = 1 := by
      apply mul_left_cancel₀ hg
      calc
        g * (c * u + d * w) = (g * u) * c + (g * w) * d := by ring
        _ = g * 1 := by simpa only [ha, hb, mul_one] using bez
    let e : (ι → ℤ) ≃ₗ[ℤ] (ι → ℤ) :=
      { toFun := fun x i => if i = p then c * x p + d * x q
          else if i = q then -w * x p + u * x q else x i
        invFun := fun y i => if i = p then u * y p - d * y q
          else if i = q then w * y p + c * y q else y i
        left_inv := by
          intro x
          ext i
          by_cases hip : i = p
          · subst i; simp only [ite_true, ite_false, hpq, Ne.symm hpq]
            calc
              _ = (c * u + d * w) * x p := by ring
              _ = x p := by rw [det, one_mul]
          by_cases hiq : i = q
          · subst i; simp only [ite_true, ite_false, hip, hpq]
            calc
              _ = (c * u + d * w) * x q := by ring
              _ = x q := by rw [det, one_mul]
          simp [hip, hiq]
        right_inv := by
          intro x
          ext i
          by_cases hip : i = p
          · subst i; simp only [ite_true, ite_false, hpq, Ne.symm hpq]
            calc
              _ = (c * u + d * w) * x p := by ring
              _ = x p := by rw [det, one_mul]
          by_cases hiq : i = q
          · subst i; simp only [ite_true, ite_false, hip, hpq]
            calc
              _ = (c * u + d * w) * x q := by ring
              _ = x q := by rw [det, one_mul]
          simp [hip, hiq]
        map_add' := by
          intro x y
          ext i
          by_cases hip : i = p <;> by_cases hiq : i = q <;>
            simp [hip, hiq, hpq, Ne.symm hpq, mul_add] <;> ring
        map_smul' := by
          intro r x
          ext i
          by_cases hip : i = p <;> by_cases hiq : i = q <;>
            simp [hip, hiq, hpq, Ne.symm hpq, smul_eq_mul] <;> ring }
    refine ⟨e, ?_⟩
    intro x hxp hxq
    ext i
    by_cases hip : i = p
    · subst i; simp [e, hxp, hxq]; simpa [g, mul_comm] using bez
    by_cases hiq : i = q
    · subst i; simp [e, hip, hxp, hxq]; rw [← ha, ← hb]; ring
    simp [e, hip, hiq]
  induction s using Finset.induction_on with
  | empty =>
    by_cases hn : a < 0
    · let e : (ι → ℤ) ≃ₗ[ℤ] (ι → ℤ) :=
        { toFun := fun x i => if i = p then -x i else x i
          invFun := fun x i => if i = p then -x i else x i
          left_inv := by intro x; ext i; by_cases h : i = p <;> simp [h]
          right_inv := by intro x; ext i; by_cases h : i = p <;> simp [h]
          map_add' := by intro x y; ext i; by_cases h : i = p <;> simp [h, add_comm]
          map_smul' := by intro r x; ext i; by_cases h : i = p <;> simp [h] }
      refine ⟨e, ?_⟩
      intro x hxp _
      ext i
      by_cases h : i = p
      · subst i; simp [e, hxp, Int.natCast_natAbs, abs_of_neg hn]
      simp [e, h]
    · refine ⟨LinearEquiv.refl ℤ _, ?_⟩
      intro x hxp _
      ext i
      by_cases h : i = p
      · subst i; simp [hxp, Int.natCast_natAbs, abs_of_nonneg (le_of_not_gt hn)]
      simp [h]
  | @insert q s hqs ih =>
    have hps : p ∉ s := fun h => hp (Finset.mem_insert_of_mem h)
    have hpq : p ≠ q := fun h => hp (h.symm ▸ Finset.mem_insert_self q s)
    obtain ⟨e, he⟩ := ih hps
    let g := Nat.gcd a.natAbs (s.gcd (fun j => (v j).natAbs))
    obtain ⟨f, hf⟩ := pair p q hpq (g : ℤ) (v q)
    refine ⟨e.trans f, ?_⟩
    intro x hxp hx
    have hxold : ∀ i ∈ s, x i = v i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have ex := he x hxp hxold
    have ep : e x p = (g : ℤ) := by rw [ex]; simp [g]
    have eq : e x q = v q := by
      rw [ex]; simp [Ne.symm hpq, hqs, hx q (Finset.mem_insert_self q s)]
    change f (e x) = _
    rw [hf (e x) ep eq]
    have hg : Int.gcd (g : ℤ) (v q) =
        Nat.gcd a.natAbs ((insert q s).gcd (fun j => (v j).natAbs)) := by
      simp only [Int.gcd, Int.natAbs_natCast, Finset.gcd_insert, g]
      change Nat.gcd (Nat.gcd a.natAbs (s.gcd _)) (v q).natAbs =
        Nat.gcd a.natAbs (Nat.gcd (v q).natAbs (s.gcd _))
      rw [Nat.gcd_assoc, Nat.gcd_comm (s.gcd _) (v q).natAbs]
    ext i
    by_cases hip : i = p
    · subst i; simp [hg]
    by_cases hiq : i = q
    · subst i; simp [hip]
    simp [hip, hiq, ex]


#print axioms finite_column_gcd_normalization

end D5.S1.Recurrence.FiniteColumnGcdNormalization

