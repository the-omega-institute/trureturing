/- GID: D5/S3/Factorization/Mordell/TangentSignAvoidance
   generality: G
   mirror-B: D5/B/S3/Factorization/Mordell/TangentSignAvoidance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simultaneous tangent avoidance in coordinate-sign orbits of common coverings. -/

import D5.S3.Factorization.Mordell.FieldKummer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Mordell.TangentSignAvoidance

universe u
variable {K : Type u} [Field K] [CharZero K]

private theorem sign_choice (x y : K) (hx : x ≠ 0) :
    x + y ≠ 0 ∨ -x + y ≠ 0 := by
  by_contra h
  push_neg at h
  apply hx
  linear_combination (h.1 - h.2) / 2

private theorem coordinate_choice (q r a b t x y z : K)
    (hqr : q * r ≠ 0) (hr : 15 * r ≠ 1) (hab : a ≠ 0 ∨ b ≠ 0)
    (hn : t ≠ 0 ∨ x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)
    (h₁ : y^2-q*x^2 = 5*q * r*t^2) (h₂ : x^2-z^2 = 15 * r*t^2) :
    ∃ t' y' z' : K, (t' = t ∨ t' = -t) ∧ (y' = y ∨ y' = -y) ∧
      (z' = z ∨ z' = -z) ∧
      ((15 * r+1)/2*x+(15 * r-1)/2*z'-15 * r*t' ≠ 0) ∧
      (a*y'-q*b*x-5*q * r*t' ≠ 0) := by
  have hq : q ≠ 0 := left_ne_zero_of_mul hqr
  have hr0 : r ≠ 0 := right_ne_zero_of_mul hqr
  have hx0 (ht : t = 0) : x ≠ 0 := by
    intro hx
    have hy : y = 0 := by simpa [ht,hx] using h₁
    have hz : z = 0 := by simpa [ht,hx] using h₂
    exact hn.elim (fun h => h ht) (fun h => h.elim (fun h => h hx)
      (fun h => h.elim (fun h => h hy) (fun h => h hz)))
  obtain ⟨t',y',ht',hy',hL₃⟩ : ∃ t' y' : K,
      (t' = t ∨ t' = -t) ∧ (y' = y ∨ y' = -y) ∧
      a*y'-q*b*x-5*q * r*t' ≠ 0 := by
    by_cases ht : t = 0
    · have hx := hx0 ht
      by_cases ha : a = 0
      · have hb : b ≠ 0 := hab.resolve_left (not_ne_iff.mpr ha)
        refine ⟨t,y,Or.inl rfl,Or.inl rfl,?_⟩
        simpa [ht,ha] using neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hq hb) hx)
      · have hy : y ≠ 0 := by
          intro hy
          have : q*x^2 = 0 := by simpa [ht,hy] using h₁.symm
          exact (mul_ne_zero hq (pow_ne_zero 2 hx)) this
        rcases sign_choice (a*y) (-q*b*x) (mul_ne_zero ha hy) with h|h
        · exact ⟨t,y,Or.inl rfl,Or.inl rfl,by simpa [ht,sub_eq_add_neg] using h⟩
        · exact ⟨t,-y,Or.inl rfl,Or.inr rfl,by simpa [ht,sub_eq_add_neg] using h⟩
    · have hc : -(5*q * r*t) ≠ 0 := neg_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hq) hr0) ht)
      rcases sign_choice (-(5*q * r*t)) (a*y-q*b*x) hc with h|h
      · exact ⟨t,y,Or.inl rfl,Or.inl rfl,by convert h using 1 <;> ring⟩
      · exact ⟨-t,y,Or.inr rfl,Or.inl rfl,by convert h using 1 <;> ring⟩
  have htsq : t'^2 = t^2 := by rcases ht' with h|h <;> simp [h]
  by_cases hz : z = 0
  · refine ⟨t',y',z,ht',hy',Or.inl rfl,?_,hL₃⟩
    intro hL₂
    have ht : t ≠ 0 := by
      intro ht
      have hx := hx0 ht
      apply hx
      have : x^2 = 0 := by simpa [ht,hz] using h₂
      exact sq_eq_zero_iff.mp this
    have ht'0 : t' ≠ 0 := by rcases ht' with h|h <;> simp [h,ht]
    have hA : ((15 * r+1)/2)^2-15 * r ≠ 0 := by
      intro h
      have hh : (15 * r-1)^2 = 0 := by linear_combination 4*h
      exact hr (sub_eq_zero.mp (sq_eq_zero_iff.mp hh))
    have hX : x^2 = 15 * r*t'^2 := by rw [htsq]; simpa [hz] using h₂
    have hZ : (15 * r)*(((15 * r+1)/2)^2-15 * r)*t'^2 = 0 := by
      have he : ((15 * r+1)/2)*x = 15 * r*t' := by simpa [hz] using sub_eq_zero.mp hL₂
      linear_combination -((15 * r+1)/2)^2*hX +
        (((15 * r+1)/2)*x+15 * r*t')*he
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hr0) hA)
      (pow_ne_zero 2 ht'0)) hZ
  · have hc : (15 * r-1)/2*z ≠ 0 :=
      mul_ne_zero (div_ne_zero (sub_ne_zero.mpr hr) (by norm_num)) hz
    rcases sign_choice ((15 * r-1)/2*z) ((15 * r+1)/2*x-15 * r*t') hc with h|h
    · exact ⟨t',y',z,ht',hy',Or.inl rfl,by convert h using 1 <;> ring,hL₃⟩
    · exact ⟨t',y',-z,ht',hy',Or.inr rfl,by convert h using 1 <;> ring,hL₃⟩

/-- Both original tangent forms avoid zero on one representative in the coordinate-sign
orbit of an actual common lambda covering tuple. Infinity and zero coordinates are included. -/
theorem simultaneous_tangent_sign_avoidance (q r a b : K)
    (hqr : q * r ≠ 0) (hr : 15 * r ≠ 1) (hab : a ≠ 0 ∨ b ≠ 0)
    (c : FieldKummer.CoveringRep (q * r) (Units.mk0 q (left_ne_zero_of_mul hqr)) 1) :
    ∃ c' : FieldKummer.CoveringRep (q * r) (Units.mk0 q (left_ne_zero_of_mul hqr)) 1,
      (c'.t = c.t ∨ c'.t = -c.t) ∧ (c'.z₁ = c.z₁ ∨ c'.z₁ = -c.z₁) ∧
      (c'.z₂ = c.z₂ ∨ c'.z₂ = -c.z₂) ∧ (c'.z₃ = c.z₃ ∨ c'.z₃ = -c.z₃) ∧
      ((15 * r+1)/2*c'.z₁+(15 * r-1)/2*c'.z₃-15 * r*c'.t ≠ 0) ∧
      (a*c'.z₂-q*b*c'.z₁-5*q * r*c'.t ≠ 0) := by
  classical
  have h₁ : c.z₂^2-q*c.z₁^2 = 5*q * r*c.t^2 := by
    simpa [mul_assoc] using c.eq₁₂
  have h₂ : c.z₁^2-c.z₃^2 = 15 * r*c.t^2 := by
    have h := c.eq₁₃
    change q*c.z₁^2-q*1*c.z₃^2 = 15*(q * r)*c.t^2 at h
    apply (mul_left_cancel₀ (left_ne_zero_of_mul hqr))
    linear_combination h
  obtain ⟨t,y,z,ht,hy,hz,hL₂,hL₃⟩ :=
    coordinate_choice q r a b c.t c.z₁ c.z₂ c.z₃ hqr hr hab c.nonzero h₁ h₂
  let c' : FieldKummer.CoveringRep (q * r) (Units.mk0 q (left_ne_zero_of_mul hqr)) 1 := {
    t := t, z₁ := c.z₁, z₂ := y, z₃ := z
    nonzero := by
      rcases ht with h|h <;> rcases hy with k|k <;> rcases hz with l|l <;>
        simpa [h,k,l] using c.nonzero
    eq₁₂ := by
      rcases ht with h|h <;> rcases hy with k|k <;>
        simpa [h,k,mul_assoc] using h₁
    eq₁₃ := by
      rcases ht with h|h <;> rcases hz with k|k <;>
        simp only [Units.val_mk0,Units.val_one,mul_one,h,k,neg_sq]
      all_goals linear_combination q*h₂ }
  exact ⟨c',ht,Or.inl rfl,hy,hz,hL₂,hL₃⟩

end D5.S3.Factorization.Mordell.TangentSignAvoidance
