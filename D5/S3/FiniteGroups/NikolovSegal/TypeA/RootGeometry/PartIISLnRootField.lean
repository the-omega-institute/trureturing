/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnRootField
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnRootField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnRootIncidence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnRootAction
open Matrix
universe u
variable {F : Type u} [Field F] {n : ℕ}

private theorem coordinate_one_ne_zero (f : F ≃+ F) : f 1 ≠ 0 :=
  fun h => one_ne_zero (f.map_eq_zero_iff.mp h)

noncomputable def normalizedCoordinate (f : F ≃+ F) : F ≃+ F where
  toFun t := (f 1)⁻¹*f t
  invFun t := f.symm (f 1*t)
  left_inv t := by simp [mul_assoc,coordinate_one_ne_zero]
  right_inv t := by simp [mul_assoc,coordinate_one_ne_zero]
  map_add' t s := by simp [map_add,mul_add]

theorem coordinate_scale (f : F ≃+ F) (t : F) : f t = f 1 * normalizedCoordinate f t := by
  change f t = f 1*((f 1)⁻¹*f t)
  rw [← mul_assoc,mul_inv_cancel₀ (coordinate_one_ne_zero f),one_mul]

/-- The genuine multiplication law from one A2 triangle reconstructs a
field automorphism. The commutator sign cancels under normalization. -/
theorem triangle_field (f g h : F ≃+ F) (e : F) (he : e ≠ 0)
    (hm : ∀ t u, h (t*u) = e*f t*g u) :
    ∃ phi : RingAut F,
      (∀ t, normalizedCoordinate f t = phi t) ∧
      (∀ t, normalizedCoordinate g t = phi t) ∧
      (∀ t, normalizedCoordinate h t = phi t) := by
  have hf := coordinate_one_ne_zero f
  have hg := coordinate_one_ne_zero g
  have hh := coordinate_one_ne_zero h
  have hrow : ∀ t, h t = e*f t*g 1 := by intro t; simpa only [mul_one] using hm t 1
  have hcol : ∀ t, h t = e*f 1*g t := by intro t; simpa only [one_mul] using hm 1 t
  have h1 : h 1 = e*f 1*g 1 := by simpa using hm 1 1
  have hfg : ∀ t, normalizedCoordinate g t = normalizedCoordinate f t := by
    intro t
    have heq : f 1*g t = f t*g 1 := by
      apply mul_left_cancel₀ he
      simpa only [mul_assoc] using (hcol t).symm.trans (hrow t)
    change (g 1)⁻¹*g t = (f 1)⁻¹*f t
    apply mul_left_cancel₀ (mul_ne_zero hf hg)
    calc
      (f 1*g 1)*((g 1)⁻¹*g t) = f 1*g t := by field_simp
      _ = f t*g 1 := heq
      _ = (f 1*g 1)*((f 1)⁻¹*f t) := by field_simp
  have hhf : ∀ t, normalizedCoordinate h t = normalizedCoordinate f t := by
    intro t
    change (h 1)⁻¹*h t = (f 1)⁻¹*f t
    rw [hrow t,h1]
    field_simp
    <;> ring
  have hprod : ∀ t u, normalizedCoordinate h (t*u) =
      normalizedCoordinate f t * normalizedCoordinate g u := by
    intro t u
    change (h 1)⁻¹*h (t*u) = ((f 1)⁻¹*f t)*((g 1)⁻¹*g u)
    rw [hm,h1]
    field_simp
    <;> ring
  let phi : RingAut F :=
    { normalizedCoordinate f with
      map_mul' := by
        intro t u
        change normalizedCoordinate f (t*u) = normalizedCoordinate f t * normalizedCoordinate f u
        simpa only [hhf,hfg] using hprod t u }
  exact ⟨phi,fun _ => rfl,hfg,hhf⟩

/-- Every A2 triangle carries the SAME normalized field map globally:
all positive intervals connect through the genuine (0,n-1) root. -/
theorem common_root_field (hn : 2 < n) (sigma : PositiveIndex n → PositiveIndex n)
    (f : PositiveIndex n → F ≃+ F)
    (hinc : ∀ (i j k : Fin n) (hij : i < j) (hjk : j < k) (t u : F),
      root (sigma ⟨(i,j),hij⟩) (f ⟨(i,j),hij⟩ t) *
        root (sigma ⟨(j,k),hjk⟩) (f ⟨(j,k),hjk⟩ u) *
        (root (sigma ⟨(i,j),hij⟩) (f ⟨(i,j),hij⟩ t))⁻¹ *
        (root (sigma ⟨(j,k),hjk⟩) (f ⟨(j,k),hjk⟩ u))⁻¹ =
        root (sigma ⟨(i,k),hij.trans hjk⟩) (f ⟨(i,k),hij.trans hjk⟩ (t*u))) :
    ∃ phi : RingAut F, ∀ r t, f r t = f r 1*phi t := by
  have htri : ∀ (i j k : Fin n) (hij : i < j) (hjk : j < k),
      ∃ phi : RingAut F,
        (∀ t, normalizedCoordinate (f ⟨(i,j),hij⟩) t = phi t) ∧
        (∀ t, normalizedCoordinate (f ⟨(j,k),hjk⟩) t = phi t) ∧
        (∀ t, normalizedCoordinate (f ⟨(i,k),hij.trans hjk⟩) t = phi t) := by
    intro i j k hij hjk
    obtain ⟨e,he,hm⟩ := root_coordinate_triangle _ _ _ _ _ _ (hinc i j k hij hjk)
    exact triangle_field _ _ _ e he hm
  have heq : ∀ (i j k : Fin n) (hij : i < j) (hjk : j < k) (t : F),
      normalizedCoordinate (f ⟨(i,j),hij⟩) t = normalizedCoordinate (f ⟨(i,k),hij.trans hjk⟩) t ∧
      normalizedCoordinate (f ⟨(j,k),hjk⟩) t = normalizedCoordinate (f ⟨(i,k),hij.trans hjk⟩) t := by
    intro i j k hij hjk t
    obtain ⟨phi,h1,h2,h3⟩ := htri i j k hij hjk
    exact ⟨(h1 t).trans (h3 t).symm,(h2 t).trans (h3 t).symm⟩
  let lo : Fin n := ⟨0,by omega⟩
  let mid : Fin n := ⟨1,by omega⟩
  let last : Fin n := ⟨n-1,by omega⟩
  have hlo : lo < mid := by change 0 < 1; decide
  have hlast : mid < last := by change 1 < n-1; omega
  let anchor : PositiveIndex n := ⟨(lo,last),hlo.trans hlast⟩
  obtain ⟨phi,_,_,ha⟩ := htri lo mid last hlo hlast
  have hall : ∀ r t, normalizedCoordinate (f r) t = normalizedCoordinate (f anchor) t := by
    rintro ⟨⟨i,j⟩,hij⟩ t
    by_cases hi : i = lo
    · subst i
      by_cases hj : j = last
      · subst j; rfl
      · have hjl : j < last := by
          have hv : j.val ≠ n-1 := fun h => hj (Fin.ext h)
          change j.val < n-1
          omega
        exact (heq lo j last hij hjl t).1
    · have hli : lo < i := by
        have hv : i.val ≠ 0 := fun h => hi (Fin.ext h)
        change 0 < i.val
        omega
      by_cases hj : j = last
      · subst j
        exact (heq lo i last hli hij t).2
      · have hjl : j < last := by
          have hv : j.val ≠ n-1 := fun h => hj (Fin.ext h)
          change j.val < n-1
          omega
        exact (heq lo i j hli hij t).2.trans (heq lo j last (hli.trans hij) hjl t).1
  refine ⟨phi,?_⟩
  intro r t
  rw [coordinate_scale (f r) t,hall r t]
  exact congrArg (fun x : F => f r 1*x) (ha t)

end NikolovSegal.SLnRootAction
