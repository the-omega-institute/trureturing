import D5.S3.FiniteGroups.LeeSquareCompression

set_option autoImplicit false

namespace D5.S3.FiniteGroups.EvenFirstInvariantFactor

open D5.S3.FiniteGroups.NearSquareLatticeRigidity
open D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity (sumDiff)
open D5.S3.FiniteGroups.LeeSquareCompression

/-- If every relation has even coordinates and the Lee ball of radius `s ≥ 1` meets every
coset of `K`, then every coset of the pull-back of `K` along `(u,v) ↦ (u+v,u-v)` meets the
square `[0,s)²`. -/
private theorem square_cover (K : Submodule ℤ Plane) {s : ℤ}
    (heven : ∀ z ∈ K, 2 ∣ z 0 ∧ 2 ∣ z 1)
    (hcover : ∀ z : Plane, ∃ r : Plane, |r 0| + |r 1| ≤ s ∧ z - r ∈ K) :
    RectangleCovers (K.comap sumDiff) s s := by
  intro z
  obtain ⟨t, rfl | rfl⟩ := Int.even_or_odd' s
  · let v : Plane := ![z 0 - t + (z 1 - t) + 1, z 0 - t - (z 1 - t)]
    obtain ⟨r, hr, hvr⟩ := hcover v
    obtain ⟨h0, h1⟩ := heven _ hvr
    rw [lee_iff_square, abs_le, abs_le] at hr
    change 2 ∣ v 0 - r 0 at h0
    change 2 ∣ v 1 - r 1 at h1
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
    obtain ⟨i, hi⟩ : 2 ∣ r 0 + r 1 - 1 := by omega
    obtain ⟨j, hj⟩ : 2 ∣ r 0 - r 1 - 1 := by omega
    refine ⟨i + t, j + t, by omega, by omega, by omega, by omega, ?_⟩
    rw [Submodule.mem_comap]
    convert hvr using 1
    ext l
    fin_cases l <;> simp [sumDiff, v] <;> omega
  · let v : Plane := ![z 0 - t + (z 1 - t), z 0 - t - (z 1 - t)]
    obtain ⟨r, hr, hvr⟩ := hcover v
    obtain ⟨h0, h1⟩ := heven _ hvr
    rw [lee_iff_square, abs_le, abs_le] at hr
    change 2 ∣ v 0 - r 0 at h0
    change 2 ∣ v 1 - r 1 at h1
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
    obtain ⟨i, hi⟩ : 2 ∣ r 0 + r 1 := by omega
    obtain ⟨j, hj⟩ : 2 ∣ r 0 - r 1 := by omega
    refine ⟨i + t, j + t, by omega, by omega, by omega, by omega, ?_⟩
    rw [Submodule.mem_comap]
    convert hvr using 1
    ext l
    fin_cases l <;> simp [sumDiff, v] <;> omega

theorem even_factor {c k : ℕ} {s : ℤ} (hc : 2 ≤ c) (hceven : Even c) (_hk : 1 ≤ k)
    (hs : 1 ≤ s) (a b : Target c k)
    (hcover : ∀ g : Target c k, ∃ x y : ℤ, |x| + |y| ≤ s ∧ x • a + y • b = g) :
    (c : ℤ) ^ 2 * k ≤ 2 * s ^ 2 ∧ ((c : ℤ) ^ 2 * k = 2 * s ^ 2 → (c : ℤ) ∣ s) ∧
      (Odd s → (c : ℤ) ^ 2 * k ≤ 2 * s ^ 2 - 2) := by
  let f : Plane →+ Target c k := {
    toFun := fun z => z 0 • a + z 1 • b
    map_zero' := by simp
    map_add' := by
      intro z w
      change (z 0 + w 0) • a + (z 1 + w 1) • b =
        (z 0 • a + z 1 • b) + (w 0 • a + w 1 • b)
      rw [add_zsmul, add_zsmul]
      abel }
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨x, y, _, he⟩ := hcover g
    exact ⟨![x, y], he⟩
  let K := f.toIntLinearMap.ker
  have hKdiv : ∀ z ∈ K, (c : ℤ) ∣ z 0 ∧ (c : ℤ) ∣ z 1 := fun z hz =>
    kernel_coordinates_dvd (by omega) f hf hz
  have h2c : (2 : ℤ) ∣ c := by exact_mod_cast hceven.two_dvd
  have hKeven : ∀ z ∈ K, 2 ∣ z 0 ∧ 2 ∣ z 1 := fun z hz =>
    ⟨h2c.trans (hKdiv z hz).1, h2c.trans (hKdiv z hz).2⟩
  have hKcover : ∀ z : Plane, ∃ r : Plane, |r 0| + |r 1| ≤ s ∧ z - r ∈ K := by
    intro z
    obtain ⟨x, y, hxy, he⟩ := hcover (f z)
    refine ⟨![x, y], hxy, ?_⟩
    change f (z - ![x, y]) = 0
    rw [map_sub]
    change f z - (x • a + y • b) = 0
    rw [he, sub_self]
  have hKidx : (K.toAddSubgroup.index : ℤ) = (c : ℤ) ^ 2 * k := by
    exact_mod_cast kernel_index f hf
  let M := K.comap sumDiff
  have hmap : M.map sumDiff = K := by
    rw [Submodule.map_comap_eq, inf_eq_right]
    intro z hz
    obtain ⟨h0, h1⟩ := hKeven z hz
    obtain ⟨p, hp⟩ : 2 ∣ z 0 + z 1 := dvd_add h0 h1
    obtain ⟨q, hq⟩ : 2 ∣ z 0 - z 1 := dvd_sub h0 h1
    refine ⟨![p, q], ?_⟩
    ext l
    fin_cases l <;> simp [sumDiff] <;> omega
  have hMidx : (K.toAddSubgroup.index : ℤ) = (M.toAddSubgroup.index : ℤ) * 2 := by
    have h := mapped_index M
    rw [hmap] at h
    exact_mod_cast h
  have hrect := square_cover K hKeven hKcover
  have hbound := rectangle_index_bound M hrect
  have hle : (c : ℤ) ^ 2 * k ≤ 2 * s ^ 2 := by nlinarith
  have heq : (c : ℤ) ^ 2 * k = 2 * s ^ 2 → (c : ℤ) ∣ s := by
    intro he
    have hMs : (M.toAddSubgroup.index : ℤ) = s ^ 2 - 0 := by nlinarith
    have hc2 : (4 : ℤ) ≤ (c : ℤ) ^ 2 * k := by
      have : (2 : ℤ) ≤ c := by exact_mod_cast hc
      have hk1 : (1 : ℤ) ≤ k := by exact_mod_cast _hk
      nlinarith
    have hs2 : 2 ≤ s := by nlinarith
    obtain ⟨a', b', ε, -, -, -, -, hε, hab, hspan⟩ :=
      near_square_rigidity M hs2 le_rfl (by omega) hMs hrect
    have hu : (![s, -ε * b'] : Plane) ∈ M := by
      rw [hspan]
      exact Submodule.subset_span ⟨0, rfl⟩
    have hw : (![-a', ε * s] : Plane) ∈ M := by
      rw [hspan]
      exact Submodule.subset_span ⟨1, rfl⟩
    rcases mul_eq_zero.1 hab with ha0 | hb0
    · have hK := hKdiv _ (Submodule.mem_comap.1 hw)
      simp [sumDiff, ha0] at hK
      rcases hε with rfl | rfl
      · simpa using hK.1
      · simpa using hK.1
    · have hK := hKdiv _ (Submodule.mem_comap.1 hu)
      simp [sumDiff, hb0] at hK
      exact hK.1
  refine ⟨hle, heq, fun hodd => ?_⟩
  have hne : (c : ℤ) ^ 2 * k ≠ 2 * s ^ 2 := by
    intro he
    obtain ⟨m, hm⟩ := hodd
    have h2s : (2 : ℤ) ∣ s := h2c.trans (heq he)
    omega
  obtain ⟨d, hd⟩ := hceven
  have hcd : (c : ℤ) ^ 2 * k = 4 * ((d : ℤ) * d * k) := by rw [hd]; push_cast; ring
  rw [hcd] at hle hne ⊢
  generalize (d : ℤ) * d * k = P at hle hne ⊢
  generalize s ^ 2 = Q at hle hne ⊢
  omega

end D5.S3.FiniteGroups.EvenFirstInvariantFactor
