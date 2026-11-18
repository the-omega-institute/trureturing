/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalElementaryFibers
   generality: G
   mirror-B: none(waiver:original-elementary-endpoint-fibers)
   mirror-E: none(waiver:original-elementary-endpoint-fibers)
   anchors: []
   utility: none
   digest: Complete elementary actual endpoint fibers, including nonunit right sides. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalLinearFibers

/-! The shifted factors may both be nonunits. A factor nonzero modulo p²
still determines the opposite literal endpoint; two factors zero modulo p²
leave at most one actual pair. -/

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem primeCube_cancel_to_square {p : ℕ} (hp : p.Prime)
    {A d : ℤ} (hA : ¬ (p : ℤ)^2 ∣ A) (h : (p : ℤ)^3 ∣ A*d) :
    (p : ℤ)^2 ∣ d := by
  have hprime := Nat.prime_iff_prime_int.mp hp
  by_cases hd : (p : ℤ) ∣ A
  · obtain ⟨u, rfl⟩ := hd
    have hu : ¬ (p : ℤ) ∣ u := by
      rintro ⟨v, rfl⟩
      apply hA
      exact ⟨v, by ring⟩
    have hh : (p : ℤ) * (p : ℤ)^2 ∣ (p : ℤ) * (u*d) := by
      convert h using 1 <;> ring
    have hh' : (p : ℤ)^2 ∣ u*d :=
      (mul_dvd_mul_iff_left (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)).mp hh
    exact hprime.pow_dvd_of_dvd_mul_left 2 hu hh'
  · exact dvd_trans (pow_dvd_pow (p : ℤ) (by decide : 2 ≤ 3))
      (hprime.pow_dvd_of_dvd_mul_left 3 hd h)

private theorem shifted_factor_cancel {p : ℕ} (hp : p.Prime)
    {X : ℝ} (hXsmall : 2*X < (p^2 : ℕ))
    {A : ZMod (p^3)} (hA : ¬ (p : ℤ)^2 ∣ (A.val : ℤ))
    {u v : ℤ} (hu : |(u : ℝ)| ≤ X) (hv : |(v : ℝ)| ≤ X)
    (he : A * (u : ZMod (p^3)) = A * (v : ZMod (p^3))) : u = v := by
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hd : (p : ℤ)^3 ∣ (A.val : ℤ)*(u-v) := by
    have hm : (((A.val : ℤ)*(u-v) : ℤ) : ZMod (p^3)) = 0 := by
      push_cast
      simpa only [ZMod.natCast_zmod_val, mul_sub] using sub_eq_zero.mpr he
    simpa only [Nat.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hm
  have hd' := primeCube_cancel_to_square hp hA hd
  apply integer_eq_of_box_residue hu hv hXsmall
  apply sub_eq_zero.mp
  simpa only [Int.cast_sub] using
    (ZMod.intCast_zmod_eq_zero_iff_dvd (u-v) (p^2)).mpr (by simpa using hd')

private theorem deep_shifted_factor_unique {p : ℕ} (hp : p.Prime)
    {X : ℝ} (hXsmall : 2*X < (p^2 : ℕ))
    {k : ZMod (p^3)} (hk : IsUnit k)
    {u v : ℤ} (hu : |(u : ℝ)| ≤ X) (hv : |(v : ℝ)| ≤ X)
    (hdu : (p : ℤ)^2 ∣ ((1-k*(u : ZMod (p^3))).val : ℤ))
    (hdv : (p : ℤ)^2 ∣ ((1-k*(v : ZMod (p^3))).val : ℤ)) : u = v := by
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let reduction : ZMod (p^3) →+* ZMod (p^2) :=
    ZMod.castHom (pow_dvd_pow p (by decide : 2 ≤ 3)) _
  have hz (n : ℤ) (hd : (p : ℤ)^2 ∣ ((1-k*(n : ZMod (p^3))).val : ℤ)) :
      1 - reduction k * (n : ZMod (p^2)) = 0 := by
    have h : (((1-k*(n : ZMod (p^3))).val : ℤ) : ZMod (p^2)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa using hd)
    have hvcast :
        (((1-k*(n : ZMod (p^3))).val : ℤ) : ZMod (p^2)) =
          reduction (1-k*(n : ZMod (p^3))) := by
      simpa only [map_natCast, Int.cast_natCast] using
        congrArg reduction (ZMod.natCast_zmod_val (1-k*(n : ZMod (p^3))))
    rw [hvcast] at h
    simpa only [map_sub, map_one, map_mul, map_intCast] using h
  have hmod : (u : ZMod (p^2)) = v := (hk.map reduction).mul_left_cancel (by
    have h₁ := hz u hdu
    have h₂ := hz v hdv
    linear_combination -h₁ + h₂)
  exact integer_eq_of_box_residue hu hv hXsmall hmod

/-- Every ordered original endpoint pair in a literal lattice section is
counted, without assuming that the hyperbola right side is a unit. -/
theorem actual_endpoint_pair_elementary_count {p : ℕ} (hp : p.Prime)
    {t w : ℤ} {X Y : ℝ}
    (hXsmall : 2*X < (p^2 : ℕ)) (hYsmall : 2*Y < (p^3 : ℕ))
    (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (ht : IsUnit (t : ZMod (p^3))) (hw : IsUnit (w : ZMod (p^3)))
    (F : Finset Coordinate)
    (hmem : ∀ z ∈ F, z ∈ middleLattice (p^3) t w)
    (hbox : ∀ z ∈ F, z ∈ literalBox X Y) :
    ((F.product F).filter fun e => sixReturnWord a₁ a₂
      (e.1.1 : ZMod (p^3)) (t : ZMod (p^3)) e.2.1 e.1.2 w e.2.2 =
        scalarReturn (-1)).card ≤ 2*F.card+1 := by
  classical
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let k : ZMod (p^3) := a₁*a₂*(t : ZMod (p^3))
  let S := (F.product F).filter fun e => sixReturnWord a₁ a₂
    (e.1.1 : ZMod (p^3)) (t : ZMod (p^3)) e.2.1 e.1.2 w e.2.2 =
      scalarReturn (-1)
  let good (z : Coordinate) : Prop := ¬ (p : ℤ)^2 ∣ ((1-k*z.1).val : ℤ)
  let L := S.filter fun e => good e.1
  let R := S.filter fun e => good e.2
  let D := S.filter fun e => ¬ good e.1 ∧ ¬ good e.2
  have hF (e : Endpoint) (he : e ∈ S) : e.1 ∈ F ∧ e.2 ∈ F :=
    Finset.mem_product.mp (Finset.mem_filter.mp he).1
  have heq (e : Endpoint) (he : e ∈ S) :
      (e.1.1 : ZMod (p^3)) + e.2.1 + w = k*e.1.1*e.2.1 := by
    have h := (sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂).mp
      (Finset.mem_filter.mp he).2
    simpa only [k, mul_assoc] using h.1
  have hpoint {z z' : Coordinate} (hz : z ∈ F) (hz' : z' ∈ F)
      (hfirst : z.1 = z'.1) : z = z' :=
    middle_box_first_projection_unique hYsmall hw
      (hmem z hz) (hmem z' hz') (hbox z hz) (hbox z' hz') hfirst
  have hleft : L.card ≤ F.card := by
    apply Finset.card_le_card_of_injOn (fun e : Endpoint => e.1)
    · intro e he
      exact (hF e (Finset.mem_filter.mp he).1).1
    · intro e he e' he' hfirst
      change e.1 = e'.1 at hfirst
      have hs := (Finset.mem_filter.mp he).1
      have hs' := (Finset.mem_filter.mp he').1
      apply Prod.ext hfirst
      apply hpoint (hF e hs).2 (hF e' hs').2
      apply shifted_factor_cancel hp hXsmall (Finset.mem_filter.mp he).2
        (hbox e.2 (hF e hs).2).1 (hbox e'.2 (hF e' hs').2).1
      have h₁ := heq e hs
      have h₂ := heq e' hs'
      rw [← hfirst] at h₂
      linear_combination h₁ - h₂
  have hright : R.card ≤ F.card := by
    apply Finset.card_le_card_of_injOn (fun e : Endpoint => e.2)
    · intro e he
      exact (hF e (Finset.mem_filter.mp he).1).2
    · intro e he e' he' hsecond
      change e.2 = e'.2 at hsecond
      have hs := (Finset.mem_filter.mp he).1
      have hs' := (Finset.mem_filter.mp he').1
      apply Prod.ext _ hsecond
      apply hpoint (hF e hs).1 (hF e' hs').1
      apply shifted_factor_cancel hp hXsmall (Finset.mem_filter.mp he).2
        (hbox e.1 (hF e hs).1).1 (hbox e'.1 (hF e' hs').1).1
      have h₁ := heq e hs
      have h₂ := heq e' hs'
      rw [← hsecond] at h₂
      linear_combination h₁ - h₂
  have hdeep : D.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro e he e' he'
    have hs := (Finset.mem_filter.mp he).1
    have hs' := (Finset.mem_filter.mp he').1
    have hds := (Finset.mem_filter.mp he).2
    have hds' := (Finset.mem_filter.mp he').2
    have hk : IsUnit k := (ha₁.mul ha₂).mul ht
    apply Prod.ext
    · apply hpoint (hF e hs).1 (hF e' hs').1
      exact deep_shifted_factor_unique hp hXsmall hk
        (hbox e.1 (hF e hs).1).1 (hbox e'.1 (hF e' hs').1).1
        (not_not.mp hds.1) (not_not.mp hds'.1)
    · apply hpoint (hF e hs).2 (hF e' hs').2
      exact deep_shifted_factor_unique hp hXsmall hk
        (hbox e.2 (hF e hs).2).1 (hbox e'.2 (hF e' hs').2).1
        (not_not.mp hds.2) (not_not.mp hds'.2)
  have hsub : S ⊆ (L ∪ R) ∪ D := by
    intro e he
    by_cases hl : good e.1
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨he, hl⟩))
    · by_cases hr : good e.2
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨he, hr⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, hl, hr⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hLR := Finset.card_union_le L R
  dsimp only [S] at hcard ⊢
  omega

end

end D5.S3.Arith.CharacterSums.Original
