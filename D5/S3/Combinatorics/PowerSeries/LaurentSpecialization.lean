/- GID: D5/S3/Combinatorics/PowerSeries/LaurentSpecialization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PowerSeries/LaurentSpecialization
   mirror-E: none(waiver:positive-weight-laurent-specialization)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Evaluation]
   utility: none
   digest: A support-controlled specialization of Laurent coefficient series. -/

import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.Algebra.Polynomial.Laurent

/-! Shift each Laurent row by its power-series degree before evaluating.
This makes the substitution legitimate on the cone k ≥ -n. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.PowerSeries.LaurentSpecialization

open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

private local instance : UniformSpace ℚ := ⊥
private local instance : DiscreteUniformity ℚ := ⟨rfl⟩
private local instance : UniformSpace (Polynomial ℚ) := ⊥
private local instance : DiscreteUniformity (Polynomial ℚ) := ⟨rfl⟩
private local instance : UniformSpace (LaurentPolynomial ℚ) := ⊥
private local instance : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩

noncomputable def lift (p : PowerSeries (LaurentPolynomial ℚ)) :
    PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk fun n => LaurentPolynomial.trunc
    ((LaurentPolynomial.T 1) ^ n * PowerSeries.coeff n p)

/-- The shifted rows are genuine polynomials; this is a support condition,
not a premise asserting the desired Jacobi identity. -/
def Admissible (p : PowerSeries (LaurentPolynomial ℚ)) : Prop :=
  ∃ q : PowerSeries (Polynomial ℚ),
    PowerSeries.map Polynomial.toLaurent q = PowerSeries.rescale (LaurentPolynomial.T 1) p

theorem lift_of_map {p : PowerSeries (LaurentPolynomial ℚ)}
    {q : PowerSeries (Polynomial ℚ)}
    (h : PowerSeries.map Polynomial.toLaurent q =
      PowerSeries.rescale (LaurentPolynomial.T 1) p) : lift p = q := by
  ext n
  have hn := congrArg (PowerSeries.coeff n) h
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_rescale] at hn
  simp only [lift, PowerSeries.coeff_mk, ← hn, Polynomial.trunc_toLaurent]

theorem map_lift {p : PowerSeries (LaurentPolynomial ℚ)} (hp : Admissible p) :
    PowerSeries.map Polynomial.toLaurent (lift p) =
      PowerSeries.rescale (LaurentPolynomial.T 1) p := by
  obtain ⟨q, hq⟩ := hp
  rw [lift_of_map hq]
  exact hq

theorem admissible_one : Admissible 1 := ⟨1, by simp⟩

theorem admissible_mul {p q : PowerSeries (LaurentPolynomial ℚ)}
    (hp : Admissible p) (hq : Admissible q) : Admissible (p * q) := by
  refine ⟨lift p * lift q, ?_⟩
  rw [map_mul, map_lift hp, map_lift hq, map_mul]

theorem lift_mul {p q : PowerSeries (LaurentPolynomial ℚ)}
    (hp : Admissible p) (hq : Admissible q) : lift (p * q) = lift p * lift q := by
  apply lift_of_map
  rw [map_mul, map_lift hp, map_lift hq, map_mul]

theorem lift_one : lift 1 = 1 := lift_of_map (by simp)

noncomputable def liftAdd :
    PowerSeries (LaurentPolynomial ℚ) →+ PowerSeries (Polynomial ℚ) where
  toFun := lift
  map_zero' := by ext n; simp [lift]
  map_add' := by intro p q; ext n; simp [lift, mul_add]

theorem continuous_lift : Continuous lift := by
  rw [continuous_iff_continuousAt]
  intro p
  apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).2
  intro n
  simp only [lift, PowerSeries.coeff_mk]
  have hc : Continuous (fun a : LaurentPolynomial ℚ =>
      LaurentPolynomial.trunc ((LaurentPolynomial.T 1) ^ n * a)) :=
    continuous_of_discreteTopology
  exact (hc.comp
    (PowerSeries.WithPiTopology.continuous_coeff (LaurentPolynomial ℚ) n)).continuousAt

private theorem hasEval_X_pow (a : ℕ) :
    PowerSeries.HasEval ((PowerSeries.X : PowerSeries ℚ) ^ (a + 1)) := by
  rw [pow_succ]
  exact PowerSeries.HasEval.X.mul_left _

noncomputable def diagonal (a r : ℕ) :
    PowerSeries (Polynomial ℚ) →+* PowerSeries ℚ :=
  PowerSeries.eval₂Hom
    (φ := Polynomial.eval₂RingHom PowerSeries.C (PowerSeries.X ^ r))
    continuous_of_discreteTopology (hasEval_X_pow a)

noncomputable def specialize (a r : ℕ)
    (p : PowerSeries (LaurentPolynomial ℚ)) : PowerSeries ℚ := diagonal a r (lift p)

noncomputable def specializeAdd (a r : ℕ) :
    PowerSeries (LaurentPolynomial ℚ) →+ PowerSeries ℚ :=
  (diagonal a r).toAddMonoidHom.comp liftAdd

theorem specialize_mul (a r : ℕ) {p q : PowerSeries (LaurentPolynomial ℚ)}
    (hp : Admissible p) (hq : Admissible q) :
    specialize a r (p * q) = specialize a r p * specialize a r q := by
  simp only [specialize, lift_mul hp hq, map_mul]

theorem specialize_one (a r : ℕ) : specialize a r 1 = 1 := by
  simp only [specialize, lift_one, map_one]

theorem continuous_specialize (a r : ℕ) : Continuous (specialize a r) := by
  have hd : Continuous (diagonal a r) := by
    change Continuous (fun f => diagonal a r f)
    simp only [diagonal, PowerSeries.coe_eval₂Hom]
    exact PowerSeries.continuous_eval₂ continuous_of_discreteTopology (hasEval_X_pow a)
  exact hd.comp continuous_lift

theorem lift_monomial (n : ℕ) (k : ℤ) (c : ℚ) (hnk : 0 ≤ (n : ℤ) + k) :
    lift (PowerSeries.C (LaurentPolynomial.C c * LaurentPolynomial.T k) *
      PowerSeries.X ^ n) =
    PowerSeries.C (Polynomial.monomial ((n : ℤ) + k).toNat c) * PowerSeries.X ^ n := by
  ext m
  simp only [lift, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  by_cases hmn : m = n
  · subst m
    simp only [ite_true, mul_one, LaurentPolynomial.T_pow, mul_one]
    rw [show LaurentPolynomial.T (n : ℤ) * (LaurentPolynomial.C c * LaurentPolynomial.T k) =
        LaurentPolynomial.C c * LaurentPolynomial.T ((n : ℤ) + k) by
      rw [LaurentPolynomial.T_add]; ring,
      LaurentPolynomial.trunc_C_mul_T, if_pos hnk]
  · simp [hmn]

theorem admissible_monomial (n : ℕ) (k : ℤ) (c : ℚ) (hnk : 0 ≤ (n : ℤ) + k) :
    Admissible (PowerSeries.C (LaurentPolynomial.C c * LaurentPolynomial.T k) *
      PowerSeries.X ^ n) := by
  refine ⟨PowerSeries.C (Polynomial.monomial ((n : ℤ) + k).toNat c) *
    PowerSeries.X ^ n, ?_⟩
  ext m
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_rescale,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  by_cases hmn : m = n
  · subst m
    simp only [ite_true, mul_one, Polynomial.toLaurent_C_mul_T,
      Int.toNat_of_nonneg hnk, LaurentPolynomial.T_add,
      LaurentPolynomial.T_pow, mul_one]
    ring
  · simp [hmn]

theorem specialize_monomial (a r n : ℕ) (k : ℤ) (c : ℚ)
    (hnk : 0 ≤ (n : ℤ) + k) :
    specialize a r (PowerSeries.C (LaurentPolynomial.C c * LaurentPolynomial.T k) *
      PowerSeries.X ^ n) =
    PowerSeries.C c * PowerSeries.X ^ ((a + 1) * n + r * ((n : ℤ) + k).toNat) := by
  rw [specialize, lift_monomial n k c hnk]
  simp only [map_mul, map_pow, diagonal, PowerSeries.coe_eval₂Hom,
    PowerSeries.eval₂_C, PowerSeries.eval₂_X, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_monomial, ← pow_mul, pow_add]
  ring

theorem admissible_sub {p q : PowerSeries (LaurentPolynomial ℚ)}
    (hp : Admissible p) (hq : Admissible q) : Admissible (p - q) := by
  refine ⟨lift p - lift q, ?_⟩
  rw [map_sub, map_lift hp, map_lift hq, map_sub]

theorem admissible_prod {ι : Type*} (s : Finset ι)
    (p : ι → PowerSeries (LaurentPolynomial ℚ))
    (hp : ∀ i ∈ s, Admissible (p i)) : Admissible (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using admissible_one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact admissible_mul (hp i (by simp)) (ih (by intro j hj; exact hp j (by simp [hj])))

theorem specialize_prod {ι : Type*} (a r : ℕ) (s : Finset ι)
    (p : ι → PowerSeries (LaurentPolynomial ℚ))
    (hp : ∀ i ∈ s, Admissible (p i)) :
    specialize a r (∏ i ∈ s, p i) = ∏ i ∈ s, specialize a r (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [specialize_one]
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, Admissible (p j) := by intro j hj; exact hp j (by simp [hj])
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      specialize_mul a r (hp i (by simp)) (admissible_prod s p hs), ih hs]

theorem specialize_factor (a r n : ℕ) (k : ℤ) (hnk : 0 ≤ (n : ℤ) + k) :
    specialize a r (1 - PowerSeries.C (LaurentPolynomial.T k) * PowerSeries.X ^ n) =
      1 - PowerSeries.X ^ ((a + 1) * n + r * ((n : ℤ) + k).toNat) := by
  have h := (specializeAdd a r).map_sub 1
    (PowerSeries.C (LaurentPolynomial.T k) * PowerSeries.X ^ n)
  change specialize a r _ = specialize a r 1 - specialize a r _ at h
  rw [h, specialize_one]
  have hm := specialize_monomial a r n k 1 hnk
  simpa only [map_one, one_mul] using congrArg (fun v : PowerSeries ℚ => 1 - v) hm

theorem admissible_factor (n : ℕ) (k : ℤ) (hnk : 0 ≤ (n : ℤ) + k) :
    Admissible (1 - PowerSeries.C (LaurentPolynomial.T k) * PowerSeries.X ^ n) := by
  apply admissible_sub admissible_one
  simpa only [map_one, one_mul] using admissible_monomial n k 1 hnk

end D5.S3.Combinatorics.PowerSeries.LaurentSpecialization
