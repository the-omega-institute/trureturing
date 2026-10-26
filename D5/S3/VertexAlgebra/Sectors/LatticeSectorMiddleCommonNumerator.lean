/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorMiddleCommonNumerator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorMiddleCommonNumerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual fully cleared middle channel has the original common numerator. -/
import D5.S3.VertexAlgebra.Sectors.LatticeSectorSecondCollisionSlice
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldPolynomialCovariance
import D5.S3.VertexAlgebra.FormalSeries.SupportedMiddleCollision

/-! The original inner numerator determines the fully cleared middle channel.
Finite polynomial recoupling and the actual Borcherds residue identify every
signed coefficient with the same legally substituted infinite series.
The imported suppliers retain Bakalov--Kac, Matsuo--Nagatomo and Carnahan
attribution. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorMiddleCommonNumerator
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticeSectorThreeFieldCommonSeries LatticeSectorThreeFieldInnerIterate
open LatticeSectorSecondCollisionSlice
open SupportedChannelSeries SupportedThreeFieldCollision SupportedCollisionSlice
open ThreeFieldPolynomialCovariance SupportedMiddleCollision
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open StateFieldResidueReconstruction (integerBinomial)
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section

/-- The y^b slice of the FULL old inner multiplier, regrouped as a finite sum
of actual u(z0)((v_r t)(z))w products cleared by (z0-z)^(2k-p). -/
def crossProductSlice (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (b x z : ℤ) : Oscillator D :=
  ∑ p ∈ Finset.range (k + 1), ∑ h ∈ Finset.range (a 1 + 1),
    (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
      (((a 1).choose h : ℂ) •
        clear (2 * k - p)
          (fun s q => product D α (β + γ) δ u
            (canonical D β γ v (-(b - k - p - h) - 1) t) w
            (s - a 0) (q - (a 2 + a 1 - h : ℕ))) x z)

private theorem actual_inner_recoupling (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (b x z : ℤ) :
    clearedInnerIterate D α β γ δ u v t w k a ![x, b, z] =
      crossProductSlice D α β γ δ u v t w k a b x z := by
  let F : Distribution 3 (Oscillator D) := fun e =>
    innerIterate D α β γ δ u v t w (e 0) (e 1) (e 2)
  have recouple := finite_inner_recoupling F k a x b z
  simpa only [F, clearedInnerIterate, clearIterate, crossProductSlice,
    innerIterate, iterate, product, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Nat.cast_add] using recouple

/-- Finite covariance of the ACTUAL Jacobi residue. B bounds only the exact
fixed-b mode interval. The scalar convolution recovers 2k-p-s-1; the right side
is literally the closed sliceResidueTerm, rather than a new product premise. -/
private theorem actual_residue_covariance (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (b : ℤ) (B : ℕ)
    (hB : ∀ r : ℤ, r ∈ modeFiber k (a 1) b → ∀ n : ℤ, (B : ℤ) ≤ n →
      canonical D (β + γ) δ (canonical D β γ v r t) n w = 0)
    (s z : ℤ) :
    (∑ i ∈ Finset.range ((z + B).toNat + 1),
      (((-1 : ℂ) ^ i) * integerBinomial (-s - 1) i) •
        clearedInnerIterate D α β γ δ u v t w k a ![s + i, b, z - i]) =
    ∑ i ∈ Finset.range ((z + B).toNat + 1),
      ∑ p ∈ Finset.range (k + 1), ∑ h ∈ Finset.range (a 1 + 1),
        sliceResidueTerm D α β γ δ u v t w k a b s z p h i := by
  classical
  let G (p h : ℕ) (x y : ℤ) : Oscillator D :=
    product D α (β + γ) δ u
      (canonical D β γ v (-(b - k - p - h) - 1) t) w
      (x - a 0) (y - (a 2 + a 1 - h : ℕ))
  have step (p h : ℕ) (hp : p ∈ Finset.range (k + 1))
      (hh : h ∈ Finset.range (a 1 + 1)) :
      (∑ i ∈ Finset.range ((z + B).toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial (-s - 1) i) •
          clear (2 * k - p) (G p h) (s + i) (z - i)) =
      ∑ i ∈ Finset.range ((z + B).toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial (((2 * k - p : ℕ) : ℤ) - s - 1) i) •
          product D α (β + γ) δ u
            (canonical D β γ v (-(b - k - p - h) - 1) t) w
            (s - a 0 - (2 * k - p : ℕ) + i)
            (z - (a 2 + a 1 - h : ℕ) - i) := by
    have hp' : p ≤ k := by simpa using Finset.mem_range.mp hp
    have hh' : h ≤ a 1 := by simpa using Finset.mem_range.mp hh
    let r : ℤ := -(b - k - p - h) - 1
    have member : r ∈ modeFiber k (a 1) b :=
      (mem_modeFiber_iff k (a 1) b r).2 ⟨p, hp', h, hh', by dsimp only [r]; omega⟩
    have lower : ∀ x y : ℤ, y < -(B : ℤ) → G p h x y = 0 := by
      intro x y hy
      dsimp only [G, product]
      rw [hB r member _ (by omega), map_zero]
    have hc := signed_transform_clear (G p h) (2 * k - p) B lower (-s - 1) s z
    refine hc.trans ?_
    apply Finset.sum_congr rfl
    intro i hi
    rw [show -s - 1 + (2 * k - p : ℕ) = ((2 * k - p : ℕ) : ℤ) - s - 1 by omega]
    apply congrArg (fun v : Oscillator D =>
      (((-1 : ℂ) ^ i) * integerBinomial (((2 * k - p : ℕ) : ℤ) - s - 1) i) • v)
    dsimp only [G]
    congr 1 <;> omega
  simp_rw [actual_inner_recoupling, crossProductSlice, Finset.smul_sum]
  change (∑ i ∈ Finset.range ((z + B).toNat + 1),
    ∑ p ∈ Finset.range (k + 1), ∑ h ∈ Finset.range (a 1 + 1),
      (((-1 : ℂ) ^ i) * integerBinomial (-s - 1) i) •
        ((((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
          (((a 1).choose h : ℂ) • clear (2 * k - p) (G p h) (s + i) (z - i)))) = _
  rw [Finset.sum_comm]
  calc
    _ = ∑ p ∈ Finset.range (k + 1), ∑ h ∈ Finset.range (a 1 + 1),
        (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
          (((a 1).choose h : ℂ) •
            (∑ i ∈ Finset.range ((z + B).toNat + 1),
              (((-1 : ℂ) ^ i) * integerBinomial (-s - 1) i) •
                clear (2 * k - p) (G p h) (s + i) (z - i))) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      simp only [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [smul_smul]
      congr 1
      ring
    _ = ∑ p ∈ Finset.range (k + 1), ∑ h ∈ Finset.range (a 1 + 1),
        ∑ i ∈ Finset.range ((z + B).toNat + 1),
          sliceResidueTerm D α β γ δ u v t w k a b s z p h i := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro h hh
      rw [step p h hp hh]
      simp only [Finset.smul_sum, sliceResidueTerm]
    _ = ∑ p ∈ Finset.range (k + 1), ∑ i ∈ Finset.range ((z + B).toNat + 1),
        ∑ h ∈ Finset.range (a 1 + 1),
          sliceResidueTerm D α β γ δ u v t w k a b s z p h i := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

/-- The original common numerator gives the fully cleared middle channel
at every signed exponent, preserving k, a, P and all six product laws. -/
theorem actual_three_field_middle_common_numerator
    (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) :
    let c : Fin 3 → Charge D := ![α, β, γ]
    let states : Fin 3 → Oscillator D := ![u, v, t]
    ∃ k : ℕ,
      (∀ i j : Fin 3, i < j →
        (deltaEnd ^ k) (commutator (labelledFields D c states i)
          (labelledFields D c states j)) = 0) ∧
      ∀ (δ : Charge D) (w : Sector D δ), ∃ a : Fin 3 → ℕ,
        ∃ P : MvPowerSeries (Fin 3) (Oscillator D),
        (∀ (i : Fin 3) (n : ℤ), (a i : ℤ) ≤ n →
          canonical D (c i) δ (states i) n w = 0) ∧
        (∀ e : Exponent 3,
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 0 1 2)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 0 2 1)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 1 0 2)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 1 2 0)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 2 0 1)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 2 1 0)
            (fun i => e i - a i) = signedExtend P e) ∧
        ∀ b s z : ℤ, clearedMiddleSlice D α β γ δ u v t w k a b s z =
          signedExtend (MvPowerSeries.subst (middleArguments (Oscillator D)) P) ![s, b, z] := by
  classical
  dsimp only
  obtain ⟨k, locality, rest⟩ := actual_three_field_inner_iterate_transport D α β γ u v t
  refine ⟨k, locality, ?_⟩
  intro δ w
  obtain ⟨a, P, truncation, six, inner⟩ := rest δ w
  refine ⟨a, P, truncation, six, ?_⟩
  intro b s z
  obtain ⟨B, hB, residue⟩ := actual_collision_slice_finite_residue
    D α β γ δ u v t w k a (truncation 0) b
  let F : ℤ → ℤ → Oscillator D := fun x y =>
    clearedInnerIterate D α β γ δ u v t w k a ![x, b, y]
  let S : MvPowerSeries (Fin 2) (Oscillator D) := middleNativeSlice (innerCollision P) b
  have common (x y : ℤ) : clear 0 F (x - (0 : ℤ)) (y - (0 : ℤ)) = extend S x y := by
    have zeroClear (G : ℤ → ℤ → Oscillator D) (s z : ℤ) : clear 0 G s z = G s z := by
      simp [clear]
    rw [sub_zero, sub_zero, zeroClear]
    exact (inner ![x, b, y]).trans
      (middleNativeSlice_extend (innerCollision P) b x y).symm
  have lower : ∀ x y : ℤ, y < -(0 : ℤ) → F x y = 0 := by
    intro x y hy
    dsimp only [F]
    rw [inner]
    have hn : ¬ ∀ i : Fin 3, 0 ≤ (![x, b, y] : Fin 3 → ℤ) i := by
      intro hn
      have := hn 2
      change 0 ≤ y at this
      omega
    simp only [signedExtend, if_neg hn]
  have signed := signed_cleared_collision F 0 0 0 lower S common s z
  have finiteSum :
      (∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial (-s - 1) i) • F (s + i) (z - i)) =
      ∑ i ∈ Finset.range ((z + B).toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial (-s - 1) i) • F (s + i) (z - i) := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hout
    apply hi
    have hib : z + B < i := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hout
      omega
    change _ • F (s + (i : ℤ)) (z - (i : ℤ)) = 0
    rw [lower _ _ (by omega), smul_zero]
  have covariance := actual_residue_covariance D α β γ δ u v t w k a b B hB s z
  calc
    clearedMiddleSlice D α β γ δ u v t w k a b s z =
        ∑ i ∈ Finset.range ((z + B).toNat + 1),
          (((-1 : ℂ) ^ i) * integerBinomial (-s - 1) i) • F (s + i) (z - i) :=
      (residue s z).trans covariance.symm
    _ = ∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial (-s - 1) i) •
          F (s + i) (z - i) := finiteSum.symm
    _ = extend (collision S) s z := by
      simpa only [Nat.cast_zero, zero_sub, sub_zero] using signed.2
    _ = signedExtend (MvPowerSeries.subst (outerArguments (Oscillator D))
          (innerCollision P)) ![s, b, z] :=
      (outerCollision_signed (innerCollision P) b s z).symm
    _ = signedExtend (MvPowerSeries.subst (middleArguments (Oscillator D)) P) ![s, b, z] := by
      rw [outer_inner_substitution]

#print axioms actual_three_field_middle_common_numerator

end
end D5.S3.VertexAlgebra.LatticeSectorMiddleCommonNumerator
