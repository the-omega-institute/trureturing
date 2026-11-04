/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldInnerIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldInnerIterate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual infinite three-field numerator reconstructs the inner iterate channel. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorThreeFieldCommonSeries
import D5.S3.VertexAlgebra.Sectors.LatticeSectorChannelTransport
import D5.S3.VertexAlgebra.FormalSeries.SupportedThreeFieldCollision

/-!
Original canonical fields only, for all oscillator descendants and arbitrary
lattice data. The suppliers retain their Bakalov--Kac, Matsuo--Nagatomo and
Carnahan attributions. This is one genuine inner collision, not two collisions
or a four-object sewing/coherence theorem.
proof_shape: actual_three_field_inner_iterate_transport: content
admission_basis: escape-witness
escape_witness: the original Borcherds law is applied before the outer actual
canonical mode. Statewise truncation gives finite residue fibers; the signed
common-numerator cancellation identifies the fully cleared inner iterate with
the same three-variable numerator under a legal native substitution. The
common locality order is not enlarged to an intermediate-state cutoff.

The entire polynomial after z1=t+z2 is
 z0^a0 (z0-t-z2)^k (z0-z2)^k t^k (t+z2)^a1 z2^a2.
It is expanded finitely below; it is never divided out of an unrestricted
coefficient distribution. The P on the right is exactly the witness of the
closed actual_three_field_common_series theorem, not a separately chosen
bivariate numerator for an intermediate state.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorThreeFieldInnerIterate
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeSectorIntertwiner LatticeAllStateField
open LatticeSectorThreeFieldCommonSeries LatticeSectorChannelTransport
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open SupportedChannelSeries SupportedThreeFieldCollision
open StateFieldResidueReconstruction (integerBinomial)
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section

/-- The actual u(z0)((v(t)tstate)(z2))w coefficient. The second charge of the
outer canonical field is the true charge of the reconstructed inner iterate. -/
def innerIterate (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (x a b : ℤ) : Oscillator D :=
  canonical D α ((β + γ) + δ) u (-x - 1)
    (iterate D β γ δ v t w a b)

/-- Full Q and monomial clearing after the inner collision. The finite p,q
fibers are the expansions of the two cross factors; clearIterate then expands
 t^k(t+z2)^(a1+p) z2^(a2+q).
All arguments e are signed. -/
def clearedInnerIterate (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) : Oscillator D :=
  ∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1),
    (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
      ((((-1 : ℂ) ^ q) * (k.choose q : ℂ)) •
        clearIterate k (a 1 + p) (a 2 + q)
          (innerIterate D α β γ δ u v t w
            (e 0 - a 0 - 2 * k + p + q)) (e 1) (e 2))

private theorem outer_borcherds (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k A B p q : ℕ)
    (hA : ∀ n : ℤ, (A : ℤ) ≤ n → canonical D β δ v n w = 0)
    (hB : ∀ n : ℤ, (B : ℤ) ≤ n → canonical D γ δ t n w = 0)
    (x a b : ℤ) :
    clearIterate k (A + p) (B + q)
      (innerIterate D α β γ δ u v t w x) a b =
      ∑ i ∈ Finset.range (b.toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - a - 1) i) •
          canonical D α (β + (γ + δ)) u (-x - 1)
            (product D β γ δ v t w
              (a - A - p - k + i) (b - B - q - i)) := by
  classical
  let L : Oscillator D →ₗ[ℂ] Oscillator D :=
    canonical D α (β + (γ + δ)) u (-x - 1)
  have boundA : ∀ n : ℤ, ((A + p : ℕ) : ℤ) ≤ n →
      canonical D β δ v n w = 0 := by
    intro n hn
    exact hA n (by omega)
  have bor := iterate_borcherds D β γ δ v t w k (A + p) (B + q) boundA a b
  have mapped := congrArg L bor.2
  rw [map_finsum L bor.1] at mapped
  simp only [map_smul] at mapped
  have left : L (clearIterate k (A + p) (B + q)
      (iterate D β γ δ v t w) a b) =
      clearIterate k (A + p) (B + q)
        (innerIterate D α β γ δ u v t w x) a b := by
    simp only [clearIterate, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro h hh
    congr 1
    dsimp only [innerIterate, L]
    rw [add_assoc]
  rw [left] at mapped
  have normalized : clearIterate k (A + p) (B + q)
      (innerIterate D α β γ δ u v t w x) a b =
      ∑ᶠ i : ℕ,
        (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - a - 1) i) •
          L (product D β γ δ v t w
            (a - A - p - k + i) (b - B - q - i)) := by
    simpa only [Nat.cast_add, sub_add_eq_sub_sub] using mapped
  rw [normalized]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hout
  apply hi
  have hib : b < i := by
    simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hout
    omega
  have zeroInner : canonical D γ δ t (-((b - B - q - i)) - 1) w = 0 :=
    hB _ (by omega)
  change (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - a - 1) i) •
    L (canonical D β (γ + δ) v (-(a - A - p - k + i) - 1)
      (canonical D γ δ t (-(b - B - q - i) - 1) w)) = 0
  rw [zeroInner, map_zero, map_zero, smul_zero]

private theorem cross_lower (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k B : ℕ)
    (hB : ∀ n : ℤ, (B : ℤ) ≤ n → canonical D γ δ t n w = 0)
    (x y z : ℤ) (hz : z < -(B : ℤ)) :
    cross k (nestedCanonical D ![α, β, γ] ![u, v, t] δ w 0 1 2) x y z = 0 := by
  classical
  unfold cross
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  have zeroInner : canonical D γ δ t (-(z - q) - 1) w = 0 := hB _ (by omega)
  change (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
    ((((-1 : ℂ) ^ q) * (k.choose q : ℂ)) •
      canonical D α (β + (γ + δ)) u (-(x - 2 * k + p + q) - 1)
        (canonical D β (γ + δ) v (-(y - p) - 1)
          (canonical D γ δ t (-(z - q) - 1) w))) = 0
  rw [zeroInner, map_zero, map_zero, smul_zero, smul_zero]

private theorem finite_outer_reconstruction (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ)
    (hA : ∀ n : ℤ, (a 1 : ℤ) ≤ n → canonical D β δ v n w = 0)
    (hB : ∀ n : ℤ, (a 2 : ℤ) ≤ n → canonical D γ δ t n w = 0)
    (e : Exponent 3) :
    clearedInnerIterate D α β γ δ u v t w k a e =
      ∑ i ∈ Finset.range ((e 2).toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - e 1 - 1) i) •
          cross k (nestedCanonical D ![α, β, γ] ![u, v, t] δ w 0 1 2)
            (e 0 - a 0) (e 1 - a 1 - k + i) (e 2 - a 2 - i) := by
  classical
  have bor (p q : ℕ) (x y z : ℤ) :=
    outer_borcherds D α β γ δ u v t w k (a 1) (a 2) p q hA hB x y z
  unfold clearedInnerIterate
  simp_rw [bor, Finset.smul_sum]
  let term (p q i : ℕ) : Oscillator D :=
    (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
      ((((-1 : ℂ) ^ q) * (k.choose q : ℂ)) •
        ((((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - e 1 - 1) i) •
          canonical D α (β + (γ + δ)) u
            (-(e 0 - a 0 - 2 * k + p + q) - 1)
            (product D β γ δ v t w
              (e 1 - a 1 - p - k + i) (e 2 - a 2 - q - i))))
  change (∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1),
    ∑ i ∈ Finset.range ((e 2).toNat + 1), term p q i) = _
  calc
    _ = ∑ p ∈ Finset.range (k + 1), ∑ i ∈ Finset.range ((e 2).toNat + 1),
          ∑ q ∈ Finset.range (k + 1), term p q i := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range ((e 2).toNat + 1), ∑ p ∈ Finset.range (k + 1),
          ∑ q ∈ Finset.range (k + 1), term p q i := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold cross
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      dsimp only [term]
      have base : canonical D α (β + (γ + δ)) u
          (-(e 0 - a 0 - 2 * k + p + q) - 1)
          (product D β γ δ v t w
            (e 1 - a 1 - p - k + i) (e 2 - a 2 - q - i)) =
          nestedCanonical D ![α, β, γ] ![u, v, t] δ w 0 1 2
            ![e 0 - a 0 - 2 * k + p + q,
              e 1 - a 1 - k + i - p, e 2 - a 2 - i - q] := by
        change canonical D α (β + (γ + δ)) u
          (-(e 0 - a 0 - 2 * k + p + q) - 1)
          (product D β γ δ v t w
            (e 1 - a 1 - p - k + i) (e 2 - a 2 - q - i)) =
          canonical D α (β + (γ + δ)) u
            (-(e 0 - a 0 - 2 * k + p + q) - 1)
            (product D β γ δ v t w
              (e 1 - a 1 - k + i - p) (e 2 - a 2 - i - q))
        congr 1
        congr 1 <;> omega
      rw [base]
      simp only [smul_smul]
      congr 1
      ring

/-- SAME actual three-field common numerator, now identified with a genuine
inner canonical iterate after the legal partial triangular collision.

The existence of P, all support bounds and the product law are derived from
the closed common-series theorem. The inner iterate identity is derived from
the original all-integer Borcherds/residue law. Neither desired identity is a
premise. k is still chosen before δ,w. All signed exponents, zero series,
repeated charges, arbitrary descendants, rank zero and indefinite data remain
in scope. No Gram inverse, energy projection, positivity or sewing axiom occurs.
-/
theorem actual_three_field_inner_iterate_transport
    (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) :
    let c : Fin 3 → Charge D := ![α, β, γ]
    let s : Fin 3 → Oscillator D := ![u, v, t]
    ∃ k : ℕ,
      (∀ i j : Fin 3, i < j →
        (deltaEnd ^ k) (commutator (labelledFields D c s i) (labelledFields D c s j)) = 0) ∧
      ∀ (δ : Charge D) (w : Sector D δ), ∃ a : Fin 3 → ℕ,
        ∃ P : MvPowerSeries (Fin 3) (Oscillator D),
        (∀ (i : Fin 3) (n : ℤ), (a i : ℤ) ≤ n →
          canonical D (c i) δ (s i) n w = 0) ∧
        (∀ e : Exponent 3,
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 0 1 2)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 0 2 1)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 1 0 2)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 1 2 0)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 2 0 1)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 2 1 0)
            (fun i => e i - a i) = signedExtend P e) ∧
        ∀ e : Exponent 3,
          clearedInnerIterate D α β γ δ u v t w k a e =
            signedExtend (innerCollision P) e := by
  classical
  dsimp only
  obtain ⟨k, locality, rest⟩ := actual_three_field_common_series D α β γ u v t
  refine ⟨k, locality, ?_⟩
  intro δ w
  obtain ⟨a, P, truncation, six⟩ := rest δ w
  have common (e : Exponent 3) := (six e).1
  refine ⟨a, P, truncation, six, ?_⟩
  intro e
  let F : Distribution 3 (Oscillator D) :=
    nestedCanonical D ![α, β, γ] ![u, v, t] δ w 0 1 2
  let G : ℤ → ℤ → Oscillator D := cross k F (e 0 - a 0)
  have lower : ∀ x y : ℤ, y < -(a 2 : ℤ) → G x y = 0 := by
    intro x y hy
    exact cross_lower D α β γ δ u v t w k (a 2)
      (truncation 2) _ x y hy
  have commonSlice (x y : ℤ) :
      clear k G (x - a 1) (y - a 2) = extend (slice P (e 0)) x y := by
    have h := common ![e 0, x, y]
    rw [clearing_three] at h
    change clear k G (x - a 1) (y - a 2) = signedExtend P ![e 0, x, y] at h
    exact h.trans (slice_extend P (e 0) x y).symm
  have signed := signed_cleared_collision G k (a 1) (a 2) lower
    (slice P (e 0)) commonSlice (e 1) (e 2)
  have finiteSum :
      (∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - e 1 - 1) i) •
        G (e 1 - a 1 - k + i) (e 2 - a 2 - i)) =
      ∑ i ∈ Finset.range ((e 2).toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - e 1 - 1) i) •
          G (e 1 - a 1 - k + i) (e 2 - a 2 - i) := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hout
    apply hi
    have hib : e 2 < i := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hout
      omega
    change (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - e 1 - 1) i) •
      G (e 1 - a 1 - k + i) (e 2 - a 2 - i) = 0
    rw [lower _ _ (by omega), smul_zero]
  calc
    clearedInnerIterate D α β γ δ u v t w k a e =
        ∑ i ∈ Finset.range ((e 2).toNat + 1),
          (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - e 1 - 1) i) •
            G (e 1 - a 1 - k + i) (e 2 - a 2 - i) :=
      finite_outer_reconstruction D α β γ δ u v t w k a
        (truncation 1) (truncation 2) e
    _ = extend (collision (slice P (e 0))) (e 1) (e 2) :=
      finiteSum.symm.trans signed.2
    _ = signedExtend (innerCollision P) ![e 0, e 1, e 2] :=
      (innerCollision_signed P (e 0) (e 1) (e 2)).symm
    _ = signedExtend (innerCollision P) e := by
      congr 1
      funext i
      fin_cases i <;> rfl

#print axioms actual_three_field_inner_iterate_transport

end
end D5.S3.VertexAlgebra.LatticeSectorThreeFieldInnerIterate
