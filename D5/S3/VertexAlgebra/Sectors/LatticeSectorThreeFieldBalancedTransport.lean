/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldBalancedTransport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldBalancedTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual balanced transport with the original three-field numerator and witnesses. -/
import D5.S3.VertexAlgebra.Sectors.LatticeSectorRawInnerCoefficients
import D5.S3.VertexAlgebra.Sectors.LatticeSectorBalancedBorcherds
import Batteries.Tactic.OpenPrivate

/-! All suppliers retain their Bakalov--Kac, Matsuo--Nagatomo and Carnahan
attributions and canonical normalization. The full all-integer Jacobi second
term is killed by coupled u/t locality and the original u-on-w cutoff.
proof_shape: actual_three_field_balanced_transport: content
admission_basis: escape-witness
escape_witness: lawful first-pair collision with the original cross factors,
including signed negative targets, produces the actual balanced tree.
Only the constructed shared witnesses of the raw-inner and balanced charts
are asserted; no five-tree common numerator, pentagon or coherence is claimed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorThreeFieldBalancedTransport
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticeSectorThreeFieldCommonSeries LatticeSectorThreeFieldInnerIterate
open LatticeSectorRawInnerCoefficients LatticeSectorBalancedBorcherds
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open SupportedChannelSeries SupportedThreeFieldCollision SupportedBalancedCollision
open ThreeFieldInnerPolynomial ThreeFieldInnerInverseCoefficients ThreeFieldInnerLaurentFiber
open FieldNormalProductLocality (deltaEnd commutator)
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section
open private balanced_clearing_three balancedSlice_extend balancedCollision_signed from
  D5.S3.VertexAlgebra.FormalSeries.SupportedBalancedCollision
open private weight fixed_q_borcherds from
  D5.S3.VertexAlgebra.Sectors.LatticeSectorBalancedBorcherds
open private cleared_local clear_reverse_below from
  D5.S3.VertexAlgebra.Sectors.LatticeSectorChannelTransport

private theorem actual_balanced_support (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ) :
    ∃ S Z : ℕ,
      (∀ s x z : ℤ, s < -(S : ℤ) → balanced D α β γ δ u v t w s x z = 0) ∧
      (∀ s x z : ℤ, z < -(Z : ℤ) → balanced D α β γ δ u v t w s x z = 0) := by
  obtain ⟨S, hs⟩ := canonical_truncation D α β u v
  obtain ⟨Z, hz⟩ := canonical_truncation D γ δ t w
  refine ⟨S.toNat, Z.toNat, ?_, ?_⟩
  · intro s x z h
    unfold balanced
    rw [hs (-s - 1) (by omega)]
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply]
  · intro s x z h
    unfold balanced
    rw [hz (-z - 1) (by omega), map_zero]

private theorem cross_lower (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k B : ℕ)
    (locality : (deltaEnd ^ k) (commutator
      (Y D (inclusion D β v)) (Y D (inclusion D γ t))) = 0)
    (cutoff : ∀ n : ℤ, (B : ℤ) ≤ n → canonical D β δ v n w = 0)
    (y x z : ℤ) (hx : x < -(B : ℤ)) :
    balancedCross k (nestedCanonical D ![α, β, γ] ![u, v, t] δ w 0 1 2) y x z = 0 := by
  classical
  have loc : FieldNormalProductLocality.delta^[k] (FieldNormalProductLocality.commutator
      (Y D (inclusion D β v)) (Y D (inclusion D γ t))) = 0 := by
    have h := locality
    rw [Module.End.pow_apply] at h
    exact h
  unfold balancedCross
  apply Finset.sum_eq_zero
  intro j hj
  let L : Oscillator D →ₗ[ℂ] Oscillator D :=
    canonical D α (β + (γ + δ)) u (-(y - k + j) - 1)
  have cleared := cleared_local D β γ v t k loc δ w x (z - j)
  have zero := clear_reverse_below D β γ δ v t w k B cutoff x (z - j) hx
  have h := congrArg L (cleared.trans zero)
  simp only [clear, map_sum, map_smul, map_zero] at h
  change (∑ l ∈ Finset.range (k + 1), weight k j • (weight k l •
    L (product D β γ δ v t w (x - k + l) (z - j - l)))) = 0
  simpa only [weight, Finset.smul_sum, smul_zero] using
    congrArg (fun q : Oscillator D => weight k j • q) h

private theorem triple_first_finite (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (y x z r : ℤ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      (((-1 : ℂ) ^ i) * integerBinomial r i) •
        nestedCanonical D ![α, β, γ] ![u, v, t] δ w 0 1 2 ![y + i, x - i, z]) := by
  obtain ⟨T, ht⟩ := canonical_truncation D β (γ + δ) v
    (canonical D γ δ t (-z - 1) w)
  apply BddAbove.finite
  apply bddAbove_def.mpr
  refine ⟨(T + x + 1).toNat, ?_⟩
  intro i hi
  by_contra h
  apply hi
  change (((-1 : ℂ) ^ i) * integerBinomial r i) •
    canonical D α (β + (γ + δ)) u (-(y + i) - 1)
      (canonical D β (γ + δ) v (-(x - i) - 1)
        (canonical D γ δ t (-z - 1) w)) = 0
  rw [ht _ (by omega), map_zero, smul_zero]

private theorem finite_first (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ)
    (locality : (deltaEnd ^ k) (commutator
      (Y D (inclusion D α u)) (Y D (inclusion D γ t))) = 0)
    (cutoff : ∀ n : ℤ, (a 0 : ℤ) ≤ n → canonical D α δ u n w = 0)
    (e : Exponent 3) :
    clearedBalanced D α β γ δ u v t w k a e =
      ∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - e 0 - 1) i) •
        balancedCross k (nestedCanonical D ![α, β, γ] ![u, v, t] δ w 0 1 2)
          (e 0 - a 0 - k + i) (e 1 - a 1 - i) (e 2 - a 2) := by
  classical
  let r : ℤ := (k : ℤ) - e 0 - 1
  let term (j l i : ℕ) :=
    (((-1 : ℂ) ^ i) * integerBinomial r i) •
      nestedCanonical D ![α, β, γ] ![u, v, t] δ w 0 1 2
        ![e 0 - a 0 - 2 * k + j + i, e 1 - a 1 - k + l - i,
          e 2 - a 2 - j - l]
  have finite (j l : ℕ) : Function.HasFiniteSupport (term j l) := by
    simpa only [term] using triple_first_finite D α β γ δ u v t w
      (e 0 - a 0 - 2 * k + j) (e 1 - a 1 - k + l) (e 2 - a 2 - j - l) r
  have finiteJ (l : ℕ) : Function.HasFiniteSupport
      (fun i : ℕ => ∑ j ∈ Finset.range (k + 1), weight k j • term j l i) :=
    Function.HasFiniteSupport.sum
      (fun j : ℕ => (finite j l).smul_right (fun _ => weight k j)) _
  unfold clearedBalanced
  rw [Finset.sum_comm]
  calc
    _ = ∑ l ∈ Finset.range (k + 1), weight k l •
        (∑ j ∈ Finset.range (k + 1), weight k j •
          clearIterate k (a 0 + k - j) (a 1 + k - l)
            (fun s x => balanced D α β γ δ u v t w s x (e 2 - a 2 - j - l))
            (e 0) (e 1)) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact smul_comm _ _ _
    _ = ∑ l ∈ Finset.range (k + 1), weight k l •
        (∑ᶠ i : ℕ, ∑ j ∈ Finset.range (k + 1), weight k j • term j l i) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [fixed_q_borcherds D α β γ δ u v t w k (a 0) (a 1) (a 2) l
        (by simpa using Finset.mem_range.mp hl) locality cutoff]
      congr 1
      apply finsum_congr
      intro i
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact smul_comm _ _ _
    _ = ∑ᶠ i : ℕ, ∑ l ∈ Finset.range (k + 1), weight k l •
        (∑ j ∈ Finset.range (k + 1), weight k j • term j l i) := by
      simp_rw [smul_finsum' _ (finiteJ _)]
      exact sum_finsum_comm _ _ (fun l _ => (finiteJ l).smul_right (fun _ => weight k l))
    _ = _ := by
      apply finsum_congr
      intro i
      simp only [balancedCross, Finset.smul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      dsimp only [term, r]
      have idx : (![e 0 - a 0 - 2 * k + j + i,
          e 1 - a 1 - k + l - i, e 2 - a 2 - j - l] : Exponent 3) =
          ![e 0 - a 0 - k + i - k + j,
            e 1 - a 1 - i - k + l, e 2 - a 2 - j - l] := by
        funext d
        fin_cases d <;> dsimp <;> omega
      rw [idx]
      simp only [smul_smul, weight]
      congr 1
      ring

theorem actual_three_field_balanced_transport
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
        (∀ e : Exponent 3,
          clearedInnerIterate D α β γ δ u v t w k a e =
            signedExtend (innerCollision P) e) ∧
        (∀ e : Exponent 3,
          polynomialAction (innerPolynomial k a)
            (fun e => innerIterate D α β γ δ u v t w (e 0) (e 1) (e 2)) e =
              signedExtend (innerCollision P) e) ∧
        (∀ x b z : ℤ,
          innerIterate D α β γ δ u v t w x b z =
            ∑ i ∈ innerFiber k a x b z, innerWeight k a i •
              signedExtend (innerCollision P) (innerInput k a x b z i) ) ∧
        (∃ S Z : ℕ,
          (∀ s x z : ℤ, s < -(S : ℤ) → balanced D α β γ δ u v t w s x z = 0) ∧
          (∀ s x z : ℤ, z < -(Z : ℤ) → balanced D α β γ δ u v t w s x z = 0)) ∧
        ∀ e : Exponent 3,
          clearedBalanced D α β γ δ u v t w k a e =
            signedExtend (balancedCollision P) e := by
  classical
  dsimp only
  obtain ⟨k, locality, rest⟩ := actual_three_field_raw_inner_coefficients D α β γ u v t
  refine ⟨k, locality, ?_⟩
  intro δ w
  obtain ⟨a, P, truncation, six, cleared, action, raw⟩ := rest δ w
  refine ⟨a, P, truncation, six, cleared, action, raw,
    actual_balanced_support D α β γ δ u v t w, ?_⟩
  intro e
  let F : Distribution 3 (Oscillator D) :=
    nestedCanonical D ![α, β, γ] ![u, v, t] δ w 0 1 2
  let G : ℤ → ℤ → Oscillator D := fun y x => balancedCross k F y x (e 2 - a 2)
  have loc02 : (deltaEnd ^ k) (commutator
      (Y D (inclusion D α u)) (Y D (inclusion D γ t))) = 0 := locality 0 2 (by decide)
  have loc12 : (deltaEnd ^ k) (commutator
      (Y D (inclusion D β v)) (Y D (inclusion D γ t))) = 0 := locality 1 2 (by decide)
  have lower (y x : ℤ) (hx : x < -(a 1 : ℤ)) : G y x = 0 :=
    cross_lower D α β γ δ u v t w k (a 1) loc12 (truncation 1) y x _ hx
  have commonSlice (y x : ℤ) :
      clear k G (y - a 0) (x - a 1) = extend (balancedSlice P (e 2)) y x := by
    have h := (six ![y, x, e 2]).1
    rw [balanced_clearing_three] at h
    change clear k G (y - a 0) (x - a 1) = signedExtend P ![y, x, e 2] at h
    exact h.trans (balancedSlice_extend P (e 2) y x).symm
  have signed := signed_cleared_collision G k (a 0) (a 1) lower
    (balancedSlice P (e 2)) commonSlice (e 0) (e 1)
  have target := finite_first D α β γ δ u v t w k a loc02 (truncation 0) e
  have ee : (![e 0, e 1, e 2] : Exponent 3) = e := by
    funext i
    fin_cases i <;> rfl
  exact target.trans (signed.2.trans (by
    rw [← balancedCollision_signed, ee]))

#print actual_three_field_balanced_transport
#print axioms actual_three_field_balanced_transport
end
end D5.S3.VertexAlgebra.LatticeSectorThreeFieldBalancedTransport
