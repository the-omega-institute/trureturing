/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Supported common numerators and finite reconstruction for actual sector products. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorFullFusion
import D5.S3.VertexAlgebra.FormalSeries.SupportedChannelSeries

/-!
Classical formal-variable locality and duality, in the coefficient conventions
of the actual lattice field. Suppliers retain the Bakalov--Kac,
Matsuo--Nagatomo and Carnahan attributions in their owning modules.

proof_shape: content: rectangular support combines the two opposite ordered
products; reconstruction takes place on supported diagonals, using finite
signed-binomial convolution, never by cancellation on all distributions.
admission_basis: escape-witness
escape_witness: locality alone has delta torsion; the actual statewise
truncation supplies the lower support needed for reconstruction.
No polynomial numerator, positivity or sewing hypothesis is imposed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorChannelTransport
open LatticeGeneratingFieldLocality LatticeSectorIntertwiner SupportedChannelSeries
open LatticeSugawaraCurrents
open LatticeAllStateField LatticeAllStateJacobi LatticeAllStateReconstruction
open FieldNormalProductLocality
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section

/-- Actual u(x)v(y)w, including every descendant and the original cocycle. -/
def product (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (w : Sector D γ) (a b : ℤ) :
    Oscillator D :=
  canonical D α (β + γ) u (-a - 1) (canonical D β γ v (-b - 1) w)

/-- Actual v(y)u(x)w; the variable x is still attached to u. -/
def reverseProduct (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (w : Sector D γ) (a b : ℤ) :
    Oscillator D :=
  canonical D β (α + γ) v (-b - 1) (canonical D α γ u (-a - 1) w)

private theorem cleared_local (D : LatticeData) (α β : Charge D)
    (u : Sector D α) (v : Sector D β) (N : ℕ)
    (locality : delta^[N] (FieldNormalProductLocality.commutator (Y D (inclusion D α u))
      (Y D (inclusion D β v))) = 0)
    (γ : Charge D) (w : Sector D γ) (a b : ℤ) :
    clear N (product D α β γ u v w) a b =
      clear N (reverseProduct D α β γ u v w) a b := by
  classical
  have killed : (deltaEnd ^ N) (FieldNormalProductLocality.commutator (Y D (inclusion D α u))
      (Y D (inclusion D β v))) = 0 := by
    rw [Module.End.pow_apply]
    exact locality
  have h := congrArg (fun d : ℤ → ℤ → Module.End ℂ (Carrier D) =>
    projection D ((α + β) + γ)
      (d (-a - 1) (-b - 1) (inclusion D γ w))) killed
  rw [FieldDeltaBinomial.delta_binomial] at h
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    FieldNormalProductLocality.commutator, LinearMap.sub_apply, Module.End.mul_apply,
    Pi.zero_apply, LinearMap.zero_apply, map_sum, map_smul, map_sub, map_zero] at h
  have first (k : ℕ) :
      (((Y D (inclusion D α u))[[-a - 1 + N - k]])
        (((Y D (inclusion D β v))[[-b - 1 + k]]) (inclusion D γ w)))
        ((α + β) + γ) =
      product D α β γ u v w (a - N + k) (b - k) := by
    simp only [inclusion, Finsupp.lsingle_apply, ← single_canonical, add_assoc, Finsupp.single_eq_same]
    unfold product
    rw [show -(a - N + k) - 1 = -a - 1 + N - k by omega,
      show -(b - k) - 1 = -b - 1 + k by omega]
  have second (k : ℕ) :
      (((Y D (inclusion D β v))[[-b - 1 + k]])
        (((Y D (inclusion D α u))[[-a - 1 + N - k]]) (inclusion D γ w)))
        ((α + β) + γ) =
      reverseProduct D α β γ u v w (a - N + k) (b - k) := by
    simp only [inclusion, Finsupp.lsingle_apply, ← single_canonical]
    rw [show β + (α + γ) = (α + β) + γ by abel]
    rw [Finsupp.single_eq_same]
    unfold reverseProduct
    rw [show -(a - N + k) - 1 = -a - 1 + N - k by omega,
      show -(b - k) - 1 = -b - 1 + k by omega]
  change (∑ k ∈ Finset.range (N + 1), (((-1 : ℂ) ^ k) * (N.choose k : ℂ)) •
    (((Y D (inclusion D α u))[[-a - 1 + N - k]])
      (((Y D (inclusion D β v))[[-b - 1 + k]]) (inclusion D γ w)) ((α + β) + γ) -
     ((Y D (inclusion D β v))[[-b - 1 + k]])
      (((Y D (inclusion D α u))[[-a - 1 + N - k]]) (inclusion D γ w)) ((α + β) + γ))) = 0 at h
  simp_rw [first, second, smul_sub] at h
  exact sub_eq_zero.mp (by simpa only [clear, Finset.sum_sub_distrib] using h)

private theorem clear_product_below (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (w : Sector D γ) (N B : ℕ)
    (cutoff : ∀ n : ℤ, (B : ℤ) ≤ n → canonical D β γ v n w = 0)
    (a b : ℤ) (low : b < -(B : ℤ)) :
    clear N (product D α β γ u v w) a b = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  simp only [product]
  rw [cutoff _ (by omega), map_zero, smul_zero]

private theorem clear_reverse_below (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (w : Sector D γ) (N A : ℕ)
    (cutoff : ∀ n : ℤ, (A : ℤ) ≤ n → canonical D α γ u n w = 0)
    (a b : ℤ) (low : a < -(A : ℤ)) :
    clear N (reverseProduct D α β γ u v w) a b = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hk' : k ≤ N := by simpa using Finset.mem_range.mp hk
  simp only [reverseProduct]
  rw [cutoff _ (by omega), map_zero, smul_zero]

/-- A shared genuinely unrestricted power series, obtained from actual
locality and the two statewise lower bounds. N is independent of γ and w. -/
private theorem common_numerator (D : LatticeData) (α β : Charge D)
    (u : Sector D α) (v : Sector D β) :
    ∃ N : ℕ,
      delta^[N] (FieldNormalProductLocality.commutator (Y D (inclusion D α u)) (Y D (inclusion D β v))) = 0 ∧
      (∀ n : ℤ, (N : ℤ) ≤ n → canonical D α β u n v = 0) ∧
      ∀ (γ : Charge D) (w : Sector D γ), ∃ A B : ℕ,
        ∃ P : MvPowerSeries (Fin 2) (Oscillator D),
        (∀ n : ℤ, (A : ℤ) ≤ n → canonical D α γ u n w = 0) ∧
        (∀ n : ℤ, (B : ℤ) ≤ n → canonical D β γ v n w = 0) ∧
        ∀ a b : ℤ,
          clear N (product D α β γ u v w) (a - A) (b - B) = extend P a b ∧
          clear N (reverseProduct D α β γ u v w) (a - A) (b - B) = extend P a b := by
  classical
  obtain ⟨N₀, hN₀⟩ := LatticeAllStateLocality.stateField_locality D
    (inclusion D α u) (inclusion D β v)
  obtain ⟨T, hT⟩ := canonical_truncation D α β u v
  let N := max N₀ T.toNat
  have hN : delta^[N] (FieldNormalProductLocality.commutator (Y D (inclusion D α u))
      (Y D (inclusion D β v))) = 0 :=
    FiniteFieldLocality.monotone _ N₀ N (Nat.le_max_left _ _) hN₀
  refine ⟨N, hN, ?_, ?_⟩
  · intro n hn
    exact hT n (by have := Nat.le_max_right N₀ T.toNat; omega)
  intro γ w
  obtain ⟨T₁, hT₁⟩ := canonical_truncation D α γ u w
  obtain ⟨T₂, hT₂⟩ := canonical_truncation D β γ v w
  let A := T₁.toNat
  let B := T₂.toNat
  have hA (n : ℤ) (hn : (A : ℤ) ≤ n) : canonical D α γ u n w = 0 :=
    hT₁ n (by omega)
  have hB (n : ℤ) (hn : (B : ℤ) ≤ n) : canonical D β γ v n w = 0 :=
    hT₂ n (by omega)
  let P : MvPowerSeries (Fin 2) (Oscillator D) :=
    fun d => clear N (product D α β γ u v w) ((d 0 : ℤ) - A) ((d 1 : ℤ) - B)
  refine ⟨A, B, P, hA, hB, ?_⟩
  intro a b
  have equal := cleared_local D α β u v N hN γ w (a - A) (b - B)
  suffices h : clear N (product D α β γ u v w) (a - A) (b - B) = extend P a b by
    exact ⟨h, equal.symm.trans h⟩
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · simp [extend, ha, hb, P, MvPowerSeries.coeff_apply, powerIndex,
        Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]
    · rw [extend, ite_eq_right (by tauto)]
      exact clear_product_below D α β γ u v w N B hB _ _ (by omega)
  · rw [extend, ite_eq_right (by tauto), equal]
    exact clear_reverse_below D α β γ u v w N A hA _ _ (by omega)


/-- Shared actual product channels with an explicit finite inverse expansion.
The same N works for all third charges and states. This statement makes no
iterate/substitution or coherence claim. -/
private theorem ordinary_actual_supported_products (D : LatticeData) (α β : Charge D)
    (u : Sector D α) (v : Sector D β) :
    ∃ N : ℕ,
      delta^[N] (FieldNormalProductLocality.commutator (Y D (inclusion D α u)) (Y D (inclusion D β v))) = 0 ∧
      (∀ n : ℤ, (N : ℤ) ≤ n → canonical D α β u n v = 0) ∧
      ∀ (γ : Charge D) (w : Sector D γ), ∃ A B : ℕ,
        ∃ P : MvPowerSeries (Fin 2) (Oscillator D),
        (∀ n : ℤ, (A : ℤ) ≤ n → canonical D α γ u n w = 0) ∧
        (∀ n : ℤ, (B : ℤ) ≤ n → canonical D β γ v n w = 0) ∧
        (∀ a b : ℤ,
          clear N (product D α β γ u v w) (a - A) (b - B) = extend P a b ∧
          clear N (reverseProduct D α β γ u v w) (a - A) (b - B) = extend P a b) ∧
        ∀ a b : ℤ, 0 ≤ b + B →
          product D α β γ u v w a b =
            ∑ j ∈ Finset.range ((b + B).toNat + 1),
              (((-1 : ℂ) ^ j) * integerBinomial (-(N : ℤ)) j) •
                extend P (a + A + N + j) (b + B - j) := by
  obtain ⟨N, hN, huv, rest⟩ := common_numerator D α β u v
  refine ⟨N, hN, huv, ?_⟩
  intro γ w
  obtain ⟨A, B, P, hA, hB, common⟩ := rest γ w
  refine ⟨A, B, P, hA, hB, common, ?_⟩
  intro a b hb
  have lower (x y : ℤ) (hy : y < -(B : ℤ)) :
      product D α β γ u v w x y = 0 := by
    unfold product
    rw [hB _ (by omega), map_zero]
  rw [supported_reconstruction (product D α β γ u v w) N B lower a b hb]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hc := (common (a + A + N + j) (b + B - j)).1
  rw [show a + A + N + j - A = a + N + j by omega,
    show b + B - j - B = b - j by omega] at hc
  exact hc


/-- Actual (u(t)v)(y)w on the true sum-charge carrier. -/
def iterate (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (w : Sector D γ) (a b : ℤ) :
    Oscillator D :=
  canonical D (α + β) γ (canonical D α β u (-a - 1) v) (-b - 1) w

/-- The finite coefficient map t^N(t+y)^A y^B. -/
def clearIterate {V : Type*} [AddCommGroup V] [Module ℂ V]
    (N A B : ℕ) (I : ℤ → ℤ → V) (a b : ℤ) : V :=
  ∑ h ∈ Finset.range (A + 1),
    (A.choose h : ℂ) • I (a - N - h) (b - B - A + h)

theorem iterate_borcherds (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (w : Sector D γ)
    (N A B : ℕ)
    (hA : ∀ n : ℤ, (A : ℤ) ≤ n → canonical D α γ u n w = 0)
    (a b : ℤ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      (((-1 : ℂ) ^ i) * integerBinomial (N - a - 1) i) •
        product D α β γ u v w (a - A - N + i) (b - B - i)) ∧
    clearIterate N A B (iterate D α β γ u v w) a b =
      ∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial (N - a - 1) i) •
        product D α β γ u v w (a - A - N + i) (b - B - i) := by
  classical
  let U := inclusion D α u
  let V := inclusion D β v
  let W := inclusion D γ w
  let P := projection D ((α + β) + γ)
  let p : ℤ := A
  let q : ℤ := B - b - 1
  let r : ℤ := N - a - 1
  have original := LatticeAllStateJacobi.borcherds D U V W p q r
  have left (i : ℕ) :
      P (jacobiLeftTerm D p q r U V W i) =
        integerBinomial (A : ℤ) i •
          iterate D α β γ u v w (a - N - i) (b - B - A + i) := by
    simp only [jacobiLeftTerm, mu, U, V, W, P, p, q, r, inclusion,
      Finsupp.lsingle_apply, ← single_canonical, projection, Finsupp.lapply_apply,
      Finsupp.smul_apply, Finsupp.single_eq_same]
    unfold iterate
    rw [show -(a - N - i) - 1 = (N : ℤ) - a - 1 + i by omega,
      show -(b - B - A + i) - 1 = (A : ℤ) + (B - b - 1) - i by omega]
  have first (i : ℕ) :
      P (jacobiRightFirstTerm D p q r U V W i) =
        (((-1 : ℂ) ^ i) * integerBinomial (N - a - 1) i) •
          product D α β γ u v w (a - A - N + i) (b - B - i) := by
    simp only [jacobiRightFirstTerm, mu, U, V, W, P, p, q, r, inclusion,
      Finsupp.lsingle_apply, ← single_canonical, projection, Finsupp.lapply_apply,
      Finsupp.smul_apply, add_assoc, Finsupp.single_eq_same]
    unfold product
    rw [show -(a - A - N + i) - 1 = (A : ℤ) + (N - a - 1) - i by omega,
      show -(b - B - i) - 1 = (B : ℤ) - b - 1 + i by omega]
  have second (i : ℕ) : P (jacobiRightSecondTerm D p q r U V W i) = 0 := by
    have inner : mu D U (p + i) W = 0 := by
      change ((Y D (inclusion D α u))[[(A : ℤ) + i]]) (inclusion D γ w) = 0
      rw [← inclusion_canonical, hA _ (by omega), map_zero]
    unfold jacobiRightSecondTerm
    rw [inner]
    simp [mu]
  have equation := original.2.2.2
  simp_rw [smul_sub] at equation
  change (∑ᶠ i : ℕ, jacobiLeftTerm D p q r U V W i) =
    ∑ᶠ i : ℕ, (jacobiRightFirstTerm D p q r U V W i -
      jacobiRightSecondTerm D p q r U V W i) at equation
  rw [finsum_sub_distrib original.2.1 original.2.2.1] at equation
  have projected := congrArg P equation
  rw [map_sub, map_finsum P original.1, map_finsum P original.2.1,
    map_finsum P original.2.2.1] at projected
  simp_rw [left, first, second] at projected
  simp only [finsum_zero, sub_zero] at projected
  have leftSum :
      (∑ᶠ i : ℕ, integerBinomial (A : ℤ) i •
        iterate D α β γ u v w (a - N - i) (b - B - A + i)) =
      clearIterate N A B (iterate D α β γ u v w) a b := by
    simp only [integerBinomial, Ring.choose_natCast, Int.cast_natCast]
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hout
    have hAi : A < i := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hout
      omega
    exact hi (by simp [Nat.choose_eq_zero_of_lt hAi])
  refine ⟨?_, ?_⟩
  · simpa only [first] using original.2.1.fun_comp (map_zero P)
  · rw [leftSum] at projected
    exact projected

private theorem iterate_collision (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (w : Sector D γ)
    (N A B : ℕ)
    (huv : ∀ n : ℤ, (N : ℤ) ≤ n → canonical D α β u n v = 0)
    (hA : ∀ n : ℤ, (A : ℤ) ≤ n → canonical D α γ u n w = 0)
    (hB : ∀ n : ℤ, (B : ℤ) ≤ n → canonical D β γ v n w = 0)
    (P : MvPowerSeries (Fin 2) (Oscillator D))
    (common : ∀ a b : ℤ,
      clear N (product D α β γ u v w) (a - A) (b - B) = extend P a b)
    (a b : ℤ) :
    clearIterate N A B (iterate D α β γ u v w) a b = extend (collision P) a b := by
  classical
  have lower (x y : ℤ) (hy : y < -(B : ℤ)) :
      product D α β γ u v w x y = 0 := by
    unfold product
    rw [hB _ (by omega), map_zero]
  by_cases ha : 0 ≤ a
  · have bor := iterate_borcherds D α β γ u v w N A B hA a b
    rw [bor.2]
    by_cases hb : 0 ≤ b
    · rw [extend, ite_eq_left ⟨ha, hb⟩]
      have finite :
          (∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial (N - a - 1) i) •
            product D α β γ u v w (a - A - N + i) (b - B - i)) =
          ∑ i ∈ Finset.range (b.toNat + 1),
            (((-1 : ℂ) ^ i) * integerBinomial (N - a - 1) i) •
              product D α β γ u v w (a - A - N + i) (b - B - i) := by
        apply finsum_eq_sum_of_support_subset
        intro i hi
        by_contra hout
        apply hi
        have hib : b < i := by simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hout; omega
        change (((-1 : ℂ) ^ i) * integerBinomial (N - a - 1) i) •
          product D α β γ u v w (a - A - N + i) (b - B - i) = 0
        rw [lower _ _ (by omega), smul_zero]
      rw [finite]
      simpa only [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb] using
        cleared_collision_coeff (product D α β γ u v w) N A B lower P common a.toNat b.toNat
    · rw [extend, ite_eq_right (by tauto)]
      apply finsum_eq_zero_of_forall_eq_zero
      intro i
      rw [lower _ _ (by omega), smul_zero]
  · rw [extend, ite_eq_right (by tauto)]
    apply Finset.sum_eq_zero
    intro h hh
    unfold iterate
    rw [huv _ (by omega), map_zero]
    simp


private theorem iterate_reconstruction (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (w : Sector D γ)
    (N A B : ℕ)
    (huv : ∀ n : ℤ, (N : ℤ) ≤ n → canonical D α β u n v = 0)
    (P : MvPowerSeries (Fin 2) (Oscillator D))
    (common : ∀ a b : ℤ,
      clearIterate N A B (iterate D α β γ u v w) a b = extend (collision P) a b)
    (a b : ℤ) :
    iterate D α β γ u v w a b =
      if 0 ≤ a + N then
        ∑ j ∈ Finset.range ((a + N).toNat + 1), integerBinomial (-(A : ℤ)) j •
          extend (collision P) (a + N - j) (b + B + A + j)
      else 0 := by
  have lower (x y : ℤ) (hx : x < -(N : ℤ)) :
      iterate D α β γ u v w x y = 0 := by
    unfold iterate
    rw [huv _ (by omega), map_zero]
    simp
  by_cases ha : 0 ≤ a + N
  · rw [ite_eq_left ha, supported_positive_reconstruction
      (iterate D α β γ u v w) A N lower a b ha]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    calc
      positiveClear A (iterate D α β γ u v w) (a - j) (b + j) =
          clearIterate N A B (iterate D α β γ u v w)
            (a + N - j) (b + B + A + j) := by
        apply Finset.sum_congr rfl
        intro h hh
        congr 2 <;> omega
      _ = extend (collision P) (a + N - j) (b + B + A + j) := common _ _
  · rw [ite_eq_right ha]
    exact lower a b (by omega)

/-- Actual all-descendant collision transport, with a common infinite vector
numerator and a supported finite inverse expansion for the ordered product. -/
theorem ordinary_actual_cleared_channel_transport
    (D : LatticeData) (α β : Charge D) (u : Sector D α) (v : Sector D β) :
    ∃ N : ℕ,
      delta^[N] (FieldNormalProductLocality.commutator
        (Y D (inclusion D α u)) (Y D (inclusion D β v))) = 0 ∧
      (∀ n : ℤ, (N : ℤ) ≤ n → canonical D α β u n v = 0) ∧
      ∀ (γ : Charge D) (w : Sector D γ), ∃ A B : ℕ,
        ∃ P : MvPowerSeries (Fin 2) (Oscillator D),
        (∀ n : ℤ, (A : ℤ) ≤ n → canonical D α γ u n w = 0) ∧
        (∀ n : ℤ, (B : ℤ) ≤ n → canonical D β γ v n w = 0) ∧
        (∀ a b : ℤ,
          clear N (product D α β γ u v w) (a - A) (b - B) = extend P a b ∧
          clear N (reverseProduct D α β γ u v w) (a - A) (b - B) = extend P a b ∧
          clearIterate N A B (iterate D α β γ u v w) a b = extend (collision P) a b) ∧
        (∀ a b : ℤ,
          product D α β γ u v w a b =
            if 0 ≤ b + B then ∑ j ∈ Finset.range ((b + B).toNat + 1),
              (((-1 : ℂ) ^ j) * integerBinomial (-(N : ℤ)) j) •
                extend P (a + A + N + j) (b + B - j) else 0) ∧
        ∀ a b : ℤ, iterate D α β γ u v w a b =
          if 0 ≤ a + N then
            ∑ j ∈ Finset.range ((a + N).toNat + 1), integerBinomial (-(A : ℤ)) j •
              extend (collision P) (a + N - j) (b + B + A + j) else 0 := by
  obtain ⟨N, hN, huv, rest⟩ := ordinary_actual_supported_products D α β u v
  refine ⟨N, hN, huv, ?_⟩
  intro γ w
  obtain ⟨A, B, P, hA, hB, common, inverse⟩ := rest γ w
  have collisionLaw := iterate_collision D α β γ u v w N A B huv hA hB P
    (fun x y => (common x y).1)
  refine ⟨A, B, P, hA, hB, ?_, ?_, ?_⟩
  · intro a b
    exact ⟨(common a b).1, (common a b).2, collisionLaw a b⟩
  · intro a b
    by_cases hb : 0 ≤ b + B
    · rw [ite_eq_left hb]
      exact inverse a b hb
    · rw [ite_eq_right hb]
      unfold product
      rw [hB _ (by omega), map_zero]
  · exact iterate_reconstruction D α β γ u v w N A B huv P collisionLaw

open LatticeSectorIntertwiner.FiniteSectorObject

/-- Reassociation transports the actual neutral-action law, preserving the
underlying linear map, including on finite targets with repeated charges. -/
private def incomingAssoc (D : LatticeData) (α β γ : Charge D) (M : FiniteSectorObject D) :
    Incoming D (α + (β + γ)) M ≃ₗ[ℂ] Incoming D ((α + β) + γ) M where
  toFun f := ⟨f.val, by
    intro a n x
    have e := congrArg (fun δ : Charge D => action D δ a n x) (add_assoc α β γ)
    exact (congrArg f.val e).trans (f.property a n x)⟩
  invFun f := ⟨f.val, by
    intro a n x
    have e := congrArg (fun δ : Charge D => action D δ a n x) (add_assoc α β γ)
    exact (congrArg f.val e.symm).trans (f.property a n x)⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv f := by apply Subtype.ext; rfl
  map_add' f g := rfl
  map_smul' c f := rfl

/-- The entire FullIO spaces are identified by their actual universal maps.
The collision theorem below is the mathematical consumer of this equivalence. -/
def fullChannel (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ : Charge D) (M : FiniteSectorObject D) :
    FullIO D α (β + γ) M ≃ₗ[ℂ] FullIO D (α + β) γ M :=
  (fullUniversal D H hHG hGH α (β + γ) M).symm.trans
    ((incomingAssoc D α β γ M).trans (fullUniversal D H hHG hGH (α + β) γ M))

private theorem map_extend {R S : Type*} [CommRing R] [Algebra ℂ R]
    [CommRing S] [Algebra ℂ S] (f : R →ₗ[ℂ] S)
    (P : MvPowerSeries (Fin 2) R) (a b : ℤ) :
    f (extend P a b) = extend (mapSeries f P) a b := by
  by_cases h : 0 ≤ a ∧ 0 ≤ b <;> simp [extend, h, mapSeries, MvPowerSeries.coeff_apply]

/-- Every actual finite-target full intertwiner inherits the supported
collision transport. Readouts are linear; no multiplicative target map or
sewing axiom is assumed. The inverse Gram hypotheses occur only in the
existing classification used to obtain its incoming map. -/
theorem fullIO_supported_channel_transport (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ : Charge D) (M : FiniteSectorObject D)
    (F : FullIO D α (β + γ) M)
    (u : Sector D α) (v : Sector D β) (w : Sector D γ) :
    let f := (fullUniversal D H hHG hGH α (β + γ) M).symm F
    let left := fullChannel D H hHG hGH α β γ M F
    let productF := fun a b : ℤ => F.val u (-a - 1) (canonical D β γ v (-b - 1) w)
    let iterateF := fun a b : ℤ => left.val (canonical D α β u (-a - 1) v) (-b - 1) w
    ∃ N A B : ℕ, ∃ Q : MvPowerSeries (Fin 2) (M.States D),
      (∀ a b : ℤ,
        clear N productF (a - A) (b - B) = extend Q a b ∧
        clear N (fun x y => f.val (reverseProduct D α β γ u v w x y))
          (a - A) (b - B) = extend Q a b ∧
        clearIterate N A B iterateF a b = extend (collision Q) a b) ∧
      (∀ a b : ℤ, productF a b =
        if 0 ≤ b + B then ∑ j ∈ Finset.range ((b + B).toNat + 1),
          (((-1 : ℂ) ^ j) * integerBinomial (-(N : ℤ)) j) •
            extend Q (a + A + N + j) (b + B - j) else 0) ∧
      ∀ a b : ℤ, iterateF a b =
        if 0 ≤ a + N then
          ∑ j ∈ Finset.range ((a + N).toNat + 1), integerBinomial (-(A : ℤ)) j •
            extend (collision Q) (a + N - j) (b + B + A + j) else 0 := by
  classical
  dsimp only
  let f := (fullUniversal D H hHG hGH α (β + γ) M).symm F
  have prod (a b : ℤ) : F.val u (-a - 1) (canonical D β γ v (-b - 1) w) =
      f.val (product D α β γ u v w a b) := by
    have eqF : fullUniversal D H hHG hGH α (β + γ) M f = F :=
      (fullUniversal D H hHG hGH α (β + γ) M).apply_symm_apply F
    change _ = ((fullUniversal D H hHG hGH α (β + γ) M f).val u (-a - 1)
      (canonical D β γ v (-b - 1) w))
    rw [eqF]
  have iter (a b : ℤ) :
      (fullChannel D H hHG hGH α β γ M F).val
        (canonical D α β u (-a - 1) v) (-b - 1) w =
      f.val (iterate D α β γ u v w a b) := rfl
  obtain ⟨N, hN, huv, rest⟩ := ordinary_actual_cleared_channel_transport D α β u v
  obtain ⟨A, B, P, hA, hB, common, inverse, inverseI⟩ := rest γ w
  refine ⟨N, A, B, mapSeries f.val P, ?_, ?_, ?_⟩
  · intro a b
    have first := congrArg f.val (common a b).1
    have second := congrArg f.val (common a b).2.1
    have third := congrArg f.val (common a b).2.2
    simp only [clear, map_sum, map_smul, map_extend] at first second
    simp only [clearIterate, map_sum, map_smul, map_extend, ← collision_map] at third
    simp_rw [prod, iter]
    exact ⟨first, second, third⟩
  · intro a b
    have eq := congrArg f.val (inverse a b)
    by_cases hb : 0 ≤ b + B
    · simpa only [prod, ite_eq_left hb, map_sum, map_smul, map_extend] using eq
    · simpa only [prod, ite_eq_right hb, map_zero] using eq
  · intro a b
    have eq := congrArg f.val (inverseI a b)
    by_cases ha : 0 ≤ a + N
    · simpa only [iter, ite_eq_left ha, map_sum, map_smul, map_extend, ← collision_map] using eq
    · simpa only [iter, ite_eq_right ha, map_zero] using eq

end
end D5.S3.VertexAlgebra.LatticeSectorChannelTransport
