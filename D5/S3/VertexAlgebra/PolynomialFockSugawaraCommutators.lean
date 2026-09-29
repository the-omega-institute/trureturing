/- GID: D5/S3/VertexAlgebra/PolynomialFockSugawaraCommutators
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/PolynomialFockSugawaraCommutators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Concrete polynomial Fock modes satisfy Heisenberg and Sugawara-current commutators. -/

/-
proof_shape: mode_heisenberg: content; L_mode_commutator: content
escape_witness: Partial differentiation of a multiplication mode produces the Kronecker
  central term. Commuting a mode through the finite normal-ordered sum leaves two
  singleton-supported contributions, each equal to the target current mode.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/VertexAlgebra/PolynomialFockSugawaraSupport.normalPair_support_interval
  (sha256:4965c0130d0dbcb3bc99ea25c46d318f4523b7b32c7450986791b3fb99994f7c).
-/

import D5.S3.VertexAlgebra.PolynomialFockSugawaraSupport
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.PolynomialFockSugawaraCommutators

open MvPolynomial
open D5.S3.VertexAlgebra.PolynomialFockSugawaraSupport

private theorem pderiv_commute (i j : ℕ) (p : Fock) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  have h : ⁅(pderiv i : Derivation ℂ Fock Fock),
      (pderiv j : Derivation ℂ Fock Fock)⁆ = (0 : Derivation ℂ Fock Fock) := by
    apply MvPolynomial.derivation_ext
    intro k
    simp only [Derivation.commutator_apply, pderiv_X, Pi.single_apply]
    split_ifs <;> simp
  have hp := congrArg (fun D : Derivation ℂ Fock Fock => D p) h
  change pderiv i (pderiv j p) - pderiv j (pderiv i p) = 0 at hp
  exact sub_eq_zero.mp hp

private theorem annihilate_create_commutator (i j : ℕ) :
    annihilate i * create j - create j * annihilate i =
      if i = j then (i + 1 : ℂ) • (1 : Module.End ℂ Fock) else 0 := by
  apply LinearMap.ext
  intro p
  change (i + 1 : ℂ) • pderiv i ((X j : Fock) * p) -
      (X j : Fock) * ((i + 1 : ℂ) • pderiv i p) =
      (if i = j then (i + 1 : ℂ) • (1 : Module.End ℂ Fock) else 0) p
  rw [pderiv_mul]
  by_cases h : i = j
  · subst j
    simp [mul_comm]
  · have hji : j ≠ i := Ne.symm h
    simp [h, pderiv_X_of_ne hji, mul_comm]

private theorem annihilate_commute (i j : ℕ) :
    annihilate i * annihilate j = annihilate j * annihilate i := by
  apply LinearMap.ext
  intro p
  change (i + 1 : ℂ) • pderiv i ((j + 1 : ℂ) • pderiv j p) =
    (j + 1 : ℂ) • pderiv j ((i + 1 : ℂ) • pderiv i p)
  rw [(pderiv i).map_smul, (pderiv j).map_smul]
  rw [pderiv_commute i j p]
  exact smul_comm _ _ _

private theorem create_commute (i j : ℕ) :
    create i * create j = create j * create i := by
  apply LinearMap.ext
  intro p
  change (X i : Fock) * ((X j : Fock) * p) =
    (X j : Fock) * ((X i : Fock) * p)
  ac_rfl

/-- All integer-indexed Heisenberg modes satisfy the central commutator relation. -/
theorem mode_heisenberg (m n : ℤ) :
    mode m * mode n - mode n * mode m =
      if m + n = 0 then (m : ℂ) • (1 : Module.End ℂ Fock) else 0 := by
  cases m with
  | ofNat a =>
      cases a with
      | zero => simp [mode]
      | succ i =>
          cases n with
          | ofNat b =>
              cases b with
              | zero =>
                  have h : Int.ofNat (i + 1) + 0 ≠ 0 := by
                    simp only [Int.ofNat_eq_natCast]
                    omega
                  change annihilate i * 0 - 0 * annihilate i =
                    if Int.ofNat (i + 1) + 0 = 0 then
                      ((Int.ofNat (i + 1) : ℤ) : ℂ) • 1 else 0
                  rw [if_neg h]
                  simp
              | succ j =>
                  have h : Int.ofNat (i + 1) + Int.ofNat (j + 1) ≠ 0 := by
                    simp only [Int.ofNat_eq_natCast]
                    omega
                  change annihilate i * annihilate j - annihilate j * annihilate i =
                    if Int.ofNat (i + 1) + Int.ofNat (j + 1) = 0 then
                      ((Int.ofNat (i + 1) : ℤ) : ℂ) • 1 else 0
                  rw [if_neg h]
                  exact sub_eq_zero.mpr (annihilate_commute i j)
          | negSucc j =>
              have h : Int.ofNat (i + 1) + Int.negSucc j = 0 ↔ i = j := by
                simp only [Int.ofNat_eq_natCast, Int.negSucc_eq]
                omega
              change annihilate i * create j - create j * annihilate i =
                if Int.ofNat (i + 1) + Int.negSucc j = 0 then
                  ((Int.ofNat (i + 1) : ℤ) : ℂ) • 1 else 0
              have hcast : ((Int.ofNat (i + 1) : ℤ) : ℂ) = (i + 1 : ℂ) := by
                norm_cast
              simpa only [h, hcast] using annihilate_create_commutator i j
  | negSucc i =>
      cases n with
      | ofNat b =>
          cases b with
          | zero =>
              have h : Int.negSucc i + 0 ≠ 0 := by
                simp only [Int.negSucc_eq]
                omega
              change create i * 0 - 0 * create i =
                if Int.negSucc i + 0 = 0 then
                  ((Int.negSucc i : ℤ) : ℂ) • 1 else 0
              rw [if_neg h]
              simp
          | succ j =>
              have h : Int.negSucc i + Int.ofNat (j + 1) = 0 ↔ j = i := by
                simp only [Int.ofNat_eq_natCast, Int.negSucc_eq]
                omega
              have hc := annihilate_create_commutator j i
              change create i * annihilate j - annihilate j * create i =
                if Int.negSucc i + Int.ofNat (j + 1) = 0 then
                  ((Int.negSucc i : ℤ) : ℂ) • 1 else 0
              by_cases hij : j = i
              · subst i
                rw [if_pos (h.mpr rfl)]
                have hcast : ((Int.negSucc j : ℤ) : ℂ) = -(j + 1 : ℂ) := by
                  simp [Int.negSucc_eq]
                rw [hcast]
                have hc' : annihilate j * create j - create j * annihilate j =
                    (j + 1 : ℂ) • 1 := by simpa using hc
                calc
                  create j * annihilate j - annihilate j * create j =
                      -(annihilate j * create j - create j * annihilate j) := by abel
                  _ = -((j + 1 : ℂ) • 1) := by rw [hc']
                  _ = (-(j + 1 : ℂ)) • 1 := by rw [neg_smul]
              · rw [if_neg (fun he => hij (h.mp he))]
                have hc' : annihilate j * create i - create i * annihilate j = 0 := by
                  simpa [hij] using hc
                exact sub_eq_zero.mpr (sub_eq_zero.mp hc').symm
      | negSucc j =>
          have h : Int.negSucc i + Int.negSucc j ≠ 0 := by
            simp only [Int.negSucc_eq]
            omega
          change create i * create j - create j * create i =
            if Int.negSucc i + Int.negSucc j = 0 then
              ((Int.negSucc i : ℤ) : ℂ) • 1 else 0
          rw [if_neg h]
          exact sub_eq_zero.mpr (create_commute i j)

private theorem mode_product_commutator (a b r : ℤ) :
    (mode a * mode b) * mode r - mode r * (mode a * mode b) =
      (if b + r = 0 then (b : ℂ) • mode a else 0) +
      (if a + r = 0 then (a : ℂ) • mode b else 0) := by
  calc
    (mode a * mode b) * mode r - mode r * (mode a * mode b) =
        mode a * (mode b * mode r - mode r * mode b) +
        (mode a * mode r - mode r * mode a) * mode b := by noncomm_ring
    _ = (if b + r = 0 then (b : ℂ) • mode a else 0) +
        (if a + r = 0 then (a : ℂ) • mode b else 0) := by
          rw [mode_heisenberg b r, mode_heisenberg a r]
          split_ifs <;> simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

private theorem normalPair_mode_commutator (a b r : ℤ) :
    normalPair a b * mode r - mode r * normalPair a b =
      (if b + r = 0 then (b : ℂ) • mode a else 0) +
      (if a + r = 0 then (a : ℂ) • mode b else 0) := by
  by_cases h : b ≤ a
  · simpa only [normalPair, h, ↓reduceIte, Module.End.mul_eq_comp, add_comm] using
      mode_product_commutator b a r
  · simpa only [normalPair, h, ↓reduceIte, Module.End.mul_eq_comp] using
      mode_product_commutator a b r

/-- The polynomial Fock Sugawara operator acts on every Heisenberg mode with weight one. -/
theorem L_mode_commutator (m r : ℤ) :
    L m * mode r - mode r * L m = -(r : ℂ) • mode (m + r) := by
  apply LinearMap.ext
  intro p
  have hp : Function.HasFiniteSupport
      (fun k : ℤ => normalPair (m - k) k p) :=
    (Set.finite_Ioo _ _).subset (normalPair_support_interval m p)
  have hmp : Function.HasFiniteSupport
      (fun k : ℤ => normalPair (m - k) k (mode r p)) :=
    (Set.finite_Ioo _ _).subset (normalPair_support_interval m (mode r p))
  have hmap : Function.HasFiniteSupport
      (fun k : ℤ => mode r (normalPair (m - k) k p)) :=
    hp.fun_comp (map_zero (mode r))
  let v : Fock := -(r : ℂ) • mode (m + r) p
  have hfirst : Function.HasFiniteSupport
      (fun k : ℤ => if k + r = 0 then v else 0) := by
    apply (Set.finite_singleton (-r)).subset
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    simp only [Set.mem_singleton_iff]
    by_contra hne
    have : k + r ≠ 0 := by omega
    exact hk (by simp [this])
  have hsecond : Function.HasFiniteSupport
      (fun k : ℤ => if m - k + r = 0 then v else 0) := by
    apply (Set.finite_singleton (m + r)).subset
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    simp only [Set.mem_singleton_iff]
    by_contra hne
    have : m - k + r ≠ 0 := by omega
    exact hk (by simp [this])
  change (2 : ℂ)⁻¹ • ∑ᶠ k : ℤ, normalPair (m - k) k (mode r p) -
      mode r ((2 : ℂ)⁻¹ • ∑ᶠ k : ℤ, normalPair (m - k) k p) =
      (-(r : ℂ) • mode (m + r)) p
  calc
    (2 : ℂ)⁻¹ • ∑ᶠ k : ℤ, normalPair (m - k) k (mode r p) -
        mode r ((2 : ℂ)⁻¹ • ∑ᶠ k : ℤ, normalPair (m - k) k p) =
      (2 : ℂ)⁻¹ • ∑ᶠ k : ℤ,
        ((normalPair (m - k) k * mode r - mode r * normalPair (m - k) k) p) := by
          rw [map_smul, map_finsum (mode r) hp, ← smul_sub,
            ← finsum_sub_distrib hmp hmap]
          congr 1
    _ = (2 : ℂ)⁻¹ • ∑ᶠ k : ℤ,
        ((if k + r = 0 then v else 0) +
          (if m - k + r = 0 then v else 0)) := by
          congr 1
          apply finsum_congr
          intro k
          rw [normalPair_mode_commutator]
          simp only [LinearMap.add_apply, LinearMap.smul_apply,
            LinearMap.zero_apply, DFunLike.ite_apply]
          congr 1
          · by_cases hk : k + r = 0
            · have hkr : k = -r := by omega
              have hmkr : m - k = m + r := by omega
              simp [hkr, v]
            · simp [hk]
          · by_cases hmk : m - k + r = 0
            · have hmr : m - k = -r := by omega
              have hkmr : k = m + r := by omega
              simp [hkmr, v]
            · simp [hmk]
    _ = (2 : ℂ)⁻¹ • ((∑ᶠ k : ℤ, if k + r = 0 then v else 0) +
        (∑ᶠ k : ℤ, if m - k + r = 0 then v else 0)) := by
          rw [finsum_add_distrib hfirst hsecond]
    _ = (2 : ℂ)⁻¹ • (v + v) := by
          rw [finsum_eq_single _ (-r) (fun k hk => by simp [show k + r ≠ 0 by omega]),
            finsum_eq_single _ (m + r) (fun k hk => by
              simp [show m - k + r ≠ 0 by omega]),
            if_pos (by omega), if_pos (by omega)]
    _ = (-(r : ℂ) • mode (m + r)) p := by
          rw [← two_smul ℂ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
          rfl

end D5.S3.VertexAlgebra.PolynomialFockSugawaraCommutators
