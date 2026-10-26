/- GID: D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed supported inner collision with a spectator variable. -/

import D5.S3.VertexAlgebra.FormalSeries.SupportedChannelSeries
import D5.S3.VertexAlgebra.FormalSeries.UngradedLocalWordSeries
import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
The binomial inversion and legal bivariate substitution are reused from
SupportedChannelSeries, retaining its Carnahan attribution. Only the signed
negative collision region, the spectator fiber, and the finite polynomial
transport are new here. No cancellation on unrestricted distributions occurs.
proof_shape: signed_cleared_collision: content
proof_shape: slice_extend, clearing_three, innerCollision_coeff,
  innerCollision_signed: bind-only, consumed by the actual inner iterate transport
admission_basis: escape-witness
escape_witness: for a negative first collision exponent, the positive integer
binomial kernel has finite degree. Splitting its finite fiber at that degree
forces every summand to vanish: the lower part uses the common numerator's
negative first-coordinate support and the upper part has zero binomial weight.
This derives signed cancellation without a separate pair-state cutoff.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.SupportedThreeFieldCollision
open SupportedChannelSeries UniformGradedLocalCorrelator UngradedLocalWordSeries
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section

/-- The original signed Borcherds transform has a finite fiber even when its
collision exponent is negative. The common numerator, not an extra truncation
premise on a varying intermediate state, kills that negative region. -/
theorem signed_cleared_collision {R : Type*} [CommRing R] [Algebra ℂ R]
    (F : ℤ → ℤ → R) (N A B : ℕ)
    (lower : ∀ x y : ℤ, y < -(B : ℤ) → F x y = 0)
    (P : MvPowerSeries (Fin 2) R)
    (common : ∀ x y : ℤ, clear N F (x - A) (y - B) = extend P x y)
    (a b : ℤ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      (((-1 : ℂ) ^ i) * integerBinomial ((N : ℤ) - a - 1) i) •
        F (a - A - N + i) (b - B - i)) ∧
    (∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial ((N : ℤ) - a - 1) i) •
        F (a - A - N + i) (b - B - i)) = extend (collision P) a b := by
  classical
  let term (i : ℕ) : R :=
    (((-1 : ℂ) ^ i) * integerBinomial ((N : ℤ) - a - 1) i) •
      F (a - A - N + i) (b - B - i)
  have outside (i : ℕ) (hi : b < i) : term i = 0 := by
    dsimp only [term]
    rw [lower _ _ (by omega), smul_zero]
  have finite : Function.HasFiniteSupport term := by
    apply Set.Finite.subset (Finset.finite_toSet (Finset.range (b.toNat + 1)))
    intro i hi
    by_contra hout
    have bound : b < i := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hout
      omega
    exact hi (outside i bound)
  refine ⟨finite, ?_⟩
  by_cases hb : 0 ≤ b
  · have finiteSum : (∑ᶠ i : ℕ, term i) =
        ∑ i ∈ Finset.range (b.toNat + 1), term i := by
      apply finsum_eq_sum_of_support_subset
      intro i hi
      by_contra hout
      have bound : b < i := by
        simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hout
        omega
      exact hi (outside i bound)
    change (∑ᶠ i : ℕ, term i) = _
    rw [finiteSum]
    by_cases ha : 0 ≤ a
    · rw [extend, ite_eq_left ⟨ha, hb⟩]
      simpa only [term, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb] using
        cleared_collision_coeff F N A B lower P common a.toNat b.toNat
    · rw [extend, ite_eq_right (by tauto)]
      let s : ℤ := a + b - A - B - N
      let f : ℕ → R := fun n => F (s - n + B) ((n : ℤ) - B)
      let r : ℕ := (-a - 1).toNat
      have hr : (r : ℤ) = -a - 1 := by dsimp only [r]; omega
      have first : (∑ i ∈ Finset.range (b.toNat + 1), term i) =
          binomialTransform ((r : ℤ) + N) f b.toNat := by
        apply Finset.sum_congr rfl
        intro i hi
        have hib : i ≤ b.toNat := by simpa using Finset.mem_range.mp hi
        dsimp only [term, f, s]
        rw [show (r : ℤ) + N = (N : ℤ) - a - 1 by omega]
        congr 2 <;> omega
      rw [first, ← binomialTransform_add]
      change (∑ j ∈ Finset.range (b.toNat + 1),
        (((-1 : ℂ) ^ j) * integerBinomial (r : ℤ) j) •
          binomialTransform (N : ℤ) f (b.toNat - j)) = 0
      apply Finset.sum_eq_zero
      intro j hj
      have hjb : j ≤ b.toNat := by simpa using Finset.mem_range.mp hj
      by_cases hjr : j ≤ r
      · have hc : binomialTransform (N : ℤ) f (b.toNat - j) =
            extend P (a + j) (b - j) := by
          dsimp only [f]
          rw [transform_clear F N B (b.toNat - j) s lower]
          have hx : s + N - (b.toNat - j : ℕ) + B = a + j - A := by
            dsimp only [s]; omega
          have hy : ((b.toNat - j : ℕ) : ℤ) - B = b - j - B := by omega
          rw [hx, hy, common]
        rw [hc, extend, ite_eq_right (by omega), smul_zero]
      · have hz : integerBinomial (r : ℤ) j = 0 := by
          simp [integerBinomial, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega : r < j)]
        rw [hz, mul_zero, zero_smul]
  · rw [extend, ite_eq_right (by tauto)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    exact outside i (by omega)

/-- Fixed spectator coefficient of an infinite three-variable series, extended
by zero when the spectator exponent is negative. -/
def slice {R : Type*} [CommRing R] [Algebra ℂ R] (P : MvPowerSeries (Fin 3) R) (x : ℤ) :
    MvPowerSeries (Fin 2) R :=
  fun d => signedExtend P ![x, (d 0 : ℤ), (d 1 : ℤ)]

theorem slice_extend {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (x a b : ℤ) :
    extend (slice P x) a b = signedExtend P ![x, a, b] := by
  classical
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [extend, ite_eq_left ⟨ha, hb⟩]
      simp only [MvPowerSeries.coeff_apply, slice,
        powerIndex, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
        Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), zero_add, add_zero,
        Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]
    · have h : ¬ ∀ i : Fin 3, 0 ≤ (![x, a, b] : Fin 3 → ℤ) i := by
        intro h; exact hb (h 2)
      simp [extend, signedExtend, hb, h]
  · have h : ¬ ∀ i : Fin 3, 0 ≤ (![x, a, b] : Fin 3 → ℤ) i := by
      intro h; exact ha (h 1)
    simp [extend, signedExtend, ha, h]

private theorem shift_power {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Exponent 3) (n : ℕ) (F : Distribution 3 V) (e : Exponent 3) :
    (shift b ^ n) F e = F (e - n • b) := by
  induction n generalizing e with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (shift b ^ n) F (e - b) = _
    rw [ih]
    congr 1
    simp only [succ_nsmul]
    abel

private theorem neg_shift_power {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Exponent 3) (n : ℕ) :
    (-shift b : Module.End ℂ (Distribution 3 V)) ^ n =
      ((-1 : ℂ) ^ n) • (shift b ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ih, pow_succ']
    ext F e
    simp only [pow_succ', Module.End.mul_apply, LinearMap.neg_apply, LinearMap.smul_apply,
      mul_smul, neg_one_smul, map_smul, smul_neg]

private theorem pair_power_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (i j : Fin 3) (k : ℕ) (F : Distribution 3 V) (e : Exponent 3) :
    polynomialAction (pairPolynomial i j ^ k) F e =
      ∑ p ∈ Finset.range (k + 1),
        (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
          F (e - (k - p) • Pi.single i 1 - p • Pi.single j 1) := by
  classical
  have hc : Commute (-shift (Pi.single j 1) : Module.End ℂ (Distribution 3 V))
      (shift (Pi.single i 1)) := by
    ext G d
    simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, shift,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    abel
  have hd : (difference i j : Module.End ℂ (Distribution 3 V)) =
      -shift (Pi.single j 1) + shift (Pi.single i 1) := by
    unfold difference
    abel
  rw [map_pow, action_pair, hd, hc.add_pow, LinearMap.sum_apply]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [neg_shift_power]
  simp only [Module.End.mul_apply, Module.End.natCast_apply,
    LinearMap.smul_apply, Pi.smul_apply, map_nsmul, shift_power]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp only [smul_smul]
  apply congrArg₂ (fun (c : ℂ) (v : V) => c • v)
  · ring
  · congr 1
    abel

/-- Cross factors (z0-z1)^k(z0-z2)^k, before colliding labels 1 and 2.
Only a finite polynomial is expanded; F itself may have infinite support. -/
def cross {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (F : Distribution 3 V) (x y z : ℤ) : V :=
  ∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1),
    (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
      ((((-1 : ℂ) ^ q) * (k.choose q : ℂ)) •
        F ![x - 2 * k + p + q, y - p, z - q])

private theorem cross_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (F : Distribution 3 V) (e : Exponent 3) :
    polynomialAction (pairPolynomial 0 1 ^ k * pairPolynomial 0 2 ^ k) F e =
      cross k F (e 0) (e 1) (e 2) := by
  rw [map_mul, Module.End.mul_apply, pair_power_apply]
  unfold cross
  apply Finset.sum_congr rfl
  intro p hp
  have hpk : p ≤ k := by simpa using Finset.mem_range.mp hp
  rw [pair_power_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hqk : q ≤ k := by simpa using Finset.mem_range.mp hq
  apply congrArg (fun d : Exponent 3 =>
    (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
      ((((-1 : ℂ) ^ q) * (k.choose q : ℂ)) • F d))
  funext i
  fin_cases i <;>
    simp [Pi.sub_apply, Pi.single_apply, nsmul_eq_mul,
      Int.natCast_sub hpk, Int.natCast_sub hqk] <;> omega

/-- All three Q factors are accounted for: the inner pair is cleared last,
after expanding only the two cross factors. -/
theorem clearing_three {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (F : Distribution 3 V) (e : Exponent 3) :
    polynomialAction (clearingPolynomial 3 k) F e =
      clear k (cross k F (e 0)) (e 1) (e 2) := by
  classical
  have pairs : labelledPairs 3 =
      {(0, 1), (0, 2), (1, 2)} := by
    ext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> decide
  have poly : clearingPolynomial 3 k =
      pairPolynomial 1 2 ^ k * (pairPolynomial 0 1 ^ k * pairPolynomial 0 2 ^ k) := by
    simp [clearingPolynomial, pairs, mul_comm, mul_left_comm, mul_assoc]
  rw [poly, map_mul, Module.End.mul_apply, pair_power_apply]
  unfold clear
  apply Finset.sum_congr rfl
  intro p hp
  have hpk : p ≤ k := by simpa using Finset.mem_range.mp hp
  rw [cross_action]
  congr 1
  congr 1 <;>
    simp [Pi.sub_apply, Pi.single_apply, nsmul_eq_mul,
      Int.natCast_sub hpk] <;> omega

/-- Native three-variable index. -/
def index3 (x a b : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 x + Finsupp.single 1 a + Finsupp.single 2 b

private def innerLabel : Fin 2 ↪ Fin 3 :=
  ⟨Fin.succ, by intro i j h; exact Fin.succ_inj.mp h⟩

private theorem index3_inner (a b : ℕ) :
    index3 0 a b = (powerIndex a b).embDomain innerLabel := by
  simp [index3, powerIndex, Finsupp.embDomain_eq_mapDomain, innerLabel,
    Finsupp.mapDomain_add, Finsupp.mapDomain_single]

/-- The smallest triangular collision: z0 is unchanged and z1=t+z2. -/
def innerArguments (R : Type*) [CommRing R] :
    Fin 3 → MvPowerSeries (Fin 3) R :=
  ![MvPowerSeries.X 0, MvPowerSeries.X 1 + MvPowerSeries.X 2, MvPowerSeries.X 2]

private theorem inner_hasSubst (R : Type*) [CommRing R] :
    MvPowerSeries.HasSubst (innerArguments R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [innerArguments]

/-- Legal native substitution on a generally infinite input. -/
def innerCollision {R : Type*} [CommRing R] (P : MvPowerSeries (Fin 3) R) :
    MvPowerSeries (Fin 3) R := MvPowerSeries.subst (innerArguments R) P

private theorem inner_monomial_coeff {R : Type*} [CommRing R]
    (d : Fin 3 →₀ ℕ) (x a b : ℕ) :
    MvPowerSeries.coeff (index3 x a b)
      (d.prod (fun i n => (innerArguments R i) ^ n)) =
      if d 0 = x ∧ d 2 ≤ b ∧ d 1 = a + (b - d 2)
      then (d 1).choose a else 0 := by
  classical
  let B : MvPowerSeries (Fin 2) R :=
    (powerIndex (d 1) (d 2)).prod (fun i n => (collisionArguments R i) ^ n)
  have B_eq : B = (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ (d 1) *
      (MvPowerSeries.X 1) ^ (d 2) := by
    dsimp only [B]
    rw [Finsupp.prod_of_support_subset _ (Finset.subset_univ _)]
    · simp [Fin.prod_univ_two, collisionArguments, powerIndex]
    · intro i hi; simp
  have prod_eq : d.prod (fun i n => (innerArguments R i) ^ n) =
      MvPowerSeries.rename innerLabel B *
        MvPowerSeries.monomial (Finsupp.single 0 (d 0)) 1 := by
    rw [Finsupp.prod_of_support_subset d (Finset.subset_univ d.support)]
    · rw [B_eq]
      simp [Fin.prod_univ_succ, innerArguments, innerLabel,
        ← MvPowerSeries.X_pow_eq, mul_comm, mul_left_comm, mul_assoc] <;> ring
    · intro i hi; simp
  rw [prod_eq, MvPowerSeries.coeff_mul_monomial]
  have le_iff : Finsupp.single 0 (d 0) ≤ index3 x a b ↔ d 0 ≤ x := by
    constructor
    · intro h; simpa [index3] using h 0
    · intro h i; fin_cases i <;> simp [index3, h]
  simp only [le_iff]
  by_cases hx : d 0 ≤ x
  · rw [ite_eq_left hx, mul_one]
    have sub : index3 x a b - Finsupp.single 0 (d 0) = index3 (x - d 0) a b := by
      ext i
      fin_cases i <;> simp [index3, Finsupp.tsub_apply]
    rw [sub]
    by_cases he : d 0 = x
    · subst x
      rw [Nat.sub_self, index3_inner, MvPowerSeries.coeff_embDomain_rename]
      dsimp only [B]
      rw [collision_monomial_coeff]
      simp [powerIndex]
    · have outside : index3 (x - d 0) a b ∉
          Set.range (Finsupp.mapDomain (innerLabel : Fin 2 → Fin 3)) := by
        rintro ⟨u, hu⟩
        have hz : u.mapDomain (innerLabel : Fin 2 → Fin 3) 0 = 0 := by
          apply Finsupp.mapDomain_of_notMem_range
          rintro ⟨i, hi⟩
          fin_cases i <;> simp [innerLabel] at hi
        have h0 := congrArg (fun z : Fin 3 →₀ ℕ => z 0) hu
        simp only [hz] at h0
        simp [index3] at h0
        omega
      rw [MvPowerSeries.coeff_rename_eq_zero innerLabel B outside]
      simp [he]
  · rw [ite_eq_right hx]
    have he : d 0 ≠ x := by omega
    simp [he]

/-- Exact finite coefficient fiber of the legal native partial collision.
No polynomial or finite-support assumption is imposed on P. -/
theorem innerCollision_coeff {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (x a b : ℕ) :
    MvPowerSeries.coeff (index3 x a b) (innerCollision P) =
      ∑ j ∈ Finset.range (b + 1),
        ((a + j).choose a : ℂ) •
          MvPowerSeries.coeff (index3 x (a + j) (b - j)) P := by
  classical
  rw [innerCollision, MvPowerSeries.coeff_subst (inner_hasSubst R)]
  let indices := (Finset.range (b + 1)).image (fun j => index3 x (a + j) (b - j))
  rw [finsum_eq_sum_of_support_subset (s := indices)]
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      have hjb : j ≤ b := by simpa using Finset.mem_range.mp hj
      rw [inner_monomial_coeff]
      have cond : (index3 x (a + j) (b - j)) 0 = x ∧
          (index3 x (a + j) (b - j)) 2 ≤ b ∧
          (index3 x (a + j) (b - j)) 1 =
            a + (b - (index3 x (a + j) (b - j)) 2) := by
        simp only [index3, Finsupp.add_apply, Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne (by decide : (0 : Fin 3) ≠ 1),
          Finsupp.single_eq_of_ne (by decide : (0 : Fin 3) ≠ 2),
          Finsupp.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 0),
          Finsupp.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 2),
          Finsupp.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0),
          Finsupp.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 1), add_zero, zero_add]
        exact ⟨by trivial, by omega, by omega⟩
      rw [ite_eq_left cond]
      simp [index3, Algebra.smul_def, smul_eq_mul, map_natCast, mul_comm]
    · intro i hi j hj h
      have h1 := congrArg (fun d : Fin 3 →₀ ℕ => d 1) h
      simp [index3] at h1
      omega
  · intro d hd
    rw [Function.mem_support, ne_eq] at hd
    have conditions : d 0 = x ∧ d 2 ≤ b ∧ d 1 = a + (b - d 2) := by
      by_contra h
      apply hd
      rw [inner_monomial_coeff, ite_eq_right h, Nat.cast_zero, smul_zero]
    refine Finset.mem_image.mpr ⟨b - d 2, Finset.mem_range.mpr (by omega), ?_⟩
    ext i
    fin_cases i
    · simpa [index3] using conditions.1.symm
    · simpa [index3] using conditions.2.2.symm
    · simpa [index3] using Nat.sub_sub_self conditions.2.1

/-- Signed coefficient form, including zero in every below-support region.
This identifies the native three-variable collision with the already proved
bivariate collision on each fixed spectator slice. -/
theorem innerCollision_signed {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (x a b : ℤ) :
    signedExtend (innerCollision P) ![x, a, b] =
      extend (collision (slice P x)) a b := by
  classical
  by_cases hx : 0 ≤ x
  · by_cases ha : 0 ≤ a
    · by_cases hb : 0 ≤ b
      · have h : ∀ i : Fin 3, 0 ≤ (![x, a, b] : Fin 3 → ℤ) i := by
          intro i; fin_cases i <;> assumption
        have idx : signedIndex (![x, a, b] : Fin 3 → ℤ) =
            index3 x.toNat a.toNat b.toNat := by
          ext i
          fin_cases i <;> simp [signedIndex, index3]
        rw [signedExtend, ite_eq_left h, idx]
        change MvPowerSeries.coeff (index3 x.toNat a.toNat b.toNat) (innerCollision P) = _
        rw [innerCollision_coeff, extend, ite_eq_left ⟨ha, hb⟩, collision_coeff]
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        simp only [MvPowerSeries.coeff_apply, slice, powerIndex, Finsupp.add_apply,
          Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
          Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), add_zero, zero_add]
        change P (index3 x.toNat (a.toNat + j) (b.toNat - j)) =
          signedExtend P ![x, (a.toNat + j : ℕ), (b.toNat - j : ℕ)]
        have hn : ∀ i : Fin 3,
            0 ≤ (![x, ((a.toNat + j : ℕ) : ℤ), ((b.toNat - j : ℕ) : ℤ)] : Fin 3 → ℤ) i := by
          intro i
          fin_cases i
          · exact hx
          · exact Int.natCast_nonneg _
          · exact Int.natCast_nonneg _
        rw [signedExtend, ite_eq_left hn]
        congr 1
        ext i
        fin_cases i <;> simp [index3, signedIndex] <;> omega
      · have h : ¬ ∀ i : Fin 3, 0 ≤ (![x, a, b] : Fin 3 → ℤ) i := by
          intro h; exact hb (h 2)
        simp [signedExtend, extend, hb, h]
    · have h : ¬ ∀ i : Fin 3, 0 ≤ (![x, a, b] : Fin 3 → ℤ) i := by
        intro h; exact ha (h 1)
      simp [signedExtend, extend, ha, h]
  · have hs : slice P x = 0 := by
      funext d
      have h : ¬ ∀ i : Fin 3,
          0 ≤ (![x, (d 0 : ℤ), (d 1 : ℤ)] : Fin 3 → ℤ) i := by
        intro h; exact hx (h 0)
      change signedExtend P ![x, (d 0 : ℤ), (d 1 : ℤ)] = 0
      simp [signedExtend, h]
    have h : ¬ ∀ i : Fin 3, 0 ≤ (![x, a, b] : Fin 3 → ℤ) i := by
      intro h; exact hx (h 0)
    have hz : collision (0 : MvPowerSeries (Fin 2) R) = 0 := by
      ext d
      have hd : d = powerIndex (d 0) (d 1) := by
        ext i
        fin_cases i <;> simp [powerIndex]
      rw [hd, collision_coeff]
      simp
    simp [signedExtend, h, hs, hz, extend]

#print axioms signed_cleared_collision
#print axioms innerCollision_signed

end
end D5.S3.VertexAlgebra.SupportedThreeFieldCollision
