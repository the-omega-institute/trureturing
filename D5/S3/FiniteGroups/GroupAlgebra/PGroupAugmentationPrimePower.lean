/- GID: D5/S3/FiniteGroups/GroupAlgebra/PGroupAugmentationPrimePower
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/PGroupAugmentationPrimePower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.PGroup]
   utility: none
   digest: Quantitative augmentation nilpotence over coefficients with nilpotent p. -/

import D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentation
import Mathlib.Algebra.CharP.Basic

/-!
Coefficient reduction identifies the scalar principal ideal as its kernel.
Split augmentation gives I ∩ pA = pI, and the resulting filtration propagates
I^(k*(|G|-1)+1) ≤ (pA)^k I. The split-filtration argument follows the supplied
GPT Pro derivation; no literature novelty or historical priority is claimed.

The characteristic-p theorem and power-transport helper are imported from the
canonical module and used directly.
No semiring structure on all left ideals of a noncommutative ring is assumed.
-/

namespace D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentationPrimePower

open MonoidAlgebra
open scoped BigOperators

universe u v
variable {R : Type u} {G : Type v} [CommRing R] [Group G]

/-- Coefficient reduction has exactly the scalar principal ideal as its kernel.
The coefficient decomposition works without finiteness of the group. -/
private theorem coefficient_reduction_kernel (t : R) :
    RingHom.ker (mapRingHom G (Ideal.Quotient.mk (Ideal.span ({t} : Set R)))) =
      Ideal.span {single (1 : G) t} := by
  classical
  let P : Ideal R := Ideal.span {t}
  let rho : MonoidAlgebra R G →+* MonoidAlgebra (R ⧸ P) G :=
    mapRingHom G (Ideal.Quotient.mk P)
  apply le_antisymm
  · intro x hx
    have hcoeff : ∀ g, x.coeff g ∈ P := by
      intro g
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have h := congrArg (fun y : MonoidAlgebra (R ⧸ P) G => y.coeff g)
        (show rho x = 0 from hx)
      simpa only [rho, coeff_mapRingHom, coeff_zero, Finsupp.zero_apply] using h
    rw [← sum_coeff_single x]
    apply Submodule.sum_mem
    intro g _hg
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hcoeff g)
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨single g c, ?_⟩
    rw [single_mul_single, mul_one, hc]
  · apply Ideal.span_le.mpr
    rintro x (rfl : x = single (1 : G) t)
    change mapRingHom G (Ideal.Quotient.mk P) (single (1 : G) t) = 0
    rw [mapRingHom_single]
    have ht : Ideal.Quotient.mk P t = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
    rw [ht, single_zero]

/-- The section `r ↦ single 1 r` splits augmentation. Subtracting the section
of the augmentation of a multiplier proves the intersection identity even
when the scalar is a zero divisor. In particular, no scalar is cancelled. -/
private theorem augmentation_inf_scalar (t : R) :
    let I : Ideal (MonoidAlgebra R G) :=
      RingHom.ker (MonoidAlgebra.lift R R G (1 : G →* R)).toRingHom
    let J : Ideal (MonoidAlgebra R G) := Ideal.span {single (1 : G) t}
    I ⊓ J = J * I := by
  classical
  let eps := (MonoidAlgebra.lift R R G (1 : G →* R)).toRingHom
  let q : MonoidAlgebra R G := single (1 : G) t
  let I : Ideal (MonoidAlgebra R G) := RingHom.ker eps
  let J : Ideal (MonoidAlgebra R G) := Ideal.span {q}
  change I ⊓ J = J * I
  have hker : RingHom.ker
      (mapRingHom G (Ideal.Quotient.mk (Ideal.span ({t} : Set R)))) = J :=
    coefficient_reduction_kernel t
  letI : J.IsTwoSided := by
    rw [← hker]
    infer_instance
  have hsection (r : R) : eps (single (1 : G) r) = r := by
    simp [eps]
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hy.2
    have hqx : q * x = y := by
      rw [show q * x = x * q from single_one_comm t x]
      exact hx
    have htx : t * eps x = 0 := by
      have h := congrArg eps hqx
      rw [map_mul, show eps q = t from hsection t,
        show eps y = 0 from hy.1] at h
      exact h
    let z : MonoidAlgebra R G := x - single (1 : G) (eps x)
    have hz : z ∈ I := by
      change eps (x - single (1 : G) (eps x)) = 0
      rw [map_sub, hsection, sub_self]
    have hqz : q * z = y := by
      have hqsection : q * single (1 : G) (eps x) = 0 := by
        change single (1 : G) t * single (1 : G) (eps x) = 0
        rw [single_mul_single, one_mul, htx, single_zero]
      change q * (x - single (1 : G) (eps x)) = y
      rw [mul_sub, hqx, hqsection, sub_zero]
    rw [← hqz]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self q) hz
  · exact le_inf Ideal.mul_le_right Ideal.mul_le_left

/-- A two-sided ideal with `I^n ≤ J*I` gains one factor of `J` every `n-1`
steps. This also covers `n = 1`, without a separate trivial-group assumption. -/
private theorem pow_pred_filtration {A : Type*} [Ring A]
    (I J : Ideal A) [I.IsTwoSided] [J.IsTwoSided] (n : ℕ) (hn : 0 < n)
    (h : I ^ n ≤ J * I) (k : ℕ) : I ^ (k * (n - 1) + 1) ≤ J ^ k * I := by
  have hn' : 1 + (n - 1) = n := by omega
  have hprod : I * I ^ (n - 1) = I ^ n := by
    calc
      I * I ^ (n - 1) = I ^ (1 + (n - 1)) := by
        rw [Ideal.IsTwoSided.pow_add, Submodule.pow_one]
      _ = I ^ n := by rw [hn']
  induction k with
  | zero =>
    simp only [Nat.zero_mul, zero_add, Submodule.pow_one, Submodule.pow_zero,
      Ideal.one_eq_top, Ideal.top_mul, le_refl]
  | succ k ih =>
    have hexp : (k + 1) * (n - 1) + 1 = (k * (n - 1) + 1) + (n - 1) := by
      rw [Nat.succ_mul]
      omega
    calc
      I ^ ((k + 1) * (n - 1) + 1) = I ^ (k * (n - 1) + 1) * I ^ (n - 1) := by
        rw [hexp, Ideal.IsTwoSided.pow_add]
      _ ≤ (J ^ k * I) * I ^ (n - 1) := Ideal.mul_mono_left ih
      _ = J ^ k * I ^ n := by rw [Ideal.mul_assoc, hprod]
      _ ≤ J ^ k * (J * I) := Ideal.mul_mono_right h
      _ = J ^ (k + 1) * I := by rw [← Ideal.mul_assoc, ← Submodule.pow_succ]

/-- If the scalar `p` has vanishing `a`-th power, the augmentation ideal of a
finite, possibly nonabelian `p`-group vanishes at power `a * (Nat.card G - 1) + 1`.
The coefficient ring can be the zero ring; coefficient and group universes
are independent. The bound is sufficient, with no minimality assertion. -/
theorem augmentation_ideal_pow_pred_card (p a : ℕ) [Fact p.Prime] [Finite G]
    (ha : 0 < a) (hp : (p : R) ^ a = 0) (hG : IsPGroup p G) :
    (RingHom.ker (MonoidAlgebra.lift R R G (1 : G →* R)).toRingHom) ^
      (a * (Nat.card G - 1) + 1) = ⊥ := by
  classical
  let I : Ideal (MonoidAlgebra R G) :=
    RingHom.ker (MonoidAlgebra.lift R R G (1 : G →* R)).toRingHom
  change I ^ (a * (Nat.card G - 1) + 1) = ⊥
  by_cases hs : Subsingleton R
  · letI := hs
    have hI : I = ⊥ := by
      apply le_antisymm _ bot_le
      intro x _hx
      change x = 0
      exact Subsingleton.elim x 0
    rw [hI]
    exact Ideal.bot_pow (Nat.succ_ne_zero _)
  · letI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hs
    let P : Ideal R := Ideal.span {(p : R)}
    have hP : P ≠ ⊤ := by
      intro htop
      have h1 : (1 : R) ∈ P := by
        rw [htop]
        exact Submodule.mem_top
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
      have hzero : (1 : R) = 0 := calc
        (1 : R) = (c * (p : R)) ^ a := by rw [hc, one_pow]
        _ = c ^ a * (p : R) ^ a := mul_pow _ _ _
        _ = 0 := by rw [hp, mul_zero]
      exact one_ne_zero hzero
    letI : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
    have hpQ : (p : R ⧸ P) = 0 := by
      have h : Ideal.Quotient.mk P (p : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : R))
      simpa only [map_natCast] using h
    letI : CharP (R ⧸ P) p :=
      (CharP.charP_iff_prime_eq_zero (R := R ⧸ P) (Fact.out : p.Prime)).mpr hpQ
    let rho : MonoidAlgebra R G →+* MonoidAlgebra (R ⧸ P) G :=
      mapRingHom G (Ideal.Quotient.mk P)
    let Ibar : Ideal (MonoidAlgebra (R ⧸ P) G) :=
      RingHom.ker (MonoidAlgebra.lift (R ⧸ P) (R ⧸ P) G
        (1 : G →* (R ⧸ P))).toRingHom
    let J : Ideal (MonoidAlgebra R G) := Ideal.span {single (1 : G) (p : R)}
    have hker : RingHom.ker rho = J := coefficient_reduction_kernel (p : R)
    letI : J.IsTwoSided := by
      rw [← hker]
      infer_instance
    have haug : ∀ x : MonoidAlgebra R G,
        MonoidAlgebra.lift (R ⧸ P) (R ⧸ P) G (1 : G →* (R ⧸ P)) (rho x) =
          Ideal.Quotient.mk P (MonoidAlgebra.lift R R G (1 : G →* R) x) := by
      intro x
      induction x using MonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | single g r => simp [rho]
    have hle : I ≤ Ibar.comap rho := by
      intro x hx
      change MonoidAlgebra.lift (R ⧸ P) (R ⧸ P) G
        (1 : G →* (R ⧸ P)) (rho x) = 0
      rw [haug x, show MonoidAlgebra.lift R R G (1 : G →* R) x = 0 from hx, map_zero]
    have hmod : Ibar ^ Nat.card G = ⊥ :=
      PGroupAugmentation.augmentation_ideal_pow_card (R := R ⧸ P) p hG
    have hpower : I ^ Nat.card G ≤ J := by
      have h := PGroupAugmentation.pow_le_comap rho I Ibar hle (Nat.card G)
      rw [hmod] at h
      change I ^ Nat.card G ≤ RingHom.ker rho at h
      exact h.trans hker.le
    have hsplit : I ⊓ J = J * I := augmentation_inf_scalar (p : R)
    have hstep : I ^ Nat.card G ≤ J * I := by
      rw [← hsplit]
      exact le_inf (Ideal.pow_le_self (Nat.ne_of_gt Nat.card_pos)) hpower
    have hscalar : (single (1 : G) (p : R)) ^ a = 0 := by
      change (singleOneRingHom (R := R) (M := G) (p : R)) ^ a = 0
      rw [← map_pow, hp, map_zero]
    have hJ : J ^ a = ⊥ := by
      change (Ideal.span {single (1 : G) (p : R)}) ^ a = ⊥
      rw [Ideal.span_singleton_pow, hscalar, Ideal.span_singleton_zero]
    apply le_antisymm _ bot_le
    calc
      I ^ (a * (Nat.card G - 1) + 1) ≤ J ^ a * I :=
        pow_pred_filtration I J (Nat.card G) Nat.card_pos hstep a
      _ = ⊥ := by rw [hJ, Ideal.bot_mul]

end D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentationPrimePower
