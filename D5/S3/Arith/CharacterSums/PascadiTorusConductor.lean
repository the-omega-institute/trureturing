/- GID: D5/S3/Arith/CharacterSums/PascadiTorusConductor
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiTorusConductor
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: The prime-cube quadratic torus word has an exact primitive character decomposition. -/

module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Ideal.Maps

/-! Quadratic unitary reduction and the cubic character conductor decomposition. -/

public section

namespace D5.S3.Arith.CharacterSums.PascadiTorusConductor

open QuadraticAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]

def reduce (f : R →+* S) (a b : R) :
    unitary (QuadraticAlgebra R a b) →*
      unitary (QuadraticAlgebra S (f a) (f b)) :=
  (Unitary.map
    { toMonoidHom := (QuadraticAlgebra.mapRingHom f a b).toMonoidHom
      map_star' := QuadraticAlgebra.mapRingHom_star f a b }).toMonoidHom

theorem reduce_surjective_of_square_zero
    (f : R →+* S) (a b : R) (hf : Function.Surjective f)
    (half : R) (hhalf : (2 : R) * half = 1)
    (hsquare : ∀ r : R, f r = 0 → r * r = 0) :
    Function.Surjective (reduce f a b) := by
  intro y
  obtain ⟨z, hz⟩ := QuadraticAlgebra.mapRingHom_surjective f a b hf y.val
  let r := z.norm - 1
  have hry : f r = 0 := by
    simp only [r, map_sub, map_one]
    rw [← QuadraticAlgebra.norm_mapRingHom, hz, QuadraticAlgebra.norm_eq_one y.property,
      sub_self]
  have hrs := hsquare r hry
  let c : R := 1 - half * r
  have hfc : f c = 1 := by simp [c, hry]
  have hc : c ^ 2 = 1 - r := by
    calc
      c ^ 2 = 1 - (2 * half) * r + half ^ 2 * (r * r) := by dsimp [c]; ring
      _ = 1 - r := by rw [hhalf, hrs]; ring
  let x := z * algebraMap R (QuadraticAlgebra R a b) c
  have hx : x.norm = 1 := by
    dsimp [x]
    rw [map_mul, QuadraticAlgebra.norm_algebraMap, hc]
    calc
      z.norm * (1 - r) = (1 + r) * (1 - r) := by dsimp [r]; ring
      _ = 1 - r * r := by ring
      _ = 1 := by rw [hrs, sub_zero]
  refine ⟨⟨x, QuadraticAlgebra.mem_unitary hx⟩, Subtype.ext ?_⟩
  change QuadraticAlgebra.mapRingHom f a b x = y.val
  have hscalar : QuadraticAlgebra.mapRingHom f a b
      (algebraMap R (QuadraticAlgebra R a b) c) = 1 := by
    ext <;> simp [hfc]
  dsimp [x]
  rw [map_mul, hz, hscalar, mul_one]

theorem kernel_re_eq_one_of_square_zero
    (f : R →+* S) (a : R) (half : R) (hhalf : (2 : R) * half = 1)
    (hsquare : ∀ r : R, f r = 0 → r * r = 0)
    (x : QuadraticAlgebra R a 0) (hx : x.norm = 1)
    (hre : f x.re = 1) (him : f x.im = 0) : x.re = 1 := by
  let r := x.re - 1
  have hr : f r = 0 := by simp [r, hre]
  have hrs := hsquare r hr
  have hiss := hsquare x.im him
  have hnorm : x.norm = 1 + 2 * r := by
    rw [QuadraticAlgebra.norm_def]
    calc
      x.re * x.re + 0 * x.re * x.im - a * x.im * x.im =
          1 + 2 * r + r * r - a * (x.im * x.im) := by dsimp [r]; ring
      _ = 1 + 2 * r := by rw [hrs, hiss]; ring
  have hzero : 2 * r = 0 := by
    rw [hx] at hnorm
    apply add_left_cancel (a := (1 : R))
    simpa using hnorm.symm
  have hr0 : r = 0 := by
    calc
      r = half * (2 * r) := by rw [← mul_assoc, mul_comm half (2 : R), hhalf, one_mul]
      _ = 0 := by rw [hzero, mul_zero]
  exact sub_eq_zero.mp hr0

def kernelEquiv
    (f : R →+* S) (a : R) (half : R) (hhalf : (2 : R) * half = 1)
    (hproduct : ∀ r s : R, f r = 0 → f s = 0 → r * s = 0) :
    Multiplicative (RingHom.ker f) ≃* MonoidHom.ker (reduce f a 0) := by
  let encode : RingHom.ker f → MonoidHom.ker (reduce f a 0) := fun b ↦ by
    have hfb : f (b : R) = 0 := RingHom.mem_ker.mp b.property
    let x : QuadraticAlgebra R a 0 := ⟨1, b⟩
    have hnorm : x.norm = 1 := by
      simp [x, QuadraticAlgebra.norm_def, mul_assoc, hproduct b b hfb hfb]
    let u : unitary (QuadraticAlgebra R a 0) := ⟨x, QuadraticAlgebra.mem_unitary hnorm⟩
    refine ⟨u, MonoidHom.mem_ker.mpr (Subtype.ext ?_)⟩
    change QuadraticAlgebra.mapRingHom f a 0 x = 1
    ext <;> simp [x, hfb]
  have hmap (x : MonoidHom.ker (reduce f a 0)) :
      QuadraticAlgebra.mapRingHom f a 0 x.val.val = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp x.property)
  have him (x : MonoidHom.ker (reduce f a 0)) : f x.val.val.im = 0 :=
    congrArg QuadraticAlgebra.im (hmap x)
  have hre (x : MonoidHom.ker (reduce f a 0)) : f x.val.val.re = 1 :=
    congrArg QuadraticAlgebra.re (hmap x)
  let decode : MonoidHom.ker (reduce f a 0) → RingHom.ker f :=
    fun x ↦ ⟨x.val.val.im, RingHom.mem_ker.mpr (him x)⟩
  refine
    { toFun := fun b ↦ encode b.toAdd
      invFun := fun x ↦ Multiplicative.ofAdd (decode x)
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · intro b
    rfl
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    apply QuadraticAlgebra.ext
    · exact (kernel_re_eq_one_of_square_zero f a half hhalf
        (fun r hr ↦ hproduct r r hr hr) x.val.val
        (QuadraticAlgebra.norm_eq_one x.val.property) (hre x) (him x)).symm
    · rfl
  · intro b c
    have hb : f (b.toAdd : R) = 0 := RingHom.mem_ker.mp b.toAdd.property
    have hc : f (c.toAdd : R) = 0 := RingHom.mem_ker.mp c.toAdd.property
    apply Subtype.ext
    apply Subtype.ext
    change (⟨1, (b.toAdd : R) + (c.toAdd : R)⟩ : QuadraticAlgebra R a 0) =
      ⟨1, b.toAdd⟩ * ⟨1, c.toAdd⟩
    ext <;> simp [mul_assoc, hproduct b.toAdd c.toAdd hb hc, add_comm]

section PrimeCube

variable (p : ℕ)

def reduceDigits : ZMod (p ^ 3) →+* ZMod (p ^ 2) :=
  ZMod.castHom (by exact pow_dvd_pow p (by decide : 2 ≤ 3)) _

theorem reduceDigits_surjective : Function.Surjective (reduceDigits p) :=
  ZMod.castHom_surjective _

variable [Fact p.Prime]

private instance cubeNeZero : NeZero (p ^ 3) :=
  ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

theorem reduceDigits_ker_mul (x y : ZMod (p ^ 3))
    (hx : reduceDigits p x = 0) (hy : reduceDigits p y = 0) : x * y = 0 := by
  have hxval : p ^ 2 ∣ x.val := by
    have h : ((x.val : ℕ) : ZMod (p ^ 2)) = 0 := by
      rw [← map_natCast (reduceDigits p), ZMod.natCast_zmod_val, hx]
    exact (ZMod.natCast_eq_zero_iff _ _).mp h
  have hyval : p ^ 2 ∣ y.val := by
    have h : ((y.val : ℕ) : ZMod (p ^ 2)) = 0 := by
      rw [← map_natCast (reduceDigits p), ZMod.natCast_zmod_val, hy]
    exact (ZMod.natCast_eq_zero_iff _ _).mp h
  have hdiv : p ^ 3 ∣ x.val * y.val := by
    have h4 : p ^ 4 ∣ x.val * y.val := by
      rw [show p ^ 4 = p ^ 2 * p ^ 2 by ring]
      exact Nat.mul_dvd_mul hxval hyval
    exact (pow_dvd_pow p (by decide : 3 ≤ 4)).trans h4
  rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, ← Nat.cast_mul]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hdiv

theorem reduceDigits_card_ker : Nat.card (RingHom.ker (reduceDigits p)) = p := by
  let f := (reduceDigits p).toAddMonoidHom
  let e : RingHom.ker (reduceDigits p) ≃ f.ker :=
    Equiv.subtypeEquivRight fun _ ↦ by
      rw [RingHom.mem_ker, AddMonoidHom.mem_ker]
      rfl
  have hf : Function.Surjective f := reduceDigits_surjective p
  have h := AddSubgroup.card_ker_mul_card_of_surjective (f := f) hf
  rw [Nat.card_zmod, Nat.card_zmod] at h
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have heq : Nat.card f.ker * p ^ 2 = p * p ^ 2 := h.trans (by ring)
  exact (Nat.card_congr e).trans (Nat.eq_of_mul_eq_mul_right (pow_pos hp _) heq)

theorem primeCube_two_inverse (hp : 2 < p) : ∃ half : ZMod (p ^ 3), 2 * half = 1 := by
  have h : ¬ p ∣ 2 := fun h ↦ (Nat.not_le_of_gt hp) (Nat.le_of_dvd (by decide) h)
  obtain ⟨u, hu⟩ := (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime)
    (by decide : 0 < 3)).mpr h
  exact ⟨(↑u⁻¹), u.mul_inv_of_eq (by simpa using hu)⟩

theorem primeCube_reduce_surjective (hp : 2 < p) (a : ZMod (p ^ 3)) :
    Function.Surjective (reduce (reduceDigits p) a 0) := by
  obtain ⟨half, hhalf⟩ := primeCube_two_inverse p hp
  exact reduce_surjective_of_square_zero _ a 0 (reduceDigits_surjective p) half hhalf
    (fun x hx ↦ reduceDigits_ker_mul p x x hx hx)

theorem primeCube_unitary_card_ker (hp : 2 < p) (a : ZMod (p ^ 3)) :
    Nat.card (MonoidHom.ker (reduce (reduceDigits p) a 0)) = p := by
  obtain ⟨half, hhalf⟩ := primeCube_two_inverse p hp
  let e := kernelEquiv (reduceDigits p) a half hhalf (reduceDigits_ker_mul p)
  exact (Nat.card_congr e.toEquiv).symm.trans (reduceDigits_card_ker p)

end PrimeCube

section CayleyWord

private def plusFactor (d x : R) : QuadraticAlgebra R (-d) 0 := ⟨1, x⟩

private def minusFactor (d x : R) : QuadraticAlgebra R (-d) 0 := ⟨1, -x⟩

private theorem norm_plusFactor (d x : R) : (plusFactor d x).norm = 1 + d * x ^ 2 := by
  simp [plusFactor, QuadraticAlgebra.norm_def, pow_two, mul_assoc]

private theorem norm_minusFactor (d x : R) : (minusFactor d x).norm = 1 + d * x ^ 2 := by
  simp [minusFactor, QuadraticAlgebra.norm_def, pow_two, mul_assoc]

private theorem minusFactor_isUnit (d x : R) (hx : IsUnit (1 + d * x ^ 2)) :
    IsUnit (minusFactor d x) := by
  apply QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
  rwa [norm_minusFactor]

noncomputable def cayley (d x : R) (hx : IsUnit (1 + d * x ^ 2)) :
    unitary (QuadraticAlgebra R (-d) 0) := by
  let u := (minusFactor_isUnit d x hx).unit
  have hu : (u : QuadraticAlgebra R (-d) 0) = minusFactor d x :=
    (minusFactor_isUnit d x hx).unit_spec
  refine ⟨plusFactor d x * (↑u⁻¹ : QuadraticAlgebra R (-d) 0),
    QuadraticAlgebra.mem_unitary ?_⟩
  rw [map_mul, norm_plusFactor, ← norm_minusFactor d x, ← hu, ← map_mul, Units.mul_inv,
    map_one]

private theorem cayley_mul_minusFactor (d x : R) (hx : IsUnit (1 + d * x ^ 2)) :
    (cayley d x hx).val * minusFactor d x = plusFactor d x := by
  let u := (minusFactor_isUnit d x hx).unit
  change plusFactor d x * (↑u⁻¹ : QuadraticAlgebra R (-d) 0) * minusFactor d x = plusFactor d x
  calc
    _ = plusFactor d x * (↑u⁻¹ : QuadraticAlgebra R (-d) 0) * ↑u :=
      congrArg (fun z ↦ plusFactor d x * (↑u⁻¹ : QuadraticAlgebra R (-d) 0) * z)
        (minusFactor_isUnit d x hx).unit_spec.symm
    _ = _ := by rw [mul_assoc, Units.inv_mul, mul_one]

theorem cayley_word_eq_one_iff (d x y z half : R) (hhalf : (2 : R) * half = 1)
    (hx : IsUnit (1 + d * x ^ 2)) (hy : IsUnit (1 + d * y ^ 2))
    (hz : IsUnit (1 + d * z ^ 2)) :
    cayley d x hx * cayley d y hy * cayley d z hz = 1 ↔ x + y + z = d * x * y * z := by
  let lhs := plusFactor d x * plusFactor d y * plusFactor d z
  let rhs := minusFactor d x * minusFactor d y * minusFactor d z
  have hrhs : IsUnit rhs := ((minusFactor_isUnit d x hx).mul
    (minusFactor_isUnit d y hy)).mul (minusFactor_isUnit d z hz)
  have hmul : (cayley d x hx * cayley d y hy * cayley d z hz).val * rhs = lhs := by
    change ((cayley d x hx).val * (cayley d y hy).val * (cayley d z hz).val) *
      (minusFactor d x * minusFactor d y * minusFactor d z) = lhs
    calc
      _ = ((cayley d x hx).val * minusFactor d x) *
          ((cayley d y hy).val * minusFactor d y) *
          ((cayley d z hz).val * minusFactor d z) := by ac_rfl
      _ = lhs := by simp only [cayley_mul_minusFactor, lhs]
  have hdiff : lhs - rhs = ⟨0, 2 * (x + y + z - d * x * y * z)⟩ := by
    ext <;> simp [lhs, rhs, plusFactor, minusFactor] <;> ring
  have hmul_iff : cayley d x hx * cayley d y hy * cayley d z hz = 1 ↔ lhs = rhs := by
    constructor
    · intro h
      rw [h] at hmul
      simpa using hmul.symm
    · intro h
      apply Subtype.ext
      apply hrhs.mul_right_cancel
      simpa [h] using hmul
  rw [hmul_iff]
  constructor
  · intro h
    rw [h, sub_self] at hdiff
    have hi : 2 * (x + y + z - d * x * y * z) = 0 :=
      (congrArg QuadraticAlgebra.im hdiff).symm
    apply sub_eq_zero.mp
    calc
      _ = half * (2 * (x + y + z - d * x * y * z)) := by
        rw [← mul_assoc, mul_comm half (2 : R), hhalf, one_mul]
      _ = 0 := by rw [hi, mul_zero]
  · intro h
    apply sub_eq_zero.mp
    rw [hdiff, h, sub_self, mul_zero]
    rfl

end CayleyWord

section CubicCharacterMoment

open scoped BigOperators

noncomputable section

variable {G H : Type*} [CommGroup G] [CommGroup H] [Fintype G] [Fintype H]

def wordMass (f : G →* H) (w : G → ℂ) : ℂ := by
  classical
  exact ∑ x : G, ∑ y : G, ∑ z : G,
    if f (x * y * z) = 1 then w x * w y * w z else 0

private theorem sum_cube_expand {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    (∑ i, a i) ^ 3 = ∑ i, ∑ j, ∑ k, a i * a j * a k := by
  symm
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [← Fintype.sum_mul_sum]
  ring

theorem pulledBackCubedSum_eq_wordMass (f : G →* H) (w : G → ℂ) :
    (∑ χ : AddChar (Additive H) ℂ, (∑ x : G, w x * χ (Additive.ofMul (f x))) ^ 3) =
      (Fintype.card H : ℂ) * wordMass f w := by
  classical
  unfold wordMass
  simp_rw [sum_cube_expand]
  rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  have hoff (χ : AddChar (Additive H) ℂ) :
      χ (Additive.ofMul (f (x * y * z))) =
        χ (Additive.ofMul (f x)) * χ (Additive.ofMul (f y)) * χ (Additive.ofMul (f z)) := by
    simp only [map_mul]
    change χ (Additive.ofMul (f x) + Additive.ofMul (f y) + Additive.ofMul (f z)) = _
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  calc
    _ = (w x * w y * w z) * ∑ χ : AddChar (Additive H) ℂ,
        χ (Additive.ofMul (f (x * y * z))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ ↦ ?_
      rw [hoff]
      ring
    _ = _ := by
      rw [AddChar.sum_apply_eq_ite]
      by_cases h : f (x * y * z) = 1
      · have h0 : Additive.ofMul (f (x * y * z)) = (0 : Additive H) := h
        rw [ite_eq_left h0, ite_eq_left h]
        rw [Fintype.card_congr (Additive.toMul : Additive H ≃ H)]
        ring
      · have h0 : Additive.ofMul (f (x * y * z)) ≠ (0 : Additive H) := h
        rw [ite_eq_right h0, ite_eq_right h, mul_zero, mul_zero]

theorem cubic_character_conductor_difference (f : G →* H) (w : G → ℂ) :
    (∑ χ : AddChar (Additive G) ℂ, (∑ x : G, w x * χ (Additive.ofMul x)) ^ 3) -
      (∑ χ : AddChar (Additive H) ℂ, (∑ x : G, w x * χ (Additive.ofMul (f x))) ^ 3) =
      (Fintype.card G : ℂ) * wordMass (MonoidHom.id G) w -
        (Fintype.card H : ℂ) * wordMass f w := by
  rw [← pulledBackCubedSum_eq_wordMass (MonoidHom.id G) w,
    ← pulledBackCubedSum_eq_wordMass f w]
  rfl

theorem wordMass_eq_conductor_split (f : G →* H) (hf : Function.Surjective f)
    (w : G → ℂ) :
    wordMass (MonoidHom.id G) w =
      wordMass f w / (Nat.card f.ker : ℂ) +
      ((∑ χ : AddChar (Additive G) ℂ, (∑ x : G, w x * χ (Additive.ofMul x)) ^ 3) -
       (∑ χ : AddChar (Additive H) ℂ, (∑ x : G, w x * χ (Additive.ofMul (f x))) ^ 3)) /
        (Fintype.card G : ℂ) := by
  have hcard := Subgroup.card_ker_mul_card_of_surjective (f := f) hf
  rw [Nat.card_eq_fintype_card (α := G), Nat.card_eq_fintype_card (α := H)] at hcard
  have hcards : (Nat.card f.ker : ℂ) * (Fintype.card H : ℂ) = Fintype.card G := by
    exact_mod_cast hcard
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hK : (Nat.card f.ker : ℂ) ≠ 0 := by
    intro he
    rw [he, zero_mul] at hcards
    exact hG hcards.symm
  rw [cubic_character_conductor_difference]
  field_simp
  linear_combination wordMass f w * hcards

end

end CubicCharacterMoment

section PrimeCubeMoment

open scoped BigOperators

variable (p : ℕ)

/-- The norm-one group in the quadratic algebra at the prime cube. -/
abbrev CubeTorus (a : ZMod (p ^ 3)) := unitary (QuadraticAlgebra (ZMod (p ^ 3)) a 0)

/-- The reduction of the same quadratic norm-one group at the prime square. -/
abbrev SquareTorus (a : ZMod (p ^ 3)) :=
  unitary (QuadraticAlgebra (ZMod (p ^ 2)) (reduceDigits p a) (reduceDigits p 0))

/-- The original prime-cube word mass is the relaxed mass divided by the kernel size,
plus the normalized difference of the two cubic character sums. -/
theorem primeCube_wordMass_conductor_split [Fact p.Prime] (hp : 2 < p)
    (a : ZMod (p ^ 3)) [Fintype (CubeTorus p a)] [Fintype (SquareTorus p a)]
    (w : CubeTorus p a → ℂ) :
    wordMass (MonoidHom.id (CubeTorus p a)) w =
      wordMass (reduce (reduceDigits p) a 0) w / (p : ℂ) +
      ((∑ χ : AddChar (Additive (CubeTorus p a)) ℂ,
        (∑ x : CubeTorus p a, w x * χ (Additive.ofMul x)) ^ 3) -
       (∑ χ : AddChar (Additive (SquareTorus p a)) ℂ,
        (∑ x : CubeTorus p a, w x * χ (Additive.ofMul (reduce (reduceDigits p) a 0 x))) ^ 3)) /
        (Fintype.card (CubeTorus p a) : ℂ) := by
  have h := wordMass_eq_conductor_split (reduce (reduceDigits p) a 0)
    (primeCube_reduce_surjective p hp a) w
  rw [primeCube_unitary_card_ker p hp a] at h
  exact h

end PrimeCubeMoment

end D5.S3.Arith.CharacterSums.PascadiTorusConductor
