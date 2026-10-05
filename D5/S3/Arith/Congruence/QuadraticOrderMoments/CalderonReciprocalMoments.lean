/- GID: D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Calderon's reciprocal moments for inert imaginary quadratic orders. -/
/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#13205; Proved)
Direct frozen dependencies:
D5/S3/Combinatorics/Parking/OperationalDynamics.orbitEquiv;
statement_id: sha256:bf8f1cce8b8f2869286843dd050c8db90b4f5169d6e4ec2c48f0e41f91913dc7.
Information-escape registration is paused under CLAUDE.md §3.9.
-/
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Rotate
import D5.S3.Combinatorics.Parking.OperationalDynamics

open Polynomial
open scoped BigOperators QuadraticAlgebra
open Fin.NatCast
namespace CalderonReciprocalMoments
noncomputable section
variable (p : ℕ) [Fact p.Prime] (T N : ℤ)

abbrev R := AdjoinRoot (X ^ 2 - C (T : ℤ_[p]) * X + C (N : ℤ_[p]))
def element (x y : ℕ) : R p T N := (x : R p T N) + (y : R p T N) *
  AdjoinRoot.root (X ^ 2 - C (T : ℤ_[p]) * X + C (N : ℤ_[p]))
def Admissible : Prop := 5 < p ∧ T ^ 2 - 4 * N < 0 ∧
  ¬ (p : ℤ) ∣ T ^ 2 - 4 * N ∧ legendreSym p (T ^ 2 - 4 * N) = -1
/-- The source's finite set of ring elements with positive coordinates. -/
def U (k : ℕ) : Finset (R p T N) := by
  classical
  exact ((Finset.Icc 1 (p ^ k) ×ˢ Finset.Icc 1 (p ^ k)).filter
    (fun z => ¬ (p ∣ z.1 ∧ p ∣ z.2))).image (fun z => element p T N z.1 z.2)
/-- `Ring.inverse z` is the underlying inverse of `hz.unit` when `hz : IsUnit z`. -/
def H1 (k : ℕ) : R p T N := ∑ z ∈ U p T N k, Ring.inverse z
def H2 (k : ℕ) : R p T N := ∑ z ∈ U p T N k, (Ring.inverse z) ^ 2

/-- Conjecture 6.3, including equations (6.1) and (6.3). -/
def claim : Prop := ∀ (p : ℕ) (hp : Fact p.Prime) (T N : ℤ),
  @Admissible p hp T N → ∀ k : ℕ, 1 ≤ k →
    @H1 p hp T N k ∈ Ideal.span {((p : @R p hp T N) ^ (2 * k))} ∧
    @H2 p hp T N k ∈ Ideal.span {((p : @R p hp T N) ^ k)}

private def rootToCoordinates {A : Type} [CommRing A] (T N : A) : AdjoinRoot (X ^ 2 - C T * X + C N) →ₐ[A] QuadraticAlgebra A (-N) T :=
  AdjoinRoot.liftAlgHom ((X ^ 2 - C T * X + C N)) (Algebra.ofId A (QuadraticAlgebra A (-N) T)) QuadraticAlgebra.omega (by
    simp [ pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap])

private def coordinatesToRoot {A : Type} [CommRing A] (T N : A) : QuadraticAlgebra A (-N) T →ₐ[A] AdjoinRoot (X ^ 2 - C T * X + C N) :=
  QuadraticAlgebra.lift ⟨AdjoinRoot.root ((X ^ 2 - C T * X + C N)), by
    have h := AdjoinRoot.mk_self (f := (X ^ 2 - C T * X + C N))
    change AdjoinRoot.root ((X ^ 2 - C T * X + C N)) ^ 2 -
      AdjoinRoot.of ((X ^ 2 - C T * X + C N)) T * AdjoinRoot.root ((X ^ 2 - C T * X + C N)) +
      AdjoinRoot.of ((X ^ 2 - C T * X + C N)) N = 0 at h
    simp only [Algebra.smul_def, mul_one, ← AdjoinRoot.algebraMap_eq, map_neg] at h ⊢
    linear_combination h⟩

private def coordinateEquiv {A : Type} [CommRing A] (T N : A) : AdjoinRoot (X ^ 2 - C T * X + C N) ≃ₐ[A] QuadraticAlgebra A (-N) T :=
  AlgEquiv.ofAlgHom (rootToCoordinates T N) (coordinatesToRoot T N)
    (by apply QuadraticAlgebra.algHom_ext; simp [rootToCoordinates, coordinatesToRoot])
    (by apply AdjoinRoot.algHom_ext; simp [rootToCoordinates, coordinatesToRoot])

private abbrev Grid (p : ℕ) (k : ℕ) := {z : Fin (p ^ k) × Fin (p ^ k) //
  ¬ (p ∣ z.1.val + 1 ∧ p ∣ z.2.val + 1)}

private def coordinateMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (T N : ℤ) :
    QuadraticAlgebra A (-(N : A)) (T : A) →+* QuadraticAlgebra B (-(N : B)) (T : B) := by
  exact {
  toFun z := ⟨f z.re, f z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by change (⟨f 1, f 0⟩ : QuadraticAlgebra B (-(N : B)) (T : B)) = ⟨1,0⟩; simp
  map_add' z w := by ext <;> simp
  map_mul' z w := by ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  }

private abbrev Level (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) := QuadraticAlgebra (ZMod (p ^ k)) (-(N : ZMod (p ^ k))) (T : ZMod (p ^ k))

private def reduceRing (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) : R p T N →+* Level p T N k :=
  (coordinateMap (PadicInt.toZModPow k) T N).comp
    (coordinateEquiv (T : ℤ_[p]) (N : ℤ_[p])).toRingHom

private abbrev ScalarU (p : ℕ) [Fact p.Prime] (k : ℕ) := {a : Fin (p ^ k) // ¬ p ∣ a.val + 1}

private def scalarPadicUnit (p : ℕ) [Fact p.Prime] (k : ℕ) (a : ScalarU p k) : ℤ_[p]ˣ := by
  have padic_isUnit_iff (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) :
      IsUnit a ↔ PadicInt.toZMod a ≠ 0 := by
    rw [PadicInt.toZMod_eq_residueField_comp_residue]
    change IsUnit a ↔ PadicInt.residueField ((IsLocalRing.residue ℤ_[p]) a) ≠ 0
    rw [_root_.map_ne_zero, IsLocalRing.residue_ne_zero_iff_isUnit]
  exact (show IsUnit ((a.val.val + 1 : ℕ) : ℤ_[p]) from by
    rw [padic_isUnit_iff p]
    simpa only [map_natCast, ne_eq, ZMod.natCast_eq_zero_iff] using a.property).unit

private def S (p : ℕ) [Fact p.Prime] (k : ℕ) : ℤ_[p] := ∑ a : ScalarU p k, (((scalarPadicUnit p k a)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ^ 2

private def scalarUnit (p : ℕ) [Fact p.Prime] (k : ℕ) (T N : ℤ) (a : ScalarU p k) : (R p T N)ˣ :=
  Units.map (algebraMap ℤ_[p] (R p T N)).toMonoidHom (scalarPadicUnit p k a)

private def tau (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k) : Grid p k ≃ Grid p k := by
  have reflection_dvd (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k) (i : Fin (p ^ k)) :
      p ∣ (((Fin.revPerm (n := p ^ k)).trans (finRotate (p ^ k)).symm) i).val + 1 ↔ p ∣ i.val + 1 := by
    have reflection_nat (q : ℕ) (i : Fin q) :
        (((Fin.revPerm (n := q)).trans (finRotate q).symm) i).val + 1 = if i.val + 1 = q then q else q - (i.val + 1) := by
      have := i.neZero
      change ((finRotate q).symm i.rev).val + 1 = _
      by_cases h : i.val + 1 = q
      · have hi : i.rev = 0 := by
          apply Fin.ext
          simp only [Fin.val_rev, Fin.val_zero]
          omega
        have heq : (finRotate q).symm i.rev = i := by
          apply (finRotate q).symm_apply_eq.mpr
          cases q with
          | zero => exact i.elim0
          | succ n =>
            have hilast : i = Fin.last n := by apply Fin.ext; simp only [Fin.val_last]; omega
            rw [hi, hilast, finRotate_last]
        rw [heq, if_pos h]
        exact h
      · have hi : i.rev ≠ 0 := by
          intro hz
          have hv := congrArg Fin.val hz
          simp only [Fin.val_rev, Fin.val_zero] at hv
          have := i.isLt
          omega
        rw [coe_finRotate_symm_of_ne_zero hi, if_neg h]
        simp only [Fin.val_rev]
        have := i.isLt
        omega
    have hpq : p ∣ p ^ k := by simpa using pow_dvd_pow p hk
    rw [reflection_nat]
    split_ifs with h
    · simp [h, hpq]
    · have hi := i.isLt
      constructor
      · intro hd
        have hsum : p ∣ (p ^ k - (i.val + 1)) + (i.val + 1) := by
          simpa [Nat.sub_add_cancel (by omega : i.val + 1 ≤ p ^ k)] using hpq
        exact (Nat.dvd_add_right hd).mp hsum
      · intro hd
        exact Nat.dvd_sub hpq hd
  exact (Equiv.prodCongr ((Fin.revPerm (n := p ^ k)).trans (finRotate (p ^ k)).symm) ((Fin.revPerm (n := p ^ k)).trans (finRotate (p ^ k)).symm)).subtypeEquiv (by
    intro z
    change ¬ (p ∣ z.1.val + 1 ∧ p ∣ z.2.val + 1) ↔
      ¬ (p ∣ (((Fin.revPerm (n := p ^ k)).trans (finRotate (p ^ k)).symm) z.1).val + 1 ∧ p ∣ (((Fin.revPerm (n := p ^ k)).trans (finRotate (p ^ k)).symm) z.2).val + 1)
    rw [reflection_dvd p k hk, reflection_dvd p k hk])

private def correction (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (z : Grid p k) : R p T N :=
  1 + AdjoinRoot.root (X ^ 2 - C (T : ℤ_[p]) * X + C (N : ℤ_[p])) + (if z.val.1.val + 1 = p ^ k then 1 else 0) +
    AdjoinRoot.root (X ^ 2 - C (T : ℤ_[p]) * X + C (N : ℤ_[p])) * (if z.val.2.val + 1 = p ^ k then 1 else 0)

private abbrev BoundaryX (p : ℕ) [Fact p.Prime] (k : ℕ) := {z : Grid p k // z.val.1.val + 1 = p ^ k}

private abbrev BoundaryY (p : ℕ) [Fact p.Prime] (k : ℕ) := {z : Grid p k // z.val.2.val + 1 = p ^ k}

private def boundaryXEquiv (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k) : BoundaryX p k ≃ ScalarU p k := by
  have lastCoord_value (p : ℕ) [Fact p.Prime] (k : ℕ) : ((Fin.cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p ^ k)))) (Fin.last (p ^ k - 1)))).val + 1 = p ^ k := by
    simp only [Fin.val_cast, Fin.val_last]
    have hpos := pow_pos (Fact.out : p.Prime).pos k
    omega
  exact {
  toFun z := ⟨z.val.val.2, by
    intro hy
    apply z.val.property
    exact ⟨by rw [z.property]; simpa using pow_dvd_pow p hk, hy⟩⟩
  invFun a := ⟨⟨((Fin.cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p ^ k)))) (Fin.last (p ^ k - 1))), a.val), by
    intro hpair
    exact a.property hpair.2⟩, lastCoord_value p k⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      change ((Fin.cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p ^ k)))) (Fin.last (p ^ k - 1)))).val = z.val.val.1.val
      have hlast := lastCoord_value p k
      have hz := z.property
      omega
    · rfl
  right_inv a := rfl
  }

private def boundaryYEquiv (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k) : BoundaryY p k ≃ ScalarU p k := by
  have lastCoord_value (p : ℕ) [Fact p.Prime] (k : ℕ) : ((Fin.cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p ^ k)))) (Fin.last (p ^ k - 1)))).val + 1 = p ^ k := by
    simp only [Fin.val_cast, Fin.val_last]
    have hpos := pow_pos (Fact.out : p.Prime).pos k
    omega
  exact {
  toFun z := ⟨z.val.val.1, by
    intro hx
    apply z.val.property
    exact ⟨hx, by rw [z.property]; simpa using pow_dvd_pow p hk⟩⟩
  invFun a := ⟨⟨(a.val, (Fin.cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p ^ k)))) (Fin.last (p ^ k - 1)))), by
    intro hpair
    exact a.property hpair.1⟩, lastCoord_value p k⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change ((Fin.cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p ^ k)))) (Fin.last (p ^ k - 1)))).val = z.val.val.2.val
      have hlast := lastCoord_value p k
      have hz := z.property
      omega
  right_inv a := rfl
  }

theorem result : claim := by
  classical
  have norm_nonzero  {F : Type} [Field F] (T N x y : F)
      (hD : ¬ IsSquare (T ^ 2 - 4 * N)) (hxy : x ≠ 0 ∨ y ≠ 0) :
      x ^ 2 + T * x * y + N * y ^ 2 ≠ 0 := by
    by_cases hy : y = 0
    · simpa only [hy, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
        ne_eq, pow_eq_zero_iff (by decide : 2 ≠ 0)] using hxy.resolve_right (not_ne_iff.mpr hy)
    · have hd : ∀ s : F, discrim (1 : F) T N ≠ s ^ 2 := by
        intro s hs
        apply hD
        refine ⟨s, ?_⟩
        simpa [discrim, pow_two] using hs
      have hn := quadratic_ne_zero_of_discrim_ne_sq hd (x / y)
      intro hz
      apply hn
      field_simp
      linear_combination hz
  have element_isUnit (p : ℕ) [Fact p.Prime] (T N : ℤ) (h : Admissible p T N) (x y : ℕ)
      (hxy : ¬ (p ∣ x ∧ p ∣ y)) : IsUnit (element p T N x y) := by
    have padic_isUnit_iff (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) :
        IsUnit a ↔ PadicInt.toZMod a ≠ 0 := by
      rw [PadicInt.toZMod_eq_residueField_comp_residue]
      change IsUnit a ↔ PadicInt.residueField ((IsLocalRing.residue ℤ_[p]) a) ≠ 0
      rw [_root_.map_ne_zero, IsLocalRing.residue_ne_zero_iff_isUnit]
    have coordinates_element (p : ℕ) [Fact p.Prime] (T N : ℤ) (x y : ℕ) :
        coordinateEquiv (T : ℤ_[p]) (N : ℤ_[p]) (element p T N x y) =
          (⟨(x : ℤ_[p]), (y : ℤ_[p])⟩ : QuadraticAlgebra ℤ_[p] (-(N : ℤ_[p])) (T : ℤ_[p])) := by
      ext <;> simp [coordinateEquiv, rootToCoordinates, element]
    have hD : ¬ IsSquare ((T : ZMod p) ^ 2 - 4 * (N : ZMod p)) := by
      simpa using (legendreSym.eq_neg_one_iff p).mp h.2.2.2
    have hpair : (x : ZMod p) ≠ 0 ∨ (y : ZMod p) ≠ 0 := by
      simpa only [ne_eq, ZMod.natCast_eq_zero_iff, not_and_or] using hxy
    have hn := norm_nonzero (T : ZMod p) (N : ZMod p) (x : ZMod p) (y : ZMod p) hD hpair
    have hu : IsUnit (⟨(x : ℤ_[p]), (y : ℤ_[p])⟩ : QuadraticAlgebra ℤ_[p] (-(N : ℤ_[p])) (T : ℤ_[p])) := by
      rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, padic_isUnit_iff]
      simpa [QuadraticAlgebra.norm_def, map_add, map_sub, map_mul, map_neg, map_natCast,
        map_intCast, pow_two, sub_neg_eq_add, mul_assoc] using hn
    have he := IsUnit.map (coordinateEquiv (T : ℤ_[p]) (N : ℤ_[p])).symm.toRingHom hu
    rw [← coordinates_element p T N x y] at he
    change IsUnit ((coordinateEquiv (T : ℤ_[p]) (N : ℤ_[p])).symm
      ((coordinateEquiv (T : ℤ_[p]) (N : ℤ_[p])) (element p T N x y))) at he
    simpa only [AlgEquiv.symm_apply_apply] using he
  let unitElement (p : ℕ) [Fact p.Prime] (T N : ℤ) (h : Admissible p T N) (k : ℕ) (z : Grid p k) : (R p T N)ˣ :=
    (element_isUnit p T N h (z.val.1.val + 1) (z.val.2.val + 1) z.property).unit
  have unitElement_val (p : ℕ) [Fact p.Prime] (T N : ℤ) (h : Admissible p T N) (k : ℕ) (z : Grid p k) :
      (unitElement p T N h k z : R p T N) =
        element p T N (z.val.1.val + 1) (z.val.2.val + 1) := IsUnit.unit_spec _
  clear_value unitElement
  let gridH1 (p : ℕ) [Fact p.Prime] (T N : ℤ) (h : Admissible p T N) (k : ℕ) : R p T N :=
    ∑ z : Grid p k, (((unitElement p T N h k z)⁻¹ : (R p T N)ˣ) : R p T N)
  let gridH2 (p : ℕ) [Fact p.Prime] (T N : ℤ) (h : Admissible p T N) (k : ℕ) : R p T N :=
    ∑ z : Grid p k, (((unitElement p T N h k z)⁻¹ : (R p T N)ˣ) : R p T N) ^ 2
  have unit_second_moment {R : Type} [CommRing R] [Fintype Rˣ] (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R)) :
      (∑ u : Rˣ, ((u⁻¹ : Rˣ) : R) ^ 2) = 0 := by
    classical
    obtain ⟨two, htwo⟩ := h2
    have hperm := Equiv.sum_comp (Equiv.mulLeft two) (fun u : Rˣ => (u : R) ^ 2)
    have hfour : (4 : R) * (∑ u : Rˣ, (u : R) ^ 2) = ∑ u : Rˣ, (u : R) ^ 2 := by
      simpa [Units.val_mul, mul_pow, htwo, ← Finset.mul_sum, show (2 : R) ^ 2 = 4 by ring] using hperm
    have hthree : (3 : R) * (∑ u : Rˣ, (u : R) ^ 2) = 0 := by
      linear_combination hfour
    have hsum : (∑ u : Rˣ, (u : R) ^ 2) = 0 := by
      obtain ⟨three, hthreeval⟩ := h3
      rw [← hthreeval] at hthree
      exact (Units.mul_right_inj three).mp (by simpa using hthree)
    have hi := Equiv.sum_comp (Equiv.inv Rˣ) (fun u : Rˣ => (u : R) ^ 2)
    exact hi.trans hsum
  have reduce_zero_iff (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (z : R p T N) :
      reduceRing p T N k z = 0 ↔ (p : R p T N) ^ k ∣ z := by
    let e := coordinateEquiv (T : ℤ_[p]) (N : ℤ_[p])
    have scalar : ∀ a : ℤ_[p], PadicInt.toZModPow k a = 0 ↔ (p : ℤ_[p]) ^ k ∣ a := by
      intro a
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    constructor
    · intro hz
      have hx : PadicInt.toZModPow k (e z).re = 0 := congrArg QuadraticAlgebra.re hz
      have hy : PadicInt.toZModPow k (e z).im = 0 := congrArg QuadraticAlgebra.im hz
      obtain ⟨a, ha⟩ := (scalar _).mp hx
      obtain ⟨b, hb⟩ := (scalar _).mp hy
      refine ⟨e.symm ⟨a,b⟩, ?_⟩
      apply e.injective
      simp only [map_mul, map_pow, map_natCast, AlgEquiv.apply_symm_apply]
      have hc : (p : QuadraticAlgebra ℤ_[p] (-(N : ℤ_[p])) (T : ℤ_[p])) ^ k =
          algebraMap ℤ_[p] (QuadraticAlgebra ℤ_[p] (-(N : ℤ_[p])) (T : ℤ_[p])) ((p : ℤ_[p]) ^ k) := by simp
      rw [hc]
      ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, zero_mul, mul_zero, add_zero, ha, hb]
    · rintro ⟨a, rfl⟩
      rw [map_mul, map_pow, map_natCast]
      have hz : (p : Level p T N k) ^ k = 0 := by
        have hs : (p : ZMod (p ^ k)) ^ k = 0 := by
          rw [← Nat.cast_pow, ZMod.natCast_self]
        have hs' := congrArg (algebraMap (ZMod (p ^ k)) (Level p T N k)) hs
        simpa only [map_pow, map_natCast, map_zero] using hs'
      rw [hz, zero_mul]
  have level_isUnit_iff (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (h : Admissible p T N) (hk : 1 ≤ k) (x y : ZMod (p ^ k)) :
      IsUnit (⟨x,y⟩ : Level p T N k) ↔
        ¬ (ZMod.castHom ((by simpa using pow_dvd_pow p hk : p ∣ p ^ k)) (ZMod p) x = 0 ∧
           ZMod.castHom ((by simpa using pow_dvd_pow p hk : p ∣ p ^ k)) (ZMod p) y = 0) := by
    have zmodPow_isUnit_iff (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k) (a : ZMod (p ^ k)) :
        IsUnit a ↔ ZMod.castHom ((by simpa using pow_dvd_pow p hk : p ∣ p ^ k)) (ZMod p) a ≠ 0 := by
      have hrep : (a.val : ZMod (p ^ k)) = a := ZMod.natCast_zmod_val a
      rw [← hrep, ZMod.isUnit_iff_coprime,
        Nat.coprime_pow_right_iff (by omega : 0 < k), Nat.coprime_comm,
        (Fact.out : p.Prime).coprime_iff_not_dvd]
      simp only [map_natCast, ne_eq, ZMod.natCast_eq_zero_iff]
    let f := ZMod.castHom ((by simpa using pow_dvd_pow p hk : p ∣ p ^ k)) (ZMod p)
    rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, zmodPow_isUnit_iff p k hk]
    have hD : ¬ IsSquare ((T : ZMod p) ^ 2 - 4 * (N : ZMod p)) := by
      simpa using (legendreSym.eq_neg_one_iff p).mp h.2.2.2
    simp only [QuadraticAlgebra.norm_def, map_add, map_mul, map_sub, map_neg, map_intCast,
      sub_neg_eq_add]
    constructor
    · intro hn hxy
      apply hn
      simp [hxy.1, hxy.2]
    · intro hxy
      have hn := norm_nonzero (T : ZMod p) (N : ZMod p) (f x) (f y) hD
        (by simpa only [not_and_or] using hxy)
      simpa only [f, pow_two, mul_assoc, neg_mul, sub_neg_eq_add] using hn
  let positiveCoordinates  (q : ℕ) [NeZero q] : Fin q ≃ ZMod q := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => exact D5.S3.Combinatorics.CircularTwoChoiceParkingBijection.orbitEquiv n 1
  have positiveEquiv_apply (q : ℕ) [NeZero q] (a : Fin q) :
      positiveCoordinates q a = (a.val + 1 : ℕ) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
      change (a + 1 : Fin (q + 1)) = (↑(a.val + 1) : Fin (q + 1))
      rw [Nat.cast_add, Nat.cast_one, Fin.cast_val_eq_self]
  clear_value positiveCoordinates
  let gridEquiv (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) : (Fin (p ^ k) × Fin (p ^ k)) ≃ Level p T N k :=
    (Equiv.prodCongr (positiveCoordinates (p ^ k)) (positiveCoordinates (p ^ k))).trans
      (QuadraticAlgebra.equivProd (-(N : ZMod (p ^ k))) (T : ZMod (p ^ k))).symm
  have gridEquiv_apply (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (z : Fin (p ^ k) × Fin (p ^ k)) :
      gridEquiv p T N k z = ⟨(z.1.val + 1 : ℕ), (z.2.val + 1 : ℕ)⟩ := by
    apply QuadraticAlgebra.ext
    · change positiveCoordinates (p ^ k) z.1 = _
      simpa only [Nat.cast_add, Nat.cast_one] using positiveEquiv_apply (p ^ k) z.1
    · change positiveCoordinates (p ^ k) z.2 = _
      simpa only [Nat.cast_add, Nat.cast_one] using positiveEquiv_apply (p ^ k) z.2
  clear_value gridEquiv
  let unitGridEquiv (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (h : Admissible p T N) (hk : 1 ≤ k) : Grid p k ≃ (Level p T N k)ˣ := by
    exact ((gridEquiv p T N k).subtypeEquiv (by
      intro z
      change ¬ (p ∣ z.1.val + 1 ∧ p ∣ z.2.val + 1) ↔ IsUnit (gridEquiv p T N k z)
      change ¬ (p ∣ z.1.val + 1 ∧ p ∣ z.2.val + 1) ↔ IsUnit (gridEquiv p T N k z)
      rw [gridEquiv_apply, level_isUnit_iff p T N k h hk]
      simp only [map_natCast, ZMod.natCast_eq_zero_iff])).trans
        (Submonoid.unitsTypeEquivIsUnitSubmonoid.symm.toEquiv)
  have unitGridEquiv_val (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ)
      (h : Admissible p T N) (hk : 1 ≤ k) (z : Grid p k) :
      (unitGridEquiv p T N k h hk z : Level p T N k) = gridEquiv p T N k z.val :=
    IsUnit.unit_spec _
  clear_value unitGridEquiv
  have H2_divisible (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (h : Admissible p T N) (hk : 1 ≤ k) :
      (p : R p T N) ^ k ∣ gridH2 p T N h k := by
    letI : Fintype (Level p T N k) := Fintype.ofEquiv _ (gridEquiv p T N k)
    have reduce_element (x y : ℕ) :
        reduceRing p T N k (element p T N x y) = ⟨(x : ZMod (p ^ k)), (y : ZMod (p ^ k))⟩ := by
      have coordinates_element :
          coordinateEquiv (T : ℤ_[p]) (N : ℤ_[p]) (element p T N x y) =
            (⟨(x : ℤ_[p]), (y : ℤ_[p])⟩ : QuadraticAlgebra ℤ_[p] (-(N : ℤ_[p])) (T : ℤ_[p])) := by
        ext <;> simp [coordinateEquiv, rootToCoordinates, element]
      simp [reduceRing, RingHom.comp_apply, coordinates_element]
      ext <;> simp [coordinateMap]
    have map_unitElement (z : Grid p k) :
        Units.map (reduceRing p T N k).toMonoidHom (unitElement p T N h k z) =
          unitGridEquiv p T N k h hk z := by
      apply Units.ext
      simp only [Units.coe_map, unitElement_val, unitGridEquiv_val, gridEquiv_apply]
      exact reduce_element _ _
    have small_level_isUnit (a : ℕ) (ha : 0 < a) (hap : a < p) :
        IsUnit (a : Level p T N k) := by
      have hu : IsUnit (a : ZMod (p ^ k)) := by
        rw [ZMod.isUnit_iff_coprime]
        apply Nat.Coprime.pow_right
        rw [Nat.coprime_comm, (Fact.out : p.Prime).coprime_iff_not_dvd]
        exact Nat.not_dvd_of_pos_of_lt ha hap
      simpa using hu.map (algebraMap (ZMod (p ^ k)) (Level p T N k))
    apply (reduce_zero_iff p T N k _).mp
    have hm := unit_second_moment
      (small_level_isUnit 2 (by omega) (by have := h.1; omega))
      (small_level_isUnit 3 (by omega) (by have := h.1; omega))
    unfold gridH2
    rw [map_sum]
    simp only [map_pow]
    have hx : ∀ z : Grid p k,
        reduceRing p T N k (((unitElement p T N h k z)⁻¹ : (R p T N)ˣ) : R p T N) =
        (((unitGridEquiv p T N k h hk z)⁻¹ : (Level p T N k)ˣ) : Level p T N k) := by
      intro z
      have he := congrArg (fun u : (Level p T N k)ˣ => ((u⁻¹ : (Level p T N k)ˣ) : Level p T N k))
        (map_unitElement z)
      simpa using he
    simp_rw [hx]
    rw [Equiv.sum_comp (unitGridEquiv p T N k h hk)
      (fun u : (Level p T N k)ˣ => ((u⁻¹ : (Level p T N k)ˣ) : Level p T N k) ^ 2)]
    exact hm
  have scalarPadicUnit_val (p : ℕ) [Fact p.Prime] (k : ℕ) (a : ScalarU p k) :
      (scalarPadicUnit p k a : ℤ_[p]) = (a.val.val + 1 : ℕ) := by
    exact IsUnit.unit_spec _
  let scalarGridEquiv (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k) : ScalarU p k ≃ (ZMod (p ^ k))ˣ := by
    exact ((positiveCoordinates (p ^ k)).subtypeEquiv (by
      intro a
      change ¬ p ∣ a.val + 1 ↔ IsUnit (positiveCoordinates (p ^ k) a)
      change ¬ p ∣ a.val + 1 ↔ IsUnit (positiveCoordinates (p ^ k) a)
      rw [positiveEquiv_apply, ZMod.isUnit_iff_coprime,
        Nat.coprime_pow_right_iff (by omega : 0 < k), Nat.coprime_comm,
        (Fact.out : p.Prime).coprime_iff_not_dvd])).trans
          (Submonoid.unitsTypeEquivIsUnitSubmonoid.symm.toEquiv)
  have S_divisible (p : ℕ) [Fact p.Prime] (k : ℕ) (hp : 5 < p) (hk : 1 ≤ k) : (p : ℤ_[p]) ^ k ∣ S p k := by
    have small_zmod_isUnit (p : ℕ) [Fact p.Prime] (k : ℕ) (a : ℕ) (ha : 0 < a) (hap : a < p) :
        IsUnit (a : ZMod (p ^ k)) := by
      rw [ZMod.isUnit_iff_coprime]
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, (Fact.out : p.Prime).coprime_iff_not_dvd]
      exact Nat.not_dvd_of_pos_of_lt ha hap
    have scalarGridEquiv_val (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k) (a : ScalarU p k) :
        (scalarGridEquiv p k hk a : ZMod (p ^ k)) = (a.val.val + 1 : ℕ) := by
      exact (IsUnit.unit_spec _).trans (positiveEquiv_apply _ _)
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    have hu : ∀ a : ScalarU p k,
        Units.map (PadicInt.toZModPow k).toMonoidHom (scalarPadicUnit p k a) = scalarGridEquiv p k hk a := by
      intro a
      apply Units.ext
      simp [scalarPadicUnit_val, scalarGridEquiv_val]
    have hx : ∀ a : ScalarU p k,
        PadicInt.toZModPow k (((scalarPadicUnit p k a)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) =
        (((scalarGridEquiv p k hk a)⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) := by
      intro a
      have he := congrArg (fun u : (ZMod (p ^ k))ˣ => ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) (hu a)
      simpa using he
    simp only [S, map_sum, map_pow]
    simp_rw [hx]
    rw [Equiv.sum_comp (scalarGridEquiv p k hk)
      (fun u : (ZMod (p ^ k))ˣ => ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) ^ 2)]
    exact unit_second_moment (small_zmod_isUnit p k 2 (by omega) (by omega))
      (small_zmod_isUnit p k 3 (by omega) (by omega))
  have scalarUnit_val (p : ℕ) [Fact p.Prime] (k : ℕ) (T N : ℤ) (a : ScalarU p k) :
      (scalarUnit p k T N a : R p T N) = (a.val.val + 1 : ℕ) := by
    simp [scalarPadicUnit_val, scalarUnit]
  have scalar_moment_divisible (p : ℕ) [Fact p.Prime] (k : ℕ) (T N : ℤ) (hp : 5 < p) (hk : 1 ≤ k) :
      (p : R p T N) ^ k ∣
        ∑ a : ScalarU p k, (((scalarUnit p k T N a)⁻¹ : (R p T N)ˣ) : R p T N) ^ 2 := by
    have hd := map_dvd (algebraMap ℤ_[p] (R p T N)) (S_divisible p k hp hk)
    simpa [S, map_pow, map_natCast, map_sum, scalarUnit] using hd
  have sum_inverse_square_divisible {A : Type} [CommRing A] {ι : Type} [Fintype ι]
      (q : A) (u v : ι → Aˣ) (h : ∀ i, q ∣ (u i : A) - (v i : A))
      (hv : q ∣ ∑ i, (((v i)⁻¹ : Aˣ) : A) ^ 2) :
      q ∣ ∑ i, (((u i)⁻¹ : Aˣ) : A) ^ 2 := by
    have inverse_square_congruence {R : Type} [CommRing R] (q : R) (u v : Rˣ)
        (h : q ∣ (u : R) - (v : R)) :
        q ∣ ((u⁻¹ : Rˣ) : R) ^ 2 - ((v⁻¹ : Rˣ) : R) ^ 2 := by
      have inverse_congruence {R : Type} [CommRing R] (q : R) (u v : Rˣ) (h : q ∣ (u : R) - (v : R)) :
          q ∣ ((u⁻¹ : Rˣ) : R) - ((v⁻¹ : Rˣ) : R) := by
        have hi : ((u⁻¹ : Rˣ) : R) - ((v⁻¹ : Rˣ) : R) =
            -((u⁻¹ : Rˣ) : R) * ((v⁻¹ : Rˣ) : R) * ((u : R) - (v : R)) := by
          have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := by simp
          have hv : (v : R) * ((v⁻¹ : Rˣ) : R) = 1 := by simp
          linear_combination ((v⁻¹ : Rˣ) : R) * hu - ((u⁻¹ : Rˣ) : R) * hv
        rw [hi]
        exact dvd_mul_of_dvd_right h _
      have hi := inverse_congruence q u v h
      convert dvd_mul_of_dvd_left hi
        (((u⁻¹ : Rˣ) : R) + ((v⁻¹ : Rˣ) : R)) using 1; ring
    classical
    have hd : q ∣ ∑ i, ((((u i)⁻¹ : Aˣ) : A) ^ 2 - (((v i)⁻¹ : Aˣ) : A) ^ 2) :=
      Finset.dvd_sum (fun i _ => inverse_square_congruence q (u i) (v i) (h i))
    rw [Finset.sum_sub_distrib] at hd
    simpa only [sub_add_cancel] using dvd_add hd hv
  let omegaUnit (p : ℕ) [Fact p.Prime] (T N : ℤ) (h : Admissible p T N) : (R p T N)ˣ :=
    (show IsUnit (AdjoinRoot.root (X ^ 2 - C (T : ℤ_[p]) * X + C (N : ℤ_[p]))) from by
      have hu := element_isUnit p T N h 0 1 (by
        simp [(Fact.out : p.Prime).not_dvd_one])
      simpa [element] using hu).unit
  have omegaUnit_val (p : ℕ) [Fact p.Prime] (T N : ℤ) (h : Admissible p T N) :
      (omegaUnit p T N h : R p T N) = AdjoinRoot.root (X ^ 2 - C (T : ℤ_[p]) * X + C (N : ℤ_[p])) := by
    exact IsUnit.unit_spec _
  clear_value omegaUnit
  let Ex (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (h : Admissible p T N) : R p T N :=
    ∑ z : BoundaryX p k, (((unitElement p T N h k z.val)⁻¹ : (R p T N)ˣ) : R p T N) ^ 2
  let Ey (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (h : Admissible p T N) : R p T N :=
    ∑ z : BoundaryY p k, (((unitElement p T N h k z.val)⁻¹ : (R p T N)ˣ) : R p T N) ^ 2
  have Ex_divisible (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (h : Admissible p T N) (hk : 1 ≤ k) :
      (p : R p T N) ^ k ∣ Ex p T N k h := by
    have boundaryX_congr (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (h : Admissible p T N) (hk : 1 ≤ k) (a : ScalarU p k) :
        (p : R p T N) ^ k ∣
          (unitElement p T N h k ((boundaryXEquiv p k hk).symm a).val : R p T N) -
            (omegaUnit p T N h * scalarUnit p k T N a : (R p T N)ˣ) := by
      have lastCoord_value (p : ℕ) [Fact p.Prime] (k : ℕ) : ((Fin.cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p ^ k)))) (Fin.last (p ^ k - 1)))).val + 1 = p ^ k := by
        simp only [Fin.val_cast, Fin.val_last]
        have hpos := pow_pos (Fact.out : p.Prime).pos k
        omega
      simp only [unitElement_val, Units.val_mul, omegaUnit_val, scalarUnit_val]
      change (p : R p T N) ^ k ∣
        element p T N (((Fin.cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p ^ k)))) (Fin.last (p ^ k - 1)))).val + 1) (a.val.val + 1) - AdjoinRoot.root (X ^ 2 - C (T : ℤ_[p]) * X + C (N : ℤ_[p])) * ((a.val.val + 1 : ℕ) : R p T N)
      rw [lastCoord_value]
      refine ⟨1, ?_⟩
      unfold element
      push_cast
      ring
    classical
    unfold Ex
    rw [← Equiv.sum_comp (boundaryXEquiv p k hk).symm
      (fun z : BoundaryX p k => (((unitElement p T N h k z.val)⁻¹ : (R p T N)ˣ) : R p T N) ^ 2)]
    apply sum_inverse_square_divisible _ _
      (fun a => omegaUnit p T N h * scalarUnit p k T N a)
      (boundaryX_congr p T N k h hk)
    have hd := scalar_moment_divisible p k T N h.1 hk
    have heq : (∑ a : ScalarU p k,
        (((omegaUnit p T N h * scalarUnit p k T N a)⁻¹ : (R p T N)ˣ) : R p T N) ^ 2) =
        (((omegaUnit p T N h)⁻¹ : (R p T N)ˣ) : R p T N) ^ 2 *
          (∑ a : ScalarU p k, (((scalarUnit p k T N a)⁻¹ : (R p T N)ˣ) : R p T N) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [mul_inv_rev, Units.val_mul, mul_pow]
      exact mul_comm _ _
    rw [heq]
    exact dvd_mul_of_dvd_right hd _
  have Ey_divisible (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (h : Admissible p T N) (hk : 1 ≤ k) :
      (p : R p T N) ^ k ∣ Ey p T N k h := by
    have boundaryY_congr (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (h : Admissible p T N) (hk : 1 ≤ k) (a : ScalarU p k) :
        (p : R p T N) ^ k ∣
          (unitElement p T N h k ((boundaryYEquiv p k hk).symm a).val : R p T N) -
            (scalarUnit p k T N a : R p T N) := by
      have lastCoord_value (p : ℕ) [Fact p.Prime] (k : ℕ) : ((Fin.cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p ^ k)))) (Fin.last (p ^ k - 1)))).val + 1 = p ^ k := by
        simp only [Fin.val_cast, Fin.val_last]
        have hpos := pow_pos (Fact.out : p.Prime).pos k
        omega
      simp only [unitElement_val, scalarUnit_val]
      change (p : R p T N) ^ k ∣
        element p T N (a.val.val + 1) (((Fin.cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p ^ k)))) (Fin.last (p ^ k - 1)))).val + 1) - ((a.val.val + 1 : ℕ) : R p T N)
      rw [lastCoord_value]
      refine ⟨AdjoinRoot.root (X ^ 2 - C (T : ℤ_[p]) * X + C (N : ℤ_[p])), ?_⟩
      unfold element
      push_cast
      ring
    classical
    unfold Ey
    rw [← Equiv.sum_comp (boundaryYEquiv p k hk).symm
      (fun z : BoundaryY p k => (((unitElement p T N h k z.val)⁻¹ : (R p T N)ˣ) : R p T N) ^ 2)]
    exact sum_inverse_square_divisible _ _ (scalarUnit p k T N)
      (boundaryY_congr p T N k h hk) (scalar_moment_divisible p k T N h.1 hk)
  let A (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (h : Admissible p T N) : R p T N :=
    ∑ z : Grid p k, correction p T N k z *
      (((unitElement p T N h k z)⁻¹ : (R p T N)ˣ) : R p T N) ^ 2
  have moment_bounds_route  (p : ℕ) [Fact p.Prime] (T N : ℤ)
      (h : Admissible p T N) (k : ℕ) (hk : 1 ≤ k) :
      (p : R p T N) ^ (2 * k) ∣ gridH1 p T N h k ∧
      (p : R p T N) ^ k ∣ gridH2 p T N h k := by
    have first_moment_from_reflection {R : Type} [CommRing R] {ι : Type} [Fintype ι]
        (q : R) (u : ι → Rˣ) (c : ι → R) (τ : ι ≃ ι)
        (hτ : ∀ i, (u (τ i) : R) = -(u i : R) + q * c i)
        (hc : q ∣ ∑ i, c i * (((u i)⁻¹ : Rˣ) : R) ^ 2)
        (h2 : IsUnit (2 : R)) :
        q ^ 2 ∣ ∑ i, (((u i)⁻¹ : Rˣ) : R) := by
      have reflection_congruence {R : Type} [CommRing R] (q c : R) (u v : Rˣ)
          (hv : (v : R) = -(u : R) + q * c) :
          q ^ 2 ∣ ((v⁻¹ : Rˣ) : R) -
            (-((u⁻¹ : Rˣ) : R) - q * c * ((u⁻¹ : Rˣ) : R) ^ 2) := by
        have reflection_exact {R : Type} [CommRing R] (q c : R) (u v : Rˣ)
            (hv : (v : R) = -(u : R) + q * c) :
            ((v⁻¹ : Rˣ) : R) + ((u⁻¹ : Rˣ) : R) +
              q * c * ((u⁻¹ : Rˣ) : R) ^ 2 =
              q ^ 2 * c ^ 2 * ((u⁻¹ : Rˣ) : R) ^ 2 * ((v⁻¹ : Rˣ) : R) := by
          have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := by simp
          have hvi : (v : R) * ((v⁻¹ : Rˣ) : R) = 1 := by simp
          rw [hv] at hvi
          have hi : ((v⁻¹ : Rˣ) : R) + ((u⁻¹ : Rˣ) : R) =
              q * c * ((u⁻¹ : Rˣ) : R) * ((v⁻¹ : Rˣ) : R) := by
            linear_combination -((u⁻¹ : Rˣ) : R) * hvi - ((v⁻¹ : Rˣ) : R) * hu
          calc
            _ = q * c * ((u⁻¹ : Rˣ) : R) * ((v⁻¹ : Rˣ) : R) +
                q * c * ((u⁻¹ : Rˣ) : R) ^ 2 := by rw [hi]
            _ = q * c * ((u⁻¹ : Rˣ) : R) *
                (((v⁻¹ : Rˣ) : R) + ((u⁻¹ : Rˣ) : R)) := by ring
            _ = q * c * ((u⁻¹ : Rˣ) : R) *
                (q * c * ((u⁻¹ : Rˣ) : R) * ((v⁻¹ : Rˣ) : R)) := by rw [hi]
            _ = _ := by ring
        refine ⟨c ^ 2 * ((u⁻¹ : Rˣ) : R) ^ 2 * ((v⁻¹ : Rˣ) : R), ?_⟩
        have h := reflection_exact q c u v hv
        linear_combination h
      classical
      have hsum : q ^ 2 ∣ ∑ i,
          ((((u (τ i))⁻¹ : Rˣ) : R) + (((u i)⁻¹ : Rˣ) : R) +
            q * c i * (((u i)⁻¹ : Rˣ) : R) ^ 2) :=
        Finset.dvd_sum (fun i _ => by
          simpa [sub_eq_add_neg, neg_sub, add_assoc, add_comm, add_left_comm] using reflection_congruence q (c i) (u i) (u (τ i)) (hτ i))
      have hp := Equiv.sum_comp τ (fun i => (((u i)⁻¹ : Rˣ) : R))
      simp only [Finset.sum_add_distrib] at hsum
      rw [hp] at hsum
      have hc' : q ^ 2 ∣ q * ∑ i, c i * (((u i)⁻¹ : Rˣ) : R) ^ 2 := by
        obtain ⟨b, hb⟩ := hc
        refine ⟨b, ?_⟩
        rw [hb]; ring
      have heq : (∑ i, (((u i)⁻¹ : Rˣ) : R)) +
          (∑ i, (((u i)⁻¹ : Rˣ) : R)) +
          (∑ i, q * c i * (((u i)⁻¹ : Rˣ) : R) ^ 2) -
          q * (∑ i, c i * (((u i)⁻¹ : Rˣ) : R) ^ 2) =
          2 * (∑ i, (((u i)⁻¹ : Rˣ) : R)) := by
        simp only [mul_assoc, ← Finset.mul_sum]
        ring
      have hdiv := dvd_sub hsum hc'
      rw [heq] at hdiv
      exact h2.dvd_mul_left.mp hdiv
    have tau_affine (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (h : Admissible p T N) (hk : 1 ≤ k) (z : Grid p k) :
        (unitElement p T N h k (tau p k hk z) : R p T N) =
          -(unitElement p T N h k z : R p T N) +
            (p : R p T N) ^ k * correction p T N k z := by
      have reflection_cast {A : Type} [CommRing A] (q : ℕ) (i : Fin q) :
          ((((Fin.revPerm (n := q)).trans (finRotate q).symm) i).val + 1 : ℕ) =
            -((i.val + 1 : ℕ) : A) + (q : A) * (1 + if i.val + 1 = q then 1 else 0) := by
        have reflection_nat (q : ℕ) (i : Fin q) :
            (((Fin.revPerm (n := q)).trans (finRotate q).symm) i).val + 1 = if i.val + 1 = q then q else q - (i.val + 1) := by
          have := i.neZero
          change ((finRotate q).symm i.rev).val + 1 = _
          by_cases h : i.val + 1 = q
          · have hi : i.rev = 0 := by
              apply Fin.ext
              simp only [Fin.val_rev, Fin.val_zero]
              omega
            have heq : (finRotate q).symm i.rev = i := by
              apply (finRotate q).symm_apply_eq.mpr
              cases q with
              | zero => exact i.elim0
              | succ n =>
                have hilast : i = Fin.last n := by apply Fin.ext; simp only [Fin.val_last]; omega
                rw [hi, hilast, finRotate_last]
            rw [heq, if_pos h]
            exact h
          · have hi : i.rev ≠ 0 := by
              intro hz
              have hv := congrArg Fin.val hz
              simp only [Fin.val_rev, Fin.val_zero] at hv
              have := i.isLt
              omega
            rw [coe_finRotate_symm_of_ne_zero hi, if_neg h]
            simp only [Fin.val_rev]
            have := i.isLt
            omega
        have hi := i.isLt
        rw [reflection_nat]
        split_ifs with h
        · simp only [h, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          ring
        · rw [Nat.cast_sub (by omega : i.val + 1 ≤ q)]
          push_cast
          ring
      simp only [unitElement_val]
      change element p T N ((((Fin.revPerm (n := p ^ k)).trans (finRotate (p ^ k)).symm) z.val.1).val + 1)
          ((((Fin.revPerm (n := p ^ k)).trans (finRotate (p ^ k)).symm) z.val.2).val + 1) = _
      unfold element correction
      rw [reflection_cast (A := R p T N), reflection_cast (A := R p T N)]
      push_cast
      ring
    have A_divisible (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (h : Admissible p T N) (hk : 1 ≤ k) :
        (p : R p T N) ^ k ∣ A p T N k h := by
      have A_decomposition (p : ℕ) [Fact p.Prime] (T N : ℤ) (k : ℕ) (h : Admissible p T N) :
          A p T N k h = (1 + AdjoinRoot.root (X ^ 2 - C (T : ℤ_[p]) * X + C (N : ℤ_[p]))) * gridH2 p T N h k +
            Ex p T N k h + AdjoinRoot.root (X ^ 2 - C (T : ℤ_[p]) * X + C (N : ℤ_[p])) * Ey p T N k h := by
        have sum_indicator_subtype {ι A : Type} [Fintype ι] [AddCommMonoid A]
            (P : ι → Prop) [DecidablePred P] (f : ι → A) :
            (∑ i, if P i then f i else 0) = ∑ i : {i // P i}, f i.val := by
          classical
          simpa only [Finset.sum_filter] using
            (Finset.sum_subtype (Finset.univ.filter P) (by simp) f)
        classical
        let f := fun z : Grid p k => (((unitElement p T N h k z)⁻¹ : (R p T N)ˣ) : R p T N) ^ 2
        have hs : ∀ z : Grid p k,
            correction p T N k z * f z = (1 + AdjoinRoot.root (X ^ 2 - C (T : ℤ_[p]) * X + C (N : ℤ_[p]))) * f z +
              (if z.val.1.val + 1 = p ^ k then f z else 0) +
              AdjoinRoot.root (X ^ 2 - C (T : ℤ_[p]) * X + C (N : ℤ_[p])) * (if z.val.2.val + 1 = p ^ k then f z else 0) := by
          intro z
          unfold correction
          split_ifs <;> ring
        unfold A
        change (∑ z : Grid p k, correction p T N k z * f z) = _
        simp_rw [hs]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [sum_indicator_subtype, sum_indicator_subtype]
      rw [A_decomposition]
      exact dvd_add
        (dvd_add (dvd_mul_of_dvd_right (H2_divisible p T N k h hk) _)
          (Ex_divisible p T N k h hk))
        (dvd_mul_of_dvd_right (Ey_divisible p T N k h hk) _)
    have h2 : IsUnit (2 : R p T N) := by
      have hn : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by omega) (by have := h.1; omega)
      have hu := element_isUnit p T N h 2 0 (by simpa using hn)
      simpa [element] using hu
    have hh := first_moment_from_reflection ((p : R p T N) ^ k)
      (unitElement p T N h k) (correction p T N k) (tau p k hk)
      (tau_affine p T N k h hk) (A_divisible p T N k h hk) h2
    constructor
    · simpa only [gridH1, pow_mul, Nat.mul_comm] using hh
    · exact H2_divisible p T N k h hk
  intro p hp T N h k hk
  letI : Fact p.Prime := hp
  have coordinates_element (x y : ℕ) :
      coordinateEquiv (T : ℤ_[p]) (N : ℤ_[p]) (element p T N x y) =
        (⟨(x : ℤ_[p]), (y : ℤ_[p])⟩ : QuadraticAlgebra ℤ_[p] (-(N : ℤ_[p])) (T : ℤ_[p])) := by
    ext <;> simp [coordinateEquiv, rootToCoordinates, element]
  have grid_injective : Function.Injective
      (fun z : Grid p k => element p T N (z.val.1.val + 1) (z.val.2.val + 1)) := by
    intro z w he
    have hc := congrArg (coordinateEquiv (T : ℤ_[p]) (N : ℤ_[p])) he
    rw [coordinates_element, coordinates_element] at hc
    have hx := congrArg QuadraticAlgebra.re hc
    have hy := congrArg QuadraticAlgebra.im hc
    have hx' : z.val.1.val + 1 = w.val.1.val + 1 := Nat.cast_injective hx
    have hy' : z.val.2.val + 1 = w.val.2.val + 1 := Nat.cast_injective hy
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> omega
  have literal_grid : U p T N k = Finset.univ.image
      (fun z : Grid p k => element p T N (z.val.1.val + 1) (z.val.2.val + 1)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hbox,hnd⟩ := Finset.mem_filter.mp hxy
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp hbox
      obtain ⟨hx1,hxq⟩ := Finset.mem_Icc.mp hx
      obtain ⟨hy1,hyq⟩ := Finset.mem_Icc.mp hy
      let g : Grid p k := ⟨(⟨x - 1, by omega⟩, ⟨y - 1, by omega⟩), by
        simpa only [Nat.sub_add_cancel hx1, Nat.sub_add_cancel hy1] using hnd⟩
      apply Finset.mem_image.mpr
      refine ⟨g, Finset.mem_univ _, ?_⟩
      dsimp [g]
      rw [Nat.sub_add_cancel hx1, Nat.sub_add_cancel hy1]
    · intro hz
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hz
      apply Finset.mem_image.mpr
      refine ⟨(g.val.1.val + 1, g.val.2.val + 1), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, g.property⟩
      · exact Finset.mem_Icc.mpr ⟨by omega, by have := g.val.1.isLt; omega⟩
      · exact Finset.mem_Icc.mpr ⟨by omega, by have := g.val.2.isLt; omega⟩
  have sum_bridge (f : R p T N → R p T N) :
      (∑ z ∈ U p T N k, f z) =
        ∑ g : Grid p k, f (element p T N (g.val.1.val + 1) (g.val.2.val + 1)) := by
    rw [literal_grid, Finset.sum_image]
    intro a _ b _ he
    exact grid_injective he
  have inverse_grid (g : Grid p k) :
      Ring.inverse (element p T N (g.val.1.val + 1) (g.val.2.val + 1)) =
        (((unitElement p T N h k g)⁻¹ : (R p T N)ˣ) : R p T N) := by
    rw [← unitElement_val p T N h k g, Ring.inverse_unit]
  have bridge1 : H1 p T N k = gridH1 p T N h k := by
    unfold H1
    rw [sum_bridge]
    simp only [inverse_grid, gridH1]
  have bridge2 : H2 p T N k = gridH2 p T N h k := by
    unfold H2
    rw [sum_bridge]
    simp only [inverse_grid, gridH2]
  rw [bridge1, bridge2]
  simpa only [Ideal.mem_span_singleton] using moment_bounds_route p T N h k hk
end
end CalderonReciprocalMoments
