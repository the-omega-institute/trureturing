/- GID: D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: A first-residue-preserving CRT bijection for integral affine arrangements. -/

/-
Public theorem: CentralizationBijection.result
proof_shape: content
escape_witness: The result itself, by integer good-reduction certificates,
coordinate CRT and translation with a valid center family, followed by the
equivalence of exact closed row tags and rational common-kernel flats.
admission_basis: open-problem-resolution (#34739, Proved)
Direct frozen dependencies: none (ordinary pinned Mathlib imports).
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-!
# Centralization convolution over coprime residue rings

This is the bijection asked for in Chen–Fu–Li–Wang, arXiv:2606.00599v1,
at the end of §4.2, with the affine localization and central restriction of
Definition 2.4. The first residue is preserved coordinatewise.
-/

namespace D5.S3.Combinatorics.Geometry.HyperplaneArrangements

open scoped BigOperators Matrix

namespace CentralizationGoodReduction

/-- The affine equations indexed by `S` have a common solution over `R`. -/
private def AffineConsistent (R : Type*) [CommRing R] {n : ℕ} {ι : Type*}
    (a : ι → Fin n → ℤ) (b : ι → ℤ) (S : Finset ι) : Prop :=
  ∃ x : Fin n → R, ∀ i ∈ S, ∑ j, (a i j : R) * x j = (b i : R)

/-- Every common zero of the normals indexed by `S` is a zero of normal `i`. -/
private def HomogeneousImplies (R : Type*) [CommRing R] {n : ℕ} {ι : Type*}
    (a : ι → Fin n → ℤ) (S : Finset ι) (i : ι) : Prop :=
  ∀ x : Fin n → R,
    (∀ k ∈ S, ∑ j, (a k j : R) * x j = 0) →
    ∑ j, (a i j : R) * x j = 0

set_option linter.unusedFintypeInType false in
private theorem clearDenominators {κ : Type*} [Fintype κ] (v : κ → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ z : κ → ℤ, (Int.castRingHom ℚ ∘ z) = (d : ℚ) • v := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.pos ℤ) v
  have h0 : 0 < (d : ℤ) := d.property
  have hdc : ((d : ℤ).toNat : ℤ) = (d : ℤ) := Int.toNat_of_nonneg h0.le
  have hpos : 0 < (d : ℤ).toNat := by omega
  choose z hz using hd
  refine ⟨(d : ℤ).toNat, hpos, z, ?_⟩
  funext i
  change (z i : ℚ) = ((d : ℤ).toNat : ℚ) * v i
  have hi := hz i
  change (z i : ℚ) = (d : ℤ) • v i at hi
  rw [Algebra.smul_def] at hi
  rw [← Int.cast_natCast ((d : ℤ).toNat), hdc]
  exact hi

private theorem intCast_isUnit_of_coprime {m : ℕ} {z : ℤ} (h : m.Coprime z.natAbs) :
    IsUnit (z : ZMod m) := by
  have hu := (ZMod.isUnit_iff_coprime z.natAbs m).2 h.symm
  obtain hz | hz := z.natAbs_eq
  · rw [hz, Int.cast_natCast]
    exact hu
  · rw [hz, Int.cast_neg, Int.cast_natCast]
    exact hu.neg

private def Solvable (R : Type*) [CommRing R] {κ : Type*} {n : ℕ}
    (A : Matrix κ (Fin n) ℤ) (b : κ → ℤ) : Prop :=
  ∃ x : Fin n → R, A.map (Int.castRingHom R) *ᵥ x = Int.castRingHom R ∘ b

set_option linter.unusedFintypeInType false in
/-- A rational point above `b` reduces after clearing denominators. If `b` is outside
the rational image, an integral functional forces any modular preimage of `t • b`
to have `t = 0` when its value at `b` reduces to a unit. -/
private theorem goodReductionForDirection {κ : Type*} [Fintype κ] {n : ℕ}
    (A : Matrix κ (Fin n) ℤ) (b : κ → ℤ) :
    ∃ d : ℕ, 0 < d ∧ ∀ m : ℕ, m.Coprime d →
      (Solvable ℚ A b → Solvable (ZMod m) A b) ∧
      (¬ Solvable ℚ A b → ∀ (t : ZMod m) (x : Fin n → ZMod m),
        A.map (Int.castRingHom (ZMod m)) *ᵥ x =
          t • (Int.castRingHom (ZMod m) ∘ b) → t = 0) := by
  classical
  let q := Int.castRingHom ℚ
  by_cases h : Solvable ℚ A b
  · obtain ⟨x, hx⟩ := h
    change A.map q *ᵥ x = q ∘ b at hx
    obtain ⟨d, hd, z, hz⟩ := clearDenominators x
    have hz_eq : A *ᵥ z = (d : ℤ) • b := by
      funext i
      apply (Int.cast_injective (α := ℚ))
      change q ((A *ᵥ z) i) = q ((d : ℤ) * b i)
      rw [q.map_mulVec, hz, Matrix.mulVec_smul, hx, q.map_mul]
      simp [q]
    refine ⟨d, hd, fun m hm => ⟨fun _ => ?_, fun hnot => (hnot ⟨x, hx⟩).elim⟩⟩
    let e := Int.castRingHom (ZMod m)
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime d m).2 hm.symm
    have heq (i : κ) : (A.map e *ᵥ (e ∘ z)) i = (d : ZMod m) * e (b i) := by
      rw [← e.map_mulVec, hz_eq]
      change e ((d : ℤ) * b i) = _
      simp [e]
    refine ⟨(↑(u⁻¹) : ZMod m) • (e ∘ z), ?_⟩
    change A.map e *ᵥ ((↑(u⁻¹) : ZMod m) • (e ∘ z)) = e ∘ b
    rw [Matrix.mulVec_smul]
    funext i
    change (↑(u⁻¹) : ZMod m) * (A.map e *ᵥ (e ∘ z)) i = e (b i)
    rw [heq, ← hu, ← mul_assoc]
    simp
  · have hb : q ∘ b ∉ (A.map q).mulVecLin.range := by
      simpa only [Solvable, LinearMap.mem_range, Matrix.mulVecLin_apply] using h
    obtain ⟨f, hf, hf_range⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hb inferInstance
    let c := (dotProductEquiv ℚ κ).symm f
    have hc (v : κ → ℚ) : c ⬝ᵥ v = f v := by
      rw [← dotProductEquiv_apply_apply ℚ κ c v]
      simp [c]
    have hc_image (x : Fin n → ℚ) : c ⬝ᵥ (A.map q *ᵥ x) = 0 := by
      rw [hc]
      have hmem : f (A.map q *ᵥ x) ∈ (A.map q).mulVecLin.range.map f :=
        ⟨A.map q *ᵥ x, ⟨x, rfl⟩, rfl⟩
      simpa only [hf_range, Submodule.mem_bot] using hmem
    have hc_zero : c ᵥ* A.map q = 0 := by
      funext j
      rw [← dotProduct_single_one (c ᵥ* A.map q) j, ← Matrix.dotProduct_mulVec]
      exact hc_image _
    obtain ⟨d, hd, z, hz⟩ := clearDenominators c
    have hz_zero : z ᵥ* A = 0 := by
      funext j
      apply (Int.cast_injective (α := ℚ))
      change q ((z ᵥ* A) j) = q 0
      rw [q.map_vecMul, hz, Matrix.smul_vecMul, hc_zero]
      simp
    have hz_b : z ⬝ᵥ b ≠ 0 := by
      intro hz_eq
      have heq := q.map_dotProduct z b
      rw [hz_eq, q.map_zero, hz, smul_dotProduct, hc] at heq
      exact (mul_ne_zero (Nat.cast_ne_zero.mpr hd.ne') hf) heq.symm
    refine ⟨(z ⬝ᵥ b).natAbs, Int.natAbs_pos.mpr hz_b, fun m hm => ⟨fun h' => (h h').elim, ?_⟩⟩
    intro _ t x hx
    let e := Int.castRingHom (ZMod m)
    change A.map e *ᵥ x = t • (e ∘ b) at hx
    have hmod_zero : (e ∘ z) ᵥ* A.map e = 0 := by
      funext j
      rw [← e.map_vecMul, hz_zero]
      exact e.map_zero
    have hu : IsUnit ((e ∘ z) ⬝ᵥ (e ∘ b)) := by
      rw [← e.map_dotProduct]
      exact intCast_isUnit_of_coprime hm
    have hprod := congrArg (fun v => (e ∘ z) ⬝ᵥ v) hx
    rw [Matrix.dotProduct_mulVec, hmod_zero, zero_dotProduct, dotProduct_smul] at hprod
    exact hu.mul_right_cancel (hprod.symm.trans (zero_mul _).symm)

private theorem affineGoodReduction {n : ℕ} {ι : Type*}
    (a : ι → Fin n → ℤ) (b : ι → ℤ) (S : Finset ι) :
    ∃ d : ℕ, 0 < d ∧ ∀ m : ℕ, 1 < m → m.Coprime d →
      (AffineConsistent ℚ a b S ↔ AffineConsistent (ZMod m) a b S) := by
  let A : Matrix S (Fin n) ℤ := Matrix.of fun i => a i
  let rhs : S → ℤ := fun i => b i
  have hSolvable (R : Type) [CommRing R] :
      Solvable R A rhs ↔ AffineConsistent R a b S := by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, fun i hi => congrFun hx ⟨i, hi⟩⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, funext fun i => hx i i.property⟩
  obtain ⟨d, hd, hred⟩ := goodReductionForDirection A rhs
  refine ⟨d, hd, fun m hm hcop => ?_⟩
  have : Fact (1 < m) := ⟨hm⟩
  rw [← hSolvable ℚ, ← hSolvable (ZMod m)]
  obtain ⟨hLift, hCancel⟩ := hred m hcop
  refine ⟨hLift, ?_⟩
  rintro ⟨x, hx⟩
  by_contra h
  exact one_ne_zero (hCancel h 1 x (by simpa only [one_smul] using hx))

private def augmentedMatrix {n : ℕ} {ι : Type*} (a : ι → Fin n → ℤ)
    (S : Finset ι) (i : ι) : Matrix (Option S) (Fin n) ℤ :=
  Matrix.of fun k => k.elim (a i) (fun j => a j)

private def augmentedRhs {κ : Type*} : Option κ → ℤ
  | none => 1
  | some _ => 0

private theorem augmented_mulVec_eq_iff {R : Type*} [CommRing R] {n : ℕ} {ι : Type*}
    (a : ι → Fin n → ℤ) (S : Finset ι) (i : ι) (x : Fin n → R) (t : R) :
    (augmentedMatrix a S i).map (Int.castRingHom R) *ᵥ x =
      t • (Int.castRingHom R ∘ augmentedRhs) ↔
      (∀ k ∈ S, ∑ j, (a k j : R) * x j = 0) ∧ ∑ j, (a i j : R) * x j = t := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · simpa [augmentedMatrix, augmentedRhs, Matrix.mulVec, dotProduct]
        using congrFun h (some ⟨k, hk⟩)
    · simpa [augmentedMatrix, augmentedRhs, Matrix.mulVec, dotProduct] using congrFun h none
  · rintro ⟨h, hi⟩
    funext k
    cases k with
    | none =>
      simpa [augmentedMatrix, augmentedRhs, Matrix.mulVec, dotProduct] using hi
    | some k =>
      simpa [augmentedMatrix, augmentedRhs, Matrix.mulVec, dotProduct] using h k k.property

private theorem implicationGoodReduction {n : ℕ} {ι : Type*}
    (a : ι → Fin n → ℤ) (S : Finset ι) (i : ι) :
    ∃ d : ℕ, 0 < d ∧ ∀ m : ℕ, 1 < m → m.Coprime d →
      (HomogeneousImplies ℚ a S i ↔ HomogeneousImplies (ZMod m) a S i) := by
  let A := augmentedMatrix a S i
  have hNoPoint : HomogeneousImplies ℚ a S i ↔ ¬ Solvable ℚ A augmentedRhs := by
    constructor
    · rintro h ⟨x, hx⟩
      have ⟨hS, hi⟩ := (augmented_mulVec_eq_iff a S i x 1).1 (by simpa only [one_smul] using hx)
      exact one_ne_zero (hi.symm.trans (h x hS))
    · intro h x hS
      by_contra hne
      let t : ℚ := (∑ j, (a i j : ℚ) * x j)⁻¹
      have hS' (k) (hk : k ∈ S) : ∑ j, (a k j : ℚ) * (t • x) j = 0 := by
        change (fun j => (a k j : ℚ)) ⬝ᵥ (t • x) = 0
        rw [dotProduct_smul]
        change t * (∑ j, (a k j : ℚ) * x j) = 0
        rw [hS k hk, mul_zero]
      have hi' : ∑ j, (a i j : ℚ) * (t • x) j = 1 := by
        change (fun j => (a i j : ℚ)) ⬝ᵥ (t • x) = 1
        rw [dotProduct_smul]
        exact inv_mul_cancel₀ hne
      apply h
      refine ⟨t • x, ?_⟩
      simpa only [one_smul] using (augmented_mulVec_eq_iff a S i (t • x) 1).2 ⟨hS', hi'⟩
  obtain ⟨d, hd, hred⟩ := goodReductionForDirection A augmentedRhs
  refine ⟨d, hd, fun m hm hcop => ?_⟩
  have : Fact (1 < m) := ⟨hm⟩
  obtain ⟨hLift, hCancel⟩ := hred m hcop
  constructor
  · intro h x hS
    exact hCancel (hNoPoint.mp h) _ x ((augmented_mulVec_eq_iff a S i x _).2 ⟨hS, rfl⟩)
  · intro h
    apply hNoPoint.mpr
    intro hPoint
    obtain ⟨x, hx⟩ := hLift hPoint
    have ⟨hS, hi⟩ := (augmented_mulVec_eq_iff a S i x 1).1 (by simpa only [one_smul] using hx)
    exact one_ne_zero (hi.symm.trans (h x hS))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- A single positive integer controls affine consistency and homogeneous implication
for all subfamilies of a finite integral row system, including at composite moduli. -/
private theorem exists_goodReduction {n : ℕ} {ι : Type*} [DecidableEq ι] [Fintype ι]
    (a : ι → Fin n → ℤ) (b : ι → ℤ) :
    ∃ D : ℕ, 0 < D ∧ ∀ m : ℕ, 1 < m → m.Coprime D →
      (∀ S : Finset ι, AffineConsistent ℚ a b S ↔ AffineConsistent (ZMod m) a b S) ∧
      (∀ (S : Finset ι) (i : ι),
        HomogeneousImplies ℚ a S i ↔ HomogeneousImplies (ZMod m) a S i) := by
  choose dAffine hdAffine ha using affineGoodReduction a b
  choose dImplies hdImplies hi using implicationGoodReduction a
  refine ⟨∏ S : Finset ι, (dAffine S * ∏ i, dImplies S i), ?_, ?_⟩
  · exact Finset.prod_pos fun S _ =>
      mul_pos (hdAffine S) (Finset.prod_pos fun i _ => hdImplies S i)
  · intro m hm hcop
    have hS (S : Finset ι) := Nat.coprime_mul_iff_right.mp
      (Nat.coprime_fintype_prod_right_iff.mp hcop S)
    exact ⟨fun S => ha S m hm (hS S).1,
      fun S i => hi S i m hm (Nat.coprime_fintype_prod_right_iff.mp (hS S).2 i)⟩

end CentralizationGoodReduction

open scoped BigOperators

namespace CentralizationTransport

variable {ι : Type*} {n : ℕ}

/-- The same integer row evaluated in the indicated ring. -/
def row (R : Type*) [Ring R] (a : ι → Fin n → ℤ) (i : ι) (x : Fin n → R) : R :=
  ∑ j, (a i j : R) * x j

private theorem row_add {R : Type*} [Ring R] (a : ι → Fin n → ℤ) (i : ι)
    (x y : Fin n → R) : row R a i (x + y) = row R a i x + row R a i y := by
  simp only [row, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem row_sub {R : Type*} [Ring R] (a : ι → Fin n → ℤ) (i : ι)
    (x y : Fin n → R) : row R a i (x - y) = row R a i x - row R a i y := by
  simp only [row, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem map_row {R T : Type*} [Ring R] [Ring T] (f : R →+* T)
    (a : ι → Fin n → ℤ) (i : ι) (x : Fin n → R) :
    f (row R a i x) = row T a i (fun j => f (x j)) := by
  simp only [row, map_sum, map_mul, map_intCast]

variable (a : ι → Fin n → ℤ) (b : ι → ℤ)

private def CentralImplies (R : Type*) [Ring R] (S : Finset ι) (i : ι) : Prop :=
  ∀ x : Fin n → R, (∀ j ∈ S, row R a j x = 0) → row R a i x = 0

private def AffineSolvable (R : Type*) [Ring R] (S : Finset ι) : Prop :=
  ∃ x : Fin n → R, ∀ i ∈ S, row R a i x = (b i : R)

/-- Good reduction of affine solvability, for every subsystem. -/
private def AffineGoodReduction (m : ℕ) : Prop :=
  ∀ S : Finset ι, AffineSolvable a b ℚ S ↔ AffineSolvable a b (ZMod m) S

/-- Good reduction of homogeneous row implication, for every subsystem and row. -/
private def CentralGoodReduction (q : ℕ) : Prop :=
  ∀ (S : Finset ι) (i : ι), CentralImplies a ℚ S i ↔ CentralImplies a (ZMod q) S i

private def rationalRow (i : ι) : Module.Dual ℚ (Fin n → ℚ) where
  toFun := row ℚ a i
  map_add' := row_add a i
  map_smul' := by
    intro r x
    simp only [RingHom.id_apply, row, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_left_comm _ r _

/-- The rational subspace cut out by the homogeneous rows in `S`. -/
def commonKernel (S : Finset ι) : Submodule ℚ (Fin n → ℚ) where
  carrier := {x | ∀ i ∈ S, row ℚ a i x = 0}
  zero_mem' := by simp [row]
  add_mem' := by
    intro x y hx hy i hi
    rw [row_add, hx i hi, hy i hi, add_zero]
  smul_mem' := by
    intro r x hx i hi
    change rationalRow a i (r • x) = 0
    rw [map_smul, show rationalRow a i x = 0 from hx i hi, smul_zero]

/-- The actual rational common-kernel subspaces. -/
def RationalFlat :=
  {K : Submodule ℚ (Fin n → ℚ) // ∃ S : Finset ι, commonKernel a S = K}

variable [Fintype ι]

/-- All rows whose rational kernels contain the given subspace. -/
private noncomputable def rowsContaining (K : Submodule ℚ (Fin n → ℚ)) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => ∀ x ∈ K, row ℚ a i x = 0

@[simp] private theorem mem_rowsContaining {K : Submodule ℚ (Fin n → ℚ)} {i : ι} :
    i ∈ rowsContaining a K ↔ ∀ x ∈ K, row ℚ a i x = 0 := by
  classical
  simp [rowsContaining]

/-- Rational homogeneous closure of a row set. -/
private noncomputable def centralClosure (S : Finset ι) : Finset ι :=
  rowsContaining a (commonKernel a S)

@[simp] private theorem mem_centralClosure {S : Finset ι} {i : ι} :
    i ∈ centralClosure a S ↔ CentralImplies a ℚ S i :=
  mem_rowsContaining a

private theorem subset_centralClosure (S : Finset ι) : S ⊆ centralClosure a S := by
  intro i hi
  exact (mem_centralClosure a).2 fun _ hx => hx i hi

private theorem commonKernel_centralClosure (S : Finset ι) :
    commonKernel a (centralClosure a S) = commonKernel a S := by
  ext x
  constructor
  · intro hx
    exact fun i hi => hx i (subset_centralClosure a S hi)
  · intro hx
    exact fun i hi => (mem_centralClosure a).1 hi x hx

private theorem centralClosure_idempotent (S : Finset ι) :
    centralClosure a (centralClosure a S) = centralClosure a S := by
  change rowsContaining a (commonKernel a (centralClosure a S)) =
    rowsContaining a (commonKernel a S)
  rw [commonKernel_centralClosure]

/-- A tag is exactly a fixed point of rational homogeneous closure. -/
private def ClosedTag :=
  {S : Finset ι // centralClosure a S = S}

/-- The inverse recovers every row containing the given rational flat. -/
private noncomputable def closedTagEquivFlat : ClosedTag a ≃ RationalFlat a where
  toFun T := ⟨commonKernel a T.val, ⟨T.val, rfl⟩⟩
  invFun K := ⟨rowsContaining a K.val, by
    obtain ⟨S, hS⟩ := K.property
    rw [← hS]
    exact centralClosure_idempotent a S⟩
  left_inv T := Subtype.ext T.property
  right_inv K := by
    apply Subtype.ext
    obtain ⟨S, hS⟩ := K.property
    change commonKernel a (rowsContaining a K.val) = K.val
    rw [← hS]
    exact commonKernel_centralClosure a S

private theorem mem_tag_iff_flat {T : ClosedTag a} {i : ι} :
    i ∈ T.val ↔ ∀ x ∈ (closedTagEquivFlat a T).val, row ℚ a i x = 0 := by
  rw [← T.property]
  exact mem_rowsContaining a

/-- The complete set of affine rows hit by a point. -/
private noncomputable def hitRows {R : Type*} [Ring R] (x : Fin n → R) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => row R a i x = (b i : R)

@[simp] private theorem mem_hitRows {R : Type*} [Ring R] {x : Fin n → R} {i : ι} :
    i ∈ hitRows a b x ↔ row R a i x = (b i : R) := by
  classical
  simp [hitRows]

/-- The complete set of homogeneous rows vanishing at a point. -/
private noncomputable def zeroRows {R : Type*} [Ring R] (y : Fin n → R) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => row R a i y = 0

@[simp] private theorem mem_zeroRows {R : Type*} [Ring R] {y : Fin n → R} {i : ι} :
    i ∈ zeroRows a y ↔ row R a i y = 0 := by
  classical
  simp [zeroRows]

private theorem zeroRows_closed {q : ℕ} (h : CentralGoodReduction a q) (y : Fin n → ZMod q) :
    centralClosure a (zeroRows a y) = zeroRows a y := by
  apply Finset.Subset.antisymm
  · intro i hi
    have hq := (h (zeroRows a y) i).1 ((mem_centralClosure a).1 hi)
    exact (mem_zeroRows a).2 (hq y fun j hj => (mem_zeroRows a).1 hj)
  · exact subset_centralClosure a _

private noncomputable def homogeneousTag {q : ℕ} (h : CentralGoodReduction a q)
    (y : Fin n → ZMod q) : ClosedTag a :=
  ⟨zeroRows a y, zeroRows_closed a h y⟩

variable {p q : ℕ}

/-- The exact affine complement at the product modulus. -/
def Complement (m : ℕ) :=
  {z : Fin n → ZMod m // ∀ i, row (ZMod m) a i z ≠ (b i : ZMod m)}

variable [DecidableEq ι]

private theorem hitRows_inter_eq_empty_iff {S : Finset ι} {x : Fin n → ZMod p} :
    hitRows a b x ∩ S = ∅ ↔ ∀ i ∈ S, row (ZMod p) a i x ≠ (b i : ZMod p) := by
  rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
  exact ⟨fun hd _ hi hx => hd ((mem_hitRows a b).2 hx) hi,
    fun ha i hx hi => ha i hi ((mem_hitRows a b).1 hx)⟩

/-- Avoid the affine rows indexed by `T` and require the exact homogeneous stratum `T`. -/
private def TaggedProduct (p q : ℕ) :=
  Σ T : ClosedTag a,
    {x : Fin n → ZMod p // hitRows a b x ∩ T.val = ∅} ×
    {y : Fin n → ZMod q // zeroRows a y = T.val}

private def TaggedProduct.first (t : TaggedProduct a b p q) : Fin n → ZMod p := t.2.1.val

private def TaggedProduct.second (t : TaggedProduct a b p q) : Fin n → ZMod q := t.2.2.val

private theorem TaggedProduct.avoids (t : TaggedProduct a b p q) (i : ι) (hi : i ∈ t.1.val) :
    row (ZMod p) a i (t.first a b) ≠ (b i : ZMod p) :=
  (hitRows_inter_eq_empty_iff a b).1 t.2.1.property i hi

private theorem TaggedProduct.exact_stratum (t : TaggedProduct a b p q) (i : ι) :
    i ∈ t.1.val ↔ row (ZMod q) a i (t.second a b) = 0 := by
  rw [← t.2.2.property]
  exact mem_zeroRows a

private theorem TaggedProduct.tag_eq_of_second_eq {s t : TaggedProduct a b p q}
    (hy : s.second a b = t.second a b) : s.1 = t.1 := by
  apply Subtype.ext
  exact s.2.2.property.symm.trans ((congrArg (zeroRows a) hy).trans t.2.2.property)

private theorem TaggedProduct.ext {s t : TaggedProduct a b p q}
    (hx : s.first a b = t.first a b) (hy : s.second a b = t.second a b) : s = t := by
  have ht := TaggedProduct.tag_eq_of_second_eq a b hy
  obtain ⟨S, sx, sy⟩ := s
  obtain ⟨T, tx, ty⟩ := t
  change S = T at ht
  subst T
  have hfirst : sx = tx := Subtype.ext hx
  have hsecond : sy = ty := Subtype.ext hy
  rw [hfirst, hsecond]

/-- Coordinatewise CRT, with the mod-`p` projection first. -/
private def crt (h : Nat.Coprime p q) :
    (Fin n → ZMod (p * q)) ≃ (Fin n → ZMod p) × (Fin n → ZMod q) where
  toFun z := (fun j => (ZMod.chineseRemainder h (z j)).1,
              fun j => (ZMod.chineseRemainder h (z j)).2)
  invFun xy j := (ZMod.chineseRemainder h).symm (xy.1 j, xy.2 j)
  left_inv z := by
    funext j
    exact (ZMod.chineseRemainder h).symm_apply_apply (z j)
  right_inv xy := by
    apply Prod.ext
    · funext j
      exact congrArg Prod.fst ((ZMod.chineseRemainder h).apply_symm_apply (xy.1 j, xy.2 j))
    · funext j
      exact congrArg Prod.snd ((ZMod.chineseRemainder h).apply_symm_apply (xy.1 j, xy.2 j))

private theorem crt_first_apply (h : Nat.Coprime p q) (z : Fin n → ZMod (p * q)) (j : Fin n) :
    (crt h z).1 j = ZMod.cast (z j) := by
  change (ZMod.cast (z j) : ZMod p × ZMod q).1 = _
  exact Prod.fst_zmod_cast _

omit [Fintype ι] [DecidableEq ι] in
private theorem crt_hit_iff (h : Nat.Coprime p q) (z : Fin n → ZMod (p * q)) (i : ι) :
    row (ZMod (p * q)) a i z = (b i : ZMod (p * q)) ↔
      row (ZMod p) a i (crt h z).1 = (b i : ZMod p) ∧
      row (ZMod q) a i (crt h z).2 = (b i : ZMod q) := by
  let e := ZMod.chineseRemainder h
  let fp := (RingHom.fst (ZMod p) (ZMod q)).comp e.toRingHom
  let fq := (RingHom.snd (ZMod p) (ZMod q)).comp e.toRingHom
  change _ ↔ row _ a i (fun j => fp (z j)) = _ ∧ row _ a i (fun j => fq (z j)) = _
  rw [← map_row fp, ← map_row fq, ← map_intCast fp (b i), ← map_intCast fq (b i)]
  constructor
  · intro hr
    exact ⟨congrArg fp hr, congrArg fq hr⟩
  · rintro ⟨hp, hq⟩
    exact e.injective (Prod.ext hp hq)

/-- A center over `q` for each first residue, solving all its hit rows. -/
private def Centers (p q : ℕ) :=
  {c : (Fin n → ZMod p) → Fin n → ZMod q //
    ∀ x i, i ∈ hitRows a b x → row (ZMod q) a i (c x) = (b i : ZMod q)}

private noncomputable def chooseCenters (hp : AffineGoodReduction a b p)
    (hq : AffineGoodReduction a b q) : Centers a b p q := by
  have solvable (x : Fin n → ZMod p) : AffineSolvable a b (ZMod q) (hitRows a b x) :=
    (hq _).1 ((hp _).2 ⟨x, fun _ hi => (mem_hitRows a b).1 hi⟩)
  exact ⟨fun x => Classical.choose (solvable x), fun x => Classical.choose_spec (solvable x)⟩

omit [DecidableEq ι] in
private theorem shifted_zero_iff (c : Centers a b p q) {x : Fin n → ZMod p}
    {i : ι} (hx : row (ZMod p) a i x = (b i : ZMod p)) (zq : Fin n → ZMod q) :
    row (ZMod q) a i (zq - c.val x) = 0 ↔ row (ZMod q) a i zq = (b i : ZMod q) := by
  rw [row_sub, c.property x i ((mem_hitRows a b).2 hx), sub_eq_zero]

/-- The forward map is CRT followed by subtraction of the center in the second coordinate. -/
private noncomputable def toTagged (h : Nat.Coprime p q) (hc : CentralGoodReduction a q)
    (c : Centers a b p q) (z : Complement a b (p * q)) : TaggedProduct a b p q := by
  let x := (crt h z.val).1
  let y := (crt h z.val).2 - c.val x
  refine ⟨homogeneousTag a hc y, ⟨⟨x, (hitRows_inter_eq_empty_iff a b).2 ?_⟩, ⟨y, rfl⟩⟩⟩
  intro i hi hx
  have hy : row (ZMod q) a i y = 0 := (mem_zeroRows a).1 hi
  exact z.property i ((crt_hit_iff a b h z.val i).2 ⟨hx, (shifted_zero_iff a b c hx _).1 hy⟩)

/-- The inverse adds the same center and applies inverse CRT. -/
private noncomputable def fromTagged (h : Nat.Coprime p q) (c : Centers a b p q)
    (t : TaggedProduct a b p q) : Complement a b (p * q) := by
  let x := t.first a b
  let y := t.second a b
  refine ⟨(crt h).symm (x, y + c.val x), ?_⟩
  intro i hi
  have hxy := (crt_hit_iff a b h _ i).1 hi
  rw [(crt h).apply_symm_apply] at hxy
  obtain ⟨hx, hq⟩ := hxy
  have hy := (shifted_zero_iff a b c hx _).2 hq
  have ht := (TaggedProduct.exact_stratum a b t i).2 (by simpa only [add_sub_cancel_right] using hy)
  exact t.avoids a b i ht hx

/-- CRT transport with any specified family of valid centers. -/
private noncomputable def transportWith (h : Nat.Coprime p q) (hc : CentralGoodReduction a q)
    (c : Centers a b p q) : Complement a b (p * q) ≃ TaggedProduct a b p q where
  toFun := toTagged a b h hc c
  invFun := fromTagged a b h c
  left_inv z := by
    apply Subtype.ext
    change (crt h).symm ((crt h z.val).1,
      (crt h z.val).2 - c.val (crt h z.val).1 + c.val (crt h z.val).1) = z.val
    rw [sub_add_cancel]
    exact (crt h).symm_apply_apply z.val
  right_inv t := by
    apply TaggedProduct.ext a b
    · change (crt h ((crt h).symm (t.first a b, t.second a b + c.val (t.first a b)))).1 = _
      rw [(crt h).apply_symm_apply]
    · change (crt h ((crt h).symm (t.first a b, t.second a b + c.val (t.first a b)))).2 -
        c.val (crt h ((crt h).symm (t.first a b, t.second a b + c.val (t.first a b)))).1 = _
      rw [(crt h).apply_symm_apply, Prod.fst, Prod.snd, add_sub_cancel_right]

/-- The conditional transport for the two good-reduction lemmas. -/
private noncomputable def transport (h : Nat.Coprime p q)
    (hp : AffineGoodReduction a b p) (hq : AffineGoodReduction a b q)
    (hc : CentralGoodReduction a q) : Complement a b (p * q) ≃ TaggedProduct a b p q :=
  transportWith a b h hc (chooseCenters a b hp hq)

private theorem transport_first (h : Nat.Coprime p q)
    (hp : AffineGoodReduction a b p) (hq : AffineGoodReduction a b q)
    (hc : CentralGoodReduction a q) (z : Complement a b (p * q)) (j : Fin n) :
    ((transport a b h hp hq hc) z).first a b j = ZMod.cast (z.val j) :=
  crt_first_apply h z.val j

end CentralizationTransport

namespace CentralizationBijection

open CentralizationTransport

/-- For a finite integral affine arrangement, a single positive (D) works for all
coprime (p,q>1) each coprime to (D). The first factor avoids the affine rows
whose normals vanish on the rational flat. The second factor lies in the
reduced flat and avoids every proper homogeneous restriction. -/
theorem result {ι : Type*} {n : ℕ} [Finite ι]
    (a : ι → Fin n → ℤ) (b : ι → ℤ) :
    ∃ D : ℕ, 0 < D ∧
      ∀ p q : ℕ, 1 < p → 1 < q → p.Coprime q → p.Coprime D → q.Coprime D →
        ∃ e : Complement a b (p * q) ≃
          (Σ V : RationalFlat a,
            {x : Fin n → ZMod p // ∀ i : ι,
              (∀ v ∈ V.val, row ℚ a i v = 0) → row (ZMod p) a i x ≠ (b i : ZMod p)} ×
            {y : Fin n → ZMod q //
              (∀ i : ι, (∀ v ∈ V.val, row ℚ a i v = 0) → row (ZMod q) a i y = 0) ∧
              (∀ i : ι, ¬ (∀ v ∈ V.val, row ℚ a i v = 0) → row (ZMod q) a i y ≠ 0)}),
          ∀ z j, (e z).2.1.val j = (ZMod.cast (z.val j) : ZMod p) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨D, hD, hReduction⟩ := CentralizationGoodReduction.exists_goodReduction a b
  refine ⟨D, hD, fun p q hp hq hpq hpD hqD => ?_⟩
  obtain ⟨hpAffine, _⟩ := hReduction p hp hpD
  obtain ⟨hqAffine, hqCentral⟩ := hReduction q hq hqD
  -- The good-reduction predicates and transport predicates unfold to the same row sums.
  let e := transport a b hpq hpAffine hqAffine hqCentral
  refine ⟨e.trans (Equiv.sigmaCongr (closedTagEquivFlat a) ?_), ?_⟩
  · intro T
    have hTag (i : ι) :
        i ∈ T.val ↔ ∀ v ∈ (closedTagEquivFlat a T).val, row ℚ a i v = 0 :=
      mem_tag_iff_flat a
    refine Equiv.prodCongr (Equiv.subtypeEquivRight fun x => ?_)
      (Equiv.subtypeEquivRight fun y => ?_)
    · rw [hitRows_inter_eq_empty_iff a b]
      exact ⟨fun hx i hi => hx i ((hTag i).2 hi), fun hx i hi => hx i ((hTag i).1 hi)⟩
    · constructor
      · intro hy
        have hZero (i : ι) : row (ZMod q) a i y = 0 ↔
            ∀ v ∈ (closedTagEquivFlat a T).val, row ℚ a i v = 0 := by
          rw [← mem_zeroRows a, hy]
          exact hTag i
        exact ⟨fun i => (hZero i).2, fun i hi hz => hi ((hZero i).1 hz)⟩
      · rintro ⟨hyIn, hyAvoid⟩
        apply Finset.ext
        intro i
        rw [mem_zeroRows]
        refine ⟨fun hz => ?_, fun hi => hyIn i ((hTag i).1 hi)⟩
        by_contra hi
        exact hyAvoid i (fun h => hi ((hTag i).2 h)) hz
  · intro z j
    exact transport_first a b hpq hpAffine hqAffine hqCentral z j

end CentralizationBijection

end D5.S3.Combinatorics.Geometry.HyperplaneArrangements
