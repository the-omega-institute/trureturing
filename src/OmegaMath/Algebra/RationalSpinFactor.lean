import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OmegaBuild.Commands

/-!
Omega original.

Rational spin-factor multiplication, signed coordinate axes and their
selected-axis Lie algebra, with and without a scalar direct summand.
The multiplication and orthogonal Lie algebras use their usual classical
definitions.
-/

compile_only_with_mathlib

open scoped Matrix
open Matrix LieAlgebra

namespace OmegaMath.RationalSpinFactor

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The spin factor with a vector coordinate for each index in `n`. -/
abbrev J (n : Type*) := ℚ × (n → ℚ)

/-- The spin factor with one scalar direct summand. -/
abbrev B (n : Type*) := J n × ℚ

variable {n : Type*} [Fintype n] [DecidableEq n]

def product (x y : B n) : B n :=
  ((x.1.1 * y.1.1 + x.1.2 ⬝ᵥ y.1.2, x.1.1 • y.1.2 + y.1.1 • x.1.2), x.2 * y.2)

omit [DecidableEq n] in
theorem product_comm (x y : B n) : product x y = product y x := by
  simp only [product, mul_comm x.1.1 y.1.1, dotProduct_comm x.1.2 y.1.2,
    add_comm (x.1.1 • y.1.2), mul_comm x.2 y.2]

def left : B n →ₗ[ℚ] Module.End ℚ (B n) :=
  LinearMap.mk₂ ℚ product
    (by
      intro x y z
      ext <;> simp [product, add_mul, add_dotProduct, add_smul] <;> ring)
    (by
      intro r x y
      ext <;> simp [product, smul_dotProduct, smul_eq_mul] <;> ring)
    (by
      intro x y z
      rw [product_comm x (y + z), product_comm x y, product_comm x z]
      ext <;> simp [product, add_mul, add_dotProduct, add_smul] <;> ring)
    (by
      intro r x y
      rw [product_comm x (r • y), product_comm x y]
      ext <;> simp [product, smul_dotProduct, smul_eq_mul] <;> ring)

private def spinAxis (s : n → ℚ) : B n := ((1 / 2, (1 / 2 : ℚ) • s), 0)
def z : B n := ((0, 0), 1)
def unitSpin : B n := ((1, 0), 0)
private def vector (s : n → ℚ) : B n := ((0, s), 0)
def coord (i : n) : n → ℚ := Pi.single i 1

def chosen : Set (B n) :=
  Set.range (fun i : n => spinAxis (coord i)) ∪
    Set.range (fun i : n => spinAxis (-coord i)) ∪ {z}

private def eig {A : Type*} [AddCommGroup A] [Module ℚ A]
    (L : A →ₗ[ℚ] Module.End ℚ A) (a : A) (t : ℚ) : Submodule ℚ A :=
  Module.End.eigenspace (L a) t

def IsAxis {A : Type*} [AddCommGroup A] [Module ℚ A]
    (L : A →ₗ[ℚ] Module.End ℚ A) (a : A) : Prop :=
  a ≠ 0 ∧ L a a = a ∧ eig L a 1 = ℚ ∙ a ∧
  eig L a 1 ⊔ eig L a 0 ⊔ eig L a (1 / 2) = ⊤ ∧
  (∀ x ∈ eig L a 1, ∀ y ∈ eig L a 1, L x y ∈ eig L a 1) ∧
  (∀ x ∈ eig L a 1, ∀ y ∈ eig L a 0, L x y = 0) ∧
  (∀ x ∈ eig L a 1, ∀ y ∈ eig L a (1 / 2), L x y ∈ eig L a (1 / 2)) ∧
  (∀ x ∈ eig L a 0, ∀ y ∈ eig L a 0, L x y ∈ eig L a 0) ∧
  (∀ x ∈ eig L a 0, ∀ y ∈ eig L a (1 / 2), L x y ∈ eig L a (1 / 2)) ∧
  (∀ x ∈ eig L a (1 / 2), ∀ y ∈ eig L a (1 / 2), L x y ∈ eig L a 1 ⊔ eig L a 0)

omit [DecidableEq n] in
private theorem mem_eig (a x : B n) (t : ℚ) :
    x ∈ eig left a t ↔ product a x = t • x :=
  Module.End.mem_eigenspace_iff

omit [DecidableEq n] in
private theorem spin_coords (s : n → ℚ) (x : B n) (t : ℚ) :
    x ∈ eig left (spinAxis s) t ↔
      (1 / 2 : ℚ) * (x.1.1 + s ⬝ᵥ x.1.2) = t * x.1.1 ∧
      (∀ i, (1 / 2 : ℚ) * (x.1.2 i + x.1.1 * s i) = t * x.1.2 i) ∧
      0 = t * x.2 := by
  rw [mem_eig]
  simp only [Prod.ext_iff]
  change (((1 / 2 : ℚ) * x.1.1 + (((1 / 2 : ℚ) • s) ⬝ᵥ x.1.2) = t * x.1.1) ∧
      (1 / 2 : ℚ) • x.1.2 + x.1.1 • ((1 / 2 : ℚ) • s) = t • x.1.2) ∧
      (0 : ℚ) * x.2 = t * x.2 ↔ _
  simp only [smul_dotProduct, smul_eq_mul, zero_mul, funext_iff, Pi.add_apply, Pi.smul_apply]
  constructor
  · rintro ⟨⟨ha, hv⟩, hz⟩
    refine ⟨?_, ?_, hz⟩
    · linarith
    · intro i
      have := hv i
      linarith
  · rintro ⟨ha, hv, hz⟩
    exact ⟨⟨by linarith, fun i => by have := hv i; linarith⟩, hz⟩

omit [DecidableEq n] in
private theorem spin_one (s : n → ℚ) (hs : s ⬝ᵥ s = 1) (x : B n) :
    x ∈ eig left (spinAxis s) 1 ↔ x.1.2 = x.1.1 • s ∧ x.2 = 0 := by
  rw [spin_coords]
  constructor
  · rintro ⟨_, hv, hz⟩
    refine ⟨funext (fun i => ?_), by linarith⟩
    change x.1.2 i = x.1.1 * s i
    have := hv i
    linarith
  · rintro ⟨hv, hz⟩
    simp only [hv, hz, dotProduct_smul, hs, one_mul, mul_zero]
    refine ⟨by ring, fun i => ?_, trivial⟩
    change (1 / 2 : ℚ) * (x.1.1 * s i + x.1.1 * s i) = x.1.1 * s i
    ring

omit [DecidableEq n] in
private theorem spin_zero (s : n → ℚ) (hs : s ⬝ᵥ s = 1) (x : B n) :
    x ∈ eig left (spinAxis s) 0 ↔ x.1.2 = (-x.1.1) • s := by
  rw [spin_coords]
  constructor
  · rintro ⟨_, hv, _⟩
    ext i
    change x.1.2 i = (-x.1.1) * s i
    have := hv i
    linarith
  · intro hv
    simp [hv, dotProduct_smul, hs]

omit [DecidableEq n] in
private theorem spin_half (s : n → ℚ) (hs : s ⬝ᵥ s = 1) (x : B n) :
    x ∈ eig left (spinAxis s) (1 / 2) ↔
      x.1.1 = 0 ∧ s ⬝ᵥ x.1.2 = 0 ∧ x.2 = 0 := by
  rw [spin_coords]
  constructor
  · rintro ⟨ha, hv, hz⟩
    have hv' : x.1.1 • s = 0 := by
      ext i
      change x.1.1 * s i = 0
      have := hv i
      linarith
    have hx : x.1.1 = 0 := by
      have h := congrArg (fun v => s ⬝ᵥ v) hv'
      simpa [dotProduct_smul, hs] using h
    exact ⟨hx, by linarith, by linarith⟩
  · rintro ⟨ha, hv, hz⟩
    simp [ha, hv, hz]

omit [DecidableEq n] in
private theorem z_eig (x : B n) (t : ℚ) :
    x ∈ eig left (z : B n) t ↔ t • x.1 = 0 ∧ x.2 = t * x.2 := by
  rw [mem_eig]
  rw [Prod.ext_iff]
  change (((0 : ℚ) * x.1.1 + (0 : n → ℚ) ⬝ᵥ x.1.2,
    (0 : ℚ) • x.1.2 + x.1.1 • (0 : n → ℚ)) = t • x.1) ∧ 1 * x.2 = t * x.2 ↔ _
  simp only [zero_mul, zero_dotProduct, add_zero, zero_smul, smul_zero, one_mul]
  change ((0 : ℚ × (n → ℚ)) = t • x.1) ∧ x.2 = t * x.2 ↔ _
  exact and_congr_left' eq_comm

def selectedLie {A : Type*} [AddCommGroup A] [Module ℚ A]
    (L : A →ₗ[ℚ] Module.End ℚ A) (X : Set A) : LieSubalgebra ℚ (Module.End ℚ A) :=
  LieSubalgebra.lieSpan ℚ (Module.End ℚ A) {F | ∃ a ∈ X, ∃ b ∈ X, F = ⁅L a, L b⁆}

def skewPair (u v : n → ℚ) : Orthogonal.so n ℚ :=
  ⟨vecMulVec u v - vecMulVec v u, by
    rw [Orthogonal.mem_so]
    simp [transpose_sub, transpose_vecMulVec, neg_sub]⟩

private def spinBlock : Orthogonal.so n ℚ →ₗ⁅ℚ⁆ Module.End ℚ (J n) where
  toFun M := (0 : Module.End ℚ ℚ).prodMap (Matrix.toLin' M.val)
  map_add' M N := by ext x <;> simp
  map_smul' c M := by ext x <;> simp
  map_lie' {M N} := by
    apply LinearMap.ext
    intro w
    refine Prod.ext ?_ ?_
    · simp [Ring.lie_def, Module.End.mul_apply]
    · change (M.val * N.val - N.val * M.val) *ᵥ w.2 =
        M.val *ᵥ (N.val *ᵥ w.2) - N.val *ᵥ (M.val *ᵥ w.2)
      rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

private def extendEnd : Module.End ℚ (J n) →ₗ⁅ℚ⁆ Module.End ℚ (B n) where
  toFun f := f.prodMap 0
  map_add' f g := by ext x <;> simp
  map_smul' c f := by ext x <;> simp
  map_lie' {f g} := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · simp [Ring.lie_def, Module.End.mul_apply]
    · simp [Ring.lie_def, Module.End.mul_apply]

private def vectorBlock : Orthogonal.so n ℚ →ₗ⁅ℚ⁆ Module.End ℚ (B n) :=
  extendEnd.comp spinBlock

private theorem left_bracket (x y : B n) :
    ⁅left x, left y⁆ = vectorBlock (skewPair x.1.2 y.1.2) := by
  apply LinearMap.ext
  intro w
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · change (product x (product y w)).1.1 - (product y (product x w)).1.1 = 0
    simp only [product, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm y.1.2 x.1.2]
    ring
  · change (product x (product y w)).1.2 - (product y (product x w)).1.2 =
      (vecMulVec x.1.2 y.1.2 - vecMulVec y.1.2 x.1.2) *ᵥ w.1.2
    rw [Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
    funext i
    simp [product, smul_eq_mul]
    ring
  · change (product x (product y w)).2 - (product y (product x w)).2 = 0
    simp only [product]
    ring

omit [Fintype n] in
private theorem positive_mem (i : n) : spinAxis (coord i) ∈ (chosen : Set (B n)) :=
  Or.inl (Or.inl ⟨i, rfl⟩)

omit [Fintype n] in
private theorem negative_mem (i : n) : spinAxis (-coord i) ∈ (chosen : Set (B n)) :=
  Or.inl (Or.inr ⟨i, rfl⟩)

omit [Fintype n] in
private theorem z_mem : (z : B n) ∈ chosen :=
  Or.inr rfl

private theorem selected_eq_range {A : Type*} [AddCommGroup A] [Module ℚ A]
    (L : A →ₗ[ℚ] Module.End ℚ A) (X : Set A) (dir : A → n → ℚ)
    (block : Orthogonal.so n ℚ →ₗ⁅ℚ⁆ Module.End ℚ A)
    (hbracket : ∀ x y, ⁅L x, L y⁆ = block (skewPair (dir x) (dir y)))
    (haxes : ∀ i, ∃ a ∈ X, dir a = (1 / 2 : ℚ) • coord i) :
    selectedLie L X = block.range := by
  apply le_antisymm
  · apply LieSubalgebra.lieSpan_le.mpr
    rintro F ⟨x, _, y, _, rfl⟩
    rw [hbracket]
    exact LieHom.mem_range_self _ _
  intro F hF
  obtain ⟨M, rfl⟩ := (block.mem_range F).mp hF
  have hcoord (i j : n) : block (skewPair (coord i) (coord j)) ∈ selectedLie L X := by
    obtain ⟨a, ha, hai⟩ := haxes i
    obtain ⟨b, hb, hbj⟩ := haxes j
    have h : ⁅L a, L b⁆ ∈ selectedLie L X :=
      LieSubalgebra.subset_lieSpan ⟨_, ha, _, hb, rfl⟩
    have hscale : skewPair ((1 / 2 : ℚ) • coord i) ((1 / 2 : ℚ) • coord j) =
        (1 / 4 : ℚ) • skewPair (coord i) (coord j) := by
      apply Subtype.ext
      change vecMulVec _ _ - vecMulVec _ _ = (1 / 4 : ℚ) • (vecMulVec _ _ - vecMulVec _ _)
      rw [smul_vecMulVec, vecMulVec_smul, smul_vecMulVec, vecMulVec_smul]
      norm_num [smul_smul, smul_sub]
    rw [hbracket, hai, hbj, hscale, map_smul] at h
    simpa [smul_smul] using (selectedLie L X).smul_mem (4 : ℚ) h
  have hsum : (∑ i, ∑ j, (M.val i j / 2) • skewPair (coord i) (coord j)) = M := by
    apply Subtype.ext
    change (Orthogonal.so n ℚ).incl (∑ i, ∑ j, (M.val i j / 2) • skewPair (coord i) (coord j)) =
      M.val
    simp only [map_sum, map_smul]
    change (∑ i, ∑ j, (M.val i j / 2) •
      (vecMulVec (coord i) (coord j) - vecMulVec (coord j) (coord i))) = M.val
    simp only [coord, ← Matrix.single_eq_single_vecMulVec_single, smul_sub, Matrix.smul_single,
      smul_eq_mul, mul_one, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => Matrix.single j i (M.val i j / 2))]
    rw [Matrix.sum_sum_single, Matrix.sum_sum_single]
    have hm := (Orthogonal.mem_so n ℚ M.val).mp M.property
    ext i j
    have hij := congrArg (fun A : Matrix n n ℚ => A i j) hm
    change M.val j i = -M.val i j at hij
    change M.val i j / 2 - M.val j i / 2 = M.val i j
    linarith
  rw [← hsum, map_sum]
  exact (selectedLie L X).sum_mem fun i _ => by
    rw [map_sum]
    exact (selectedLie L X).sum_mem fun j _ => by
      rw [map_smul]
      exact (selectedLie L X).smul_mem _ (hcoord i j)

/-- The selected-axis Lie span is the skew block on the vector coordinates. -/
noncomputable def chosenLieEquiv :
    Orthogonal.so n ℚ ≃ₗ⁅ℚ⁆ selectedLie left (chosen : Set (B n)) := by
  rw [selected_eq_range left chosen (fun x => x.1.2) vectorBlock left_bracket
    (fun i => ⟨spinAxis (coord i), positive_mem i, rfl⟩)]
  apply vectorBlock.equivRangeOfInjective
  intro M N h
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  exact congrArg (fun f : Module.End ℚ (B n) => (f (vector v)).1.2) h

omit [DecidableEq n] in
private theorem spin_axis (s : n → ℚ) (hs : s ⬝ᵥ s = 1) :
    IsAxis left (spinAxis s) := by
  have ha : spinAxis s ∈ eig left (spinAxis s) 1 :=
    (spin_one s hs _).mpr ⟨rfl, rfl⟩
  have hb : spinAxis (-s) ∈ eig left (spinAxis s) 0 := by
    apply (spin_zero s hs _).mpr
    simp [spinAxis, smul_neg, neg_smul]
  have hz : (z : B n) ∈ eig left (spinAxis s) 0 :=
    (spin_zero s hs _).mpr (by simp [z])
  have hu : (unitSpin : B n) ∈ eig left (spinAxis s) 1 ⊔ eig left (spinAxis s) 0 :=
    Submodule.mem_sup.mpr ⟨_, ha, _, hb, by
      refine Prod.ext (Prod.ext ?_ ?_) (by norm_num [spinAxis, unitSpin, vector])
      · norm_num [spinAxis, unitSpin]
      · simp [spinAxis, unitSpin, smul_neg]⟩
  have hline : eig left (spinAxis s) 1 = ℚ ∙ spinAxis s := by
    apply le_antisymm _ ((Submodule.span_singleton_le_iff_mem _ _).mpr ha)
    intro x hx
    obtain ⟨hv, hxz⟩ := (spin_one s hs x).mp hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨2 * x.1.1, Prod.ext (Prod.ext ?_ ?_) ?_⟩
    · change (2 * x.1.1) * (1 / 2) = x.1.1
      ring
    · change (2 * x.1.1) • ((1 / 2 : ℚ) • s) = x.1.2
      rw [smul_smul, hv]
      congr 1
      ring
    · simpa [spinAxis] using hxz.symm
  refine ⟨?_, ?_, hline, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun x : B n => x.1.1) h
    norm_num [spinAxis] at this
  · change product (spinAxis s) (spinAxis s) = spinAxis s
    simpa using (mem_eig (spinAxis s) _ 1).mp ha
  · apply top_unique
    intro x _
    let t := s ⬝ᵥ x.1.2
    let xp : B n := (x.1.1 + t) • spinAxis s
    let xm : B n := (x.1.1 - t) • spinAxis (-s) + x.2 • z
    let xh : B n := vector (x.1.2 - t • s)
    refine Submodule.mem_sup.mpr ⟨xp + xm, ?_, xh, ?_, ?_⟩
    · exact Submodule.mem_sup.mpr ⟨xp, (eig left _ 1).smul_mem _ ha, xm,
        (eig left _ 0).add_mem ((eig left _ 0).smul_mem _ hb) ((eig left _ 0).smul_mem _ hz),
        rfl⟩
    · apply (spin_half s hs _).mpr
      simp [xh, vector, dotProduct_sub, dotProduct_smul, hs, t]
    · refine Prod.ext (Prod.ext ?_ ?_) ?_
      · change (x.1.1 + t) * (1 / 2) + ((x.1.1 - t) * (1 / 2) + x.2 * 0) + 0 = x.1.1
        ring
      · funext i
        change (x.1.1 + t) * ((1 / 2) * s i) +
          ((x.1.1 - t) * ((1 / 2) * (-s i)) + x.2 * 0) + (x.1.2 i - t * s i) = x.1.2 i
        ring
      · change (x.1.1 + t) * 0 + ((x.1.1 - t) * 0 + x.2 * 1) + 0 = x.2
        ring
  · intro x hx y hy
    rw [hline] at hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, LinearMap.smul_apply]
    rw [show left (spinAxis s) y = (1 : ℚ) • y from Module.End.mem_eigenspace_iff.mp hy]
    exact (eig left _ 1).smul_mem _ ((eig left _ 1).smul_mem _ hy)
  · intro x hx y hy
    rw [hline] at hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, LinearMap.smul_apply,
      show left (spinAxis s) y = (0 : ℚ) • y from Module.End.mem_eigenspace_iff.mp hy]
    simp
  · intro x hx y hy
    rw [hline] at hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, LinearMap.smul_apply,
      show left (spinAxis s) y = (1 / 2 : ℚ) • y from Module.End.mem_eigenspace_iff.mp hy]
    exact (eig left _ _).smul_mem _ ((eig left _ _).smul_mem _ hy)
  · intro x hx y hy
    have hx' := (spin_zero s hs x).mp hx
    have hy' := (spin_zero s hs y).mp hy
    apply (spin_zero s hs _).mpr
    change (product x y).1.2 = (-(product x y).1.1) • s
    funext i
    simp [product, hx', hy', smul_dotProduct, dotProduct_smul, hs, smul_eq_mul]
    ring
  · intro x hx y hy
    have hx' := (spin_zero s hs x).mp hx
    obtain ⟨hya, hyv, hyz⟩ := (spin_half s hs y).mp hy
    apply (spin_half s hs _).mpr
    change (product x y).1.1 = 0 ∧ s ⬝ᵥ (product x y).1.2 = 0 ∧ (product x y).2 = 0
    simp [product, hx', hya, hyv, hyz, smul_dotProduct, dotProduct_smul]
  · intro x hx y hy
    obtain ⟨hxa, _, hxz⟩ := (spin_half s hs x).mp hx
    obtain ⟨hya, _, hyz⟩ := (spin_half s hs y).mp hy
    change product x y ∈ _
    have hxy : product x y = (x.1.2 ⬝ᵥ y.1.2) • unitSpin := by
      simp [product, unitSpin, hxa, hya, hxz, hyz]
    rw [hxy]
    exact Submodule.smul_mem _ _ hu

omit [DecidableEq n] in
omit [DecidableEq n] in
private theorem z_axis : IsAxis left (z : B n) := by
  have h1 (x : B n) : x ∈ eig left z 1 ↔ x.1 = 0 := by simp [z_eig]
  have h0 (x : B n) : x ∈ eig left z 0 ↔ x.2 = 0 := by simp [z_eig]
  have hh (x : B n) : x ∈ eig left z (1 / 2) ↔ x = 0 := by
    rw [z_eig]
    have ht : (1 / 2 : ℚ) ≠ 0 := by norm_num
    constructor
    · rintro ⟨hspin, hscalar⟩
      have hs : x.2 = 0 := by linarith
      exact Prod.ext ((smul_eq_zero.mp hspin).resolve_left ht) (show x.2 = 0 from hs)
    · rintro rfl
      simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg Prod.snd h
    norm_num [z] at this
  · change product z z = z
    simp [product, z]
  · ext x
    rw [h1, Submodule.mem_span_singleton]
    constructor
    · intro hx
      exact ⟨x.2, Prod.ext (by rw [hx, z]; simp) (by simp [z])⟩
    · rintro ⟨r, rfl⟩
      simp [z]
  · apply top_unique
    rintro ⟨u, t⟩ _
    apply (le_sup_left : eig left z 1 ⊔ eig left z 0 ≤ _ )
    exact (Submodule.mem_sup.mpr
      ⟨(0, t), (h1 _).mpr rfl, (u, 0), (h0 _).mpr rfl, by simp⟩)
  · intro x hx y hy
    apply (h1 _).mpr
    obtain ⟨⟨a, u⟩, t⟩ := x
    obtain ⟨⟨b, v⟩, w⟩ := y
    simp [h1] at hx hy
    change (product ((a, u), t) ((b, v), w)).1 = 0
    simp [product, hx, hy]
  · intro x hx y hy
    obtain ⟨⟨a, u⟩, t⟩ := x
    obtain ⟨⟨b, v⟩, w⟩ := y
    simp [h1] at hx
    simp [h0] at hy
    change product ((a, u), t) ((b, v), w) = 0
    simp [product, hx, hy]
  · intro x _ y hy
    rw [(hh y).mp hy, map_zero]
    exact Submodule.zero_mem _
  · intro x hx y hy
    apply (h0 _).mpr
    change x.2 * y.2 = 0
    rw [(h0 x).mp hx, zero_mul]
  · intro x _ y hy
    rw [(hh y).mp hy, map_zero]
    exact Submodule.zero_mem _
  · intro x _ y hy
    rw [(hh y).mp hy, map_zero]
    exact Submodule.zero_mem _

theorem chosen_axes (a : B n) (ha : a ∈ chosen) : IsAxis left a := by
  rcases ha with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ha
  · exact spin_axis (coord i) (by simp [coord])
  · exact spin_axis (-coord i) (by simp [coord, dotProduct_neg])
  · obtain rfl : a = z := ha
    exact z_axis

omit [Fintype n] in
private theorem chosen_spans [Finite n] [Nonempty n] :
    Submodule.span ℚ (chosen : Set (B n)) = ⊤ := by
  let := Fintype.ofFinite n
  let W := Submodule.span ℚ (chosen : Set (B n))
  have hp (i : n) : spinAxis (coord i) ∈ W := Submodule.subset_span (positive_mem i)
  have hm (i : n) : spinAxis (-coord i) ∈ W := Submodule.subset_span (negative_mem i)
  have hAdd (i : n) : spinAxis (coord i) + spinAxis (-coord i) = unitSpin := by
    refine Prod.ext (Prod.ext ?_ ?_) (by norm_num [spinAxis, unitSpin, vector])
    · norm_num [spinAxis, unitSpin]
    · simp [spinAxis, unitSpin, smul_neg]
  have hSub (i : n) : spinAxis (coord i) - spinAxis (-coord i) = vector (coord i) := by
    refine Prod.ext (Prod.ext ?_ ?_) (by norm_num [spinAxis, unitSpin, vector])
    · simp [spinAxis, vector]
    · funext j
      change (1 / 2) * coord i j - (1 / 2) * (-coord i j) = coord i j
      ring
  let i : n := Classical.choice inferInstance
  have hu : (unitSpin : B n) ∈ W := hAdd i ▸ W.add_mem (hp i) (hm i)
  have hz : (z : B n) ∈ W := Submodule.subset_span z_mem
  have hv (v : n → ℚ) : vector v ∈ W := by
    have hsum : (∑ j, v j • vector (coord j)) = vector v := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · simp [vector, Prod.fst_sum]
      · simp only [vector, Prod.fst_sum, Prod.snd_sum, Prod.smul_mk, coord]
        exact (pi_eq_sum_univ' v).symm
      · simp [vector, Prod.snd_sum]
    rw [← hsum]
    exact W.sum_mem fun j _ => W.smul_mem _ (hSub j ▸ W.sub_mem (hp j) (hm j))
  apply top_unique
  rintro ⟨⟨r, v⟩, t⟩ _
  have h : r • (unitSpin : B n) + vector v + t • z = ((r, v), t) := by
    simp [unitSpin, vector, z]
  rw [← h]
  exact W.add_mem (W.add_mem (W.smul_mem _ hu) (hv v)) (W.smul_mem _ hz)

def Generates {A : Type*} [AddCommGroup A] [Module ℚ A]
    (L : A →ₗ[ℚ] Module.End ℚ A) (X : Set A) : Prop :=
  ∀ S : Submodule ℚ A, X ⊆ S → (∀ x ∈ S, ∀ y ∈ S, L x y ∈ S) → S = ⊤

def AlgebraSimple {A : Type*} [AddCommGroup A] [Module ℚ A]
    (L : A →ₗ[ℚ] Module.End ℚ A) : Prop :=
  ∀ I : Submodule ℚ A, (∀ a x, x ∈ I → L a x ∈ I) → I = ⊥ ∨ I = ⊤

theorem chosen_generates [Nonempty n] : Generates left (chosen : Set (B n)) := by
  intro S hS _
  apply top_unique
  rw [← chosen_spans]
  exact Submodule.span_le.mpr hS

/-- Left multiplication for the rational spin product on the pair carrier. -/
def spinLeft : J n →ₗ[ℚ] Module.End ℚ (J n) :=
  (left.compl₁₂ (LinearMap.inl ℚ _ _) (LinearMap.inl ℚ _ _)).compr₂ₛₗ (LinearMap.fst ℚ _ _)

omit [DecidableEq n] in
theorem spinLeft_apply (x y : J n) :
    spinLeft x y = (x.1 * y.1 + x.2 ⬝ᵥ y.2, x.1 • y.2 + y.1 • x.2) := rfl

omit [DecidableEq n] in
private theorem spin_first (x y : B n) : (left x y).1 = spinLeft x.1 y.1 := rfl

/-- The two signed half-axes for each coordinate. -/
def signedAxes : Set (J n) :=
  Set.range (fun i : n => (spinAxis (coord i)).1) ∪
    Set.range (fun i : n => (spinAxis (-coord i)).1)

omit [DecidableEq n] in
private theorem spin_eig_fst {s : n → ℚ} {t : ℚ} {x : B n}
    (h : x ∈ eig left (spinAxis s) t) : x.1 ∈ eig spinLeft (spinAxis s).1 t :=
  Module.End.mem_eigenspace_iff.mpr (congrArg Prod.fst (mem_eig _ _ _ |>.mp h))

omit [DecidableEq n] in
private theorem spin_eig_embed {s : n → ℚ} {t : ℚ} {x : J n}
    (h : x ∈ eig spinLeft (spinAxis s).1 t) : (x, 0) ∈ eig left (spinAxis s) t := by
  apply Module.End.mem_eigenspace_iff.mpr
  exact Prod.ext (Module.End.mem_eigenspace_iff.mp h) (by simp [show
    (left (spinAxis s) (x, 0)).2 = (0 : ℚ) * 0 from rfl])

omit [DecidableEq n] in
private theorem spin_eig_sup_fst {s : n → ℚ} {r t : ℚ} {x : B n}
    (h : x ∈ eig left (spinAxis s) r ⊔ eig left (spinAxis s) t) :
    x.1 ∈ eig spinLeft (spinAxis s).1 r ⊔ eig spinLeft (spinAxis s).1 t := by
  obtain ⟨y, hy, w, hw, heq⟩ := Submodule.mem_sup.mp h
  exact Submodule.mem_sup.mpr ⟨y.1, spin_eig_fst hy, w.1, spin_eig_fst hw,
    congrArg Prod.fst heq⟩

omit [DecidableEq n] in
private theorem pure_axis (s : n → ℚ) (hs : s ⬝ᵥ s = 1) :
    IsAxis spinLeft (spinAxis s).1 := by
  obtain ⟨_, hidem, hline, hspan, h11, h10, h1h, h00, h0h, hhh⟩ := spin_axis s hs
  refine ⟨?_, congrArg Prod.fst hidem, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hfst := congrArg Prod.fst h
    norm_num [spinAxis] at hfst
  · apply le_antisymm
    · intro x hx
      have hx' := spin_eig_embed hx
      rw [hline] at hx'
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx'
      exact Submodule.mem_span_singleton.mpr ⟨r, congrArg Prod.fst hr⟩
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      exact spin_eig_fst ((spin_one s hs _).mpr ⟨rfl, rfl⟩)
  · apply top_unique
    intro x _
    have hx : (x, (0 : ℚ)) ∈ eig left (spinAxis s) 1 ⊔ eig left (spinAxis s) 0 ⊔
        eig left (spinAxis s) (1 / 2) := hspan.symm ▸ Submodule.mem_top
    obtain ⟨y, hy, w, hw, heq⟩ := Submodule.mem_sup.mp hx
    exact Submodule.mem_sup.mpr ⟨y.1, spin_eig_sup_fst hy, w.1, spin_eig_fst hw,
      congrArg Prod.fst heq⟩
  · intro x hx y hy
    exact spin_eig_fst (h11 _ (spin_eig_embed hx) _ (spin_eig_embed hy))
  · intro x hx y hy
    exact congrArg Prod.fst (h10 _ (spin_eig_embed hx) _ (spin_eig_embed hy))
  · intro x hx y hy
    exact spin_eig_fst (h1h _ (spin_eig_embed hx) _ (spin_eig_embed hy))
  · intro x hx y hy
    exact spin_eig_fst (h00 _ (spin_eig_embed hx) _ (spin_eig_embed hy))
  · intro x hx y hy
    exact spin_eig_fst (h0h _ (spin_eig_embed hx) _ (spin_eig_embed hy))
  · intro x hx y hy
    exact spin_eig_sup_fst (hhh _ (spin_eig_embed hx) _ (spin_eig_embed hy))

theorem signedAxes_are_axes (a : J n) (ha : a ∈ signedAxes) : IsAxis spinLeft a := by
  rcases ha with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact pure_axis (coord i) (by simp [coord])
  · exact pure_axis (-coord i) (by simp [coord, dotProduct_neg])

theorem signedAxes_generate [Nonempty n] :
    Generates spinLeft (signedAxes : Set (J n)) := by
  intro S hS _
  let fst : B n →ₗ[ℚ] J n := LinearMap.fst ℚ _ _
  have h : Submodule.span ℚ (chosen : Set (B n)) ≤ S.comap fst :=
    Submodule.span_le.mpr (by
      intro x hx
      rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩) | hx
      · exact hS (Or.inl ⟨i, rfl⟩)
      · exact hS (Or.inr ⟨i, rfl⟩)
      · obtain rfl : x = z := hx
        exact S.zero_mem)
  rw [chosen_spans] at h
  exact top_unique fun x _ => h (show (x, (0 : ℚ)) ∈ (⊤ : Submodule ℚ (B n)) from trivial)

private theorem spinBracket (x y : J n) :
    ⁅spinLeft x, spinLeft y⁆ = spinBlock (skewPair x.2 y.2) := by
  apply LinearMap.ext
  intro w
  have h := congrArg (fun f : Module.End ℚ (B n) => (f (w, 0)).1)
    (left_bracket (x, 0) (y, 0))
  change (⁅left (x, 0), left (y, 0)⁆ (w, 0)).1 = spinBlock (skewPair x.2 y.2) w at h
  simpa only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Prod.fst_sub,
    spin_first] using h

/-- A commutator of spin left multiplications vanishes on the unit coordinate. -/
theorem spinBracket_apply (x y w : J n) :
    ⁅spinLeft x, spinLeft y⁆ w = (0, (skewPair x.2 y.2).val *ᵥ w.2) := by
  rw [spinBracket]
  rfl

/-- The selected-axis Lie algebra on the pair carrier is the actual standard orthogonal algebra. -/
noncomputable def signedAxesLieEquiv :
    Orthogonal.so n ℚ ≃ₗ⁅ℚ⁆ selectedLie spinLeft (signedAxes : Set (J n)) := by
  rw [selected_eq_range spinLeft signedAxes Prod.snd spinBlock spinBracket
    (fun i => ⟨(spinAxis (coord i)).1, Or.inl ⟨i, rfl⟩, rfl⟩)]
  apply spinBlock.equivRangeOfInjective
  intro M N h
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  exact congrArg (fun f : Module.End ℚ (J n) => (f (0, v)).2) h

end OmegaMath.RationalSpinFactor
