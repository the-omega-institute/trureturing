/- GID: D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Common finite stages and an augmentation-first rational splitting connect the actual dimension-group action to natural equal powers, sharp rational cutoffs and every original fixed-block attachment. -/

import Mathlib.Algebra.Colimit.Module
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Order.WithBot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis
import D5.S3.ConceptDynamics.Coding.FixedBlockRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Module
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity

namespace D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy

universe u

section StationaryColimitActionContent

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The actual stationary system, with the original forward stationaryTransition T. -/
def stationaryTransition (T : Module.End R M) (i j : ℕ) (_ : i ≤ j) : Module.End R M :=
  T ^ (j-i)

instance stationarySystem (T : Module.End R M) :
    DirectedSystem (fun _ : ℕ => M) (fun i j h => stationaryTransition T i j h) where
  map_self x := by simp [stationaryTransition]
  map_map := by
    intro k j i hij hjk x
    change (T^(k-j)) ((T^(j-i)) x) = (T^(k-i)) x
    rw [← Module.End.mul_apply, ← pow_add]
    congr 2
    omega

abbrev StationaryModule (T : Module.End R M) :=
  Module.DirectLimit (fun _ : ℕ => M) (stationaryTransition T)

/-- A commuting endomorphism acts on the actual direct limit. -/
def induced (T P : Module.End R M) (hPT : Commute P T) :
    Module.End R (StationaryModule T) :=
  Module.DirectLimit.map (fun _ : ℕ => P) (by
    intro i j hij
    change P * T^(j-i) = T^(j-i) * P
    exact (hPT.pow_right (j-i)).eq)

private theorem propagate (T P : Module.End R M) {a k : ℕ} (hak : a ≤ k)
    (h : T^a * P = T^a) : T^k * P = T^k := by
  have h' := congrArg (fun Q : Module.End R M => T^(k-a) * Q) h
  simpa only [← mul_assoc, ← pow_add, Nat.sub_add_cancel hak] using h'

/-- Identity on a stationary direct limit is detected at one finite stage
uniformly on a finite basis. No desired matrix-power equality is assumed. -/
private theorem induced_eq_id_iff {I : Type*} [Fintype I]
    (b : Basis I R M) (T P : Module.End R M) (hPT : Commute P T) :
    induced T P hPT = LinearMap.id ↔ ∃ N : ℕ, T^N * P = T^N := by
  classical
  constructor
  · intro h
    have each (i : I) : ∃ N : ℕ, (T^N) (P (b i)) = (T^N) (b i) := by
      have hi := LinearMap.congr_fun h
        (Module.DirectLimit.of R ℕ (fun _ : ℕ => M) (stationaryTransition T) 0 (b i))
      simp only [induced, Module.DirectLimit.map_apply_of, LinearMap.id_apply] at hi
      obtain ⟨N, h0N, hN⟩ := Module.DirectLimit.exists_eq_of_of_eq hi
      exact ⟨N, by simpa only [stationaryTransition, Nat.sub_zero] using hN⟩
    choose stage stage_eq using each
    let N : ℕ := Finset.univ.sup stage
    refine ⟨N, b.ext (fun i => ?_)⟩
    have hi : stage i ≤ N := Finset.le_sup (f := stage) (Finset.mem_univ i)
    have heq := congrArg (fun x : M => (T^(N-stage i)) x) (stage_eq i)
    change (T^N) (P (b i)) = (T^N) (b i)
    simpa only [← Module.End.mul_apply, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hi] using heq
  · rintro ⟨N, hN⟩
    apply Module.DirectLimit.hom_ext
    intro i
    apply LinearMap.ext
    intro x
    change induced T P hPT
        (Module.DirectLimit.of R ℕ (fun _ : ℕ => M) (stationaryTransition T) i x) =
      Module.DirectLimit.of R ℕ (fun _ : ℕ => M) (stationaryTransition T) i x
    rw [induced, Module.DirectLimit.map_apply_of]
    have lift_stage (v : M) :
        Module.DirectLimit.of R ℕ (fun _ : ℕ => M) (stationaryTransition T) (i+N)
          ((T^N) v) =
        Module.DirectLimit.of R ℕ (fun _ : ℕ => M) (stationaryTransition T) i v := by
      simpa only [stationaryTransition, Nat.add_sub_cancel_left] using
        (Module.DirectLimit.of_f (R := R) (ι := ℕ) (G := fun _ : ℕ => M)
          (f := stationaryTransition T) (i := i) (j := i+N) (hij := Nat.le_add_right i N) (x := v))
    calc
      _ = Module.DirectLimit.of R ℕ (fun _ : ℕ => M) (stationaryTransition T) (i+N)
            ((T^N) (P x)) := (lift_stage (P x)).symm
      _ = Module.DirectLimit.of R ℕ (fun _ : ℕ => M) (stationaryTransition T) (i+N)
            ((T^N) x) := by
        exact congrArg (Module.DirectLimit.of R ℕ (fun _ : ℕ => M)
          (stationaryTransition T) (i+N)) (LinearMap.congr_fun hN x)
      _ = _ := lift_stage x

/-- A finite family acting identically on the dimension group has one common
annihilation stage; conversely one common stage proves identity on every level.
For original18.1, R=Z, I=Fin n x H, and P is the original left H action. -/
theorem finite_family_inert_iff_eventual {I Γ : Type*} [Fintype I] [Fintype Γ]
    (b : Basis I R M) (T : Module.End R M) (P : Γ → Module.End R M)
    (hPT : ∀ g, Commute (P g) T) :
    (∀ g, induced T (P g) (hPT g) = LinearMap.id) ↔
      ∃ N : ℕ, ∀ g, T^N * P g = T^N := by
  classical
  constructor
  · intro h
    have each : ∀ g, ∃ N : ℕ, T^N * P g = T^N :=
      fun g => (induced_eq_id_iff b T (P g) (hPT g)).mp (h g)
    choose stage hstage using each
    refine ⟨Finset.univ.sup stage, fun g => ?_⟩
    exact propagate T (P g) (Finset.le_sup (f := stage) (Finset.mem_univ g)) (hstage g)
  · rintro ⟨N, hN⟩ g
    exact (induced_eq_id_iff b T (P g) (hPT g)).mpr ⟨N, hN g⟩

end StationaryColimitActionContent

section NaturalGroupMatrixUniformizationContent

variable {H : Type*} [Group H] [Fintype H] {n : ℕ}

/-- Actual naturalAugmentation of the natural group algebra. -/
def naturalAugmentation : MonoidAlgebra ℕ H →+* ℕ :=
  (MonoidAlgebra.lift ℕ ℕ H (1 : H →* ℕ)).toRingHom

def matrixAugmentation : GroupMat H n n →+* Matrix (Fin n) (Fin n) ℕ :=
  (naturalAugmentation (H := H)).mapMatrix

/-- Equality of all actual coefficients, including zero coefficients. -/
def NaturalUniform (x : MonoidAlgebra ℕ H) : Prop :=
  ∀ g : H, x.coeff g = x.coeff 1

def UniformMatrix (A : GroupMat H n n) : Prop := ∀ i j, NaturalUniform (A i j)

def Uniformizes (A : GroupMat H n n) : Prop :=
  ∃ k : ℕ, 0 < k ∧ UniformMatrix (A^k)

/-- Least positive uniformizing exponent, only when it exists. -/
def positiveTau (A : GroupMat H n n) (hA : Uniformizes A) : ℕ := by
  classical
  exact Nat.find hA

/-- Original positive-exponent convention, with infinity if no exponent exists. -/
def tau (A : GroupMat H n n) : WithTop ℕ := by
  classical
  exact if hA : Uniformizes A then (positiveTau A hA : WithTop ℕ) else ⊤

theorem naturalAugmentation_eq_sum (x : MonoidAlgebra ℕ H) :
    naturalAugmentation x = ∑ g : H, x.coeff g := by
  classical
  change MonoidAlgebra.lift ℕ ℕ H (1 : H →* ℕ) x = _
  rw [MonoidAlgebra.lift_apply']
  simp only [MonoidHom.one_apply, Algebra.algebraMap_self, RingHom.id_apply, mul_one]
  exact Finsupp.sum_fintype _ _ (fun _ => rfl)

private theorem augmentation_of_uniform (x : MonoidAlgebra ℕ H) (hx : NaturalUniform x) :
    naturalAugmentation x = Fintype.card H * x.coeff 1 := by
  change ∀ g, x.coeff g = x.coeff 1 at hx
  rw [naturalAugmentation_eq_sum]
  simp_rw [hx]
  simp

/-- NaturalUniform natural coefficients are determined by their actual naturalAugmentation. -/
private theorem uniform_eq_of_augmentation_eq (x y : MonoidAlgebra ℕ H)
    (hx : NaturalUniform x) (hy : NaturalUniform y) (h : naturalAugmentation x = naturalAugmentation y) : x = y := by
  have hs : 0 < Fintype.card H := Fintype.card_pos_iff.mpr ⟨1⟩
  have h1 : x.coeff 1 = y.coeff 1 := by
    apply Nat.eq_of_mul_eq_mul_left hs
    simpa only [augmentation_of_uniform x hx, augmentation_of_uniform y hy] using h
  ext g
  exact (hx g).trans (h1.trans (hy g).symm)

private theorem natural_uniform_mul_right (x y : MonoidAlgebra ℕ H) (hx : NaturalUniform x) :
    NaturalUniform (x*y) := by
  change ∀ g, x.coeff g = x.coeff 1 at hx
  intro g
  rw [MonoidAlgebra.coeff_mul_apply_right, MonoidAlgebra.coeff_mul_apply_right]
  simp_rw [hx]

/-- Uniformity is preserved by right multiplication, without commutativity of H. -/
private theorem uniformMatrix_mul_right (A B : GroupMat H n n)
    (hA : UniformMatrix A) : UniformMatrix (A*B) := by
  classical
  intro i j g
  change (∑ t, A i t * B t j).coeff g = (∑ t, A i t * B t j).coeff 1
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro t _
  exact natural_uniform_mul_right (A i t) (B t j) (hA i t) g

/-- One uniform power implies every later power is uniform. -/
theorem uniform_power_mono (A : GroupMat H n n) {a k : ℕ}
    (hak : a ≤ k) (ha : UniformMatrix (A^a)) : UniformMatrix (A^k) := by
  rw [← Nat.add_sub_of_le hak, pow_add]
  exact uniformMatrix_mul_right (A^a) (A^(k-a)) ha

private theorem positiveTau_spec (A : GroupMat H n n) (hA : Uniformizes A) :
    0 < positiveTau A hA ∧ UniformMatrix (A^(positiveTau A hA)) := by
  classical
  exact Nat.find_spec hA

private theorem positiveTau_le (A : GroupMat H n n) (hA : Uniformizes A)
    {k : ℕ} (hk : 0 < k) (hu : UniformMatrix (A^k)) : positiveTau A hA ≤ k := by
  classical
  exact Nat.find_min' hA ⟨hk, hu⟩

/-- The output is equality in the original natural group-matrix ring. -/
private theorem equal_power_of_uniform (A B : GroupMat H n n) {k : ℕ}
    (haug : matrixAugmentation A = matrixAugmentation B)
    (hA : UniformMatrix (A^k)) (hB : UniformMatrix (B^k)) : A^k = B^k := by
  have hpow : matrixAugmentation (A^k) = matrixAugmentation (B^k) := by
    simpa only [map_pow] using congrArg (fun M => M^k) haug
  ext i j g
  exact congrArg (fun x : MonoidAlgebra ℕ H => x.coeff g)
    (uniform_eq_of_augmentation_eq ((A^k) i j) ((B^k) i j) (hA i j) (hB i j)
      (congrFun (congrFun hpow i) j))

/-- The positive-exponent convention applies also to the zero matrix. -/
private theorem one_le_tau (A : GroupMat H n n) : (1 : WithTop ℕ) ≤ tau A := by
  classical
  by_cases hA : Uniformizes A
  · have hpos : 1 ≤ positiveTau A hA := (positiveTau_spec A hA).1
    simpa [tau, hA] using hpos
  · simp [tau, hA]

/-- A finite upper bound on tau is equivalent to uniformity at that exact
positive exponent. Infinity and exponent zero are handled by the same statement. -/
theorem tau_le_iff_uniform_power (A : GroupMat H n n) (k : ℕ) :
    tau A ≤ (k : WithTop ℕ) ↔ 0 < k ∧ UniformMatrix (A^k) := by
  classical
  constructor
  · intro hbound
    by_cases hA : Uniformizes A
    · have hmin : positiveTau A hA ≤ k := by
        simpa [tau, hA] using hbound
      exact ⟨lt_of_lt_of_le (positiveTau_spec A hA).1 hmin,
        uniform_power_mono A hmin (positiveTau_spec A hA).2⟩
    · simp [tau, hA] at hbound
  · rintro ⟨hk,huniform⟩
    have hA : Uniformizes A := ⟨k,hk,huniform⟩
    simpa [tau, hA] using positiveTau_le A hA hk huniform

/-- NaturalUniform matrices have least positive exponent one. This includes zero
matrices and every matrix over a trivial group. -/
theorem tau_eq_one_iff_uniform (A : GroupMat H n n) :
    tau A = 1 ↔ UniformMatrix A := by
  constructor
  · intro h
    have hu := ((tau_le_iff_uniform_power A 1).mp h.le).2
    simpa only [pow_one] using hu
  · intro hu
    apply le_antisymm
    · exact (tau_le_iff_uniform_power A 1).mpr ⟨by decide, by simpa only [pow_one] using hu⟩
    · exact one_le_tau A

/-- Every original admissible k yields equality in the natural group-matrix
ring. Neither positivity nor equality of powers is an additional premise. -/
theorem equal_power_of_tau_le (A B : GroupMat H n n)
    (haug : matrixAugmentation A = matrixAugmentation B)
    {k : ℕ} (hk : max (tau A) (tau B) ≤ (k : WithTop ℕ)) :
    0 < k ∧ A^k = B^k := by
  have hA := (tau_le_iff_uniform_power A k).mp ((le_max_left _ _).trans hk)
  have hB := (tau_le_iff_uniform_power B k).mp ((le_max_right _ _).trans hk)
  exact ⟨hA.1,equal_power_of_uniform A B haug hA.2 hB.2⟩

end NaturalGroupMatrixUniformizationContent

section RationalGroupAlgebraSplittingContent

variable {H : Type u} [Group H] [Fintype H]

abbrev rationalAugmentation : MonoidAlgebra ℚ H →ₐ[ℚ] ℚ :=
  MonoidAlgebra.lift ℚ ℚ H (1 : H →* ℚ)

def RationalUniform (x : MonoidAlgebra ℚ H) : Prop := ∀ g : H, x.coeff g = x.coeff 1

theorem rationalAugmentation_eq_sum (x : MonoidAlgebra ℚ H) : rationalAugmentation x = ∑ g : H, x.coeff g := by
  classical
  rw [rationalAugmentation, MonoidAlgebra.lift_apply']
  simp only [MonoidHom.one_apply, Algebra.algebraMap_self, RingHom.id_apply, mul_one]
  exact Finsupp.sum_fintype _ _ (fun _ => rfl)

@[simp] theorem augmentation_single (g : H) (c : ℚ) : rationalAugmentation (MonoidAlgebra.single g c) = c := by
  simp [rationalAugmentation, MonoidAlgebra.lift_single]

private theorem uniform_mul_left (x y : MonoidAlgebra ℚ H) (hy : RationalUniform y) :
    RationalUniform (x*y) := by
  change ∀ g, y.coeff g = y.coeff 1 at hy
  intro g
  rw [MonoidAlgebra.coeff_mul_apply_left, MonoidAlgebra.coeff_mul_apply_left]
  simp_rw [hy]

private theorem rational_uniform_mul_right (x y : MonoidAlgebra ℚ H) (hx : RationalUniform x) :
    RationalUniform (x*y) := by
  change ∀ g, x.coeff g = x.coeff 1 at hx
  intro g
  rw [MonoidAlgebra.coeff_mul_apply_right, MonoidAlgebra.coeff_mul_apply_right]
  simp_rw [hx]

private theorem uniform_smul (c : ℚ) (x : MonoidAlgebra ℚ H) (hx : RationalUniform x) :
    RationalUniform (c • x) := by
  intro g
  simp only [MonoidAlgebra.coeff_smul_apply, hx g]

/-- Exact rationalAugmentation action on a uniform left factor, by public convolution. -/
private theorem uniform_mul_eq_aug_smul (x y : MonoidAlgebra ℚ H) (hx : RationalUniform x) :
    x*y = rationalAugmentation y • x := by
  classical
  change ∀ g, x.coeff g = x.coeff 1 at hx
  ext g
  rw [MonoidAlgebra.coeff_mul_apply_right]
  rw [Finsupp.sum_fintype _ _ (fun _ => mul_zero _)]
  simp_rw [hx]
  rw [← Finset.mul_sum, rationalAugmentation_eq_sum]
  simp only [MonoidAlgebra.coeff_smul_apply, smul_eq_mul, hx g]
  exact mul_comm _ _

/-- Actual Q[H]-ideal whose elements have constant coefficients. -/
def uniformIdeal (H : Type*) [Group H] [Fintype H] : Ideal (MonoidAlgebra ℚ H) where
  carrier := {x | RationalUniform x}
  zero_mem' := by intro g; rfl
  add_mem' := by
    intro x y hx hy g
    change x.coeff g + y.coeff g = x.coeff 1 + y.coeff 1
    rw [hx g, hy g]
  smul_mem' := by
    intro x y hy
    exact uniform_mul_left x y hy

instance uniformIdeal_twoSided : (uniformIdeal H).IsTwoSided where
  mul_mem_of_left y hx := rational_uniform_mul_right _ y hx

/-- Original normalized sum e_H: each actual coefficient equals 1/|H|. -/
def average (H : Type*) [Group H] [Fintype H] : MonoidAlgebra ℚ H :=
  ∑ g : H, MonoidAlgebra.single g (Fintype.card H : ℚ)⁻¹

@[simp] theorem average_coeff (g : H) :
    (average H).coeff g = (Fintype.card H : ℚ)⁻¹ := by
  classical
  simp [average, MonoidAlgebra.coeff_sum, Finsupp.sum_apply]

private theorem average_uniform : RationalUniform (average H) := by
  intro g
  rw [average_coeff, average_coeff]

@[simp] theorem augmentation_average : rationalAugmentation (average H) = 1 := by
  have hcard : (Fintype.card H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [rationalAugmentation_eq_sum]
  simp only [average_coeff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ hcard

private theorem uniform_augmentation_zero (x : MonoidAlgebra ℚ H)
    (hx : RationalUniform x) (haug : rationalAugmentation x = 0) : x = 0 := by
  have hcard : (Fintype.card H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : (Fintype.card H : ℚ) * x.coeff 1 = 0 := by
    rw [rationalAugmentation_eq_sum] at haug
    have hx' (g : H) : x.coeff g = x.coeff 1 := hx g
    simpa only [hx', Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using haug
  have h1 : x.coeff 1 = 0 := (mul_eq_zero.mp hs).resolve_left hcard
  ext g
  exact (hx g).trans h1

abbrev Reduced (H : Type*) [Group H] [Fintype H] :=
  MonoidAlgebra ℚ H ⧸ uniformIdeal H

/-- The first coordinate is literally rationalAugmentation; the second is the actual
quotient removing the uniform ideal. -/
def splitHom (H : Type*) [Group H] [Fintype H] :
    MonoidAlgebra ℚ H →ₐ[ℚ] ℚ × Reduced H :=
  rationalAugmentation.prod (Ideal.Quotient.mkₐ ℚ (uniformIdeal H))

private theorem splitHom_injective : Function.Injective (splitHom H) := by
  intro x y hxy
  have haug : rationalAugmentation x = rationalAugmentation y := congrArg Prod.fst hxy
  have hquot : Ideal.Quotient.mk (uniformIdeal H) x =
      Ideal.Quotient.mk (uniformIdeal H) y := congrArg Prod.snd hxy
  have hu : RationalUniform (x-y) := (Ideal.Quotient.eq.mp hquot)
  apply sub_eq_zero.mp
  exact uniform_augmentation_zero (x-y) hu (by rw [map_sub, haug, sub_self])

private theorem splitHom_surjective : Function.Surjective (splitHom H) := by
  rintro ⟨a,z⟩
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨x + (a-rationalAugmentation x) • average H, ?_⟩
  apply Prod.ext
  · change rationalAugmentation (x + (a-rationalAugmentation x) • average H) = a
    rw [map_add, map_smul, augmentation_average, smul_eq_mul, mul_one]
    ring
  · change Ideal.Quotient.mk (uniformIdeal H) (x + (a-rationalAugmentation x) • average H) = _
    rw [map_add]
    have hz : Ideal.Quotient.mk (uniformIdeal H) ((a-rationalAugmentation x) • average H) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (uniform_smul _ _ average_uniform)
    rw [hz, add_zero]

/-- Actual rationalAugmentation-first splitting, constructed without choosing a
trivial factor from an arbitrary list of Wedderburn factors. -/
def augmentationSplit (H : Type*) [Group H] [Fintype H] :
    MonoidAlgebra ℚ H ≃ₐ[ℚ] ℚ × Reduced H :=
  AlgEquiv.ofBijective (splitHom H) ⟨splitHom_injective,splitHom_surjective⟩

@[simp] theorem augmentationSplit_first (x : MonoidAlgebra ℚ H) :
    (augmentationSplit H x).1 = rationalAugmentation x := rfl

/-- Nontrivial H leaves a nontrivial quotient, so its Wedderburn index set cannot
be empty. This branch is not used to invent b_H for a trivial group. -/
instance reduced_nontrivial [Nontrivial H] : Nontrivial (Reduced H) := by
  apply nontrivial_of_ne (1 : Reduced H) 0
  intro h10
  have hu : RationalUniform (1 : MonoidAlgebra ℚ H) := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (show Ideal.Quotient.mk (uniformIdeal H) (1 : MonoidAlgebra ℚ H) = 0 by
        simpa only [map_one] using h10)
  obtain ⟨g,hg⟩ := exists_ne (1 : H)
  have hbad : (0 : ℚ) = 1 := by
    simpa [MonoidAlgebra.one_def, hg, Ne.symm hg] using hu g
  exact zero_ne_one hbad

/-- A rational uniform element is its rationalAugmentation times the normalized
uniform idempotent. The formula includes zero. -/
theorem uniform_eq_augmentation_smul_average (x : MonoidAlgebra ℚ H) (hx : RationalUniform x) :
    x = rationalAugmentation x • average H := by
  apply (augmentationSplit H).injective
  apply Prod.ext
  · change rationalAugmentation x = rationalAugmentation (rationalAugmentation x • average H)
    rw [map_smul, augmentation_average, smul_eq_mul, mul_one]
  · change Ideal.Quotient.mk (uniformIdeal H) x =
      Ideal.Quotient.mk (uniformIdeal H) (rationalAugmentation x • average H)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx,
      Ideal.Quotient.eq_zero_iff_mem.mpr (uniform_smul _ _ average_uniform)]

/-- A faithful product decomposition whose first factor is rationalAugmentation has
precisely the uniform group-algebra elements in the kernel of its tail. -/
theorem uniform_iff_tail_zero {S : Type*} [Ring S] [Algebra ℚ S]
    (phi : MonoidAlgebra ℚ H ≃ₐ[ℚ] ℚ × S)
    (hfirst : ∀ x, (phi x).1 = rationalAugmentation x)
    (x : MonoidAlgebra ℚ H) : RationalUniform x ↔ (phi x).2 = 0 := by
  have hfst (z : MonoidAlgebra ℚ H) : (phi z).1 = rationalAugmentation z := hfirst z
  constructor
  · intro hx
    let p : MonoidAlgebra ℚ H := phi.symm (1,0)
    have hp : rationalAugmentation p = 1 := by
      rw [← hfst]
      simp [p]
    have hxp : x*p = x := by
      rw [uniform_mul_eq_aug_smul x p hx, hp, one_smul]
    have htail := congrArg (fun z : MonoidAlgebra ℚ H => (phi z).2) hxp
    simpa [map_mul, p] using htail.symm
  · intro hx
    have htranslate (g : H) : MonoidAlgebra.single g 1 * x = x := by
      apply phi.injective
      apply Prod.ext
      · change (phi (MonoidAlgebra.single g 1 * x)).1 = (phi x).1
        rw [hfst, hfst, map_mul, augmentation_single, one_mul]
      · rw [map_mul]
        change (phi (MonoidAlgebra.single g 1)).2 * (phi x).2 = (phi x).2
        rw [hx, mul_zero]
    intro t
    have hcoeff := congrArg (fun z : MonoidAlgebra ℚ H => z.coeff 1) (htranslate (t⁻¹))
    simpa only [MonoidAlgebra.coeff_single_mul_apply, one_mul, inv_inv, mul_one] using hcoeff

instance reduced_finite : Module.Finite ℚ (Reduced H) := by
  letI : Module.Finite ℚ (MonoidAlgebra ℚ H) :=
    Module.Finite.of_basis (MonoidAlgebra.basis H ℚ)
  exact Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ ℚ (uniformIdeal H)).toLinearMap
    (Ideal.Quotient.mkₐ_surjective ℚ (uniformIdeal H))

instance reduced_semisimple : IsSemisimpleRing (Reduced H) := by
  letI : NeZero (Nat.card H : ℚ) := ⟨by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero⟩
  letI : IsSemisimpleRing (MonoidAlgebra ℚ H) := inferInstance
  exact RingHom.isSemisimpleRing_of_surjective
    (Ideal.Quotient.mk (uniformIdeal H)) Ideal.Quotient.mk_surjective

/-- An rationalAugmentation-first rational decomposition with the original orders
of its nontrivial simple matrix factors. -/
structure RationalDecomposition (H : Type u) [Group H] [Fintype H] where
  count : ℕ
  count_pos : 0 < count
  DivisionAlgebra : Fin count → Type u
  [divisionRing : ∀ l, DivisionRing (DivisionAlgebra l)]
  [algebra : ∀ l, Algebra ℚ (DivisionAlgebra l)]
  [finite : ∀ l, Module.Finite ℚ (DivisionAlgebra l)]
  order : Fin count → ℕ
  order_pos : ∀ l, 0 < order l
  equiv : MonoidAlgebra ℚ H ≃ₐ[ℚ]
    ℚ × (∀ l, Matrix (Fin (order l)) (Fin (order l)) (DivisionAlgebra l))
  augmentation_first : ∀ x, (equiv x).1 = rationalAugmentation x

attribute [instance] RationalDecomposition.divisionRing RationalDecomposition.algebra
  RationalDecomposition.finite

/-- Maschke and the finite Wedderburn theorem applied to the actual quotient
produce all nontrivial blocks, with rationalAugmentation first by construction. -/
theorem nonempty_decomposition [Nontrivial H] : Nonempty (RationalDecomposition H) := by
  obtain ⟨m,D,r,instD,instA,instFinite,hr,⟨psi⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite ℚ (Reduced H)
  letI := instD
  letI := instA
  letI := instFinite
  have hm : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    have h01 : psi (0 : Reduced H) = psi 1 := by
      funext i
      exact Fin.elim0 i
    exact zero_ne_one (psi.injective h01)
  let phi := (augmentationSplit H).trans (AlgEquiv.prodCongr (AlgEquiv.refl : ℚ ≃ₐ[ℚ] ℚ) psi)
  exact ⟨{
    count := m
    count_pos := hm
    DivisionAlgebra := D
    divisionRing := instD
    algebra := instA
    finite := instFinite
    order := r
    order_pos := fun l => by
      letI := hr l
      exact Nat.pos_of_ne_zero (NeZero.ne (r l))
    equiv := phi
    augmentation_first := fun x => augmentationSplit_first x }⟩

end RationalGroupAlgebraSplittingContent

section RationalGroupMatrixCutoffContent

section DivisionRingBound

variable {D I : Type*} [DivisionRing D] [Fintype I] [DecidableEq I]

/-- Right multiplication reverses products, but preserves powers of one matrix. -/
private theorem right_power (M : Matrix I I D) (k : ℕ) :
    (M^k).toLinearMapRight' = (M.toLinearMapRight')^k := by
  induction k with
  | zero => simp; rfl
  | succ k ih =>
      rw [pow_succ, Matrix.toLinearMapRight'_mul, ih]
      change M.toLinearMapRight' * (M.toLinearMapRight')^k = (M.toLinearMapRight')^(k+1)
      exact (pow_succ' M.toLinearMapRight' k).symm

/-- A nilpotent d by d matrix over an arbitrary division ring vanishes by d. -/
private theorem matrix_power_zero_at_card (M : Matrix I I D)
    {N : ℕ} (hN : M^N = 0) : M^(Fintype.card I) = 0 := by
  let T : Module.End D (I → D) := M.toLinearMapRight'
  have hT : T^N = 0 := by
    change (M.toLinearMapRight')^N = 0
    rw [← right_power, hN, map_zero]
  have hker := Module.End.ker_pow_le_ker_pow_finrank T N
  have hdim : T^(Module.finrank D (I → D)) = 0 := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ LinearMap.ker (T^N) := by simp only [hT, LinearMap.ker_zero, Submodule.mem_top]
    exact hker hv
  apply Matrix.toLinearMapRight'.injective
  rw [right_power, map_zero]
  simpa only [Module.finrank_pi] using hdim

/-- Used to pass from the sharp component order n*r to a common k. -/
private theorem matrix_power_zero_mono (M : Matrix I I D)
    {a k : ℕ} (hak : a ≤ k) (ha : M^a = 0) : M^k = 0 := by
  calc
    M^k = M^(a+(k-a)) := by rw [Nat.add_sub_of_le hak]
    _ = M^a * M^(k-a) := pow_add M a (k-a)
    _ = 0 := by rw [ha, zero_mul]

end DivisionRingBound

variable {H : Type*} [Group H] [Fintype H] {n : ℕ}

def naturalToRational : MonoidAlgebra ℕ H →+* MonoidAlgebra ℚ H :=
  MonoidAlgebra.mapRingHom H (Nat.castRingHom ℚ)

def rationalMatrix : GroupMat H n n →+* Matrix (Fin n) (Fin n) (MonoidAlgebra ℚ H) :=
  (naturalToRational (H := H)).mapMatrix

/-- The largest ORIGINAL nontrivial rational matrix order. -/
def bH (W : RationalDecomposition H) : ℕ := Finset.univ.sup W.order

private theorem block_order_le (W : RationalDecomposition H) (l : Fin W.count) :
    W.order l ≤ bH W := Finset.le_sup (f := W.order) (Finset.mem_univ l)

private theorem cutoff_positive (W : RationalDecomposition H) (hn : 0 < n) :
    0 < n*bH W := by
  let l : Fin W.count := ⟨0,W.count_pos⟩
  exact Nat.mul_pos hn (lt_of_lt_of_le (W.order_pos l) (block_order_le W l))

private def component (W : RationalDecomposition H) (l : Fin W.count) :
    MonoidAlgebra ℚ H →+* Matrix (Fin (W.order l)) (Fin (W.order l)) (W.DivisionAlgebra l) where
  toFun x := (W.equiv x).2 l
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp
  map_mul' x y := by simp

/-- The faithful component map, flattened over the SAME division algebra. -/
def block (W : RationalDecomposition H) (l : Fin W.count) :
    GroupMat H n n →+* Matrix (Fin n × Fin (W.order l)) (Fin n × Fin (W.order l))
      (W.DivisionAlgebra l) :=
  (Matrix.compRingEquiv (Fin n) (Fin (W.order l)) (W.DivisionAlgebra l)).toRingHom.comp
    (((component W l).comp naturalToRational).mapMatrix)

private theorem natural_cast_uniform_iff (x : MonoidAlgebra ℕ H) :
    RationalUniform (naturalToRational x) ↔ NaturalUniform x := by
  constructor
  · intro hx g
    have hg := hx g
    simp only [naturalToRational, MonoidAlgebra.coeff_mapRingHom] at hg
    change (x.coeff g : ℚ) = (x.coeff 1 : ℚ) at hg
    exact Nat.cast_injective hg
  · intro hx g
    simp only [naturalToRational, MonoidAlgebra.coeff_mapRingHom]
    change (x.coeff g : ℚ) = (x.coeff 1 : ℚ)
    exact congrArg (fun a : ℕ => (a : ℚ)) (hx g)

/-- This is proved for every natural matrix from the actual rational equivalence;
it is not an additional hypothesis on powers or on the desired cutoff. -/
theorem uniform_iff_blocks_zero (W : RationalDecomposition H) (C : GroupMat H n n) :
    UniformMatrix C ↔ ∀ l, block W l C = 0 := by
  constructor
  · intro hC l
    ext ⟨i,a⟩ ⟨j,b⟩
    have hu := (natural_cast_uniform_iff (C i j)).mpr (hC i j)
    have hz := (uniform_iff_tail_zero
      W.equiv W.augmentation_first (naturalToRational (C i j))).mp hu
    change (W.equiv (naturalToRational (C i j))).2 l a b = 0
    exact congrArg (fun f : ∀ l, Matrix (Fin (W.order l)) (Fin (W.order l))
      (W.DivisionAlgebra l) => f l a b) hz
  · intro hC i j
    have hz : (W.equiv (naturalToRational (C i j))).2 = 0 := by
      funext l
      ext a b
      exact congrArg (fun M : Matrix (Fin n × Fin (W.order l)) (Fin n × Fin (W.order l))
        (W.DivisionAlgebra l) => M (i,a) (j,b)) (hC l)
    exact (natural_cast_uniform_iff (C i j)).mp
      ((uniform_iff_tail_zero
        W.equiv W.augmentation_first (naturalToRational (C i j))).mpr hz)

private theorem uniform_at_cutoff (W : RationalDecomposition H)
    (A : GroupMat H n n) (hA : Uniformizes A) : UniformMatrix (A^(n*bH W)) := by
  classical
  obtain ⟨N,hNpos,hN⟩ := hA
  apply (uniform_iff_blocks_zero W (A^(n*bH W))).mpr
  intro l
  have hnil : (block W l A)^N = 0 := by
    simpa only [map_pow] using (uniform_iff_blocks_zero W (A^N)).mp hN l
  have hsharp : (block W l A)^(n*W.order l) = 0 := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      matrix_power_zero_at_card (block W l A) hnil
  simpa only [map_pow] using
    matrix_power_zero_mono (block W l A) (Nat.mul_le_mul_left n (block_order_le W l)) hsharp

/-- Least POSITIVE uniformization time is bounded by n*b_H. -/
theorem tau_le_cutoff (W : RationalDecomposition H) (hn : 0 < n)
    (A : GroupMat H n n) (hA : Uniformizes A) : tau A ≤ (n*bH W : WithTop ℕ) :=
  (tau_le_iff_uniform_power A (n*bH W)).mpr
    ⟨cutoff_positive W hn,uniform_at_cutoff W A hA⟩

private theorem augmentation_cast (x : MonoidAlgebra ℕ H) :
    rationalAugmentation (naturalToRational x) =
      (naturalAugmentation x : ℚ) := by
  simp [rationalAugmentation_eq_sum, naturalAugmentation_eq_sum,
    naturalToRational, MonoidAlgebra.coeff_mapRingHom]

/-- The normalized rational expression is derived from natural uniformity,
without dividing any natural coefficient. -/
theorem uniform_rational_expression (C : GroupMat H n n) (hC : UniformMatrix C) :
    rationalMatrix C = fun i j => (matrixAugmentation C i j : ℚ) •
      average H := by
  apply Matrix.ext
  intro i j
  have hx := uniform_eq_augmentation_smul_average
    (naturalToRational (C i j)) ((natural_cast_uniform_iff (C i j)).mpr (hC i j))
  change naturalToRational (C i j) = (naturalAugmentation (C i j) : ℚ) •
    average H
  simpa only [augmentation_cast] using hx

end RationalGroupMatrixCutoffContent

section FreeExpansionDimensionGroupContent

variable {H : Type*} [Group H] [Fintype H] {n : ℕ}

abbrev VertexModule (H : Type*) [Group H] (n : ℕ) := Fin n → MonoidAlgebra ℤ H

def integerMatrix : GroupMat H n n →+* Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ H) :=
  (MonoidAlgebra.mapRingHom H (Nat.castRingHom ℤ)).mapMatrix

/-- Row adjacency on the actual free abelian group of vertices (i,h). -/
def transition (A : GroupMat H n n) : Module.End ℤ (VertexModule H n) :=
  (integerMatrix A).toLinearMapRight'.restrictScalars ℤ

/-- Original left action on the group coordinate, preserving the base vertex. -/
def leftTranslation (g : H) : Module.End ℤ (VertexModule H n) where
  toFun v i := MonoidAlgebra.single g 1 * v i
  map_add' v w := by funext i; exact mul_add _ _ _
  map_smul' c v := by
    funext i
    change MonoidAlgebra.single g 1 * (c • v i) = c • (MonoidAlgebra.single g 1 * v i)
    exact mul_smul_comm _ _ _

private theorem action_commutes (A : GroupMat H n n) (g : H) :
    Commute (leftTranslation (n := n) g) (transition A) := by
  change leftTranslation g * transition A = transition A * leftTranslation g
  apply LinearMap.ext
  intro v
  exact ((integerMatrix A).toLinearMapRight'.map_smul (MonoidAlgebra.single g 1) v).symm

/-- The stationary group of the actual integer free-expansion adjacency. -/
abbrev DimensionGroup (A : GroupMat H n n) := StationaryModule (transition A)

/-- The original left H-action induced on the stationary group. -/
def groupAction (A : GroupMat H n n) (g : H) : Module.End ℤ (DimensionGroup A) :=
  induced (transition A) (leftTranslation g) (action_commutes A g)

/-- Inertness is identity of the actual induced action, not a power condition. -/
def Inert (A : GroupMat H n n) : Prop :=
  ∀ g : H, groupAction A g = LinearMap.id

def vertexBasis : Basis (Σ _ : Fin n, H) ℤ (VertexModule H n) :=
  Pi.basis fun _ : Fin n => MonoidAlgebra.basis H ℤ

def vertex (i : Fin n) (h : H) : VertexModule H n :=
  Pi.single i (MonoidAlgebra.single h 1)

private theorem vertexBasis_apply (i : Fin n) (h : H) :
    vertexBasis (H := H) (n := n) ⟨i,h⟩ = vertex i h := by
  simp only [vertexBasis, Pi.basis_apply, MonoidAlgebra.basis_apply, vertex]

private theorem translate_vertex (g h : H) (i : Fin n) :
    leftTranslation g (vertex i h) = vertex i (g*h) := by
  classical
  ext j t
  by_cases hij : i = j
  · subst j
    simp [leftTranslation, vertex, MonoidAlgebra.single_mul_single]
  · simp [leftTranslation, vertex, Pi.single_eq_of_ne (Ne.symm hij)]

private theorem transition_power (A : GroupMat H n n) (k : ℕ) (v : VertexModule H n) :
    ((transition A)^k) v = v ᵥ* integerMatrix (A^k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change (v ᵥ* integerMatrix (A^k)) ᵥ* integerMatrix A =
        v ᵥ* integerMatrix (A^(k+1))
      rw [Matrix.vecMul_vecMul, ← map_mul, ← pow_succ]

/-- Exact adjacency-coordinate identification: from (i,h), a label s reaches
(j,h*s). The inverse and multiplication order are fixed even when H is nonabelian. -/
theorem actual_expansion_adjacency (A : GroupMat H n n) (i j : Fin n) (h t : H) :
    ((transition A (vertex i h)) j).coeff t = ((A i j).coeff (h⁻¹*t) : ℤ) := by
  classical
  change ((Pi.single i (MonoidAlgebra.single h 1) ᵥ* integerMatrix A) j).coeff t = _
  rw [Matrix.single_vecMul]
  simp [integerMatrix, Matrix.row, MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mapRingHom]

private theorem vertex_mul_coeff (C : GroupMat H n n) (i j : Fin n) (h t : H) :
    ((vertex i h ᵥ* integerMatrix C) j).coeff t = ((C i j).coeff (h⁻¹*t) : ℤ) :=
  actual_expansion_adjacency C i j h t

private theorem stage_implies_uniform (A : GroupMat H n n) {N : ℕ}
    (hN : ∀ g : H, (transition A)^N * leftTranslation g = (transition A)^N) :
    UniformMatrix (A^N) := by
  intro i j t
  have hv := congrArg
    (fun F : Module.End ℤ (VertexModule H n) => ((F (vertex i 1)) j).coeff 1)
    (hN (t⁻¹))
  simp only [Module.End.mul_apply, translate_vertex, mul_one,
    transition_power, vertex_mul_coeff, inv_inv, inv_one, one_mul] at hv
  exact_mod_cast hv

private theorem uniform_implies_stage (A : GroupMat H n n) {N : ℕ}
    (hN : UniformMatrix (A^N)) (g : H) :
    (transition A)^N * leftTranslation g = (transition A)^N := by
  apply (vertexBasis (H := H) (n := n)).ext
  rintro ⟨i,h⟩
  rw [vertexBasis_apply]
  ext j t
  simp only [Module.End.mul_apply, translate_vertex, transition_power, vertex_mul_coeff]
  rw [hN i j ((g*h)⁻¹*t), hN i j (h⁻¹*t)]

/-- The original H-action is inert exactly when a positive power has constant
group coefficients. A finite basis and finite H provide one common stage. -/
theorem inert_iff_uniformizes (A : GroupMat H n n) : Inert A ↔ Uniformizes A := by
  have hfinite := finite_family_inert_iff_eventual
    (vertexBasis (H := H) (n := n)) (transition A) (leftTranslation (n := n))
    (action_commutes A)
  constructor
  · intro hinert
    obtain ⟨N,hN⟩ := hfinite.mp hinert
    refine ⟨N+1, Nat.succ_pos N, ?_⟩
    exact uniform_power_mono A (Nat.le_succ N) (stage_implies_uniform A hN)
  · rintro ⟨N,hNpos,hN⟩
    exact hfinite.mpr ⟨N,uniform_implies_stage A hN⟩

end FreeExpansionDimensionGroupContent

section InertGroupBlockConjugacyContent

variable {H : Type*} [Group H] [Fintype H] {n : ℕ}
variable [TopologicalSpace H] [DiscreteTopology H]

/-- The exact original construction at one exponent. Positivity and equality
of natural powers are outputs. Both rational expressions use the same actual
augmentation matrix. The final four clauses name the unchanged constructor. -/
def AtExponent (A B : GroupMat H n n) (k : ℕ) : Prop :=
  ∃ hk : 0 < k, ∃ hpower : A^k = B^k,
    (rationalMatrix (A^k) = fun i j => (((matrixAugmentation A)^k) i j : ℚ) •
      average H) ∧
    (rationalMatrix (B^k) = fun i j => (((matrixAugmentation A)^k) i j : ℚ) •
      average H) ∧
    (∀ x, original181History A B hk
      (fiber_counts_of_equal_power A B hk hpower) x =
      equalPowerHomeomorph A B hk hpower x) ∧
    (∀ a x, equalPowerHomeomorph A B hk hpower (groupHistory A a x) =
      groupHistory B a (equalPowerHomeomorph A B hk hpower x)) ∧
    (∀ x, equalPowerHomeomorph A B hk hpower
      ((shift (expandedGraph A))^[k] x) =
      (shift (expandedGraph B))^[k]
        (equalPowerHomeomorph A B hk hpower x)) ∧
    ((∀ x, equalPowerHomeomorph A B hk hpower (shift (expandedGraph A) x) =
      shift (expandedGraph B) (equalPowerHomeomorph A B hk hpower x)) → A = B)

private theorem atExponent_of_tau_le (A B : GroupMat H n n)
    (hA : Essential (baseGraph A)) (hB : Essential (baseGraph B))
    (haug : matrixAugmentation A = matrixAugmentation B) {k : ℕ}
    (hkTau : max (tau A) (tau B) ≤ (k : WithTop ℕ)) : AtExponent A B k := by
  obtain ⟨hk,hpower⟩ := equal_power_of_tau_le A B haug hkTau
  have huniform := ((tau_le_iff_uniform_power A k).mp
    ((le_max_left _ _).trans hkTau)).2
  have hrat : rationalMatrix (A^k) = fun i j =>
      (((matrixAugmentation A)^k) i j : ℚ) •
        average H := by
    simpa only [map_pow] using uniform_rational_expression (A^k) huniform
  refine ⟨hk,hpower,hrat,?_,?_⟩
  · rw [← hpower]
    exact hrat
  · exact equalPower_attachment A B hA hB hk hpower

/-- The full original threshold theorem. Inertness concerns the actual
stationary dimension group. Every rational decomposition retains its own
nontrivial matrix orders; no replacement degree or cutoff is assumed.
The same fixed alignment is constructed separately for each admissible k. -/
private theorem original18_1_core (A B : GroupMat H n n)
    (hA : Essential (baseGraph A)) (hB : Essential (baseGraph B))
    (hInertA : Inert A) (hInertB : Inert B)
    (haug : matrixAugmentation A = matrixAugmentation B) :
    (Subsingleton H → tau A = 1 ∧ tau B = 1 ∧ A = B) ∧
    (∀ W : RationalDecomposition H, 0 < n →
      max (tau A) (tau B) ≤ (n*bH W : WithTop ℕ)) ∧
    (∀ k : ℕ, max (tau A) (tau B) ≤ (k : WithTop ℕ) → AtExponent A B k) := by
  have huniformA := (inert_iff_uniformizes A).mp hInertA
  have huniformB := (inert_iff_uniformizes B).mp hInertB
  refine ⟨?_,?_,?_⟩
  · intro hH
    letI : Subsingleton H := hH
    have huA : UniformMatrix A := by
      intro i j g
      rw [Subsingleton.elim g 1]
    have huB : UniformMatrix B := by
      intro i j g
      rw [Subsingleton.elim g 1]
    have htA := (tau_eq_one_iff_uniform A).mpr huA
    have htB := (tau_eq_one_iff_uniform B).mpr huB
    refine ⟨htA,htB,?_⟩
    have hp := (equal_power_of_tau_le A B haug (k := 1) (by simp [htA,htB])).2
    simpa only [pow_one] using hp
  · intro W hn
    exact max_le (tau_le_cutoff W hn A huniformA) (tau_le_cutoff W hn B huniformB)
  · intro k hkTau
    exact atExponent_of_tau_le A B hA hB haug hkTau

/-- The complete threshold conclusion, together with an actual rational
 decomposition that supplies the same cutoff and every later constructed map. -/
theorem original18_1 (A B : GroupMat H n n)
    (hA : Essential (baseGraph A)) (hB : Essential (baseGraph B))
    (hInertA : Inert A) (hInertB : Inert B)
    (haug : matrixAugmentation A = matrixAugmentation B) :
    ((Subsingleton H → tau A = 1 ∧ tau B = 1 ∧ A = B) ∧
      (∀ W : RationalDecomposition H, 0 < n →
        max (tau A) (tau B) ≤ (n*bH W : WithTop ℕ)) ∧
      (∀ k : ℕ, max (tau A) (tau B) ≤ (k : WithTop ℕ) → AtExponent A B k)) ∧
    (Nontrivial H → 0 < n → ∃ W : RationalDecomposition H,
      max (tau A) (tau B) ≤ (n*bH W : WithTop ℕ) ∧
      ∀ k : ℕ, (n*bH W : WithTop ℕ) ≤ (k : WithTop ℕ) → AtExponent A B k) := by
  have hcore := original18_1_core A B hA hB hInertA hInertB haug
  refine ⟨hcore, ?_⟩
  intro hH hn
  letI : Nontrivial H := hH
  obtain ⟨W⟩ := nonempty_decomposition (H := H)
  have hbound := hcore.2.1 W hn
  exact ⟨W, hbound, fun k hk => hcore.2.2 k (hbound.trans hk)⟩

end InertGroupBlockConjugacyContent

end D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
