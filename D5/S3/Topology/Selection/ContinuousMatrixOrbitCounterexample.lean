/- GID: D5/S3/Topology/Selection/ContinuousMatrixOrbitCounterexample
   generality: I
   mirror-B: D5/B/S3/Topology/Selection/ContinuousMatrixOrbitCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equal Gram fields on the inverse-natural compactum admit approximate but no exact continuous unitary alignment. -/

import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-! The literal inverse-natural real subspace in Proposition 10.3.
The matrix topology is the product topology on the finitely many complex entries.
The L2Operator scope uses the actual Euclidean operator norm; Mathlib
transports it with the existing product topology and uniformity preserved. OnePoint is used only through the explicit homeomorphism below. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology OnePoint Matrix.Norms.L2Operator ComplexOrder MatrixOrder
namespace D5.S3.Topology.Selection.ContinuousMatrixOrbitCounterexample

abbrev S := OnePoint ℕ

def radius (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ)⁻¹

def realPoint (s : S) : ℝ := s.elim 0 radius

def literalSet : Set ℝ := insert 0 (Set.range radius)
abbrev X := literalSet

def origin : X := ⟨0, Or.inl rfl⟩
def point (k : ℕ) : X := ⟨radius k, Or.inr ⟨k, rfl⟩⟩

private lemma literalSet_description (t : ℝ) :
    t ∈ literalSet ↔ t = 0 ∨ ∃ k : ℕ, 1 ≤ k ∧ t = 1 / (k : ℝ) := by
  constructor
  · rintro (h | ⟨k, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨k + 1, by omega, by simp [radius, one_div]⟩
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨k - 1, by simp [radius, Nat.sub_add_cancel hk, one_div]⟩

private lemma radius_pos (k : ℕ) : 0 < radius k := by
  dsimp [radius]
  positivity

private lemma radius_injective : Function.Injective radius := by
  intro j k h
  have hc : ((j + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) := inv_injective h
  exact Nat.add_right_cancel (Nat.cast_injective hc)

private lemma radius_tendsto : Tendsto radius atTop (𝓝 0) := by
  exact tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)

private lemma realPoint_continuous : Continuous realPoint := by
  exact (OnePoint.continuous_iff_from_nat _).2 radius_tendsto

def toLiteral (s : S) : X := ⟨realPoint s, by
  induction s using OnePoint.rec with
  | infty => exact Or.inl rfl
  | coe k => exact Or.inr ⟨k, rfl⟩⟩

private lemma toLiteral_bijective : Function.Bijective toLiteral := by
  constructor
  · intro s t h
    have hv := congrArg Subtype.val h
    induction s using OnePoint.rec with
    | infty =>
      induction t using OnePoint.rec with
      | infty => rfl
      | coe k => exact False.elim ((ne_of_gt (radius_pos k)) hv.symm)
    | coe j =>
      induction t using OnePoint.rec with
      | infty => exact False.elim ((ne_of_gt (radius_pos j)) hv)
      | coe k => exact congrArg (fun k : ℕ => (k : S)) (radius_injective hv)
  · rintro ⟨t, h | ⟨k, rfl⟩⟩
    · exact ⟨∞, Subtype.ext h.symm⟩
    · exact ⟨(k : S), rfl⟩

private lemma toLiteral_continuous : Continuous toLiteral :=
  realPoint_continuous.subtype_mk _

noncomputable def literalHomeomorph : S ≃ₜ X :=
  (Equiv.ofBijective toLiteral toLiteral_bijective).toHomeomorphOfContinuousClosed
    toLiteral_continuous toLiteral_continuous.isClosedMap

@[simp] private lemma homeomorph_infty : literalHomeomorph ∞ = origin := rfl
@[simp] private lemma homeomorph_coe (k : ℕ) : literalHomeomorph (k : S) = point k := rfl

instance : Nonempty X := ⟨origin⟩
instance : CompactSpace X := literalHomeomorph.compactSpace
instance : Countable X := ((Set.countable_range radius).insert 0).to_subtype
instance : ZeroDimensionalSpace X := inferInstance

private lemma literal_compact : IsCompact literalSet := by
  exact isCompact_iff_compactSpace.mpr inferInstance

/-- The radius, interpreted in the actual complex scalar field. -/
def a (s : S) : ℂ := (realPoint s : ℂ)
def b (s : S) : ℂ := s.elim 0 (fun k => (-1 : ℂ) ^ (k + 1) * (radius k : ℂ))

private lemma a_continuous : Continuous a :=
  Complex.continuous_ofReal.comp realPoint_continuous

private lemma b_continuous : Continuous b := by
  apply (OnePoint.continuous_iff_from_nat _).2
  apply squeeze_zero_norm (fun k => ?_) (radius_tendsto)
  simp only [b, OnePoint.elim_some, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (radius_pos k)]
  exact le_rfl

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def first (n : ℕ) (s : S) : Mat n := Matrix.diagonal (fun _ => a s)
def second (n : ℕ) (s : S) : Mat n := Matrix.diagonal (fun _ => b s)

def Z1 (n : ℕ) (x : X) : Mat n := first n (literalHomeomorph.symm x)
def Z2 (n : ℕ) (x : X) : Mat n := second n (literalHomeomorph.symm x)

private lemma first_continuous (n : ℕ) : Continuous (first n) := by
  classical
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  by_cases h : i = j
  · simpa [first, Matrix.diagonal_apply, h] using a_continuous
  · simp [first, h, continuous_const]

private lemma second_continuous (n : ℕ) : Continuous (second n) := by
  classical
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  by_cases h : i = j
  · simpa [second, Matrix.diagonal_apply, h] using b_continuous
  · simp [second, h, continuous_const]

private lemma fields_continuous (n : ℕ) : Continuous (Z1 n) ∧ Continuous (Z2 n) :=
  ⟨(first_continuous n).comp literalHomeomorph.symm.continuous,
   (second_continuous n).comp literalHomeomorph.symm.continuous⟩

private lemma fields_origin (n : ℕ) : Z1 n origin = 0 ∧ Z2 n origin = 0 := by
  have ho := literalHomeomorph.symm_apply_apply ∞
  rw [homeomorph_infty] at ho
  simp [Z1, Z2, ho, first, second, a, b, realPoint]

private lemma fields_point (n k : ℕ) :
    Z1 n (point k) = (radius k : ℂ) • (1 : Mat n) ∧
    Z2 n (point k) = ((-1 : ℂ) ^ (k + 1) * (radius k : ℂ)) • (1 : Mat n) := by
  have hp := literalHomeomorph.symm_apply_apply (k : S)
  rw [homeomorph_coe] at hp
  constructor <;> ext i j <;>
    simp [Z1, Z2, hp, first, second, a, b, realPoint, Matrix.diagonal_apply,
      Matrix.one_apply, smul_eq_mul]

private lemma scalar_gram (s : S) : star (a s) * a s = star (b s) * b s := by
  induction s using OnePoint.rec with
  | infty => simp [a, b, realPoint]
  | coe k =>
    have hs : ((-1 : ℂ) ^ (k + 1)) * ((-1 : ℂ) ^ (k + 1)) = 1 := by
      rw [← mul_pow]; norm_num
    simp only [a, b, realPoint, OnePoint.elim_some, star_mul, star_pow,
      star_neg, star_one, Complex.star_def, Complex.conj_ofReal]
    calc
      (radius k : ℂ) * (radius k : ℂ) =
          (((-1 : ℂ) ^ (k + 1)) * ((-1 : ℂ) ^ (k + 1))) *
            ((radius k : ℂ) * (radius k : ℂ)) := by rw [hs, one_mul]
      _ = _ := by ring

private lemma same_gram (n : ℕ) (x : X) :
    (Z1 n x).conjTranspose * Z1 n x = (Z2 n x).conjTranspose * Z2 n x := by
  simp only [Z1, Z2, first, second, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact scalar_gram _

/-- No continuity or algebraic assumption is made on an unknown response.
The obstruction is proved for every continuous matrix-valued multiplier. -/
private theorem no_continuous_multiplier (n : ℕ) (hn : 1 ≤ n) :
    ¬ ∃ U : X → Mat n, Continuous U ∧ ∀ x, Z2 n x = U x * Z1 n x := by
  rintro ⟨U, hU, heq⟩
  let i : Fin n := ⟨0, hn⟩
  let u : S → ℂ := fun s => U (literalHomeomorph s) i i
  have hu : Continuous u :=
    ((continuous_apply i).comp ((continuous_apply i).comp
      (hU.comp literalHomeomorph.continuous)))
  have forced (k : ℕ) : u (k : S) = (-1 : ℂ) ^ (k + 1) := by
    have hm := congrArg (fun M : Mat n => M i i) (heq (point k))
    have hr : (radius k : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (radius_pos k))
    have hp := fields_point n k
    rw [hp.1, hp.2] at hm
    have hv : ((-1 : ℂ) ^ (k + 1)) * (radius k : ℂ) =
        u (k : S) * (radius k : ℂ) := by
      simpa [u, Matrix.mul_smul, Matrix.mul_one, Matrix.one_apply,
        Pi.smul_apply, smul_eq_mul, mul_comm] using hm
    exact (mul_right_cancel₀ hr hv).symm
  have hlim : Tendsto (fun k : ℕ => (-1 : ℂ) ^ (k + 1)) atTop (𝓝 (u ∞)) := by
    simpa only [forced] using (OnePoint.continuous_iff_from_nat u).1 hu
  have heven : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_mono (fun k => (show k ≤ 2 * k by omega)) tendsto_id
  have hodd : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => (show k ≤ 2 * k + 1 by omega)) tendsto_id
  have hminus : Tendsto (fun _ : ℕ => (-1 : ℂ)) atTop (𝓝 (u ∞)) := by
    convert hlim.comp heven using 1
    funext k
    simp [pow_add, pow_mul]
  have hplus : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 (u ∞)) := by
    convert hlim.comp hodd using 1
    funext k
    simp [pow_add, pow_mul]
  have hm : (-1 : ℂ) = u ∞ := tendsto_nhds_unique tendsto_const_nhds hminus
  have hp : (1 : ℂ) = u ∞ := tendsto_nhds_unique tendsto_const_nhds hplus
  have : (-1 : ℂ) = 1 := hm.trans hp.symm
  norm_num at this

/-- The positive-natural indexing is the literal indexing of the theory. -/
def positivePoint (k : ℕ) (hk : 1 ≤ k) : X :=
  ⟨1 / (k : ℝ), (literalSet_description _).2 (Or.inr ⟨k, hk, rfl⟩)⟩

private lemma fields_positive (n k : ℕ) (hk : 1 ≤ k) :
    Z1 n (positivePoint k hk) = (1 / (k : ℂ)) • (1 : Mat n) ∧
    Z2 n (positivePoint k hk) = ((-1 : ℂ) ^ k / (k : ℂ)) • (1 : Mat n) := by
  have hp : positivePoint k hk = point (k - 1) := by
    apply Subtype.ext
    simp [positivePoint, point, radius, Nat.sub_add_cancel hk, one_div]
  rw [hp]
  simpa [radius, Nat.sub_add_cancel hk, one_div, div_eq_mul_inv] using fields_point n (k - 1)

/-- The actual finite head, transported to the literal real subspace. -/
def finiteHead (N : ℕ) : Set X :=
  literalHomeomorph.symm ⁻¹' ((fun k : ℕ => (k : S)) '' Set.Iio N)

private lemma finiteHead_clopen (N : ℕ) : IsClopen (finiteHead N) := by
  have hf : (((fun k : ℕ => (k : S)) '' Set.Iio N) : Set S).Finite :=
    (Set.finite_Iio N).image _
  have hinf : (∞ : S) ∉ ((fun k : ℕ => (k : S)) '' Set.Iio N) := by
    rintro ⟨k, hk, h⟩
    cases h
  have ho : IsOpen (((fun k : ℕ => (k : S)) '' Set.Iio N) : Set S) :=
    (OnePoint.isOpen_iff_of_notMem hinf).2 (isOpen_discrete _)
  exact (show IsClopen (((fun k : ℕ => (k : S)) '' Set.Iio N) : Set S) from
    ⟨hf.isClosed, ho⟩).preimage literalHomeomorph.symm.continuous

/-- Finite head with the constant identity phase on the cofinite clopen tail. -/
def phase (N : ℕ) (s : S) : ℂ :=
  s.elim 1 (fun k => if k + 1 ≤ N then (-1 : ℂ) ^ (k + 1) else 1)

def approximant (n N : ℕ) (x : X) : Mat n :=
  Matrix.diagonal (fun _ => phase N (literalHomeomorph.symm x))

private lemma phase_continuous (N : ℕ) : Continuous (phase N) := by
  apply (OnePoint.continuous_iff_from_nat _).2
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with k hk
  simp [phase, show ¬ k < N by omega]

private lemma approximant_continuous (n N : ℕ) : Continuous (approximant n N) := by
  classical
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  by_cases h : i = j
  · simpa only [approximant, Matrix.diagonal_apply, ite_eq_left h, Function.comp_def] using
      (phase_continuous N).comp literalHomeomorph.symm.continuous
  · simp [approximant, h, continuous_const]

private lemma phase_unitary (N : ℕ) (s : S) :
    star (phase N s) * phase N s = 1 ∧ phase N s * star (phase N s) = 1 := by
  induction s using OnePoint.rec with
  | infty => simp [phase]
  | coe k =>
    by_cases hk : k < N
    · simp [phase, hk, ← mul_pow]
    · simp [phase, hk]

private lemma approximant_unitary (n N : ℕ) (x : X) :
    (approximant n N x).conjTranspose * approximant n N x = 1 ∧
    approximant n N x * (approximant n N x).conjTranspose = 1 := by
  constructor <;> simp only [approximant, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  · congr 1; funext i; exact (phase_unitary N _).1
  · congr 1; funext i; exact (phase_unitary N _).2

private lemma scalar_error (N : ℕ) (s : S) :
    ‖b s - phase N s * a s‖ ≤ 2 / (N + 1 : ℝ) := by
  induction s using OnePoint.rec with
  | infty => simp [b, phase, a, realPoint]; positivity
  | coe k =>
    by_cases hk : k < N
    · simp [b, phase, a, realPoint, hk]; positivity
    · have hr : radius k ≤ 1 / (N + 1 : ℝ) := by
        dsimp [radius]
        rw [one_div]
        apply inv_le_inv₀ (by positivity) (by positivity) |>.2
        exact_mod_cast (show N + 1 ≤ k + 1 by omega)
      calc
        ‖b (k : S) - phase N (k : S) * a (k : S)‖ ≤ 2 * radius k := by
          simpa [b, phase, a, realPoint, Nat.succ_le_iff, hk, norm_mul, norm_pow,
            abs_of_pos (radius_pos k), two_mul] using
            norm_sub_le ((-1 : ℂ) ^ (k + 1) * (radius k : ℂ)) (radius k : ℂ)
        _ ≤ 2 * (1 / (N + 1 : ℝ)) := mul_le_mul_of_nonneg_left hr (by norm_num)
        _ = 2 / (N + 1 : ℝ) := by ring

/-- Uniform pointwise error in the intended complex Euclidean operator norm. -/
private lemma approximant_error (n N : ℕ) (hn : 1 ≤ n) (x : X) :
    ‖Z2 n x - approximant n N x * Z1 n x‖ ≤ 2 / (N + 1 : ℝ) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have heq : Z2 n x - approximant n N x * Z1 n x =
      (b (literalHomeomorph.symm x) - phase N (literalHomeomorph.symm x) *
        a (literalHomeomorph.symm x)) • (1 : Mat n) := by
    ext i j
    simp [Z1, Z2, first, second, approximant, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp_all
  rw [heq, norm_smul, norm_one, mul_one]
  exact scalar_error N _

private lemma first_nonnegative (n : ℕ) (x : X) : 0 ≤ Z1 n x := by
  apply Matrix.PosSemidef.nonneg
  apply Matrix.PosSemidef.diagonal
  intro i
  change 0 ≤ a (literalHomeomorph.symm x)
  generalize literalHomeomorph.symm x = s
  induction s using OnePoint.rec with
  | infty => simp [a, realPoint]
  | coe k => simpa [a, realPoint] using (radius_pos k).le

private lemma positive_modulus (n : ℕ) (x : X) : CFC.abs (Z2 n x) = Z1 n x := by
  unfold CFC.abs
  change CFC.sqrt ((Z2 n x).conjTranspose * Z2 n x) = Z1 n x
  rw [← same_gram n x]
  have hs : (Z1 n x).conjTranspose = Z1 n x :=
    (IsSelfAdjoint.of_nonneg (first_nonnegative n x)).star_eq
  rw [hs]
  exact CFC.sqrt_mul_self _ (first_nonnegative n x)

private lemma no_continuous_polar (n : ℕ) (hn : 1 ≤ n) :
    ¬ ∃ U : X → Mat n, Continuous U ∧ ∀ x, Z2 n x = U x * CFC.abs (Z2 n x) := by
  rintro ⟨U, hU, h⟩
  apply no_continuous_multiplier n hn
  refine ⟨U, hU, fun x => ?_⟩
  simpa only [positive_modulus] using h x

/-- Clause-complete counterexample endpoint, valid already for every n ≥ 1. -/
theorem proposition10_3 (n : ℕ) (hn : 1 ≤ n) :
    IsCompact literalSet ∧ Nonempty X ∧ CompactSpace X ∧ T2Space X ∧ ZeroDimensionalSpace X ∧
    Continuous (Z1 n) ∧ Continuous (Z2 n) ∧
    (Z1 n origin = 0 ∧ Z2 n origin = 0) ∧
    (∀ k : ℕ, Z1 n (point k) = (radius k : ℂ) • (1 : Mat n) ∧
      Z2 n (point k) = ((-1 : ℂ) ^ (k + 1) * (radius k : ℂ)) • (1 : Mat n)) ∧
    (∀ k : ℕ, ∀ hk : 1 ≤ k,
      Z1 n (positivePoint k hk) = (1 / (k : ℂ)) • (1 : Mat n) ∧
      Z2 n (positivePoint k hk) = ((-1 : ℂ) ^ k / (k : ℂ)) • (1 : Mat n)) ∧
    (∀ N, IsClopen (finiteHead N) ∧ Continuous (approximant n N) ∧
      (∀ x, (approximant n N x).conjTranspose * approximant n N x = 1 ∧
        approximant n N x * (approximant n N x).conjTranspose = 1) ∧
      ∀ x, ‖Z2 n x - approximant n N x * Z1 n x‖ ≤ 2 / (N + 1 : ℝ)) ∧
    (∀ x, (Z1 n x).conjTranspose * Z1 n x = (Z2 n x).conjTranspose * Z2 n x) ∧
    (∀ x, 0 ≤ Z1 n x ∧ CFC.abs (Z2 n x) = Z1 n x) ∧
    (¬ ∃ U : X → Mat n, Continuous U ∧ ∀ x, Z2 n x = U x * CFC.abs (Z2 n x)) ∧
    ¬ ∃ U : X → Mat n, Continuous U ∧ ∀ x, Z2 n x = U x * Z1 n x := by
  exact ⟨literal_compact, inferInstance, inferInstance, inferInstance, inferInstance,
    (fields_continuous n).1, (fields_continuous n).2, fields_origin n,
    fields_point n, fields_positive n,
    fun N => ⟨finiteHead_clopen N, approximant_continuous n N, approximant_unitary n N,
      approximant_error n N hn⟩,
    same_gram n, fun x => ⟨first_nonnegative n x, positive_modulus n x⟩,
    no_continuous_polar n hn, no_continuous_multiplier n hn⟩

end D5.S3.Topology.Selection.ContinuousMatrixOrbitCounterexample
