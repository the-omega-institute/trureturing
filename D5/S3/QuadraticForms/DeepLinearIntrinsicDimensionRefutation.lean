/- GID: D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.claim; result=D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.result; claim=D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.claim
   digest: Gaussian affine lines can miss the scalar deep-linear solution fiber. -/

/-
admission_basis: open-problem-resolution (#26399; Refuted)
proof_shape: result = bind-only; escape_witness: none.
Direct frozen dependencies: none (all imports are pinned Mathlib).
Private theorem classifications (all bind-only; direct frozen dependencies: none):
  gaussian_open_support -> hit_zero_lt_one, hit_one_lt_one;
  scalar_fiber -> miss_zero_disjoint, miss_one_disjoint;
  miss_zero_open, miss_zero_nonempty, miss_zero_disjoint -> hit_zero_lt_one;
  miss_one_open, miss_one_nonempty, miss_one_disjoint -> hit_one_lt_one;
  hit_zero_lt_one, hit_one_lt_one -> result.
Each helper has escape_witness: none; no helper supplies the admission basis.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The claim retains the Gaussian generator, the full-dimensional case, the ENat infimum,
and the ordered matrix fiber of arXiv:2610.39674v1, equations (3) and (20).
Existing EuclideanSpace, Sigma, Sum and matrix types are used directly, without aliases.
The scalar instance excludes dimensions zero and one. No general-width bound is claimed.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Random affine intersections of ordered deep-linear polynomial fibers. -/

public noncomputable section
namespace D5.S3.QuadraticForms.DeepLinearIntrinsicDimensionRefutation

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Independent standard Gaussian columns and an independent standard Gaussian offset. -/
def sampleLaw (ι : Type) [Fintype ι] (d : ℕ) :
    Measure ((Fin d → EuclideanSpace ℝ ι) × EuclideanSpace ℝ ι) :=
  (Measure.pi (fun _ : Fin d => stdGaussian (EuclideanSpace ℝ ι))).prod (stdGaussian (EuclideanSpace ℝ ι))

/-- The source's random affine d-plane, using its equivalent Gaussian column generator. -/
def affinePlane {ι : Type} [Fintype ι] (d : ℕ)
    (z : (Fin d → EuclideanSpace ℝ ι) × EuclideanSpace ℝ ι) : Set (EuclideanSpace ℝ ι) :=
  if d = Fintype.card ι then Set.univ
  else {x | x - z.2 ∈ Submodule.span ℝ (Set.range z.1)}

/-- Equation (3); the empty infimum is infinity, and only dimensions 0 through p occur. -/
def intrinsicDimension {ι : Type} [Fintype ι] (Θ : Set (EuclideanSpace ℝ ι)) : ℕ∞ :=
  sInf {n | ∃ d : ℕ, d ≤ Fintype.card ι ∧ n = (d : ℕ∞) ∧
    sampleLaw ι d {z | (affinePlane d z ∩ Θ).Nonempty} = 1}

/-- W_(l+1), with zero only at unused indices l >= L. -/
def weight {L : ℕ} {m : ℕ → ℕ}
    (θ : EuclideanSpace ℝ ((Σ l : Fin L, Fin (m (l.val + 1)) × Fin (m l.val)) ⊕ Fin (m L))) (l : ℕ)
    : Matrix (Fin (m (l + 1))) (Fin (m l)) ℝ :=
  fun i j => if h : l < L then θ (Sum.inl ⟨⟨l, h⟩, (i, j)⟩) else 0

/-- W_l ... W_1, with the identity at l = 0. -/
def weightProduct {L : ℕ} {m : ℕ → ℕ}
    (θ : EuclideanSpace ℝ ((Σ l : Fin L, Fin (m (l.val + 1)) × Fin (m l.val)) ⊕ Fin (m L))) :
    (l : ℕ) → Matrix (Fin (m l)) (Fin (m 0)) ℝ
  | 0 => 1
  | l + 1 => weight θ l * weightProduct θ l

/-- W_1^T ... W_L^T a, using the transpose of the ordered matrix product. -/
def realization {L : ℕ} {m : ℕ → ℕ}
    (θ : EuclideanSpace ℝ ((Σ l : Fin L, Fin (m (l.val + 1)) × Fin (m l.val)) ⊕ Fin (m L))) : Fin (m 0) → ℝ :=
  (weightProduct θ L).transpose.mulVec (fun i => θ (Sum.inr i))

/-- Equation (20), as an explicit polynomial fiber. -/
def solutionSet {L : ℕ} {m : ℕ → ℕ} (u : Fin (m 0) → ℝ) :
    Set (EuclideanSpace ℝ ((Σ l : Fin L, Fin (m (l.val + 1)) × Fin (m l.val)) ⊕ Fin (m L))) :=
  {θ | realization θ = u}

/-- The source's equality for every positive depth, input dimension and hidden widths. -/
def claim : Prop :=
  ∀ (L : ℕ) (m : ℕ → ℕ), 1 ≤ L → (∀ l : ℕ, l ≤ L → 1 ≤ m l) →
    ∀ u : Fin (m 0) → ℝ, u ≠ 0 →
      intrinsicDimension (solutionSet (L := L) u) = (m 0 : ℕ∞)


set_option synthInstance.maxSize 512

private theorem gaussian_open_support (ι : Type) [Fintype ι] :
    (stdGaussian (EuclideanSpace ℝ ι)).IsOpenPosMeasure := by
  let : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure
  rw [← map_pi_eq_stdGaussian]
  exact (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).isOpenPosMeasure_map
    (Equiv.surjective (WithLp.equiv 2 (ι → ℝ)).symm)

private def w : ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1) := Sum.inl ⟨0, (0, 0)⟩
private def a : ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1) := Sum.inr 0

private def missZero :
    Set ((Fin 0 → EuclideanSpace ℝ ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1)) ×
      EuclideanSpace ℝ ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1)) :=
  {z | z.2 w * z.2 a < 1}
private def missOne :
    Set ((Fin 1 → EuclideanSpace ℝ ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1)) ×
      EuclideanSpace ℝ ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1)) :=
  {z | z.1 0 w * z.1 0 a < 0 ∧
    discrim (z.1 0 w * z.1 0 a)
      (z.2 w * z.1 0 a + z.1 0 w * z.2 a) (z.2 w * z.2 a - 1) < 0}

private theorem scalar_fiber (θ : EuclideanSpace ℝ ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1))
    (h : θ ∈ solutionSet (L := 1) (m := fun _ => 1) (fun _ => 1)) :
    θ w * θ a = 1 := by
  have hv := congrFun h 0
  simpa [realization, weightProduct, weight, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply, w, a] using hv

private theorem miss_zero_open : IsOpen missZero := by
  exact isOpen_lt (by fun_prop) continuous_const

private theorem miss_one_open : IsOpen missOne := by
  exact (isOpen_lt
    (by fun_prop : Continuous
      (fun z : (Fin 1 → EuclideanSpace ℝ ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1)) ×
      EuclideanSpace ℝ ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1) => z.1 0 w * z.1 0 a))
    continuous_const).inter
    (isOpen_lt (by unfold discrim; fun_prop : Continuous
      (fun z : (Fin 1 → EuclideanSpace ℝ ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1)) ×
      EuclideanSpace ℝ ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1) => discrim (z.1 0 w * z.1 0 a)
        (z.2 w * z.1 0 a + z.1 0 w * z.2 a) (z.2 w * z.2 a - 1)))
      continuous_const)

private theorem miss_zero_nonempty : missZero.Nonempty := by
  exact ⟨(0, 0), by norm_num [missZero]⟩

private theorem miss_one_nonempty : missOne.Nonempty := by
  refine ⟨(fun _ => WithLp.toLp 2
    (fun i : ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1) =>
      Sum.elim (fun _ => (1 : ℝ)) (fun _ => -1) i), 0), ?_⟩
  norm_num [missOne, discrim, w, a]

private theorem miss_zero_disjoint :
    Disjoint missZero {z | (affinePlane 0 z ∩
      solutionSet (L := 1) (m := fun _ => 1) (fun _ => 1)).Nonempty} := by
  rw [Set.disjoint_left]
  intro z hz hx
  obtain ⟨θ, hθ, hs⟩ := hx
  have hzero : θ - z.2 = 0 := by
    simpa [affinePlane] using hθ
  have heq : θ = z.2 := sub_eq_zero.mp hzero
  have hf := scalar_fiber θ hs
  rw [heq] at hf
  exact (ne_of_lt hz) hf

private theorem miss_one_disjoint :
    Disjoint missOne {z | (affinePlane 1 z ∩
      solutionSet (L := 1) (m := fun _ => 1) (fun _ => 1)).Nonempty} := by
  rw [Set.disjoint_left]
  intro z hz hx
  obtain ⟨θ, hθ, hs⟩ := hx
  have hspan : θ - z.2 ∈ Submodule.span ℝ ({z.1 0} : Set (EuclideanSpace ℝ ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1))) := by
    simpa [affinePlane, Set.range_unique] using hθ
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hspan
  have heq : θ = z.2 + t • z.1 0 := Eq.symm (add_eq_of_eq_sub' ht)
  have hf := scalar_fiber θ hs
  rw [heq] at hf
  have hq : (z.1 0 w * z.1 0 a) * (t * t) +
      (z.2 w * z.1 0 a + z.1 0 w * z.2 a) * t + (z.2 w * z.2 a - 1) = 0 := by
    change (z.2 w + t * z.1 0 w) * (z.2 a + t * z.1 0 a) = 1 at hf
    nlinarith [hf]
  exact quadratic_ne_zero_of_discrim_ne_sq
    (fun s h => (not_le_of_gt hz.2) (h ▸ sq_nonneg s)) t hq

private theorem hit_zero_lt_one :
    sampleLaw ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1) 0 {z | (affinePlane 0 z ∩
      solutionSet (L := 1) (m := fun _ => 1) (fun _ => 1)).Nonempty} < 1 := by
  let hGauss : (stdGaussian (EuclideanSpace ℝ ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1))).IsOpenPosMeasure := gaussian_open_support ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1)
  let : (sampleLaw ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1) 0).IsOpenPosMeasure := by
    unfold sampleLaw
    infer_instance
  let : IsProbabilityMeasure (sampleLaw ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1) 0) := by
    unfold sampleLaw
    infer_instance
  have hp := miss_zero_open.measure_pos (sampleLaw ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1) 0) miss_zero_nonempty
  have hc := prob_compl_lt_one_sub_of_lt_prob hp miss_zero_open.measurableSet
  simp only [tsub_zero] at hc
  exact lt_of_le_of_lt
    (measure_mono (fun z hz hm => Set.disjoint_left.mp miss_zero_disjoint hm hz)) hc

private theorem hit_one_lt_one :
    sampleLaw ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1) 1 {z | (affinePlane 1 z ∩
      solutionSet (L := 1) (m := fun _ => 1) (fun _ => 1)).Nonempty} < 1 := by
  let hGauss : (stdGaussian (EuclideanSpace ℝ ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1))).IsOpenPosMeasure := gaussian_open_support ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1)
  let : (sampleLaw ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1) 1).IsOpenPosMeasure := by
    unfold sampleLaw
    infer_instance
  let : IsProbabilityMeasure (sampleLaw ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1) 1) := by
    unfold sampleLaw
    infer_instance
  have hp := miss_one_open.measure_pos (sampleLaw ((Σ _ : Fin 1, Fin 1 × Fin 1) ⊕ Fin 1) 1) miss_one_nonempty
  have hc := prob_compl_lt_one_sub_of_lt_prob hp miss_one_open.measurableSet
  simp only [tsub_zero] at hc
  exact lt_of_le_of_lt
    (measure_mono (fun z hz hm => Set.disjoint_left.mp miss_one_disjoint hm hz)) hc

theorem result : ¬ claim := by
  intro h
  have hh := h 1 (fun _ => 1) (by decide) (by intros; exact le_refl _) (fun _ => 1)
    (by intro hzero; have := congrFun hzero 0; norm_num at this)
  have hl : (2 : ℕ∞) ≤ intrinsicDimension
      (solutionSet (L := 1) (m := fun _ => 1) (fun _ => 1)) := by
    apply le_sInf
    rintro n ⟨d, hd, rfl, hp⟩
    by_cases htwo : 2 ≤ d
    · exact_mod_cast htwo
    · have hdlt : d < 2 := Nat.lt_of_not_ge htwo
      interval_cases d
      · exact False.elim ((ne_of_lt hit_zero_lt_one) hp)
      · exact False.elim ((ne_of_lt hit_one_lt_one) hp)
  rw [hh] at hl
  norm_num at hl

end D5.S3.QuadraticForms.DeepLinearIntrinsicDimensionRefutation
