/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Function.LpSpace.Basic]
   utility: none
   digest: Nonlinear contractions of the actual free-root tree extensions. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryMarkovSemigroup

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (Edge H P)
open BiasedBoundaryTrace (G M J Omega cylinder indicator)
open BiasedBoundaryPathSplit (prefixes prefixSum constG boundary_path_split)
open BiasedBoundaryFreeRootForm (D energy free_root_least_energy)
open MeasureTheory Filter
open scoped BigOperators Topology

private theorem prefixes_step (p : Address) (b : Bool) :
    prefixes (p ++ [b]) = insert ⟨p ++ [b], by simp⟩ (prefixes p) := by
  classical
  ext q
  simp [prefixes, List.inits_append, List.inits_cons, Subtype.ext_iff, or_comm]

private theorem prefix_step (p : Address) (b : Bool) (z : H) :
    prefixSum (p ++ [b]) z = prefixSum p z + z ⟨p ++ [b], by simp⟩ := by
  classical
  rw [boundary_path_split.2.2.1, prefixes_step, Finset.sum_insert]
  · rw [boundary_path_split.2.2.1]
    ring
  · intro h
    have hpre : (p ++ [b]).IsPrefix p := by
      simpa [prefixes, List.mem_inits] using h
    have := hpre.length_le
    simp at this

/-- The actual rooted potential, including its free real root value. -/
def potential (c : ℝ) (z : H) (p : Address) : ℝ := c + prefixSum p z

private theorem potential_step (c : ℝ) (z : H) (p : Address) (b : Bool) :
    potential c z (p ++ [b]) = potential c z p + z ⟨p ++ [b], by simp⟩ := by
  simp only [potential, prefix_step]
  ring

private theorem potential_increment (c : ℝ) (z : H) (p : Edge) :
    potential c z p.val - potential c z p.val.dropLast = z p := by
  have h : ∀ (q : Address) (hq : q ≠ []),
      potential c z q - potential c z q.dropLast = z ⟨q,hq⟩ := by
    intro q
    induction q using List.reverseRecOn with
    | nil => simp
    | append_singleton q b ih =>
      intro hq
      rw [List.dropLast_concat, potential_step]
      ring
  exact h p.val p.property

/-- Increment of the contracted actual potential along an original edge. -/
def contractedCoordinate (χ : ℝ → ℝ) (c : ℝ) (z : H) (p : Edge) : ℝ :=
  χ (potential c z p.val) - χ (potential c z p.val.dropLast)

private theorem contracted_bound (χ : ℝ → ℝ) (hχ : LipschitzWith 1 χ)
    (c : ℝ) (z : H) (p : Edge) : ‖contractedCoordinate χ c z p‖ ≤ ‖z p‖ := by
  have h := hχ.norm_sub_le (potential c z p.val) (potential c z p.val.dropLast)
  simpa only [contractedCoordinate, NNReal.coe_one, one_mul, potential_increment] using h

/-- Square-summable increments after contraction of the actual rooted potential. -/
def contracted (χ : ℝ → ℝ) (hχ : LipschitzWith 1 χ) (c : ℝ) (z : H) : H :=
  ⟨contractedCoordinate χ c z,
    (lp.memℓp z).mono' (contracted_bound χ hχ c z)⟩

private theorem contracted_prefix (χ : ℝ → ℝ) (hχ : LipschitzWith 1 χ)
    (c : ℝ) (z : H) (p : Address) :
    potential (χ c) (contracted χ hχ c z) p = χ (potential c z p) := by
  induction p using List.reverseRecOn with
  | nil => simp [potential, prefixSum, prefixes]
  | append_singleton p b ih =>
    rw [potential_step, ih]
    change χ (potential c z p) +
      (χ (potential c z (p ++ [b])) - χ (potential c z (p ++ [b]).dropLast)) = _
    rw [List.dropLast_concat]
    ring

/-- Every real normal contraction acts on the original all-edge extension with
no increase of increment energy, and its exact potential agrees at every vertex.
The root is transformed freely; no condition on the image of zero is required. -/
theorem contracted_extension (χ : ℝ → ℝ) (hχ : LipschitzWith 1 χ)
    (c : ℝ) (z : H) :
    (∀ p : Edge, contracted χ hχ c z p =
      χ (potential c z p.val) - χ (potential c z p.val.dropLast)) ∧
    ‖contracted χ hχ c z‖ ≤ ‖z‖ ∧
    (∀ p : Address, potential (χ c) (contracted χ hχ c z) p =
      χ (potential c z p)) := by
  refine ⟨fun _ => rfl, ?_, contracted_prefix χ hχ c z⟩
  exact lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (contracted_bound χ hχ c z)

#print axioms contracted_extension
end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryMarkovSemigroup
