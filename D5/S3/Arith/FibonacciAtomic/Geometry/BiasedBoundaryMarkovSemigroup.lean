/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Function.LpSpace.Basic]
   utility: none
   digest: Nonlinear contractions of the actual free-root tree extensions. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm

/-! Nonlinear original-edge extensions and their actual biased boundary traces. -/

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
  simp [prefixes, List.inits_append, Subtype.ext_iff, or_comm]

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
  | nil =>
    have he : prefixes [] = ∅ := by
      ext q
      simp [prefixes, q.property]
    simp [potential, prefixSum, he]
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

private def cutoff (h : ℕ) : Finset Edge := by
  classical
  exact ((Finset.range (h+1)).biUnion fun n =>
    (Finset.univ : Finset (Fin n → Bool)).image List.ofFn).subtype (· ≠ [])

private theorem mem_cutoff (h : ℕ) (p : Edge) : p ∈ cutoff h ↔ p.val.length ≤ h := by
  classical
  simp only [cutoff, Finset.mem_subtype, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, w, hw⟩
    rw [← hw, List.length_ofFn]
    omega
  · intro hp
    exact ⟨p.val.length, by omega, p.val.get, List.ofFn_get p.val⟩

private theorem cutoff_expansion (h : ℕ) (z : H) :
    P h z = ∑ p ∈ cutoff h, lp.single 2 p (z p) := by
  classical
  ext q
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Pi.single_apply]
  change (if q.val.length ≤ h then z q else 0) = _
  simp [← mem_cutoff h q, eq_comm]

private theorem ray_prefix_iff (ω : Omega) (h : ℕ) (p : Edge) :
    p.val.IsPrefix (D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix ω h) ↔
      p.val.length ≤ h ∧ ω ∈ cylinder p.val := by
  let r := D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix ω h
  have hr : r.length = h := by simp [r, D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix]
  constructor
  · intro hp
    refine ⟨by simpa only [hr] using hp.length_le, ?_⟩
    apply (BiasedBoundaryCylinderProjection.cylinder_ray _ _).mpr
    rw [List.prefix_iff_eq_take.mp hp]
    simp [r, D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix, List.take_ofFn,
      show min p.val.length h = p.val.length from min_eq_left (by simpa only [hr] using hp.length_le)]
  · rintro ⟨hl,hω⟩
    rw [(BiasedBoundaryCylinderProjection.cylinder_ray _ _).mp hω]
    apply List.prefix_iff_getElem.mpr
    refine ⟨by simpa [r, D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix] using hl, ?_⟩
    intro i hi
    simp [r, D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix]

private theorem cutoff_trace (h : ℕ) (z : H) :
    J (P h z) =ᵐ[M] (fun ω => prefixSum
      (D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix ω h) z) := by
  classical
  rw [cutoff_expansion, map_sum]
  simp_rw [BiasedBoundaryTrace.J_single]
  have hi : ∀ᵐ ω ∂M, ∀ p : Edge,
      indicator p ω = (cylinder p.val).indicator (fun _ => (1 : ℝ)) ω :=
    ae_all_iff.mpr (fun _ => indicatorConstLp_coeFn)
  have hm : ∀ᵐ ω ∂M, ∀ p : Edge,
      (z p • indicator p : G) ω = z p * indicator p ω :=
    ae_all_iff.mpr (fun p => Lp.coeFn_smul (z p) (indicator p))
  filter_upwards [Lp.coeFn_finsetSum (cutoff h) (fun p => z p • indicator p), hi, hm]
    with ω hs hi hm
  rw [hs, boundary_path_split.2.2.1]
  simp only [Finset.sum_apply]
  have he : (cutoff h).filter (fun p => ω ∈ cylinder p.val) =
      prefixes (D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix ω h) := by
    ext p
    simp only [Finset.mem_filter, mem_cutoff, prefixes, Finset.mem_subtype,
      List.mem_toFinset, List.mem_inits]
    exact (ray_prefix_iff ω h p).symm
  rw [← he, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hm p, hi p]
  by_cases hω : ω ∈ cylinder p.val <;> simp [hω]

/-- The contracted original-edge extension has an actual trace in the original
free-root domain. Its energy is no larger than that of the least extension of F,
and its value at every finite vertex is the contracted original potential. -/
theorem contracted_trace_candidate (χ : ℝ → ℝ) (hχ : LipschitzWith 1 χ) (F : D) :
    ∃ (c : ℝ) (w : H),
      F.val = constG c + J (BiasedBoundaryFreeRootForm.lift F) ∧
      constG (χ c) + J w ∈ D ∧
      energy (constG (χ c) + J w) ≤ energy F.val ∧
      (∀ p : Address, potential (χ c) w p =
        χ (potential c (BiasedBoundaryFreeRootForm.lift F) p)) := by
  let z := BiasedBoundaryFreeRootForm.lift F
  let c := BiasedBoundaryCentering.mean F.val - BiasedBoundaryCentering.mean (J z)
  let w := contracted χ hχ c z
  have he := free_root_least_energy F
  have hm : constG (χ c) + J w ∈ D := ⟨χ c, w, rfl⟩
  have hw := contracted_extension χ hχ c z
  refine ⟨c, w, he.2.2.1, hm, ?_, hw.2.2⟩
  have hb := (free_root_least_energy ⟨constG (χ c) + J w, hm⟩).2.2.2.2.1
    (χ c) w rfl
  calc
    energy (constG (χ c) + J w) =
        ‖BiasedBoundaryFreeRootForm.lift ⟨constG (χ c) + J w, hm⟩‖^2 :=
      (free_root_least_energy ⟨constG (χ c) + J w, hm⟩).2.2.2.1
    _ ≤ ‖w‖^2 := hb.2
    _ ≤ ‖z‖^2 := pow_le_pow_left₀ (norm_nonneg _) hw.2.1 2
    _ = energy F.val := he.2.2.2.1.symm

#print axioms contracted_extension
#print axioms contracted_trace_candidate
end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryMarkovSemigroup
