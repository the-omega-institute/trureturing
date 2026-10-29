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
open MeasureTheory hiding cylinder
open Filter
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
private theorem contracted_extension (χ : ℝ → ℝ) (hχ : LipschitzWith 1 χ)
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
  rw [FiniteSourceCovariance.P_expand]
  apply Finset.sum_congr
  · ext p
    change p ∈ ((List.finite_length_le Bool h).toFinset).subtype (· ≠ []) ↔ p ∈ cutoff h
    simp [mem_cutoff]
  · intro p hp
    change z p • lp.single 2 p (1 : ℝ) = lp.single 2 p (z p)
    rw [← lp.single_smul]
    simp

private theorem ray_prefix_iff (ω : Omega) (h : ℕ) (p : Edge) :
    p.val.IsPrefix (D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix ω h) ↔
      p.val.length ≤ h ∧ ω ∈ cylinder p.val := by
  constructor
  · intro hp
    have hl : p.val.length ≤ h := by
      simpa [D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix] using hp.length_le
    refine ⟨hl, (BiasedBoundaryCylinderProjection.cylinder_ray _ _).mpr ?_⟩
    apply List.ext_getElem (by simp [D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix])
    intro i hi hj
    have he := hp.getElem hi
    simpa [D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix] using he
  · rintro ⟨hl,hω⟩
    rw [(BiasedBoundaryCylinderProjection.cylinder_ray _ _).mp hω]
    apply List.prefix_iff_getElem.mpr
    refine ⟨by simpa [D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix] using hl, ?_⟩
    intro i hi
    simp [D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix]

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
  have he : (cutoff h).filter (fun p : Edge => ω ∈ cylinder p.val) =
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

private theorem projection_tendsto (z : H) : Tendsto (fun h : ℕ => P h z) atTop (𝓝 z) := by
  have hc : Tendsto cutoff atTop atTop := by
    apply tendsto_atTop.mpr
    intro s
    filter_upwards [eventually_ge_atTop (s.sup (fun p : Edge => p.val.length))] with h hh
    intro p hp
    exact (mem_cutoff h p).mpr ((Finset.le_sup hp).trans hh)
  have hs := (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) z).comp hc
  simpa only [Function.comp_def, ← cutoff_expansion] using hs

private theorem shifted_lipschitz (χ : ℝ → ℝ) (hχ : LipschitzWith 1 χ) :
    LipschitzWith 1 (fun x => χ x - χ 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hχ.dist_le_mul x y

/-- Composition on the actual probability L2 space, without requiring χ(0)=0. -/
def contractLp (χ : ℝ → ℝ) (hχ : LipschitzWith 1 χ) (F : G) : G :=
  constG (χ 0) + (shifted_lipschitz χ hχ).compLp (by simp) F

private theorem contractLp_ae (χ : ℝ → ℝ) (hχ : LipschitzWith 1 χ) (F : G) :
    contractLp χ hχ F =ᵐ[M] (fun ω => χ (F ω)) := by
  filter_upwards [Lp.coeFn_add (constG (χ 0)) ((shifted_lipschitz χ hχ).compLp (by simp) F),
    boundary_path_split.2.2.2.1 (χ 0),
    (shifted_lipschitz χ hχ).coeFn_compLp (by simp) F] with ω ha hc hf
  change (constG (χ 0) + (shifted_lipschitz χ hχ).compLp (by simp) F) ω = _
  rw [ha, Pi.add_apply, hc, hf]
  change χ 0 + (χ (F ω) - χ 0) = _
  ring

private theorem depth_ae (c : ℝ) (z : H) (h : ℕ) :
    constG c + J (P h z) =ᵐ[M] (fun ω => potential c z
      (D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix ω h)) := by
  filter_upwards [Lp.coeFn_add (constG c) (J (P h z)),
    boundary_path_split.2.2.2.1 c, cutoff_trace h z] with ω ha hc hz
  rw [ha, Pi.add_apply, hc, hz]
  rfl

private theorem trace_compatibility (χ : ℝ → ℝ) (hχ : LipschitzWith 1 χ)
    (c : ℝ) (z : H) :
    contractLp χ hχ (constG c + J z) = constG (χ c) + J (contracted χ hχ c z) := by
  have hc : Continuous (contractLp χ hχ : G → G) :=
    continuous_const.add ((shifted_lipschitz χ hχ).continuous_compLp (by simp))
  have hlim (d : ℝ) (w : H) :
      Tendsto (fun h : ℕ => constG d + J (P h w)) atTop (𝓝 (constG d + J w)) :=
    tendsto_const_nhds.add (J.continuous.continuousAt.tendsto.comp (projection_tendsto w))
  have he (h : ℕ) : contractLp χ hχ (constG c + J (P h z)) =
      constG (χ c) + J (P h (contracted χ hχ c z)) := by
    apply Lp.ext
    filter_upwards [contractLp_ae χ hχ (constG c + J (P h z)),
      depth_ae c z h, depth_ae (χ c) (contracted χ hχ c z) h] with ω hχ hF hG
    rw [hχ, hF, hG, contracted_prefix]
  exact tendsto_nhds_unique ((hc.continuousAt.tendsto.comp (hlim c z)).congr he)
    (hlim (χ c) (contracted χ hχ c z))

/-- The contracted original-edge extension has an actual trace in the original
free-root domain. Its energy is no larger than that of the least extension of F,
and its value at every finite vertex is the contracted original potential. -/
private theorem contracted_trace_candidate (χ : ℝ → ℝ) (hχ : LipschitzWith 1 χ) (F : D) :
    ∃ (c : ℝ) (w : H),
      F.val = constG c + J (BiasedBoundaryFreeRootForm.lift F) ∧
      w = contracted χ hχ c (BiasedBoundaryFreeRootForm.lift F) ∧
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
  refine ⟨c, w, he.2.2.1, rfl, hm, ?_, hw.2.2⟩
  have hb := (free_root_least_energy ⟨constG (χ c) + J w, hm⟩).2.2.2.2.1
    (χ c) w rfl
  calc
    energy (constG (χ c) + J w) =
        ‖BiasedBoundaryFreeRootForm.lift ⟨constG (χ c) + J w, hm⟩‖^2 :=
      (free_root_least_energy ⟨constG (χ c) + J w, hm⟩).2.2.2.1
    _ ≤ ‖w‖^2 := hb.2
    _ ≤ ‖z‖^2 := pow_le_pow_left₀ (norm_nonneg _) hw.2.1 2
    _ = energy F.val := he.2.2.2.1.symm

/-- Every real one-Lipschitz map preserves the actual free-root trace domain
and decreases its original infimum energy on the actual biased probability law. -/
theorem actual_trace_contraction (χ : ℝ → ℝ) (hχ : LipschitzWith 1 χ) (F : D) :
    (contractLp χ hχ F.val =ᵐ[M] (fun ω => χ (F.val ω))) ∧
    contractLp χ hχ F.val ∈ D ∧ energy (contractLp χ hχ F.val) ≤ energy F.val := by
  obtain ⟨c,w,hF,hw,hm,hen,_⟩ := contracted_trace_candidate χ hχ F
  refine ⟨contractLp_ae χ hχ F.val, ?_, ?_⟩
  · rw [hF, trace_compatibility, ← hw]
    exact hm
  · rw [hF, trace_compatibility, ← hw]
    simpa only [← hF] using hen

#print axioms actual_trace_contraction
#print axioms contracted_extension
#print axioms contracted_trace_candidate
end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryMarkovSemigroup
