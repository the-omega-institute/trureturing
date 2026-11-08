/- GID: D5/S3/ContinuousObservables/C0Multipliers
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/C0Multipliers
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.Multiplier, mathlib/module/Mathlib.Topology.ContinuousMap.ZeroAtInfty, mathlib/module/Mathlib.Topology.UrysohnsLemma]
   utility: none
   digest: Double centralizers of continuous fields vanishing at infinity are bounded continuous fields with their pointwise left and right actions. -/

import Mathlib.Analysis.CStarAlgebra.Multiplier
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FunProp

/-! # Multipliers of fields vanishing at infinity

Local unit sections recover a matrix field from the two centralizer actions.
The recovered field is continuous, bounded, and has exactly the multiplier norm.
-/

noncomputable section

open Filter Set
open scoped Topology ZeroAtInfty BoundedContinuousFunction ComplexOrder

namespace D5.S3.ContinuousObservables.C0Multipliers

variable {X B : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [CStarAlgebra B] [Nontrivial B]

private theorem local_unit (K : Set X) (hK : IsCompact K) :
    ∃ e : C₀(X, B), ‖e‖ ≤ 1 ∧ ∀ x ∈ K, e x = 1 := by
  obtain ⟨c, hcK, _, hcs, hc⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  let e : C₀(X, B) :=
    { toFun := fun x => (c x : ℂ) • (1 : B)
      continuous_toFun := by fun_prop
      zero_at_infty' := by
        have hs : HasCompactSupport (fun x => (c x : ℂ)) :=
          hcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
        exact (hs.smul_right (f' := fun _ => (1 : B))).is_zero_at_infty }
  refine ⟨e, ?_, ?_⟩
  · change ‖e.toBCF‖ ≤ 1
    apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)).2
    intro x
    change ‖(c x : ℂ) • (1 : B)‖ ≤ 1
    simpa [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc x).1]
      using (hc x).2
  · intro x hx
    change (c x : ℂ) • (1 : B) = 1
    rw [show c x = 1 from hcK hx]
    simp

private def pointUnit (x : X) : C₀(X, B) :=
  (local_unit (B := B) {x} isCompact_singleton).choose

private theorem pointUnit_spec (x : X) :
    ‖pointUnit (B := B) x‖ ≤ 1 ∧ pointUnit (B := B) x x = 1 := by
  have h := (local_unit (B := B) {x} isCompact_singleton).choose_spec
  exact ⟨h.1, h.2 x (mem_singleton x)⟩

private def field (m : DoubleCentralizer ℂ C₀(X, B)) (x : X) : B :=
  m.fst (pointUnit x) x

private theorem actions (m : DoubleCentralizer ℂ C₀(X, B)) (f : C₀(X, B)) (x : X) :
    m.fst f x = field m x * f x ∧ m.snd f x = f x * field m x := by
  have he := (pointUnit_spec (B := B) x).2
  have heq := congrArg (fun g : C₀(X, B) => g x) (m.central (pointUnit x) (pointUnit x))
  change m.snd (pointUnit x) x * pointUnit x x =
    pointUnit x x * m.fst (pointUnit x) x at heq
  rw [he, mul_one, one_mul] at heq
  constructor
  · have h := congrArg (fun g : C₀(X, B) => g x) (m.central (pointUnit x) f)
    change m.snd (pointUnit x) x * f x = pointUnit x x * m.fst f x at h
    simpa [he, heq, field] using h.symm
  · have h := congrArg (fun g : C₀(X, B) => g x) (m.central f (pointUnit x))
    change m.snd f x * pointUnit x x = f x * m.fst (pointUnit x) x at h
    simpa [he, field] using h

private theorem field_continuous (m : DoubleCentralizer ℂ C₀(X, B)) :
    Continuous (field m) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨e, _, he⟩ := local_unit (B := B) K hK
  apply (map_continuous (m.fst e)).continuousAt.congr
  filter_upwards [hKx] with y hy
  simpa [he y hy] using (actions m e y).1

private theorem field_bound (m : DoubleCentralizer ℂ C₀(X, B)) (x : X) :
    ‖field m x‖ ≤ ‖m‖ := by
  calc
    ‖field m x‖ ≤ ‖m.fst (pointUnit x)‖ :=
      (m.fst (pointUnit x)).toBCF.norm_coe_le_norm x
    _ ≤ ‖m.fst‖ * ‖pointUnit (B := B) x‖ := m.fst.le_opNorm _
    _ ≤ ‖m‖ * 1 := by
      rw [DoubleCentralizer.norm_fst]
      exact mul_le_mul_of_nonneg_left (pointUnit_spec x).1 (norm_nonneg _)
    _ = ‖m‖ := mul_one _

private def boundedField (m : DoubleCentralizer ℂ C₀(X, B)) : X →ᵇ B :=
  BoundedContinuousFunction.mkOfBound ⟨field m, field_continuous m⟩ (2 * ‖m‖)
    (fun x y => (dist_le_norm_add_norm _ _).trans <| by
      change ‖field m x‖ + ‖field m y‖ ≤ 2 * ‖m‖
      simpa [two_mul] using add_le_add (field_bound m x) (field_bound m y))

private def leftProduct (h : X →ᵇ B) (f : C₀(X, B)) : C₀(X, B) where
  toFun x := h x * f x
  continuous_toFun := h.continuous.mul (map_continuous f)
  zero_at_infty' := Filter.isBoundedUnder_le_mul_tendsto_zero
    (isBoundedUnder_of ⟨‖h‖, h.norm_coe_le_norm⟩) (zero_at_infty f)

private def rightProduct (h : X →ᵇ B) (f : C₀(X, B)) : C₀(X, B) where
  toFun x := f x * h x
  continuous_toFun := (map_continuous f).mul h.continuous
  zero_at_infty' := (zero_at_infty f).zero_mul_isBoundedUnder_le
    (isBoundedUnder_of ⟨‖h‖, h.norm_coe_le_norm⟩)

private def leftOperator (h : X →ᵇ B) : C₀(X, B) →L[ℂ] C₀(X, B) :=
  LinearMap.mkContinuous
    { toFun := leftProduct h
      map_add' := fun f g => ZeroAtInftyContinuousMap.ext fun x => mul_add _ _ _
      map_smul' := fun c f => ZeroAtInftyContinuousMap.ext fun x => mul_smul_comm _ _ _ }
    ‖h‖ (fun f => by
      change ‖(leftProduct h f).toBCF‖ ≤ ‖h‖ * ‖f‖
      apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
      intro x
      change ‖h x * f x‖ ≤ ‖h‖ * ‖f‖
      exact (norm_mul_le _ _).trans (mul_le_mul (h.norm_coe_le_norm x)
        (f.toBCF.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)))

private def rightOperator (h : X →ᵇ B) : C₀(X, B) →L[ℂ] C₀(X, B) :=
  LinearMap.mkContinuous
    { toFun := rightProduct h
      map_add' := fun f g => ZeroAtInftyContinuousMap.ext fun x => add_mul _ _ _
      map_smul' := fun c f => ZeroAtInftyContinuousMap.ext fun x => smul_mul_assoc _ _ _ }
    ‖h‖ (fun f => by
      apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
      intro x
      exact (norm_mul_le _ _).trans ((mul_le_mul (f.toBCF.norm_coe_le_norm x)
        (h.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)))

/-- A bounded continuous field acts on every element vanishing at infinity. -/
def multiplier (h : X →ᵇ B) : DoubleCentralizer ℂ C₀(X, B) where
  fst := leftOperator h
  snd := rightOperator h
  central _ _ := ZeroAtInftyContinuousMap.ext fun _ => mul_assoc _ _ _

/-- Every double centralizer is represented by a unique bounded continuous field,
with both actions on the whole complex algebra and the exact uniform norm. -/
private theorem representation (m : DoubleCentralizer ℂ C₀(X, B)) :
    ∃! h : X →ᵇ B, (∀ (f : C₀(X, B)) (x : X),
      m.fst f x = h x * f x ∧ m.snd f x = f x * h x) ∧ ‖h‖ = ‖m‖ := by
  refine ⟨boundedField m, ⟨fun f x => actions m f x, ?_⟩, ?_⟩
  · apply le_antisymm
    · exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 (field_bound m)
    · rw [← DoubleCentralizer.norm_fst]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro f
      change ‖(m.fst f).toBCF‖ ≤ ‖boundedField m‖ * ‖f‖
      apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
      intro x
      change ‖m.fst f x‖ ≤ ‖boundedField m‖ * ‖f‖
      rw [(actions m f x).1]
      exact (norm_mul_le _ _).trans (mul_le_mul
        ((boundedField m).norm_coe_le_norm x) (f.toBCF.norm_coe_le_norm x)
        (norm_nonneg _) (norm_nonneg _))
  · intro h hh
    apply BoundedContinuousFunction.ext
    intro x
    have hv := (hh.1 (pointUnit x) x).1
    change h x = m.fst (pointUnit x) x
    rw [(pointUnit_spec (B := B) x).2, mul_one] at hv
    exact hv.symm

omit [LocallyCompactSpace X] [T2Space X] [Nontrivial B] in
private theorem centralizer_ext {m n : DoubleCentralizer ℂ C₀(X, B)}
    (hL : ∀ f x, m.fst f x = n.fst f x)
    (hR : ∀ f x, m.snd f x = n.snd f x) : m = n := by
  apply DoubleCentralizer.ext ℂ C₀(X, B)
  exact Prod.ext
    (ContinuousLinearMap.ext fun f => ZeroAtInftyContinuousMap.ext (hL f))
    (ContinuousLinearMap.ext fun f => ZeroAtInftyContinuousMap.ext (hR f))

private def multiplierHom : (X →ᵇ B) →⋆ₙₐ[ℂ] DoubleCentralizer ℂ C₀(X, B) where
  toFun := multiplier
  map_zero' := by
    apply centralizer_ext <;> intro f x
    · change (0 : B) * f x = 0
      exact zero_mul _
    · change f x * (0 : B) = 0
      exact mul_zero _
  map_add' h k := by
    apply centralizer_ext <;> intro f x
    · change (h x + k x) * f x = h x * f x + k x * f x
      exact add_mul _ _ _
    · change f x * (h x + k x) = f x * h x + f x * k x
      exact mul_add _ _ _
  map_mul' h k := by
    apply centralizer_ext <;> intro f x
    · change (h x * k x) * f x = h x * (k x * f x)
      exact mul_assoc _ _ _
    · change f x * (h x * k x) = (f x * h x) * k x
      exact (mul_assoc _ _ _).symm
  map_smul' c h := by
    apply centralizer_ext <;> intro f x
    · change (c • h x) * f x = c • (h x * f x)
      exact smul_mul_assoc _ _ _
    · change f x * (c • h x) = c • (f x * h x)
      exact mul_smul_comm _ _ _
  map_star' h := by
    apply centralizer_ext <;> intro f x
    · change star (h x) * f x = star (star (f x) * h x)
      simp only [star_mul, star_star]
    · change f x * star (h x) = star (h x * star (f x))
      simp only [star_mul, star_star]

private theorem multiplier_bijective :
    Function.Bijective (multiplierHom (X := X) (B := B)) := by
  constructor
  · intro h k heq
    apply BoundedContinuousFunction.ext
    intro x
    have hx := congrArg
      (fun m : DoubleCentralizer ℂ C₀(X, B) => m.fst (pointUnit x) x) heq
    change h x * pointUnit x x = k x * pointUnit x x at hx
    simpa [(pointUnit_spec (B := B) x).2] using hx
  · intro m
    obtain ⟨h, hh, _⟩ := representation m
    refine ⟨h, ?_⟩
    apply centralizer_ext <;> intro f x
    · exact (hh.1 f x).1.symm
    · exact (hh.1 f x).2.symm

/-- The genuine star algebra equivalence between bounded fields and double centralizers. -/
def equivalence : (X →ᵇ B) ≃⋆ₐ[ℂ] DoubleCentralizer ℂ C₀(X, B) :=
  StarAlgEquiv.ofBijective multiplierHom multiplier_bijective

/-- The equivalence is isometric for the uniform field norm and multiplier operator norm. -/
private theorem equivalence_isometry :
    Isometry (equivalence (X := X) (B := B)) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro h
  obtain ⟨k, hk, _⟩ := representation (equivalence h)
  have hkh : k = h := by
    apply BoundedContinuousFunction.ext
    intro x
    have hx := (hk.1 (pointUnit x) x).1
    change h x * pointUnit x x = k x * pointUnit x x at hx
    simpa [(pointUnit_spec (B := B) x).2] using hx.symm
  exact (hkh ▸ hk.2).symm

/-- Both pointwise actions hold for every complex element vanishing at infinity. -/
private theorem equivalence_actions (h : X →ᵇ B) (f : C₀(X, B)) (x : X) :
    (equivalence h).fst f x = h x * f x ∧
      (equivalence h).snd f x = f x * h x := ⟨rfl, rfl⟩

/-- The punctured interval, with every reciprocal from the fifth onward removed. -/
def sourceDomain : Set ℝ :=
  Ioo 0 (1 / 4) \ {t | ∃ n : ℕ, 5 ≤ n ∧ t = 1 / (n : ℝ)}

private theorem sourceDomain_open : IsOpen sourceDomain := by
  have hlim : Tendsto (fun n : ℕ => 1 / ((n + 5 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 5).2 tendsto_one_div_atTop_nhds_zero_nat
  have hc := hlim.isCompact_insert_range.isClosed
  have heq : sourceDomain =
      Ioo 0 (1 / 4) \ insert 0 (range (fun n : ℕ => 1 / ((n + 5 : ℕ) : ℝ))) := by
    ext t
    constructor
    · rintro ⟨ht, hn⟩
      refine ⟨ht, ?_⟩
      rintro (hzero | ⟨n, hn'⟩)
      · exact (ne_of_gt ht.1) hzero
      · exact hn ⟨n + 5, by omega, hn'.symm⟩
    · rintro ⟨ht, hn⟩
      refine ⟨ht, ?_⟩
      rintro ⟨n, h5, rfl⟩
      apply hn
      right
      refine ⟨n - 5, ?_⟩
      change 1 / ((n - 5 + 5 : ℕ) : ℝ) = 1 / (n : ℝ)
      rw [Nat.sub_add_cancel h5]
  rw [heq]
  exact isOpen_Ioo.sdiff hc

instance sourceDomain_locallyCompact : LocallyCompactSpace sourceDomain :=
  sourceDomain_open.locallyCompactSpace

/-- The full two by two complex matrix algebra with its C-star operator norm. -/
abbrev MatrixFiber := CStarMatrix (Fin 2) (Fin 2) ℂ

/-- The whole complex algebra of matrix fields vanishing at infinity on the punctured interval. -/
abbrev SourceAlgebra := C₀(sourceDomain, MatrixFiber)

/-- Every multiplier of the whole source algebra is represented uniquely and isometrically
by a bounded continuous full matrix field, with both actions on every algebra element. -/
theorem source_multiplier_certificate :
    ∃ e : (sourceDomain →ᵇ MatrixFiber) ≃⋆ₐ[ℂ] DoubleCentralizer ℂ SourceAlgebra,
      Isometry e ∧
      (∀ (h : sourceDomain →ᵇ MatrixFiber) (f : SourceAlgebra) (x : sourceDomain),
        (e h).fst f x = h x * f x ∧ (e h).snd f x = f x * h x) ∧
      (∀ m : DoubleCentralizer ℂ SourceAlgebra,
        ∃! h : sourceDomain →ᵇ MatrixFiber,
          (∀ (f : SourceAlgebra) (x : sourceDomain),
            m.fst f x = h x * f x ∧ m.snd f x = f x * h x) ∧ ‖h‖ = ‖m‖) := by
  exact ⟨equivalence, equivalence_isometry, equivalence_actions, representation⟩

end D5.S3.ContinuousObservables.C0Multipliers
