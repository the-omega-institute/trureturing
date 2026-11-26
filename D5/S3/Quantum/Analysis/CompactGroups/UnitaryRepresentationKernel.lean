/- GID: D5/S3/Quantum/Analysis/CompactGroups/UnitaryRepresentationKernel
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CompactGroups/UnitaryRepresentationKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact groups have finite-dimensional unitary representations with small kernels. -/

import D5.S3.Quantum.Analysis.CompactGroups.ContinuousKernelCompact
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.UrysohnsLemma
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Small kernels of finite-dimensional unitary representations of compact groups

Let `G` be a compact topological group (no separation axiom is assumed) and `U` a neighbourhood
of `1`. Then there is a continuous homomorphism `ρ : G → U(n)` with `ker ρ ⊆ U`.

Let `μ` be a Haar measure and `π` the left regular representation `(π g f) x = f (g⁻¹ * x)` on
`L²(μ)`; it is isometric and strongly continuous. Choose a neighbourhood `V` of `1` with
`V / V ⊆ interior U` and a continuous `φ ≥ 0` with `φ 1 = 1` vanishing outside `V`. The integral
operator `T` with kernel `φ (x⁻¹ * y)` maps `L²(μ)` compactly into `C(G)` and commutes with `π`.
For `g ∉ U` the continuous function `T φ` takes the nonzero value `∫ φ ^ 2` at `1` and the value
`0` at `g`, so `π g` moves `T φ`.

The operator `S = T T†` is compact and self-adjoint and commutes with `π`. Its eigenspaces span a
dense subspace (spectral theorem), so a continuous operator that fixes every eigenspace of `S`
with nonzero eigenvalue fixes the closure of the range of `S`, which contains the range of `T`.
Hence for each
`c ∉ interior U` some eigenspace of `S` with nonzero eigenvalue, which is finite-dimensional and
`π`-invariant, contains a vector moved by `c`, and then by every point of a neighbourhood of `c`.
Compactness of the complement of `interior U` gives finitely many such eigenspaces; their sum `W`
is finite-dimensional and invariant, and the matrix of `π` on `W` in an orthonormal basis is the
required representation. No symmetry of the kernel and no Fubini argument is needed, so the
proof works for non-metrizable groups.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel

/-- A unitary representation on a finite-dimensional invariant subspace, in an orthonormal basis. -/
private lemma exists_unitaryRep_of_invariant {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (π : G →* Module.End ℂ E)
    (hπ : ∀ g v, ‖π g v‖ = ‖v‖) (hc : ∀ v, Continuous fun g => π g v)
    (W : Submodule ℂ E) [FiniteDimensional ℂ W] (hW : ∀ g, ∀ w ∈ W, π g w ∈ W) :
    ∃ (n : ℕ) (ρ : G →ₜ* Matrix.unitaryGroup (Fin n) ℂ), ∀ g, ρ g = 1 → ∀ w ∈ W, π g w = w := by
  let b := stdOrthonormalBasis ℂ W
  let r : G →* Module.End ℂ W :=
    { toFun := fun g => (π g).restrict (hW g)
      map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
      map_mul' := fun g h => LinearMap.ext fun x => Subtype.ext (by simp) }
  let Φ := LinearMap.toMatrixOrthonormal b
  let Ψ : G →* Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ :=
    (Φ.toRingEquiv.toMonoidHom).comp r
  have hU : ∀ g, Ψ g ∈ Matrix.unitaryGroup (Fin (Module.finrank ℂ W)) ℂ := by
    intro g
    have hr : star (r g) * r g = 1 := by
      refine LinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
      rw [LinearMap.star_eq_adjoint, Module.End.mul_apply, LinearMap.adjoint_inner_left,
        Module.End.one_apply]
      have hn : ∀ v : W, ‖r g v‖ = ‖v‖ := fun v => hπ g v
      exact (LinearMap.norm_map_iff_inner_map_map (r g)).1 hn x y
    rw [Matrix.mem_unitaryGroup_iff']
    change star (Φ (r g)) * Φ (r g) = 1
    rw [← map_star, ← map_mul, hr, map_one]
  let ρ0 : G →* Matrix.unitaryGroup (Fin (Module.finrank ℂ W)) ℂ := Ψ.codRestrict _ hU
  have hρc : Continuous ρ0 := by
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    change Continuous fun g => Φ (r g) i j
    simp only [Φ, LinearMap.toMatrixOrthonormal_apply_apply, Submodule.coe_inner]
    exact continuous_const.inner (hc _)
  refine ⟨Module.finrank ℂ W, ⟨ρ0, hρc⟩, fun g hg w hw => ?_⟩
  have h1 : r g = 1 := by
    have : Φ (r g) = Φ 1 := by
      rw [map_one]
      exact congrArg Subtype.val hg
    exact Φ.injective this
  exact congrArg Subtype.val (LinearMap.congr_fun h1 ⟨w, hw⟩)

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- If a continuous linear map `P` fixes every eigenvector of `T ∘ T†` with nonzero eigenvalue,
for a compact operator `T`, then `P` fixes the range of `T`. -/
private lemma apply_eq_of_forall_eigenspace {T : E →L[ℂ] E} (hT : IsCompactOperator T)
    {P : E →ₗ[ℂ] E} (hP : Continuous P)
    (hfix : ∀ c : ℂ, c ≠ 0 →
      ∀ v ∈ Module.End.eigenspace ((T ∘L T.adjoint : E →L[ℂ] E) : E →ₗ[ℂ] E) c, P v = v)
    (f : E) : P (T f) = T f := by
  set S : E →L[ℂ] E := T ∘L T.adjoint with hSdef
  have hS : IsCompactOperator S := hT.comp_clm _
  have hSs : (S : E →ₗ[ℂ] E).IsSymmetric := (IsSelfAdjoint.mul_star_self T).isSymmetric
  let F : Set E := {v | P v = v}
  have hF : IsClosed F := isClosed_eq hP continuous_id
  have hD : ∀ y ∈ ⨆ c, Module.End.eigenspace (S : E →ₗ[ℂ] E) c, S y ∈ F := by
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y => S y ∈ F) hy (fun c x hx => ?_)
      (by simp [F]) (fun x y hx hy => ?_)
    · have hx' : S x = c • x := Module.End.mem_eigenspace_iff.1 hx
      rcases eq_or_ne c 0 with rfl | hc
      · simp [F, hx']
      · simp [F, hx', hfix c hc x hx]
    · simp only [F, Set.mem_ofPred_eq, map_add] at hx hy ⊢
      rw [hx, hy]
  have hdense : Dense ((⨆ c, Module.End.eigenspace (S : E →ₗ[ℂ] E) c : Submodule ℂ E) : Set E) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, ← Submodule.orthogonal_orthogonal_eq_closure,
      ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hS hSs,
      Submodule.bot_orthogonal_eq_top]
  have hrange : ∀ z, S z ∈ F := fun z =>
    hF.closure_subset (map_mem_closure S.continuous (hdense z) fun y hy => hD y hy)
  have hTf : T f ∈ (LinearMap.range (S : E →ₗ[ℂ] E)).topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro u hu
    have h0 : T.adjoint u = 0 := by
      have h := (Submodule.mem_orthogonal _ u).1 hu (S u) (LinearMap.mem_range_self _ _)
      rw [hSdef, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_right] at h
      exact inner_self_eq_zero.1 h
    rw [← ContinuousLinearMap.adjoint_inner_left, h0, inner_zero_left]
  exact hF.closure_subset_iff.2 (by rintro _ ⟨z, rfl⟩; exact hrange z) hTf

/-- The adjoint of an operator commuting with an inner-product preserving group action
commutes with it. -/
private lemma adjoint_commute {G : Type*} [Group G] (π : G →* Module.End ℂ E)
    (hπ : ∀ g v, ‖π g v‖ = ‖v‖) {T : E →L[ℂ] E} (hT : ∀ g f, T (π g f) = π g (T f))
    (g : G) (f : E) : T.adjoint (π g f) = π g (T.adjoint f) := by
  have hi : ∀ g x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g =>
    (LinearMap.norm_map_iff_inner_map_map (π g)).1 (hπ g)
  have hinv : ∀ v, π g (π g⁻¹ v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  refine ext_inner_left ℂ fun w => ?_
  calc ⟪w, T.adjoint (π g f)⟫_ℂ = ⟪π g (π g⁻¹ (T w)), π g f⟫_ℂ := by
        rw [ContinuousLinearMap.adjoint_inner_right, hinv]
    _ = ⟪π g (π g⁻¹ w), π g (T.adjoint f)⟫_ℂ := by
        rw [hi, hi, ← hT, ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪w, π g (T.adjoint f)⟫_ℂ := by rw [hinv]

end Hilbert

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- The left regular representation `(π g f) x = f (g⁻¹ * x)` on `L²(μ)`. -/
private noncomputable def leftReg : G →* Module.End ℂ (Lp ℂ 2 μ) :=
  (DistribMulAction.toModuleEnd ℂ (Lp ℂ 2 μ)).comp
    { toFun := fun g => DomMulAct.mk g⁻¹
      map_one' := by simp
      map_mul' := fun g h => by simp [DomMulAct.mk_mul] }

/-- `π g` acts through the domain action of `g⁻¹`. -/
private lemma leftReg_apply (g : G) (f : Lp ℂ 2 μ) : leftReg μ g f = DomMulAct.mk g⁻¹ • f := rfl

/-- Left translation is isometric on `L²(μ)`. -/
private lemma norm_leftReg (g : G) (f : Lp ℂ 2 μ) : ‖leftReg μ g f‖ = ‖f‖ :=
  DomMulAct.norm_smul_Lp _ _

variable [CompactSpace G]

/-- The left regular representation is strongly continuous. -/
private lemma continuous_leftReg (f : Lp ℂ 2 μ) : Continuous fun g => leftReg μ g f := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have h1 : Continuous fun g : G => DomMulAct.mk g⁻¹ :=
    DomMulAct.continuous_mk.comp continuous_inv
  exact h1.smul (continuous_const (y := f))

/-- Translating the class of a continuous function translates the function. -/
private lemma leftReg_toLp (g : G) (u : C(G, ℂ)) :
    leftReg μ g (ContinuousMap.toLp 2 μ ℂ u) =
      ContinuousMap.toLp 2 μ ℂ (u.comp ⟨(g⁻¹ * ·), continuous_const.mul continuous_id⟩) := by
  refine Lp.ext ?_
  refine (DomMulAct.smul_Lp_ae_eq _ _).trans ?_
  refine ((measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) μ u)).trans ?_
  exact (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) μ
    (u.comp ⟨(g⁻¹ * ·), continuous_const.mul continuous_id⟩)).symm

/-- A continuous function supported in a set `V` with `V / V ⊆ U`, for a neighbourhood `U` of
`1`, whose square has nonzero integral. -/
private lemma exists_bump {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ V : Set G, (∀ v ∈ V, ∀ w ∈ V, v / w ∈ U) ∧
      ∃ φ : C(G, ℂ), (∀ x, φ x ≠ 0 → x ∈ V) ∧ ∫ y, φ y * φ y ∂μ ≠ 0 := by
  obtain ⟨V, hV, hVU⟩ := exists_nhds_split_inv hU
  obtain ⟨ψ, hψ1, hψ0, -, -⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : G))) isOpen_interior.isClosed_compl
    (Set.disjoint_singleton_left.2 (not_not.2 (mem_interior_iff_mem_nhds.2 hV)))
  let φ : C(G, ℂ) := ⟨fun x => (ψ x : ℂ), Complex.continuous_ofReal.comp ψ.continuous⟩
  refine ⟨V, hVU, φ, fun x hx => ?_, ?_⟩
  · by_contra hxV
    exact hx (by simp [φ, hψ0 (fun h => hxV (interior_subset h))])
  · have hpos : 0 < ∫ y, ψ y * ψ y ∂μ :=
      (ψ.continuous.mul ψ.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
        (HasCompactSupport.of_compactSpace _) (fun y => mul_self_nonneg (ψ y)) (x := 1)
        (by simp [hψ1 rfl])
    have h : ∫ y, φ y * φ y ∂μ = ((∫ y, ψ y * ψ y ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      simp [φ]
    rw [h]
    exact Complex.ofReal_ne_zero.2 hpos.ne'

omit [CompactSpace G] in
/-- The integral operator with kernel `φ (x⁻¹ * y)` commutes with left translation. -/
private lemma kernel_leftReg (φ : C(G, ℂ)) (T₀ : Lp ℂ 2 μ →L[ℂ] C(G, ℂ))
    (hT₀ : ∀ f x, T₀ f x = ∫ y, φ (x⁻¹ * y) * f y ∂μ) (g : G) (f : Lp ℂ 2 μ) :
    T₀ (leftReg μ g f) = (T₀ f).comp ⟨(g⁻¹ * ·), continuous_const.mul continuous_id⟩ := by
  ext x
  rw [hT₀, ContinuousMap.comp_apply, hT₀]
  calc ∫ y, φ (x⁻¹ * y) * leftReg μ g f y ∂μ = ∫ y, φ (x⁻¹ * y) * f (g⁻¹ * y) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [DomMulAct.smul_Lp_ae_eq (DomMulAct.mk g⁻¹) f] with y hy
        rw [leftReg_apply, hy]
        rfl
    _ = ∫ y, φ (x⁻¹ * (g * y)) * f (g⁻¹ * (g * y)) ∂μ :=
        (integral_mul_left_eq_self (fun y => φ (x⁻¹ * y) * f (g⁻¹ * y)) g).symm
    _ = ∫ y, φ ((g⁻¹ * x)⁻¹ * y) * f y ∂μ := by
        simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]

omit [IsTopologicalGroup G] in
/-- The values of the integral operator on the class of `φ` itself. -/
private lemma kernel_toLp_self (φ : C(G, ℂ)) (T₀ : Lp ℂ 2 μ →L[ℂ] C(G, ℂ))
    (hT₀ : ∀ f x, T₀ f x = ∫ y, φ (x⁻¹ * y) * f y ∂μ) (x : G) :
    T₀ (ContinuousMap.toLp 2 μ ℂ φ) x = ∫ y, φ (x⁻¹ * y) * φ y ∂μ := by
  rw [hT₀]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) μ φ] with y hy
  rw [hy]

/-- If `φ` is supported in `V` with `V / V ⊆ U` and `∫ φ ^ 2 ≠ 0`, translation by any `g ∉ U`
moves the image of `φ` under the integral operator with kernel `φ (x⁻¹ * y)`. -/
private lemma leftReg_ne {U V : Set G} (hVU : ∀ v ∈ V, ∀ w ∈ V, v / w ∈ U) (φ : C(G, ℂ))
    (hφV : ∀ x, φ x ≠ 0 → x ∈ V) (hφ : ∫ y, φ y * φ y ∂μ ≠ 0) (T₀ : Lp ℂ 2 μ →L[ℂ] C(G, ℂ))
    (hT₀ : ∀ f x, T₀ f x = ∫ y, φ (x⁻¹ * y) * f y ∂μ) {g : G} (hg : g ∉ U) :
    leftReg μ g (ContinuousMap.toLp 2 μ ℂ (T₀ (ContinuousMap.toLp 2 μ ℂ φ))) ≠
      ContinuousMap.toLp 2 μ ℂ (T₀ (ContinuousMap.toLp 2 μ ℂ φ)) := by
  intro h
  rw [leftReg_toLp] at h
  have h1 := congrArg (fun u : C(G, ℂ) => u g) (ContinuousMap.toLp_injective μ h)
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, inv_mul_cancel] at h1
  rw [kernel_toLp_self μ φ T₀ hT₀, kernel_toLp_self μ φ T₀ hT₀] at h1
  have h0 : ∫ y, φ (g⁻¹ * y) * φ y ∂μ = 0 := by
    refine integral_eq_zero_of_ae (ae_of_all _ fun y => ?_)
    by_contra hne
    have hy := hφV _ (right_ne_zero_of_mul hne)
    have hgy := hφV _ (left_ne_zero_of_mul hne)
    have hgU := hVU y hy _ hgy
    rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_cancel_left] at hgU
    exact hg hgU
  rw [h0, inv_one] at h1
  simp only [one_mul] at h1
  exact hφ h1

end Group

/-- Every neighbourhood of the identity of a compact group contains the kernel of a continuous
finite-dimensional unitary representation. -/
theorem exists_unitaryRep_ker_subset {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ (n : ℕ) (ρ : G →ₜ* Matrix.unitaryGroup (Fin n) ℂ), ∀ g, ρ g = 1 → g ∈ U := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  obtain ⟨V, hVU, φ, hφV, hφ⟩ := exists_bump μ (interior_mem_nhds.2 hU)
  let K : C(G × G, ℂ) := ⟨fun p => φ (p.1⁻¹ * p.2), φ.continuous.comp
    (continuous_fst.inv.mul continuous_snd)⟩
  obtain ⟨T₀, hT₀c, hT₀⟩ :=
    ContinuousKernelCompact.exists_isCompactOperator_kernel (X := G) (p := 2) μ K
  let T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := (ContinuousMap.toLp 2 μ ℂ).comp T₀
  have hT : IsCompactOperator T := hT₀c.clm_comp (ContinuousMap.toLp (E := ℂ) 2 μ ℂ)
  let π := leftReg μ
  have hTπ : ∀ g f, T (π g f) = π g (T f) := fun g f => by
    simp only [T, ContinuousLinearMap.comp_apply, π, kernel_leftReg μ φ T₀ hT₀ g f,
      leftReg_toLp]
  let S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := T ∘L T.adjoint
  have hS : IsCompactOperator S := hT.comp_clm _
  have hSπ : ∀ g, Commute (S : Module.End ℂ (Lp ℂ 2 μ)) (π g) := fun g => by
    refine LinearMap.ext fun f => ?_
    simp only [Module.End.mul_apply, ContinuousLinearMap.coe_coe, S, ContinuousLinearMap.comp_apply,
      adjoint_commute π (norm_leftReg μ) hTπ, hTπ]
  have hπc : ∀ g, Continuous (π g) := fun g => by
    change Continuous fun f : Lp ℂ 2 μ => DomMulAct.mk g⁻¹ • f
    exact continuous_const_smul _
  have hkey : ∀ c : G, ∃ l : ℂ, l ≠ 0 ∧ (c ∉ interior U →
      ∃ v ∈ Module.End.eigenspace (S : Module.End ℂ (Lp ℂ 2 μ)) l, π c v ≠ v) := by
    intro c
    by_cases hc : c ∈ interior U
    · exact ⟨1, one_ne_zero, fun h => (h hc).elim⟩
    · have hnot : ¬ ∀ l : ℂ, l ≠ 0 →
          ∀ v ∈ Module.End.eigenspace (S : Module.End ℂ (Lp ℂ 2 μ)) l, π c v = v := fun hall =>
        leftReg_ne μ hVU φ hφV hφ T₀ hT₀ hc
          (apply_eq_of_forall_eigenspace hT (hπc c) hall (ContinuousMap.toLp 2 μ ℂ φ))
      push Not at hnot
      obtain ⟨l, hl, w, hw, hne⟩ := hnot
      exact ⟨l, hl, fun _ => ⟨w, hw, hne⟩⟩
  choose lam hlam hv using hkey
  choose! v hvE hvne using hv
  obtain ⟨t, htC, ht⟩ := isOpen_interior.isClosed_compl.isCompact.elim_nhds_subcover
    (fun c => {g | π g (v c) ≠ v c}) fun c hc =>
      (isOpen_ne_fun (continuous_leftReg μ (v c)) continuous_const).mem_nhds (hvne c hc)
  let Ev : G → Submodule ℂ (Lp ℂ 2 μ) := fun c =>
    Module.End.eigenspace (S : Module.End ℂ (Lp ℂ 2 μ)) (lam c)
  have hEv : ∀ c, FiniteDimensional ℂ (Ev c) := fun c =>
    ContinuousLinearMap.finite_dimensional_eigenspace hS (lam c) (hlam c)
  let W : Submodule ℂ (Lp ℂ 2 μ) := t.sup Ev
  have hWfin : FiniteDimensional ℂ W := Submodule.finite_finset_sup _ _
  have hW : ∀ g, ∀ w ∈ W, π g w ∈ W := fun g => by
    have hle : W ≤ W.comap (π g) := Finset.sup_le fun c hc x hx =>
      Finset.le_sup (f := Ev) hc (Module.End.mapsTo_genEigenspace_of_comm (hSπ g) (lam c) 1 hx)
    exact fun w hw => hle hw
  obtain ⟨n, ρ, hρ⟩ :=
    exists_unitaryRep_of_invariant π (norm_leftReg μ) (continuous_leftReg μ) W hW
  refine ⟨n, ρ, fun g hg => ?_⟩
  by_contra hgU
  obtain ⟨c, hct, hgc⟩ := Set.mem_iUnion₂.1 (ht fun h => hgU (interior_subset h))
  exact hgc (hρ g hg (v c) (Finset.le_sup (f := Ev) hct (hvE c (htC c hct))))

end D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel
