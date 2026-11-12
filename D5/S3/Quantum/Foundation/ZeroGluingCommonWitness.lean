/- GID: D5/S3/Quantum/Foundation/ZeroGluingCommonWitness
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ZeroGluingCommonWitness
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Full-base zero fibers of original proper confirmations are compact, convex, and exposed under zero gluing. -/

import D5.S3.Quantum.Foundation.WeightedRelationConfirmation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor

noncomputable section
open scoped Topology
open scoped BigOperators
open Set Filter

namespace D5.S3.Quantum.Foundation.ZeroGluingCommonWitness

open D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open D5.S3.Quantum.Foundation.WeightedRelationConfirmation

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

/-- The full normalized zero fiber of the original confirmation relation. -/
def zeroFiber (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) (p : pure C u) : Set A :=
  {x | x ∈ base C u ∧ ∃ f : A →ₗ[ℝ] ℝ, confirms C u p f ∧ f x = 0}

private def properEffects (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) :
    Set (A →L[ℝ] ℝ) :=
  {f | proper C u f.toLinearMap}

private def confirmingEffects (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (p : pure C u) : Set (A →L[ℝ] ℝ) :=
  {f | confirms C u p f.toLinearMap}

private theorem properEffects_compact
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤) :
    IsCompact (properEffects C u) := by
  classical
  obtain ⟨s, hsC, hs_card, hs_span, _⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℝ (C : Set A)
  have htop : (⊤ : Submodule ℝ A) ≤ Submodule.span ℝ (s : Set A) := by
    rw [hs_span, hspan]
  have hs_cardA : s.card = Module.finrank ℝ A := by
    rw [hs_card, hspan, finrank_top]
  let b : Module.Basis {x // x ∈ s} ℝ A :=
    finsetBasisOfTopLeSpanOfCardEqFinrank htop hs_cardA
  obtain ⟨R, hR, hnorm⟩ := b.exists_opNorm_le (F := ℝ)
  let M : ℝ := 1 + ∑ i, ‖u (b i)‖
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hclosed : IsClosed (properEffects C u) := by
    change IsClosed {f : A →L[ℝ] ℝ | ∀ x ∈ C, 0 ≤ f x ∧ f x ≤ u x}
    have heq : {f : A →L[ℝ] ℝ | ∀ x ∈ C, 0 ≤ f x ∧ f x ≤ u x} =
        ⋂ x, ⋂ (_ : x ∈ C), {f : A →L[ℝ] ℝ | 0 ≤ f x ∧ f x ≤ u x} := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [heq]
    exact isClosed_iInter fun x => isClosed_iInter fun _ =>
      (isClosed_le continuous_const (ContinuousLinearMap.apply ℝ ℝ x).continuous).inter
        (isClosed_le (ContinuousLinearMap.apply ℝ ℝ x).continuous continuous_const)
  have hsubset : properEffects C u ⊆ Metric.closedBall (0 : A →L[ℝ] ℝ) (R * M) := by
    intro f hf
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (hnorm (M := M) hM fun i => ?_).trans
      (le_rfl)
    have hiC : (b i : A) ∈ C := by
      simpa [b, finsetBasisOfTopLeSpanOfCardEqFinrank,
        basisOfTopLeSpanOfCardEqFinrank] using hsC i.property
    have hfi := hf (b i) hiC
    have hui : 0 ≤ u (b i) := hfi.1.trans hfi.2
    have hfi0 : 0 ≤ f (b i) := hfi.1
    have hnormi : ‖f (b i)‖ = f (b i) := by
      simpa only [Real.norm_eq_abs] using (abs_of_nonneg hfi0)
    rw [hnormi]
    calc
      f (b i) ≤ u (b i) := hfi.2
      _ = ‖u (b i)‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hui]
      _ ≤ ∑ j, ‖u (b j)‖ := by
        exact Finset.single_le_sum (s := Finset.univ)
          (fun j _ => norm_nonneg (u (b j))) (Finset.mem_univ i)
      _ ≤ M := by
        dsimp [M]
        linarith
  exact (Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed,
    (Metric.isBounded_closedBall : Bornology.IsBounded
      (Metric.closedBall (0 : A →L[ℝ] ℝ) (R * M))).subset hsubset⟩)

private theorem confirmingEffects_compact
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (p : pure C u) (hspan : Submodule.span ℝ (C : Set A) = ⊤) :
    IsCompact (confirmingEffects C u p) := by
  have hclosed : IsClosed (confirmingEffects C u p) := by
    have heq : confirmingEffects C u p = properEffects C u ∩ {f | f p = 1} := by
      ext f
      rfl
    rw [heq]
    exact (properEffects_compact C u hspan).isClosed.inter
      (isClosed_eq (by fun_prop) continuous_const)
  exact (properEffects_compact C u hspan).of_isClosed_subset hclosed (by
    intro f hf
    exact hf.1)

private theorem zeroFiber_compact
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (p : pure C u) (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤) :
    IsCompact (zeroFiber C u p) := by
  let R : Set ((A →L[ℝ] ℝ) × A) :=
    {z | z.1 ∈ confirmingEffects C u p ∧ z.2 ∈ base C u ∧ z.1 z.2 = 0}
  have hclosedR : IsClosed R := by
    have hF : IsClosed {z : (A →L[ℝ] ℝ) × A | z.1 ∈ confirmingEffects C u p} :=
      (confirmingEffects_compact C u p hspan).isClosed.preimage continuous_fst
    have hK : IsClosed {z : (A →L[ℝ] ℝ) × A | z.2 ∈ base C u} :=
      (base_compact hclosed hstrict).isClosed.preimage continuous_snd
    have hev : Continuous (fun z : (A →L[ℝ] ℝ) × A => z.1 z.2) := by
      letI : IsModuleTopology ℝ A := isModuleTopologyOfFiniteDimensional
      letI : IsModuleTopology ℝ (A →L[ℝ] ℝ) := isModuleTopologyOfFiniteDimensional
      let bil : (A →L[ℝ] ℝ) →ₗ[ℝ] A →ₗ[ℝ] ℝ :=
        { toFun := fun f => f.toLinearMap
          map_add' := by intro f g; ext x; simp
          map_smul' := by intro c f; ext x; simp }
      have h := IsModuleTopology.continuous_bilinear_of_finite_left bil
      simpa [bil] using h
    have hzero : IsClosed {z : (A →L[ℝ] ℝ) × A | z.1 z.2 = 0} :=
      isClosed_eq hev continuous_const
    have heq : R =
        {z : (A →L[ℝ] ℝ) × A | z.1 ∈ confirmingEffects C u p} ∩
        {z | z.2 ∈ base C u} ∩ {z | z.1 z.2 = 0} := by
      ext z
      simp [R, and_assoc]
    rw [heq]
    exact (hF.inter hK).inter hzero
  have hcompactProd : IsCompact (confirmingEffects C u p ×ˢ base C u) :=
    (confirmingEffects_compact C u p hspan).prod (base_compact hclosed hstrict)
  have hcompactR : IsCompact R :=
    hcompactProd.of_isClosed_subset hclosedR (by intro z hz; exact ⟨hz.1, hz.2.1⟩)
  have himage : (Prod.snd '' R) = zeroFiber C u p := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz.2.1, z.1.toLinearMap, hz.1, hz.2.2⟩
    · rintro ⟨hx, f, hf, hfx⟩
      refine ⟨(f.toContinuousLinearMap, x), ?_, rfl⟩
      exact ⟨by simpa [confirmingEffects] using hf, hx, hfx⟩
  rw [← himage]
  exact hcompactR.image continuous_snd

private theorem dyadic_mem_of_midpoint_mem {s : Set A}
    (hmid : ∀ ⦃x y : A⦄, x ∈ s → y ∈ s →
      (1 / 2 : ℝ) • (x + y) ∈ s)
    {x y : A} (hx : x ∈ s) (hy : y ∈ s) :
    ∀ (n k : ℕ), k ≤ 2 ^ n →
      ((1 - (k : ℝ) / (2 ^ n : ℝ)) • x +
        ((k : ℝ) / (2 ^ n : ℝ)) • y) ∈ s := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have hk0 : k = 0 ∨ k = 1 := by omega
      rcases hk0 with rfl | rfl <;> norm_num
      · simpa using hx
      · simpa using hy
  | succ n ih =>
      intro k hk
      have hp : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by
        rw [pow_succ]
        omega
      obtain ⟨j, rfl⟩ | ⟨j, hjk⟩ := Nat.even_or_odd k
      · have hj : j ≤ 2 ^ n := by omega
        have hh := ih j hj
        convert hh using 1 <;> norm_num [pow_succ] <;> module
      · have hj : j + 1 ≤ 2 ^ n := by omega
        have hleft := ih j (by omega)
        have hright := ih (j + 1) hj
        have hm := hmid hleft hright
        rw [hjk]
        convert hm using 1 <;> norm_num [pow_succ] <;> module

private theorem convex_of_closed_midpoint_mem {s : Set A}
    (hclosed : IsClosed s)
    (hmid : ∀ ⦃x y : A⦄, x ∈ s → y ∈ s →
      (1 / 2 : ℝ) • (x + y) ∈ s) :
    Convex ℝ s := by
  intro x hx y hy a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  let d : ℕ → A := fun n =>
    (1 - ((Nat.floor (b * (2 ^ n : ℝ)) : ℝ) / (2 ^ n : ℝ))) • x +
      ((Nat.floor (b * (2 ^ n : ℝ)) : ℝ) / (2 ^ n : ℝ)) • y
  have hd : ∀ n, d n ∈ s := by
    intro n
    apply dyadic_mem_of_midpoint_mem hmid hx hy n
      (Nat.floor (b * (2 ^ n : ℝ)))
    have hfloor : (Nat.floor (b * (2 ^ n : ℝ)) : ℝ) ≤ (2 ^ n : ℝ) := by
      calc
        (Nat.floor (b * (2 ^ n : ℝ)) : ℝ) ≤ b * (2 ^ n : ℝ) :=
          Nat.floor_le (mul_nonneg hb (by positivity))
        _ ≤ (2 ^ n : ℝ) := by
          have hpow0 : 0 ≤ (2 ^ n : ℝ) := by positivity
          nlinarith [mul_nonneg (sub_nonneg.mpr hb1) hpow0]
    exact_mod_cast hfloor
  have hpow : Tendsto (fun n : ℕ => (2 ^ n : ℝ)) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlim : Tendsto (fun n : ℕ =>
      ((Nat.floor (b * (2 ^ n : ℝ)) : ℝ) / (2 ^ n : ℝ))) atTop (𝓝 b) := by
    convert (tendsto_nat_floor_mul_div_atTop (R := ℝ) hb).comp hpow using 1
    rfl
  have hdl : Tendsto d atTop (𝓝 (a • x + b • y)) := by
    have hleft : Tendsto (fun n =>
        (1 - ((Nat.floor (b * (2 ^ n : ℝ)) : ℝ) / (2 ^ n : ℝ))) • x)
        atTop (𝓝 ((1 - b) • x)) := by
      convert (tendsto_const_nhds.sub hlim).smul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)) using 1
    have hright : Tendsto (fun n =>
        ((Nat.floor (b * (2 ^ n : ℝ)) : ℝ) / (2 ^ n : ℝ)) • y)
        atTop (𝓝 (b • y)) :=
      hlim.smul (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y))
    have hadd := Tendsto.add hleft hright
    convert hadd using 1
    rw [show a = 1 - b by linarith]
  exact hclosed.mem_of_tendsto hdl (Filter.Eventually.of_forall hd)

private theorem common_zero_of_intrinsicInterior
    {s t : Set A} (hsub : s ⊆ t) {f : A →ₗ[ℝ] ℝ}
    (hf_nonneg : ∀ z ∈ t, 0 ≤ f z)
    {x₀ : A} (hx₀ : x₀ ∈ intrinsicInterior ℝ s) (hfx₀ : f x₀ = 0) :
    ∀ {x}, x ∈ s → f x = 0 := by
  obtain ⟨x₀', hx₀', rfl⟩ := mem_intrinsicInterior.mp hx₀
  have hnhds : ((↑) ⁻¹' s : Set (affineSpan ℝ s)) ∈ 𝓝 x₀' :=
    mem_interior_iff_mem_nhds.mp hx₀'
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  intro x hx
  by_cases hxx : (x : A) = (x₀' : A)
  · simpa [hxx] using hfx₀
  let ε : ℝ := r / (dist (x₀' : A) x + 1)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  let z : A := AffineMap.lineMap x (x₀' : A) (1 + ε)
  have hzspan : z ∈ affineSpan ℝ s := by
    exact AffineMap.lineMap_mem (1 + ε) (mem_affineSpan ℝ hx) x₀'.property
  let z' : affineSpan ℝ s := ⟨z, hzspan⟩
  have hzball : z' ∈ Metric.ball x₀' r := by
    rw [Metric.mem_ball]
    change dist z (x₀' : A) < r
    dsimp [z]
    rw [dist_lineMap_right]
    rw [show (1 : ℝ) - (1 + ε) = -ε by ring, norm_neg,
      Real.norm_eq_abs, abs_of_pos hε]
    dsimp [ε]
    have hd : 0 ≤ dist (x₀' : A) x := dist_nonneg
    have hden : 0 < dist (x₀' : A) x + 1 := by linarith
    have hmul : ε * dist (x₀' : A) x < ε * (dist (x₀' : A) x + 1) :=
      mul_lt_mul_of_pos_left (by linarith) hε
    have heq : ε * (dist (x₀' : A) x + 1) = r := by
      dsimp [ε]
      field_simp
    simpa [ε, dist_comm] using hmul.trans_eq heq
  have hzS : z ∈ s := hball hzball
  have hzT : z ∈ t := hsub hzS
  have hfx : 0 ≤ f x := hf_nonneg x (hsub hx)
  have hfz : 0 ≤ f z := hf_nonneg z hzT
  have hrel : f z = -ε * f x := by
    dsimp [z]
    rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul, hfx₀]
    ring
  have hprod : ε * f x ≤ 0 := by
    calc
      ε * f x = -f z := by rw [hrel]; ring
      _ ≤ 0 := neg_nonpos.mpr hfz
  have hprod' : ε * f x = 0 := le_antisymm hprod (mul_nonneg hε.le hfx)
  exact (mul_eq_zero.mp hprod').resolve_left hε.ne'

theorem zeroFiber_compact_convex_common_witness
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (hZ : zeroGluing C u) :
    ∀ p : pure C u,
      IsCompact (zeroFiber C u p) ∧ Convex ℝ (zeroFiber C u p) ∧
        ((zeroFiber C u p).Nonempty →
          ∃ f : A →ₗ[ℝ] ℝ,
            confirms C u p f ∧
              {x | x ∈ base C u ∧ f x = 0} = zeroFiber C u p) := by
  intro p
  have hcompact : IsCompact (zeroFiber C u p) :=
    zeroFiber_compact C u p hclosed hstrict hspan
  have hmid : ∀ ⦃x y : A⦄, x ∈ zeroFiber C u p → y ∈ zeroFiber C u p →
      (1 / 2 : ℝ) • (x + y) ∈ zeroFiber C u p := by
    intro x y hx hy
    obtain ⟨fx, hfx, hfx0⟩ := hx.2
    obtain ⟨fy, hfy, hfy0⟩ := hy.2
    obtain ⟨f, hf, hfmid⟩ := hZ p x y hx.1 hy.1 ⟨fx, hfx, hfx0⟩ ⟨fy, hfy, hfy0⟩
    refine ⟨?_, f, hf, hfmid⟩
    have hbase := base_convex C u hx.1 hy.1
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    simpa [smul_add] using hbase
  have hconvex : Convex ℝ (zeroFiber C u p) :=
    convex_of_closed_midpoint_mem hcompact.isClosed hmid
  refine ⟨hcompact, hconvex, ?_⟩
  intro hne
  obtain ⟨x₀, hx₀⟩ := Set.Nonempty.intrinsicInterior hconvex hne
  have hx₀S : x₀ ∈ zeroFiber C u p := intrinsicInterior_subset hx₀
  obtain ⟨hx₀base, f, hf, hfx₀⟩ := hx₀S
  have hzero : ∀ {x}, x ∈ zeroFiber C u p → f x = 0 :=
    common_zero_of_intrinsicInterior (s := zeroFiber C u p) (t := base C u)
      (fun x hx => hx.1) (fun x hx => (hf.1 x hx.1).1) hx₀ hfx₀
  refine ⟨f, hf, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hfx⟩
    exact ⟨hx, f, hf, hfx⟩
  · rintro ⟨hx, g, hg, hgx⟩
    exact ⟨hx, hzero ⟨hx, g, hg, hgx⟩⟩

end D5.S3.Quantum.Foundation.ZeroGluingCommonWitness
