/- GID: D5/S3/Quantum/Foundation/RealRogFailureQuantitative
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/RealRogFailureQuantitative
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: A rank-one cross pair gives a quantitative gap on the entire PSD section. -/

import D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Matrix.Normed
import D5.S3.Quantum.Dynamics.BaseNormContraction

/-!
The quantitative step of Quantum Origin VI (93.24) is an estimate on the
actual PSD section. Its consumer uses every proper linear effect on the
section's own carrier. The cross pair and trace normalization are inputs to
this predecessor; their extraction from the original arbitrary-unit ROG
model, determinant normalization and optimal base-norm duality are not proved
here. The original-carrier primal part of the optimization bridge is proved
separately, retaining the original arbitrary unit and compact base. No
completion of Proposition 93.3 or block classification is asserted.
-/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise

namespace D5.S3.Quantum.Foundation.RealRogFailureQuantitative

variable {ι : Type*} [Fintype ι]

private theorem dot_cauchy (v w : ι → ℝ) :
    (v ⬝ᵥ w) ^ 2 ≤ (v ⬝ᵥ v) * (w ⬝ᵥ w) := by
  simpa only [dotProduct, pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w

private theorem dot_self_nonneg (z : ι → ℝ) : 0 ≤ z ⬝ᵥ z := by
  simpa only [star_trivial] using dotProduct_star_self_nonneg z

private theorem residual_identities (v w z : ι → ℝ)
    (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1) :
    let a := v ⬝ᵥ w
    let b := w - a • v
    let h := z - (v ⬝ᵥ z) • v
    b ⬝ᵥ b = 1 - a ^ 2 ∧
    h ⬝ᵥ h = z ⬝ᵥ z - (v ⬝ᵥ z) ^ 2 ∧
    b ⬝ᵥ h = w ⬝ᵥ z - a * (v ⬝ᵥ z) := by
  dsimp
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hv, hw, dotProduct_comm w v, dotProduct_comm z v]
  constructor
  · ring
  constructor <;> ring

private theorem quadratic_bound (v w z : ι → ℝ) (d : ℝ)
    (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1) (hd : 1 < d) :
    (v ⬝ᵥ w) ^ 2 * (v ⬝ᵥ z) ^ 2 ≤
      d * ((w ⬝ᵥ z) ^ 2 + (z ⬝ᵥ z - (v ⬝ᵥ z) ^ 2) / (d - 1)) := by
  let a := v ⬝ᵥ w
  let α := v ⬝ᵥ z
  let r := w ⬝ᵥ z
  let b := w - a • v
  let h := z - α • v
  let H := z ⬝ᵥ z - α ^ 2
  obtain ⟨hb, hh, hbh⟩ := residual_identities v w z hv hw
  change b ⬝ᵥ b = 1 - a ^ 2 at hb
  change h ⬝ᵥ h = H at hh
  change b ⬝ᵥ h = r - a * α at hbh
  have hH : 0 ≤ H := hh ▸ dot_self_nonneg h
  have hcs := dot_cauchy b h
  rw [hb, hh, hbh] at hcs
  have hres : (r - a * α) ^ 2 ≤ H := by
    nlinarith [mul_nonneg (sq_nonneg a) hH]
  have hweighted : (d - 1) * (a ^ 2 * α ^ 2) ≤
      d * ((d - 1) * r ^ 2 + H) := by
    nlinarith [sq_nonneg ((d - 1) * r + (r - a * α)),
      mul_nonneg (show 0 ≤ d by linarith) (sub_nonneg.mpr hres)]
  have hden : 0 < d - 1 := sub_pos.mpr hd
  apply (le_of_mul_le_mul_left (a := d - 1) (b := a ^ 2 * α ^ 2)
    (c := d * (r ^ 2 + H / (d - 1))) ?_ hden)
  calc
    (d - 1) * (a ^ 2 * α ^ 2) ≤ d * ((d - 1) * r ^ 2 + H) := hweighted
    _ = (d - 1) * (d * (r ^ 2 + H / (d - 1))) := by
      field_simp

omit [Fintype ι] in
private theorem rank_one_hermitian (v : ι → ℝ) :
    (vecMulVec v v).IsHermitian := by
  rw [isHermitian_iff_isSymm]
  ext i j
  simp [vecMulVec, mul_comm]

omit [Fintype ι] in
private theorem rank_one_psd [Finite ι] (v : ι → ℝ) : (vecMulVec v v).PosSemidef := by
  simpa only [star_trivial] using posSemidef_vecMulVec_self_star v

private theorem quadratic_rank_one (v z : ι → ℝ) :
    z ⬝ᵥ ((vecMulVec v v) *ᵥ z) = (v ⬝ᵥ z) ^ 2 := by
  rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul,
    dotProduct_comm z v]
  ring

/-- The actual quadratic-form estimate gives a PSD cone difference with the
source constant, uniformly in the dimension and both unit directions. -/
theorem midpoint_psd_gap [DecidableEq ι] (v w : ι → ℝ)
    (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1)
    (hd : 2 ≤ Fintype.card ι) :
    ((1 / 2 : ℝ) • (vecMulVec w w +
        ((Fintype.card ι : ℝ) - 1)⁻¹ • (1 - vecMulVec v v)) -
      ((v ⬝ᵥ w) ^ 2 / (2 * (Fintype.card ι : ℝ))) • vecMulVec v v).PosSemidef := by
  have hd' : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (((rank_one_hermitian w).add
      ((isHermitian_one.sub (rank_one_hermitian v)).smul (IsSelfAdjoint.all _))).smul
      (IsSelfAdjoint.all _)).sub ((rank_one_hermitian v).smul (IsSelfAdjoint.all _))
  intro z
  have hb := quadratic_bound v w z (Fintype.card ι : ℝ) hv hw (by linarith)
  simp only [star_trivial, sub_mulVec, smul_mulVec, add_mulVec, one_mulVec,
    dotProduct_sub, dotProduct_smul, dotProduct_add, smul_eq_mul, quadratic_rank_one]
  apply sub_nonneg.mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < 2 * (Fintype.card ι : ℝ) by positivity)).mpr
  simp only [div_eq_mul_inv] at hb
  nlinarith [hb]

private theorem complement_psd [DecidableEq ι] (v : ι → ℝ)
    (hv : v ⬝ᵥ v = 1) : (1 - vecMulVec v v).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
    (isHermitian_one.sub (rank_one_hermitian v))
  intro z
  simp only [star_trivial, sub_mulVec, one_mulVec, dotProduct_sub, quadratic_rank_one]
  have h := dot_cauchy v z
  rw [hv, one_mul] at h
  exact sub_nonneg.mpr h

private def projection_effect (L : Submodule ℝ (Matrix ι ι ℝ)) (v : ι → ℝ) :
    L →ₗ[ℝ] ℝ where
  toFun A := v ⬝ᵥ ((A : Matrix ι ι ℝ) *ᵥ v)
  map_add' A B := by simp [add_mulVec, dotProduct_add]
  map_smul' a A := by simp [smul_mulVec, dotProduct_smul]

private theorem trace_rank_pair (v : ι → ℝ) (A : Matrix ι ι ℝ) :
    (vecMulVec v v * A).trace = v ⬝ᵥ (A *ᵥ v) := by
  rw [trace_mul_comm, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

open CircuitBalancedConfirmation

private theorem projection_proper
    (L : Submodule ℝ (Matrix ι ι ℝ)) (C : PointedCone ℝ L) (u : L →ₗ[ℝ] ℝ)
    (hC : ∀ A : L, A ∈ C ↔ (A : Matrix ι ι ℝ).PosSemidef)
    (hu : ∀ A : L, u A = (A : Matrix ι ι ℝ).trace)
    (v : ι → ℝ) (hv : v ⬝ᵥ v = 1) : proper C u (projection_effect L v) := by
  classical
  intro A hA
  have hpos := (hC A).mp hA
  refine ⟨?_, ?_⟩
  · exact hpos.dotProduct_mulVec_nonneg v
  · have ht := RHLinalg.trace_mul_nonneg_of_posSemidef (complement_psd v hv) hpos
    rw [sub_mul, one_mul, trace_sub, trace_rank_pair] at ht
    change 0 ≤ (A : Matrix ι ι ℝ).trace - v ⬝ᵥ ((A : Matrix ι ι ℝ) *ᵥ v) at ht
    rw [hu A]
    exact sub_nonneg.mp ht

private theorem comparison_zero
    (L : Submodule ℝ (Matrix ι ι ℝ)) (C : PointedCone ℝ L) (u : L →ₗ[ℝ] ℝ)
    (s z : L) (hz : z ∈ C) (f : L →ₗ[ℝ] ℝ)
    (hf : confirms C u s f) (hfz : f z = 0) : comparison C u s z = 0 := by
  change sInf {r | ∃ g : L →ₗ[ℝ] ℝ, confirms C u s g ∧ g z = r} = 0
  have hne : ({r | ∃ g : L →ₗ[ℝ] ℝ, confirms C u s g ∧ g z = r} : Set ℝ).Nonempty :=
    ⟨f z, f, hf, rfl⟩
  have hlow : ∀ r ∈ ({r | ∃ g : L →ₗ[ℝ] ℝ, confirms C u s g ∧ g z = r} : Set ℝ),
      0 ≤ r := by
    rintro r ⟨g, hg, rfl⟩
    exact (hg.1 z hz).1
  exact le_antisymm (csInf_le ⟨0, hlow⟩ ⟨f, hf, hfz⟩) (le_csInf hne hlow)

/-- Once a normalized cross pair has actually been supplied, the complement
and its midpoint are states of the same section. The two zero comparisons may
use different effects. Every confirmer on the section's whole carrier obeys
the quantitative positive lower bound. -/
theorem normalized_cross_pair_gap [DecidableEq ι]
    (L : Submodule ℝ (Matrix ι ι ℝ)) (C : PointedCone ℝ L) (u : L →ₗ[ℝ] ℝ)
    (hC : ∀ A : L, A ∈ C ↔ (A : Matrix ι ι ℝ).PosSemidef)
    (hu : ∀ A : L, u A = (A : Matrix ι ι ℝ).trace)
    (j s x : L) (hj : (j : Matrix ι ι ℝ) = 1)
    (v w : ι → ℝ) (hs : (s : Matrix ι ι ℝ) = vecMulVec v v)
    (hx : (x : Matrix ι ι ℝ) = vecMulVec w w)
    (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1) (hd : 2 ≤ Fintype.card ι)
    (hc : 0 < (v ⬝ᵥ w) ^ 2)
    (f : L →ₗ[ℝ] ℝ) (hf : confirms C u s f) (hfx : f x = 0) :
    let c := (v ⬝ᵥ w) ^ 2
    let y := ((Fintype.card ι : ℝ) - 1)⁻¹ • (j - s)
    let m := (1 / 2 : ℝ) • (x + y)
    let δ := c / (2 * (Fintype.card ι : ℝ))
    c < 1 ∧ s ∈ base C u ∧ x ∈ base C u ∧ y ∈ base C u ∧ m ∈ base C u ∧
      comparison C u s x = 0 ∧ comparison C u s y = 0 ∧
      (m : Matrix ι ι ℝ).PosDef ∧ m - δ • s ∈ C ∧
      (∀ g : L →ₗ[ℝ] ℝ, confirms C u s g → δ ≤ g m) ∧
      δ ≤ comparison C u s m ∧ 0 < δ := by
  dsimp only
  let d : ℝ := Fintype.card ι
  let c := (v ⬝ᵥ w) ^ 2
  let y := (d - 1)⁻¹ • (j - s)
  let m := (1 / 2 : ℝ) • (x + y)
  let δ := c / (2 * d)
  have hd' : (2 : ℝ) ≤ d := by dsimp [d]; exact_mod_cast hd
  have hd1 : 0 < d - 1 := by linarith
  have hδ : 0 < δ := div_pos hc (by positivity)
  have hsu : u s = 1 := by rw [hu, hs, trace_vecMulVec, hv]
  have hxu : u x = 1 := by rw [hu, hx, trace_vecMulVec, hw]
  have hju : u j = d := by rw [hu, hj, trace_one]
  have hsC : s ∈ C := (hC s).mpr (hs ▸ rank_one_psd v)
  have hxC : x ∈ C := (hC x).mpr (hx ▸ rank_one_psd w)
  have hyC : y ∈ C := by
    apply (hC y).mpr
    change ((d - 1)⁻¹ • ((j : Matrix ι ι ℝ) - (s : Matrix ι ι ℝ))).PosSemidef
    rw [hj, hs]
    exact (complement_psd v hv).smul (inv_nonneg.mpr hd1.le)
  have hyu : u y = 1 := by
    simp only [y, map_smul, map_sub, smul_eq_mul, hju, hsu]
    exact inv_mul_cancel₀ hd1.ne'
  have hmC : m ∈ C := C.smul_mem (by norm_num) (C.add_mem hxC hyC)
  have hmu : u m = 1 := by norm_num [m, hxu, hyu]
  have hgapPSD : ((m - δ • s : L) : Matrix ι ι ℝ).PosSemidef := by
    simpa [m, y, δ, c, d, hs, hx, hj] using midpoint_psd_gap v w hv hw hd
  have hgap : m - δ • s ∈ C := (hC _).mpr hgapPSD
  have hall (g : L →ₗ[ℝ] ℝ) (hg : confirms C u s g) : δ ≤ g m := by
    have h := (hg.1 _ hgap).1
    simp only [map_sub, map_smul, smul_eq_mul, hg.2, mul_one] at h
    exact sub_nonneg.mp h
  have hlower : δ ≤ comparison C u s m := by
    apply le_csInf (s := {r | ∃ g : L →ₗ[ℝ] ℝ, confirms C u s g ∧ g m = r})
      ⟨f m, f, hf, rfl⟩
    rintro r ⟨g, hg, rfl⟩
    exact hall g hg
  have hproj : confirms C u s (projection_effect L v) := by
    refine ⟨projection_proper L C u hC hu v hv, ?_⟩
    change v ⬝ᵥ ((s : Matrix ι ι ℝ) *ᵥ v) = 1
    rw [hs, quadratic_rank_one, hv]
    norm_num
  have hprojy : projection_effect L v y = 0 := by
    change v ⬝ᵥ (((d - 1)⁻¹ • ((j : Matrix ι ι ℝ) - (s : Matrix ι ι ℝ))) *ᵥ v) = 0
    simp [hj, hs, smul_mulVec, sub_mulVec, dotProduct_smul, dotProduct_sub,
      quadratic_rank_one, hv]
  have hc1 : c < 1 := by
    have hle : c ≤ 1 := by simpa [c, hv, hw] using dot_cauchy v w
    by_contra hn
    have heq : c = 1 := le_antisymm hle (le_of_not_gt hn)
    obtain ⟨hb, _, _⟩ := residual_identities v w v hv hw
    have hb0 : w - (v ⬝ᵥ w) • v = 0 := by
      apply dotProduct_self_eq_zero.mp
      simpa [c, heq] using hb
    have hxs : x = s := by
      apply Subtype.ext
      rw [hx, hs, sub_eq_zero.mp hb0]
      ext i k
      change ((v ⬝ᵥ w) * v i) * ((v ⬝ᵥ w) * v k) = v i * v k
      calc
        _ = c * (v i * v k) := by dsimp [c]; ring
        _ = v i * v k := by rw [heq, one_mul]
    have hbad := congrArg f hxs
    rw [hfx, hf.2] at hbad
    norm_num at hbad
  have hmPD : (m : Matrix ι ι ℝ).PosDef := by
    apply PosDef.of_dotProduct_mulVec_pos ((hC m).mp hmC).isHermitian
    intro z hz
    have hself : 0 < z ⬝ᵥ z := lt_of_le_of_ne (dot_self_nonneg z)
      (Ne.symm (dotProduct_self_eq_zero.not.mpr hz))
    have hdiff := hgapPSD.dotProduct_mulVec_nonneg z
    simp only [star_trivial, Submodule.coe_sub, Submodule.coe_smul, sub_mulVec,
      smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, hs,
      quadratic_rank_one] at hdiff
    have heval : z ⬝ᵥ ((m : Matrix ι ι ℝ) *ᵥ z) =
        (1 / 2 : ℝ) * ((w ⬝ᵥ z) ^ 2 + (d - 1)⁻¹ *
          (z ⬝ᵥ z - (v ⬝ᵥ z) ^ 2)) := by
      simp [m, y, hj, hs, hx, smul_mulVec, add_mulVec, sub_mulVec,
        dotProduct_smul, dotProduct_add, dotProduct_sub, quadratic_rank_one]
      ring
    simp only [star_trivial]
    by_contra hn
    have hle := le_of_not_gt hn
    have hvz : (v ⬝ᵥ z) ^ 2 = 0 := by nlinarith [sq_nonneg (v ⬝ᵥ z)]
    rw [hvz, sub_zero] at heval
    have hpos := mul_pos (inv_pos.mpr hd1) hself
    nlinarith [sq_nonneg (w ⬝ᵥ z)]
  exact ⟨hc1, ⟨hsC, hsu⟩, ⟨hxC, hxu⟩, ⟨hyC, hyu⟩, ⟨hmC, hmu⟩,
    comparison_zero L C u s x hxC f hf hfx,
    comparison_zero L C u s y hyC _ hproj hprojy,
    hmPD, hgap, hall, hlower, hδ⟩

section OriginalPrimal

open scoped Pointwise
open D5.S3.Quantum.Dynamics.BaseNormContraction

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

omit [FiniteDimensional ℝ A] in
private theorem mass_cap_compact (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hK : IsCompact (base C u))
    (hu : ∀ a ∈ C, a ≠ 0 → 0 < u a) (R : ℝ) (hR : 0 ≤ R) :
    IsCompact {a : A | a ∈ C ∧ u a ≤ R} := by
  have heq : {a : A | a ∈ C ∧ u a ≤ R} =
      (Set.Icc 0 R : Set ℝ) • insert 0 (base C u) := by
    ext a
    constructor
    · rintro ⟨ha, hmass⟩
      by_cases ha0 : a = 0
      · subst a
        exact ⟨0, ⟨le_rfl, hR⟩, 0, Set.mem_insert _ _, zero_smul _ _⟩
      have hpos := hu a ha ha0
      refine ⟨u a, ⟨hpos.le, hmass⟩, (u a)⁻¹ • a, Set.mem_insert_of_mem _ ?_, ?_⟩
      · exact ⟨C.smul_mem (inv_nonneg.mpr hpos.le) ha, by simp [hpos.ne']⟩
      · simp [smul_smul, hpos.ne']
    · rintro ⟨r, hr, k, hk, rfl⟩
      rcases hk with rfl | hk
      · simpa using And.intro C.zero_mem hR
      · exact ⟨C.smul_mem hr.1 hk.1, by simpa [hk.2] using hr.2⟩
  rw [heq]
  exact isCompact_Icc.smul_set (hK.insert 0)

/-- The infimum defining the original cone base norm is attained on that same
cone and with that same arbitrary strictly positive unit. This is the primal
part of (93.23); no dual effect or failed-pair extraction is assumed or supplied. -/
theorem original_primal_attainment (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hK : IsCompact (base C u))
    (hu : ∀ a ∈ C, a ≠ 0 → 0 < u a)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤) (z : A) :
    ∃ X Y : A, X ∈ C ∧ Y ∈ C ∧ z = X - Y ∧
      u X + u Y = baseNorm C.toConvexCone u z ∧
      (∀ a b : A, a ∈ C → b ∈ C → z = a - b → u X + u Y ≤ u a + u b) ∧
      u X = (baseNorm C.toConvexCone u z + u z) / 2 ∧
      u Y = (baseNorm C.toConvexCone u z - u z) / 2 := by
  have hnonneg (a : A) (ha : a ∈ C) : 0 ≤ u a := by
    by_cases h : a = 0
    · simp [h]
    · exact (hu a ha h).le
  obtain ⟨a₀, ha₀, b₀, hb₀, hz₀⟩ :=
    C.mem_span.mp (show z ∈ Submodule.span ℝ (C : Set A) by rw [hspan]; trivial)
  let R := u a₀ + u b₀
  have hR : 0 ≤ R := add_nonneg (hnonneg _ ha₀) (hnonneg _ hb₀)
  let cap : Set A := {a | a ∈ C ∧ u a ≤ R}
  let feasible : Set (A × A) := (cap ×ˢ cap) ∩ {ab | z = ab.1 - ab.2}
  have hcap : IsCompact cap := mass_cap_compact C u hK hu R hR
  have hfeasible : IsCompact feasible := (hcap.prod hcap).inter_right
    (isClosed_eq continuous_const (continuous_fst.sub continuous_snd))
  have hseed : (a₀, b₀) ∈ feasible := by
    refine ⟨⟨⟨ha₀, ?_⟩, ⟨hb₀, ?_⟩⟩, hz₀⟩ <;>
      dsimp [R] <;> linarith [hnonneg _ ha₀, hnonneg _ hb₀]
  have hcost : Continuous (fun ab : A × A => u ab.1 + u ab.2) :=
    (u.continuous_of_finiteDimensional.comp continuous_fst).add
      (u.continuous_of_finiteDimensional.comp continuous_snd)
  obtain ⟨XY, hXY, hmin⟩ := hfeasible.exists_isMinOn ⟨(a₀, b₀), hseed⟩ hcost.continuousOn
  have hbound : u XY.1 + u XY.2 ≤ R := hmin hseed
  have hglobal (a b : A) (ha : a ∈ C) (hb : b ∈ C) (hz : z = a - b) :
      u XY.1 + u XY.2 ≤ u a + u b := by
    by_cases hcostR : u a + u b ≤ R
    · apply hmin (a := (a, b))
      exact ⟨⟨⟨ha, (le_add_of_nonneg_right (hnonneg _ hb)).trans hcostR⟩,
        ⟨hb, (le_add_of_nonneg_left (hnonneg _ ha)).trans hcostR⟩⟩, hz⟩
    · exact hbound.trans (le_of_not_ge hcostR)
  have hinf : u XY.1 + u XY.2 = baseNorm C.toConvexCone u z := by
    apply Eq.symm
    apply IsLeast.csInf_eq
    refine ⟨⟨XY.1, XY.2, hXY.1.1.1, hXY.1.2.1, hXY.2, rfl⟩, ?_⟩
    rintro r ⟨a, b, ha, hb, hz, rfl⟩
    exact hglobal a b ha hb hz
  have hunit : u z = u XY.1 - u XY.2 := by rw [hXY.2, map_sub]
  refine ⟨XY.1, XY.2, hXY.1.1.1, hXY.1.2.1, hXY.2, hinf, hglobal, ?_, ?_⟩ <;>
    linarith

end OriginalPrimal

end D5.S3.Quantum.Foundation.RealRogFailureQuantitative
