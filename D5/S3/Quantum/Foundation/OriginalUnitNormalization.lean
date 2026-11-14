/- GID: D5/S3/Quantum/Foundation/OriginalUnitNormalization
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalUnitNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual original-unit principal congruence transports the entire original geometry. -/

import D5.S3.Quantum.Foundation.OriginalUnitSupport
import D5.S3.Quantum.Foundation.SectionROGFrame
import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import Mathlib.Data.Sym.Card
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dual.Defs

/-!
The same native determinant maximizer and principal inverse square root give a
trace-preserving map on every original vector. Its entire original geometry,
proper effect interval and native ambient coefficient spaces are transported.
-/

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder Pointwise
open Filter Topology
open D5.S3.Quantum.Foundation.OriginalUnitSupport

namespace D5.S3.Quantum.Foundation.OriginalUnitNormalization

variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  [AddCommGroup V] [Module ℝ V]

omit [DecidableEq ι] in
private theorem psd_rank_one_outer (A : HermitianMat ι 𝕜)
    (hA : 0 ≤ A) (hr : A.mat.rank = 1) :
    ∃ v : EuclideanSpace 𝕜 ι, v ≠ 0 ∧ SectionROGFrame.rankOne v = A := by
  classical
  have hp := HermitianMat.zero_le_iff.mp hA
  have hc : Fintype.card {i // A.H.eigenvalues i ≠ 0} = 1 :=
    A.H.rank_eq_card_non_zero_eigs.symm.trans hr
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hc
  have hzero (j : ι) (hj : j ≠ i.val) : A.H.eigenvalues j = 0 := by
    by_contra hne
    exact hj (congrArg Subtype.val (hi ⟨j, hne⟩))
  have hsum : A = ∑ j, A.H.eigenvalues j •
      SectionROGFrame.rankOne (A.H.eigenvectorBasis j) := by
    have houter (j : ι) : (SectionROGFrame.rankOne (A.H.eigenvectorBasis j)).mat =
        Matrix.vecMulVec (A.H.eigenvectorBasis j : ι → 𝕜)
          (star (A.H.eigenvectorBasis j : ι → 𝕜)) := rfl
    apply HermitianMat.ext
    change A.mat = (∑ j, A.H.eigenvalues j •
      SectionROGFrame.rankOne (A.H.eigenvectorBasis j)).mat
    simp only [HermitianMat.mat_finset_sum, HermitianMat.mat_smul, houter]
    conv_lhs => rw [A.H.spectral_theorem, Unitary.conjStarAlgAut_apply]
    ext k l
    simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply,
      SectionROGFrame.rankOne, Matrix.conjTranspose_apply, Matrix.star_apply,
      mul_comm, mul_left_comm, mul_assoc, RCLike.real_smul_eq_coe_mul]
  have heq : A = A.H.eigenvalues i.val •
      SectionROGFrame.rankOne (A.H.eigenvectorBasis i.val) := by
    calc
      A = ∑ j, A.H.eigenvalues j •
          SectionROGFrame.rankOne (A.H.eigenvectorBasis j) := hsum
      _ = _ := Finset.sum_eq_single i.val
        (fun j _ hj => by rw [hzero j hj, zero_smul]) (by simp)
  let v : EuclideanSpace 𝕜 ι := Real.sqrt (A.H.eigenvalues i.val) • A.H.eigenvectorBasis i.val
  have hpos : 0 < A.H.eigenvalues i.val :=
    lt_of_le_of_ne (hp.eigenvalues_nonneg i.val) (Ne.symm i.property)
  refine ⟨v, ?_, ?_⟩
  · exact smul_ne_zero (Real.sqrt_pos.mpr hpos).ne'
      (A.H.eigenvectorBasis.orthonormal.ne_zero i.val)
  · change SectionROGFrame.rankOne
      (Real.sqrt (A.H.eigenvalues i.val) • (A.H.eigenvectorBasis i.val : ι → 𝕜)) = A
    rw [SectionROGFrame.rankOne_real_smul, Real.mul_self_sqrt hpos.le]
    exact heq.symm

/-- The actual native Hermitian image, its whole pure carrier, and frames
returned to the original space with the same normalizing point. -/
def NativeGeometry (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (Ψ : V →ₗ[ℝ] Matrix ι ι 𝕜) (h : V) : Prop :=
  ∃ H : V →ₗ[ℝ] HermitianMat ι 𝕜,
    (∀ v, (H v).mat = Ψ v) ∧
    H '' {v | v ∈ C ∧ u v = 1} = SectionROGFrame.base H.range ∧
    ((∀ x ∈ C, ∃ (k : ℕ) (y : Fin k → V),
      (∀ j, y j ∈ C ∧ (Ψ (y j)).rank = 1) ∧ Ψ x = ∑ j, Ψ (y j)) →
      SectionROGFrame.ROG H.range ∧
      H '' ({v | v ∈ C ∧ u v = 1}).extremePoints ℝ =
        SectionROGFrame.pureRanks H.range ∧
      (∀ p ∈ ({v | v ∈ C ∧ u v = 1}).extremePoints ℝ,
        H p ≤ 1 ∧ (1 < Fintype.card ι →
          (((Fintype.card ι : ℝ) - 1)⁻¹ • (h - p) ∈ {v | v ∈ C ∧ u v = 1}) ∧
          H (((Fintype.card ι : ℝ) - 1)⁻¹ • (h - p)) =
            ((Fintype.card ι : ℝ) - 1)⁻¹ • (1 - H p))) ∧
      (∀ p ∈ ({v | v ∈ C ∧ u v = 1}).extremePoints ℝ, ∀ i₀ : ι,
        ∃ (b : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) (y : ι → V),
          y i₀ = p ∧
          (∀ j, y j ∈ ({v | v ∈ C ∧ u v = 1}).extremePoints ℝ ∧
            H (y j) = SectionROGFrame.rankOne (b j)) ∧
          (∑ j, y j) = h))

private theorem native_geometry [Nonempty ι]
    (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (Ψ : V →ₗ[ℝ] Matrix ι ι 𝕜) (hΨ : Function.Injective Ψ)
    (hHerm : ∀ v, (Ψ v).IsHermitian)
    (htrace : ∀ v, (Ψ v).trace = (u v : 𝕜))
    (hsection : ∀ v, v ∈ C ↔ (Ψ v).PosSemidef)
    (h : V) (hh : Ψ h = 1) : NativeGeometry C u Ψ h := by
  classical
  let H : V →ₗ[ℝ] HermitianMat ι 𝕜 :=
    { toFun := fun v => ⟨Ψ v, (hHerm v).isSelfAdjoint⟩
      map_add' := by intros; apply HermitianMat.ext; exact Ψ.map_add _ _
      map_smul' := by intros; apply HermitianMat.ext; exact Ψ.map_smul _ _ }
  have hH : Function.Injective H := fun x y heq => hΨ (congrArg HermitianMat.mat heq)
  have hHt (v : V) : (H v).trace = u v := by
    rw [HermitianMat.trace_eq_re_trace]
    change RCLike.re (Ψ v).trace = u v
    rw [htrace, RCLike.ofReal_re]
  have hHC (v : V) : v ∈ C ↔ 0 ≤ H v := by
    constructor
    · intro hv
      exact HermitianMat.zero_le_iff.mpr ((hsection v).mp hv)
    · intro hv
      exact (hsection v).mpr (HermitianMat.zero_le_iff.mp hv)
  have hHh : H h = 1 := HermitianMat.ext hh
  let K := {v : V | v ∈ C ∧ u v = 1}
  have hbase : H '' K = SectionROGFrame.base H.range := by
    ext X
    constructor
    · rintro ⟨v, ⟨hv, hvu⟩, rfl⟩
      exact ⟨⟨v, rfl⟩, (hHC v).mp hv, (hHt v).trans hvu⟩
    · rintro ⟨⟨v, rfl⟩, hv, hvu⟩
      exact ⟨v, ⟨(hHC v).mpr hv, (hHt v).symm.trans hvu⟩, rfl⟩
  have htransport : H '' K.extremePoints ℝ = (H '' K).extremePoints ℝ := by
    ext X
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ ⟨r, s, hr, hs, hrs, heq⟩
      have heq' : r • a + s • b = p := hH (by simpa using heq)
      exact congrArg H (hp.2 ha hb ⟨r, s, hr, hs, hrs, heq'⟩)
    · intro hX
      obtain ⟨p, hp, rfl⟩ := hX.1
      refine ⟨p, ⟨hp, ?_⟩, rfl⟩
      rintro a ha b hb ⟨r, s, hr, hs, hrs, heq⟩
      apply hH
      apply hX.2 ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨r, s, hr, hs, hrs, by simpa using congrArg H heq⟩
  refine ⟨H, fun _ => rfl, hbase, ?_⟩
  intro hrog
  have hROG : SectionROGFrame.ROG H.range := by
    rintro _ ⟨x, rfl⟩ hx
    obtain ⟨k, y, hy, hsum⟩ := hrog x ((hHC x).mpr hx)
    choose v hv using fun j => psd_rank_one_outer (H (y j))
      ((hHC (y j)).mp (hy j).1) (hy j).2
    refine ⟨k, v, fun j => ⟨(hv j).1, ?_⟩, ?_⟩
    · rw [(hv j).2]
      exact ⟨y j, rfl⟩
    · have heq : x = ∑ j, y j := hΨ (by simpa only [map_sum] using hsum)
      rw [heq, map_sum]
      exact Finset.sum_congr rfl (fun j _ => (hv j).2.symm)
  have hpure : H '' K.extremePoints ℝ = SectionROGFrame.pureRanks H.range := by
    rw [htransport, hbase, SectionROGFrame.whole_pure_carrier H.range hROG]
  have hframe (p : V) (hp : p ∈ K.extremePoints ℝ) (i₀ : ι) :
      ∃ (b : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) (y : ι → V),
        y i₀ = p ∧ (∀ j, y j ∈ K.extremePoints ℝ ∧
          H (y j) = SectionROGFrame.rankOne (b j)) ∧ (∑ j, y j) = h := by
    have hp' : H p ∈ SectionROGFrame.pureRanks H.range := hpure ▸ ⟨p, hp, rfl⟩
    obtain ⟨v, hv, hveq, hvL⟩ := hp'
    rw [← hveq] at hvL
    obtain ⟨b, hb, hbL, _, hsum⟩ :=
      SectionROGFrame.rog_frame H.range ⟨h, hHh⟩ hROG v hv hvL i₀
    let e : V ≃ₗ[ℝ] H.range := LinearEquiv.ofInjective H hH
    let y : ι → V := fun j => e.symm ⟨SectionROGFrame.rankOne (b j), hbL j⟩
    have hy (j : ι) : H (y j) = SectionROGFrame.rankOne (b j) :=
      congrArg Subtype.val (e.apply_symm_apply _)
    have hyP (j : ι) : y j ∈ K.extremePoints ℝ := by
      apply hH.mem_set_image.mp
      rw [hpure, hy]
      exact ⟨b j, b.orthonormal.norm_eq_one j, rfl, hbL j⟩
    refine ⟨b, y, hH (by rw [hy, hb, hveq]), fun j => ⟨hyP j, hy j⟩, ?_⟩
    apply hH
    rw [map_sum]
    simpa only [hy, hHh] using hsum
  refine ⟨hROG, hpure, ?_, hframe⟩
  intro p hp
  let i₀ : ι := Classical.choice inferInstance
  obtain ⟨b, y, hy₀, hy, hsum⟩ := hframe p hp i₀
  have hPsum : (∑ j, SectionROGFrame.rankOne (b j)) = (1 : HermitianMat ι 𝕜) := by
    have heq := congrArg H hsum
    simpa only [map_sum, (hy _).2, hHh] using heq
  have hpI : H p ≤ 1 := by
    rw [← hy₀, (hy i₀).2, ← hPsum]
    exact Finset.single_le_sum (fun j _ => SectionROGFrame.rankOne_nonneg (b j))
      (Finset.mem_univ i₀)
  refine ⟨hpI, ?_⟩
  intro hn
  have hnR : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hmass : u h = (Fintype.card ι : ℝ) := by
    rw [← hHt, hHh]
    simp
  have heq : H (((Fintype.card ι : ℝ) - 1)⁻¹ • (h - p)) =
      ((Fintype.card ι : ℝ) - 1)⁻¹ • (1 - H p) := by simp [hHh]
  refine ⟨⟨(hHC _).mpr ?_, ?_⟩, heq⟩
  · rw [heq]
    exact smul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hnR.le)) (sub_nonneg.mpr hpI)
  · simp only [map_smul, map_sub, hmass, hp.1.2, smul_eq_mul]
    exact inv_mul_cancel₀ (sub_pos.mpr hnR).ne'

/-- The full original dual interval and each confirmer set, represented faithfully
in the space of all real pointwise readings, together with attained comparisons. -/
def OriginalEffectGeometry (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  let O := fun f : V →ₗ[ℝ] ℝ => ∀ x ∈ C, 0 ≤ f x ∧ f x ≤ u x
  let coeFn := fun f : V →ₗ[ℝ] ℝ => (f : V → ℝ)
  IsCompact (coeFn '' {f | O f}) ∧
    ∀ p : V, u p = 1 →
      IsCompact (coeFn '' {f | O f ∧ f p = 1}) ∧
      (coeFn '' {f | O f ∧ f p = 1}).Nonempty ∧
      ∀ x : V, ∃ f : V →ₗ[ℝ] ℝ, O f ∧ f p = 1 ∧
        (∀ g, O g → g p = 1 → f x ≤ g x) ∧
        f x = sInf {r : ℝ | ∃ g, O g ∧ g p = 1 ∧ g x = r} ∧
        (x ∈ C → (f x = 0 ↔ ∃ g, O g ∧ g p = 1 ∧ g x = 0))

private theorem original_effect_geometry [Nontrivial V]
    (C : PointedCone ℝ V) (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    (u : V →ₗ[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x) :
    OriginalEffectGeometry C u := by
  classical
  let O := fun f : V →ₗ[ℝ] ℝ => ∀ x ∈ C, 0 ≤ f x ∧ f x ≤ u x
  let coeFn := fun f : V →ₗ[ℝ] ℝ => (f : V → ℝ)
  let E : Set (V → ℝ) := coeFn '' {f | O f}
  have hnonneg (x : V) (hx : x ∈ C) : 0 ≤ u x := by
    by_cases hz : x = 0
    · simp [hz]
    · exact (hu x hx hz).le
  have huO : O u := fun x hx => ⟨hnonneg x hx, le_rfl⟩
  have hclosed : IsClosed E := by
    have heq : E = {f : V → ℝ |
        (∀ x y, f (x + y) = f x + f y) ∧
        (∀ (r : ℝ) x, f (r • x) = r • f x) ∧
        (∀ x ∈ C, 0 ≤ f x ∧ f x ≤ u x)} := by
      ext f
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨g.map_add, g.map_smul, hg⟩
      · rintro ⟨hadd, hsmul, hO⟩
        let g : V →ₗ[ℝ] ℝ := { toFun := f, map_add' := hadd, map_smul' := hsmul }
        exact ⟨g, hO, rfl⟩
    rw [heq]
    simp only [Set.setOf_and, Set.setOf_forall]
    refine (isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply (x + y))
        ((continuous_apply x).add (continuous_apply y))).inter ?_
    refine (isClosed_iInter fun r => isClosed_iInter fun x =>
      isClosed_eq (continuous_apply (r • x)) ((continuous_apply x).const_smul r)).inter ?_
    exact isClosed_iInter fun x => isClosed_iInter fun _ =>
      (isClosed_le continuous_const (continuous_apply x)).inter
        (isClosed_le (continuous_apply x) continuous_const)
  have hd : ∀ x : V, ∃ a ∈ C, ∃ b ∈ C, a - b = x := by
    have hrep : (C : ConvexCone ℝ V).IsReproducing :=
      ConvexCone.IsReproducing.of_span_eq_top hgen
    intro x
    have hx : x ∈ (C : Set V) - (C : Set V) :=
      (Set.eq_univ_iff_forall.mp hrep) x
    exact Set.mem_sub.mp hx
  choose a ha b hb hab using hd
  let B : Set (V → ℝ) := Set.pi Set.univ (fun x => Set.Icc (-u (b x)) (u (a x)))
  have hB : IsCompact B := isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : E ⊆ B := by
    rintro _ ⟨f, hf, rfl⟩ x _
    have heq : f x = f (a x) - f (b x) :=
      (congrArg f (hab x).symm).trans (map_sub f _ _)
    have hfa := hf (a x) (ha x)
    have hfb := hf (b x) (hb x)
    change -u (b x) ≤ f x ∧ f x ≤ u (a x)
    rw [heq]
    constructor <;> linarith
  have hE : IsCompact E := hB.of_isClosed_subset hclosed hsub
  refine ⟨hE, ?_⟩
  intro p hp
  have hconf : coeFn '' {f | O f ∧ f p = 1} = E ∩ {g : V → ℝ | g p = 1} := by
    ext g
    constructor
    · rintro ⟨f, ⟨hf, hfp⟩, rfl⟩
      exact ⟨⟨f, hf, rfl⟩, hfp⟩
    · rintro ⟨⟨f, hf, rfl⟩, hfp⟩
      exact ⟨f, ⟨hf, hfp⟩, rfl⟩
  have hcompact : IsCompact (coeFn '' {f | O f ∧ f p = 1}) := by
    rw [hconf]
    exact hE.inter_right (isClosed_eq (continuous_apply p) continuous_const)
  have hne : (coeFn '' {f | O f ∧ f p = 1}).Nonempty :=
    ⟨coeFn u, u, ⟨huO, hp⟩, rfl⟩
  refine ⟨hcompact, hne, ?_⟩
  intro x
  obtain ⟨g, ⟨f, ⟨hf, hfp⟩, rfl⟩, hmin⟩ :=
    hcompact.exists_isMinOn hne (continuous_apply x).continuousOn
  have hleast (j : V →ₗ[ℝ] ℝ) (hj : O j) (hjp : j p = 1) : f x ≤ j x :=
    hmin ⟨j, ⟨hj, hjp⟩, rfl⟩
  let R : Set ℝ := {r | ∃ j, O j ∧ j p = 1 ∧ j x = r}
  have hfR : f x ∈ R := ⟨f, hf, hfp, rfl⟩
  have hlower : ∀ r ∈ R, f x ≤ r := by
    rintro r ⟨j, hj, hjp, rfl⟩
    exact hleast j hj hjp
  have hinf : f x = sInf R := le_antisymm
    (le_csInf ⟨f x, hfR⟩ hlower) (csInf_le ⟨f x, hlower⟩ hfR)
  refine ⟨f, hf, hfp, hleast, hinf, ?_⟩
  intro hx
  constructor
  · intro hz
    exact ⟨f, hf, hfp, hz⟩
  · rintro ⟨j, hj, hjp, hjx⟩
    exact le_antisymm (hjx ▸ hleast j hj hjp) (hf x hx).1

/-- Native real and complex ambient dimensions and their trace codimensions. -/
def NativeAmbientDimensions (n : ℕ) : Prop :=
  Module.finrank ℝ (HermitianMat (Fin n) ℝ) = n * (n + 1) / 2 ∧
  Module.finrank ℝ (HermitianMat (Fin n) ℂ) = n ^ 2 ∧
  (∀ L : Submodule ℝ (HermitianMat (Fin n) ℝ),
    Module.finrank ℝ L + Module.finrank ℝ Lᗮ = n * (n + 1) / 2) ∧
  (∀ L : Submodule ℝ (HermitianMat (Fin n) ℂ),
    Module.finrank ℝ L + Module.finrank ℝ Lᗮ = n ^ 2)

private def real_symmetric_coordinates (n : ℕ) :
    HermitianMat (Fin n) ℝ ≃ₗ[ℝ] (Sym2 (Fin n) → ℝ) where
  toFun A := Sym2.lift ⟨A.mat, fun i j => by
    simpa only [Matrix.conjTranspose_apply, star_trivial] using (congrFun₂ A.H i j).symm⟩
  invFun f := ⟨fun i j => f s(i, j), by
    change (fun i j => star (f s(j, i))) = (fun i j => f s(i, j))
    ext i j
    simp only [star_trivial, Sym2.eq_swap]⟩
  left_inv A := by apply HermitianMat.ext; ext i j; rfl
  right_inv f := by
    funext q
    exact Sym2.ind (fun i j => rfl) q
  map_add' A B := by
    funext q
    exact Sym2.ind (fun i j => rfl) q
  map_smul' r A := by
    funext q
    exact Sym2.ind (fun i j => rfl) q

private theorem native_ambient_dimensions (n : ℕ) : NativeAmbientDimensions n := by
  have hr : Module.finrank ℝ (HermitianMat (Fin n) ℝ) = n * (n + 1) / 2 := by
    rw [(real_symmetric_coordinates n).finrank_eq,
      Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin,
      Nat.choose_two_right]
    simp only [Nat.add_sub_cancel, Nat.mul_comm]
  let e : HermitianMat (Fin n) ℂ ≃ₗ[ℝ]
      D5.S3.Quantum.Measurement.BasisMeasurementProjection.HermitianSpace n :=
    { toFun := fun A => ⟨A.mat, A.property⟩
      invFun := fun A => ⟨A.val, A.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hc : Module.finrank ℝ (HermitianMat (Fin n) ℂ) = n ^ 2 :=
    e.finrank_eq.trans
      (D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition.hermitian_space_finrank n)
  exact ⟨hr, hc,
    fun L => L.finrank_add_finrank_orthogonal.trans hr,
    fun L => L.finrank_add_finrank_orthogonal.trans hc⟩

/-- The same native normalization congruence transports the full image,
trace coefficients, annihilators and real ambient codimension. -/
def NativeCongruence (σ Ψ : V →ₗ[ℝ] Matrix ι ι 𝕜) (S : Matrix ι ι 𝕜) : Prop :=
  ∃ (H₀ H₁ : V →ₗ[ℝ] HermitianMat ι 𝕜)
    (e : HermitianMat ι 𝕜 ≃ₗ[ℝ] HermitianMat ι 𝕜),
    (∀ v, (H₀ v).mat = σ v) ∧ (∀ v, (H₁ v).mat = Ψ v) ∧
    (∀ A, (e A).mat = S * A.mat * S) ∧
    (∀ A, (e.symm A).mat = S⁻¹ * A.mat * S⁻¹) ∧
    (∀ v, H₁ v = e (H₀ v)) ∧ H₁.range = H₀.range.map e.toLinearMap ∧
    Module.finrank ℝ H₀.rangeᗮ = Module.finrank ℝ H₁.rangeᗮ ∧
    (∀ A B, inner ℝ (e A) B = inner ℝ A (e B)) ∧
    (∀ A v, RCLike.re (A.mat * Ψ v).trace =
      RCLike.re ((e A).mat * σ v).trace) ∧
    (∀ A, A ∈ H₁.rangeᗮ ↔ e A ∈ H₀.rangeᗮ) ∧
    (∀ A, A ∈ H₀.rangeᗮ ↔ e.symm A ∈ H₁.rangeᗮ)

private theorem native_congruence
    (σ Ψ : V →ₗ[ℝ] Matrix ι ι 𝕜) (hσ : ∀ v, (σ v).IsHermitian)
    (S : Matrix ι ι 𝕜) (hS : S.IsHermitian) (hSU : IsUnit S)
    (hΨ : ∀ v, Ψ v = S * σ v * S) : NativeCongruence σ Ψ S := by
  classical
  have hd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSU
  have hl : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hd
  have hr : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hd
  have hSinv : (S⁻¹).IsHermitian := hS.inv
  let T := HermitianMat.conjLinear ℝ S
  let Tinv := HermitianMat.conjLinear ℝ S⁻¹
  have hT (A : HermitianMat ι 𝕜) : (T A).mat = S * A.mat * S := by
    change S * A.mat * Sᴴ = _
    rw [hS.eq]
  have hTi (A : HermitianMat ι 𝕜) : (Tinv A).mat = S⁻¹ * A.mat * S⁻¹ := by
    change S⁻¹ * A.mat * S⁻¹ᴴ = _
    rw [hSinv.eq]
  have hleft (A : HermitianMat ι 𝕜) : Tinv (T A) = A := by
    apply HermitianMat.ext
    rw [hTi, hT]
    calc
      S⁻¹ * (S * A.mat * S) * S⁻¹ = (S⁻¹ * S) * A.mat * (S * S⁻¹) := by
        simp only [Matrix.mul_assoc]
      _ = A.mat := by rw [hl, hr, Matrix.one_mul, Matrix.mul_one]
  have hright (A : HermitianMat ι 𝕜) : T (Tinv A) = A := by
    apply HermitianMat.ext
    rw [hT, hTi]
    calc
      S * (S⁻¹ * A.mat * S⁻¹) * S = (S * S⁻¹) * A.mat * (S⁻¹ * S) := by
        simp only [Matrix.mul_assoc]
      _ = A.mat := by rw [hl, hr, Matrix.one_mul, Matrix.mul_one]
  let e : HermitianMat ι 𝕜 ≃ₗ[ℝ] HermitianMat ι 𝕜 :=
    { toLinearMap := T, invFun := Tinv, left_inv := hleft, right_inv := hright }
  let H₀ : V →ₗ[ℝ] HermitianMat ι 𝕜 :=
    { toFun := fun v => ⟨σ v, (hσ v).isSelfAdjoint⟩
      map_add' := by intros; apply HermitianMat.ext; exact σ.map_add _ _
      map_smul' := by intros; apply HermitianMat.ext; exact σ.map_smul _ _ }
  let H₁ : V →ₗ[ℝ] HermitianMat ι 𝕜 := T.comp H₀
  have hH₁ (v : V) : (H₁ v).mat = Ψ v := (hT (H₀ v)).trans (hΨ v).symm
  have hmap : H₁.range = H₀.range.map e.toLinearMap := by
    rw [LinearMap.range_comp]
  have hdim : Module.finrank ℝ H₀.rangeᗮ = Module.finrank ℝ H₁.rangeᗮ := by
    have h₀ := H₀.range.finrank_add_finrank_orthogonal
    have h₁ := H₁.range.finrank_add_finrank_orthogonal
    have hm : Module.finrank ℝ H₁.range = Module.finrank ℝ H₀.range := by
      rw [hmap]
      exact e.finrank_map_eq H₀.range
    omega
  have hadj (A B : HermitianMat ι 𝕜) : inner ℝ (e A) B = inner ℝ A (e B) := by
    simp only [HermitianMat.inner_eq_re_trace]
    change RCLike.re ((T A).mat * B.mat).trace = RCLike.re (A.mat * (T B).mat).trace
    rw [hT, hT]
    congr 1
    calc
      (S * A.mat * S * B.mat).trace = (S * (A.mat * (S * B.mat))).trace := by
        simp only [Matrix.mul_assoc]
      _ = ((A.mat * (S * B.mat)) * S).trace := Matrix.trace_mul_comm _ _
      _ = (A.mat * (S * B.mat * S)).trace := by simp only [Matrix.mul_assoc]
  have hcoeff (A : HermitianMat ι 𝕜) (v : V) :
      RCLike.re (A.mat * Ψ v).trace = RCLike.re ((e A).mat * σ v).trace := by
    have hh : inner ℝ A (H₁ v) = inner ℝ (e A) (H₀ v) := (hadj A (H₀ v)).symm
    simpa only [HermitianMat.inner_eq_re_trace, hH₁,
      show (H₀ v).mat = σ v from rfl] using hh
  have hann (A : HermitianMat ι 𝕜) : A ∈ H₁.rangeᗮ ↔ e A ∈ H₀.rangeᗮ := by
    rw [H₁.range.mem_orthogonal', H₀.range.mem_orthogonal']
    constructor
    · intro h X hX
      obtain ⟨v, rfl⟩ := hX
      rw [hadj]
      exact h (H₁ v) ⟨v, rfl⟩
    · intro h X hX
      obtain ⟨v, rfl⟩ := hX
      change inner ℝ A (e (H₀ v)) = 0
      rw [← hadj]
      exact h (H₀ v) ⟨v, rfl⟩
  refine ⟨H₀, H₁, e, fun _ => rfl, hH₁, hT, hTi, fun _ => rfl,
    hmap, hdim, hadj, hcoeff, hann, ?_⟩
  intro A
  simpa only [e.apply_symm_apply] using (hann (e.symm A)).symm

private theorem matrix_eq_one_of_card_one (A : Matrix ι ι 𝕜)
    (hcard : Fintype.card ι = 1) (htrace : A.trace = 1) : A = 1 := by
  classical
  obtain ⟨hunique⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hcard
  letI : Unique ι := hunique
  ext i j
  have htr : A.trace = A i i := by simp [Matrix.trace, Subsingleton.elim (default : ι) i]
  have hij : i = j := Subsingleton.elim _ _
  subst j
  simpa only [Matrix.one_apply, ite_true] using htr.symm.trans htrace

set_option maxHeartbeats 1200000 in
/-- The principal congruence of the actual original-unit maximizer normalizes
all original vectors, with the identity and entire base in the same image. -/
theorem exists_original_unit_normalization
    [FiniteDimensional ℝ V] [Nontrivial V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    (C : PointedCone ℝ V) (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    (u : V →ₗ[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hcompact : IsCompact {x : V | x ∈ C ∧ u x = 1})
    (ρ : V →ₗ[ℝ] Matrix ι ι 𝕜) (hρ : Function.Injective ρ)
    (hsection : ∀ x, x ∈ C ↔ (ρ x).PosSemidef) :
    let n := Module.finrank 𝕜 (commonSupport C ρ)
    0 < n ∧ ∃ U : Matrix ι (Fin n) 𝕜,
      ∃ σ Ψ : V →ₗ[ℝ] Matrix (Fin n) (Fin n) 𝕜,
        Uᴴ * U = 1 ∧ U.toEuclideanLin.range = commonSupport C ρ ∧
        (∀ x, σ x = Uᴴ * ρ x * U) ∧ (∀ x, ρ x = U * σ x * Uᴴ) ∧
        Function.Injective σ ∧ (∀ x, (σ x).IsHermitian) ∧
        (∀ x, x ∈ C ↔ (σ x).PosSemidef) ∧ (∀ x, (σ x).rank = (ρ x).rank) ∧
        ∃ h : V, h ∈ C ∧ u h = (n : ℝ) ∧ (σ h).PosDef ∧
          (∀ v : V, ((σ h)⁻¹ * σ v).trace = (u v : 𝕜)) ∧
          (∀ x ∈ C, u x = (n : ℝ) → RCLike.re (σ x).det ≤ RCLike.re (σ h).det) ∧
          (∀ k ∈ C, u k = (n : ℝ) →
            (∀ x ∈ C, u x = (n : ℝ) → RCLike.re (σ x).det ≤ RCLike.re (σ k).det) →
            k = h) ∧
          let S := CFC.sqrt (σ h)⁻¹
          S.IsHermitian ∧ IsUnit S ∧ S * S = (σ h)⁻¹ ∧
          (∀ v, Ψ v = S * σ v * S) ∧ Ψ h = 1 ∧
          Function.Injective Ψ ∧ (∀ v, (Ψ v).IsHermitian) ∧
          (∀ v, (Ψ v).trace = (u v : 𝕜)) ∧
          (∀ v, v ∈ C ↔ (Ψ v).PosSemidef) ∧
          (∀ v, (Ψ v).rank = (ρ v).rank) ∧
          (∀ v, ρ v = U * (S⁻¹ * Ψ v * S⁻¹) * Uᴴ) ∧
          (1 : Matrix (Fin n) (Fin n) 𝕜) ∈ Ψ.range ∧
          Ψ '' {v : V | v ∈ C ∧ u v = 1} =
            {X | X ∈ Ψ.range ∧ X.PosSemidef ∧ X.trace = 1} ∧
          (∀ x ∈ C,
            (∃ (k : ℕ) (y : Fin k → V),
              (∀ j, y j ∈ C ∧ (ρ (y j)).rank = 1) ∧ ρ x = ∑ j, ρ (y j)) ↔
            (∃ (k : ℕ) (y : Fin k → V),
              (∀ j, y j ∈ C ∧ (Ψ (y j)).rank = 1) ∧ Ψ x = ∑ j, Ψ (y j))) ∧
          ((∃ p : V, {v : V | v ∈ C ∧ u v = 1} = {p}) →
            (∀ x ∈ C, ∃ (k : ℕ) (y : Fin k → V),
              (∀ j, y j ∈ C ∧ (ρ (y j)).rank = 1) ∧ ρ x = ∑ j, ρ (y j)) → n = 1) ∧
          (n = 1 →
            {v : V | v ∈ C ∧ u v = 1} = {h} ∧
            ({v : V | v ∈ C ∧ u v = 1}).extremePoints ℝ = {h} ∧
            {f : V →ₗ[ℝ] ℝ | (∀ v ∈ C, 0 ≤ f v ∧ f v ≤ u v) ∧ f h = 1} = {u} ∧
            {v : V | (v ∈ C ∧ u v = 1) ∧ ∃ f : V →ₗ[ℝ] ℝ,
              (∀ w ∈ C, 0 ≤ f w ∧ f w ≤ u w) ∧ f h = 1 ∧ f v = 0} = ∅ ∧
            {f : V →ₗ[ℝ] ℝ | ∀ v ∈ C, 0 ≤ f v ∧ f v ≤ u v} =
              {f | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ f = t • u}) ∧
          ∃ e : V ≃ₗ[ℝ] Ψ.range,
            (∀ v, (e v).val = Ψ v) ∧
            let K := {v : V | v ∈ C ∧ u v = 1}
            let Q := {X : Ψ.range | X.val.PosSemidef ∧ X.val.trace = 1}
            let d := e.symm.dualMap
            let O := fun f : V →ₗ[ℝ] ℝ => ∀ v ∈ C, 0 ≤ f v ∧ f v ≤ u v
            let N := fun g : Ψ.range →ₗ[ℝ] ℝ => ∀ X : Ψ.range,
              X.val.PosSemidef → 0 ≤ g X ∧ g X ≤ RCLike.re X.val.trace
            e '' K = Q ∧ e '' K.extremePoints ℝ = Q.extremePoints ℝ ∧
            (∀ F : Set V, Convex ℝ F ↔ Convex ℝ (e '' F)) ∧
            (∀ A B : Set V, IsExtreme ℝ A B ↔ IsExtreme ℝ (e '' A) (e '' B)) ∧
            (∀ A S : Set V,
              e '' {v | ∀ F : Set V, Convex ℝ F → IsExtreme ℝ A F → S ⊆ F → v ∈ F} =
              {X | ∀ G : Set Ψ.range, Convex ℝ G → IsExtreme ℝ (e '' A) G →
                e '' S ⊆ G → X ∈ G}) ∧
            (∀ f, O f ↔ N (d f)) ∧
            (∀ p, d '' {f | O f ∧ f p = 1} = {g | N g ∧ g (e p) = 1}) ∧
            (∀ p x,
              {r : ℝ | ∃ f, O f ∧ f p = 1 ∧ f x = r} =
              {r : ℝ | ∃ g, N g ∧ g (e p) = 1 ∧ g (e x) = r}) ∧
            (∀ p x,
              d '' {f | O f ∧ f p = 1 ∧ ∀ g, O g → g p = 1 → f x ≤ g x} =
              {g | N g ∧ g (e p) = 1 ∧ ∀ j, N j → j (e p) = 1 → g (e x) ≤ j (e x)}) ∧
            NativeGeometry C u Ψ h ∧ OriginalEffectGeometry C u ∧
            NativeAmbientDimensions n ∧ NativeCongruence σ Ψ S := by
  classical
  dsimp only
  obtain ⟨hn, U, σ, hU, hUr, hσeq, hrec, hσ, hHerm, hC, hrank,
      h, hh, hmass, hhPD, htrace, hmax, hunique⟩ :=
    exists_original_unit_inverse_trace_stationarity C hgen u hu hcompact ρ hρ hsection
  let S := CFC.sqrt (σ h)⁻¹
  obtain ⟨hSH, hSU, hSS, hroot⟩ := principal_inverse_sqrt_laws (σ h) hhPD
  change S.IsHermitian at hSH
  change IsUnit S at hSU
  change S * S = (σ h)⁻¹ at hSS
  change S * σ h * S = 1 at hroot
  have hSd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSU
  have hleft : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSd
  have hright : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSd
  let Ψ : V →ₗ[ℝ] Matrix _ _ 𝕜 :=
    { toFun := fun v => S * σ v * S
      map_add' := by intros; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intros; simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hinv (v : V) : S⁻¹ * Ψ v * S⁻¹ = σ v := by
    change S⁻¹ * (S * σ v * S) * S⁻¹ = σ v
    calc
      _ = (S⁻¹ * S) * σ v * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
      _ = σ v := by rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]
  have hΨ : Function.Injective Ψ := by
    intro v w heq
    apply hσ
    rw [← hinv v, ← hinv w, heq]
  have hΨC (v : V) : v ∈ C ↔ (Ψ v).PosSemidef := by
    rw [hC v]
    change (σ v).PosSemidef ↔ (S * σ v * S).PosSemidef
    simpa only [Matrix.star_eq_conjTranspose, hSH.eq] using
      (Matrix.IsUnit.posSemidef_star_left_conjugate_iff (x := σ v) hSU).symm
  have hΨtrace (v : V) : (Ψ v).trace = (u v : 𝕜) := by
    change (S * σ v * S).trace = (u v : 𝕜)
    calc
      (S * σ v * S).trace = (S * S * σ v).trace := Matrix.trace_mul_cycle _ _ _
      _ = (u v : 𝕜) := by rw [hSS, htrace v]
  have hΨHerm (v : V) : (Ψ v).IsHermitian := by
    change (S * σ v * S).IsHermitian
    simpa only [hSH.eq] using Matrix.isHermitian_conjTranspose_mul_mul S (hHerm v)
  refine ⟨hn, U, σ, Ψ, hU, hUr, hσeq, hrec, hσ, hHerm, hC, hrank,
    h, hh, hmass, hhPD, htrace, hmax, hunique, hSH, hSU, hSS, (fun _ => rfl), hroot,
    hΨ, hΨHerm, hΨtrace, hΨC, ?_, ?_, ⟨h, hroot⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    change (S * σ v * S).rank = (ρ v).rank
    rw [Matrix.rank_mul_eq_left_of_isUnit_det S _ hSd,
      Matrix.rank_mul_eq_right_of_isUnit_det S _ hSd, hrank v]
  · intro v
    rw [hinv, hrec v]
  · ext X
    constructor
    · rintro ⟨v, ⟨hv, huv⟩, rfl⟩
      exact ⟨⟨v, rfl⟩, (hΨC v).mp hv, by rw [hΨtrace v, huv]; simp⟩
    · rintro ⟨⟨v, rfl⟩, hv, huv⟩
      refine ⟨v, ⟨(hΨC v).mpr hv, ?_⟩, rfl⟩
      have hre := congrArg RCLike.re huv
      simpa [hΨtrace v] using hre
  · intro x hx
    have hsum (k : ℕ) (y : Fin k → V) :
        ρ x = ∑ j, ρ (y j) ↔ Ψ x = ∑ j, Ψ (y j) := by
      rw [← map_sum, ← map_sum]
      constructor
      · intro heq
        exact congrArg Ψ (hρ heq)
      · intro heq
        exact congrArg ρ (hΨ heq)
    constructor
    · rintro ⟨k, y, hy, heq⟩
      exact ⟨k, y, (fun j => ⟨(hy j).1, by rw [show (Ψ (y j)).rank = (ρ (y j)).rank from
        by change (S * σ (y j) * S).rank = _
           rw [Matrix.rank_mul_eq_left_of_isUnit_det S _ hSd,
             Matrix.rank_mul_eq_right_of_isUnit_det S _ hSd, hrank], (hy j).2]⟩),
        (hsum k y).mp heq⟩
    · rintro ⟨k, y, hy, heq⟩
      refine ⟨k, y, ?_, (hsum k y).mpr heq⟩
      intro j
      refine ⟨(hy j).1, ?_⟩
      have hr : (Ψ (y j)).rank = (ρ (y j)).rank := by
        change (S * σ (y j) * S).rank = _
        rw [Matrix.rank_mul_eq_left_of_isUnit_det S _ hSd,
          Matrix.rank_mul_eq_right_of_isUnit_det S _ hSd, hrank]
      exact hr.symm.trans (hy j).2
  · rintro ⟨p, hp⟩ hrog
    let n := Module.finrank 𝕜 (commonSupport C ρ)
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hh0 : h ≠ 0 := by
      intro hz
      have : (n : ℝ) = 0 := by simpa only [hz, map_zero] using hmass.symm
      exact hnR.ne' this
    have hscale (v : V) (hv : v ∈ C) (hv0 : v ≠ 0) : v = u v • p := by
      have huv := hu v hv hv0
      have hw : (u v)⁻¹ • v ∈ {v : V | v ∈ C ∧ u v = 1} :=
        ⟨C.smul_mem (inv_nonneg.mpr huv.le) hv, by simp [huv.ne']⟩
      rw [hp, Set.mem_singleton_iff] at hw
      calc
        v = u v • ((u v)⁻¹ • v) := by simp [smul_smul, huv.ne']
        _ = u v • p := by rw [hw]
    obtain ⟨k, y, hy, heq⟩ := hrog h hh
    have hk : 0 < k := by
      by_contra! hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      haveI : IsEmpty (Fin k) := by rw [hk0]; infer_instance
      have hzero : ρ h = 0 := by simpa using heq
      exact hh0 (hρ (by simpa only [map_zero] using hzero))
    let j : Fin k := ⟨0, hk⟩
    have hy0 : y j ≠ 0 := by
      intro hz
      have hbad := (hy j).2
      simpa [hz] using hbad
    have hyp := hu (y j) (hy j).1 hy0
    have hscaled : y j = (u (y j) / (n : ℝ)) • h := by
      calc
        y j = u (y j) • p := hscale (y j) (hy j).1 hy0
        _ = (u (y j) / (n : ℝ) * (n : ℝ)) • p := by
          congr 1
          field_simp [hnR.ne']
        _ = (u (y j) / (n : ℝ)) • h := by
          rw [hscale h hh hh0, hmass, smul_smul]
    have hyPD : (σ (y j)).PosDef := by
      rw [hscaled, map_smul]
      exact hhPD.smul (div_pos hyp hnR)
    have hr := Matrix.rank_of_isUnit (σ (y j)) hyPD.isUnit
    rw [hrank, (hy j).2, Fintype.card_fin] at hr
    exact hr.symm
  · intro hn1
    have hmass1 : u h = 1 := by simpa only [hn1, Nat.cast_one] using hmass
    have hsingle (v : V) (hv : u v = 1) : v = h := by
      apply hΨ
      change Ψ v = S * σ h * S
      rw [hroot]
      exact matrix_eq_one_of_card_one (Ψ v) (by simpa using hn1)
        (by rw [hΨtrace, hv]; simp)
    have hbase : {v : V | v ∈ C ∧ u v = 1} = {h} := by
      ext v
      constructor
      · intro hv
        exact Set.mem_singleton_iff.mpr (hsingle v hv.2)
      · rintro rfl
        exact ⟨hh, hmass1⟩
    have huray (v : V) (hv : v ∈ C) : v = u v • h := by
      by_cases hz : v = 0
      · simp [hz]
      have hp := hu v hv hz
      have hw : (u v)⁻¹ • v ∈ C ∧ u ((u v)⁻¹ • v) = 1 :=
        ⟨C.smul_mem (inv_nonneg.mpr hp.le) hv, by simp [hp.ne']⟩
      have heq := hsingle ((u v)⁻¹ • v) hw.2
      calc
        v = u v • ((u v)⁻¹ • v) := by simp [smul_smul, hp.ne']
        _ = u v • h := by rw [heq]
    have hu_nonneg (v : V) (hv : v ∈ C) : 0 ≤ u v := by
      by_cases hz : v = 0
      · simp [hz]
      · exact (hu v hv hz).le
    have heffect (f : V →ₗ[ℝ] ℝ) : f = f h • u := by
      apply LinearMap.ext_on hgen
      intro v hv
      calc
        f v = f (u v • h) := congrArg f (huray v hv)
        _ = (f h • u) v := by simp [mul_comm]
    have hproper_u : ∀ v ∈ C, 0 ≤ u v ∧ u v ≤ u v :=
      fun v hv => ⟨hu_nonneg v hv, le_rfl⟩
    refine ⟨hbase, by rw [hbase, extremePoints_singleton], ?_, ?_, ?_⟩
    · ext f
      constructor
      · rintro ⟨hf, hfh⟩
        exact Set.mem_singleton_iff.mpr (by simpa [hfh] using heffect f)
      · rintro rfl
        exact ⟨hproper_u, hmass1⟩
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro v ⟨hv, f, hf, hfh, hfv⟩
      have hvh := hsingle v hv.2
      have heq : f h = 0 := by simpa only [hvh] using hfv
      exact zero_ne_one (heq.symm.trans hfh)
    · ext f
      constructor
      · intro hf
        have hbound := hf h hh
        exact ⟨f h, hbound.1, by simpa only [hmass1] using hbound.2, heffect f⟩
      · rintro ⟨t, ht0, ht1, rfl⟩ v hv
        change 0 ≤ t * u v ∧ t * u v ≤ u v
        exact ⟨mul_nonneg ht0 (hu_nonneg v hv),
          by simpa using mul_le_mul_of_nonneg_right ht1 (hu_nonneg v hv)⟩
  · let e : V ≃ₗ[ℝ] Ψ.range := LinearEquiv.ofInjective Ψ hΨ
    let K := {v : V | v ∈ C ∧ u v = 1}
    let Q := {X : Ψ.range | X.val.PosSemidef ∧ X.val.trace = 1}
    let d := e.symm.dualMap
    let O := fun f : V →ₗ[ℝ] ℝ => ∀ v ∈ C, 0 ≤ f v ∧ f v ≤ u v
    let N := fun g : Ψ.range →ₗ[ℝ] ℝ => ∀ X : Ψ.range,
      X.val.PosSemidef → 0 ≤ g X ∧ g X ≤ RCLike.re X.val.trace
    have hd (f : V →ₗ[ℝ] ℝ) (v : V) : d f (e v) = f v := by simp [d]
    have hreal (v : V) : RCLike.re (Ψ v).trace = u v := by rw [hΨtrace]; simp
    have hbase : e '' K = Q := by
      ext X
      obtain ⟨v, rfl⟩ := e.surjective X
      rw [e.injective.mem_set_image]
      change (v ∈ C ∧ u v = 1) ↔ (Ψ v).PosSemidef ∧ (Ψ v).trace = 1
      rw [← hΨC, hΨtrace]
      constructor
      · rintro ⟨hv, huv⟩
        exact ⟨hv, by rw [huv]; simp⟩
      · rintro ⟨hv, huv⟩
        exact ⟨hv, by simpa using congrArg RCLike.re huv⟩
    have hconvex (F : Set V) : Convex ℝ F ↔ Convex ℝ (e '' F) := by
      constructor
      · exact fun hF => hF.linear_image e.toLinearMap
      · intro hF
        have hp := hF.linear_preimage e.toLinearMap
        change Convex ℝ (e ⁻¹' (e '' F)) at hp
        simpa only [e.injective.preimage_image] using hp
    have hsegs (x y : V) : e '' openSegment ℝ x y = openSegment ℝ (e x) (e y) :=
      image_openSegment ℝ e.toLinearMap.toAffineMap x y
    have hface (A B : Set V) : IsExtreme ℝ A B ↔ IsExtreme ℝ (e '' A) (e '' B) := by
      constructor
      · intro hF
        refine ⟨Set.image_mono hF.subset, ?_⟩
        rintro X ⟨x, hx, rfl⟩ Y ⟨y, hy, rfl⟩ Z ⟨z, hz, rfl⟩ hseg
        rw [← hsegs] at hseg
        have hseg' : z ∈ openSegment ℝ x y := e.injective.mem_set_image.mp hseg
        exact ⟨x, hF.left_mem_of_mem_openSegment hx hy hz hseg', rfl⟩
      · intro hF
        refine ⟨?_, ?_⟩
        · intro z hz
          exact e.injective.mem_set_image.mp (hF.subset ⟨z, hz, rfl⟩)
        · intro x hx y hy z hz hseg
          have hs : e z ∈ openSegment ℝ (e x) (e y) := by
            rw [← hsegs]
            exact ⟨z, hseg, rfl⟩
          exact e.injective.mem_set_image.mp
            (hF.left_mem_of_mem_openSegment ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩ hs)
    have hminimal (A S : Set V) :
        e '' {v | ∀ F : Set V, Convex ℝ F → IsExtreme ℝ A F → S ⊆ F → v ∈ F} =
          {X | ∀ G : Set Ψ.range, Convex ℝ G → IsExtreme ℝ (e '' A) G →
            e '' S ⊆ G → X ∈ G} := by
      ext X
      constructor
      · rintro ⟨v, hv, rfl⟩ G hGc hGface hSG
        have hpre : e '' (e ⁻¹' G) = G := Set.image_preimage_eq G e.surjective
        have hpreFace : IsExtreme ℝ A (e ⁻¹' G) := (hface A _).mpr (by
          rw [hpre]
          exact hGface)
        exact hv (e ⁻¹' G) (hGc.linear_preimage e.toLinearMap) hpreFace
          (fun z hz => hSG ⟨z, hz, rfl⟩)
      · intro hv
        obtain ⟨v, rfl⟩ := e.surjective X
        refine ⟨v, ?_, rfl⟩
        intro F hFc hFface hSF
        exact e.injective.mem_set_image.mp
          (hv (e '' F) ((hconvex F).mp hFc) ((hface A F).mp hFface) (Set.image_mono hSF))
    have hproper (f : V →ₗ[ℝ] ℝ) : O f ↔ N (d f) := by
      constructor
      · intro hf X hX
        obtain ⟨v, rfl⟩ := e.surjective X
        change (Ψ v).PosSemidef at hX
        change 0 ≤ d f (e v) ∧ d f (e v) ≤ RCLike.re (Ψ v).trace
        rw [hd, hreal]
        exact hf v ((hΨC v).mpr hX)
      · intro hf v hv
        have hp := hf (e v) ((hΨC v).mp hv)
        change 0 ≤ d f (e v) ∧ d f (e v) ≤ RCLike.re (Ψ v).trace at hp
        simpa only [hd, hreal] using hp
    refine ⟨e, (fun _ => rfl), hbase, ?_, hconvex, hface, hminimal,
      hproper, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [image_extremePoints, hbase]
    · intro p
      ext g
      obtain ⟨f, rfl⟩ := d.surjective g
      rw [d.injective.mem_set_image]
      change (O f ∧ f p = 1) ↔ (N (d f) ∧ d f (e p) = 1)
      rw [hproper, hd]
    · intro p x
      ext r
      constructor
      · rintro ⟨f, hf, hfp, hfx⟩
        exact ⟨d f, (hproper f).mp hf, by rw [hd, hfp], by rw [hd, hfx]⟩
      · rintro ⟨g, hg, hgp, hgx⟩
        obtain ⟨f, rfl⟩ := d.surjective g
        exact ⟨f, (hproper f).mpr hg, by simpa only [hd] using hgp,
          by simpa only [hd] using hgx⟩
    · intro p x
      ext g
      obtain ⟨f, rfl⟩ := d.surjective g
      rw [d.injective.mem_set_image]
      change (O f ∧ f p = 1 ∧ ∀ j, O j → j p = 1 → f x ≤ j x) ↔
        (N (d f) ∧ d f (e p) = 1 ∧
          ∀ j, N j → j (e p) = 1 → d f (e x) ≤ j (e x))
      constructor
      · rintro ⟨hf, hfp, hmin⟩
        refine ⟨(hproper f).mp hf, by rw [hd, hfp], ?_⟩
        intro j hj hjp
        obtain ⟨k, rfl⟩ := d.surjective j
        simpa only [hd] using hmin k ((hproper k).mpr hj) (by simpa only [hd] using hjp)
      · rintro ⟨hf, hfp, hmin⟩
        refine ⟨(hproper f).mpr hf, by simpa only [hd] using hfp, ?_⟩
        intro j hj hjp
        simpa only [hd] using hmin (d j) ((hproper j).mp hj) (by simpa only [hd] using hjp)

    · letI : Nonempty (Fin (Module.finrank 𝕜 (commonSupport C ρ))) := ⟨⟨0, hn⟩⟩
      exact native_geometry C u Ψ hΨ hΨHerm hΨtrace hΨC h hroot

    · exact original_effect_geometry C hgen u hu
    · exact native_ambient_dimensions _
    · exact native_congruence σ Ψ hHerm S hSH hSU (fun _ => rfl)

end D5.S3.Quantum.Foundation.OriginalUnitNormalization
