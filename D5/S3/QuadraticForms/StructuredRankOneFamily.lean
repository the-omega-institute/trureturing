/- GID: D5/S3/QuadraticForms/StructuredRankOneFamily
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/StructuredRankOneFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous structured downdates on a finitely punctured open simplex have constant pivot sign and a fixed negative index. -/

import D5.S3.QuadraticForms.StructuredRankOneInertia
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Connected.Clopen

/-!
The original open-simplex-minus-finite-points domain is transported through its
explicit log-ratio chart. The matrix result uses Lucid's proposed congruence
mechanism from https://mathoverflow.net/revisions/513954/2 (CC BY-SA 4.0).
-/

noncomputable section
open Matrix Set
open scoped BigOperators
set_option autoImplicit false

namespace D5.S3.QuadraticForms.StructuredRankOneFamily
open D5.S3.QuadraticForms.StructuredRankOneInertia
open RHLinalg

/-- The open m-simplex in independent barycentric coordinates; the last coordinate is one minus their sum. -/
def openSimplex (m : ℕ) : Set (Fin m → ℝ) :=
  {u | (∀ i, 0 < u i) ∧ ∑ i, u i < 1}

private def chartDenom {m : ℕ} (t : Fin m → ℝ) : ℝ := 1 + ∑ i, Real.exp (t i)

private theorem chartDenom_pos {m : ℕ} (t : Fin m → ℝ) : 0 < chartDenom t := by
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (Real.exp_pos (t i)).le)
  dsimp [chartDenom]
  linarith

private def simplexChart (m : ℕ) : (Fin m → ℝ) ≃ₜ openSimplex m where
  toFun t := ⟨fun i => Real.exp (t i) / chartDenom t, by
    constructor
    · intro i; exact div_pos (Real.exp_pos _) (chartDenom_pos t)
    · rw [← Finset.sum_div, div_lt_one (chartDenom_pos t)]
      simp only [chartDenom]; linarith⟩
  invFun u := fun i => Real.log (u.val i / (1 - ∑ j, u.val j))
  left_inv t := by
    ext i
    have hc := chartDenom_pos t
    have hs : 1 - ∑ j, Real.exp (t j) / chartDenom t = 1 / chartDenom t := by
      rw [← Finset.sum_div]
      dsimp [chartDenom] at *
      field_simp
      <;> ring
    change Real.log ((Real.exp (t i) / chartDenom t) /
      (1 - ∑ j, Real.exp (t j) / chartDenom t)) = t i
    rw [hs]
    have hh : Real.exp (t i) / chartDenom t / (1 / chartDenom t) = Real.exp (t i) := by
      field_simp
    rw [hh, Real.log_exp]
  right_inv u := by
    apply Subtype.ext
    ext i
    have hu : 0 < 1 - ∑ j, u.val j := sub_pos.mpr u.property.2
    have he : ∀ j, Real.exp (Real.log (u.val j / (1 - ∑ k, u.val k))) =
        u.val j / (1 - ∑ k, u.val k) := fun j => Real.exp_log (div_pos (u.property.1 j) hu)
    change Real.exp (Real.log (u.val i / (1 - ∑ j, u.val j))) /
      (1 + ∑ k, Real.exp (Real.log (u.val k / (1 - ∑ j, u.val j)))) = u.val i
    simp only [he]
    rw [← Finset.sum_div]
    field_simp
    <;> ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply (Real.continuous_exp.comp (continuous_apply i)).div
    · exact continuous_const.add (continuous_finset_sum _ fun j _ => Real.continuous_exp.comp (continuous_apply j))
    · intro t; exact (chartDenom_pos t).ne'
  continuous_invFun := by
    apply continuous_pi
    intro i
    apply Continuous.log
    · apply ((continuous_apply i).comp continuous_subtype_val).div
      · exact continuous_const.sub (continuous_finset_sum _ fun j _ =>
          (continuous_apply j).comp continuous_subtype_val)
      · intro u; exact (sub_pos.mpr u.property.2).ne'
    · intro u; exact (div_pos (u.property.1 i) (sub_pos.mpr u.property.2)).ne'

/-- Finite punctures leave the original simplex model nonempty and path connected. -/
theorem punctured_simplex_pathConnected {n : ℕ} (hn : 3 ≤ n)
    {X : Type*} [TopologicalSpace X] (e : X ≃ₜ openSimplex (n - 1))
    (A : Set X) (hA : A.Finite) : IsPathConnected Aᶜ := by
  let h := e.trans (simplexChart (n - 1)).symm
  have hd : 1 < Module.rank ℝ (Fin (n - 1) → ℝ) := by
    rw [← Module.finrank_eq_rank]
    simp only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
    exact_mod_cast (show 1 < n - 1 by omega)
  have hc := (hA.image h).countable.isPathConnected_compl_of_one_lt_rank hd
  have hp := (h.isPathConnected_preimage).mpr hc
  simpa only [preimage_compl, Set.preimage_image_eq _ h.injective] using hp

/-- The source-domain continuous-family corollary, including a globally unique negative index. -/
theorem continuous_family {n : ℕ} (hn : 3 ≤ n)
    {X : Type} [TopologicalSpace X] (e : X ≃ₜ openSimplex (n - 1))
    (A : Set X) (hA : A.Finite)
    (d x : ↥(Aᶜ : Set X) → (Fin n → ℝ)) (hd : Continuous d) (hx : Continuous x)
    (hdelta : ∀ y, pivot (diagonal (d y)) (x y) ≠ 0)
    (hpsd : ∀ y, (downdate (diagonal (d y)) (x y)).PosSemidef) :
    Aᶜ.Nonempty ∧
      ((∀ y, 0 < pivot (diagonal (d y)) (x y)) ∨
        ((∀ y, pivot (diagonal (d y)) (x y) < 0) ∧
          ∃! j : Fin n, (∀ y, d y j < 0) ∧ (∀ i, i ≠ j → ∀ y, 0 ≤ d y i))) := by
  classical
  have hpath := punctured_simplex_pathConnected hn e A hA
  have hconn := hpath.isConnected
  letI : ConnectedSpace ↥(Aᶜ : Set X) := isConnected_iff_connectedSpace.mp hconn
  have hcont : Continuous (fun y => pivot (diagonal (d y)) (x y)) := by
    change Continuous (fun y => ∑ i, x y i * (diagonal (d y) *ᵥ x y) i)
    simp only [mulVec_diagonal, Pi.mul_apply]
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp hx).mul
        (((continuous_apply i).comp hd).mul ((continuous_apply i).comp hx))
  refine ⟨hconn.nonempty, ?_⟩
  have hs := isPreconnected_univ.mapsTo_Ioi_or_Iio hcont.continuousOn
    (fun y _ => hdelta y)
  rcases hs with hp | hn'
  · exact Or.inl (fun y => hp (Set.mem_univ y))
  · right
    have hnegative : ∀ y, pivot (diagonal (d y)) (x y) < 0 :=
      fun y => hn' (Set.mem_univ y)
    refine ⟨hnegative, ?_⟩
    have hone : ∀ y, ∃! i : Fin n, d y i < 0 := by
      intro y
      obtain ⟨hM, _, hneg⟩ := inertia_downdate (diagonal (d y))
        (isHermitian_diagonal _) (x y) (hdelta y)
      have hi := (hneg (hnegative y)).2.1
      have hr := RHLinalg.posIndex_eq_rank_of_posSemidef (hpsd y)
      have hpn := D5.S3.SpectralTopology.PointGapExactInertia.posIndex_add_negIndex_eq_rank
        (hpsd y).isHermitian
      have hcount := (diagonal_counts (d y)).2
      have hzero : negIndex hM = 0 := by omega
      have hc : (Finset.univ.filter fun i => d y i < 0).card = 1 := by omega
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
      have hall : ∀ j, d y j < 0 ↔ j = i := by
        intro j
        simpa using Finset.ext_iff.mp hi j
      exact ⟨i, (hall i).mpr rfl, fun j hj => (hall j).mp hj⟩
    obtain ⟨y0, hy0⟩ := hconn.nonempty
    obtain ⟨j, hj, hjunique⟩ := hone ⟨y0, hy0⟩
    have hopen : ∀ i : Fin n, IsOpen {y : ↥(Aᶜ : Set X) | d y i < 0} := by
      intro i
      exact isOpen_lt ((continuous_apply i).comp hd) continuous_const
    have hcompl : {y : ↥(Aᶜ : Set X) | d y j < 0}ᶜ =
        ⋃ (i : Fin n) (_ : i ≠ j), {y : ↥(Aᶜ : Set X) | d y i < 0} := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      constructor
      · intro hnj
        obtain ⟨i, hi, _⟩ := hone y
        exact ⟨i, fun heq => hnj (heq ▸ hi), hi⟩
      · rintro ⟨i, hij, hi⟩ hj'
        obtain ⟨k, _, hu⟩ := hone y
        exact hij ((hu i hi).trans (hu j hj').symm)
    have hclosed : IsClosed {y : ↥(Aᶜ : Set X) | d y j < 0} := by
      rw [← isOpen_compl_iff, hcompl]
      exact isOpen_iUnion fun i => isOpen_iUnion fun _ => hopen i
    have hevery : {y : ↥(Aᶜ : Set X) | d y j < 0} = Set.univ :=
      (show IsClopen {y : ↥(Aᶜ : Set X) | d y j < 0} from ⟨hclosed, hopen j⟩).eq_univ
        ⟨⟨y0, hy0⟩, hj⟩
    have hjall : ∀ y, d y j < 0 := by
      intro y
      have hm := Set.mem_univ y
      rwa [← hevery] at hm
    refine ⟨j, ⟨hjall, ?_⟩, ?_⟩
    · intro i hij y
      by_contra hi
      have hi' : d y i < 0 := lt_of_not_ge hi
      obtain ⟨k, _, hu⟩ := hone y
      exact hij ((hu i hi').trans (hu j (hjall y)).symm)
    · intro k hk
      exact hjunique k (hk.1 ⟨y0, hy0⟩)

/-- The complete revision-2 source statement: both inertia triples and the original-domain corollary. -/
theorem mo513954_revision2 :
    (∀ (n : ℕ) (d x : Fin n → ℝ), pivot (diagonal d) x ≠ 0 →
      ∃ hM : (downdate (diagonal d) x).IsHermitian,
        (0 < pivot (diagonal d) x →
          posIndex (isHermitian_diagonal d) = posIndex hM + 1 ∧
          negIndex hM = negIndex (isHermitian_diagonal d) ∧
          zeroIndex hM = zeroIndex (isHermitian_diagonal d) + 1) ∧
        (pivot (diagonal d) x < 0 →
          posIndex hM = posIndex (isHermitian_diagonal d) ∧
          negIndex (isHermitian_diagonal d) = negIndex hM + 1 ∧
          zeroIndex hM = zeroIndex (isHermitian_diagonal d) + 1)) ∧
    (∀ (n : ℕ) (_hn : 3 ≤ n) (X : Type) [TopologicalSpace X]
      (e : X ≃ₜ openSimplex (n - 1)) (A : Set X), A.Finite →
      ∀ (d x : ↥(Aᶜ : Set X) → (Fin n → ℝ)), Continuous d → Continuous x →
      (∀ y, pivot (diagonal (d y)) (x y) ≠ 0) →
      (∀ y, (downdate (diagonal (d y)) (x y)).PosSemidef) →
        Aᶜ.Nonempty ∧
          ((∀ y, 0 < pivot (diagonal (d y)) (x y)) ∨
            ((∀ y, pivot (diagonal (d y)) (x y) < 0) ∧
              ∃! j : Fin n, (∀ y, d y j < 0) ∧ (∀ i, i ≠ j → ∀ y, 0 ≤ d y i)))) := by
  constructor
  · intro n d x h
    exact inertia_downdate (diagonal d) (isHermitian_diagonal d) x h
  · intro n hn X _ e A hA d x hd hx hdelta hpsd
    exact continuous_family hn e A hA d x hd hx hdelta hpsd

#print axioms mo513954_revision2
#print axioms punctured_simplex_pathConnected
#print axioms continuous_family

end D5.S3.QuadraticForms.StructuredRankOneFamily
