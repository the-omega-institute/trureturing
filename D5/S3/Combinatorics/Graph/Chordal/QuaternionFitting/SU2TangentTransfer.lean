/- GID: D5/S3/Combinatorics/Graph/Chordal/QuaternionFitting/SU2TangentTransfer
   generality: G
   mirror-B: none(waiver:covered-by-su2-tangent-lower-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-graph first-order transfer with unrestricted ambient potentials. -/

import D5.S3.Geometry.UnitQuaternions.SU2TangentGeometry
import D5.S3.Combinatorics.Graph.Chordal.QuaternionFitting.SU2TangentFitClosure
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Omega original.

Fixed-graph first-order transfer with unrestricted ambient potentials. -/

noncomputable section
open scoped Quaternion InnerProductSpace Topology BigOperators
open Filter
namespace SimpleGraph.SU2Tangent

open Omega.Geometry.UnitQuaternion

variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- A coefficient for all positive-defect-bound round SU(2) assignments on this graph.
The potential ranges over the full unit-quaternion group. -/
def RoundUpper (G : SimpleGraph V) (C : ℝ) : Prop :=
  ∀ (g : V → V → U) (δ : ℝ), 0 < δ →
    (∀ u v, G.Adj u v → g v u = (g u v)⁻¹) →
    (∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w →
      roundDist (g u v * g v w) (g u w) ≤ δ) →
    ∃ p : V → U, ∀ u v, G.Adj u v →
      roundDist (g u v) ((p u)⁻¹ * p v) ≤ C * δ

omit [Finite V] in
/-- Ambient edge displacement along any fixed finite walk. -/
theorem walk_bound {a b : V} (w : G.Walk a b) (p : V → ℍ[ℝ]) {B : ℝ}
    (hp : ∀ u v, G.Adj u v → ‖p v - p u‖ ≤ B) :
    ‖p b - p a‖ ≤ w.length * B := by
  induction w with
  | nil => simp
  | @cons a c b hac w ih =>
    have he : p b - p a = (p b - p c) + (p c - p a) := by abel
    rw [he]
    apply (norm_add_le _ _).trans
    simp only [Walk.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith [hp a c hac]

/-- A finite connected graph supplies a uniform path-length bound from a root. -/
theorem exists_path_bound (hG : G.Connected) (o : V) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ v, ∃ w : G.Walk o v, (w.length : ℝ) ≤ D := by
  classical
  let := Fintype.ofFinite V
  let w (v : V) : G.Walk o v := (hG.preconnected o v).some
  refine ⟨∑ v, ((w v).length : ℝ), by positivity, fun v => ⟨w v, ?_⟩⟩
  exact Finset.single_le_sum (f := fun i => ((w i).length : ℝ))
    (fun i _ => by positivity) (Finset.mem_univ v)

/-- The algebraic comparison uses normalized ambient differences of arbitrary
potentials. No assumption that a potential is exponential is needed. -/
theorem ambient_residual_bound (a p q : ℍ[ℝ]) (g : U) {t r M B η : ℝ}
    (ht : 0 < t) (_hM : 0 ≤ M) (hB : 0 ≤ B)
    (ha : ‖a - t⁻¹ • ((g : ℍ[ℝ]) - 1)‖ ≤ η)
    (hg : ‖(g : ℍ[ℝ]) - 1‖ ≤ t * M)
    (hp : ‖p - 1‖ ≤ B)
    (hr : ‖p * (g : ℍ[ℝ]) - q‖ ≤ t * r) :
    ‖a - (t⁻¹ • (q - 1) - t⁻¹ • (p - 1))‖ ≤ η + B * M + r := by
  have he : a - (t⁻¹ • (q - 1) - t⁻¹ • (p - 1)) =
      (a - t⁻¹ • ((g : ℍ[ℝ]) - 1)) +
      t⁻¹ • ((1 - p) * ((g : ℍ[ℝ]) - 1)) + t⁻¹ • (p * g - q) := by
    simp only [sub_mul, one_mul, mul_sub, mul_one]
    module
  rw [he]
  have hcross : ‖t⁻¹ • ((1 - p) * ((g : ℍ[ℝ]) - 1))‖ ≤ B * M := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, norm_mul, norm_sub_rev 1 p]
    calc
      _ ≤ t⁻¹ * (B * (t * M)) := mul_le_mul_of_nonneg_left
        (mul_le_mul hp hg (norm_nonneg _) hB) (inv_nonneg.mpr ht.le)
      _ = B * M := by field_simp
  have herr : ‖t⁻¹ • (p * (g : ℍ[ℝ]) - q)‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr ht.le)).trans_eq
      (by field_simp)
  exact (norm_add_le _ _).trans ((add_le_add
    ((norm_add_le _ _).trans (add_le_add ha hcross)) herr))

/-- Fixed-graph tangent transfer for any differentiable unit-quaternion gains.
The hypotheses express first-order triangle and edge behavior only. -/
theorem transfer_of_first_order (hG : G.Connected) {C : ℝ} (hC : 0 ≤ C)
    (hupper : RoundUpper G C) (a : V → V → ℍ[ℝ])
    (g : ℝ → V → V → U) {M : ℝ} (hM : 0 ≤ M)
    (hrev : ∀ t u v, G.Adj u v → g t v u = (g t u v)⁻¹)
    (hedge : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ u v,
      ‖(g t u v : ℍ[ℝ]) - 1‖ ≤ t * M)
    (hslope : ∀ u v, Tendsto (fun t : ℝ =>
      t⁻¹ • ((g t u v : ℍ[ℝ]) - 1)) (𝓝[>] 0) (𝓝 (a u v)))
    (htriangle : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w →
      ∀ η : ℝ, 0 < η → ∀ᶠ t in 𝓝[>] (0 : ℝ),
        roundDist (g t u v * g t v w) (g t u w) ≤ t * (1 + η)) :
    ∃ p : V → ℍ[ℝ], ∀ u v, G.Adj u v → ‖a u v - (p v - p u)‖ ≤ C := by
  classical
  let := Fintype.ofFinite V
  have : Nonempty V := hG.nonempty
  let o : V := Classical.choice inferInstance
  obtain ⟨D, hD, hpath⟩ := exists_path_bound hG o
  apply SimpleGraph.exists_gain_fit_of_forall_pos G a hC
  intro ζ hζ
  let η := min 1 (ζ / (C + 2))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hζ (by linarith))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηζ : (C + 2) * η ≤ ζ := by
    have hh := min_le_right (1 : ℝ) (ζ / (C + 2))
    exact (mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ C + 2)).trans_eq
      (by field_simp)
  let K := M + 2 * C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ u v,
      ‖a u v - t⁻¹ • ((g t u v : ℍ[ℝ]) - 1)‖ ≤ η := by
    apply eventually_all.mpr
    intro u
    apply eventually_all.mpr
    intro v
    have hh := ((hslope u v).sub (tendsto_const_nhds (x := a u v))).norm
    simp only [sub_self, norm_zero] at hh
    have he := hh.eventually (gt_mem_nhds hη)
    simpa only [sub_self, norm_zero, norm_sub_rev] using he.mono fun t ht => ht.le
  have htri : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ u v w,
      G.Adj u v → G.Adj v w → G.Adj u w →
      roundDist (g t u v * g t v w) (g t u w) ≤ t * (1 + η) := by
    simp only [eventually_all]
    exact fun u v w huv hvw huw => htriangle u v w huv hvw huw η hη
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t * D * K * M ≤ η := by
    have hh : Tendsto (fun t : ℝ => t * D * K * M) (𝓝[>] 0) (𝓝 0) := by
      have htend : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      simpa using ((htend.mul_const D).mul_const K).mul_const M
    exact (hh.eventually (gt_mem_nhds hη)).mono fun _ h => h.le
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, he, hs, htri, hsmall⟩ :=
    (hpos.and (hedge.and (hs.and (htri.and hsmall)))).exists
  have ht : 0 < t := ht
  obtain ⟨p, hp⟩ := hupper (g t) (t * (1 + η)) (by positivity) (hrev t) htri
  let P (v : V) : U := (p o)⁻¹ * p v
  have hP : ∀ u v, G.Adj u v → roundDist (g t u v) ((P u)⁻¹ * P v) ≤ C * (t * (1 + η)) := by
    intro u v huv
    convert hp u v huv using 1
    dsimp [P]
    group
  have hpedge : ∀ u v, G.Adj u v →
      ‖(P u : ℍ[ℝ]) * g t u v - P v‖ ≤ t * (C * (1 + η)) := by
    intro u v huv
    exact (chord_le_round (P u * g t u v) (P v)).trans
      (by simpa only [← round_edge, mul_assoc, mul_left_comm, mul_comm] using hP u v huv)
  have hstep : ∀ u v, G.Adj u v → ‖(P v : ℍ[ℝ]) - P u‖ ≤ t * K := by
    intro u v huv
    have heq : (P v : ℍ[ℝ]) - P u =
        ((P v : ℍ[ℝ]) - (P u : ℍ[ℝ]) * g t u v) +
          (P u : ℍ[ℝ]) * ((g t u v : ℍ[ℝ]) - 1) := by noncomm_ring
    rw [heq]
    have hh := hpedge u v huv
    rw [norm_sub_rev] at hh
    have hn : ‖(P u : ℍ[ℝ]) * ((g t u v : ℍ[ℝ]) - 1)‖ ≤ t * M := by
      simpa only [norm_mul, norm_coe, one_mul] using he u v
    exact (norm_add_le _ _).trans (by
      dsimp [K]
      nlinarith [mul_nonneg (mul_nonneg ht.le hC) (sub_nonneg.mpr hη1)])
  have hroot : ∀ v, ‖(P v : ℍ[ℝ]) - 1‖ ≤ t * D * K := by
    intro v
    obtain ⟨w, hw⟩ := hpath v
    have hh := walk_bound w (fun v => (P v : ℍ[ℝ])) hstep
    have hPo : (P o : ℍ[ℝ]) = 1 := by simp [P]
    rw [hPo] at hh
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hw (mul_nonneg ht.le hK)])
  refine ⟨fun v => t⁻¹ • ((P v : ℍ[ℝ]) - 1), fun u v huv => ?_⟩
  have hh := ambient_residual_bound (a u v) (P u) (P v) (g t u v) ht hM
    (mul_nonneg (mul_nonneg ht.le hD) hK) (hs u v) (he u v) (hroot u)
    (hpedge u v huv)
  exact hh.trans (by nlinarith)


/-- Every round SU(2) coefficient on a fixed finite connected graph also fits
all normalized imaginary-quaternion cochains in the full ambient vector space. -/
theorem fixed_graph_pure_transfer (hG : G.Connected) {C : ℝ} (hC : 0 ≤ C)
    (hupper : RoundUpper G C) (a : V → V → ℍ[ℝ])
    (hpure : ∀ u v, (a u v).re = 0) (hrev : ∀ u v, a v u = -a u v)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w →
      ‖a u v + a v w - a u w‖ ≤ 1) :
    ∃ p : V → ℍ[ℝ], ∀ u v, G.Adj u v → ‖a u v - (p v - p u)‖ ≤ C := by
  classical
  let := Fintype.ofFinite V
  let g (t : ℝ) (u v : V) := curve (a u v) (hpure u v) t
  let M : ℝ := (∑ u, ∑ v, ‖a u v‖) + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbig (u v : V) : ‖a u v‖ < M := by
    have hh : ‖a u v‖ ≤ ∑ u, ∑ v, ‖a u v‖ := by
      exact (Finset.single_le_sum (fun i _ => norm_nonneg (a u i))
        (Finset.mem_univ v)).trans (Finset.single_le_sum
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg (a i j)) (Finset.mem_univ u))
    dsimp [M]
    linarith
  have hed : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ u v,
      ‖(g t u v : ℍ[ℝ]) - 1‖ ≤ t * M := by
    simp only [eventually_all]
    intro u v
    have hh := (curve_slope (a u v)).norm
    have he := hh.eventually (gt_mem_nhds (hbig u v))
    filter_upwards [he, self_mem_nhdsWithin] with t ht hpos
    have htpos : 0 < t := hpos
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htpos] at ht
    have hn := (mul_lt_mul_of_pos_left ht htpos).le
    simpa [g, mul_assoc, htpos.ne', mul_comm] using hn
  refine transfer_of_first_order hG hC hupper a g hM ?_ hed
    (fun u v => curve_slope (a u v)) ?_
  · intro t u v _
    dsimp [g]
    simpa only [hrev u v] using curve_neg (a u v) (hpure u v) t
  · intro u v w huv hvw huw η hη
    have hh := triangle_slope (a u v) (a v w) (a u w)
      (hpure u v) (hpure v w) (hpure u w)
    have he := hh.eventually (gt_mem_nhds (lt_of_le_of_lt (htri u v w huv hvw huw)
      (by linarith : (1 : ℝ) < 1 + η)))
    filter_upwards [he, self_mem_nhdsWithin] with t ht hpos
    exact (div_le_iff₀ (show 0 < t from hpos)).mp ht.le |>.trans_eq (by ring)

end SimpleGraph.SU2Tangent
