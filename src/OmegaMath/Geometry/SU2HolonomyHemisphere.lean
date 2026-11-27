import OmegaMath.Geometry.QuaternionicHermitianSpectrum
import OmegaMath.Geometry.SU2HolonomyMatrix
import OmegaMath.Geometry.SphericalJung

/-!
Omega original.

The first three holonomy moments exclude zero convex combinations of
unit-quaternion candidates beyond the diameter-only spherical Jung threshold.
-/

open scoped Quaternion InnerProductSpace BigOperators

namespace Omega.Geometry.HolonomySpectrum

open Omega.Geometry.UnitQuaternion Real

local notation "U" => unitary ℍ[ℝ]

/-- Five candidates satisfying both pair and triangle holonomy bounds cannot
have a zero convex combination at cosine threshold strictly above `9/16`. -/
theorem five_point_hemisphere {c : ℝ} (hc : 9 / 16 < c) (hc' : c ≤ 1)
    (q : Fin 5 → U) (g : HolonomyGains (Fin 5))
    (hedge : ∀ i j, i ≠ j → c ≤ (g.gain i j : ℍ[ℝ]).re)
    (hpoint : ∀ i j, i ≠ j → c ≤ (↑((q i)⁻¹ * g.gain i j * q j) : ℍ[ℝ]).re)
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      c ≤ (↑(g.gain i j * g.gain j k * g.gain k i) : ℍ[ℝ]).re) :
    (0 : ℍ[ℝ]) ∉ convexHull ℝ (Set.range fun i => (q i : ℍ[ℝ])) := by
  intro hz
  obtain ⟨w, hw, hw₁, hwz⟩ := SphericalJung.exists_weights_of_mem_convexHull hz
  let M := holonomyMatrix g w
  let a := weightedColumn w (fun _ => (1 : U))
  let b := weightedColumn w q
  have han : ‖a‖ = 1 := norm_weightedColumn _ hw hw₁
  have hbn : ‖b‖ = 1 := norm_weightedColumn _ hw hw₁
  have hab : pairing a b = (0 : ℍ[ℝ]) := by
    rw [show pairing a b = pairing (weightedColumn w fun _ => (1 : U)) (weightedColumn w q) from rfl,
      pairing_weightedColumn _ _ hw]
    simpa using hwz
  obtain ⟨μ, hμ, e, he⟩ := exists_ordered_spectrum (isHermitian_holonomyMatrix g w)
  let ν : Fin 5 → ℝ := fun i => μ i
  have htop := rayleigh_two_unit_le (by simp : 2 ≤ Fintype.card (Fin 5)) M μ hμ e he a b han hbn
    (a := 0) le_rfl zero_lt_one (by exact hab)
  have htop' : ⟪a, realAction M a⟫_ℝ + ⟪b, realAction M b⟫_ℝ ≤ ν 0 + ν 1 := by
    simp only [add_zero, sub_zero, one_mul] at htop
    exact htop
  have hM₁ := spectrum_moments M e he 1
  have hM₂ := spectrum_moments M e he 2
  have hM₃ := spectrum_moments M e he 3
  have htrace₁ := holonomy_trace g hw
  have htrace₂ := holonomy_trace_sq g hw
  have htrace₃ := holonomy_trace_cube_lower g hw hw₁ htri
  have hm := simplex_moments w hw hw₁ (by simp)
  have hweight₁ : (1 / 5 : ℝ) ≤ ∑ i, w i ^ 2 := by
    simpa only [Fintype.card_fin, Nat.cast_ofNat] using hm.1
  have hweight₂ : (13 / 25 : ℝ) ≤ ∑ i, (3 * w i ^ 2 - 2 * w i ^ 3) := by
    have h := hm.2
    change (3 * (5 : ℝ) - 2) / 5 ^ 2 ≤ _ at h
    norm_num at h
    simpa only [Finset.sum_sub_distrib] using h
  have hnon : 0 ≤ 1 - c := sub_nonneg.mpr hc'
  have h₁ : ∑ i, ν i = 1 := by
    simp only [M, pow_one, htrace₁, hw₁] at hM₁
    exact hM₁
  have h₂ : ∑ i, ν i ^ 2 = 1 := by
    simp only [M, htrace₂, hw₁, one_pow] at hM₂
    exact hM₂
  have h₃ : (13 + 12 * c) / 25 ≤ ∑ i, ν i ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left hweight₂ hnon
    change (13 + 12 * c) / 25 ≤ ∑ i, μ i ^ 3
    rw [hM₃]
    change c + (1 - c) * (∑ i, (3 * w i ^ 2 - 2 * w i ^ 3)) ≤ _ at htrace₃
    linarith only [hm, htrace₃]
  let tail (i : Fin 3) : ℝ := ν i.succ.succ
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h₁ h₂ h₃
  have hfin : (0 : Fin 4).succ = 1 := by decide
  rw [hfin] at h₁ h₂ h₃
  have hlim := five_point_moment_obstruction (ν 0) (ν 1) tail hc
    (hμ (by decide : (0 : Fin 5) ≤ 1)) (fun i => hμ (by
      change 1 ≤ i.val + 2
      omega)) (by simpa only [tail, add_assoc] using h₁)
    (by simpa only [tail, add_assoc] using h₂) (by simpa only [tail, add_assoc] using h₃)
  have hr₁ := rayleigh_weightedColumn_lower g (fun _ => (1 : U)) hw hw₁
    (fun i j hij => by simpa using hedge i j hij)
  have hr₂ := rayleigh_weightedColumn_lower g q hw hw₁ hpoint
  change c + (1 - c) * (∑ i, w i ^ 2) ≤ ⟪a, realAction M a⟫_ℝ at hr₁
  change c + (1 - c) * (∑ i, w i ^ 2) ≤ ⟪b, realAction M b⟫_ℝ at hr₂
  have hmul := mul_le_mul_of_nonneg_left hweight₁ hnon
  linarith only [htop', hlim, hr₁, hr₂, hmul]


/-- A holonomy family can be restricted along any index map, including
repeated copies of a candidate used to pad a finite support. -/
def HolonomyGains.pullback {κ : Type*} (g : HolonomyGains ι) (f : κ → ι) :
    HolonomyGains κ where
  gain i j := g.gain (f i) (f j)
  diag i := g.diag (f i)
  flip i j := g.flip (f i) (f j)

private theorem fin_surjection {κ : Type*} [Fintype κ] [Nonempty κ] {n : ℕ}
    (h : Fintype.card κ ≤ n) : ∃ f : Fin n → κ, Function.Surjective f := by
  classical
  let e := Fintype.equivFin κ
  let f (i : Fin n) : κ := if hi : i.val < Fintype.card κ then e.symm ⟨i.val, hi⟩ else Classical.arbitrary κ
  refine ⟨f, fun x => ⟨Fin.castLE h (e x), ?_⟩⟩
  dsimp [f]
  split_ifs with hf
  · exact e.symm_apply_apply x
  · exact (hf (e x).isLt).elim

/-- Any finite holonomy family with cosine threshold strictly above `9/16`
lies in an open hemisphere. Carathéodory's theorem reduces a hypothetical
zero convex combination to a support of at most five candidates. -/
theorem holonomy_hemisphere {ι : Type*} [Fintype ι] {c : ℝ} (hc : 9 / 16 < c) (hc' : c ≤ 1)
    (q : ι → U) (g : HolonomyGains ι)
    (hedge : ∀ i j, i ≠ j → c ≤ (g.gain i j : ℍ[ℝ]).re)
    (hpoint : ∀ i j, i ≠ j → c ≤ (↑((q i)⁻¹ * g.gain i j * q j) : ℍ[ℝ]).re)
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      c ≤ (↑(g.gain i j * g.gain j k * g.gain k i) : ℍ[ℝ]).re) :
    (0 : ℍ[ℝ]) ∉ convexHull ℝ (Set.range fun i => (q i : ℍ[ℝ])) := by
  classical
  intro hz
  obtain ⟨κ, _, v, w, hv, hi, hw, hs, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hz
  have hne : Nonempty κ := by
    cases isEmpty_or_nonempty κ with
    | inl h =>
      let : IsEmpty κ := h
      simp at hs
    | inr h => exact h
  let : Nonempty κ := hne
  have hcard : Fintype.card κ ≤ 5 := by
    have hfin := hi.card_le_finrank_succ
    have hsub := Submodule.finrank_le (vectorSpan ℝ (Set.range v))
    rw [Quaternion.finrank_eq_four] at hsub
    omega
  choose j hj using fun k => hv (Set.mem_range_self k)
  obtain ⟨f, hf⟩ := fin_surjection hcard
  let Q : Fin 5 → U := q ∘ j ∘ f
  let G : HolonomyGains (Fin 5) := g.pullback (j ∘ f)
  have hq : Set.range (fun i => (Q i : ℍ[ℝ])) = Set.range v := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨f i, (hj (f i)).symm⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨i, rfl⟩ := hf k
      exact ⟨i, hj (f i)⟩
  have hz' : (0 : ℍ[ℝ]) ∈ convexHull ℝ (Set.range fun i => (Q i : ℍ[ℝ])) := by
    rw [hq]
    exact mem_convexHull_of_exists_fintype w v (fun i => (hw i).le) hs
      (fun i => Set.mem_range_self i) hsum
  have H₁ (i j' : Fin 5) (_ : i ≠ j') : c ≤ (G.gain i j' : ℍ[ℝ]).re := by
    change c ≤ (g.gain (j (f i)) (j (f j')) : ℍ[ℝ]).re
    rcases eq_or_ne (j (f i)) (j (f j')) with he | he
    · rw [he, g.diag]
      exact hc'
    · exact hedge _ _ he
  have H₂ (i j' : Fin 5) (_ : i ≠ j') :
      c ≤ (↑((Q i)⁻¹ * G.gain i j' * Q j') : ℍ[ℝ]).re := by
    change c ≤ (↑((q (j (f i)))⁻¹ * g.gain (j (f i)) (j (f j')) * q (j (f j'))) : ℍ[ℝ]).re
    rcases eq_or_ne (j (f i)) (j (f j')) with he | he
    · rw [he, g.diag, mul_one, inv_mul_cancel]
      exact hc'
    · exact hpoint _ _ he
  have H₃ (i j' k : Fin 5) (_ : i ≠ j') (_ : j' ≠ k) (_ : i ≠ k) :
      c ≤ (↑(G.gain i j' * G.gain j' k * G.gain k i) : ℍ[ℝ]).re := by
    change c ≤ (↑(g.gain (j (f i)) (j (f j')) * g.gain (j (f j')) (j (f k)) *
      g.gain (j (f k)) (j (f i))) : ℍ[ℝ]).re
    by_cases h : j (f i) = j (f j') ∨ j (f j') = j (f k) ∨ j (f i) = j (f k)
    · rw [cycle_gain_eq_one g h]
      exact hc'
    · push Not at h
      exact htri _ _ _ h.1 h.2.1 h.2.2
  exact five_point_hemisphere hc hc' Q G H₁ H₂ H₃ hz'


/-- A family of candidates, with its pair and triangle holonomy bounds. -/
structure SU2Patch (ι : Type*) (δ : ℝ) where
  point : ι → U
  holonomy : HolonomyGains ι
  edge : ∀ i j, i ≠ j → cos δ ≤ (holonomy.gain i j : ℍ[ℝ]).re
  aligned : ∀ i j, i ≠ j →
    cos δ ≤ (↑((point i)⁻¹ * holonomy.gain i j * point j) : ℍ[ℝ]).re
  triangle : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
    cos δ ≤ (↑(holonomy.gain i j * holonomy.gain j k * holonomy.gain k i) : ℍ[ℝ]).re

/-- The cap center is the normalization of a nonzero nearest point of the
convex hull of the candidates. -/
structure SU2Cap {ι : Type*} (q : ι → U) (r : ℝ) where
  center : U
  nearest : ℍ[ℝ]
  mem_hull : nearest ∈ convexHull ℝ (Set.range fun i => (q i : ℍ[ℝ]))
  pos : 0 < ‖nearest‖
  normalized : (center : ℍ[ℝ]) = ‖nearest‖⁻¹ • nearest
  support : ∀ i, ‖nearest‖ ^ 2 ≤ ⟪nearest, (q i : ℍ[ℝ])⟫_ℝ
  radius : ∀ i, roundDist (q i) center ≤ r

/-- A family may be right-translated without changing the holonomy witnesses. -/
def SU2Patch.rightTranslate {ι : Type*} {δ : ℝ} (P : SU2Patch ι δ) (u : U) :
    SU2Patch ι δ where
  point i := P.point i * u
  holonomy := P.holonomy
  edge := P.edge
  triangle := P.triangle
  aligned i j hij := by
    have h := P.aligned i j hij
    have he : (P.point i * u)⁻¹ * P.holonomy.gain i j * (P.point j * u) =
        u⁻¹ * ((P.point i)⁻¹ * P.holonomy.gain i j * P.point j) * u := by group
    rw [he]
    let x := (P.point i)⁻¹ * P.holonomy.gain i j * P.point j
    change cos δ ≤ (((↑u⁻¹ : ℍ[ℝ]) * (x : ℍ[ℝ])) * (u : ℍ[ℝ])).re
    have hu : (u : ℍ[ℝ]) * (↑u⁻¹ : ℍ[ℝ]) = 1 :=
      congrArg (fun v : U => (v : ℍ[ℝ])) (mul_inv_cancel u)
    rw [re_mul_cycle, ← mul_assoc, hu, one_mul]
    exact h


theorem roundDist_re_iff (x : U) {s : ℝ} (hs : 0 ≤ s) (hπ : s ≤ π) :
    roundDist x 1 ≤ s ↔ cos s ≤ (x : ℍ[ℝ]).re := by
  rw [round_le_iff x 1 hs hπ]
  change cos s ≤ ((x : ℍ[ℝ]) * star (1 : ℍ[ℝ])).re ↔ _
  simp

theorem SU2Patch.diameter {ι : Type*} {δ : ℝ} (P : SU2Patch ι δ)
    (hδ : 0 ≤ δ) (hδπ : δ ≤ π) (i j : ι) (hij : i ≠ j) :
    roundDist (P.point i) (P.point j) ≤ 2 * δ := by
  have h₁ := (roundDist_re_iff _ hδ hδπ).mpr (P.edge i j hij)
  have h₂ := (roundDist_re_iff _ hδ hδπ).mpr (P.aligned i j hij)
  rw [← round_mul_right (P.point j), one_mul] at h₁
  rw [← round_mul_left (P.point i)] at h₂
  simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h₂
  rw [round_comm] at h₂
  exact (round_triangle _ _ _).trans (by linarith only [h₁, h₂])

theorem SU2Patch.zero_not_mem {ι : Type*} [Fintype ι] {δ : ℝ} (P : SU2Patch ι δ)
    (hc : 9 / 16 < cos δ) : (0 : ℍ[ℝ]) ∉ convexHull ℝ (Set.range fun i => (P.point i : ℍ[ℝ])) :=
  holonomy_hemisphere hc (cos_le_one _) P.point P.holonomy P.edge P.aligned P.triangle

theorem SU2Cap.of_nearest {ι : Type*} {q : ι → U} {r : ℝ}
    (hr : 0 ≤ r) (hrπ : r ≤ π) (z : ℍ[ℝ])
    (hz : z ∈ convexHull ℝ (Set.range fun i => (q i : ℍ[ℝ])))
    (hpos : 0 < ‖z‖) (hR : cos r ≤ ‖z‖)
    (hs : ∀ i, ‖z‖ ^ 2 ≤ ⟪z, (q i : ℍ[ℝ])⟫_ℝ) :
    Nonempty (SU2Cap q r) := by
  have hn : ‖‖z‖⁻¹ • z‖ = 1 := by simp [norm_smul, hpos.ne']
  refine ⟨⟨ofUnit (‖z‖⁻¹ • z) hn, z, hz, hpos, rfl, hs, fun i => ?_⟩⟩
  apply (round_le_iff _ _ hr hrπ).mpr
  rw [coe_ofUnit, real_inner_comm, real_inner_smul_left, ← div_eq_inv_mul, le_div_iff₀ hpos]
  exact (mul_le_mul_of_nonneg_right hR hpos.le).trans (by simpa [pow_two] using hs i)

/-- The classical four-point spherical Jung cap for a holonomy family. -/
theorem SU2Patch.exists_jung_cap {ι : Type*} [Fintype ι] [Nonempty ι] {δ r : ℝ}
    (P : SU2Patch ι δ) (hδ : 0 ≤ δ) (hδπ : δ ≤ π / 2)
    (hc : 9 / 16 < cos δ) (hr : 0 ≤ r) (hrπ : r ≤ π)
    (hR : cos r ≤ √(cos (2 * δ) + (1 - cos (2 * δ)) / 4)) : Nonempty (SU2Cap P.point r) := by
  let q (i : ι) := (P.point i : ℍ[ℝ])
  have hpair (i j : ι) (hij : i ≠ j) : cos (2 * δ) ≤ ⟪q i, q j⟫_ℝ :=
    (round_le_iff _ _ (by linarith) (by linarith)).mp (P.diameter hδ (by linarith [pi_pos]) i j hij)
  have hz₀ := P.zero_not_mem hc
  obtain ⟨z, hz, hsupport⟩ := SphericalJung.exists_min_norm_support q
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr (fun h => hz₀ (h ▸ hz))
  obtain ⟨v, hv, hcap⟩ := SphericalJung.exists_cap q 4 (by decide)
    (.inr (by rw [Quaternion.finrank_eq_four])) (fun _ => norm_coe _) (cos_le_one _) hpair hz₀
  obtain ⟨w, hw, hw₁, hwz⟩ := SphericalJung.exists_weights_of_mem_convexHull hz
  have hi : cos r ≤ ⟪v, z⟫_ℝ := by
    rw [← hwz, inner_sum]
    simp only [real_inner_smul_right]
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => mul_le_mul_of_nonneg_left (hR.trans (hcap i)) (hw i))
    simpa only [← Finset.sum_mul, hw₁, one_mul] using h
  have hn := real_inner_le_norm v z
  rw [hv, one_mul] at hn
  exact SU2Cap.of_nearest hr hrπ z hz hp (hi.trans hn) hsupport


/-- The normalized mean has projection at least `cos(R + δ)` on the
second cap center after translating the first family. -/
theorem cap_projection {ι κ : Type*} [Fintype ι] {q : ι → U} {v : κ → U}
    {R δ : ℝ} (C : SU2Cap q R) (D : SU2Cap v R) (e : ι → κ) (u : U)
    (hδ : 0 ≤ δ) (hR : 0 ≤ R) (hπ : R + δ ≤ π)
    (h : ∀ i, roundDist (q i * u) (v (e i)) ≤ δ) :
    cos (R + δ) ≤ ‖C.nearest‖ * cos (roundDist (C.center * u) D.center) := by
  obtain ⟨w, hw, hsum, hwz⟩ := SphericalJung.exists_weights_of_mem_convexHull C.mem_hull
  have hmean : ‖C.nearest‖ • (C.center : ℍ[ℝ]) = C.nearest := by
    rw [C.normalized, smul_smul, mul_inv_cancel₀ C.pos.ne', one_smul]
  have hvec : ‖C.nearest‖ • (↑(C.center * u) : ℍ[ℝ]) =
      ∑ i, w i • (↑(q i * u) : ℍ[ℝ]) := by
    change ‖C.nearest‖ • ((C.center : ℍ[ℝ]) * (u : ℍ[ℝ])) =
      ∑ i, w i • ((q i : ℍ[ℝ]) * (u : ℍ[ℝ]))
    simp only [← smul_mul_assoc, ← Finset.sum_mul, hwz, hmean]
  have hp (i : ι) : cos (R + δ) ≤ ⟪(↑(q i * u) : ℍ[ℝ]), (D.center : ℍ[ℝ])⟫_ℝ :=
    (round_le_iff _ _ (add_nonneg hR hδ) hπ).mp
      ((round_triangle _ _ _).trans (by linarith only [h i, D.radius (e i)]))
  have hlow := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonneg_left (hp i) (hw i))
  simp only [← Finset.sum_mul, hsum, one_mul, ← real_inner_smul_left, ← sum_inner,
    ← hvec] at hlow
  rw [real_inner_smul_left] at hlow
  have hangle :
      cos (roundDist (C.center * u) D.center) = ⟪(↑(C.center * u) : ℍ[ℝ]), (D.center : ℍ[ℝ])⟫_ℝ := by
    unfold roundDist
    have hb := real_inner_mem_Icc_of_norm_eq_one (norm_coe (C.center * u)) (norm_coe D.center)
    exact cos_arccos hb.1 hb.2
  rwa [hangle]

/-- The nearest point of the convex hull of unit vectors has norm at most one. -/
theorem SU2Cap.nearest_norm_le_one {ι : Type*} [Fintype ι] {q : ι → U} {R : ℝ}
    (C : SU2Cap q R) : ‖C.nearest‖ ≤ 1 := by
  obtain ⟨w, hw, hsum, hwz⟩ := SphericalJung.exists_weights_of_mem_convexHull C.mem_hull
  rw [← hwz]
  refine (norm_sum_le _ _).trans_eq ?_
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw _), norm_coe, mul_one, hsum]

theorem SU2Cap.cos_radius_le_nearest_norm {ι : Type*} [Fintype ι] {q : ι → U}
    {R : ℝ} (C : SU2Cap q R) (hR : 0 ≤ R) (hπ : R ≤ π) : cos R ≤ ‖C.nearest‖ := by
  obtain ⟨w, hw, hsum, hwz⟩ := SphericalJung.exists_weights_of_mem_convexHull C.mem_hull
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left ((round_le_iff _ _ hR hπ).mp (C.radius i)) (hw i))
  simp only [← Finset.sum_mul, hsum, one_mul, ← real_inner_smul_left, ← sum_inner, hwz] at h
  rw [C.normalized, real_inner_smul_right, real_inner_self_eq_norm_sq, pow_two,
    ← mul_assoc, inv_mul_cancel₀ C.pos.ne', one_mul] at h
  exact h


/-- Any restriction of a patch inherits its holonomy, including diagrams with
repeated indices. -/
def SU2Patch.pullback {ι κ : Type*} {δ : ℝ} (P : SU2Patch ι δ) (f : κ → ι) :
    SU2Patch κ δ where
  point i := P.point (f i)
  holonomy := P.holonomy.pullback f
  edge i j _ := by
    change cos δ ≤ (P.holonomy.gain (f i) (f j) : ℍ[ℝ]).re
    rcases eq_or_ne (f i) (f j) with he | he
    · rw [he, P.holonomy.diag]
      exact cos_le_one _
    · exact P.edge _ _ he
  aligned i j _ := by
    change cos δ ≤ (↑((P.point (f i))⁻¹ * P.holonomy.gain (f i) (f j) * P.point (f j)) : ℍ[ℝ]).re
    rcases eq_or_ne (f i) (f j) with he | he
    · rw [he, P.holonomy.diag, mul_one, inv_mul_cancel]
      exact cos_le_one _
    · exact P.aligned _ _ he
  triangle i j k _ _ _ := by
    change cos δ ≤ (↑(P.holonomy.gain (f i) (f j) * P.holonomy.gain (f j) (f k) *
      P.holonomy.gain (f k) (f i)) : ℍ[ℝ]).re
    by_cases h : f i = f j ∨ f j = f k ∨ f i = f k
    · rw [cycle_gain_eq_one P.holonomy h]
      exact cos_le_one _
    · push Not at h
      exact P.triangle _ _ _ h.1 h.2.1 h.2.2

/-- In four real dimensions the supporting affine hyperplane of a nonzero
nearest point needs at most four candidates. -/
theorem exists_contact_fin_four {ι : Type*} [Fintype ι] {q : ι → U} {z : ℍ[ℝ]}
    (hm : z ∈ convexHull ℝ (Set.range fun i => (q i : ℍ[ℝ]))) (hpos : 0 < ‖z‖)
    (hsupport : ∀ i, ‖z‖ ^ 2 ≤ ⟪z, (q i : ℍ[ℝ])⟫_ℝ) :
    ∃ (f : Fin 4 → ι) (w : Fin 4 → ℝ), (∀ i, 0 ≤ w i) ∧
      (∑ i, w i = 1) ∧ (∑ i, w i • (q (f i) : ℍ[ℝ])) = z := by
  obtain ⟨κ, hκ, f, w, hcard, hw, hs, hsum⟩ :=
    SphericalJung.exists_contact_weights hm (norm_pos_iff.mp hpos) hsupport
  letI : Fintype κ := hκ
  have hne : Nonempty κ := by
    cases isEmpty_or_nonempty κ with
    | inl h =>
      let : IsEmpty κ := h
      simp at hs
    | inr h => exact h
  let : Nonempty κ := hne
  rw [Quaternion.finrank_eq_four] at hcard
  obtain ⟨j, hj⟩ := fin_surjection hcard
  have hrange : Set.range (fun i => (q (f (j i)) : ℍ[ℝ])) =
      Set.range (fun i => (q (f i) : ℍ[ℝ])) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨j i, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨k, rfl⟩ := hj i
      exact ⟨k, rfl⟩
  have hz : z ∈ convexHull ℝ (Set.range (fun i => (q (f (j i)) : ℍ[ℝ]))) := by
    rw [hrange]
    exact mem_convexHull_of_exists_fintype w _ (fun i => (hw i).le) hs
      (fun i => Set.mem_range_self i) hsum
  obtain ⟨v, hv, h, hvz⟩ := SphericalJung.exists_weights_of_mem_convexHull hz
  exact ⟨f ∘ j, v, hv, h, hvz⟩

end Omega.Geometry.HolonomySpectrum
