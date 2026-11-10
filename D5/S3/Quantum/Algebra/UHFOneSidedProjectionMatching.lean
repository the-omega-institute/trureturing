/- GID: D5/S3/Quantum/Algebra/UHFOneSidedProjectionMatching
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/UHFOneSidedProjectionMatching
   mirror-E: none(waiver:intrinsic-algebraic-supplier)
   anchors: []
   utility: none
   digest: Finite-stage localization and one-sided matching of actual completed algebra projections. -/

import D5.S3.Quantum.Analysis.RussoDye
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-! Actual matrix ranges and projection localization in the completed algebra. -/

namespace D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching

open scoped Matrix.Norms.L2Operator
open Matrix

variable {C : Type*} [CStarAlgebra C]

/-- Actual unital full-matrix ranges, increasing and norm dense in the completed algebra.
No growth, parity, trace, localization, or matching condition is part of these data. -/
structure FullMatrixModel (C : Type*) [CStarAlgebra C] where
  size : ℕ → ℕ
  embed : (n : ℕ) → Matrix (Fin (size n)) (Fin (size n)) ℂ →⋆ₐ[ℂ] C
  injective : ∀ n, Function.Injective (embed n)
  increasing : ∀ n N, n ≤ N → Set.range (embed n) ⊆ Set.range (embed N)
  dense : Dense (⋃ n, Set.range (embed n))

private theorem close_projections_unitary {p q : C}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hclose : ‖p - q‖ < 1) :
    ∃ u : unitary C, (u : C) * p * star (u : C) = q := by
  let _ := CStarAlgebra.spectralOrder C
  let _ := CStarAlgebra.spectralOrderedRing C
  let x := q * p + (1 - q) * (1 - p)
  have hpp := hp.isIdempotentElem.eq
  have hqq := hq.isIdempotentElem.eq
  have hppA (a : C) : p * (p * a) = p * a := by rw [← mul_assoc, hpp]
  have hqqA (a : C) : q * (q * a) = q * a := by rw [← mul_assoc, hqq]
  have hs : p + p - 1 ∈ unitary C := by
    apply Unitary.mem_iff.mpr
    simp only [star_sub, star_add, hp.isSelfAdjoint.star_eq, star_one]
    constructor <;> noncomm_ring [hpp]
  have hx : IsUnit x := by
    have he : 1 - x = (p - q) * (p + p - 1) := by
      dsimp [x]
      noncomm_ring [hpp]
    have hn : ‖1 - x‖ < 1 := by
      rw [he, CStarRing.norm_mul_coe_unitary (p - q) ⟨_, hs⟩]
      exact hclose
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hn
  have hxp : x * p = q * x := by dsimp [x]; noncomm_ring [hpp, hqq, hppA, hqqA]
  have hxx : star x * x = 1 - (p - q) * (p - q) := by
    dsimp [x]
    simp only [star_add, star_mul, star_sub, star_one,
      hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
    noncomm_ring [hpp, hqq, hppA, hqqA]
  have hcomm : Commute (star x * x) p := by
    rw [hxx]
    change (1 - (p - q) * (p - q)) * p = p * (1 - (p - q) * (p - q))
    noncomm_ring [hpp, hqq, hppA, hqqA]
  have ha : Commute (CFC.abs x) p := by
    exact hcomm.cfcₙ_nnreal NNReal.sqrt
  obtain ⟨u, hu, hxu⟩ :=
    D5.S3.Quantum.Analysis.RussoDye.exists_mem_unitary_eq_mul_cfcAbs hx
  have hau : IsUnit (CFC.abs x) :=
    isUnit_mul_self_iff.mp (CFC.abs_mul_abs x ▸ hx.star.mul hx)
  have hup : u * p = q * u := by
    apply hau.mul_left_inj.mp
    calc u * p * CFC.abs x = u * CFC.abs x * p := by rw [mul_assoc, ← ha.eq, ← mul_assoc]
      _ = x * p := by rw [← hxu]
      _ = q * x := hxp
      _ = q * u * CFC.abs x := by
        simpa only [mul_assoc] using congrArg (fun z => q * z) hxu
  refine ⟨⟨u, hu⟩, ?_⟩
  change u * p * star u = q
  rw [hup, mul_assoc, Unitary.mul_star_self_of_mem hu, mul_one]

private theorem round_scalar (t : ℝ) (ht : |t * t - t| < 1 / 16) :
    |t - (if t < 1 / 2 then 0 else 1)| ≤ 1 / 4 := by
  have ht₁ := (abs_lt.mp ht).1
  have ht₂ := (abs_lt.mp ht).2
  split_ifs with h
  · rw [sub_zero, abs_le]
    constructor
    · nlinarith [sq_nonneg (t + 1 / 4)]
    · by_contra hn
      have hb : 1 / 4 < t := lt_of_not_ge hn
      nlinarith [mul_nonneg (sub_nonneg.mpr hb.le) (sub_nonneg.mpr h.le)]
  · rw [abs_le]
    have hb : 1 / 2 ≤ t := le_of_not_gt h
    constructor
    · by_contra hn
      have hc : t < 3 / 4 := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc.le)]
    · nlinarith [sq_nonneg (t - 5 / 4)]

private theorem matrix_round_projection {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (hdef : ‖H * H - H‖ < 1 / 16) :
    ∃ Q : Matrix n n ℂ, IsStarProjection Q ∧ ‖H - Q‖ ≤ 1 / 4 := by
  classical
  let e := hH.eigenvalues
  let U := hH.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  let D := diagonal (fun i => (e i : ℂ))
  have hHD : H = φ D := hH.spectral_theorem
  have hd : ‖H * H - H‖ = ‖fun i => ((e i : ℂ) * (e i : ℂ) - (e i : ℂ))‖ := by
    rw [hHD, ← map_mul, ← map_sub, NonUnitalStarAlgHom.norm_map φ φ.injective]
    simp only [D, diagonal_mul_diagonal, diagonal_sub, l2_opNorm_diagonal]
  have he (i : n) : |e i * e i - e i| < 1 / 16 := by
    have hi := norm_le_pi_norm (fun j => ((e j : ℂ) * (e j : ℂ) - (e j : ℂ))) i
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hi
    exact hi.trans_lt (hd ▸ hdef)
  let b : n → ℂ := fun i => if e i < 1 / 2 then 0 else 1
  have hb : IsStarProjection (diagonal b) := by
    constructor
    · change diagonal b * diagonal b = diagonal b
      rw [diagonal_mul_diagonal]
      congr 1
      funext i
      dsimp [b]
      split_ifs <;> simp
    · change (diagonal b)ᴴ = diagonal b
      rw [diagonal_conjTranspose]
      congr 1
      funext i
      dsimp [b]
      split_ifs <;> simp
  refine ⟨φ (diagonal b), hb.map φ, ?_⟩
  rw [hHD, ← map_sub, NonUnitalStarAlgHom.norm_map φ φ.injective]
  change ‖diagonal (fun i => (e i : ℂ)) - diagonal b‖ ≤ _
  rw [diagonal_sub, l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr
  intro i
  have hi := round_scalar (e i) (he i)
  dsimp [b]
  split_ifs with h
  · rw [if_pos h] at hi
    simpa only [sub_zero, Complex.norm_real, Real.norm_eq_abs] using hi
  · rw [if_neg h] at hi
    simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using hi

/-- Every actual completed-algebra projection is unitarily conjugate, inside that
algebra, to an actual projection in one of the given matrix ranges. -/
theorem localize_projection (M : FullMatrixModel C) (p : C) (hp : IsStarProjection p) :
    ∃ (n : ℕ) (u : unitary C) (Q : Matrix (Fin (M.size n)) (Fin (M.size n)) ℂ),
      IsStarProjection Q ∧ (u : C) * p * star (u : C) = M.embed n Q := by
  classical
  obtain ⟨a, ha, hpa⟩ := M.dense.exists_dist_lt p (by norm_num : (0 : ℝ) < 1 / 100)
  obtain ⟨n, A, rfl⟩ := Set.mem_iUnion.mp ha
  have hAp : ‖M.embed n A - p‖ < 1 / 100 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hpa
  let H : Matrix (Fin (M.size n)) (Fin (M.size n)) ℂ :=
    (2⁻¹ : ℂ) • (A + star A)
  have hH : H.IsHermitian := by
    change star H = H
    simp [H, star_smul, star_add, add_comm]
  have hmap : M.embed n H = (2⁻¹ : ℂ) • (M.embed n A + star (M.embed n A)) := by
    simp only [H, map_smul, map_add, map_star]
  have he : M.embed n H - p =
      (2⁻¹ : ℂ) • ((M.embed n A - p) + star (M.embed n A - p)) := by
    rw [hmap]
    simp only [star_sub, hp.isSelfAdjoint.star_eq]
    module
  have hHp : ‖M.embed n H - p‖ < 1 / 100 := by
    calc ‖M.embed n H - p‖ = (1 / 2 : ℝ) *
          ‖(M.embed n A - p) + star (M.embed n A - p)‖ := by
            rw [he, norm_smul]
            norm_num
      _ ≤ (1 / 2 : ℝ) * (‖M.embed n A - p‖ + ‖star (M.embed n A - p)‖) := by
        gcongr
        exact norm_add_le _ _
      _ = ‖M.embed n A - p‖ := by rw [norm_star]; ring
      _ < 1 / 100 := hAp
  have hpNorm : ‖p‖ ≤ 1 := by
    have heq : ‖p‖ * ‖p‖ = ‖p‖ := by
      rw [← CStarRing.norm_star_mul_self, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
    nlinarith [norm_nonneg p]
  have hHnorm : ‖M.embed n H‖ ≤ 2 := by
    calc ‖M.embed n H‖ = ‖(M.embed n H - p) + p‖ := by rw [sub_add_cancel]
      _ ≤ ‖M.embed n H - p‖ + ‖p‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  have hdef : ‖H * H - H‖ < 1 / 16 := by
    rw [← NonUnitalStarAlgHom.norm_map (M.embed n) (M.injective n), map_sub, map_mul]
    have hid : M.embed n H * M.embed n H - M.embed n H =
        (M.embed n H - p) * M.embed n H + p * (M.embed n H - p) -
          (M.embed n H - p) := by noncomm_ring [hp.isIdempotentElem.eq]
    rw [hid]
    calc ‖(M.embed n H - p) * M.embed n H + p * (M.embed n H - p) -
          (M.embed n H - p)‖ ≤
          ‖(M.embed n H - p) * M.embed n H + p * (M.embed n H - p)‖ +
            ‖M.embed n H - p‖ := norm_sub_le _ _
      _ ≤ ‖M.embed n H - p‖ * ‖M.embed n H‖ +
          ‖p‖ * ‖M.embed n H - p‖ + ‖M.embed n H - p‖ := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ‖M.embed n H - p‖ * 2 + 1 * ‖M.embed n H - p‖ + ‖M.embed n H - p‖ := by
        gcongr
      _ < 1 / 16 := by linarith
  obtain ⟨Q, hQ, hHQ⟩ := matrix_round_projection H hH hdef
  have hclose : ‖p - M.embed n Q‖ < 1 := by
    have hHQ' : ‖M.embed n H - M.embed n Q‖ ≤ 1 / 4 := by
      rw [← map_sub, NonUnitalStarAlgHom.norm_map (M.embed n) (M.injective n)]
      exact hHQ
    have htri := norm_sub_le_norm_sub_add_norm_sub p (M.embed n H) (M.embed n Q)
    rw [norm_sub_rev p (M.embed n H)] at htri
    linarith
  obtain ⟨u, hu⟩ := close_projections_unitary hp (hQ.map (M.embed n)) hclose
  exact ⟨n, u, Q, hQ, hu⟩

end D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching
