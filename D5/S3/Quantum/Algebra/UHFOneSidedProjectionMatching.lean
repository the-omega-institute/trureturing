/- GID: D5/S3/Quantum/Algebra/UHFOneSidedProjectionMatching
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/UHFOneSidedProjectionMatching
   mirror-E: none(waiver:intrinsic-algebraic-supplier)
   anchors: []
   utility: none
   digest: Intrinsic finite-stage localization and one-sided projection matching. -/

import D5.S3.Quantum.Analysis.RussoDye
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-! Actual matrix ranges and projection localization in the completed algebra. -/

namespace D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching

open scoped Matrix.Norms.L2Operator
open _root_.Matrix

/-- A coordinate matrix unit on the diagonal is a self-adjoint projection. -/
lemma proj_single {d : ℕ} (i : Fin d) :
    IsStarProjection (single i i (1 : ℂ)) := by
  constructor
  · change single i i (1 : ℂ) * single i i 1 = single i i 1
    simp only [single_mul_single_same, mul_one]
  · change (single i i (1 : ℂ)).conjTranspose = single i i 1
    rw [conjTranspose_single, star_one]

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
  · rw [ite_eq_left h] at hi
    simpa only [sub_zero, Complex.norm_real, Real.norm_eq_abs] using hi
  · rw [ite_eq_right h] at hi
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

private theorem projection_diagonal {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : IsStarProjection P) :
    ∃ (u : unitaryGroup (Fin d) ℂ) (a : Fin d → ℝ),
      (∀ i, a i = 0 ∨ a i = 1) ∧
      P = Unitary.conjStarAlgAut ℂ _ u (diagonal (fun i => (a i : ℂ))) := by
  let hH : P.IsHermitian := hP.isSelfAdjoint
  let a := hH.eigenvalues
  let u := hH.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) u
  have hPD : P = φ (diagonal (fun i => (a i : ℂ))) := hH.spectral_theorem
  refine ⟨u, a, ?_, hPD⟩
  intro i
  have hd : diagonal (fun i => (a i : ℂ)) * diagonal (fun i => (a i : ℂ)) =
      diagonal (fun i => (a i : ℂ)) := by
    apply φ.injective
    change φ (diagonal (fun i => (a i : ℂ)) * diagonal (fun i => (a i : ℂ))) =
      φ (diagonal (fun i => (a i : ℂ)))
    rw [map_mul, ← hPD]
    exact hP.isIdempotentElem.eq
  have hi := congrArg (fun T : Matrix (Fin d) (Fin d) ℂ => T i i) hd
  simp only [diagonal_mul_diagonal, diagonal_apply_eq] at hi
  have hi' : a i * a i = a i := by exact_mod_cast hi
  have hf : a i * (a i - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with hz | ho
  · exact Or.inl hz
  · exact Or.inr (by linarith)

private theorem matrix_matching {d : ℕ} (P Q : Matrix (Fin d) (Fin d) ℂ)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    ∃ (s : Finset (Fin d)) (L : Fin d → Matrix (Fin d) (Fin d) ℂ)
      (m : Matrix (Fin d) (Fin d) ℂ) (W : Fin d → Matrix (Fin d) (Fin d) ℂ),
      s.Nonempty ∧ (∀ i ∈ s, IsStarProjection (L i) ∧ L i ≠ 0) ∧
      (↑s : Set (Fin d)).Pairwise (fun i j => L i * L j = 0) ∧ (∑ i ∈ s, L i) = P ∧
      IsStarProjection m ∧ m ≠ 0 ∧ m * Q = m ∧
      (∀ i ∈ s, star (W i) * W i = m ∧ W i * star (W i) = L i) := by
  classical
  obtain ⟨u, a, ha, hPa⟩ := projection_diagonal P hP
  obtain ⟨v, b, hb, hQb⟩ := projection_diagonal Q hQ
  have support (c : Fin d → ℝ) (hc : ∀ i, c i = 0 ∨ c i = 1)
      (t : unitaryGroup (Fin d) ℂ)
      (ht : Unitary.conjStarAlgAut ℂ _ t (diagonal (fun i => (c i : ℂ))) ≠ 0) :
      ∃ i, c i = 1 := by
    by_contra! h
    have hc0 (i) : c i = 0 := (hc i).resolve_right (h i)
    apply ht
    simp [hc0]
  obtain ⟨i₀, hi₀⟩ := support a ha u (hPa ▸ hP0)
  obtain ⟨j, hj⟩ := support b hb v (hQb ▸ hQ0)
  let s : Finset (Fin d) := Finset.univ.filter (fun i => a i = 1)
  let φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) u
  let ψ := Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) v
  let L := fun i => φ (single i i 1)
  let m := ψ (single j j 1)
  let W := fun i => (u : Matrix (Fin d) (Fin d) ℂ) * single i j 1 *
    star (v : Matrix (Fin d) (Fin d) ℂ)
  have hE (i : Fin d) : IsStarProjection (single i i (1 : ℂ)) :=
    proj_single i
  have hE0 (i : Fin d) : (single i i (1 : ℂ) : Matrix (Fin d) (Fin d) ℂ) ≠ 0 := by
    intro h
    have hi := congrArg (fun T : Matrix (Fin d) (Fin d) ℂ => T i i) h
    simp at hi
  have hsum : (∑ i ∈ s, single i i (1 : ℂ)) = diagonal (fun i => (a i : ℂ)) := by
    dsimp only [s]
    rw [Finset.sum_filter]
    calc (∑ i : Fin d, if a i = 1 then single i i (1 : ℂ) else 0) =
        ∑ i : Fin d, single i i (a i : ℂ) := by
          apply Finset.sum_congr rfl
          intro i _
          rcases ha i with h | h
          · simp [h]
          · simp [h]
      _ = _ := sum_single_eq_diagonal _
  refine ⟨s, L, m, W, ⟨i₀, by simp [s, hi₀]⟩, ?_, ?_, ?_, (hE j).map ψ, ?_, ?_, ?_⟩
  · intro i _
    refine ⟨(hE i).map φ, ?_⟩
    intro hz
    apply hE0 i
    exact φ.injective (hz.trans (map_zero φ).symm)
  · intro i _ k _ hik
    dsimp [L]
    rw [← map_mul, _root_.Matrix.single_mul_single_of_ne (1 : ℂ) i i k hik (1 : ℂ), map_zero]
  · change (∑ i ∈ s, φ (single i i 1)) = P
    rw [← map_sum, hsum]
    exact hPa.symm
  · change ψ (single j j 1) ≠ 0
    intro hz
    apply hE0 j
    exact ψ.injective (hz.trans (map_zero ψ).symm)
  · change ψ (single j j 1) * Q = ψ (single j j 1)
    rw [hQb, ← map_mul]
    congr 1
    ext i k
    by_cases hi : j = i
    · subst i
      by_cases hk : j = k
      · subst k
        simp [single, mul_apply, diagonal, hj]
      · simp [single, mul_apply, diagonal, hk]
    · simp [single, mul_apply, diagonal, hi]
  · intro i _
    dsimp [W, m, L, φ, ψ]
    have hsingle (i k : Fin d) : star (single i k (1 : ℂ) : Matrix (Fin d) (Fin d) ℂ) =
        single k i 1 := by exact conjTranspose_single i k (1 : ℂ) |>.trans (by rw [star_one])
    simp only [star_mul, star_star, hsingle]
    constructor
    · simp only [mul_assoc, ← mul_assoc (star (u : Matrix (Fin d) (Fin d) ℂ)),
        Unitary.coe_star_mul_self, one_mul]
      rw [← mul_assoc (single j i (1 : ℂ)), single_mul_single_same, one_mul]
    · simp only [mul_assoc, ← mul_assoc (star (v : Matrix (Fin d) (Fin d) ℂ)),
        Unitary.coe_star_mul_self, one_mul]
      rw [← mul_assoc (single i j (1 : ℂ)), single_mul_single_same, one_mul]

/-- A one-sided complete partition of an arbitrary nonzero completed-algebra
projection, all of whose pieces match the same nonzero subprojection of another
arbitrary nonzero projection. The two multiplication identities express `m ≤ v`
intrinsically, without choosing an auxiliary order on the C-star algebra. -/
theorem one_sided_projection_matching (M : FullMatrixModel C) (r v : C)
    (hr : IsStarProjection r) (hv : IsStarProjection v) (hr0 : r ≠ 0) (hv0 : v ≠ 0) :
    ∃ (N : ℕ) (s : Finset (Fin (M.size N))) (l : Fin (M.size N) → C)
      (m : C) (w : Fin (M.size N) → C),
      s.Nonempty ∧ (∀ i ∈ s, IsStarProjection (l i) ∧ l i ≠ 0) ∧
      (↑s : Set (Fin (M.size N))).Pairwise (fun i j => l i * l j = 0) ∧
      (∑ i ∈ s, l i) = r ∧ IsStarProjection m ∧ m ≠ 0 ∧ m * v = m ∧ v * m = m ∧
      (∀ i ∈ s, star (w i) * w i = m ∧ w i * star (w i) = l i) := by
  classical
  obtain ⟨nr, ur, R, hR, hur⟩ := localize_projection M r hr
  obtain ⟨nv, uv, V, hV, huv⟩ := localize_projection M v hv
  let N := max nr nv
  obtain ⟨R', hR'⟩ := M.increasing nr N (le_max_left _ _) ⟨R, rfl⟩
  obtain ⟨V', hV'⟩ := M.increasing nv N (le_max_right _ _) ⟨V, rfl⟩
  have hur' : (ur : C) * r * star (ur : C) = M.embed N R' := hur.trans hR'.symm
  have huv' : (uv : C) * v * star (uv : C) = M.embed N V' := huv.trans hV'.symm
  have hR'proj : IsStarProjection R' := by
    have hp : IsStarProjection (M.embed N R') := hR'.symm ▸ hR.map (M.embed nr)
    constructor
    · apply M.injective N
      simpa only [map_mul] using hp.isIdempotentElem.eq
    · change star R' = R'
      apply M.injective N
      simpa only [map_star] using hp.isSelfAdjoint.star_eq
  have hV'proj : IsStarProjection V' := by
    have hp : IsStarProjection (M.embed N V') := hV'.symm ▸ hV.map (M.embed nv)
    constructor
    · apply M.injective N
      simpa only [map_mul] using hp.isIdempotentElem.eq
    · change star V' = V'
      apply M.injective N
      simpa only [map_star] using hp.isSelfAdjoint.star_eq
  have hR'0 : R' ≠ 0 := by
    intro h
    apply hr0
    apply (Unitary.conjStarAlgAut ℂ C ur).injective
    change (ur : C) * r * star (ur : C) = (ur : C) * 0 * star (ur : C)
    simpa only [h, map_zero, mul_zero, zero_mul] using hur'
  have hV'0 : V' ≠ 0 := by
    intro h
    apply hv0
    apply (Unitary.conjStarAlgAut ℂ C uv).injective
    change (uv : C) * v * star (uv : C) = (uv : C) * 0 * star (uv : C)
    simpa only [h, map_zero, mul_zero, zero_mul] using huv'
  obtain ⟨s, L, m₀, W, hs, hL, horth, hsum, hm₀, hm₀0, hmV, hW⟩ :=
    matrix_matching R' V' hR'proj hV'proj hR'0 hV'0
  let α := (Unitary.conjStarAlgAut ℂ C ur).symm
  let β := (Unitary.conjStarAlgAut ℂ C uv).symm
  let l := fun i => α (M.embed N (L i))
  let m := β (M.embed N m₀)
  let w := fun i => star (ur : C) * M.embed N (W i) * (uv : C)
  have hrback : α (M.embed N R') = r := by
    rw [← hur']
    exact (Unitary.conjStarAlgAut ℂ C ur).symm_apply_apply r
  have hvback : β (M.embed N V') = v := by
    rw [← huv']
    exact (Unitary.conjStarAlgAut ℂ C uv).symm_apply_apply v
  have hm : IsStarProjection m := (hm₀.map (M.embed N)).map β
  have hmv : m * v = m := by
    dsimp only [m]
    rw [← hvback, ← map_mul, ← map_mul, hmV]
  refine ⟨N, s, l, m, w, hs, ?_, ?_, ?_, hm, ?_, hmv, ?_, ?_⟩
  · intro i hi
    refine ⟨((hL i hi).1.map (M.embed N)).map α, ?_⟩
    intro hz
    apply (hL i hi).2
    apply M.injective N
    apply α.injective
    change l i = α (M.embed N 0)
    simpa only [map_zero] using hz
  · intro i hi j hj hij
    change α (M.embed N (L i)) * α (M.embed N (L j)) = 0
    rw [← map_mul, ← map_mul, horth hi hj hij, map_zero, map_zero]
  · change (∑ i ∈ s, α (M.embed N (L i))) = r
    rw [← map_sum, ← map_sum, hsum]
    exact hrback
  · intro hz
    apply hm₀0
    apply M.injective N
    apply β.injective
    change m = β (M.embed N 0)
    simpa only [map_zero] using hz
  · simpa only [star_mul, hv.isSelfAdjoint.star_eq, hm.isSelfAdjoint.star_eq] using
      congrArg star hmv
  · intro i hi
    obtain ⟨hWm, hWL⟩ := hW i hi
    constructor
    · change star (star (ur : C) * M.embed N (W i) * (uv : C)) *
          (star (ur : C) * M.embed N (W i) * (uv : C)) =
          star (uv : C) * M.embed N m₀ * (uv : C)
      simp only [star_mul, star_star, mul_assoc]
      rw [← mul_assoc (ur : C), Unitary.mul_star_self_of_mem ur.2, one_mul]
      rw [← mul_assoc (star (M.embed N (W i))), ← map_star, ← map_mul, hWm]
    · change (star (ur : C) * M.embed N (W i) * (uv : C)) *
          star (star (ur : C) * M.embed N (W i) * (uv : C)) =
          star (ur : C) * M.embed N (L i) * (ur : C)
      simp only [star_mul, star_star, mul_assoc]
      rw [← mul_assoc (uv : C), Unitary.mul_star_self_of_mem uv.2, one_mul]
      rw [← mul_assoc (M.embed N (W i)), ← map_star, ← map_mul, hWL]

end D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching
