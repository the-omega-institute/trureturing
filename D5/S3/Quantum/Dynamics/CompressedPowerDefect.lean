/- GID: D5/S3/Quantum/Dynamics/CompressedPowerDefect
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/CompressedPowerDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coisometric compression has quadratic power defect controlled by its two-step leak. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Algebra.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Dynamics.CompressedPowerDefect

open ContinuousLinearMap
open D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity

/-- A self-adjoint contraction compressed by a coisometry has a power defect quadratic in the
compression order and linear in its two-step leakage. -/
theorem compressed_power_defect
    {𝕜 R E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup R] [InnerProductSpace 𝕜 R] [FiniteDimensional 𝕜 R]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (F : R →L[𝕜] E) (S : R →L[𝕜] R) (b : ℝ) :
    letI : CompleteSpace R := FiniteDimensional.complete 𝕜 R
    letI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
    F ∘L F.adjoint = 1 → IsSelfAdjoint S → ‖S‖ ≤ b →
    let P := F.adjoint ∘L F
    let Q := 1 - P
    let A := F ∘L S ∘L F.adjoint
    let δ := ‖F ∘L S ∘L Q ∘L S ∘L F.adjoint‖
    F ∘L (S ^ 2) ∘L F.adjoint - A ^ 2 =
        F ∘L S ∘L Q ∘L S ∘L F.adjoint ∧
      ∀ n : ℕ, 2 ≤ n →
        ‖F ∘L (S ^ n) ∘L F.adjoint - A ^ n‖ ≤
          (n.choose 2 : ℝ) * b ^ (n - 2) * δ := by
  letI := FiniteDimensional.complete 𝕜 R
  letI := FiniteDimensional.complete 𝕜 E
  intro hF hS hSb
  let G : E →L[𝕜] R := F.adjoint
  change F ∘L G = 1 at hF
  let P : R →L[𝕜] R := G ∘L F
  let Q : R →L[𝕜] R := 1 - P
  let A : E →L[𝕜] E := F ∘L S ∘L G
  let δ : ℝ := ‖F ∘L S ∘L Q ∘L S ∘L G‖
  change (F ∘L (S ^ 2) ∘L G - A ^ 2 =
      F ∘L S ∘L Q ∘L S ∘L G) ∧
    ∀ n : ℕ, 2 ≤ n →
      ‖F ∘L (S ^ n) ∘L G - A ^ n‖ ≤
        (n.choose 2 : ℝ) * b ^ (n - 2) * δ

  have hSadj : S.adjoint = S := hS.adjoint_eq
  have hPadj : P.adjoint = P := by
    simp only [P, G, adjoint_comp, adjoint_adjoint]
  have hPmul : P * P = P := by
    change (G ∘L F) ∘L (G ∘L F) = G ∘L F
    rw [comp_assoc, ← comp_assoc F G F, hF, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp]
  have hPstar : IsStarProjection P :=
    ⟨show IsIdempotentElem P from hPmul, show IsSelfAdjoint P from hPadj⟩
  have hQstar : IsStarProjection Q := by
    simpa only [Q] using hPstar.one_sub
  have hQadj : Q.adjoint = Q := hQstar.isSelfAdjoint
  have hQmul : Q * Q = Q := hQstar.isIdempotentElem
  have hPQ : P * Q = 0 := by
    simpa only [Q] using hPstar.mul_one_sub_self
  have hQP : Q * P = 0 := by
    simpa only [Q] using hPstar.one_sub_mul_self
  have hQnorm : ‖Q‖ ≤ 1 := hQstar.norm_le Q
  have hPG : P ∘L G = G := by
    simp only [P, comp_assoc, hF, ContinuousLinearMap.one_def,
      ContinuousLinearMap.comp_id]

  have hFadj_norm : ∀ x : E, ‖G x‖ = ‖x‖ := by
    apply (norm_map_iff_adjoint_comp_self G).2
    simpa only [G, adjoint_adjoint] using hF
  have hFadjnorm : ‖G‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro x
    rw [hFadj_norm, one_mul]
  have hFnorm : ‖F‖ ≤ 1 := by simpa only [G, adjoint.norm_map] using hFadjnorm
  have hb : 0 ≤ b := (norm_nonneg S).trans hSb

  have hnormSpow : ∀ k : ℕ, ‖S ^ k‖ ≤ b ^ k := by
    intro k
    have hfirst : ‖S ^ k‖ ≤ ‖S‖ ^ k := by
      cases k with
      | zero =>
          simpa only [pow_zero, ContinuousLinearMap.one_def] using
            (norm_id_le (𝕜 := 𝕜) (E := R))
      | succ k => exact norm_pow_le' S k.succ_pos
    exact hfirst.trans (pow_le_pow_left₀ (norm_nonneg S) hSb k)

  let ell : ℝ := ‖Q ∘L S ∘L G‖
  have hell : 0 ≤ ell := norm_nonneg _

  have hcommutator : ∀ k : ℕ,
      P * S ^ k - S ^ k * P =
        ∑ j ∈ Finset.range k, S ^ j * (P * S - S * P) * S ^ (k - 1 - j) := by
    intro k
    let f : ℕ → (R →L[𝕜] R) := fun j => S ^ j * P * S ^ (k - j)
    calc
      P * S ^ k - S ^ k * P = f 0 - f k := by
        simp only [f, pow_zero, one_mul, Nat.sub_zero, Nat.sub_self, mul_one]
      _ = ∑ j ∈ Finset.range k, (f j - f (j + 1)) :=
        (Finset.sum_range_sub' f k).symm
      _ = ∑ j ∈ Finset.range k,
          S ^ j * (P * S - S * P) * S ^ (k - 1 - j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjlt : j < k := Finset.mem_range.mp hj
        have hright : k - j = (k - 1 - j) + 1 := by omega
        have hnext : k - (j + 1) = k - 1 - j := by omega
        simp only [f, hright, hnext]
        rw [pow_succ' S (k - 1 - j), pow_succ S j]
        simp only [mul_sub, sub_mul, mul_assoc]

  have hcommutator_norm : ‖P * S - S * P‖ ≤ ‖Q * S * P‖ := by
    let B : R →L[𝕜] R := Q * S * P
    have hBadj : B.adjoint = P * S * Q := by
      simp only [B, ContinuousLinearMap.mul_def, adjoint_comp, hPadj, hQadj, hSadj,
        comp_assoc]
    have hcomm : P * S - S * P = B.adjoint - B := by
      calc
        P * S - S * P = P * S * Q - Q * S * P :=
          commutator_eq_cross_blocks P Q S rfl
        _ = B.adjoint - B := by rw [hBadj]
    rw [hcomm]
    apply opNorm_le_bound _ (norm_nonneg B)
    intro x
    have horth : inner 𝕜 (B.adjoint (Q x)) (B (P x)) = 0 := by
      rw [hBadj]
      change inner 𝕜 (P (S (Q (Q x)))) (Q (S (P (P x)))) = 0
      rw [← adjoint_inner_right, hPadj]
      change inner 𝕜 (S (Q (Q x))) ((P * Q) (S (P (P x)))) = 0
      rw [hPQ, zero_apply, inner_zero_right]
    have hdecomp : x = P x + Q x := by
      simp only [Q, sub_apply]
      abel
    have hPQinner : inner 𝕜 (P x) (Q x) = 0 := by
      rw [← adjoint_inner_right, hPadj]
      change inner 𝕜 x ((P * Q) x) = 0
      rw [hPQ, zero_apply, inner_zero_right]
    have hpyth : ‖P x‖ ^ 2 + ‖Q x‖ ^ 2 = ‖x‖ ^ 2 := by
      have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (P x) (Q x) hPQinner
      rw [← hdecomp] at hp
      simpa only [pow_two] using hp.symm
    have hBadjQ : B.adjoint * Q = B.adjoint := by
      rw [hBadj]
      simp only [mul_assoc, hQmul]
    have hBP : B * P = B := by
      simp only [B, mul_assoc, hPmul]
    have heval : (B.adjoint - B) x = B.adjoint (Q x) - B (P x) := by
      change (B.adjoint - B) x = (B.adjoint * Q) x - (B * P) x
      simp only [sub_apply, hBadjQ, hBP]
    rw [heval]
    have hnormsq :
        ‖B.adjoint (Q x) - B (P x)‖ ^ 2 =
          ‖B.adjoint (Q x)‖ ^ 2 + ‖B (P x)‖ ^ 2 := by
      rw [norm_sub_sq (𝕜 := 𝕜), horth, RCLike.zero_re, mul_zero, sub_zero]
    have hy : ‖B.adjoint (Q x)‖ ≤ ‖B‖ * ‖Q x‖ := by
      calc
        ‖B.adjoint (Q x)‖ ≤ ‖B.adjoint‖ * ‖Q x‖ := B.adjoint.le_opNorm (Q x)
        _ = ‖B‖ * ‖Q x‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    have hz : ‖B (P x)‖ ≤ ‖B‖ * ‖P x‖ := B.le_opNorm (P x)
    have hy2 : ‖B.adjoint (Q x)‖ ^ 2 ≤ (‖B‖ * ‖Q x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hy 2
    have hz2 : ‖B (P x)‖ ^ 2 ≤ (‖B‖ * ‖P x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hz 2
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg B) (norm_nonneg x))).mp
    rw [hnormsq]
    calc
      ‖B.adjoint (Q x)‖ ^ 2 + ‖B (P x)‖ ^ 2 ≤
          (‖B‖ * ‖Q x‖) ^ 2 + (‖B‖ * ‖P x‖) ^ 2 := add_le_add hy2 hz2
      _ = ‖B‖ ^ 2 * (‖P x‖ ^ 2 + ‖Q x‖ ^ 2) := by ring
      _ = ‖B‖ ^ 2 * ‖x‖ ^ 2 := by rw [hpyth]
      _ = (‖B‖ * ‖x‖) ^ 2 := by rw [mul_pow]

  have hleak_eq : ‖Q ∘L S ∘L G‖ = ‖Q * S * P‖ := by
    apply le_antisymm
    · rw [show Q ∘L S ∘L G = (Q * S * P) ∘L G by
        simp only [ContinuousLinearMap.mul_def, comp_assoc, hPG]]
      exact (opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg (Q * S * P)) hFadjnorm)
    · rw [show Q * S * P = (Q ∘L S ∘L G) ∘L F by
        simp only [P, ContinuousLinearMap.mul_def, comp_assoc]]
      exact (opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg (Q ∘L S ∘L G)) hFnorm)
  have hcommutator_norm_ell : ‖P * S - S * P‖ ≤ ell :=
    hcommutator_norm.trans_eq hleak_eq.symm
  have hcommutator_apply_ell (x : R) :
      ‖(P * S - S * P) x‖ ≤ ell * ‖x‖ :=
    (P * S - S * P).le_opNorm x |>.trans
      (mul_le_mul_of_nonneg_right hcommutator_norm_ell (norm_nonneg x))

  have hleak_power : ∀ k : ℕ, 1 ≤ k →
      ‖Q ∘L (S ^ k) ∘L G‖ ≤ (k : ℝ) * b ^ (k - 1) * ell := by
    intro k hk
    have hrewrite : Q ∘L (S ^ k) ∘L G =
        -(Q ∘L (P * S ^ k - S ^ k * P) ∘L G) := by
      ext x
      change Q ((S ^ k) (G x)) = -Q ((P * S ^ k - S ^ k * P) (G x))
      simp only [sub_apply, mul_apply_eq_comp, map_sub]
      have hzero : Q (P ((S ^ k) (G x))) = 0 := by
        change (Q * P) ((S ^ k) (G x)) = 0
        rw [hQP, zero_apply]
      have hfixed : P (G x) = G x := by
        change (P ∘L G) x = G x
        rw [hPG]
      rw [hzero, hfixed, zero_sub, neg_neg]
    apply opNorm_le_bound _ (by positivity)
    intro x
    rw [hrewrite, hcommutator]
    rw [ContinuousLinearMap.finsetSum_comp
      (fun j => S ^ j * (P * S - S * P) * S ^ (k - 1 - j)) G]
    rw [ContinuousLinearMap.comp_finsetSum Q
      (fun j => (S ^ j * (P * S - S * P) * S ^ (k - 1 - j)) ∘L G)]
    change ‖-((∑ j ∈ Finset.range k,
      Q ∘L (S ^ j * (P * S - S * P) * S ^ (k - 1 - j)) ∘L G) x)‖ ≤
        ((k : ℝ) * b ^ (k - 1) * ell) * ‖x‖
    rw [norm_neg]
    rw [sum_apply]
    refine (norm_sum_le _ _).trans ?_
    calc
      (∑ j ∈ Finset.range k,
          ‖(Q ∘L (S ^ j * (P * S - S * P) * S ^ (k - 1 - j)) ∘L G) x‖) ≤
          ∑ _j ∈ Finset.range k, b ^ (k - 1) * ell * ‖x‖ := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hjlt : j < k := Finset.mem_range.mp hj
            have hjle : j ≤ k - 1 := by omega
            have hexp : j + (k - 1 - j) = k - 1 := Nat.add_sub_of_le hjle
            change ‖Q ((S ^ j) ((P * S - S * P) ((S ^ (k - 1 - j)) (G x))))‖ ≤
              b ^ (k - 1) * ell * ‖x‖
            calc
              ‖Q ((S ^ j) ((P * S - S * P) ((S ^ (k - 1 - j)) (G x))))‖ ≤
                  ‖Q‖ * ‖(S ^ j) ((P * S - S * P) ((S ^ (k - 1 - j)) (G x)))‖ :=
                Q.le_opNorm _
              _ ≤ 1 * ‖(S ^ j) ((P * S - S * P) ((S ^ (k - 1 - j)) (G x)))‖ :=
                mul_le_mul_of_nonneg_right hQnorm (norm_nonneg _)
              _ ≤ 1 * (‖S ^ j‖ * ‖(P * S - S * P) ((S ^ (k - 1 - j)) (G x))‖) := by
                gcongr
                exact (S ^ j).le_opNorm _
              _ ≤ 1 * (‖S ^ j‖ * (ell * ‖(S ^ (k - 1 - j)) (G x)‖)) := by
                gcongr
                exact hcommutator_apply_ell _
              _ ≤ 1 * (‖S ^ j‖ *
                  (ell * (‖S ^ (k - 1 - j)‖ * ‖G x‖))) := by
                gcongr
                exact (S ^ (k - 1 - j)).le_opNorm _
              _ ≤ 1 * (b ^ j * (ell * (b ^ (k - 1 - j) * ‖x‖))) := by
                gcongr
                · exact hnormSpow j
                · exact hnormSpow (k - 1 - j)
                · exact le_of_eq (hFadj_norm x)
              _ = b ^ (k - 1) * ell * ‖x‖ := by
                rw [one_mul]
                calc
                  b ^ j * (ell * (b ^ (k - 1 - j) * ‖x‖)) =
                      (b ^ j * b ^ (k - 1 - j)) * ell * ‖x‖ := by ring
                  _ = b ^ (j + (k - 1 - j)) * ell * ‖x‖ := by rw [pow_add]
                  _ = b ^ (k - 1) * ell * ‖x‖ := by rw [hexp]
      _ = ((k : ℝ) * b ^ (k - 1) * ell) * ‖x‖ := by simp; ring

  have hell_sq : ell * ell = δ := by
    let T : E →L[𝕜] R := Q ∘L S ∘L G
    have hTadj : T.adjoint = F ∘L S ∘L Q := by
      simp only [T, G, adjoint_comp, adjoint_adjoint, hQadj, hSadj, comp_assoc]
    have hgram : T.adjoint ∘L T = F ∘L S ∘L Q ∘L S ∘L G := by
      rw [hTadj]
      ext x
      change F (S (Q (Q (S (G x))))) = F (S (Q (S (G x))))
      rw [show Q (Q (S (G x))) = Q (S (G x)) by
        simpa only [mul_apply_eq_comp] using
          congrArg (fun U : R →L[𝕜] R => U (S (G x))) hQmul]
    calc
      ell * ell = ‖T‖ * ‖T‖ := rfl
      _ = ‖T.adjoint ∘L T‖ := (norm_adjoint_comp_self T).symm
      _ = δ := by rw [hgram]
  have hleft_leak : ‖F ∘L S ∘L Q‖ = ell := by
    have hadj : (Q ∘L S ∘L G).adjoint = F ∘L S ∘L Q := by
      simp only [G, adjoint_comp, adjoint_adjoint, hSadj, hQadj, comp_assoc]
    rw [← hadj]
    exact ContinuousLinearMap.adjoint.norm_map _

  have hAnorm : ‖A‖ ≤ b := by
    dsimp only [A]
    apply opNorm_le_bound _ hb
    intro x
    change ‖F (S (G x))‖ ≤ b * ‖x‖
    calc
      ‖F (S (G x))‖ ≤ ‖F‖ * ‖S (G x)‖ := F.le_opNorm _
      _ ≤ 1 * ‖S (G x)‖ :=
        mul_le_mul_of_nonneg_right hFnorm (norm_nonneg _)
      _ = ‖S (G x)‖ := one_mul _
      _ ≤ ‖S‖ * ‖G x‖ := S.le_opNorm _
      _ = ‖S‖ * ‖x‖ := by rw [hFadj_norm]
      _ ≤ b * ‖x‖ := mul_le_mul_of_nonneg_right hSb (norm_nonneg x)

  have hdefect_two : F ∘L (S ^ 2) ∘L G - A ^ 2 =
      F ∘L S ∘L Q ∘L S ∘L G := by
    dsimp only [A, Q, P]
    simp only [pow_two, ContinuousLinearMap.mul_def, comp_assoc,
      comp_sub, ContinuousLinearMap.one_def, sub_comp, ContinuousLinearMap.id_comp]

  have hrecursion : ∀ n : ℕ,
      F ∘L (S ^ (n + 1)) ∘L G - A ^ (n + 1) =
        A * (F ∘L (S ^ n) ∘L G - A ^ n) +
          F ∘L S ∘L Q ∘L (S ^ n) ∘L G := by
    intro n
    dsimp only [A]
    rw [pow_succ', pow_succ']
    simp only [ContinuousLinearMap.mul_def, comp_assoc, comp_sub]
    dsimp only [Q, P]
    simp only [comp_sub, ContinuousLinearMap.one_def, sub_comp, comp_assoc,
      ContinuousLinearMap.id_comp]
    abel

  have hsource : ∀ n : ℕ, 2 ≤ n →
      ‖F ∘L S ∘L Q ∘L (S ^ (n - 1)) ∘L G‖ ≤
        ((n - 1 : ℕ) : ℝ) * b ^ (n - 2) * δ := by
    intro n hn
    have hk : 1 ≤ n - 1 := by omega
    have hfactor : F ∘L S ∘L Q ∘L (S ^ (n - 1)) ∘L G =
        (F ∘L S ∘L Q) ∘L (Q ∘L (S ^ (n - 1)) ∘L G) := by
      ext x
      change F (S (Q ((S ^ (n - 1)) (G x)))) =
        F (S (Q (Q ((S ^ (n - 1)) (G x)))))
      rw [show Q (Q ((S ^ (n - 1)) (G x))) = Q ((S ^ (n - 1)) (G x)) by
        simpa only [mul_apply_eq_comp] using
          congrArg (fun U : R →L[𝕜] R => U ((S ^ (n - 1)) (G x))) hQmul]
    rw [hfactor]
    calc
      ‖(F ∘L S ∘L Q) ∘L (Q ∘L (S ^ (n - 1)) ∘L G)‖ ≤
          ‖F ∘L S ∘L Q‖ * ‖Q ∘L (S ^ (n - 1)) ∘L G‖ := opNorm_comp_le _ _
      _ ≤ ell * (((n - 1 : ℕ) : ℝ) * b ^ ((n - 1) - 1) * ell) := by
        rw [hleft_leak]
        exact mul_le_mul_of_nonneg_left (hleak_power (n - 1) hk) hell
      _ = ((n - 1 : ℕ) : ℝ) * b ^ (n - 2) * δ := by
        rw [Nat.sub_sub, add_comm 1 1]
        calc
          ell * (((n - 1 : ℕ) : ℝ) * b ^ (n - 2) * ell) =
              ((n - 1 : ℕ) : ℝ) * b ^ (n - 2) * (ell * ell) := by ring
          _ = ((n - 1 : ℕ) : ℝ) * b ^ (n - 2) * δ := by rw [hell_sq]

  refine ⟨hdefect_two, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 2 m]
  clear hn
  induction m with
  | zero =>
      rw [show 0 + 2 = 2 by rfl]
      simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero]
      rw [hdefect_two]
  | succ m ih =>
      rw [show m + 1 + 2 = (m + 2) + 1 by omega, hrecursion (m + 2)]
      let D : E →L[𝕜] E := F ∘L (S ^ (m + 2)) ∘L G - A ^ (m + 2)
      let L : E →L[𝕜] E := F ∘L S ∘L Q ∘L (S ^ (m + 2)) ∘L G
      change ‖A * D + L‖ ≤ ((m + 3).choose 2 : ℝ) * b ^ (m + 1) * δ
      refine (norm_add_le _ _).trans ?_
      have hD : ‖D‖ ≤ ((m + 2).choose 2 : ℝ) * b ^ m * δ := by
        dsimp only [D]
        simpa only [Nat.add_sub_cancel] using ih
      have hcompressed :
          ‖A * D‖ ≤ b * ((m + 2).choose 2 : ℝ) * b ^ m * δ := by
        calc
          ‖A * D‖ ≤ ‖A‖ * ‖D‖ := norm_mul_le _ _
          _ ≤ b * (((m + 2).choose 2 : ℝ) * b ^ m * δ) := by
            apply mul_le_mul hAnorm
            · exact hD
            · exact norm_nonneg _
            · exact hb
          _ = b * ((m + 2).choose 2 : ℝ) * b ^ m * δ := by
            simp only [mul_assoc]
      have hleak_step :
          ‖L‖ ≤ ((m + 2 : ℕ) : ℝ) * b ^ (m + 1) * δ := by
        have hs := hsource (m + 3) (by omega)
        have hsub_one : m + 3 - 1 = m + 2 := by omega
        have hsub_two : m + 3 - 2 = m + 1 := by omega
        rw [hsub_one, hsub_two] at hs
        exact show ‖L‖ ≤ ((m + 2 : ℕ) : ℝ) * b ^ (m + 1) * δ from hs
      calc
        ‖A * D‖ + ‖L‖ ≤
            b * ((m + 2).choose 2 : ℝ) * b ^ m * δ +
              ((m + 2 : ℕ) : ℝ) * b ^ (m + 1) * δ :=
                add_le_add hcompressed hleak_step
        _ = ((m + 3).choose 2 : ℝ) * b ^ (m + 1) * δ := by
              have hchoose : (m + 3).choose 2 = (m + 2).choose 2 + (m + 2) := by
                calc
                  (m + 3).choose 2 = (m + 2).choose 1 + (m + 2).choose 2 := by
                    simpa only [Nat.succ_eq_add_one] using Nat.choose_succ_succ (m + 2) 1
                  _ = (m + 2) + (m + 2).choose 2 := by rw [Nat.choose_one_right]
                  _ = (m + 2).choose 2 + (m + 2) := Nat.add_comm _ _
              rw [hchoose]
              push_cast
              ring

#print axioms compressed_power_defect

end D5.S3.Quantum.Dynamics.CompressedPowerDefect
