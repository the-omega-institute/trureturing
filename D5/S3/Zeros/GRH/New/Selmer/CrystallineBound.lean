/- GID: D5/S3/Zeros/GRH/New/Selmer/CrystallineBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/CrystallineBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.CrystallineBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/CrystallineBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.CrystallineRank
import D5.S3.Zeros.GRH.New.Lift.ExponentTheorems
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Crystalline losses above ℓ are affordable (see New.Selmer.RibetElement).

This file: Case analysis on ℓ bounding crystalline classes modulo those orthogonal to congruent
lattices. -/

open Lift Nat Module Finset Real

/-- Local loss, crystalline case. Let L be crystalline with jumps in U'; let U, U' lie in
opposite windows `Lift.IsInJumpWindow` at b + δ (thick) or G + δ (thin), with the listed conditions
on sizes and on a Kummer chart. Assume U' lies in [−η, 0], or negative members of U' and
negative members of U are ≤ −h/2 with ≤ μ jumps per embedding in [−η, η]. Then Z_f(L) modulo
`Lift.cupOrthogonal` for crystalline lattices with jumps in U has normalised length ≤ [G_ℓ :
j(Γ)]·y if y ≥ 10⁵(rk L·⌊2λ/Q⌋·m + μλ), λ = `lambdaLoss`. -/
lemma crystalline_defect_le {ℓ} [hp : ThePrime ℓ] [Γ : GroupOverGp ℓ] [TopologicalSpace Γ]
    {O : CoeffRing ℓ} {L : GalLattice O Γ} (Q m h μ : ℕ) {G b δ η W} {th ε : _ →
  _} {U U'} (Q₀ : 0 < Q) (hQ : 99 * (Q * Q + (W + 1) * Q + Q + W + m) ≤ h) (hG : 99 * h ^ 3 ≤
  G) (hb : 99 * (G * h ^ 3 + G) ≤ b) (hm : 2 * (4 * b : ℝ).log < m) (hδ : δ < η) (hη : 99 *
  ((η + W) * Q + η + h) ≤ h ^ 3) (hU : ∀ g, IsInJumpWindow η (-ε g) (ite (th g) b G + δ) W (U g))
  (hU' : ∀ g, IsInJumpWindow η (ε g) (ite (th g) b G + δ) W (U' g)) (hL : InClass ⊤ ⊥ U' L) (c :
  (∀ g, (∀ u < 0, u ∈ U g ∨ u ∈ U' g → 2 * u ≤ -h) ∧ ∑ u ∈ Icc (-↑η) ↑η, jump L.ρ g u ≤ μ) ∨ ∀ g,
  U' g ⊆ Icc (-η) 0) {y : NNReal} (hy : (10 ^ 5 * (finrank O L * (2 * lambdaLoss h b ℓ / Q * m) +
  μ * lambdaLoss h b ℓ) : ℕ) ≤ y) (k : KummerChart Γ) (ζ : k.LetterRoot O) (T s : _ → _) (hj :
  Topology.IsOpenEmbedding Γ.overGp.toGp) (hf : k.e * k.f = Γ.overGp.toGp.range.index) (he : k.e ≤
  h) (hs : ∀ g, th g ∨ Q < ℓ → th g = T (g ζ) ∧ ε g = s (g ζ)) (hu : k.IsUnramified ∧ 7 ≤ ℓ ∨ ℓ ≤
  Q ∧ ∀ z z', s z = s z') (hT : ℓ ≤ Q → ∀ᵉ (z) (a ∈ Icc 1 (ℓ.log (h ^ 3)))
  (b ∈ Icc 1 (ℓ.log (h ^ 3))), T z → T (z ^ ℓ ^ a) → ¬T (z ^ ℓ ^ (a + b))) : O.normLength (relLength
  (crysCocycles L.ρ) (cupOrthogonal (InClass ⊤ ⊥ U) L)) ≤ Γ.overGp.toGp.range.index * y := by
  have M {H} (h : H ≤ 4 * b := by omega) : ℓ.log H < m := by grw [← @cast_lt ℝ, ← hm, h,
    natLog_le_logb, logb, ← hp.out.two_le, ← one_sub_inv_le_log_of_pos] <;> norm_num; linarith
  have N {n} :=
    (lambdaLoss.eq_1 h b ℓ ▸ padicValNat_dvd_iff_le (n := n) (by simp [prod_eq_zero_iff])).1
  have A := (2 * lambdaLoss h b ℓ).lt_div_mul_add Q₀
  generalize lambdaLoss .. = v, _ / Q = K at *
  have Λ : 2 * b < ℓ * (v + 1) := (lt_mul_div_succ _ hp.out.pos).trans_le (by grw [← N (.mul_right
    pow_padicValNat_dvd _), ← padicValNat_mul_div_factorial, padicValNat_factorial_mul]; lia)
  have hv i : let z := ↑(theta (k.letterTeich i)); let w :=
        (IsInJumpWindow (ite (ℓ ≤ Q) (2 * G) η) · (ite (T z)
        (b + δ) (G + δ)) W); w (-s z) (k.letterJumps ζ U i) ∧ w (s z) (k.letterJumps ζ U' i) := by
    clear * - hs hU hU' hδ hη hG hQ
    simp [← ite_add, KummerChart.letterJumps, IsInJumpWindow, -cast_ite] at *
    generalize theta _ = z; grind
  have ex {x} (e : x ≤ m) := normLength_defect_le hL.isPotCrys (k := 10 ^ 4 * (K * x))
    (hy.trans' (mod_cast by grw [e]; ring; omega)) ∘ forall₂_imp
    (k.mem_cupOrthogonal_of_scaledCupBounds ζ hj le_top le_rfl hL (U := U) _ ⟨·, ·⟩)
  split_ifs at hv with hl <;> simp [hl] at hu
  · have D : 2 * (b + δ) < h ^ 2 * K := by
      nlinarith only [A, Λ, hl, hQ, h.le_mul_self, (by omega : h + δ ≤ b)]
    have := (lt_pow_succ_log_self hp.out.one_lt (h ^ 3)).le
    refine ex M fun _ _ _ _ P _ ↦ P.scaledCupBounds_sparse_thick (by omega : _ ≤ 9 * G) hv (by
      grw [← this, D, he]; linarith) (this.trans' (by omega)) (by omega) rfl
      (by clear * - hu; tauto) (by omega) (by grw [pow_log_le_self]; linarith; omega) (by
      simpa [(k.letterFrob.coe_pow · |>.trans (pow_iterate ..))] using hT hl <| theta <|
        k.letterTeich ·) ?_ ..
    grw [KummerChart.differentExp, ite_le_sup, padicValNat_le_nat_log, M, M, M,
      (by omega : _ + m ≤ h)]
    nlinarith only [D, hb]
  -- If `h³ ≤ v`, then `v` pays for the general bound. If not, `ℓ` is at least `9 G` and divides no
  -- integer near `b`, so it divides no nonzero integer near `0`, `± G` or `± b`.
  by_cases Z : h ^ 3 ≤ v
  · refine ex M fun _ _ _ _ P _ ↦ P.scaledCupBounds_two_sizes le_rfl hv ?_ rfl hu.1 hu.2 ?_ ?_ (by
      and_intros <;> nlinarith only [Λ, hl, hb, hη, hδ, Z, A, (by omega : Q ≤ h ^ 3)]) .. <;> omega
  obtain ⟨F, B⟩ := k.few_low_jumps ζ hj hu.1 (by omega) (a := 2 * (v + 1)) (by
    intro; grw [ite_le_sup, mul_left_comm, tsub_mul]; omega) (by omega) (by
    intro; split <;> omega) (fun _ y A d ↦ by_contra fun o ↦ Z (N (by
    obtain _ := Int.natAbs_le_of_dvd_ne_zero d o, (by nlinarith only [Λ, Z, hb] : 9 * G ≤ ℓ)
    grw [← dvd_prod_of_mem (a := y.natAbs), ← Int.natCast_dvd.1 d] <;> simp at A ⊢; omega))) hL hv
  exact if n : h / 5 ≤ v ∧ _ then by
    grw [B μ n.2, O.normLength_natCast_mul, ← hy, ← hf, (by omega : _ + 1 ≤ 6 * v),
      ← (M bot_le).succ_le, @Nat.le_of_mul_le_mul_right (W + 1) K _ (by omega) Q₀]
    simp [hu.1.2]; norm_cast; ring; omega
  else by simp [relLength_eq_zero.2 (F (by clear * - n c; grind))]
