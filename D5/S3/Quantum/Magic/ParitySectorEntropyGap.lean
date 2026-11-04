/- GID: D5/S3/Quantum/Magic/ParitySectorEntropyGap
   generality: G
   mirror-B: D5/B/S3/Quantum/Magic/ParitySectorEntropyGap
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Extrinsic terms, positive stabilizer-entropy gaps, and parity-sector comparisons. -/

import D5.S3.Quantum.Magic.ParitySectorMoments

/-!
# Extrinsic terms and positive stabilizer-entropy gaps of the qudit parity sectors

Closed-form extrinsic fourth-moment scores of the even and odd qudit parity sectors for all odd
dimensions `d ≥ 3` (including the `8`-element order-`3` Weyl label correction when `3 ∣ d`),
four-branch average stabilizer-entropy gap formulas classified by `d mod 4` and divisibility by `3`,
universal positivity across all odd `d ≥ 3`, and comparison with the whole-space intrinsic average
when `3 ∤ d`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Magic.ParitySectorEntropyGap

open D5.S3.Quantum.Magic.SubspaceStabilizerEntropy
open D5.S3.Quantum.Magic.ParitySectorMoments

/-- Closed-form real extrinsic score `X(E_d)` of the even parity sector for odd `d ≥ 3`. -/
def evenExtrinsicFormula (d : ℕ) : ℝ :=
  if 3 ∣ d then
    4 / ((d : ℝ) + 3) + 64 / (((d : ℝ) + 1) * ((d : ℝ) + 3) * ((d : ℝ) + 5) * ((d : ℝ) + 7))
  else
    4 / ((d : ℝ) + 3)

/-- Closed-form real extrinsic score `X(O_d)` of the odd parity sector for odd `d ≥ 3`. -/
def oddExtrinsicFormula (d : ℕ) : ℝ :=
  if 3 ∣ d then
    4 / ((d : ℝ) + 3) - 64 / (((d : ℝ) - 1) * ((d : ℝ) + 1) * ((d : ℝ) + 3) * ((d : ℝ) + 5))
  else
    4 / ((d : ℝ) + 3)

/-- Closed-form real average stabilizer-entropy gap `ΔM(E_d)` of the even parity sector. -/
def evenGapFormula (d : ℕ) : ℝ :=
  if d % 4 = 1 then
    if 3 ∣ d then
      2 * ((d : ℝ) ^ 2 + 4 * (d : ℝ) - 13) / (((d : ℝ) + 1) * ((d : ℝ) + 5) * ((d : ℝ) + 7))
    else
      2 * ((d : ℝ) - 1) / (((d : ℝ) + 3) * ((d : ℝ) + 5))
  else
    if 3 ∣ d then
      2 * ((d : ℝ) ^ 3 + 7 * (d : ℝ) ^ 2 + 11 * (d : ℝ) - 27) /
        (((d : ℝ) + 1) * ((d : ℝ) + 3) * ((d : ℝ) + 5) * ((d : ℝ) + 7))
    else
      2 * ((d : ℝ) + 1) / (((d : ℝ) + 3) * ((d : ℝ) + 7))

/-- Closed-form real average stabilizer-entropy gap `ΔM(O_d)` of the odd parity sector. -/
def oddGapFormula (d : ℕ) : ℝ :=
  if d % 4 = 3 then
    if 3 ∣ d then
      2 * ((d : ℝ) ^ 3 + 5 * (d : ℝ) ^ 2 - (d : ℝ) + 27) /
        (((d : ℝ) - 1) * ((d : ℝ) + 1) * ((d : ℝ) + 3) * ((d : ℝ) + 5))
    else
      2 / ((d : ℝ) + 3)
  else
    if 3 ∣ d then
      2 * ((d : ℝ) ^ 2 + 2 * (d : ℝ) + 5) / (((d : ℝ) - 1) * ((d : ℝ) + 1) * ((d : ℝ) + 5))
    else
      2 * ((d : ℝ) ^ 2 + 6 * (d : ℝ) + 17) / (((d : ℝ) + 1) * ((d : ℝ) + 3) * ((d : ℝ) + 5))

private theorem order_three_label_card (d : ℕ) [NeZero d] :
    (Finset.univ.filter (fun a : ZMod d × ZMod d => a ≠ (0, 0) ∧ weylLabelOrder d a = 3)).card =
      if 3 ∣ d then 8 else 0 := by
  have hg_mul (a : ZMod d × ZMod d) :
      Nat.gcd a.1.val (Nat.gcd a.2.val d) * weylLabelOrder d a = d :=
    Nat.mul_div_cancel' (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))
  by_cases hdvd : 3 ∣ d
  · simp only [hdvd, ↓reduceIte]
    rcases hdvd with ⟨q, hdq⟩
    have hq_pos : 0 < q := by have := NeZero.ne d; omega
    let φ : Fin 3 × Fin 3 → ZMod d × ZMod d :=
      fun p => (((p.1.val * q : ℕ) : ZMod d), ((p.2.val * q : ℕ) : ZMod d))
    have hval (i : Fin 3) : ((i.val * q : ℕ) : ZMod d).val = i.val * q := by
      rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by have := i.isLt; nlinarith)
    have hφ0 : φ (0, 0) = (0, 0) := by simp [φ]
    have hφ_inj : Function.Injective φ := fun p₁ p₂ h => by
      have h1 := congrArg (fun x : ZMod d × ZMod d => x.1.val) h
      have h2 := congrArg (fun x : ZMod d × ZMod d => x.2.val) h
      dsimp [φ] at h1 h2; rw [hval, hval] at h1; rw [hval, hval] at h2
      exact Prod.ext (Fin.ext (Nat.eq_of_mul_eq_mul_right hq_pos h1))
        (Fin.ext (Nat.eq_of_mul_eq_mul_right hq_pos h2))
    have hset : Finset.univ.filter (fun a : ZMod d × ZMod d =>
          a ≠ (0, 0) ∧ weylLabelOrder d a = 3) =
        Finset.image φ (Finset.univ.erase ((0 : Fin 3), (0 : Fin 3))) := by
      ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_erase, and_true]
      constructor
      · rintro ⟨ha, hord⟩
        have hgq : Nat.gcd a.1.val (Nat.gcd a.2.val d) = q := by
          have hgm := hg_mul a; rw [hord] at hgm; omega
        rcases (hgq ▸ Nat.gcd_dvd_left a.1.val (Nat.gcd a.2.val d) : q ∣ a.1.val) with ⟨r₁, hr₁⟩
        rcases (hgq ▸ Nat.dvd_trans (Nat.gcd_dvd_right a.1.val _) (Nat.gcd_dvd_left a.2.val d) :
          q ∣ a.2.val) with ⟨r₂, hr₂⟩
        have hr₁_lt : r₁ < 3 := by have := ZMod.val_lt a.1; nlinarith
        have hr₂_lt : r₂ < 3 := by have := ZMod.val_lt a.2; nlinarith
        let p : Fin 3 × Fin 3 := (⟨r₁, hr₁_lt⟩, ⟨r₂, hr₂_lt⟩)
        have hφp : φ p = a := by
          dsimp [φ, p]; rw [mul_comm r₁ q, ← hr₁, mul_comm r₂ q, ← hr₂]
          exact Prod.ext (ZMod.natCast_zmod_val a.1) (ZMod.natCast_zmod_val a.2)
        exact ⟨p, fun hp => ha (hφp ▸ hp ▸ hφ0), hφp⟩
      · rintro ⟨p, hp0, rfl⟩
        refine ⟨fun h => hp0 (hφ_inj (h.trans hφ0.symm)), ?_⟩
        have hgcd1 : Nat.gcd p.1.val (Nat.gcd p.2.val 3) = 1 := by
          have hp_ne : p.1.val ≠ 0 ∨ p.2.val ≠ 0 := by
            by_contra h; rw [not_or, not_ne_iff, not_ne_iff] at h
            exact hp0 (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
          have := p.1.isLt; have := p.2.isLt
          rcases (by omega : p.1.val = 0 ∨ p.1.val = 1 ∨ p.1.val = 2) with h1 | h1 | h1 <;>
            rcases (by omega : p.2.val = 0 ∨ p.2.val = 1 ∨ p.2.val = 2) with h2 | h2 | h2 <;>
            simp_all
        calc weylLabelOrder d (φ p)
            = (3 * q) / Nat.gcd (p.1.val * q) (Nat.gcd (p.2.val * q) (3 * q)) := by
                dsimp only [weylLabelOrder, φ]; rw [hval, hval, hdq]
          _ = (3 * q) / (Nat.gcd p.1.val (Nat.gcd p.2.val 3) * q) := by
                rw [Nat.gcd_mul_right, Nat.gcd_mul_right]
          _ = (3 * q) / q := by rw [hgcd1, one_mul]
          _ = 3 := Nat.mul_div_cancel 3 hq_pos
    rw [hset, Finset.card_image_of_injective _ hφ_inj, Finset.card_erase_of_mem (Finset.mem_univ _)]
    decide
  · simp only [hdvd, ↓reduceIte, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
      forall_true_left, not_and]
    intro a _ hord
    exact hdvd ⟨Nat.gcd a.1.val (Nat.gcd a.2.val d),
      by have := hg_mul a; rw [hord] at this; linarith⟩

private theorem extrinsic_from_two_level_moments {d : ℕ} [NeZero d] {S : Type} [Fintype S]
    (E : Matrix (ZMod d) S ℂ) (G G3 : ℝ)
    (horig : labelFourthMoment E (0, 0) = 1)
    (hgen : ∀ a, a ≠ (0, 0) → weylLabelOrder d a ≠ 3 → labelFourthMoment E a = (G : ℂ))
    (hord3 : ∀ a, a ≠ (0, 0) → weylLabelOrder d a = 3 → labelFourthMoment E a = (G3 : ℂ)) :
    let N3 := (Finset.univ.filter (fun a : ZMod d × ZMod d =>
      a ≠ (0, 0) ∧ weylLabelOrder d a = 3)).card
    extrinsicScore E =
      ((((d : ℝ)⁻¹ * (1 + ((d : ℝ) ^ 2 - 1 - (N3 : ℝ)) * G + (N3 : ℝ) * G3)) : ℝ) : ℂ) := by
  intro N3
  let S3 := Finset.univ.filter (fun a : ZMod d × ZMod d => a ≠ (0, 0) ∧ weylLabelOrder d a = 3)
  have hpt (a : ZMod d × ZMod d) : labelFourthMoment E a =
      (G : ℂ) + (if a = (0, 0) then ((1 - G : ℝ) : ℂ) else 0) +
        (if a ∈ S3 then ((G3 - G : ℝ) : ℂ) else 0) := by
    by_cases ha0 : a = (0, 0)
    · subst ha0; simp [S3, horig]
    · by_cases h3 : weylLabelOrder d a = 3
      · simp [S3, ha0, h3, hord3 a ha0 h3]
      · simp [S3, ha0, h3, hgen a ha0 h3]
  rw [(fourth_moment_cycle_and_hermitian_formula d).2.2.2.2.2.1 E]
  simp_rw [hpt, Finset.sum_add_distrib]
  have hs1 : (∑ _a : ZMod d × ZMod d, (G : ℂ)) = (((d : ℝ) ^ 2 * G : ℝ) : ℂ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul]
    push_cast; ring
  have hs2 : (∑ a : ZMod d × ZMod d, (if a = (0, 0) then ((1 - G : ℝ) : ℂ) else 0)) =
      ((1 - G : ℝ) : ℂ) := by simp
  have hs3 : (∑ a : ZMod d × ZMod d, (if a ∈ S3 then ((G3 - G : ℝ) : ℂ) else 0)) =
      (((N3 : ℝ) * (G3 - G) : ℝ) : ℂ) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]; push_cast; rfl
  rw [hs1, hs2, hs3]; push_cast; ring

/-- Closed-form extrinsic fourth-moment scores of the even and odd qudit parity sectors for all odd
dimensions `d ≥ 3`, together with the `8`-element order-`3` Weyl label count when `3 ∣ d` and
invariance across all isometric sector embeddings. -/
theorem parity_sector_extrinsic_terms (d : ℕ) [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d) :
    (Finset.univ.filter (fun a : ZMod d × ZMod d => a ≠ (0, 0) ∧ weylLabelOrder d a = 3)).card =
      (if 3 ∣ d then 8 else 0) ∧
    (extrinsicScore (evenIsometry d) = (evenExtrinsicFormula d : ℂ) ∧
      extrinsicScore (oddIsometry d) = (oddExtrinsicFormula d : ℂ)) ∧
    (∀ {S : Type} [Fintype S] [DecidableEq S] [NeZero (Fintype.card S)]
        (E : Matrix (ZMod d) S ℂ), Eᴴ * E = 1 →
      (LinearMap.range E.mulVecLin = evenSectorSubspace d →
        extrinsicScore E = (evenExtrinsicFormula d : ℂ)) ∧
      (LinearMap.range E.mulVecLin = oddSectorSubspace d →
        extrinsicScore E = (oddExtrinsicFormula d : ℂ))) := by
  have hcard3 := order_three_label_card d
  obtain ⟨⟨horigE, horigO⟩, _⟩ := parity_clifford_label_reduction d hd3 hd
  let G : ℝ := (3 : ℝ) / (((d : ℝ) + 1) * ((d : ℝ) + 3))
  let G3E : ℝ := (3 * (d : ℝ) + 35) / (((d : ℝ) + 1) * ((d : ℝ) + 5) * ((d : ℝ) + 7))
  let G3O : ℝ := (3 * (d : ℝ) - 5) / (((d : ℝ) - 1) * ((d : ℝ) + 1) * ((d : ℝ) + 5))
  have hd3_r : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd3
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd_m1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hd_p1 : (d : ℝ) + 1 ≠ 0 := by linarith
  have hd_p3 : (d : ℝ) + 3 ≠ 0 := by linarith
  have hd_p5 : (d : ℝ) + 5 ≠ 0 := by linarith
  have hd_p7 : (d : ℝ) + 7 ≠ 0 := by linarith
  have hE : extrinsicScore (evenIsometry d) = (evenExtrinsicFormula d : ℂ) := by
    have hsum := extrinsic_from_two_level_moments (evenIsometry d) G G3E horigE
      (fun a ha hne => by
        rw [((parity_nonzero_label_fourth_moment d hd3 hd a ha).1 hne).1]; push_cast [G]; rfl)
      (fun a ha heq => by
        rw [((parity_nonzero_label_fourth_moment d hd3 hd a ha).2 heq).1]; push_cast [G3E]; rfl)
    dsimp only at hsum; rw [hsum, hcard3]; unfold evenExtrinsicFormula; congr 1
    by_cases hdvd : 3 ∣ d <;> simp only [hdvd, ↓reduceIte, Nat.cast_ofNat, Nat.cast_zero, G, G3E]
    · field_simp [hd0, hd_p1, hd_p3, hd_p5, hd_p7]; ring
    · field_simp [hd0, hd_p1, hd_p3]; ring
  have hO : extrinsicScore (oddIsometry d) = (oddExtrinsicFormula d : ℂ) := by
    have hsum := extrinsic_from_two_level_moments (oddIsometry d) G G3O horigO
      (fun a ha hne => by
        rw [((parity_nonzero_label_fourth_moment d hd3 hd a ha).1 hne).2]; push_cast [G]; rfl)
      (fun a ha heq => by
        rw [((parity_nonzero_label_fourth_moment d hd3 hd a ha).2 heq).2]; push_cast [G3O]; rfl)
    dsimp only at hsum; rw [hsum, hcard3]; unfold oddExtrinsicFormula; congr 1
    by_cases hdvd : 3 ∣ d <;> simp only [hdvd, ↓reduceIte, Nat.cast_ofNat, Nat.cast_zero, G, G3O]
    · field_simp [hd0, hd_m1, hd_p1, hd_p3, hd_p5]; ring
    · field_simp [hd0, hd_p1, hd_p3]; ring
  refine ⟨hcard3, ⟨hE, hO⟩, fun {S} _ _ _ E hEE => ?_⟩
  have : NeZero (Fintype.card (Fin ((d + 1) / 2))) := ⟨by rw [Fintype.card_fin]; omega⟩
  have : NeZero (Fintype.card (Fin ((d - 1) / 2))) := ⟨by rw [Fintype.card_fin]; omega⟩
  obtain ⟨_, ⟨hEE_iso, _, hrangeE, _⟩, ⟨hOO_iso, _, hrangeO, _⟩, _⟩ :=
    parity_sectors_bases_and_isometries d hd3 hd
  exact ⟨fun hr => (((subspace_gap_isometry_invariance_and_twirl d).1 E (evenIsometry d)
      hEE hEE_iso).2 (hr.trans hrangeE.symm)).2.2.1.trans hE,
    fun hr => (((subspace_gap_isometry_invariance_and_twirl d).1 E (oddIsometry d)
      hEE hOO_iso).2 (hr.trans hrangeO.symm)).2.2.1.trans hO⟩

private theorem gap_formulas_pos {d : ℕ} (hd3 : 3 ≤ d) :
    0 < evenGapFormula d ∧ 0 < oddGapFormula d := by
  let t : ℝ := (d : ℝ) - 3
  have ht : 0 ≤ t := sub_nonneg.mpr (by exact_mod_cast hd3)
  have hd_t : (d : ℝ) = t + 3 := by dsimp [t]; ring
  constructor
  · unfold evenGapFormula; split_ifs
    · rw [hd_t, show 2 * ((t + 3) ^ 2 + 4 * (t + 3) - 13) = 2 * t ^ 2 + 20 * t + 16 by ring]
      positivity
    · rw [hd_t, show 2 * (t + 3 - 1) = 2 * t + 4 by ring]; positivity
    · rw [hd_t, show 2 * ((t + 3) ^ 3 + 7 * (t + 3) ^ 2 + 11 * (t + 3) - 27) =
        2 * t ^ 3 + 32 * t ^ 2 + 160 * t + 192 by ring]; positivity
    · rw [hd_t, show 2 * (t + 3 + 1) = 2 * t + 8 by ring]; positivity
  · unfold oddGapFormula; split_ifs
    · rw [hd_t, show 2 * ((t + 3) ^ 3 + 5 * (t + 3) ^ 2 - (t + 3) + 27) =
        2 * t ^ 3 + 28 * t ^ 2 + 112 * t + 192 by ring, show t + 3 - 1 = t + 2 by ring]; positivity
    · rw [hd_t]; positivity
    · rw [hd_t, show 2 * ((t + 3) ^ 2 + 2 * (t + 3) + 5) = 2 * t ^ 2 + 16 * t + 40 by ring,
        show t + 3 - 1 = t + 2 by ring]; positivity
    · rw [hd_t, show 2 * ((t + 3) ^ 2 + 6 * (t + 3) + 17) = 2 * t ^ 2 + 24 * t + 88 by ring]
      positivity

private theorem canonical_sector_gaps {d : ℕ} [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d) :
    @aseGap d _ (Fin ((d + 1) / 2)) _ ⟨by rw [Fintype.card_fin]; omega⟩ (evenIsometry d) =
      (evenGapFormula d : ℂ) ∧
    @aseGap d _ (Fin ((d - 1) / 2)) _ ⟨by rw [Fintype.card_fin]; omega⟩ (oddIsometry d) =
      (oddGapFormula d : ℂ) := by
  have hparE : Odd ((d + 1) / 2) ↔ d % 4 = 1 := by
    rcases hd with ⟨m, _⟩; rw [Nat.odd_iff]; omega
  have hparO : Odd ((d - 1) / 2) ↔ d % 4 = 3 := by
    rcases hd with ⟨m, _⟩; rw [Nat.odd_iff]; omega
  obtain ⟨_, ⟨hEE_ext, hOO_ext⟩, _⟩ := parity_sector_extrinsic_terms d hd3 hd
  have hint := (intrinsic_term_and_rank_one_entropy d).1
  have : NeZero ((d + 1) / 2) := ⟨by omega⟩
  have : NeZero ((d - 1) / 2) := ⟨by omega⟩
  rcases hd with ⟨m, hdm⟩
  have hd_r : (d : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hdm
  have hd3_r : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd3
  have hm1_r : (1 : ℝ) ≤ (m : ℝ) := by linarith
  have hkE_c : (((d + 1) / 2 : ℕ) : ℂ) = (((m : ℝ) + 1 : ℝ) : ℂ) := by
    exact_mod_cast (by omega : (d + 1) / 2 = m + 1)
  have hkO_c : (((d - 1) / 2 : ℕ) : ℂ) = ((m : ℝ) : ℂ) := by
    exact_mod_cast (by omega : (d - 1) / 2 = m)
  have hd_m1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hd_p1 : (d : ℝ) + 1 ≠ 0 := by linarith
  have hd_p3 : (d : ℝ) + 3 ≠ 0 := by linarith
  have hd_p5 : (d : ℝ) + 5 ≠ 0 := by linarith
  have hd_p7 : (d : ℝ) + 7 ≠ 0 := by linarith
  constructor
  · unfold aseGap; simp only [Fintype.card_fin, hEE_ext]
    by_cases hmod : d % 4 = 1
    · rw [(hint ((d + 1) / 2)).1 (hparE.mpr hmod), hkE_c]
      unfold evenGapFormula evenExtrinsicFormula; simp only [hmod, ↓reduceIte]
      by_cases hdvd : 3 ∣ d <;> simp only [hdvd, ↓reduceIte]
      · rw [show (3 : ℂ) / ((((m : ℝ) + 1 : ℝ) : ℂ) + 2) = (((3 / ((m : ℝ) + 3)) : ℝ) : ℂ) by
          push_cast; ring, ← Complex.ofReal_sub]; congr 1
        field_simp [show (m : ℝ) + 3 ≠ 0 by positivity, hd_p1, hd_p3, hd_p5, hd_p7]
        rw [hd_r]; ring
      · rw [show (3 : ℂ) / ((((m : ℝ) + 1 : ℝ) : ℂ) + 2) = (((3 / ((m : ℝ) + 3)) : ℝ) : ℂ) by
          push_cast; ring, ← Complex.ofReal_sub]; congr 1
        field_simp [show (m : ℝ) + 3 ≠ 0 by positivity, hd_p3, hd_p5]; rw [hd_r]; ring
    · have hev : Even ((d + 1) / 2) := Nat.not_odd_iff_even.mp (mt hparE.mp hmod)
      rw [(hint ((d + 1) / 2)).2 hev, hkE_c]
      unfold evenGapFormula evenExtrinsicFormula; simp only [hmod, ↓reduceIte]
      have hint_r : (3 * ((((m : ℝ) + 1 : ℝ) : ℂ) + 2)) /
          (((((m : ℝ) + 1 : ℝ) : ℂ) + 1) * ((((m : ℝ) + 1 : ℝ) : ℂ) + 3)) =
          (((3 * ((m : ℝ) + 3)) / (((m : ℝ) + 2) * ((m : ℝ) + 4)) : ℝ) : ℂ) := by push_cast; ring
      rw [hint_r]
      by_cases hdvd : 3 ∣ d <;> simp only [hdvd, ↓reduceIte] <;> rw [← Complex.ofReal_sub] <;>
        congr 1
      · field_simp [show (m : ℝ) + 2 ≠ 0 by positivity, show (m : ℝ) + 4 ≠ 0 by positivity,
          hd_p1, hd_p3, hd_p5, hd_p7]; rw [hd_r]; ring
      · field_simp [show (m : ℝ) + 2 ≠ 0 by positivity, show (m : ℝ) + 4 ≠ 0 by positivity,
          hd_p3, hd_p7]; rw [hd_r]; ring
  · unfold aseGap; simp only [Fintype.card_fin, hOO_ext]
    by_cases hmod : d % 4 = 3
    · rw [(hint ((d - 1) / 2)).1 (hparO.mpr hmod), hkO_c]
      unfold oddGapFormula oddExtrinsicFormula; simp only [hmod, ↓reduceIte]
      rw [show (3 : ℂ) / (((m : ℝ) : ℂ) + 2) = (((3 / ((m : ℝ) + 2)) : ℝ) : ℂ) by push_cast; rfl]
      by_cases hdvd : 3 ∣ d <;> simp only [hdvd, ↓reduceIte] <;> rw [← Complex.ofReal_sub] <;>
        congr 1
      · field_simp [show (m : ℝ) + 2 ≠ 0 by positivity, hd_m1, hd_p1, hd_p3, hd_p5]
        rw [hd_r]; ring
      · field_simp [show (m : ℝ) + 2 ≠ 0 by positivity, hd_p3]; rw [hd_r]; ring
    · have hev : Even ((d - 1) / 2) := Nat.not_odd_iff_even.mp (mt hparO.mp hmod)
      rw [(hint ((d - 1) / 2)).2 hev, hkO_c]
      unfold oddGapFormula oddExtrinsicFormula; simp only [hmod, ↓reduceIte]
      have hint_r : (3 * (((m : ℝ) : ℂ) + 2)) / ((((m : ℝ) : ℂ) + 1) * (((m : ℝ) : ℂ) + 3)) =
          (((3 * ((m : ℝ) + 2)) / (((m : ℝ) + 1) * ((m : ℝ) + 3)) : ℝ) : ℂ) := by push_cast; rfl
      rw [hint_r]
      by_cases hdvd : 3 ∣ d <;> simp only [hdvd, ↓reduceIte] <;> rw [← Complex.ofReal_sub] <;>
        congr 1
      · field_simp [show (m : ℝ) + 1 ≠ 0 by positivity, show (m : ℝ) + 3 ≠ 0 by positivity,
          hd_m1, hd_p1, hd_p3, hd_p5]; rw [hd_r]; ring
      · field_simp [show (m : ℝ) + 1 ≠ 0 by positivity, show (m : ℝ) + 3 ≠ 0 by positivity,
          hd_p1, hd_p3, hd_p5]; rw [hd_r]; ring

/-- Four-branch closed-form average stabilizer-entropy gaps of the even and odd qudit parity
sectors classified by `d mod 4` and divisibility by `3`, dimension-parity criteria, and universal
positivity for every odd `d ≥ 3` and every isometric sector embedding. -/
theorem parity_sector_gaps_and_positivity (d : ℕ) [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d) :
    ((Odd ((d + 1) / 2) ↔ d % 4 = 1) ∧ (Odd ((d - 1) / 2) ↔ d % 4 = 3)) ∧
    (0 < evenGapFormula d ∧ 0 < oddGapFormula d) ∧
    (∀ {S : Type} [Fintype S] [DecidableEq S] [NeZero (Fintype.card S)]
        (E : Matrix (ZMod d) S ℂ), Eᴴ * E = 1 →
      (LinearMap.range E.mulVecLin = evenSectorSubspace d →
        aseGap E = (evenGapFormula d : ℂ) ∧
        (d % 4 = 1 ∧ ¬ (3 ∣ d) →
          aseGap E = ((2 * ((d : ℝ) - 1) / (((d : ℝ) + 3) * ((d : ℝ) + 5)) : ℝ) : ℂ)) ∧
        (d % 4 = 1 ∧ 3 ∣ d →
          aseGap E = ((2 * ((d : ℝ) ^ 2 + 4 * (d : ℝ) - 13) /
            (((d : ℝ) + 1) * ((d : ℝ) + 5) * ((d : ℝ) + 7)) : ℝ) : ℂ)) ∧
        (d % 4 = 3 ∧ ¬ (3 ∣ d) →
          aseGap E = ((2 * ((d : ℝ) + 1) / (((d : ℝ) + 3) * ((d : ℝ) + 7)) : ℝ) : ℂ)) ∧
        (d % 4 = 3 ∧ 3 ∣ d →
          aseGap E = ((2 * ((d : ℝ) ^ 3 + 7 * (d : ℝ) ^ 2 + 11 * (d : ℝ) - 27) /
            (((d : ℝ) + 1) * ((d : ℝ) + 3) * ((d : ℝ) + 5) * ((d : ℝ) + 7)) : ℝ) : ℂ)) ∧
        0 < (aseGap E).re ∧ (aseGap E).im = 0) ∧
      (LinearMap.range E.mulVecLin = oddSectorSubspace d →
        aseGap E = (oddGapFormula d : ℂ) ∧
        (d % 4 = 3 ∧ ¬ (3 ∣ d) → aseGap E = ((2 / ((d : ℝ) + 3) : ℝ) : ℂ)) ∧
        (d % 4 = 3 ∧ 3 ∣ d →
          aseGap E = ((2 * ((d : ℝ) ^ 3 + 5 * (d : ℝ) ^ 2 - (d : ℝ) + 27) /
            (((d : ℝ) - 1) * ((d : ℝ) + 1) * ((d : ℝ) + 3) * ((d : ℝ) + 5)) : ℝ) : ℂ)) ∧
        (d % 4 = 1 ∧ ¬ (3 ∣ d) →
          aseGap E = ((2 * ((d : ℝ) ^ 2 + 6 * (d : ℝ) + 17) /
            (((d : ℝ) + 1) * ((d : ℝ) + 3) * ((d : ℝ) + 5)) : ℝ) : ℂ)) ∧
        (d % 4 = 1 ∧ 3 ∣ d →
          aseGap E = ((2 * ((d : ℝ) ^ 2 + 2 * (d : ℝ) + 5) /
            (((d : ℝ) - 1) * ((d : ℝ) + 1) * ((d : ℝ) + 5)) : ℝ) : ℂ)) ∧
        0 < (aseGap E).re ∧ (aseGap E).im = 0)) := by
  have hpar : (Odd ((d + 1) / 2) ↔ d % 4 = 1) ∧ (Odd ((d - 1) / 2) ↔ d % 4 = 3) := by
    rcases hd with ⟨m, _⟩; rw [Nat.odd_iff, Nat.odd_iff]; constructor <;> omega
  obtain ⟨hposE, hposO⟩ := gap_formulas_pos hd3
  obtain ⟨hcanE, hcanO⟩ := canonical_sector_gaps hd3 hd
  refine ⟨hpar, ⟨hposE, hposO⟩, fun {S} _ _ _ E hE => ?_⟩
  obtain ⟨hisoE, hisoO⟩ := (parity_sectors_bases_and_isometries d hd3 hd).2.2.2 E hE
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · have hgap : aseGap E = (evenGapFormula d : ℂ) := (hisoE hr).2.2.2.trans hcanE
    refine ⟨hgap, ?_, ?_, ?_, ?_, by rw [hgap, Complex.ofReal_re]; exact hposE,
      by rw [hgap, Complex.ofReal_im]⟩
    · rintro ⟨h1, h2⟩; rw [hgap]; simp [evenGapFormula, h1, h2]
    · rintro ⟨h1, h2⟩; rw [hgap]; simp [evenGapFormula, h1, h2]
    · rintro ⟨h1, h2⟩; rw [hgap]; simp [evenGapFormula, h1, h2]
    · rintro ⟨h1, h2⟩; rw [hgap]; simp [evenGapFormula, h1, h2]
  · have hgap : aseGap E = (oddGapFormula d : ℂ) := (hisoO hr).2.2.2.trans hcanO
    refine ⟨hgap, ?_, ?_, ?_, ?_, by rw [hgap, Complex.ofReal_re]; exact hposO,
      by rw [hgap, Complex.ofReal_im]⟩
    · rintro ⟨h1, h2⟩; rw [hgap]; simp [oddGapFormula, h1, h2]
    · rintro ⟨h1, h2⟩; rw [hgap]; simp [oddGapFormula, h1, h2]
    · rintro ⟨h1, h2⟩; rw [hgap]; simp [oddGapFormula, h1, h2]
    · rintro ⟨h1, h2⟩; rw [hgap]; simp [oddGapFormula, h1, h2]

/-- Comparison of the even and odd parity sectors against the whole-space intrinsic average when
`3 ∤ d`: both extrinsic scores equal `4 / (d + 3)`, strictly exceeding the ambient odd-dimension
intrinsic term `3 / (d + 2)`, so both sector gaps lie strictly below the random-subspace average
gap `I(k) - 3 / (d + 2)` of the same sector dimension. -/
theorem parity_sector_whole_space_comparison
    (d : ℕ) [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d) (hnd3 : ¬ (3 ∣ d)) :
    (evenExtrinsicFormula d = 4 / ((d : ℝ) + 3) ∧
      oddExtrinsicFormula d = 4 / ((d : ℝ) + 3)) ∧
    intrinsicTerm d = ((3 / ((d : ℝ) + 2) : ℝ) : ℂ) ∧
    (3 / ((d : ℝ) + 2) < evenExtrinsicFormula d ∧
      3 / ((d : ℝ) + 2) < oddExtrinsicFormula d) ∧
    (evenGapFormula d < (@intrinsicTerm ((d + 1) / 2) ⟨by omega⟩).re - 3 / ((d : ℝ) + 2) ∧
      oddGapFormula d < (@intrinsicTerm ((d - 1) / 2) ⟨by omega⟩).re - 3 / ((d : ℝ) + 2)) := by
  have hextE : evenExtrinsicFormula d = 4 / ((d : ℝ) + 3) := by simp [evenExtrinsicFormula, hnd3]
  have hextO : oddExtrinsicFormula d = 4 / ((d : ℝ) + 3) := by simp [oddExtrinsicFormula, hnd3]
  have hint_d : intrinsicTerm d = ((3 / ((d : ℝ) + 2) : ℝ) : ℂ) := by
    rw [((intrinsic_term_and_rank_one_entropy d).1 d).1 hd]; push_cast; rfl
  have hd3_r : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd3
  have hlt : 3 / ((d : ℝ) + 2) < 4 / ((d : ℝ) + 3) := sub_pos.mp (by
    rw [show 4 / ((d : ℝ) + 3) - 3 / ((d : ℝ) + 2) =
      ((d : ℝ) - 1) / (((d : ℝ) + 2) * ((d : ℝ) + 3)) by
        field_simp [show (d : ℝ) + 2 ≠ 0 by linarith, show (d : ℝ) + 3 ≠ 0 by linarith]; ring]
    have : 0 < (d : ℝ) - 1 := by linarith
    positivity)
  obtain ⟨hcanE, hcanO⟩ := canonical_sector_gaps hd3 hd
  obtain ⟨_, ⟨hEE_ext, hOO_ext⟩, _⟩ := parity_sector_extrinsic_terms d hd3 hd
  have hreE : evenGapFormula d =
      (@intrinsicTerm ((d + 1) / 2) ⟨by omega⟩).re - evenExtrinsicFormula d := by
    have h := congrArg Complex.re hcanE
    unfold aseGap at h; simp only [Fintype.card_fin, hEE_ext, Complex.sub_re,
      Complex.ofReal_re] at h
    exact h.symm
  have hreO : oddGapFormula d =
      (@intrinsicTerm ((d - 1) / 2) ⟨by omega⟩).re - oddExtrinsicFormula d := by
    have h := congrArg Complex.re hcanO
    unfold aseGap at h; simp only [Fintype.card_fin, hOO_ext, Complex.sub_re,
      Complex.ofReal_re] at h
    exact h.symm
  exact ⟨⟨hextE, hextO⟩, hint_d, ⟨hextE ▸ hlt, hextO ▸ hlt⟩,
    ⟨by linarith, by linarith⟩⟩

end D5.S3.Quantum.Magic.ParitySectorEntropyGap
