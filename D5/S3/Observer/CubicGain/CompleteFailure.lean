/- GID: D5/S3/Observer/CubicGain/CompleteFailure
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/CompleteFailure
   mirror-E: none(waiver:unrestricted-complete-world-history)
   anchors: []
   utility: none
   digest: Complete polynomial worlds have unrestricted actual response fibers and stopping-guarded failure recursion. -/

import D5.S3.Observer.CubicGain.MixedTripleExclusion

/-! Entire polynomial targets and unrestricted actual-history failure. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix Classical

namespace D5.S3.Observer.CubicGain.CompleteFailure
open D5.S3.Observer.Linear.GainRay

theorem legal_source_iff (P : Mat) :
    LegalSource P ↔ (∀ i j, 0 < P i j) ∧ P.det = 0 ∧ Matrix.trace P = 1 := by
  constructor
  · intro h
    refine ⟨h.1, ?_, h.2.2⟩
    by_contra hn
    have hr := Matrix.rank_of_det_ne_zero hn
    rw [h.2.1] at hr
    norm_num at hr
  · rintro ⟨hp, hd, ht⟩
    have ha := hp 0 0
    have hz : P 0 0 ≠ 0 := ne_of_gt ha
    have htr : P 0 0 + P 1 1 = 1 := by
      simpa [Matrix.trace, Fin.sum_univ_two] using ht
    have hdet : P 0 0 * P 1 1 = P 0 1 * P 1 0 := by
      simpa [Matrix.det_fin_two, sub_eq_zero] using hd
    have hi : (1 + (P 1 0 / P 0 0) * (P 0 1 / P 0 0))⁻¹ = P 0 0 := by
      apply inv_eq_of_mul_eq_one_right
      field_simp
      nlinarith
    have he : P = sourceChart (P 1 0 / P 0 0) (P 0 1 / P 0 0) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sourceChart, hi]
      · field_simp
      · field_simp
      · field_simp
        nlinarith
    rw [he]
    exact source_chart_legal _ _ (div_pos (hp 1 0) ha) (div_pos (hp 0 1) ha)

/-- Exact correspondence with all original sources and all nonzero polynomials
of the specified degree bound. The drift is an arbitrary real number. -/
theorem whole_domain (d : ℕ) (P : Mat) (p : Polynomial ℝ) (δ : ℝ) :
    (∃ W : World d, W.source = P ∧ gain d W.coeff = p ∧ W.drift = δ) ↔
      (∀ i j, 0 < P i j) ∧ P.det = 0 ∧ Matrix.trace P = 1 ∧
        p ≠ 0 ∧ p.natDegree ≤ d := by
  constructor
  · rintro ⟨W, rfl, rfl, rfl⟩
    obtain ⟨hp, hd, ht⟩ := (legal_source_iff W.source).mp W.legal
    have hn : gain d W.coeff ≠ 0 := by
      intro h
      apply W.nonzero
      apply Polynomial.injective_ofFn (d + 1)
      simpa [gain] using h
    refine ⟨hp, hd, ht, hn, ?_⟩
    have hdeg := Polynomial.ofFn_degree_lt W.coeff
    have hnat := (Polynomial.natDegree_lt_iff_degree_lt hn).mpr hdeg
    omega
  · rintro ⟨hp, hd, ht, hn, hdeg⟩
    have he : Polynomial.ofFn (d + 1) (Polynomial.toFn (d + 1) p) = p :=
      Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
    have hc : Polynomial.toFn (d + 1) p ≠ 0 := by
      intro h
      rw [h, map_zero] at he
      exact hn he.symm
    exact ⟨⟨P, (legal_source_iff P).mpr ⟨hp, hd, ht⟩,
      Polynomial.toFn (d + 1) p, hc, δ⟩, rfl, he, rfl⟩

/-- No promise on sources, coefficients, roots, signs or drift is imposed. -/
def wholeSet {d : ℕ} (v : List Bool) (h : History v) : Set (World d) :=
  {W | readings W v = h}

/-- The full next-response intersection of the current candidate set. -/
def slice {d : ℕ} (K : Set (World d)) (v : List Bool) (E : Bool) (z : ℝ) :
    Set (World d) := {W | W ∈ K ∧ readAt W (v ++ [E]) (v.length + 1) = z}

/-- The guard at every node includes every possible early stop. -/
def Loses {d : ℕ} : ℕ → Set (World d) → List Bool → Prop
  | 0, K, _ => K.Nontrivial
  | n + 1, K, v => K.Nontrivial ∧ ∀ E : Bool, ∃ z : ℝ,
      Loses n (slice K v E z) (v ++ [E])

private theorem loses_guard {d n : ℕ} {K : Set (World d)} {v : List Bool}
    (h : Loses n K v) : K.Nontrivial := by
  cases n <;> exact (by first | exact h | exact h.1)

/-- Inclusion uses the same literal word and the same original clocks. -/
theorem loses_mono {d n : ℕ} {K K' : Set (World d)} {v : List Bool}
    (h : Loses n K v) (hsub : K ⊆ K') : Loses n K' v := by
  induction n generalizing K K' v with
  | zero => exact h.mono hsub
  | succ n ih =>
    refine ⟨h.1.mono hsub, ?_⟩
    intro E
    obtain ⟨z, hz⟩ := h.2 E
    exact ⟨z, ih hz (fun W hW => ⟨hsub hW.1, hW.2⟩)⟩

/-- Set recursion agrees with the existing finite native-world recursion. -/
theorem finite_losing_iff (n : ℕ) (T : Finset (World 3)) (v : List Bool) :
    Loses n (T : Set (World 3)) v ↔ MixedTripleExclusion.Losing n T v := by
  induction n generalizing T v with
  | zero =>
    change (∃ a ∈ T, ∃ b ∈ T, a ≠ b) ↔ 1 < T.card
    exact Finset.one_lt_card.symm
  | succ n ih =>
    have hs (E : Bool) (z : ℝ) :
        slice (T : Set (World 3)) v E z =
          (MixedTripleExclusion.responseSlice T v E z : Set (World 3)) := by
      ext W
      simp [slice, MixedTripleExclusion.responseSlice]
    simp only [Loses, MixedTripleExclusion.Losing, hs, ih]
    exact and_congr (by
      change (∃ a ∈ T, ∃ b ∈ T, a ≠ b) ↔ 1 < T.card
      exact Finset.one_lt_card.symm) Iff.rfl

private theorem readings_append {d : ℕ} (W Z : World d) (v : List Bool) (E : Bool)
    (h : readings W v = readings Z v)
    (hz : readAt W (v ++ [E]) (v.length + 1) =
      readAt Z (v ++ [E]) (v.length + 1)) :
    readings W (v ++ [E]) = readings Z (v ++ [E]) := by
  ext i
  by_cases hi : i.val ≤ v.length
  · have hh := congrFun h ⟨i.val, by omega⟩
    simpa [readings, readAt, List.take_append_of_le_length hi] using hh
  · have hib := i.isLt
    simp only [List.length_append, List.length_singleton] at hib
    have hi' : i.val = v.length + 1 := by omega
    simpa [readings, hi'] using hz

/-- Arbitrary deterministic actual-history decisions return either one next atom
or the entire target, with no palette or regularity restriction. -/
abbrev Policy (d : ℕ) := ∀ v : List Bool, History v → Bool ⊕ World d

/-- At most n additional readings; stopping remains available at every node. -/
def Identifies {d : ℕ} (P : Policy d) : ℕ → List Bool → World d → Prop
  | 0, v, W => P v (readings W v) = .inr W
  | n + 1, v, W => match P v (readings W v) with
      | .inr Z => Z = W
      | .inl E => Identifies P n (v ++ [E]) W

/-- Every guarded failure tree excludes every actual-history policy, including
policies that stop before exhausting the horizon. -/
theorem loses_excludes_policy {d n : ℕ} (K : Set (World d)) (v : List Bool)
    (h : History v) (hc : K ⊆ wholeSet v h) (hl : Loses n K v) (P : Policy d) :
    ¬ ∀ W ∈ K, Identifies P n v W := by
  intro hs
  induction n generalizing K v with
  | zero =>
    obtain ⟨W, hW, Z, hZ, hne⟩ := hl
    have hw := hs W hW
    have hz := hs Z hZ
    change P v (readings W v) = .inr W at hw
    change P v (readings Z v) = .inr Z at hz
    have hcw : readings W v = h := hc hW
    have hcz : readings Z v = h := hc hZ
    rw [hcw] at hw
    rw [hcz] at hz
    exact hne (Sum.inr.inj (hw.symm.trans hz))
  | succ n ih =>
    cases hp : P v h with
    | inr U =>
      obtain ⟨W, hW, Z, hZ, hne⟩ := hl.1
      have hw := hs W hW
      have hz := hs Z hZ
      have hcw : readings W v = h := hc hW
      have hcz : readings Z v = h := hc hZ
      simp only [Identifies, hcw, hp] at hw
      simp only [Identifies, hcz, hp] at hz
      exact hne (hw.symm.trans hz)
    | inl E =>
      obtain ⟨z, hz⟩ := hl.2 E
      obtain ⟨W, hW, Z, hZ, hne⟩ := loses_guard hz
      have hc' : slice K v E z ⊆ wholeSet (v ++ [E]) (readings W (v ++ [E])) := by
        intro U hU
        apply readings_append
        · exact (hc hU.1).trans (hc hW.1).symm
        · exact hU.2.trans hW.2.symm
      apply ih (slice K v E z) (v ++ [E]) (readings W (v ++ [E])) hc' hz
      intro U hU
      have hu := hs U hU.1
      have hcu : readings U v = h := hc hU.1
      simpa only [Identifies, hcu, hp] using hu

end D5.S3.Observer.CubicGain.CompleteFailure
