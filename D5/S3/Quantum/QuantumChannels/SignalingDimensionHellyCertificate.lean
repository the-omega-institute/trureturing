/- GID: D5/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: At most binomially many inputs certify classical signaling dimension. -/

import D5.S3.Estimation.DecisionRisk.DescentDefectBounds
import D5.S3.Estimation.DataProcessing.OrderedCoordinateHistoryInterpreter

/-! Finite shared randomness reduces simulation to intersecting convex sets indexed by inputs.
Deleting one simplex coordinate allows Helly's theorem to bound a separating input family. -/

open scoped BigOperators

namespace D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate

open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
  (IsRowStochastic deterministicPostprocess)
open D5.S3.Estimation.DataProcessing.OrderedCoordinateHistoryInterpreter
  (product_row_marginal)

/-- Source equation for classical simulation, with shared randomness indexed by some `Fin n`. -/
def IsSimulable {α : Type} {k : ℕ} (d : ℕ) (p : α → Fin k → ℝ) : Prop :=
  ∃ n : ℕ, ∃ q : Fin n → ℝ,
    ∃ t : Fin n → α → Fin d → ℝ, ∃ r : Fin n → Fin d → Fin k → ℝ,
      (∀ l, 0 ≤ q l) ∧ (∑ l, q l = 1) ∧
      (∀ l, IsRowStochastic (t l)) ∧ (∀ l, IsRowStochastic (r l)) ∧
      ∀ x y, p x y = ∑ l, q l * ∑ μ, r l μ y * t l x μ

private def feasible {α : Type} {k d : ℕ} (p : α → Fin k → ℝ) (x : α) :
    Set (↥((Finset.univ : Finset (Fin k)).powersetCard d) → ℝ) :=
  {q | (∀ s, 0 ≤ q s) ∧ (∑ s, q s = 1) ∧
    ∃ a : ↥((Finset.univ : Finset (Fin k)).powersetCard d) → Fin k → ℝ,
      (∀ s y, 0 ≤ a s y) ∧ (∀ s y, y ∉ s.val → a s y = 0) ∧
      (∀ s, ∑ y, a s y = q s) ∧ (∀ y, ∑ s, a s y = p x y)}

private lemma channel_decomposition {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (p : α → β → ℝ) (hp : IsRowStochastic p) :
    (∀ f : α → β, 0 ≤ ∏ x, p x (f x)) ∧
    (∑ f : α → β, ∏ x, p x (f x)) = 1 ∧
    ∀ x y, (∑ f : α → β, (∏ z, p z (f z)) * if f x = y then 1 else 0) = p x y := by
  classical
  obtain ⟨hn, hs⟩ := hp
  refine ⟨fun f => Finset.prod_nonneg (fun x _ => hn x (f x)), ?_, ?_⟩
  · rw [← Fintype.prod_sum]
    simp only [hs, Finset.prod_const_one]
  · intro x y
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] using
      (product_row_marginal p hs x (fun b => if b = y then 1 else 0))

private lemma mixture_common {α ι : Type} [Fintype α] [Fintype ι] {k d : ℕ}
    (hk : d < k) (p : α → Fin k → ℝ) (w : ι → ℝ) (v : ι → α → Fin k)
    (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1)
    (hv : ∀ j, (Finset.univ.image (v j)).card ≤ d)
    (hp : ∀ x y, p x y = ∑ j, w j * if v j x = y then 1 else 0) :
    ∃ q, ∀ x, q ∈ feasible (d := d) p x := by
  classical
  have he (j : ι) :
      ∃ s : ↥((Finset.univ : Finset (Fin k)).powersetCard d), ∀ x, v j x ∈ s.val := by
    obtain ⟨s, hrs, _, hsc⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (Finset.univ.image (v j))) (hv j)
      (by simpa only [Finset.card_univ, Fintype.card_fin] using Nat.le_of_lt hk)
    exact ⟨⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, hsc⟩⟩,
      fun x => hrs (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)⟩
  choose s hsupport using he
  let q : ↥((Finset.univ : Finset (Fin k)).powersetCard d) → ℝ :=
    fun t => ∑ j, if s j = t then w j else 0
  refine ⟨q, fun x => ⟨?_, ?_, ?_⟩⟩
  · intro t
    exact Finset.sum_nonneg (fun j _ => by
      split
      · exact hw j
      · exact le_rfl)
  · change (∑ t, ∑ j, if s j = t then w j else 0) = 1
    rw [Finset.sum_comm]
    simpa only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] using hs
  · refine ⟨fun t y => ∑ j, if s j = t ∧ v j x = y then w j else 0, ?_, ?_, ?_, ?_⟩
    · intro t y
      exact Finset.sum_nonneg (fun j _ => by
        split
        · exact hw j
        · exact le_rfl)
    · intro t y hy
      apply Finset.sum_eq_zero
      intro j _
      rw [ite_eq_right]
      rintro ⟨rfl, rfl⟩
      exact hy (hsupport j x)
    · intro t
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : s j = t <;> simp [hj]
    · intro y
      rw [hp, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : v j x = y <;> simp [hj]

private lemma simulable_common {α : Type} [Fintype α] {k d : ℕ}
    (hd : 1 ≤ d) (hk : d < k) (p : α → Fin k → ℝ) (h : IsSimulable d p) :
    ∃ q, ∀ x, q ∈ feasible (d := d) p x := by
  classical
  obtain ⟨n, q, t, r, hq, hqs, ht, hr, hp⟩ := h
  let w : (Fin n × (α → Fin d) × (Fin d → Fin k)) → ℝ :=
    fun j => q j.1 * (∏ x, t j.1 x (j.2.1 x)) * ∏ μ, r j.1 μ (j.2.2 μ)
  let v : (Fin n × (α → Fin d) × (Fin d → Fin k)) → α → Fin k :=
    fun j x => j.2.2 (j.2.1 x)
  apply mixture_common hk p w v
  · intro j
    exact mul_nonneg (mul_nonneg (hq j.1)
      ((channel_decomposition (t j.1) (ht j.1)).1 j.2.1))
      ((channel_decomposition (r j.1) (hr j.1)).1 j.2.2)
  · change (∑ j : Fin n × (α → Fin d) × (Fin d → Fin k),
      q j.1 * (∏ x, t j.1 x (j.2.1 x)) *
        ∏ μ, r j.1 μ (j.2.2 μ)) = 1
    simp only [Fintype.sum_prod_type]
    calc
      _ = ∑ l, ∑ f : α → Fin d, q l * (∏ z, t l z (f z)) * 1 := by
        apply Finset.sum_congr rfl
        intro l _
        apply Finset.sum_congr rfl
        intro f _
        rw [← Finset.mul_sum, (channel_decomposition (r l) (hr l)).2.1]
      _ = ∑ l, q l := by
        apply Finset.sum_congr rfl
        intro l _
        simp only [mul_one]
        rw [← Finset.mul_sum, (channel_decomposition (t l) (ht l)).2.1, mul_one]
      _ = 1 := hqs
  · intro j
    change (Finset.univ.image (fun x => j.2.2 (j.2.1 x))).card ≤ d
    calc
      _ ≤ (Finset.univ.image j.2.2).card := Finset.card_le_card (by
        intro y hy
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_image.mpr ⟨j.2.1 x, Finset.mem_univ _, rfl⟩)
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = d := by simp only [Finset.card_univ, Fintype.card_fin]
  · intro x y
    rw [hp]
    change (∑ l, q l * ∑ μ, r l μ y * t l x μ) =
      ∑ j : Fin n × (α → Fin d) × (Fin d → Fin k),
        (q j.1 * (∏ z, t j.1 z (j.2.1 z)) *
        ∏ μ, r j.1 μ (j.2.2 μ)) * if j.2.2 (j.2.1 x) = y then 1 else 0
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro l _
    symm
    calc
      _ = ∑ f : α → Fin d, q l * (∏ z, t l z (f z)) * r l (f x) y := by
        apply Finset.sum_congr rfl
        intro f _
        calc
          _ = (q l * ∏ z, t l z (f z)) *
              ∑ g : Fin d → Fin k, (∏ μ, r l μ (g μ)) *
                (if g (f x) = y then 1 else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro g _
            ring
          _ = _ := by rw [(channel_decomposition (r l) (hr l)).2.2 (f x) y]
      _ = q l * ∑ μ, t l x μ * r l μ y := by
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum, product_row_marginal (t l) (ht l).2 x (fun μ => r l μ y)]
      _ = _ := by congr 1; apply Finset.sum_congr rfl; intro μ _; ring

private lemma finite_simulation {α ι : Type} [Fintype ι] {k d : ℕ}
    (p : α → Fin k → ℝ) (q : ι → ℝ)
    (t : ι → α → Fin d → ℝ) (r : ι → Fin d → Fin k → ℝ)
    (hq : ∀ l, 0 ≤ q l) (hs : ∑ l, q l = 1)
    (ht : ∀ l, IsRowStochastic (t l)) (hr : ∀ l, IsRowStochastic (r l))
    (hp : ∀ x y, p x y = ∑ l, q l * ∑ μ, r l μ y * t l x μ) :
    IsSimulable d p := by
  classical
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, q ∘ e, fun l => t (e l), fun l => r (e l),
    fun l => hq (e l), ?_, fun l => ht (e l), fun l => hr (e l), ?_⟩
  · exact (e.sum_comp q).trans hs
  · intro x y
    exact (hp x y).trans (e.sum_comp (fun l => q l * ∑ μ, r l μ y * t l x μ)).symm

private lemma common_simulable {α : Type} [Fintype α] [Nonempty α] {k d : ℕ}
    (hd : 1 ≤ d) (hk : d < k) (p : α → Fin k → ℝ)
    (h : ∃ q, ∀ x, q ∈ feasible (d := d) p x) : IsSimulable d p := by
  classical
  obtain ⟨q, hq⟩ := h
  have hqn := (hq (Classical.choice (inferInstance : Nonempty α))).1
  have hqs := (hq (Classical.choice (inferInstance : Nonempty α))).2.1
  choose a han haz has hay using fun x => (hq x).2.2
  let e (s : ↥((Finset.univ : Finset (Fin k)).powersetCard d)) : Fin d ≃ s.val :=
    (Finset.equivFinOfCardEq (Finset.mem_powersetCard.mp s.property).2).symm
  let z : Fin d := ⟨0, by omega⟩
  let c : ↥((Finset.univ : Finset (Fin k)).powersetCard d) → α → Fin d → ℝ :=
    fun s x μ => if q s = 0 then (if μ = z then 1 else 0) else a x s (e s μ) / q s
  have ha0 (x : α) (s : ↥((Finset.univ : Finset (Fin k)).powersetCard d))
      (hz : q s = 0) (y : Fin k) :
      a x s y = 0 := by
    have hle := Finset.single_le_sum (fun y _ => han x s y) (Finset.mem_univ y)
    rw [has, hz] at hle
    exact le_antisymm hle (han x s y)
  have heSum (x : α) (s : ↥((Finset.univ : Finset (Fin k)).powersetCard d)) :
      (∑ μ, a x s (e s μ)) = q s := by
    calc
      _ = ∑ y : s.val, a x s y := (e s).sum_comp _
      _ = ∑ y ∈ s.val, a x s y := Finset.sum_coe_sort _ _
      _ = ∑ y, a x s y := Finset.sum_subset (Finset.subset_univ _) (by
        intro y _ hy
        exact haz x s y hy)
      _ = q s := has x s
  have hc (s : ↥((Finset.univ : Finset (Fin k)).powersetCard d)) : IsRowStochastic (c s) := by
    constructor
    · intro x μ
      change 0 ≤ if q s = 0 then (if μ = z then 1 else 0) else _
      split
      · split <;> norm_num
      · exact div_nonneg (han x s _) (hqn s)
    · intro x
      change (∑ μ, if q s = 0 then (if μ = z then 1 else 0) else _) = 1
      by_cases hz : q s = 0
      · simp only [ite_eq_left hz]; simp
      · simp only [ite_eq_right hz]
        rw [← Finset.sum_div, heSum, div_self hz]
  let r : ↥((Finset.univ : Finset (Fin k)).powersetCard d) → Fin d → Fin k → ℝ :=
    fun s => deterministicPostprocess (fun μ => (e s μ).val)
  have hr (s : ↥((Finset.univ : Finset (Fin k)).powersetCard d)) : IsRowStochastic (r s) := by
    constructor
    · intro μ y
      simpa only [r, deterministicPostprocess, Convexity.StdSimplex.weights_single,
        Finsupp.single_apply, Finsupp.zero_apply, eq_comm] using
        (Convexity.StdSimplex.single (R := ℝ) ((e s μ).val)).nonneg y
    · intro μ
      simpa only [r, deterministicPostprocess, Convexity.StdSimplex.weights_single,
        Finsupp.single_apply, eq_comm] using
        (Convexity.StdSimplex.single (R := ℝ) ((e s μ).val)).total_of_fintype
  have hrec (s : ↥((Finset.univ : Finset (Fin k)).powersetCard d)) (x : α) (y : Fin k) :
      q s * ∑ μ, r s μ y * c s x μ = a x s y := by
    by_cases hz : q s = 0
    · rw [hz, zero_mul, ha0 x s hz y]
    · have heach (μ : Fin d) : q s * (r s μ y * c s x μ) =
          if (e s μ).val = y then a x s (e s μ) else 0 := by
        dsimp only [r, deterministicPostprocess, c]
        rw [ite_eq_right hz]
        by_cases he : (e s μ).val = y
        · simp only [ite_eq_left he, one_mul]
          rw [div_eq_mul_inv]
          calc
            q s * (a x s (e s μ) * (q s)⁻¹) =
                a x s (e s μ) * (q s * (q s)⁻¹) := by ring
            _ = a x s (e s μ) := by rw [mul_inv_cancel₀ hz, mul_one]
        · simp only [ite_eq_right he, zero_mul, mul_zero]
      rw [Finset.mul_sum]
      simp_rw [heach]
      rw [(e s).sum_comp (fun b : s.val => if b.val = y then a x s b else 0)]
      by_cases hy : y ∈ s.val
      · simpa only [ite_eq_left rfl, ite_true] using
          (Finset.sum_eq_single (⟨y, hy⟩ : s.val)
            (by intro b _ hb; rw [ite_eq_right]; intro hh; exact hb (Subtype.ext hh))
            (by simp) :
            (∑ b : s.val, if b.val = y then a x s b else 0) = _)
      · rw [haz x s y hy]
        apply Finset.sum_eq_zero
        intro b _
        rw [ite_eq_right]
        intro hb
        exact hy (hb ▸ b.property)
  let w : (↥((Finset.univ : Finset (Fin k)).powersetCard d) × (α → Fin d)) → ℝ :=
    fun j => q j.1 * ∏ x, c j.1 x (j.2 x)
  let t : (↥((Finset.univ : Finset (Fin k)).powersetCard d) × (α → Fin d)) →
      α → Fin d → ℝ :=
    fun j => deterministicPostprocess j.2
  apply finite_simulation p w t (fun j => r j.1)
  · intro j
    exact mul_nonneg (hqn j.1) ((channel_decomposition _ (hc j.1)).1 j.2)
  · change (∑ j : ↥((Finset.univ : Finset (Fin k)).powersetCard d) × (α → Fin d),
      q j.1 * ∏ x, c j.1 x (j.2 x)) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (channel_decomposition _ (hc _)).2.1, mul_one]
    exact hqs
  · intro j
    constructor
    · intro x μ
      simpa only [t, deterministicPostprocess, Convexity.StdSimplex.weights_single,
        Finsupp.single_apply, Finsupp.zero_apply, eq_comm] using
        (Convexity.StdSimplex.single (R := ℝ) (j.2 x)).nonneg μ
    · intro x
      simpa only [t, deterministicPostprocess, Convexity.StdSimplex.weights_single,
        Finsupp.single_apply, eq_comm] using
        (Convexity.StdSimplex.single (R := ℝ) (j.2 x)).total_of_fintype
  · exact fun j => hr j.1
  · intro x y
    dsimp only [w, t, deterministicPostprocess]
    rw [Fintype.sum_prod_type, ← hay x y]
    apply Finset.sum_congr rfl
    intro s _
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, product_row_marginal (c s) (hc s).2 x (fun μ => r s μ y)]
    simpa only [mul_comm] using (hrec s x y).symm

private lemma empty_inputs_simulable {α : Type} [IsEmpty α] {k d : ℕ}
    (hd : 1 ≤ d) (hk : d < k) (p : α → Fin k → ℝ) : IsSimulable d p := by
  classical
  let y : Fin k := ⟨0, by omega⟩
  refine ⟨1, fun _ => 1, fun _ x => isEmptyElim x,
    fun _ => deterministicPostprocess (fun _ => y), ?_, ?_, ?_, ?_, ?_⟩
  · intro l; norm_num
  · simp
  · intro l
    exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩
  · intro l
    constructor
    · intro μ b
      simpa only [deterministicPostprocess, Convexity.StdSimplex.weights_single,
        Finsupp.single_apply, Finsupp.zero_apply, eq_comm] using
        (Convexity.StdSimplex.single (R := ℝ) y).nonneg b
    · intro μ
      simpa only [deterministicPostprocess, Convexity.StdSimplex.weights_single,
        Finsupp.single_apply, eq_comm] using
        (Convexity.StdSimplex.single (R := ℝ) y).total_of_fintype
  · intro x
    exact isEmptyElim x

private lemma feasible_convex {α : Type} {k d : ℕ} (p : α → Fin k → ℝ) (x : α) :
    Convex ℝ (feasible (d := d) p x) := by
  classical
  intro q hq v hv b c hb hc hbc
  obtain ⟨hqn, hqs, a, han, haz, has, hay⟩ := hq
  obtain ⟨hvn, hvs, u, hun, huz, hus, huy⟩ := hv
  refine ⟨?_, ?_, fun s y => b * a s y + c * u s y, ?_, ?_, ?_, ?_⟩
  · intro s
    exact add_nonneg (mul_nonneg hb (hqn s)) (mul_nonneg hc (hvn s))
  · change (∑ s, (b * q s + c * v s)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hqs, hvs]
    simpa only [mul_one] using hbc
  · intro s y
    exact add_nonneg (mul_nonneg hb (han s y)) (mul_nonneg hc (hun s y))
  · intro s y hy
    change b * a s y + c * u s y = 0
    rw [haz s y hy, huz s y hy, mul_zero, mul_zero, add_zero]
  · intro s
    change (∑ y, (b * a s y + c * u s y)) = b * q s + c * v s
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, has, hus]
  · intro y
    change (∑ s, (b * a s y + c * u s y)) = p x y
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hay, huy]
    rw [← add_mul, hbc, one_mul]

private lemma helly_normalized {α β : Type} [Fintype α] [Fintype β] [Nonempty β]
    (f : α → Set (β → ℝ)) (hc : ∀ x, Convex ℝ (f x))
    (hn : ∀ x q, q ∈ f x → ∑ s, q s = 1)
    (he : ¬ ∃ q, ∀ x, q ∈ f x) :
    ∃ i : Finset α, i.Nonempty ∧ i.card ≤ Fintype.card β ∧
      ¬ ∃ q, ∀ x ∈ i, q ∈ f x := by
  classical
  rcases isEmpty_or_nonempty α with hempty | hnonempty
  · exact False.elim (he ⟨0, fun x => isEmptyElim x⟩)
  let s : β := Classical.choice (inferInstance : Nonempty β)
  let v := {b : β // b ≠ s}
  let l := LinearMap.funLeft ℝ ℝ (fun b : v => b.val)
  have hinj (q r : β → ℝ) (hq : ∑ b, q b = 1) (hr : ∑ b, r b = 1)
      (heq : l q = l r) : q = r := by
    have hoff (b : v) : q b.val = r b.val := congrFun heq b
    have hsum : (∑ b : v, q b.val) = ∑ b : v, r b.val :=
      Finset.sum_congr rfl (fun b _ => hoff b)
    rw [Fintype.sum_eq_add_sum_subtype_ne q s] at hq
    rw [Fintype.sum_eq_add_sum_subtype_ne r s] at hr
    funext b
    by_cases hb : b = s
    · subst b; linarith only [hq, hr, hsum]
    · exact hoff ⟨b, hb⟩
  have hdim : Module.finrank ℝ (v → ℝ) + 1 = Fintype.card β := by
    rw [Module.finrank_pi]
    exact (Fintype.card_option (α := v)).symm.trans (Fintype.card_congr (Equiv.optionSubtypeNe s))
  by_contra hsmall
  have hall (i : Finset α) (hcard : i.card ≤ Fintype.card β) :
      ∃ q, ∀ x ∈ i, q ∈ f x := by
    by_cases hi : i.Nonempty
    · by_contra hnone
      exact hsmall ⟨i, hi, hcard, hnone⟩
    · have hi0 : i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hi
      exact ⟨0, by subst i; simp⟩
  have hz : (⋂ x ∈ (Finset.univ : Finset α), l '' f x).Nonempty := by
    apply Convex.helly_theorem' (𝕜 := ℝ) (fun x _ => (hc x).linear_image l)
    intro i _ hcard
    obtain ⟨q, hq⟩ := hall i (by simpa only [hdim] using hcard)
    exact ⟨l q, Set.mem_iInter.mpr (fun x => Set.mem_iInter.mpr
      (fun hx => ⟨q, hq x hx, rfl⟩))⟩
  obtain ⟨z, hz⟩ := hz
  have hx (x : α) : ∃ q, q ∈ f x ∧ l q = z :=
    Set.mem_iInter.mp (Set.mem_iInter.mp hz x) (Finset.mem_univ x)
  choose q hq heq using hx
  let x0 : α := Classical.choice hnonempty
  apply he
  refine ⟨q x0, fun x => ?_⟩
  have hsame : q x0 = q x := hinj _ _ (hn x0 _ (hq x0)) (hn x _ (hq x))
    ((heq x0).trans (heq x).symm)
  rw [hsame]
  exact hq x


/-- The Doolittle–Chitambar certificate-size conjecture for finite classical channels. -/
theorem result (m k d : ℕ) (hd : 1 ≤ d) (hk : d < k)
    (p : Fin m → Fin k → ℝ) (hp : IsRowStochastic p) (h : ¬ IsSimulable d p) :
    ∃ i : Finset (Fin m), i.Nonempty ∧ i.card ≤ k.choose d ∧
      ¬ IsSimulable d ((i : Set _).domRestrict p) := by
  classical
  have hm : 0 < m := by
    by_contra hz
    have : m = 0 := by omega
    subst m
    exact h (empty_inputs_simulable hd hk p)
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hs : 0 < Fintype.card (↥((Finset.univ : Finset (Fin k)).powersetCard d)) := by
    rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact Nat.choose_pos (Nat.le_of_lt hk)
  haveI : Nonempty (↥((Finset.univ : Finset (Fin k)).powersetCard d)) :=
    Fintype.card_pos_iff.mp hs
  have he : ¬ ∃ q, ∀ x, q ∈ feasible (d := d) p x :=
    fun hq => h (common_simulable hd hk p hq)
  obtain ⟨i, hi, hcard, hempty⟩ := helly_normalized (feasible (d := d) p)
    (feasible_convex p) (fun _ _ hq => hq.2.1) he
  refine ⟨i, hi, by simpa only [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin] using hcard, ?_⟩
  intro hiSim
  obtain ⟨q, hq⟩ := simulable_common hd hk ((i : Set _).domRestrict p) hiSim
  apply hempty
  exact ⟨q, fun x hx => hq ⟨x, hx⟩⟩

end D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate
