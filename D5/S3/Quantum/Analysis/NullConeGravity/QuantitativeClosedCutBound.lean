/- GID: D5/S3/Quantum/Analysis/NullConeGravity/QuantitativeClosedCutBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/QuantitativeClosedCutBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative finite-anchor dimension bound repairing Eq. 5.38, optimal cycle variance bound, and one-sided joint-cut tail modulus. -/

import D5.S3.Quantum.Analysis.NullConeGravity.ClosedTraceFinitenessBoundary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace D5.S3.Quantum.Analysis.NullConeGravity.QuantitativeClosedCutBound

section OptimalVariance

variable {ι : Type*} [DecidableEq ι]

private theorem optimal_variance_le (s I : Finset ι) (hIs : I ⊆ s)
    (hs : s.Nonempty) (w val : ι → ℝ) (c s₀ d D : ℝ) (r : ℕ)
    (hc : 0 < c) (hd : 0 ≤ d) (hdD : d ≤ D) (hr : 1 ≤ r)
    (hw_lo : ∀ i ∈ s, c ≤ w i) (hw_hi : ∀ i ∈ s, w i ≤ 1)
    (hI_dev : ∀ i ∈ I, |val i - s₀| ≤ d)
    (hout_dev : ∀ i ∈ s \ I, |val i - s₀| ≤ D)
    (hfrac : ((s \ I).card : ℝ) * (r : ℝ) ≤ (s.card : ℝ)) :
    (∑ i ∈ s, w i * (val i - s₀) ^ 2) / (∑ i ∈ s, w i) ≤
      d ^ 2 + (D ^ 2 - d ^ 2) / (1 + c * ((r : ℝ) - 1)) := by
  have hsum_lo : (s.card : ℝ) * c ≤ ∑ i ∈ s, w i := by
    calc
      (s.card : ℝ) * c = ∑ _i ∈ s, c := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, w i := Finset.sum_le_sum hw_lo
  have hspos : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  have hWpos : 0 < ∑ i ∈ s, w i := lt_of_lt_of_le (mul_pos hspos hc) hsum_lo
  let W : ℝ := ∑ i ∈ s, w i
  let Wo : ℝ := ∑ i ∈ s \ I, w i
  have hW_eq : W = (∑ i ∈ I, w i) + Wo := by
    dsimp [W, Wo]
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hIs]
  have hcard_eq : (s.card : ℝ) = (I.card : ℝ) + ((s \ I).card : ℝ) := by
    have hnat : s.card = I.card + (s \ I).card := by
      rw [Finset.card_sdiff_of_subset hIs]
      have hIcard : I.card ≤ s.card := Finset.card_le_card hIs
      omega
    exact_mod_cast hnat
  have hcard_out : ((s \ I).card : ℝ) * ((r : ℝ) - 1) ≤ (I.card : ℝ) := by
    nlinarith [hfrac, hcard_eq]
  have hWin : (I.card : ℝ) * c ≤ ∑ i ∈ I, w i := by
    calc
      (I.card : ℝ) * c = ∑ _i ∈ I, c := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ I, w i := Finset.sum_le_sum fun i hi => hw_lo i (hIs hi)
  have hWo_card : Wo ≤ ((s \ I).card : ℝ) := by
    dsimp [Wo]
    calc
      ∑ i ∈ s \ I, w i ≤ ∑ _i ∈ s \ I, (1 : ℝ) :=
        Finset.sum_le_sum fun i hi => hw_hi i ((Finset.mem_sdiff.mp hi).1)
      _ = ((s \ I).card : ℝ) := by simp [nsmul_eq_mul]
  have hWo_nonneg : 0 ≤ Wo := by
    dsimp [Wo]
    exact Finset.sum_nonneg fun i hi => by
      nlinarith [hc, hw_lo i ((Finset.mem_sdiff.mp hi).1)]
  have hrsub : 0 ≤ (r : ℝ) - 1 := by
    have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hLpos : 0 < 1 + c * ((r : ℝ) - 1) := by
    nlinarith
  have hWoL : Wo * (1 + c * ((r : ℝ) - 1)) ≤ W := by
    calc
      Wo * (1 + c * ((r : ℝ) - 1)) = Wo + c * ((r : ℝ) - 1) * Wo := by ring
      _ ≤ Wo + c * ((r : ℝ) - 1) * ((s \ I).card : ℝ) := by
        have hcoef : 0 ≤ c * ((r : ℝ) - 1) := mul_nonneg hc.le hrsub
        have hmul := mul_le_mul_of_nonneg_left hWo_card hcoef
        nlinarith [hmul]
      _ ≤ Wo + c * (I.card : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hcard_out hc.le
        nlinarith [hmul]
      _ ≤ W := by rw [hW_eq]; nlinarith [hWin]
  have hI_bound : (∑ i ∈ I, w i * (val i - s₀) ^ 2) ≤
      (∑ i ∈ I, w i) * d ^ 2 := by
    calc
      ∑ i ∈ I, w i * (val i - s₀) ^ 2 ≤ ∑ i ∈ I, w i * d ^ 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hsq : (val i - s₀) ^ 2 ≤ d ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hI_dev i hi) 2
        exact mul_le_mul_of_nonneg_left hsq (le_trans hc.le (hw_lo i (hIs hi)))
      _ = (∑ i ∈ I, w i) * d ^ 2 := by rw [Finset.sum_mul]
  have hout_bound : (∑ i ∈ s \ I, w i * (val i - s₀) ^ 2) ≤ Wo * D ^ 2 := by
    calc
      ∑ i ∈ s \ I, w i * (val i - s₀) ^ 2 ≤ ∑ i ∈ s \ I, w i * D ^ 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hsq : (val i - s₀) ^ 2 ≤ D ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hout_dev i hi) 2
        exact mul_le_mul_of_nonneg_left hsq
          (le_trans hc.le (hw_lo i ((Finset.mem_sdiff.mp hi).1)))
      _ = Wo * D ^ 2 := by rw [Finset.sum_mul]
  have hsplit : (∑ i ∈ s, w i * (val i - s₀) ^ 2) =
      (∑ i ∈ I, w i * (val i - s₀) ^ 2) +
        (∑ i ∈ s \ I, w i * (val i - s₀) ^ 2) := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hIs]
  have hnum : (∑ i ∈ s, w i * (val i - s₀) ^ 2) ≤
      W * d ^ 2 + Wo * (D ^ 2 - d ^ 2) := by
    rw [hsplit]
    calc
      (∑ i ∈ I, w i * (val i - s₀) ^ 2) +
          (∑ i ∈ s \ I, w i * (val i - s₀) ^ 2)
          ≤ (∑ i ∈ I, w i) * d ^ 2 + Wo * D ^ 2 := add_le_add hI_bound hout_bound
      _ = W * d ^ 2 + Wo * (D ^ 2 - d ^ 2) := by rw [hW_eq]; ring
  have hratio : Wo / W ≤ 1 / (1 + c * ((r : ℝ) - 1)) := by
    apply (div_le_iff₀ hWpos).2
    have hdiv := (le_div_iff₀ hLpos).2 hWoL
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hgap : 0 ≤ D ^ 2 - d ^ 2 := by nlinarith [hd, hdD]
  calc
    (∑ i ∈ s, w i * (val i - s₀) ^ 2) / (∑ i ∈ s, w i) =
        (∑ i ∈ s, w i * (val i - s₀) ^ 2) / W := by rfl
    _ ≤ (W * d ^ 2 + Wo * (D ^ 2 - d ^ 2)) / W :=
      div_le_div_of_nonneg_right hnum hWpos.le
    _ = d ^ 2 + (D ^ 2 - d ^ 2) * (Wo / W) := by
      rw [add_div]
      have hcancel : W * d ^ 2 / W = d ^ 2 := by
        apply (div_eq_iff hWpos.ne').2
        ring
      rw [hcancel]
      ring
    _ ≤ d ^ 2 + (D ^ 2 - d ^ 2) * (1 / (1 + c * ((r : ℝ) - 1))) := by
      gcongr
    _ = d ^ 2 + (D ^ 2 - d ^ 2) / (1 + c * ((r : ℝ) - 1)) := by ring

/-- The sharp bound and its one-outlier equality model. -/
theorem optimal_cycle_union_area_variance_bound (s I : Finset ι) (hIs : I ⊆ s)
    (hs : s.Nonempty) (w val : ι → ℝ) (c s₀ d D : ℝ) (r : ℕ)
    (hc : 0 < c) (hd : 0 ≤ d) (hdD : d ≤ D) (hr : 1 ≤ r)
    (hw_lo : ∀ i ∈ s, c ≤ w i) (hw_hi : ∀ i ∈ s, w i ≤ 1)
    (hI_dev : ∀ i ∈ I, |val i - s₀| ≤ d)
    (hout_dev : ∀ i ∈ s \ I, |val i - s₀| ≤ D)
    (hfrac : ((s \ I).card : ℝ) * (r : ℝ) ≤ (s.card : ℝ)) :
    ((∑ i ∈ s, w i * (val i - s₀) ^ 2) / (∑ i ∈ s, w i) ≤
      d ^ 2 + (D ^ 2 - d ^ 2) / (1 + c * ((r : ℝ) - 1))) ∧
    ((∑ i ∈ Finset.range r, (if i = 0 then 1 else c) * (if i = 0 then D else d) ^ 2) /
      (∑ i ∈ Finset.range r, if i = 0 then 1 else c) =
      d ^ 2 + (D ^ 2 - d ^ 2) / (1 + c * ((r : ℝ) - 1))) := by
  refine ⟨optimal_variance_le s I hIs hs w val c s₀ d D r hc hd hdD hr hw_lo hw_hi
    hI_dev hout_dev hfrac, ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.succ_ne_zero, ite_false, ite_true, one_mul, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, Nat.cast_succ]
  have hden : 0 < 1 + c * (n : ℝ) := by positivity
  have hcast : (n : ℝ) + 1 - 1 = n := by ring
  rw [hcast]
  field_simp [hden.ne']
  ring

end OptimalVariance

section FiniteAnchor

variable {ι : Type*} [DecidableEq ι]

variable {m : ℕ}

/-- Eventual positivity bounds every band by padding the anchor with in-band indices. -/
theorem finite_and_card_fiber_le_of_eventually_positive
    (band : ι → Fin m) (w : ι → ℝ) (cutoffAmplitude : Finset ι → ℝ)
    (K δ c d D : ℝ) (r : ℕ) (F₀ : Finset ι)
    (hc : 0 < c) (hδ : 0 < δ) (hK : 0 ≤ K) (hd : 0 ≤ d) (hD : 0 ≤ D)
    (hr : 2 ≤ r) (hw : ∀ i, w i ∈ Set.Icc c 1)
    (hsmall : K ^ 2 * (d ^ 2 + D ^ 2 / ((r : ℝ) * c)) ≤ δ ^ 2 / 4)
    (hboost : ∀ (F : Finset ι) (j : Fin m), F.Nonempty →
      (F.filter (fun i => band i ≠ j)).card * r ≤ F.card →
      cutoffAmplitude F ≤
        (∑ i ∈ F, w i) *
          (K * Real.sqrt
            ((∑ i ∈ F, w i * (if band i = j then d else D) ^ 2) /
              (∑ i ∈ F, w i)) - δ / 2))
    (hpositive : ∀ F, F₀ ⊆ F → F.Nonempty → 0 < cutoffAmplitude F) :
    Finite ι ∧ ∀ j : Fin m,
      let qj := (F₀.filter (fun i => band i = j)).card
      Nat.card {i // band i = j} ≤ max 1 (qj + (r - 1) * (F₀.card - qj)) - 1 := by
  classical
  have hbad : ∀ (F : Finset ι) (j : Fin m), F₀ ⊆ F → F.Nonempty →
      (F.filter (fun i => band i ≠ j)).card * r ≤ F.card → False := by
    intro F j hsub hne hfrac
    let I := F.filter (fun i => band i = j)
    let val : ι → ℝ := fun i => if band i = j then d else D
    have hdiff : F \ I = F.filter (fun i => band i ≠ j) := by
      ext i
      simp [I]
      tauto
    have hvar := ClosedTraceFinitenessBoundary.cycle_union_area_variance_bound
      F I (Finset.filter_subset _ _) hne w val c 0 d D r hc hd hD (by omega)
      (fun i _ => (hw i).1) (fun i _ => (hw i).2)
      (by intro i hi; have hb := (Finset.mem_filter.mp hi).2; simp [val, hb, abs_of_nonneg hd])
      (by intro i hi; rw [hdiff] at hi; have hb := (Finset.mem_filter.mp hi).2;
          simp [val, hb, abs_of_nonneg hD])
      (by rw [hdiff]; exact_mod_cast hfrac)
    simp only [sub_zero] at hvar
    have hW : 0 < ∑ i ∈ F, w i := Finset.sum_pos (fun i _ => hc.trans_le (hw i).1) hne
    have hv : 0 ≤ (∑ i ∈ F, w i * (val i)^2) / (∑ i ∈ F, w i) :=
      div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hc.le.trans (hw i).1) (sq_nonneg _)) hW.le
    have hsqrt := Real.sq_sqrt hv
    have hsq := mul_le_mul_of_nonneg_left hvar (sq_nonneg K)
    have hlim : K * Real.sqrt ((∑ i ∈ F, w i * (val i)^2) / (∑ i ∈ F, w i)) ≤ δ / 2 := by
      have hnn := mul_nonneg hK (Real.sqrt_nonneg ((∑ i ∈ F, w i * (val i)^2) / (∑ i ∈ F, w i)))
      nlinarith [sq_nonneg (K * Real.sqrt ((∑ i ∈ F, w i * (val i)^2) / (∑ i ∈ F, w i)) - δ / 2)]
    have hb := hboost F j hne hfrac
    change cutoffAmplitude F ≤ _ * (K * Real.sqrt ((∑ i ∈ F, w i * (val i)^2) / _) - δ / 2) at hb
    exact (not_lt_of_ge (hb.trans (mul_nonpos_of_nonneg_of_nonpos hW.le (sub_nonpos.mpr hlim))))
      (hpositive F hsub hne)
  have hcap : ∀ j : Fin m, ∀ G : Finset {i // band i = j},
      G.card < max 1 ((F₀.filter (fun i => band i = j)).card +
        (r - 1) * (F₀.card - (F₀.filter (fun i => band i = j)).card)) := by
    intro j G
    by_contra! hG
    let B := G.map (Function.Embedding.subtype (fun i => band i = j))
    let F := F₀ ∪ B
    let O := F₀.filter (fun i => band i ≠ j)
    have hB : ∀ i ∈ B, band i = j := by
      intro i hi
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hi
      exact x.property
    have hBc : B.card = G.card := Finset.card_map _
    have hO : O.card = F₀.card - (F₀.filter (fun i => band i = j)).card := by
      have h := Finset.card_filter_add_card_filter_not (s := F₀) (fun i => band i = j)
      dsimp [O]
      omega
    have hfilter : F.filter (fun i => band i ≠ j) = O := by
      ext i
      simp only [F, O, Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hi | hi, hn⟩
        · exact ⟨hi, hn⟩
        · exact (hn (hB i hi)).elim
      · exact fun ⟨hi, hn⟩ => ⟨Or.inl hi, hn⟩
    have hdis : Disjoint O B := Finset.disjoint_left.mpr fun i hi hiB =>
      (Finset.mem_filter.mp hi).2 (hB i hiB)
    have hsub : O ∪ B ⊆ F := Finset.union_subset
      (fun i hi => Finset.mem_union_left _ (Finset.mem_filter.mp hi).1) (Finset.subset_union_right)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, hBc] at hcard
    have hG1 : 1 ≤ G.card := (le_max_left _ _).trans hG
    have hG2 := (le_max_right 1 _).trans hG
    have hfrac : O.card * r ≤ F.card := by
      have hmul : O.card * r = O.card + (r - 1) * O.card := by
        have hre : r = (r - 1) + 1 := by omega
        conv_lhs => rw [hre, Nat.mul_add, Nat.mul_one]
        ac_rfl
      rw [hmul, hO]
      omega
    exact hbad F j Finset.subset_union_left (Finset.card_pos.mp (by omega)) (by rwa [hfilter])
  have hfib : ∀ j : Fin m, Finite {i // band i = j} := by
    intro j
    by_contra hn
    let : Infinite {i // band i = j} := not_finite_iff_infinite.mp hn
    obtain ⟨G, hG⟩ := Infinite.exists_subset_card_eq {i // band i = j}
      (max 1 ((F₀.filter (fun i => band i = j)).card +
        (r - 1) * (F₀.card - (F₀.filter (fun i => band i = j)).card)))
    exact (Nat.lt_irrefl _) (hG ▸ hcap j G)
  let : ∀ j : Fin m, Finite {i // band i = j} := hfib
  refine ⟨Finite.of_equiv _ (Equiv.sigmaFiberEquiv band), ?_⟩
  intro j
  let := Fintype.ofFinite {i // band i = j}
  have h := hcap j (Finset.univ : Finset {i // band i = j})
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h
  dsimp
  omega

end FiniteAnchor

section HilbertConsumer

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [DecidableEq ι]

/-- Sum the band capacities and identify the finite Hilbert basis cardinal with the dimension. -/
theorem finrank_le_of_eventually_positive_cycle_cuts {m : ℕ}
    (b : HilbertBasis ι ℂ H)
    (band : ι → Fin m) (w : ι → ℝ) (cutoffAmplitude : Finset ι → ℝ)
    (K δ c d D : ℝ) (r : ℕ) (F₀ : Finset ι)
    (hc : 0 < c) (hδ : 0 < δ) (hK : 0 ≤ K) (hd : 0 ≤ d) (hD : 0 ≤ D)
    (hr : 2 ≤ r) (hw : ∀ i, w i ∈ Set.Icc c 1)
    (hsmall : K ^ 2 * (d ^ 2 + D ^ 2 / ((r : ℝ) * c)) ≤ δ ^ 2 / 4)
    (hboost : ∀ (F : Finset ι) (j : Fin m), F.Nonempty →
      (F.filter (fun i => band i ≠ j)).card * r ≤ F.card →
      cutoffAmplitude F ≤
        (∑ i ∈ F, w i) *
          (K * Real.sqrt
            ((∑ i ∈ F, w i * (if band i = j then d else D) ^ 2) /
              (∑ i ∈ F, w i)) - δ / 2))
    (hpositive : ∀ F, F₀ ⊆ F → F.Nonempty → 0 < cutoffAmplitude F) :
    FiniteDimensional ℂ H ∧
      (F₀.card = 0 → Module.finrank ℂ H = 0) ∧
      (F₀.card > 0 → Module.finrank ℂ H ≤ F₀.card * (1 + (m - 1) * (r - 1)) - m) := by
  classical
  obtain ⟨hfinite, hcard⟩ := finite_and_card_fiber_le_of_eventually_positive
    band w cutoffAmplitude K δ c d D r F₀ hc hδ hK hd hD hr hw hsmall hboost hpositive
  let : Finite ι := hfinite
  let : Fintype ι := Fintype.ofFinite ι
  have hfd : FiniteDimensional ℂ H := b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  have hfinrank : Module.finrank ℂ H = Fintype.card ι :=
    Module.finrank_eq_card_basis b.toOrthonormalBasis.toBasis
  let qj : Fin m → ℕ := fun j => (F₀.filter (fun i => band i = j)).card
  let nj : Fin m → ℕ := fun j => Fintype.card {i // band i = j}
  have hsum : Fintype.card ι = ∑ j, nj j := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv band), Fintype.card_sigma]
  have hsumq : F₀.card = ∑ j, qj j :=
    Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (by simp)
  have hterm : ∀ j, nj j ≤ max 1 (qj j + (r - 1) * (F₀.card - qj j)) - 1 := by
    intro j
    simpa only [Nat.card_eq_fintype_card, qj, nj] using hcard j
  refine ⟨hfd, ?_, ?_⟩
  · intro hzero
    rw [hfinrank, hsum]
    have hq : F₀ = ∅ := Finset.card_eq_zero.mp hzero
    have hn : ∀ j, nj j = 0 := by
      intro j
      have h := hterm j
      simpa [qj, hq] using h
    simp [hn]
  · intro hpos
    have hm : 1 ≤ m := by
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      exact Nat.succ_le_of_lt (Nat.zero_lt_of_lt (band i).isLt)
    have hqle : ∀ j, qj j ≤ F₀.card := fun j => Finset.card_le_card (Finset.filter_subset _ _)
    have hcap : ∀ j, nj j + 1 ≤ qj j + (r - 1) * (F₀.card - qj j) := by
      intro j
      have ht := hterm j
      have hmul := Nat.mul_le_mul_right (F₀.card - qj j) (show 1 ≤ r - 1 by omega)
      have hpositiveCap : 1 ≤ qj j + (r - 1) * (F₀.card - qj j) := by
        simp only [one_mul] at hmul
        omega
      rw [max_eq_right hpositiveCap] at ht
      omega
    have hcompsum : (∑ j, (F₀.card - qj j)) = (m - 1) * F₀.card := by
      have h : (∑ j : Fin m, (F₀.card - qj j)) + (∑ j, qj j) = m * F₀.card := by
        rw [← Finset.sum_add_distrib]
        calc
          (∑ j : Fin m, (F₀.card - qj j + qj j)) = ∑ _j : Fin m, F₀.card := by
            exact Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (hqle j))
          _ = m * F₀.card := by simp
      rw [← hsumq] at h
      have hmul : m * F₀.card = (m - 1) * F₀.card + F₀.card := by
        calc
          m * F₀.card = ((m - 1) + 1) * F₀.card := by congr 1; omega
          _ = _ := by rw [Nat.add_mul, Nat.one_mul]
      omega
    have hsumcap := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun j _ => hcap j)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← hsumq, hcompsum] at hsumcap
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsumcap
    rw [← hsum] at hsumcap
    have heq : F₀.card * (1 + (m - 1) * (r - 1)) =
        F₀.card + (r - 1) * ((m - 1) * F₀.card) := by ring
    rw [hfinrank, heq]
    have hfinal : Fintype.card ι + m ≤ F₀.card + (r - 1) * ((m - 1) * F₀.card) := by
      simpa using hsumcap
    omega

end HilbertConsumer

section JointCutTail

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Complete one-sign cuts attain the signed tail sums and dominate any finite joint cut. -/
theorem disjoint_joint_cut_one_sided_tail_bound (w : ℕ → ℝ) (v : α → ℝ)
    (I : Finset α) (J : Finset ℕ) (hw : ∀ i, 0 ≤ w i) (hv : ∀ a, 0 ≤ v a)
    (hv_sum : ∑ a : α, v a = 1) (hp_pos : 0 < ∑ a ∈ I, v a)
    (hp_lt : ∑ a ∈ I, v a < 1):
    let p := ∑ a ∈ I, v a;
      (∀ K : Finset ℕ, (∀ i ∈ K, i ∉ J) →
      (∑ x ∈ K.product I, ClosedTraceFinitenessBoundary.jointCutTerm w v I x) =
        p * (1 - p) * ∑ i ∈ K, w i) ∧
    (∀ K : Finset ℕ, (∀ i ∈ K, i ∉ J) →
      (∑ x ∈ K.product (Finset.univ \ I), ClosedTraceFinitenessBoundary.jointCutTerm w v I x) =
        -p * (1 - p) * ∑ i ∈ K, w i) ∧
    (∀ S : Finset (ℕ × α), (∀ x ∈ S, x.1 ∉ J) →
      |∑ x ∈ S, ClosedTraceFinitenessBoundary.jointCutTerm w v I x| ≤
        p * (1 - p) * ∑ i ∈ S.image Prod.fst, w i) := by
  classical
  intro p
  have hp_nonneg : 0 ≤ p := hp_pos.le
  have hq_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp_lt.le
  have hI_sum : ∀ i : ℕ, ∑ a ∈ I, ClosedTraceFinitenessBoundary.jointCutTerm w v I (i, a) =
      p * (1 - p) * w i := by
    intro i
    have hterm : ∀ a ∈ I,
        ClosedTraceFinitenessBoundary.jointCutTerm w v I (i, a) =
          w i * v a * (1 - p) := by
      intro a ha
      change w i * v a * ((if a ∈ I then (1 : ℝ) else 0) - ∑ b ∈ I, v b) =
        w i * v a * (1 - p)
      rw [ite_eq_left ha]
    rw [Finset.sum_congr rfl hterm]
    calc
      (∑ a ∈ I, w i * v a * (1 - p)) =
          (∑ a ∈ I, w i * v a) * (1 - p) := by
            rw [← Finset.sum_mul]
      _ = w i * (∑ a ∈ I, v a) * (1 - p) := by
            rw [Finset.mul_sum]
      _ = p * (1 - p) * w i := by simp [p]; ring
  have hcomp_sum : ∀ i : ℕ, ∑ a ∈ Finset.univ \ I, v a = 1 - p := by
    intro i
    have hunion : I ∪ (Finset.univ \ I) = Finset.univ := by
      ext a
      by_cases ha : a ∈ I <;> simp [ha]
    have htot : (∑ a ∈ I, v a) + (∑ a ∈ Finset.univ \ I, v a) = 1 := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, hunion, hv_sum]
    linarith
  have hIc_sum : ∀ i : ℕ, ∑ a ∈ Finset.univ \ I,
      ClosedTraceFinitenessBoundary.jointCutTerm w v I (i, a) =
      -p * (1 - p) * w i := by
    intro i
    have hsum := hcomp_sum i
    have hI : ∀ a ∈ Finset.univ \ I, a ∉ I := fun a ha => (Finset.mem_sdiff.mp ha).2
    have hterm : ∀ a ∈ Finset.univ \ I,
        ClosedTraceFinitenessBoundary.jointCutTerm w v I (i, a) =
          w i * v a * (0 - p) := by
      intro a ha
      change w i * v a * ((if a ∈ I then (1 : ℝ) else 0) - ∑ b ∈ I, v b) =
        w i * v a * (0 - p)
      rw [ite_eq_right (hI a ha)]
    rw [Finset.sum_congr rfl hterm]
    calc
      (∑ a ∈ Finset.univ \ I, w i * v a * (0 - p)) =
          (∑ a ∈ Finset.univ \ I, w i * v a) * (0 - p) := by
            rw [← Finset.sum_mul]
      _ = w i * (∑ a ∈ Finset.univ \ I, v a) * (0 - p) := by
            rw [Finset.mul_sum]
      _ = -p * (1 - p) * w i := by rw [hsum]; ring
  have hpos : ∀ K : Finset ℕ,
      (∑ x ∈ K.product I, ClosedTraceFinitenessBoundary.jointCutTerm w v I x) =
        p * (1 - p) * ∑ i ∈ K, w i := by
    intro K
    calc
      (∑ x ∈ K.product I, ClosedTraceFinitenessBoundary.jointCutTerm w v I x) =
          ∑ i ∈ K, ∑ a ∈ I,
            ClosedTraceFinitenessBoundary.jointCutTerm w v I (i, a) :=
        Finset.sum_product K I _
      _ = ∑ i ∈ K, p * (1 - p) * w i := by simp_rw [hI_sum]
      _ = p * (1 - p) * ∑ i ∈ K, w i := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (Finset.mul_sum K (fun i => w i) (p * (1 - p))).symm
  have hneg : ∀ K : Finset ℕ,
      (∑ x ∈ K.product (Finset.univ \ I), ClosedTraceFinitenessBoundary.jointCutTerm w v I x) =
        -p * (1 - p) * ∑ i ∈ K, w i := by
    intro K
    calc
      (∑ x ∈ K.product (Finset.univ \ I), ClosedTraceFinitenessBoundary.jointCutTerm w v I x) =
          ∑ i ∈ K, ∑ a ∈ Finset.univ \ I,
            ClosedTraceFinitenessBoundary.jointCutTerm w v I (i, a) :=
        Finset.sum_product K (Finset.univ \ I) _
      _ = ∑ i ∈ K, -p * (1 - p) * w i := by simp_rw [hIc_sum]
      _ = -p * (1 - p) * ∑ i ∈ K, w i := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (Finset.mul_sum K (fun i => w i) (-p * (1 - p))).symm
  refine ⟨fun K _ => hpos K, fun K _ => hneg K, ?_⟩
  intro S hS
  let f := ClosedTraceFinitenessBoundary.jointCutTerm w v I
  let K := S.image Prod.fst
  let A := S.filter (fun x => x.2 ∈ I)
  let B := S.filter (fun x => x.2 ∉ I)
  have hA : A ⊆ K.product I := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Prod.fst hx'.1, hx'.2⟩
  have hB : B ⊆ K.product (Finset.univ \ I) := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Prod.fst hx'.1,
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx'.2⟩⟩
  have hfpos : ∀ x : ℕ × α, x.2 ∈ I → 0 ≤ f x := by
    intro x hx
    change 0 ≤ w x.1 * v x.2 * ((if x.2 ∈ I then (1 : ℝ) else 0) - p)
    rw [ite_eq_left hx]
    exact mul_nonneg (mul_nonneg (hw _) (hv _)) hq_nonneg
  have hfneg : ∀ x : ℕ × α, x.2 ∉ I → f x ≤ 0 := by
    intro x hx
    change w x.1 * v x.2 * ((if x.2 ∈ I then (1 : ℝ) else 0) - p) ≤ 0
    rw [ite_eq_right hx]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hw _) (hv _)) (by linarith)
  have hAsum : ∑ x ∈ A, f x ≤ p * (1 - p) * ∑ i ∈ K, w i := by
    rw [← hpos K]
    exact Finset.sum_le_sum_of_subset_of_nonneg hA fun x hx _ =>
      hfpos x (Finset.mem_product.mp hx).2
  have hBsum : -p * (1 - p) * ∑ i ∈ K, w i ≤ ∑ x ∈ B, f x := by
    rw [← hneg K]
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun x => -f x) hB
      (fun x hx _ => neg_nonneg.mpr (hfneg x (Finset.mem_sdiff.mp (Finset.mem_product.mp hx).2).2))
    simp only [Finset.sum_neg_distrib] at h
    linarith
  have hAn : 0 ≤ ∑ x ∈ A, f x := Finset.sum_nonneg fun x hx => hfpos x (Finset.mem_filter.mp hx).2
  have hBn : ∑ x ∈ B, f x ≤ 0 := Finset.sum_nonpos fun x hx => hfneg x (Finset.mem_filter.mp hx).2
  have hsplit : ∑ x ∈ S, f x = (∑ x ∈ A, f x) + ∑ x ∈ B, f x := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun x => x.2 ∈ I) f).symm
  change |∑ x ∈ S, f x| ≤ p * (1 - p) * ∑ i ∈ K, w i
  rw [abs_le, hsplit]
  constructor <;> linarith

end JointCutTail

#print axioms optimal_cycle_union_area_variance_bound
#print axioms finite_and_card_fiber_le_of_eventually_positive
#print axioms finrank_le_of_eventually_positive_cycle_cuts
#print axioms disjoint_joint_cut_one_sided_tail_bound

end D5.S3.Quantum.Analysis.NullConeGravity.QuantitativeClosedCutBound
