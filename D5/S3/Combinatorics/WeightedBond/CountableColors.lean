/- GID: D5/S3/Combinatorics/WeightedBond/CountableColors
   generality: I
   mirror-B: D5/B/S3/Combinatorics/WeightedBond/CountableColors
   mirror-E: none(waiver:kernel-checked-source-model)
   anchors: []
   utility: none
   digest: Finite support, padding and specialization of countable color weights. -/

import D5.S3.Combinatorics.WeightedBond.FiniteOrder

/-! Finite support, padding and specialization of countable color weights. -/

set_option autoImplicit false
open Finset
open D5.S0.Certificates.GonzalezDLeonWachsWeightedBondSource (children children_self parentBlock parentBlock_mem_children children_parent_fiber)

namespace D5.S3.Combinatorics.WeightedBond
noncomputable section
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The paper's countable color carrier. A cutoff certifies the finite weight sum of a block. -/
structure CountableBond (G : SimpleGraph V) where
  partition : Finpartition (univ : Finset V)
  weight : Finset V → ℕ → Fin (Fintype.card V + 1)
  weight_sum : ∀ B ∈ partition.parts, ∃ m : ℕ,
    (∀ i ≥ m, weight B i = 0) ∧
      (∑ i ∈ range m, (weight B i : ℕ)) = B.card - 1
  weight_off : ∀ B ∉ partition.parts, ∀ i, weight B i = 0
  connected : ∀ B ∈ partition.parts, (G.induce (B : Set V)).Connected

namespace CountableBond

def childSum (P : CountableBond G) (B : Finset V) (i : ℕ) : ℕ :=
  ∑ A ∈ children P.partition B, (P.weight A.val i : ℕ)

private theorem ext_weights {P Q : CountableBond G} (hp : P.partition = Q.partition)
    (hw : ∀ B ∈ P.partition.parts, ∀ i, P.weight B i = Q.weight B i) : P = Q := by
  have he : P.weight = Q.weight := by
    funext B i
    by_cases hB : B ∈ P.partition.parts
    · exact hw B hB i
    · rw [P.weight_off B hB, Q.weight_off B (hp ▸ hB)]
  cases P
  cases Q
  cases hp
  cases he
  rfl

def Refines (P Q : CountableBond G) : Prop :=
  P.partition ≤ Q.partition ∧
    ∀ B : Q.partition.parts, ∀ c, childSum P B.val c ≤ (Q.weight B.val c : ℕ)

instance : LE (CountableBond G) := ⟨Refines⟩

private theorem childSum_self (P : CountableBond G) (B : P.partition.parts)
    (c : ℕ) : childSum P B.val c = (P.weight B.val c : ℕ) := by
  rw [childSum, children_self, sum_singleton]

private theorem childSum_decompose (P Q R : CountableBond G)
    (hPQ : P.partition ≤ Q.partition) (hQR : Q.partition ≤ R.partition)
    (B : R.partition.parts) (c : ℕ) :
    childSum P B.val c =
      ∑ A ∈ children Q.partition B.val, childSum P A.val c := by
  classical
  symm
  calc
    _ = ∑ A ∈ children Q.partition B.val,
          ∑ D ∈ (children P.partition B.val).filter (fun D => parentBlock hPQ D = A),
            (P.weight D.val c : ℕ) := by
      apply sum_congr rfl
      intro A hA
      rw [children_parent_fiber hPQ B hA]
      rfl
    _ = _ := sum_fiberwise_of_maps_to
      (fun _ hD => parentBlock_mem_children hPQ hQR B hD) _

instance : PartialOrder (CountableBond G) where
  le_refl P := ⟨le_rfl, fun B c => (childSum_self P B c).le⟩
  le_trans P Q R hPQ hQR := by
    change Refines P Q at hPQ
    change Refines Q R at hQR
    refine ⟨hPQ.1.trans hQR.1, fun B c => ?_⟩
    rw [childSum_decompose P Q R hPQ.1 hQR.1 B c]
    exact (sum_le_sum fun A _ => hPQ.2 A c).trans (hQR.2 B c)
  le_antisymm P Q hPQ hQP := by
    change Refines P Q at hPQ
    change Refines Q P at hQP
    have hp := le_antisymm hPQ.1 hQP.1
    apply ext_weights hp
    intro B hB c
    have hBQ : B ∈ Q.partition.parts := hp ▸ hB
    have hp1 := hPQ.2 ⟨B, hBQ⟩ c
    have hp2 := hQP.2 ⟨B, hB⟩ c
    change childSum P B c ≤ _ at hp1
    change childSum Q B c ≤ _ at hp2
    rw [childSum_self P ⟨B, hB⟩ c] at hp1
    rw [childSum_self Q ⟨B, hBQ⟩ c] at hp2
    exact Fin.ext (le_antisymm hp1 hp2)

def pad {r : ℕ} (P : MultiweightedBond r G) : CountableBond G where
  partition := P.partition
  weight B i := if h : i < r then P.weight B ⟨i,h⟩ else 0
  weight_sum B hB := by
    refine ⟨r, (fun i hi => dite_eq_right (Nat.not_lt.mpr hi)), ?_⟩
    rw [← Fin.sum_univ_eq_sum_range]
    simpa using P.weight_sum B hB
  weight_off B hB i := by
    split_ifs
    · exact P.weight_off B hB _
    · rfl
  connected := P.connected

@[simp] theorem pad_fin {r : ℕ} (P : MultiweightedBond r G) (B : Finset V) (c : Fin r) :
    (pad P).weight B c = P.weight B c := by simp [pad]

@[simp] theorem pad_out {r : ℕ} (P : MultiweightedBond r G) (B : Finset V) {i : ℕ}
    (hi : r ≤ i) : (pad P).weight B i = 0 := by simp [pad, Nat.not_lt.mpr hi]

private theorem childSum_fin {r : ℕ} (P : MultiweightedBond r G) (B : Finset V) (c : Fin r) :
    (pad P).childSum B c = P.childSum B c := by
  change (∑ A ∈ children P.partition B, ((pad P).weight A.val c : ℕ)) = _
  simp [MultiweightedBond.childSum]

theorem pad_le_iff {r : ℕ} (P Q : MultiweightedBond r G) : pad P ≤ pad Q ↔ P ≤ Q := by
  constructor
  · intro h
    refine ⟨h.1, fun B c => ?_⟩
    have hh := h.2 B (c : ℕ)
    simpa only [childSum_fin, pad_fin] using hh
  · intro h
    refine ⟨h.1, fun B i => ?_⟩
    by_cases hi : i < r
    · have hh := h.2 B (⟨i, hi⟩ : Fin r)
      rw [← childSum_fin, ← pad_fin] at hh
      exact hh
    · simp [childSum, pad_out P _ (Nat.le_of_not_gt hi)]

theorem lower_supported {r : ℕ} {Q : MultiweightedBond r G} {P : CountableBond G}
    (h : P ≤ pad Q) (B : Finset V) {i : ℕ} (hi : r ≤ i) : P.weight B i = 0 := by
  by_cases hB : B ∈ P.partition.parts
  · obtain ⟨D, hD, hBD⟩ := h.1 hB
    have hm : (⟨B,hB⟩ : P.partition.parts) ∈ children P.partition D := by simp [children, hBD]
    have hs : (P.weight B i : ℕ) ≤ P.childSum D i :=
      single_le_sum (fun A _ => Nat.zero_le (P.weight A.val i : ℕ)) hm
    have hu := h.2 ⟨D,hD⟩ i
    change P.childSum D i ≤ ((pad Q).weight D i : ℕ) at hu
    rw [pad_out Q D hi] at hu
    apply Fin.ext
    exact Nat.eq_zero_of_le_zero (hs.trans hu)
  · exact P.weight_off B hB i

theorem sum_range_cutoff (f : ℕ → ℕ) {a b : ℕ}
    (ha : ∀ i ≥ a, f i = 0) (hb : ∀ i ≥ b, f i = 0) :
    (∑ i ∈ range a, f i) = ∑ i ∈ range b, f i := by
  let m := max a b
  have hg (c : ℕ) (hc : c ≤ m) (hz : ∀ i ≥ c, f i = 0) :
      (∑ i ∈ range c, f i) = ∑ i ∈ range m, f i :=
    sum_subset (range_subset_range.mpr hc) (fun i _ hn => hz i (Nat.le_of_not_gt (fun hlt => hn (mem_range.mpr hlt))))
  exact (hg a (le_max_left _ _) ha).trans (hg b (le_max_right _ _) hb).symm

def truncate (P : CountableBond G) {r : ℕ} (h : ∀ B i, r ≤ i → P.weight B i = 0) :
    MultiweightedBond r G where
  partition := P.partition
  weight B i := P.weight B i
  weight_sum B hB := by
    obtain ⟨m, hm, hs⟩ := P.weight_sum B hB
    rw [Fin.sum_univ_eq_sum_range (fun i => (P.weight B i : ℕ))]
    exact (sum_range_cutoff (fun i => P.weight B i) (fun i hi => congrArg Fin.val (h B i hi))
      (fun i hi => congrArg Fin.val (hm i hi))).trans hs
  weight_off B hB i := P.weight_off B hB i
  connected := P.connected

theorem pad_truncate (P : CountableBond G) {r : ℕ}
    (h : ∀ B i, r ≤ i → P.weight B i = 0) : pad (truncate P h) = P := by
  apply ext_weights (P := pad (truncate P h)) (Q := P) rfl
  intro B _ i
  by_cases hi : i < r
  · exact pad_fin (truncate P h) B ⟨i,hi⟩
  · exact (pad_out (truncate P h) B (Nat.le_of_not_gt hi)).trans (h B i (Nat.le_of_not_gt hi)).symm

/-- The literal lower intervals agree under zero-padding. -/
def padLowerIso {r : ℕ} (Q : MultiweightedBond r G) : Set.Iic Q ≃o Set.Iic (pad Q) where
  toFun P := ⟨pad P.val, (pad_le_iff _ _).mpr P.property⟩
  invFun P := by
    let h : ∀ B i, r ≤ i → P.val.weight B i = 0 :=
      fun B _ hi => lower_supported P.property B hi
    exact ⟨truncate P.val h, (pad_le_iff _ _).mp (by rw [pad_truncate]; exact P.property)⟩
  left_inv P := by
    apply Subtype.ext
    apply MultiweightedBond.ext_weights (P := truncate (pad P.val) (fun B _ hi => pad_out P.val B hi)) (Q := P.val) rfl
    intro B _ c
    exact pad_fin P.val B c
  right_inv P := Subtype.ext (pad_truncate P.val (fun B _ hi => lower_supported P.property B hi))
  map_rel_iff' := by
    intro P T
    exact pad_le_iff P.val T.val

end CountableBond
end
end D5.S3.Combinatorics.WeightedBond

set_option autoImplicit false
open Finset

namespace D5.S3.Combinatorics.WeightedBond
noncomputable section
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def colorExponent (P : CountableBond G) (i : ℕ) : ℕ :=
  ∑ B ∈ P.partition.parts, (P.weight B i : ℕ)

theorem colorExponent_finite (P : CountableBond G) :
    ∃ m : ℕ, ∀ i ≥ m, colorExponent P i = 0 := by
  have h (B : P.partition.parts) : ∃ m : ℕ, ∀ i ≥ m, P.weight B.val i = 0 := by
    obtain ⟨m, hm, _⟩ := P.weight_sum B.val B.property
    exact ⟨m, hm⟩
  choose bound hbound using h
  refine ⟨∑ B : P.partition.parts, bound B, fun i hi => ?_⟩
  apply sum_eq_zero
  intro B hB
  have hm : bound ⟨B,hB⟩ ≤ ∑ D : P.partition.parts, bound D :=
    single_le_sum (fun D _ => Nat.zero_le (bound D)) (mem_univ (⟨B,hB⟩ : P.partition.parts))
  exact congrArg Fin.val (hbound ⟨B,hB⟩ i (hm.trans hi))

theorem supported_iff_exponents (P : CountableBond G) (r : ℕ) :
    (∀ B i, r ≤ i → P.weight B i = 0) ↔ (∀ i ≥ r, colorExponent P i = 0) := by
  constructor
  · intro h i hr
    simp [colorExponent, h _ _ hr]
  · intro h B i hr
    by_cases hB : B ∈ P.partition.parts
    · have hle : (P.weight B i : ℕ) ≤ colorExponent P i :=
        single_le_sum (fun D _ => Nat.zero_le (P.weight D i : ℕ)) hB
      rw [h i hr] at hle
      exact Fin.ext (Nat.eq_zero_of_le_zero hle)
    · exact P.weight_off B hB i

/-- Restriction and zero-padding are inverse on the carrier selected by the substitution. -/
def supportedColorsEquiv (r : ℕ) :
    MultiweightedBond r G ≃ {P : CountableBond G // ∀ i ≥ r, colorExponent P i = 0} where
  toFun P := ⟨CountableBond.pad P, (supported_iff_exponents _ r).mp
    (fun B _ hi => CountableBond.pad_out P B hi)⟩
  invFun P := P.val.truncate ((supported_iff_exponents P.val r).mpr P.property)
  left_inv P := by
    apply MultiweightedBond.ext_weights
      (P := (CountableBond.pad P).truncate (fun B _ hi => CountableBond.pad_out P B hi)) (Q := P) rfl
    intro B _ c
    exact CountableBond.pad_fin P B c
  right_inv P := Subtype.ext (CountableBond.pad_truncate P.val _)

theorem monomial_specializes (P : CountableBond G) (r m : ℕ)
    (hm : ∀ i ≥ m, colorExponent P i = 0) :
    (∏ i ∈ range m, (if i < r then Polynomial.X else (0 : Polynomial ℚ)) ^ colorExponent P i) =
      if ∀ i ≥ r, colorExponent P i = 0 then
        Polynomial.X ^ (Fintype.card V - P.partition.parts.card) else 0 := by
  split_ifs with h
  · let Q := (supportedColorsEquiv r).symm ⟨P, h⟩
    have he : CountableBond.pad Q = P :=
      CountableBond.pad_truncate P ((supported_iff_exponents P r).mpr h)
    have hs (i : ℕ) :
        (if i < r then Polynomial.X else (0 : Polynomial ℚ)) ^ colorExponent P i =
          Polynomial.X ^ colorExponent P i := by
      by_cases hi : i < r
      · simp [hi]
      · simp [hi, h i (Nat.le_of_not_gt hi)]
    simp_rw [hs]
    rw [prod_pow_eq_pow_sum]
    congr 1
    calc
      _ = ∑ i ∈ range r, colorExponent P i :=
        CountableBond.sum_range_cutoff (colorExponent P) hm h
      _ = ∑ c : Fin r, ∑ B ∈ Q.partition.parts, (Q.weight B c : ℕ) := by
        rw [← Fin.sum_univ_eq_sum_range (colorExponent P), ← he]
        apply sum_congr rfl
        intro c _
        simp [colorExponent, CountableBond.pad, c.isLt]
      _ = _ := by
        rw [sum_comm]
        rw [← he]
        exact Q.total_weight_eq_rank
  · push Not at h
    obtain ⟨i, hi, hne⟩ := h
    have him : i ∈ range m := mem_range.mpr (by
      by_contra! hl
      exact hne (hm i hl))
    apply prod_eq_zero him
    simp [Nat.not_lt.mpr hi, zero_pow hne]

end
end D5.S3.Combinatorics.WeightedBond

namespace D5.S3.Combinatorics.WeightedBond

open Finset IncidenceAlgebra
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

instance : OrderBot (CountableBond G) where
  bot := CountableBond.pad (⊥ : MultiweightedBond 0 G)
  bot_le P := by
    refine ⟨bot_le, fun B i => ?_⟩
    simp [CountableBond.childSum, CountableBond.pad]

/-- Finite support of the top bounds every element in its actual lower interval. -/
private def countableLowerFintype (P : CountableBond G) : Fintype (Set.Iic P) := by
  let e := supportedColorsEquiv (colorExponent_finite P).choose (G := G)
  let Q := e.symm ⟨P, (colorExponent_finite P).choose_spec⟩
  have hp : CountableBond.pad Q = P :=
    congrArg Subtype.val (e.apply_symm_apply ⟨P, (colorExponent_finite P).choose_spec⟩)
  rw [← hp]
  exact Fintype.ofEquiv _ (CountableBond.padLowerIso Q).toEquiv

/-- The Möbius value is taken in the literal lower interval of the countable poset. -/
def sourceMu (P : CountableBond G) : ℤ :=
  letI := countableLowerFintype P
  letI : LocallyFiniteOrder (Set.Iic P) := Fintype.toLocallyFiniteOrder
  mu ℤ (⊥ : Set.Iic P) ⊤

theorem sourceMu_pad {r : ℕ} (P : MultiweightedBond r G) :
    sourceMu (CountableBond.pad P) = mu ℤ (⊥ : MultiweightedBond r G) P := by
  letI := countableLowerFintype (CountableBond.pad P)
  letI : LocallyFiniteOrder (Set.Iic (CountableBond.pad P)) := Fintype.toLocallyFiniteOrder
  let e := CountableBond.padLowerIso P
  have h := MultiweightedBond.mu_bot_orderIso e ⊤
  rw [e.map_top, MultiweightedBond.mu_bot_iic] at h
  exact h.symm

/-- In (7.1), set the first r colors to X and every other color to zero. -/
def sourceMonomial (r : ℕ) (P : CountableBond G) : Polynomial ℚ :=
  ∏ i ∈ range (colorExponent_finite P).choose,
    (if i < r then Polynomial.X else (0 : Polynomial ℚ)) ^ colorExponent P i

/-- The finite-support sum over the source's countable-color bond poset of K_n. -/
def sourceSpecialization (n r : ℕ) : Polynomial ℚ :=
  ∑ᶠ P : CountableBond (SimpleGraph.completeGraph (Fin n)),
    Polynomial.C (sourceMu P : ℚ) * sourceMonomial r P

theorem sourceSpecialization_eq (n r : ℕ) :
    sourceSpecialization n r = psiComplete n r := by
  let e := supportedColorsEquiv r (G := SimpleGraph.completeGraph (Fin n))
  let embed : CompleteBond n r ↪ CountableBond (SimpleGraph.completeGraph (Fin n)) :=
    e.toEmbedding.trans (Function.Embedding.subtype _)
  let a (P : CountableBond (SimpleGraph.completeGraph (Fin n))) :=
    Polynomial.C (sourceMu P : ℚ) * sourceMonomial r P
  have monomial (P : CountableBond (SimpleGraph.completeGraph (Fin n))) :
      sourceMonomial r P = if ∀ i ≥ r, colorExponent P i = 0 then
        Polynomial.X ^ (n - P.partition.parts.card) else 0 := by
    simpa only [Fintype.card_fin, sourceMonomial] using
      monomial_specializes P r _ (colorExponent_finite P).choose_spec
  change (∑ᶠ P, a P) = psiComplete n r
  rw [finsum_eq_sum_of_support_subset a (s := univ.map embed) ?_, sum_map]
  · unfold psiComplete
    apply sum_congr rfl
    intro P _
    change a (CountableBond.pad P) = _
    dsimp only [a]
    have hs : ∀ i ≥ r, colorExponent (CountableBond.pad P) i = 0 := (e P).property
    rw [sourceMu_pad, monomial, if_pos hs]
    rfl
  · intro P hP
    have hs : ∀ i ≥ r, colorExponent P i = 0 := by
      by_contra h
      exact hP (by simp [a, monomial, h])
    exact mem_map.mpr ⟨e.symm ⟨P, hs⟩, mem_univ _, congrArg Subtype.val (e.apply_symm_apply ⟨P, hs⟩)⟩

end
end D5.S3.Combinatorics.WeightedBond
