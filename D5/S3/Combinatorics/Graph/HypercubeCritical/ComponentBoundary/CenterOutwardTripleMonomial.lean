/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleMonomial
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleMonomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Three nonzero common-radius closed residuals with compatible Laurent exponents cannot cancel at distinct centers. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CenterOutwardTripleCurvature
import Mathlib.Tactic.LinearCombination

/-! Three-center Laurent residual obstruction for the Huang signing, in arbitrary
dimension. The square-curvature conclusion uses the previously verified
single-active support theorem. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CenterOutwardTripleMonomial

open scoped BigOperators
open BalancedCriticalSpectrum (Q)
open CenterOutwardDifference (outward closed_triple_energy_relation)
open CenterOutwardWeightGauge (monomial outward_monomial_mul)
open CenterOutwardTripleCurvature
  (SingleActiveSupport closed_eq_zero_of_fixed_center_bit closed_triple_single_active_eq_zero)

/-- At every row the entries sum to zero and at least one entry is zero.
Equivalently, either all entries vanish or exactly two are opposite nonzero values. -/
def TwoContacts {n : ℕ} (x y z : Q n → ℝ) : Prop :=
  ∀ r, (x r = 0 ∨ y r = 0 ∨ z r = 0) ∧ (x r + y r + z r = 0)

/-- The coordinate contribution to the exponent in the center's weight gauge. -/
def relativeBit (d r : Bool) : ℤ := if r = d then 0 else 1

/-- Each common support row has the same Laurent exponent in either gauge. -/
def ExponentAgreement {n : ℕ} (a b : Q n) (x y : Q n → ℝ)
    (u v : Fin n → ℤ) : Prop :=
  ∀ r, x r ≠ 0 → y r ≠ 0 → ∀ i,
    u i + relativeBit (a i) (r i) = v i + relativeBit (b i) (r i)

private theorem ExponentAgreement.symm {n : ℕ} {a b : Q n} {x y : Q n → ℝ}
    {u v : Fin n → ℤ} (h : ExponentAgreement a b x y u v) :
    ExponentAgreement b a y x v u :=
  fun r hy hx i => (h r hx hy i).symm

/-- Coordinates on which a row differs from its reference vertex. -/
def differingCoordinates {n : ℕ} (d r : Q n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => r i ≠ d i)

private theorem TwoContacts.rotate {n : ℕ} {x y z : Q n → ℝ}
    (h : TwoContacts x y z) : TwoContacts y z x := by
  intro r
  obtain ⟨hz, hs⟩ := h r
  exact ⟨by tauto, by linarith only [hs]⟩

private theorem TwoContacts.cancel {n : ℕ} {x y z : Q n → ℝ}
    (h : TwoContacts x y z) : x + y + z = 0 := by
  funext r
  exact (h r).2

private theorem TwoContacts.other_ne_zero {n : ℕ} {x y z : Q n → ℝ}
    (h : TwoContacts x y z) (r : Q n) (hx : x r ≠ 0) (hy : y r = 0) :
    z r ≠ 0 := by
  intro hz
  exact hx (by simpa only [hy, hz, add_zero] using (h r).2)

private def pairRows {n : ℕ} (x y : Q n → ℝ) : Finset (Q n) := by
  classical
  exact Finset.univ.filter (fun r => x r ≠ 0 ∧ y r ≠ 0)

private theorem mem_pairRows {n : ℕ} {x y : Q n → ℝ} {r : Q n} :
    r ∈ pairRows x y ↔ x r ≠ 0 ∧ y r ≠ 0 := by
  classical
  simp [pairRows]

private def pairEnergy {n : ℕ} (x y : Q n → ℝ) : ℝ :=
  ∑ r ∈ pairRows x y, x r ^ 2

private theorem energy_split {n : ℕ} {x y z : Q n → ℝ} (h : TwoContacts x y z) :
    (∑ r, x r ^ 2) = pairEnergy z x + pairEnergy x y := by
  classical
  unfold pairEnergy pairRows
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hx : x r = 0
  · simp [hx]
  by_cases hy : y r = 0
  · have hz := h.other_ne_zero r hx hy
    have hzx : z r = -(x r) := by linarith only [(h r).2, hy]
    have hsq : z r ^ 2 = x r ^ 2 := by rw [hzx, neg_sq]
    simp [hx, hy, hz, hsq]
  · have hz : z r = 0 := ((h r).1.resolve_left hx).resolve_left hy
    simp [hx, hy, hz]

private def blockWeight {n : ℕ} (w : Fin n → ℝ) (D : Finset (Fin n)) : ℝ :=
  ∑ i ∈ D, w i ^ 2

private theorem center_distance_eq {n : ℕ} (m a b : Q n) (A B : Finset (Fin n))
    (hAB : Disjoint A B) (ha : ∀ i, a i ≠ m i ↔ i ∈ A)
    (hb : ∀ i, b i ≠ m i ↔ i ∈ B) :
    (Finset.univ.filter fun i => a i ≠ b i) = A ∪ B := by
  ext i
  have hd : ¬ (i ∈ A ∧ i ∈ B) := fun h => Finset.disjoint_left.mp hAB h.1 h.2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  have hleft := ha i
  have hright := hb i
  cases h₁ : a i <;> cases h₂ : b i <;> cases h₃ : m i <;>
    simp [h₁, h₂, h₃] at hleft hright ⊢ <;> tauto

private theorem blockWeight_center_distance {n : ℕ} (w : Fin n → ℝ)
    (m a b : Q n) (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (ha : ∀ i, a i ≠ m i ↔ i ∈ A) (hb : ∀ i, b i ≠ m i ↔ i ∈ B) :
    (∑ i ∈ Finset.univ.filter (fun i => a i ≠ b i), w i ^ 2) =
      blockWeight w A + blockWeight w B := by
  simp only [center_distance_eq m a b A B hAB ha hb, Finset.sum_union hAB, blockWeight]

/-- The three pair energies correspond to the opposite private blocks. The
identities have no denominator, so apply before the blocks are known to be nonempty. -/
private theorem pair_energy_proportional {n : ℕ} (w : Fin n → ℝ) (m a b c : Q n)
    (A B C : Finset (Fin n))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (ha : ∀ i, a i ≠ m i ↔ i ∈ A) (hb : ∀ i, b i ≠ m i ↔ i ∈ B)
    (hc : ∀ i, c i ≠ m i ↔ i ∈ C) (x y z : Q n → ℝ)
    (hx : outward w a x = 0) (hy : outward w b y = 0) (hz : outward w c z = 0)
    (h : TwoContacts x y z) :
    let s := blockWeight w A + blockWeight w B + blockWeight w C
    let p := pairEnergy y z + pairEnergy z x + pairEnergy x y
    s * pairEnergy y z = blockWeight w A * p ∧
    s * pairEnergy z x = blockWeight w B * p ∧
    s * pairEnergy x y = blockWeight w C * p := by
  have hxE := energy_split h
  have hyE := energy_split h.rotate
  have hzE := energy_split h.rotate.rotate
  have hab := blockWeight_center_distance w m a b A B hAB ha hb
  have hac := blockWeight_center_distance w m a c A C hAC ha hc
  have hba := blockWeight_center_distance w m b a B A hAB.symm hb ha
  have hbc := blockWeight_center_distance w m b c B C hBC hb hc
  have hca := blockWeight_center_distance w m c a C A hAC.symm hc ha
  have hcb := blockWeight_center_distance w m c b C B hBC.symm hc hb
  have h₁ := closed_triple_energy_relation w a b c x y z hx hy hz h.cancel
  have h₂ := closed_triple_energy_relation w b c a y z x hy hz hx h.rotate.cancel
  have h₃ := closed_triple_energy_relation w c a b z x y hz hx hy h.rotate.rotate.cancel
  rw [hab, hac, hyE, hzE] at h₁
  rw [hbc, hba, hzE, hxE] at h₂
  rw [hca, hcb, hxE, hyE] at h₃
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (1 / 2 : ℝ) * h₂ - (1 / 2 : ℝ) * h₃
  · linear_combination (1 / 2 : ℝ) * h₃ - (1 / 2 : ℝ) * h₁
  · linear_combination (1 / 2 : ℝ) * h₁ - (1 / 2 : ℝ) * h₂

private theorem exists_row_ne_zero {n : ℕ} {v : Q n → ℝ} (hv : v ≠ 0) :
    ∃ r, v r ≠ 0 := by
  by_contra h
  apply hv
  funext r
  by_contra hr
  exact h ⟨r, hr⟩

private theorem pairEnergy_pos_iff {n : ℕ} (x y : Q n → ℝ) :
    0 < pairEnergy x y ↔ ∃ r, x r ≠ 0 ∧ y r ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    have he : pairRows x y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      exact hn ⟨r, mem_pairRows.mp hr⟩
    simp [pairEnergy, he] at h
  · rintro ⟨r, hx, hy⟩
    exact Finset.sum_pos' (fun s _ => sq_nonneg (x s))
      ⟨r, mem_pairRows.mpr ⟨hx, hy⟩, sq_pos_of_ne_zero hx⟩

private theorem pairEnergy_nonneg {n : ℕ} (x y : Q n → ℝ) : 0 ≤ pairEnergy x y :=
  Finset.sum_nonneg fun r _ => sq_nonneg (x r)

private theorem blockWeight_one {n : ℕ} (D : Finset (Fin n)) :
    blockWeight (fun _ => 1) D = (D.card : ℝ) := by
  simp [blockWeight]

private theorem nonempty_iff_card_pos {n : ℕ} (D : Finset (Fin n)) :
    D.Nonempty ↔ 0 < (D.card : ℝ) := by
  rw [Nat.cast_pos, Finset.card_pos]

private theorem shared_rows_of_proportional {n : ℕ} {s p : ℝ}
    (hs : 0 < s) (hp : 0 < p) (D : Finset (Fin n)) (y z : Q n → ℝ)
    (h : s * pairEnergy y z = (D.card : ℝ) * p) :
    (∃ r, y r ≠ 0 ∧ z r ≠ 0) ↔ D.Nonempty := by
  rw [← pairEnergy_pos_iff y z, nonempty_iff_card_pos D]
  constructor
  · intro hpair
    have hprod : 0 < (D.card : ℝ) * p := by
      rw [← h]
      exact mul_pos hs hpair
    exact pos_of_mul_pos_left hprod hp.le
  · intro hcard
    have hprod : 0 < s * pairEnergy y z := by
      rw [h]
      exact mul_pos hcard hp
    exact pos_of_mul_pos_right hprod hs.le

private theorem bit_eq_of_offset_match (a b r s : Bool) (u v : ℤ) (hab : a ≠ b)
    (hr : u + relativeBit a r = v + relativeBit b r)
    (hs : u + relativeBit a s = v + relativeBit b s) : r = s := by
  cases a <;> cases b <;> cases r <;> cases s <;> simp_all [relativeBit] <;> omega

/-- An axis private to the first center is fixed to the majority bit over the
entire first support. The opposite pair supplies the offset equality even if
one of the two pairs incident to the first center is absent. -/
private theorem fixed_on_own_block {n : ℕ} (m a b c : Q n) (A : Finset (Fin n))
    (x y z : Q n → ℝ) (u v w : Fin n → ℤ)
    (ha : ∀ i ∈ A, a i ≠ m i) (hb : ∀ i ∈ A, b i = m i)
    (hc : ∀ i ∈ A, c i = m i)
    (hx : outward (fun _ => 1) a x = 0) (hn : x ≠ 0)
    (h : TwoContacts x y z)
    (hxy : ExponentAgreement a b x y u v) (hyz : ExponentAgreement b c y z v w)
    (hzx : ExponentAgreement c a z x w u)
    (hopp : A.Nonempty → ∃ r, y r ≠ 0 ∧ z r ≠ 0) :
    ∀ r, x r ≠ 0 → ∀ i ∈ A, r i = m i := by
  intro r hr i hi
  obtain ⟨q, hqy, hqz⟩ := hopp ⟨i, hi⟩
  have hbc : b i = c i := (hb i hi).trans (hc i hi).symm
  have huv : v i = w i := by
    have he := hyz q hqy hqz i
    rw [← hbc] at he
    omega
  have hmatch (s : Q n) (hs : x s ≠ 0) :
      u i + relativeBit (a i) (s i) = v i + relativeBit (b i) (s i) := by
    by_cases hsy : y s = 0
    · have hsz := h.other_ne_zero s hs hsy
      simpa only [← hbc, ← huv] using (hzx s hsz hs i).symm
    · exact hxy s hs hsy i
  have hab : a i ≠ b i := by simpa only [hb i hi] using ha i hi
  by_contra hri
  have hra : r i = a i := by
    have hai := ha i hi
    revert hai hri
    cases r i <;> cases a i <;> cases m i <;> simp
  apply hn
  apply closed_eq_zero_of_fixed_center_bit (fun _ => 1) a x i one_ne_zero hx
  intro s hs
  exact (bit_eq_of_offset_match (a i) (b i) (s i) (r i) (u i) (v i)
    hab (hmatch s hs) (hmatch r hr)).trans hra

private theorem eq_majority_of_not_mem {n : ℕ} {m d : Q n} {D : Finset (Fin n)}
    (hd : ∀ i, d i ≠ m i ↔ i ∈ D) {i : Fin n} (hi : i ∉ D) : d i = m i := by
  by_contra h
  exact hi ((hd i).mp h)

private theorem differingCoordinates_union {n : ℕ} (m d r : Q n)
    (D : Finset (Fin n)) (hd : ∀ i, d i ≠ m i ↔ i ∈ D)
    (hr : ∀ i ∈ D, r i = m i) :
    differingCoordinates d r = D ∪ differingCoordinates m r ∧
    Disjoint D (differingCoordinates m r) := by
  constructor
  · ext i
    by_cases hi : i ∈ D
    · have hne : r i ≠ d i := by rw [hr i hi]; exact ((hd i).mpr hi).symm
      simp [differingCoordinates, hne, hi]
    · simp [differingCoordinates, hi, eq_majority_of_not_mem hd hi]
  · apply Finset.disjoint_left.mpr
    intro i hi him
    exact (Finset.mem_filter.mp him).2 (hr i hi)

/-- With the first private block empty, its residual must meet each of the
other two residuals. A shared row with the second center then has strictly
larger distance from that center than from the majority. -/
private theorem own_block_nonempty {n : ℕ} (m a b : Q n) (A B : Finset (Fin n))
    (ha : ∀ i, a i ≠ m i ↔ i ∈ A) (hb : ∀ i, b i ≠ m i ↔ i ∈ B)
    (x y z : Q n → ℝ) (hy : y ≠ 0) (hz : z ≠ 0)
    (h : TwoContacts x y z)
    (hA : (∃ r, y r ≠ 0 ∧ z r ≠ 0) ↔ A.Nonempty)
    (hB : (∃ r, z r ≠ 0 ∧ x r ≠ 0) ↔ B.Nonempty)
    (hfixed : ∀ r, y r ≠ 0 → ∀ i ∈ B, r i = m i) (R : ℕ)
    (hxr : ∀ r, x r ≠ 0 → (differingCoordinates a r).card = R)
    (hyr : ∀ r, y r ≠ 0 → (differingCoordinates b r).card = R) :
    A.Nonempty := by
  by_contra hn
  have ham : a = m := funext fun i =>
    eq_majority_of_not_mem ha (fun hi => hn ⟨i, hi⟩)
  obtain ⟨s, hs⟩ := exists_row_ne_zero hz
  have hsy : y s = 0 := by
    by_contra hsy
    exact hn (hA.mp ⟨s, hsy, hs⟩)
  have hsx : x s ≠ 0 := by
    intro hsx
    exact hs (by simpa only [hsx, hsy, zero_add] using (h s).2)
  have hBpos : 0 < B.card := Finset.card_pos.mpr (hB.mp ⟨s, hs, hsx⟩)
  obtain ⟨r, hr⟩ := exists_row_ne_zero hy
  have hrz : z r = 0 := by
    by_contra hrz
    exact hn (hA.mp ⟨r, hr, hrz⟩)
  have hrx := h.rotate.other_ne_zero r hr hrz
  obtain ⟨hu, hd⟩ := differingCoordinates_union m b r B hb (hfixed r hr)
  have hxm := hxr r hrx
  rw [ham] at hxm
  have hym := hyr r hr
  rw [hu, Finset.card_union_of_disjoint hd, hxm] at hym
  omega

private theorem outward_const_mul {n : ℕ} (w : Fin n → ℝ) (d : Q n)
    (k : ℝ) (v : Q n → ℝ) (r : Q n) :
    outward w d (fun q => k * v q) r = k * outward w d v r := by
  simp only [outward, BalancedCriticalSpectrum.gamma_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : r i ≠ d i <;> simp [hi] <;> ring

/-- On the residual's support, the center monomial equals the majority
monomial times a constant (the product of the weights of the private block). -/
private theorem majority_weighted_closed {n : ℕ} (w : Fin n → ℝ) (m d : Q n)
    (D : Finset (Fin n)) (v : Q n → ℝ) (hw : ∀ i, w i ≠ 0)
    (hd : ∀ i, d i ≠ m i ↔ i ∈ D)
    (hfixed : ∀ r, v r ≠ 0 → ∀ i ∈ D, r i = m i)
    (hclosed : outward (fun _ => 1) d v = 0) :
    outward w d (monomial w m * v) = 0 := by
  let k := ∏ i ∈ D, w i
  have hk : k ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)
  have hfactor : monomial w d * v = fun r => k * (monomial w m * v) r := by
    funext r
    change monomial w d r * v r = k * (monomial w m r * v r)
    by_cases hr : v r = 0
    · simp [hr]
    · obtain ⟨hu, hdj⟩ := differingCoordinates_union m d r D hd (hfixed r hr)
      have hprod : monomial w d r = k * monomial w m r := by
        change (∏ i ∈ differingCoordinates d r, w i) =
          k * (∏ i ∈ differingCoordinates m r, w i)
        simp only [hu, Finset.prod_union hdj, k]
      rw [hprod, mul_assoc]
  have h := outward_monomial_mul w d v
  rw [hclosed, mul_zero, hfactor] at h
  funext r
  have hr := congrFun h r
  rw [outward_const_mul] at hr
  exact (mul_eq_zero.mp hr).resolve_left hk

private theorem TwoContacts.mul {n : ℕ} {x y z : Q n → ℝ} (h : TwoContacts x y z)
    (f : Q n → ℝ) : TwoContacts (f * x) (f * y) (f * z) := by
  intro r
  simp only [Pi.mul_apply]
  refine ⟨?_, ?_⟩
  · rcases (h r).1 with hx | hy | hz
    · exact Or.inl (by rw [hx, mul_zero])
    · exact Or.inr (Or.inl (by rw [hy, mul_zero]))
    · exact Or.inr (Or.inr (by rw [hz, mul_zero]))
  · rw [← mul_add, ← mul_add, (h r).2, mul_zero]

private def blockWeights {n : ℕ} (D : Finset (Fin n)) (t : ℝ) (i : Fin n) : ℝ :=
  if i ∈ D then t else 1

private theorem blockWeights_ne_zero {n : ℕ} (D : Finset (Fin n)) {t : ℝ} (ht : t ≠ 0) :
    ∀ i, blockWeights D t i ≠ 0 := by
  intro i
  by_cases hi : i ∈ D <;> simp [blockWeights, hi, ht]

private theorem blockWeight_scale_own {n : ℕ} (D : Finset (Fin n)) (t : ℝ) :
    blockWeight (blockWeights D t) D = (D.card : ℝ) * t ^ 2 := by
  unfold blockWeight
  calc
    _ = ∑ _i ∈ D, t ^ 2 := Finset.sum_congr rfl fun i hi => by simp [blockWeights, hi]
    _ = _ := by simp [nsmul_eq_mul]

private theorem blockWeight_scale_disjoint {n : ℕ} (D E : Finset (Fin n)) (t : ℝ)
    (hDE : Disjoint D E) :
    blockWeight (blockWeights D t) E = (E.card : ℝ) := by
  calc
    _ = blockWeight (fun _ => 1) E := by
      unfold blockWeight
      apply Finset.sum_congr rfl
      intro i hi
      have hni : i ∉ D := fun h => Finset.disjoint_left.mp hDE h hi
      simp [blockWeights, hni]
    _ = _ := blockWeight_one E

private def activeCoordinates {n : ℕ} (m : Q n) (D : Finset (Fin n)) (r : Q n) :
    Finset (Fin n) :=
  D.filter (fun i => r i ≠ m i)

private theorem monomial_at_blockWeights {n : ℕ} (m r : Q n)
    (D : Finset (Fin n)) (t : ℝ) :
    monomial (blockWeights D t) m r = t ^ (activeCoordinates m D r).card := by
  unfold monomial blockWeights
  rw [← Finset.prod_filter]
  have hset : (Finset.univ.filter (fun i => r i ≠ m i)).filter (fun i => i ∈ D) =
      activeCoordinates m D r := by
    ext i
    simp [activeCoordinates, and_comm]
  rw [hset, Finset.prod_const]

private theorem pairEnergy_at_blockWeights {n : ℕ} (m : Q n)
    (D : Finset (Fin n)) (t : ℝ) (ht : t ≠ 0) (y z : Q n → ℝ) :
    pairEnergy (monomial (blockWeights D t) m * y) (monomial (blockWeights D t) m * z) =
      ∑ r ∈ pairRows y z, (t ^ 2) ^ (activeCoordinates m D r).card * y r ^ 2 := by
  let f := monomial (blockWeights D t) m
  have hf (r : Q n) : f r ≠ 0 := by
    dsimp only [f]
    rw [monomial_at_blockWeights]
    exact pow_ne_zero _ ht
  have hset : pairRows (f * y) (f * z) = pairRows y z := by
    ext r
    simp [mem_pairRows, Pi.mul_apply, mul_ne_zero_iff, hf r]
  change pairEnergy (f * y) (f * z) = _
  unfold pairEnergy
  rw [hset]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Pi.mul_apply, f, monomial_at_blockWeights, mul_pow]
  rw [pow_right_comm t (activeCoordinates m D r).card 2]

private theorem pairEnergy_at_blockWeights_of_fixed {n : ℕ} (m : Q n)
    (D : Finset (Fin n)) (t : ℝ) (ht : t ≠ 0) (z x : Q n → ℝ)
    (hfixed : ∀ r, x r ≠ 0 → ∀ i ∈ D, r i = m i) :
    pairEnergy (monomial (blockWeights D t) m * z) (monomial (blockWeights D t) m * x) =
      pairEnergy z x := by
  rw [pairEnergy_at_blockWeights m D t ht]
  unfold pairEnergy
  apply Finset.sum_congr rfl
  intro r hr
  have he : activeCoordinates m D r = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun i hi hn => hn (hfixed r (mem_pairRows.mp hr).2 i hi)
  simp [he]

/-- A pair energy scales by the square of the block weight. When compared at
weights one, two, and four, positivity forces every shared row to have exactly
one active bit in the scaled block. -/
private theorem one_active_of_block_ratio {n : ℕ} (m : Q n) (D E : Finset (Fin n))
    (hDE : Disjoint D E) (hE : E.Nonempty) (x y z : Q n → ℝ)
    (hfixed : ∀ r, x r ≠ 0 → ∀ i ∈ D, r i = m i)
    (hratio : ∀ t : ℝ, t ≠ 0 →
      let w := blockWeights D t
      let f := monomial w m
      blockWeight w E * pairEnergy (f * y) (f * z) =
        blockWeight w D * pairEnergy (f * z) (f * x)) :
    ∀ r, y r ≠ 0 → z r ≠ 0 → (activeCoordinates m D r).card = 1 := by
  let S := pairRows y z
  let k (r : Q n) := (activeCoordinates m D r).card
  have heq (t : ℝ) (ht : t ≠ 0) :
      (E.card : ℝ) * (∑ r ∈ S, (t ^ 2) ^ k r * y r ^ 2) =
        (D.card : ℝ) * t ^ 2 * pairEnergy z x := by
    have h := hratio t ht
    dsimp only at h
    rw [blockWeight_scale_disjoint D E t hDE, blockWeight_scale_own D t,
      pairEnergy_at_blockWeights m D t ht y z,
      pairEnergy_at_blockWeights_of_fixed m D t ht z x hfixed] at h
    exact h
  have hunit : (E.card : ℝ) * pairEnergy y z = (D.card : ℝ) * pairEnergy z x := by
    simpa only [one_pow, one_mul, mul_one, pairEnergy, S] using heq 1 one_ne_zero
  have hmoment (t : ℝ) (ht : t ≠ 0) :
      (∑ r ∈ S, (t ^ 2) ^ k r * y r ^ 2) = t ^ 2 * pairEnergy y z := by
    apply mul_left_cancel₀ (ne_of_gt ((nonempty_iff_card_pos E).mp hE))
    linear_combination heq t ht - t ^ 2 * hunit
  let f (r : Q n) := (4 : ℝ) ^ k r
  have htwo : (∑ r ∈ S, f r * y r ^ 2) = 4 * pairEnergy y z := by
    simpa only [f, show (2 : ℝ) ^ 2 = 4 by norm_num] using hmoment 2 (by norm_num)
  have hfour : (∑ r ∈ S, f r ^ 2 * y r ^ 2) = 16 * pairEnergy y z := calc
    _ = ∑ r ∈ S, ((4 : ℝ) ^ 2) ^ k r * y r ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [show f r ^ 2 = ((4 : ℝ) ^ 2) ^ k r from pow_right_comm 4 (k r) 2]
    _ = _ := by
      simpa only [show (4 : ℝ) ^ 2 = 16 by norm_num] using hmoment 4 (by norm_num)
  have hvariance :
      (∑ r ∈ S, y r ^ 2 * (f r - 4) ^ 2) =
        (∑ r ∈ S, f r ^ 2 * y r ^ 2) -
          8 * (∑ r ∈ S, f r * y r ^ 2) + 16 * (∑ r ∈ S, y r ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hzero : (∑ r ∈ S, y r ^ 2 * (f r - 4) ^ 2) = 0 := by
    rw [htwo, hfour] at hvariance
    change (∑ r ∈ S, y r ^ 2 * (f r - 4) ^ 2) =
      16 * pairEnergy y z - 8 * (4 * pairEnergy y z) + 16 * pairEnergy y z at hvariance
    linarith only [hvariance]
  intro r hy hz
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun q (_ : q ∈ S) => mul_nonneg (sq_nonneg (y q)) (sq_nonneg (f q - 4)))).mp
      hzero r (mem_pairRows.mpr ⟨hy, hz⟩)
  have hf : f r = 4 := sub_eq_zero.mp
    (sq_eq_zero_iff.mp ((mul_eq_zero.mp hterm).resolve_left (pow_ne_zero 2 hy)))
  apply (pow_right_strictMono₀ (show (1 : ℝ) < 4 by norm_num)).injective
  simpa only [f, k, pow_one] using hf

private theorem singleton_active_support {n : ℕ} (m r : Q n)
    (A B C : Finset (Fin n)) (hAC : Disjoint A C)
    (ha : ∀ i ∈ A, r i = m i) (hb : ∀ i ∈ B, r i = m i)
    (hc : (activeCoordinates m C r).card = 1) :
    ∃ k ∈ A ∪ B ∪ C, k ∉ A ∧ r k ≠ m k ∧
      ∀ l ∈ A ∪ B ∪ C, l ≠ k → r l = m l := by
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hc
  have hkmem : k ∈ activeCoordinates m C r := by rw [hk]; simp
  have hkC := (Finset.mem_filter.mp hkmem).1
  refine ⟨k, Finset.mem_union.mpr (Or.inr hkC),
    fun h => Finset.disjoint_left.mp hAC h hkC, (Finset.mem_filter.mp hkmem).2, ?_⟩
  intro l hl hlk
  rcases Finset.mem_union.mp hl with hlAB | hlC
  · rcases Finset.mem_union.mp hlAB with hlA | hlB
    · exact ha l hlA
    · exact hb l hlB
  · by_contra hne
    have hlmem : l ∈ activeCoordinates m C r := Finset.mem_filter.mpr ⟨hlC, hne⟩
    exact hlk (by simpa only [hk, Finset.mem_singleton] using hlmem)

private theorem residual_single_active {n : ℕ} (m : Q n) (A B C : Finset (Fin n))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (x y z : Q n → ℝ)
    (h : TwoContacts x y z)
    (hx : ∀ r, x r ≠ 0 → ∀ i ∈ A, r i = m i)
    (hy : ∀ r, y r ≠ 0 → ∀ i ∈ B, r i = m i)
    (hz : ∀ r, z r ≠ 0 → ∀ i ∈ C, r i = m i)
    (hzx : ∀ r, z r ≠ 0 → x r ≠ 0 → (activeCoordinates m B r).card = 1)
    (hxy : ∀ r, x r ≠ 0 → y r ≠ 0 → (activeCoordinates m C r).card = 1) :
    SingleActiveSupport m (A ∪ B ∪ C) A x := by
  intro r hr
  by_cases hry : y r = 0
  · have hrz := h.other_ne_zero r hr hry
    rw [Finset.union_right_comm A B C]
    exact singleton_active_support m r A C B hAB (hx r hr) (hz r hrz) (hzx r hrz hr)
  · exact singleton_active_support m r A B C hAC (hx r hr) (hy r hry) (hxy r hr hry)

/-- Three nonzero closed Laurent residuals at a common exact Hamming radius
force three nonempty private blocks and single-active support on their union.
It suffices that two of the centers differ. -/
theorem closed_triple_laurent_single_active {n : ℕ} (m a b c : Q n)
    (A B C : Finset (Fin n)) (hcenters : a ≠ b ∨ b ≠ c)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (ha : ∀ i, a i ≠ m i ↔ i ∈ A) (hb : ∀ i, b i ≠ m i ↔ i ∈ B)
    (hc : ∀ i, c i ≠ m i ↔ i ∈ C)
    (x y z : Q n → ℝ) (hxn : x ≠ 0) (hyn : y ≠ 0) (hzn : z ≠ 0)
    (hx : outward (fun _ => 1) a x = 0) (hy : outward (fun _ => 1) b y = 0)
    (hz : outward (fun _ => 1) c z = 0) (h : TwoContacts x y z)
    (R : ℕ)
    (hxr : ∀ r, x r ≠ 0 → (differingCoordinates a r).card = R)
    (hyr : ∀ r, y r ≠ 0 → (differingCoordinates b r).card = R)
    (hzr : ∀ r, z r ≠ 0 → (differingCoordinates c r).card = R)
    (u v w : Fin n → ℤ)
    (hxy : ExponentAgreement a b x y u v)
    (hyz : ExponentAgreement b c y z v w)
    (hxz : ExponentAgreement a c x z u w) :
    A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧
      SingleActiveSupport m (A ∪ B ∪ C) A x ∧
      SingleActiveSupport m (A ∪ B ∪ C) B y ∧
      SingleActiveSupport m (A ∪ B ∪ C) C z := by
  have hzx := hxz.symm
  have hsome : A.Nonempty ∨ B.Nonempty ∨ C.Nonempty := by
    by_contra hn
    have hAn : ¬ A.Nonempty := fun hh => hn (Or.inl hh)
    have hBn : ¬ B.Nonempty := fun hh => hn (Or.inr (Or.inl hh))
    have hCn : ¬ C.Nonempty := fun hh => hn (Or.inr (Or.inr hh))
    have ham : a = m := funext fun i =>
      eq_majority_of_not_mem ha (fun hi => hAn ⟨i, hi⟩)
    have hbm : b = m := funext fun i =>
      eq_majority_of_not_mem hb (fun hi => hBn ⟨i, hi⟩)
    have hcm : c = m := funext fun i =>
      eq_majority_of_not_mem hc (fun hi => hCn ⟨i, hi⟩)
    rcases hcenters with hab | hbc
    · exact hab (ham.trans hbm.symm)
    · exact hbc (hbm.trans hcm.symm)
  let s : ℝ := (A.card : ℝ) + B.card + C.card
  have hs : 0 < s := by
    have hA0 : 0 ≤ (A.card : ℝ) := Nat.cast_nonneg _
    have hB0 : 0 ≤ (B.card : ℝ) := Nat.cast_nonneg _
    have hC0 : 0 ≤ (C.card : ℝ) := Nat.cast_nonneg _
    change 0 < (A.card : ℝ) + B.card + C.card
    rcases hsome with hA | hB | hC
    · linarith only [hB0, hC0, (nonempty_iff_card_pos A).mp hA]
    · linarith only [hA0, hC0, (nonempty_iff_card_pos B).mp hB]
    · linarith only [hA0, hB0, (nonempty_iff_card_pos C).mp hC]
  let p := pairEnergy y z + pairEnergy z x + pairEnergy x y
  have hp : 0 < p := by
    obtain ⟨r, hr⟩ := exists_row_ne_zero hxn
    have hpos : 0 < ∑ q, x q ^ 2 := Finset.sum_pos' (fun q _ => sq_nonneg (x q))
      ⟨r, Finset.mem_univ r, sq_pos_of_ne_zero hr⟩
    rw [energy_split h] at hpos
    change 0 < pairEnergy y z + pairEnergy z x + pairEnergy x y
    linarith only [hpos, pairEnergy_nonneg y z]
  have hunit := pair_energy_proportional (fun _ => 1) m a b c A B C
    hAB hAC hBC ha hb hc x y z hx hy hz h
  simp only [blockWeight_one] at hunit
  obtain ⟨hpa, hpb, hpc⟩ := hunit
  have hsharedA := shared_rows_of_proportional hs hp A y z hpa
  have hsharedB := shared_rows_of_proportional hs hp B z x hpb
  have hsharedC := shared_rows_of_proportional hs hp C x y hpc
  have offBlock (d : Q n) (D E : Finset (Fin n)) (hED : Disjoint E D)
      (hd : ∀ i, d i ≠ m i ↔ i ∈ D) (i : Fin n) (hi : i ∈ E) : d i = m i :=
    eq_majority_of_not_mem hd (fun hiD => Finset.disjoint_left.mp hED hi hiD)
  have hfixA := fixed_on_own_block m a b c A x y z u v w
    (fun i hi => (ha i).mpr hi) (offBlock b B A hAB hb) (offBlock c C A hAC hc)
    hx hxn h hxy hyz hzx hsharedA.mpr
  have hfixB := fixed_on_own_block m b c a B y z x v w u
    (fun i hi => (hb i).mpr hi) (offBlock c C B hBC hc) (offBlock a A B hAB.symm ha)
    hy hyn h.rotate hyz hzx hxy hsharedB.mpr
  have hfixC := fixed_on_own_block m c a b C z x y w u v
    (fun i hi => (hc i).mpr hi) (offBlock a A C hAC.symm ha) (offBlock b B C hBC.symm hb)
    hz hzn h.rotate.rotate hzx hxy hyz hsharedC.mpr
  have hA := own_block_nonempty m a b A B ha hb x y z hyn hzn
    h hsharedA hsharedB hfixB R hxr hyr
  have hB := own_block_nonempty m b c B C hb hc y z x hzn hxn
    h.rotate hsharedB hsharedC hfixC R hyr hzr
  have hC := own_block_nonempty m c a C A hc ha z x y hxn hyn
    h.rotate.rotate hsharedC hsharedA hfixA R hzr hxr
  have hratio (weights : Fin n → ℝ) (hw : ∀ i, weights i ≠ 0) :
      let f := monomial weights m
      blockWeight weights B * pairEnergy (f * y) (f * z) =
        blockWeight weights A * pairEnergy (f * z) (f * x) ∧
      blockWeight weights C * pairEnergy (f * z) (f * x) =
        blockWeight weights B * pairEnergy (f * x) (f * y) ∧
      blockWeight weights A * pairEnergy (f * x) (f * y) =
        blockWeight weights C * pairEnergy (f * y) (f * z) := by
    let f := monomial weights m
    have hwa := majority_weighted_closed weights m a A x hw ha hfixA hx
    have hwb := majority_weighted_closed weights m b B y hw hb hfixB hy
    have hwc := majority_weighted_closed weights m c C z hw hc hfixC hz
    obtain ⟨hpa, hpb, hpc⟩ :=
      pair_energy_proportional weights m a b c A B C hAB hAC hBC ha hb hc
        (f * x) (f * y) (f * z) hwa hwb hwc (h.mul f)
    obtain ⟨i, hi⟩ := hA
    have htotal : blockWeight weights A + blockWeight weights B + blockWeight weights C ≠ 0 := by
      have ha0 : 0 < blockWeight weights A := Finset.sum_pos'
        (fun j _ => sq_nonneg (weights j)) ⟨i, hi, sq_pos_of_ne_zero (hw i)⟩
      have hb0 : 0 ≤ blockWeight weights B := Finset.sum_nonneg (fun j _ => sq_nonneg (weights j))
      have hc0 : 0 ≤ blockWeight weights C := Finset.sum_nonneg (fun j _ => sq_nonneg (weights j))
      exact ne_of_gt (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg ha0 hb0) hc0)
    dsimp only
    refine ⟨mul_left_cancel₀ htotal ?_, mul_left_cancel₀ htotal ?_, mul_left_cancel₀ htotal ?_⟩
    · linear_combination blockWeight weights B * hpa - blockWeight weights A * hpb
    · linear_combination blockWeight weights C * hpb - blockWeight weights B * hpc
    · linear_combination blockWeight weights A * hpc - blockWeight weights C * hpa
  have hactiveA := one_active_of_block_ratio m A B hAB hB x y z hfixA
    (fun t ht => (hratio (blockWeights A t) (blockWeights_ne_zero A ht)).1)
  have hactiveB := one_active_of_block_ratio m B C hBC hC y z x hfixB
    (fun t ht => (hratio (blockWeights B t) (blockWeights_ne_zero B ht)).2.1)
  have hactiveC := one_active_of_block_ratio m C A hAC.symm hA z x y hfixC
    (fun t ht => (hratio (blockWeights C t) (blockWeights_ne_zero C ht)).2.2)
  refine ⟨hA, hB, hC, ?_, ?_, ?_⟩
  · exact residual_single_active m A B C hAB hAC x y z h hfixA hfixB hfixC hactiveB hactiveC
  · simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
      residual_single_active m B C A hBC hAB.symm y z x
        h.rotate hfixB hfixC hfixA hactiveC hactiveA
  · simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
      residual_single_active m C A B hAC.symm hBC.symm z x y
        h.rotate.rotate hfixC hfixA hfixB hactiveA hactiveB

/-- Three nonzero, two-contact Laurent residuals at a common exact Hamming
radius are impossible as soon as at least two of the centers differ. -/
theorem closed_triple_laurent_false {n : ℕ} (m a b c : Q n)
    (A B C : Finset (Fin n)) (hcenters : a ≠ b ∨ b ≠ c)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (ha : ∀ i, a i ≠ m i ↔ i ∈ A) (hb : ∀ i, b i ≠ m i ↔ i ∈ B)
    (hc : ∀ i, c i ≠ m i ↔ i ∈ C)
    (x y z : Q n → ℝ) (hxn : x ≠ 0) (hyn : y ≠ 0) (hzn : z ≠ 0)
    (hx : outward (fun _ => 1) a x = 0) (hy : outward (fun _ => 1) b y = 0)
    (hz : outward (fun _ => 1) c z = 0) (h : TwoContacts x y z)
    (R : ℕ)
    (hxr : ∀ r, x r ≠ 0 → (differingCoordinates a r).card = R)
    (hyr : ∀ r, y r ≠ 0 → (differingCoordinates b r).card = R)
    (hzr : ∀ r, z r ≠ 0 → (differingCoordinates c r).card = R)
    (u v w : Fin n → ℤ)
    (hxy : ExponentAgreement a b x y u v)
    (hyz : ExponentAgreement b c y z v w)
    (hxz : ExponentAgreement a c x z u w) : False := by
  obtain ⟨hA, hB, hC, hxs, hys, hzs⟩ :=
    closed_triple_laurent_single_active m a b c A B C hcenters hAB hAC hBC ha hb hc
      x y z hxn hyn hzn hx hy hz h R hxr hyr hzr u v w hxy hyz hxz
  exact hxn (closed_triple_single_active_eq_zero m a b c A B C hA hB hC
    hAB hAC hBC ha hb hc x y z hx hy hz h.cancel hxs hys hzs).1

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CenterOutwardTripleMonomial
