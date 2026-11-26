/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity, mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Huang square curvature extends empty-row exponent gains to all cube neighbor rows. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactTransport

/-!
# Extending the contact potential on the Huang cube

Opposite paths through a coordinate square have opposite Huang products.
The row sign equations therefore assign one occupied row and one empty row to
each distance-two column pair. The empty-row gain gives the occupied-row
exponent equality with the two coordinates exchanged.

This is a geometric step for Hong–Wu–Xia, arXiv:2610.09483v1, §7, Problem 2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCubeLift

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip_adj)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCubeGirth (adjacent_exists_flip flip_comm)
open BalancedCubeComponentBoundary (flip_injective)
open PrimeContactTransport (Exponent axis)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private edge edge_sq edge_reciprocal edge_curvature from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

variable {n : ℕ} {K : Set (Q n)} {occupied : Q n → Bool}
variable {τ σ : Q n → ℝ} {v : Q n → Exponent n}

/-- Unit column signs and the actual Huang row equations on every pair of contacts. -/
structure RowSigns (K : Set (Q n)) (occupied : Q n → Bool) (τ σ : Q n → ℝ) : Prop where
  switching_unit : ∀ q ∈ K, τ q ^ 2 = 1
  kernel_unit : ∀ q ∈ K, σ q ^ 2 = 1
  occupied_eq : ∀ ⦃q p : Q n⦄ ⦃i j : Fin n⦄, q ∈ K → p ∈ K → q ≠ p →
    flip q i = flip p j → occupied (flip q i) = true →
    huangMatrix n (flip q i) q * τ q = huangMatrix n (flip q i) p * τ p
  empty_eq : ∀ ⦃q p : Q n⦄ ⦃i j : Fin n⦄, q ∈ K → p ∈ K → q ≠ p →
    flip q i = flip p j → occupied (flip q i) = false →
    huangMatrix n (flip q i) q * σ q = -(huangMatrix n (flip q i) p * σ p)

/-- The upper exponent agrees at every empty row with distinct contacts. -/
def EmptyGain (K : Set (Q n)) (occupied : Q n → Bool) (v : Q n → Exponent n) : Prop :=
  ∀ ⦃q p : Q n⦄ ⦃i j : Fin n⦄, q ∈ K → p ∈ K → q ≠ p →
    flip q i = flip p j → occupied (flip q i) = false →
    v q + axis i = v p + axis j

/-- Two distinct columns are joined when they share an empty row. -/
def EmptyAdj (K : Set (Q n)) (occupied : Q n → Bool) (q p : Q n) : Prop :=
  q ∈ K ∧ p ∈ K ∧ q ≠ p ∧
    ∃ i j : Fin n, flip q i = flip p j ∧ occupied (flip q i) = false

private theorem square_of_shared_row {q p : Q n} {i j : Fin n} (hqp : q ≠ p)
    (hr : flip q i = flip p j) :
    i ≠ j ∧ flip (flip q i) j = p ∧ flip q j = flip p i := by
  have hp : flip (flip q i) j = p := by rw [hr, BalancedCriticalSpectrum.flip_flip]
  have hij : i ≠ j := by
    intro he
    subst j
    exact hqp (by simpa only [BalancedCriticalSpectrum.flip_flip] using hp)
  have hp' : flip (flip q j) i = p := (flip_comm q j i).trans hp
  exact ⟨hij, hp, by rw [← hp', BalancedCriticalSpectrum.flip_flip]⟩

private theorem double_flip_apply (q : Q n) {i j : Fin n} (hij : i ≠ j) (k : Fin n) :
    flip (flip q i) j k = if k = i ∨ k = j then !q k else q k := by
  by_cases hki : k = i
  · subst k
    simp [BalancedCriticalSpectrum.flip, hij]
  · by_cases hkj : k = j
    · subst k
      simp [BalancedCriticalSpectrum.flip, hki]
    · simp [BalancedCriticalSpectrum.flip, hki, hkj]

private theorem product_of_signed_eq {a b s t : ℝ} (hs : s ^ 2 = 1) (hb : b ^ 2 = 1)
    (he : a * s = b * t) : a * b = s * t := by
  calc
    a * b = (a * s) * (b * s) := by
      calc
        a * b = a * b * s ^ 2 := by rw [hs, mul_one]
        _ = _ := by ring
    _ = (b * t) * (b * s) := by rw [he]
    _ = s * t * b ^ 2 := by ring
    _ = s * t := by rw [hb, mul_one]

private theorem row_product (h : RowSigns K occupied τ σ) {q p : Q n} {i j : Fin n}
    (hq : q ∈ K) (hp : p ∈ K) (hqp : q ≠ p) (hr : flip q i = flip p j) :
    huangMatrix n (flip q i) q * huangMatrix n (flip q i) p =
      if occupied (flip q i) = true then τ q * τ p else -(σ q * σ p) := by
  have hb : huangMatrix n (flip q i) p ^ 2 = 1 := by
    rw [hr]
    simpa only [edge, BalancedCriticalSpectrum.flip_flip] using edge_sq (flip p j) j
  cases ho : occupied (flip q i) with
  | false =>
    have he : huangMatrix n (flip q i) q * σ q = huangMatrix n (flip q i) p * (-σ p) := by
      rw [mul_neg]
      exact h.empty_eq hq hp hqp hr ho
    simpa [ho, mul_neg] using product_of_signed_eq (h.kernel_unit q hq) hb he
  | true =>
    simpa [ho] using product_of_signed_eq (h.switching_unit q hq) hb
      (h.occupied_eq hq hp hqp hr ho)

private theorem signed_square (h : RowSigns K occupied τ σ) {q p : Q n} {i j : Fin n}
    (hq : q ∈ K) (hp : p ∈ K) (hqp : q ≠ p) (hr : flip q i = flip p j) :
    (if occupied (flip q i) = true then τ q * τ p else -(σ q * σ p)) =
      -(if occupied (flip q j) = true then τ q * τ p else -(σ q * σ p)) := by
  obtain ⟨hij, hpi, hr'⟩ := square_of_shared_row hqp hr
  have hpj : flip (flip q j) i = p := (flip_comm q j i).trans hpi
  have hiq : huangMatrix n (flip q i) q = edge q i := by
    simpa only [edge, BalancedCriticalSpectrum.flip_flip] using edge_reciprocal q i
  have hjq : huangMatrix n (flip q j) q = edge q j := by
    simpa only [edge, BalancedCriticalSpectrum.flip_flip] using edge_reciprocal q j
  have hip : edge (flip q i) j = huangMatrix n (flip q i) p := by
    simp only [edge, hpi]
  have hjp : edge (flip q j) i = huangMatrix n (flip q j) p := by
    simp only [edge, hpj]
  rw [← row_product h hq hp hqp hr, ← row_product h hq hp hqp hr', hiq, hjq, ← hip, ← hjp]
  exact edge_curvature q hij

private theorem unit_ne_zero {s : ℝ} (hs : s ^ 2 = 1) : s ≠ 0 := by
  intro hz
  simp [hz] at hs

/-- The two common rows of a distinct column pair have opposite classifications.
The contacts at the second row exchange the two coordinate directions. -/
theorem occupied_ne_at_common_rows (h : RowSigns K occupied τ σ)
    {q p : Q n} {i j : Fin n} (hq : q ∈ K) (hp : p ∈ K)
    (hqp : q ≠ p) (hr : flip q i = flip p j) :
    occupied (flip q i) ≠ occupied (flip q j) := by
  have hs := signed_square h hq hp hqp hr
  intro he
  rw [← he] at hs
  cases ho : occupied (flip q i) with
  | false =>
    have hz : σ q * σ p = 0 := by
      simp only [ho, Bool.false_eq_true, ↓reduceIte] at hs
      linarith only [hs]
    exact (mul_ne_zero (unit_ne_zero (h.kernel_unit q hq))
      (unit_ne_zero (h.kernel_unit p hp))) hz
  | true =>
    have hz : τ q * τ p = 0 := by
      simp only [ho, ↓reduceIte] at hs
      linarith only [hs]
    exact (mul_ne_zero (unit_ne_zero (h.switching_unit q hq))
      (unit_ne_zero (h.switching_unit p hp))) hz

/-- A distance-two column pair has exactly two common neighbors, one occupied and one empty. -/
theorem common_rows_of_hammingDist_two (h : RowSigns K occupied τ σ)
    {q p : Q n} (hq : q ∈ K) (hp : p ∈ K) (hd : hammingDist q p = 2) :
    ∃ r s : Q n, occupied r = true ∧ occupied s = false ∧
      ∀ x : Q n, ((hypercube n).Adj q x ∧ (hypercube n).Adj p x) ↔ x = r ∨ x = s := by
  have hqp : q ≠ p := by
    intro he
    subst p
    simp at hd
  change (Finset.univ.filter (fun k => q k ≠ p k)).card = 2 at hd
  obtain ⟨i, j, hij, hset⟩ := Finset.card_eq_two.mp hd
  have hdiff (k : Fin n) : q k ≠ p k ↔ k = i ∨ k = j := by
    have hk := Finset.ext_iff.mp hset k
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] using hk
  have hpi : flip (flip q i) j = p := by
    funext k
    rw [double_flip_apply q hij k]
    by_cases hk : k = i ∨ k = j
    · rw [if_pos hk]
      exact Bool.not_eq_iff.mpr ((hdiff k).2 hk)
    · rw [if_neg hk]
      by_contra hn
      exact hk ((hdiff k).1 hn)
  have hrow : flip q i = flip p j := by rw [← hpi, BalancedCriticalSpectrum.flip_flip]
  have hrow' := (square_of_shared_row hqp hrow).2.2
  have hrows (x : Q n) :
      ((hypercube n).Adj q x ∧ (hypercube n).Adj p x) ↔ x = flip q i ∨ x = flip q j := by
    constructor
    · rintro ⟨hqx, hpx⟩
      obtain ⟨a, ha⟩ := adjacent_exists_flip hqx
      obtain ⟨b, hb⟩ := adjacent_exists_flip hpx
      obtain ⟨hab, hpab, _⟩ := square_of_shared_row hqp (ha.symm.trans hb)
      have hda : q a ≠ p a := by
        rw [← hpab, double_flip_apply q hab a, if_pos (Or.inl rfl)]
        exact Bool.self_ne_not (q a)
      rcases (hdiff a).1 hda with hai | haj
      · exact Or.inl (ha.trans (congrArg (flip q) hai))
      · exact Or.inr (ha.trans (congrArg (flip q) haj))
    · rintro (rfl | rfl)
      · exact ⟨flip_adj q i, hrow.symm ▸ flip_adj p j⟩
      · exact ⟨flip_adj q j, hrow'.symm ▸ flip_adj p i⟩
  have hclass := occupied_ne_at_common_rows h hq hp hqp hrow
  cases hi : occupied (flip q i) with
  | false =>
    have hj : occupied (flip q j) = true :=
      Bool.eq_true_of_not_eq_false (fun hj => hclass (hi.trans hj.symm))
    exact ⟨flip q j, flip q i, hj, hi, fun x => (hrows x).trans or_comm⟩
  | true =>
    have hj : occupied (flip q j) = false :=
      Bool.eq_false_of_not_eq_true (fun hj => hclass (hi.trans hj.symm))
    exact ⟨flip q i, flip q j, hi, hj, hrows⟩

/-- At an occupied row, the lower exponent agrees at any two distinct contacts. -/
theorem lower_exponent_eq (h : RowSigns K occupied τ σ) (hv : EmptyGain K occupied v)
    {q p : Q n} {i j : Fin n} (hq : q ∈ K) (hp : p ∈ K)
    (hqp : q ≠ p) (hr : flip q i = flip p j) (ho : occupied (flip q i) = true) :
    v q - axis i = v p - axis j := by
  have hr' := (square_of_shared_row hqp hr).2.2
  have hclass := occupied_ne_at_common_rows h hq hp hqp hr
  have he : occupied (flip q j) = false :=
    Bool.eq_false_of_not_eq_true (fun hj => hclass (ho.trans hj.symm))
  have hu := hv hq hp hqp hr' he
  funext k
  have hk := congrFun hu k
  change v q k + axis j k = v p k + axis i k at hk
  change v q k - axis i k = v p k - axis j k
  omega

/-- Every row contacting the column set admits an exponent consistent with every
contact, including rows with a single contact. -/
theorem exists_row_exponent (h : RowSigns K occupied τ σ) (hv : EmptyGain K occupied v) :
    ∃ e : Q n → Exponent n, ∀ q ∈ K, ∀ i : Fin n,
      e (flip q i) = if occupied (flip q i) = true then v q - axis i else v q + axis i := by
  classical
  let value (q : Q n) (i : Fin n) : Exponent n :=
    if occupied (flip q i) = true then v q - axis i else v q + axis i
  have agree {q p : Q n} {i j : Fin n} (hq : q ∈ K) (hp : p ∈ K)
      (hr : flip q i = flip p j) : value q i = value p j := by
    by_cases hqp : q = p
    · subst p
      rw [flip_injective q hr]
    · simp only [value, ← hr]
      cases ho : occupied (flip q i) with
      | false => simpa [ho] using hv hq hp hqp hr ho
      | true => simpa [ho] using lower_exponent_eq h hv hq hp hqp hr ho
  let e (r : Q n) : Exponent n :=
    if hcontact : ∃ qi : Q n × Fin n, qi.1 ∈ K ∧ flip qi.1 qi.2 = r then
      value (Classical.choose hcontact).1 (Classical.choose hcontact).2
    else 0
  refine ⟨e, ?_⟩
  intro q hq i
  have hcontact : ∃ qi : Q n × Fin n, qi.1 ∈ K ∧ flip qi.1 qi.2 = flip q i :=
    ⟨(q, i), hq, rfl⟩
  change e (flip q i) = value q i
  dsimp only [e]
  rw [dif_pos hcontact]
  exact agree (Classical.choose_spec hcontact).1 hq (Classical.choose_spec hcontact).2

/-- The products of the switching and kernel signs agree across an empty row. -/
theorem sign_product_eq (h : RowSigns K occupied τ σ)
    {q p : Q n} (hadj : EmptyAdj K occupied q p) : τ q * σ q = τ p * σ p := by
  obtain ⟨hq, hp, hqp, i, j, hr, he⟩ := hadj
  have hclass := occupied_ne_at_common_rows h hq hp hqp hr
  have ho : occupied (flip q j) = true :=
    Bool.eq_true_of_not_eq_false (fun hj => hclass (he.trans hj.symm))
  have hs : σ q * σ p = τ q * τ p := by
    have hsquare := signed_square h hq hp hqp hr
    simp only [he, ho, Bool.false_eq_true, ↓reduceIte] at hsquare
    linarith only [hsquare]
  calc
    τ q * σ q = (τ q * σ q) * σ p ^ 2 := by rw [h.kernel_unit p hp, mul_one]
    _ = (τ q * σ p) * (σ q * σ p) := by ring
    _ = (τ q * σ p) * (τ q * τ p) := by rw [hs]
    _ = (τ p * σ p) * τ q ^ 2 := by ring
    _ = τ p * σ p := by rw [h.switching_unit q hq, mul_one]

/-- The product sign is constant on each component of the empty-row contact graph. -/
theorem sign_product_eq_of_reachable (h : RowSigns K occupied τ σ)
    {q p : Q n} (hpath : Relation.ReflTransGen (EmptyAdj K occupied) q p) :
    τ q * σ q = τ p * σ p := by
  induction hpath with
  | refl => rfl
  | tail _ hadj ih => exact ih.trans (sign_product_eq h hadj)

private def bit (b : Bool) : ℤ := if b = true then 1 else 0

private theorem bit_xor_mod (b c : Bool) :
    bit (Bool.xor b c) = (bit b + bit c) % 2 := by
  cases b <;> cases c <;> decide

private theorem sum_axis (i : Fin n) : (∑ k, axis i k) = 1 := by
  simpa only [axis] using (Fintype.sum_ite_eq' i (fun _ : Fin n => (1 : ℤ)))

private theorem empty_gain_invariants (hv : EmptyGain K occupied v)
    {q p : Q n} (hadj : EmptyAdj K occupied q p) :
    (∑ k, v q k) = (∑ k, v p k) ∧
      ∀ k, (v q k + bit (q k)) % 2 = (v p k + bit (p k)) % 2 := by
  obtain ⟨hq, hp, hqp, i, j, hr, he⟩ := hadj
  have hgain := hv hq hp hqp hr he
  obtain ⟨hij, hpi, _⟩ := square_of_shared_row hqp hr
  constructor
  · have hsum := congrArg (fun a : Exponent n => ∑ k, a k) hgain
    change (∑ k, (v q k + axis i k)) = (∑ k, (v p k + axis j k)) at hsum
    simp only [Finset.sum_add_distrib, sum_axis] at hsum
    omega
  · intro k
    have hg := congrFun hgain k
    change v q k + axis i k = v p k + axis j k at hg
    have hb : p k = if k = i ∨ k = j then !q k else q k :=
      (congrFun hpi.symm k).trans (double_flip_apply q hij k)
    by_cases hk : k = i ∨ k = j
    · rw [hb, if_pos hk]
      rcases hk with hki | hkj
      · have hkj : k ≠ j := fun heq => hij (hki.symm.trans heq)
        simp only [axis, if_pos hki, if_neg hkj] at hg
        cases hqk : q k <;> simp [bit, hqk] <;> omega
      · have hki : k ≠ i := fun heq => hij (heq.symm.trans hkj)
        simp only [axis, if_neg hki, if_pos hkj] at hg
        cases hqk : q k <;> simp [bit, hqk] <;> omega
    · have hki : k ≠ i := fun heq => hk (Or.inl heq)
      have hkj : k ≠ j := fun heq => hk (Or.inr heq)
      simp only [axis, if_neg hki, if_neg hkj, add_zero] at hg
      rw [hb, if_neg hk, hg]

/-- On a rooted empty-row component, the integer grade is constant and the
coordinate exponent mod two is the cube bit XOR a shift determined by the root. -/
theorem grade_and_parity_of_connected (hv : EmptyGain K occupied v) (root : Q n)
    (hreach : ∀ q ∈ K, Relation.ReflTransGen (EmptyAdj K occupied) root q) :
    ∃ shift : Fin n → Bool, ∀ q ∈ K,
      (∑ k, v q k) = (∑ k, v root k) ∧
      ∀ k, v q k % 2 = if Bool.xor (q k) (shift k) = true then 1 else 0 := by
  have along {p : Q n} (hpath : Relation.ReflTransGen (EmptyAdj K occupied) root p) :
      (∑ k, v root k) = (∑ k, v p k) ∧
        ∀ k, (v root k + bit (root k)) % 2 = (v p k + bit (p k)) % 2 := by
    induction hpath with
    | refl => exact ⟨rfl, fun _ => rfl⟩
    | tail _ hadj ih =>
      obtain ⟨hgrade, hparity⟩ := empty_gain_invariants hv hadj
      exact ⟨ih.1.trans hgrade, fun k => (ih.2 k).trans (hparity k)⟩
  let shift (k : Fin n) : Bool := decide ((v root k + bit (root k)) % 2 = 1)
  have hshift (k : Fin n) :
      bit (shift k) = (v root k + bit (root k)) % 2 := by
    by_cases h : (v root k + bit (root k)) % 2 = 1
    · have hs : shift k = true := by simp only [shift, decide_eq_true_eq, h]
      rw [hs, h]
      rfl
    · have hz : (v root k + bit (root k)) % 2 = 0 := by omega
      have hs : shift k = false := by simp only [shift, decide_eq_false_iff_not, h, not_false_eq_true]
      rw [hs, hz]
      rfl
  refine ⟨shift, fun q hq => ?_⟩
  obtain ⟨hgrade, hparity⟩ := along (hreach q hq)
  refine ⟨hgrade.symm, fun k => ?_⟩
  change v q k % 2 = bit (Bool.xor (q k) (shift k))
  rw [bit_xor_mod, hshift k, hparity k]
  cases hqk : q k <;> simp [bit, hqk] <;> omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCubeLift
