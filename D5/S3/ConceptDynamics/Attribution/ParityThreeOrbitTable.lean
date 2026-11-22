/- GID: D5/S3/ConceptDynamics/Attribution/ParityThreeOrbitTable
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityThreeOrbitTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-coordinate parity seed implementations correspond to integer orbit tables. -/

import D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
import D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts
import D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
import D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.EquivFin

/-! Integer orbit tables for three coloured parity coordinates. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable

open Finset MulAction

open CoordinateFlagCoupling
open ParitySeedBudget

def leftWord : Fin 4 → Fin 3 → Bool :=
  ![![false, false, false], ![false, true, true], ![true, false, true], ![true, true, false]]

def rightWord : Fin 4 → Fin 3 → Bool := fun q i => !(leftWord q i)

def leftProfile (p : Fin 4) : ParityClass 3 0 :=
  ⟨bitProfile (leftWord p), (by decide : ∀ p, parity (bitProfile (leftWord p)) = 0) p⟩

private def rightProfile (q : Fin 4) : ParityClass 3 1 :=
  ⟨bitProfile (rightWord q), (by decide : ∀ q, parity (bitProfile (rightWord q)) = 1) q⟩

theorem leftProfile_bijective : Function.Bijective leftProfile := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨?_, ?_⟩
  · intro i j h
    exact (by decide : ∀ i j : Fin 4, bitProfile (leftWord i) = bitProfile (leftWord j) → i = j)
      i j (congrArg Subtype.val h)
  · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, parityCard]; rfl

private theorem rightProfile_bijective : Function.Bijective rightProfile := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨?_, ?_⟩
  · intro i j h
    exact (by decide : ∀ i j : Fin 4, bitProfile (rightWord i) = bitProfile (rightWord j) → i = j)
      i j (congrArg Subtype.val h)
  · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, parityCard]; rfl

private theorem ordinary_shifts (p q : Fin 4) (hq : q ≠ 0) (c d : ZMod 2) :
    ∃ v : Fin 3 → ZMod 2, shift (leftWord p) v = c ∧ shift (rightWord q) v = d := by
  have different : ∀ p q : Fin 4, leftWord p ≠ rightWord q := by decide
  have leftMoves : ∀ p : Fin 4, ∃ i : Fin 3, leftWord p i = false := by decide
  have rightMoves : ∀ q : Fin 4, q ≠ 0 → ∃ i : Fin 3, rightWord q i = false := by decide
  obtain ⟨v, shifts⟩ := CoordinateColourOrbit.shifts_surjective (leftWord p) (rightWord q)
    (different p q) (leftMoves p) (rightMoves q hq) (c, d)
  exact ⟨v, congrArg Prod.fst shifts, congrArg Prod.snd shifts⟩

private theorem special_shifts (p : Fin 4) (c : ZMod 2) :
    ∃ v : Fin 3 → ZMod 2, shift (leftWord p) v = c ∧ shift (rightWord 0) v = 0 :=
  (by decide : ∀ (p : Fin 4) (c : ZMod 2),
    ∃ v : Fin 3 → ZMod 2, shift (leftWord p) v = c ∧ shift (rightWord 0) v = 0) p c

private noncomputable def indexedOutput (word : Fin 4 → Fin 3 → Bool) (par : ZMod 2)
    (classLaw : ∀ p, parity (bitProfile (word p)) = par)
    (injective : Function.Injective (fun p => (bitProfile (word p) : Profile 3))) :
    Fin 4 × ZMod 2 ≃ slice 3 par :=
  Equiv.ofBijective (fun p => ⟨⟨word p.1, p.2⟩, classLaw p.1⟩) <| by
    apply (Fintype.bijective_iff_injective_and_card _).2
    refine ⟨?_, ?_⟩
    · intro a b h
      have eq : (⟨word a.1, a.2⟩ : Output (Fin 3)) = ⟨word b.1, b.2⟩ :=
        congrArg Subtype.val h
      exact Prod.ext (injective (congrArg (fun x => bitProfile x.profile) eq))
        (congrArg Output.colour eq)
    · rw [← Fintype.card_congr (sliceEquiv 3 par), Fintype.card_prod, Fintype.card_prod,
        Fintype.card_fin, ← Nat.card_eq_fintype_card (α := ParityClass 3 par), parityCard]
      rfl

private noncomputable def leftOutput : Fin 4 × ZMod 2 ≃ slice 3 0 :=
  indexedOutput leftWord 0 (fun p => (leftProfile p).property)
    (fun _ _ h => leftProfile_bijective.injective (Subtype.ext h))

private noncomputable def rightOutput : Fin 4 × ZMod 2 ≃ slice 3 1 :=
  indexedOutput rightWord 1 (fun q => (rightProfile q).property)
    (fun _ _ h => rightProfile_bijective.injective (Subtype.ext h))

private noncomputable def point (p q : Fin 4) (c d : ZMod 2) : Pair 1 :=
  (leftOutput (p, c), rightOutput (q, d))

private theorem left_value (p : Fin 4) (c : ZMod 2) :
    (leftOutput (p, c)).val = Output.mk (leftWord p) c := rfl

private theorem right_value (q : Fin 4) (d : ZMod 2) :
    (rightOutput (q, d)).val = Output.mk (rightWord q) d := rfl

private theorem move_point (g : Acting (Fin 3)) (p q : Fin 4) (c d : ZMod 2) :
    g • point p q c d =
      point p q (shift (leftWord p) g.toAdd + c) (shift (rightWord q) g.toAdd + d) := by
  apply Prod.ext <;> apply Subtype.ext
  · change g • (leftOutput (p, c)).val = (leftOutput (p, _)).val
    rw [left_value, left_value]
    rfl
  · change g • (rightOutput (q, d)).val = (rightOutput (q, _)).val
    rw [right_value, right_value]
    rfl

private theorem subgroup_fixed_iff {X : Type*} [MulAction (Acting (Fin 3)) X] (x : X) (i : Fin 3) :
    (∀ h : coordinate i, (h : Acting (Fin 3)) • x = x) ↔ generator i • x = x := by
  rw [show (∀ h : coordinate i, (h : Acting (Fin 3)) • x = x) ↔
      coordinate i ≤ stabilizer (Acting (Fin 3)) x from
    ⟨fun fixes g hg => fixes ⟨g, hg⟩, fun sub h => sub h.property⟩]
  rw [coordinate, Subgroup.zpowers_le, mem_stabilizer_iff]

private theorem point_fixed (p q : Fin 4) (c d : ZMod 2) (i : Fin 3) :
    generator i • point p q c d = point p q c d ↔ leftWord p i = true ∧ rightWord q i = true := by
  rw [← subgroup_fixed_iff]
  let t := point p q c d
  have h :
      (∀ g : coordinate i, (g : Acting (Fin 3)) • t = t) ↔
      ∀ g ∈ coordinate i, g • t.1.val = t.1.val ∧ g • t.2.val = t.2.val := by
    constructor
    · intro fixed g hg
      exact ⟨congrArg (fun x : Pair 1 => x.1.val) (fixed ⟨g, hg⟩),
        congrArg (fun x : Pair 1 => x.2.val) (fixed ⟨g, hg⟩)⟩
    · intro fixed g
      have pair := fixed g g.property
      exact Prod.ext (Subtype.ext pair.1) (Subtype.ext pair.2)
  change (∀ g : coordinate i, (g : Acting (Fin 3)) • t = t) ↔ _
  rw [h, fixed_pair_iff, Bool.and_eq_true]
  rfl

private theorem ordinary_same_orbit (p q : Fin 4) (hq : q ≠ 0) (c d : ZMod 2) :
    Quotient.mk'' (s₁ := orbitRel (Acting (Fin 3)) (Pair 1)) (point p q c d) =
      Quotient.mk'' (point p q 0 0) := by
  apply Quotient.sound
  obtain ⟨v, a, b⟩ := ordinary_shifts p q hq c d
  refine ⟨Multiplicative.ofAdd v, ?_⟩
  change Multiplicative.ofAdd v • point p q 0 0 = point p q c d
  rw [move_point]
  change point p q (shift (leftWord p) v + 0) (shift (rightWord q) v + 0) = _
  rw [a, b, add_zero, add_zero]

private theorem special_same_orbit (p : Fin 4) (c d : ZMod 2) :
    Quotient.mk'' (s₁ := orbitRel (Acting (Fin 3)) (Pair 1)) (point p 0 c d) =
      Quotient.mk'' (point p 0 0 d) := by
  apply Quotient.sound
  obtain ⟨v, a, b⟩ := special_shifts p c
  refine ⟨Multiplicative.ofAdd v, ?_⟩
  change Multiplicative.ofAdd v • point p 0 0 d = point p 0 c d
  rw [move_point]
  change point p 0 (shift (leftWord p) v + 0) (shift (rightWord 0) v + d) = _
  rw [a, b, add_zero, zero_add]

private theorem count_by_point {S T : Type*} [Fintype S] [Fintype T]
    (f : S → T) (P : S → Prop) [DecidablePred P] :
    (∑ s, if P s then (1 : ℕ) else 0) =
      ∑ t, Nat.card {s : S // f s = t ∧ P s} := by
  classical
  calc
    _ = #(univ.filter P) := by rw [← sum_filter, card_eq_sum_ones]
    _ = ∑ t : T, #((univ.filter P).filter fun s => f s = t) := by
      simpa only [mem_univ, filter_true] using
        (sum_card_fiberwise_eq_card_filter (univ.filter P) univ f).symm
    _ = _ := by
      apply sum_congr rfl
      intro t _
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, filter_filter]
      apply congrArg Finset.card
      ext x
      simp [and_comm]

private theorem sum_over_points (f : Pair 1 → ℕ) :
    (∑ t, f t) = ∑ p : Fin 4, ∑ q : Fin 4, ∑ c : ZMod 2, ∑ d : ZMod 2, f (point p q c d) := by
  let e : ((Fin 4 × ZMod 2) × (Fin 4 × ZMod 2)) ≃ Pair 1 := leftOutput.prodCongr rightOutput
  rw [← Equiv.sum_comp e f]
  simp only [Fintype.sum_prod_type]
  change (∑ p : Fin 4, ∑ c : ZMod 2, ∑ q : Fin 4, ∑ d : ZMod 2, f (point p q c d)) = _
  exact sum_congr rfl fun _ _ => sum_comm

open Classical in
private theorem count_source_event {S T : Type*} [Fintype S] [Fintype T]
    (f : S → T) (P : T → Prop) :
    (∑ s, if P (f s) then (1 : ℕ) else 0) =
      ∑ t, if P t then Nat.card {s : S // f s = t} else 0 := by
  rw [count_by_point f (fun s => P (f s))]
  apply sum_congr rfl
  intro t _
  by_cases h : P t
  · rw [ite_eq_left h]
    let e : {s : S // f s = t ∧ P (f s)} ≃ {s : S // f s = t} :=
      { toFun := fun s => ⟨s.val, s.property.1⟩
        invFun := fun s => ⟨s.val, s.property, s.property.symm ▸ h⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Nat.card_congr e
  · rw [ite_eq_right h]
    have : IsEmpty {s : S // f s = t ∧ P (f s)} :=
      ⟨fun s => h (s.property.1 ▸ s.property.2)⟩
    simp

private def atPoint (ordinary : Fin 4 → Fin 3 → ℕ) (special : Fin 4 → ZMod 2 → ℕ)
    (p q : Fin 4) (d : ZMod 2) : ℕ :=
  Fin.cases (special p d) (ordinary p) q

open Classical in
private theorem left_row_total (p : Fin 4) (c : ZMod 2)
    (w : Pair 1 → ℕ) (o : Fin 4 → Fin 3 → ℕ) (s : Fin 4 → ZMod 2 → ℕ)
    (value : ∀ p q c d, w (point p q c d) = atPoint o s p q d) :
    (∑ t : Pair 1, if t.1 = leftOutput (p, c) then w t else 0) =
      (∑ d, s p d) + 2 * ∑ j, o p j := by
  rw [sum_over_points]
  have entry (p' q : Fin 4) (c' d : ZMod 2) :
      (if (point p' q c' d).1 = leftOutput (p, c) then w (point p' q c' d) else 0) =
        if p' = p then (if c' = c then atPoint o s p q d else 0) else 0 := by
    rw [value]
    by_cases h : p' = p <;> by_cases hc : c' = c <;> simp [point, h, hc]
  simp_rw [entry]
  rw [sum_eq_single p]
  · simp only [eq_self, ite_true]
    have removeColour (q : Fin 4) :
        (∑ c' : ZMod 2, ∑ d : ZMod 2, if c' = c then atPoint o s p q d else 0) =
          ∑ d : ZMod 2, atPoint o s p q d := by
      rw [sum_comm]
      exact sum_congr rfl fun d _ => by simp
    simp_rw [removeColour]
    rw [Fin.sum_univ_succ]
    change (∑ d, s p d) + (∑ j : Fin 3, ∑ _ : ZMod 2, o p j) = _
    simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_id, mul_sum]
  · intro p' _ hp
    simp [hp]
  · exact fun h => (h (mem_univ p)).elim

open Classical in
private theorem right_col_total (q : Fin 4) (d : ZMod 2)
    (w : Pair 1 → ℕ) (o : Fin 4 → Fin 3 → ℕ) (s : Fin 4 → ZMod 2 → ℕ)
    (value : ∀ p q c d, w (point p q c d) = atPoint o s p q d) :
    (∑ t : Pair 1, if t.2 = rightOutput (q, d) then w t else 0) =
      2 * ∑ p, atPoint o s p q d := by
  rw [sum_over_points]
  have entry (p q' : Fin 4) (c d' : ZMod 2) :
      (if (point p q' c d').2 = rightOutput (q, d) then w (point p q' c d') else 0) =
        if q' = q then (if d' = d then atPoint o s p q d else 0) else 0 := by
    rw [value]
    by_cases h : q' = q <;> by_cases hd : d' = d <;> simp [point, h, hd]
  simp_rw [entry]
  rw [mul_sum]
  apply sum_congr rfl
  intro p _
  rw [sum_eq_single q]
  · simp only [eq_self, ite_true, sum_ite_eq', sum_ite_eq, mem_univ,
      sum_const, card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_id]
  · intro q' _ hq
    simp [hq]
  · exact fun h => (h (mem_univ q)).elim

private def fixedPointValue
    (ordinary : Fin 4 → Fin 3 → Fin 3 → ℕ) (special : Fin 4 → ZMod 2 → Fin 3 → ℕ)
    (p q : Fin 4) (d : ZMod 2) (i : Fin 3) : ℕ :=
  if leftWord p i && rightWord q i then
    Fin.cases (special p d i) (fun j => ordinary p j i) q
  else 0

open Classical in
private theorem fixed_total_at_coordinate (i : Fin 3)
    (w : Pair 1 → ℕ)
    (o : Fin 4 → Fin 3 → Fin 3 → ℕ) (s : Fin 4 → ZMod 2 → Fin 3 → ℕ)
    (value : ∀ p q c d, w (point p q c d) = fixedPointValue o s p q d i) :
    (∑ t, w t) = 4 * (∑ p : Fin 4, ∑ j : Fin 3,
      if leftWord p i && rightWord j.succ i then o p j i else 0) +
      2 * (∑ p : Fin 4, ∑ d : ZMod 2, if leftWord p i then s p d i else 0) := by
  rw [sum_over_points]
  simp_rw [value]
  have ones : ∀ i : Fin 3, rightWord 0 i = true := by decide
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [add_comm, Fin.sum_univ_succ]
  congr 1
  · simp [fixedPointValue, ones, ZMod.card]
  · rw [mul_sum]
    apply sum_congr rfl
    intro j _
    change (∑ _ : ZMod 2, ∑ _ : ZMod 2,
      if leftWord p i && rightWord j.succ i then o p j i else 0) =
      4 * (if leftWord p i && rightWord j.succ i then o p j i else 0)
    simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_id]
    rw [← Nat.mul_assoc]

structure OrbitTable (k : ℕ) (z : Fin 3 → ℕ) where
  ordinary : Fin 4 → Fin 3 → ℕ
  special : Fin 4 → ZMod 2 → ℕ
  ordinaryFixed : Fin 4 → Fin 3 → Fin 3 → ℕ
  specialFixed : Fin 4 → ZMod 2 → Fin 3 → ℕ
  rows : ∀ p, (∑ d, special p d) + 2 * ∑ j, ordinary p j = 2 * k
  ordinaryCols : ∀ j, ∑ p, ordinary p j = k
  specialCols : ∀ d, ∑ p, special p d = k
  ordinaryBounds : ∀ p j i, ordinaryFixed p j i ≤ ordinary p j
  ordinaryParity : ∀ p j i, ordinaryFixed p j i % 2 = ordinary p j % 2
  specialBounds : ∀ p d i, specialFixed p d i ≤ special p d
  specialParity : ∀ p d i, specialFixed p d i % 2 = special p d % 2
  totals : ∀ i, z i = 4 * (∑ p : Fin 4, ∑ j : Fin 3,
    if leftWord p i && rightWord j.succ i then ordinaryFixed p j i else 0) +
    2 * (∑ p : Fin 4, ∑ d : ZMod 2, if leftWord p i then specialFixed p d i else 0)

open CoordinateFibreCounts
open ParitySeedOptimization
open ParitySeedCountSpectrum (left_colour_marginal)

private theorem orbit_table_of_realization {k : ℕ} {z : Fin 3 → ℕ}
    (realized : RealizableSeedCounts 1 k z) : Nonempty (OrbitTable k z) := by
  classical
  obtain ⟨S, _, _, f, card, equiv, ⟨margin, rows, cols⟩, fixed⟩ := realized
  have marginEq := left_colour_marginal (n := 1) (k := k) f card margin rows
  obtain ⟨m, b, bounds, parity, fibres, fixedFibres⟩ := orbit_fixed_fibre_counts f equiv
  let Q := orbitRel.Quotient (Acting (Fin 3)) (Pair 1)
  let ordinaryOrbit (p : Fin 4) (j : Fin 3) : Q := Quotient.mk'' (point p j.succ 0 0)
  let specialOrbit (p : Fin 4) (d : ZMod 2) : Q := Quotient.mk'' (point p 0 0 d)
  let ordinary (p : Fin 4) (j : Fin 3) := m (ordinaryOrbit p j)
  let special (p : Fin 4) (d : ZMod 2) := m (specialOrbit p d)
  let ordinaryFixed (p : Fin 4) (j i : Fin 3) := b (ordinaryOrbit p j) i
  let specialFixed (p : Fin 4) (d : ZMod 2) (i : Fin 3) := b (specialOrbit p d) i
  have value (p q : Fin 4) (c d : ZMod 2) :
      Nat.card {s : S // f s = point p q c d} = atPoint ordinary special p q d := by
    rw [fibres]
    refine Fin.cases ?_ (fun j => ?_) q
    · change m (Quotient.mk'' (point p 0 c d)) = m (specialOrbit p d)
      rw [special_same_orbit]
    · change m (Quotient.mk'' (point p j.succ c d)) = m (ordinaryOrbit p j)
      rw [ordinary_same_orbit p j.succ (Fin.succ_ne_zero j)]
  have fixedValue (i : Fin 3) (p q : Fin 4) (c d : ZMod 2) :
      Nat.card {s : S // f s = point p q c d ∧ generator i • s = s} =
        fixedPointValue ordinaryFixed specialFixed p q d i := by
    rw [fixedFibres, point_fixed, ← Bool.and_eq_true]
    unfold fixedPointValue
    congr 1
    refine Fin.cases ?_ (fun j => ?_) q
    · change b (Quotient.mk'' (point p 0 c d)) i = b (specialOrbit p d) i
      rw [special_same_orbit]
    · change b (Quotient.mk'' (point p j.succ c d)) i = b (ordinaryOrbit p j) i
      rw [ordinary_same_orbit p j.succ (Fin.succ_ne_zero j)]
  have rowTotal (p : Fin 4) :
      (∑ d, special p d) + 2 * ∑ j, ordinary p j = 2 * k := by
    rw [← left_row_total p 0 (fun t : Pair 1 => Nat.card {s : S // f s = t}) ordinary special value,
      ← marginEq]
    convert (count_source_event f (fun t => t.1 = leftOutput (p, 0))).symm.trans
      (rows (leftOutput (p, 0))) using 2 <;> congr 1
  have colTotal (q : Fin 4) (d : ZMod 2) : (∑ p, atPoint ordinary special p q d) = k := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
    rw [← right_col_total q d (fun t : Pair 1 => Nat.card {s : S // f s = t}) ordinary special value,
      ← marginEq]
    convert (count_source_event f (fun t => t.2 = rightOutput (q, d))).symm.trans
      (cols (rightOutput (q, d))) using 2 <;> congr 1
  refine ⟨⟨ordinary, special, ordinaryFixed, specialFixed, rowTotal,
    fun j => colTotal j.succ 0, colTotal 0,
    fun p j i => bounds (ordinaryOrbit p j) i, fun p j i => parity (ordinaryOrbit p j) i,
    fun p d i => bounds (specialOrbit p d) i, fun p d i => parity (specialOrbit p d) i, ?_⟩⟩
  intro i
  rw [← fixed_total_at_coordinate i (fun t : Pair 1 => Nat.card {s : S // f s = t ∧ generator i • s = s}) ordinaryFixed specialFixed (fixedValue i),
    ← count_by_point f (fun s => generator i • s = s), ← fixed i]
  apply sum_congr rfl
  intro x _
  by_cases h : generator i • x = x
  · simp [h, (subgroup_fixed_iff x i).mpr h]
  · have hn : ¬ (∀ a : coordinate i, (a : Acting (Fin 3)) • x = x) :=
      fun fixed => h ((subgroup_fixed_iff x i).mp fixed)
    rw [ite_eq_right hn, ite_eq_right h]

private noncomputable def pointEquiv : ((Fin 4 × ZMod 2) × (Fin 4 × ZMod 2)) ≃ Pair 1 :=
  leftOutput.prodCongr rightOutput

private theorem pointEquiv_apply (p q : Fin 4) (c d : ZMod 2) :
    pointEquiv ((p, c), (q, d)) = point p q c d := rfl

private theorem pointEquiv_inverse (p q : Fin 4) (c d : ZMod 2) :
    pointEquiv.symm (point p q c d) = ((p, c), (q, d)) := by
  rw [← pointEquiv_apply, Equiv.symm_apply_apply]

private noncomputable def orbitWeight (ordinary : Fin 4 → Fin 3 → ℕ)
    (special : Fin 4 → ZMod 2 → ℕ) : orbitRel.Quotient (Acting (Fin 3)) (Pair 1) → ℕ := by
  let e := pointEquiv
  let pointWeight (t : Pair 1) := atPoint ordinary special (e.symm t).1.1 (e.symm t).2.1 (e.symm t).2.2
  have eval (p q : Fin 4) (c d : ZMod 2) : pointWeight (point p q c d) = atPoint ordinary special p q d := by
    simp only [pointWeight, e, pointEquiv_inverse]
  refine Quotient.lift pointWeight ?_
  intro a t h
  obtain ⟨g, hg⟩ := h
  change g • t = a at hg
  rw [← hg]
  obtain ⟨⟨⟨p, c⟩,⟨q, d⟩⟩, eq⟩ := e.surjective t
  change point p q c d = t at eq
  rw [← eq, move_point, eval, eval]
  refine Fin.cases ?_ (fun j => ?_) q
  · rw [CoordinateColourOrbit.all_true_shift (rightWord 0) (by decide), zero_add]
  · rfl

private theorem orbitWeight_mk (ordinary : Fin 4 → Fin 3 → ℕ) (special : Fin 4 → ZMod 2 → ℕ)
    (p q : Fin 4) (c d : ZMod 2) :
    orbitWeight ordinary special (Quotient.mk'' (point p q c d)) = atPoint ordinary special p q d := by
  unfold orbitWeight
  rw [Quotient.lift_mk]
  rw [pointEquiv_inverse]

private theorem sums_ite_same {X : Type*} {A : Finset X}
    (P : X → Prop) (a b : X → ℕ) (d e : DecidablePred P) :
    (∑ x ∈ A, @ite ℕ (P x) (d x) (a x) (b x)) =
      ∑ x ∈ A, @ite ℕ (P x) (e x) (a x) (b x) := by
  apply sum_congr rfl
  intro x _
  rw [Subsingleton.elim (d x) (e x)]

-- Reindexing both coloured marginal sums and the fixed-seed sum needs extra elaboration.
set_option maxHeartbeats 800000 in
private theorem make_realization_of_orbit_table {k : ℕ} {z : Fin 3 → ℕ}
    (table : OrbitTable k z) : RealizableSeedCounts 1 k z := by
  classical
  let Q := orbitRel.Quotient (Acting (Fin 3)) (Pair 1)
  let e : ((Fin 4 × ZMod 2) × (Fin 4 × ZMod 2)) ≃ Pair 1 := leftOutput.prodCongr rightOutput
  let m : Q → ℕ := orbitWeight table.ordinary table.special
  let b (o : Q) (i : Fin 3) :=
    orbitWeight (fun p j => table.ordinaryFixed p j i) (fun p d => table.specialFixed p d i) o
  have conditions (t : Pair 1) (i : Fin 3) :
      b (Quotient.mk'' t) i ≤ m (Quotient.mk'' t) ∧
        b (Quotient.mk'' t) i % 2 = m (Quotient.mk'' t) % 2 := by
    obtain ⟨⟨⟨p, c⟩,⟨q, d⟩⟩, eq⟩ := e.surjective t
    change point p q c d = t at eq
    subst t
    simp only [b, m, orbitWeight_mk]
    refine Fin.cases ?_ (fun j => ?_) q
    · exact ⟨table.specialBounds p d i, table.specialParity p d i⟩
    · exact ⟨table.ordinaryBounds p j i, table.ordinaryParity p j i⟩
  obtain ⟨S, _, _, f, equiv, fibre, fixedFibre⟩ :=
    (exact_orbit_fibre_counts m b).mpr (fun t i _ => conditions t i)
  have pointTotal (p q : Fin 4) (c d : ZMod 2) :
      Nat.card {s : S // f s = point p q c d} = atPoint table.ordinary table.special p q d := by
    rw [fibre]
    exact orbitWeight_mk _ _ p q c d
  have row (x : slice 3 0) : (∑ s, if (f s).1 = x then (1 : ℕ) else 0) = 2 * k := by
    obtain ⟨⟨p, c⟩, rfl⟩ := leftOutput.surjective x
    exact (sums_ite_same (fun seed => (f seed).1 = leftOutput (p, c))
      (fun _ => 1) (fun _ => 0) _ _).trans
      ((count_source_event f (fun t => t.1 = leftOutput (p, c))).trans
        ((sums_ite_same (fun t : Pair 1 => t.1 = leftOutput (p, c))
          (fun t => Nat.card {s : S // f s = t}) (fun _ => 0) _ _).trans
          ((left_row_total p c (fun t : Pair 1 => Nat.card {s : S // f s = t}) _ _ pointTotal).trans
            (table.rows p))))
  have col (y : slice 3 1) : (∑ s, if (f s).2 = y then (1 : ℕ) else 0) = 2 * k := by
    obtain ⟨⟨q, d⟩, rfl⟩ := rightOutput.surjective y
    have mass (q : Fin 4) : (∑ p, atPoint table.ordinary table.special p q d) = k := by
      refine Fin.cases ?_ (fun j => ?_) q
      · exact table.specialCols d
      · exact table.ordinaryCols j
    exact (sums_ite_same (fun seed => (f seed).2 = rightOutput (q, d))
      (fun _ => 1) (fun _ => 0) _ _).trans
      ((count_source_event f (fun t => t.2 = rightOutput (q, d))).trans
        ((sums_ite_same (fun t : Pair 1 => t.2 = rightOutput (q, d))
          (fun t => Nat.card {s : S // f s = t}) (fun _ => 0) _ _).trans
          ((right_col_total q d (fun t : Pair 1 => Nat.card {s : S // f s = t}) _ _ pointTotal).trans
            (congrArg (2 * ·) (mass q)))))
  have card : Fintype.card S = 2 ^ (1 + 3) * k := by
    calc
      Fintype.card S = ∑ x : slice 3 0, ∑ s, if (f s).1 = x then (1 : ℕ) else 0 := by
        rw [sum_comm]
        simp
      _ = _ := by
        simp only [row, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id]
        rw [← Fintype.card_congr leftOutput, Fintype.card_prod, Fintype.card_fin, ZMod.card]
        omega
  have pointFixed (i : Fin 3) (p q : Fin 4) (c d : ZMod 2) :
      Nat.card {s : S // f s = point p q c d ∧ generator i • s = s} =
        fixedPointValue table.ordinaryFixed table.specialFixed p q d i := by
    rw [fixedFibre, point_fixed, ← Bool.and_eq_true]
    simp [b, orbitWeight_mk, fixedPointValue, atPoint]
  refine ⟨S, inferInstance, inferInstance, f, card, equiv, ⟨2 * k, ?_, ?_⟩, ?_⟩
  · intro x
    refine Eq.trans ?_ (row x)
    apply sum_congr rfl
    intro seed _
    by_cases hs : (f seed).1 = x <;> simp [hs]
  · intro y
    refine Eq.trans ?_ (col y)
    apply sum_congr rfl
    intro seed _
    by_cases hs : (f seed).2 = y <;> simp [hs]
  intro i
  rw [table.totals i, ← fixed_total_at_coordinate i (fun t : Pair 1 => Nat.card {s : S // f s = t ∧ generator i • s = s}) _ _ (pointFixed i),
    ← count_by_point f (fun s => generator i • s = s)]
  apply sum_congr rfl
  intro s _
  by_cases h : generator i • s = s
  · simp [h, (subgroup_fixed_iff s i).mpr h]
  · have hn : ¬ (∀ a : coordinate i, (a : Acting (Fin 3)) • s = s) :=
      fun fixed => h ((subgroup_fixed_iff s i).mp fixed)
    rw [ite_eq_right hn, ite_eq_right h]

/-- The integer orbit table conditions characterize precisely the seed implementations. -/
theorem exact_orbit_table (k : ℕ) (z : Fin 3 → ℕ) :
    RealizableSeedCounts 1 k z ↔ Nonempty (OrbitTable k z) :=
  ⟨orbit_table_of_realization, fun ⟨table⟩ => make_realization_of_orbit_table table⟩

end D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable

end
