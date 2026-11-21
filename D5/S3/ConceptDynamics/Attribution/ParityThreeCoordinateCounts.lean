/- GID: D5/S3/ConceptDynamics/Attribution/ParityThreeCoordinateCounts
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityThreeCoordinateCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp integer constraints on three simultaneous coordinate fixed counts. -/

import D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
import D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts
import D5.S3.ConceptDynamics.Attribution.ParityMinimumSeedSpectrum
import D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
import D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Sign

/-! Integer orbit tables and their sharp three-coordinate fixed-count bounds. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Attribution.ParityThreeCoordinateCounts

open Finset MulAction

open CoordinateFlagCoupling
open ParitySeedBudget

private def leftWord : Fin 4 → Fin 3 → Bool :=
  ![![false, false, false], ![false, true, true], ![true, false, true], ![true, true, false]]

private def rightWord : Fin 4 → Fin 3 → Bool := fun q i => !(leftWord q i)

private def leftProfile (p : Fin 4) : ParityClass 3 0 :=
  ⟨bitProfile (leftWord p), (by decide : ∀ p, parity (bitProfile (leftWord p)) = 0) p⟩

private def rightProfile (q : Fin 4) : ParityClass 3 1 :=
  ⟨bitProfile (rightWord q), (by decide : ∀ q, parity (bitProfile (rightWord q)) = 1) q⟩

private theorem leftProfile_bijective : Function.Bijective leftProfile := by
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

private theorem special_shift_zero (v : Fin 3 → ZMod 2) : shift (rightWord 0) v = 0 :=
  (by decide : ∀ v : Fin 3 → ZMod 2, shift (rightWord 0) v = 0) v

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
    haveI : IsEmpty {s : S // f s = t ∧ P (f s)} :=
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

private structure OrbitTable (k : ℕ) (z : Fin 3 → ℕ) where
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
  · rw [special_shift_zero, zero_add]
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

private theorem odd_sum_forces_fixed {k a b f g : ℕ}
    (hSum : a + b = k) (odd : k % 2 = 1)
    (hF : f % 2 = a % 2) (hG : g % 2 = b % 2) :
    1 ≤ f + g := by
  by_cases hf : f = 0
  · by_cases hg : g = 0
    · have aa : a % 2 = 0 := hF.symm.trans (by simp [hf])
      have bb : b % 2 = 0 := hG.symm.trans (by simp [hg])
      have evenK : k % 2 = 0 := by rw [← hSum, Nat.add_mod, aa, bb]
      exact (Nat.zero_ne_one (evenK.symm.trans odd)).elim
    · omega
  · omega

private theorem odd_from_other_even {k a b c d : ℕ}
    (sum : a + b + c + d = k) (odd : k % 2 = 1)
    (evenB : b % 2 = 0) (evenC : c % 2 = 0) (evenD : d % 2 = 0) :
    1 ≤ a := by
  by_cases ha : a = 0
  · have evenK : k % 2 = 0 := by
      rw [← sum, Nat.add_mod _ d, Nat.add_mod _ c, Nat.add_mod _ b, ha, evenB, evenC, evenD]
    exact (Nat.zero_ne_one (evenK.symm.trans odd)).elim
  · exact Nat.pos_of_ne_zero ha

private theorem odd_coordinate_cut (k u v w : ℕ)
    (A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ x₀ x₁ y z C D F₂ F₃ G₂ G₃ : ℕ)
    (odd : k % 2 = 1)
    (colA : A₀ + A₁ + A₂ + A₃ = k) (colB : B₀ + B₁ + B₂ + B₃ = k)
    (row : A₁ + B₁ + 2 * x₁ + 2 * (y + z) = 2 * k)
    (iCap : 2 * u + A₀ + B₀ + A₁ + B₁ + 2 * x₀ + 2 * x₁ ≤ 4 * k)
    (otherCap : 2 * C + 2 * D + F₂ + F₃ + G₂ + G₃ ≤ 2 * (v + w))
    (extra : A₁ % 2 ≤ 2 * (v + w) ∧ B₁ % 2 ≤ 2 * (v + w))
    (parityC : C % 2 = y % 2) (parityD : D % 2 = z % 2)
    (parityF₂ : F₂ % 2 = A₂ % 2) (parityF₃ : F₃ % 2 = A₃ % 2)
    (parityG₂ : G₂ % 2 = B₂ % 2) (parityG₃ : G₃ % 2 = B₃ % 2) :
    u ≤ v + w + 2 * (k - 1) := by
  by_contra notLe
  have bad := Nat.lt_of_not_ge notLe
  have posK : 0 < k := Nat.pos_of_ne_zero (fun h => by simp [h] at odd)
  by_cases max : u = 2 * k
  · have noCross : A₀ = 0 ∧ B₀ = 0 ∧ A₁ = 0 ∧ B₁ = 0 ∧ x₁ = 0 := by
      clear * - max iCap
      omega
    obtain ⟨a₀, b₀, a₁, b₁, hx⟩ := noCross
    have yz : y + z = k := by
      simpa [a₁, b₁, hx, Nat.mul_right_inj (by decide : 2 ≠ 0)] using row
    have ac : A₂ + A₃ = k := by simpa [a₀, a₁] using colA
    have bc : B₂ + B₃ = k := by simpa [b₀, b₁] using colB
    have hC := odd_sum_forces_fixed yz odd parityC parityD
    have hF := odd_sum_forces_fixed ac odd parityF₂ parityF₃
    have hG := odd_sum_forces_fixed bc odd parityG₂ parityG₃
    clear * - otherCap hC hF hG posK max bad
    omega
  · have ⟨near, hv, hw⟩ : u = 2 * k - 1 ∧ v = 0 ∧ w = 0 := by
      clear * - bad max iCap posK
      omega
    have ⟨hc, hd, hf₂, hf₃, hg₂, hg₃⟩ :
        C = 0 ∧ D = 0 ∧ F₂ = 0 ∧ F₃ = 0 ∧ G₂ = 0 ∧ G₃ = 0 := by
      clear * - otherCap hv hw
      omega
    have ⟨evenA, evenB⟩ : A₁ % 2 = 0 ∧ B₁ % 2 = 0 := by simpa [hv, hw] using extra
    have hA := odd_from_other_even colA odd evenA (by simpa [hf₂] using parityF₂.symm)
      (by simpa [hf₃] using parityF₃.symm)
    have hB := odd_from_other_even colB odd evenB (by simpa [hg₂] using parityG₂.symm)
      (by simpa [hg₃] using parityG₃.symm)
    have evenY : y % 2 = 0 := by simpa [hc] using parityC.symm
    have evenZ : z % 2 = 0 := by simpa [hd] using parityD.symm
    have notFull : y + z ≠ k := by
      intro sum
      have evenK : k % 2 = 0 := by rw [← sum, Nat.add_mod, evenY, evenZ]
      exact Nat.zero_ne_one (evenK.symm.trans odd)
    have hRow : 2 ≤ A₁ + B₁ + 2 * x₁ := by
      clear * - row notFull
      omega
    clear * - near iCap posK hA hB hRow
    omega

private theorem colour_sum_two (f : ZMod 2 → ℕ) : (∑ d, f d) = f 0 + f 1 := by
  have universe_eq : (univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [universe_eq, sum_insert (by decide : 0 ∉ ({1} : Finset (ZMod 2))), sum_singleton]

private theorem odd_table_coordinate_zero {k : ℕ} {u : Fin 3 → ℕ}
    (table : OrbitTable k (fun i => 4 * u i)) (odd : k % 2 = 1) :
    u 0 ≤ u 1 + u 2 + 2 * (k - 1) := by
  let o := table.ordinary
  let s := table.special
  let b := table.ordinaryFixed
  let d := table.specialFixed
  have colA := table.specialCols 0
  have colB := table.specialCols 1
  have colOrdinary := table.ordinaryCols 0
  have row := table.rows 1
  have totalZero := table.totals 0
  have totalOne := table.totals 1
  have totalTwo := table.totals 2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, colour_sum_two] at colA colB colOrdinary row
  norm_num [Fin.sum_univ_succ, colour_sum_two, leftWord, rightWord] at totalZero totalOne totalTwo
  have iCap : 2 * u 0 + s 0 0 + s 0 1 + s 1 0 + s 1 1 + 2 * o 0 0 + 2 * o 1 0 ≤ 4 * k := by
    have b₂ := table.ordinaryBounds 2 0 0
    have b₃ := table.ordinaryBounds 3 0 0
    have f₂ := table.specialBounds 2 0 0
    have f₃ := table.specialBounds 3 0 0
    have g₂ := table.specialBounds 2 1 0
    have g₃ := table.specialBounds 3 1 0
    dsimp [o, s] at *
    omega
  have otherCap :
      2 * b 1 1 1 + 2 * b 1 2 2 + d 2 0 2 + d 3 0 1 + d 2 1 2 + d 3 1 1 ≤
        2 * (u 1 + u 2) := by
    dsimp [b, d] at *
    omega
  have extraA : s 1 0 % 2 ≤ 2 * (u 1 + u 2) := by
    have h := table.specialParity 1 0 1
    dsimp [s] at *
    omega
  have extraB : s 1 1 % 2 ≤ 2 * (u 1 + u 2) := by
    have h := table.specialParity 1 1 1
    dsimp [s] at *
    omega
  apply odd_coordinate_cut k (u 0) (u 1) (u 2)
    (s 0 0) (s 1 0) (s 2 0) (s 3 0) (s 0 1) (s 1 1) (s 2 1) (s 3 1)
    (o 0 0) (o 1 0) (o 1 1) (o 1 2) (b 1 1 1) (b 1 2 2)
    (d 2 0 2) (d 3 0 1) (d 2 1 2) (d 3 1 1)
    odd _ _ _ iCap otherCap ⟨extraA, extraB⟩
    (table.ordinaryParity 1 1 1) (table.ordinaryParity 1 2 2)
    (table.specialParity 2 0 2) (table.specialParity 3 0 1)
    (table.specialParity 2 1 2) (table.specialParity 3 1 1)
  all_goals clear * - colA colB row o s
  all_goals dsimp [s, o] at *
  all_goals omega

private theorem swapped_left_bit (a c i : Fin 3) (p : Fin 4) :
    leftWord (Equiv.swap a.succ c.succ p) (Equiv.swap a c i) = leftWord p i :=
  (by decide : ∀ (a c i : Fin 3) (p : Fin 4),
    leftWord (Equiv.swap a.succ c.succ p) (Equiv.swap a c i) = leftWord p i) a c i p

private theorem swapped_right_bit (a c i j : Fin 3) :
    rightWord (Equiv.swap a c j).succ (Equiv.swap a c i) = rightWord j.succ i :=
  (by decide : ∀ (a c i j : Fin 3),
    rightWord (Equiv.swap a c j).succ (Equiv.swap a c i) = rightWord j.succ i) a c i j

private def swap_coordinates {k : ℕ} {z : Fin 3 → ℕ} (table : OrbitTable k z) (a c : Fin 3) :
    OrbitTable k (fun i => z (Equiv.swap a c i)) := by
  let P := Equiv.swap a.succ c.succ
  let Q := Equiv.swap a c
  refine ⟨fun p j => table.ordinary (P p) (Q j), fun p d => table.special (P p) d,
    fun p j i => table.ordinaryFixed (P p) (Q j) (Q i), fun p d i => table.specialFixed (P p) d (Q i),
    ?_, ?_, ?_,
    fun p j i => table.ordinaryBounds (P p) (Q j) (Q i),
    fun p j i => table.ordinaryParity (P p) (Q j) (Q i),
    fun p d i => table.specialBounds (P p) d (Q i),
    fun p d i => table.specialParity (P p) d (Q i), ?_⟩
  · intro p
    rw [Equiv.sum_comp Q (table.ordinary (P p)), table.rows]
  · intro j
    rw [Equiv.sum_comp P (fun p => table.ordinary p (Q j)), table.ordinaryCols]
  · intro d
    rw [Equiv.sum_comp P (fun p => table.special p d), table.specialCols]
  · intro i
    have ordinary :
      (∑ p : Fin 4, ∑ j : Fin 3, if leftWord p i && rightWord j.succ i then
        table.ordinaryFixed (P p) (Q j) (Q i) else 0) =
      ∑ p : Fin 4, ∑ j : Fin 3, if leftWord p (Q i) && rightWord j.succ (Q i) then
        table.ordinaryFixed p j (Q i) else 0 := by
      rw [← Equiv.sum_comp P (fun p : Fin 4 => ∑ j : Fin 3, if leftWord p (Q i) &&
        rightWord j.succ (Q i) then table.ordinaryFixed p j (Q i) else 0)]
      apply sum_congr rfl
      intro p _
      rw [← Equiv.sum_comp Q (fun j : Fin 3 => if leftWord (P p) (Q i) &&
        rightWord j.succ (Q i) then table.ordinaryFixed (P p) j (Q i) else 0)]
      apply sum_congr rfl
      intro j _
      simp only [P, Q, swapped_left_bit, swapped_right_bit]
    have special :
      (∑ p : Fin 4, ∑ d : ZMod 2, if leftWord p i then table.specialFixed (P p) d (Q i) else 0) =
      ∑ p : Fin 4, ∑ d : ZMod 2, if leftWord p (Q i) then table.specialFixed p d (Q i) else 0 := by
      rw [← Equiv.sum_comp P (fun p : Fin 4 => ∑ d : ZMod 2,
        if leftWord p (Q i) then table.specialFixed p d (Q i) else 0)]
      apply sum_congr rfl
      intro p _
      simp only [P, Q, swapped_left_bit]
    rw [ordinary, special]
    exact table.totals (Q i)

private structure BudgetTwoCoupling where
  firstMatch : Fin 4 → Fin 4
  secondMatch : Fin 4 → Fin 4
  specialFirstColour : Fin 4 → ℕ

private def BudgetTwoCoupling.pooled (c : BudgetTwoCoupling) (p q : Fin 4) : ℕ :=
  (if c.firstMatch p = q then 1 else 0) + (if c.secondMatch p = q then 1 else 0)

private def BudgetTwoCoupling.special (c : BudgetTwoCoupling) (p : Fin 4) (colour : Fin 2) : ℕ :=
  if colour = 0 then c.specialFirstColour p else 2 * c.pooled p 0 - c.specialFirstColour p

private def BudgetTwoCoupling.valid (c : BudgetTwoCoupling) : Bool :=
  decide (∀ p, ∑ q, c.pooled p q = 2) &&
  decide (∀ q, ∑ p, c.pooled p q = 2) &&
  decide (∀ p, c.specialFirstColour p ≤ 2 * c.pooled p 0) &&
  decide (∀ colour, ∑ p, c.special p colour = 2)

private def budgetTwoCouplings : List BudgetTwoCoupling :=
  [⟨![1, 0, 3, 2], ![1, 3, 0, 2], ![0, 0, 2, 0]⟩,
   ⟨![2, 0, 3, 1], ![2, 0, 3, 1], ![0, 2, 0, 0]⟩,
   ⟨![1, 2, 3, 0], ![2, 0, 3, 1], ![0, 0, 0, 2]⟩,
   ⟨![1, 0, 3, 2], ![1, 0, 3, 2], ![0, 2, 0, 0]⟩]

private abbrev Cell := Fin 4 × (Fin 3 ⊕ Fin 2)

private def cells : List Cell :=
  (List.finRange 4).flatMap fun p =>
    (List.finRange 3).map (fun j => (p, Sum.inl j)) ++
      (List.finRange 2).map (fun d => (p, Sum.inr d))

private def BudgetTwoCoupling.multiplicity (c : BudgetTwoCoupling) : Cell → ℕ
  | (p, .inl j) => c.pooled p j.succ
  | (p, .inr d) => c.special p d

private def BudgetTwoCoupling.fixed (c : BudgetTwoCoupling) (mask : ℕ) (cell : Cell) : ℕ :=
  if c.multiplicity cell = 2 ∧ mask.testBit ((cells.filter fun a => c.multiplicity a = 2).idxOf cell) then
    2
  else
    c.multiplicity cell % 2

private theorem fixed_law (c : BudgetTwoCoupling) (mask : ℕ) (cell : Cell) :
    c.fixed mask cell ≤ c.multiplicity cell ∧
      c.fixed mask cell % 2 = c.multiplicity cell % 2 := by
  unfold BudgetTwoCoupling.fixed
  split
  · rename_i h
    simp [h.1]
  · omega

private def BudgetTwoCoupling.total (c : BudgetTwoCoupling) (i : Fin 3) (mask : Fin 64) : ℕ :=
  4 * (∑ p : Fin 4, ∑ j : Fin 3, if leftWord p i && rightWord j.succ i then
    c.fixed mask.val (p, .inl j) else 0) +
  2 * (∑ p : Fin 4, ∑ d : Fin 2, if leftWord p i then c.fixed mask.val (p, .inr d) else 0)

private def BudgetTwoCoupling.reaches (c : BudgetTwoCoupling) (i : Fin 3) (value : ℕ) : Bool :=
  (List.finRange 64).any (fun mask => c.total i mask == 4 * value)

-- The kernel checks the finite certificate by reduction over the tuple and mask indices.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private theorem budget_two_mask_certificate :
    ∀ x y z : Fin 5, x.val ≤ y.val → y.val ≤ z.val → x.val + y.val + z.val ≤ 8 →
      budgetTwoCouplings.any (fun c => c.valid && c.reaches 0 x.val && c.reaches 1 y.val &&
        c.reaches 2 z.val) = true := by
  decide

private theorem table_at_budget_two (u : Fin 3 → ℕ)
    (bounds : ∀ i, u i ≤ 4) (order₁ : u 0 ≤ u 1) (order₂ : u 1 ≤ u 2)
    (cap : u 0 + u 1 + u 2 ≤ 8) : Nonempty (OrbitTable 2 (fun i => 4 * u i)) := by
  let x (i : Fin 3) : Fin 5 := ⟨u i, Nat.lt_succ_of_le (bounds i)⟩
  have cert := budget_two_mask_certificate (x 0) (x 1) (x 2) order₁ order₂ cap
  obtain ⟨coupling, _, hc⟩ := List.any_eq_true.mp cert
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨valid, reaches₀⟩, reaches₁⟩, reaches₂⟩ := hc
  have reaches (i : Fin 3) : coupling.reaches i (u i) = true := by
    fin_cases i
    · exact reaches₀
    · exact reaches₁
    · exact reaches₂
  have masks (i : Fin 3) : ∃ mask : Fin 64, coupling.total i mask = 4 * u i := by
    obtain ⟨mask, _, hit⟩ := List.any_eq_true.mp (reaches i)
    exact ⟨mask, of_decide_eq_true hit⟩
  choose mask total using masks
  unfold BudgetTwoCoupling.valid at valid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
  obtain ⟨⟨⟨rows, cols⟩, specialBound⟩, specialCols⟩ := valid
  let colour := (ZMod.finEquiv 2).toEquiv
  let o (p : Fin 4) (j : Fin 3) := coupling.multiplicity (p, .inl j)
  let s (p : Fin 4) (d : ZMod 2) := coupling.multiplicity (p, .inr (colour.symm d))
  let b (p : Fin 4) (j i : Fin 3) := coupling.fixed (mask i).val (p, .inl j)
  let a (p : Fin 4) (d : ZMod 2) (i : Fin 3) := coupling.fixed (mask i).val (p, .inr (colour.symm d))
  refine ⟨⟨o, s, b, a, ?_, fun j => cols j.succ, fun d => specialCols (colour.symm d),
    fun p j i => (fixed_law coupling _ (p, .inl j)).1,
    fun p j i => (fixed_law coupling _ (p, .inl j)).2,
    fun p d i => (fixed_law coupling _ (p, .inr (colour.symm d))).1,
    fun p d i => (fixed_law coupling _ (p, .inr (colour.symm d))).2, ?_⟩⟩
  · intro p
    have left := rows p
    rw [Fin.sum_univ_succ] at left
    have colourSum : (∑ d : ZMod 2, s p d) = 2 * coupling.pooled p 0 := by
      rw [← Equiv.sum_comp colour (s p)]
      simp only [s, Equiv.symm_apply_apply]
      rw [Fin.sum_univ_two]
      simp only [BudgetTwoCoupling.multiplicity, BudgetTwoCoupling.special, ite_eq_left rfl,
        show (1 : Fin 2) ≠ 0 by decide, ite_false]
      exact Nat.add_sub_of_le (specialBound p)
    rw [colourSum]
    change 2 * coupling.pooled p 0 + 2 * (∑ j : Fin 3, coupling.pooled p j.succ) = _
    omega
  · intro i
    have read := total i
    unfold BudgetTwoCoupling.total at read
    simp only [b]
    have colourSum (p : Fin 4) :
        (∑ d : ZMod 2, if leftWord p i then a p d i else 0) =
          ∑ d : Fin 2, if leftWord p i then coupling.fixed (mask i).val (p, Sum.inr d) else 0 := by
      rw [← Equiv.sum_comp colour (fun d : ZMod 2 => if leftWord p i then a p d i else 0)]
      simp only [a, Equiv.symm_apply_apply]
    simp_rw [colourSum]
    exact read.symm

private theorem table_permute {k : ℕ} {z : Fin 3 → ℕ} (table : Nonempty (OrbitTable k z))
    (σ : Equiv.Perm (Fin 3)) : Nonempty (OrbitTable k (z ∘ σ)) := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => exact table
  | mul_swap σ a c distinct rest =>
    obtain ⟨T⟩ := rest
    exact ⟨swap_coordinates T a c⟩

private theorem table_at_budget_two_any_order (u : Fin 3 → ℕ)
    (bounds : ∀ i, u i ≤ 4) (cap : ∑ i, u i ≤ 8) :
    Nonempty (OrbitTable 2 (fun i => 4 * u i)) := by
  let σ := Tuple.sort u
  have ordered := Tuple.monotone_sort u
  have total : (∑ i, u (σ i)) ≤ 8 := by
    rw [Equiv.sum_comp σ u]
    exact cap
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at total
  have numerals : u (σ 0) + u (σ 1) + u (σ 2) ≤ 8 := by
    simpa [add_assoc] using total
  have sorted := table_at_budget_two (u ∘ σ) (fun i => bounds (σ i))
    (ordered (by decide : (0 : Fin 3) ≤ 1)) (ordered (by decide : (1 : Fin 3) ≤ 2)) numerals
  simpa only [Function.comp_def, σ.apply_symm_apply] using table_permute sorted σ.symm

private theorem table_at_budget_one (u : Fin 3 → ℕ)
    (bounds : ∀ i, u i ≤ 2) (cap : u 0 + u 1 + u 2 ≤ 4)
    (t₀ : u 0 ≤ u 1 + u 2) (t₁ : u 1 ≤ u 0 + u 2) (t₂ : u 2 ≤ u 0 + u 1) :
    Nonempty (OrbitTable 1 (fun i => 4 * u i)) := by
  let x (i : Fin 3) : Fin 3 := ⟨u i, Nat.lt_succ_of_le (bounds i)⟩
  have profileCuts : ∀ (a b c : Fin 3), a.val + b.val + c.val ≤ 4 →
      a.val ≤ b.val + c.val → b.val ≤ a.val + c.val → c.val ≤ a.val + b.val →
      ∀ p : Fin 4, 2 ≤ ∑ i : Fin 3, if bitProfile (leftWord p) i = 0
        then 2 - (![a.val, b.val, c.val] i) else (![a.val, b.val, c.val] i) := by
    decide
  apply orbit_table_of_realization
  apply (D5.S3.ConceptDynamics.Attribution.ParityMinimumSeedSpectrum.exact_minimal_budget_fixed_counts
    1 (fun i => 4 * u i)).mpr
  refine ⟨fun i => 2 - u i, fun i => ?_, fun e even => ?_⟩
  · have hi := bounds i
    change 2 - u i ≤ 2 ∧ 4 * u i = 4 * (2 - (2 - u i))
    omega
  · obtain ⟨p, hp⟩ := leftProfile_bijective.surjective ⟨e, even⟩
    have profileEq : bitProfile (leftWord p) = e := congrArg Subtype.val hp
    have val (i : Fin 3) : (![ (x 0).val, (x 1).val, (x 2).val ] i) = u i := by
      fin_cases i <;> rfl
    have h := profileCuts (x 0) (x 1) (x 2) cap t₀ t₁ t₂ p
    simp only [profileEq, val] at h
    change 2 ≤ ∑ i, if e i = 0 then 2 - u i else 2 - (2 - u i)
    refine h.trans_eq (sum_congr rfl (fun i _ => ?_))
    have hi := bounds i
    split <;> simp_all [Nat.sub_sub_self]

private def zero_table : OrbitTable 0 (fun _ => 0) where
  ordinary _ _ := 0
  special _ _ := 0
  ordinaryFixed _ _ _ := 0
  specialFixed _ _ _ := 0
  rows := by simp
  ordinaryCols := by simp
  specialCols := by simp
  ordinaryBounds := by simp
  ordinaryParity := by simp
  specialBounds := by simp
  specialParity := by simp
  totals := by simp

private def add_tables {k l : ℕ} {z w : Fin 3 → ℕ}
    (A : OrbitTable k z) (B : OrbitTable l w) : OrbitTable (k + l) (fun i => z i + w i) := by
  refine ⟨fun p j => A.ordinary p j + B.ordinary p j,
    fun p d => A.special p d + B.special p d,
    fun p j i => A.ordinaryFixed p j i + B.ordinaryFixed p j i,
    fun p d i => A.specialFixed p d i + B.specialFixed p d i,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    have a := A.rows p
    have b := B.rows p
    simp only [sum_add_distrib]
    omega
  · intro j
    simp [sum_add_distrib, A.ordinaryCols, B.ordinaryCols]
  · intro d
    simp [sum_add_distrib, A.specialCols, B.specialCols]
  · intro p j i
    exact Nat.add_le_add (A.ordinaryBounds p j i) (B.ordinaryBounds p j i)
  · intro p j i
    rw [Nat.add_mod, A.ordinaryParity, B.ordinaryParity, ← Nat.add_mod]
  · intro p d i
    exact Nat.add_le_add (A.specialBounds p d i) (B.specialBounds p d i)
  · intro p d i
    rw [Nat.add_mod, A.specialParity, B.specialParity, ← Nat.add_mod]
  · intro i
    have add_if (P : Prop) [Decidable P] (x y : ℕ) :
        (if P then x + y else 0) = (if P then x else 0) + (if P then y else 0) := by
      by_cases h : P <;> simp [h]
    simp only [A.totals i, B.totals i, add_if, sum_add_distrib, Nat.mul_add]
    omega

private theorem split_three_caps (c₀ c₁ c₂ t : ℕ) (h : t ≤ c₀ + c₁ + c₂) :
    ∃ a b c : ℕ, a ≤ c₀ ∧ b ≤ c₁ ∧ c ≤ c₂ ∧ a + b + c=t := by
  refine ⟨min t c₀, min (t - c₀) c₁, t - c₀ - c₁, ?_⟩
  omega

private theorem split_even_budget (m x y z : ℕ)
    (hx : x ≤ 4 * (m + 1)) (hy : y ≤ 4 * (m + 1)) (hz : z ≤ 4 * (m + 1))
    (total : x + y + z ≤ 8 * (m + 1)) :
    ∃ a b c : ℕ, a ≤ min x 4 ∧ b ≤ min y 4 ∧ c ≤ min z 4 ∧ a + b + c ≤ 8 ∧
      x - a ≤ 4 * m ∧ y - b ≤ 4 * m ∧ z - c ≤ 4 * m ∧ (x - a) + (y - b) + (z - c) ≤ 8 * m := by
  let Lx := x - 4 * m
  let Ly := y - 4 * m
  let Lz := z - 4 * m
  let Ux := min x 4
  let Uy := min y 4
  let Uz := min z 4
  let T := max (Lx + Ly + Lz) (x + y + z - 8 * m)
  have lx : Lx ≤ Ux := by dsimp [Lx, Ux]; omega
  have ly : Ly ≤ Uy := by dsimp [Ly, Uy]; omega
  have lz : Lz ≤ Uz := by dsimp [Lz, Uz]; omega
  have lowTotal : Lx + Ly + Lz ≤ 8 := by
    dsimp [Lx, Ly, Lz]
    omega
  have highTotal : x + y + z - 8 * m ≤ Ux + Uy + Uz := by
    dsimp [Ux, Uy, Uz]
    omega
  have target : T - (Lx + Ly + Lz) ≤ (Ux - Lx) + (Uy - Ly) + (Uz - Lz) := by
    dsimp [T]
    omega
  obtain ⟨a, b, c, ha, hb, hc, sum⟩ := split_three_caps _ _ _ _ target
  refine ⟨Lx + a, Ly + b, Lz + c, ?_⟩
  unfold T at sum
  dsimp [Lx, Ly, Lz, Ux, Uy, Uz] at *
  omega

private theorem split_odd_budget_sorted (m x y z : ℕ)
    (mpos : 2 ≤ m) (hxy : x ≤ y) (hyz : y ≤ z)
    (hz : z ≤ 2 * m + 2) (total : x + y + z ≤ 4 * m + 4)
    (cut : z ≤ x + y + 2 * m) :
    ∃ a b c : ℕ, a ≤ min x 2 ∧ b ≤ min y 2 ∧ c ≤ min z 2 ∧
      a + b + c ≤ 4 ∧ a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧
      x - a ≤ 2 * m ∧ y - b ≤ 2 * m ∧ z - c ≤ 2 * m ∧ (x - a) + (y - b) + (z - c) ≤ 4 * m := by
  by_cases largeY : 2 ≤ y
  · exact ⟨0, 2, 2, by omega⟩
  · by_cases threePositive : 1 ≤ x
    · by_cases largeZ : 2 ≤ z
      · exact ⟨1, 1, 2, by omega⟩
      · exact ⟨0, 0, 0, by omega⟩
    · by_cases highZ : 2 * m < z
      · exact ⟨0, 1, 1, by omega⟩
      · exact ⟨0, 0, 0, by omega⟩

private theorem trio_sum (u : Fin 3 → ℕ) : (∑ i, u i) = u 0 + u 1 + u 2 := by
  simp [Fin.sum_univ_succ, add_assoc]

private theorem table_at_even_budget (m : ℕ) (u : Fin 3 → ℕ)
    (bounds : ∀ i, u i ≤ 4 * m) (cap : ∑ i, u i ≤ 8 * m) :
    Nonempty (OrbitTable (2 * m) (fun i => 4 * u i)) := by
  induction m generalizing u with
  | zero =>
    have h : (fun i => 4 * u i) = fun _ => 0 := by
      funext i
      have hi := bounds i
      omega
    simpa [h] using (show Nonempty (OrbitTable 0 (fun _ => 0)) from ⟨zero_table⟩)
  | succ m ih =>
    obtain ⟨a, b, c, ha, hb, hc, abc, ax, byy, cz, total⟩ :=
      split_even_budget m (u 0) (u 1) (u 2) (bounds 0) (bounds 1) (bounds 2)
        ((trio_sum u) ▸ cap)
    let block : Fin 3 → ℕ := ![a, b, c]
    let remain : Fin 3 → ℕ := fun i => u i - block i
    have boundedBlock (i : Fin 3) : block i ≤ 4 := by
      fin_cases i
      · exact ha.trans (min_le_right _ _)
      · exact hb.trans (min_le_right _ _)
      · exact hc.trans (min_le_right _ _)
    have blockCap : ∑ i, block i ≤ 8 := by simpa [trio_sum, block] using abc
    have boundedRemain (i : Fin 3) : remain i ≤ 4 * m := by
      fin_cases i <;> assumption
    have remainCap : ∑ i, remain i ≤ 8 * m := by simpa [trio_sum, remain, block] using total
    obtain ⟨A⟩ := table_at_budget_two_any_order block boundedBlock blockCap
    obtain ⟨B⟩ := ih remain boundedRemain remainCap
    have combine : (fun i => 4 * block i + 4 * remain i) = (fun i => 4 * u i) := by
      funext i
      fin_cases i
      · have h := ha.trans (min_le_left _ _)
        change 4 * a + 4 * (u 0 - a) = 4 * u 0
        omega
      · have h := hb.trans (min_le_left _ _)
        change 4 * b + 4 * (u 1 - b) = 4 * u 1
        omega
      · have h := hc.trans (min_le_left _ _)
        change 4 * c + 4 * (u 2 - c) = 4 * u 2
        omega
    have budget : 2 + 2 * m = 2 * (m + 1) := by omega
    exact budget ▸ combine ▸ ⟨add_tables A B⟩

private theorem table_at_odd_budget_sorted (m : ℕ) (u : Fin 3 → ℕ)
    (ordered₁ : u 0 ≤ u 1) (ordered₂ : u 1 ≤ u 2)
    (bounds : ∀ i, u i ≤ 2 * (2 * m + 1)) (cap : ∑ i, u i ≤ 4 * (2 * m + 1))
    (cuts : ∀ i, 2 * u i ≤ (∑ j, u j) + 2 * (2 * m)) :
    Nonempty (OrbitTable (2 * m + 1) (fun i => 4 * u i)) := by
  by_cases hm : m = 0
  · subst m
    apply table_at_budget_one u
    · exact bounds
    · exact (trio_sum u) ▸ cap
    all_goals
      have a := cuts 0
      have b := cuts 1
      have c := cuts 2
      rw [trio_sum] at a b c
      omega
  · have mpos : 2 ≤ 2 * m := by omega
    have zBound := bounds 2
    have zCap := (trio_sum u) ▸ cap
    have zCut := (trio_sum u) ▸ cuts 2
    obtain ⟨a, b, c, ha, hb, hc, blockCap, ta, tb, tc, ax, byy, cz, remCap⟩ :=
      split_odd_budget_sorted (2 * m) (u 0) (u 1) (u 2) mpos ordered₁ ordered₂
        (by omega) (by omega) (by omega)
    let block : Fin 3 → ℕ := ![a, b, c]
    let remain : Fin 3 → ℕ := fun i => u i - block i
    have boundedBlock (i : Fin 3) : block i ≤ 2 := by
      fin_cases i
      · exact ha.trans (min_le_right _ _)
      · exact hb.trans (min_le_right _ _)
      · exact hc.trans (min_le_right _ _)
    have boundedRemain (i : Fin 3) : remain i ≤ 4 * m := by
      fin_cases i
      · change u 0 - a ≤ 4 * m
        omega
      · change u 1 - b ≤ 4 * m
        omega
      · change u 2 - c ≤ 4 * m
        omega
    have remainCap : ∑ i, remain i ≤ 8 * m := by
      rw [trio_sum]
      change (u 0 - a) + (u 1 - b) + (u 2 - c) ≤ 8 * m
      omega
    obtain ⟨A⟩ := table_at_budget_one block boundedBlock blockCap ta tb tc
    obtain ⟨B⟩ := table_at_even_budget m remain boundedRemain remainCap
    have combine : (fun i => 4 * remain i + 4 * block i) = (fun i => 4 * u i) := by
      funext i
      fin_cases i
      · have h := ha.trans (min_le_left _ _)
        change 4 * (u 0 - a) + 4 * a = 4 * u 0
        omega
      · have h := hb.trans (min_le_left _ _)
        change 4 * (u 1 - b) + 4 * b = 4 * u 1
        omega
      · have h := hc.trans (min_le_left _ _)
        change 4 * (u 2 - c) + 4 * c = 4 * u 2
        omega
    exact combine ▸ ⟨add_tables B A⟩

private theorem table_at_budget (k : ℕ) (u : Fin 3 → ℕ)
    (bounds : ∀ i, u i ≤ 2 * k) (cap : ∑ i, u i ≤ 4 * k)
    (cuts : k % 2 = 1 → ∀ i, 2 * u i ≤ (∑ j, u j) + 2 * (k - 1)) :
    Nonempty (OrbitTable k (fun i => 4 * u i)) := by
  let m := k/2
  by_cases odd : k % 2 = 1
  · have eq : k = 2 * m + 1 := by dsimp [m]; omega
    let σ := Tuple.sort u
    have ordered := Tuple.monotone_sort u
    have sameTotal : (∑ i, u (σ i)) = ∑ i, u i := Equiv.sum_comp σ u
    have sorted := table_at_odd_budget_sorted m (u ∘ σ)
      (ordered (by decide : (0 : Fin 3) ≤ 1)) (ordered (by decide : (1 : Fin 3) ≤ 2))
      (fun i => eq ▸ bounds (σ i))
      (by rw [show (∑ i, (u ∘ σ) i) = ∑ i, u i from sameTotal]; exact eq ▸ cap)
      (fun i => by
        have h := cuts odd (σ i)
        change 2 * u (σ i) ≤ (∑ j, u (σ j)) + 2 * (2 * m)
        rw [sameTotal]
        omega)
    have antirelabel := table_permute sorted σ.symm
    simpa only [Function.comp_def, σ.apply_symm_apply, ← eq] using antirelabel
  · have eq : k = 2 * m := by dsimp [m]; omega
    have b (i : Fin 3) : u i ≤ 4 * m := by have hi := bounds i; omega
    have c : (∑ i, u i) ≤ 8 * m := by omega
    simpa only [← eq] using table_at_even_budget m u b c

private theorem odd_cuts_for_table {k : ℕ} {u : Fin 3 → ℕ}
    (table : OrbitTable k (fun i => 4 * u i)) (odd : k % 2 = 1) (i : Fin 3) :
    2 * u i ≤ (∑ j, u j) + 2 * (k - 1) := by
  let σ := Equiv.swap 0 i
  have onZero : σ 0 = i := by simp [σ]
  have total := Equiv.sum_comp σ u
  rw [trio_sum] at total
  have relabelled : OrbitTable k (fun j => 4 * u (σ j)) := swap_coordinates table 0 i
  have cut := odd_table_coordinate_zero relabelled odd
  simp only [onZero] at cut total
  omega

private theorem normalized_feasible_bounds {k : ℕ} {u : Fin 3 → ℕ}
    (h : RealizableSeedCounts 1 k (fun i => 4 * u i)) :
    (∀ i, u i ≤ 2 * k) ∧ (∑ i, u i) ≤ 4 * k := by
  obtain ⟨v, hv, dominates⟩ := seed_vector_dominated h
  obtain ⟨bounded, wall⟩ := hv
  have front (i : Fin 3) : u i ≤ v i := by
    have hi := dominates i
    change 4 * u i ≤ 4 * v i at hi
    omega
  have upper (i : Fin 3) : v i ≤ 2 * k := by
    have hi := bounded i
    change v i ≤ k * 2 at hi
    omega
  refine ⟨fun i => (front i).trans (upper i), ?_⟩
  change (∑ i : Fin 3, (k * 2 - v i)) = k * 2 at wall
  rw [trio_sum] at wall ⊢
  have a := upper 0
  have b := upper 1
  have c := upper 2
  have d := front 0
  have e := front 1
  have f := front 2
  omega

/-- In dimension three the coordinate and total bounds, together with the odd-budget
cuts, characterize simultaneous fixed counts under both uniform parity marginals. -/
theorem exact_three_coordinate_counts (k : ℕ) (z : Fin 3 → ℕ) :
    RealizableSeedCounts 1 k z ↔
      ∃ u : Fin 3 → ℕ, (∀ i, z i = 4 * u i) ∧ (∀ i, u i ≤ 2 * k) ∧
        (∑ i, u i) ≤ 4 * k ∧ (k % 2 = 1 → ∀ i, 2 * u i ≤ (∑ j, u j) + 2 * (k - 1)) := by
  constructor
  · intro realized
    have divisible (i : Fin 3) : 4 ∣ z i := by
      obtain ⟨S, _, _, f, card, equiv, ⟨margin, rows, cols⟩, fixed⟩ := realized
      rw [← fixed i]
      exact D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum.coordinate_fixed_count_four_dvd
        f equiv margin rows cols i
    choose u hu using divisible
    have eq : z = fun i => 4 * u i := funext hu
    have realized' := eq ▸ realized
    obtain ⟨bounds, cap⟩ := normalized_feasible_bounds realized'
    obtain ⟨table⟩ := orbit_table_of_realization realized'
    exact ⟨u, hu, bounds, cap, fun odd i => odd_cuts_for_table table odd i⟩
  · rintro ⟨u, hu, bounds, cap, cuts⟩
    have eq : (fun i => 4 * u i) = z := (funext hu).symm
    obtain ⟨table⟩ := table_at_budget k u bounds cap cuts
    exact eq ▸ make_realization_of_orbit_table table

end D5.S3.ConceptDynamics.Attribution.ParityThreeCoordinateCounts

end
