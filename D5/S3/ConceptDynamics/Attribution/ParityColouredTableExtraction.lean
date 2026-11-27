/- GID: D5/S3/ConceptDynamics/Attribution/ParityColouredTableExtraction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityColouredTableExtraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Extract a parity table from an even-dimensional equivariant seed action. -/

import D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts
import D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
import D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
import D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable
import D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.ParityColouredTableExtraction

open Finset MulAction
open D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling
open D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
open D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts
open D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
open D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
open D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
open D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable
open D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds

noncomputable section

def indicator {n : ℕ} (p : Finset (Fin n)) : Profile n :=
  fun i => if i ∈ p then 1 else 0

private theorem parity_indicator {n : ℕ} (p : Finset (Fin n)) :
    parity (indicator p) = (p.card : ZMod 2) := by
  change (∑ i, if i ∈ p then (1 : ZMod 2) else 0) = (p.card : ZMod 2)
  rw [← sum_filter]
  simp

private def profileEquiv (n : ℕ) : Finset (Fin n) ≃ Profile n where
  toFun := indicator
  invFun x := univ.filter fun i => x i = 1
  left_inv p := by
    ext i
    by_cases hp : i ∈ p <;> simp [indicator, hp]
  right_inv x := by
    funext i
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (x i) with h | h <;>
      simp [indicator, h]

private theorem parity_indicator_iff {n : ℕ} (p : Finset (Fin n)) (t : ℕ) (ht : t < 2) :
    parity (indicator p) = (t : ZMod 2) ↔ p.card % 2 = t := by
  rw [parity_indicator, ZMod.natCast_eq_natCast_iff]
  change (p.card % 2 = t % 2) ↔ _
  rw [Nat.mod_eq_of_lt ht]

def parityClassEquiv (n t : ℕ) (ht : t < 2) :
    {p : Finset (Fin n) // p.card % 2 = t} ≃ ParityClass n (t : ZMod 2) :=
  (profileEquiv n).subtypeEquiv fun p => (parity_indicator_iff p t ht).symm

section
variable {I : Type*} [Fintype I]
open Classical

private theorem same_ordinary_orbit {I : Type*} [Fintype I]
    (p q : I → Bool) (different : p ≠ q)
    (leftMoves : ∃ i, p i = false) (rightMoves : ∃ i, q i = false)
    (c c' d d' : ZMod 2) :
    ∃ g : Acting I, g • ((⟨p,c⟩, ⟨q,d⟩) : Output I × Output I) =
      ((⟨p,c'⟩, ⟨q,d'⟩) : Output I × Output I) := by
  obtain ⟨v, lifts⟩ := shifts_surjective p q different leftMoves rightMoves (c' - c, d' - d)
  refine ⟨Multiplicative.ofAdd v, ?_⟩
  change ((⟨p, shift p v + c⟩, ⟨q, shift q v + d⟩) : Output I × Output I) =
    ((⟨p,c'⟩, ⟨q,d'⟩) : Output I × Output I)
  have a : shift p v = c' - c := congrArg Prod.fst lifts
  have b : shift q v = d' - d := congrArg Prod.snd lifts
  simp [a, b]

private theorem same_special_orbit {I : Type*} [Fintype I]
    (p q : I → Bool) (all : ∀ i, p i = true) (rightMoves : ∃ i, q i = false)
    (c d d' : ZMod 2) :
    ∃ g : Acting I, g • ((⟨p,c⟩, ⟨q,d⟩) : Output I × Output I) =
      ((⟨p,c⟩, ⟨q,d'⟩) : Output I × Output I) := by
  classical
  obtain ⟨i, hi⟩ := rightMoves
  let v : I → ZMod 2 := Pi.single i (d' - d)
  refine ⟨Multiplicative.ofAdd v, ?_⟩
  change ((⟨p, shift p v + c⟩, ⟨q, shift q v + d⟩) : Output I × Output I) =
    ((⟨p,c⟩, ⟨q,d'⟩) : Output I × Output I)
  rw [all_true_shift p all, zero_add]
  have h : shift q v = d' - d := by simp [v, eval_single, hi]
  simp [h]

private theorem point_to_profile
    {n k : ℕ}
    (weight : (EvenSubset n × Fin 2) → (OddSubset n × Fin 2) → ℕ)
    (rows : ∀ x, ∑ y, weight x y = 2 * k)
    (cols : ∀ y, ∑ x, weight x y = 2 * k)
    (right_colour : ∀ p q c d, weight (p,c) (q,d) = weight (p,c) (q,0)) :
    (∀ p c, ∑ q, weight (p,c) (q,0) = k) ∧
    ∀ q, ∑ p, (weight (p,0) (q,0) + weight (p,1) (q,0)) = 2 * k := by
  constructor
  · intro p c
    have h := rows (p,c)
    rw [Fintype.sum_prod_type] at h
    simp_rw [right_colour, Fin.sum_univ_two, ← two_mul, ← mul_sum] at h
    omega
  · intro q
    simpa only [Fintype.sum_prod_type, Fin.sum_univ_two] using cols (q,0)

private def colouredSlice (n t : ℕ) (ht : t < 2) :
    ({p : Finset (Fin n) // p.card % 2 = t} × Fin 2) ≃ slice n (t : ZMod 2) :=
  ((parityClassEquiv n t ht).prodCongr (Equiv.refl (Fin 2))).trans (sliceEquiv n (t : ZMod 2))

private theorem colouredSlice_profile {n t : ℕ} (ht : t < 2)
    (x : {p : Finset (Fin n) // p.card % 2 = t} × Fin 2) (i : Fin n) :
    (colouredSlice n t ht x).val.profile i = true ↔ i ∈ x.1.val := by
  change decide (indicator x.1.val i = 1) = true ↔ i ∈ x.1.val
  rw [decide_eq_true_eq]
  by_cases hi : i ∈ x.1.val <;> simp [indicator, hi, zero_ne_one]

private theorem odd_proper {n : ℕ} (even : n % 2 = 0) (q : OddSubset n) :
    q.val ≠ univ := by
  intro full
  have h := q.property
  rw [full, card_univ, Fintype.card_fin, even] at h
  omega

private theorem profile_moves {n t : ℕ} (ht : t < 2)
    {p : {p : Finset (Fin n) // p.card % 2 = t}} (notFull : p.val ≠ univ) (c : Fin 2) :
    ∃ i, (colouredSlice n t ht (p,c)).val.profile i = false := by
  by_contra! fixed
  apply notFull
  ext i
  simp only [mem_univ, iff_true]
  apply (colouredSlice_profile ht (p,c) i).mp
  cases h : (colouredSlice n t ht (p,c)).val.profile i
  · exact (fixed i h).elim
  · rfl

private theorem even_odd_profiles_different {n : ℕ} (p : EvenSubset n) (q : OddSubset n)
    (c d : Fin 2) :
    (colouredSlice n 0 (by decide) (p,c)).val.profile ≠
      (colouredSlice n 1 (by decide) (q,d)).val.profile := by
  intro eq
  have same : p.val = q.val := by
    ext i
    rw [← colouredSlice_profile (by decide : 0 < 2) (p,c) i,
      ← colouredSlice_profile (by decide : 1 < 2) (q,d) i, eq]
  have hp := p.property
  have hq := q.property
  rw [same] at hp
  omega

open Classical in
private theorem card_eq_indicator {A : Type*} [Fintype A] (P : A → Prop) :
    Nat.card {a : A // P a} = ∑ a, if P a then 1 else 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [sum_filter]

open Classical in
private theorem point_sums {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → B × C) (x : B) :
    (∑ c : C, Nat.card {a : A // f a = (x,c)}) =
      ∑ a, if (f a).1 = x then 1 else 0 := by
  simp_rw [card_eq_indicator, Prod.ext_iff]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  by_cases h : (f a).1 = x <;> simp [h]

private def evenPoint (n : ℕ) : (EvenSubset (n + 2) × Fin 2) ≃ slice (n + 2) 0 :=
  colouredSlice (n+2) 0 (by decide)

private def oddPoint (n : ℕ) : (OddSubset (n + 2) × Fin 2) ≃ slice (n + 2) 1 :=
  colouredSlice (n+2) 1 (by decide)

private theorem cell_weight_right {n : ℕ} (even : (n + 2) % 2 = 0)
    (m : orbitRel.Quotient (Acting (Fin (n+2))) (Pair n) → ℕ)
    (p : EvenSubset (n + 2)) (q : OddSubset (n + 2)) (c d : Fin 2) :
    m (Quotient.mk'' (evenPoint n (p,c), oddPoint n (q,0))) =
      m (Quotient.mk'' (evenPoint n (p,c), oddPoint n (q,d))) := by
  classical
  suffices ∃ g : Acting (Fin (n + 2)),
      g • (evenPoint n (p,c), oddPoint n (q,0)) =
        (evenPoint n (p,c), oddPoint n (q,d)) by
    apply congrArg m
    symm
    exact Quotient.sound this
  have rightMoves := profile_moves (by decide : 1 < 2) (odd_proper even q) 0
  have lift (g : Acting (Fin (n + 2)))
      (h : g • (((evenPoint n (p,c)).val, (oddPoint n (q,0)).val) :
          Output (Fin (n + 2)) × Output (Fin (n + 2))) =
        ((evenPoint n (p,c)).val, (oddPoint n (q,d)).val)) :
      g • (evenPoint n (p,c), oddPoint n (q,0)) =
        (evenPoint n (p,c), oddPoint n (q,d)) :=
    Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  by_cases full : p.val = univ
  · have all (i : Fin (n + 2)) : (evenPoint n (p,c)).val.profile i = true :=
      (colouredSlice_profile (by decide : 0 < 2) (p,c) i).mpr (by simp [full])
    obtain ⟨g, hg⟩ := same_special_orbit (evenPoint n (p,c)).val.profile
      (oddPoint n (q,0)).val.profile all rightMoves (c : ZMod 2) 0 (d : ZMod 2)
    exact ⟨g, lift g hg⟩
  · obtain ⟨g, hg⟩ := same_ordinary_orbit (evenPoint n (p,c)).val.profile
      (oddPoint n (q,0)).val.profile (even_odd_profiles_different p q c 0)
      (profile_moves (by decide : 0 < 2) full c) rightMoves (c : ZMod 2) c 0 d
    exact ⟨g, lift g hg⟩

private theorem cell_weight_left {n : ℕ} (even : (n + 2) % 2 = 0)
    (m : orbitRel.Quotient (Acting (Fin (n+2))) (Pair n) → ℕ)
    (p : EvenSubset (n + 2)) (q : OddSubset (n + 2)) (ordinary : p.val ≠ univ) :
    m (Quotient.mk'' (evenPoint n (p,0), oddPoint n (q,0))) =
      m (Quotient.mk'' (evenPoint n (p,1), oddPoint n (q,0))) := by
  apply congrArg m
  symm
  apply Quotient.sound
  obtain ⟨g, hg⟩ := same_ordinary_orbit (evenPoint n (p,0)).val.profile
    (oddPoint n (q,0)).val.profile (even_odd_profiles_different p q 0 0)
    (profile_moves (by decide : 0 < 2) ordinary 0)
    (profile_moves (by decide : 1 < 2) (odd_proper even q) 0) 0 1 0 0
  exact ⟨g, Prod.ext (Subtype.ext (congrArg Prod.fst hg)) (Subtype.ext (congrArg Prod.snd hg))⟩

/-- The parity table extracted from an even-dimensional action gives simultaneous
lower bounds for its coordinate fixed counts. -/
theorem extract_coloured_subsets (n k : ℕ)
    (even : (n + 2) % 2 = 0) (z : Fin (n + 2) → ℕ)
    (realized : RealizableSeedCounts n k z) :
    ∃ b : EvenSubset (n + 2) → OddSubset (n + 2) → Fin 2 → ℕ,
      (∀ p c, ∑ q, b p q c = k) ∧
      (∀ q, ∑ p, (b p q 0 + b p q 1) = 2 * k) ∧
      (∀ p q, p.val ≠ univ → b p q 0 = b p q 1) ∧
      (∀ i, 2 * (∑ p, ∑ q, ∑ c : Fin 2,
        if i ∈ p.val ∩ q.val then b p q c % 2 else 0) ≤ z i) := by
  classical
  rcases realized with ⟨S, _, _, f, card, equiv, ⟨c, rows, cols⟩, counts⟩
  have c_eq := left_colour_marginal f card c rows
  obtain ⟨m, zPoint, _, parity, fibre, fixed⟩ := orbit_fixed_fibre_counts f equiv
  let point (x : EvenSubset (n + 2) × Fin 2) (y : OddSubset (n + 2) × Fin 2) : Pair n :=
    (evenPoint n x, oddPoint n y)
  let w (x : EvenSubset (n + 2) × Fin 2) (y : OddSubset (n + 2) × Fin 2) :=
    m (Quotient.mk'' (point x y))
  have rowSum (x : EvenSubset (n + 2) × Fin 2) : ∑ y, w x y = 2 * k := by
    change (∑ y, m (Quotient.mk'' (evenPoint n x, oddPoint n y))) = 2 * k
    rw [(oddPoint n).sum_comp (fun y => m (Quotient.mk'' (evenPoint n x, y)))]
    simp_rw [← fibre]
    rw [point_sums, rows, c_eq]
  have colSum (y : OddSubset (n + 2) × Fin 2) : ∑ x, w x y = 2 * k := by
    change (∑ x, m (Quotient.mk'' (evenPoint n x, oddPoint n y))) = 2 * k
    rw [(evenPoint n).sum_comp (fun x => m (Quotient.mk'' (x, oddPoint n y)))]
    simp_rw [← fibre]
    rw [← c_eq, ← cols (oddPoint n y)]
    simp_rw [card_eq_indicator, Prod.ext_iff]
    rw [sum_comm]
    apply sum_congr rfl
    intro s _
    by_cases h : (f s).2 = oddPoint n y <;> simp [h]
  have rightIndependent (p : EvenSubset (n+2)) (q : OddSubset (n+2)) (c d : Fin 2) :
      w (p,c) (q,d) = w (p,c) (q,0) :=
    (cell_weight_right even m p q c d).symm
  have ordinary (p : EvenSubset (n+2)) (q : OddSubset (n+2)) (hp : p.val ≠ univ) :
      w (p,0) (q,0) = w (p,1) (q,0) :=
    cell_weight_left even m p q hp
  obtain ⟨rowSmall, colSmall⟩ := point_to_profile w rowSum colSum rightIndependent
  refine ⟨fun p q c => w (p,c) (q,0), rowSmall, colSmall, ordinary, ?_⟩
  suffices coordinate_bound : ∀ i : Fin (n + 2),
      (∑ p : EvenSubset (n + 2), ∑ q : OddSubset (n + 2), ∑ c : Fin 2, ∑ d : Fin 2,
        if i ∈ p.val ∩ q.val then w (p,c) (q,d) % 2 else 0) ≤ z i by
    intro i
    simpa only [rightIndependent, Fin.sum_univ_two, ← two_mul, mul_sum, Nat.mul_add] using coordinate_bound i
  intro i
  let fixedAt (t : Pair n) := Nat.card {s : S // f s = t ∧ generator i • s = s}
  have fixed_total : fixedSeedCount (n := n) S i = ∑ t : Pair n, fixedAt t := by
    unfold fixedSeedCount
    simp_rw [coordinate_fixed_iff_generator]
    exact count_by_point f (fun s => generator i • s = s)
  rw [← counts i, fixed_total]
  rw [Fintype.sum_prod_type]
  rw [← (evenPoint n).sum_comp (fun x => ∑ y, fixedAt (x,y))]
  simp_rw [← (oddPoint n).sum_comp (fun y => fixedAt (_,y)), Fintype.sum_prod_type]
  simp_rw [sum_comm (s := (univ : Finset (Fin 2))) (t := (univ : Finset (OddSubset (n + 2))))]
  apply sum_le_sum
  intro p _
  apply sum_le_sum
  intro q _
  apply sum_le_sum
  intro c _
  apply sum_le_sum
  intro d _
  change (if i ∈ p.val ∩ q.val then w (p,c) (q,d) % 2 else 0) ≤
    Nat.card {s : S // f s = point (p,c) (q,d) ∧ generator i • s = s}
  rw [fixed]
  by_cases mem : i ∈ p.val ∩ q.val
  · have hfix : generator i • point (p,c) (q,d) = point (p,c) (q,d) := by
      rw [← coordinate_fixed_iff_generator, pair_fixed_coordinate]
      exact ⟨(colouredSlice_profile (by decide : 0 < 2) (p,c) i).mpr (mem_inter.mp mem).1,
          (colouredSlice_profile (by decide : 1 < 2) (q,d) i).mpr (mem_inter.mp mem).2⟩
    rw [ite_eq_left mem, ite_eq_left hfix]
    change m (Quotient.mk'' (point (p,c) (q,d))) % 2 ≤ _
    rw [← parity]
    exact Nat.mod_le _ _
  · simp [mem]


end
end
end D5.S3.ConceptDynamics.Attribution.ParityColouredTableExtraction
