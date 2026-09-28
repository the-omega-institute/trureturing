/- GID: D5/S3/Observer/Separation/MissingRowWidthAmplifier
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/MissingRowWidthAmplifier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fixed surjective component with no surjective row admits Boolean tasks with unbounded normalized-to-original width ratios. -/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/- The four coordinates are labelled a, b, x, y. The rho order is (a,b,x,y),
   and pi is the coordinate permutation (x,a,b,y). Each map below fixes exactly
   its prefix and retains one common, labelled product for all suffixes at that
   layer. The empty suffix is Unit, so terminal responses are functions on Unit,
   and its two constant Boolean functions remain distinct.

   Writing A = B = (Z → ZMod m), the fixed prefix | suffix products are:
     rho: Unit | A×B×X×Y; A | B×X×Y; A×B | X×Y; A×B×X | Y;
          A×B×X×Y | Unit.
     pi:  Unit | X×A×B×Y; X | A×B×Y; X×A | B×Y; X×A×B | Y;
          X×A×B×Y | Unit.
   Products associate to the right. The full-input bijection sends (x,a,b,y)
   to (a,b,x,y), with inverse (a,b,x,y) ↦ (x,a,b,y). Both full maps evaluate
   exactly task φ m a b x y by definition; no dependent-coordinate transport
   theorem is assumed. Factor maps later in the proof retain these same suffix
   labels, even when prefixes come from different, intersecting row images. -/
namespace D5.S3.Observer.Separation.MissingRowWidthAmplifier

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

abbrev Table (Z : Type u) (m : ℕ) := Z → ZMod m

def task (φ : X × Y → Z) (m : ℕ) (a b : Table Z m) (x : X) (y : Y) : Bool :=
  decide (a (φ (x, y)) + b (φ (x, y)) = 0)

def rho0 (φ : X × Y → Z) (m : ℕ) :
    Unit → (Table Z m × Table Z m × X × Y) → Bool :=
  fun _ p => task φ m p.1 p.2.1 p.2.2.1 p.2.2.2

def rho1 (φ : X × Y → Z) (m : ℕ) :
    Table Z m → (Table Z m × X × Y) → Bool :=
  fun a p => task φ m a p.1 p.2.1 p.2.2

def rho2 (φ : X × Y → Z) (m : ℕ) :
    (Table Z m × Table Z m) → (X × Y) → Bool :=
  fun p q => task φ m p.1 p.2 q.1 q.2

def rho3 (φ : X × Y → Z) (m : ℕ) :
    (Table Z m × Table Z m × X) → Y → Bool :=
  fun p y => task φ m p.1 p.2.1 p.2.2 y

def rho4 (φ : X × Y → Z) (m : ℕ) :
    (Table Z m × Table Z m × X × Y) → Unit → Bool :=
  fun p _ => task φ m p.1 p.2.1 p.2.2.1 p.2.2.2

def pi0 (φ : X × Y → Z) (m : ℕ) :
    Unit → (X × Table Z m × Table Z m × Y) → Bool :=
  fun _ p => task φ m p.2.1 p.2.2.1 p.1 p.2.2.2

def pi1 (φ : X × Y → Z) (m : ℕ) :
    X → (Table Z m × Table Z m × Y) → Bool :=
  fun x p => task φ m p.1 p.2.1 x p.2.2

def pi2 (φ : X × Y → Z) (m : ℕ) :
    (X × Table Z m) → (Table Z m × Y) → Bool :=
  fun p q => task φ m p.2 q.1 p.1 q.2

def pi3 (φ : X × Y → Z) (m : ℕ) :
    (X × Table Z m × Table Z m) → Y → Bool :=
  fun p y => task φ m p.2.1 p.2.2 p.1 y

def pi4 (φ : X × Y → Z) (m : ℕ) :
    (X × Table Z m × Table Z m × Y) → Unit → Bool :=
  fun p _ => task φ m p.2.1 p.2.2.1 p.1 p.2.2.2

noncomputable def capacity {P S : Type*} (f : P → S → Bool) : ℕ :=
  Nat.card (Set.range f)

noncomputable def rhoCapacity (φ : X × Y → Z) (m : ℕ) : Fin 5 → ℕ :=
  ![capacity (rho0 φ m), capacity (rho1 φ m), capacity (rho2 φ m),
    capacity (rho3 φ m), capacity (rho4 φ m)]

noncomputable def piCapacity (φ : X × Y → Z) (m : ℕ) : Fin 5 → ℕ :=
  ![capacity (pi0 φ m), capacity (pi1 φ m), capacity (pi2 φ m),
    capacity (pi3 φ m), capacity (pi4 φ m)]

noncomputable def rhoWidth (φ : X × Y → Z) (m : ℕ) : ℕ :=
  Finset.univ.sup (rhoCapacity φ m)

noncomputable def piWidth (φ : X × Y → Z) (m : ℕ) : ℕ :=
  Finset.univ.sup (piCapacity φ m)

def Row (φ : X × Y → Z) (x : X) := Set.range (fun y => φ (x, y))
noncomputable def rowSize (φ : X × Y → Z) (x : X) : ℕ := Nat.card (Row φ x)
noncomputable def maxRow [Fintype X] (φ : X × Y → Z) : ℕ :=
  Finset.univ.sup (rowSize φ)

/-- The full no-surjective-row Boolean amplifier, with all five actual raw layers,
    every integer alphabet size above |X|, and unbounded ratios for the same φ. -/
theorem missing_row_width_amplifier
    [Fintype X] [Fintype Y] [Fintype Z] [Nonempty X] [Nonempty Y] [Nonempty Z]
    (φ : X × Y → Z) (hφ : Function.Surjective φ)
    (hrow : ∀ x, ¬ Function.Surjective (fun y => φ (x, y))) :
    (∀ x, 1 ≤ rowSize φ x ∧ rowSize φ x < Nat.card Z) ∧
    maxRow φ < Nat.card Z ∧
    (∀ m : ℕ, Nat.card X < m →
      rhoCapacity φ m 0 = 1 ∧ piCapacity φ m 0 = 1 ∧
      rhoCapacity φ m 1 = m ^ Nat.card Z ∧
      rhoCapacity φ m 2 ≤ 2 ^ Nat.card Z ∧
      rhoCapacity φ m 3 ≤ ∑ x, 2 ^ rowSize φ x ∧
      rhoCapacity φ m 4 = 2 ∧
      piCapacity φ m 1 ≤ Nat.card X ∧
      piCapacity φ m 2 ≤ ∑ x, m ^ rowSize φ x ∧
      piCapacity φ m 3 ≤ ∑ x, m ^ rowSize φ x ∧
      piCapacity φ m 4 = 2 ∧
      rhoWidth φ m = m ^ Nat.card Z ∧
      0 < piWidth φ m ∧
      piWidth φ m ≤ ∑ x, m ^ rowSize φ x ∧
      (∑ x, m ^ rowSize φ x) ≤ Nat.card X * m ^ maxRow φ ∧
      Nat.card X * m ^ maxRow φ < m ^ Nat.card Z ∧
      (m : ℝ) ^ (Nat.card Z - maxRow φ) / (Nat.card X : ℝ) ≤
        (rhoWidth φ m : ℝ) / (piWidth φ m : ℝ)) ∧
    (∀ R : ℝ, ∃ M : ℕ, Nat.card X < M ∧ ∀ m : ℕ, M ≤ m →
      R < (rhoWidth φ m : ℝ) / (piWidth φ m : ℝ)) := by
  classical
  have hxpos : 0 < Nat.card X := Nat.card_pos
  have hzpos : 0 < Nat.card Z := Nat.card_pos
  have rows : ∀ x, 1 ≤ rowSize φ x ∧ rowSize φ x < Nat.card Z := by
    intro x
    let : Nonempty (Row φ x) := ⟨⟨φ (x, Classical.choice inferInstance),
      ⟨Classical.choice inferInstance, rfl⟩⟩⟩
    constructor
    · exact Nat.card_pos
    · change Nat.card (Row φ x) < Nat.card Z
      let : Fintype (Row φ x) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      apply Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
      intro hs
      apply hrow x
      intro z
      obtain ⟨⟨_, y, hy⟩, rfl⟩ := hs z
      exact ⟨y, hy⟩
  have row_le : ∀ x, rowSize φ x ≤ maxRow φ := by
    intro x
    exact Finset.le_sup (f := rowSize φ) (Finset.mem_univ x)
  have hr : maxRow φ < Nat.card Z := by
    apply Finset.sup_lt_iff (by omega) |>.2
    intro x _
    exact (rows x).2
  have per_m : ∀ m : ℕ, Nat.card X < m →
      rhoCapacity φ m 0 = 1 ∧ piCapacity φ m 0 = 1 ∧
      rhoCapacity φ m 1 = m ^ Nat.card Z ∧
      rhoCapacity φ m 2 ≤ 2 ^ Nat.card Z ∧
      rhoCapacity φ m 3 ≤ ∑ x, 2 ^ rowSize φ x ∧
      rhoCapacity φ m 4 = 2 ∧
      piCapacity φ m 1 ≤ Nat.card X ∧
      piCapacity φ m 2 ≤ ∑ x, m ^ rowSize φ x ∧
      piCapacity φ m 3 ≤ ∑ x, m ^ rowSize φ x ∧
      piCapacity φ m 4 = 2 ∧
      rhoWidth φ m = m ^ Nat.card Z ∧
      0 < piWidth φ m ∧
      piWidth φ m ≤ ∑ x, m ^ rowSize φ x ∧
      (∑ x, m ^ rowSize φ x) ≤ Nat.card X * m ^ maxRow φ ∧
      Nat.card X * m ^ maxRow φ < m ^ Nat.card Z ∧
      (m : ℝ) ^ (Nat.card Z - maxRow φ) / (Nat.card X : ℝ) ≤
        (rhoWidth φ m : ℝ) / (piWidth φ m : ℝ) := by
    intro m hm
    have hm2 : 2 ≤ m := by omega
    have hmpos : 0 < m := by omega
    let : NeZero m := ⟨by omega⟩
    have hm1 : 1 < m := by omega
    let : Fact (1 < m) := ⟨hm1⟩
    have card_table : Nat.card (Table Z m) = m ^ Nat.card Z := by
      simp [Table]
    have card_row : Nat.card (Σ x, Row φ x → ZMod m) = ∑ x, m ^ rowSize φ x := by
      simp [rowSize]
    have card_bool_row : Nat.card (Σ x, Row φ x → Bool) = ∑ x, 2 ^ rowSize φ x := by
      simp [rowSize, Nat.card_eq_fintype_card]
    have c0rho : capacity (rho0 φ m) = 1 := by
      rw [capacity, Nat.card_range_of_injective (f := rho0 φ m)]
      · simp [Nat.card_eq_fintype_card]
      · exact fun _ _ _ => Subsingleton.elim _ _
    have c0pi : capacity (pi0 φ m) = 1 := by
      rw [capacity, Nat.card_range_of_injective (f := pi0 φ m)]
      · simp [Nat.card_eq_fintype_card]
      · exact fun _ _ _ => Subsingleton.elim _ _
    have inject_a : Function.Injective (rho1 φ m) := by
      intro a a' heq
      funext z
      obtain ⟨⟨x, y⟩, hxy⟩ := hφ z
      have he := congrFun heq ((fun z => -a z), x, y)
      have hz : decide (a' z + -a z = 0) = true := by
        simpa [rho1, task, hxy] using he.symm
      have hh : a' z + -a z = 0 := of_decide_eq_true hz
      exact (add_neg_eq_zero.mp hh).symm
    have c1rho : capacity (rho1 φ m) = m ^ Nat.card Z := by
      rw [capacity, Nat.card_range_of_injective inject_a, card_table]
    have c1pi : capacity (pi1 φ m) ≤ Nat.card X :=
      Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := pi1 φ m))
    have c2rho : capacity (rho2 φ m) ≤ 2 ^ Nat.card Z := by
      let g : (Z → Bool) → (X × Y → Bool) := fun t p => t (φ p)
      have hs : Set.range (rho2 φ m) ⊆ Set.range g := by
        rintro _ ⟨⟨a, b⟩, rfl⟩
        exact ⟨fun z => decide (a z + b z = 0), rfl⟩
      calc
        capacity (rho2 φ m) ≤ Nat.card (Set.range g) :=
          Nat.card_mono (Set.finite_range g) hs
        _ ≤ Nat.card (Z → Bool) :=
          Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
        _ = 2 ^ Nat.card Z := by simp [Nat.card_eq_fintype_card]
    have c3rho : capacity (rho3 φ m) ≤ ∑ x, 2 ^ rowSize φ x := by
      let g : (Σ x, Row φ x → Bool) → Y → Bool :=
        fun p y => p.2 ⟨φ (p.1, y), ⟨y, rfl⟩⟩
      have hs : Set.range (rho3 φ m) ⊆ Set.range g := by
        rintro _ ⟨⟨a, b, x⟩, rfl⟩
        exact ⟨⟨x, fun z => decide (a z + b z = 0)⟩, rfl⟩
      calc
        capacity (rho3 φ m) ≤ Nat.card (Set.range g) :=
          Nat.card_mono (Set.finite_range g) hs
        _ ≤ Nat.card (Σ x, Row φ x → Bool) :=
          Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
        _ = _ := card_bool_row
    have c2pi : capacity (pi2 φ m) ≤ ∑ x, m ^ rowSize φ x := by
      let g : (Σ x, Row φ x → ZMod m) → (Table Z m × Y) → Bool :=
        fun p q => decide (p.2 ⟨φ (p.1, q.2), ⟨q.2, rfl⟩⟩ + q.1 (φ (p.1, q.2)) = 0)
      have hs : Set.range (pi2 φ m) ⊆ Set.range g := by
        rintro _ ⟨⟨x, a⟩, rfl⟩
        exact ⟨⟨x, fun z => a z⟩, rfl⟩
      calc
        capacity (pi2 φ m) ≤ Nat.card (Set.range g) :=
          Nat.card_mono (Set.finite_range g) hs
        _ ≤ Nat.card (Σ x, Row φ x → ZMod m) :=
          Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
        _ = _ := card_row
    have c3pi : capacity (pi3 φ m) ≤ ∑ x, m ^ rowSize φ x := by
      let g : (Σ x, Row φ x → ZMod m) → Y → Bool :=
        fun p y => decide (p.2 ⟨φ (p.1, y), ⟨y, rfl⟩⟩ = 0)
      have hs : Set.range (pi3 φ m) ⊆ Set.range g := by
        rintro _ ⟨⟨x, a, b⟩, rfl⟩
        exact ⟨⟨x, fun z => a z + b z⟩, rfl⟩
      calc
        capacity (pi3 φ m) ≤ Nat.card (Set.range g) :=
          Nat.card_mono (Set.finite_range g) hs
        _ ≤ Nat.card (Σ x, Row φ x → ZMod m) :=
          Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
        _ = _ := card_row
    have c4rho : capacity (rho4 φ m) = 2 := by
      have hs : Function.Surjective (rho4 φ m) := by
        intro f
        let x : X := Classical.choice inferInstance
        let y : Y := Classical.choice inferInstance
        cases hf : f ()
        · refine ⟨((fun _ => 0), (fun _ => 1), x, y), ?_⟩
          funext u
          cases u
          simp [rho4, task, hf]
        · refine ⟨((fun _ => 0), (fun _ => 0), x, y), ?_⟩
          funext u
          cases u
          simp [rho4, task, hf]
      rw [capacity, hs.range_eq, Nat.card_univ]
      simp [Nat.card_eq_fintype_card]
    have c4pi : capacity (pi4 φ m) = 2 := by
      have hs : Set.range (pi4 φ m) = Set.range (rho4 φ m) := by
        ext f
        constructor
        · rintro ⟨⟨x, a, b, y⟩, rfl⟩
          exact ⟨(a, b, x, y), rfl⟩
        · rintro ⟨⟨a, b, x, y⟩, rfl⟩
          exact ⟨(x, a, b, y), rfl⟩
      simpa [capacity, hs] using c4rho
    have hsum : (∑ x, m ^ rowSize φ x) ≤ Nat.card X * m ^ maxRow φ := by
      calc
        _ ≤ ∑ _x : X, m ^ maxRow φ :=
          Finset.sum_le_sum fun x _ => Nat.pow_le_pow_right hmpos (row_le x)
        _ = _ := by simp [Nat.card_eq_fintype_card]
    have hstrict : Nat.card X * m ^ maxRow φ < m ^ Nat.card Z := by
      calc
        Nat.card X * m ^ maxRow φ < m * m ^ maxRow φ :=
          Nat.mul_lt_mul_of_pos_right hm (pow_pos hmpos _)
        _ = m ^ (maxRow φ + 1) := by rw [pow_succ, Nat.mul_comm]
        _ ≤ m ^ Nat.card Z := Nat.pow_le_pow_right hmpos hr
    have hm_sum : m ≤ ∑ x, m ^ rowSize φ x := by
      let x : X := Classical.choice inferInstance
      calc
        m = m ^ 1 := (pow_one m).symm
        _ ≤ m ^ rowSize φ x := Nat.pow_le_pow_right hmpos (rows x).1
        _ ≤ ∑ x, m ^ rowSize φ x := Finset.single_le_sum (f := fun x : X => m ^ rowSize φ x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    have h2d : 2 ≤ m ^ Nat.card Z := by
      calc
        2 ≤ m := hm2
        _ = m ^ 1 := (pow_one m).symm
        _ ≤ m ^ Nat.card Z := Nat.pow_le_pow_right hmpos hzpos
    have hboolsum : (∑ x, 2 ^ rowSize φ x) ≤ ∑ x, m ^ rowSize φ x :=
      Finset.sum_le_sum fun x _ => Nat.pow_le_pow_left hm2 _
    have wrho : rhoWidth φ m = m ^ Nat.card Z := by
      apply le_antisymm
      · apply Finset.sup_le
        intro i _
        fin_cases i
        · change capacity (rho0 φ m) ≤ _
          rw [c0rho]
          omega
        · exact c1rho.le
        · exact c2rho.trans (Nat.pow_le_pow_left hm2 _)
        · exact c3rho.trans (hboolsum.trans (hsum.trans hstrict.le))
        · change capacity (rho4 φ m) ≤ _
          rw [c4rho]
          exact h2d
      · exact c1rho ▸ Finset.le_sup (f := rhoCapacity φ m) (Finset.mem_univ (1 : Fin 5))
    have wpi : piWidth φ m ≤ ∑ x, m ^ rowSize φ x := by
      apply Finset.sup_le
      intro i _
      fin_cases i
      · change capacity (pi0 φ m) ≤ _
        rw [c0pi]
        omega
      · exact c1pi.trans (by omega)
      · exact c2pi
      · exact c3pi
      · change capacity (pi4 φ m) ≤ _
        rw [c4pi]
        omega
    have wpipos : 0 < piWidth φ m := by
      have h := Finset.le_sup (f := piCapacity φ m) (Finset.mem_univ (0 : Fin 5))
      change capacity (pi0 φ m) ≤ piWidth φ m at h
      omega
    have ratio : (m : ℝ) ^ (Nat.card Z - maxRow φ) / (Nat.card X : ℝ) ≤
        (rhoWidth φ m : ℝ) / (piWidth φ m : ℝ) := by
      have hxR : (0 : ℝ) < Nat.card X := by exact_mod_cast hxpos
      have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
      have hpR : (0 : ℝ) < piWidth φ m := by exact_mod_cast wpipos
      have hwR : (piWidth φ m : ℝ) ≤ (Nat.card X : ℝ) * (m : ℝ) ^ maxRow φ := by
        exact_mod_cast wpi.trans hsum
      rw [wrho, Nat.cast_pow]
      apply (div_le_div_iff₀ hxR hpR).2
      calc
        (m : ℝ) ^ (Nat.card Z - maxRow φ) * (piWidth φ m : ℝ) ≤
            (m : ℝ) ^ (Nat.card Z - maxRow φ) * ((Nat.card X : ℝ) * (m : ℝ) ^ maxRow φ) :=
          mul_le_mul_of_nonneg_left hwR (by positivity)
        _ = (m : ℝ) ^ Nat.card Z * (Nat.card X : ℝ) := by
          rw [← mul_assoc, mul_right_comm, ← pow_add, Nat.sub_add_cancel hr.le]
    exact ⟨c0rho, c0pi, c1rho, c2rho, c3rho, c4rho, c1pi, c2pi, c3pi,
      c4pi, wrho, wpipos, wpi, hsum, hstrict, ratio⟩
  refine ⟨rows, hr, per_m, ?_⟩
  intro R
  obtain ⟨N, hN⟩ := exists_nat_gt (R * (Nat.card X : ℝ))
  refine ⟨max N (Nat.card X + 1), by omega, ?_⟩
  intro m hm
  have hmX : Nat.card X < m := by omega
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hxR : (0 : ℝ) < Nat.card X := by exact_mod_cast hxpos
  have hRm : R * (Nat.card X : ℝ) < (m : ℝ) :=
    hN.trans_le (by exact_mod_cast (show N ≤ m by omega))
  have hm_pow : (m : ℝ) ≤ (m : ℝ) ^ (Nat.card Z - maxRow φ) := by
    calc
      (m : ℝ) = (m : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hm1 (by omega)
  have hb := per_m m hmX
  exact ((lt_div_iff₀ hxR).2 (hRm.trans_le hm_pow)).trans_le
    hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

#print axioms missing_row_width_amplifier
end D5.S3.Observer.Separation.MissingRowWidthAmplifier
