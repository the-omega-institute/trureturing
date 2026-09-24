/- GID: D5/S0/FiniteGeometry/SylvesterSimplexEhrhartNonpositivity
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/SylvesterSimplexEhrhartNonpositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Source-faithful lattice-count semantics for Sylvester simplex nonpositivity. -/

import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic.Linarith

open Set
open scoped Pointwise

noncomputable section

namespace D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

/-- The source indexing starts with `s₀ = 1`, `s₁ = 2`. -/
def sylvester : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => sylvester (n + 1) * (sylvester (n + 1) - 1) + 1

private lemma sylvester_pos (n : ℕ) : 0 < sylvester n := by
  rcases n with _ | _ | n <;> simp [sylvester]

private lemma two_le_sylvester (n : ℕ) (hn : 1 ≤ n) : 2 ≤ sylvester n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | n
      · omega
      · simp [sylvester]
      · have hprev : 2 ≤ sylvester (n + 1) := ih (n + 1) (by omega) (by omega)
        have hmul : 0 < sylvester (n + 1) * (sylvester (n + 1) - 1) :=
          Nat.mul_pos (by omega) (by omega)
        simp only [sylvester]
        omega

private lemma sylvester_sub_one_eq_prod (d : ℕ) (hd : 1 ≤ d) :
    sylvester d - 1 = ∏ i ∈ Finset.range d, sylvester i := by
  induction d, hd using Nat.le_induction with
  | base => simp [sylvester]
  | succ d hd ih =>
      rw [Finset.prod_range_succ, ← ih]
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
      simp [sylvester, Nat.mul_comm]

/-- The coordinate length in the literal source simplex. -/
def axisScale (d k : ℕ) (i : Fin d) : ℕ :=
  if i.val + 1 = d then (k + 1) * (sylvester d - 1) else sylvester (i.val + 1)

private lemma axisScale_pos (d k : ℕ) (i : Fin d) : 0 < axisScale d k i := by
  rw [axisScale]
  split_ifs with hi
  · apply Nat.mul_pos (Nat.succ_pos k)
    apply Nat.sub_pos_of_lt
    exact lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d (by omega))
  · exact sylvester_pos (i.val + 1)

/-- The `i`th axis vertex of the literal source simplex. -/
def axisVertex (d k : ℕ) (i : Fin d) : Fin d → ℝ :=
  Pi.single i (axisScale d k i : ℝ)

/-- The literal vertex set
`{0, s₁e₁, ..., s_(d-1)e_(d-1), (k+1)(s_d-1)e_d}`. -/
def sourceVertices (d k : ℕ) : Set (Fin d → ℝ) :=
  insert 0 (range (axisVertex d k))

/-- The actual convex hull from Conjecture 6.6. -/
def sourceSimplex (d k : ℕ) : Set (Fin d → ℝ) :=
  convexHull ℝ (sourceVertices d k)

/-- Natural dilation of the actual convex hull. -/
def sourceDilation (d k t : ℕ) : Set (Fin d → ℝ) :=
  (t : ℝ) • sourceSimplex d k

/-- Coordinatewise embedding of an integer lattice point into real space. -/
def latticeEmbedding {d : ℕ} (p : Fin d → ℤ) : Fin d → ℝ :=
  fun i => (p i : ℝ)

/-- Integer points in the actual dilated convex hull. -/
def latticePointSet (d k t : ℕ) : Set (Fin d → ℤ) :=
  {p | latticeEmbedding p ∈ sourceDilation d k t}

/-- Actual lattice-point count. Finiteness for every dilation is a later proof obligation. -/
def ehrhartCount (d k t : ℕ) : ℕ :=
  (latticePointSet d k t).ncard

private lemma mem_diagonal_simplex_iff {d : ℕ} (a : Fin d → ℝ)
    (ha : ∀ i, 0 < a i) (x : Fin d → ℝ) :
    x ∈ convexHull ℝ (insert 0 (range fun i => Pi.single i (a i))) ↔
      (∀ i, 0 ≤ x i) ∧ ∑ i, x i / a i ≤ 1 := by
  classical
  constructor
  · apply convexHull_min
    · rintro y (rfl | ⟨i, rfl⟩)
      · constructor
        · intro i
          exact le_rfl
        · simp
      · constructor
        · intro j
          simp only [Pi.single_apply]
          split_ifs
          · exact (ha i).le
          · exact le_rfl
        · simp only [Pi.single_apply, ite_div, zero_div]
          rw [Finset.sum_ite_eq']
          simp [ha i |>.ne']
    · intro y hy z hz u v hu hv huv
      constructor
      · intro i
        simp only [Pi.add_apply, Pi.smul_apply]
        exact add_nonneg (mul_nonneg hu (hy.1 i)) (mul_nonneg hv (hz.1 i))
      · simp_rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_div, mul_div_assoc]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        nlinarith [hy.2, hz.2]
  · rintro ⟨hx, hsum⟩
    let w : Option (Fin d) → ℝ
      | none => 1 - ∑ i, x i / a i
      | some i => x i / a i
    let z : Option (Fin d) → (Fin d → ℝ)
      | none => 0
      | some i => Pi.single i (a i)
    apply mem_convexHull_of_exists_fintype w z
    · intro i
      cases i with
      | none => exact sub_nonneg.mpr hsum
      | some i => exact div_nonneg (hx i) (ha i).le
    · simp [w]
    · intro i
      cases i with
      | none => exact mem_insert _ _
      | some i => exact mem_insert_of_mem _ (mem_range_self i)
    · funext j
      simp [w, z, Finset.sum_apply, Pi.single_apply, ha j |>.ne']

private lemma mem_sourceSimplex_iff (d k : ℕ) (x : Fin d → ℝ) :
    x ∈ sourceSimplex d k ↔
      (∀ i, 0 ≤ x i) ∧ ∑ i, x i / (axisScale d k i : ℝ) ≤ 1 := by
  unfold sourceSimplex sourceVertices axisVertex
  apply mem_diagonal_simplex_iff
  intro i
  exact_mod_cast axisScale_pos d k i

private lemma zero_mem_sourceSimplex (d k : ℕ) :
    (0 : Fin d → ℝ) ∈ sourceSimplex d k := by
  apply subset_convexHull ℝ
  exact mem_insert _ _

private lemma sourceDilation_zero (d k : ℕ) :
    sourceDilation d k 0 = {(0 : Fin d → ℝ)} := by
  have hnonempty : (sourceSimplex d k).Nonempty :=
    ⟨0, zero_mem_sourceSimplex d k⟩
  simpa only [sourceDilation, Nat.cast_zero, Set.singleton_zero] using
    (Set.zero_smul_set (α := ℝ) hnonempty)

private lemma latticeEmbedding_eq_zero_iff {d : ℕ} (p : Fin d → ℤ) :
    latticeEmbedding p = 0 ↔ p = 0 := by
  constructor
  · intro hp
    funext i
    have hi := congrFun hp i
    have hi' : (p i : ℝ) = 0 := by
      simpa [latticeEmbedding] using hi
    exact Int.cast_eq_zero.mp hi'
  · intro hp
    subst p
    ext i
    simp [latticeEmbedding]

private lemma latticePointSet_zero (d k : ℕ) :
    latticePointSet d k 0 = {(0 : Fin d → ℤ)} := by
  ext p
  change latticeEmbedding p ∈ sourceDilation d k 0 ↔ p = 0
  rw [sourceDilation_zero]
  exact latticeEmbedding_eq_zero_iff p

private lemma latticePointSet_finite (d k t : ℕ) :
    (latticePointSet d k t).Finite := by
  let upper : Fin d → ℤ := fun i => (t * axisScale d k i : ℕ)
  apply (Set.Finite.pi' (fun i => Set.finite_Icc (0 : ℤ) (upper i))).subset
  intro p hp i
  change latticeEmbedding p ∈ (t : ℝ) • sourceSimplex d k at hp
  rcases Set.mem_smul_set.mp hp with ⟨y, hy, hpy⟩
  have hy' := (mem_sourceSimplex_iff d k y).mp hy
  have hscale : 0 < (axisScale d k i : ℝ) := by
    exact_mod_cast axisScale_pos d k i
  have hterm : y i / (axisScale d k i : ℝ) ≤
      ∑ j, y j / (axisScale d k j : ℝ) := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j => y j / (axisScale d k j : ℝ)) (fun j _ =>
        div_nonneg (hy'.1 j) (by exact_mod_cast (axisScale_pos d k j).le))
      (Finset.mem_univ i)
  have hy_le : y i ≤ (axisScale d k i : ℝ) :=
    (div_le_one hscale).mp (hterm.trans hy'.2)
  have hcoord := congrFun hpy i
  have hp_real : (p i : ℝ) = (t : ℝ) * y i := by
    simpa [latticeEmbedding, smul_eq_mul] using hcoord.symm
  constructor
  · have hreal : (0 : ℝ) ≤ (p i : ℝ) := by
      rw [hp_real]
      exact mul_nonneg (Nat.cast_nonneg t) (hy'.1 i)
    exact_mod_cast hreal
  · have hreal : (p i : ℝ) ≤ (t : ℝ) * (axisScale d k i : ℝ) := by
      rw [hp_real]
      exact mul_le_mul_of_nonneg_left hy_le (Nat.cast_nonneg t)
    change p i ≤ (t * axisScale d k i : ℕ)
    exact_mod_cast hreal

private lemma mem_latticePointSet_iff (d k t : ℕ) (p : Fin d → ℤ) :
    p ∈ latticePointSet d k t ↔
      (∀ i, 0 ≤ p i) ∧
        ∑ i, (p i : ℝ) / (axisScale d k i : ℝ) ≤ t := by
  classical
  cases t with
  | zero =>
      constructor
      · intro hp
        rw [latticePointSet_zero] at hp
        have hp0 : p = 0 := Set.mem_singleton_iff.mp hp
        subst p
        simp
      · rintro ⟨hp_nonneg, hsum⟩
        have hp0 : p = 0 := by
          funext i
          have hscale : 0 < (axisScale d k i : ℝ) := by
            exact_mod_cast axisScale_pos d k i
          have hterm_nonneg : 0 ≤ (p i : ℝ) / (axisScale d k i : ℝ) :=
            div_nonneg (by exact_mod_cast hp_nonneg i) hscale.le
          have hterm_le_sum : (p i : ℝ) / (axisScale d k i : ℝ) ≤
              ∑ j, (p j : ℝ) / (axisScale d k j : ℝ) := by
            exact Finset.single_le_sum (s := Finset.univ)
              (f := fun j => (p j : ℝ) / (axisScale d k j : ℝ)) (fun j _ =>
                div_nonneg (by exact_mod_cast hp_nonneg j) (by
                  exact_mod_cast (axisScale_pos d k j).le)) (Finset.mem_univ i)
          have hterm_zero : (p i : ℝ) / (axisScale d k i : ℝ) = 0 := by
            apply le_antisymm
            · exact hterm_le_sum.trans (by simpa using hsum)
            · exact hterm_nonneg
          have hp_real : (p i : ℝ) = 0 := (div_eq_zero_iff).mp hterm_zero |>.resolve_right
            (by exact_mod_cast (axisScale_pos d k i).ne')
          exact_mod_cast hp_real
        rw [hp0, latticePointSet_zero]
        exact Set.mem_singleton 0
  | succ t =>
      let T : ℝ := (t + 1 : ℕ)
      have hT : 0 < T := by
        dsimp [T]
        positivity
      constructor
      · intro hp
        change latticeEmbedding p ∈ T • sourceSimplex d k at hp
        rcases Set.mem_smul_set.mp hp with ⟨y, hy, hpy⟩
        have hy' := (mem_sourceSimplex_iff d k y).mp hy
        have hcoord (i : Fin d) : (p i : ℝ) = T * y i := by
          have hi := congrFun hpy i
          simpa [T, latticeEmbedding, smul_eq_mul] using hi.symm
        constructor
        · intro i
          have hreal : (0 : ℝ) ≤ (p i : ℝ) := by
            rw [hcoord]
            exact mul_nonneg hT.le (hy'.1 i)
          exact_mod_cast hreal
        · simp_rw [hcoord, mul_div_assoc]
          rw [← Finset.mul_sum]
          simpa [T] using mul_le_mul_of_nonneg_left hy'.2 hT.le
      · rintro ⟨hp_nonneg, hsum⟩
        let y : Fin d → ℝ := fun i => (p i : ℝ) / T
        have hsum_y : ∑ i, y i / (axisScale d k i : ℝ) =
            (∑ i, (p i : ℝ) / (axisScale d k i : ℝ)) / T := by
          calc
            (∑ i, y i / (axisScale d k i : ℝ)) =
                ∑ i, ((p i : ℝ) / (axisScale d k i : ℝ)) / T := by
              apply Finset.sum_congr rfl
              intro i _
              dsimp [y]
              field_simp
            _ = (∑ i, (p i : ℝ) / (axisScale d k i : ℝ)) / T := by
              simp only [div_eq_mul_inv]
              rw [Finset.sum_mul]
        have hy : y ∈ sourceSimplex d k := (mem_sourceSimplex_iff d k y).mpr ⟨by
          intro i
          exact div_nonneg (by exact_mod_cast hp_nonneg i) hT.le, by
          rw [hsum_y]
          exact (div_le_one hT).mpr (by simpa [T] using hsum)⟩
        change latticeEmbedding p ∈ T • sourceSimplex d k
        apply Set.mem_smul_set.mpr
        refine ⟨y, hy, ?_⟩
        funext i
        change T * ((p i : ℝ) / T) = (p i : ℝ)
        exact mul_div_cancel₀ (p i : ℝ) hT.ne'

private def baseWeight (d : ℕ) (i : Fin d) : ℕ :=
  (sylvester d - 1) / axisScale d 0 i

private def integerWeightedMass (d : ℕ) (p : Fin d → ℤ) : ℤ :=
  ∑ i, p i * (baseWeight d i : ℤ)

private lemma base_axisScale_dvd_mass (d : ℕ) (hd : 1 ≤ d) (i : Fin d) :
    axisScale d 0 i ∣ sylvester d - 1 := by
  by_cases hi : i.val + 1 = d
  · simp [axisScale, hi]
  · rw [axisScale, if_neg hi, sylvester_sub_one_eq_prod d hd]
    apply Finset.dvd_prod_of_mem
    simp only [Finset.mem_range]
    omega

private lemma baseWeight_cast (d : ℕ) (hd : 1 ≤ d) (i : Fin d) :
    (baseWeight d i : ℝ) =
      (sylvester d - 1 : ℕ) / (axisScale d 0 i : ℕ) := by
  rw [baseWeight, Nat.cast_div (base_axisScale_dvd_mass d hd i)]
  exact_mod_cast (axisScale_pos d 0 i).ne'

private lemma real_coordinate_sum_eq_weighted_mass (d : ℕ) (hd : 1 ≤ d)
    (p : Fin d → ℤ) :
    ∑ i, (p i : ℝ) / (axisScale d 0 i : ℝ) =
      (integerWeightedMass d p : ℝ) / (sylvester d - 1 : ℕ) := by
  rw [integerWeightedMass, Int.cast_sum]
  have hmass : ((sylvester d - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt
      (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd))).ne'
  apply (eq_div_iff hmass).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Int.cast_mul, Int.cast_natCast, baseWeight_cast d hd i]
  have hscale : (axisScale d 0 i : ℝ) ≠ 0 := by
    exact_mod_cast (axisScale_pos d 0 i).ne'
  field_simp

private lemma mem_latticePointSet_base_iff_weighted (d t : ℕ) (hd : 1 ≤ d)
    (p : Fin d → ℤ) :
    p ∈ latticePointSet d 0 t ↔
      (∀ i, 0 ≤ p i) ∧
        integerWeightedMass d p ≤ ((t * (sylvester d - 1) : ℕ) : ℤ) := by
  rw [mem_latticePointSet_iff, real_coordinate_sum_eq_weighted_mass d hd p]
  have hmass_nat : 0 < sylvester d - 1 :=
    Nat.sub_pos_of_lt (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd))
  have hmass_real : (0 : ℝ) < (sylvester d - 1 : ℕ) := by
    exact_mod_cast hmass_nat
  constructor
  · rintro ⟨hp, hsum⟩
    refine ⟨hp, ?_⟩
    have hreal := (div_le_iff₀ hmass_real).mp hsum
    exact_mod_cast hreal
  · rintro ⟨hp, hmass⟩
    refine ⟨hp, ?_⟩
    apply (div_le_iff₀ hmass_real).mpr
    exact_mod_cast hmass

private lemma mem_latticePointSet_base_iff_unique_slack (d t : ℕ) (hd : 1 ≤ d)
    (p : Fin d → ℤ) :
    p ∈ latticePointSet d 0 t ↔
      (∀ i, 0 ≤ p i) ∧ ∃! slack : ℕ,
        integerWeightedMass d p + (slack : ℤ) =
          ((t * (sylvester d - 1) : ℕ) : ℤ) := by
  rw [mem_latticePointSet_base_iff_weighted d t hd p]
  constructor
  · rintro ⟨hp, hmass⟩
    refine ⟨hp, ?_⟩
    let target : ℤ := ((t * (sylvester d - 1) : ℕ) : ℤ)
    let slack : ℕ := (target - integerWeightedMass d p).toNat
    have hdiff : 0 ≤ target - integerWeightedMass d p := sub_nonneg.mpr hmass
    have hslack : integerWeightedMass d p + (slack : ℤ) = target := by
      dsimp [slack]
      rw [Int.toNat_of_nonneg hdiff]
      ring
    refine ⟨slack, by simpa [target] using hslack, ?_⟩
    intro other hother
    have hother' : integerWeightedMass d p + (other : ℤ) = target := by
      simpa [target] using hother
    have heq : (slack : ℤ) = (other : ℤ) := by linarith
    exact_mod_cast heq.symm
  · rintro ⟨hp, slack, hslack, _⟩
    refine ⟨hp, ?_⟩
    have hnonneg : (0 : ℤ) ≤ (slack : ℤ) := by positivity
    linarith

private def naturalWeightedMass (d : ℕ) (x : Fin d → ℕ) : ℕ :=
  ∑ i, x i * baseWeight d i

private def IsBaseSolution (d t : ℕ) (x : (Fin d → ℕ) × ℕ) : Prop :=
  naturalWeightedMass d x.1 + x.2 = t * (sylvester d - 1)

private lemma integerWeightedMass_eq_natural (d : ℕ) (p : Fin d → ℤ)
    (hp : ∀ i, 0 ≤ p i) :
    integerWeightedMass d p =
      (naturalWeightedMass d (fun i => (p i).toNat) : ℤ) := by
  unfold integerWeightedMass naturalWeightedMass
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_mul, Int.toNat_of_nonneg (hp i)]

private lemma mem_latticePointSet_base_iff_unique_solution (d t : ℕ) (hd : 1 ≤ d)
    (p : Fin d → ℤ) :
    p ∈ latticePointSet d 0 t ↔
      ∃! x : (Fin d → ℕ) × ℕ,
        (∀ i, p i = (x.1 i : ℤ)) ∧ IsBaseSolution d t x := by
  constructor
  · intro hp
    rcases (mem_latticePointSet_base_iff_unique_slack d t hd p).mp hp with
      ⟨hp_nonneg, slack, hslack, hslack_unique⟩
    let coords : Fin d → ℕ := fun i => (p i).toNat
    have hcoords (i : Fin d) : p i = (coords i : ℤ) := by
      exact (Int.toNat_of_nonneg (hp_nonneg i)).symm
    have hmass : integerWeightedMass d p = (naturalWeightedMass d coords : ℤ) := by
      simpa [coords] using integerWeightedMass_eq_natural d p hp_nonneg
    have hsolution : IsBaseSolution d t (coords, slack) := by
      unfold IsBaseSolution
      exact_mod_cast (show (naturalWeightedMass d coords : ℤ) + (slack : ℤ) =
          ((t * (sylvester d - 1) : ℕ) : ℤ) by simpa [← hmass] using hslack)
    refine ⟨(coords, slack), ⟨hcoords, hsolution⟩, ?_⟩
    rintro ⟨otherCoords, otherSlack⟩ ⟨hotherCoords, hotherSolution⟩
    have hfirst : otherCoords = coords := by
      funext i
      exact_mod_cast (hotherCoords i).symm.trans (hcoords i)
    subst otherCoords
    have hotherSlack : integerWeightedMass d p + (otherSlack : ℤ) =
        ((t * (sylvester d - 1) : ℕ) : ℤ) := by
      rw [hmass]
      exact_mod_cast hotherSolution
    have hsecond : otherSlack = slack := hslack_unique otherSlack hotherSlack
    exact Prod.ext rfl hsecond
  · rintro ⟨⟨coords, slack⟩, ⟨hcoords, hsolution⟩, _⟩
    have hp_nonneg (i : Fin d) : 0 ≤ p i := by
      rw [hcoords i]
      exact Int.natCast_nonneg _
    have hmass : integerWeightedMass d p = (naturalWeightedMass d coords : ℤ) := by
      unfold integerWeightedMass naturalWeightedMass
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoords i, Nat.cast_mul]
    apply (mem_latticePointSet_base_iff_unique_slack d t hd p).mpr
    refine ⟨hp_nonneg, slack, ?_, ?_⟩
    · rw [hmass]
      exact_mod_cast hsolution
    · intro other hother
      have hslack : integerWeightedMass d p + (slack : ℤ) =
          ((t * (sylvester d - 1) : ℕ) : ℤ) := by
        rw [hmass]
        exact_mod_cast hsolution
      have heq : (other : ℤ) = (slack : ℤ) := by linarith
      exact_mod_cast heq

private noncomputable def baseSolutionOfLattice (d t : ℕ) (hd : 1 ≤ d)
    (p : {p // p ∈ latticePointSet d 0 t}) : {x // IsBaseSolution d t x} := by
  let h := (mem_latticePointSet_base_iff_unique_solution d t hd p.val).mp p.property
  exact ⟨h.choose, h.choose_spec.1.2⟩

private def baseLatticeOfSolution (d t : ℕ) (hd : 1 ≤ d)
    (x : {x // IsBaseSolution d t x}) : {p // p ∈ latticePointSet d 0 t} := by
  let p : Fin d → ℤ := fun i => (x.val.1 i : ℤ)
  refine ⟨p, (mem_latticePointSet_base_iff_unique_solution d t hd p).mpr ?_⟩
  refine ⟨x.val, ⟨fun _ => rfl, x.property⟩, ?_⟩
  rintro ⟨otherCoords, otherSlack⟩ ⟨hcoords, hsolution⟩
  have hfirst : otherCoords = x.val.1 := by
    funext i
    have hcast : (x.val.1 i : ℤ) = (otherCoords i : ℤ) := by
      simpa [p] using hcoords i
    exact_mod_cast hcast.symm
  subst otherCoords
  have hxsolution := x.property
  have hsecond : otherSlack = x.val.2 := by
    change naturalWeightedMass d x.val.1 + otherSlack =
      t * (sylvester d - 1) at hsolution
    change naturalWeightedMass d x.val.1 + x.val.2 =
      t * (sylvester d - 1) at hxsolution
    exact Nat.add_left_cancel (hsolution.trans hxsolution.symm)
  exact Prod.ext rfl hsecond

private lemma baseLatticeOfSolution_baseSolutionOfLattice (d t : ℕ) (hd : 1 ≤ d)
    (p : {p // p ∈ latticePointSet d 0 t}) :
    baseLatticeOfSolution d t hd (baseSolutionOfLattice d t hd p) = p := by
  apply Subtype.ext
  funext i
  unfold baseLatticeOfSolution baseSolutionOfLattice
  dsimp only
  let h := (mem_latticePointSet_base_iff_unique_solution d t hd p.val).mp p.property
  exact_mod_cast (h.choose_spec.1.1 i).symm

private lemma baseSolutionOfLattice_baseLatticeOfSolution (d t : ℕ) (hd : 1 ≤ d)
    (x : {x // IsBaseSolution d t x}) :
    baseSolutionOfLattice d t hd (baseLatticeOfSolution d t hd x) = x := by
  apply Subtype.ext
  unfold baseSolutionOfLattice
  dsimp only
  let p := baseLatticeOfSolution d t hd x
  let h := (mem_latticePointSet_base_iff_unique_solution d t hd p.val).mp p.property
  exact (h.choose_spec.2 x.val ⟨fun _ => rfl, x.property⟩).symm

private noncomputable def baseLatticeSolutionEquiv (d t : ℕ) (hd : 1 ≤ d) :
    {p // p ∈ latticePointSet d 0 t} ≃ {x // IsBaseSolution d t x} where
  toFun := baseSolutionOfLattice d t hd
  invFun := baseLatticeOfSolution d t hd
  left_inv := baseLatticeOfSolution_baseSolutionOfLattice d t hd
  right_inv := baseSolutionOfLattice_baseLatticeOfSolution d t hd

private lemma ehrhartCount_base_eq_solution_card (d t : ℕ) (hd : 1 ≤ d) :
    ehrhartCount d 0 t = Nat.card {x // IsBaseSolution d t x} := by
  rw [ehrhartCount, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (baseLatticeSolutionEquiv d t hd)

private lemma ehrhartCount_zero (d k : ℕ) :
    ehrhartCount d k 0 = 1 := by
  rw [ehrhartCount, latticePointSet_zero, Set.ncard_singleton]

private lemma baseWeight_last (n : ℕ) :
    baseWeight (n + 1) (Fin.last n) = 1 := by
  have hM : 0 < sylvester (n + 1) - 1 :=
    Nat.sub_pos_of_lt (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester (n + 1) (by omega)))
  rw [baseWeight]
  simp only [axisScale, Fin.val_last, ↓reduceIte]
  simpa using Nat.div_self hM

private def prefixNaturalMass (n : ℕ) (x : Fin (n + 1) → ℕ) : ℕ :=
  ∑ i : Fin n, x i.castSucc * baseWeight (n + 1) i.castSucc

private lemma naturalWeightedMass_succ (n : ℕ) (x : Fin (n + 1) → ℕ) :
    naturalWeightedMass (n + 1) x = prefixNaturalMass n x + x (Fin.last n) := by
  rw [naturalWeightedMass, Fin.sum_univ_castSucc]
  simp [prefixNaturalMass, baseWeight_last]

private lemma real_prefix_sum_eq_mass (n k : ℕ) (x : Fin (n + 1) → ℕ) :
    ∑ i : Fin n, (x i.castSucc : ℝ) /
        (axisScale (n + 1) k i.castSucc : ℝ) =
      (prefixNaturalMass n x : ℝ) / (sylvester (n + 1) - 1 : ℕ) := by
  have hn : 1 ≤ n + 1 := by omega
  have hM : ((sylvester (n + 1) - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt
      (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester (n + 1) hn))).ne'
  apply (eq_div_iff hM).mpr
  rw [prefixNaturalMass, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_mul, baseWeight_cast (n + 1) hn i.castSucc]
  have hscale : ((axisScale (n + 1) k i.castSucc : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (axisScale_pos (n + 1) k i.castSucc).ne'
  have haxis : axisScale (n + 1) k i.castSucc = axisScale (n + 1) 0 i.castSucc := by
    have hi : i.val ≠ n := by omega
    simp [axisScale, hi]
  rw [haxis]
  field_simp

private lemma real_source_sum_eq_mass (n k : ℕ) (x : Fin (n + 1) → ℕ) :
    ∑ i, (x i : ℝ) / (axisScale (n + 1) k i : ℝ) =
      (((k + 1) * prefixNaturalMass n x + x (Fin.last n) : ℕ) : ℝ) /
        (((k + 1) * (sylvester (n + 1) - 1) : ℕ) : ℝ) := by
  rw [Fin.sum_univ_castSucc, real_prefix_sum_eq_mass]
  have hM : ((sylvester (n + 1) - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt
      (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester (n + 1) (by omega)))).ne'
  have hK : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  simp only [axisScale, Fin.val_last, Nat.add_sub_cancel, if_pos, Nat.cast_add,
    Nat.cast_one, Nat.cast_mul]
  field_simp

private lemma natural_point_mem_source_iff (n k t : ℕ) (x : Fin (n + 1) → ℕ) :
    (fun i => (x i : ℤ)) ∈ latticePointSet (n + 1) k t ↔
      (k + 1) * prefixNaturalMass n x + x (Fin.last n) ≤
        (k + 1) * (t * (sylvester (n + 1) - 1)) := by
  rw [mem_latticePointSet_iff]
  simp only [Int.cast_natCast, Int.natCast_nonneg, forall_const, true_and]
  rw [real_source_sum_eq_mass]
  have hden : (0 : ℝ) < (((k + 1) * (sylvester (n + 1) - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.succ_pos k) (Nat.sub_pos_of_lt
      (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester (n + 1) (by omega))))
  constructor
  · intro h
    have h' := (div_le_iff₀ hden).mp h
    have hn : (k + 1) * prefixNaturalMass n x + x (Fin.last n) ≤
        t * ((k + 1) * (sylvester (n + 1) - 1)) := by exact_mod_cast h'
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hn
  · intro h
    apply (div_le_iff₀ hden).mpr
    have hn : (k + 1) * prefixNaturalMass n x + x (Fin.last n) ≤
        t * ((k + 1) * (sylvester (n + 1) - 1)) := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
    exact_mod_cast hn

/-- The `Mt-1` constituent, written without truncated subtraction.  At `t = 0`
the defining type is empty because its left side is positive. -/
private def IsInteriorShiftSolution (d t : ℕ) (x : (Fin d → ℕ) × ℕ) : Prop :=
  naturalWeightedMass d x.1 + x.2 + 1 = t * (sylvester d - 1)

private lemma no_interior_shift_solution_zero (d : ℕ) :
    IsEmpty {x // IsInteriorShiftSolution d 0 x} := by
  refine ⟨fun x => ?_⟩
  simpa [IsInteriorShiftSolution] using x.property

/-- The colored restricted-partition equation belonging to the actual simplex
whose last axis has length `(k+1)(s_d-1)`. -/
private def IsSourceSolution (n k t : ℕ)
    (x : (Fin (n + 1) → ℕ) × ℕ) : Prop :=
  (k + 1) * prefixNaturalMass n x.1 + x.1 (Fin.last n) + x.2 =
    (k + 1) * (t * (sylvester (n + 1) - 1))

private lemma prefixNaturalMass_update_last (n y : ℕ) (x : Fin (n + 1) → ℕ) :
    prefixNaturalMass n (fun i => if i = Fin.last n then y else x i) =
      prefixNaturalMass n x := by
  apply Finset.sum_congr rfl
  intro i _
  simp [prefixNaturalMass, Fin.castSucc_ne_last]

private lemma source_remainders_mod_eq_zero (n k t : ℕ)
    (x : {x // IsSourceSolution n k t x}) :
    (x.val.1 (Fin.last n) + x.val.2) % (k + 1) = 0 := by
  have hmod := congrArg (fun z => z % (k + 1)) x.property
  simpa [IsSourceSolution, Nat.add_mod] using hmod

private lemma mod_complement_of_add_mod_eq_zero {a b K : ℕ} (hK : 0 < K)
    (ha : a % K ≠ 0) (hsum : (a + b) % K = 0) :
    b % K = K - a % K := by
  rw [Nat.add_mod] at hsum
  have halt : a % K < K := Nat.mod_lt _ hK
  have hblt : b % K < K := Nat.mod_lt _ hK
  have hdiv : K ∣ a % K + b % K := Nat.dvd_iff_mod_eq_zero.mpr hsum
  rcases hdiv with ⟨c, hc⟩
  have hsumPos : 0 < a % K + b % K := by omega
  have hsumLt : a % K + b % K < K + K := by omega
  have hc1 : c = 1 := by nlinarith
  subst c
  omega

private def sourceToLayer (n k t : ℕ) (x : {x // IsSourceSolution n k t x}) :
    {x // IsBaseSolution (n + 1) t x} ⊕
      Fin k × {x // IsInteriorShiftSolution (n + 1) t x} := by
  let K := k + 1
  let last := x.val.1 (Fin.last n)
  let slack := x.val.2
  let coords : Fin (n + 1) → ℕ :=
    fun i => if i = Fin.last n then last / K else x.val.1 i
  by_cases hr : last % K = 0
  · apply Sum.inl
    refine ⟨(coords, slack / K), ?_⟩
    rw [IsBaseSolution, naturalWeightedMass_succ]
    have hK : 0 < K := by omega
    have hlast : last = K * (last / K) := by
      calc
        last = last % K + K * (last / K) := (Nat.mod_add_div last K).symm
        _ = K * (last / K) := by simp [hr]
    have hsource := x.property
    change K * prefixNaturalMass n x.val.1 + last + slack =
      K * (t * (sylvester (n + 1) - 1)) at hsource
    have hsumMod : (last + slack) % K = 0 := by
      simpa [K, last, slack] using source_remainders_mod_eq_zero n k t x
    have hdiv : K ∣ slack := by
      rw [Nat.dvd_iff_mod_eq_zero]
      have hslackMod : slack % K < K := Nat.mod_lt _ hK
      rw [Nat.add_mod, hr, zero_add, Nat.mod_eq_of_lt hslackMod] at hsumMod
      exact hsumMod
    have hslack : slack = K * (slack / K) := by
      exact (Nat.mul_div_cancel' hdiv).symm
    have hprefix : prefixNaturalMass n coords = prefixNaturalMass n x.val.1 := by
      simpa [coords] using prefixNaturalMass_update_last n (last / K) x.val.1
    simp only [hprefix, coords, if_pos]
    change prefixNaturalMass n x.val.1 + last / K + slack / K =
      t * (sylvester (n + 1) - 1)
    apply Nat.mul_left_cancel hK
    have hlast' : K * (last / K) = last := hlast.symm
    have hslack' : K * (slack / K) = slack := hslack.symm
    calc
      K * (prefixNaturalMass n x.val.1 + x.val.1 (Fin.last n) / K + x.val.2 / K) =
          K * prefixNaturalMass n x.val.1 + K * (last / K) + K * (slack / K) := by ring
      _ = K * prefixNaturalMass n x.val.1 + last + slack := by rw [hlast', hslack']
      _ = K * (t * (sylvester (n + 1) - 1)) := hsource
  · apply Sum.inr
    have hK : 0 < K := by omega
    have hrlt : last % K < K := Nat.mod_lt _ hK
    have hrpos : 0 < last % K := Nat.pos_of_ne_zero hr
    let layer : Fin k := ⟨last % K - 1, by omega⟩
    refine ⟨layer, ⟨(coords, slack / K), ?_⟩⟩
    rw [IsInteriorShiftSolution, naturalWeightedMass_succ]
    have hsource := x.property
    change K * prefixNaturalMass n x.val.1 + last + slack =
      K * (t * (sylvester (n + 1) - 1)) at hsource
    have hlast : last = K * (last / K) + last % K := by
      simpa [Nat.add_comm] using (Nat.mod_add_div last K).symm
    have hsumMod : (last + slack) % K = 0 := by
      simpa [K, last, slack] using source_remainders_mod_eq_zero n k t x
    have hslackMod : slack % K = K - last % K :=
      mod_complement_of_add_mod_eq_zero hK hr hsumMod
    have hslack : slack = K * (slack / K) + (K - last % K) := by
      calc
        slack = slack % K + K * (slack / K) := (Nat.mod_add_div slack K).symm
        _ = K * (slack / K) + (K - last % K) := by omega
    have hprefix : prefixNaturalMass n coords = prefixNaturalMass n x.val.1 := by
      simpa [coords] using prefixNaturalMass_update_last n (last / K) x.val.1
    simp only [hprefix, coords, if_pos]
    change prefixNaturalMass n x.val.1 + last / K + slack / K + 1 =
      t * (sylvester (n + 1) - 1)
    apply Nat.mul_left_cancel hK
    have hcombine : K * (last / K) + K * (slack / K) + K = last + slack := by
      omega
    calc
      K * (prefixNaturalMass n x.val.1 + x.val.1 (Fin.last n) / K +
          x.val.2 / K + 1) =
          K * prefixNaturalMass n x.val.1 + K * (last / K) +
            K * (slack / K) + K := by ring
      _ = K * prefixNaturalMass n x.val.1 + last + slack := by
        calc
          K * prefixNaturalMass n x.val.1 + K * (last / K) + K * (slack / K) + K =
              K * prefixNaturalMass n x.val.1 +
                (K * (last / K) + K * (slack / K) + K) := by ring
          _ = K * prefixNaturalMass n x.val.1 + (last + slack) := by rw [hcombine]
          _ = K * prefixNaturalMass n x.val.1 + last + slack := by ring
      _ = K * (t * (sylvester (n + 1) - 1)) := hsource

private def layerToSource (n k t : ℕ) :
    {x // IsBaseSolution (n + 1) t x} ⊕
      Fin k × {x // IsInteriorShiftSolution (n + 1) t x} →
        {x // IsSourceSolution n k t x}
  | Sum.inl x => by
      let K := k + 1
      let coords : Fin (n + 1) → ℕ :=
        fun i => if i = Fin.last n then K * x.val.1 (Fin.last n) else x.val.1 i
      refine ⟨(coords, K * x.val.2), ?_⟩
      rw [IsSourceSolution]
      change K * prefixNaturalMass n coords + coords (Fin.last n) + K * x.val.2 =
        K * (t * (sylvester (n + 1) - 1))
      have hx := x.property
      rw [IsBaseSolution, naturalWeightedMass_succ] at hx
      have hprefix : prefixNaturalMass n coords = prefixNaturalMass n x.val.1 := by
        simpa [coords] using
          prefixNaturalMass_update_last n (K * x.val.1 (Fin.last n)) x.val.1
      simp only [hprefix, coords, if_pos]
      calc
        K * prefixNaturalMass n x.val.1 + K * x.val.1 (Fin.last n) + K * x.val.2 =
            K * (prefixNaturalMass n x.val.1 + x.val.1 (Fin.last n) + x.val.2) := by ring
        _ = K * (t * (sylvester (n + 1) - 1)) := by rw [hx]
  | Sum.inr ⟨layer, x⟩ => by
      let K := k + 1
      let r := layer.val + 1
      let coords : Fin (n + 1) → ℕ :=
        fun i => if i = Fin.last n then K * x.val.1 (Fin.last n) + r else x.val.1 i
      refine ⟨(coords, K * x.val.2 + (K - r)), ?_⟩
      rw [IsSourceSolution]
      change K * prefixNaturalMass n coords + coords (Fin.last n) +
        (K * x.val.2 + (K - r)) = K * (t * (sylvester (n + 1) - 1))
      have hx := x.property
      rw [IsInteriorShiftSolution, naturalWeightedMass_succ] at hx
      have hr : 0 < r ∧ r < K := by
        dsimp [r, K]
        omega
      have hprefix : prefixNaturalMass n coords = prefixNaturalMass n x.val.1 := by
        simpa [coords] using
          prefixNaturalMass_update_last n (K * x.val.1 (Fin.last n) + r) x.val.1
      simp only [hprefix, coords, if_pos]
      have hsub : K - r + r = K := by omega
      calc
        K * prefixNaturalMass n x.val.1 + (K * x.val.1 (Fin.last n) + r) +
              (K * x.val.2 + (K - r)) =
            K * (prefixNaturalMass n x.val.1 + x.val.1 (Fin.last n) + x.val.2) +
              (r + (K - r)) := by ring
        _ = K * (prefixNaturalMass n x.val.1 + x.val.1 (Fin.last n) + x.val.2) + K := by
          congr 1
          omega
        _ = K * (prefixNaturalMass n x.val.1 + x.val.1 (Fin.last n) + x.val.2 + 1) := by ring
        _ = K * (t * (sylvester (n + 1) - 1)) := by rw [hx]

private lemma layerToSource_sourceToLayer (n k t : ℕ)
    (x : {x // IsSourceSolution n k t x}) :
    layerToSource n k t (sourceToLayer n k t x) = x := by
  apply Subtype.ext
  let K := k + 1
  let last := x.val.1 (Fin.last n)
  let slack := x.val.2
  have hK : 0 < K := by omega
  by_cases hr : last % K = 0
  · simp [sourceToLayer, layerToSource, hr, K, last, slack]
    apply Prod.ext
    · funext i
      by_cases hi : i = Fin.last n
      · subst i
        have hdiv : K ∣ last := Nat.dvd_iff_mod_eq_zero.mpr hr
        simp [last]
        exact Nat.mul_div_cancel' hdiv
      · simp [hi]
    · have hsource := x.property
      change K * prefixNaturalMass n x.val.1 + last + slack =
        K * (t * (sylvester (n + 1) - 1)) at hsource
      have hdiv : K ∣ slack := by
        rw [Nat.dvd_iff_mod_eq_zero]
        have hsumMod : (last + slack) % K = 0 := by
          simpa [K, last, slack] using source_remainders_mod_eq_zero n k t x
        have hslt : slack % K < K := Nat.mod_lt _ hK
        rw [Nat.add_mod, hr, zero_add, Nat.mod_eq_of_lt hslt] at hsumMod
        exact hsumMod
      exact Nat.mul_div_cancel' hdiv
  · have hrpos : 0 < last % K := Nat.pos_of_ne_zero hr
    have hrlt : last % K < K := Nat.mod_lt _ hK
    have hlayer : last % K - 1 + 1 = last % K := by omega
    have hrle : last % K ≤ k := by
      have : last % K < k + 1 := by simpa [K] using hrlt
      omega
    have hcomp : k - (last % K - 1) = K - last % K := by
      change k - (last % K - 1) = (k + 1) - last % K
      omega
    simp [sourceToLayer, layerToSource, hr, K, last, slack, hlayer, hcomp]
    apply Prod.ext
    · funext i
      by_cases hi : i = Fin.last n
      · subst i
        simp only [Prod.fst, if_pos]
        change K * (last / K) + last % K = last
        have hmod := Nat.mod_add_div last K
        omega
      · simp [hi]
    · have hsource := x.property
      change K * prefixNaturalMass n x.val.1 + last + slack =
        K * (t * (sylvester (n + 1) - 1)) at hsource
      have hsumMod : (last + slack) % K = 0 := by
        simpa [K, last, slack] using source_remainders_mod_eq_zero n k t x
      have hslackMod : slack % K = K - last % K :=
        mod_complement_of_add_mod_eq_zero hK hr hsumMod
      simp only [Prod.snd]
      change K * (slack / K) + (K - last % K) = slack
      calc
        K * (slack / K) + (K - last % K) =
            K * (slack / K) + slack % K := by rw [hslackMod]
        _ = slack := by simpa [Nat.add_comm] using Nat.mod_add_div slack K

private lemma sourceToLayer_layerToSource (n k t : ℕ)
    (x : {x // IsBaseSolution (n + 1) t x} ⊕
      Fin k × {x // IsInteriorShiftSolution (n + 1) t x}) :
    sourceToLayer n k t (layerToSource n k t x) = x := by
  rcases x with x | ⟨layer, x⟩
  · simp [layerToSource, sourceToLayer]
    apply Subtype.ext
    apply Prod.ext
    · funext i
      by_cases hi : i = Fin.last n <;> simp [hi]
    · simp
  · simp only [layerToSource]
    have hrlt : layer.val + 1 < k + 1 := by omega
    have hr : (layer.val + 1) % (k + 1) = layer.val + 1 := by
      exact Nat.mod_eq_of_lt hrlt
    simp [sourceToLayer, hr]
    apply Subtype.ext
    apply Prod.ext
    · funext i
      by_cases hi : i = Fin.last n
      · subst i
        simp only [Subtype.coe_mk, Prod.fst, if_pos]
        change ((k + 1) * x.val.1 (Fin.last n) + (layer.val + 1)) / (k + 1) =
          x.val.1 (Fin.last n)
        rw [Nat.mul_add_div (by omega : 0 < k + 1),
          Nat.div_eq_of_lt hrlt, Nat.add_zero]
      · simp only [Subtype.coe_eta, Subtype.coe_mk, Prod.fst]
        simp [hi]
    · have hrpos : 0 < layer.val + 1 := by omega
      have hcompLt : k - layer.val < k + 1 := by omega
      change ((k + 1) * x.val.2 + (k - layer.val)) / (k + 1) = x.val.2
      rw [Nat.mul_add_div (by omega : 0 < k + 1)]
      simp [Nat.div_eq_of_lt hcompLt]

private def sourceLayerEquiv (n k t : ℕ) :
    {x // IsSourceSolution n k t x} ≃
      {x // IsBaseSolution (n + 1) t x} ⊕
        Fin k × {x // IsInteriorShiftSolution (n + 1) t x} where
  toFun := sourceToLayer n k t
  invFun := layerToSource n k t
  left_inv := layerToSource_sourceToLayer n k t
  right_inv := sourceToLayer_layerToSource n k t

private noncomputable def sourceSolutionOfLattice (n k t : ℕ)
    (p : {p // p ∈ latticePointSet (n + 1) k t}) :
    {x // IsSourceSolution n k t x} := by
  let coords : Fin (n + 1) → ℕ := fun i => (p.val i).toNat
  let mass := (k + 1) * prefixNaturalMass n coords + coords (Fin.last n)
  let target := (k + 1) * (t * (sylvester (n + 1) - 1))
  have hp_nonneg : ∀ i, 0 ≤ p.val i :=
    ((mem_latticePointSet_iff (n + 1) k t p.val).mp p.property).1
  have hcoords (i : Fin (n + 1)) : p.val i = (coords i : ℤ) := by
    exact (Int.toNat_of_nonneg (hp_nonneg i)).symm
  have hmem : (fun i => (coords i : ℤ)) ∈ latticePointSet (n + 1) k t := by
    convert p.property using 1
    funext i
    exact (hcoords i).symm
  have hle : mass ≤ target := by
    exact (natural_point_mem_source_iff n k t coords).mp hmem
  refine ⟨(coords, target - mass), ?_⟩
  rw [IsSourceSolution]
  exact Nat.add_sub_of_le hle

private def sourceLatticeOfSolution (n k t : ℕ)
    (x : {x // IsSourceSolution n k t x}) :
    {p // p ∈ latticePointSet (n + 1) k t} := by
  let p : Fin (n + 1) → ℤ := fun i => (x.val.1 i : ℤ)
  refine ⟨p, (natural_point_mem_source_iff n k t x.val.1).mpr ?_⟩
  have hx := x.property
  rw [IsSourceSolution] at hx
  omega

private lemma sourceLatticeOfSolution_sourceSolutionOfLattice (n k t : ℕ)
    (p : {p // p ∈ latticePointSet (n + 1) k t}) :
    sourceLatticeOfSolution n k t (sourceSolutionOfLattice n k t p) = p := by
  apply Subtype.ext
  funext i
  unfold sourceLatticeOfSolution sourceSolutionOfLattice
  dsimp only
  have hp_nonneg : ∀ i, 0 ≤ p.val i :=
    ((mem_latticePointSet_iff (n + 1) k t p.val).mp p.property).1
  exact Int.toNat_of_nonneg (hp_nonneg i)

private lemma sourceSolutionOfLattice_sourceLatticeOfSolution (n k t : ℕ)
    (x : {x // IsSourceSolution n k t x}) :
    sourceSolutionOfLattice n k t (sourceLatticeOfSolution n k t x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    simp [sourceSolutionOfLattice, sourceLatticeOfSolution]
  · unfold sourceSolutionOfLattice sourceLatticeOfSolution
    dsimp only
    simp only [Int.toNat_natCast]
    let mass := (k + 1) * prefixNaturalMass n x.val.1 + x.val.1 (Fin.last n)
    let target := (k + 1) * (t * (sylvester (n + 1) - 1))
    change target - mass = x.val.2
    have hx := x.property
    rw [IsSourceSolution] at hx
    have hxm : mass + x.val.2 = target := by simpa [mass, target] using hx
    omega

private noncomputable def sourceLatticeSolutionEquiv (n k t : ℕ) :
    {p // p ∈ latticePointSet (n + 1) k t} ≃
      {x // IsSourceSolution n k t x} where
  toFun := sourceSolutionOfLattice n k t
  invFun := sourceLatticeOfSolution n k t
  left_inv := sourceLatticeOfSolution_sourceSolutionOfLattice n k t
  right_inv := sourceSolutionOfLattice_sourceLatticeOfSolution n k t

private noncomputable instance sourceSolutionFinite (n k t : ℕ) :
    Finite {x // IsSourceSolution n k t x} := by
  letI : Fintype {p // p ∈ latticePointSet (n + 1) k t} :=
    (latticePointSet_finite (n + 1) k t).fintype
  exact Finite.of_equiv _ (sourceLatticeSolutionEquiv n k t)

private noncomputable instance baseSolutionFinite (n t : ℕ) :
    Finite {x // IsBaseSolution (n + 1) t x} := by
  let e := sourceLayerEquiv n 0 t
  exact Finite.of_injective (fun x => e.symm (Sum.inl x))
    (e.symm.injective.comp Sum.inl_injective)

private noncomputable instance interiorShiftSolutionFinite (n t : ℕ) :
    Finite {x // IsInteriorShiftSolution (n + 1) t x} := by
  let e := sourceLayerEquiv n 1 t
  exact Finite.of_injective (fun x => e.symm (Sum.inr (0, x)))
    (e.symm.injective.comp (Sum.inr_injective.comp (Prod.mk_right_injective 0)))

private lemma ehrhartCount_source_decomposition (n k t : ℕ) :
    ehrhartCount (n + 1) k t = ehrhartCount (n + 1) 0 t +
      k * Nat.card {x // IsInteriorShiftSolution (n + 1) t x} := by
  rw [ehrhartCount, ← Nat.card_coe_set_eq,
    Nat.card_congr (sourceLatticeSolutionEquiv n k t),
    Nat.card_congr (sourceLayerEquiv n k t), Nat.card_sum, Nat.card_prod,
    Nat.card_fin, ehrhartCount_base_eq_solution_card (n + 1) t (by omega)]

end D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity
