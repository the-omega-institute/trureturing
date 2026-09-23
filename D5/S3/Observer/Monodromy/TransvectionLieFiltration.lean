/- GID: D5/S3/Observer/Monodromy/TransvectionLieFiltration
   generality: G
   mirror-B: D5/B/S3/Observer/Monodromy/TransvectionLieFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact Lie-generation filtration is the graph-distance band of symmetric dyads. -/

import Mathlib.Algebra.Lie.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
# The exact pairing-graph filtration

`layer H k` is defined from the actual increments, linear span, and actual
commutators. It contains iterated right extensions using at most k+1 generators.
`band H k` is independently defined using walks of at most k edges in the
actual nonzero-entry pairing graph. The main theorem identifies these spaces.
For invertible H the support theorem detects coefficients outside the band.

Yelton, arXiv:1703.10917v5, Remark 3.4, already uses graph diameter in an
l-adic transvection-generation bound. Here the target is the entire exact
linear filtration and a matching support obstruction, not only an upper bound.
No assertion of global priority or geometric monodromy closure is made.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Monodromy.TransvectionLieFiltration

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The rank-at-most-one increment supported on row i. -/
def increment (H : Matrix I I K) (i : I) : Matrix I I K :=
  fun r c => if r = i then H i c else 0

/-- The symmetric dyad `(E_ij + E_ji) H`, also defined for i=j. -/
def cross (H : Matrix I I K) (i j : I) : Matrix I I K :=
  fun r c => (if r = i then H j c else 0) + (if r = j then H i c else 0)

/-- A path of the displayed length, with edges tested on actual matrix entries. -/
inductive Walk (H : Matrix I I K) : ℕ → I → I → Prop
  | nil (i : I) : Walk H 0 i i
  | snoc {d : ℕ} {i j k : I} : Walk H d i j → H j k ≠ 0 → Walk H (d+1) i k

/-- The bounded-distance predicate includes shorter paths. -/
def Within (H : Matrix I I K) (k : ℕ) (i j : I) : Prop :=
  ∃ d, d ≤ k ∧ Walk H d i j

/-- A graph band defined without reference to any Lie closure. -/
def band (H : Matrix I I K) (k : ℕ) : Submodule K (Matrix I I K) :=
  Submodule.span K { X | ∃ i j, Within H k i j ∧ X = cross H i j }

/-- One genuine commutator extension of a linear space by the given increments. -/
def extend (H : Matrix I I K) (L : Submodule K (Matrix I I K)) :
    Submodule K (Matrix I I K) :=
  Submodule.span K { X | ∃ i Y, Y ∈ L ∧ X = ⁅Y, increment H i⁆ }

/-- At stage k, at most k+1 occurrences of the original generators have been used. -/
def layer (H : Matrix I I K) : ℕ → Submodule K (Matrix I I K)
  | 0 => Submodule.span K (Set.range (increment H))
  | k+1 => layer H k ⊔ extend H (layer H k)

/-- Exact equality of independently constructed linear spaces, including singular H.
The inverse matrix is not needed for the propagation part. -/
theorem layer_eq_band (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) (h2 : (2 : K) ≠ 0) (k : ℕ) :
    layer H k = band H k := by
  classical
  have walk_append : ∀ {d e : ℕ} {i j l : I},
      Walk H d i j → Walk H e j l → Walk H (d+e) i l := by
    intro d e i j l p q
    induction q with
    | nil => simpa using p
    | snoc q h ih => simpa [Nat.add_assoc] using Walk.snoc (ih p) h
  have walk_reverse : ∀ {d : ℕ} {i j : I}, Walk H d i j → Walk H d j i := by
    intro d i j p
    induction p with
    | nil => exact .nil _
    | @snoc d i j l p h ih =>
        have hrev : H l j ≠ 0 := by
          rw [hs l j]
          exact neg_ne_zero.mpr h
        have first : Walk H 1 l j := Walk.snoc (.nil l) hrev
        simpa [Nat.add_comm] using walk_append first ih
  have within_refl (n : ℕ) (i : I) : Within H n i i :=
    ⟨0, Nat.zero_le n, .nil i⟩
  have within_mono : ∀ {n l : ℕ} {i j : I},
      n ≤ l → Within H n i j → Within H l i j := by
    intro n l i j h
    rintro ⟨d, hd, hp⟩
    exact ⟨d, hd.trans h, hp⟩
  have within_symm : ∀ {n : ℕ} {i j : I}, Within H n i j → Within H n j i := by
    intro n i j
    rintro ⟨d, hd, hp⟩
    exact ⟨d, hd, walk_reverse hp⟩
  have within_step : ∀ {n : ℕ} {i j l : I},
      Within H n i j → H j l ≠ 0 → Within H (n+1) i l := by
    intro n i j l h e
    rcases h with ⟨d, hd, hp⟩
    exact ⟨d+1, Nat.add_le_add_right hd 1, .snoc hp e⟩
  have within_zero : ∀ {i j : I}, Within H 0 i j → i = j := by
    intro i j
    rintro ⟨d, hd, hp⟩
    have hd0 : d = 0 := Nat.eq_zero_of_le_zero hd
    subst d
    cases hp
    rfl
  have within_succ_cases : ∀ {n : ℕ} {i j : I},
      Within H (n+1) i j →
        Within H n i j ∨ ∃ u, Within H n i u ∧ H u j ≠ 0 := by
    intro n i j h
    rcases h with ⟨d, hd, hp⟩
    cases hp with
    | nil => exact Or.inl (within_refl n i)
    | @snoc d i u j hp he =>
        exact Or.inr ⟨u, ⟨d, by omega, hp⟩, he⟩
  have layer_mono : Monotone (layer H) :=
    monotone_nat_of_le_succ fun n =>
      show layer H n ≤ layer H n ⊔ extend H (layer H n) from le_sup_left
  have band_mono : ∀ {n l : ℕ}, n ≤ l → band H n ≤ band H l := by
    intro n l h
    apply Submodule.span_mono
    rintro X ⟨i, j, hp, rfl⟩
    exact ⟨i, j, within_mono h hp, rfl⟩
  have cross_mem_band : ∀ {n : ℕ} {i j : I},
      Within H n i j → cross H i j ∈ band H n := by
    intro n i j h
    exact Submodule.subset_span ⟨i, j, h, rfl⟩
  have cross_self (i : I) : cross H i i = (2 : K) • increment H i := by
    ext r c
    by_cases h : r = i <;> simp [cross, increment, h, two_mul]
  have bracket_increment (i j : I) :
      ⁅increment H i, increment H j⁆ = H i j • cross H i j := by
    have product_entry (a b r c : I) :
        (increment H a * increment H b) r c =
          if r = a then H a b * H b c else 0 := by
      by_cases h : r = a
      · subst r
        simp [Matrix.mul_apply, increment]
      · simp [Matrix.mul_apply, increment, h]
    change increment H i * increment H j - increment H j * increment H i = _
    ext r c
    simp only [Matrix.sub_apply, product_entry, Matrix.smul_apply, smul_eq_mul, cross]
    rw [hs j i]
    split_ifs <;> ring
  have bracket_cross_increment (i j l : I) :
      ⁅cross H i j, increment H l⁆ =
        H j l • cross H i l + H i l • cross H j l := by
    have cross_mul_increment (a b v r c : I) :
        (cross H a b * increment H v) r c =
          (if r = a then H b v * H v c else 0) +
          (if r = b then H a v * H v c else 0) := by
      simp [Matrix.mul_apply, cross, increment, add_mul]
    have increment_mul_cross (a b v r c : I) :
        (increment H v * cross H a b) r c =
          if r = v then H v a * H b c + H v b * H a c else 0 := by
      by_cases h : r = v
      · subst r
        simp [Matrix.mul_apply, cross, increment, mul_add, Finset.sum_add_distrib]
      · simp [Matrix.mul_apply, increment, h]
    change cross H i j * increment H l - increment H l * cross H i j = _
    ext r c
    simp only [Matrix.sub_apply, cross_mul_increment, increment_mul_cross,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cross]
    rw [hs l i, hs l j]
    split_ifs <;> ring
  have increment_mem_layer_zero (i : I) : increment H i ∈ layer H 0 :=
    Submodule.subset_span ⟨i, rfl⟩
  have bracket_mem_next : ∀ {n : ℕ} {X : Matrix I I K},
      X ∈ layer H n → ∀ i, ⁅X, increment H i⁆ ∈ layer H (n+1) := by
    intro n X h i
    exact
      (show extend H (layer H n) ≤ layer H n ⊔ extend H (layer H n) from le_sup_right)
        (Submodule.subset_span ⟨i, X, h, rfl⟩)
  have edge_mem_layer_one : ∀ i j : I, H i j ≠ 0 → cross H i j ∈ layer H 1 := by
    intro i j hij
    have hm := bracket_mem_next (increment_mem_layer_zero i) j
    have h := (layer H 1).smul_mem (H i j)⁻¹ hm
    rwa [bracket_increment, smul_smul, inv_mul_cancel₀ hij, one_smul] at h
  have cross_bracket_mem_band : ∀ {n : ℕ} {i j : I},
      Within H n i j → ∀ v, ⁅cross H i j, increment H v⁆ ∈ band H (n+1) := by
    intro n i j hp v
    rw [bracket_cross_increment]
    apply (band H (n+1)).add_mem
    · by_cases he : H j v = 0
      · simp [he]
      · exact (band H (n+1)).smul_mem _ (cross_mem_band (within_step hp he))
    · by_cases he : H i v = 0
      · simp [he]
      · exact (band H (n+1)).smul_mem _
          (cross_mem_band (within_step (within_symm hp) he))
  induction k with
  | zero =>
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro X ⟨i, rfl⟩
        have h := (band H 0).smul_mem (2 : K)⁻¹
          (cross_mem_band (within_refl 0 i))
        rwa [cross_self, smul_smul, inv_mul_cancel₀ h2, one_smul] at h
      · apply Submodule.span_le.mpr
        rintro X ⟨i, j, hp, rfl⟩
        have he := within_zero hp
        subst j
        rw [cross_self]
        exact (layer H 0).smul_mem 2 (increment_mem_layer_zero i)
  | succ k ih =>
      apply le_antisymm
      · change layer H k ⊔ extend H (layer H k) ≤ band H (k+1)
        apply sup_le
        · rw [ih]
          exact band_mono (Nat.le_succ k)
        · apply Submodule.span_le.mpr
          rintro X ⟨i, Y, hY, rfl⟩
          rw [ih] at hY
          induction hY using Submodule.span_induction with
          | mem Y hY =>
              rcases hY with ⟨u, v, hp, rfl⟩
              exact cross_bracket_mem_band hp i
          | zero => simp
          | add Y Z _ _ hY hZ =>
              rw [add_lie]
              exact (band H (k+1)).add_mem hY hZ
          | smul c Y _ hY =>
              rw [smul_lie]
              exact (band H (k+1)).smul_mem c hY
      · apply Submodule.span_le.mpr
        rintro X ⟨i, j, hp, rfl⟩
        rcases within_succ_cases hp with hold | ⟨u, hpre, he⟩
        · apply layer_mono (Nat.le_succ k)
          rw [ih]
          exact cross_mem_band hold
        · have hpre' : cross H i u ∈ layer H k := by
            rw [ih]
            exact cross_mem_band hpre
          have hedge : cross H u j ∈ layer H (k+1) :=
            layer_mono (by omega) (edge_mem_layer_one u j he)
          have hm := (layer H (k+1)).sub_mem (bracket_mem_next hpre' j)
            ((layer H (k+1)).smul_mem (H i j) hedge)
          rw [bracket_cross_increment, add_sub_cancel_right] at hm
          have hn := (layer H (k+1)).smul_mem (H u j)⁻¹ hm
          rwa [smul_smul, inv_mul_cancel₀ he, one_smul] at hn

/-- Every coefficient beyond the graph-distance band is genuinely zero, so a
shorter Lie calculation cannot reach that state direction. -/
theorem layer_support (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) (h2 : (2 : K) ≠ 0)
    (hdet : H.det ≠ 0) (k : ℕ) {X : Matrix I I K} (hX : X ∈ layer H k)
    (r c : I) (hfar : ¬ Within H k r c) : (X * H⁻¹) r c = 0 := by
  classical
  have walk_append : ∀ {d e : ℕ} {i j l : I},
      Walk H d i j → Walk H e j l → Walk H (d+e) i l := by
    intro d e i j l p q
    induction q with
    | nil => simpa using p
    | snoc q h ih => simpa [Nat.add_assoc] using Walk.snoc (ih p) h
  have walk_reverse : ∀ {d : ℕ} {i j : I}, Walk H d i j → Walk H d j i := by
    intro d i j p
    induction p with
    | nil => exact .nil _
    | @snoc d i j l p h ih =>
        have hrev : H l j ≠ 0 := by
          rw [hs l j]
          exact neg_ne_zero.mpr h
        have first : Walk H 1 l j := Walk.snoc (.nil l) hrev
        simpa [Nat.add_comm] using walk_append first ih
  have within_symm : ∀ {n : ℕ} {i j : I}, Within H n i j → Within H n j i := by
    intro n i j
    rintro ⟨d, hd, hp⟩
    exact ⟨d, hd, walk_reverse hp⟩
  have cross_times_inverse (i j : I) :
      cross H i j * H⁻¹ =
        (fun r c => (if r = i then (1 : Matrix I I K) j c else 0) +
          (if r = j then (1 : Matrix I I K) i c else 0)) := by
    have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
    have he (a b : I) : (∑ v, H a v * H⁻¹ v b) = (1 : Matrix I I K) a b :=
      congrArg (fun M : Matrix I I K => M a b) (Matrix.mul_nonsing_inv H hu)
    ext a b
    by_cases hi : a = i <;> by_cases hj : a = j <;>
      simp [Matrix.mul_apply, cross, hi, hj, add_mul, Finset.sum_add_distrib, he]
  rw [layer_eq_band H hs h2] at hX
  induction hX using Submodule.span_induction with
  | mem X hX =>
      rcases hX with ⟨i, j, hp, rfl⟩
      rw [cross_times_inverse]
      have hfirst : ¬ (r = i ∧ j = c) := by
        rintro ⟨rfl, rfl⟩
        exact hfar hp
      have hsecond : ¬ (r = j ∧ i = c) := by
        rintro ⟨rfl, rfl⟩
        exact hfar (within_symm hp)
      by_cases hi : r = i <;> by_cases hj : r = j
      · subst r
        have hjc : j ≠ c := fun h => hfirst ⟨rfl, h⟩
        have hic : i ≠ c := fun h => hsecond ⟨hj, h⟩
        simp [hj, hjc]
      · subst r
        have hjc : j ≠ c := fun h => hfirst ⟨rfl, h⟩
        simp [hj, hjc]
      · subst r
        have hic : i ≠ c := fun h => hsecond ⟨rfl, h⟩
        simp [hi, hic]
      · simp [hi, hj]
  | zero => simp
  | add X Y _ _ hX hY => simp [Matrix.add_mul, hX, hY]
  | smul a X _ hX => simp [hX]

#print axioms layer_eq_band
#print axioms layer_support

end D5.S3.Observer.Monodromy.TransvectionLieFiltration
