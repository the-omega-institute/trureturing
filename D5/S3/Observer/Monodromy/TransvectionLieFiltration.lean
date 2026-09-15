/- GID: D5/S3/Observer/Monodromy/TransvectionLieFiltration
   generality: G
   mirror-B: D5/B/S3/Observer/Monodromy/TransvectionLieFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The exact Lie-generation filtration is the graph-distance band of symmetric dyads. -/

import D5.S3.Observer.Monodromy.TransvectionLieGeneration
import Mathlib.Tactic

/-!
# The exact pairing-graph filtration

`layer H k` is defined from the actual increments, linear span, and actual
commutators. It contains iterated right extensions using at most k+1 generators.
`band H k` is independently defined using walks of at most k edges in the
actual nonzero-entry pairing graph. The main theorem identifies these spaces.
For invertible H an off-diagonal dyad first appears at its exact graph distance.

Yelton, arXiv:1703.10917v5, Remark 3.4, already uses graph diameter in an
l-adic transvection-generation bound. Here the target is the entire exact
linear filtration and a matching support obstruction, not only an upper bound.
No assertion of global priority or geometric monodromy closure is made.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Monodromy.TransvectionLieFiltration

open D5.S3.Observer.Monodromy.TransvectionTraceReconstruction
open D5.S3.Observer.Monodromy.TransvectionLieGeneration

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- A path of the displayed length, with edges tested on actual matrix entries. -/
inductive Walk (H : Matrix I I K) : ℕ → I → I → Prop
  | nil (i : I) : Walk H 0 i i
  | snoc {d : ℕ} {i j k : I} : Walk H d i j → H j k ≠ 0 → Walk H (d+1) i k

/-- The bounded-distance predicate includes shorter paths. -/
def Within (H : Matrix I I K) (k : ℕ) (i j : I) : Prop :=
  ∃ d, d ≤ k ∧ Walk H d i j

private theorem walk_append (H : Matrix I I K) {d e : ℕ} {i j k : I}
    (p : Walk H d i j) (q : Walk H e j k) : Walk H (d+e) i k := by
  induction q with
  | nil => simpa using p
  | snoc q h ih => simpa [Nat.add_assoc] using Walk.snoc ih h

private theorem walk_reverse (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) {d : ℕ} {i j : I}
    (p : Walk H d i j) : Walk H d j i := by
  induction p with
  | nil => exact .nil _
  | @snoc d i j k p h ih =>
      have hrev : H k j ≠ 0 := by rw [hs k j]; exact neg_ne_zero.mpr h
      have first : Walk H 1 k j := Walk.snoc (.nil k) hrev
      simpa [Nat.add_comm] using walk_append H first ih

private theorem within_refl (H : Matrix I I K) (k : ℕ) (i : I) : Within H k i i :=
  ⟨0, Nat.zero_le k, .nil i⟩

private theorem within_mono (H : Matrix I I K) {k l : ℕ} (h : k ≤ l)
    {i j : I} : Within H k i j → Within H l i j := by
  rintro ⟨d, hd, hp⟩
  exact ⟨d, hd.trans h, hp⟩

private theorem within_symm (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) {k : ℕ} {i j : I} :
    Within H k i j → Within H k j i := by
  rintro ⟨d, hd, hp⟩
  exact ⟨d, hd, walk_reverse H hs hp⟩

private theorem within_step (H : Matrix I I K) {k : ℕ} {i j l : I}
    (h : Within H k i j) (e : H j l ≠ 0) : Within H (k+1) i l := by
  rcases h with ⟨d, hd, hp⟩
  exact ⟨d+1, Nat.add_le_add_right hd 1, .snoc hp e⟩

private theorem within_zero (H : Matrix I I K) {i j : I} :
    Within H 0 i j → i = j := by
  rintro ⟨d, hd, hp⟩
  have hd0 : d = 0 := Nat.eq_zero_of_le_zero hd
  subst d
  cases hp
  rfl

private theorem within_succ_cases (H : Matrix I I K) {k : ℕ} {i j : I}
    (h : Within H (k+1) i j) :
    Within H k i j ∨ ∃ u, Within H k i u ∧ H u j ≠ 0 := by
  rcases h with ⟨d, hd, hp⟩
  cases hp with
  | nil => exact Or.inl (within_refl H k i)
  | @snoc d i u j hp he =>
      exact Or.inr ⟨u, ⟨d, by omega, hp⟩, he⟩

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

private theorem layer_mono (H : Matrix I I K) : Monotone (layer H) :=
  monotone_nat_of_le_succ fun k => show layer H k ≤ layer H k ⊔ extend H (layer H k) from le_sup_left

private theorem band_mono (H : Matrix I I K) {k l : ℕ} (h : k ≤ l) :
    band H k ≤ band H l := by
  apply Submodule.span_mono
  rintro X ⟨i, j, hp, rfl⟩
  exact ⟨i, j, within_mono H h hp, rfl⟩

private theorem cross_mem_band (H : Matrix I I K) {k : ℕ} {i j : I}
    (h : Within H k i j) : cross H i j ∈ band H k :=
  Submodule.subset_span ⟨i, j, h, rfl⟩

private theorem increment_mem_layer_zero (H : Matrix I I K) (i : I) :
    increment H i ∈ layer H 0 := Submodule.subset_span ⟨i, rfl⟩

private theorem bracket_mem_next (H : Matrix I I K) {k : ℕ}
    {X : Matrix I I K} (h : X ∈ layer H k) (i : I) :
    ⁅X, increment H i⁆ ∈ layer H (k+1) :=
  (show extend H (layer H k) ≤ layer H k ⊔ extend H (layer H k) from le_sup_right)
    (Submodule.subset_span ⟨i, X, h, rfl⟩)

private theorem edge_mem_layer_one (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) (i j : I) (hij : H i j ≠ 0) :
    cross H i j ∈ layer H 1 := by
  have hm := bracket_mem_next H (increment_mem_layer_zero H i) j
  have h := (layer H 1).smul_mem (H i j)⁻¹ hm
  rwa [bracket_increment H hs, smul_smul, inv_mul_cancel₀ hij, one_smul] at h

private theorem cross_bracket_mem_band (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) {k : ℕ} {i j : I}
    (hp : Within H k i j) (v : I) :
    ⁅cross H i j, increment H v⁆ ∈ band H (k+1) := by
  rw [bracket_cross_increment H hs]
  apply (band H (k+1)).add_mem
  · by_cases he : H j v = 0
    · simp [he]
    · exact (band H (k+1)).smul_mem _ (cross_mem_band H (within_step H hp he))
  · by_cases he : H i v = 0
    · simp [he]
    · exact (band H (k+1)).smul_mem _
        (cross_mem_band H (within_step H (within_symm H hs hp) he))

/-- Exact equality of independently constructed linear spaces, including singular H.
The inverse matrix is not needed for the propagation part. -/
theorem layer_eq_band (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) (h2 : (2 : K) ≠ 0) (k : ℕ) :
    layer H k = band H k := by
  induction k with
  | zero =>
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro X ⟨i, rfl⟩
        have h := (band H 0).smul_mem (2 : K)⁻¹
          (cross_mem_band H (within_refl H 0 i))
        rwa [cross_self, smul_smul, inv_mul_cancel₀ h2, one_smul] at h
      · apply Submodule.span_le.mpr
        rintro X ⟨i, j, hp, rfl⟩
        have he := within_zero H hp
        subst j
        rw [cross_self]
        exact (layer H 0).smul_mem 2 (increment_mem_layer_zero H i)
  | succ k ih =>
      apply le_antisymm
      · change layer H k ⊔ extend H (layer H k) ≤ band H (k+1)
        apply sup_le
        · rw [ih]
          exact band_mono H (Nat.le_succ k)
        · apply Submodule.span_le.mpr
          rintro X ⟨i, Y, hY, rfl⟩
          rw [ih] at hY
          induction hY using Submodule.span_induction with
          | mem Y hY =>
              rcases hY with ⟨u, v, hp, rfl⟩
              exact cross_bracket_mem_band H hs hp i
          | zero => simp
          | add Y Z _ _ hY hZ =>
              rw [add_lie]
              exact (band H (k+1)).add_mem hY hZ
          | smul c Y _ hY =>
              rw [smul_lie]
              exact (band H (k+1)).smul_mem c hY
      · apply Submodule.span_le.mpr
        rintro X ⟨i, j, hp, rfl⟩
        rcases within_succ_cases H hp with hold | ⟨u, hpre, he⟩
        · apply layer_mono H (Nat.le_succ k)
          rw [ih]
          exact cross_mem_band H hold
        · have hpre' : cross H i u ∈ layer H k := by
            rw [ih]
            exact cross_mem_band H hpre
          have hedge : cross H u j ∈ layer H (k+1) :=
            layer_mono H (by omega) (edge_mem_layer_one H hs u j he)
          have hm := (layer H (k+1)).sub_mem (bracket_mem_next H hpre' j)
            ((layer H (k+1)).smul_mem (H i j) hedge)
          rw [bracket_cross_increment H hs, add_sub_cancel_right] at hm
          have hn := (layer H (k+1)).smul_mem (H u j)⁻¹ hm
          rwa [smul_smul, inv_mul_cancel₀ he, one_smul] at hn

private theorem cross_times_inverse (H : Matrix I I K) (hdet : H.det ≠ 0)
    (i j : I) :
    cross H i j * H⁻¹ =
      (fun r c => (if r = i then (1 : Matrix I I K) j c else 0) +
        (if r = j then (1 : Matrix I I K) i c else 0)) := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have he (r c : I) : (∑ v, H r v * H⁻¹ v c) = (1 : Matrix I I K) r c :=
    congrArg (fun M : Matrix I I K => M r c) (Matrix.mul_nonsing_inv H hu)
  ext r c
  by_cases hi : r = i <;> by_cases hj : r = j <;>
    simp [Matrix.mul_apply, cross, hi, hj, add_mul, Finset.sum_add_distrib, he]

/-- Every coefficient beyond the graph-distance band is genuinely zero, so a
shorter Lie calculation cannot reach that state direction. -/
theorem layer_support (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) (h2 : (2 : K) ≠ 0)
    (hdet : H.det ≠ 0) (k : ℕ) {X : Matrix I I K} (hX : X ∈ layer H k)
    (r c : I) (hfar : ¬ Within H k r c) : (X * H⁻¹) r c = 0 := by
  rw [layer_eq_band H hs h2] at hX
  induction hX using Submodule.span_induction with
  | mem X hX =>
      rcases hX with ⟨i, j, hp, rfl⟩
      rw [cross_times_inverse H hdet]
      have hfirst : ¬ (r = i ∧ j = c) := by
        rintro ⟨rfl, rfl⟩
        exact hfar hp
      have hsecond : ¬ (r = j ∧ i = c) := by
        rintro ⟨rfl, rfl⟩
        exact hfar (within_symm H hs hp)
      by_cases hi : r = i <;> by_cases hj : r = j
      · subst r
        have hjc : j ≠ c := fun h => hfirst ⟨rfl, h⟩
        have hic : i ≠ c := fun h => hsecond ⟨hj, h⟩
        simp [hj, hjc, hic]
      · subst r
        have hjc : j ≠ c := fun h => hfirst ⟨rfl, h⟩
        simp [hj, hjc]
      · subst r
        have hic : i ≠ c := fun h => hsecond ⟨rfl, h⟩
        simp [hi, hic]
      · simp [hi, hj]
  | zero => simp
  | add X Y _ _ hX hY => simp [Matrix.add_mul, hX, hY]
  | smul a X _ hX => simp [Matrix.smul_mul, hX]

/-- Exact onset of an off-diagonal direction. The forward implication is the
support lower bound; the reverse is the constructive path argument. -/
theorem cross_mem_layer_iff (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) (h2 : (2 : K) ≠ 0)
    (hdet : H.det ≠ 0) (k : ℕ) (i j : I) (hij : i ≠ j) :
    cross H i j ∈ layer H k ↔ Within H k i j := by
  constructor
  · intro h
    by_contra hfar
    have hz := layer_support H hs h2 hdet k h i j hfar
    rw [cross_times_inverse H hdet] at hz
    have hone : (1 : K) = 0 := by simpa [hij, Ne.symm hij] using hz
    exact one_ne_zero hone
  · intro h
    rw [layer_eq_band H hs h2]
    exact cross_mem_band H h

#print axioms layer_eq_band
#print axioms layer_support
#print axioms cross_mem_layer_iff

end D5.S3.Observer.Monodromy.TransvectionLieFiltration
