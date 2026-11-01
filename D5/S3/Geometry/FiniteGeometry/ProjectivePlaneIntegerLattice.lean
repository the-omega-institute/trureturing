/- GID: D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice
   mirror-E: none(waiver:no-experimental-evidence)
   anchors: []
   utility: none
   digest: Exact integer image and Boolean closure of finite projective-plane incidence. -/

import Mathlib.Combinatorics.Configuration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push

/-!
The plane, its original points and its original lines are arbitrary. Its order
is Mathlib's derived order, not a plane-existence assumption. The new inference
is divisibility-certified integer reconstruction and its Boolean consequences.
No cancellation in a quotient group is used. Standard geometric counts are
reused from Configuration.

Admission: escape-witness. The divisibility-certified inverse and the complete
Boolean coefficient dichotomy are the new inferences, not supplied by the
inspected geometry, matrix or quotient contracts. There are no direct frozen
D5 dependencies: all imports are pinned Mathlib. Utility none: all declarations
are symbolic general results, not enumerations or numeric certificates.
The total and line identities and injectivity are consumed algebraic helpers;
integer_reconstruction consumes injectivity for its unique original witness;
mem_lattice_iff consumes reconstruction; the three exact ideals consume the
criterion and original geometric existence facts. Boolean closure consumes
both master identities and the integer 0/1 coefficient dichotomy. All private
sum, bound and existence helpers have live consumers in these proofs.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Configuration
attribute [local instance] Classical.propDecidable

namespace D5.S3.Geometry.FiniteGeometry.ProjectivePlaneIntegerLattice

variable {P L : Type*} [Membership P L] [Fintype P] [Fintype L]

/-- The original line indicator, with integer coordinates. -/
def row (l : L) (x : P) : ℤ := if x ∈ l then 1 else 0

/-- Integer original-line potentials mapped to original-point coordinates. -/
def incidence (a : L → ℤ) (x : P) : ℤ := ∑ l, row l x * a l

/-- The sum of an integer vector along an original line. -/
def lineSum (z : P → ℤ) (l : L) : ℤ := ∑ x, row l x * z x

/-- The exact integer image; no saturation or rational span. -/
def lattice : Set (P → ℤ) := Set.range (incidence (P := P) (L := L))

variable [ProjectivePlane P L]

abbrev q : ℤ := (ProjectivePlane.order P L : ℤ)

lemma q_ge_two : 2 ≤ q (P := P) (L := L) := by
  exact_mod_cast ProjectivePlane.one_lt_order P L

lemma row_total (l : L) : ∑ x : P, row l x = q (P := P) (L := L) + 1 := by
  have h := ProjectivePlane.pointCount_eq P l
  rw [pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  simpa [row, Finset.sum_ite, q] using congrArg (fun n : ℕ => (n : ℤ)) h

lemma column_total (x : P) : ∑ l : L, row l x = q (P := P) (L := L) + 1 := by
  have h := ProjectivePlane.lineCount_eq L x
  rw [lineCount, Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  simpa [row, Finset.sum_ite, q] using congrArg (fun n : ℕ => (n : ℤ)) h

lemma row_gram (l k : L) :
    ∑ x : P, row l x * row k x = if l = k then q (P := P) (L := L) + 1 else 1 := by
  classical
  by_cases h : l = k
  · subst k
    rw [ite_eq_left rfl, ← row_total l]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ l <;> simp [row, hx]
  · rw [ite_eq_right h]
    obtain ⟨x, hx, hu⟩ := HasPoints.existsUnique_point P L l k h
    rw [Finset.sum_eq_single x]
    · simp [row, hx.1, hx.2]
    · intro y _ hy
      have hn : ¬ (y ∈ l ∧ y ∈ k) := fun hy' => hy (hu y hy')
      by_cases hl : y ∈ l <;> by_cases hk : y ∈ k <;> simp_all [row]
    · simp

lemma column_gram (x y : P) :
    ∑ l : L, row l x * row l y = if x = y then q (P := P) (L := L) + 1 else 1 := by
  classical
  by_cases h : x = y
  · subst y
    rw [ite_eq_left rfl, ← column_total x]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hx : x ∈ l <;> simp [row, hx]
  · rw [ite_eq_right h]
    obtain ⟨l, hl, hu⟩ := HasLines.existsUnique_line P L x y h
    rw [Finset.sum_eq_single l]
    · simp [row, hl.1, hl.2]
    · intro k _ hk
      have hn : ¬ (x ∈ k ∧ y ∈ k) := fun hk' => hk (hu k hk')
      by_cases hx : x ∈ k <;> by_cases hy : y ∈ k <;> simp_all [row]
    · simp

/-- The total incidence mass is q+1 times the total integer potential. -/
theorem total_incidence (a : L → ℤ) :
    ∑ x : P, incidence a x = (q (P := P) (L := L) + 1) * ∑ l, a l := by
  unfold incidence
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, row_total]
  rw [Finset.mul_sum]

/-- A line sum separates its own coefficient from the total potential. -/
theorem lineSum_incidence (a : L → ℤ) (l : L) :
    lineSum (incidence a) l = q (P := P) (L := L) * a l + ∑ k, a k := by
  unfold lineSum incidence
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, row_gram]
  calc
    ∑ k : L, (if l = k then q (P := P) (L := L) + 1 else 1) * a k =
        ∑ k : L, ((if k = l then q (P := P) (L := L) * a l else 0) + a k) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : k = l
      · subst k; simp; ring
      · simp [h, Ne.symm h]
    _ = _ := by simp [Finset.sum_add_distrib]

private lemma incidence_lineSum (z : P → ℤ) (x : P) :
    incidence (L := L) (lineSum (L := L) z) x = q (P := P) (L := L) * z x + ∑ y, z y := by
  unfold incidence lineSum
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, column_gram]
  calc
    ∑ y : P, (if x = y then q (P := P) (L := L) + 1 else 1) * z y =
        ∑ y : P, ((if y = x then q (P := P) (L := L) * z x else 0) + z y) := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : y = x
      · subst y; simp; ring
      · simp [h, Ne.symm h]
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Distinct integer potentials never give the same original vector. -/
theorem incidence_injective : Function.Injective (incidence (P := P) (L := L)) := by
  intro a b hab
  have hq := q_ge_two (P := P) (L := L)
  have ht : ∑ l, a l = ∑ l, b l := by
    have h := congrArg (fun z : P → ℤ => ∑ x, z x) hab
    rw [total_incidence, total_incidence] at h
    nlinarith
  funext l
  have h := congrArg (fun z : P → ℤ => lineSum z l) hab
  rw [lineSum_incidence, lineSum_incidence, ht] at h
  nlinarith

/-- Divisibility reconstructs a unique original INTEGER potential. -/
theorem integer_reconstruction (z : P → ℤ) (s : ℤ)
    (ht : (∑ x, z x) = (q (P := P) (L := L) + 1) * s)
    (hd : ∀ l : L, q (P := P) (L := L) ∣ lineSum z l - s) :
    ∃! a : L → ℤ, incidence a = z ∧ (∑ l, a l) = s ∧
      ∀ l, a l = (lineSum z l - s) / q (P := P) (L := L) := by
  -- Divisibility is established before defining any integer quotient.
  let a : L → ℤ := fun l => (lineSum z l - s) / q (P := P) (L := L)
  have ha : ∀ l, q (P := P) (L := L) * a l = lineSum z l - s :=
    fun l => Int.mul_ediv_cancel' (hd l)
  have hq := q_ge_two (P := P) (L := L)
  have heq : incidence a = z := by
    funext x
    have h := incidence_lineSum (L := L) z x
    have he : q (P := P) (L := L) * incidence a x =
        incidence (L := L) (lineSum (L := L) z) x - (q (P := P) (L := L) + 1) * s := by
      unfold incidence
      rw [Finset.mul_sum]
      calc
        ∑ l : L, q (P := P) (L := L) * (row l x * a l) =
            ∑ l : L, (row l x * lineSum z l - row l x * s) := by
          apply Finset.sum_congr rfl
          intro l _
          have := ha l
          linear_combination row l x * this
        _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_mul, column_total]
    nlinarith
  have hsum : (∑ l, a l) = s := by
    have hm := total_incidence a
    rw [heq, ht] at hm
    nlinarith
  exact ⟨a, ⟨heq, hsum, fun _ => rfl⟩,
    fun b hb => incidence_injective (hb.1.trans heq.symm)⟩

/-- Exact original integer-image criterion, including an integer witness s. -/
theorem mem_lattice_iff (z : P → ℤ) :
    z ∈ lattice (P := P) (L := L) ↔ ∃ s : ℤ,
      (∑ x, z x) = (q (P := P) (L := L) + 1) * s ∧
      ∀ l : L, q (P := P) (L := L) ∣ lineSum z l - s := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨∑ l, a l, total_incidence a, ?_⟩
    intro l
    rw [lineSum_incidence]
    exact ⟨a l, by ring⟩
  · rintro ⟨s, ht, hd⟩
    obtain ⟨a, ha, _⟩ := integer_reconstruction z s ht hd
    exact ⟨a, ha.1⟩

/-- The Boolean indicator retains every original point coordinate. -/
def indicator (S : Finset P) (x : P) : ℤ := if x ∈ S then 1 else 0

private lemma indicator_total (S : Finset P) : ∑ x, indicator S x = (S.card : ℤ) := by
  classical
  simp [indicator]

private lemma lineSum_indicator_bounds (S : Finset P) (l : L) :
    0 ≤ lineSum (indicator S) l ∧ lineSum (indicator S) l ≤ q (P := P) (L := L) + 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro x _
    by_cases hx : x ∈ l <;> by_cases hs : x ∈ S <;> simp [row, indicator, hx, hs]
  · rw [← row_total l]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : x ∈ l <;> by_cases hs : x ∈ S <;> simp [row, indicator, hx, hs]

/-- All nonempty proper Boolean vectors in the exact image are original lines. -/
theorem boolean_mem_lattice_iff (S : Finset P) (hne : S.Nonempty) (hp : S ≠ univ) :
    indicator S ∈ lattice (P := P) (L := L) ↔ ∃ l : L, S = univ.filter (· ∈ l) := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    let s : ℤ := ∑ l, a l
    have hq := q_ge_two (P := P) (L := L)
    have ht : (S.card : ℤ) = (q (P := P) (L := L) + 1) * s := by
      rw [← indicator_total, ← ha, total_incidence]
    have hm : (0 : ℤ) < S.card := by exact_mod_cast hne.card_pos
    have hc : S.card < Fintype.card P := by
      simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hp)
    have hb : (S.card : ℤ) < q (P := P) (L := L) ^ 2 + q (P := P) (L := L) + 1 := by
      rw [ProjectivePlane.card_points P L] at hc
      exact_mod_cast hc
    have hs : 1 ≤ s ∧ s ≤ q (P := P) (L := L) := by
      constructor <;> by_contra h <;> push Not at h <;> nlinarith
    have hl : ∀ l, 0 ≤ q (P := P) (L := L) * a l + s ∧
        q (P := P) (L := L) * a l + s ≤ q (P := P) (L := L) + 1 := by
      intro l
      simpa only [← ha, lineSum_incidence] using lineSum_indicator_bounds (L := L) S l
    have hs1 : s = 1 := by
      by_contra h
      have hs2 : 2 ≤ s := by omega
      have hn : ∀ l, a l ≤ 0 := by
        intro l
        have := hl l
        by_contra h
        have : 1 ≤ a l := by omega
        nlinarith
      have hn' := Finset.sum_nonpos (s := (univ : Finset L)) (fun l _ => hn l)
      change s ≤ 0 at hn'
      omega
    have ha01 : ∀ l, a l = 0 ∨ a l = 1 := by
      intro l
      have h := hl l
      rw [hs1] at h
      have hlo : 0 ≤ a l := by
        by_contra hn
        have : a l ≤ -1 := by omega
        nlinarith
      have hhi : a l ≤ 1 := by
        by_contra hn
        have : 2 ≤ a l := by omega
        nlinarith
      omega
    have hnonneg : ∀ l, 0 ≤ a l := fun l => by rcases ha01 l with h | h <;> omega
    obtain ⟨l, hal⟩ : ∃ l, a l = 1 := by
      by_contra h
      push Not at h
      have hz : ∀ l, a l = 0 := fun l => (ha01 l).resolve_right (h l)
      have : s = 0 := by simp [s, hz]
      omega
    have he : ∑ k ∈ univ.erase l, a k = 0 := by
      have := Finset.sum_erase_add (univ : Finset L) a (mem_univ l)
      change (∑ k ∈ univ.erase l, a k) + a l = s at this
      omega
    have hz : ∀ k, k ≠ l → a k = 0 := by
      intro k hk
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp he k (by simp [hk])
    have hf : incidence a = row l := by
      funext x
      unfold incidence
      rw [Finset.sum_eq_single l]
      · simp [hal]
      · intro k _ hk; simp [hz k hk]
      · simp
    refine ⟨l, ?_⟩
    ext x
    have hx := congrFun (ha.symm.trans hf) x
    by_cases hxs : x ∈ S <;> by_cases hxl : x ∈ l <;> simp_all [indicator, row]
  · rintro ⟨l, rfl⟩
    refine ⟨fun k => if k = l then 1 else 0, ?_⟩
    funext x
    simp [incidence, row, indicator]

/-- An original point unit, scaled by any signed integer. -/
def unit (x : P) (y : P) : ℤ := if y = x then 1 else 0

omit [Fintype L] [ProjectivePlane P L] in
private lemma lineSum_unit (x : P) (k : ℤ) (l : L) :
    lineSum (fun y => k * unit x y) l = k * row l x := by
  classical
  simp [lineSum, unit, mul_ite, mul_comm]

private lemma incidence_pencil (x : P) (y : P) :
    incidence (fun l : L => row l x) y = q (P := P) (L := L) * unit x y + 1 := by
  rw [incidence, column_gram]
  by_cases h : y = x
  · subst y; simp [unit]
  · simp [unit, h]

private lemma exists_line_separating (x y : P) (hxy : x ≠ y) :
    ∃ l : L, x ∈ l ∧ y ∉ l := by
  classical
  obtain ⟨l, hl, hu⟩ := HasLines.existsUnique_line P L x y hxy
  by_contra hn
  push Not at hn
  have he : ∀ k : L, x ∈ k ↔ k = l := by
    intro k
    constructor
    · intro hk; exact hu k ⟨hk, hn k hk⟩
    · rintro rfl; exact hl.1
  have ht := column_total (P := P) (L := L) x
  have hsum : ∑ k : L, row k x = (1 : ℤ) := by simp [row, he]
  rw [hsum] at ht
  have := q_ge_two (P := P) (L := L)
  omega

/-- The exact integer ideal annihilating an original point unit. -/
theorem unit_mem_lattice_iff (x : P) (k : ℤ) :
    (fun y => k * unit x y) ∈ lattice (L := L) ↔
      q (P := P) (L := L) * (q (P := P) (L := L) + 1) ∣ k := by
  classical
  constructor
  · intro h
    obtain ⟨s, ht, hd⟩ := (mem_lattice_iff _).mp h
    have ht' : k = (q (P := P) (L := L) + 1) * s := by simpa [unit] using ht
    obtain ⟨l, hl⟩ := Configuration.Nondegenerate.exists_line (L := L) x
    have hh := hd l
    rw [lineSum_unit] at hh
    simp only [row, ite_eq_right hl, mul_zero, zero_sub] at hh
    obtain ⟨r, hr⟩ := (dvd_neg.mp hh)
    refine ⟨r, ?_⟩
    rw [ht', hr]
    ring
  · rintro ⟨r, rfl⟩
    refine ⟨fun l => r * ((q (P := P) (L := L) + 1) * row l x - 1), ?_⟩
    funext y
    change (∑ l : L, row l y * (r * ((q (P := P) (L := L) + 1) * row l x - 1))) = _
    calc
      _ = ∑ l : L, ((r * (q (P := P) (L := L) + 1)) *
          (row l y * row l x) - r * row l y) := by
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = (r * (q (P := P) (L := L) + 1)) *
          incidence (fun l : L => row l x) y - r * (∑ l : L, row l y) := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, incidence]
      _ = _ := by rw [incidence_pencil, column_total]; ring

/-- The exact integer ideal annihilating a difference of distinct original units. -/
theorem difference_mem_lattice_iff (x y : P) (hxy : x ≠ y) (k : ℤ) :
    (fun z => k * (unit x z - unit y z)) ∈ lattice (L := L) ↔
      q (P := P) (L := L) ∣ k := by
  classical
  constructor
  · intro h
    obtain ⟨s, ht, hd⟩ := (mem_lattice_iff _).mp h
    have hq := q_ge_two (P := P) (L := L)
    have hs : s = 0 := by
      have hz : (∑ z : P, k * (unit x z - unit y z)) = 0 := by
        simp [mul_sub, Finset.sum_sub_distrib, unit]
      rw [hz] at ht
      nlinarith
    obtain ⟨l, hx, hy⟩ := exists_line_separating (L := L) x y hxy
    have hh := hd l
    have he : lineSum (fun z => k * (unit x z - unit y z)) l = k := by
      simp only [lineSum, mul_sub, Finset.sum_sub_distrib]
      change lineSum (fun z => k * unit x z) l - lineSum (fun z => k * unit y z) l = k
      rw [lineSum_unit, lineSum_unit]
      simp [row, hx, hy]
    simpa [he, hs] using hh
  · rintro ⟨r, rfl⟩
    refine ⟨fun l => r * (row l x - row l y), ?_⟩
    funext z
    change (∑ l : L, row l z * (r * (row l x - row l y))) = _
    calc
      _ = ∑ l : L, (r * (row l z * row l x) - r * (row l z * row l y)) := by
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = r * incidence (fun l : L => row l x) z -
          r * incidence (fun l : L => row l y) z := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, incidence]
      _ = _ := by rw [incidence_pencil, incidence_pencil]; ring

/-- The exact integer ideal annihilating the original all-ones vector. -/
theorem constant_mem_lattice_iff (k : ℤ) :
    (fun _ : P => k) ∈ lattice (L := L) ↔ q (P := P) (L := L) + 1 ∣ k := by
  constructor
  · intro h
    obtain ⟨s, ht, _⟩ := (mem_lattice_iff _).mp h
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ht
    have hn : (Fintype.card P : ℤ) = q (P := P) (L := L)^2 + q (P := P) (L := L) + 1 := by
      exact_mod_cast ProjectivePlane.card_points P L
    rw [hn] at ht
    refine ⟨s - q (P := P) (L := L) * k, ?_⟩
    nlinarith
  · rintro ⟨r, rfl⟩
    refine ⟨fun _ : L => r, ?_⟩
    funext x
    simpa [incidence, ← Finset.sum_mul] using
      congrArg (fun n : ℤ => n * r) (column_total (L := L) x)

end D5.S3.Geometry.FiniteGeometry.ProjectivePlaneIntegerLattice
