/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalPathNine
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A modulus-nine gain family gives optimal error two on finite path powers of width at least three. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.ChordalAbelianReduction
import D5.S3.Combinatorics.Graph.GroupWordMetric
import D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo
import D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential
import Mathlib.Algebra.BigOperators.Fin

compile_only_with_mathlib

/-! Omega original.

A modulus-nine witness for error two on the width-`k` power path with
`9 * k` vertices. The lifted potential differences are tested in the integer
sum-zero simplex coordinates.
-/

namespace SimpleGraph.BanachPathPower.ModulusNine

open Finset GainReduction GroupWordMetric

abbrev Lattice (m : ℕ) := Fin m → ℤ
abbrev Target (m : ℕ) := Fin m → ZMod 9
abbrev H (m : ℕ) := Multiplicative (Target m)

private def basis {m : ℕ} (i : Fin m) : Lattice m :=
  fun j => if i = j then 1 else 0

private def simplex {m : ℕ} (a : Fin (m + 1)) : Lattice m :=
  fun i => (if a = i.castSucc then 1 else 0) - (if a = Fin.last m then 1 else 0)

private theorem simplex_castSucc {m : ℕ} (i : Fin m) :
    simplex i.castSucc = basis i := by
  funext j
  simp [simplex, basis]

private theorem simplex_last {m : ℕ} : simplex (Fin.last m) = fun _ => -1 := by
  funext i
  simp [simplex, (Fin.castSucc_lt_last i).ne.symm]

private def generators (m : ℕ) : Set (Lattice m) :=
  {x | x = 0 ∨ (∃ a, x = simplex a) ∨ (∃ a, x = -simplex a) ∨
    ∃ a b, x = simplex a - simplex b}

private theorem generators_zero (m : ℕ) : (0 : Lattice m) ∈ generators m := Or.inl rfl

private theorem generators_simplex {m : ℕ} (a : Fin (m + 1)) :
    simplex a ∈ generators m := Or.inr (Or.inl ⟨a, rfl⟩)

private theorem generators_sub {m : ℕ} (a b : Fin (m + 1)) :
    simplex a - simplex b ∈ generators m := Or.inr (Or.inr (Or.inr ⟨a, b, rfl⟩))

private theorem generators_neg {m : ℕ} : ∀ x ∈ generators m, -x ∈ generators m := by
  rintro _ (rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, b, rfl⟩)
  · simpa only [neg_zero] using generators_zero m
  · exact Or.inr (Or.inr (Or.inl ⟨a, rfl⟩))
  · simpa only [neg_neg] using generators_simplex a
  · rw [neg_sub]
    exact generators_sub b a

private theorem simplex_coordinate {m : ℕ} (a : Fin (m + 1)) (i : Fin m) :
    |simplex a i| ≤ 1 := by
  unfold simplex
  split_ifs <;> norm_num

private theorem generators_coordinate {m : ℕ} :
    ∀ x ∈ generators m, ∀ i, |x i| ≤ 2 := by
  rintro _ (rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, b, rfl⟩) i
  · simp
  · exact (simplex_coordinate a i).trans (by decide)
  · simpa only [Pi.neg_apply, abs_neg] using (simplex_coordinate a i).trans (by decide : (1 : ℤ) ≤ 2)
  · change |simplex a i - simplex b i| ≤ 2
    exact (abs_sub _ _).trans (by linarith [simplex_coordinate a i, simplex_coordinate b i])

private def center {m : ℕ} : Lattice m →+ (Fin (m + 1) → ℤ) where
  toFun x a := (m + 1 : ℤ) * Fin.snoc (α := fun _ => ℤ) x 0 a - ∑ i, x i
  map_zero' := by
    funext a
    refine Fin.lastCases ?_ (fun i => ?_) a <;> simp
  map_add' := by
    intro x y
    funext a
    refine Fin.lastCases ?_ (fun i => ?_) a <;>
      simp [Finset.sum_add_distrib, mul_add] <;> abel

private theorem center_sum_zero {m : ℕ} (x : Lattice m) : ∑ a, center x a = 0 := by
  change (∑ a, ((m + 1 : ℤ) * Fin.snoc (α := fun _ => ℤ) x 0 a - ∑ i, x i)) = 0
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Fin.sum_univ_castSucc]
  simp [mul_comm]

private theorem sum_basis {m : ℕ} (i : Fin m) : ∑ j, basis i j = 1 := by
  simp [basis]

private theorem center_simplex {m : ℕ} (a b : Fin (m + 1)) :
    center (simplex a) b = (if a = b then (m + 1 : ℤ) else 0) - 1 := by
  refine Fin.lastCases ?_ (fun i => ?_) a
  · refine Fin.lastCases ?_ (fun j => ?_) b
    · simp [center, simplex_last]
    · simp [center, simplex_last, (Fin.castSucc_lt_last j).ne.symm]
  · refine Fin.lastCases ?_ (fun j => ?_) b
    · simp [center, simplex_castSucc, sum_basis]
    · simp only [center, AddMonoidHom.coe_mk, ZeroHom.coe_mk, simplex_castSucc, sum_basis,
        Fin.snoc_castSucc, Fin.castSucc_inj]
      by_cases h : i = j <;> simp [basis, h]

private theorem center_generators {m : ℕ} :
    ∀ x ∈ generators m, ∀ i, |center x i| ≤ (m + 1 : ℤ) := by
  rintro _ (rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, b, rfl⟩) i
  · simp
    positivity
  · rw [center_simplex]
    rw [abs_le]
    split_ifs <;> omega
  · rw [map_neg, Pi.neg_apply, abs_neg, center_simplex]
    rw [abs_le]
    split_ifs <;> omega
  · rw [map_sub, Pi.sub_apply, center_simplex, center_simplex]
    rw [abs_le]
    split_ifs <;> omega

private def phase (m i : ℕ) : Fin (m + 1) := ⟨i % (m + 1), Nat.mod_lt i (by omega)⟩

private theorem phase_repeat {m : ℕ} (a : Fin (m + 1)) (t : ℕ) :
    phase m (a.val + t * (m + 1)) = a := by
  apply Fin.ext
  simp [phase, Nat.add_mod, Nat.mod_eq_of_lt a.isLt]

private def forward (m i j : ℕ) : Lattice m :=
  if j = i + (m + 1) then simplex (phase m i) + simplex (phase m i) else simplex (phase m i)

/-- The integer gains in a gauge with short forward edge gains equal to their start phase. -/
def gain {m n : ℕ} (a b : Fin n) : Lattice m :=
  if a < b then forward m a b else if b < a then -forward m b a else 0

private theorem gain_reverse {m n : ℕ} (a b : Fin n) :
    gain (m := m) b a = -gain a b := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [gain, h, h.not_gt]
  · simp [gain]
  · simp [gain, h, h.not_gt]

private theorem triangle {m n : ℕ} (a b c : Fin n) (hab : (pathPower n (m + 1)).Adj a b)
    (hbc : (pathPower n (m + 1)).Adj b c) (hac : (pathPower n (m + 1)).Adj a c) :
    gain (m := m) a b + gain b c - gain a c ∈ generators m := by
  let d (x y z : Fin n) := gain (m := m) x y + gain y z - gain x z
  have ordered (x y z : Fin n) (hxy : x < y) (hyz : y < z)
      (hxz : (pathPower n (m + 1)).Adj x z) : d x y z ∈ generators m := by
    have hxy' : x.val < y.val := hxy
    have hyz' : y.val < z.val := hyz
    have hspan := hxz.2.2
    simp only [d, gain, ite_eq_left hxy, ite_eq_left hyz, ite_eq_left (hxy.trans hyz), forward,
      ite_eq_right (show y.val ≠ x.val + (m + 1) by omega),
      ite_eq_right (show z.val ≠ y.val + (m + 1) by omega)]
    split_ifs
    · rw [show simplex (phase m x) + simplex (phase m y) -
          (simplex (phase m x) + simplex (phase m x)) =
          simplex (phase m y) - simplex (phase m x) by abel]
      exact generators_sub _ _
    · rw [add_comm, add_sub_cancel_right]
      exact generators_simplex _
  have swapFirst (x y z : Fin n) : d y x z = -d x y z := by
    dsimp [d]
    rw [gain_reverse x y]
    abel
  have swapLast (x y z : Fin n) : d x z y = -d x y z := by
    dsimp [d]
    rw [gain_reverse y z]
    abel
  change d a b c ∈ generators m
  rcases lt_or_gt_of_ne hab.ne with hab' | hba'
  · rcases lt_or_gt_of_ne hbc.ne with hbc' | hcb'
    · exact ordered a b c hab' hbc' hac
    · rcases lt_or_gt_of_ne hac.ne with hac' | hca'
      · rw [← neg_neg (d a b c), ← swapLast a b c]
        exact generators_neg _ (ordered a c b hac' hcb' hab)
      · rw [← neg_neg (d a b c), ← swapLast a b c, ← neg_neg (d a c b), ← swapFirst a c b, neg_neg]
        exact ordered c a b hca' hab' hbc.symm
  · rcases lt_or_gt_of_ne hac.ne with hac' | hca'
    · rw [swapFirst b a c]
      exact generators_neg _ (ordered b a c hba' hac' hbc)
    · rcases lt_or_gt_of_ne hbc.ne with hbc' | hcb'
      · rw [swapFirst b a c, ← neg_neg (d b a c), ← swapLast b a c, neg_neg]
        exact ordered b c a hbc' hca' hab.symm
      · rw [swapFirst b a c, ← neg_neg (d b a c), ← swapLast b a c, neg_neg, swapFirst c b a]
        exact generators_neg _ (ordered c b a hcb' hba' hac.symm)

private abbrev Vertex (m : ℕ) := Fin (9 * (m + 1))

private def atRow {m : ℕ} (a : Fin (m + 1)) (t : ℕ) (ht : t ≤ 8) : Vertex m :=
  ⟨a.val + t * (m + 1), by
    have h := Nat.mul_le_mul_right (m + 1) ht
    nlinarith [a.isLt]⟩

private theorem column_edge {m : ℕ} (a : Fin (m + 1)) {t : ℕ} (ht : t + 1 ≤ 8) :
    (pathPower (9 * (m + 1)) (m + 1)).Adj (atRow a t (by omega)) (atRow a (t + 1) ht) := by
  have h : (atRow a (t + 1) ht).val = (atRow a t (by omega)).val + (m + 1) := by
    dsimp [atRow]
    rw [Nat.add_mul]
    omega
  refine ⟨fun eq => ?_, by omega, h.le⟩
  have := congrArg Fin.val eq
  omega

private theorem row_edge {m : ℕ} {a b : Fin (m + 1)} (hab : a < b) (t : ℕ) (ht : t ≤ 8) :
    (pathPower (9 * (m + 1)) (m + 1)).Adj (atRow a t ht) (atRow b t ht) := by
  have hab' : a.val < b.val := hab
  have hb := b.isLt
  refine ⟨fun eq => ?_, ?_, ?_⟩
  · have := congrArg Fin.val eq
    dsimp [atRow] at this
    omega
  · dsimp [atRow]
    omega
  · dsimp [atRow]
    omega

private theorem column_gain {m : ℕ} (a : Fin (m + 1)) {t : ℕ} (ht : t + 1 ≤ 8) :
    gain (m := m) (atRow a t (by omega)) (atRow a (t + 1) ht) = simplex a + simplex a := by
  have he : (atRow a (t + 1) ht).val = (atRow a t (by omega)).val + (m + 1) := by
    dsimp [atRow]
    rw [Nat.add_mul]
    omega
  have hlt : atRow a t (by omega) < atRow a (t + 1) ht := by
    change (atRow a t (by omega)).val < (atRow a (t + 1) ht).val
    omega
  simp only [gain, ite_eq_left hlt, forward, ite_eq_left he]
  rw [show (atRow a t (by omega)).val = a.val + t * (m + 1) by rfl, phase_repeat]

private theorem row_gain {m : ℕ} {a b : Fin (m + 1)} (hab : a < b) (t : ℕ) (ht : t ≤ 8) :
    gain (m := m) (atRow a t ht) (atRow b t ht) = simplex a := by
  have hab' : a.val < b.val := hab
  have hb := b.isLt
  have hlt : atRow a t ht < atRow b t ht := by
    change (atRow a t ht).val < (atRow b t ht).val
    dsimp [atRow]
    omega
  have he : (atRow b t ht).val ≠ (atRow a t ht).val + (m + 1) := by
    dsimp [atRow]
    omega
  simp only [gain, ite_eq_left hlt, forward, ite_eq_right he]
  rw [show (atRow a t ht).val = a.val + t * (m + 1) by rfl, phase_repeat]


private theorem integral_obstruction {m : ℕ} (hm : 2 ≤ m)
    (p : Vertex m → Lattice m)
    (hp : ∀ v w, (pathPower (9 * (m + 1)) (m + 1)).Adj v w →
      gain (m := m) v w - (p w - p v) ∈ generators m) : False := by
  let P (v : Vertex m) := center (p v)
  let base (a : Fin (m + 1)) := atRow a 0 (by decide)
  let finish (a : Fin (m + 1)) := atRow a 8 (by decide)
  let a₀ : Fin (m + 1) := 0
  let disp (a : Fin (m + 1)) := P (finish a) - P (base a)
  have step (a : Fin (m + 1)) (t : ℕ) (ht : t + 1 ≤ 8) :
      (m : ℤ) - 1 ≤ P (atRow a (t + 1) ht) a - P (atRow a t (by omega)) a := by
    have hh := center_generators _ (hp _ _ (column_edge a ht)) a
    rw [column_gain a ht, map_sub, map_sub, map_add, Pi.sub_apply, Pi.sub_apply,
      Pi.add_apply, center_simplex, ite_eq_left rfl] at hh
    have h := (abs_le.mp hh).2
    change (_ : ℤ) ≤ _
    dsimp [P]
    linarith
  have column (a : Fin (m + 1)) (t : ℕ) (ht : t ≤ 8) :
      (t : ℤ) * ((m : ℤ) - 1) ≤ P (atRow a t ht) a - P (base a) a := by
    induction t with
    | zero => simp [base]
    | succ t ih =>
      have hprev := ih (by omega)
      have hstep := step a t ht
      push_cast
      nlinarith
  have positive (a : Fin (m + 1)) : 0 < disp a₀ a := by
    have hcol := column a 8 (by decide)
    change (8 : ℤ) * ((m : ℤ) - 1) ≤ disp a a at hcol
    by_cases h : a = a₀
    · subst a
      omega
    have hlt : a₀ < a := Nat.pos_of_ne_zero (fun he => h (Fin.ext he))
    have hrow0 := center_generators _ (hp _ _ (row_edge hlt 0 (by decide))) a
    have hrow8 := center_generators _ (hp _ _ (row_edge hlt 8 (by decide))) a
    rw [row_gain hlt, map_sub, map_sub, Pi.sub_apply, Pi.sub_apply] at hrow0 hrow8
    change |center (simplex a₀) a - (P (base a) a - P (base a₀) a)| ≤ _ at hrow0
    change |center (simplex a₀) a - (P (finish a) a - P (finish a₀) a)| ≤ _ at hrow8
    have h0 := (abs_le.mp hrow0).2
    have h8 := (abs_le.mp hrow8).1
    simp only [disp, Pi.sub_apply] at hcol ⊢
    omega
  have hsum : ∑ a, disp a₀ a = 0 := by
    simp [disp, P, Finset.sum_sub_distrib, center_sum_zero]
  have hpos : 0 < ∑ a, disp a₀ a :=
    Finset.sum_pos (fun a _ => positive a) Finset.univ_nonempty
  omega

private theorem short_one_iff {A : Type*} [AddCommMonoid A] (U : Set A) (x : A) :
    Short U 1 x ↔ x ∈ U := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv 0
  · intro h
    exact ⟨fun _ => x, fun _ => h, by simp⟩

private def letters (m : ℕ) : Set (H m) :=
  {x | x.toAdd ∈ reduce 9 '' generators m}

private theorem letters_inv (m : ℕ) : ∀ x ∈ letters m, x⁻¹ ∈ letters m := by
  rintro x ⟨v, h, he⟩
  refine ⟨-v, generators_neg v h, ?_⟩
  change reduce 9 (-v) = -x.toAdd
  rw [map_neg, he]

private theorem letters_conj (m : ℕ) (a : H m) : ∀ x ∈ letters m, a * x * a⁻¹ ∈ letters m := by
  intro x hx
  rwa [mul_comm a x, mul_assoc, mul_inv_cancel, mul_one]

private theorem letters_generate (m : ℕ) : Generates (letters m) := by
  let S : AddSubgroup (Target m) :=
    { carrier := {x | ∃ n, Fits (letters m) n (Multiplicative.ofAdd x)}
      zero_mem' := ⟨0, Fits.one⟩
      add_mem' := fun ⟨n, hn⟩ ⟨p, hp⟩ => ⟨n + p, hn.mul hp⟩
      neg_mem' := fun ⟨n, hn⟩ => ⟨n, hn.inv (letters_inv m)⟩ }
  have hB (i : Fin m) : reduce 9 (basis i) ∈ S := by
    change ∃ n, Fits (letters m) n (Multiplicative.ofAdd (reduce 9 (basis i)))
    rw [← simplex_castSucc i]
    exact ⟨1, Fits.of_mem ⟨_, generators_simplex i.castSucc, rfl⟩⟩
  intro x
  have hx : (∑ i : Fin m, (x.toAdd i).val • reduce 9 (basis i)) = x.toAdd := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · change (x.toAdd j).val • ((basis j j : ℤ) : ZMod 9) = x.toAdd j
      simp [basis, nsmul_eq_mul]
    · intro i _ hij
      change (x.toAdd i).val • ((basis i j : ℤ) : ZMod 9) = 0
      simp [basis, hij]
    · simp
  have hS : x.toAdd ∈ S := by
    rw [← hx]
    exact AddSubgroup.sum_mem S (fun i _ => S.nsmul_mem (hB i) _)
  exact hS

/-- The bi-invariant Cayley metric on the finite abelian target. -/
@[instance_reducible]
noncomputable def cayleyMetric (m : ℕ) : MetricSpace (H m) :=
  metric (letters_generate m) (letters_inv m)

theorem cayley_left (m : ℕ) : letI := cayleyMetric m; IsIsometricSMul (H m) (H m) :=
  left_isometric (letters_generate m) (letters_inv m)

theorem cayley_right (m : ℕ) : letI := cayleyMetric m; IsIsometricSMul (H m)ᵐᵒᵖ (H m) :=
  right_isometric (letters_generate m) (letters_inv m) (letters_conj m)

private theorem length_le_one_iff {m : ℕ} (x : H m) :
    length (letters_generate m) x ≤ 1 ↔ x ∈ letters m := by
  rw [length_le_iff]
  refine ⟨?_, Fits.of_mem⟩
  rintro ⟨l, hmem, hlen, rfl⟩
  cases l with
  | nil =>
    change (0 : Target m) ∈ reduce 9 '' generators m
    exact ⟨0, generators_zero m, map_zero _⟩
  | cons a l =>
    have hl : l = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst l
    simpa using hmem a List.mem_cons_self

private theorem distance_le_one_iff {m : ℕ} (x y : Target m) :
    let := cayleyMetric m
    Dist.dist (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) ≤ (1 : ℝ) ↔
      x - y ∈ reduce 9 '' generators m := by
  let := cayleyMetric m
  change (length (letters_generate m) (Multiplicative.ofAdd (-x + y)) : ℝ) ≤ 1 ↔ _
  rw [← length_inv (letters_generate m) (letters_inv m)]
  have he : (Multiplicative.ofAdd (-x + y))⁻¹ = Multiplicative.ofAdd (x - y) := by
    change -(-x + y) = x - y
    abel
  rw [he, ← Nat.cast_one (R := ℝ), Nat.cast_le, length_le_one_iff]
  rfl

/-- The explicit reduced periodic gain on the power path. -/
def metricGain (m : ℕ) (a b : Vertex m) : H m :=
  Multiplicative.ofAdd (reduce 9 (gain (m := m) a b))

private theorem metricGain_reverse (m : ℕ) (a b : Vertex m) :
    metricGain m b a = (metricGain m a b)⁻¹ := by
  change reduce 9 (gain (m := m) b a) = -(reduce 9 (gain a b))
  rw [gain_reverse, map_neg]

private theorem metricGain_triangle (m : ℕ) (a b c : Vertex m)
    (hab : (pathPower (9 * (m + 1)) (m + 1)).Adj a b)
    (hbc : (pathPower (9 * (m + 1)) (m + 1)).Adj b c)
    (hac : (pathPower (9 * (m + 1)) (m + 1)).Adj a c) :
    let := cayleyMetric m
    Dist.dist (metricGain m a b * metricGain m b c) (metricGain m a c) ≤ 1 := by
  let := cayleyMetric m
  apply (distance_le_one_iff _ _).2
  refine ⟨_, triangle a b c hab hbc hac, ?_⟩
  rw [map_sub, map_add]
  rfl

private theorem interval_bound (m : ℕ) :
    let := cayleyMetric m
    (pathPower (9 * (m + 1)) (m + 1)).IsChordal ∧
    ∃ p : Vertex m → H m, ∀ u v, (pathPower (9 * (m + 1)) (m + 1)).Adj u v →
      Dist.dist (metricGain m u v) ((p u)⁻¹ * p v) ≤ 2 := by
  let := cayleyMetric m
  let := cayley_left m
  let := cayley_right m
  obtain ⟨l, r, _, hI, hshape⟩ := pathPower_isIntervalGraph (9 * (m + 1)) (m + 1)
  simpa using intervalGraph_isChordal_and_two_approximate_gain_potential l r hI hshape
    (metricGain m) 1 (by norm_num) (fun a b _ => metricGain_reverse m a b)
    (metricGain_triangle m)

private theorem no_modular_potential {m : ℕ} (hm : 2 ≤ m) (p : Vertex m → Target m)
    (hp : ∀ v w, (pathPower (9 * (m + 1)) (m + 1)).Adj v w →
      reduce 9 (gain (m := m) v w) - (p w - p v) ∈ reduce 9 '' generators m) : False := by
  let G := pathPower (9 * (m + 1)) (m + 1)
  let g : Vertex m → Vertex m → Lattice m := gain (m := m)
  have htri (v w x : Vertex m) (hvw : G.Adj v w) (hwx : G.Adj w x) (hvx : G.Adj v x)
      (i : Fin m) : |g v w i + g w x i - g v x i| ≤ (2 : ℤ) :=
    generators_coordinate _ (triangle v w x hvw hwx hvx) i
  obtain ⟨r, hr, hmem, hclosed⟩ :=
    exists_integral_residuals_of_bounded_modular_potential
      (G := G) g (fun v w _ => gain_reverse v w) (generators m) generators_neg
      (B := 2) generators_coordinate htri (k := 1) (q := 9) (by decide) p
      (fun v w h => (short_one_iff _ _).2 (hp v w h))
  have hG : G.IsChordal := (interval_bound m).1
  obtain ⟨p', hp'⟩ := integrate hG (fun v w => g v w - r v w)
    (fun v w h => by
      change g w v - r w v = -(g v w - r v w)
      rw [show g w v = -g v w from gain_reverse _ _, hr v w h]
      abel)
    (fun v w x hvw hwx hvx => by
      have he := hclosed v w x hvw hwx hvx
      calc
        _ = (g v w + g w x - g v x) - (r v w + r w x - r v x) +
            (g v x - r v x) := by abel
        _ = _ := by rw [he, sub_self, zero_add])
  apply integral_obstruction hm p'
  intro v w h
  change g v w - (p' w - p' v) ∈ generators m
  rw [← hp' v w h, sub_sub_cancel]
  exact (short_one_iff _ _).1 (hmem v w h)


/-- For every width `m + 1 ≥ 3`, the displayed gain in
`(ℤ/9ℤ)^m` has optimum two on the width-`(m + 1)` power path with
`9 * (m + 1)` vertices. -/
theorem optimal_error {m : ℕ} (hm : 2 ≤ m) :
    let := cayleyMetric m
    (∀ a b, metricGain m b a = (metricGain m a b)⁻¹) ∧
    (∀ a b c, (pathPower (9 * (m + 1)) (m + 1)).Adj a b →
      (pathPower (9 * (m + 1)) (m + 1)).Adj b c →
      (pathPower (9 * (m + 1)) (m + 1)).Adj a c →
      Dist.dist (metricGain m a b * metricGain m b c) (metricGain m a c) ≤ 1) ∧
    (∃ p : Vertex m → H m, ∀ a b, (pathPower (9 * (m + 1)) (m + 1)).Adj a b →
      Dist.dist (metricGain m a b) ((p a)⁻¹ * p b) ≤ 2) ∧
    ∀ p : Vertex m → H m, ∃ a b, (pathPower (9 * (m + 1)) (m + 1)).Adj a b ∧
      2 ≤ Dist.dist (metricGain m a b) ((p a)⁻¹ * p b) := by
  let := cayleyMetric m
  refine ⟨metricGain_reverse m, metricGain_triangle m, (interval_bound m).2, fun p => ?_⟩
  by_contra! h
  apply no_modular_potential hm (fun v => (p v).toAdd)
  intro a b hab
  let x := reduce 9 (gain (m := m) a b)
  let y := (p b).toAdd - (p a).toAdd
  have he : Multiplicative.ofAdd y = (p a)⁻¹ * p b := by
    dsimp [y]
    change (p b).toAdd - (p a).toAdd = -(p a).toAdd + (p b).toAdd
    abel
  have hlt : (length (letters_generate m) ((metricGain m a b)⁻¹ * ((p a)⁻¹ * p b)) : ℝ) < 2 :=
    h a b hab
  have hn : length (letters_generate m) ((metricGain m a b)⁻¹ * ((p a)⁻¹ * p b)) < 2 := by
    exact_mod_cast hlt
  have hb : Dist.dist (metricGain m a b) ((p a)⁻¹ * p b) ≤ (1 : ℝ) := by
    change (length (letters_generate m) ((metricGain m a b)⁻¹ * ((p a)⁻¹ * p b)) : ℝ) ≤ 1
    exact_mod_cast Nat.le_of_lt_succ hn
  change x - y ∈ reduce 9 '' generators m
  exact (distance_le_one_iff x y).1 (he.symm ▸ hb)

end SimpleGraph.BanachPathPower.ModulusNine
