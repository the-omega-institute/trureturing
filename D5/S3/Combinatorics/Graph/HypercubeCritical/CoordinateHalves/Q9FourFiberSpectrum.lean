/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourFiberSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourFiberSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The square of the signed four-cube row on fibers of a balanced cubic support. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection

/-! The TRUE-prefix signed row restricts to occupied patterns at both steps of
the four-cube square identity, constraining projected degrees and fiber support. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip)
open BalancedCubeComponentBoundary (directions)
open Q9SignedProjection (join fiber signedRow q9_signed_row_eq_zero_outside_projection)
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private coeff matrix_coeff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private matrix_row from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
open private theta theta_unit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeSigning
open private matrix_true_prefix from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangIntegralSwitching

/-- The projection to coordinates zero through three, in coordinate order. -/
def leftProjection (C : Finset (Q 9)) : Finset (Q 4) :=
  C.image fun u i => u (i.castAdd 5)

private theorem mem_leftProjection {C : Finset (Q 9)} {x : Q 4} :
    x ∈ leftProjection C ↔ ∃ y : Q 5, join x y ∈ C := by
  constructor
  · rintro hx
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    exact ⟨fun j => u (j.natAdd 4), by
      simpa only [join, Fin.append_castAdd_natAdd] using hu⟩
  · rintro ⟨y, hy⟩
    exact mem_image.mpr ⟨join x y, hy, funext fun i => Fin.append_left x y i⟩

/-- Both the fiber and its TRUE-prefix signed image are supported in the projection.
Only the ambient row equation and vanishing off the ambient support are required. -/
theorem fiber_and_signedRow_supported {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hz : ∀ u ∉ C, z u = 0) (hrow : ∀ u, signedRow z u = 3 * z u)
    (y : Q 5) {x : Q 4} (hx : x ∉ leftProjection C) :
    fiber z y x = 0 ∧ signedRow (fiber z y) x = 0 := by
  have hzero (v : Q 5) : fiber z v x = 0 :=
    hz _ (fun hv => hx (mem_leftProjection.mpr ⟨v, hv⟩))
  exact ⟨hzero y, q9_signed_row_eq_zero_outside_projection hrow hzero y⟩

private theorem gauge_row (f : Q 4 → ℤ) (x : Q 4) :
    (huangMatrix 4).mulVec (fun y => theta y * (f y : ℝ)) x =
      theta x * (signedRow f x : ℝ) := by
  rw [matrix_row, signedRow]
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  change huangMatrix 4 x (flip x i) * _ = _
  rw [matrix_true_prefix]
  rcases theta_unit (flip x i) with h | h <;> rw [h] <;> ring

/-- The integral TRUE-prefix row operator on the four-cube squares to four times
the identity, by diagonal sign conjugacy with Huang's matrix. -/
theorem signedRow_square (f : Q 4 → ℤ) (x : Q 4) :
    signedRow (signedRow f) x = 4 * f x := by
  let g : Q 4 → ℝ := fun y => theta y * (f y : ℝ)
  have hsquare : (huangMatrix 4).mulVec ((huangMatrix 4).mulVec g) = (4 : ℝ) • g := by
    rw [matrix_coeff, matrix_coeff, (coeff 4).symm_apply_apply, Sensitivity.f_squared,
      map_smul]
    norm_num
  have h := congrFun hsquare x
  have hg : (huangMatrix 4).mulVec g = fun y => theta y * (signedRow f y : ℝ) :=
    funext (gauge_row f)
  rw [hg, gauge_row] at h
  change theta x * (signedRow (signedRow f) x : ℝ) = 4 * (theta x * (f x : ℝ)) at h
  have hcast : (signedRow (signedRow f) x : ℝ) = 4 * (f x : ℝ) := by
    rcases theta_unit x with ht | ht <;> rw [ht] at h <;> linarith
  exact_mod_cast hcast

/-- The signed row of the induced four-cube on `P`, indexed by the occupied
coordinate flips. -/
def signedRowOn (P : Finset (Q 4)) (f : Q 4 → ℤ) (x : Q 4) : ℤ :=
  ∑ i ∈ directions P x, truePrefixSign x i * f (flip x i)

private theorem signedRow_eq_on (P : Finset (Q 4)) {f : Q 4 → ℤ}
    (hf : ∀ x ∉ P, f x = 0) (x : Q 4) : signedRow f x = signedRowOn P f x := by
  unfold signedRow signedRowOn
  symm
  apply sum_subset (subset_univ _)
  intro i _ hi
  rw [hf _ (fun h => hi ((mem_directions P x i).mpr h)), mul_zero]

/-- If both a vector and its Huang signed image vanish outside `P`, applying
the signed rows restricted to `P` twice recovers four times the vector. -/
theorem signedRowOn_square {P : Finset (Q 4)} {f : Q 4 → ℤ}
    (hf : ∀ x ∉ P, f x = 0) (hrow : ∀ x ∉ P, signedRow f x = 0) (x : Q 4) :
    signedRowOn P (signedRowOn P f) x = 4 * f x := by
  rw [← funext (signedRow_eq_on P hf), ← signedRow_eq_on P hrow, signedRow_square]

private theorem abs_prefixSign (x : Q 4) (i : Fin 4) : |truePrefixSign x i| = 1 := by
  simp [truePrefixSign, abs_pow]

private theorem abs_signedRowOn_le (P : Finset (Q 4)) {f : Q 4 → ℤ}
    (hunit : ∀ x, |f x| ≤ 1) (x : Q 4) :
    |signedRowOn P f x| ≤ (directions P x).card := by
  unfold signedRowOn
  calc
    _ ≤ ∑ i ∈ directions P x, |truePrefixSign x i * f (flip x i)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ directions P x, (1 : ℤ) := by
      apply sum_le_sum
      intro i _
      simpa only [abs_mul, abs_prefixSign, one_mul] using hunit (flip x i)
    _ = _ := by simp

private theorem directions_nonempty_and_leaf_full {P : Finset (Q 4)} {f : Q 4 → ℤ}
    (hf : ∀ x ∉ P, f x = 0) (hrow : ∀ x ∉ P, signedRow f x = 0)
    (hunit : ∀ x, |f x| ≤ 1) {x : Q 4} (hx : |f x| = 1) :
    (directions P x).Nonempty ∧
      ∀ i : Fin 4, directions P x = {i} → (directions P (flip x i)).card = 4 := by
  have hsquare : |signedRowOn P (signedRowOn P f) x| = 4 := by
    rw [signedRowOn_square hf hrow, abs_mul, hx, mul_one]
    decide
  constructor
  · by_contra hempty
    simp [signedRowOn, not_nonempty_iff_eq_empty.mp hempty] at hsquare
  · intro i hi
    simp only [signedRowOn, hi, sum_singleton, abs_mul, abs_prefixSign, one_mul] at hsquare
    have hlower := abs_signedRowOn_le P hunit (flip x i)
    unfold signedRowOn at hlower
    rw [hsquare] at hlower
    have hupper := card_le_univ (directions P (flip x i))
    simp only [Fintype.card_fin] at hupper
    omega

open Classical in
private theorem abs_fiber {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hunit : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ C, z u = 0)
    (y : Q 5) (x : Q 4) :
    |fiber z y x| = if join x y ∈ C then 1 else 0 := by
  change |z (join x y)| = _
  split_ifs with h
  · rcases hunit _ h with h' | h' <;> simp [h']
  · simp [hzero _ h]

open Classical in
/-- The four-coordinate projection of a balanced cubic support has no isolated
vertex. If a projected vertex has a unique neighbor, that neighbor has degree four.
The directions enumerate the distinct hypercube neighbors obtained by a single flip. -/
theorem balanced_projection_no_isolated_and_leaf_full {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) {x : Q 4} (hx : x ∈ leftProjection C) :
    (directions (leftProjection C) x).Nonempty ∧
      ∀ i : Fin 4, directions (leftProjection C) x = {i} →
        (directions (leftProjection C) (flip x i)).card = 4 := by
  obtain ⟨z, hunit, hzero, _, hrow⟩ := q9_integral_true_prefix_switching hreg hb
  obtain ⟨y, hy⟩ := mem_leftProjection.mp hx
  have hsupport (p : Q 4) (hp : p ∉ leftProjection C) :=
    fiber_and_signedRow_supported hzero hrow y hp
  have hbound (p : Q 4) : |fiber z y p| ≤ 1 := by
    rw [abs_fiber hunit hzero]
    split <;> decide
  have hxunit : |fiber z y x| = 1 := by rw [abs_fiber hunit hzero, ite_eq_left hy]
  exact directions_nonempty_and_leaf_full
    (fun p hp => (hsupport p hp).1) (fun p hp => (hsupport p hp).2) hbound hxunit

/-- At a unit entry whose projected degree and neighbors' degrees are all two,
every projected two-step walk transports the entry with its path sign. -/
theorem two_step_signed_value {P : Finset (Q 4)} {f : Q 4 → ℤ}
    (hf : ∀ p ∉ P, f p = 0) (hrow : ∀ p ∉ P, signedRow f p = 0)
    (hunit : ∀ p, |f p| ≤ 1) {x : Q 4} (hx : |f x| = 1)
    (hdegree : (directions P x).card = 2)
    (hnear : ∀ i ∈ directions P x, (directions P (flip x i)).card = 2)
    {i j : Fin 4} (hi : i ∈ directions P x) (hj : j ∈ directions P (flip x i)) :
    truePrefixSign x i * (truePrefixSign (flip x i) j * f (flip (flip x i) j)) = f x := by
  -- Multiply all terms by the sign at x, so the four contributions sum to +4.
  let term (a b : Fin 4) := f x *
    (truePrefixSign x a * (truePrefixSign (flip x a) b * f (flip (flip x a) b)))
  have hsign : f x = 1 ∨ f x = -1 := (abs_eq (by decide)).mp hx
  have hterm (a b : Fin 4) : term a b ≤ 1 := by
    apply (le_abs_self _).trans
    simpa only [term, abs_mul, abs_prefixSign, hx, one_mul] using
      hunit (flip (flip x a) b)
  have hbound (a : Fin 4) (ha : a ∈ directions P x) :
      (∑ b ∈ directions P (flip x a), term a b) ≤ (2 : ℤ) := by
    calc
      _ ≤ ∑ _b ∈ directions P (flip x a), (1 : ℤ) := sum_le_sum fun b _ => hterm a b
      _ = _ := by simp [hnear a ha]
  have hsum :
      (∑ a ∈ directions P x, ∑ b ∈ directions P (flip x a), term a b) =
        ∑ _a ∈ directions P x, (2 : ℤ) := by
    calc
      _ = f x * signedRowOn P (signedRowOn P f) x := by
        simp only [signedRowOn, mul_sum, term]
      _ = 4 := by
        rw [signedRowOn_square hf hrow]
        rcases hsign with h | h <;> norm_num [h]
      _ = _ := by norm_num [hdegree]
  have hinner := (sum_eq_sum_iff_of_le hbound).mp hsum i hi
  have hin : (∑ b ∈ directions P (flip x i), term i b) =
      ∑ _b ∈ directions P (flip x i), (1 : ℤ) := by
    simpa [hnear i hi] using hinner
  have heq := (sum_eq_sum_iff_of_le (fun b _ => hterm i b)).mp hin j hj
  dsimp only [term] at heq
  rcases hsign with h | h
  · simpa only [h, one_mul] using heq
  · simpa only [h, neg_one_mul, neg_eq_iff_eq_neg] using heq

open Classical in
/-- Along a projected two-step walk in a degree-two projection, the endpoints
are occupied in exactly the same suffix fibers. -/
theorem balanced_projection_two_step_mem_iff {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hdegree : ∀ p ∈ leftProjection C, (directions (leftProjection C) p).card = 2)
    (y : Q 5) {x : Q 4} (hx : x ∈ leftProjection C) {i j : Fin 4}
    (hi : i ∈ directions (leftProjection C) x)
    (hj : j ∈ directions (leftProjection C) (flip x i)) :
    join x y ∈ C ↔ join (flip (flip x i) j) y ∈ C := by
  obtain ⟨z, hunit, hzero, _, hrow⟩ := q9_integral_true_prefix_switching hreg hb
  have hsupport (p : Q 4) (hp : p ∉ leftProjection C) :=
    fiber_and_signedRow_supported hzero hrow y hp
  have hbound (p : Q 4) : |fiber z y p| ≤ 1 := by
    rw [abs_fiber hunit hzero]
    split <;> decide
  have step (p : Q 4) (hp : join p y ∈ C) {a b : Fin 4}
      (ha : a ∈ directions (leftProjection C) p)
      (hb' : b ∈ directions (leftProjection C) (flip p a)) :
      join (flip (flip p a) b) y ∈ C := by
    have hentry : |fiber z y p| = 1 := by rw [abs_fiber hunit hzero, ite_eq_left hp]
    have hphase := two_step_signed_value
      (fun v hv => (hsupport v hv).1) (fun v hv => (hsupport v hv).2) hbound hentry
      (hdegree p (mem_leftProjection.mpr ⟨y, hp⟩))
      (fun k hk => hdegree _ ((mem_directions _ _ k).mp hk)) ha hb'
    by_contra h
    have hz : fiber z y (flip (flip p a) b) = 0 := hzero _ h
    rw [hz, mul_zero, mul_zero] at hphase
    rw [← hphase] at hentry
    norm_num at hentry
  refine ⟨fun h => step x h hi hj, fun h => ?_⟩
  have hji : j ∈ directions (leftProjection C) (flip (flip x i) j) := by
    rw [mem_directions, BalancedCriticalSpectrum.flip_flip]
    exact (mem_directions _ _ i).mp hi
  have hii : i ∈ directions (leftProjection C) (flip (flip (flip x i) j) j) := by
    rw [BalancedCriticalSpectrum.flip_flip, mem_directions, BalancedCriticalSpectrum.flip_flip]
    exact hx
  simpa only [BalancedCriticalSpectrum.flip_flip] using step _ h hji hii

#print axioms fiber_and_signedRow_supported
#print axioms signedRow_square
#print axioms signedRowOn_square
#print axioms balanced_projection_no_isolated_and_leaf_full
#print axioms two_step_signed_value
#print axioms balanced_projection_two_step_mem_iff

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum
