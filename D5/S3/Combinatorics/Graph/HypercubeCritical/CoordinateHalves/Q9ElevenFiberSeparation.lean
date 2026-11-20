/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9ElevenFiberSeparation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9ElevenFiberSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Seven signed-fiber inequalities exclude a balanced cubic eleven-pattern projection. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowExterior
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum

/-! A structural exclusion for Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2.
The exterior rows leave six ternary entries. Seven linear inequalities then
eliminate signed fibers in pairs until every fiber vanishes at code four. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ElevenFiberSeparation

open Finset
open BalancedCriticalSpectrum (Q IsBalanced flip)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open Q9SignedProjection (join fiber signedRow leftParitySign q9_signed_row_split)
open Q9ThetaProjection (leftCode)
open Q9FourFiberSpectrum (leftProjection fiber_and_signedRow_supported)
open private abs_prefixSign mem_leftProjection from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum
open private pattern flipCode flip_pattern prefixSign prefixSign_eq sum_four from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private code column unitOrZero occupied fiber_admissible fiber_occupied from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSelfAdjoint
open private projection_avoid not_mem_projection_of_zero_column from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowExterior
open private flip_join_left flip_join_right sign_join_left sign_join_right left_lt_right from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection

/-- The four-bit projection with omitted codes 0, 1, 6, 11, and 14. -/
def elevenProjection : Finset (BitVec 4) := {2, 3, 4, 5, 7, 8, 9, 10, 12, 13, 15}

/-- An integer-valued fiber indexed by the little-endian four-bit code. -/
abbrev Fiber := BitVec 4 → ℤ

/-- Huang's signed horizontal row in little-endian codes. -/
def horizontalRow (f : Fiber) (k : BitVec 4) : ℤ :=
  prefixSign k 0 * f (flipCode k 0) + (prefixSign k 1 * f (flipCode k 1) +
    (prefixSign k 2 * f (flipCode k 2) + prefixSign k 3 * f (flipCode k 3)))

/-- The row remaining after subtracting the horizontal contribution and
multiplying by the parity of the four horizontal coordinates. -/
def residual (f : Fiber) (k : BitVec 4) : ℤ :=
  leftParitySign (pattern k) * (3 * f k - horizontalRow f k)

/-- Ternary entries, horizontal degree at most three on the support, and
agreement with the Huang signs on occupied horizontal edges. -/
def Admissible (f : Fiber) : Prop :=
  (∀ k : Fin 16, unitOrZero (f (code k))) ∧
  ∀ k : Fin 16, f (code k) ≠ 0 →
    (∑ i : Fin 4, occupied (f (flipCode (code k) i))) ≤ 3 ∧
    ∀ i : Fin 4, f (flipCode (code k) i) ≠ 0 →
      f (code k) * f (flipCode (code k) i) = prefixSign (code k) i

private instance (f : Fiber) : Decidable (Admissible f) := by
  unfold Admissible
  infer_instance

/-- In the intersection of a fiber and a signed neighbor, the products equal
the horizontal parity sign and no two points are horizontally adjacent. -/
def Compatible (f g : Fiber) : Prop :=
  ∀ k : Fin 16, f (code k) ≠ 0 → g (code k) ≠ 0 →
    f (code k) * g (code k) = leftParitySign (pattern (code k)) ∧
    ∀ i : Fin 4, f (flipCode (code k) i) ≠ 0 → g (flipCode (code k) i) = 0

private instance (f g : Fiber) : Decidable (Compatible f g) := by
  unfold Compatible
  infer_instance

private def reconstruct (a b c d e h : ℤ) (k : BitVec 4) : ℤ :=
  let atNine := -b - d
  let atFifteen := -b + atNine - e
  match k.toNat with
  | 2 => a
  | 3 => b
  | 4 => c
  | 5 => d
  | 7 => a - c
  | 8 => -a - c
  | 9 => atNine
  | 10 => e
  | 12 => e - atFifteen
  | 13 => h
  | 15 => atFifteen
  | _ => 0

private theorem reconstruct_eq (f : Fiber)
    (hout : ∀ k ∉ elevenProjection, f k = 0 ∧ horizontalRow f k = 0) :
    f = reconstruct (f 2) (f 3) (f 4) (f 5) (f 10) (f 13) := by
  obtain ⟨z0, e0⟩ := hout 0 (by decide +kernel)
  obtain ⟨z1, e1⟩ := hout 1 (by decide +kernel)
  obtain ⟨z6, e6⟩ := hout 6 (by decide +kernel)
  obtain ⟨z11, e11⟩ := hout 11 (by decide +kernel)
  obtain ⟨z14, e14⟩ := hout 14 (by decide +kernel)
  change 1 * f 1 + (1 * f 2 + (1 * f 4 + 1 * f 8)) = 0 at e0
  change 1 * f 0 + (-1 * f 3 + (-1 * f 5 + -1 * f 9)) = 0 at e1
  change 1 * f 7 + (1 * f 4 + (-1 * f 2 + 1 * f 14)) = 0 at e6
  change 1 * f 10 + (-1 * f 9 + (1 * f 15 + 1 * f 3)) = 0 at e11
  change 1 * f 15 + (1 * f 12 + (-1 * f 10 + 1 * f 6)) = 0 at e14
  have atSeven : f 7 = f 2 - f 4 := by omega
  have atEight : f 8 = -f 2 - f 4 := by omega
  have atNine : f 9 = -f 3 - f 5 := by omega
  have atFifteen : f 15 = -f 3 + (-f 3 - f 5) - f 10 := by omega
  have atTwelve : f 12 = f 10 - (-f 3 + (-f 3 - f 5) - f 10) := by omega
  have atCode (k : Fin 16) :
      f (code k) = reconstruct (f 2) (f 3) (f 4) (f 5) (f 10) (f 13) (code k) := by
    fin_cases k
    all_goals
      first | exact z0 | exact z1 | exact z6 | exact z11 | exact z14 |
        exact atSeven | exact atEight | exact atNine | exact atFifteen |
        exact atTwelve | rfl
  exact funext fun k => atCode k.toFin

private def entries : List ℤ := [-1, 0, 1]

private def initial : List Fiber :=
  (do
    let a ← entries
    let b ← entries
    let c ← entries
    let d ← entries
    let e ← entries
    let h ← entries
    pure (reconstruct a b c d e h)).filter fun f => decide (Admissible f)

private theorem mem_initial {f : Fiber} (hf : Admissible f)
    (hout : ∀ k ∉ elevenProjection, f k = 0 ∧ horizontalRow f k = 0) :
    f ∈ initial := by
  have hentry (k : Fin 16) : f (code k) ∈ entries := by
    rcases hf.1 k with h | h | h <;> simp [entries, h]
  unfold initial
  refine List.mem_filter.mpr ⟨?_, decide_eq_true hf⟩
  refine List.mem_flatMap.mpr ⟨f 2, hentry 2, ?_⟩
  refine List.mem_flatMap.mpr ⟨f 3, hentry 3, ?_⟩
  refine List.mem_flatMap.mpr ⟨f 4, hentry 4, ?_⟩
  refine List.mem_flatMap.mpr ⟨f 5, hentry 5, ?_⟩
  refine List.mem_flatMap.mpr ⟨f 10, hentry 10, ?_⟩
  refine List.mem_flatMap.mpr ⟨f 13, hentry 13, ?_⟩
  exact List.mem_singleton.mpr (reconstruct_eq f hout)

private def linear : List (BitVec 4 × ℤ) → Fiber → ℤ
  | [], _ => 0
  | (k, c) :: w, f => c * f k + linear w f

private theorem linear_sum (w : List (BitVec 4 × ℤ)) (f : Fin 5 → Fiber) :
    linear w (fun k => ∑ j, f j k) = ∑ j, linear w (f j) := by
  induction w with
  | nil => simp [linear]
  | cons p w ih =>
    obtain ⟨k, c⟩ := p
    simp only [linear, Finset.sum_add_distrib, Finset.mul_sum, ih]

private structure Elimination where
  fiber : Fiber
  form : List (BitVec 4 × ℤ)
  bound : ℤ

private def ofEntries (es : List (BitVec 4 × ℤ)) : Fiber := fun k =>
  ((es.find? fun p => p.1 == k).map Prod.snd).getD 0

private def exclusions : List Elimination :=
  [⟨ofEntries [(3,1), (4,-1), (5,-1), (7,1), (8,1), (12,1), (15,-1)], [(2,1)], 0⟩,
   ⟨ofEntries [(4,1), (5,1), (7,-1), (8,-1), (9,-1), (10,-1), (12,-1)], [(2,1)], 0⟩,
   ⟨ofEntries [(3,1), (5,-1), (12,1), (15,-1)], [(7,1), (12,1)], 1⟩,
   ⟨ofEntries [(4,1), (7,-1), (8,-1), (13,1)], [(5,-1), (7,1)], 1⟩,
   ⟨ofEntries [(4,1), (7,-1), (8,-1), (13,-1)], [(7,1), (12,1)], 1⟩,
   ⟨ofEntries [(5,1), (9,-1), (10,-1), (12,-1)], [(5,1), (8,-1)], 1⟩,
   ⟨ofEntries [(4,1), (7,-1), (8,-1)], [(5,-1), (12,1)], 0⟩]

private def removeSigns (pool : List Fiber) (f : Fiber) : List Fiber :=
  pool.filter fun g =>
    decide (¬ (∀ k : Fin 16, g (code k) = f (code k)) ∧
      ¬ (∀ k : Fin 16, g (code k) = -f (code k)))

private def Checks (pool : List Fiber) (e : Elimination) : Prop :=
  5 * e.bound < linear e.form (residual e.fiber) ∧
  5 * e.bound < -linear e.form (residual (-e.fiber)) ∧
  ∀ g ∈ pool,
    (Compatible e.fiber g → linear e.form g ≤ e.bound) ∧
    (Compatible (-e.fiber) g → -linear e.form g ≤ e.bound)

private instance (pool : List Fiber) (e : Elimination) : Decidable (Checks pool e) := by
  unfold Checks
  infer_instance

private def Certified (pool : List Fiber) : List Elimination → Prop
  | [] => ∀ f ∈ pool, f 4 = 0
  | e :: es => Checks pool e ∧ Certified (removeSigns pool e.fiber) es

private instance certifiedDecidable (pool : List Fiber) (es : List Elimination) :
    Decidable (Certified pool es) := by
  induction es generalizing pool with
  | nil => unfold Certified; infer_instance
  | cons e es ih =>
    unfold Certified
    letI := ih (removeSigns pool e.fiber)
    infer_instance

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Evaluate the seven eliminations over the six-entry ternary table in the kernel.
private theorem certificate : Certified initial exclusions := by
  decide +kernel

private def HasNeighbors (S : Set Fiber) : Prop :=
  ∀ f ∈ S, ∃ g : Fin 5 → Fiber,
    (∀ j, g j ∈ S ∧ Compatible f (g j)) ∧
    ∀ k, (∑ j, g j k) = residual f k

private theorem exceeds_neighbor_bound {S : Set Fiber} (hS : HasNeighbors S)
    {f : Fiber} (hf : f ∈ S) (w : List (BitVec 4 × ℤ)) (s b : ℤ)
    (hout : 5 * b < s * linear w (residual f))
    (hbound : ∀ g ∈ S, Compatible f g → s * linear w g ≤ b) : False := by
  obtain ⟨g, hg, hsum⟩ := hS f hf
  have htotal : (∑ j, s * linear w (g j)) = s * linear w (residual f) := by
    rw [← Finset.mul_sum, ← linear_sum, funext hsum]
  have hle : (∑ j, s * linear w (g j)) ≤ 5 * b := by
    calc
      _ ≤ ∑ _j : Fin 5, b := Finset.sum_le_sum fun j _ => hbound _ (hg j).1 (hg j).2
      _ = 5 * b := by simp
  omega

private theorem certified_zero {S : Set Fiber} (hS : HasNeighbors S)
    {pool : List Fiber} {es : List Elimination} (hc : Certified pool es)
    (hpool : ∀ f ∈ S, f ∈ pool) : ∀ f ∈ S, f 4 = 0 := by
  induction es generalizing pool with
  | nil => exact fun f hf => hc f (hpool f hf)
  | cons e es ih =>
    obtain ⟨⟨hpos, hneg, hbounds⟩, hrest⟩ := hc
    apply ih hrest
    intro f hf
    apply List.mem_filter.mpr
    refine ⟨hpool f hf, decide_eq_true ⟨?_, ?_⟩⟩
    · intro h
      have heq : f = e.fiber := funext fun k => h k.toFin
      subst f
      exact exceeds_neighbor_bound hS hf e.form 1 e.bound (by simpa using hpos)
        (fun g hg h => by simpa using (hbounds g (hpool g hg)).1 h)
    · intro h
      have heq : f = -e.fiber := funext fun k => h k.toFin
      subst f
      exact exceeds_neighbor_bound hS hf e.form (-1) e.bound (by simpa using hneg)
        (fun g hg h => by simpa using (hbounds g (hpool g hg)).2 h)

/-- The exterior equations and a closed family of five compatible signed
neighbors force every member of the family to vanish at code four. -/
theorem fiber_four_eq_zero {S : Set Fiber}
    (hadm : ∀ f ∈ S, Admissible f)
    (hout : ∀ f ∈ S, ∀ k ∉ elevenProjection, f k = 0 ∧ horizontalRow f k = 0)
    (hnext : ∀ f ∈ S, ∃ g : Fin 5 → Fiber,
      (∀ j, g j ∈ S ∧ Compatible f (g j)) ∧
      ∀ k, (∑ j, g j k) = residual f k) :
    ∀ f ∈ S, f 4 = 0 :=
  certified_zero hnext certificate fun f hf => mem_initial (hadm f hf) (hout f hf)

#print axioms certificate
#print axioms fiber_four_eq_zero


private theorem horizontalRow_transport (g : Q 4 → ℤ) (k : BitVec 4) :
    horizontalRow (fun p => g (pattern p)) k = signedRow g (pattern k) := by
  simp only [horizontalRow, signedRow, sum_four, flip_pattern, prefixSign_eq]

private theorem horizontalRow_scale (s : ℤ) (f : Fiber) (k : BitVec 4) :
    horizontalRow (fun p => s * f p) k = s * horizontalRow f k := by
  unfold horizontalRow
  ring

private theorem residual_scale (s : ℤ) (f : Fiber) (k : BitVec 4) :
    residual (fun p => s * f p) k = s * residual f k := by
  unfold residual
  rw [horizontalRow_scale]
  ring

private theorem parity_unit (x : Q 4) : leftParitySign x = 1 ∨ leftParitySign x = -1 :=
  (abs_eq (by decide : (0 : ℤ) ≤ 1)).mp (by simp [leftParitySign, abs_pow])

private theorem prefix_unit {n : ℕ} (x : Q n) (i : Fin n) :
    truePrefixSign x i = 1 ∨ truePrefixSign x i = -1 :=
  (abs_eq (by decide : (0 : ℤ) ≤ 1)).mp (abs_prefixSign x i)

private theorem unit_mul {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with h | h <;> rcases hb with h' | h' <;> norm_num [h, h']

private theorem unit_square {s : ℤ} (hs : s = 1 ∨ s = -1) : s * s = 1 := by
  rcases hs with h | h <;> norm_num [h]

private theorem admissible_scale {s : ℤ} {f : Fiber} (hs : s = 1 ∨ s = -1)
    (hf : Admissible f) : Admissible (fun k => s * f k) := by
  have hs0 : s ≠ 0 := by rcases hs with h | h <;> norm_num [h]
  constructor
  · intro k
    rcases hf.1 k with h | h | h
    · exact Or.inl (show s * f (code k) = 0 by rw [h, mul_zero])
    · exact Or.inr (unit_mul hs (Or.inl h))
    · exact Or.inr (unit_mul hs (Or.inr h))
  · intro k hk
    obtain ⟨hdegree, hsign⟩ := hf.2 k (right_ne_zero_of_mul hk)
    constructor
    · simpa only [occupied, mul_eq_zero, hs0, false_or] using hdegree
    · intro i hi
      calc
        (s * f (code k)) * (s * f (flipCode (code k) i)) =
            (s * s) * (f (code k) * f (flipCode (code k) i)) := by ring
        _ = prefixSign (code k) i := by
          rw [unit_square hs, one_mul, hsign i (right_ne_zero_of_mul hi)]

open Classical in
private theorem ambient_admissible {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hunit : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ C, z u = 0)
    (hsign : ∀ u ∈ C, ∀ i : Fin 9, flip u i ∈ C →
      truePrefixSign u i = z u * z (flip u i)) (y : Q 5) :
    Admissible (fun k => column z k y) := by
  have ha := fiber_admissible hr hunit hzero hsign y
  refine ⟨ha.1, fun k hk => ⟨(ha.2 k hk).1, ?_⟩⟩
  intro i hi
  have hx := (fiber_occupied hunit hzero (code k) y).mpr hk
  have hy := (fiber_occupied hunit hzero (flipCode (code k) i) y).mpr hi
  have he := hsign _ hx (i.castAdd 5) (by rwa [flip_join_left, flip_pattern])
  rw [flip_join_left, flip_pattern, sign_join_left, prefixSign_eq] at he
  exact he.symm

private theorem ambient_compatible {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hb : IsBalanced C) (hunit : ∀ u ∈ C, z u = 1 ∨ z u = -1)
    (hzero : ∀ u ∉ C, z u = 0)
    (hsign : ∀ u ∈ C, ∀ i : Fin 9, flip u i ∈ C →
      truePrefixSign u i = z u * z (flip u i))
    (y : Q 5) (j : Fin 5) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    Compatible (fun k => s * column z k y)
      (fun k => (s * truePrefixSign y j) * column z k (flip y j)) := by
  intro k hk hg
  let x := code k
  have selected := fiber_occupied hunit hzero
  have hx := (selected x y).mpr (right_ne_zero_of_mul hk)
  have htail := (selected x (flip y j)).mpr (right_ne_zero_of_mul hg)
  constructor
  · have hedge := hsign _ hx (j.natAdd 4) (by rwa [flip_join_right])
    rw [sign_join_right, flip_join_right] at hedge
    change leftParitySign (pattern x) * truePrefixSign y j =
      column z x y * column z x (flip y j) at hedge
    calc
      (s * column z x y) * ((s * truePrefixSign y j) * column z x (flip y j)) =
          (s * s) * ((column z x y * column z x (flip y j)) * truePrefixSign y j) := by ring
      _ = leftParitySign (pattern x) := by
        rw [unit_square hs, one_mul, ← hedge, mul_assoc, unit_square (prefix_unit y j), mul_one]
  · intro i hi
    by_contra hboth
    have hhead := (selected (flipCode x i) y).mpr (right_ne_zero_of_mul hi)
    have hcorner := (selected (flipCode x i) (flip y j)).mpr (right_ne_zero_of_mul hboth)
    have hne : (i.castAdd 5 : Fin 9) ≠ j.natAdd 4 := (left_lt_right i j).ne
    exact BalancedCubeGirth.no_selected_square hb hne hx
      (by rwa [flip_join_left, flip_pattern])
      (by rwa [flip_join_right])
      (by rwa [flip_join_left, flip_join_right, flip_pattern])

private theorem ambient_neighbor_sum {z : Q 9 → ℤ}
    (hrow : ∀ u, signedRow z u = 3 * z u) (y : Q 5) (s : ℤ) (k : BitVec 4) :
    (∑ j : Fin 5, (s * truePrefixSign y j) * column z k (flip y j)) =
      residual (fun x => s * column z x y) k := by
  have h := q9_signed_row_split hrow (pattern k) y
  change 3 * column z k y = signedRow (fiber z y) (pattern k) +
    leftParitySign (pattern k) * ∑ j : Fin 5, truePrefixSign y j * column z k (flip y j) at h
  rw [← horizontalRow_transport (fiber z y) k] at h
  have hbase : (∑ j : Fin 5, truePrefixSign y j * column z k (flip y j)) =
      residual (fun x => column z x y) k := by
    change 3 * column z k y = horizontalRow (fun x => column z x y) k +
      leftParitySign (pattern k) * ∑ j : Fin 5, truePrefixSign y j * column z k (flip y j) at h
    change _ = leftParitySign (pattern k) *
      (3 * column z k y - horizontalRow (fun x => column z x y) k)
    rcases parity_unit (pattern k) with hk | hk <;> rw [hk] at h ⊢ <;> omega
  rw [residual_scale, ← hbase, Finset.mul_sum]
  exact sum_congr rfl fun j _ => mul_assoc _ _ _

open Classical in
/-- The projection with omitted codes 0, 1, 6, 11, and 14 is impossible for a
Huang-balanced induced cubic support in Q9. -/
theorem elevenProjection_excluded {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) : C.image leftCode ≠ elevenProjection := by
  intro hshadow
  obtain ⟨z, hunit, hzero, hsign, hrow⟩ := q9_integral_true_prefix_switching hr hb
  let S : Set Fiber := {f | ∃ (y : Q 5) (s : ℤ), (s = 1 ∨ s = -1) ∧
    f = fun k => s * column z k y}
  have hvalid : ∀ f ∈ S, Admissible f := by
    rintro f ⟨y, s, hs, rfl⟩
    exact admissible_scale hs (ambient_admissible hr hunit hzero hsign y)
  have hout : ∀ f ∈ S, ∀ k ∉ elevenProjection, f k = 0 ∧ horizontalRow f k = 0 := by
    rintro f ⟨y, s, _, rfl⟩ k hk
    have hmiss : pattern k ∉ leftProjection C :=
      fun hp => by
        obtain ⟨v, hv⟩ := mem_leftProjection.mp hp
        exact projection_avoid hshadow hk v hv
    obtain ⟨hz, hh⟩ := fiber_and_signedRow_supported hzero hrow y hmiss
    constructor
    · change s * fiber z y (pattern k) = 0
      rw [hz, mul_zero]
    · rw [horizontalRow_scale]
      change s * horizontalRow (fun p => fiber z y (pattern p)) k = 0
      rw [horizontalRow_transport, hh, mul_zero]
  have hneighbors : HasNeighbors S := by
    rintro f ⟨y, s, hs, rfl⟩
    refine ⟨fun j k => (s * truePrefixSign y j) * column z k (flip y j), ?_,
      ambient_neighbor_sum hrow y s⟩
    intro j
    exact ⟨⟨flip y j, s * truePrefixSign y j, unit_mul hs (prefix_unit y j), rfl⟩,
      ambient_compatible hb hunit hzero hsign y j hs⟩
  have zeroFour (y : Q 5) : column z 4 y = 0 := by
    have hmem : (fun k => column z k y) ∈ S :=
      ⟨y, 1, Or.inl rfl, funext fun k => (one_mul _).symm⟩
    exact fiber_four_eq_zero hvalid hout hneighbors _ hmem
  exact not_mem_projection_of_zero_column hunit hzero zeroFour
    (hshadow.symm ▸ (by decide +kernel : (4 : BitVec 4) ∈ elevenProjection))

#print axioms elevenProjection_excluded

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ElevenFiberSeparation
