/- GID: D5/S3/FiniteGroups/HeadleyRankTwoPath
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyRankTwoPath
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The unbounded native circular-length path for the Headley rank-two base. -/

module

public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.List.Intervals
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Tactic

/-! The native reconstruction of the rank-two base in the R-sequenceability
construction of Headley (1994). The R-to-L and L-to-R transitions are combined
into one recursive block. The three terminal branches retain exactly the native
L(0), R(1), and early L(2) completions. No ordering search is used. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

public section

namespace D5.S3.FiniteGroups.HeadleyRankTwoPath

/-- The shorter distance between the indicated residues on a circle of size n. -/
@[expose] def circularLength (n x y : ℕ) : ℕ :=
  min (Nat.dist x y) (n - Nat.dist x y)

/-- The lengths of a path with a specified starting vertex. -/
@[expose] def steps (n : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | x, y :: ys => circularLength n x y :: steps n y ys

/-- The unused vertices in the native right state R(a). -/
private def rightUnused (n a x : ℕ) : Prop :=
  (1 ≤ x ∧ x < a) ∨ x = a + 1 ∨ (n - a ≤ x ∧ x < n)

/-- The complete right-state tail. The default branch is unreachable on its
proved domain (a positive and different from two). For a at least six, the
six displayed entries are exactly R(a) -> L(a - 3) -> R(a - 3). -/
private def rightTail (n a : ℕ) : List ℕ :=
  if a = 1 then [n - 1, 2]
  else if a = 3 then [n - 3, 4, n - 1, 1, n - 2, 2]
  else if a = 4 then [n - 4, 5, n - 2, 3, n - 3, 1, n - 1, 2]
  else if a = 5 then [n - 5, 6, n - 3, 3, n - 4, 4, n - 1, 1, n - 2, 2]
  else if 6 ≤ a then
    [n - a, a + 1, n - a + 2, a - 1, n - a + 1, a - 3] ++ rightTail n (a - 3)
  else []
termination_by a

private theorem right_one (n : ℕ) (hn : 6 < n) :
    steps n 1 (rightTail n 1) = [2, 3] := by
  simp [rightTail, steps, circularLength, Nat.dist]; omega

private theorem right_three (n : ℕ) (hn : 14 < n) :
    steps n 3 (rightTail n 3) = [6, 7, 5, 2, 3, 4] := by
  simp [rightTail, steps, circularLength, Nat.dist]; omega

private theorem right_four (n : ℕ) (hn : 18 < n) :
    steps n 4 (rightTail n 4) = [8, 9, 7, 5, 6, 4, 2, 3] := by
  simp [rightTail, steps, circularLength, Nat.dist]; omega

private theorem right_five (n : ℕ) (hn : 22 < n) :
    steps n 5 (rightTail n 5) = [10, 11, 9, 6, 7, 8, 5, 2, 3, 4] := by
  simp [rightTail, steps, circularLength, Nat.dist]; omega

private theorem right_block (n a : ℕ) (ha : 6 ≤ a) (hn : 4 * a + 2 < n) :
    steps n a (rightTail n a) =
      [2 * a, 2 * a + 1, 2 * a - 1, 2 * a - 3, 2 * a - 2, 2 * a - 4] ++
        steps n (a - 3) (rightTail n (a - 3)) := by
  have he : rightTail n a =
      [n - a, a + 1, n - a + 2, a - 1, n - a + 1, a - 3] ++ rightTail n (a - 3) := by
    rw [rightTail]
    simp only [show a ≠ 1 by omega, show a ≠ 3 by omega,
      show a ≠ 4 by omega, show a ≠ 5 by omega, ha, ↓reduceIte]
  rw [he]
  simp [steps, circularLength, Nat.dist]; omega

/-- Both finite inventories of every reachable right state. The strict bound
ensures all declared lengths are shorter than the diameter. This is proved by
parameter descent, not by assuming a certificate for the returned list. -/
private theorem right_inventory (n a : ℕ) (ha : 1 ≤ a) (ha2 : a ≠ 2)
    (hn : 4 * a + 2 < n) :
    (rightTail n a).Nodup ∧
      (∀ x, x ∈ rightTail n a ↔ rightUnused n a x) ∧
      (steps n a (rightTail n a)).Nodup ∧
      (∀ d, d ∈ steps n a (rightTail n a) ↔ 2 ≤ d ∧ d ≤ 2 * a + 1) := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases h1 : a = 1
    · subst a
      rw [right_one n hn]
      refine ⟨?_, ?_, by decide, ?_⟩
      · simp [rightTail] <;> omega
      · intro x
        simp [rightTail, rightUnused]; omega
      · intro d
        simp; omega
    by_cases h3 : a = 3
    · subst a
      rw [right_three n hn]
      refine ⟨?_, ?_, by decide, ?_⟩
      · simp [rightTail] <;> omega
      · intro x
        simp [rightTail, rightUnused]; omega
      · intro d
        simp; omega
    by_cases h4 : a = 4
    · subst a
      rw [right_four n hn]
      refine ⟨?_, ?_, by decide, ?_⟩
      · simp [rightTail] <;> omega
      · intro x
        simp [rightTail, rightUnused]; omega
      · intro d
        simp; omega
    by_cases h5 : a = 5
    · subst a
      rw [right_five n hn]
      refine ⟨?_, ?_, by decide, ?_⟩
      · simp [rightTail] <;> omega
      · intro x
        simp [rightTail, rightUnused]; omega
      · intro d
        simp; omega
    have h6 : 6 ≤ a := by omega
    obtain ⟨hV, hM, hD, hL⟩ := ih (a - 3) (by omega) (by omega) (by omega) (by omega)
    have he : rightTail n a =
        [n - a, a + 1, n - a + 2, a - 1, n - a + 1, a - 3] ++ rightTail n (a - 3) := by
      rw [rightTail]
      simp only [h1, h3, h4, h5, h6, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [he]
      simp only [List.cons_append, List.nil_append, List.nodup_cons,
        List.mem_cons, hV, hM, rightUnused, and_true]
      omega
    · intro x
      rw [he]
      simp only [List.cons_append, List.nil_append, List.mem_cons, hM, rightUnused]
      omega
    · rw [right_block n a h6 hn]
      simp only [List.cons_append, List.nil_append, List.nodup_cons,
        List.mem_cons, hD, hL, and_true]
      omega
    · intro d
      rw [right_block n a h6 hn]
      simp only [List.cons_append, List.nil_append, List.mem_cons, hL]
      omega


private theorem steps_append (n x : ℕ) (p q : List ℕ) :
    steps n x (p ++ q) = steps n x p ++ steps n (p.getLastD x) q := by
  induction p generalizing x with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.cons_append, steps, ih, List.cons_append, List.getLastD_cons]

private def zig (m i : ℕ) : ℕ :=
  if i % 2 = 0 then m + i/2 else m - (i + 1)/2

private def zigWalk (m : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => zigWalk m k ++ [zig m k]

private theorem zig_walk_eq (m k : ℕ) :
    zigWalk m k = (List.range k).map (zig m) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [zigWalk, ih, List.range_succ, List.map_append, List.map_singleton]

private theorem zig_bounds (s i : ℕ) (hi : i < 2 * s) :
    s ≤ zig (2 * s) i ∧ zig (2 * s) i < 3 * s := by
  dsimp [zig]
  split_ifs <;> omega

private theorem zig_injective (s i j : ℕ) (hi : i < 2 * s) (hj : j < 2 * s)
    (h : zig (2 * s) i = zig (2 * s) j) : i = j := by
  dsimp [zig] at h
  split_ifs at h <;> omega

private theorem zig_inventory (s : ℕ) :
    (zigWalk (2 * s) (2 * s)).Nodup ∧
      (∀ x, x ∈ zigWalk (2 * s) (2 * s) ↔ s ≤ x ∧ x < 3 * s) := by
  rw [zig_walk_eq]
  constructor
  · apply List.Nodup.map_on
    · intro i hi j hj h
      exact zig_injective s i j (List.mem_range.mp hi) (List.mem_range.mp hj) h
    · exact List.nodup_range
  · intro x
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact zig_bounds s i hi
    · intro hx
      by_cases h : 2 * s ≤ x
      · refine ⟨2 * (x - 2 * s), by omega, ?_⟩
        simp only [zig]
        split_ifs <;> omega
      · refine ⟨2 * (2 * s - x) - 1, by omega, ?_⟩
        simp only [zig]
        split_ifs <;> omega

private theorem zig_step (s i : ℕ) (hi : i + 1 < 2 * s) :
    circularLength (4 * s) (zig (2 * s) i) (zig (2 * s) (i + 1)) = i + 1 := by
  simp only [zig, circularLength, Nat.dist]
  split_ifs <;> omega

private theorem zig_lengths (s k : ℕ) (hs : 1 ≤ s) (hk : k + 1 ≤ 2 * s) :
    steps (4 * s) 0 (zigWalk (2 * s) (k + 1)) = 2 * s :: List.range' 1 k := by
  induction k with
  | zero =>
    simp only [zigWalk, List.nil_append, steps, zig, Nat.zero_mod, Nat.zero_div,
      ↓reduceIte, Nat.add_zero, List.range'_zero]
    congr 1
    simp only [circularLength, Nat.dist]
    omega
  | succ k ih =>
    rw [zigWalk, steps_append, ih (by omega)]
    have he : (zigWalk (2 * s) (k + 1)).getLastD 0 = zig (2 * s) k := by
      rw [zigWalk, List.getLastD_concat]
    rw [he]
    simp only [steps, zig_step s k (by omega), List.cons_append]
    rw [List.range'_1_concat]
    simp only [Nat.add_comm]

/-- A Hamilton path beginning at zero and the diameter, with one diameter edge
and exactly two occurrences of every other positive circular length. -/
structure LengthPath (m : ℕ) where
  tail : List ℕ
  start : tail.head? = some m
  vertex_inventory : (0 :: tail).Perm (List.range (2 * m))
  length_inventory : (steps (2 * m) 0 tail).Perm
    (m :: (List.range' 1 (m - 1) ++ List.range' 1 (m - 1)))


private def continuation (s : ℕ) : List ℕ :=
  [3 * s + 1, 3 * s, s - 2] ++ rightTail (4 * s) (s - 2)

private theorem continuation_vertices (s : ℕ) (hs : 8 ≤ s) :
    (continuation s).Nodup ∧
      (∀ x, x ∈ continuation s ↔ (1 ≤ x ∧ x < s) ∨ (3 * s ≤ x ∧ x < 4 * s)) := by
  obtain ⟨hV,hM,hD,hL⟩ := right_inventory (4 * s) (s - 2) (by omega) (by omega) (by omega)
  constructor
  · simp only [continuation, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, hV, hM, rightUnused, and_true]
    omega
  · intro x
    simp only [continuation, List.cons_append, List.nil_append, List.mem_cons, hM, rightUnused]
    omega

private theorem continuation_lengths (s : ℕ) (hs : 8 ≤ s) :
    (steps (4 * s) s (continuation s)).Perm (List.range' 1 (2 * s - 1)) := by
  obtain ⟨hV,hM,hD,hL⟩ := right_inventory (4 * s) (s - 2) (by omega) (by omega) (by omega)
  have he : steps (4 * s) s (continuation s) =
      [2 * s - 1,1,2 * s - 2] ++ steps (4 * s) (s - 2) (rightTail (4 * s) (s - 2)) := by
    simp [continuation, steps, circularLength, Nat.dist]; omega
  have hd : (steps (4 * s) s (continuation s)).Nodup := by
    rw [he]
    simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
      hD,hL,and_true]
    omega
  apply (List.perm_ext_iff_of_nodup hd (List.nodup_range')).mpr
  intro d
  rw [he]
  simp only [List.cons_append, List.nil_append, List.mem_cons, hL, List.mem_range'_1]
  omega

/-- The large-parameter branch, retaining the explicit native initial three
edges and the right-state completion. This branch works for every s at least 8. -/
private def largePath (s : ℕ) : List ℕ :=
  zigWalk (2 * s) (2 * s) ++ continuation s

private theorem large_start (s : ℕ) (hs : 8 ≤ s) :
    (largePath s).head? = some (2 * s) := by
  rw [largePath, zig_walk_eq]
  have he : 2 * s = (2 * s - 1) + 1 := by omega
  rw [he, List.range_succ_eq_map]
  simp [zig]

private theorem large_vertices (s : ℕ) (hs : 8 ≤ s) :
    (0 :: largePath s).Perm (List.range (4 * s)) := by
  obtain ⟨hZ,hZM⟩ := zig_inventory s
  obtain ⟨hC,hCM⟩ := continuation_vertices s hs
  have h0 : 0 ∉ largePath s := by
    simp only [largePath, List.mem_append, hZM, hCM]
    omega
  have hP : (largePath s).Nodup := by
    rw [largePath, List.nodup_append]
    refine ⟨hZ,hC,?_⟩
    intro x hx y hy he
    have hz := (hZM x).mp hx
    have hc := (hCM y).mp hy
    omega
  apply (List.perm_ext_iff_of_nodup (List.nodup_cons.mpr ⟨h0,hP⟩)
    List.nodup_range).mpr
  intro x
  simp only [List.mem_cons, largePath, List.mem_append, hZM,hCM,List.mem_range]
  omega

private theorem large_lengths (s : ℕ) (hs : 8 ≤ s) :
    (steps (4 * s) 0 (largePath s)).Perm
      (2 * s :: (List.range' 1 (2 * s - 1) ++ List.range' 1 (2 * s - 1))) := by
  have hk : 2 * s = (2 * s - 1) + 1 := by omega
  have hz : steps (4 * s) 0 (zigWalk (2 * s) (2 * s)) = 2 * s :: List.range' 1 (2 * s - 1) := by
    simpa only [← hk] using zig_lengths s (2 * s - 1) (by omega) (by omega)
  have ht : (zigWalk (2 * s) (2 * s)).getLastD 0 = s := by
    conv_lhs => arg 1; rw [hk,zigWalk]
    rw [List.getLastD_concat]
    simp only [zig]
    split_ifs <;> omega
  rw [largePath,steps_append,hz,ht]
  exact List.Perm.cons _ (List.Perm.append_left _ (continuation_lengths s hs))

/-- A proved path at every even half-order at least sixteen. -/
private def largeLengthPath (s : ℕ) (hs : 8 ≤ s) : LengthPath (2 * s) where
  tail := largePath s
  start := large_start s hs
  vertex_inventory := by simpa only [show 2 * (2 * s)=4 * s by omega] using large_vertices s hs
  length_inventory := by simpa only [show 2 * (2 * s)=4 * s by omega] using large_lengths s hs

/-- The single unbounded path construction for every cyclic factor of order
2 ^ a, a at least three. The m=4 and m=8 words are consumed leaves of this function;
all larger exponents use the strictly descending symbolic right-state algorithm. -/
def powerTwoPath (a : ℕ) (ha : 3 ≤ a) : LengthPath (2 ^ (a - 1)) := by
  by_cases h3 : a = 3
  · subst a
    exact {
      tail := [4,1,3,2,5,7,6]
      start := rfl
      vertex_inventory := by decide
      length_inventory := by decide }
  by_cases h4 : a = 4
  · subst a
    exact {
      tail := [8,1,7,2,6,3,5,4,11,15,9,14,13,10,12]
      start := rfl
      vertex_inventory := by decide
      length_inventory := by decide }
  let s := 2 ^ (a - 2)
  have hs : 8 ≤ s := by
    dsimp [s]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 3 ≤ a - 2)
  have hm : 2 ^ (a - 1) = 2 * s := by
    have he : a - 1 = (a - 2) + 1 := by omega
    dsimp [s]
    rw [he, pow_succ, Nat.mul_comm]
  rw [hm]
  exact largeLengthPath s hs

end D5.S3.FiniteGroups.HeadleyRankTwoPath
