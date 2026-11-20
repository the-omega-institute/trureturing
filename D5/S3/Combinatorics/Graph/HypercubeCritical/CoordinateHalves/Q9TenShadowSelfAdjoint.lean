/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSelfAdjoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSelfAdjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: An analytic bound for the signed fibers of a normalized ten-pattern shadow. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridProjection

/-! For the normalized ten-pattern shadow in Hong–Wu–Xia, arXiv:2610.09483v1,
§7 Problem 2, the exterior rows leave four free switching labels. A local
inequality in those labels sums to a support bound by signed self-adjointness. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSelfAdjoint

open Finset
open scoped BigOperators
open BalancedCriticalSpectrum (Q IsBalanced flip flip_flip)
open BalancedCubeComponentBoundary (directions regular_directions)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open Q9SignedProjection (join fiber signedRow leftParitySign q9_signed_row_split
  q9_signed_row_eq_zero_outside_projection)
open Q9ThetaProjection (leftCode)
open private pattern rightBlock leftCode_join join_blocks
  flipCode flip_pattern prefixSign prefixSign_eq signed_row_four degree_split occupation from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private flip_join_left sign_join_left from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection

/-- The ten allowed patterns, with the first coordinate as the least significant bit. -/
def tenShadow : Finset (BitVec 4) := {0, 1, 2, 3, 4, 5, 10, 11, 12, 14}

private def reconstructed (a b c d : ℤ) (k : BitVec 4) : ℤ :=
  match k.toNat with
  | 0 => -b - c
  | 1 => d
  | 2 => a + d
  | 3 => -c
  | 4 => a
  | 5 => -c
  | 10 => b
  | 11 => -d
  | 12 => c
  | 14 => d
  | _ => 0

private def horizontalRow (a b c d : ℤ) (k : BitVec 4) : ℤ :=
  match k.toNat with
  | 0 => 2 * a + 2 * d
  | 1 => -b + c
  | 2 => -2 * b - 2 * c
  | 3 => a - d
  | 4 => -b - 3 * c
  | 5 => a - d
  | 10 => -a - 3 * d
  | 11 => b - c
  | 12 => -a + d
  | 14 => -b + c
  | _ => 0

private theorem exterior_reconstruction {f : Q 4 → ℤ}
    (hf : ∀ k ∉ tenShadow, f (pattern k) = 0)
    (hr : ∀ k ∉ tenShadow, signedRow f (pattern k) = 0) (k : BitVec 4) :
    f (pattern k) = reconstructed (f (pattern 4)) (f (pattern 10))
      (f (pattern 12)) (f (pattern 14)) k := by
  have outside : (6 : BitVec 4) ∉ tenShadow ∧ (7 : BitVec 4) ∉ tenShadow ∧
      (8 : BitVec 4) ∉ tenShadow ∧ (9 : BitVec 4) ∉ tenShadow ∧
      (13 : BitVec 4) ∉ tenShadow ∧ (15 : BitVec 4) ∉ tenShadow := by decide +kernel
  obtain ⟨n6, n7, n8, n9, n13, n15⟩ := outside
  have e6 := signed_row_four f 6 7 4 2 14 1 1 (-1) 1 (by decide +kernel) (by decide +kernel)
  have e7 := signed_row_four f 7 6 5 3 15 1 (-1) 1 (-1) (by decide +kernel) (by decide +kernel)
  have e8 := signed_row_four f 8 9 10 12 0 1 1 1 1 (by decide +kernel) (by decide +kernel)
  have e9 := signed_row_four f 9 8 11 13 1 1 (-1) (-1) (-1) (by decide +kernel) (by decide +kernel)
  have e13 := signed_row_four f 13 12 15 9 5 1 (-1) (-1) 1 (by decide +kernel) (by decide +kernel)
  have e15 := signed_row_four f 15 14 13 11 7 1 (-1) 1 (-1) (by decide +kernel) (by decide +kernel)
  simp only [hr 6 n6, hr 7 n7, hr 8 n8, hr 9 n9, hr 13 n13, hr 15 n15,
    hf 6 n6, hf 7 n7, hf 8 n8, hf 9 n9, hf 13 n13, hf 15 n15,
    one_mul, neg_one_mul, neg_zero, zero_add, add_zero] at e6 e7 e8 e9 e13 e15
  obtain ⟨k⟩ := k
  fin_cases k <;> try (first | rfl | exact hf _ (by decide +kernel))
  case «0» =>
    change f (pattern 0) = -f (pattern 10) - f (pattern 12)
    omega
  case «1» =>
    change f (pattern 1) = f (pattern 14)
    omega
  case «2» =>
    change f (pattern 2) = f (pattern 4) + f (pattern 14)
    omega
  case «3» =>
    change f (pattern 3) = -f (pattern 12)
    omega
  case «5» =>
    change f (pattern 5) = -f (pattern 12)
    omega
  case «11» =>
    change f (pattern 11) = -f (pattern 14)
    omega

private theorem reconstructed_signedRow (a b c d : ℤ) (k : BitVec 4) :
    signedRow (fun x => reconstructed a b c d ((cubeBitVec 4).symm x)) (pattern k) =
      horizontalRow a b c d k := by
  let g : Q 4 → ℤ := fun x => reconstructed a b c d ((cubeBitVec 4).symm x)
  have hg (l : BitVec 4) : g (pattern l) = reconstructed a b c d l :=
    congrArg (reconstructed a b c d) ((cubeBitVec 4).symm_apply_apply l)
  change signedRow g (pattern k) = _
  obtain ⟨k⟩ := k
  fin_cases k
  · change signedRow g (pattern 0) = horizontalRow a b c d 0
    rw [signed_row_four g 0 1 2 4 8 1 1 1 1 (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul]
    change d + ((a + d) + (a + 0)) = 2 * a + 2 * d
    ring
  · change signedRow g (pattern 1) = horizontalRow a b c d 1
    rw [signed_row_four g 1 0 3 5 9 1 (-1) (-1) (-1) (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul, neg_one_mul]
    change (-b - c) + (-(-c) + (-(-c) + -0)) = -b + c
    ring
  · change signedRow g (pattern 2) = horizontalRow a b c d 2
    rw [signed_row_four g 2 3 0 6 10 1 1 (-1) (-1) (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul, neg_one_mul]
    change (-c) + ((-b - c) + (-0 + -b)) = -2 * b - 2 * c
    ring
  · change signedRow g (pattern 3) = horizontalRow a b c d 3
    rw [signed_row_four g 3 2 1 7 11 1 (-1) 1 1 (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul, neg_one_mul]
    change (a + d) + (-d + (0 + (-d))) = a - d
    ring
  · change signedRow g (pattern 4) = horizontalRow a b c d 4
    rw [signed_row_four g 4 5 6 0 12 1 1 1 (-1) (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul, neg_one_mul]
    change (-c) + (0 + ((-b - c) + -c)) = -b - 3 * c
    ring
  · change signedRow g (pattern 5) = horizontalRow a b c d 5
    rw [signed_row_four g 5 4 7 1 13 1 (-1) (-1) 1 (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul, neg_one_mul]
    change a + (-0 + (-d + 0)) = a - d
    ring
  · change signedRow g (pattern 6) = horizontalRow a b c d 6
    rw [signed_row_four g 6 7 4 2 14 1 1 (-1) 1 (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul, neg_one_mul]
    change 0 + (a + (-(a + d) + d)) = 0
    ring
  · change signedRow g (pattern 7) = horizontalRow a b c d 7
    rw [signed_row_four g 7 6 5 3 15 1 (-1) 1 (-1) (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul, neg_one_mul]
    change 0 + (-(-c) + ((-c) + -0)) = 0
    ring
  · change signedRow g (pattern 8) = horizontalRow a b c d 8
    rw [signed_row_four g 8 9 10 12 0 1 1 1 1 (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul]
    change 0 + (b + (c + (-b - c))) = 0
    ring
  · change signedRow g (pattern 9) = horizontalRow a b c d 9
    rw [signed_row_four g 9 8 11 13 1 1 (-1) (-1) (-1) (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul, neg_one_mul]
    change 0 + (-(-d) + (-0 + -d)) = 0
    ring
  · change signedRow g (pattern 10) = horizontalRow a b c d 10
    rw [signed_row_four g 10 11 8 14 2 1 1 (-1) (-1) (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul, neg_one_mul]
    change (-d) + (0 + (-d + -(a + d))) = -a - 3 * d
    ring
  · change signedRow g (pattern 11) = horizontalRow a b c d 11
    rw [signed_row_four g 11 10 9 15 3 1 (-1) 1 1 (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul, neg_one_mul]
    change b + (-0 + (0 + (-c))) = b - c
    ring
  · change signedRow g (pattern 12) = horizontalRow a b c d 12
    rw [signed_row_four g 12 13 14 8 4 1 1 1 (-1) (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul, neg_one_mul]
    change 0 + (d + (0 + -a)) = -a + d
    ring
  · change signedRow g (pattern 13) = horizontalRow a b c d 13
    rw [signed_row_four g 13 12 15 9 5 1 (-1) (-1) 1 (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul, neg_one_mul]
    change c + (-0 + (-0 + (-c))) = 0
    ring
  · change signedRow g (pattern 14) = horizontalRow a b c d 14
    rw [signed_row_four g 14 15 12 10 6 1 1 (-1) 1 (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul, neg_one_mul]
    change 0 + (c + (-b + 0)) = -b + c
    ring
  · change signedRow g (pattern 15) = horizontalRow a b c d 15
    rw [signed_row_four g 15 14 13 11 7 1 (-1) 1 (-1) (by decide +kernel) (by decide +kernel)]
    simp only [hg, one_mul, neg_one_mul]
    change d + (-0 + ((-d) + -0)) = 0
    ring

private def column (z : Q 9 → ℤ) (k : BitVec 4) (y : Q 5) : ℤ := fiber z y (pattern k)

private theorem reconstruct_fiber {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hshadow : ∀ u ∈ C, leftCode u ∈ tenShadow)
    (hzero : ∀ u ∉ C, z u = 0) (hrow : ∀ u, signedRow z u = 3 * z u)
    (y : Q 5) (k : BitVec 4) :
    column z k y = reconstructed (column z 4 y) (column z 10 y)
      (column z 12 y) (column z 14 y) k := by
  have zero (l : BitVec 4) (hl : l ∉ tenShadow) (v : Q 5) : column z l v = 0 := by
    apply hzero
    intro hu
    exact hl (by simpa only [leftCode_join] using hshadow _ hu)
  exact exterior_reconstruction (fun l hl => zero l hl y) (fun l hl =>
    q9_signed_row_eq_zero_outside_projection hrow (zero l hl) y) k

private theorem suffix_rows {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hshadow : ∀ u ∈ C, leftCode u ∈ tenShadow)
    (hzero : ∀ u ∉ C, z u = 0) (hrow : ∀ u, signedRow z u = 3 * z u) (y : Q 5) :
    let f := fun k => column z k y
    signedRow (column z 0) y = 3 * f 0 - 2 * f 2 ∧
    signedRow (column z 2) y = -3 * f 2 + 2 * f 0 ∧
    signedRow (column z 1) y = -3 * f 14 - f 10 + f 12 ∧
    signedRow (column z 3) y = -3 * f 12 - f 4 + f 14 := by
  have hf := reconstruct_fiber hshadow hzero hrow y
  have hfun : fiber z y = fun x =>
      reconstructed (column z 4 y) (column z 10 y) (column z 12 y) (column z 14 y)
        ((cubeBitVec 4).symm x) := by
    funext x
    obtain ⟨k, rfl⟩ := (cubeBitVec 4).surjective x
    simpa only [column, Equiv.symm_apply_apply] using hf k
  have split (k : BitVec 4) : 3 * column z k y =
      horizontalRow (column z 4 y) (column z 10 y) (column z 12 y) (column z 14 y) k +
        leftParitySign (pattern k) * signedRow (column z k) y := by
    have h := q9_signed_row_split hrow (pattern k) y
    change 3 * column z k y = signedRow (fiber z y) (pattern k) +
      leftParitySign (pattern k) * signedRow (column z k) y at h
    rw [hfun, reconstructed_signedRow] at h
    exact h
  have signs : leftParitySign (pattern 0) = 1 ∧ leftParitySign (pattern 1) = -1 ∧
      leftParitySign (pattern 2) = -1 ∧ leftParitySign (pattern 3) = 1 := by decide +kernel
  obtain ⟨p0, p1, p2, p3⟩ := signs
  have e0 := split 0
  have e1 := split 1
  have e2 := split 2
  have e3 := split 3
  have f0 := hf 0
  have f1 := hf 1
  have f2 := hf 2
  have f3 := hf 3
  simp only [p0, p1, p2, p3, one_mul, neg_one_mul] at e0 e1 e2 e3
  change 3 * column z 0 y = 2 * column z 4 y + 2 * column z 14 y + _ at e0
  change 3 * column z 1 y = -column z 10 y + column z 12 y + _ at e1
  change 3 * column z 2 y = -2 * column z 10 y - 2 * column z 12 y + _ at e2
  change 3 * column z 3 y = column z 4 y - column z 14 y + _ at e3
  change column z 0 y = -column z 10 y - column z 12 y at f0
  change column z 1 y = column z 14 y at f1
  change column z 2 y = column z 4 y + column z 14 y at f2
  change column z 3 y = -column z 12 y at f3
  dsimp only
  exact ⟨by omega, by omega, by omega, by omega⟩

private def occupied (v : ℤ) : ℤ := if v = 0 then 0 else 1

private def whole (_ : BitVec 4) : Bool := true
private def zeroTwo (k : BitVec 4) : Bool := k == 0 || k == 2
private def firstTrue (k : BitVec 4) : Bool := pattern k 0

private abbrev code (k : Fin 16) : BitVec 4 := BitVec.ofFin k

private def weight (p : BitVec 4 → Bool) (f : BitVec 4 → ℤ) : ℤ :=
  ∑ k : Fin 16, if p (code k) then occupied (f (code k)) else 0

private def unitOrZero (v : ℤ) : Prop := v = 0 ∨ v = 1 ∨ v = -1
  deriving Decidable

private def admissible (f : BitVec 4 → ℤ) : Prop :=
  (∀ k : Fin 16, unitOrZero (f (code k))) ∧
  ∀ k : Fin 16, let x := code k
    f x ≠ 0 →
      (∑ i : Fin 4, occupied (f (flipCode x i))) ≤ 3 ∧
      ∀ i : Fin 4, f (flipCode x i) ≠ 0 →
        0 < prefixSign x i * f x * f (flipCode x i)

private instance (f : BitVec 4 → ℤ) : Decidable (admissible f) :=
  by unfold admissible; infer_instance

private def skew (a b c d : ℤ) : ℤ :=
  (-3 * d - b + c) * (-c) - d * (-3 * c - a + d)

private def ternary (i : Fin 3) : ℤ := (i.val : ℤ) - 1

private theorem local_inequality_finite :
    ∀ a b c d : Fin 3,
      let f := reconstructed (ternary a) (ternary b) (ternary c) (ternary d)
      admissible f →
        4 * weight zeroTwo f + 3 * weight firstTrue f ≤
          2 * weight whole f - 2 * skew (ternary a) (ternary b) (ternary c) (ternary d) := by
  decide +kernel

private theorem exists_ternary {v : ℤ} (hv : unitOrZero v) : ∃ i : Fin 3, ternary i = v := by
  rcases hv with rfl | rfl | rfl
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨0, rfl⟩

private theorem fiber_occupied {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hunit : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ C, z u = 0)
    (k : BitVec 4) (y : Q 5) :
    join (pattern k) y ∈ C ↔ column z k y ≠ 0 := by
  constructor
  · intro hy
    change z (join (pattern k) y) ≠ 0
    rcases hunit _ hy with hs | hs <;> simp [hs]
  · intro hn
    by_contra hy
    exact hn (hzero _ hy)

open Classical in
private theorem fiber_admissible {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hunit : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ C, z u = 0)
    (hsign : ∀ u ∈ C, ∀ i : Fin 9, flip u i ∈ C →
      truePrefixSign u i = z u * z (flip u i)) (y : Q 5) :
    admissible (fun k => column z k y) := by
  have selected := fun k => fiber_occupied hunit hzero k y
  have count (k : BitVec 4) : occupied (column z k y) = (occupation C k y : ℤ) := by
    by_cases hk : join (pattern k) y ∈ C
    · simp [occupied, occupation, hk, (selected k).mp hk]
    · have hz : column z k y = 0 := hzero _ hk
      simp [occupied, occupation, hk, hz]
  constructor
  · intro k
    change unitOrZero (z (join (pattern (code k)) y))
    by_cases hk : join (pattern (code k)) y ∈ C
    · exact Or.inr (hunit _ hk)
    · exact Or.inl (hzero _ hk)
  · intro k
    let x := code k
    change column z x y ≠ 0 → _
    intro hx
    have hxC := (selected x).mpr hx
    constructor
    · have hd := (degree_split C x y).symm.trans (regular_directions C hr hxC)
      have hb : (∑ i : Fin 4, occupation C (flipCode x i) y) ≤ 3 := by omega
      simp_rw [count]
      exact_mod_cast hb
    · intro i hi
      have hiC := (selected (flipCode x i)).mpr hi
      have he := hsign _ hxC (i.castAdd 5) (by rwa [flip_join_left, flip_pattern])
      rw [flip_join_left, flip_pattern, sign_join_left, prefixSign_eq] at he
      change prefixSign x i = column z x y * column z (flipCode x i) y at he
      change 0 < prefixSign x i * column z x y * column z (flipCode x i) y
      rw [he]
      rcases hunit _ hxC with h | h <;> rcases hunit _ hiC with h' | h' <;>
        change column z x y = _ at h <;>
        change column z (flipCode x i) y = _ at h' <;> norm_num [h, h']

private theorem fiber_inequality {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hshadow : ∀ u ∈ C, leftCode u ∈ tenShadow)
    (hzero : ∀ u ∉ C, z u = 0) (hrow : ∀ u, signedRow z u = 3 * z u)
    (y : Q 5) (hpass : admissible (fun k => column z k y)) :
    let f := fun k => column z k y
    4 * weight zeroTwo f + 3 * weight firstTrue f ≤ 2 * weight whole f -
      2 * (signedRow (column z 1) y * f 3 - f 1 * signedRow (column z 3) y) := by
  let f := fun k => column z k y
  have hf := reconstruct_fiber hshadow hzero hrow y
  have form : f = reconstructed (f 4) (f 10) (f 12) (f 14) := funext hf
  obtain ⟨a, ha⟩ := exists_ternary (hpass.1 4)
  obtain ⟨b, hb⟩ := exists_ternary (hpass.1 10)
  obtain ⟨c, hc⟩ := exists_ternary (hpass.1 12)
  obtain ⟨d, hd⟩ := exists_ternary (hpass.1 14)
  change ternary a = f 4 at ha
  change ternary b = f 10 at hb
  change ternary c = f 12 at hc
  change ternary d = f 14 at hd
  obtain ⟨_, _, row1, row3⟩ := suffix_rows hshadow hzero hrow y
  have f1 : f 1 = f 14 := hf 1
  have f3 : f 3 = -f 12 := hf 3
  have hs : signedRow (column z 1) y * f 3 - f 1 * signedRow (column z 3) y =
      skew (f 4) (f 10) (f 12) (f 14) := by
    rw [row1, row3, f1, f3]
    rfl
  change 4 * weight zeroTwo f + 3 * weight firstTrue f ≤ 2 * weight whole f -
    2 * (signedRow (column z 1) y * f 3 - f 1 * signedRow (column z 3) y)
  rw [hs]
  have bound := local_inequality_finite a b c d
  dsimp only at bound
  rw [ha, hb, hc, hd, ← form] at bound
  exact bound hpass

private theorem prefixSign_flip {n : ℕ} (y : Q n) (i : Fin n) :
    truePrefixSign (flip y i) i = truePrefixSign y i := by
  unfold truePrefixSign
  congr 2
  ext j
  simp only [mem_filter, mem_univ, true_and]
  constructor <;> rintro ⟨hj, hs⟩ <;>
    exact ⟨hj, by simpa only [BalancedCriticalSpectrum.flip, Function.update_of_ne hj.ne] using hs⟩

private theorem signedRow_pairing_symmetric {n : ℕ} (f g : Q n → ℤ) :
    (∑ y, signedRow f y * g y) = ∑ y, f y * signedRow g y := by
  calc
    (∑ y, signedRow f y * g y) =
        ∑ i : Fin n, ∑ y, truePrefixSign y i * f (flip y i) * g y := by
      simp only [signedRow, Finset.sum_mul]
      rw [sum_comm]
    _ = ∑ i : Fin n, ∑ y, f y * (truePrefixSign y i * g (flip y i)) := by
      refine sum_congr rfl (fun i _ => ?_)
      let e : Q n ≃ Q n := ⟨fun y => flip y i, fun y => flip y i,
        fun y => flip_flip y i, fun y => flip_flip y i⟩
      refine Fintype.sum_equiv e _ _ (fun y => ?_)
      change truePrefixSign y i * f (flip y i) * g y =
        f (flip y i) * (truePrefixSign (flip y i) i * g (flip (flip y i) i))
      rw [prefixSign_flip, BalancedCriticalSpectrum.flip_flip]
      ring
    _ = ∑ y, f y * signedRow g y := by
      rw [sum_comm]
      simp only [signedRow, Finset.mul_sum]

private def suffixPrefixEquiv : (Q 5 × Fin 16) ≃ Q 9 where
  toFun pair := join (pattern (BitVec.ofFin pair.2)) pair.1
  invFun u := (rightBlock u, (leftCode u).toFin)
  left_inv := by
    rintro ⟨y, k⟩
    apply Prod.ext
    · funext i
      simp only [rightBlock, join, Fin.append_right]
    · change (leftCode (join (pattern (code k)) y)).toFin = k
      rw [leftCode_join]
  right_inv := join_blocks

open Classical in
private theorem sum_weight {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hunit : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ C, z u = 0)
    (p : BitVec 4 → Bool) :
    (∑ y : Q 5, weight p (fun k => column z k y)) =
      ((C.filter fun u => p (leftCode u) = true).card : ℤ) := by
  calc
    (∑ y : Q 5, weight p (fun k => column z k y)) =
        ∑ u : Q 9, if u ∈ C ∧ p (leftCode u) = true then (1 : ℤ) else 0 := by
      unfold weight
      rw [← Fintype.sum_prod_type']
      refine Fintype.sum_equiv suffixPrefixEquiv _ _ ?_
      rintro ⟨y, k⟩
      change (if p (code k) then occupied (column z (code k) y) else 0) =
        if join (pattern (code k)) y ∈ C ∧ p (leftCode (join (pattern (code k)) y)) =
          true then 1 else 0
      rw [leftCode_join, occupied]
      by_cases hk : join (pattern (code k)) y ∈ C
      · simp [hk, (fiber_occupied hunit hzero _ _).mp hk]
      · have hz : column z (code k) y = 0 := hzero _ hk
        simp [hk, hz]
    _ = _ := by
      rw [sum_boole]
      congr 2
      ext u
      simp

private theorem firstTrue_leftCode (u : Q 9) : firstTrue (leftCode u) = u 0 := by
  exact congrFun ((cubeBitVec 4).apply_symm_apply (fun i : Fin 4 => u (i.castAdd 5))) 0

open Classical in
private theorem card_zeroTwo (C : Finset (Q 9)) :
    (C.filter fun u => zeroTwo (leftCode u) = true).card =
      (C.filter fun u => leftCode u = 0).card + (C.filter fun u => leftCode u = 2).card := by
  have hfilter : (C.filter fun u => zeroTwo (leftCode u) = true) =
      (C.filter fun u => leftCode u = 0) ∪ (C.filter fun u => leftCode u = 2) := by
    ext u
    simp [zeroTwo, and_or_left]
  rw [hfilter, card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro u hu hv
  have impossible : (0 : BitVec 4) = 2 := (mem_filter.mp hu).2.symm.trans (mem_filter.mp hv).2
  exact (by decide : (0 : BitVec 4) ≠ 2) impossible

open Classical in
/-- The two parity fibers and the TRUE half of the first coordinate satisfy a
joint bound in every balanced induced cubic support contained in the ten-pattern shadow. -/
theorem tenShadow_global_inequality {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hshadow : ∀ u ∈ C, leftCode u ∈ tenShadow) :
    4 * ((C.filter fun u => leftCode u = 0).card +
      (C.filter fun u => leftCode u = 2).card) +
      3 * (C.filter fun u => u 0 = true).card ≤ 2 * C.card := by
  obtain ⟨z, hunit, hzero, hsign, hrow⟩ := q9_integral_true_prefix_switching hr hb
  change ∀ u, signedRow z u = 3 * z u at hrow
  have hlocal := fun y => fiber_inequality hshadow hzero hrow y
    (fiber_admissible hr hunit hzero hsign y)
  have total := sum_le_sum (s := (univ : Finset (Q 5))) (fun y _ => hlocal y)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    signedRow_pairing_symmetric (column z 1) (column z 3), sub_self, mul_zero, sub_zero,
    sum_weight hunit hzero, card_zeroTwo, firstTrue_leftCode, whole, filter_true]
    at total
  exact_mod_cast total

#check tenShadow_global_inequality
#print axioms tenShadow_global_inequality


open private carrier mem_carrier card_carrier mem_encoded flip_cubeBitVec
  encoded_neighborParity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridProjection

open Classical in
private theorem eight_le_slice {C : Finset (Q 9)} {z : Q 9 → ℤ} {k : BitVec 4}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hunit : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ C, z u = 0)
    (hnonempty : (carrier C k).Nonempty) (b : Q 5 → ℤ)
    (hrow : ∀ y, signedRow (column z k) y = 3 * column z k y - 2 * b y) :
    8 ≤ (C.filter fun u => leftCode u = k).card := by
  let A := carrier C k
  let E := A.image (cubeBitVec 5).symm
  have unit (y : Q 5) (hy : y ∈ A) : column z k y = 1 ∨ column z k y = -1 :=
    hunit _ ((mem_carrier C k y).mp hy)
  have zero (y : Q 5) (hy : y ∉ A) : column z k y = 0 :=
    hzero _ (fun h => hy ((mem_carrier C k y).mpr h))
  have hpar := encoded_neighborParity (b := b) (c := fun _ => 0) unit zero (by simpa using hrow)
  have hdeg (x : BitVec 5) (hx : x ∈ E) :
      ((univ : Finset (Fin 5)).filter fun i => (x ^^^ BitVec.twoPow 5 i.val) ∈ E).card ≤ 3 := by
    let y := cubeBitVec 5 x
    have hy := (mem_carrier C k y).mp ((mem_encoded A x).mp hx)
    have hsplit := (degree_split C k y).symm.trans (regular_directions C hr hy)
    have hright : (∑ i : Fin 5, occupation C k (flip y i)) ≤ 3 := by omega
    change ((univ : Finset (Fin 5)).filter
      (fun i => (x ^^^ BitVec.twoPow 5 i.val) ∈ A.image (cubeBitVec 5).symm)).card ≤ 3
    rw [Finset.card_filter]
    simpa only [mem_encoded, ← flip_cubeBitVec, A, mem_carrier, occupation, y] using hright
  have bound := Q5SmallParitySupport.eight_le_card_of_neighborParity
    (S := E) (hnonempty.image _) hpar hdeg
  rwa [show E.card = A.card from card_image_of_injective _ (cubeBitVec 5).symm.injective,
    card_carrier] at bound

open Classical in
/-- A balanced induced cubic support of order 72 with at least 30 vertices
on the TRUE half of the first coordinate cannot have this exact projection. -/
theorem tenShadow_excluded {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hsize : C.card = 72)
    (htrue : 30 ≤ (C.filter fun u => u 0 = true).card) :
    C.image leftCode ≠ tenShadow := by
  intro heq
  have hshadow (u : Q 9) (hu : u ∈ C) : leftCode u ∈ tenShadow :=
    heq ▸ mem_image_of_mem leftCode hu
  have reachable (k : BitVec 4) (hk : k ∈ tenShadow) : (carrier C k).Nonempty := by
    obtain ⟨u, hu, hku⟩ := mem_image.mp (heq.symm ▸ hk)
    refine ⟨rightBlock u, (mem_carrier C k _).mpr ?_⟩
    rwa [← hku, join_blocks]
  obtain ⟨z, hunit, hzero, _, hrow⟩ := q9_integral_true_prefix_switching hr hb
  change ∀ u, signedRow z u = 3 * z u at hrow
  have w0 := eight_le_slice hr hunit hzero (reachable 0 (by decide +kernel)) (column z 2)
    (fun y => (suffix_rows hshadow hzero hrow y).1)
  have w2 := eight_le_slice hr hunit hzero (reachable 2 (by decide +kernel))
    (fun y => 3 * column z 2 y - column z 0 y) (by
      intro y
      have he := (suffix_rows hshadow hzero hrow y).2.1
      dsimp only at he
      omega)
  have bound := tenShadow_global_inequality hr hb hshadow
  omega

#check tenShadow_excluded
#print axioms tenShadow_excluded


end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSelfAdjoint
