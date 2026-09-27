/- GID: D5/S3/Arith/Congruence/ArbitraryHoleGram
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ArbitraryHoleGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual hole degrees control the weighted four-block square sum. -/

import Mathlib
import D5.S3.PrimeGaps.GreedyResidues

/-!
For arbitrary finite row and column carriers, deleting an arbitrary relation
of cells still permits a common four-block quadratic bound after weighting
each surviving cell by one plus epsilon times its two incident hole counts.
The proof derives all incidence budgets, the nonexceptional anchored-star gap,
and the exceptional Laplacian from the relation itself. The existing frozen
symmetric row-sum inequality is used directly inside the perturbation step.

This is a symbolic inequality for every finite carrier and real four-vector,
not finite enumeration, a certificate checker, or a numerical reduction.
It formalizes the unnormalized grid estimate used in the odd-covering head
construction. Normalization, the graph-counting denominator bound, integration
over arithmetic head laws, and the unrestricted-tail conclusion are separate
obligations; they are not assertions of this declaration.
-/

open scoped BigOperators

namespace D5.S3.Arith.Congruence.ArbitraryHoleGram

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Literal row incidence count of the hole relation. -/
def rowDegree (E : I → J → Prop) [DecidableRel E] (i : I) : ℕ :=
  (Finset.univ.filter (E i)).card

/-- Literal column incidence count of the hole relation. -/
def colDegree (E : I → J → Prop) [DecidableRel E] (j : J) : ℕ :=
  (Finset.univ.filter (fun i => E i j)).card

/-- Number of actual holes, counted once by their row. -/
def holeCount (E : I → J → Prop) [DecidableRel E] : ℕ :=
  ∑ i, rowDegree E i

/-- The unweighted actual row/column/cell Gram diagonal difference.
The constant-coordinate survivor cardinal cancels from the difference. -/
private noncomputable def holeBaselineGap
    (E : I → J → Prop) [DecidableRel E]
    (i : I) (j : J) (z : {p : I × J // ¬ E p.1 p.2}) (x : Fin 4 → ℝ) : ℝ := by
  classical
  let m : ℝ := Fintype.card I
  let n : ℝ := Fintype.card J
  let r : ℝ := (Finset.univ.filter (fun j => ¬ E i j)).card
  let c : ℝ := (Finset.univ.filter (fun i => ¬ E i j)).card
  let u : ℝ := if E i j then 0 else 1
  let v : ℝ := if z.val.1 = i then 1 else 0
  let t : ℝ := if z.val.2 = j then 1 else 0
  exact (m+n+1)*x 0^2+(2*(n+1)-r)*x 1^2+(2*(m+1)-c)*x 2^2+3*x 3^2
    -2*(r*x 0*x 1+c*x 0*x 2+x 0*x 3+u*x 1*x 2+v*x 1*x 3+t*x 2*x 3)

set_option maxHeartbeats 4000000 in
-- The single endpoint inlines both incidence counts, the anchored-star case
-- split, all four perturbation rows, and the actual weighted-sum expansion.
/-- Arbitrary finite hole relations admit the degree-weighted common Gram diagonal. -/
theorem degree_reweighted_grid_second_moment_le [DecidableEq I] [DecidableEq J]
    (E : I → J → Prop) [DecidableRel E]
    (hm : 3 ≤ Fintype.card I) (hn : 3 ≤ Fintype.card J)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : 9 * ε * (holeCount E : ℝ) *
      max (max ((Fintype.card I : ℝ) + Fintype.card J + 1)
        (2 * ((Fintype.card I : ℝ) - 1)))
        (max (2 * ((Fintype.card J : ℝ) - 1)) 4) ≤ 1)
    (i : I) (j : J) (z : {p : I × J // ¬ E p.1 p.2}) (x : Fin 4 → ℝ) :
    let T := Finset.univ.filter (fun p : I × J => ¬ E p.1 p.2)
    let w := fun p : I × J => 1 + ε * ((rowDegree E p.1 : ℝ) + colDegree E p.2)
    let Z := ∑ p ∈ T, w p
    (∑ p ∈ T, w p *
      (x 0 + (if p.1=i then x 1 else 0) +
        (if p.2=j then x 2 else 0) + (if p=z.val then x 3 else 0))^2) ≤
      (Z+(Fintype.card I:ℝ)+Fintype.card J+1+2*ε*holeCount E)*x 0^2+
      2*((Fintype.card J:ℝ)+1+ε*holeCount E)*x 1^2+
      2*((Fintype.card I:ℝ)+1+ε*holeCount E)*x 2^2+4*x 3^2 := by
  classical

  have degree_reweighted_row_controls
      (E : I → J → Prop) [DecidableRel E]
      (ε : ℝ) (hε : 0 ≤ ε)
      (hεn : ε * ((Fintype.card J : ℝ) - 2) ≤ 1)
      (hn : 2 ≤ Fintype.card J) (i : I) :
      ((∑ j ∈ Finset.univ.filter (fun j => ¬ E i j),
        (1 + ε * ((rowDegree E i : ℝ) + colDegree E j))) ≤
        (Fintype.card J : ℝ) + ε * holeCount E) ∧
      ((∑ j ∈ Finset.univ.filter (fun j => ¬ E i j),
        ((rowDegree E i : ℝ) + colDegree E j)) ≤
        (holeCount E : ℝ) * ((Fintype.card J : ℝ) - 1)) ∧
      (∀ j, ¬ E i j → rowDegree E i + colDegree E j ≤ holeCount E) := by
    classical
    let H : Finset J := Finset.univ.filter (E i)
    let S : Finset J := Finset.univ.filter (fun j => ¬ E i j)
    let d : ℕ := rowDegree E i
    have hd : H.card = d := rfl
    have hcard : (S.card : ℝ) + d = Fintype.card J := by
      have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := E i)
      have hc' : S.card + d = Fintype.card J := by
        simpa only [S, d, rowDegree, Nat.add_comm, Finset.card_univ] using hc
      exact_mod_cast hc'
    have hcols : (∑ j : J, (colDegree E j : ℝ)) = holeCount E := by
      simp only [holeCount, colDegree, rowDegree, Nat.cast_sum, Finset.card_eq_sum_ones,
        Finset.sum_filter]
      exact Finset.sum_comm
    have hloss : (d : ℝ) ≤ ∑ j ∈ H, (colDegree E j : ℝ) := by
      calc
        (d : ℝ) = ∑ _j ∈ H, (1 : ℝ) := by simp [hd]
        _ ≤ ∑ j ∈ H, (colDegree E j : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          have hij : E i j := (Finset.mem_filter.mp hj).2
          have hp : 0 < colDegree E j := by
            apply Finset.card_pos.mpr
            exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
          exact_mod_cast hp
    have hsplit : (∑ j ∈ H, (colDegree E j : ℝ)) +
        (∑ j ∈ S, (colDegree E j : ℝ)) = holeCount E := by
      calc
        _ = ∑ j : J, (colDegree E j : ℝ) := by
          simpa only [H, S] using
            (Finset.sum_filter_add_sum_filter_not Finset.univ (E i)
              (fun j => (colDegree E j : ℝ)))
        _ = _ := hcols
    have hremain : (∑ j ∈ S, (colDegree E j : ℝ)) ≤ (holeCount E : ℝ) - d := by
      linarith
    have hidentity : (∑ j ∈ S, (1 + ε * ((d : ℝ) + colDegree E j))) =
        (S.card : ℝ) + ε * ((S.card : ℝ) * d + ∑ j ∈ S, (colDegree E j : ℝ)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, ← Finset.mul_sum]
      ring
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have hdd : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
      by_cases hz : d = 0
      · simp [hz]
      · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
        exact mul_nonneg hd0 (sub_nonneg.mpr hd1)
    have hcoeff : ε * (d : ℝ) * ((Fintype.card J : ℝ) - d - 1) ≤ d := by
      have hh := mul_le_mul_of_nonneg_right hεn hd0
      have he := mul_nonneg hε hdd
      nlinarith
    have hrow : (∑ j ∈ S, (1 + ε * ((d : ℝ) + colDegree E j))) ≤
        (Fintype.card J : ℝ) + ε * holeCount E := by
      calc
        _ = (S.card : ℝ) + ε * ((S.card : ℝ) * d + ∑ j ∈ S, (colDegree E j : ℝ)) := hidentity
        _ ≤ (S.card : ℝ) + ε * ((S.card : ℝ) * d + ((holeCount E : ℝ) - d)) :=
    by
          gcongr
        _ ≤ (Fintype.card J : ℝ) + ε * holeCount E := by
          have hcS : (S.card : ℝ) = (Fintype.card J : ℝ) - d := by linarith
          rw [hcS]
          nlinarith

    have hpoint (j : J) (hij : ¬ E i j) :
        rowDegree E i + colDegree E j ≤ holeCount E := by
      have hlocal (r : I) :
          (if E r j then 1 else 0) + (if r = i then rowDegree E i else 0) ≤
            rowDegree E r := by
        by_cases hr : r = i
        · subst r
          simp [hij]
        · simp only [if_neg hr, add_zero]
          split_ifs with hrj
          · have hp : 0 < rowDegree E r := by
              apply Finset.card_pos.mpr
              exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrj⟩⟩
            exact hp
          · exact Nat.zero_le _
      have hs := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hlocal r)
      simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, ← Finset.sum_filter, ← Finset.card_eq_sum_ones,
        colDegree, holeCount, Nat.add_comm] using hs
    have hderiv : (∑ j ∈ S, ((d : ℝ) + colDegree E j)) ≤
        (holeCount E : ℝ) * ((Fintype.card J : ℝ) - 1) := by
      have hk0 : (0 : ℝ) ≤ holeCount E := Nat.cast_nonneg _
      have hnR : (2 : ℝ) ≤ Fintype.card J := by exact_mod_cast hn
      by_cases hz : d = 0
      · have hs : (∑ j ∈ S, ((d : ℝ) + colDegree E j)) ≤ (holeCount E : ℝ) := by
          simpa [hz] using hremain
        exact hs.trans (by nlinarith)
      · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
        have hsize : (S.card : ℝ) ≤ (Fintype.card J : ℝ) - 1 := by linarith
        calc
          _ ≤ ∑ _j ∈ S, (holeCount E : ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            have hp := hpoint j (Finset.mem_filter.mp hj).2
            exact_mod_cast hp
          _ = (S.card : ℝ) * holeCount E := by simp
          _ ≤ ((Fintype.card J : ℝ) - 1) * holeCount E :=
            mul_le_mul_of_nonneg_right hsize hk0
          _ = (holeCount E : ℝ) * ((Fintype.card J : ℝ) - 1) := by ring
    exact ⟨hrow, hderiv, hpoint⟩

  have degree_reweighted_col_controls
      (E : J → I → Prop) [DecidableRel E]
      (ε : ℝ) (hε : 0 ≤ ε)
      (hεn : ε * ((Fintype.card I : ℝ) - 2) ≤ 1)
      (hn : 2 ≤ Fintype.card I) (i : J) :
      ((∑ j ∈ Finset.univ.filter (fun j => ¬ E i j),
        (1 + ε * ((rowDegree E i : ℝ) + colDegree E j))) ≤
        (Fintype.card I : ℝ) + ε * holeCount E) ∧
      ((∑ j ∈ Finset.univ.filter (fun j => ¬ E i j),
        ((rowDegree E i : ℝ) + colDegree E j)) ≤
        (holeCount E : ℝ) * ((Fintype.card I : ℝ) - 1)) ∧
      (∀ j, ¬ E i j → rowDegree E i + colDegree E j ≤ holeCount E) := by
    classical
    let H : Finset I := Finset.univ.filter (E i)
    let S : Finset I := Finset.univ.filter (fun j => ¬ E i j)
    let d : ℕ := rowDegree E i
    have hd : H.card = d := rfl
    have hcard : (S.card : ℝ) + d = Fintype.card I := by
      have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := E i)
      have hc' : S.card + d = Fintype.card I := by
        simpa only [S, d, rowDegree, Nat.add_comm, Finset.card_univ] using hc
      exact_mod_cast hc'
    have hcols : (∑ j : I, (colDegree E j : ℝ)) = holeCount E := by
      simp only [holeCount, colDegree, rowDegree, Nat.cast_sum, Finset.card_eq_sum_ones,
        Finset.sum_filter]
      exact Finset.sum_comm
    have hloss : (d : ℝ) ≤ ∑ j ∈ H, (colDegree E j : ℝ) := by
      calc
        (d : ℝ) = ∑ _j ∈ H, (1 : ℝ) := by simp [hd]
        _ ≤ ∑ j ∈ H, (colDegree E j : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          have hij : E i j := (Finset.mem_filter.mp hj).2
          have hp : 0 < colDegree E j := by
            apply Finset.card_pos.mpr
            exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
          exact_mod_cast hp
    have hsplit : (∑ j ∈ H, (colDegree E j : ℝ)) +
        (∑ j ∈ S, (colDegree E j : ℝ)) = holeCount E := by
      calc
        _ = ∑ j : I, (colDegree E j : ℝ) := by
          simpa only [H, S] using
            (Finset.sum_filter_add_sum_filter_not Finset.univ (E i)
              (fun j => (colDegree E j : ℝ)))
        _ = _ := hcols
    have hremain : (∑ j ∈ S, (colDegree E j : ℝ)) ≤ (holeCount E : ℝ) - d := by
      linarith
    have hidentity : (∑ j ∈ S, (1 + ε * ((d : ℝ) + colDegree E j))) =
        (S.card : ℝ) + ε * ((S.card : ℝ) * d + ∑ j ∈ S, (colDegree E j : ℝ)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, ← Finset.mul_sum]
      ring
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have hdd : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
      by_cases hz : d = 0
      · simp [hz]
      · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
        exact mul_nonneg hd0 (sub_nonneg.mpr hd1)
    have hcoeff : ε * (d : ℝ) * ((Fintype.card I : ℝ) - d - 1) ≤ d := by
      have hh := mul_le_mul_of_nonneg_right hεn hd0
      have he := mul_nonneg hε hdd
      nlinarith
    have hrow : (∑ j ∈ S, (1 + ε * ((d : ℝ) + colDegree E j))) ≤
        (Fintype.card I : ℝ) + ε * holeCount E := by
      calc
        _ = (S.card : ℝ) + ε * ((S.card : ℝ) * d + ∑ j ∈ S, (colDegree E j : ℝ)) := hidentity
        _ ≤ (S.card : ℝ) + ε * ((S.card : ℝ) * d + ((holeCount E : ℝ) - d)) :=
    by
          gcongr
        _ ≤ (Fintype.card I : ℝ) + ε * holeCount E := by
          have hcS : (S.card : ℝ) = (Fintype.card I : ℝ) - d := by linarith
          rw [hcS]
          nlinarith

    have hpoint (j : I) (hij : ¬ E i j) :
        rowDegree E i + colDegree E j ≤ holeCount E := by
      have hlocal (r : J) :
          (if E r j then 1 else 0) + (if r = i then rowDegree E i else 0) ≤
            rowDegree E r := by
        by_cases hr : r = i
        · subst r
          simp [hij]
        · simp only [if_neg hr, add_zero]
          split_ifs with hrj
          · have hp : 0 < rowDegree E r := by
              apply Finset.card_pos.mpr
              exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrj⟩⟩
            exact hp
          · exact Nat.zero_le _
      have hs := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hlocal r)
      simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, ← Finset.sum_filter, ← Finset.card_eq_sum_ones,
        colDegree, holeCount, Nat.add_comm] using hs
    have hderiv : (∑ j ∈ S, ((d : ℝ) + colDegree E j)) ≤
        (holeCount E : ℝ) * ((Fintype.card I : ℝ) - 1) := by
      have hk0 : (0 : ℝ) ≤ holeCount E := Nat.cast_nonneg _
      have hnR : (2 : ℝ) ≤ Fintype.card I := by exact_mod_cast hn
      by_cases hz : d = 0
      · have hs : (∑ j ∈ S, ((d : ℝ) + colDegree E j)) ≤ (holeCount E : ℝ) := by
          simpa [hz] using hremain
        exact hs.trans (by nlinarith)
      · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
        have hsize : (S.card : ℝ) ≤ (Fintype.card I : ℝ) - 1 := by linarith
        calc
          _ ≤ ∑ _j ∈ S, (holeCount E : ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            have hp := hpoint j (Finset.mem_filter.mp hj).2
            exact_mod_cast hp
          _ = (S.card : ℝ) * holeCount E := by simp
          _ ≤ ((Fintype.card I : ℝ) - 1) * holeCount E :=
            mul_le_mul_of_nonneg_right hsize hk0
          _ = (holeCount E : ℝ) * ((Fintype.card I : ℝ) - 1) := by ring
    exact ⟨hrow, hderiv, hpoint⟩

  have actual_hole_baseline_gap
      (E : I → J → Prop) [DecidableRel E]
      (hm : 3 ≤ Fintype.card I) (hn : 3 ≤ Fintype.card J)
      (i : I) (j : J) (z : {p : I × J // ¬ E p.1 p.2})
      (hne : rowDegree E i + colDegree E j ≠ 0 ∨ z.val ≠ (i,j))
      (x : Fin 4 → ℝ) :
      x 0^2+x 1^2+x 2^2+x 3^2 ≤ 9 * holeBaselineGap E i j z x := by
    classical
    let r : ℕ := (Finset.univ.filter (fun j => ¬ E i j)).card
    let c : ℕ := (Finset.univ.filter (fun i => ¬ E i j)).card
    let dr : ℕ := rowDegree E i
    let dc : ℕ := colDegree E j
    let u : ℝ := if E i j then 0 else 1
    let v : ℝ := if z.val.1 = i then 1 else 0
    let t : ℝ := if z.val.2 = j then 1 else 0
    let a := x 0
    let b := x 1
    let q := x 2
    let d := x 3
    let star := (a-b)^2+(a-q)^2+(a-d)^2
    let sx : ℝ := dr+dc
    let sy : ℝ := 2+2*dr-u-v
    let sz : ℝ := 2+2*dc-u-t
    let sw : ℝ := 2-v-t
    let energy := (r:ℝ)*(a-b)^2+(c:ℝ)*(a-q)^2+(a-d)^2+
      u*(b-q)^2+v*(b-d)^2+t*(q-d)^2+sx*a^2+sy*b^2+sz*q^2+sw*d^2
    have hrow : r + dr = Fintype.card J := by
      simpa only [r, dr, rowDegree, Nat.add_comm, Finset.card_univ] using
        Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := E i)
    have hcol : c + dc = Fintype.card I := by
      simpa only [c, dc, colDegree, Nat.add_comm, Finset.card_univ] using
        Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun i => E i j)
    have hrowR : (r:ℝ)+dr=Fintype.card J := by exact_mod_cast hrow
    have hcolR : (c:ℝ)+dc=Fintype.card I := by exact_mod_cast hcol
    have hu0 : 0 ≤ u := by simp only [u]; split_ifs <;> norm_num
    have hu1 : u ≤ 1 := by simp only [u]; split_ifs <;> norm_num
    have hv0 : 0 ≤ v := by simp only [v]; split_ifs <;> norm_num
    have hv1 : v ≤ 1 := by simp only [v]; split_ifs <;> norm_num
    have ht0 : 0 ≤ t := by simp only [t]; split_ifs <;> norm_num
    have ht1 : t ≤ 1 := by simp only [t]; split_ifs <;> norm_num
    have hdr : (0:ℝ) ≤ dr := Nat.cast_nonneg _
    have hdc : (0:ℝ) ≤ dc := Nat.cast_nonneg _
    have hsx : 0 ≤ sx := by dsimp [sx]; positivity
    have hsy : 0 ≤ sy := by dsimp [sy]; linarith
    have hsz : 0 ≤ sz := by dsimp [sz]; linarith
    have hsw : 0 ≤ sw := by dsimp [sw]; linarith
    have henergy : holeBaselineGap E i j z x = energy := by
      have hform : holeBaselineGap E i j z x =
          ((Fintype.card I:ℝ)+(Fintype.card J:ℝ)+1)*a^2+
          (2*((Fintype.card J:ℝ)+1)-r)*b^2+
          (2*((Fintype.card I:ℝ)+1)-c)*q^2+3*d^2-
          2*((r:ℝ)*a*b+(c:ℝ)*a*q+a*d+u*b*q+v*b*d+t*q*d) := by
        simp only [holeBaselineGap,a,b,q,d,r,c,u,v,t]
        congr!
      rw [hform, ← hrowR, ← hcolR]
      dsimp [energy, sx, sy, sz, sw]
      ring
    have hthree (w y z : ℝ) : (w+y+z)^2 ≤ 3*(w^2+y^2+z^2) := by
      simpa [Fin.sum_univ_succ, add_assoc] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := ![w,y,z]))
    have hanchor0 : a^2+b^2+q^2+d^2 ≤ 9*(star+a^2) := by
      have hb : b^2 ≤ 2*(a^2+(a-b)^2) := by nlinarith only [sq_nonneg (2*a-b)]
      have hq : q^2 ≤ 2*(a^2+(a-q)^2) := by nlinarith only [sq_nonneg (2*a-q)]
      have hd : d^2 ≤ 2*(a^2+(a-d)^2) := by nlinarith only [sq_nonneg (2*a-d)]
      dsimp [star]
      nlinarith only [hb, hq, hd, sq_nonneg a, sq_nonneg (a-b), sq_nonneg (a-q), sq_nonneg (a-d)]
    have hanchor1 : a^2+b^2+q^2+d^2 ≤ 9*(star+b^2) := by
      have ha : a^2 ≤ 2*(b^2+(a-b)^2) := by nlinarith only [sq_nonneg (a-2*b)]
      have hq := hthree b (a-b) (q-a)
      have hd := hthree b (a-b) (d-a)
      dsimp [star]
      nlinarith only [ha, hq, hd, sq_nonneg b, sq_nonneg (a-b), sq_nonneg (a-q), sq_nonneg (a-d)]
    have hanchor2 : a^2+b^2+q^2+d^2 ≤ 9*(star+q^2) := by
      have ha : a^2 ≤ 2*(q^2+(a-q)^2) := by nlinarith only [sq_nonneg (a-2*q)]
      have hb := hthree q (a-q) (b-a)
      have hd := hthree q (a-q) (d-a)
      dsimp [star]
      nlinarith only [ha, hb, hd, sq_nonneg q, sq_nonneg (a-b), sq_nonneg (a-q), sq_nonneg (a-d)]
    have hdropU : 0 ≤ u*(b-q)^2 := mul_nonneg hu0 (sq_nonneg _)
    have hdropV : 0 ≤ v*(b-d)^2 := mul_nonneg hv0 (sq_nonneg _)
    have hdropT : 0 ≤ t*(q-d)^2 := mul_nonneg ht0 (sq_nonneg _)
    have hdropW : 0 ≤ sw*d^2 := mul_nonneg hsw (sq_nonneg _)
    rw [henergy]
    change a^2+b^2+q^2+d^2 ≤ 9*energy
    by_cases hholes : 0 < dr+dc
    · let ar : ℕ := if r=0 then 2 else 0
      let ac : ℕ := if c=0 then 2 else 0
      have hbudgetN : 1+ar+ac ≤ dr+dc := by
        by_cases hr : r=0 <;> by_cases hc : c=0 <;> simp only [ar, ac, hr, hc, if_true, if_false] <;> omega
      have hbudget : 1+(ar:ℝ)+ac ≤ sx := by dsimp [sx]; exact_mod_cast hbudgetN
      have harN : ar ≤ 2*dr := by
        by_cases hr : r=0 <;> simp only [ar, hr, if_true, if_false] <;> omega
      have hacN : ac ≤ 2*dc := by
        by_cases hc : c=0 <;> simp only [ac, hc, if_true, if_false] <;> omega
      have har : (ar:ℝ) ≤ sy := by
        have hh : (ar:ℝ) ≤ 2*dr := by exact_mod_cast harN
        dsimp [sy]
        linarith
      have hac : (ac:ℝ) ≤ sz := by
        have hh : (ac:ℝ) ≤ 2*dc := by exact_mod_cast hacN
        dsimp [sz]
        linarith
      have hrowStar : (a-b)^2 ≤ (r:ℝ)*(a-b)^2+(ar:ℝ)*(a^2+b^2) := by
        by_cases hr : r=0
        · simp only [hr, ar, if_pos, Nat.cast_zero, Nat.cast_ofNat, zero_mul, zero_add]
          nlinarith only [sq_nonneg (a+b)]
        · have hrR : (1:ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
          simp only [ar, if_neg hr, Nat.cast_zero, zero_mul, add_zero]
          nlinarith only [mul_nonneg (sub_nonneg.mpr hrR) (sq_nonneg (a-b))]
      have hcolStar : (a-q)^2 ≤ (c:ℝ)*(a-q)^2+(ac:ℝ)*(a^2+q^2) := by
        by_cases hc : c=0
        · simp only [hc, ac, if_pos, Nat.cast_zero, Nat.cast_ofNat, zero_mul, zero_add]
          nlinarith only [sq_nonneg (a+q)]
        · have hcR : (1:ℝ) ≤ c := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
          simp only [ac, if_neg hc, Nat.cast_zero, zero_mul, add_zero]
          nlinarith only [mul_nonneg (sub_nonneg.mpr hcR) (sq_nonneg (a-q))]
      have hbase : star+a^2 ≤ energy := by
        have hbx := mul_le_mul_of_nonneg_right hbudget (sq_nonneg a)
        have hby := mul_le_mul_of_nonneg_right har (sq_nonneg b)
        have hbq := mul_le_mul_of_nonneg_right hac (sq_nonneg q)
        dsimp [star, energy]
        nlinarith only [hrowStar, hcolStar, hbx, hby, hbq, hdropU, hdropV, hdropT, hdropW]
      nlinarith only [hanchor0, hbase]
    · have hdr0 : dr=0 := by omega
      have hdc0 : dc=0 := by omega
      have hrR : (1:ℝ) ≤ r := by
        have : 1 ≤ r := by omega
        exact_mod_cast this
      have hcR : (1:ℝ) ≤ c := by
        have : 1 ≤ c := by omega
        exact_mod_cast this
      have hrowStar : (a-b)^2 ≤ (r:ℝ)*(a-b)^2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hrR) (sq_nonneg (a-b))]
      have hcolStar : (a-q)^2 ≤ (c:ℝ)*(a-q)^2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hcR) (sq_nonneg (a-q))]
      have hzx : z.val ≠ (i,j) := by
        rcases hne with h | h
        · change dr+dc≠0 at h
          omega
        · exact h
      by_cases hzi : z.val.1=i
      · have hzj : z.val.2≠j := by
          intro h
          exact hzx (Prod.ext hzi h)
        have ht : t=0 := by simp [t, hzj]
        have hanchor : 1 ≤ sz := by dsimp [sz]; rw [ht]; linarith
        have hbase : star+q^2 ≤ energy := by
          have hax := mul_nonneg hsx (sq_nonneg a)
          have hay := mul_nonneg hsy (sq_nonneg b)
          have haq := mul_le_mul_of_nonneg_right hanchor (sq_nonneg q)
          dsimp [star, energy]
          nlinarith only [hrowStar, hcolStar, hax, hay, haq, hdropU, hdropV, hdropT, hdropW]
        nlinarith only [hanchor2, hbase]
      · have hv : v=0 := by simp [v, hzi]
        have hanchor : 1 ≤ sy := by dsimp [sy]; rw [hv]; linarith
        have hbase : star+b^2 ≤ energy := by
          have hax := mul_nonneg hsx (sq_nonneg a)
          have haq := mul_nonneg hsz (sq_nonneg q)
          have hay := mul_le_mul_of_nonneg_right hanchor (sq_nonneg b)
          dsimp [star, energy]
          nlinarith only [hrowStar, hcolStar, hax, hay, haq, hdropU, hdropV, hdropT, hdropW]
        nlinarith only [hanchor1, hbase]

  have actual_degree_perturbation_gap
      (E : I → J → Prop) [DecidableRel E]
      (hm : 3 ≤ Fintype.card I) (hn : 3 ≤ Fintype.card J)
      (ε : ℝ) (hε : 0 ≤ ε)
      (hsmall : 9 * ε * (holeCount E : ℝ) *
        max (max ((Fintype.card I : ℝ) + Fintype.card J + 1)
          (2 * ((Fintype.card I : ℝ) - 1)))
          (max (2 * ((Fintype.card J : ℝ) - 1)) 4) ≤ 1)
      (i : I) (j : J) (z : {p : I × J // ¬ E p.1 p.2}) (x : Fin 4 → ℝ) :
      let rp : ℝ := ∑ b ∈ Finset.univ.filter (fun b => ¬ E i b),
        ((rowDegree E i : ℝ) + colDegree E b)
      let cp : ℝ := ∑ a ∈ Finset.univ.filter (fun a => ¬ E a j),
        ((rowDegree E a : ℝ) + colDegree E j)
      let h : ℝ := (rowDegree E z.val.1 : ℝ) + colDegree E z.val.2
      let up : ℝ := if E i j then 0 else (rowDegree E i : ℝ) + colDegree E j
      let v : ℝ := if z.val.1 = i then 1 else 0
      let t : ℝ := if z.val.2 = j then 1 else 0
      0 ≤ holeBaselineGap E i j z x + ε *
        (2*(holeCount E:ℝ)*x 0^2+(2*(holeCount E:ℝ)-rp)*x 1^2+
          (2*(holeCount E:ℝ)-cp)*x 2^2-h*x 3^2-
          2*(rp*x 0*x 1+cp*x 0*x 2+h*x 0*x 3+up*x 1*x 2+
            h*v*x 1*x 3+h*t*x 2*x 3)) := by
    classical
    dsimp only
    let rp : ℝ := ∑ b ∈ Finset.univ.filter (fun b => ¬ E i b),
        ((rowDegree E i : ℝ) + colDegree E b)
    let cp : ℝ := ∑ a ∈ Finset.univ.filter (fun a => ¬ E a j),
        ((rowDegree E a : ℝ) + colDegree E j)
    let h : ℝ := (rowDegree E z.val.1 : ℝ) + colDegree E z.val.2
    let up : ℝ := if E i j then 0 else (rowDegree E i : ℝ) + colDegree E j
    let v : ℝ := if z.val.1 = i then 1 else 0
    let t : ℝ := if z.val.2 = j then 1 else 0
    let k : ℝ := holeCount E
    let m : ℝ := Fintype.card I
    let n : ℝ := Fintype.card J
    let C0 : ℝ := max (max (m+n+1) (2*(m-1))) (max (2*(n-1)) 4)
    let Δ : Fin 4 → Fin 4 → ℝ :=
      ![![2*k,-rp,-cp,-h], ![-rp,2*k-rp,-up,-h*v],
        ![-cp,-up,2*k-cp,-h*t], ![-h,-h*v,-h*t,-h]]
    let Q := ∑ a : Fin 4, ∑ b : Fin 4, x a*x b*Δ a b
    have hQ : Q = 2*k*x 0^2+(2*k-rp)*x 1^2+(2*k-cp)*x 2^2-h*x 3^2-
        2*(rp*x 0*x 1+cp*x 0*x 2+h*x 0*x 3+up*x 1*x 2+
          h*v*x 1*x 3+h*t*x 2*x 3) := by
      simp [Q, Δ, Fin.sum_univ_succ]
      <;> ring
    change 0 ≤ holeBaselineGap E i j z x + ε *
        (2*k*x 0^2+(2*k-rp)*x 1^2+(2*k-cp)*x 2^2-h*x 3^2-
        2*(rp*x 0*x 1+cp*x 0*x 2+h*x 0*x 3+up*x 1*x 2+
          h*v*x 1*x 3+h*t*x 2*x 3))
    rw [← hQ]
    have hcols : (∑ b : J, (colDegree E b : ℝ)) = k := by
      simp only [k, holeCount, colDegree, rowDegree, Nat.cast_sum,
        Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    have hswap : holeCount (fun b a => E a b) = holeCount E := by
      simp only [holeCount, rowDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    have hrControls := degree_reweighted_row_controls E 0 (le_refl 0)
      (by simp) (by omega) i
    have hcControls := degree_reweighted_col_controls (fun b a => E a b) 0 (le_refl 0)
      (by simp) (by omega) j
    have hr : rp ≤ k*(n-1) := hrControls.2.1
    have hc : cp ≤ k*(m-1) := by
      simpa only [cp, k, m, rowDegree, colDegree, add_comm, hswap] using hcControls.2.1
    have hh : h ≤ k := by
      have hp := (degree_reweighted_row_controls E 0 (le_refl 0)
        (by simp) (by omega) z.val.1).2.2 z.val.2 z.property
      dsimp [h,k]
      exact_mod_cast hp
    have hup : up ≤ k := by
      dsimp [up]
      split_ifs with hij
      · exact Nat.cast_nonneg _
      · dsimp [k]
        exact_mod_cast hrControls.2.2 j hij
    have hk : 0 ≤ k := Nat.cast_nonneg _
    have hr0 : 0 ≤ rp := by dsimp [rp]; positivity
    have hc0 : 0 ≤ cp := by dsimp [cp]; positivity
    have hh0 : 0 ≤ h := by dsimp [h]; positivity
    have hup0 : 0 ≤ up := by dsimp [up]; split_ifs <;> positivity
    have hv0 : 0 ≤ v := by dsimp [v]; split_ifs <;> norm_num
    have ht0 : 0 ≤ t := by dsimp [t]; split_ifs <;> norm_num
    have hv1 : v ≤ 1 := by dsimp [v]; split_ifs <;> norm_num
    have ht1 : t ≤ 1 := by dsimp [t]; split_ifs <;> norm_num
    have hhv0 : 0 ≤ h*v := mul_nonneg hh0 hv0
    have hht0 : 0 ≤ h*t := mul_nonneg hh0 ht0
    have hhv : h*v ≤ k := (mul_le_of_le_one_right hh0 hv1).trans hh
    have hht : h*t ≤ k := (mul_le_of_le_one_right hh0 ht1).trans hh
    have hmR : 3 ≤ m := by dsimp [m]; exact_mod_cast hm
    have hnR : 3 ≤ n := by dsimp [n]; exact_mod_cast hn
    have hdiagR : |2*k-rp|+rp+up+h*v ≤ 2*k*(n-1) := by
      by_cases hd : 0 ≤ 2*k-rp
      · rw [abs_of_nonneg hd]
        nlinarith only [hup, hhv, mul_nonneg hk (sub_nonneg.mpr hnR)]
      · rw [abs_of_neg (lt_of_not_ge hd)]
        linarith only [hr, hup, hhv]
    have hdiagC : |2*k-cp|+cp+up+h*t ≤ 2*k*(m-1) := by
      by_cases hd : 0 ≤ 2*k-cp
      · rw [abs_of_nonneg hd]
        nlinarith only [hup, hht, mul_nonneg hk (sub_nonneg.mpr hmR)]
      · rw [abs_of_neg (lt_of_not_ge hd)]
        linarith only [hc, hup, hht]
    have hCmn : m+n+1 ≤ C0 := (le_max_left _ _).trans (le_max_left _ _)
    have hCm : 2*(m-1) ≤ C0 := (le_max_right _ _).trans (le_max_left _ _)
    have hCn : 2*(n-1) ≤ C0 := (le_max_left _ _).trans (le_max_right _ _)
    have hC4 : 4 ≤ C0 := (le_max_right _ _).trans (le_max_right _ _)
    have hrows (a : Fin 4) : (∑ b : Fin 4, |Δ a b|) ≤ k*C0 := by
      fin_cases a
      · simp [Δ, Fin.sum_univ_succ, abs_mul, abs_of_nonneg hk,
          abs_of_nonneg hr0, abs_of_nonneg hc0, abs_of_nonneg hh0]
        nlinarith only [hr, hc, hh, mul_le_mul_of_nonneg_left hCmn hk]
      · simp [Δ, Fin.sum_univ_succ, neg_mul, abs_of_nonneg hr0,
          abs_of_nonneg hup0, abs_of_nonneg hhv0]
        nlinarith only [hdiagR, mul_le_mul_of_nonneg_left hCn hk]
      · simp [Δ, Fin.sum_univ_succ, neg_mul, abs_of_nonneg hc0,
          abs_of_nonneg hup0, abs_of_nonneg hht0]
        nlinarith only [hdiagC, mul_le_mul_of_nonneg_left hCm hk]
      · simp [Δ, Fin.sum_univ_succ, neg_mul, abs_of_nonneg hh0,
          abs_of_nonneg hhv0, abs_of_nonneg hht0]
        nlinarith only [hh, hhv, hht, mul_le_mul_of_nonneg_left hC4 hk]
    have habs : |Q| ≤ k*C0*(x 0^2+x 1^2+x 2^2+x 3^2) := by
      calc
        |Q| ≤ ∑ a : Fin 4, x a^2 * ∑ b : Fin 4, |Δ a b| :=
          LongGapsBetweenPrimes.abs_quadratic_form_le_rows x Δ (by
            intro a b
            fin_cases a <;> fin_cases b <;> rfl)
        _ ≤ ∑ a : Fin 4, x a^2*(k*C0) :=
          Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hrows a) (sq_nonneg _))
        _ = _ := by simp [Fin.sum_univ_succ]; ring
    by_cases hne : rowDegree E i+colDegree E j≠0 ∨ z.val≠(i,j)
    · have hgap := actual_hole_baseline_gap E hm hn i j z hne x
      have hnorm : 0 ≤ x 0^2+x 1^2+x 2^2+x 3^2 := by positivity
      have hsmall' : 9*ε*k*C0≤1 := hsmall
      have herror := mul_le_mul_of_nonneg_left (neg_le_of_abs_le habs) hε
      have hbudget := mul_le_mul_of_nonneg_right hsmall' hnorm
      nlinarith only [hgap, herror, hbudget]
    · have hdeg : rowDegree E i+colDegree E j=0 := not_not.mp (not_or.mp hne).1
      have hz : z.val=(i,j) := not_not.mp (not_or.mp hne).2
      have hdr : rowDegree E i=0 := by omega
      have hdc : colDegree E j=0 := by omega
      have hrowEmpty (b : J) : ¬ E i b := by
        intro hb
        have hp : 0 < rowDegree E i := Finset.card_pos.mpr
          ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩⟩
        omega
      have hcolEmpty (a : I) : ¬ E a j := by
        intro ha
        have hp : 0 < colDegree E j := Finset.card_pos.mpr
          ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
        omega
      have hrk : rp=k := by simpa [rp, hdr, hrowEmpty] using hcols
      have hck : cp=k := by simp [cp, hdc, hcolEmpty, k, holeCount]
      have hzero : h=0 := by simp [h, hz, hdr, hdc]
      have huzero : up=0 := by simp [up, hrowEmpty, hdr, hdc]
      have hv : v=1 := by simp [v,hz]
      have ht : t=1 := by simp [t,hz]
      have hQpos : 0 ≤ Q := by
        rw [hQ, hrk, hck, hzero, huzero]
        nlinarith only [mul_nonneg hk (sq_nonneg (x 0-x 1)),
          mul_nonneg hk (sq_nonneg (x 0-x 2))]
      have hbase : 0 ≤ holeBaselineGap E i j z x := by
        have hrCard : ((Finset.univ.filter (fun b => ¬ E i b)).card : ℝ)=n := by
          simp [hrowEmpty,n]
        have hcCard : ((Finset.univ.filter (fun a => ¬ E a j)).card : ℝ)=m := by
          simp [hcolEmpty,m]
        have heq : holeBaselineGap E i j z x =
            n*(x 0-x 1)^2+m*(x 0-x 2)^2+(x 0-x 3)^2+
            (x 1-x 2)^2+(x 1-x 3)^2+(x 2-x 3)^2 := by
          simp [holeBaselineGap, hrowEmpty, hcolEmpty, hz, m, n]
          <;> ring
        rw [heq]
        positivity
      exact add_nonneg hbase (mul_nonneg hε hQpos)

  have weighted_load_gram_expansion
      (E : I → J → Prop) [DecidableRel E]
      (w : I × J → ℝ) (i : I) (j : J)
      (z : {p : I × J // ¬ E p.1 p.2}) (a b c d : ℝ) :
      let T := Finset.univ.filter (fun p : I × J => ¬ E p.1 p.2)
      let Z := ∑ p ∈ T, w p
      let R := ∑ p ∈ T, if p.1 = i then w p else 0
      let C := ∑ p ∈ T, if p.2 = j then w p else 0
      (∑ p ∈ T, w p *
        (a + (if p.1 = i then b else 0) +
          (if p.2 = j then c else 0) + (if p = z.val then d else 0)) ^ 2) =
        Z * a ^ 2 + R * (b ^ 2 + 2 * a * b) + C * (c ^ 2 + 2 * a * c) +
        w z.val * (d ^ 2 + 2 * a * d) +
        2 * (if ¬ E i j then w (i, j) else 0) * b * c +
        2 * (if z.val.1 = i then 1 else 0) * w z.val * b * d +
        2 * (if z.val.2 = j then 1 else 0) * w z.val * c * d := by
    classical
    dsimp only
    let T := Finset.univ.filter (fun p : I × J => ¬ E p.1 p.2)
    have hz : z.val ∈ T := by simp [T, z.property]
    have hpoint : (∑ p ∈ T, if p = z.val then w p else 0) = w z.val := by
      simp [hz]
    have hcross : (∑ p ∈ T, if p = (i, j) then w p else 0) =
        if ¬ E i j then w (i, j) else 0 := by
      simp [T]
    have hrowpoint : (∑ p ∈ T,
        if p = z.val then (if z.val.1 = i then w p else 0) else 0) =
        (if z.val.1 = i then 1 else 0) * w z.val := by
      simp only [Finset.sum_ite_eq', hz, if_true]
      split_ifs <;> ring
    have hcolpoint : (∑ p ∈ T,
        if p = z.val then (if z.val.2 = j then w p else 0) else 0) =
        (if z.val.2 = j then 1 else 0) * w z.val := by
      simp only [Finset.sum_ite_eq', hz, if_true]
      split_ifs <;> ring
    change (∑ p ∈ T, _) = _
    calc
      _ = ∑ p ∈ T,
          (w p * a ^ 2 + (if p.1 = i then w p else 0) * (b ^ 2 + 2 * a * b) +
          (if p.2 = j then w p else 0) * (c ^ 2 + 2 * a * c) +
          (if p = z.val then w p else 0) * (d ^ 2 + 2 * a * d) +
          2 * (if p = (i, j) then w p else 0) * b * c +
          2 * (if p = z.val then (if z.val.1 = i then w p else 0) else 0) * b * d +
          2 * (if p = z.val then (if z.val.2 = j then w p else 0) else 0) * c * d) := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hpz : p = z.val
        · subst p
          by_cases hi : z.val.1 = i <;> by_cases hj : z.val.2 = j <;>
            simp [hi, hj, Prod.ext_iff] <;> ring
        · by_cases hi : p.1 = i <;> by_cases hj : p.2 = j <;>
            simp [hpz, hi, hj, Prod.ext_iff] <;> ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
          hpoint, hcross, hrowpoint, hcolpoint]
        ring

  have row_mass_expansion
      (E : I → J → Prop) [DecidableRel E]
      (f : I × J → ℝ) (ε : ℝ) (i : I) :
      (∑ p ∈ Finset.univ.filter (fun p : I × J => ¬ E p.1 p.2),
        if p.1 = i then 1 + ε * f p else 0) =
        ((Finset.univ.filter (fun j => ¬ E i j)).card : ℝ) +
          ε * ∑ j ∈ Finset.univ.filter (fun j => ¬ E i j), f (i, j) := by
    classical
    have hfiber : (∑ p ∈ Finset.univ.filter (fun p : I × J => ¬ E p.1 p.2),
        if p.1 = i then 1 + ε * f p else 0) =
        ∑ j ∈ Finset.univ.filter (fun j => ¬ E i j), (1 + ε * f (i, j)) := by
      simp only [Finset.sum_filter, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      calc
        _ = ∑ a : I, if a = i then (if ¬ E i j then 1 + ε * f (i, j) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          by_cases h : a = i <;> simp [h]
        _ = _ := by simp
    rw [hfiber]
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      mul_one, ← Finset.mul_sum]

  let T := Finset.univ.filter (fun p : I × J => ¬ E p.1 p.2)
  let f := fun p : I × J => (rowDegree E p.1 : ℝ) + colDegree E p.2
  let w := fun p : I × J => 1+ε*f p
  let Z := ∑ p ∈ T, w p
  let R := ∑ p ∈ T, if p.1=i then w p else 0
  let C := ∑ p ∈ T, if p.2=j then w p else 0
  let r : ℝ := (Finset.univ.filter (fun b => ¬ E i b)).card
  let c : ℝ := (Finset.univ.filter (fun a => ¬ E a j)).card
  let rp : ℝ := ∑ b ∈ Finset.univ.filter (fun b => ¬ E i b), f (i,b)
  let cp : ℝ := ∑ a ∈ Finset.univ.filter (fun a => ¬ E a j), f (a,j)
  let h := f z.val
  let u : ℝ := if E i j then 0 else 1
  let up : ℝ := if E i j then 0 else f (i,j)
  let v : ℝ := if z.val.1=i then 1 else 0
  let t : ℝ := if z.val.2=j then 1 else 0
  let k : ℝ := holeCount E
  let m : ℝ := Fintype.card I
  let n : ℝ := Fintype.card J
  have hR : R=r+ε*rp := row_mass_expansion E f ε i
  have hC : C=c+ε*cp := by
    have hfiber : C=∑ a ∈ Finset.univ.filter (fun a => ¬ E a j), (1+ε*f (a,j)) := by
      dsimp [C,T,w]
      simp only [Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a ha
      calc
        _ = ∑ b : J, if b=j then (if ¬ E a j then 1+ε*f (a,j) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro b hb
          by_cases hh : b=j <;> simp [hh]
        _ = _ := by simp
    rw [hfiber]
    dsimp [c,cp]
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      mul_one, ← Finset.mul_sum]
  have hu : (if ¬ E i j then w (i,j) else 0)=u+ε*up := by
    dsimp [w,u,up]
    split_ifs <;> ring
  have hsum := weighted_load_gram_expansion E w i j z (x 0) (x 1) (x 2) (x 3)
  change (∑ p ∈ T, w p *
      (x 0 + (if p.1=i then x 1 else 0) +
        (if p.2=j then x 2 else 0) + (if p=z.val then x 3 else 0))^2) ≤
      (Z+m+n+1+2*ε*k)*x 0^2+2*(n+1+ε*k)*x 1^2+
      2*(m+1+ε*k)*x 2^2+4*x 3^2
  change (∑ p ∈ T, _) = Z*x 0^2+R*(x 1^2+2*x 0*x 1)+C*(x 2^2+2*x 0*x 2)+
    w z.val*(x 3^2+2*x 0*x 3)+2*(if ¬ E i j then w (i,j) else 0)*x 1*x 2+
    2*v*w z.val*x 1*x 3+2*t*w z.val*x 2*x 3 at hsum
  rw [hsum,hR,hC,hu]
  have hgap := actual_degree_perturbation_gap E hm hn ε hε hsmall i j z x
  change 0 ≤ holeBaselineGap E i j z x+ε*
    (2*k*x 0^2+(2*k-rp)*x 1^2+(2*k-cp)*x 2^2-h*x 3^2-
    2*(rp*x 0*x 1+cp*x 0*x 2+h*x 0*x 3+up*x 1*x 2+
      h*v*x 1*x 3+h*t*x 2*x 3)) at hgap
  have hbase : holeBaselineGap E i j z x =
      (m+n+1)*x 0^2+(2*(n+1)-r)*x 1^2+(2*(m+1)-c)*x 2^2+3*x 3^2-
      2*(r*x 0*x 1+c*x 0*x 2+x 0*x 3+u*x 1*x 2+v*x 1*x 3+t*x 2*x 3) := by
    simp only [holeBaselineGap,m,n,r,c,u,v,t]
    congr!
  rw [hbase] at hgap
  have hw : w z.val=1+ε*h := rfl
  rw [hw]
  nlinarith only [hgap]


end D5.S3.Arith.Congruence.ArbitraryHoleGram
