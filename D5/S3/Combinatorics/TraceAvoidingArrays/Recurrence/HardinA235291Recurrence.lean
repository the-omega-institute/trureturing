/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235291Recurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235291Recurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hardin's signed order-four recurrence for literal two-column arrays. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import OmegaBuild.Commands

/-! Weighted row differences for two-column constant-stress arrays. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235291Recurrence

open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet (C Legal)

private abbrev Row := Fin 2 → Fin 4
private abbrev Grid (n : ℕ) := Fin (n + 1) → Row

/-- Main diagonal sum minus antidiagonal sum in a consecutive-row block. -/
private def stress (r s : Row) : ℤ :=
  (r 0).val + (s 1).val - (r 1).val - (s 0).val

private def Bond (r s : Row) : Prop := (stress r s).natAbs = 3

private instance (r s : Row) : Decidable (Bond r s) := inferInstanceAs (Decidable (_ = _))

private def Valid {n : ℕ} (g : Grid n) : Prop :=
  ∀ i : Fin n, Bond (g i.castSucc) (g i.succ)

private instance {n : ℕ} (g : Grid n) : Decidable (Valid g) := by
  unfold Valid
  infer_instance

private def rowDiff (r : Row) : ℤ := (r 0).val - (r 1).val

/-- Difference class indexed by the signed difference plus three. -/
private def diffIndex (r : Row) : Fin 7 :=
  ⟨(rowDiff r + 3).toNat, by
    have h0 := (r 0).isLt
    have h1 := (r 1).isLt
    unfold rowDiff
    omega⟩

private def Adj (i j : Fin 7) : Prop := ((i.val : ℤ) - j.val).natAbs = 3

private instance (i j : Fin 7) : Decidable (Adj i j) := inferInstanceAs (Decidable (_ = _))

private theorem bond_iff_adj (r s : Row) : Bond r s ↔ Adj (diffIndex r) (diffIndex s) := by
  have idx (u : Row) : ((diffIndex u).val : ℤ) = rowDiff u + 3 := by
    apply Int.toNat_of_nonneg
    have h1 := (u 1).isLt
    unfold rowDiff
    omega
  unfold Bond Adj
  rw [idx r, idx s]
  have hs : stress r s = (rowDiff r + 3) - (rowDiff s + 3) := by
    unfold stress rowDiff
    ring
  rw [hs]

/-- Size of the row fiber at a difference class. -/
private def weight (i : Fin 7) : ℕ := 4 - ((i.val : ℤ) - 3).natAbs

private theorem row_fiber_count (i : Fin 7) :
    Fintype.card {r : Row // diffIndex r = i} = weight i := by
  fin_cases i <;> decide

/-- One step, with the multiplicity of the next row included. The residue
components on shifted indices are 0–3–6, 1–4, and 2–5. -/
private def step (f : Fin 7 → ℤ) : Fin 7 → ℤ :=
  ![4 * f 3, 3 * f 4, 2 * f 5, f 0 + f 6, 2 * f 1, 3 * f 2, 4 * f 3]

private theorem step_eq_sum (f : Fin 7 → ℤ) (i : Fin 7) :
    step f i = ∑ j : Fin 7, if Adj i j then (weight j : ℤ) * f j else 0 := by
  fin_cases i <;> norm_num [step, Adj, weight, Fin.sum_univ_succ]

private def iterate (n : ℕ) (f : Fin 7 → ℤ) : Fin 7 → ℤ :=
  match n with
  | 0 => f
  | n + 1 => step (iterate n f)

private def total (f : Fin 7 → ℤ) : ℤ := ∑ i : Fin 7, (weight i : ℤ) * f i

private def weightedCount (n : ℕ) : ℤ := total (iterate n fun _ => 1)

/-- The fourth-order polynomial annihilates functions that agree at the two
leaves of 0–3–6. On this space two steps act by 8 there and by 6 elsewhere. -/
private theorem annihilate (f : Fin 7 → ℤ) (h : f 0 = f 6) (i : Fin 7) :
    iterate 4 f i = 14 * iterate 2 f i - 48 * f i := by
  fin_cases i <;> simp [iterate, step, h] <;> ring

/-- Arbitrary terminal data, including a point indicator for any chosen finish. -/
private theorem endpoint_recurrence (n : ℕ) (f : Fin 7 → ℤ) (i : Fin 7) :
    iterate (n + 5) f i = 14 * iterate (n + 3) f i - 48 * iterate (n + 1) f i := by
  exact annihilate (iterate (n + 1) f) (by rfl) i

private abbrev WithHead (n : ℕ) (r : Row) := {g : Grid n // g 0 = r ∧ Valid g}

private theorem valid_cons {n : ℕ} (r : Row) (g : Grid n) :
    Valid (Fin.cons r g) ↔ Bond r (g 0) ∧ Valid g := by
  simp [Valid, Fin.forall_fin_succ, Fin.castSucc_succ]

private def splitHead (n : ℕ) : {g : Grid n // Valid g} ≃ (Σ r : Row, WithHead n r) where
  toFun g := ⟨g.val 0, ⟨g.val, rfl, g.property⟩⟩
  invFun x := ⟨x.2.val, x.2.property.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨r, g, hg, _⟩
    subst r
    rfl

private def splitNext (n : ℕ) (r : Row) :
    WithHead (n + 1) r ≃ (Σ s : {s : Row // Bond r s}, WithHead n s.val) where
  toFun g := by
    let tail := Fin.tail g.val
    have hv : Valid (Fin.cons r tail) := by
      rw [← g.property.1]
      simpa only [tail, Fin.cons_self_tail] using g.property.2
    have h := (valid_cons r tail).mp hv
    exact ⟨⟨tail 0, h.1⟩, ⟨tail, rfl, h.2⟩⟩
  invFun x := ⟨Fin.cons r x.2.val, Fin.cons_zero _ _,
    (valid_cons r x.2.val).mpr
      ⟨(congrArg (Bond r) x.2.property.1).mpr x.1.property, x.2.property.2⟩⟩
  left_inv g := Subtype.ext (by
    calc
      Fin.cons r (Fin.tail g.val) = Fin.cons (g.val 0) (Fin.tail g.val) :=
        congrArg (fun s => Fin.cons s (Fin.tail g.val)) g.property.1.symm
      _ = g.val := Fin.cons_self_tail g.val)
  right_inv := by
    rintro ⟨⟨s, hs⟩, ⟨g, hg, hv⟩⟩
    change g 0 = s at hg
    subst s
    simp
    rfl

private def headCount (n : ℕ) (r : Row) : ℤ := (Fintype.card (WithHead n r) : ℤ)

private theorem headCount_zero (r : Row) : headCount 0 r = 1 := by
  let e : WithHead 0 r ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨fun _ => r, rfl, by simp [Valid]⟩
      left_inv := by
        intro g
        apply Subtype.ext
        funext i
        have hi : i = 0 := Fin.eq_zero i
        rw [hi]
        exact g.property.1.symm
      right_inv := fun x => by cases x; rfl }
  simpa [headCount] using congrArg (fun k : ℕ => (k : ℤ)) (Fintype.card_congr e)

private theorem headCount_succ (n : ℕ) (r : Row) :
    headCount (n + 1) r = ∑ s : Row, if Bond r s then headCount n s else 0 := by
  calc
    _ = ∑ s : {s : Row // Bond r s}, headCount n s.val := by
      unfold headCount
      rw [Fintype.card_congr (splitNext n r), Fintype.card_sigma, Nat.cast_sum]
    _ = _ := by
      rw [← Finset.subtype_univ (Bond r), Finset.sum_subtype_eq_sum_filter, Finset.sum_filter]

private theorem sum_by_diff (f : Fin 7 → ℤ) :
    (∑ r : Row, f (diffIndex r)) = total f := by
  let e := Equiv.sigmaFiberEquiv diffIndex
  calc
    _ = ∑ x : Σ i : Fin 7, {r : Row // diffIndex r = i}, f x.1 := by
      symm
      apply Fintype.sum_equiv e
      intro x
      exact congrArg f x.2.property.symm
    _ = total f := by simp [Fintype.sum_sigma, total, row_fiber_count]

private theorem head_count_bridge (n : ℕ) (r : Row) :
    headCount n r = iterate n (fun _ => 1) (diffIndex r) := by
  induction n generalizing r with
  | zero => exact headCount_zero r
  | succ n ih =>
    let f := iterate n fun _ => 1
    calc
      _ = ∑ s : Row, if Adj (diffIndex r) (diffIndex s) then f (diffIndex s) else 0 := by
        rw [headCount_succ]
        apply Finset.sum_congr rfl
        intro s _
        by_cases h : Adj (diffIndex r) (diffIndex s) <;> simp [bond_iff_adj, h, ih, f]
      _ = total (fun j => if Adj (diffIndex r) j then f j else 0) :=
        sum_by_diff (fun j => if Adj (diffIndex r) j then f j else 0)
      _ = _ := by
        rw [iterate, step_eq_sum, total]
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : Adj (diffIndex r) j <;> simp [h, f]

private def legalEquiv (n : ℕ) :
    {g : HardinA235280A235310Alphabet.Grid 3 n 1 // Legal 3 g} ≃
      {g : Grid n // Valid g} :=
  Equiv.subtypeEquiv (Equiv.curry _ _ _) (by
    intro g
    unfold Legal Valid
    refine forall_congr' fun i => ?_
    have hzero : (0 : Fin 1).castSucc = (0 : Fin 2) := rfl
    have hone : (0 : Fin 1).succ = (1 : Fin 2) := rfl
    change (∀ c : Fin 1, _) ↔ Bond (g ∘ Prod.mk i.castSucc) (g ∘ Prod.mk i.succ)
    rw [Fin.forall_fin_one]
    simp only [Bond, stress, Function.comp_apply, hzero, hone, sub_sub])

private theorem literal_eq_weighted (n : ℕ) : (C 3 3 n 1 : ℤ) = weightedCount n := by
  unfold C weightedCount
  rw [Nat.card_congr (legalEquiv n), Nat.card_eq_fintype_card,
    Fintype.card_congr (splitHead n), Fintype.card_sigma, Nat.cast_sum]
  change (∑ r : Row, headCount n r) = _
  simp_rw [head_count_bridge]
  exact sum_by_diff _

private theorem weighted_recurrence (n : ℕ) :
    weightedCount (n + 5) = 14 * weightedCount (n + 3) - 48 * weightedCount (n + 1) := by
  simp only [weightedCount, total, endpoint_recurrence]
  calc
    _ = ∑ i : Fin 7,
        (14 * ((weight i : ℤ) * iterate (n + 3) (fun _ => 1) i) -
         48 * ((weight i : ℤ) * iterate (n + 1) (fun _ => 1) i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

/-- The signed recurrence at every left index for which all published lags are positive. -/
theorem result (n : ℕ) (hn : 5 ≤ n) :
    (C 3 3 n 1 : ℤ) = 14 * (C 3 3 (n - 2) 1 : ℤ) - 48 * (C 3 3 (n - 4) 1 : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [literal_eq_weighted, Nat.add_comm 5 k]
  exact weighted_recurrence k

end D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235291Recurrence
