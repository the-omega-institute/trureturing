/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47TypeIIBounds
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47TypeIIBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47TypeII
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-! The actual permutation-cycle count in Part I Proposition 9.1 and
Proposition 10.2, printed pp. 222 and 230.  Singleton fixed-point cycles
are included, as required by c(g_j) in inequality (36). -/
namespace NikolovSegal.Equation47TypeII
universe u
variable {I : Type u} [Fintype I]

noncomputable def actualCycleCount (sigma : Equiv.Perm I) : ℕ :=
  Nat.card (Quotient (Equiv.Perm.SameCycle.setoid sigma))

noncomputable def actualFixedCount (sigma : Equiv.Perm I) : ℕ :=
  Nat.card {i : I // sigma i = i}

/-- The genuine nonbase VALUE coordinates left free by substitution (50).
Exactly one base coordinate is removed for EACH ACTUAL permutation cycle. -/
abbrev NonbaseValueCoordinate (sigma : Equiv.Perm I) :=
  {i : I // i ≠ (Quotient.mk (Equiv.Perm.SameCycle.setoid sigma) i).out}

private theorem nonbase_card (sigma : Equiv.Perm I) :
    Nat.card (NonbaseValueCoordinate sigma) + actualCycleCount sigma = Fintype.card I := by
  classical
  let C := ActualCycle sigma
  letI : Fintype C := Fintype.ofFinite C
  let Q : I → C := fun i => Quotient.mk _ i
  let p : I → Prop := fun i => i = (Q i).out
  let e : C ≃ {i : I // p i} :=
    { toFun := fun c => ⟨c.out,by change c.out = (Quotient.mk _ c.out).out; rw [c.out_eq]⟩
      invFun := fun i => Q i.val
      left_inv := fun c => c.out_eq
      right_inv := fun i => Subtype.ext i.prop.symm }
  have hc := Fintype.card_congr e
  have hp := Fintype.card_subtype_le p
  have hb := Fintype.card_subtype_compl p
  simp only [Nat.card_eq_fintype_card,actualCycleCount]
  change Fintype.card {i : I // ¬p i} + Fintype.card C = Fintype.card I
  rw [hb,hc]
  exact Nat.sub_add_cancel hp

/-- The actual variable count mn - sum c(g_j), BEFORE the n-1 tree
substitutions.  This identifies the paper's matching-pair count with the
number of genuinely free nonbase coordinate values, rather than abstract men
or unused labels. -/
theorem cycle_value_free_coordinate_count {m : ℕ} (tau : Fin m → Equiv.Perm I) :
    (∑ j : Fin m, Nat.card (NonbaseValueCoordinate (tau j))) +
      (∑ j : Fin m, actualCycleCount (tau j)) = m * Fintype.card I := by
  rw [← Finset.sum_add_distrib]
  simp [nonbase_card]

/-- Each nonfixed ACTUAL cycle contributes a second distinct vertex.
The two injections are disjoint; arbitrarily labelled representatives of
one cycle would not justify this count. -/
theorem actual_cycle_count_bound (sigma : Equiv.Perm I) :
    2 * actualCycleCount sigma ≤ Fintype.card I + actualFixedCount sigma := by
  classical
  let C := Quotient (Equiv.Perm.SameCycle.setoid sigma)
  letI : Fintype C := Fintype.ofFinite C
  let good : C → Prop := fun c => sigma c.out = c.out
  let bad : Type u := {c : C // ¬ good c}
  let f : C ⊕ bad → I := fun s => match s with
    | .inl c => c.out
    | .inr b => sigma b.val.out
  have hclass : ∀ c : C, Quotient.mk (Equiv.Perm.SameCycle.setoid sigma)
      (sigma c.out) = c := by
    intro c
    calc
      Quotient.mk (Equiv.Perm.SameCycle.setoid sigma) (sigma c.out) =
          Quotient.mk (Equiv.Perm.SameCycle.setoid sigma) c.out :=
        Quotient.sound (Equiv.Perm.SameCycle.refl sigma c.out).apply_left
      _ = c := c.out_eq
  have hf : Function.Injective f := by
    intro s t h
    cases s with
    | inl c => cases t with
      | inl d => exact congrArg Sum.inl (Quotient.out_injective h)
      | inr b =>
        have hh := congrArg (Quotient.mk (Equiv.Perm.SameCycle.setoid sigma)) h
        change Quotient.mk _ c.out = Quotient.mk _ (sigma b.val.out) at hh
        rw [c.out_eq,hclass] at hh
        change c.out = sigma b.val.out at h
        rw [hh] at h
        exact False.elim (b.prop h.symm)
    | inr b => cases t with
      | inl c =>
        have hh := congrArg (Quotient.mk (Equiv.Perm.SameCycle.setoid sigma)) h
        change Quotient.mk _ (sigma b.val.out) = Quotient.mk _ c.out at hh
        rw [hclass,c.out_eq] at hh
        change sigma b.val.out = c.out at h
        rw [← hh] at h
        exact False.elim (b.prop h)
      | inr d =>
        exact congrArg Sum.inr (Subtype.ext
          (Quotient.out_injective (sigma.injective h)))
  have hsize := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_sum] at hsize
  let g : {c : C // good c} → {i : I // sigma i = i} :=
    fun c => ⟨c.val.out,c.prop⟩
  have hg : Function.Injective g := by
    intro c d h
    exact Subtype.ext (Quotient.out_injective (congrArg Subtype.val h))
  have hfixed := Fintype.card_le_of_injective g hg
  have hcompl := Fintype.card_subtype_compl good
  have hle := Fintype.card_subtype_le good
  change Fintype.card bad = Fintype.card C - Fintype.card {c : C // good c} at hcompl
  simp only [actualCycleCount,actualFixedCount,Nat.card_eq_fintype_card]
  change 2 * Fintype.card C ≤ Fintype.card I + Fintype.card {i : I // sigma i = i}
  omega

/-- The actual type-II movement threshold gives precisely Proposition
9.1's cycle inequality.  Its twisted constant is D; the Section 10
classification constant is 4+2D.  The argument applies to each genuine
powered component separately, with its own cardinal n. -/
theorem typeII_cycle_budget {m D : ℕ} (tau : Fin m → Equiv.Perm I)
    (hn : 2 ≤ Fintype.card I)
    (htype : (4+2*D) * Fintype.card I ≤
      ∑ j : Fin m, (Fintype.card I - actualFixedCount (tau j))) :
    (∑ j : Fin m, actualCycleCount (tau j)) +
      2 * Fintype.card I + 2 * D ≤ m * Fintype.card I := by
  classical
  let n := Fintype.card I
  have hf : ∀ j, actualFixedCount (tau j) ≤ n := by
    intro j
    simpa [actualFixedCount,Nat.card_eq_fintype_card,n] using
      Fintype.card_subtype_le (fun i : I => tau j i = i)
  have htotal : (∑ j : Fin m, (n-actualFixedCount (tau j))) +
      (∑ j : Fin m, actualFixedCount (tau j)) = m*n := by
    rw [← Finset.sum_add_distrib]
    simp [Nat.sub_add_cancel (hf _)]
  have hcycle : 2*(∑ j : Fin m, actualCycleCount (tau j)) ≤
      m*n + ∑ j : Fin m, actualFixedCount (tau j) := by
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
      actual_cycle_count_bound (tau j))
    simpa [Finset.mul_sum,Finset.sum_add_distrib,n] using hh
  change (4+2*D)*n ≤ _ at htype
  change 2 ≤ n at hn
  change _ + 2*n + 2*D ≤ m*n
  nlinarith

/-- The number of matching pairs remaining AFTER the paper's cycle-value
substitution and n-1 inter-equation substitutions.  This is the numerical
bound used by Proposition 8.4, not a claim that extraction already exists. -/
theorem typeII_residual_pair_budget {m D : ℕ} (tau : Fin m → Equiv.Perm I)
    (hn : 2 ≤ Fintype.card I)
    (htype : (4+2*D) * Fintype.card I ≤
      ∑ j : Fin m, (Fintype.card I - actualFixedCount (tau j))) :
    Fintype.card I + 2*D + 1 ≤
      m * Fintype.card I - (∑ j : Fin m, actualCycleCount (tau j)) -
        (Fintype.card I - 1) := by
  have h := typeII_cycle_budget tau hn htype
  omega

/-- Consume both the actual coordinate count and the type-II cycle bound.
The subsequent balanced-word/colour-type argument must still construct the
extraction certificate; this count alone does not assert that conclusion. -/
theorem typeII_free_coordinate_budget {m D : ℕ} (tau : Fin m → Equiv.Perm I)
    (hn : 2 ≤ Fintype.card I)
    (htype : (4+2*D) * Fintype.card I ≤
      ∑ j : Fin m, (Fintype.card I - actualFixedCount (tau j))) :
    Fintype.card I + 2*D + 1 ≤
      (∑ j : Fin m, Nat.card (NonbaseValueCoordinate (tau j))) -
        (Fintype.card I - 1) := by
  have h := typeII_residual_pair_budget tau hn htype
  have hc := cycle_value_free_coordinate_count tau
  omega

end NikolovSegal.Equation47TypeII
