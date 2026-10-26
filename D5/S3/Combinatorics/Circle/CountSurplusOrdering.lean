/- GID: D5/S3/Combinatorics/Circle/CountSurplusOrdering
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/CountSurplusOrdering
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic, mathlib/module/Mathlib.Algebra.Order.BigOperators.Group.List]
   utility: none
   digest: A surplus of actual negative LARGE occurrences orders bounded exceptional positives. -/
module
public import D5.S3.Combinatorics.Circle.SmallStepOrdering

/-! # Ordering exceptional positive steps by paired consumption

`E` marks actual list occurrences through their labels. Its count is the list
count, so repeated values and repeated labels are counted with multiplicity.
Only marked steps need the bound `Q - 1`. Every unmarked positive step must
be compatible with every negative step. With one more negative LARGE than
marked steps, a negative LARGE can always be followed immediately by a
marked positive. The final result permutes the entire original list.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.CountSurplusOrdering
open SourceWidth

private theorem sum_le_two_counts {α : Type*} (f : α → ℤ)
    (E N : α → Bool) (a d : ℤ) (labels : List α)
    (hpoint : ∀ x ∈ labels,
      f x ≤ (if E x then a else 0) + (if N x then d else 0)) :
    (labels.map f).sum ≤ (labels.countP E : ℤ) * a +
      (labels.countP N : ℤ) * d := by
  induction labels with
  | nil => simp
  | cons x xs ih =>
    have hx := hpoint x (by simp)
    have hxs := ih (fun y hy => hpoint y (by simp [hy]))
    cases hEx : E x <;> cases hNx : N x <;>
      simp [List.countP_cons, hEx, hNx, Nat.cast_add] at hx ⊢ <;>
      nlinarith only [hx, hxs]

/- The only possible dead end would force all positive mass into E and all
negative LARGE steps strictly below the lower boundary. Counted with their
actual multiplicities, those LARGE steps force a negative final height. -/
private theorem exists_fitting_step {α : Type*} (f : α → ℤ)
    (E : α → Bool) (Q : ℤ) (labels : List α) (b : ℤ)
    (hQ : 2 ≤ Q)
    (hstart : 0 ≤ b ∧ b ≤ 2 * Q - 1)
    (hend : 0 ≤ b + (labels.map f).sum)
    (hEbound : ∀ x ∈ labels, E x = true → 0 < f x ∧ f x ≤ Q - 1)
    (hcompatible : ∀ p ∈ labels, ∀ n ∈ labels,
      E p = false → 0 < f p → f n < 0 → f p - f n ≤ 2 * Q - 1)
    (hEpos : 0 < labels.countP E)
    (hgap : labels.countP E + 1 ≤
      labels.countP (fun x => decide (f x ≤ -Q))) :
    ∃ q ∈ labels, 0 ≤ b + f q ∧ b + f q ≤ 2 * Q - 1 := by
  by_contra hnone
  have hfail : ∀ x ∈ labels, ¬ (0 ≤ b + f x ∧ b + f x ≤ 2 * Q - 1) := by
    intro x hx hfit
    exact hnone ⟨x, hx, hfit⟩
  have hNpos : 0 < labels.countP (fun x => decide (f x ≤ -Q)) := by omega
  obtain ⟨n, hn, hnN⟩ := List.countP_pos_iff.mp hNpos
  have hnlarge : f n ≤ -Q := of_decide_eq_true hnN
  have hallpos : ∀ p ∈ labels, 0 < f p → E p = true := by
    intro p hp hp0
    cases hEp : E p with
    | false =>
      have hpfail := hfail p hp
      have hnfail := hfail n hn
      have hcross := hcompatible p hp n hn hEp hp0 (by omega)
      exfalso
      omega
    | true => rfl
  obtain ⟨p, hp, hpE⟩ := List.countP_pos_iff.mp hEpos
  have hpbound := hEbound p hp hpE
  have hpfailed := hfail p hp
  have hb : Q + 1 ≤ b := by omega
  have hpoint : ∀ x ∈ labels,
      f x ≤ (if E x then Q - 1 else 0) +
        (if decide (f x ≤ -Q) then -(b + 1) else 0) := by
    intro x hx
    cases hEx : E x with
    | false =>
      by_cases hxN : f x ≤ -Q
      · have hxfailed := hfail x hx
        have hxupper : f x ≤ -(b + 1) := by omega
        simpa [hEx, hxN] using hxupper
      · have hxnonpos : f x ≤ 0 := by
          by_contra hxpos
          have hxt := hallpos x hx (by omega)
          simp [hEx] at hxt
        simpa [hEx, hxN] using hxnonpos
    | true =>
      have hxbound := hEbound x hx hEx
      have hxN : ¬ f x ≤ -Q := by omega
      simpa [hEx, hxN] using hxbound.2
  have hmass := sum_le_two_counts f E (fun x => decide (f x ≤ -Q))
    (Q - 1) (-(b + 1)) labels hpoint
  have hgapZ : (labels.countP E : ℤ) + 1 ≤
      (labels.countP (fun x => decide (f x ≤ -Q)) : ℤ) := by
    exact_mod_cast hgap
  have hnegative : -(b + 1) ≤ 0 := by omega
  have hlarge := mul_le_mul_of_nonpos_right hgapZ hnegative
  have hsmall : (labels.countP E : ℤ) * (Q - b - 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by omega)
  nlinarith only [hmass, hlarge, hsmall, hend]

private theorem complete_between {α : Type*} (f : α → ℤ)
    (E : α → Bool) (Q : ℤ) (hQ : 2 ≤ Q)
    (fuel : ℕ) (labels : List α) (b : ℤ)
    (hlen : labels.length ≤ fuel)
    (hstart : 0 ≤ b ∧ b ≤ 2 * Q - 1)
    (hend : 0 ≤ b + (labels.map f).sum ∧
      b + (labels.map f).sum ≤ 2 * Q - 1)
    (hEbound : ∀ x ∈ labels, E x = true → 0 < f x ∧ f x ≤ Q - 1)
    (hcompatible : ∀ p ∈ labels, ∀ n ∈ labels,
      E p = false → 0 < f p → f n < 0 → f p - f n ≤ 2 * Q - 1)
    (hsurplus : labels.countP E ≠ 0 → labels.countP E + 1 ≤
      labels.countP (fun x => decide (f x ≤ -Q))) :
    ∃ word : List α, word.Perm labels ∧ InStrip f (2 * Q - 1) b word := by
  classical
  induction fuel generalizing labels b with
  | zero =>
    have hempty : labels = [] := List.length_eq_zero_iff.mp (by omega)
    subst labels
    exact ⟨[], .refl _, hstart⟩
  | succ fuel ih =>
    by_cases hEzero : labels.countP E = 0
    · apply SmallStepOrdering.exists_order_between f labels (2 * Q - 1) b hstart hend
      intro p hp n hn hp0 hn0
      have hpnotE := List.countP_eq_zero.mp hEzero p hp
      have hpE : E p = false := Bool.eq_false_iff.mpr hpnotE
      exact hcompatible p hp n hn hpE hp0 hn0
    · have hEpos : 0 < labels.countP E := by omega
      have hgap := hsurplus hEzero
      obtain ⟨q, hq, hqlo, hqhi⟩ :=
        exists_fitting_step f E Q labels b hQ hstart hend.1
          hEbound hcompatible hEpos hgap
      by_cases hqN : f q ≤ -Q
      · obtain ⟨p, hp, hpE⟩ := List.countP_pos_iff.mp hEpos
        have hpbound := hEbound p hp hpE
        have hpne : p ≠ q := by
          intro hpq
          subst p
          omega
        have hp' : p ∈ labels.erase q := (List.mem_erase_of_ne hpne).mpr hp
        have hqE : E q = false := Bool.eq_false_iff.mpr (by
          intro hEq
          have hqbound := hEbound q hq hEq
          omega)
        have hpN : ¬ f p ≤ -Q := by omega
        have hpair : 0 ≤ b + f q + f p ∧ b + f q + f p ≤ 2 * Q - 1 := by
          constructor <;> omega
        have hperm : labels.Perm (q :: p :: (labels.erase q).erase p) :=
          (List.perm_cons_erase hq).trans ((List.perm_cons_erase hp').cons q)
        have he := (hperm.map f).sum_eq
        simp only [List.map_cons, List.sum_cons] at he
        have hlenq := List.length_erase_add_one hq
        have hlenp := List.length_erase_add_one hp'
        have hEc : labels.countP E = ((labels.erase q).erase p).countP E + 1 := by
          simpa [List.countP_cons, hqE, hpE] using
            (List.Perm.countP_eq E hperm)
        have hNc : labels.countP (fun x => decide (f x ≤ -Q)) =
            ((labels.erase q).erase p).countP (fun x => decide (f x ≤ -Q)) + 1 := by
          simpa [List.countP_cons, hqN, hpN] using
            (List.Perm.countP_eq (fun x => decide (f x ≤ -Q)) hperm)
        have hgap' : ((labels.erase q).erase p).countP E ≠ 0 →
            ((labels.erase q).erase p).countP E + 1 ≤
              ((labels.erase q).erase p).countP (fun x => decide (f x ≤ -Q)) := by
          intro _
          omega
        obtain ⟨word, hw, hs⟩ := ih ((labels.erase q).erase p) (b + f q + f p)
          (by omega) hpair (by constructor <;> omega)
          (fun x hx => hEbound x (List.mem_of_mem_erase (List.mem_of_mem_erase hx)))
          (fun x hx y hy => hcompatible x
            (List.mem_of_mem_erase (List.mem_of_mem_erase hx)) y
            (List.mem_of_mem_erase (List.mem_of_mem_erase hy))) hgap'
        exact ⟨q :: p :: word, ((hw.cons p).cons q).trans hperm.symm,
          hstart.1, hstart.2, hqlo, hqhi, hs⟩
      · have hperm : labels.Perm (q :: labels.erase q) := List.perm_cons_erase hq
        have he := (hperm.map f).sum_eq
        simp only [List.map_cons, List.sum_cons] at he
        have hlenq := List.length_erase_add_one hq
        have hEc := List.Perm.countP_eq E hperm
        simp only [List.countP_cons] at hEc
        have hNc : labels.countP (fun x => decide (f x ≤ -Q)) =
            (labels.erase q).countP (fun x => decide (f x ≤ -Q)) := by
          simpa [List.countP_cons, hqN] using
            (List.Perm.countP_eq (fun x => decide (f x ≤ -Q)) hperm)
        have hgap' : (labels.erase q).countP E ≠ 0 →
            (labels.erase q).countP E + 1 ≤
              (labels.erase q).countP (fun x => decide (f x ≤ -Q)) := by
          intro _
          split at hEc <;> omega
        obtain ⟨word, hw, hs⟩ := ih (labels.erase q) (b + f q)
          (by omega) ⟨hqlo, hqhi⟩ (by constructor <;> omega)
          (fun x hx => hEbound x (List.mem_of_mem_erase hx))
          (fun x hx y hy => hcompatible x (List.mem_of_mem_erase hx)
            y (List.mem_of_mem_erase hy)) hgap'
        exact ⟨q :: word, (hw.cons q).trans hperm.symm,
          hstart.1, hstart.2, hs⟩

/-- Let `C = 2 * Q - 1`. Mark a collection of positive physical occurrences
by `E`, bounding just those values by `Q - 1`. Assume every unmarked positive
is compatible with every negative. If there are marked occurrences, require
one more actual negative LARGE occurrence than marked occurrences; if there
are none, impose no counting condition. Then all occurrences can be ordered
between the given legal endpoints. No distinctness of labels or values is
needed, and no occurrence is discarded.

`SourceWidth.inStrip_prefix` supplies the strip inequalities for every natural
take, including empty and overlong takes. -/
theorem exists_order_between {α : Type*} (f : α → ℤ) (E : α → Bool)
    (labels : List α) (Q b e : ℤ)
    (hQ : 2 ≤ Q)
    (hstart : 0 ≤ b ∧ b ≤ 2 * Q - 1)
    (hend : 0 ≤ e ∧ e ≤ 2 * Q - 1)
    (hsum : b + (labels.map f).sum = e)
    (hEbound : ∀ x ∈ labels, E x = true → 0 < f x ∧ f x ≤ Q - 1)
    (hcompatible : ∀ p ∈ labels, ∀ n ∈ labels,
      E p = false → 0 < f p → f n < 0 → f p - f n ≤ 2 * Q - 1)
    (hsurplus : labels.countP E ≠ 0 → labels.countP E + 1 ≤
      labels.countP (fun x => decide (f x ≤ -Q))) :
    ∃ word : List α, word.Perm labels ∧ InStrip f (2 * Q - 1) b word ∧
      b + (word.map f).sum = e := by
  obtain ⟨word, hw, hs⟩ := complete_between f E Q hQ labels.length labels b
    (le_refl _) hstart (by simpa only [hsum] using hend)
    hEbound hcompatible hsurplus
  refine ⟨word, hw, hs, ?_⟩
  rw [(hw.map f).sum_eq]
  exact hsum

end D5.S3.Combinatorics.Circle.CountSurplusOrdering
