/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.finite_certificate
   digest: Hardin's recurrence for canonical six-column zero-defect arrays. -/

/-
admission_basis: open-problem-resolution (#32721; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA203981Strip.result)
a: proof_shape=bind-only; consumers=counting_bridge, result
scale_count_of_bonds: proof_shape=content; consumers=scale_count
scale_count: proof_shape=content; consumers=HardinA229508Strip.counting_bridge, HardinA229683Strip.counting_bridge, counting_bridge
counting_bridge: proof_shape=content; consumers=result
result: proof_shape=content; consumers=none (external open-problem-resolution #32721)
-/

import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Init.Core
import Init.Data.Fin.Lemmas
import Init.Data.Function
import Init.Data.Int.Basic
import Init.Data.List.OfFn
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Prelude
import Init.PropLemmas
import Init.SimpLemmas
import Init.Tactics
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
import Init.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Monoid
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.SetTheory.Cardinal.Finite

/-! Literal canonical counts and the six-column diagonal-strip recurrence. -/

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981Strip

open HardinA203981StripData
open HardinA203981StripCertificate (coeff finite_certificate)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn (betw)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)
set_option backward.isDefEq.respectTransparency false

/-- The literal row-major canonical count with n+1 rows and zero defects. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Fin (n + 1) × Fin 6 → Fin 3 =>
    defects ∅ (betw 6) (List.ofFn fun i j => f (i, j)) = 0 ∧
    (@Canonical (Fin (n + 1) × Fin 6)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f)).card

/-- Every nonconstant orbit has six labellings. At the constant-array budget
the constant orbit has three, so the labelled total needs a correction of three. -/
theorem scale_count_of_bonds (w m d : ℕ)
    (H V : Finset (Fin (w + 1) × Fin (w + 1))) :
    literalCount (q := 3) H V d (m + 1) + (if d = H.card + m * (V.card + H.card) then 3 else 0) =
      6 * (Finset.univ.filter fun f : Fin (m + 1) × Fin (w + 1) → Fin 3 =>
        defects H V (List.ofFn fun i j => f (i, j)) = d ∧
        (@Canonical (Fin (m + 1) × Fin (w + 1))
          (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f)).card := by
  classical
  let C := Fin (m + 1) × Fin (w + 1)
  let order : LinearOrder C := LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective
  let z : C := (0, 0)
  let s (f : C → Fin 3) := defects H V (List.ofFn fun i j => f (i, j)) = d
  let D (f : C → Fin 3) := ∃ x y, f x ≠ f y
  let L := Finset.univ.filter s
  let A := Finset.univ.filter fun f => s f ∧ @Canonical C order.toLT 3 f
  rw [show literalCount (q := 3) H V d (m + 1) = L.card by
    unfold literalCount L
    congr 1]
  have hA : (Finset.univ.filter fun f : Fin (m + 1) × Fin (w + 1) → Fin 3 =>
      defects H V (List.ofFn fun i j => f (i, j)) = d ∧
      (@Canonical (Fin (m + 1) × Fin (w + 1))
        (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f)) = A := by
    ext f
    simp only [A, Finset.mem_filter]
    rfl
  rw [hA]
  have inv : ∀ e : Equiv.Perm (Fin 3), ∀ f, (s (e ∘ f) ∧ D (e ∘ f)) ↔ s f ∧ D f := by
    intro e f
    have h : s (e ∘ f) ↔ s f := by
      change defects H V _ = d ↔ _
      rw [show (List.ofFn fun i j => (e ∘ f) (i, j)) =
        (List.ofFn fun i j => f (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
        relabel_defects]
    exact and_congr h (by simp [D, e.injective.ne_iff])
  have hn := @canonical_pattern_card C inferInstance order
    (fun f => s f ∧ D f) inv (fun f hf => hf.2)
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at hn
  have lsplit : (L.filter D).card + (L.filter fun f => ¬ D f).card = L.card :=
    Finset.card_filter_add_card_filter_not D
  have asplit : (A.filter D).card + (A.filter fun f => ¬ D f).card = A.card :=
    Finset.card_filter_add_card_filter_not D
  have hnc : (L.filter D).card = 6 * (A.filter D).card := by
    simpa only [L, A, Finset.filter_filter, and_assoc, and_left_comm, and_comm] using hn
  have const (f : C → Fin 3) (h : ¬ D f) : f = fun _ => f z := by
    funext x
    by_contra hne
    exact h ⟨x,z,hne⟩
  have cost (c : Fin 3) : s (fun _ => c) ↔ d = H.card + m * (V.card + H.card) := by
    change defects H V _ = d ↔ _
    simp only [List.ofFn_const]
    rw [constant_defects]
    exact eq_comm
  have can (c : Fin 3) : @Canonical C order.toLT 3 (fun _ : C => c) ↔ c = 0 := by
    constructor
    · intro h
      by_contra hc
      obtain ⟨_, _, he⟩ := h z 0 (Fin.pos_iff_ne_zero.mpr hc)
      exact hc he
    · rintro rfl _ t ht
      change t < (0 : Fin 3) at ht
      omega
  by_cases hd : d = H.card + m * (V.card + H.card)
  · have lconst : L.filter (fun f => ¬ D f) =
        Finset.univ.image (fun c : Fin 3 => fun _ : C => c) := by
      ext f
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨_, h⟩
        exact ⟨f z, (const f h).symm⟩
      · rintro ⟨c, rfl⟩
        exact ⟨(cost c).2 hd, by simp [D]⟩
    have aconst : A.filter (fun f => ¬ D f) = {fun _ : C => (0 : Fin 3)} := by
      ext f
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨_, hcan⟩, hf⟩
        have he := const f hf
        rw [he] at hcan ⊢
        rw [(can _).1 hcan]
      · rintro rfl
        exact ⟨⟨(cost 0).2 hd, (can 0).2 rfl⟩, by simp [D]⟩
    have hinj : Function.Injective (fun c : Fin 3 => fun _ : C => c) :=
      fun _ _ h => congrFun h z
    rw [lconst, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at lsplit
    rw [aconst, Finset.card_singleton] at asplit
    simp only [if_pos hd]
    omega
  · have emptyL : L.filter (fun f => ¬ D f) = ∅ := by
      ext f
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨hf, hc⟩
      rw [const f hc] at hf
      exact hd ((cost _).1 hf)
    have emptyA : A.filter (fun f => ¬ D f) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro f hf
      have hf' : f ∈ L.filter (fun f => ¬ D f) := by
        simp only [L, A, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
        exact ⟨hf.1.1, hf.2⟩
      simpa [emptyL] using hf'
    simp only [emptyL, emptyA, Finset.card_empty, add_zero] at lsplit asplit
    simpa only [if_neg hd, add_zero, ← lsplit, ← asplit] using hnc

/-- The six-column diagonal and antidiagonal strip has ten bonds per row pair. -/
theorem scale_count (m d : ℕ) :
    literalCount (q := 3) ∅ (betw 6) d (m + 1) + (if d = m * 10 then 3 else 0) =
      6 * (Finset.univ.filter fun f : Fin (m + 1) × Fin 6 → Fin 3 =>
        defects ∅ (betw 6) (List.ofFn fun i j => f (i, j)) = d ∧
        (@Canonical (Fin (m + 1) × Fin 6)
          (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f)).card := by
  have bonds : (betw 6).card = 10 := by
    rw [between_six]
    decide +kernel
  simpa only [Finset.card_empty, bonds, add_zero, zero_add] using
    scale_count_of_bonds 5 m d ∅ (betw 6)

attribute [local irreducible] a

/-- The labelled zero-budget transfer has a correction of three for a single row. -/
theorem counting_bridge (m : ℕ) :
    dotProduct initial ((T ^ m).mulVec (1 : Fin 15 → ℤ)) +
      (if m = 0 then 3 else 0) = 6 * (a m : ℤ) := by
  have labelled : (literalCount (q := 3) ∅ (betw 6) 0 (m + 1) : ℤ) =
      dotProduct initial ((T ^ m).mulVec (1 : Fin 15 → ℤ)) := by
    apply lumped_count ∅ (betw 6) id (bondDefects (betw 6))
      (fun _ d => d = 0) (fun p _ => boundary p) T initial 1 0 (fun _ _ => rfl)
    · intro p d hd
      subst d
      rfl
    · intro p d hd r hr
      subst d
      exact Nat.zero_sub _
    · intro p d hd j
      subst d
      simpa only [bondDefects, Finset.filter_empty, Finset.card_empty, Nat.add_zero,
        Nat.le_zero, id_eq] using HardinA203981StripCertificate.counts p j
    · intro r hr
      rfl
    · intro j
      simpa only [bondDefects, Finset.filter_empty, Finset.card_empty, Nat.le_refl,
        true_and, id_eq] using HardinA203981StripCertificate.initial_counts j
  have h : literalCount (q := 3) ∅ (betw 6) 0 (m + 1) +
      (if m = 0 then 3 else 0) = 6 * a m := by
    unfold a
    have same : (0 = m * 10) ↔ m = 0 := by omega
    simpa only [same] using scale_count m 0
  have cast := congrArg (fun k : ℕ => (k : ℤ)) h
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ite, Nat.cast_zero, labelled]
    using cast

/-- The order-six recurrence at every index at least seven. -/
theorem result (n : ℕ) :
    (a (n + 7) : ℤ) = 25 * a (n + 6) - 45 * a (n + 5) - 963 * a (n + 4) + 2025 * a (n + 3) + 3645 * a (n + 2) - 6561 * a (n + 1) := by
  have h := forward_shift T initial (1 : Fin 15 → ℤ) 6 1 coeff finite_certificate n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    coeff, Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.reduceAdd, Nat.add_zero,
    Nat.add_assoc] at h
  have bridge (m : ℕ) (hm : 1 ≤ m) :
      dotProduct initial ((T ^ m).mulVec (1 : Fin 15 → ℤ)) = 6 * (a m : ℤ) := by
    simpa only [if_neg (Nat.ne_of_gt hm), add_zero] using counting_bridge m
  rw [bridge _ (Nat.succ_pos _), bridge _ (Nat.succ_pos _),
    bridge _ (Nat.succ_pos _), bridge _ (Nat.succ_pos _),
    bridge _ (Nat.succ_pos _), bridge _ (Nat.succ_pos _),
    bridge _ (Nat.succ_pos _)] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981Strip
