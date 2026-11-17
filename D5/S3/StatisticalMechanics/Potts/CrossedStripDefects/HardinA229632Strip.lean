/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229632Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229632Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229632Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229632Strip.finite_certificate
   digest: Exact HDA defect transfer and Hardin's registered recurrence. -/

/-
admission_basis: open-problem-resolution (#31121; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229632Strip.result)
Row: proof_shape=bind-only; consumers=result
horizontal: proof_shape=bind-only; consumers=result
between: proof_shape=bind-only; consumers=result
Valid: proof_shape=bind-only; consumers=result
decidableValid: proof_shape=bind-only; consumers=result
cl: proof_shape=bind-only; consumers=result
T: proof_shape=bind-only; consumers=result
initial: proof_shape=bind-only; consumers=result
terminal: proof_shape=bind-only; consumers=result
W: proof_shape=bind-only; consumers=result
finite_certificate: proof_shape=bind-only; consumers=result
a: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31121)
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229529Strip
import Mathlib.Data.Matrix.Block
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229581Strip

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229632Strip
open DefectTransfer (bondDefects defects literalCount lumped_count forward forward_shift)
open HardinA233177Canonical (Canonical canonical_pattern_card)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev Row := Fin 3 → Fin 3
private def horizontal : Finset (Fin 3 × Fin 3) := HardinA229581Strip.horizontal
private def between : Finset (Fin 3 × Fin 3) :=
  HardinA229529Strip.between
private def Valid (p : Row) (d : ℕ) : Prop :=
  d ≤ 2 ∧ bondDefects horizontal p p ≤ 2 - d
private instance decidableValid (p : Row) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (_ ∧ _))
private def cl (p : Row) (d : ℕ) : Fin 9 :=
  if 0 < d then (HardinA229529Strip.cl p (d - 1)).castAdd 4 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinThinGraphTransport.boundaryClass p = true then 5 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinThinGraphTransport.boundaryClass p = false then 6 else
  if d = 0 ∧ ((p 0 = p 1 ∧ p 0 = p 2 ∧ p 1 = p 2) ∨ (p 0 = p 1 ∧ p 0 = p 2 ∧ p 1 = p 2)) then 7 else
  8
private def T : Matrix (Fin 9) (Fin 9) ℤ :=
  Matrix.reindex (finSumFinEquiv : Fin 5 ⊕ Fin 4 ≃ Fin 9)
    (finSumFinEquiv : Fin 5 ⊕ Fin 4 ≃ Fin 9)
    (Matrix.fromBlocks HardinA229529Strip.T
      (![![2, 0, 1, 6],
        ![0, 4, 0, 8],
        ![0, 2, 0, 2],
        ![2, 0, 0, 0],
        ![3, 4, 0, 2]])
      (0)
      (![![(HardinThinGraphTransport.K true true : ℤ), (HardinThinGraphTransport.K true false : ℤ), 0, 0],
        ![(HardinThinGraphTransport.K false true : ℤ), (HardinThinGraphTransport.K false false : ℤ), 0, 0],
        ![2, 0, 0, 0],
        ![1, 0, 0, 0]]))
private def initial : Fin 9 → ℤ :=
  Fin.append HardinA229529Strip.initial (![0, 0, 3, 0])
def terminal : Fin 9 → ℤ := ![0, 0, 0, 0, 0, 1, 1, 1, 1]
private def W : Fin 8 → Fin 9 → ℤ :=
  Fin.append (fun i => Fin.append (HardinA229529Strip.W i)
      ((![![0, 0, 3, 0],
        ![54, 72, 6, 108],
        ![546, 444, 30, 444],
        ![3750, 2964, 138, 2124],
        ![23370, 18516, 630, 10284],
        ![138174, 109764, 2874, 49692]]) i))
    (![![59802, 46692, 182604, 148932, 26220, 788322, 627156, 13110, 239388],
        ![272790, 212988, 965280, 782676, 119604, 4381014, 3487812, 59802, 1149996]])

/-- The literal row-major canonical filtered array count. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin n × Fin 3 → Fin 3 =>
    @Canonical (Fin n × Fin 3)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin n × Fin 3 → Fin 3 =>
    defects horizontal between (List.ofFn fun i j => A (i, j)) = 2 ∧
    (@Canonical (Fin n × Fin 3)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

private theorem finite_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ r : Row,
      bondDefects between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects between p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ s : Fin 9,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 2 →
      Valid r (2 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 9, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl r (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 7, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 7 = ∑ j : Fin 6, (![-8, 60, -162, 185, -81, 15] j : ℤ) • W ⟨1 + j.val, by omega⟩ := by
  refine ⟨by decide +kernel, (by
    intro p d hp r hr
    dsimp only [Valid] at hp ⊢
    omega), ?_, by decide +kernel, ?_, ?_,
    by decide +kernel⟩
  · have valid_cut : ∀ p (d : Fin 3), Valid p d.val → 0 < d.val →
        HardinA229529Strip.Valid p (d.val - 1) := by decide +kernel
    have active_cut : ∀ (p r : Row) (d : Fin 3) (j : Fin 5),
        Valid p d.val → 0 < d.val →
        ((bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
          cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = j.castAdd 4) ↔
          bondDefects HardinA229529Strip.between p r + bondDefects horizontal r r ≤ d.val - 1 ∧
            HardinA229529Strip.cl r (d.val - 1 - (bondDefects HardinA229529Strip.between p r + bondDefects horizontal r r)) = j) := by
      decide +kernel
    have active_table : ∀ p (d : Fin 3) (j : Fin 5),
        Valid p d.val → 0 < d.val →
        HardinA229529Strip.T (HardinA229529Strip.cl p (d.val - 1)) j =
          T (cl p d.val) (j.castAdd 4) := by decide +kernel
    have zero_cut : ∀ (p r : Row) (d : Fin 3) (s : Fin 9)
        (hz : HardinThinGraphTransport.proper p ∧ d.val = 0 ∧ 5 ≤ s.val ∧ s.val < 7),
        (bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
          cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s) ↔
          HardinThinGraphTransport.proper r ∧ HardinThinGraphTransport.compatible true p r ∧
          HardinThinGraphTransport.boundaryClass r = decide (s.val = 5) := by decide +kernel
    have zero_table : ∀ p (d : Fin 3) (s : Fin 9)
        (hz : HardinThinGraphTransport.proper p ∧ d.val = 0 ∧ 5 ≤ s.val ∧ s.val < 7),
        (HardinThinGraphTransport.K (HardinThinGraphTransport.boundaryClass p)
          (decide (s.val = 5)) : ℤ) = T (cl p d.val) s := by decide +kernel
    have remaining : ∀ p (d : Fin 3), Valid p d.val → ∀ s : Fin 9,
        ¬ (0 < d.val ∧ s.val < 5) →
        ¬ (HardinThinGraphTransport.proper p ∧ d.val = 0 ∧ 5 ≤ s.val ∧ s.val < 7) →
        (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
          cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
          then (1 : ℤ) else 0) = T (cl p d.val) s := by
      intro p
      generalize h0 : p 0 = c0
      generalize h1 : p 1 = c1
      fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert
    intro p d hp s
    by_cases ha : 0 < d.val ∧ s.val < 5
    · let j : Fin 5 := ⟨s.val, ha.2⟩
      have he : s = j.castAdd 4 := rfl
      rw [he]
      simp_rw [active_cut p _ d j hp ha.1]
      exact (HardinA229529Strip.finite_certificate.2.2.1 p
        ⟨d.val - 1, by omega⟩ (valid_cut p d hp ha.1) j).trans
          (active_table p d j hp ha.1)
    · by_cases hz : HardinThinGraphTransport.proper p ∧ d.val = 0 ∧ 5 ≤ s.val ∧ s.val < 7
      · simp_rw [zero_cut p _ d s hz]
        have h := HardinThinGraphTransport.transition_counts.2 true p hz.1
          (decide (s.val = 5))
        have cast : (∑ r : Row, if HardinThinGraphTransport.proper r ∧
            HardinThinGraphTransport.compatible true p r ∧
            HardinThinGraphTransport.boundaryClass r = decide (s.val = 5)
            then (1 : ℤ) else 0) =
            (HardinThinGraphTransport.K (HardinThinGraphTransport.boundaryClass p)
              (decide (s.val = 5)) : ℤ) := by exact_mod_cast h
        exact cast.trans (zero_table p d s hz)
      · exact remaining p d hp s ha hz
  · have initial_cut : ∀ (r : Row) (j : Fin 5),
        (bondDefects horizontal r r ≤ 2 ∧
          cl r (2 - bondDefects horizontal r r) = j.castAdd 4) ↔
          bondDefects horizontal r r ≤ 1 ∧
            HardinA229529Strip.cl r (1 - bondDefects horizontal r r) = j := by decide +kernel
    have initial_table : ∀ j : Fin 5,
        HardinA229529Strip.initial j = initial (j.castAdd 4) := by decide +kernel
    have remaining : ∀ s : Fin 9, 5 ≤ s.val →
        (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
          cl r (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s := by
      decide +kernel
    intro s
    by_cases hs : s.val < 5
    · let j : Fin 5 := ⟨s.val, hs⟩
      have he : s = j.castAdd 4 := rfl
      rw [he]
      simp_rw [initial_cut _ j]
      exact (HardinA229529Strip.finite_certificate.2.2.2.2.1 j).trans (initial_table j)
    · exact remaining s (by omega)
  · have zero_cut : ∀ j : Fin 5,
        W 0 (j.castAdd 4) = HardinA229529Strip.W 0 j ∧
        initial (j.castAdd 4) = HardinA229529Strip.initial j := by decide +kernel
    have zero_remaining : ∀ s : Fin 9, 5 ≤ s.val →
        W 0 s = initial s := by decide +kernel
    have step_cut : ∀ (i : Fin 5) (j : Fin 5),
        W (i.succ.castAdd 2) (j.castAdd 4) = HardinA229529Strip.W i.succ j ∧
        Matrix.vecMul (W (i.castSucc.castAdd 2)) T (j.castAdd 4) =
          Matrix.vecMul (HardinA229529Strip.W i.castSucc) HardinA229529Strip.T j := by decide +kernel
    have step_remaining : ∀ (i : Fin 7) (s : Fin 9),
        ¬ (i.val < 5 ∧ s.val < 5) →
        W i.succ s = Matrix.vecMul (W i.castSucc) T s := by decide +kernel
    constructor
    · funext s
      by_cases hs : s.val < 5
      · let j : Fin 5 := ⟨s.val, hs⟩
        have he : s = j.castAdd 4 := rfl
        rw [he, (zero_cut j).1, (zero_cut j).2]
        exact congrFun HardinA229529Strip.finite_certificate.2.2.2.2.2.1.1 j
      · exact zero_remaining s (by omega)
    · intro i
      funext s
      by_cases hs : i.val < 5 ∧ s.val < 5
      · let k : Fin 5 := ⟨i.val, hs.1⟩
        let j : Fin 5 := ⟨s.val, hs.2⟩
        have he : s = j.castAdd 4 := rfl
        have h0 : i.castSucc = k.castSucc.castAdd 2 := rfl
        have h1 : i.succ = k.succ.castAdd 2 := rfl
        rw [he, h0, h1, (step_cut k j).1, (step_cut k j).2]
        exact congrFun (HardinA229529Strip.finite_certificate.2.2.2.2.2.1.2 k) j
      · exact step_remaining i s hs

attribute [local irreducible] a

/-- The registered recurrence at every index at least 8. -/
theorem result (n : ℕ) :
    (a (n + 8) : ℤ) = 15 * a (n + 7) - 81 * a (n + 6) + 185 * a (n + 5) - 162 * a (n + 4) + 60 * a (n + 3) - 8 * a (n + 2) := by
  have labelled (m : ℕ) :
      (literalCount (q := 3) horizontal between 2 (m + 1) : ℤ) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal between id (bondDefects between) Valid cl T initial terminal 2
      (fun _ _ => rfl)
    · intro p d h
      exact finite_certificate.1 p ⟨d, by have := h.1; omega⟩ h
    · intro p d h r hr
      exact finite_certificate.2.1 p ⟨d, by have := h.1; omega⟩ h r hr
    · intro p d h s
      exact finite_certificate.2.2.1 p ⟨d, by have := h.1; omega⟩ h s
    · exact finite_certificate.2.2.2.1
    · exact finite_certificate.2.2.2.2.1
  have tab (i : Fin 8) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (finite_certificate.2.2.2.2.2.1.2 i).symm
  have poly : forward T initial (1 + 6) =
      ∑ j : Fin 6, (![-8, 60, -162, 185, -81, 15] j : ℤ) • forward T initial (1 + j.val) := by
    rw [tab ⟨7, by omega⟩]
    simp_rw [show ∀ j : Fin 6, forward T initial (1 + j.val) = W ⟨1 + j.val, by omega⟩
      from fun j => tab ⟨1 + j.val, by omega⟩]
    exact finite_certificate.2.2.2.2.2.2
  have scale (m : ℕ) (hm : 1 ≤ m) :
      literalCount (q := 3) horizontal between 2 (m + 1) = 6 * a (m + 1) := by
    classical
    let S : (Fin (m + 1) × Fin 3 → Fin 3) → Prop := fun A =>
      defects horizontal between (List.ofFn fun i j => A (i, j)) = 2
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
      intro e A
      change defects horizontal between _ = 2 ↔ _
      rw [show (List.ofFn fun i j => (e ∘ A) (i, j)) =
        (List.ofFn fun i j => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
        DefectTransfer.relabel_defects]
    have nonconstant : ∀ A, S A → ∃ x y, A x ≠ A y := by
      intro A h
      by_contra he
      push_neg at he
      have const : A = fun _ => A (0, 0) := funext fun x => he x (0, 0)
      change defects horizontal between _ = 2 at h
      rw [const] at h
      simp only [List.ofFn_const] at h
      rw [DefectTransfer.constant_defects] at h
      have cards : horizontal.card = 2 ∧ between.card = 4 := by decide +kernel
      rw [cards.1, cards.2] at h
      omega
    have orbit := @canonical_pattern_card (Fin (m + 1) × Fin 3) inferInstance
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) S invariant nonconstant
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit
    unfold literalCount a
    convert orbit using 1
    apply congrArg (fun x : ℕ => 6 * x)
    apply congrArg Finset.card
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
  have bridge (m : ℕ) (hm : 1 ≤ m) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← labelled, scale m hm]
    push_cast
    rfl
  have h := forward_shift T initial terminal 6 1 ![-8, 60, -162, 185, -81, 15] poly n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h0 := bridge (n + 1) (by omega)
  have h1 := bridge (n + 2) (by omega)
  have h2 := bridge (n + 3) (by omega)
  have h3 := bridge (n + 4) (by omega)
  have h4 := bridge (n + 5) (by omega)
  have h5 := bridge (n + 6) (by omega)
  have h6 := bridge (n + 7) (by omega)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h0 h1 h2 h3 h4 h5 h6
  rw [h0, h1, h2, h3, h4, h5, h6] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229632Strip
