/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.finite_certificate
   digest: Exact HDA defect transfer and Hardin's registered recurrence. -/

/-
admission_basis: open-problem-resolution (#31121; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229530Strip.result)
Row: proof_shape=bind-only; consumers=result
horizontal: proof_shape=bind-only; consumers=result
between: proof_shape=bind-only; consumers=result, HardinA229633Strip.finite_certificate
Valid: proof_shape=bind-only; consumers=result, HardinA229633Strip.finite_certificate
decidableValid: proof_shape=bind-only; consumers=result, HardinA229633Strip.finite_certificate
cl: proof_shape=bind-only; consumers=result, HardinA229633Strip.finite_certificate
T: proof_shape=bind-only; consumers=result, HardinA229633Strip.finite_certificate
initial: proof_shape=bind-only; consumers=result, HardinA229633Strip.finite_certificate
terminal: proof_shape=bind-only; consumers=result
W: proof_shape=bind-only; consumers=result, HardinA229633Strip.finite_certificate
raw_successors: proof_shape=bind-only; consumers=finite_certificate, HardinA229633Strip.finite_certificate
finite_certificate: proof_shape=bind-only; consumers=result, HardinA229633Strip.finite_certificate
a: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31121)
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import Mathlib.Data.Matrix.Block
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinSourceContinuations
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229582Strip

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229530Strip
open DefectTransfer (bondDefects defects literalCount lumped_count forward forward_shift)
open HardinA233177Canonical (Canonical canonical_pattern_card)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev Row := Fin 4 → Fin 3
private def horizontal : Finset (Fin 4 × Fin 4) := HardinA229582Strip.horizontal
def between : Finset (Fin 4 × Fin 4) :=
  HardinA229582Strip.antidiagonal ∪ HardinA229582Strip.antidiagonal.image Prod.swap
def Valid (p : Row) (d : ℕ) : Prop :=
  d ≤ 1 ∧ bondDefects horizontal p p ≤ 1 - d
private instance decidableValid (p : Row) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (_ ∧ _))
def cl (p : Row) (d : ℕ) : Fin 10 :=
  if d = 1 ∧ bondDefects horizontal p p = 0 ∧ HardinSourceContinuations.sourceClass (true, true) p = 1 then 0 else
  if d = 1 ∧ bondDefects horizontal p p = 0 ∧ HardinSourceContinuations.sourceClass (true, true) p = 2 then 1 else
  if d = 1 ∧ bondDefects horizontal p p = 0 ∧ HardinSourceContinuations.sourceClass (true, true) p = 3 then 2 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinSourceContinuations.sourceClass (true, true) p = 1 then 3 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinSourceContinuations.sourceClass (true, true) p = 2 then 4 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinSourceContinuations.sourceClass (true, true) p = 3 then 5 else
  if d = 0 ∧ ((p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3) ∨ (p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 = p 3)) then 6 else
  if d = 0 ∧ ((p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3) ∨ (p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 = p 3)) then 7 else
  if d = 0 ∧ ((p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3) ∨ (p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3)) then 8 else
  9
def T : Matrix (Fin 10) (Fin 10) ℤ :=
  ![![(HardinSourceContinuations.M 1 1 / 16), (HardinSourceContinuations.M 1 2 / 16), (HardinSourceContinuations.M 1 3 / 16), 0, 2, 2, 2, 2, 0, 1],
    ![(HardinSourceContinuations.M 2 1 / 16), (HardinSourceContinuations.M 2 2 / 16), (HardinSourceContinuations.M 2 3 / 16), 2, 0, 2, 0, 0, 0, 0],
    ![(HardinSourceContinuations.M 3 1 / 16), (HardinSourceContinuations.M 3 2 / 16), (HardinSourceContinuations.M 3 3 / 16), 1, 1, 3, 1, 1, 0, 0],
    ![0, 0, 0, (HardinSourceContinuations.M 1 1 / 16), (HardinSourceContinuations.M 1 2 / 16), (HardinSourceContinuations.M 1 3 / 16), 0, 0, 0, 0],
    ![0, 0, 0, (HardinSourceContinuations.M 2 1 / 16), (HardinSourceContinuations.M 2 2 / 16), (HardinSourceContinuations.M 2 3 / 16), 0, 0, 0, 0],
    ![0, 0, 0, (HardinSourceContinuations.M 3 1 / 16), (HardinSourceContinuations.M 3 2 / 16), (HardinSourceContinuations.M 3 3 / 16), 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]]
def initial : Fin 10 → ℤ := ![6, 6, 12, 0, 0, 0, 12, 12, 6, 6]
private def terminal : Fin 10 → ℤ := ![0, 0, 0, 1, 1, 1, 1, 1, 1, 1]
def W : Fin 7 → Fin 10 → ℤ :=
  ![![6, 6, 12, 0, 0, 0, 12, 12, 6, 6],
    ![48, 24, 72, 54, 24, 84, 24, 24, 0, 6],
    ![312, 144, 456, 528, 330, 924, 168, 168, 0, 48],
    ![1992, 912, 2904, 4890, 2862, 8160, 1080, 1080, 0, 312],
    ![12696, 5808, 18504, 41052, 22800, 66444, 6888, 6888, 0, 1992],
    ![80904, 37008, 117912, 324732, 174192, 515436, 43896, 43896, 0, 12696],
    ![515544, 235824, 751368, 2471676, 1294080, 3870972, 279720, 279720, 0, 80904]]

/-- The literal row-major canonical filtered array count. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin n × Fin 4 → Fin 3 =>
    @Canonical (Fin n × Fin 4)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin n × Fin 4 → Fin 3 =>
    defects horizontal between (List.ofFn fun i j => A (i, j)) = 1 ∧
    (@Canonical (Fin n × Fin 4)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

open HardinA233255LiteralBridge (rowWeight rowFinish scanner_fibres)
open HardinA233175PairStrip (good finish)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

theorem raw_successors (p : Fin 4 → Fin 3) (hp : HardinThinGraphTransport.proper p) (j : Fin 4) :
    16 * (∑ q : Fin 4 → Fin 3,
      if HardinThinGraphTransport.proper q ∧ HardinThinGraphTransport.compatible true p q ∧
        HardinSourceContinuations.sourceClass (true, true) q = j then (1 : ℤ) else 0) =
      HardinSourceContinuations.M (HardinSourceContinuations.sourceClass (true, true) p) j := by
  have ha : HardinSourceContinuations.admissible (true, true) p := ⟨rfl, hp, by simp⟩
  have h := HardinSourceContinuations.four_class_certificate.2.2.1 (true, true) p ha j
  let H := fun s (q : Fin 4 → Fin 3) =>
    if HardinThinGraphTransport.proper q ∧ HardinThinGraphTransport.compatible true p q ∧
      HardinSourceContinuations.sourceClass s q = j then (1 : ℤ) else 0
  have hs : ∀ q : Fin 4 → Fin 3,
      rowWeight (true, true) q = 16 ∧ rowFinish (true, true) q = (true, true) := by
    decide +kernel
  change (∑ c : Fin 4 → Fin 6, if HardinThinGraphTransport.proper (fun i => beta (c i)) ∧
    HardinThinGraphTransport.compatible true p (fun i => beta (c i)) ∧ good (true, true) c ∧
      HardinSourceContinuations.sourceClass (finish (true, true) c) (fun i => beta (c i)) = j
    then (1 : ℤ) else 0) = _ at h
  have he : (∑ c : Fin 4 → Fin 6, if good (true, true) c then
      H (finish (true, true) c) (fun i => beta (c i)) else 0) =
      HardinSourceContinuations.M (HardinSourceContinuations.sourceClass (true, true) p) j := by
    convert h using 1
    apply Finset.sum_congr rfl
    intro c _
    dsimp [H]
    by_cases hc : good (true, true) c <;> simp [hc]
  rw [scanner_fibres] at he
  simp_rw [(hs _).1, (hs _).2] at he
  simpa only [← Finset.mul_sum] using he

theorem finite_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      bondDefects between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects between p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 10,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid r (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 10, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl r (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 6, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 6 = ∑ j : Fin 4, (![-16, 56, -57, 14] j : ℤ) • W ⟨2 + j.val, by omega⟩ := by
  refine ⟨by decide +kernel, (by
    intro p d hp r hr
    dsimp only [Valid] at hp ⊢
    omega), ?_, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩
  have cut : ∀ (p r : Row) (d : Fin 2) (s : Fin 10),
      HardinThinGraphTransport.proper p ∧
        ((d.val = 1 ∧ s.val < 3) ∨ (d.val = 0 ∧ 3 ≤ s.val ∧ s.val < 6)) →
      ((bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s) ↔
        HardinThinGraphTransport.proper r ∧ HardinThinGraphTransport.compatible true p r ∧
          HardinSourceContinuations.sourceClass (true, true) r =
            ⟨s.val % 3 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 3); omega⟩) := by
    intro p
    generalize h0 : p 0 = c0
    generalize h1 : p 1 = c1
    fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert
  have table : ∀ p (d : Fin 2) (s : Fin 10),
      HardinThinGraphTransport.proper p ∧
        ((d.val = 1 ∧ s.val < 3) ∨ (d.val = 0 ∧ 3 ≤ s.val ∧ s.val < 6)) →
      HardinSourceContinuations.M (HardinSourceContinuations.sourceClass (true, true) p)
        ⟨s.val % 3 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 3); omega⟩ / 16 =
          T (cl p d.val) s := by decide +kernel
  have remaining : ∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 10,
      ¬ (HardinThinGraphTransport.proper p ∧
        ((d.val = 1 ∧ s.val < 3) ∨ (d.val = 0 ∧ 3 ≤ s.val ∧ s.val < 6))) →
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s := by
    intro p
    generalize h0 : p 0 = c0
    generalize h1 : p 1 = c1
    fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert
  intro p d hp s
  by_cases hz : HardinThinGraphTransport.proper p ∧
      ((d.val = 1 ∧ s.val < 3) ∨ (d.val = 0 ∧ 3 ≤ s.val ∧ s.val < 6))
  · simp_rw [cut p _ d s hz]
    have h := raw_successors p hz.1
      ⟨s.val % 3 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 3); omega⟩
    have hd : (∑ r : Row, if HardinThinGraphTransport.proper r ∧
        HardinThinGraphTransport.compatible true p r ∧
        HardinSourceContinuations.sourceClass (true, true) r =
          ⟨s.val % 3 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 3); omega⟩
        then (1 : ℤ) else 0) =
        HardinSourceContinuations.M (HardinSourceContinuations.sourceClass (true, true) p)
          ⟨s.val % 3 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 3); omega⟩ / 16 := by
      exact Int.eq_ediv_of_mul_eq_right (by decide) h
    exact hd.trans (table p d s hz)
  · exact remaining p d hp s hz

attribute [local irreducible] a

/-- The registered recurrence at every index at least 6. -/
theorem result (n : ℕ) :
    (a (n + 6) : ℤ) = 14 * a (n + 5) - 57 * a (n + 4) + 56 * a (n + 3) - 16 * a (n + 2) := by
  have labelled (m : ℕ) :
      (literalCount (q := 3) horizontal between 1 (m + 1) : ℤ) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal between id (bondDefects between) Valid cl T initial terminal 1
      (fun _ _ => rfl)
    · intro p d h
      exact finite_certificate.1 p ⟨d, by have := h.1; omega⟩ h
    · intro p d h r hr
      exact finite_certificate.2.1 p ⟨d, by have := h.1; omega⟩ h r hr
    · intro p d h s
      exact finite_certificate.2.2.1 p ⟨d, by have := h.1; omega⟩ h s
    · exact finite_certificate.2.2.2.1
    · exact finite_certificate.2.2.2.2.1
  have tab (i : Fin 7) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (finite_certificate.2.2.2.2.2.1.2 i).symm
  have poly : forward T initial (2 + 4) =
      ∑ j : Fin 4, (![-16, 56, -57, 14] j : ℤ) • forward T initial (2 + j.val) := by
    rw [tab ⟨6, by omega⟩]
    simp_rw [show ∀ j : Fin 4, forward T initial (2 + j.val) = W ⟨2 + j.val, by omega⟩
      from fun j => tab ⟨2 + j.val, by omega⟩]
    exact finite_certificate.2.2.2.2.2.2
  have scale (m : ℕ) (hm : 1 ≤ m) :
      literalCount (q := 3) horizontal between 1 (m + 1) = 6 * a (m + 1) := by
    classical
    let S : (Fin (m + 1) × Fin 4 → Fin 3) → Prop := fun A =>
      defects horizontal between (List.ofFn fun i j => A (i, j)) = 1
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
      intro e A
      change defects horizontal between _ = 1 ↔ _
      rw [show (List.ofFn fun i j => (e ∘ A) (i, j)) =
        (List.ofFn fun i j => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
        DefectTransfer.relabel_defects]
    have nonconstant : ∀ A, S A → ∃ x y, A x ≠ A y := by
      intro A h
      by_contra he
      push_neg at he
      have const : A = fun _ => A (0, 0) := funext fun x => he x (0, 0)
      change defects horizontal between _ = 1 at h
      rw [const] at h
      simp only [List.ofFn_const] at h
      rw [DefectTransfer.constant_defects] at h
      have cards : horizontal.card = 3 ∧ between.card = 6 := by decide +kernel
      rw [cards.1, cards.2] at h
      omega
    have orbit := @canonical_pattern_card (Fin (m + 1) × Fin 4) inferInstance
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
  cases n with
  | zero =>
    have h : dotProduct (W 5) terminal = 14 * dotProduct (W 4) terminal -
        57 * dotProduct (W 3) terminal + 56 * dotProduct (W 2) terminal -
        16 * dotProduct (W 1) terminal := by decide +kernel
    have h0 : dotProduct (W 5) terminal = 6 * (a 6 : ℤ) := by
      calc
        dotProduct (W 5) terminal = dotProduct (forward T initial 5) terminal := by
          exact congrArg (fun w => dotProduct w terminal) (tab ⟨5, by omega⟩).symm
        _ = dotProduct initial ((T ^ 5).mulVec terminal) := by
          rw [DefectTransfer.forward_eq]
          exact (Matrix.dotProduct_mulVec initial (T ^ 5) terminal).symm
        _ = 6 * (a 6 : ℤ) := bridge 5 (by omega)
    have h1 : dotProduct (W 4) terminal = 6 * (a 5 : ℤ) := by
      calc
        dotProduct (W 4) terminal = dotProduct (forward T initial 4) terminal := by
          exact congrArg (fun w => dotProduct w terminal) (tab ⟨4, by omega⟩).symm
        _ = dotProduct initial ((T ^ 4).mulVec terminal) := by
          rw [DefectTransfer.forward_eq]
          exact (Matrix.dotProduct_mulVec initial (T ^ 4) terminal).symm
        _ = 6 * (a 5 : ℤ) := bridge 4 (by omega)
    have h2 : dotProduct (W 3) terminal = 6 * (a 4 : ℤ) := by
      calc
        dotProduct (W 3) terminal = dotProduct (forward T initial 3) terminal := by
          exact congrArg (fun w => dotProduct w terminal) (tab ⟨3, by omega⟩).symm
        _ = dotProduct initial ((T ^ 3).mulVec terminal) := by
          rw [DefectTransfer.forward_eq]
          exact (Matrix.dotProduct_mulVec initial (T ^ 3) terminal).symm
        _ = 6 * (a 4 : ℤ) := bridge 3 (by omega)
    have h3 : dotProduct (W 2) terminal = 6 * (a 3 : ℤ) := by
      calc
        dotProduct (W 2) terminal = dotProduct (forward T initial 2) terminal := by
          exact congrArg (fun w => dotProduct w terminal) (tab ⟨2, by omega⟩).symm
        _ = dotProduct initial ((T ^ 2).mulVec terminal) := by
          rw [DefectTransfer.forward_eq]
          exact (Matrix.dotProduct_mulVec initial (T ^ 2) terminal).symm
        _ = 6 * (a 3 : ℤ) := bridge 2 (by omega)
    have h4 : dotProduct (W 1) terminal = 6 * (a 2 : ℤ) := by
      calc
        dotProduct (W 1) terminal = dotProduct (forward T initial 1) terminal := by
          exact congrArg (fun w => dotProduct w terminal) (tab ⟨1, by omega⟩).symm
        _ = dotProduct initial ((T ^ 1).mulVec terminal) := by
          rw [DefectTransfer.forward_eq]
          exact (Matrix.dotProduct_mulVec initial (T ^ 1) terminal).symm
        _ = 6 * (a 2 : ℤ) := bridge 1 (by omega)
    rw [h0, h1, h2, h3, h4] at h
    norm_num only [Nat.reduceAdd, zero_add] at h ⊢
    linarith
  | succ n =>
    have h := forward_shift T initial terminal 4 2 ![-16, 56, -57, 14] poly n
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
    have h0 := bridge (n + 2) (by omega)
    have h1 := bridge (n + 3) (by omega)
    have h2 := bridge (n + 4) (by omega)
    have h3 := bridge (n + 5) (by omega)
    have h4 := bridge (n + 6) (by omega)
    simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h0 h1 h2 h3 h4
    rw [h0, h1, h2, h3, h4] at h
    norm_num only [Nat.reduceAdd, zero_add] at h
    linarith

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229530Strip
