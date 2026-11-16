/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229633Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229633Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229633Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229633Strip.finite_certificate
   digest: Exact HDA defect transfer and Hardin's registered recurrence. -/

/-
admission_basis: open-problem-resolution (#31121; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229633Strip.result)
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

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229530Strip
import Mathlib.Data.Matrix.Block
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinSourceContinuations
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229582Strip

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229633Strip
open DefectTransfer (bondDefects defects literalCount lumped_count forward forward_shift)
open HardinA233177Canonical (Canonical canonical_pattern_card)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev Row := Fin 4 → Fin 3
private def horizontal : Finset (Fin 4 × Fin 4) := HardinA229582Strip.horizontal
private def between : Finset (Fin 4 × Fin 4) :=
  HardinA229530Strip.between
private def Valid (p : Row) (d : ℕ) : Prop :=
  d ≤ 2 ∧ bondDefects horizontal p p ≤ 2 - d
private instance decidableValid (p : Row) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (_ ∧ _))
private def cl (p : Row) (d : ℕ) : Fin 19 :=
  if 0 < d then (HardinA229530Strip.cl p (d - 1)).castAdd 9 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinSourceContinuations.sourceClass (true, true) p = 1 then 10 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinSourceContinuations.sourceClass (true, true) p = 2 then 11 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinSourceContinuations.sourceClass (true, true) p = 3 then 12 else
  if d = 0 ∧ ((p 0 = p 1 ∧ p 0 = p 2 ∧ p 0 ≠ p 3 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3) ∨ (p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 = p 2 ∧ p 1 = p 3 ∧ p 2 = p 3)) then 13 else
  if d = 0 ∧ ((p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3) ∨ (p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 = p 3)) then 14 else
  if d = 0 ∧ ((p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 = p 3) ∨ (p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 = p 3)) then 15 else
  if d = 0 ∧ ((p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3) ∨ (p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 = p 3)) then 16 else
  if d = 0 ∧ ((p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3) ∨ (p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3)) then 17 else
  18
private def T : Matrix (Fin 19) (Fin 19) ℤ :=
  Matrix.reindex (finSumFinEquiv : Fin 10 ⊕ Fin 9 ≃ Fin 19)
    (finSumFinEquiv : Fin 10 ⊕ Fin 9 ≃ Fin 19)
    (Matrix.fromBlocks HardinA229530Strip.T
      (![![0, 0, 2, 2, 4, 0, 2, 2, 0],
        ![0, 3, 4, 0, 4, 0, 4, 2, 2],
        ![1, 2, 1, 0, 5, 0, 4, 1, 2],
        ![0, 2, 2, 0, 2, 0, 2, 0, 1],
        ![2, 0, 2, 0, 0, 0, 0, 0, 0],
        ![1, 1, 3, 0, 1, 0, 1, 0, 0],
        ![2, 2, 5, 0, 1, 0, 1, 0, 1],
        ![1, 2, 4, 0, 1, 0, 1, 0, 0],
        ![2, 2, 2, 0, 0, 0, 0, 1, 0],
        ![0, 2, 4, 0, 2, 0, 0, 0, 0]])
      (0)
      (![![(HardinSourceContinuations.M 1 1 / 16), (HardinSourceContinuations.M 1 2 / 16), (HardinSourceContinuations.M 1 3 / 16), 0, 0, 0, 0, 0, 0],
        ![(HardinSourceContinuations.M 2 1 / 16), (HardinSourceContinuations.M 2 2 / 16), (HardinSourceContinuations.M 2 3 / 16), 0, 0, 0, 0, 0, 0],
        ![(HardinSourceContinuations.M 3 1 / 16), (HardinSourceContinuations.M 3 2 / 16), (HardinSourceContinuations.M 3 3 / 16), 0, 0, 0, 0, 0, 0],
        ![1, 0, 0, 0, 0, 0, 0, 0, 0],
        ![1, 0, 1, 0, 0, 0, 0, 0, 0],
        ![0, 0, 0, 0, 0, 0, 0, 0, 0],
        ![1, 0, 1, 0, 0, 0, 0, 0, 0],
        ![0, 0, 0, 0, 0, 0, 0, 0, 0],
        ![1, 0, 0, 0, 0, 0, 0, 0, 0]]))
private def initial : Fin 19 → ℤ :=
  Fin.append HardinA229530Strip.initial (![0, 0, 0, 12, 0, 6, 0, 0, 0])
private def terminal : Fin 19 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private def W : Fin 11 → Fin 19 → ℤ :=
  Fin.append (fun i => Fin.append (HardinA229530Strip.W i)
      ((![![0, 0, 0, 12, 0, 6, 0, 0, 0],
        ![72, 114, 192, 12, 144, 0, 108, 42, 48],
        ![1302, 894, 2256, 96, 900, 0, 720, 216, 270],
        ![13842, 8544, 23232, 624, 6516, 0, 5340, 1368, 1896],
        ![130938, 77046, 215496, 3984, 46860, 0, 39348, 8712, 13602],
        ![1155858, 657996, 1874664, 25392, 332844, 0, 284964, 55512, 96564],
        ![9728082, 5401242, 15598980, 161808, 2339292, 0, 2034180, 353736, 678468]]) i))
    (![![3285192, 1502736, 4787928, 18314412, 9419184, 28404060, 1782456, 1782456, 0, 515544, 79046856, 43033524, 125596500, 1031088, 16297884, 0, 14353620, 2254104, 4725780],
        ![20934168, 9575856, 30510024, 133044396, 67495968, 204812748, 11358312, 11358312, 0, 3285192, 625153188, 334954740, 985848384, 6570384, 112720236, 0, 100330836, 14363784, 32678196],
        ![133398408, 61020048, 194418456, 951918204, 477731472, 1456874508, 72378360, 72378360, 0, 20934168, 4838800368, 2558609100, 7582684788, 41868336, 774778764, 0, 695830020, 91530072, 224574468],
        ![850052184, 388836912, 1238889096, 6729384540, 3347739456, 10250608284, 461215272, 461215272, 0, 133398408, 36801322356, 19244084004, 57361443072, 266796816, 5297102076, 0, 4794018468, 583255368, 1535173572]])

/-- The literal row-major canonical filtered array count. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin n × Fin 4 → Fin 3 =>
    @Canonical (Fin n × Fin 4)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin n × Fin 4 → Fin 3 =>
    defects horizontal between (List.ofFn fun i j => A (i, j)) = 2 ∧
    (@Canonical (Fin n × Fin 4)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

private theorem finite_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ r : Row,
      bondDefects between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects between p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ s : Fin 19,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 2 →
      Valid r (2 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 19, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl r (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 10, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 10 = ∑ j : Fin 6, (![-64, 336, -636, 511, -159, 21] j : ℤ) • W ⟨4 + j.val, by omega⟩ := by
  refine ⟨by decide +kernel, (by
    intro p d hp r hr
    dsimp only [Valid] at hp ⊢
    omega), ?_, by decide +kernel, ?_, ?_,
    by decide +kernel⟩
  · have valid_cut : ∀ p (d : Fin 3), Valid p d.val → 0 < d.val →
        HardinA229530Strip.Valid p (d.val - 1) := by decide +kernel
    have active_cut : ∀ (p r : Row) (d : Fin 3) (j : Fin 10),
        Valid p d.val → 0 < d.val →
        ((bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
          cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = j.castAdd 9) ↔
          bondDefects HardinA229530Strip.between p r + bondDefects horizontal r r ≤ d.val - 1 ∧
            HardinA229530Strip.cl r (d.val - 1 - (bondDefects HardinA229530Strip.between p r + bondDefects horizontal r r)) = j) := by
      have numeric : ∀ (r : Row) (c d : Fin 3) (j : Fin 10), 0 < d.val →
          ((c.val ≤ d.val ∧ cl r (d.val - c.val) = j.castAdd 9) ↔
            c.val ≤ d.val - 1 ∧ HardinA229530Strip.cl r (d.val - 1 - c.val) = j) := by
        decide +kernel
      intro p r d j _ hd
      by_cases hc : bondDefects between p r + bondDefects horizontal r r < 3
      · exact numeric r ⟨_, hc⟩ d j hd
      · have h0 : ¬ (bondDefects between p r + bondDefects horizontal r r ≤ d.val) := by omega
        have h1 : ¬ (bondDefects HardinA229530Strip.between p r +
            bondDefects horizontal r r ≤ d.val - 1) := by
          change ¬ (bondDefects between p r + bondDefects horizontal r r ≤ d.val - 1)
          omega
        simp only [h0, h1, false_and]
    have active_table : ∀ p (d : Fin 3) (j : Fin 10),
        Valid p d.val → 0 < d.val →
        HardinA229530Strip.T (HardinA229530Strip.cl p (d.val - 1)) j =
          T (cl p d.val) (j.castAdd 9) := by decide +kernel
    have zero_cut : ∀ (p r : Row) (d : Fin 3) (s : Fin 19)
        (hz : HardinThinGraphTransport.proper p ∧ d.val = 0 ∧ 10 ≤ s.val ∧ s.val < 13),
        (bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
          cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s) ↔
          HardinThinGraphTransport.proper r ∧ HardinThinGraphTransport.compatible true p r ∧
          HardinSourceContinuations.sourceClass (true, true) r =
            ⟨s.val - 10 + 1, by omega⟩ := by
      intro p
      generalize h0 : p 0 = c0
      generalize h1 : p 1 = c1
      fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert
    have zero_table : ∀ p (d : Fin 3) (s : Fin 19)
        (hz : HardinThinGraphTransport.proper p ∧ d.val = 0 ∧ 10 ≤ s.val ∧ s.val < 13),
        HardinSourceContinuations.M (HardinSourceContinuations.sourceClass (true, true) p)
          ⟨s.val - 10 + 1, by omega⟩ / 16 = T (cl p d.val) s := by decide +kernel
    have remaining : ∀ p (d : Fin 3), Valid p d.val → ∀ s : Fin 19,
        ¬ (0 < d.val ∧ s.val < 10) →
        ¬ (HardinThinGraphTransport.proper p ∧ d.val = 0 ∧ 10 ≤ s.val ∧ s.val < 13) →
        (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
          cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
          then (1 : ℤ) else 0) = T (cl p d.val) s := by
      intro p
      generalize h0 : p 0 = c0
      generalize h1 : p 1 = c1
      fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert
    intro p d hp s
    by_cases ha : 0 < d.val ∧ s.val < 10
    · let j : Fin 10 := ⟨s.val, ha.2⟩
      have he : s = j.castAdd 9 := rfl
      rw [he]
      simp_rw [active_cut p _ d j hp ha.1]
      exact (HardinA229530Strip.finite_certificate.2.2.1 p
        ⟨d.val - 1, by omega⟩ (valid_cut p d hp ha.1) j).trans
          (active_table p d j hp ha.1)
    · by_cases hz : HardinThinGraphTransport.proper p ∧ d.val = 0 ∧ 10 ≤ s.val ∧ s.val < 13
      · simp_rw [zero_cut p _ d s hz]
        have h := HardinA229530Strip.raw_successors p hz.1 ⟨s.val - 10 + 1, by omega⟩
        have hd : (∑ r : Row, if HardinThinGraphTransport.proper r ∧
            HardinThinGraphTransport.compatible true p r ∧
            HardinSourceContinuations.sourceClass (true, true) r =
              ⟨s.val - 10 + 1, by omega⟩ then (1 : ℤ) else 0) =
            HardinSourceContinuations.M
              (HardinSourceContinuations.sourceClass (true, true) p)
              ⟨s.val - 10 + 1, by omega⟩ / 16 := by
          exact Int.eq_ediv_of_mul_eq_right (by decide) h
        exact hd.trans (zero_table p d s hz)
      · exact remaining p d hp s ha hz
  · have initial_cut : ∀ (r : Row) (j : Fin 10),
        (bondDefects horizontal r r ≤ 2 ∧
          cl r (2 - bondDefects horizontal r r) = j.castAdd 9) ↔
          bondDefects horizontal r r ≤ 1 ∧
            HardinA229530Strip.cl r (1 - bondDefects horizontal r r) = j := by decide +kernel
    have initial_table : ∀ j : Fin 10,
        HardinA229530Strip.initial j = initial (j.castAdd 9) := by decide +kernel
    have remaining : ∀ s : Fin 19, 10 ≤ s.val →
        (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
          cl r (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s := by
      decide +kernel
    intro s
    by_cases hs : s.val < 10
    · let j : Fin 10 := ⟨s.val, hs⟩
      have he : s = j.castAdd 9 := rfl
      rw [he]
      simp_rw [initial_cut _ j]
      exact (HardinA229530Strip.finite_certificate.2.2.2.2.1 j).trans (initial_table j)
    · exact remaining s (by omega)
  · have zero_cut : ∀ j : Fin 10,
        W 0 (j.castAdd 9) = HardinA229530Strip.W 0 j ∧
        initial (j.castAdd 9) = HardinA229530Strip.initial j := by decide +kernel
    have zero_remaining : ∀ s : Fin 19, 10 ≤ s.val →
        W 0 s = initial s := by decide +kernel
    have step_cut : ∀ (i : Fin 6) (j : Fin 10),
        W (i.succ.castAdd 4) (j.castAdd 9) = HardinA229530Strip.W i.succ j ∧
        Matrix.vecMul (W (i.castSucc.castAdd 4)) T (j.castAdd 9) =
          Matrix.vecMul (HardinA229530Strip.W i.castSucc) HardinA229530Strip.T j := by decide +kernel
    have step_remaining : ∀ (i : Fin 10) (s : Fin 19),
        ¬ (i.val < 6 ∧ s.val < 10) →
        W i.succ s = Matrix.vecMul (W i.castSucc) T s := by decide +kernel
    constructor
    · funext s
      by_cases hs : s.val < 10
      · let j : Fin 10 := ⟨s.val, hs⟩
        have he : s = j.castAdd 9 := rfl
        rw [he, (zero_cut j).1, (zero_cut j).2]
        exact congrFun HardinA229530Strip.finite_certificate.2.2.2.2.2.1.1 j
      · exact zero_remaining s (by omega)
    · intro i
      funext s
      by_cases hs : i.val < 6 ∧ s.val < 10
      · let k : Fin 6 := ⟨i.val, hs.1⟩
        let j : Fin 10 := ⟨s.val, hs.2⟩
        have he : s = j.castAdd 9 := rfl
        have h0 : i.castSucc = k.castSucc.castAdd 4 := rfl
        have h1 : i.succ = k.succ.castAdd 4 := rfl
        rw [he, h0, h1, (step_cut k j).1, (step_cut k j).2]
        exact congrFun (HardinA229530Strip.finite_certificate.2.2.2.2.2.1.2 k) j
      · exact step_remaining i s hs

attribute [local irreducible] a

/-- The registered recurrence at every index at least 10. -/
theorem result (n : ℕ) :
    (a (n + 10) : ℤ) = 21 * a (n + 9) - 159 * a (n + 8) + 511 * a (n + 7) - 636 * a (n + 6) + 336 * a (n + 5) - 64 * a (n + 4) := by
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
  have tab (i : Fin 11) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (finite_certificate.2.2.2.2.2.1.2 i).symm
  have poly : forward T initial (4 + 6) =
      ∑ j : Fin 6, (![-64, 336, -636, 511, -159, 21] j : ℤ) • forward T initial (4 + j.val) := by
    rw [tab ⟨10, by omega⟩]
    simp_rw [show ∀ j : Fin 6, forward T initial (4 + j.val) = W ⟨4 + j.val, by omega⟩
      from fun j => tab ⟨4 + j.val, by omega⟩]
    exact finite_certificate.2.2.2.2.2.2
  have scale (m : ℕ) (hm : 1 ≤ m) :
      literalCount (q := 3) horizontal between 2 (m + 1) = 6 * a (m + 1) := by
    classical
    let S : (Fin (m + 1) × Fin 4 → Fin 3) → Prop := fun A =>
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
    have h : dotProduct (W 9) terminal = 21 * dotProduct (W 8) terminal -
        159 * dotProduct (W 7) terminal + 511 * dotProduct (W 6) terminal -
        636 * dotProduct (W 5) terminal + 336 * dotProduct (W 4) terminal -
        64 * dotProduct (W 3) terminal := by decide +kernel
    have h0 : dotProduct (W 9) terminal = 6 * (a 10 : ℤ) := by
      calc
        dotProduct (W 9) terminal = dotProduct (forward T initial 9) terminal := by
          exact congrArg (fun w => dotProduct w terminal) (tab ⟨9, by omega⟩).symm
        _ = dotProduct initial ((T ^ 9).mulVec terminal) := by
          rw [DefectTransfer.forward_eq]
          exact (Matrix.dotProduct_mulVec initial (T ^ 9) terminal).symm
        _ = 6 * (a 10 : ℤ) := bridge 9 (by omega)
    have h1 : dotProduct (W 8) terminal = 6 * (a 9 : ℤ) := by
      calc
        dotProduct (W 8) terminal = dotProduct (forward T initial 8) terminal := by
          exact congrArg (fun w => dotProduct w terminal) (tab ⟨8, by omega⟩).symm
        _ = dotProduct initial ((T ^ 8).mulVec terminal) := by
          rw [DefectTransfer.forward_eq]
          exact (Matrix.dotProduct_mulVec initial (T ^ 8) terminal).symm
        _ = 6 * (a 9 : ℤ) := bridge 8 (by omega)
    have h2 : dotProduct (W 7) terminal = 6 * (a 8 : ℤ) := by
      calc
        dotProduct (W 7) terminal = dotProduct (forward T initial 7) terminal := by
          exact congrArg (fun w => dotProduct w terminal) (tab ⟨7, by omega⟩).symm
        _ = dotProduct initial ((T ^ 7).mulVec terminal) := by
          rw [DefectTransfer.forward_eq]
          exact (Matrix.dotProduct_mulVec initial (T ^ 7) terminal).symm
        _ = 6 * (a 8 : ℤ) := bridge 7 (by omega)
    have h3 : dotProduct (W 6) terminal = 6 * (a 7 : ℤ) := by
      calc
        dotProduct (W 6) terminal = dotProduct (forward T initial 6) terminal := by
          exact congrArg (fun w => dotProduct w terminal) (tab ⟨6, by omega⟩).symm
        _ = dotProduct initial ((T ^ 6).mulVec terminal) := by
          rw [DefectTransfer.forward_eq]
          exact (Matrix.dotProduct_mulVec initial (T ^ 6) terminal).symm
        _ = 6 * (a 7 : ℤ) := bridge 6 (by omega)
    have h4 : dotProduct (W 5) terminal = 6 * (a 6 : ℤ) := by
      calc
        dotProduct (W 5) terminal = dotProduct (forward T initial 5) terminal := by
          exact congrArg (fun w => dotProduct w terminal) (tab ⟨5, by omega⟩).symm
        _ = dotProduct initial ((T ^ 5).mulVec terminal) := by
          rw [DefectTransfer.forward_eq]
          exact (Matrix.dotProduct_mulVec initial (T ^ 5) terminal).symm
        _ = 6 * (a 6 : ℤ) := bridge 5 (by omega)
    have h5 : dotProduct (W 4) terminal = 6 * (a 5 : ℤ) := by
      calc
        dotProduct (W 4) terminal = dotProduct (forward T initial 4) terminal := by
          exact congrArg (fun w => dotProduct w terminal) (tab ⟨4, by omega⟩).symm
        _ = dotProduct initial ((T ^ 4).mulVec terminal) := by
          rw [DefectTransfer.forward_eq]
          exact (Matrix.dotProduct_mulVec initial (T ^ 4) terminal).symm
        _ = 6 * (a 5 : ℤ) := bridge 4 (by omega)
    have h6 : dotProduct (W 3) terminal = 6 * (a 4 : ℤ) := by
      calc
        dotProduct (W 3) terminal = dotProduct (forward T initial 3) terminal := by
          exact congrArg (fun w => dotProduct w terminal) (tab ⟨3, by omega⟩).symm
        _ = dotProduct initial ((T ^ 3).mulVec terminal) := by
          rw [DefectTransfer.forward_eq]
          exact (Matrix.dotProduct_mulVec initial (T ^ 3) terminal).symm
        _ = 6 * (a 4 : ℤ) := bridge 3 (by omega)
    rw [h0, h1, h2, h3, h4, h5, h6] at h
    norm_num only [Nat.reduceAdd, zero_add] at h ⊢
    linarith
  | succ n =>
    have h := forward_shift T initial terminal 6 4 ![-64, 336, -636, 511, -159, 21] poly n
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
    have h0 := bridge (n + 4) (by omega)
    have h1 := bridge (n + 5) (by omega)
    have h2 := bridge (n + 6) (by omega)
    have h3 := bridge (n + 7) (by omega)
    have h4 := bridge (n + 8) (by omega)
    have h5 := bridge (n + 9) (by omega)
    have h6 := bridge (n + 10) (by omega)
    simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h0 h1 h2 h3 h4 h5 h6
    rw [h0, h1, h2, h3, h4, h5, h6] at h
    norm_num only [Nat.reduceAdd, zero_add] at h
    linarith

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229633Strip
