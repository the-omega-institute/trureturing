/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_power,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.step_checks,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_entries,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_readout,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.image_entries
   digest: Residual-budget states for width-six two-defect HDA strips. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229532Strip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
open D5.S3.Combinatorics.TraceAvoidingArrays

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State

open WidthSix
open HardinA229584StripData (Row horizontal)
open HardinA229532StripData (between)
open HardinA233177Canonical (Canonical)
open DefectTransfer (bondDefects)

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

abbrev State := Fin 127
abbrev Fresh := Fin 96
abbrev RowNumber := Fin 729

def h (p : Row) : ℕ := bondDefects horizontal p p

def cost (p r : Row) : ℕ := bondDefects between p r + h r

def Valid (p : Row) (d : ℕ) : Prop := h p + d ≤ 2

def rowEquiv : RowNumber ≃ Row := (finFunctionFinEquiv (m := 3) (n := 6)).symm

private def rowCode (p : Row) : ℕ :=
  (if p 0 = p 1 then 1 else 0) + (if p 0 = p 2 then 2 else 0) +
  (if p 0 = p 3 then 4 else 0) + (if p 0 = p 4 then 8 else 0) +
  (if p 0 = p 5 then 16 else 0) + (if p 1 = p 2 then 32 else 0) +
  (if p 1 = p 3 then 64 else 0) + (if p 1 = p 4 then 128 else 0) +
  (if p 1 = p 5 then 256 else 0) + (if p 2 = p 3 then 512 else 0) +
  (if p 2 = p 4 then 1024 else 0) + (if p 2 = p 5 then 2048 else 0) +
  (if p 3 = p 4 then 4096 else 0) + (if p 3 = p 5 then 8192 else 0) +
  (if p 4 = p 5 then 16384 else 0)

private def representativeNumbers : Array Nat := #[
  270, 513, 189, 432, 252, 495, 333, 657, 279, 522, 198, 441,
  63, 387, 225, 468, 246, 489, 327, 651, 354, 705, 255, 498,
  336, 660, 282, 525, 201, 444, 66, 390, 228, 471, 21, 372,
  75, 399, 237, 480, 90, 576, 171, 414, 306, 549, 144, 630,
  84, 570, 165, 408, 30, 111, 597, 678, 57, 381, 219, 462,
  93, 579, 174, 417, 309, 552, 147, 633, 264, 507, 345, 669,
  48, 129, 615, 696, 318, 561, 156, 642, 273, 516, 192, 435,
  300, 543, 138, 624, 102, 588, 183, 426, 291, 534, 210, 453]

private def representativeCodes : List Nat := [
  9387, 1195, 2355, 8227, 6349, 4301, 19525, 16453, 10889, 649, 785, 10753,
  16793, 19457, 4369, 6145, 5902, 5646, 17286, 16902, 29122, 28674, 6444, 4140,
  19876, 16420, 11112, 616, 624, 11104, 16440, 19872, 4144, 6432, 28700, 29120,
  16920, 17280, 5648, 5888, 9557, 1093, 8533, 2117, 2185, 8329, 1297, 9217,
  10902, 646, 10774, 774, 19546, 6354, 4290, 16450, 19482, 16770, 6162, 4354,
  9396, 1188, 8244, 2340, 2344, 8232, 1200, 9376, 4364, 6156, 16772, 19460,
  16472, 4304, 6336, 19520, 776, 10760, 656, 10880, 9546, 1098, 2130, 8514,
  1290, 9226, 2194, 8322, 8340, 2180, 9236, 1284, 8520, 2120, 1104, 9536]

def rep (i : Fresh) : Row :=
  rowEquiv (Fin.ofNat 729 (representativeNumbers[i.val]?.getD 0))

def budget (i : Fresh) : ℕ := 2 - h (rep i)

def fresh (p : Row) : Fresh := Fin.ofNat 96 (representativeCodes.idxOf (rowCode p))

def cl (p : Row) (d : ℕ) : State :=
  if h p + d ≤ 1 then (HardinA229532StripData.cl p d).castAdd 96
  else (fresh p).natAdd 31

def destination (p : Row) (d : ℕ) (r : Row) : Option State :=
  if cost p r ≤ d then some (cl r (d - cost p r)) else none

def outgoing (p : Row) (d : ℕ) : List State :=
  (List.ofFn rowEquiv).filterMap (destination p d)

def startClass (p : Row) : Option State :=
  if h p ≤ 2 then some (cl p (2 - h p)) else none

def startClasses : List State := (List.ofFn rowEquiv).filterMap startClass

private theorem filterMap_count (f : Row → Option State) (s : State) (rows : List Row) :
    ((rows.filterMap f).count s : ℤ) =
      (rows.map fun r => if f r = some s then (1 : ℤ) else 0).sum := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    cases hr : f r with
    | none => simp [hr, ih]
    | some j =>
      by_cases hs : s = j
      · subst j
        simp [hr, ih, add_comm]
      · simp [hr, ih, Ne.symm hs]

theorem count_classes (f : Row → Option State) (s : State) :
    (((List.ofFn rowEquiv).filterMap f).count s : ℤ) =
      ∑ r : Row, if f r = some s then (1 : ℤ) else 0 := by
  rw [filterMap_count, List.map_ofFn, List.sum_ofFn]
  exact rowEquiv.sum_comp (fun r : Row => if f r = some s then (1 : ℤ) else 0)

theorem outgoing_count (p : Row) (d : ℕ) (s : State) :
    ((outgoing p d).count s : ℤ) =
      ∑ r : Row, if cost p r ≤ d ∧ cl r (d - cost p r) = s then (1 : ℤ) else 0 := by
  rw [outgoing, count_classes]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : cost p r ≤ d <;> simp [destination, hr]

theorem start_count (s : State) :
    (startClasses.count s : ℤ) =
      ∑ r : Row, if h r ≤ 2 ∧ cl r (2 - h r) = s then (1 : ℤ) else 0 := by
  rw [startClasses, count_classes]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : h r ≤ 2 <;> simp [startClass, hr]

private theorem bond_relabel (e : Equiv.Perm (Fin 3))
    (E : Finset (Fin 6 × Fin 6)) (p r : Row) :
    bondDefects E (e ∘ p) (e ∘ r) = bondDefects E p r := by
  simp only [bondDefects, Function.comp_apply, ne_eq, e.injective.eq_iff]

theorem h_relabel (e : Equiv.Perm (Fin 3)) (p : Row) : h (e ∘ p) = h p :=
  bond_relabel e horizontal p p

theorem cost_relabel (e : Equiv.Perm (Fin 3)) (p r : Row) :
    cost (e ∘ p) (e ∘ r) = cost p r := by
  simp only [cost, bond_relabel, h_relabel]

theorem cl_relabel (e : Equiv.Perm (Fin 3)) (p : Row) (d : ℕ) :
    cl (e ∘ p) d = cl p d := by
  simp only [cl, h_relabel, HardinA229532StripData.cl,
    HardinA233172DiagonalStrip.boundaryClass, fresh, rowCode, bondDefects,
    Function.comp_apply, ne_eq, e.injective.eq_iff]

theorem legal (p : Row) (d : ℕ) (hp : Valid p d) (r : Row) (hr : cost p r ≤ d) :
    Valid r (d - cost p r) := by
  unfold cost at hr ⊢
  unfold Valid at hp ⊢
  omega

private theorem inherited_valid_iff (p : Row) (d : ℕ) :
    HardinA229532StripData.Valid p d ↔ h p + d ≤ 1 := by
  change d ≤ 1 ∧ h p ≤ 1 - d ↔ h p + d ≤ 1
  omega

theorem closed (p r : Row) (d : ℕ) (hp : h p + d ≤ 1) (hr : cost p r ≤ d) :
    h r + (d - cost p r) ≤ 1 := by
  let budget : Fin 2 := ⟨d, by omega⟩
  exact (inherited_valid_iff r (d - cost p r)).mp
    (HardinA229532Strip.finite_certificate.2.1 p budget ((inherited_valid_iff p d).mpr hp) r hr)

theorem legal_start (r : Row) (hr : h r ≤ 2) : Valid r (2 - h r) := by
  unfold Valid
  omega

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
