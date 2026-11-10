/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.finite_certificate
   digest: The six-row pair-pattern transfer has fifty live relabelling classes and an order-24 tail relation. -/
/-
admission_basis: open-problem-resolution (#28655; Proved)
escape_witness: none; existing unfrozen TransferMatrix theorems and finite table
  instantiation/normalization supply the pair-count relation.
Proper: proof_shape=bind-only; consumers=instDecidableProper, L, grid_good
instDecidableProper: proof_shape=bind-only; consumers=L
L: proof_shape=bind-only; consumers=count_transfer, initial_values, recurrence
Col: proof_shape=bind-only; consumers=column, compatible, gridEquiv
column: proof_shape=bind-only; consumers=compatible, column_relabel, column_grid
compatible: proof_shape=bind-only; consumers=instDecidableCompatible, grid_good, quotient_rows
instDecidableCompatible: proof_shape=bind-only; consumers=successors_spec, representative_rows
orbit: proof_shape=bind-only; consumers=cls, class_rep
liveClass: proof_shape=bind-only; consumers=cls
cls: proof_shape=bind-only; consumers=class_relabel, representative_rows, count_transfer
representatives: proof_shape=bind-only; consumers=class_rep, successors_spec
Q: proof_shape=bind-only; consumers=representative_rows, table_steps, powers_table
sizes: proof_shape=bind-only; consumers=class_sizes, initial_weights
weights: proof_shape=bind-only; consumers=initial_weights, count_transfer
successors: proof_shape=bind-only; consumers=successors_spec, representative_rows
relabel: proof_shape=bind-only; consumers=column_relabel, class_rep
column_relabel: proof_shape=bind-only; consumers=compatible_relabel
compatible_relabel: proof_shape=bind-only; consumers=quotient_rows
class_relabel: proof_shape=bind-only; consumers=quotient_rows
class_rep: proof_shape=bind-only; consumers=quotient_rows
successors_spec: proof_shape=bind-only; consumers=representative_rows
representative_rows: proof_shape=bind-only; consumers=quotient_rows
quotient_rows: proof_shape=bind-only; consumers=initial_weights, count_transfer
compatible_symm: proof_shape=bind-only; consumers=initial_weights
class_sizes: proof_shape=bind-only; consumers=initial_weights
initial_weights: proof_shape=bind-only; consumers=count_transfer
gridEquiv: proof_shape=bind-only; consumers=column_grid, grid_good, count_transfer
column_grid: proof_shape=bind-only; consumers=grid_good
tail_iff: proof_shape=bind-only; consumers=good_iff
good_iff: proof_shape=bind-only; consumers=grid_good
grid_good: proof_shape=bind-only; consumers=count_transfer
count_transfer: proof_shape=bind-only; consumers=initial_values, recurrence_core
W: proof_shape=bind-only; consumers=table_zero, table_steps, powers_table
coefficients: proof_shape=bind-only; consumers=power_polynomial, recurrence_core
table_zero: proof_shape=bind-only; consumers=powers_table
table_steps: proof_shape=bind-only; consumers=powers_table
powers_table: proof_shape=bind-only; consumers=initial_values, power_polynomial
power_polynomial: proof_shape=bind-only; consumers=recurrence_core
initial_values: proof_shape=bind-only; consumers=HardinA233179Ladder.finite_certificate
recurrence_core: proof_shape=bind-only; consumers=recurrence
recurrence: proof_shape=bind-only; consumers=HardinA233179Ladder.result
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
/-! Exact column enumeration and arbitrary-width transfer for six rows. -/
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays

def Proper {n : ℕ} (P : Fin 6 × Fin n → Fin 3) : Prop :=
  ∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin 6),
    (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) →
    P (r, j) ≠ P (s, ⟨j.val + 1, h⟩)
private instance instDecidableProper {n : ℕ} (P : Fin 6 × Fin n → Fin 3) :
    Decidable (Proper P) := inferInstanceAs (Decidable (∀ _ _ _ _, _ → _))
def L (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun P : Fin 6 × Fin n → Fin 3 => Proper P)).card
private abbrev Col := Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3
private def column (c : Col) : Fin 6 → Fin 3 :=
  ![c.1,c.2.1,c.2.2.1,c.2.2.2.1,c.2.2.2.2.1,c.2.2.2.2.2]
private def compatible (a b : Col) : Prop :=
  ∀ r s : Fin 6, (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) → column a r ≠ column b s
private instance instDecidableCompatible (a b : Col) : Decidable (compatible a b) :=
  inferInstanceAs (Decidable (∀ _ _, _ → _))
private def orbit (c : Col) : Fin 122 :=
  if column c 1 = column c 0 then (if column c 2 = column c 0 then (if column c 3 = column c 0 then
    (if column c 4 = column c 0 then (if column c 5 = column c 0 then (0) else (1)) else (if column
    c 5 = column c 0 then (2) else (if column c 5 = column c 4 then (3) else (4)))) else (if column
    c 4 = column c 0 then (if column c 5 = column c 0 then (5) else (if column c 5 = column c 3 then
    (6) else (7))) else (if column c 4 = column c 3 then (if column c 5 = column c 0 then (8) else
    (if column c 5 = column c 3 then (9) else (10))) else (if column c 5 = column c 0 then (11) else
    (if column c 5 = column c 3 then (12) else (13)))))) else (if column c 3 = column c 0 then (if
    column c 4 = column c 0 then (if column c 5 = column c 0 then (14) else (if column c 5 = column
    c 2 then (15) else (16))) else (if column c 4 = column c 2 then (if column c 5 = column c 0 then
    (17) else (if column c 5 = column c 2 then (18) else (19))) else (if column c 5 = column c 0
    then (20) else (if column c 5 = column c 2 then (21) else (22))))) else (if column c 3 = column
    c 2 then (if column c 4 = column c 0 then (if column c 5 = column c 0 then (23) else (if column
    c 5 = column c 2 then (24) else (25))) else (if column c 4 = column c 2 then (if column c 5 =
    column c 0 then (26) else (if column c 5 = column c 2 then (27) else (28))) else (if column c 5
    = column c 0 then (29) else (if column c 5 = column c 2 then (30) else (31))))) else (if column
    c 4 = column c 0 then (if column c 5 = column c 0 then (32) else (if column c 5 = column c 2
    then (33) else (34))) else (if column c 4 = column c 2 then (if column c 5 = column c 0 then
    (35) else (if column c 5 = column c 2 then (36) else (37))) else (if column c 5 = column c 0
    then (38) else (if column c 5 = column c 2 then (39) else (40)))))))) else (if column c 2 =
    column c 0 then (if column c 3 = column c 0 then (if column c 4 = column c 0 then (if column c 5
    = column c 0 then (41) else (if column c 5 = column c 1 then (42) else (43))) else (if column c
    4 = column c 1 then (if column c 5 = column c 0 then (44) else (if column c 5 = column c 1 then
    (45) else (46))) else (if column c 5 = column c 0 then (47) else (if column c 5 = column c 1
    then (48) else (49))))) else (if column c 3 = column c 1 then (if column c 4 = column c 0 then
    (if column c 5 = column c 0 then (50) else (if column c 5 = column c 1 then (51) else (52)))
    else (if column c 4 = column c 1 then (if column c 5 = column c 0 then (53) else (if column c 5
    = column c 1 then (54) else (55))) else (if column c 5 = column c 0 then (56) else (if column c
    5 = column c 1 then (57) else (58))))) else (if column c 4 = column c 0 then (if column c 5 =
    column c 0 then (59) else (if column c 5 = column c 1 then (60) else (61))) else (if column c 4
    = column c 1 then (if column c 5 = column c 0 then (62) else (if column c 5 = column c 1 then
    (63) else (64))) else (if column c 5 = column c 0 then (65) else (if column c 5 = column c 1
    then (66) else (67))))))) else (if column c 2 = column c 1 then (if column c 3 = column c 0 then
    (if column c 4 = column c 0 then (if column c 5 = column c 0 then (68) else (if column c 5 =
    column c 1 then (69) else (70))) else (if column c 4 = column c 1 then (if column c 5 = column c
    0 then (71) else (if column c 5 = column c 1 then (72) else (73))) else (if column c 5 = column
    c 0 then (74) else (if column c 5 = column c 1 then (75) else (76))))) else (if column c 3 =
    column c 1 then (if column c 4 = column c 0 then (if column c 5 = column c 0 then (77) else (if
    column c 5 = column c 1 then (78) else (79))) else (if column c 4 = column c 1 then (if column c
    5 = column c 0 then (80) else (if column c 5 = column c 1 then (81) else (82))) else (if column
    c 5 = column c 0 then (83) else (if column c 5 = column c 1 then (84) else (85))))) else (if
    column c 4 = column c 0 then (if column c 5 = column c 0 then (86) else (if column c 5 = column
    c 1 then (87) else (88))) else (if column c 4 = column c 1 then (if column c 5 = column c 0 then
    (89) else (if column c 5 = column c 1 then (90) else (91))) else (if column c 5 = column c 0
    then (92) else (if column c 5 = column c 1 then (93) else (94))))))) else (if column c 3 =
    column c 0 then (if column c 4 = column c 0 then (if column c 5 = column c 0 then (95) else (if
    column c 5 = column c 1 then (96) else (97))) else (if column c 4 = column c 1 then (if column c
    5 = column c 0 then (98) else (if column c 5 = column c 1 then (99) else (100))) else (if column
    c 5 = column c 0 then (101) else (if column c 5 = column c 1 then (102) else (103))))) else (if
    column c 3 = column c 1 then (if column c 4 = column c 0 then (if column c 5 = column c 0 then
    (104) else (if column c 5 = column c 1 then (105) else (106))) else (if column c 4 = column c 1
    then (if column c 5 = column c 0 then (107) else (if column c 5 = column c 1 then (108) else
    (109))) else (if column c 5 = column c 0 then (110) else (if column c 5 = column c 1 then (111)
    else (112))))) else (if column c 4 = column c 0 then (if column c 5 = column c 0 then (113) else
    (if column c 5 = column c 1 then (114) else (115))) else (if column c 4 = column c 1 then (if
    column c 5 = column c 0 then (116) else (if column c 5 = column c 1 then (117) else (118))) else
    (if column c 5 = column c 0 then (119) else (if column c 5 = column c 1 then (120) else
    (121)))))))))
private def liveClass : Fin 122 → Fin 51 :=
  ![1, 2, 3, 4, 0, 5, 6, 0, 7, 8, 9, 0, 0, 0, 10, 11, 12, 13, 14, 0, 0, 0, 0, 15, 16, 0, 17, 18, 19,
    0, 20, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 24, 25, 26, 0, 27, 0, 28, 29, 30, 0, 31, 32, 33,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 35, 36, 37, 38, 0, 0, 0, 0, 39, 40, 0, 41, 42, 43, 0,
    44, 45, 0, 0, 0, 0, 46, 47, 48, 49, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]
private def cls (c : Col) : Fin 51 := liveClass (orbit c)
private def representatives : Fin 122 → Col :=
  ![(0,0,0,0,0,0), (0,0,0,0,0,1), (0,0,0,0,1,0), (0,0,0,0,1,1), (0,0,0,0,1,2), (0,0,0,1,0,0),
    (0,0,0,1,0,1), (0,0,0,1,0,2), (0,0,0,1,1,0), (0,0,0,1,1,1), (0,0,0,1,1,2), (0,0,0,1,2,0),
    (0,0,0,1,2,1), (0,0,0,1,2,2), (0,0,1,0,0,0), (0,0,1,0,0,1), (0,0,1,0,0,2), (0,0,1,0,1,0),
    (0,0,1,0,1,1), (0,0,1,0,1,2), (0,0,1,0,2,0), (0,0,1,0,2,1), (0,0,1,0,2,2), (0,0,1,1,0,0),
    (0,0,1,1,0,1), (0,0,1,1,0,2), (0,0,1,1,1,0), (0,0,1,1,1,1), (0,0,1,1,1,2), (0,0,1,1,2,0),
    (0,0,1,1,2,1), (0,0,1,1,2,2), (0,0,1,2,0,0), (0,0,1,2,0,1), (0,0,1,2,0,2), (0,0,1,2,1,0),
    (0,0,1,2,1,1), (0,0,1,2,1,2), (0,0,1,2,2,0), (0,0,1,2,2,1), (0,0,1,2,2,2), (0,1,0,0,0,0),
    (0,1,0,0,0,1), (0,1,0,0,0,2), (0,1,0,0,1,0), (0,1,0,0,1,1), (0,1,0,0,1,2), (0,1,0,0,2,0),
    (0,1,0,0,2,1), (0,1,0,0,2,2), (0,1,0,1,0,0), (0,1,0,1,0,1), (0,1,0,1,0,2), (0,1,0,1,1,0),
    (0,1,0,1,1,1), (0,1,0,1,1,2), (0,1,0,1,2,0), (0,1,0,1,2,1), (0,1,0,1,2,2), (0,1,0,2,0,0),
    (0,1,0,2,0,1), (0,1,0,2,0,2), (0,1,0,2,1,0), (0,1,0,2,1,1), (0,1,0,2,1,2), (0,1,0,2,2,0),
    (0,1,0,2,2,1), (0,1,0,2,2,2), (0,1,1,0,0,0), (0,1,1,0,0,1), (0,1,1,0,0,2), (0,1,1,0,1,0),
    (0,1,1,0,1,1), (0,1,1,0,1,2), (0,1,1,0,2,0), (0,1,1,0,2,1), (0,1,1,0,2,2), (0,1,1,1,0,0),
    (0,1,1,1,0,1), (0,1,1,1,0,2), (0,1,1,1,1,0), (0,1,1,1,1,1), (0,1,1,1,1,2), (0,1,1,1,2,0),
    (0,1,1,1,2,1), (0,1,1,1,2,2), (0,1,1,2,0,0), (0,1,1,2,0,1), (0,1,1,2,0,2), (0,1,1,2,1,0),
    (0,1,1,2,1,1), (0,1,1,2,1,2), (0,1,1,2,2,0), (0,1,1,2,2,1), (0,1,1,2,2,2), (0,1,2,0,0,0),
    (0,1,2,0,0,1), (0,1,2,0,0,2), (0,1,2,0,1,0), (0,1,2,0,1,1), (0,1,2,0,1,2), (0,1,2,0,2,0),
    (0,1,2,0,2,1), (0,1,2,0,2,2), (0,1,2,1,0,0), (0,1,2,1,0,1), (0,1,2,1,0,2), (0,1,2,1,1,0),
    (0,1,2,1,1,1), (0,1,2,1,1,2), (0,1,2,1,2,0), (0,1,2,1,2,1), (0,1,2,1,2,2), (0,1,2,2,0,0),
    (0,1,2,2,0,1), (0,1,2,2,0,2), (0,1,2,2,1,0), (0,1,2,2,1,1), (0,1,2,2,1,2), (0,1,2,2,2,0),
    (0,1,2,2,2,1), (0,1,2,2,2,2)]
private def Q : Matrix (Fin 51) (Fin 51) ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2,
    2, 0, 2, 2, 2, 2, 2, 2, 0, 0, 0, 2, 2, 0, 2, 2, 0, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 2, 2, 2, 2, 2,
    0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1,
    0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0,
    0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0,
    0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
    0, 0, 0, 0], ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    0, 0, 0, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1], ![0, 0, 0,
    0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![0, 1, 1, 1, 1, 1, 1,
    1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0], ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0,
    0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def sizes : Fin 51 → ℤ := ![432, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6]
private def weights : Fin 51 → ℤ := ![0, 192, 96, 48, 96, 48, 24, 24, 96, 24, 48, 12, 12, 12, 24,
    24, 12, 24, 96, 24, 12, 24, 48, 12, 12, 6, 12, 6, 12, 12, 6, 6, 24, 6, 24, 6, 6, 6, 12, 24, 12,
    24, 96, 24, 12, 24, 12, 6, 6, 6, 24]
private def successors : Fin 122 → Finset Col :=
  ![{(1,1,1,1,1,1), (1,1,1,1,1,2), (1,1,1,1,2,1), (1,1,1,1,2,2), (1,1,1,2,1,1), (1,1,1,2,1,2),
    (1,1,1,2,2,1), (1,1,1,2,2,2), (1,1,2,1,1,1), (1,1,2,1,1,2), (1,1,2,1,2,1), (1,1,2,1,2,2),
    (1,1,2,2,1,1), (1,1,2,2,1,2), (1,1,2,2,2,1), (1,1,2,2,2,2), (1,2,1,1,1,1), (1,2,1,1,1,2),
    (1,2,1,1,2,1), (1,2,1,1,2,2), (1,2,1,2,1,1), (1,2,1,2,1,2), (1,2,1,2,2,1), (1,2,1,2,2,2),
    (1,2,2,1,1,1), (1,2,2,1,1,2), (1,2,2,1,2,1), (1,2,2,1,2,2), (1,2,2,2,1,1), (1,2,2,2,1,2),
    (1,2,2,2,2,1), (1,2,2,2,2,2), (2,1,1,1,1,1), (2,1,1,1,1,2), (2,1,1,1,2,1), (2,1,1,1,2,2),
    (2,1,1,2,1,1), (2,1,1,2,1,2), (2,1,1,2,2,1), (2,1,1,2,2,2), (2,1,2,1,1,1), (2,1,2,1,1,2),
    (2,1,2,1,2,1), (2,1,2,1,2,2), (2,1,2,2,1,1), (2,1,2,2,1,2), (2,1,2,2,2,1), (2,1,2,2,2,2),
    (2,2,1,1,1,1), (2,2,1,1,1,2), (2,2,1,1,2,1), (2,2,1,1,2,2), (2,2,1,2,1,1), (2,2,1,2,1,2),
    (2,2,1,2,2,1), (2,2,1,2,2,2), (2,2,2,1,1,1), (2,2,2,1,1,2), (2,2,2,1,2,1), (2,2,2,1,2,2),
    (2,2,2,2,1,1), (2,2,2,2,1,2), (2,2,2,2,2,1), (2,2,2,2,2,2)}, {(1,1,1,1,2,2), (1,1,1,2,2,2),
    (1,1,2,1,2,2), (1,1,2,2,2,2), (1,2,1,1,2,2), (1,2,1,2,2,2), (1,2,2,1,2,2), (1,2,2,2,2,2),
    (2,1,1,1,2,2), (2,1,1,2,2,2), (2,1,2,1,2,2), (2,1,2,2,2,2), (2,2,1,1,2,2), (2,2,1,2,2,2),
    (2,2,2,1,2,2), (2,2,2,2,2,2)}, {(1,1,1,2,2,2), (1,1,2,2,2,2), (1,2,1,2,2,2), (1,2,2,2,2,2),
    (2,1,1,2,2,2), (2,1,2,2,2,2), (2,2,1,2,2,2), (2,2,2,2,2,2)}, {(1,1,1,2,2,0), (1,1,1,2,2,2),
    (1,1,2,2,2,0), (1,1,2,2,2,2), (1,2,1,2,2,0), (1,2,1,2,2,2), (1,2,2,2,2,0), (1,2,2,2,2,2),
    (2,1,1,2,2,0), (2,1,1,2,2,2), (2,1,2,2,2,0), (2,1,2,2,2,2), (2,2,1,2,2,0), (2,2,1,2,2,2),
    (2,2,2,2,2,0), (2,2,2,2,2,2)}, ∅, {(1,1,2,2,2,1), (1,1,2,2,2,2), (1,2,2,2,2,1), (1,2,2,2,2,2),
    (2,1,2,2,2,1), (2,1,2,2,2,2), (2,2,2,2,2,1), (2,2,2,2,2,2)}, {(1,1,2,2,2,2), (1,2,2,2,2,2),
    (2,1,2,2,2,2), (2,2,2,2,2,2)}, ∅, {(1,1,2,2,2,2), (1,2,2,2,2,2), (2,1,2,2,2,2), (2,2,2,2,2,2)},
    {(1,1,2,2,0,0), (1,1,2,2,0,2), (1,1,2,2,2,0), (1,1,2,2,2,2), (1,2,2,2,0,0), (1,2,2,2,0,2),
    (1,2,2,2,2,0), (1,2,2,2,2,2), (2,1,2,2,0,0), (2,1,2,2,0,2), (2,1,2,2,2,0), (2,1,2,2,2,2),
    (2,2,2,2,0,0), (2,2,2,2,0,2), (2,2,2,2,2,0), (2,2,2,2,2,2)}, {(1,1,2,2,0,0), (1,2,2,2,0,0),
    (2,1,2,2,0,0), (2,2,2,2,0,0)}, ∅, ∅, ∅, {(1,2,2,2,1,1), (1,2,2,2,1,2), (1,2,2,2,2,1),
    (1,2,2,2,2,2), (2,2,2,2,1,1), (2,2,2,2,1,2), (2,2,2,2,2,1), (2,2,2,2,2,2)}, {(1,2,2,2,2,2),
    (2,2,2,2,2,2)}, {(1,2,2,2,1,1), (2,2,2,2,1,1)}, {(1,2,2,2,2,2), (2,2,2,2,2,2)}, {(1,2,2,2,2,0),
    (1,2,2,2,2,2), (2,2,2,2,2,0), (2,2,2,2,2,2)}, ∅, ∅, ∅, ∅, {(1,2,2,2,2,1), (1,2,2,2,2,2),
    (2,2,2,2,2,1), (2,2,2,2,2,2)}, {(1,2,2,2,2,2), (2,2,2,2,2,2)}, ∅, {(1,2,2,0,2,2), (1,2,2,2,2,2),
    (2,2,2,0,2,2), (2,2,2,2,2,2)}, {(1,2,2,0,0,0), (1,2,2,0,0,2), (1,2,2,0,2,0), (1,2,2,0,2,2),
    (1,2,2,2,0,0), (1,2,2,2,0,2), (1,2,2,2,2,0), (1,2,2,2,2,2), (2,2,2,0,0,0), (2,2,2,0,0,2),
    (2,2,2,0,2,0), (2,2,2,0,2,2), (2,2,2,2,0,0), (2,2,2,2,0,2), (2,2,2,2,2,0), (2,2,2,2,2,2)},
    {(1,2,2,0,0,0), (1,2,2,2,0,0), (2,2,2,0,0,0), (2,2,2,2,0,0)}, ∅, {(1,2,2,0,0,0), (2,2,2,0,0,0)},
    {(1,2,2,0,0,0), (1,2,2,0,0,1), (2,2,2,0,0,0), (2,2,2,0,0,1)}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅,
    {(2,2,2,1,1,1), (2,2,2,1,1,2), (2,2,2,1,2,1), (2,2,2,1,2,2), (2,2,2,2,1,1), (2,2,2,2,1,2),
    (2,2,2,2,2,1), (2,2,2,2,2,2)}, {(2,2,2,1,2,2), (2,2,2,2,2,2)}, {(2,2,2,1,1,1), (2,2,2,2,1,1)},
    {(2,2,2,2,2,2)}, {(2,2,2,2,2,0), (2,2,2,2,2,2)}, ∅, {(2,2,2,1,1,1)}, ∅, {(2,2,2,1,1,0),
    (2,2,2,1,1,1)}, {(2,2,2,2,2,1), (2,2,2,2,2,2)}, {(2,2,2,2,2,2)}, ∅, {(2,2,2,2,2,2)},
    {(2,2,2,2,0,0), (2,2,2,2,0,2), (2,2,2,2,2,0), (2,2,2,2,2,2)}, {(2,2,2,2,0,0)}, ∅, ∅, ∅, ∅, ∅, ∅,
    ∅, ∅, ∅, ∅, ∅, ∅, {(2,2,2,2,1,1), (2,2,2,2,1,2), (2,2,2,2,2,1), (2,2,2,2,2,2)}, {(2,2,2,2,2,2)},
    {(2,2,2,2,1,1)}, {(2,2,2,2,2,2)}, {(2,2,2,2,2,0), (2,2,2,2,2,2)}, ∅, ∅, ∅, ∅, {(2,2,0,2,2,1),
    (2,2,0,2,2,2), (2,2,2,2,2,1), (2,2,2,2,2,2)}, {(2,2,0,2,2,2), (2,2,2,2,2,2)}, ∅, {(2,2,0,0,2,2),
    (2,2,0,2,2,2), (2,2,2,0,2,2), (2,2,2,2,2,2)}, {(2,2,0,0,0,0), (2,2,0,0,0,2), (2,2,0,0,2,0),
    (2,2,0,0,2,2), (2,2,0,2,0,0), (2,2,0,2,0,2), (2,2,0,2,2,0), (2,2,0,2,2,2), (2,2,2,0,0,0),
    (2,2,2,0,0,2), (2,2,2,0,2,0), (2,2,2,0,2,2), (2,2,2,2,0,0), (2,2,2,2,0,2), (2,2,2,2,2,0),
    (2,2,2,2,2,2)}, {(2,2,0,0,0,0), (2,2,0,2,0,0), (2,2,2,0,0,0), (2,2,2,2,0,0)}, ∅, {(2,2,0,0,0,0),
    (2,2,2,0,0,0)}, {(2,2,0,0,0,0), (2,2,0,0,0,1), (2,2,2,0,0,0), (2,2,2,0,0,1)}, ∅, ∅, ∅, ∅,
    {(2,2,0,0,0,0), (2,2,0,0,0,2)}, {(2,2,0,0,0,0)}, {(2,2,0,0,1,1)}, {(2,2,0,0,0,0)},
    {(2,2,0,0,0,0), (2,2,0,0,0,1), (2,2,0,0,1,0), (2,2,0,0,1,1)}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅,
    ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅]
private def relabel (e : Equiv.Perm (Fin 3)) : Col ≃ Col :=
  Equiv.prodCongr e (Equiv.prodCongr e (Equiv.prodCongr e
    (Equiv.prodCongr e (Equiv.prodCongr e e))))
private theorem column_relabel (e : Equiv.Perm (Fin 3)) (c : Col) (r : Fin 6) :
    column (relabel e c) r = e (column c r) := by
  fin_cases r <;> rfl
private theorem compatible_relabel (e : Equiv.Perm (Fin 3)) (a b : Col) :
    compatible (relabel e a) (relabel e b) ↔ compatible a b := by
  simp only [compatible, column_relabel, e.injective.ne_iff]
private theorem class_relabel : ∀ e : Equiv.Perm (Fin 3), ∀ c : Col,
    cls (relabel e c) = cls c := by decide +kernel
private theorem class_rep : ∀ c : Col, ∃ e : Equiv.Perm (Fin 3),
    relabel e c = representatives (orbit c) := by decide +kernel
set_option synthInstance.maxSize 10000 in
private theorem successors_spec : ∀ i : Fin 122,
    Finset.univ.filter (compatible (representatives i)) = successors i := by
  intro i
  fin_cases i
  all_goals
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    revert c
    decide +kernel
private theorem representative_rows : ∀ i : Fin 122, ∀ s : Fin 51,
    (∑ c : Col, if compatible (representatives i) c ∧ cls c = s then (1 : ℤ) else 0) =
      Q (cls (representatives i)) s := by
  have h : ∀ i : Fin 122, ∀ s : Fin 51,
      (∑ c ∈ successors i, if cls c = s then (1 : ℤ) else 0) =
        Q (cls (representatives i)) s := by decide +kernel
  intro i s
  rw [← h i s, ← successors_spec i, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp_all
private theorem quotient_rows (b : Col) (s : Fin 51) :
    (∑ c : Col, if compatible b c ∧ cls c = s then (1 : ℤ) else 0) = Q (cls b) s := by
  obtain ⟨e, he⟩ := class_rep b
  calc
    _ = ∑ c : Col, if compatible (relabel e b) (relabel e c) ∧
        cls (relabel e c) = s then (1 : ℤ) else 0 := by
      simp only [compatible_relabel, class_relabel]
    _ = ∑ c : Col, if compatible (representatives (orbit b)) c ∧
        cls c = s then (1 : ℤ) else 0 := by
      rw [he]
      exact (relabel e).sum_comp (fun c =>
        if compatible (representatives (orbit b)) c ∧ cls c = s then (1 : ℤ) else 0)
    _ = _ := by
      rw [representative_rows, ← he, class_relabel]
private theorem compatible_symm (a b : Col) : compatible a b ↔ compatible b a := by
  constructor <;> intro h r s hrs <;> exact (h s r ⟨hrs.2,hrs.1⟩).symm
private theorem class_sizes : ∀ s : Fin 51,
    (∑ b : Col, if cls b = s then (1 : ℤ) else 0) = sizes s := by decide +kernel
private theorem initial_weights (s : Fin 51) :
    (∑ a : Col, ∑ b : Col, if compatible a b ∧ cls b = s then (1 : ℤ) else 0) = weights s := by
  have degree (b : Col) : (∑ a : Col, if compatible b a then (1 : ℤ) else 0) =
      ∑ t : Fin 51, Q (cls b) t := by
    simp_rw [← quotient_rows]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : compatible b a <;> simp [h]
  rw [Finset.sum_comm]
  calc
    _ = ∑ b : Col, (if cls b = s then (1 : ℤ) else 0) * (∑ t : Fin 51, Q s t) := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : cls b = s
      · simp only [h, and_true, compatible_symm, ite_true, one_mul]
        rw [degree, h]
      · simp [h]
    _ = sizes s * (∑ t : Fin 51, Q s t) := by rw [← Finset.sum_mul, class_sizes]
    _ = _ := by revert s; decide +kernel

section CountBridge
attribute [local irreducible] compatible cls orbit Q weights
private def gridEquiv (n : ℕ) : (Fin 6 × Fin n → Fin 3) ≃ (Fin n → Col) where
  toFun P j := (P (0,j), P (1,j), P (2,j), P (3,j), P (4,j), P (5,j))
  invFun f p := column (f p.2) p.1
  left_inv P := by funext p; rcases p with ⟨r,j⟩; fin_cases r <;> rfl
  right_inv f := rfl
private theorem column_grid (n : ℕ) (P : Fin 6 × Fin n → Fin 3)
    (j : Fin n) (r : Fin 6) : column (gridEquiv n P j) r = P (r,j) := by
  fin_cases r <;> rfl
private theorem tail_iff (a b : Col) (xs : List Col) :
    TransferMatrix.tailGood compatible (fun _ _ _ => True) a b xs ↔
      (b :: xs).IsChain compatible := by
  induction xs generalizing a b with
  | nil => simp [TransferMatrix.tailGood]
  | cons c xs ih => simp [TransferMatrix.tailGood, List.isChain_cons_cons, ih]
private theorem good_iff (xs : List Col) :
    TransferMatrix.good compatible (fun _ _ _ => True) xs ↔ xs.IsChain compatible := by
  cases xs with
  | nil => simp [TransferMatrix.good]
  | cons a xs =>
    cases xs with
    | nil => simp [TransferMatrix.good]
    | cons b xs => simp [TransferMatrix.good, tail_iff, List.isChain_cons_cons]
private theorem grid_good (n : ℕ) (P : Fin 6 × Fin n → Fin 3) :
    Proper P ↔ TransferMatrix.good compatible (fun _ _ _ => True)
      (List.ofFn (gridEquiv n P)) := by
  rw [good_iff, List.isChain_ofFn]
  simp only [Proper, compatible, column_grid]
  constructor
  · intro h j hj; exact h ⟨j, by omega⟩ hj
  · intro h j hj; exact h j.val hj
private theorem count_transfer (n : ℕ) :
    (L (n+2) : ℤ) = dotProduct weights ((Q^n).mulVec (1 : Fin 51 → ℤ)) := by
  classical
  let he : {P : Fin 6 × Fin (n+2) → Fin 3 // Proper P} ≃
      {f : Fin (n+2) → Col //
        TransferMatrix.good compatible (fun _ _ _ => True) (List.ofFn f)} :=
    Equiv.subtypeEquiv (gridEquiv (n+2)) (fun P => grid_good (n+2) P)
  have hc : L (n+2) = Nat.card {f : Fin (n+2) → Col //
      TransferMatrix.good compatible (fun _ _ _ => True) (List.ofFn f)} := by
    rw [← Nat.card_congr he]
    simp [L, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc]
  refine TransferMatrix.cardMatrix compatible (fun _ _ _ => True) (fun _ b => cls b)
    Q weights ?_ ?_ n
  · intro a b _ s
    rw [← quotient_rows b s]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : compatible b c <;> by_cases hs : cls c = s <;> simp [h, hs]
  · intro s
    rw [← initial_weights s]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : compatible a b ∧ cls b = s <;> simp [h]

end CountBridge
private def W : Fin 26 → Fin 51 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![0, 64, 16, 8, 16, 8, 4, 4, 16, 4,
    8, 2, 2, 2, 4, 4, 2, 4, 16, 4, 2, 4, 8, 2, 2, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 2, 4,
    16, 4, 2, 4, 2, 1, 1, 1, 4], ![0, 466, 178, 136, 170, 130, 104, 104, 169, 26, 130, 80, 20, 80,
    100, 100, 80, 90, 170, 40, 20, 25, 136, 72, 32, 64, 80, 16, 20, 80, 64, 64, 104, 16, 104, 64,
    16, 64, 80, 90, 72, 84, 178, 52, 32, 40, 20, 16, 4, 16, 26], ![0, 7374, 2287, 1457, 1837, 1374,
    950, 950, 1711, 255, 1374, 644, 260, 644, 874, 906, 644, 794, 1837, 405, 195, 225, 1457, 596,
    339, 466, 644, 169, 195, 644, 466, 466, 950, 170, 950, 466, 170, 466, 644, 794, 596, 826, 2287,
    609, 339, 405, 260, 170, 25, 170, 255], ![0, 76750, 25657, 17940, 22435, 17458, 12955, 12955,
    21417, 2662, 17458, 9661, 2631, 9661, 12557, 12774, 9661, 11295, 22435, 4208, 1966, 2246, 17940,
    8748, 3548, 7374, 9661, 1711, 1966, 9661, 7374, 7374, 12955, 1837, 12955, 7374, 1837, 7374,
    9661, 11295, 8748, 11028, 25657, 6259, 3548, 4208, 2631, 1837, 225, 1837, 2662], ![0, 976496,
    313069, 207567, 256206, 199510, 142782, 142782, 238474, 30855, 199510, 102407, 33730, 102407,
    134323, 139092, 102407, 122496, 256206, 50722, 24079, 26966, 207567, 94208, 43852, 76750,
    102407, 21417, 24079, 102407, 76750, 76750, 142782, 22435, 142782, 76750, 22435, 76750, 102407,
    122496, 94208, 124440, 313069, 78844, 43852, 50722, 33730, 22435, 2246, 22435, 30855], ![0,
    11136514, 3635734, 2476886, 3072828, 2407551, 1753338, 1753338, 2894713, 357973, 2407551,
    1289565, 378702, 1289565, 1681478, 1727074, 1289565, 1522805, 3072828, 576257, 269329, 302430,
    2476886, 1176006, 494680, 976496, 1289565, 238474, 269329, 1289565, 976496, 976496, 1753338,
    256206, 1753338, 976496, 256206, 976496, 1289565, 1522805, 1176006, 1514608, 3635734, 885209,
    494680, 576257, 378702, 256206, 26966, 256206, 357973], ![0, 134342458, 43411333, 29130902,
    35971869, 28171115, 20321962, 20321962, 33614055, 4220844, 28171115, 14772248, 4595633,
    14772248, 19293191, 19922590, 14772248, 17558501, 35971869, 6901771, 3252686, 3637625, 29130902,
    13544065, 5967541, 11136514, 14772248, 2894713, 3252686, 14772248, 11136514, 11136514, 20321962,
    3072828, 20321962, 11136514, 3072828, 11136514, 14772248, 17558501, 13544065, 17678690,
    43411333, 10721847, 5967541, 6901771, 4595633, 3072828, 302430, 3072828, 4220844], ![0,
    1572060920, 510519666, 345285656, 427250281, 335049151, 242856562, 242856562, 400868847,
    49763951, 335049151, 177753791, 53530370, 177753791, 231886971, 238843814, 177753791, 210520539,
    427250281, 80708539, 37834899, 42358173, 345285656, 162513573, 69585924, 134342458, 177753791,
    33614055, 37834899, 177753791, 134342458, 134342458, 242856562, 35971869, 242856562, 134342458,
    35971869, 134342458, 177753791, 210520539, 162513573, 210607278, 510519666, 124850984, 69585924,
    80708539, 53530370, 35971869, 3637625, 35971869, 49763951], ![0, 18692413692, 6053559774,
    4076747645, 5037650817, 3949277579, 2855116523, 2855116523, 4715254062, 588151892, 3949277579,
    2082580586, 637770820, 2082580586, 2717951236, 2803707530, 2082580586, 2471160107, 5037650817,
    958591618, 450632798, 504034374, 4076747645, 1907110071, 828119128, 1572060920, 2082580586,
    400868847, 450632798, 2082580586, 1572060920, 1572060920, 2855116523, 427250281, 2855116523,
    1572060920, 427250281, 1572060920, 2082580586, 2471160107, 1907110071, 2481003036, 6053559774,
    1487256380, 828119128, 958591618, 637770820, 427250281, 42358173, 427250281, 588151892], ![0,
    220355191500, 71462625642, 48235136615, 59643086789, 46773204916, 33860371928, 33860371928,
    55895176853, 6950909607, 46773204916, 24745973466, 7508810924, 24745973466, 32286789620,
    33280536276, 24745973466, 29333021865, 59643086789, 11299648389, 5303405954, 5933916019,
    48235136615, 22641691271, 9752904879, 18692413692, 24745973466, 4715254062, 5303405954,
    24745973466, 18692413692, 18692413692, 33860371928, 5037650817, 33860371928, 18692413692,
    5037650817, 18692413692, 24745973466, 29333021865, 22641691271, 29394676380, 71462625642,
    17508506932, 9752904879, 11299648389, 7508810924, 5037650817, 504034374, 5037650817,
    6950909607], ![0, 2609538603586, 845639726035, 570085166171, 704643874178, 552528055704,
    399696040546, 399696040546, 659906485049, 82180057151, 552528055704, 291817817142, 88976108654,
    291817817142, 380788949716, 392675119164, 291817817142, 346099832982, 704643874178,
    133788821638, 62846086460, 70301030441, 570085166171, 267128396416, 115538263642, 220355191500,
    291817817142, 55895176853, 62846086460, 291817817142, 220355191500, 220355191500, 399696040546,
    59643086789, 399696040546, 220355191500, 59643086789, 220355191500, 291817817142, 346099832982,
    267128396416, 347182137608, 845639726035, 207468140051, 115538263642, 133788821638, 88976108654,
    59643086789, 5933916019, 59643086789, 82180057151], ![0, 30827616841262, 9993923274985,
    6741733991815, 8334611282564, 6535957463011, 4729907369970, 4729907369970, 7808286827179,
    971579812717, 6535957463011, 3455178329621, 1050743707160, 3455178329621, 4508286195707,
    4648000193264, 3455178329621, 4096682493979, 8334611282564, 1580519238016, 742086542200,
    830200515370, 6741733991815, 3162066659290, 1364550359227, 2609538603586, 3455178329621,
    659906485049, 742086542200, 3455178329621, 2609538603586, 2609538603586, 4729907369970,
    704643874178, 4729907369970, 2609538603586, 704643874178, 2609538603586, 3455178329621,
    4096682493979, 3162066659290, 4107269834158, 9993923274985, 2449983183121, 1364550359227,
    1580519238016, 1050743707160, 704643874178, 70301030441, 704643874178, 971579812717], ![0,
    364655605396788, 118191017038144, 79701944420756, 98522531744338, 77257827653038,
    55897885390626, 55897885390626, 92282556402416, 11487417578150, 77257827653038, 40821540116247,
    12431293776543, 40821540116247, 53265446574353, 54922733225390, 40821540116247, 48408241286418,
    98522531744338, 18694997160476, 8779866639896, 9821747483054, 79701944420756, 37363574304273,
    16142898109743, 30827616841262, 40821540116247, 7808286827179, 8779866639896, 40821540116247,
    30827616841262, 30827616841262, 55897885390626, 8334611282564, 55897885390626, 30827616841262,
    8334611282564, 30827616841262, 40821540116247, 48408241286418, 37363574304273, 48547531960548,
    118191017038144, 28985795588014, 16142898109743, 18694997160476, 12431293776543, 8334611282564,
    830200515370, 8334611282564, 11487417578150], ![0, 4310446025839450, 1397248654269010,
    942407253436732, 1165009895252930, 913581463189409, 661071098600026, 661071098600026,
    1091337945521741, 135819143027764, 913581463189409, 482846622434932, 146930773030756,
    482846622434932, 630023435061090, 649585171433624, 482846622434932, 572535743864513,
    1165009895252930, 220987502885380, 103769973980566, 116087592074086, 942407253436732,
    441913433049826, 190805088146754, 364655605396788, 482846622434932, 92282556402416,
    103769973980566, 482846622434932, 364655605396788, 364655605396788, 661071098600026,
    98522531744338, 661071098600026, 364655605396788, 98522531744338, 364655605396788,
    482846622434932, 572535743864513, 441913433049826, 574093993928254, 1397248654269010,
    342593066465445, 190805088146754, 220987502885380, 146930773030756, 98522531744338,
    9821747483054, 98522531744338, 135819143027764], ![0, 50971043227805270, 16521449010815686,
    11142173434709324, 13773602726023109, 10800903653909725, 7815111828798122, 7815111828798122,
    12901865976724141, 1605854964192962, 10800903653909725, 5707694680108460, 1737545639117443,
    5707694680108460, 7447536400842915, 7679037328305724, 5707694680108460, 6768206916328625,
    13773602726023109, 2613154486687815, 1227157088549505, 1372797979060323, 11142173434709324,
    5224027489028859, 2256347840774671, 4310446025839450, 5707694680108460, 1091337945521741,
    1227157088549505, 5707694680108460, 4310446025839450, 4310446025839450, 7815111828798122,
    1165009895252930, 7815111828798122, 4310446025839450, 1165009895252930, 4310446025839450,
    5707694680108460, 6768206916328625, 5224027489028859, 6787194123651892, 16521449010815686,
    4051381171088691, 2256347840774671, 2613154486687815, 1737545639117443, 1165009895252930,
    116087592074086, 1165009895252930, 1605854964192962], ![0, 602612498088002192,
    195333632753318977, 131741261687583499, 162857014590766627, 127709145939178451,
    92408268399353389, 92408268399353389, 152554329498596245, 18986712280320752, 127709145939178451,
    67492492238620956, 20541809642351734, 67492492238620956, 88065322420525333, 90801135373088534,
    67492492238620956, 80030941531648124, 162857014590766627, 30894478153628027, 14507720940917103,
    16229663497184151, 131741261687583499, 61771946881714995, 26675468702747250, 50971043227805270,
    67492492238620956, 12901865976724141, 14507720940917103, 67492492238620956, 50971043227805270,
    50971043227805270, 92408268399353389, 13773602726023109, 92408268399353389, 50971043227805270,
    13773602726023109, 50971043227805270, 67492492238620956, 80030941531648124, 61771946881714995,
    80251887863930444, 195333632753318977, 47896607829613274, 26675468702747250, 30894478153628027,
    20541809642351734, 13773602726023109, 1372797979060323, 13773602726023109, 18986712280320752],
    ![0, 7125232606361459472, 2309565455927222706, 1557624419356152769, 1925500334170179001,
    1509932816150283835, 1092544407119671295, 1092544407119671295, 1803659789049446724,
    224488877182495908, 1509932816150283835, 797946130841321169, 242887956122414751,
    797946130841321169, 1041176371424253420, 1073531651458570590, 797946130841321169,
    946197086422851354, 1925500334170179001, 365292534523311651, 171541041778916997,
    191900552038298072, 1557624419356152769, 730321644027180643, 315411344089362872,
    602612498088002192, 797946130841321169, 152554329498596245, 171541041778916997,
    797946130841321169, 602612498088002192, 602612498088002192, 1092544407119671295,
    162857014590766627, 1092544407119671295, 602612498088002192, 162857014590766627,
    602612498088002192, 797946130841321169, 946197086422851354, 730321644027180643,
    948831925339447628, 2309565455927222706, 566333681100654832, 315411344089362872,
    365292534523311651, 242887956122414751, 162857014590766627, 16229663497184151,
    162857014590766627, 224488877182495908], ![0, 84243265519415083208, 27306780887404188804,
    18416604235254087097, 22766298113381083071, 17852838927531716279, 12917922815815013948,
    12917922815815013948, 21325891428689300613, 2654234462510705721, 17852838927531716279,
    9434798062288682178, 2871697420593030355, 9434798062288682178, 12310697199316559716,
    12693195443555352512, 9434798062288682178, 11187618834561380764, 22766298113381083071,
    4318941534925433284, 2028148666231942632, 2268867206911622691, 18416604235254087097,
    8635165422511743307, 3729160123219625725, 7125232606361459472, 9434798062288682178,
    1803659789049446724, 2028148666231942632, 9434798062288682178, 7125232606361459472,
    7125232606361459472, 12917922815815013948, 1925500334170179001, 12917922815815013948,
    7125232606361459472, 1925500334170179001, 7125232606361459472, 9434798062288682178,
    11187618834561380764, 8635165422511743307, 11218629890120597732, 27306780887404188804,
    6695836828814058146, 3729160123219625725, 4318941534925433284, 2871697420593030355,
    1925500334170179001, 191900552038298072, 1925500334170179001, 2654234462510705721], ![0,
    996057869982369477290, 322862567448517625844, 217747524743305486968, 269175176669112887005,
    211081143790052352787, 152732948755454442180, 152732948755454442180, 252143496465022931995,
    31382255521450081678, 211081143790052352787, 111550046406819272012, 33953916947942463835,
    111550046406819272012, 145552664123037518962, 150075457184344058548, 111550046406819272012,
    132274582754944018646, 269175176669112887005, 51065365539506522689, 23980125891200006334,
    26826260905749010127, 217747524743305486968, 102096104446946799487, 44092189542070383684,
    84243265519415083208, 111550046406819272012, 21325891428689300613, 23980125891200006334,
    111550046406819272012, 84243265519415083208, 84243265519415083208, 152732948755454442180,
    22766298113381083071, 152732948755454442180, 84243265519415083208, 22766298113381083071,
    84243265519415083208, 111550046406819272012, 132274582754944018646, 102096104446946799487,
    132642138818033868278, 322862567448517625844, 79169184854768026471, 44092189542070383684,
    51065365539506522689, 33953916947942463835, 22766298113381083071, 2268867206911622691,
    22766298113381083071, 31382255521450081678], ![0, 11776788454676750026758,
    3817342840351238298233, 2574533676609289646249, 3182591752690306916592, 2495718532311747789362,
    1805843138843305477107, 1805843138843305477107, 2981225106839001639549, 371046929005568426155,
    2495718532311747789362, 1318920437430887103134, 401449759424056905651, 1318920437430887103134,
    1720952189734172755449, 1774425143697438597256, 1318920437430887103134, 1563955498168881919756,
    3182591752690306916592, 603766294195092423367, 283525751986473013673, 317176874714834718042,
    2574533676609289646249, 1207139013772421830077, 521318673134135819000, 996057869982369477290,
    1318920437430887103134, 252143496465022931995, 283525751986473013673, 1318920437430887103134,
    996057869982369477290, 996057869982369477290, 1805843138843305477107, 269175176669112887005,
    1805843138843305477107, 996057869982369477290, 269175176669112887005, 996057869982369477290,
    1318920437430887103134, 1563955498168881919756, 1207139013772421830077, 1568295614746818241412,
    3817342840351238298233, 936046513926286224967, 521318673134135819000, 603766294195092423367,
    401449759424056905651, 269175176669112887005, 26826260905749010127, 269175176669112887005,
    371046929005568426155], ![0, 139242867334744691949288, 45134291070060154558774,
    30439886641164945270957, 37629208004539549142340, 29507989691366945177310,
    21351256724327584887832, 21351256724327584887832, 35248313317715966135990,
    4387060673586707071674, 29507989691366945177310, 15594131295027988324991,
    4746547250859188836348, 15594131295027988324991, 20347520649305512848191,
    20979769750126044864636, 15594131295027988324991, 18491299586763793020004,
    37629208004539549142340, 7138630082729969405663, 3352272035844570065704, 3750145225755887501986,
    30439886641164945270957, 14272506986988497816120, 6163816859529308556141,
    11776788454676750026758, 15594131295027988324991, 2981225106839001639549,
    3352272035844570065704, 15594131295027988324991, 11776788454676750026758,
    11776788454676750026758, 21351256724327584887832, 3182591752690306916592,
    21351256724327584887832, 11776788454676750026758, 3182591752690306916592,
    11776788454676750026758, 15594131295027988324991, 18491299586763793020004,
    14272506986988497816120, 18542650662997684202738, 45134291070060154558774,
    11067360801953788228182, 6163816859529308556141, 7138630082729969405663, 4746547250859188836348,
    3182591752690306916592, 317176874714834718042, 3182591752690306916592, 4387060673586707071674],
    ![0, 1646330485235039379213834, 533643251075433232037777, 359905069508247422010323,
    444907959752347152500289, 348887001357319470518995, 252446253050509340921359,
    252446253050509340921359, 416757807857030363318163, 51870255348869976115693,
    348887001357319470518995, 184377158404804846508062, 56120507591303342162344,
    184377158404804846508062, 240578810276818789295018, 248054100137862685269574,
    184377158404804846508062, 218631695347030980521720, 444907959752347152500289,
    84403212078572191755667, 39635373991302673207664, 44339611539604214997380,
    359905069508247422010323, 168750857026111637126598, 72877521322255515278330,
    139242867334744691949288, 184377158404804846508062, 35248313317715966135990,
    39635373991302673207664, 184377158404804846508062, 139242867334744691949288,
    139242867334744691949288, 252446253050509340921359, 37629208004539549142340,
    252446253050509340921359, 139242867334744691949288, 37629208004539549142340,
    139242867334744691949288, 184377158404804846508062, 218631695347030980521720,
    168750857026111637126598, 219238616467604627168544, 533643251075433232037777,
    130854249976100577268861, 72877521322255515278330, 84403212078572191755667,
    56120507591303342162344, 37629208004539549142340, 3750145225755887501986,
    37629208004539549142340, 51870255348869976115693], ![0, 19465347574823851072353570,
    6309515122972229319071881, 4255324080886435701442099, 5260351494288049634345451,
    4125051185487247662616862, 2984786765571067185762223, 2984786765571067185762223,
    4927517435524776511196165, 613286157361826232461000, 4125051185487247662616862,
    2179973736310472611251611, 663539655099378133022009, 2179973736310472611251611,
    2844471237362006420558249, 2932855603853510470457932, 2179973736310472611251611,
    2584981245259095423932950, 5260351494288049634345451, 997939235036819683689812,
    468628063205900339433856, 524248463780526203051535, 4255324080886435701442099,
    1995217486592358849732829, 861665767609377515818452, 1646330485235039379213834,
    2179973736310472611251611, 416757807857030363318163, 468628063205900339433856,
    2179973736310472611251611, 1646330485235039379213834, 1646330485235039379213834,
    2984786765571067185762223, 444907959752347152500289, 2984786765571067185762223,
    1646330485235039379213834, 444907959752347152500289, 1646330485235039379213834,
    2179973736310472611251611, 2584981245259095423932950, 1995217486592358849732829,
    2592158588087541005521398, 6309515122972229319071881, 1547152537638543457613759,
    861665767609377515818452, 997939235036819683689812, 663539655099378133022009,
    444907959752347152500289, 44339611539604214997380, 444907959752347152500289,
    613286157361826232461000], ![0, 230147747153889639937998372, 74600312400306051718216751,
    50312680425124724272550474, 62195594820347592919227965, 48772410715881790325472059,
    35290538272970565727213001, 35290538272970565727213001, 58260353912097575483940129,
    7251167256311295860520654, 48772410715881790325472059, 25774862697796080391425451,
    7845332739547145058278401, 25774862697796080391425451, 33631530358406853168111091,
    34676536408855850716018730, 25774862697796080391425451, 30563453538382706187064322,
    62195594820347592919227965, 11799094322211472061692428, 5540803592886602743657165,
    6198429361788033191115545, 50312680425124724272550474, 23590398760311098734970432,
    10187868929812826145541616, 19465347574823851072353570, 25774862697796080391425451,
    4927517435524776511196165, 5540803592886602743657165, 25774862697796080391425451,
    19465347574823851072353570, 19465347574823851072353570, 35290538272970565727213001,
    5260351494288049634345451, 35290538272970565727213001, 19465347574823851072353570,
    5260351494288049634345451, 19465347574823851072353570, 25774862697796080391425451,
    30563453538382706187064322, 23590398760311098734970432, 30648305549651856868045226,
    74600312400306051718216751, 18292691661462882200445316, 10187868929812826145541616,
    11799094322211472061692428, 7845332739547145058278401, 5260351494288049634345451,
    524248463780526203051535, 5260351494288049634345451, 7251167256311295860520654], ![0,
    2721144483712775410216580228, 882034289908851540602002272, 594870175973588506111831752,
    735367346271816278425217820, 576658805048319722356290293, 417256334799668008847993562,
    417256334799668008847993562, 688839094594043871562528196, 85733922097233700915693103,
    576658805048319722356290293, 304748059554195691656215123, 92759048358730299106292287,
    304748059554195691656215123, 397641063615964625574877190, 409996677504153600242477100,
    304748059554195691656215123, 361365803009624627039965583, 735367346271816278425217820,
    139506210310967936325381176, 65511521168408871344460783, 73286936888500693408032972,
    594870175973588506111831752, 278920157869771430263470431, 120455948732445168403168094,
    230147747153889639937998372, 304748059554195691656215123, 58260353912097575483940129,
    65511521168408871344460783, 304748059554195691656215123, 230147747153889639937998372,
    230147747153889639937998372, 417256334799668008847993562, 62195594820347592919227965,
    417256334799668008847993562, 230147747153889639937998372, 62195594820347592919227965,
    230147747153889639937998372, 304748059554195691656215123, 361365803009624627039965583,
    278920157869771430263470431, 362369104994509071304961220, 882034289908851540602002272,
    216283073911199614490507150, 120455948732445168403168094, 139506210310967936325381176,
    92759048358730299106292287, 62195594820347592919227965, 6198429361788033191115545,
    62195594820347592919227965, 85733922097233700915693103]]
private def coefficients : Fin 24 → ℤ := ![420, -906, -9672, 19997, 81406, -166928, -312941, 690388,
    557502, -1524689, -363389, 1850161, -155206, -1225001, 333692, 426135, -161805, -75471, 32291,
    7168, -2896, -365, 103, 7]
private theorem table_zero : W 0 = (1 : Fin 51 → ℤ) := by exact List.ofFn_inj.mp rfl
private theorem table_steps : ∀ k : Fin 25, W k.succ = Q.mulVec (W k.castSucc) := by
  intro k
  fin_cases k <;> exact List.ofFn_inj.mp rfl
private theorem powers_table : ∀ k : Fin 26,
    (Q^k.val).mulVec (1 : Fin 51 → ℤ) = W k :=
  TransferMatrix.tabulatedPowers Q 25 W table_zero table_steps
private theorem power_polynomial : (Q^(1+24)).mulVec (1 : Fin 51 → ℤ) =
    ∑ j : Fin 24, coefficients j • (Q^(1+j.val)).mulVec (1 : Fin 51 → ℤ) := by
  rw [show 1+24 = (25 : Fin 26).val from rfl, powers_table]
  have hh (j : Fin 24) : (Q^(1+j.val)).mulVec (1 : Fin 51 → ℤ) =
      W ⟨1+j.val, by omega⟩ := powers_table ⟨1+j.val, by omega⟩
  simp_rw [hh]
  exact List.ofFn_inj.mp rfl
theorem initial_values : ∀ k : Fin 26, (L (k.val+2) : ℤ) =
  ![1458, 23346, 235824, 2986152, 33994188, 409408542, 4791504648, 56948232390, 671408641884,
    7950212281224, 93923210426688, 1110971521842576, 13132515793768920, 155290791915166218,
    1835954950424998884, 21708106678579996182, 256660237490505696204, 3034643594159596884672,
    35879810376487028900160, 424224888649277811420648, 5015800426651629427544760,
    59304188625218088516497046, 701180686835907546543927912, 8290387169164139913131170926,
    98021089474277074253102673060, 1158948987790395127011466558572] k := by
  intro k
  rw [count_transfer, powers_table]
  fin_cases k <;> rfl
private theorem recurrence_core (n : ℕ) : (L (n+27) : ℤ) + 6 =
    ∑ j : Fin 24, coefficients j * ((L (n+j.val+3) : ℤ) + 6) := by
  have h := TransferMatrix.scalarRelationShift Q weights 24 1 coefficients power_polynomial n
  have ht (k : ℕ) : dotProduct weights ((Q^(k+1)).mulVec (1 : Fin 51 → ℤ)) =
      (L (k+3) : ℤ) := (count_transfer (k+1)).symm
  have hh (j : Fin 24) : n+1+j.val = (n+j.val)+1 := by omega
  simp_rw [hh] at h
  rw [show n+1+24 = (n+24)+1 from by omega] at h
  simp_rw [ht] at h
  norm_num [coefficients, Fin.sum_univ_succ, Nat.add_assoc] at h ⊢
  linear_combination h
theorem recurrence (n : ℕ) : (L (n+27) : ℤ) + 6 =
    7 * ((L (n+26) : ℤ) + 6) + 103 * ((L (n+25) : ℤ) + 6) - 365 * ((L (n+24) : ℤ) + 6) - 2896 * ((L
      (n+23) : ℤ) + 6) + 7168 * ((L (n+22) : ℤ) + 6) + 32291 * ((L (n+21) : ℤ) + 6) - 75471 * ((L
      (n+20) : ℤ) + 6) - 161805 * ((L (n+19) : ℤ) + 6) + 426135 * ((L (n+18) : ℤ) + 6) + 333692 *
      ((L (n+17) : ℤ) + 6) - 1225001 * ((L (n+16) : ℤ) + 6) - 155206 * ((L (n+15) : ℤ) + 6) +
      1850161 * ((L (n+14) : ℤ) + 6) - 363389 * ((L (n+13) : ℤ) + 6) - 1524689 * ((L (n+12) : ℤ) +
      6) + 557502 * ((L (n+11) : ℤ) + 6) + 690388 * ((L (n+10) : ℤ) + 6) - 312941 * ((L (n+9) : ℤ) +
      6) - 166928 * ((L (n+8) : ℤ) + 6) + 81406 * ((L (n+7) : ℤ) + 6) + 19997 * ((L (n+6) : ℤ) + 6)
      - 9672 * ((L (n+5) : ℤ) + 6) - 906 * ((L (n+4) : ℤ) + 6) + 420 * ((L (n+3) : ℤ) + 6) := by
  have h := recurrence_core n
  norm_num [coefficients, Fin.sum_univ_succ, Nat.add_assoc] at h
  linear_combination h
end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer
