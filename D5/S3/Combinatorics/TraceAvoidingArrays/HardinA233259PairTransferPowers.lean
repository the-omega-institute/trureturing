/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.power_polynomial; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.powers_table
   digest: Four-row transfer-power and scalar-polynomial certificate. -/
/-
admission_basis: escape-witness
escape_witness: table_steps certifies the eight concrete power steps; power_polynomial certifies the concrete annihilation used by Recurrence.shifted
W: proof_shape=bind-only; consumers=table_zero, table_steps, powers_table, power_polynomial
coefficients: proof_shape=bind-only; consumers=power_polynomial, HardinA233259PairTransferRecurrence.shifted
table_zero: proof_shape=bind-only; consumers=powers_table
table_steps: proof_shape=content; consumers=powers_table
powers_table: proof_shape=content; consumers=power_polynomial, HardinA233259PairTransferBase.initial_values
power_polynomial: proof_shape=content; consumers=HardinA233259PairTransferRecurrence.shifted
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
open HardinA233259PairTransferCore

def W : Fin 9 → Fin 14 → ℤ :=
  ![![1,1,1,1,1,1,1,1,1,1,1,1,1,1],
    ![16,8,4,8,4,4,2,2,4,8,4,2,2,4],
    ![108,54,36,54,18,36,24,12,30,54,24,6,12,18],
    ![792,360,246,360,96,252,162,72,210,396,150,24,84,108],
    ![5556,2478,1758,2496,588,1758,1152,456,1476,2778,1002,132,606,738],
    ![38904,17112,12288,17412,3954,12288,8034,3084,10248,19452,6864,870,4254,5124],
    ![271476,119070,85716,121410,27360,85716,56016,21366,71388,135738,47682,5994,29700,35694],
    ![1893060,829818,597672,846486,190458,597672,390546,148770,497628,946530,332190,41688,207126,248814],
    ![13198824,5784984,4167036,5901696,1327446,4167036,2722878,1036944,3469320,6599412,2315664,290502,1444158,1734660]]

def coefficients : Fin 4 → ℤ := ![-6, 21, -24, 10]
theorem table_zero : W 0 = (1 : Fin 14 → ℤ) := by exact List.ofFn_inj.mp rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem table_steps : ∀ k : Fin 8, W k.succ = Q.mulVec (W k.castSucc) := by
  intro k
  fin_cases k <;> exact List.ofFn_inj.mp rfl
theorem powers_table : ∀ k : Fin 9,
    (Q^k.val).mulVec (1 : Fin 14 → ℤ) = W k :=
  TransferMatrix.tabulatedPowers Q 8 W table_zero table_steps
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem power_polynomial : (Q^(4+4)).mulVec (1 : Fin 14 → ℤ) =
    ∑ j : Fin 4, coefficients j • (Q^(4+j.val)).mulVec (1 : Fin 14 → ℤ) := by
  rw [show 4+4 = (8 : Fin 9).val from rfl, powers_table]
  have hh (j : Fin 4) : (Q^(4+j.val)).mulVec (1 : Fin 14 → ℤ) =
      W ⟨4+j.val, by omega⟩ := powers_table ⟨4+j.val, by omega⟩
  simp_rw [hh]
  simp only [coefficients, Fin.sum_univ_succ]
  exact List.ofFn_inj.mp rfl

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
