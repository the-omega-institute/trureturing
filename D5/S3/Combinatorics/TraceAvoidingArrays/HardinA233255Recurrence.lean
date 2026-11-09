/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255Recurrence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233255Recurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original positive-height seven-column count obeys Hardin's recurrence. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix

/-! The finite certificate is checked against every actual row fibre before propagation. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence
open HardinA233255PairTransfer (a)
open HardinA233255ShapeSymmetry (K F literal_canonical_bridge)
open TransferMatrix (tabulatedPowers scalarRelationShift)

private def table : Matrix (Fin 16) (Fin 16) ℤ :=
  ![![5, 5, 3, 3, 4, 4, 2, 2, 0, 0, 1, 1, 3, 3, 3, 3],
    ![4, 4, 3, 3, 4, 4, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1],
    ![1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 2, 2],
    ![3, 3, 3, 3, 3, 3, 2, 2, 0, 0, 2, 2, 3, 3, 3, 3],
    ![4, 4, 2, 2, 4, 4, 2, 2, 0, 0, 1, 1, 3, 3, 1, 1],
    ![4, 4, 2, 2, 4, 4, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3],
    ![0, 0, 2, 2, 0, 0, 2, 2, 3, 3, 2, 2, 0, 0, 2, 2],
    ![2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2],
    ![1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1],
    ![0, 0, 1, 1, 0, 0, 1, 1, 3, 3, 1, 1, 0, 0, 1, 1],
    ![2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3],
    ![2, 2, 1, 1, 2, 2, 1, 1, 0, 0, 2, 2, 3, 3, 2, 2],
    ![3, 3, 3, 3, 3, 3, 1, 1, 0, 0, 1, 1, 3, 3, 3, 3],
    ![2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 2, 1, 1],
    ![2, 2, 3, 3, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2],
    ![4, 4, 3, 3, 2, 2, 1, 1, 0, 0, 2, 2, 3, 3, 3, 3]]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem table_matches : K = table := by
  have h : List.ofFn (fun i : Fin 16 => List.ofFn (fun j : Fin 16 => K i j)) =
      List.ofFn (fun i : Fin 16 => List.ofFn (fun j : Fin 16 => table i j)) := by
    decide +kernel
  exact funext fun i => List.ofFn_inj.mp (congrFun (List.ofFn_inj.mp h) i)

private def T : Matrix (Fin 17) (Fin 17) ℤ :=
  Fin.cons (Fin.cons 128 (fun _ => 0)) (fun i => Fin.cons 0 (fun j => 128 * K i j))
private def U (n : ℕ) : Fin 17 → ℤ := Fin.cons ((128 : ℤ)^n) (F n)
private def weights : Fin 17 → ℤ := Fin.cons 16 (fun _ => 32)
private def W : Fin 6 → Fin 17 → ℤ :=
  ![![1, 1, 1,
      1, 1, 1,
      1, 1, 1,
      1, 1, 1,
      1, 1, 1,
      1, 1],
    ![128, 5376, 4608,
      3584, 4864, 4352,
      4864, 2816, 4096,
      2816, 1792, 3584,
      3328, 4352, 3328,
      3840, 4608],
    ![16384, 23199744, 19365888,
      13369344, 20348928, 18677760,
      20447232, 9633792, 16220160,
      10321920, 5701632, 14057472,
      13762560, 18579456, 13172736,
      15138816, 19562496],
    ![2097152, 95919538176, 79574335488,
      53187969024, 83575701504, 77271662592,
      84141932544, 37408997376, 65909293056,
      41372614656, 21781020672, 57151586304,
      56736350208, 76705431552, 53338963968,
      61341696000, 80706797568],
    ![268435456, 392987896971264, 325598249484288,
      216142618558464, 341978181009408, 316654516961280,
      344456914010112, 151231704072192, 269181706567680,
      168582835077120, 87741350019072, 233493749563392,
      232435576995840, 314175783960576, 217563178991616,
      250323042041856, 330555715485696],
    ![34359738368, 1607212565010579456, 1331275484771647488,
      882583412454457344, 1398271202153201664, 1295089113992527872,
      1408540984354013184, 616916114416336896, 1100263831168352256,
      688804589822017536, 357672300746637312, 954471887860137984,
      950625590027747328, 1284819331791716352, 889006896822878208,
      1022998331585986560, 1351815049173270528]]
private def coefficients : Fin 5 → ℤ := ![27831388078080, -478351982592, 2774532096, -6438912, 5504]

private theorem F_succ (n : ℕ) (i : Fin 16) :
    F (n + 1) i = 128 * ∑ j : Fin 16, K i j * F n j := by
  unfold F
  rw [pow_succ' (128 : ℤ), pow_succ' K, ← Matrix.mulVec_mulVec]
  change (128 * 128^n) * (∑ j : Fin 16, K i j * (K^n).mulVec (1 : Fin 16 → ℤ) j) =
    128 * ∑ j : Fin 16, K i j * (128^n * (K^n).mulVec (1 : Fin 16 → ℤ) j)
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem U_powers (n : ℕ) : (T^n).mulVec (1 : Fin 17 → ℤ) = U n := by
  induction n with
  | zero =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [U, Matrix.one_mulVec]
    · simp [U, F, Matrix.one_mulVec]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [T, U, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pow_succ]
      ring
    · change (∑ k : Fin 17, T j.succ k * U n k) = F (n + 1) j
      rw [Fin.sum_univ_succ]
      simp only [T, U, Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add]
      rw [F_succ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

private theorem count_transfer (n : ℕ) :
    (a ⟨n + 1, Nat.succ_pos n⟩ : ℤ) = dotProduct weights ((T^n).mulVec (1 : Fin 17 → ℤ)) := by
  rw [U_powers, literal_canonical_bridge]
  change (16 : ℤ) * 128^n + 32 * ∑ i : Fin 16, F n i =
    ∑ i : Fin 17, weights i * U n i
  conv_rhs => rw [Fin.sum_univ_succ]
  simp only [weights, U, Fin.cons_zero, Fin.cons_succ]
  rw [Finset.mul_sum]

private theorem table_zero : W 0 = (1 : Fin 17 → ℤ) := by
  exact List.ofFn_inj.mp rfl

private theorem table_steps : ∀ k : Fin 5, W k.succ = T.mulVec (W k.castSucc) := by
  intro k
  simp only [T, table_matches]
  fin_cases k <;> exact List.ofFn_inj.mp rfl

private theorem powers_table : ∀ k : Fin 6,
    (T^k.val).mulVec (1 : Fin 17 → ℤ) = W k :=
  tabulatedPowers T 5 W table_zero table_steps

private theorem power_polynomial : (T^5).mulVec (1 : Fin 17 → ℤ) =
    ∑ j : Fin 5, coefficients j • (T^(0+j.val)).mulVec (1 : Fin 17 → ℤ) := by
  simp only [Nat.zero_add]
  calc
    _ = W 5 := powers_table 5
    _ = ∑ j : Fin 5, coefficients j • W ⟨j.val, by omega⟩ := by
      exact List.ofFn_inj.mp rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [powers_table ⟨j.val, by omega⟩]

private theorem shifted_recurrence (m : ℕ) :
    (a ⟨m + 6, by omega⟩ : ℤ) =
      5504 * (a ⟨m + 5, by omega⟩ : ℤ) -
      6438912 * (a ⟨m + 4, by omega⟩ : ℤ) +
      2774532096 * (a ⟨m + 3, by omega⟩ : ℤ) -
      478351982592 * (a ⟨m + 2, by omega⟩ : ℤ) +
      27831388078080 * (a ⟨m + 1, by omega⟩ : ℤ) := by
  have h := scalarRelationShift T weights 5 0 coefficients power_polynomial m
  simp_rw [← count_transfer] at h
  norm_num [coefficients, Fin.sum_univ_succ, Nat.add_assoc] at h
  linear_combination h

/-- Hardin's literal recurrence, precisely on the all-positive-predecessor domain. -/
theorem result (n : ℕ) (hn : 6 ≤ n) :
    (a ⟨n, by omega⟩ : ℤ) =
      5504 * (a ⟨n - 1, by omega⟩ : ℤ) -
      6438912 * (a ⟨n - 2, by omega⟩ : ℤ) +
      2774532096 * (a ⟨n - 3, by omega⟩ : ℤ) -
      478351982592 * (a ⟨n - 4, by omega⟩ : ℤ) +
      27831388078080 * (a ⟨n - 5, by omega⟩ : ℤ) := by
  have h := shifted_recurrence (n - 6)
  simpa only [show n - 6 + 6 = n from by omega,
    show n - 6 + 5 = n - 1 from by omega,
    show n - 6 + 4 = n - 2 from by omega,
    show n - 6 + 3 = n - 3 from by omega,
    show n - 6 + 2 = n - 4 from by omega,
    show n - 6 + 1 = n - 5 from by omega] using h

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence
