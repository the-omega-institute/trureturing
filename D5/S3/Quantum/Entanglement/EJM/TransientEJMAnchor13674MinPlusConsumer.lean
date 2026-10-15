/- Prepared actual original anchor13/4/674 MinPlus consumer; uncompiled.
All original 32 factors, full compatible events on Fin20/Fin4, F1/F2 and
scale 6987435 are retained. This independent source consumes the six actual
inequality_at receipts and all eighteen public group normalizations.
Its initial lower bound is reconstructed from original Group.bound proofs;
no existing final prefix bound or private VE step/final bound is used.
Initial normalization offsets sum to 21271424; every bucket offset is zero.
The terminal lower minimum -45112 is proved over its actual four entries.
No native verification JSON or producer minimum is a proof premise.
Source-owned Reg evidence and current binding remain unfinished under
https://github.com/the-omega-institute/trureturing/issues/16309.
No raw Accepted or complete frontier coverage is asserted. -/

import D5.S0.Certificates.FiniteMinPlusElimination
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VERoot

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674MinPlusConsumer
open D5.S0.Certificates.FiniteMinPlusElimination
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Compatible)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (Assignment)
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)
open D5.S3.Quantum.Entanglement.EJMInflationScore (score)

/-- Every full original event compatible with this actual prefix is retained. -/
def Context := { e : Assignment // Compatible (prefixPartial 13 4) e }

/-- Lift normalized units through the unchanged original positive scale. -/
def lift (f : Assignment → ℤ) : Factor Context := fun e => (6987435 : ℤ) * f e.val

/-- Literal labels preserve each actual group and bucket-output occurrence. -/
def factor : ℕ → Factor Context
  | 0 => lift TransientEJMAnchor13674VEGroups.lowerAt00
  | 1 => lift TransientEJMAnchor13674VEGroups.lowerAt01
  | 2 => lift TransientEJMAnchor13674VEGroups.lowerAt02
  | 3 => lift TransientEJMAnchor13674VEGroups.lowerAt03
  | 4 => lift TransientEJMAnchor13674VEGroups.lowerAt04
  | 5 => lift TransientEJMAnchor13674VEGroups.lowerAt05
  | 6 => lift TransientEJMAnchor13674VEGroups.lowerAt06
  | 7 => lift TransientEJMAnchor13674VEGroups.lowerAt07
  | 8 => lift TransientEJMAnchor13674VEGroups.lowerAt08
  | 9 => lift TransientEJMAnchor13674VEGroups.lowerAt09
  | 10 => lift TransientEJMAnchor13674VEGroups.lowerAt10
  | 11 => lift TransientEJMAnchor13674VEGroups.lowerAt11
  | 12 => lift TransientEJMAnchor13674VEGroups.lowerAt12
  | 13 => lift TransientEJMAnchor13674VEGroups.lowerAt13
  | 14 => lift TransientEJMAnchor13674VEGroups.lowerAt14
  | 15 => lift TransientEJMAnchor13674VEGroups.lowerAt15
  | 16 => lift TransientEJMAnchor13674VEGroups.lowerAt16
  | 17 => lift TransientEJMAnchor13674VEGroups.lowerAt17
  | 18 => lift TransientEJMAnchor13674VEBucket00.lowerAt
  | 19 => lift TransientEJMAnchor13674VEBucket01.lowerAt
  | 20 => lift TransientEJMAnchor13674VEBucket02.lowerAt
  | 21 => lift TransientEJMAnchor13674VEBucket03.lowerAt
  | 22 => lift TransientEJMAnchor13674VEBucket04.lowerAt
  | 23 => lift TransientEJMAnchor13674VEBucket05.lowerAt
  | _ => fun _ => 0

/-- The eighteen normalized original groups, with all their actual offsets. -/
def initial : State Context :=
  ⟨(6987435 : ℤ) * 21271424, [factor 0, factor 1, factor 2, factor 3, factor 4, factor 5, factor 6, factor 7, factor 8, factor 9, factor 10, factor 11, factor 12, factor 13, factor 14, factor 15, factor 16, factor 17]⟩

def operation0 : Elimination Context :=
  ⟨[factor 0, factor 2, factor 4, factor 5, factor 8, factor 11, factor 15, factor 16], [factor 1, factor 3, factor 6, factor 7, factor 9, factor 10, factor 12, factor 13, factor 14, factor 17], 0, factor 18⟩

def operation1 : Elimination Context :=
  ⟨[factor 3, factor 6, factor 7, factor 12, factor 18], [factor 1, factor 9, factor 10, factor 13, factor 14, factor 17], 0, factor 19⟩

def operation2 : Elimination Context :=
  ⟨[factor 9, factor 17, factor 19], [factor 1, factor 10, factor 13, factor 14], 0, factor 20⟩

def operation3 : Elimination Context :=
  ⟨[factor 20], [factor 1, factor 10, factor 13, factor 14], 0, factor 21⟩

def operation4 : Elimination Context :=
  ⟨[factor 1, factor 10, factor 14, factor 21], [factor 13], 0, factor 22⟩

def operation5 : Elimination Context :=
  ⟨[factor 13, factor 22], [], 0, factor 23⟩

def state1 : State Context := next initial operation0

def state2 : State Context := next state1 operation1

def state3 : State Context := next state2 operation2

def state4 : State Context := next state3 operation3

def state5 : State Context := next state4 operation4

def state6 : State Context := next state5 operation5

def operations : List (Elimination Context) :=
  [operation0, operation1, operation2, operation3, operation4, operation5]

private theorem step0_valid : ValidStep initial operation0 := by
  constructor
  · have literal : ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] : List ℕ).Perm
        ([0, 2, 4, 5, 8, 11, 15, 16] ++ [1, 3, 6, 7, 9, 10, 12, 13, 14, 17]) := by
      decide +kernel
    simpa only [initial, operation0, next, List.map_append, List.map_cons, List.map_nil] using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (TransientEJMAnchor13674VEBucket00.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation0, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem step1_valid : ValidStep state1 operation1 := by
  constructor
  · have literal : ([18, 1, 3, 6, 7, 9, 10, 12, 13, 14, 17] : List ℕ).Perm
        ([3, 6, 7, 12, 18] ++ [1, 9, 10, 13, 14, 17]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, state1, next, List.map_append, List.map_cons, List.map_nil] using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (TransientEJMAnchor13674VEBucket01.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation1, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem step2_valid : ValidStep state2 operation2 := by
  constructor
  · have literal : ([19, 1, 9, 10, 13, 14, 17] : List ℕ).Perm
        ([9, 17, 19] ++ [1, 10, 13, 14]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, state1, state2, next, List.map_append, List.map_cons, List.map_nil] using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (TransientEJMAnchor13674VEBucket02.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation2, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem step3_valid : ValidStep state3 operation3 := by
  constructor
  · have literal : ([20, 1, 10, 13, 14] : List ℕ).Perm
        ([20] ++ [1, 10, 13, 14]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, state1, state2, state3, next, List.map_append, List.map_cons, List.map_nil] using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (TransientEJMAnchor13674VEBucket03.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation3, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem step4_valid : ValidStep state4 operation4 := by
  constructor
  · have literal : ([21, 1, 10, 13, 14] : List ℕ).Perm
        ([1, 10, 14, 21] ++ [13]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, operation4, state1, state2, state3, state4, next, List.map_append, List.map_cons, List.map_nil] using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (TransientEJMAnchor13674VEBucket04.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation4, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem step5_valid : ValidStep state5 operation5 := by
  constructor
  · have literal : ([22, 13] : List ℕ).Perm
        ([13, 22] ++ []) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, operation4, operation5, state1, state2, state3, state4, state5, next, List.map_append, List.map_cons, List.map_nil] using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (TransientEJMAnchor13674VEBucket05.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation5, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem valid_program : ValidProgram initial operations := by
  change ValidStep initial operation0 ∧ ValidStep state1 operation1 ∧
    ValidStep state2 operation2 ∧ ValidStep state3 operation3 ∧
      ValidStep state4 operation4 ∧ ValidStep state5 operation5 ∧ True
  exact ⟨step0_valid, step1_valid, step2_valid, step3_valid, step4_valid, step5_valid, trivial⟩

/- Reuse the existing source proof of exact original 32-factor coverage;
only its private namespace ownership changes. -/
private theorem component_sum (e : Assignment) :
    TransientEJMAnchor13674Group02.score e + TransientEJMAnchor13674Group11.score e + TransientEJMAnchor13674Group05.score e + TransientEJMAnchor13674Group08.score e + TransientEJMAnchor13674Group04.score e + TransientEJMAnchor13674Group06.score e + TransientEJMAnchor13674Group10.score e + TransientEJMAnchor13674Group14.score e + TransientEJMAnchor13674Group01.score e + TransientEJMAnchor13674Group16.score e + TransientEJMAnchor13674Group13.score e + TransientEJMAnchor13674Group00.score e + TransientEJMAnchor13674Group15.score e + TransientEJMAnchor13674Group17.score e + TransientEJMAnchor13674Group12.score e + TransientEJMAnchor13674Group03.score e + TransientEJMAnchor13674Group07.score e + TransientEJMAnchor13674Group09.score e = D5.S3.Quantum.Entanglement.EJMInflationScore.score F1 F2 e := by
  simp only [TransientEJMAnchor13674Factor00.score, TransientEJMAnchor13674Factor01.score, TransientEJMAnchor13674Factor02.score, TransientEJMAnchor13674Factor03.score, TransientEJMAnchor13674Factor04.score, TransientEJMAnchor13674Factor05.score, TransientEJMAnchor13674Factor06.score, TransientEJMAnchor13674Factor07.score, TransientEJMAnchor13674Factor08.score, TransientEJMAnchor13674Factor09.score, TransientEJMAnchor13674Factor10.score, TransientEJMAnchor13674Factor11.score, TransientEJMAnchor13674Factor12.score, TransientEJMAnchor13674Factor13.score, TransientEJMAnchor13674Factor14.score, TransientEJMAnchor13674Factor15.score, TransientEJMAnchor13674Factor16.score, TransientEJMAnchor13674Factor17.score, TransientEJMAnchor13674Factor18.score, TransientEJMAnchor13674Factor19.score, TransientEJMAnchor13674Factor20.score, TransientEJMAnchor13674Factor21.score, TransientEJMAnchor13674Factor22.score, TransientEJMAnchor13674Factor23.score, TransientEJMAnchor13674Factor24.score, TransientEJMAnchor13674Factor25.score, TransientEJMAnchor13674Factor26.score, TransientEJMAnchor13674Factor27.score, TransientEJMAnchor13674Factor28.score, TransientEJMAnchor13674Factor29.score, TransientEJMAnchor13674Factor30.score, TransientEJMAnchor13674Factor31.score, TransientEJMAnchor13674Group00.score, TransientEJMAnchor13674Group01.score, TransientEJMAnchor13674Group02.score, TransientEJMAnchor13674Group03.score, TransientEJMAnchor13674Group04.score, TransientEJMAnchor13674Group05.score, TransientEJMAnchor13674Group06.score, TransientEJMAnchor13674Group07.score, TransientEJMAnchor13674Group08.score, TransientEJMAnchor13674Group09.score, TransientEJMAnchor13674Group10.score, TransientEJMAnchor13674Group11.score, TransientEJMAnchor13674Group12.score, TransientEJMAnchor13674Group13.score, TransientEJMAnchor13674Group14.score, TransientEJMAnchor13674Group15.score, TransientEJMAnchor13674Group16.score, TransientEJMAnchor13674Group17.score,
    D5.S3.Quantum.Entanglement.EJMInflationScore.score, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero]
  ac_rfl

private theorem initial_lower : ∀ e : Context, initial.value e ≤ score F1 F2 e.val := by
  intro e
  have h0 := TransientEJMAnchor13674Group02.bound e.val e.property
  change TransientEJMAnchor13674Group02.table (e.val 13) (e.val 15) (e.val 16) ≤ TransientEJMAnchor13674Group02.score e.val at h0
  rw [← TransientEJMAnchor13674VERoot.group00_normalization (e.val 13) (e.val 15) (e.val 16)] at h0
  have h1 := TransientEJMAnchor13674Group11.bound e.val e.property
  change TransientEJMAnchor13674Group11.table (e.val 14) (e.val 17) ≤ TransientEJMAnchor13674Group11.score e.val at h1
  rw [← TransientEJMAnchor13674VERoot.group01_normalization (e.val 14) (e.val 17)] at h1
  have h2 := TransientEJMAnchor13674Group05.bound e.val e.property
  change TransientEJMAnchor13674Group05.table (e.val 13) (e.val 16) (e.val 17) ≤ TransientEJMAnchor13674Group05.score e.val at h2
  rw [← TransientEJMAnchor13674VERoot.group02_normalization (e.val 13) (e.val 16) (e.val 17)] at h2
  have h3 := TransientEJMAnchor13674Group08.bound e.val e.property
  change TransientEJMAnchor13674Group08.table (e.val 14) (e.val 15) (e.val 16) (e.val 17) ≤ TransientEJMAnchor13674Group08.score e.val at h3
  rw [← TransientEJMAnchor13674VERoot.group03_normalization (e.val 14) (e.val 15) (e.val 16) (e.val 17)] at h3
  have h4 := TransientEJMAnchor13674Group04.bound e.val e.property
  change TransientEJMAnchor13674Group04.table (e.val 13) (e.val 15) (e.val 18) ≤ TransientEJMAnchor13674Group04.score e.val at h4
  rw [← TransientEJMAnchor13674VERoot.group04_normalization (e.val 13) (e.val 15) (e.val 18)] at h4
  have h5 := TransientEJMAnchor13674Group06.bound e.val e.property
  change TransientEJMAnchor13674Group06.table (e.val 13) (e.val 16) (e.val 18) ≤ TransientEJMAnchor13674Group06.score e.val at h5
  rw [← TransientEJMAnchor13674VERoot.group05_normalization (e.val 13) (e.val 16) (e.val 18)] at h5
  have h6 := TransientEJMAnchor13674Group10.bound e.val e.property
  change TransientEJMAnchor13674Group10.table (e.val 14) (e.val 16) (e.val 18) ≤ TransientEJMAnchor13674Group10.score e.val at h6
  rw [← TransientEJMAnchor13674VERoot.group06_normalization (e.val 14) (e.val 16) (e.val 18)] at h6
  have h7 := TransientEJMAnchor13674Group14.bound e.val e.property
  change TransientEJMAnchor13674Group14.table (e.val 15) (e.val 16) (e.val 18) ≤ TransientEJMAnchor13674Group14.score e.val at h7
  rw [← TransientEJMAnchor13674VERoot.group07_normalization (e.val 15) (e.val 16) (e.val 18)] at h7
  have h8 := TransientEJMAnchor13674Group01.bound e.val e.property
  change TransientEJMAnchor13674Group01.table (e.val 13) (e.val 14) (e.val 17) (e.val 18) ≤ TransientEJMAnchor13674Group01.score e.val at h8
  rw [← TransientEJMAnchor13674VERoot.group08_normalization (e.val 13) (e.val 14) (e.val 17) (e.val 18)] at h8
  have h9 := TransientEJMAnchor13674Group16.bound e.val e.property
  change TransientEJMAnchor13674Group16.table (e.val 15) (e.val 17) (e.val 18) ≤ TransientEJMAnchor13674Group16.score e.val at h9
  rw [← TransientEJMAnchor13674VERoot.group09_normalization (e.val 15) (e.val 17) (e.val 18)] at h9
  have h10 := TransientEJMAnchor13674Group13.bound e.val e.property
  change TransientEJMAnchor13674Group13.table (e.val 14) (e.val 19) ≤ TransientEJMAnchor13674Group13.score e.val at h10
  rw [← TransientEJMAnchor13674VERoot.group10_normalization (e.val 14) (e.val 19)] at h10
  have h11 := TransientEJMAnchor13674Group00.bound e.val e.property
  change TransientEJMAnchor13674Group00.table (e.val 13) (e.val 14) (e.val 16) (e.val 19) ≤ TransientEJMAnchor13674Group00.score e.val at h11
  rw [← TransientEJMAnchor13674VERoot.group11_normalization (e.val 13) (e.val 14) (e.val 16) (e.val 19)] at h11
  have h12 := TransientEJMAnchor13674Group15.bound e.val e.property
  change TransientEJMAnchor13674Group15.table (e.val 15) (e.val 16) (e.val 19) ≤ TransientEJMAnchor13674Group15.score e.val at h12
  rw [← TransientEJMAnchor13674VERoot.group12_normalization (e.val 15) (e.val 16) (e.val 19)] at h12
  have h13 := TransientEJMAnchor13674Group17.bound e.val e.property
  change TransientEJMAnchor13674Group17.table (e.val 17) (e.val 19) ≤ TransientEJMAnchor13674Group17.score e.val at h13
  rw [← TransientEJMAnchor13674VERoot.group13_normalization (e.val 17) (e.val 19)] at h13
  have h14 := TransientEJMAnchor13674Group12.bound e.val e.property
  change TransientEJMAnchor13674Group12.table (e.val 14) (e.val 17) (e.val 19) ≤ TransientEJMAnchor13674Group12.score e.val at h14
  rw [← TransientEJMAnchor13674VERoot.group14_normalization (e.val 14) (e.val 17) (e.val 19)] at h14
  have h15 := TransientEJMAnchor13674Group03.bound e.val e.property
  change TransientEJMAnchor13674Group03.table (e.val 13) (e.val 15) (e.val 17) (e.val 19) ≤ TransientEJMAnchor13674Group03.score e.val at h15
  rw [← TransientEJMAnchor13674VERoot.group15_normalization (e.val 13) (e.val 15) (e.val 17) (e.val 19)] at h15
  have h16 := TransientEJMAnchor13674Group07.bound e.val e.property
  change TransientEJMAnchor13674Group07.table (e.val 13) (e.val 18) (e.val 19) ≤ TransientEJMAnchor13674Group07.score e.val at h16
  rw [← TransientEJMAnchor13674VERoot.group16_normalization (e.val 13) (e.val 18) (e.val 19)] at h16
  have h17 := TransientEJMAnchor13674Group09.bound e.val e.property
  change TransientEJMAnchor13674Group09.table (e.val 14) (e.val 15) (e.val 18) (e.val 19) ≤ TransientEJMAnchor13674Group09.score e.val at h17
  rw [← TransientEJMAnchor13674VERoot.group17_normalization (e.val 14) (e.val 15) (e.val 18) (e.val 19)] at h17
  have combined := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17
  rw [component_sum e.val] at combined
  simp only [initial, State.value, factor, lift, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero,
    TransientEJMAnchor13674VEGroups.lowerAt00, TransientEJMAnchor13674VEGroups.lowerAt01, TransientEJMAnchor13674VEGroups.lowerAt02, TransientEJMAnchor13674VEGroups.lowerAt03, TransientEJMAnchor13674VEGroups.lowerAt04, TransientEJMAnchor13674VEGroups.lowerAt05, TransientEJMAnchor13674VEGroups.lowerAt06, TransientEJMAnchor13674VEGroups.lowerAt07, TransientEJMAnchor13674VEGroups.lowerAt08, TransientEJMAnchor13674VEGroups.lowerAt09, TransientEJMAnchor13674VEGroups.lowerAt10, TransientEJMAnchor13674VEGroups.lowerAt11, TransientEJMAnchor13674VEGroups.lowerAt12, TransientEJMAnchor13674VEGroups.lowerAt13, TransientEJMAnchor13674VEGroups.lowerAt14, TransientEJMAnchor13674VEGroups.lowerAt15, TransientEJMAnchor13674VEGroups.lowerAt16, TransientEJMAnchor13674VEGroups.lowerAt17]
  convert combined using 1 <;> ring

/-- Four actual terminal entries; this is a new small kernel obligation. -/
private theorem last_table_lower : ∀ x19 : Fin 4,
    (-45112 : ℤ) ≤ TransientEJMAnchor13674VEBucket05.table x19 := by
  decide +kernel

private theorem terminal : Terminal state6 (6987435 : ℤ) := by
  refine ⟨[(6987435 : ℤ) * (-45112)], ?_, ?_⟩
  · change List.Forall₂ (fun m f => ∀ e : Context, m ≤ f e)
      [(6987435 : ℤ) * (-45112)] [factor 23]
    constructor
    · intro e
      have lower := mul_le_mul_of_nonneg_left (last_table_lower (e.val 19))
        (by decide : (0 : ℤ) ≤ 6987435)
      simpa only [factor, lift, TransientEJMAnchor13674VEBucket05.lowerAt] using lower
    · exact List.Forall₂.nil
  · change (6987435 : ℤ) ≤ (6987435 : ℤ) * 21271424 +
      ((6987435 : ℤ) * (-45112) + 0)
    norm_num

/-- Actual six-step program delivery on the unchanged original score. -/
theorem actual_prefix_score_lower_bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 4) e) : scale ≤ score F1 F2 e := by
  change (6987435 : ℤ) ≤ score F1 F2 e
  exact program_lower_bound (fun v : Context => score F1 F2 v.val)
    initial operations (6987435 : ℤ) initial_lower valid_program terminal ⟨e, hp⟩

#print axioms actual_prefix_score_lower_bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674MinPlusConsumer
