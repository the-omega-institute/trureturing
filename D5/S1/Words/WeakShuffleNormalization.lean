/- GID: D5/S1/Words/WeakShuffleNormalization
   generality: G
   mirror-B: D5/B/S1/Words/WeakShuffleNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mammez Conjecture 3.10 normalization for every alphabet. -/

/-
Public result: proof_shape: content; escape_witness:
D5.S1.Words.WeakShuffleNormalization.APath.exponents; admission_basis: open-problem-resolution
(#15815; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16034 (result).
Direct frozen dependencies: none (the proof uses pinned Mathlib and same-delivery helpers only).
The public claim retains the preregistered wsWord/wsMul/norm1/norm2 conventions literally; proofs
use the local implementation helpers without introducing duplicate public aliases.
Private helpers are all consumed on the proof path to result; bind-only helpers are classified by
their consumers.
Private declaration classifications (theorem/lemma proofs have named consumers):
wsMul_add_left: proof_shape=bind-only; consumer=coeff_assoc_triple2.
wsMul_add_right: proof_shape=bind-only; consumer=coeff_assoc_triple2.
wsWord_one_one': proof_shape=bind-only; consumer=coeff_assoc_triple2.
coeff_assoc_triple2: proof_shape=bind-only; consumer=barrier_outside.
coeff_comm: proof_shape=bind-only; consumer=exceptional_reverse_zero.
assoc_aab_raw: proof_shape=bind-only; consumer=exceptional_diag_f1_zero.
exceptional_diag_f1_zero: proof_shape=bind-only; consumer=exceptional_diag_f2_zero.
comm_aab_raw: proof_shape=bind-only; consumer=exceptional_diag_f2_zero.
exceptional_diag_f2_zero: proof_shape=bind-only; consumer=exceptional_f2_reverse_zero.
assoc_aba_raw: proof_shape=bind-only; consumer=exceptional_f2_reverse_zero.
exceptional_f2_reverse_zero: proof_shape=bind-only; consumer=exceptional_reverse_zero.
comm_bab_raw: proof_shape=bind-only; consumer=exceptional_target_diag_zero.
assoc_abb_raw: proof_shape=bind-only; consumer=exceptional_target_diag_zero.
exceptional_reverse_zero: proof_shape=bind-only; consumer=norm1_factor.
exceptional_target_diag_zero: proof_shape=bind-only; consumer=barrier_outside.
zero_diag_mutual: proof_shape=bind-only; consumer=barrier_outside.
barrier_outside: proof_shape=bind-only; consumer=actual_barriers.
barrier_source: proof_shape=bind-only; consumer=actual_barriers.
noR_tick: proof_shape=bind-only; consumer=APath.noR.
APath.noR: proof_shape=content; escape_witness=APath.noR; consumer=APath.exponents.
outside_opponent: proof_shape=bind-only; consumer=APath.markers.
APath.markers: proof_shape=content; escape_witness=APath.markers; consumer=APath.exponents.
APath.exponents: proof_shape=content; escape_witness=APath.exponents; consumer=Run.weight_factor.
actual_barriers: proof_shape=bind-only; consumer=Run.weight_factor.
plans_run: proof_shape=content; escape_witness=plans_run; consumer=diagonal_wsWord.
Run.mem: proof_shape=content; escape_witness=Run.mem; consumer=Run.q_identity.
Run.events_mem: proof_shape=content; escape_witness=Run.events_mem; consumer=Run.q_identity.
Run.toAPath: proof_shape=content; escape_witness=Run.toAPath; consumer=Run.weight_factor.
planSum_branch: proof_shape=bind-only; consumer=planSum_eq_wsWord.
planSum_eq_wsWord: proof_shape=content; escape_witness=planSum_eq_wsWord; consumer=diagonal_wsWord.
Exceptional: proof_shape=bind-only; consumer=edgeFactor.
edgeFactor_ne_zero: proof_shape=bind-only; consumer=pathCoeff_zero_iff.
norm1_factor: proof_shape=bind-only; consumer=branch_factor.
branch_factor: proof_shape=bind-only; consumer=pathCoeff_factor.
pathCoeff_factor: proof_shape=bind-only; consumer=pathCoeff_zero_iff.
pathCoeff_zero_iff: proof_shape=bind-only; consumer=Run.q_identity.
event_product: proof_shape=bind-only; consumer=pathFactor_product.
pathFactor_product: proof_shape=bind-only; consumer=Run.qOn_factor.
marker_false_of_not_mem: proof_shape=bind-only; consumer=weight_one_of_missing.
expo_zero_of_marker_false: proof_shape=bind-only; consumer=weight_one_of_missing.
expo_zero_of_not_mem_a: proof_shape=bind-only; consumer=weight_one_of_missing.
weight_one_of_missing: proof_shape=bind-only; consumer=q_eq_qOn.
q_eq_qOn: proof_shape=bind-only; consumer=Run.q_identity.
q_ne_zero: proof_shape=bind-only; consumer=result.
scalar_weight_identity: proof_shape=bind-only; consumer=Run.weight_factor.
Run.weight_factor: proof_shape=content; escape_witness=APath.exponents; consumer=Run.qOn_factor.
Run.qOn_factor: proof_shape=content; escape_witness=APath.exponents; consumer=Run.q_identity.
Run.q_identity: proof_shape=content; escape_witness=APath.exponents; consumer=diagonal_wsWord.
diagonal_single: proof_shape=bind-only; consumer=diagonalEquiv.
diagonal_wsWord: proof_shape=content; escape_witness=APath.exponents; consumer=diagonal_wsMul.
diagonal_wsMul: proof_shape=content; escape_witness=APath.exponents; consumer=result.
Private proposition carriers APath, BarrierData and Run are implementation types used by these
declarations.
Private proposition-valued definitions are classified as bind-only helpers:
allowed: proof_shape=bind-only; consumer=actual_barriers, Run.toAPath, branch_factor.
Exceptional: proof_shape=bind-only; consumer=edgeFactor, norm1_factor, pathCoeff_factor.
-/

import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace D5.S1.Words.WeakShuffleNormalization

abbrev KX (X K : Type*) [Zero K] := List X →₀ K

variable {X K : Type*} [Field K] [DecidableEq X]

noncomputable def wsWord (f1 f2 : X → X → K) : List X → List X → KX X K
  | [], v => Finsupp.single v 1
  | u, [] => Finsupp.single u 1
  | a :: u, b :: v =>
      f1 a b • Finsupp.lmapDomain K K (List.cons a) (wsWord f1 f2 u (b :: v)) +
      f2 a b • Finsupp.lmapDomain K K (List.cons b) (wsWord f1 f2 (a :: u) v)
termination_by u v => u.length + v.length

noncomputable def wsMul (f1 f2 : X → X → K) : KX X K → KX X K → KX X K :=
  fun x y => x.sum fun u a => y.sum fun v b => (a * b) • wsWord f1 f2 u v

def IsWeakShuffle (f1 f2 : X → X → K) : Prop :=
  (∀ x y, wsMul f1 f2 x y = wsMul f1 f2 y x) ∧
  (∀ x y z, wsMul f1 f2 (wsMul f1 f2 x y) z =
    wsMul f1 f2 x (wsMul f1 f2 y z))

noncomputable def norm1 (f1 : X → X → K) (a b : X) : K := by
  classical
  exact if a ≠ b ∧ f1 a b ∉ ({0, 1} : Set K) then 1
    else if a ≠ b ∧ f1 b a ∉ ({0, 1} : Set K) then 0
    else f1 a b

noncomputable def norm2 (f1 f2 : X → X → K) (a b : X) : K := by
  classical
  exact if a = b then f2 a a else norm1 f1 b a

def claim : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (X : Type) [DecidableEq X]
    (f1 f2 : X → X → K), IsWeakShuffle f1 f2 →
      ∃ Φ : KX X K ≃ₗ[K] KX X K,
        Φ (Finsupp.single [] 1) = Finsupp.single [] 1 ∧
        ∀ x y, Φ (wsMul f1 f2 x y) =
          wsMul (norm1 f1) (norm2 f1 f2) (Φ x) (Φ y)

end D5.S1.Words.WeakShuffleNormalization
namespace D5.S1.Words.WeakShuffleNormalization
variable {X K : Type*} [Field K]
private lemma wsMul_add_left (f1 f2 : X → X → K) (x y z : KX X K) :
    wsMul f1 f2 (x + y) z = wsMul f1 f2 x z + wsMul f1 f2 y z := by
  classical
  unfold wsMul
  rw [Finsupp.sum_add_index]
  · intro a ha
    simp
  · intro a ha b c
    simp only [add_mul, add_smul]
    rw [Finsupp.sum_add]
end D5.S1.Words.WeakShuffleNormalization
namespace D5.S1.Words.WeakShuffleNormalization
variable {X K : Type*} [Field K]
private lemma wsMul_add_right (f1 f2 : X → X → K) (x y z : KX X K) :
    wsMul f1 f2 x (y + z) = wsMul f1 f2 x y + wsMul f1 f2 x z := by
  classical
  unfold wsMul
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro a ha
  rw [Finsupp.sum_add_index]
  · intro b hb
    simp
  · intro b hb c d
    simp only [mul_add, add_smul]
end D5.S1.Words.WeakShuffleNormalization
namespace D5.S1.Words.WeakShuffleNormalization
variable {X K : Type*} [Field K]
private lemma wsWord_one_one' (f1 f2 : X → X → K) (a b : X) :
    wsWord f1 f2 [a] [b] =
      f1 a b • Finsupp.single [a, b] 1 + f2 a b • Finsupp.single [b, a] 1 := by
  simp [wsWord, Finsupp.lmapDomain]
private lemma coeff_assoc_triple2 (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {x y z : X} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    f1 x y * f1 y z * (f1 x z - 1) = 0 := by
  classical
  have h := hws.2 (Finsupp.single [x] 1) (Finsupp.single [y] 1) (Finsupp.single [z] 1)
  have hxy' : wsMul f1 f2 (Finsupp.single [x] 1) (Finsupp.single [y] 1) =
      wsWord f1 f2 [x] [y] := by simp [wsMul]
  have hyz' : wsMul f1 f2 (Finsupp.single [y] 1) (Finsupp.single [z] 1) =
      wsWord f1 f2 [y] [z] := by simp [wsMul]
  rw [hxy', hyz'] at h
  simp only [wsWord_one_one'] at h
  -- distribute the outer product over the two explicit branches
  rw [wsMul_add_left] at h
  rw [wsMul_add_right] at h
  simp only [wsMul, Finsupp.smul_single, smul_eq_mul, mul_one, mul_zero,
    zero_smul, Finsupp.sum_single_index, zero_mul, one_mul] at h
  have hc := congrArg (fun w : KX X K => w [x, y, z]) h
  have hc' : f1 x y * (f1 x z * f1 y z) = f1 y z * f1 x y := by
    simpa [wsWord, Finsupp.lmapDomain, Finsupp.mapDomain, Finsupp.sum_add_index,
      Finsupp.sum_single_index, hxy, hxz, hyz,
      Ne.symm hxy, Ne.symm hxz, Ne.symm hyz] using hc
  calc
    f1 x y * f1 y z * (f1 x z - 1) =
        f1 x y * (f1 x z * f1 y z) - f1 y z * f1 x y := by ring
    _ = 0 := by rw [hc']; ring
private lemma coeff_comm (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {a b : X} (hab : a ≠ b) : f1 a b = f2 b a := by
  classical
  have h := hws.1 (Finsupp.single [a] 1) (Finsupp.single [b] 1)
  have hc := congrArg (fun z : KX X K => z [a, b]) h
  simpa [wsMul, wsWord, Finsupp.lmapDomain, hab] using hc

private lemma assoc_aab_raw (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    (a b : X) (hneq : a ≠ b) :
    (f1 a a * f1 a b * f1 a b + f2 a a * f1 a b * f1 a b) =
      (f1 a b * f1 a a + f1 a b * (f2 a a * f1 a b)) := by
  classical
  have h := hws.2 (Finsupp.single [a] 1) (Finsupp.single [a] 1) (Finsupp.single [b] 1)
  have haa : wsMul f1 f2 (Finsupp.single [a] 1) (Finsupp.single [a] 1) =
      wsWord f1 f2 [a] [a] := by simp [wsMul]
  have hab : wsMul f1 f2 (Finsupp.single [a] 1) (Finsupp.single [b] 1) =
      wsWord f1 f2 [a] [b] := by simp [wsMul]
  rw [haa, hab] at h
  simp only [wsWord_one_one'] at h
  rw [wsMul_add_left, wsMul_add_right] at h
  simp only [wsMul, Finsupp.smul_single, smul_eq_mul, mul_one, mul_zero,
    zero_smul, Finsupp.sum_single_index, zero_mul, one_mul] at h
  have hc := congrArg (fun w : KX X K => w [a, a, b]) h
  simpa [wsWord, Finsupp.lmapDomain, Finsupp.mapDomain, Finsupp.sum_add_index,
    Finsupp.sum_single_index, hneq, Ne.symm hneq, mul_assoc] using hc
private lemma exceptional_diag_f1_zero (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {a b : X} (hab : a ≠ b) (hk0 : f1 a b ≠ 0) (hk1 : f1 a b ≠ 1) :
    f1 a a = 0 := by
  have he := assoc_aab_raw f1 f2 hws a b hab
  have hz : f1 a a * f1 a b * (f1 a b - 1) = 0 := by
    calc
      f1 a a * f1 a b * (f1 a b - 1) =
          (f1 a a * f1 a b * f1 a b + f2 a a * f1 a b * f1 a b) -
            (f1 a b * f1 a a + f1 a b * (f2 a a * f1 a b)) := by ring
      _ = 0 := by rw [he]; ring
  rcases mul_eq_zero.mp hz with hAk | hk1z
  · rcases mul_eq_zero.mp hAk with hA | hk
    · exact hA
    · exact False.elim (hk0 hk)
  · exact False.elim (hk1 (sub_eq_zero.mp hk1z))
private lemma comm_aab_raw (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {a b : X} (hneq : a ≠ b) :
    f1 a a + f2 a a * f1 a b = f1 a a * f2 b a + f2 a a := by
  classical
  have h := hws.1 (Finsupp.single [a] 1) (Finsupp.single [a, b] 1)
  have hc := congrArg (fun w : KX X K => w [a, a, b]) h
  simpa [wsMul, wsWord, Finsupp.lmapDomain, Finsupp.mapDomain, Finsupp.sum_add_index,
    Finsupp.sum_single_index, hneq, Ne.symm hneq] using hc
private lemma exceptional_diag_f2_zero (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {a b : X} (hab : a ≠ b) (hk0 : f1 a b ≠ 0) (hk1 : f1 a b ≠ 1) :
    f2 a a = 0 := by
  have hA := exceptional_diag_f1_zero f1 f2 hws hab hk0 hk1
  have he := comm_aab_raw f1 f2 hws hab
  simp only [hA, zero_mul, zero_add] at he
  have hz : f2 a a * (f1 a b - 1) = 0 := by
    calc
      f2 a a * (f1 a b - 1) = f2 a a * f1 a b - f2 a a := by ring
      _ = 0 := by rw [he]; ring
  rcases mul_eq_zero.mp hz with hB | hk
  · exact hB
  · exact False.elim (hk1 (sub_eq_zero.mp hk))
private lemma assoc_aba_raw (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {a b : X} (hneq : a ≠ b) :
    (f1 a a + f2 a a) * f1 a b * f2 a b =
      f1 a b * f2 a a * f2 a b + f2 a b * f1 a b := by
  classical
  have h := hws.2 (Finsupp.single [a] 1) (Finsupp.single [a] 1) (Finsupp.single [b] 1)
  have haa : wsMul f1 f2 (Finsupp.single [a] 1) (Finsupp.single [a] 1) =
      wsWord f1 f2 [a] [a] := by simp [wsMul]
  have hab : wsMul f1 f2 (Finsupp.single [a] 1) (Finsupp.single [b] 1) =
      wsWord f1 f2 [a] [b] := by simp [wsMul]
  rw [haa, hab] at h
  simp only [wsWord_one_one'] at h
  rw [wsMul_add_left, wsMul_add_right] at h
  simp only [wsMul, Finsupp.smul_single, smul_eq_mul, mul_one, mul_zero,
    zero_smul, Finsupp.sum_single_index, zero_mul, one_mul] at h
  have hc := congrArg (fun w : KX X K => w [a, b, a]) h
  have hc' : f1 a a * (f1 a b * f2 a b) + f2 a a * (f1 a b * f2 a b) =
      f1 a b * (f2 a a * f2 a b) + f2 a b * f1 a b := by
    simpa [wsWord, Finsupp.lmapDomain, Finsupp.mapDomain, Finsupp.sum_add_index,
      Finsupp.sum_single_index, hneq, Ne.symm hneq] using hc
  simpa [add_mul, mul_assoc] using hc'
private lemma exceptional_f2_reverse_zero (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {a b : X} (hab : a ≠ b) (hk0 : f1 a b ≠ 0) (hk1 : f1 a b ≠ 1) :
    f2 a b = 0 := by
  have hA := exceptional_diag_f1_zero f1 f2 hws hab hk0 hk1
  have hB := exceptional_diag_f2_zero f1 f2 hws hab hk0 hk1
  have he := assoc_aba_raw f1 f2 hws hab
  simp only [hA, hB, add_zero, zero_mul, mul_zero, zero_add] at he
  rcases mul_eq_zero.mp he.symm with hl | hk
  · exact hl
  · exact False.elim (hk0 hk)
private lemma comm_bab_raw (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {a b : X} (hneq : a ≠ b) :
    f2 b b * f2 b a = f1 b b * f1 a b := by
  classical
  have h := hws.1 (Finsupp.single [b] 1) (Finsupp.single [b, a] 1)
  have hc := congrArg (fun w : KX X K => w [b, a, b]) h
  simpa [wsMul, wsWord, Finsupp.lmapDomain, Finsupp.mapDomain, Finsupp.sum_add_index,
    Finsupp.sum_single_index, hneq, Ne.symm hneq] using hc
private lemma assoc_abb_raw (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {a b : X} (hneq : a ≠ b) :
    f1 a b * (f1 a b * f1 b b) + f1 a b * (f1 a b * f2 b b) =
      f1 b b * f1 a b + f2 b b * f1 a b := by
  classical
  have h := hws.2 (Finsupp.single [a] 1) (Finsupp.single [b] 1) (Finsupp.single [b] 1)
  have hab : wsMul f1 f2 (Finsupp.single [a] 1) (Finsupp.single [b] 1) =
      wsWord f1 f2 [a] [b] := by simp [wsMul]
  have hbb : wsMul f1 f2 (Finsupp.single [b] 1) (Finsupp.single [b] 1) =
      wsWord f1 f2 [b] [b] := by simp [wsMul]
  rw [hab, hbb] at h
  simp only [wsWord_one_one'] at h
  rw [wsMul_add_left, wsMul_add_right] at h
  simp only [wsMul, Finsupp.smul_single, smul_eq_mul, mul_one, mul_zero,
    zero_smul, Finsupp.sum_single_index, zero_mul, one_mul] at h
  have hc := congrArg (fun w : KX X K => w [a, b, b]) h
  simpa [wsWord, Finsupp.lmapDomain, Finsupp.mapDomain, Finsupp.sum_add_index,
    Finsupp.sum_single_index, hneq, Ne.symm hneq, mul_assoc, add_mul] using hc
end D5.S1.Words.WeakShuffleNormalization
namespace D5.S1.Words.WeakShuffleNormalization
variable {X K : Type*} [Field K]
private lemma exceptional_reverse_zero (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {a b : X} (hab : a ≠ b) (hk0 : f1 a b ≠ 0) (hk1 : f1 a b ≠ 1) :
    f1 b a = 0 := by
  rw [coeff_comm f1 f2 hws hab.symm]
  exact exceptional_f2_reverse_zero f1 f2 hws hab hk0 hk1
private lemma exceptional_target_diag_zero [CharZero K] (f1 f2 : X → X → K)
    (hws : IsWeakShuffle f1 f2) {a b : X} (hab : a ≠ b)
    (hk0 : f1 a b ≠ 0) (hk1 : f1 a b ≠ 1) : f1 b b = 0 ∧ f2 b b = 0 := by
  have hc := comm_bab_raw f1 f2 hws hab
  rw [← coeff_comm f1 f2 hws hab] at hc
  have hdiag : f2 b b = f1 b b := (mul_right_cancel₀ hk0 hc)
  have he := assoc_abb_raw f1 f2 hws hab
  rw [hdiag] at he
  have hz : (2 : K) * f1 b b * f1 a b * (f1 a b - 1) = 0 := by
    calc
      (2 : K) * f1 b b * f1 a b * (f1 a b - 1) =
        (f1 a b * (f1 a b * f1 b b) + f1 a b * (f1 a b * f1 b b)) -
          (f1 b b * f1 a b + f1 b b * f1 a b) := by ring
      _ = 0 := by rw [he]; ring
  have hd : f1 b b = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact False.elim ((show (2 : K) ≠ 0 from Nat.cast_ne_zero.mpr (by decide)) h)
        · exact h
      · exact False.elim (hk0 h)
    · exact False.elim (hk1 (sub_eq_zero.mp h))
  exact ⟨hd, hdiag.trans hd⟩
private lemma zero_diag_mutual (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {b x : X} (hbx : b ≠ x) (hB : f1 b b = 0) (hD : f2 b b = 0) :
    f1 b x * f1 x b = 0 := by
  have h := assoc_aba_raw f1 f2 hws hbx
  simp only [hB, hD, zero_add, zero_mul, mul_zero] at h
  rw [← coeff_comm f1 f2 hws hbx.symm] at h
  simpa [mul_comm] using h.symm
private lemma barrier_outside [CharZero K] (f1 f2 : X → X → K)
    (hws : IsWeakShuffle f1 f2) {a b x z : X} (hab : a ≠ b)
    (hk0 : f1 a b ≠ 0) (hk1 : f1 a b ≠ 1)
    (hx : f1 x b ≠ 0) (hz : f1 z b = 0) : f1 z x = 0 := by
  obtain ⟨hB, hD⟩ := exceptional_target_diag_zero f1 f2 hws hab hk0 hk1
  have hxb : x ≠ b := by intro h; subst x; exact hx hB
  have hzx : z ≠ x := by intro h; subst z; exact hx hz
  by_cases hzb : z = b
  · subst z
    exact (mul_eq_zero.mp (zero_diag_mutual f1 f2 hws hxb.symm hB hD)).resolve_right hx
  · have h := coeff_assoc_triple2 f1 f2 hws hzx hzb hxb
    rw [hz] at h
    simp only [zero_sub, mul_neg, mul_one, neg_eq_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hx
private lemma barrier_source [CharZero K] (f1 f2 : X → X → K)
    (hws : IsWeakShuffle f1 f2) {a b x : X} (hab : a ≠ b)
    (hk0 : f1 a b ≠ 0) (hk1 : f1 a b ≠ 1)
    (hx : f1 x b ≠ 0) : f1 a x = 0 := by
  have hB := (exceptional_target_diag_zero f1 f2 hws hab hk0 hk1).1
  by_cases hax : a = x
  · subst x; exact exceptional_diag_f1_zero f1 f2 hws hab hk0 hk1
  · have hxb : x ≠ b := by intro h; subst x; exact hx hB
    have h := coeff_assoc_triple2 f1 f2 hws hax hab hxb
    have hk : f1 a b - 1 ≠ 0 := by intro h; exact hk1 (sub_eq_zero.mp h)
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hk)).resolve_right hx
end D5.S1.Words.WeakShuffleNormalization
namespace D5.S1.Words.WeakShuffleNormalization
variable {X : Type*} [DecidableEq X]
private def marker (P : X → Bool) (b : X) : List X → Bool
  | [] => false
  | x :: w => if P x then marker P b w else decide (x = b)
private def expo (P : X → Bool) (a b : X) : List X → ℕ
  | [] => 0
  | x :: w => if P x then expo P a b w + if x = a ∧ marker P b w = true then 1 else 0 else 0
private def tick (a b x y : X) : ℕ := if x = a ∧ y = b then 1 else 0
private inductive APath (allow : X → X → Prop) (a b : X) : List X → List X → List X → ℕ → Prop
  | nilL (v : List X) : APath allow a b [] v v 0
  | nilR (u : List X) : APath allow a b u [] u 0
  | left {x y u v w t} (hs : allow x y) (ht : APath allow a b u (y :: v) w t) :
      APath allow a b (x :: u) (y :: v) (x :: w) (t + tick a b x y)
  | right {x y u v w t} (hs : allow y x) (ht : APath allow a b (x :: u) v w t) :
      APath allow a b (x :: u) (y :: v) (y :: w) (t + tick a b y x)
private structure BarrierData (P : X → Bool) (a b : X) (allow : X → X → Prop) : Prop where
  pa : P a = true
  pb : P b = false
  outside : ∀ x y, allow x y → P y = true → P x = true
  source : ∀ y, allow a y → P y = false
  bb : ¬ allow b b
  rb : ∀ r, P r = false → r ≠ b → ¬ allow r b
private lemma noR_tick {P : X → Bool} {a b : X} {allow : X → X → Prop}
    (H : BarrierData P a b allow) {x y : X} (hs : allow x y)
    (hx : P x = false) (hxb : x ≠ b) : P y = false ∧ y ≠ b ∧ tick a b x y = 0 := by
  have hy : P y = false := by
    cases he : P y with
    | false => rfl
    | true => have hh := H.outside x y hs he; rw [hx] at hh; contradiction
  have hyb : y ≠ b := by intro e; subst y; exact H.rb x hx hxb hs
  have hxa : x ≠ a := by intro e; subst x; rw [H.pa] at hx; contradiction
  exact ⟨hy, hyb, by simp [tick, hxa]⟩

private lemma APath.noR {P : X → Bool} {a b : X} {allow : X → X → Prop}
    (H : BarrierData P a b allow) {u v w : List X} {t : ℕ}
    (h : APath allow a b u v w t) :
    (∃ x s, u = x :: s ∧ P x = false ∧ x ≠ b) ∨
    (∃ x s, v = x :: s ∧ P x = false ∧ x ≠ b) → t = 0 := by
  induction h with
  | nilL v => intro _; rfl
  | nilR u => intro _; rfl
  | @left x y u v w t hs ht ih =>
    intro hr
    rcases hr with ⟨z,s,he,hz,hzb⟩ | ⟨z,s,he,hz,hzb⟩
    · rcases List.cons.inj he with ⟨rfl, rfl⟩
      obtain ⟨hy, hyb, htick⟩ := noR_tick H hs hz hzb
      have it := ih (Or.inr ⟨y,v,rfl,hy,hyb⟩)
      simp [it, htick]
    · rcases List.cons.inj he with ⟨rfl, rfl⟩
      have it := ih (Or.inr ⟨y,v,rfl,hz,hzb⟩)
      have htick : tick a b x y = 0 := by simp [tick, hzb]
      simp [it, htick]
  | @right x y u v w t hs ht ih =>
    intro hr
    rcases hr with ⟨z,s,he,hz,hzb⟩ | ⟨z,s,he,hz,hzb⟩
    · rcases List.cons.inj he with ⟨rfl, rfl⟩
      have it := ih (Or.inl ⟨x,u,rfl,hz,hzb⟩)
      have htick : tick a b y x = 0 := by simp [tick, hzb]
      simp [it, htick]
    · rcases List.cons.inj he with ⟨rfl, rfl⟩
      obtain ⟨hx, hxb, htick⟩ := noR_tick H hs hz hzb
      have it := ih (Or.inl ⟨x,u,rfl,hx,hxb⟩)
      simp [it, htick]
end D5.S1.Words.WeakShuffleNormalization
namespace D5.S1.Words.WeakShuffleNormalization
variable {X : Type*} [DecidableEq X]

omit [DecidableEq X] in
private lemma outside_opponent {P : X → Bool} {a b : X} {allow : X → X → Prop}
    (H : BarrierData P a b allow) {x y : X} (hs : allow x y) (hx : P x = false) :
    P y = false := by
  cases he : P y with
  | false => rfl
  | true => have hh := H.outside x y hs he; rw [hx] at hh; contradiction

private lemma APath.markers {P : X → Bool} {a b : X} {allow : X → X → Prop}
    (H : BarrierData P a b allow) {u v w : List X} {t : ℕ}
    (h : APath allow a b u v w t) :
    marker P b w = (marker P b u || marker P b v) ∧
      ¬ (marker P b u = true ∧ marker P b v = true) := by
  induction h with
  | nilL v => simp [marker]
  | nilR u => simp [marker]
  | @left x y u v w t hs ht ih =>
    by_cases hx : P x = true
    · simpa [marker, hx] using ih
    · have hxf : P x = false := by cases he : P x <;> simp_all
      have hy := outside_opponent H hs hxf
      by_cases hxb : x = b
      · subst x
        have hyb : y ≠ b := by intro e; subst y; exact H.bb hs
        simp [marker, H.pb, hy, hyb]
      · by_cases hyb : y = b
        · subst y; exact False.elim (H.rb x hxf hxb hs)
        · simp [marker, hxf, hy, hxb, hyb]
  | @right x y u v w t hs ht ih =>
    by_cases hy : P y = true
    · simpa [marker, hy] using ih
    · have hyf : P y = false := by cases he : P y <;> simp_all
      have hx := outside_opponent H hs hyf
      by_cases hyb : y = b
      · subst y
        have hxb : x ≠ b := by intro e; subst x; exact H.bb hs
        simp [marker, H.pb, hx, hxb]
      · by_cases hxb : x = b
        · subst x; exact False.elim (H.rb y hyf hyb hs)
        · simp [marker, hyf, hx, hxb, hyb]

private lemma APath.exponents {P : X → Bool} {a b : X} {allow : X → X → Prop}
    (H : BarrierData P a b allow) {u v w : List X} {t : ℕ}
    (h : APath allow a b u v w t) :
    t + expo P a b u + expo P a b v = expo P a b w := by
  induction h with
  | nilL v => simp [expo]
  | nilR u => simp [expo]
  | @left x y u v w t hs ht ih =>
    have hm := ht.markers H
    by_cases hx : P x = true
    · by_cases hxa : x = a
      · subst x
        have hy := H.source y hs
        by_cases hyb : y = b
        · subst y
          have hu : marker P b u = false := by
            cases he : marker P b u with
            | false => rfl
            | true => exact False.elim (hm.2 ⟨he, by simp [marker, H.pb]⟩)
          have hw : marker P b w = true := by rw [hm.1]; simp [marker, H.pb]
          simp [expo, H.pa, H.pb, tick, hu, hw] at ih ⊢
          omega
        · have hv : marker P b (y :: v) = false := by simp [marker, hy, hyb]
          have hw : marker P b w = marker P b u := by rw [hm.1, hv]; simp
          simp only [expo, H.pa, hy, ↓reduceIte, tick,
            hyb, and_false, hw] at ih ⊢
          omega
      · simp only [expo, hx, ↓reduceIte, tick, hxa,
          false_and, ↓reduceIte, Nat.add_zero] at ih ⊢
        exact ih
    · have hxf : P x = false := by cases he : P x <;> simp_all
      have hy := outside_opponent H hs hxf
      have hxa : x ≠ a := by intro e; subst x; rw [H.pa] at hxf; contradiction
      have ht0 : t = 0 := by
        by_cases hxb : x = b
        · subst x
          have hyb : y ≠ b := by intro e; subst y; exact H.bb hs
          exact ht.noR H (Or.inr ⟨y,v,rfl,hy,hyb⟩)
        · obtain ⟨_,hyb,_⟩ := noR_tick H hs hxf hxb
          exact ht.noR H (Or.inr ⟨y,v,rfl,hy,hyb⟩)
      simp [expo, hxf, hy, tick, hxa, ht0]
  | @right x y u v w t hs ht ih =>
    -- symmetry reduces this constructor to the same head calculation
    have hm := ht.markers H
    by_cases hy : P y = true
    · by_cases hya : y = a
      · subst y
        have hx := H.source x hs
        by_cases hxb : x = b
        · subst x
          have hv : marker P b v = false := by
            cases he : marker P b v with
            | false => rfl
            | true => exact False.elim (hm.2 ⟨by simp [marker, H.pb],he⟩)
          have hw : marker P b w = true := by rw [hm.1]; simp [marker, H.pb]
          simp [expo, H.pa, H.pb, tick, hv, hw] at ih ⊢
          omega
        · have hu : marker P b (x :: u) = false := by simp [marker, hx, hxb]
          have hw : marker P b w = marker P b v := by rw [hm.1, hu]; simp
          simp only [expo, H.pa, hx, ↓reduceIte, tick,
            hxb, and_false, hw] at ih ⊢
          omega
      · simp only [expo, hy, ↓reduceIte, tick, hya,
          false_and, ↓reduceIte, Nat.add_zero] at ih ⊢
        omega
    · have hyf : P y = false := by cases he : P y <;> simp_all
      have hx := outside_opponent H hs hyf
      have hya : y ≠ a := by intro e; subst y; rw [H.pa] at hyf; contradiction
      have ht0 : t = 0 := by
        by_cases hyb : y = b
        · subst y
          have hxb : x ≠ b := by intro e; subst x; exact H.bb hs
          exact ht.noR H (Or.inl ⟨x,u,rfl,hx,hxb⟩)
        · obtain ⟨_,hxb,_⟩ := noR_tick H hs hyf hyb
          exact ht.noR H (Or.inl ⟨x,u,rfl,hx,hxb⟩)
      simp [expo, hyf, hx, tick, hya, ht0]
end D5.S1.Words.WeakShuffleNormalization
namespace D5.S1.Words.WeakShuffleNormalization
variable {X K : Type*} [Field K] [CharZero K] [DecidableEq X]
private noncomputable def region (f1 : X → X → K) (b : X) (x : X) : Bool := by
  classical exact decide (f1 x b ≠ 0)
private noncomputable def allowed (f1 f2 : X → X → K) (x y : X) : Prop :=
  if x = y then f1 x y ≠ 0 ∨ f2 y x ≠ 0 else f1 x y ≠ 0
private lemma actual_barriers (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {a b : X} (hab : a ≠ b) (hk0 : f1 a b ≠ 0) (hk1 : f1 a b ≠ 1) :
    BarrierData (region f1 b) a b (allowed f1 f2) := by
  classical
  obtain ⟨hB,hD⟩ := exceptional_target_diag_zero f1 f2 hws hab hk0 hk1
  refine ⟨by simp [region, hk0], by simp [region,hB], ?_, ?_, ?_, ?_⟩
  · intro x y hs hy
    by_cases hxy : x = y
    · subst x; exact hy
    · have hxz : f1 x b ≠ 0 := by
        intro hx
        have h := barrier_outside f1 f2 hws hab hk0 hk1
          (by simpa [region] using hy) hx
        exact (by simpa [allowed,hxy] using hs : f1 x y ≠ 0) h
      simpa [region] using hxz
  · intro y hs
    by_cases hay : a = y
    · subst y
      simp [allowed,exceptional_diag_f1_zero f1 f2 hws hab hk0 hk1,
        exceptional_diag_f2_zero f1 f2 hws hab hk0 hk1] at hs
    · have hy : f1 y b = 0 := by
        by_contra hz
        have h := barrier_source f1 f2 hws hab hk0 hk1 hz
        exact (by simpa [allowed,hay] using hs : f1 a y ≠ 0) h
      simp [region,hy]
  · simp [allowed,hB,hD]
  · intro r hr hrb hs
    have hz : f1 r b = 0 := by simpa [region] using hr
    exact (by simpa [allowed,hrb] using hs : f1 r b ≠ 0) hz
end D5.S1.Words.WeakShuffleNormalization
namespace D5.S1.Words.WeakShuffleNormalization
variable {X : Type*} [DecidableEq X]
private abbrev Event (X : Type*) := Bool × X × X
private inductive Run : List X → List X → List X → List (Event X) → Prop
  | nilL (v) : Run [] v v []
  | nilR (u) : Run u [] u []
  | left {x y u v w es} (ht : Run u (y :: v) w es) :
      Run (x :: u) (y :: v) (x :: w) ((false,x,y) :: es)
  | right {x y u v w es} (ht : Run (x :: u) v w es) :
      Run (x :: u) (y :: v) (y :: w) ((true,y,x) :: es)

private def plans : List X → List X → List (List X × List (Event X))
  | [], v => [(v,[])]
  | u, [] => [(u,[])]
  | x :: u, y :: v =>
      (plans u (y :: v)).map (fun p => (x :: p.1, (false,x,y) :: p.2)) ++
      (plans (x :: u) v).map (fun p => (y :: p.1, (true,y,x) :: p.2))
termination_by u v => u.length + v.length

omit [DecidableEq X] in
private lemma plans_run (u v : List X) (p : List X × List (Event X)) (hp : p ∈ plans u v) :
    Run u v p.1 p.2 := by
  induction h : u.length + v.length using Nat.strong_induction_on generalizing u v p with
  | h n ih =>
    cases u with
    | nil =>
      simp only [plans, List.mem_cons, List.not_mem_nil, or_false] at hp
      subst p
      exact .nilL v
    | cons x u =>
      cases v with
      | nil =>
        simp only [plans, List.mem_cons, List.not_mem_nil, or_false] at hp
        subst p
        exact .nilR (x :: u)
      | cons y v =>
        simp only [plans, List.mem_append, List.mem_map] at hp
        rcases hp with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
        · exact .left (ih _ (by simp only [List.length_cons] at h ⊢; omega) u (y :: v) q hq rfl)
        · exact .right (ih _ (by simp only [List.length_cons] at h ⊢; omega) (x :: u) v q hq rfl)

omit [DecidableEq X] in
private lemma Run.mem {u v w : List X} {es : List (Event X)} (h : Run u v w es) (z : X) :
    z ∈ w ↔ z ∈ u ∨ z ∈ v := by
  induction h with
  | nilL => simp
  | nilR => simp
  | left ht ih => simp only [List.mem_cons, ih]; tauto
  | right ht ih => simp only [List.mem_cons, ih]; tauto

omit [DecidableEq X] in
private lemma Run.events_mem {u v w : List X} {es : List (Event X)} (h : Run u v w es)
    {e : Event X} (he : e ∈ es) : (e.2.1 ∈ u ∨ e.2.1 ∈ v) ∧ (e.2.2 ∈ u ∨ e.2.2 ∈ v) := by
  induction h with
  | nilL => simp at he
  | nilR => simp at he
  | left ht ih =>
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · simp
    · obtain ⟨h1,h2⟩ := ih he
      simp only [List.mem_cons] at h1 h2 ⊢; tauto
  | right ht ih =>
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · simp
    · obtain ⟨h1,h2⟩ := ih he
      simp only [List.mem_cons] at h1 h2 ⊢; tauto

variable {K : Type*} [Field K]
private def branch (f1 f2 : X → X → K) (e : Event X) : K :=
  if e.1 then f2 e.2.2 e.2.1 else f1 e.2.1 e.2.2

private def pathCoeff (f1 f2 : X → X → K) (es : List (Event X)) : K :=
  (es.map (branch f1 f2)).prod

private def pathTicks (a b : X) (es : List (Event X)) : ℕ :=
  (es.map (fun e => tick a b e.2.1 e.2.2)).sum

private lemma Run.toAPath (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {u v w : List X} {es : List (Event X)} (h : Run u v w es)
    (hc : pathCoeff f1 f2 es ≠ 0) (a b : X) :
    APath (allowed f1 f2) a b u v w (pathTicks a b es) := by
  induction h with
  | nilL v => exact .nilL v
  | nilR u => exact .nilR u
  | @left x y u v w es ht ih =>
    have hc' : f1 x y ≠ 0 ∧ pathCoeff f1 f2 es ≠ 0 := by
      simpa [pathCoeff,branch,mul_ne_zero_iff] using hc
    have hs : allowed f1 f2 x y := by
      by_cases hh : x = y
      · subst y; simp [allowed,hc'.1]
      · simp [allowed,hh,hc'.1]
    simpa [pathTicks, Nat.add_comm] using APath.left hs (ih hc'.2)
  | @right x y u v w es ht ih =>
    have hc' : f2 x y ≠ 0 ∧ pathCoeff f1 f2 es ≠ 0 := by
      simpa [pathCoeff,branch,mul_ne_zero_iff] using hc
    have hs : allowed f1 f2 y x := by
      by_cases hh : y = x
      · subst y; simp [allowed,hc'.1]
      · simpa [allowed,hh,coeff_comm f1 f2 hws hh] using hc'.1
    simpa [pathTicks, Nat.add_comm] using APath.right hs (ih hc'.2)
end D5.S1.Words.WeakShuffleNormalization
namespace D5.S1.Words.WeakShuffleNormalization
variable {X K : Type*} [Field K] [DecidableEq X]
private noncomputable def planSum (f1 f2 : X → X → K)
    (L : List (List X × List (Event X))) : KX X K :=
  (L.map (fun p => Finsupp.single p.1 (pathCoeff f1 f2 p.2))).sum
omit [DecidableEq X] in
private lemma planSum_branch (f1 f2 : X → X → K) (side : Bool) (x y : X)
    (L : List (List X × List (Event X))) :
    planSum f1 f2 (L.map (fun p => (x :: p.1,(side,x,y) :: p.2))) =
      branch f1 f2 (side,x,y) • Finsupp.lmapDomain K K (List.cons x) (planSum f1 f2 L) := by
  induction L with
  | nil => simp [planSum]
  | cons p L ih =>
    simp only [planSum, List.map_cons, List.sum_cons, List.map_map] at ih ⊢
    rw [map_add, smul_add, ← ih]
    simp [pathCoeff, Finsupp.lmapDomain, Finsupp.smul_single]

omit [DecidableEq X] in
private lemma planSum_eq_wsWord (f1 f2 : X → X → K) (u v : List X) :
    planSum f1 f2 (plans u v) = wsWord f1 f2 u v := by
  induction h : u.length + v.length using Nat.strong_induction_on generalizing u v with
  | h n ih =>
    cases u with
    | nil => simp [plans,planSum,pathCoeff,wsWord]
    | cons x u =>
      cases v with
      | nil => simp [plans,planSum,pathCoeff,wsWord]
      | cons y v =>
        simp only [plans, wsWord]
        have hadd (L M : List (List X × List (Event X))) :
            planSum f1 f2 (L ++ M) = planSum f1 f2 L + planSum f1 f2 M := by
          simp [planSum]
        rw [hadd, planSum_branch, planSum_branch]
        rw [ih _ (by simp only [List.length_cons] at h ⊢; omega) u (y :: v) rfl,
          ih _ (by simp only [List.length_cons] at h ⊢; omega) (x :: u) v rfl]
        rfl
end D5.S1.Words.WeakShuffleNormalization
namespace D5.S1.Words.WeakShuffleNormalization
variable {X K : Type*} [Field K] [DecidableEq X]
private def Exceptional (f1 : X → X → K) (e : X × X) : Prop :=
  e.1 ≠ e.2 ∧ f1 e.1 e.2 ≠ 0 ∧ f1 e.1 e.2 ≠ 1
private noncomputable def edgeFactor (f1 : X → X → K) (e : X × X) : K := by
  classical exact if Exceptional f1 e then f1 e.1 e.2 else 1
omit [DecidableEq X] in
private lemma edgeFactor_ne_zero (f1 : X → X → K) (e : X × X) : edgeFactor f1 e ≠ 0 := by
  classical
  by_cases h : Exceptional f1 e
  · simpa [edgeFactor,h] using h.2.1
  · simp [edgeFactor,h]

private lemma norm1_factor (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2) (x y : X) :
    f1 x y = norm1 f1 x y * edgeFactor f1 (x,y) := by
  classical
  by_cases hxy : x = y
  · subst y; simp [norm1,edgeFactor,Exceptional]
  · by_cases he : Exceptional f1 (x,y)
    · simp [norm1,edgeFactor,Exceptional,hxy,he.2.1,he.2.2]
    · by_cases hr : Exceptional f1 (y,x)
      · have hz := exceptional_reverse_zero f1 f2 hws hr.1 hr.2.1 hr.2.2
        simp [norm1,edgeFactor,Exceptional,hxy,hz,hr.2.1,hr.2.2]
      · have he' : ¬ (f1 x y ≠ 0 ∧ f1 x y ≠ 1) := by simpa [Exceptional,hxy] using he
        have hr' : ¬ (f1 y x ≠ 0 ∧ f1 y x ≠ 1) := by simpa [Exceptional,(Ne.symm hxy)] using hr
        simp [norm1,edgeFactor,he,Set.mem_insert_iff,not_or,hxy,he',hr']

private lemma branch_factor (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2) (e : Event X) :
    branch f1 f2 e = branch (norm1 f1) (norm2 f1 f2) e * edgeFactor f1 e.2 := by
  classical
  obtain ⟨side,x,y⟩ := e
  cases side with
  | false => exact norm1_factor f1 f2 hws x y
  | true =>
    by_cases hxy : x = y
    · subst y; simp [branch,norm2,edgeFactor,Exceptional]
    · simp only [branch, ↓reduceIte, norm2, (Ne.symm hxy), ↓reduceIte]
      rw [← coeff_comm f1 f2 hws hxy]
      exact norm1_factor f1 f2 hws x y

private noncomputable def pathFactor (f1 : X → X → K) (es : List (Event X)) : K :=
  (es.map (fun e => edgeFactor f1 e.2)).prod
private lemma pathCoeff_factor (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    (es : List (Event X)) : pathCoeff f1 f2 es =
      pathCoeff (norm1 f1) (norm2 f1 f2) es * pathFactor f1 es := by
  induction es with
  | nil => simp [pathCoeff,pathFactor]
  | cons e es ih =>
    simp only [pathCoeff,pathFactor,List.map_cons,List.prod_cons] at ih ⊢
    rw [branch_factor f1 f2 hws e,ih]
    ring

private lemma pathCoeff_zero_iff (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    (es : List (Event X)) : pathCoeff f1 f2 es = 0 ↔
      pathCoeff (norm1 f1) (norm2 f1 f2) es = 0 := by
  have hf : pathFactor f1 es ≠ 0 := by
    induction es with
    | nil => simp [pathFactor]
    | cons e es ih =>
      change edgeFactor f1 e.2 * pathFactor f1 es ≠ 0
      exact mul_ne_zero (edgeFactor_ne_zero f1 e.2) ih
  rw [pathCoeff_factor f1 f2 hws,mul_eq_zero]
  simp [hf]

private lemma event_product (f1 : X → X → K) (S : Finset (X × X)) (x y : X)
    (hxy : (x, y) ∈ S) :
    (∏ e ∈ S, edgeFactor f1 e ^ tick e.1 e.2 x y) = edgeFactor f1 (x,y) := by
  classical
  rw [Finset.prod_eq_single (x,y)]
  · simp [tick]
  · intro e he hne
    have hh : ¬ (x = e.1 ∧ y = e.2) := by
      rintro ⟨rfl,rfl⟩; exact hne rfl
    simp [tick,hh]
  · exact fun hn => False.elim (hn hxy)

private lemma pathFactor_product (f1 : X → X → K) (S : Finset (X × X))
    (es : List (Event X)) (hm : ∀ e ∈ es, e.2 ∈ S) :
    pathFactor f1 es = ∏ e ∈ S, edgeFactor f1 e ^ pathTicks e.1 e.2 es := by
  classical
  induction es with
  | nil => simp [pathFactor,pathTicks]
  | cons ev es ih =>
    rw [show pathFactor f1 (ev :: es) = edgeFactor f1 ev.2 * pathFactor f1 es by simp [pathFactor]]
    rw [ih (fun e he => hm e (List.mem_cons_of_mem _ he))]
    simp only [pathTicks,List.map_cons,List.sum_cons,pow_add,Finset.prod_mul_distrib]
    rw [event_product f1 S ev.2.1 ev.2.2 (hm ev (by simp))]
end D5.S1.Words.WeakShuffleNormalization
namespace D5.S1.Words.WeakShuffleNormalization
variable {X : Type*} [DecidableEq X]
private lemma marker_false_of_not_mem (P : X → Bool) (b : X) (w : List X) (hb : b ∉ w) :
    marker P b w = false := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have hxb : x ≠ b := by intro he; subst x; exact hb (by simp)
    have hw : b ∉ w := fun hm => hb (by simp [hm])
    simp [marker,hxb,ih hw]
private lemma expo_zero_of_marker_false (P : X → Bool) (a b : X) (w : List X)
    (hm : marker P b w = false) : expo P a b w = 0 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    by_cases hx : P x = true
    · have hw : marker P b w = false := by simpa [marker,hx] using hm
      simp [expo,hx,hw,ih hw]
    · have hxf : P x = false := by cases he : P x <;> simp_all
      simp [expo,hxf]
private lemma expo_zero_of_not_mem_a (P : X → Bool) (a b : X) (w : List X) (ha : a ∉ w) :
    expo P a b w = 0 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have hxa : x ≠ a := by intro he; subst x; exact ha (by simp)
    have hw : a ∉ w := fun hm => ha (by simp [hm])
    simp [expo,hxa,ih hw]

variable {K : Type*} [Field K]
private noncomputable def weight (f1 : X → X → K) (e : X × X) (w : List X) : K :=
  (edgeFactor f1 e)⁻¹ ^ expo (region f1 e.2) e.1 e.2 w
private noncomputable def qOn (f1 : X → X → K) (S : Finset (X × X)) (w : List X) : K :=
  ∏ e ∈ S, weight f1 e w
private noncomputable def q (f1 : X → X → K) (w : List X) : K :=
  qOn f1 (w.toFinset ×ˢ w.toFinset) w

private lemma weight_one_of_missing (f1 : X → X → K) (e : X × X) (w : List X)
    (he : e ∉ w.toFinset ×ˢ w.toFinset) : weight f1 e w = 1 := by
  classical
  have he' : e.1 ∉ w ∨ e.2 ∉ w := by
    simpa only [Finset.mem_product,List.mem_toFinset,not_and_or] using he
  rcases he' with ha | hb
  · simp [weight,expo_zero_of_not_mem_a _ _ _ _ ha]
  · simp [weight,expo_zero_of_marker_false _ _ _ _ (marker_false_of_not_mem _ _ _ hb)]

private lemma q_eq_qOn (f1 : X → X → K) (w : List X) (S : Finset (X × X))
    (hw : w.toFinset ×ˢ w.toFinset ⊆ S) : q f1 w = qOn f1 S w := by
  classical
  apply Finset.prod_subset hw
  intro e he hnot
  exact weight_one_of_missing f1 e w hnot

private lemma q_ne_zero (f1 : X → X → K) (w : List X) : q f1 w ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro e he
  exact pow_ne_zero _ (inv_ne_zero (edgeFactor_ne_zero f1 e))

private lemma scalar_weight_identity (k : K) (hk : k ≠ 0) (t hu hv hw : ℕ)
    (h : t + hu + hv = hw) : (k⁻¹)^hw * k^t = (k⁻¹)^hu * (k⁻¹)^hv := by
  rw [← h, pow_add, pow_add]
  calc
    (k⁻¹)^t * (k⁻¹)^hu * (k⁻¹)^hv * k^t =
        ((k⁻¹)^t * k^t) * ((k⁻¹)^hu * (k⁻¹)^hv) := by ring
    _ = (k⁻¹)^hu * (k⁻¹)^hv := by simp [inv_mul_cancel₀ (pow_ne_zero t hk)]

private lemma Run.weight_factor [CharZero K] (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {u v w : List X} {es : List (Event X)} (h : Run u v w es)
    (hc : pathCoeff f1 f2 es ≠ 0) (e : X × X) :
    weight f1 e w * edgeFactor f1 e ^ pathTicks e.1 e.2 es =
      weight f1 e u * weight f1 e v := by
  classical
  by_cases he : Exceptional f1 e
  · have hp := h.toAPath f1 f2 hws hc e.1 e.2
    have H := actual_barriers f1 f2 hws he.1 he.2.1 he.2.2
    have ht := hp.exponents H
    exact scalar_weight_identity (edgeFactor f1 e) (edgeFactor_ne_zero f1 e)
      _ _ _ _ ht
  · simp [weight,edgeFactor,he]

private lemma Run.qOn_factor [CharZero K] (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {u v w : List X} {es : List (Event X)} (h : Run u v w es)
    (hc : pathCoeff f1 f2 es ≠ 0) (S : Finset (X × X))
    (hm : ∀ e ∈ es, e.2 ∈ S) :
    qOn f1 S w * pathFactor f1 es = qOn f1 S u * qOn f1 S v := by
  classical
  rw [pathFactor_product f1 S es hm]
  simp only [qOn,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e he
  exact h.weight_factor f1 f2 hws hc e

private lemma Run.q_identity [CharZero K] (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    {u v w : List X} {es : List (Event X)} (h : Run u v w es) :
    q f1 w * pathCoeff f1 f2 es = q f1 u * q f1 v *
      pathCoeff (norm1 f1) (norm2 f1 f2) es := by
  classical
  by_cases hc : pathCoeff f1 f2 es = 0
  · have hg := (pathCoeff_zero_iff f1 f2 hws es).mp hc
    simp [hc,hg]
  · let S := (u.toFinset ∪ v.toFinset) ×ˢ (u.toFinset ∪ v.toFinset)
    have hu : u.toFinset ×ˢ u.toFinset ⊆ S := by
      intro e he; simp only [S,Finset.mem_product,Finset.mem_union] at he ⊢; tauto
    have hv : v.toFinset ×ˢ v.toFinset ⊆ S := by
      intro e he; simp only [S,Finset.mem_product,Finset.mem_union] at he ⊢; tauto
    have hw : w.toFinset ×ˢ w.toFinset ⊆ S := by
      intro e he
      simp only [S,Finset.mem_product,Finset.mem_union,List.mem_toFinset] at he ⊢
      exact ⟨(h.mem e.1).mp he.1,(h.mem e.2).mp he.2⟩
    have hm : ∀ e ∈ es, e.2 ∈ S := by
      intro e he
      simpa only [S,Finset.mem_product,Finset.mem_union,List.mem_toFinset] using h.events_mem he
    rw [q_eq_qOn f1 u S hu,q_eq_qOn f1 v S hv,q_eq_qOn f1 w S hw,
      pathCoeff_factor f1 f2 hws es]
    calc
      qOn f1 S w * (pathCoeff (norm1 f1) (norm2 f1 f2) es * pathFactor f1 es) =
        (qOn f1 S w * pathFactor f1 es) * pathCoeff (norm1 f1) (norm2 f1 f2) es := by ring
      _ = _ := by rw [h.qOn_factor f1 f2 hws hc S hm]
end D5.S1.Words.WeakShuffleNormalization
namespace D5.S1.Words.WeakShuffleNormalization
variable {X K : Type*} [Field K] [DecidableEq X]
private noncomputable def diagonal (r : List X → K) : KX X K →ₗ[K] KX X K :=
  Finsupp.linearCombination K (fun w => Finsupp.single w (r w))
omit [DecidableEq X] in
@[simp] private lemma diagonal_single (r : List X → K) (w : List X) (c : K) :
    diagonal r (Finsupp.single w c) = Finsupp.single w (c * r w) := by
  simp [diagonal,Finsupp.linearCombination_single,Finsupp.smul_single]

private noncomputable def diagonalEquiv (r : List X → K) (hr : ∀ w, r w ≠ 0) :
    KX X K ≃ₗ[K] KX X K :=
  LinearEquiv.ofLinearMap (diagonal r) (diagonal (fun w => (r w)⁻¹))
    (by
      apply Finsupp.lhom_ext
      intro w c
      simp [LinearMap.comp_apply,hr])
    (by
      apply Finsupp.lhom_ext
      intro w c
      simp [LinearMap.comp_apply,hr])

private lemma diagonal_wsWord [CharZero K] (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    (u v : List X) : diagonal (q f1) (wsWord f1 f2 u v) =
      (q f1 u * q f1 v) • wsWord (norm1 f1) (norm2 f1 f2) u v := by
  rw [← planSum_eq_wsWord,← planSum_eq_wsWord]
  unfold planSum
  rw [map_list_sum]
  rw [List.smul_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply,diagonal_single,Finsupp.smul_single,smul_eq_mul]
  congr 1
  rw [mul_comm]
  exact (plans_run u v p hp).q_identity f1 f2 hws

private lemma diagonal_wsMul [CharZero K] (f1 f2 : X → X → K) (hws : IsWeakShuffle f1 f2)
    (x y : KX X K) : diagonal (q f1) (wsMul f1 f2 x y) =
      wsMul (norm1 f1) (norm2 f1 f2) (diagonal (q f1) x) (diagonal (q f1) y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [wsMul]
  | add x z hx hz =>
    rw [wsMul_add_left,map_add,map_add,wsMul_add_left,hx,hz]
  | single u a =>
    induction y using Finsupp.induction_linear with
    | zero => simp [wsMul]
    | add y z hy hz =>
      rw [wsMul_add_right,map_add,map_add,wsMul_add_right,hy,hz]
    | single v b =>
      simp only [diagonal_single]
      have hs (f g : X → X → K) (r s : K) :
          wsMul f g (Finsupp.single u r) (Finsupp.single v s) = (r*s) • wsWord f g u v := by
        simp [wsMul]
      rw [hs,hs,map_smul,diagonal_wsWord f1 f2 hws,smul_smul]
      congr 1
      ring

theorem result : claim := by
  intro K _ _ X _ f1 f2 hws
  let Phi := diagonalEquiv (q f1) (q_ne_zero f1)
  refine ⟨Phi, ?_, ?_⟩
  · change diagonal (q f1) (Finsupp.single [] 1) = Finsupp.single [] 1
    simp [q,qOn]
  · intro x y
    exact diagonal_wsMul f1 f2 hws x y

end D5.S1.Words.WeakShuffleNormalization
