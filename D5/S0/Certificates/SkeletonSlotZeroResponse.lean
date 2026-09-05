/- GID: D5/S0/Certificates/SkeletonSlotZeroResponse
   generality: G
   mirror-B: D5/B/S0/Certificates/SkeletonSlotZeroResponse
   mirror-E: none(waiver:exact-shared-transition-factorization)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank]
   digest: Zero-gap responses of the existing slot skeleton factor through the same recurrent carrier, giving exact rank and minor constraints without discarding legal transitions. -/

import D5.S0.Certificates.SkeletonSlotCNF
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Function.Iterate

/- The existing Skeleton and SlotWitness own all machine semantics. The S3
   HankelRankMinimality node already owns general linear-system Hankel theory;
   this module supplies the finite deterministic-slot bridge, using upstream
   Matrix multiplication and rank rather than defining another rank notion.
   No output on an unobserved power input is assumed. Slot probes are latent
   variables when this theorem is applied to an unknown candidate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.SkeletonSlotZeroResponse

open D5.S0.Automata.BinaryZeckendorfBlockSkeleton
open D5.S0.Certificates.SkeletonSlotCNF
open scoped BigOperators

variable {r s : Nat} {K : Skeleton (Fin 4) (Fin r)}

/-- Reuse the single zero transition of the existing serialization. -/
def advance (W : SlotWitness K s) (k : Nat) (q : Fin r) : Fin r :=
  (W.zeroTarget^[k]) q

/-- All zero lengths are iterates of the same map. -/
theorem advance_add (W : SlotWitness K s) (i j : Nat) (q : Fin r) :
    advance W (i + j) q = advance W j (advance W i q) := by
  unfold advance
  rw [Nat.add_comm i j, Function.iterate_add_apply]

/-- An arbitrary number of zero blocks can be removed using the original
Option-valued evaluation, including every possible continuation. -/
theorem evalFrom_zero_prefix (W : SlotWitness K s) (k : Nat) (q : Fin r)
    (tail : List ReturnBlock) (terminal : TerminalChannel) :
    K.evalFrom q (List.replicate k .zero ++ tail) terminal =
      K.evalFrom (advance W k q) tail terminal := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
      simpa only [List.replicate_succ, List.cons_append, Skeleton.evalFrom,
        W.zero_eq, Option.bind_some, advance, Function.iterate_succ_apply]
        using ih (W.zeroTarget q)

/-- After entering a transient slot, k+1 zeroes followed by one select this
slot. Different k use the same zeroTarget, slotOf and returnTarget. -/
def gapSlot (W : SlotWitness K s) (k : Nat) (t : Fin s) : Fin s :=
  W.slotOf (advance W k (W.returnTarget t))

/-- The shared-gap factorization is tied to existing block evaluation. -/
theorem evalFrom_one_zero_gap (W : SlotWitness K s) (q : Fin r) (k : Nat) :
    K.evalFrom q (.oneZero :: List.replicate k .zero) .transient =
      some (W.transientOutput (gapSlot W k (W.slotOf q))) := by
  change (K.oneSignature q).bind (fun signature => signature.2.bind
    (fun next => K.evalFrom next (List.replicate k .zero) .transient)) = _
  rw [W.one_eq]
  simp only [Option.bind_some]
  have hz := evalFrom_zero_prefix W k (W.returnTarget (W.slotOf q)) [] .transient
  simp only [List.append_nil] at hz
  rw [hz]
  change (K.oneSignature (advance W k (W.returnTarget (W.slotOf q)))).map Prod.fst = _
  rw [W.one_eq]
  rfl

/-- Exact one-hot readout of either a digit or a selected transient slot.
The latter is a latent structural readout, not a supplied arithmetic oracle. -/
def probe (W : SlotWitness K s) : Fin 4 ⊕ Fin s → Fin r → Rat
  | .inl d, q => if K.zeroOutput q = d then 1 else 0
  | .inr t, q => if W.slotOf q = t then 1 else 0

/-- Sampled joint zero responses with arbitrary row access states and delays. -/
def response (W : SlotWitness K s) {m n : Nat}
    (origin : Fin m → Fin r) (rowDelay : Fin m → Nat)
    (columnDelay : Fin n → Nat) (test : Fin n → Fin 4 ⊕ Fin s) :
    Matrix (Fin m) (Fin n) Rat :=
  fun i j => probe W (test j)
    (advance W (rowDelay i + columnDelay j) (origin i))

/-- One-hot intermediate recurrent states. -/
def reach (W : SlotWitness K s) {m : Nat}
    (origin : Fin m → Fin r) (rowDelay : Fin m → Nat) :
    Matrix (Fin m) (Fin r) Rat :=
  fun i q => if q = advance W (rowDelay i) (origin i) then 1 else 0

/-- The continuation response of each recurrent state. -/
def readout (W : SlotWitness K s) {n : Nat}
    (columnDelay : Fin n → Nat) (test : Fin n → Fin 4 ⊕ Fin s) :
    Matrix (Fin r) (Fin n) Rat :=
  fun q j => probe W (test j) (advance W (columnDelay j) q)

/-- The sampled joint response factors through the actual recurrent carrier.
No reachability, state ordering or self-loop restriction is imposed. -/
theorem response_factorization (W : SlotWitness K s) {m n : Nat}
    (origin : Fin m → Fin r) (rowDelay : Fin m → Nat)
    (columnDelay : Fin n → Nat) (test : Fin n → Fin 4 ⊕ Fin s) :
    response W origin rowDelay columnDelay test =
      reach W origin rowDelay * readout W columnDelay test := by
  ext i j
  simp [response, reach, readout, Matrix.mul_apply, ite_mul, advance_add]

/-- Every candidate supplies a completion whose response rank is at most r. -/
theorem response_rank_le (W : SlotWitness K s) {m n : Nat}
    (origin : Fin m → Fin r) (rowDelay : Fin m → Nat)
    (columnDelay : Fin n → Nat) (test : Fin n → Fin 4 ⊕ Fin s) :
    (response W origin rowDelay columnDelay test).rank ≤ r := by
  rw [response_factorization]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

/-- Every square response minor larger than the recurrent capacity vanishes. -/
theorem response_det_eq_zero (W : SlotWitness K s) {n : Nat}
    (origin : Fin n → Fin r) (rowDelay columnDelay : Fin n → Nat)
    (test : Fin n → Fin 4 ⊕ Fin s) (small : r < n) :
    (response W origin rowDelay columnDelay test).det = 0 := by
  by_contra hn
  have hr := response_rank_le W origin rowDelay columnDelay test
  have full := Matrix.rank_of_det_ne_zero hn
  rw [full, Fintype.card_fin] at hr
  exact (Nat.not_lt_of_ge hr) small

/-- A supplied right inverse is an exact finite lower-bound certificate for
this response, requiring neither numerical rank thresholds nor determinants. -/
theorem capacity_ge_of_right_inverse (W : SlotWitness K s) {n : Nat}
    (origin : Fin n → Fin r) (rowDelay columnDelay : Fin n → Nat)
    (test : Fin n → Fin 4 ⊕ Fin s) (inverse : Matrix (Fin n) (Fin n) Rat)
    (certificate : response W origin rowDelay columnDelay test * inverse = 1) :
    n ≤ r := by
  have lower := Matrix.rank_mul_le_left
    (response W origin rowDelay columnDelay test) inverse
  rw [certificate, Matrix.rank_one, Fintype.card_fin] at lower
  exact lower.trans (response_rank_le W origin rowDelay columnDelay test)

#print axioms evalFrom_one_zero_gap
#print axioms response_factorization
#print axioms response_det_eq_zero

end D5.S0.Certificates.SkeletonSlotZeroResponse
