/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all OmegaInit.Prelude
public import Mathlib.Data.Nat.Fib.Zeckendorf
public import OmegaChecks.NatCorrespondence
public import OmegaMath.Arithmetic.WDigits.Codec

/-! Conversion between zero-based W positions and Mathlib's occupied Fibonacci indices. -/

noncomputable section

namespace OmegaChecks.WDigitCorrespondence

open Omega.Arithmetic (NatList)
open OmegaChecks.NatCorrespondence
open Omega.Arithmetic.WDigits (decode encode IsCanonical LegalBelow wValue)

/-- Read zero-based weight positions as Fibonacci indices in decreasing order. -/
@[expose] public def indices : NatList → List Nat :=
  NatList.rec [] (fun index _ tail => (toStd index + 2) :: tail)

/-- The weight of each strict position is the Mathlib Fibonacci number at its shifted index. -/
public theorem toStd_wValue (index : Omega.Nat) :
    toStd (wValue index) = Nat.fib (toStd index + 2) :=
  toStd_fib index.succ.succ

/-- Decoding agrees with summing the Mathlib Fibonacci weights of the occupied indices. -/
public theorem toStd_decode (digits : NatList) :
    toStd (decode digits) = ((indices digits).map Nat.fib).sum := by
  induction digits using NatList.rec with
  | nil => rfl
  | cons index tail ih =>
    change toStd ((wValue index).add (decode tail)) =
      Nat.fib (toStd index + 2) + ((indices tail).map Nat.fib).sum
    rw [toStd_add, toStd_wValue, ih]

private theorem rep_cons_iff (head : Nat) (tail : List Nat) :
    List.IsZeckendorfRep (head :: tail) ↔
      tail.IsZeckendorfRep ∧ tail.headD 0 + 2 ≤ head := by
  cases tail <;> simp [List.IsZeckendorfRep, List.isChain_cons_cons, and_comm]

private theorem toStd_pred (index : Omega.Nat) :
    toStd index.pred = toStd index - 1 := by
  induction index using Omega.Nat.rec with
  | zero => exact congrArg toStd (fromOmegaEq Omega.Nat.pred_zero)
  | succ n _ => exact congrArg toStd (fromOmegaEq (Omega.Nat.pred_succ n))

private theorem tail_bound (index : Omega.Nat) (tail : NatList) :
    (indices tail).headD 0 ≤ toStd index.pred + 1 ↔
      (indices tail).headD 0 + 2 ≤ toStd index + 2 := by
  rw [toStd_pred]
  induction tail using NatList.rec with
  | nil => simp [indices]
  | cons next rest _ =>
    change toStd next + 2 ≤ toStd index - 1 + 1 ↔
      toStd next + 2 + 2 ≤ toStd index + 2
    omega

private theorem legalBelow_iff (digits : NatList) (bound : Omega.Nat) :
    LegalBelow bound digits ↔
      (indices digits).IsZeckendorfRep ∧ (indices digits).headD 0 ≤ toStd bound + 1 := by
  induction digits using NatList.rec generalizing bound with
  | nil =>
    exact ⟨fun _ => ⟨List.IsZeckendorfRep_nil, Nat.zero_le _⟩, fun _ => Omega.True.intro⟩
  | cons index tail ih =>
    have order : Omega.Nat.lt index bound ↔ toStd index + 2 ≤ toStd bound + 1 := by
      have step := (toStd_le_iff index.succ bound).symm
      change Omega.Nat.lt index bound ↔ toStd index + 1 ≤ toStd bound at step
      constructor
      · intro h
        have bound' := step.mp h
        omega
      · intro h
        exact step.mpr (by omega)
    have tailRep := ih index.pred
    change Omega.And (Omega.Nat.lt index bound) (LegalBelow index.pred tail) ↔
      List.IsZeckendorfRep ((toStd index + 2) :: indices tail) ∧
        toStd index + 2 ≤ toStd bound + 1
    rw [rep_cons_iff]
    exact ⟨
      fun h =>
        let ⟨canonical, below⟩ := tailRep.mp h.right
        ⟨⟨canonical, (tail_bound index tail).mp below⟩, order.mp h.left⟩,
      fun h => Omega.And.intro (order.mpr h.2)
        (tailRep.mpr ⟨h.1.1, (tail_bound index tail).mpr h.1.2⟩)⟩

/-- A strict word is canonical exactly when its shifted indices form a Mathlib representation. -/
public theorem isCanonical_iff (digits : NatList) :
    IsCanonical digits ↔ (indices digits).IsZeckendorfRep := by
  induction digits using NatList.rec with
  | nil => exact ⟨fun _ => List.IsZeckendorfRep_nil, fun _ => Omega.True.intro⟩
  | cons index tail _ =>
    change LegalBelow index.pred tail ↔
      List.IsZeckendorfRep ((toStd index + 2) :: indices tail)
    rw [legalBelow_iff, rep_cons_iff, tail_bound]

/-- The strict encoder computes the same occupied Fibonacci indices as Mathlib. -/
public theorem indices_encode (n : Omega.Nat) :
    indices (encode n) = Nat.zeckendorf (toStd n) := by
  have decoded : decode (encode n) = n :=
    Omega.Eq.rec (motive := fun value _ => decode (encode n) = value) rfl
      (Omega.Arithmetic.WDigits.decode_encode n)
  rw [← congrArg toStd decoded, toStd_decode]
  exact (Nat.zeckendorf_sum_fib
    ((isCanonical_iff (encode n)).mp (Omega.Arithmetic.WDigits.encode_isCanonical n))).symm

/-- Every canonical Mathlib representation comes from a canonical strict word. -/
public theorem isZeckendorfRep_iff_exists (digits : List Nat) :
    digits.IsZeckendorfRep ↔ ∃ word : NatList, IsCanonical word ∧ indices word = digits := by
  constructor
  · intro rep
    let n := fromStd (digits.map Nat.fib).sum
    refine ⟨encode n, Omega.Arithmetic.WDigits.encode_isCanonical n, ?_⟩
    rw [indices_encode, toStd_fromStd]
    exact Nat.zeckendorf_sum_fib rep
  · rintro ⟨word, canonical, rfl⟩
    exact (isCanonical_iff word).mp canonical

end OmegaChecks.WDigitCorrespondence
