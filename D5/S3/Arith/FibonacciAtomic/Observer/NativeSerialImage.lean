/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialImage
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Prefix-free terminal native reply words give the sharp four-power whole-output bound. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
import Mathlib.Data.List.Infix
import Mathlib.Data.Fintype.Vector

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Reply)
open NativeSerialMachine

/-- Terminal words are prefix-free; equality also fixes every silent/update
step, every epoch/address, and the entire terminal output. -/
theorem terminal_prefix_free {C O : Type} {δ : C → Op C O}
    {c : C} {N : Nat} {u v : Source} {t s : Trace} {o p : O}
    (first : Run δ c N u t o) (second : Run δ c N v s p)
    (pre : answers t <+: answers s) : t = s ∧ o = p := by
  induction first generalizing v s p with
  | stop h =>
      cases second with
      | stop hq =>
          exact ⟨rfl,Op.stop.inj (h.symm.trans hq)⟩
      | localStep hq q =>
          cases h.symm.trans hq
      | update hq q =>
          cases h.symm.trans hq
      | @read _ _ v b j z s p hq hz q =>
          cases h.symm.trans hq
  | localStep h run ih =>
      cases second with
      | stop hq =>
          cases h.symm.trans hq
      | localStep hq q =>
          have he := Op.localStep.inj (h.symm.trans hq)
          cases he
          obtain ⟨ht,ho⟩ := ih q (by simpa [answers,reads] using pre)
          exact ⟨congrArg (List.cons _) ht,ho⟩
      | update hq q =>
          cases h.symm.trans hq
      | @read _ _ v b j z s p hq hz q =>
          cases h.symm.trans hq
  | update h run ih =>
      cases second with
      | stop hq =>
          cases h.symm.trans hq
      | localStep hq q =>
          cases h.symm.trans hq
      | update hq q =>
          have he := Op.applyRho.inj (h.symm.trans hq)
          cases he
          obtain ⟨ht,ho⟩ := ih q (by simpa [answers,reads] using pre)
          exact ⟨congrArg (List.cons _) ht,ho⟩
      | @read _ _ v b j z s p hq hz q =>
          cases h.symm.trans hq
  | @read c e r a k y t o h hy run ih =>
      cases second with
      | stop hq =>
          cases h.symm.trans hq
      | localStep hq q =>
          cases h.symm.trans hq
      | update hq q =>
          cases h.symm.trans hq
      | @read _ _ v b j z s p hq hz q =>
          obtain ⟨ha,hk⟩ := Op.read.inj (h.symm.trans hq)
          cases ha
          cases hk
          have hp : y = z ∧ answers t <+: answers s := by
            simpa [answers,reads] using pre
          rcases hp with ⟨rfl,hp⟩
          obtain ⟨ht,ho⟩ := ih q hp
          exact ⟨congrArg (List.cons _) ht,ho⟩

/-- Padding is a proof construction, not an operation on the physical source. -/
def pad (K : Nat) (w : List Reply) (bound : w.length ≤ K) : List.Vector Reply K :=
  ⟨w ++ List.replicate (K-w.length) .absent, by simp; omega⟩

private theorem pad_comparable {K : Nat} {w z : List Reply}
    {hw : w.length ≤ K} {hz : z.length ≤ K}
    (same : pad K w hw = pad K z hz) : w <+: z ∨ z <+: w := by
  have eq : w ++ List.replicate (K-w.length) .absent =
      z ++ List.replicate (K-z.length) .absent := congrArg Subtype.val same
  have left : w <+: w ++ List.replicate (K-w.length) .absent := ⟨_,rfl⟩
  have right : z <+: w ++ List.replicate (K-w.length) .absent := by
    rw [eq]; exact ⟨_,rfl⟩
  by_cases h : w.length ≤ z.length
  · left
    apply List.prefix_iff_eq_take.mpr
    rw [List.prefix_iff_eq_take.mp right, List.take_take, Nat.min_eq_left h]
    exact List.prefix_iff_eq_take.mp left
  · right
    have h : z.length ≤ w.length := by omega
    apply List.prefix_iff_eq_take.mpr
    rw [List.prefix_iff_eq_take.mp left, List.take_take, Nat.min_eq_left h]
    exact List.prefix_iff_eq_take.mp right

/-- For arbitrary whole outputs, bounded chronological reads give at most 4^K
actual terminal values. Sourcewise runtime need not have a uniform bound. -/
theorem bounded_serial_output_image {C O : Type} (δ : C → Op C O) (c : C)
    (N K : Nat) (U : Set Source) (hne : U.Nonempty) (F : Source → O)
    (correct : ∀ u ∈ U, ∃ t, Run δ c N (substitution^[N] u) t (F u) ∧
      (answers t).length ≤ K) :
    ∃ labels : Finset O, labels.card ≤ 4^K ∧ ∀ u ∈ U, F u ∈ labels := by
  classical
  let run (u : U) := (correct u.val u.property).choose
  have run_ok (u : U) : Run δ c N (substitution^[N] u.val) (run u) (F u.val) ∧
      (answers (run u)).length ≤ K := (correct u.val u.property).choose_spec
  let code (u : U) := pad K (answers (run u)) (run_ok u).2
  have code_output (u v : U) (eq : code u = code v) : F u.val = F v.val := by
    rcases pad_comparable eq with h | h
    · exact (terminal_prefix_free (run_ok u).1 (run_ok v).1 h).2
    · exact (terminal_prefix_free (run_ok v).1 (run_ok u).1 h).2.symm
  let decode (w : List.Vector Reply K) : O :=
    if h : ∃ u : U, code u = w then F h.choose.val else F hne.choose
  refine ⟨Finset.univ.image decode, ?_, ?_⟩
  · calc
      (Finset.univ.image decode).card ≤ (Finset.univ : Finset (List.Vector Reply K)).card :=
        Finset.card_image_le
      _ = 4^K := by
        rw [Finset.card_univ, Fintype.card_congr (Equiv.vectorEquivFin Reply K)]
        simp [show Fintype.card Reply = 4 from by decide]
  · intro u hu
    apply Finset.mem_image.mpr
    refine ⟨code ⟨u,hu⟩, Finset.mem_univ _, ?_⟩
    have h : ∃ v : U, code v = code ⟨u,hu⟩ := ⟨⟨u,hu⟩,rfl⟩
    dsimp [decode]
    rw [dif_pos h]
    exact code_output h.choose ⟨u,hu⟩ h.choose_spec

end D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage
