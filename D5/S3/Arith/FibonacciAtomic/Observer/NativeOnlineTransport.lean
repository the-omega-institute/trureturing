/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeOnlineTransport
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Online phase compilation for fixed even-lag native reads, including prefixes cut inside a read macro. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
import D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeOnlineTransport

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open DelayedOriginalReadout (halfCeil guardAccept originalDecode originalQueries rights)
open NativeSerialMachine

/-- Compiler phases retain the original continuation and the first physical
reply. `needG` is explicit even though the absent branch completes without a
second physical read. -/
inductive Phase (C O : Type) where
  | ready : C → Phase C O
  | needC : Address → (Reply → C) → Reply → Phase C O
  | needG : Address → (Reply → C) → Reply → Phase C O

private def evenGuardQuery (N : Nat) (p : Address) : Address :=
  p.dropLast ++ rights (N / 2 + 1)

private def evenLabelQuery (N : Nat) (p : Address) : Address :=
  p ++ rights (halfCeil N)

private def evenCompiler {C O : Type} (N : Nat) (δ : C → Op C O) :
    Phase C O → Op (Phase C O) O
  | .ready c =>
      match δ c with
      | .localStep c' => .localStep (.ready c')
      | .applyRho c' => .applyRho (.ready c')
      | .stop o => .stop o
      | .read p f =>
          if hp : p = [] then
            .read (evenLabelQuery N p) (fun y => .ready (f (originalDecode N p [y])))
          else
            .read (evenGuardQuery N p) (fun y =>
              if guardAccept N y then .needC p f y else .needG p f y)
  | .needC p f g =>
      .read (evenLabelQuery N p) (fun y =>
        .ready (f (originalDecode N p [g, y])))
  | .needG p f _ => .localStep (.ready (f .absent))

/-- Consume one physical reply at a phase-machine operation. -/
def completion {C O : Type} : Op (Phase C O) O → Reply → Option (Phase C O)
  | .read _ k, y => some (k y)
  | _, _ => none

private theorem even_mod (k : Nat) : (2*k) % 2 = 0 := by omega
private theorem even_half (k : Nat) : (2*k) / 2 = k := by omega

private theorem even_query_shape (k : Nat) (hk : 1 ≤ k) (p : Address) (hp : p ≠ []) :
    originalQueries (2*k) p =
      [evenGuardQuery (2*k) p, evenLabelQuery (2*k) p] := by
  have hk0 : 2*k ≠ 0 := by omega
  simp [originalQueries, evenGuardQuery, evenLabelQuery, halfCeil,
    even_mod, even_half, hk0, hp]

private theorem even_decoder (k : Nat) (hk : 1 ≤ k) (p : Address) (u : Source)
    (g y : Reply)
    (hg : g = readout (evenGuardQuery (2*k) p) (substitution^[2*k] u))
    (hy : y = readout (evenLabelQuery (2*k) p) (substitution^[2*k] u))
    (hp : p ≠ []) :
    originalDecode (2*k) p [g, y] = readout p u := by
  have shape := even_query_shape k hk p hp
  have correct :=
    DelayedOriginalReadout.original_decoder_correct (2*k) p u
  rw [shape] at correct
  rw [hg, hy]
  simpa [evenGuardQuery, evenLabelQuery, halfCeil, even_mod, even_half] using correct

/-- Applying the newly introduced compiler to a pending present phase and
then consuming the physical label reply reaches the original continuation.
The relation is stated at the phase-machine boundary, so it remains valid for
an online prefix cut immediately before this label event. -/
theorem fixed_even_needC_completion {C O : Type} {δ : C → Op C O}
    (k : Nat) (hk : 1 ≤ k) (p : Address) (f : Reply → C)
    (g y : Reply) (u : Source) (hp : p ≠ [])
    (hg : g = readout (evenGuardQuery (2*k) p) (substitution^[2*k] u))
    (hy : y = readout (evenLabelQuery (2*k) p) (substitution^[2*k] u)) :
    completion (evenCompiler (2*k) δ (.needC p f g)) y =
      some (.ready (f (readout p u))) := by
  simp only [completion, evenCompiler]
  rw [even_decoder k hk p u g y hg hy hp]

end D5.S3.Arith.FibonacciAtomic.Observer.NativeOnlineTransport

#print axioms D5.S3.Arith.FibonacciAtomic.Observer.NativeOnlineTransport.fixed_even_needC_completion
