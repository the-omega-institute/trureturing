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

private theorem even_mod (k : Nat) : (2*k) % 2 = 0 := by omega
private theorem even_half (k : Nat) : (2*k) / 2 = k := by omega

/-- The fixed even certificate has a guard and label query at every non-root
address. -/
theorem even_query_shape (k : Nat) (hk : 1 ≤ k) (p : Address) (hp : p ≠ []) :
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

/-- The compiler leaves the original control untouched until a read macro has
completed. These equations are the phase invariant used by the event-level
interpreter: `needC` consumes the label reply and `needG` completes absence
without inspecting a second reply. -/
theorem needC_step {C O : Type} {δ : C → Op C O} (N : Nat)
    (p : Address) (f : Reply → C) (g : Reply) :
    evenCompiler N δ (.needC p f g) =
      .read (evenLabelQuery N p) (fun y =>
        .ready (f (originalDecode N p [g, y]))) := rfl

theorem needG_step {C O : Type} {δ : C → Op C O} (N : Nat)
    (p : Address) (f : Reply → C) (g : Reply) :
    evenCompiler N δ (.needG p f g) = .localStep (.ready (f .absent)) := rfl

/-- A non-root read is compiled to one guard event followed by one of the two
pending phases. The proof exposes the actual continuation selected by the
physical existence bit. -/
theorem ready_nonroot_step {C O : Type} {δ : C → Op C O} (N : Nat)
    (c : C) (p : Address) (f : Reply → C) (hp : p ≠ [])
    (h : δ c = .read p f) :
    evenCompiler N δ (.ready c) =
      .read (evenGuardQuery N p) (fun y =>
        if guardAccept N y then .needC p f y else .needG p f y) := by
  simp [evenCompiler, h, hp]

/-- The root case has no pending phase: its single label probe is decoded
immediately. -/
theorem ready_root_step {C O : Type} {δ : C → Op C O} (N : Nat)
    (c : C) (f : Reply → C) (h : δ c = .read [] f) :
    evenCompiler N δ (.ready c) =
      .read (evenLabelQuery N []) (fun y =>
        .ready (f (originalDecode N [] [y]))) := by
  simp [evenCompiler, h]

/-- At a positive fixed even lag, the two physical replies used by the phase
compiler are exactly the existing delayed decoder's query list. -/
theorem even_queries_are_decoder_queries (k : Nat) (hk : 1 ≤ k) (p : Address)
    (hp : p ≠ []) :
    originalQueries (2*k) p =
      [evenGuardQuery (2*k) p, evenLabelQuery (2*k) p] :=
  even_query_shape k hk p hp

/-- The completed `needC` phase returns the original four-valued reply on the
same shifted register. This is the nontrivial bridge from physical replies to
logical control; it uses no source or history hidden in the compiler state. -/
theorem needC_decodes_original {C : Type} (k : Nat) (hk : 1 ≤ k)
    (p : Address) (u : Source) (g y : Reply)
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

/-- A false physical guard really means that the original non-root address
was absent. This is the guard half of the `needG` phase invariant, rather than
an assumption about the logical source. -/
theorem needG_original_absent (k : Nat) (hk : 1 ≤ k) (p : Address)
    (u : Source) (g : Reply)
    (hg : g = readout (evenGuardQuery (2*k) p) (substitution^[2*k] u))
    (hzero : guardAccept (2*k) g = false) (hp : p ≠ []) :
    readout p u = .absent := by
  let a := p.dropLast
  let d := p.getLast hp
  have he : p = a ++ [d] := (List.dropLast_concat_getLast hp).symm
  have hguard := DelayedOriginalReadout.original_presence_guard
    (2*k) a d u
  have hg' : g = readout (a ++ rights ((2*k)/2 + 1))
      (substitution^[2*k] u) := by
    simpa [evenGuardQuery, a, even_half] using hg
  have hfalse : ¬ guardAccept (2*k)
      (readout (a ++ rights ((2*k)/2 + 1)) (substitution^[2*k] u)) = true := by
    intro ht
    have ht' : guardAccept (2*k) g = true := by rw [hg']; exact ht
    rw [hzero] at ht'
    cases ht'
  have hnot : ¬ readout (a ++ [d]) u ≠ .absent := by
    intro hpres
    exact hfalse (hguard.mpr hpres)
  have habs : readout (a ++ [d]) u = .absent := not_ne_iff.mp hnot
  simpa [he] using habs

end D5.S3.Arith.FibonacciAtomic.Observer.NativeOnlineTransport

#print axioms D5.S3.Arith.FibonacciAtomic.Observer.NativeOnlineTransport.needC_decodes_original
