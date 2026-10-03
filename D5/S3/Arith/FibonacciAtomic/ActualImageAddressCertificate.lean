/- GID: D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact address certificate cardinality and depth for actual Fibonacci substitution images. -/

import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate

open GenealogicalFiberTransport (Source substitution composition decompose)

/-- Root-first paths: false is left and true is right. Leaf labels use true for
alpha and false for beta, as in GenealogicalFiberTransport.Source. -/
abbrev Address := List Bool

/-- The four original endpoint observations, including the empty root address. -/
inductive Output
  | leafAlpha | leafBeta | branch | absent
  deriving DecidableEq

/-- Read the raw endpoint; continuing beyond a leaf gives absent. -/
def out : Source → Address → Output
  | .of true, [] => .leafAlpha
  | .of false, [] => .leafBeta
  | .mul _ _, [] => .branch
  | .of _, _ :: _ => .absent
  | .mul s _, false :: u => out s u
  | .mul _ t, true :: u => out t u

/-- Root depth is zero. Reuse the ordered shape from the existing decomposition. -/
def height (t : Source) : ℕ := (decompose t).1.height

/-- The actual image, with the complete ordered tree retained. -/
def ActualImage (d : ℕ) : Set Source := Set.range (substitution^[d])

/-- A finite query set obeys the raw path depth budget. -/
def Within (h : ℕ) (Q : Finset Address) : Prop := ∀ u ∈ Q, u.length ≤ h

/-- Soundness ranges over every complete source of the same exact composition. -/
def Sound (d : ℕ) (V : Source) (h : ℕ) (Q : Finset Address) : Prop :=
  Within h Q ∧ ∀ U : Source, composition U = composition V →
    (∀ u ∈ Q, out U u = out V u) → U ∈ ActualImage d

/-- All addresses carrying an alpha leaf. -/
def alphaAddresses : Source → Finset Address
  | .of true => {[]}
  | .of false => ∅
  | .mul s t => (alphaAddresses s).image (List.cons false) ∪
      (alphaAddresses t).image (List.cons true)

/-- The complete subtree at an address, absent when the path passes a leaf. -/
def subtree : Source → Address → Option Source
  | t, [] => some t
  | .of _, _ :: _ => none
  | .mul s _, false :: u => subtree s u
  | .mul _ t, true :: u => subtree t u

/-- Replace the subtree at a valid address; invalid addresses leave the tree alone. -/
def replace : Source → Address → Source → Source
  | _, [], v => v
  | .of b, _ :: _, _ => .of b
  | .mul s t, false :: u, v => .mul (replace s u v) t
  | .mul s t, true :: u, v => .mul s (replace t u v)

/-- Every branch has an alpha descendant, recursively through the whole tree. -/
def AlphaCovered : Source → Prop
  | .of _ => True
  | .mul s t => AlphaCovered s ∧ AlphaCovered t ∧
      (alphaAddresses (.mul s t)).Nonempty

end D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate
