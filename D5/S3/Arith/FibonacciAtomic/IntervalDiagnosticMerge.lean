/- GID: D5/S3/Arith/FibonacciAtomic/IntervalDiagnosticMerge
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/IntervalDiagnosticMerge
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ordered interval messages preserve the earliest internal failure and the incoming boundary. -/

import D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
import D5.S3.Arith.FibonacciAtomic.TreeMessageRealization

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.IntervalDiagnosticMerge

open LiteralWindowEnd (Window first last)
open FirstRejectionCutCapacity (Word Label bad task interval)
open TreeMessageRealization (Tree leaf fork leaves Full subtrees Implementation evaluate)

/-- Failed messages retain their incoming bit, but have no outgoing field. -/
inductive Msg (k : ℕ)
  | failed (position : Fin (k + 1)) (incoming : Bool)
  | live (incoming outgoing : Bool)
  deriving DecidableEq

def incoming {k : ℕ} : Msg k → Bool
  | .failed _ u => u
  | .live u _ => u

/-- Half-open adjacent blocks, with no constraint on the binary tree's shape. -/
inductive Ordered (k : ℕ) : ℕ → ℕ → Tree (Fin (k + 1)) → Prop
  | leaf (i : Fin (k + 1)) : Ordered k i.val (i.val + 1) (leaf i)
  | fork {a b c : ℕ} {L R : Tree (Fin (k + 1))}
      (hab : a < b) (hbc : b < c) (hc : c ≤ k + 1)
      (left : Ordered k a b L) (right : Ordered k b c R) :
      Ordered k a c (fork L R)

/-- The last coordinate in a left child identifies its seam with the right child. -/
noncomputable def seam {k : ℕ} (L : Tree (Fin (k + 1))) : Fin (k + 1) :=
  ⟨min ((leaves L).sup Fin.val) k, by omega⟩

/-- Four syntax rules. The merger reads messages and a seam coordinate only. -/
def combine {k : ℕ} (j : Fin (k + 1)) : Msg k → Msg k → Msg k
  | .failed f u, _ => .failed f u
  | .live u v, q =>
      if v = true ∧ incoming q = true then .failed j u else
        match q with
        | .failed f _ => .failed f u
        | .live _ z => .live u z

def encode {k : ℕ} (i : Fin (k + 1)) (x : Window) : Msg k :=
  .live (if i.val = 0 then false else first x)
    (if i.val = k then decide (x = .zero) else last x)

noncomputable def implementation (k : ℕ) : Implementation (fun _ : Fin (k + 1) => Window) where
  Message := fun _ => Msg k
  empty := .live false false
  encode := fun i _ _ => encode i
  combine := fun L _ => combine (seam L)

def read {k : ℕ} : Msg k → Label k
  | .failed f _ => f
  | .live _ z => if z then (Fin.last k : Label k) else ⊤

/-- Boundary fields are defined from the original word independently of the merger. -/
def leftBit {k : ℕ} (a : ℕ) (w : Word k) : Bool :=
  if a = 0 then false else first (w ⟨min a k, by omega⟩)

def rightBit {k : ℕ} (b : ℕ) (w : Word k) : Bool :=
  if b = k + 1 then decide (w (Fin.last k) = .zero)
  else last (w ⟨min (b - 1) k, by omega⟩)

/-- The declarative message meaning: the first bad internal seam, or absence
of internal bad seams together with the two boundary fields. Terminal zero
is a boundary flag and never an internal failure. -/
def Semantics {k : ℕ} (a b : ℕ) (w : Word k) : Msg k → Prop
  | .failed f u => u = leftBit a w ∧ a ≤ f.val ∧ f.val + 1 < b ∧ bad w f ∧
      ∀ i : Fin (k + 1), a ≤ i.val → i.val < f.val → ¬ bad w i
  | .live u z => u = leftBit a w ∧ z = rightBit b w ∧
      ∀ i : Fin (k + 1), a ≤ i.val → i.val + 1 < b → ¬ bad w i

#check Finset.inf_le
#check Finset.le_inf
#check Finset.le_inf_iff
#check Finset.inf_le_iff
#check Finset.inf_eq_top
#check Finset.min'_mem
#check Finset.Ico_union_Ico_eq_Ico
#check Finset.sup_le
#check Finset.le_sup

end D5.S3.Arith.FibonacciAtomic.IntervalDiagnosticMerge
