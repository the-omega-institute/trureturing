/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualInductionState
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualInductionState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Retain one actual cycle with both boundary orders and its edge invariants. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSimultaneousBoundaryState
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeSelectedOrders

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualInductionState

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSimultaneousBoundaryState
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeSelectedOrders
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance

/-- Every field belongs to this same selected order and this same actual
cycle. The opposite order changes the port table, not the native domain.
The fixed protected labels are the last two selected labels, so ordinary
base rotations and subsequent prepending cannot change their identities. -/
structure StateFor {m k : ℕ} (F : SupplyFrame m k)
    (hk : 2 ≤ k) (hB : 3 ≤ F.base.length) where
  oppositeFrame : SupplyFrame m k
  canonicalOpposite : oppositeFrame = oppositeSelectedFrame F hk
  sameSelected : oppositeFrame.selected.toFinset = F.selected.toFinset
  sameBase : oppositeFrame.base = F.base
  sameTerminal : oppositeFrame.terminal = F.terminal
  sameProtectedPair :
    s(protectedP oppositeFrame hk, protectedQ oppositeFrame hk) =
      s(protectedP F hk, protectedQ F hk)
  primaryOdd : Bool
  oppositeOdd : Bool
  distinguishedOpposite : Bool
  base : {x : Configuration m // SpecialDomain F hB x}
  walk : (domainGraph (SpecialDomain F hB)).Walk base base
  hamiltonian : walk.IsHamiltonianCycle
  K : Finset (Sym2 {x : Configuration m // SpecialDomain F hB x})
  H : Finset (Sym2 {x : Configuration m // SpecialDomain F hB x})
  primaryCuts : K.image (Sym2.map Subtype.val) = markedCuts F
  oppositeCuts : H.image (Sym2.map Subtype.val) = markedCuts oppositeFrame
  left : {x : Configuration m // SpecialDomain F hB x}
  right : {x : Configuration m // SpecialDomain F hB x}
  otherLeft : {x : Configuration m // SpecialDomain F hB x}
  far : {x : Configuration m // SpecialDomain F hB x}
  primaryFar : {x : Configuration m // SpecialDomain F hB x}
  oppositeFar : {x : Configuration m // SpecialDomain F hB x}
  leftCoordinate : left.val = leftPort F 0
  rightCoordinate : right.val = rightPort F 0
  otherLeftCoordinate : otherLeft.val = leftPort oppositeFrame 0
  farCoordinate : far.val = leftPort
    (if distinguishedOpposite then oppositeFrame else F) (k - 1)
  primaryFarCoordinate : primaryFar.val = leftPort F (k - 1)
  oppositeFarCoordinate : oppositeFar.val = leftPort oppositeFrame (k - 1)
  distinguished : (domainGraph (SpecialDomain F hB)).Walk left far
  crossing : (domainGraph (SpecialDomain F hB)).Walk right otherLeft
  jointRest : List (Piece (domainGraph (SpecialDomain F hB)))
  primary : (domainGraph (SpecialDomain F hB)).Walk left primaryFar
  primaryRest : List (Piece (domainGraph (SpecialDomain F hB)))
  opposite : (domainGraph (SpecialDomain F hB)).Walk otherLeft oppositeFar
  oppositeRest : List (Piece (domainGraph (SpecialDomain F hB)))
  partitions : ActualTwoOrderPartitions walk K H
    (⟨left, far, distinguished⟩ :: ⟨right, otherLeft, crossing⟩ :: jointRest)
    (⟨left, primaryFar, primary⟩ :: primaryRest)
    (⟨otherLeft, oppositeFar, opposite⟩ :: oppositeRest)
  primaryBoundary : NativeBoundaryPairs F primaryOdd Subtype.val
    (⟨left, primaryFar, primary⟩ :: primaryRest)
  oppositeBoundary : NativeBoundaryPairs oppositeFrame oppositeOdd Subtype.val
    (⟨otherLeft, oppositeFar, opposite⟩ :: oppositeRest)
  firstCut : s(right, left) ∈ K
  keepsProtectedA : ∀ (x y : {v : Configuration m // SpecialDomain F hB v}),
    y.val = x.val * a m →
    s(x.val (Fin.last m), y.val (Fin.last m)) ≠
      s(protectedP F hk, protectedQ F hk) → s(x, y) ∈ walk.edges
  keepsRemainingB : ∀ (x y : {v : Configuration m // SpecialDomain F hB v}),
    y.val = x.val * b m → x.val (Fin.last m) ∉ F.selected.toFinset →
      s(x, y) ∈ walk.edges
  selectedC : ∀ (x : Configuration m),
    s(x, x * c m) ∈ walk.edges.map (Sym2.map Subtype.val) →
      x (Fin.last m) ∈ F.selected.toFinset

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualInductionState
