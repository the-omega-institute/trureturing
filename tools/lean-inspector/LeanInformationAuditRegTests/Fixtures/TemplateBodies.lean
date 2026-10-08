import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates

namespace LeanInformationAudit.Tests.DeclaredTemplates
open Lean
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

-- A homogeneous signature avoids proof-to-data Eq.rec transports. The existing
-- heterogeneous separation signature is an explicit unsupported control below.
def symbolicSignature (X Y : Type) [DecidableEq Y] : PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Y
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def symbolicPointwise {X Y : Type} [DecidableEq Y] (f g : X → Y) :
    PrimitiveRealization (symbolicSignature X Y) where
  readout := fun b x => Bool.rec (f x) (g x) b
  anchor := Fin.elim0

def boolCases {X : Type} (f g : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun x => Bool.rec (f x) (g x) (f x))

def propositionSlot (P : Prop) {X : Type} (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) := cutRealization f

def wrongInterface (x : Bool) : Bool := x

def closedDecision {X : Type} : PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun _ => decide True)

def recursiveBody {X : Type} (f : X → Bool) (n : Nat) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun x => Nat.rec (f x) (fun _ b => b) n)

end LeanInformationAudit.Tests.DeclaredTemplates
