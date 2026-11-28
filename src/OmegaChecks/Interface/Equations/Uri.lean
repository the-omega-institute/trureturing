module
public import OmegaChecks.InitPort.Alternatives.Uri
import all OmegaChecks.InitPort.Alternatives.Uri
import all Init.System.Uri
import all Init.While

/-! The bounded URI decoder is a fixed point of the loop from the pinned implementation. -/

namespace OmegaChecks.Interface.Equations
open OmegaChecks.InitPort.Alternatives.System.Uri.UriEscape

private theorem loop_eq (raw : ByteArray) (st : State) :
    decodeLoop raw st = Lean.Loop.forIn (m := Id) {} st (fun _ => decodeStep raw) := by
  let turn (s : State) : State ⊕ State := match decodeStep raw s with
    | .done result => .inr result
    | .yield next => .inl next
  have fixed : repeatM.body (m := Id) turn (decodeLoop raw) = decodeLoop raw := by
    funext s
    rw [decodeLoop_eq]
    unfold turn repeatM.body
    dsimp only
    cases h : decodeStep raw s <;> rfl
  have unroll : Lean.Loop.forIn (m := Id) {} st (fun _ => decodeStep raw) = repeatM (m := Id) turn st := by
    unfold Lean.Loop.forIn
    congr 1
    funext s
    cases h : decodeStep raw s <;> simp [turn, h] <;> rfl
  rw [unroll]
  clear unroll
  induction st using (measure (fun s : State => raw.size - s.2)).wf.induction with
  | h st ih =>
    rw [decodeLoop_eq, repeatM_eq (m := Id) (f := turn) st ⟨_, fixed⟩]
    unfold repeatM.body turn
    split
    · rename_i _ step
      rw [step]
      rfl
    · rename_i next step
      rw [step]
      exact ih next (decodeStep_decreases step)

public theorem System.Uri.UriEscape.decodeUri (uri : String) :
    OmegaChecks.InitPort.Alternatives.System.Uri.UriEscape.decodeUri uri =
      _root_.System.Uri.UriEscape.decodeUri uri := by
  unfold OmegaChecks.InitPort.Alternatives.System.Uri.UriEscape.decodeUri _root_.System.Uri.UriEscape.decodeUri
  rw [loop_eq]
  rfl

end OmegaChecks.Interface.Equations
