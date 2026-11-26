module
import all Init.Data.String.Modify
import all Init.Data.String.Lemmas.Intercalate

/-! Termination of character mapping and intercalation of nonempty lists. -/

namespace OmegaChecks.InitPort.Alternatives

public theorem String.mapAux._unary._proof_1 :
    type_of% (private_decl% @_root_.String.mapAux._unary._proof_1) := by
  intro f s p h
  change (p.pastModify f h).remainingBytes < p.remainingBytes
  rw [_root_.String.remainingBytes_pastModify]
  exact (_root_.String.Pos.lt_iff_remainingBytes_lt ..).mp (_root_.String.Pos.lt_next ..)

public theorem String.intercalate_append_of_ne_nil :
    type_of% @_root_.String.intercalate_append_of_ne_nil := by
  intro l m sep hl hm
  induction l with
  | nil => exact (hl rfl).elim
  | cons a tail ih =>
    cases tail with
    | nil =>
      exact (_root_.String.intercalate_cons_of_ne_nil hm).trans
        (congrArg (fun t => t ++ sep ++ sep.intercalate m) _root_.String.intercalate_singleton.symm)
    | cons b bs =>
      change sep.intercalate (a :: b :: (bs ++ m)) = _
      rw [List.cons_append] at ih
      rw [_root_.String.intercalate_cons_cons, ih (List.cons_ne_nil b bs),
        _root_.String.intercalate_cons_cons]
      repeat rw [String.append_assoc]

end OmegaChecks.InitPort.Alternatives
