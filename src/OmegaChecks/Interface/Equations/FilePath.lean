module
public import OmegaChecks.InitPort.Alternatives.FilePath
import all OmegaChecks.InitPort.Alternatives.FilePath
import all OmegaChecks.Interface.Equations.Collect
import all OmegaChecks.InitPort.Alternatives.FiniteLoop
import all Init.Data.String.Search
import all Init.System.FilePath
import all Init.Data.String.Iter.Basic
import all Init.Data.Iterators.Consumers.Total
import all Init.Data.Iterators.Consumers.Collect
import Init.Data.String.Lemmas.Pattern.Char
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred

/-! The finite loop visits the same backward search states as the pinned file-path operations. -/

namespace OmegaChecks.Interface.Equations
open _root_.System _root_.String.Slice.Pattern

private theorem findLast_eq (s : String) (pred : Char → Bool) :
    OmegaChecks.InitPort.Alternatives.System.FilePath.findLast s pred = s.revFind? pred := by
  unfold OmegaChecks.InitPort.Alternatives.System.FilePath.findLast
  exact congrArg (fun loop => @_root_.String.revFind? _ (ToBackwardSearcher.DefaultBackwardSearcher pred)
    inferInstance loop s pred inferInstance) (funext (fun _ => finiteIteratorLoop_eq))

public theorem System.FilePath.parent (p : FilePath) :
    OmegaChecks.InitPort.Alternatives.System.FilePath.parent p = p.parent := by
  unfold OmegaChecks.InitPort.Alternatives.System.FilePath.parent _root_.System.FilePath.parent
    _root_.System.FilePath.posOfLastSep
  rw [findLast_eq]

public theorem System.FilePath.fileName (p : FilePath) :
    OmegaChecks.InitPort.Alternatives.System.FilePath.fileName p = p.fileName := by
  unfold OmegaChecks.InitPort.Alternatives.System.FilePath.fileName _root_.System.FilePath.fileName
    _root_.System.FilePath.posOfLastSep
  rw [findLast_eq]
  cases p.toString.revFind? FilePath.pathSeparators.contains <;> rfl

public theorem System.FilePath.fileStem (p : FilePath) :
    OmegaChecks.InitPort.Alternatives.System.FilePath.fileStem p = p.fileStem := by
  unfold OmegaChecks.InitPort.Alternatives.System.FilePath.fileStem _root_.System.FilePath.fileStem
  congr 1
  funext fname
  rw [findLast_eq]
  simp only [_root_.String.revFind?, _root_.String.Slice.revFind?_char_eq_revFind?_beq]
  generalize ((fname.toSlice.revFind? (· == '.')).map String.Pos.ofToSlice |>.map String.Pos.offset) = pos
  rcases pos with _ | ⟨_ | _⟩ <;> rfl

public theorem System.FilePath.extension (p : FilePath) :
    OmegaChecks.InitPort.Alternatives.System.FilePath.extension p = p.extension := by
  unfold OmegaChecks.InitPort.Alternatives.System.FilePath.extension _root_.System.FilePath.extension
  congr 1
  funext fname
  rw [findLast_eq]
  simp only [_root_.String.revFind?, _root_.String.Slice.revFind?_char_eq_revFind?_beq]
  generalize ((fname.toSlice.revFind? (· == '.')).map String.Pos.ofToSlice |>.map String.Pos.offset) = pos
  rcases pos with _ | ⟨_ | _⟩ <;> rfl

public theorem System.FilePath.components (p : FilePath) :
    OmegaChecks.InitPort.Alternatives.System.FilePath.components p = p.components := by
  unfold OmegaChecks.InitPort.Alternatives.System.FilePath.components _root_.System.FilePath.components
  rfl

end OmegaChecks.Interface.Equations
