/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
module
public import Init.System.FilePath
import all Init.System.FilePath
import Init.Data.Iterators.Consumers.Total
import Init.Data.String.Iter
import Init.Data.String.Pattern.String
import all OmegaChecks.InitPort.Alternatives.FiniteLoop
import Init.Data.String.Pattern.Char
import Init.Data.String.Pattern.Pred

/-! The separator and dot searches consume a finite backward iterator on every platform. -/

namespace OmegaChecks.InitPort.Alternatives.System.FilePath
open _root_.System _root_.System.FilePath String.Slice.Pattern

private noncomputable def findLast (s : String) (pred : Char → Bool) : Option s.Pos :=
  @String.revFind? _ (ToBackwardSearcher.DefaultBackwardSearcher pred) inferInstance
    (fun _ => finiteIteratorLoop) s pred inferInstance

public noncomputable def parent (p : FilePath) : Option FilePath :=
  let pos := findLast p.toString pathSeparators.contains
  let extract := FilePath.mk <$> String.Slice.copy <$> String.sliceTo _ <$> pos
  if p.isAbsolute then
    let rootEnd := (private_decl% _root_.System.FilePath.afterRootDirectory) p
    if rootEnd.IsAtEnd then none
    else if pos.bind String.Pos.next? = some rootEnd then some ⟨(p.toString.sliceTo rootEnd).copy⟩
    else extract
  else extract

public noncomputable def fileName (p : FilePath) : Option String :=
  let lastPart := match findLast p.toString pathSeparators.contains with
    | some sep => (p.toString.sliceFrom sep.next!).copy
    | none => p.toString
  if lastPart.isEmpty || lastPart == "." || lastPart == ".." then none else some lastPart

public noncomputable def fileStem (p : FilePath) : Option String :=
  p.fileName.map fun fname =>
    match (findLast fname (· == '.')).map String.Pos.offset with
    | some ⟨0⟩ => fname
    | some pos => String.Pos.Raw.extract fname 0 pos
    | none => fname

public noncomputable def extension (p : FilePath) : Option String :=
  p.fileName.bind fun fname =>
    match (findLast fname (· == '.')).map String.Pos.offset with
    | some 0 => none
    | some pos => some (String.Pos.Raw.extract fname (pos + '.') fname.rawEndPos)
    | none => none

public noncomputable def components (p : FilePath) : List String :=
  ((p.normalize.toString.split pathSeparator.toString).map ToString.toString).ensureTermination.toList

end OmegaChecks.InitPort.Alternatives.System.FilePath
