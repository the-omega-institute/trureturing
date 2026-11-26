/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Leonardo de Moura, Sebastian Ullrich, Mac Malone, Henrik Böving
-/
module
prelude

noncomputable section

public section

namespace Omega

inductive IO.FS.FileType where
  | dir
  | file
  | symlink
  | other

inductive IO.FS.Mode where
  | «read»
  | «write»
  | writeNew
  | readWrite
  | append

inductive IO.Process.Stdio where
  | piped
  | inherit
  | null

inductive IO.TaskState where
  | waiting
  | running
  | finished

end Omega
