import LeanInformationAudit.SealCommand

/-!
The publication type has no destination or command-syntax argument. The exact
allowlist is pinned here: widening it to a read, process, stdin or environment
capability must fail. See RealSeal.lean for the runtime boundary and residual:
IO, System and Lean.FS direct runtime references only, external module bodies
opaque, own unsafe/extern/implemented_by rejected, no OS sandbox claim.
-/

open Lean Lean.Elab.Command LeanInformationAudit

example : List ArtifactKind → CommandElabM SealPublicationPlan := @prepareSealPublication

#guard sealIOAllowlist == [``IO.FS.writeFile, ``Lean.logInfo]

#check @prepareSealPublication
