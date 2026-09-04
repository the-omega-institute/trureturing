import LeanInformationAudit.Tests.Seal.SystemContentSensitivity.ConstantReadout
import LeanInformationAudit.Tests.Seal.SystemContentSensitivity.FixedStage

/-! T-013 primitive-content mutations.

The two imported fixtures isolate the erasures the seal can see: an all-constant census
and a census fixed at one stage. Each is exactly IE-C007 `full 2 without 2`.

Law-level erasure is instead pinned by the literal type checks in
`SealSystemTheorem.lean`; by the A2 design the seal reads the registered bundle at
`CatalogBuilder.lean:50-53`, never its `Law`. -/
