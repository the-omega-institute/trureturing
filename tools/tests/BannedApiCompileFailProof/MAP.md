# BannedApiCompileFailProof Map

This project is intentionally excluded from the solution. Engineering CI restores
it in locked mode and proves that its deterministic-API violations fail compilation
with `RS0030`. A successful build is itself a gate failure.
