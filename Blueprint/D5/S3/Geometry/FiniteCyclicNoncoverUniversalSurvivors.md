# FiniteCyclicNoncoverUniversalSurvivors

## Abstract

Universal original-label cyclic noncover survivors follow from exact interval images, actual ordered suffix conjugacy and named critical-face readback.

Universal proof bodies are attempted source. No compiler, kernel, Scribe/Reg audit or admission was executed. Every handle names its exact D5 source owner. Section variables below are lexical context only, not an asserted compiled telescope. FromLean requests the native projection; no fixture or readout is fabricated.

**Theorem 1.1 (remaining_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors.remaining_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors.remaining_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem remaining_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    remainingFaces (show 3 ≤ 3*q by omega) s =

      insert {point (by omega) s} {criticalA q hq s, criticalB q hq s}

**Theorem 1.2 (remaining_one).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors.remaining_one`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors.remaining_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem remaining_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :

    remainingFaces (show 3 ≤ 3*q+1 by omega) s =

      insert {point (by omega) s} {criticalOne q s}

**Theorem 1.3 (remaining_two).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors.remaining_two`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors.remaining_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem remaining_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    remainingFaces (show 3 ≤ 3*q+2 by omega) s =

      insert {point (by omega) s} {criticalTwo q hq s}

## References

- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors.remaining_one`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors.remaining_two`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors.remaining_zero`
- Dependency: [D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths](FiniteCyclicNoncoverIntervalPaths.md)
