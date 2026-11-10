# FiniteCyclicNoncoverNative

## Abstract

Exact cyclic survivors construct the actual CriticalData and native main/core sequences and coordinate SDRs on the original finite ambient type.

Universal proof bodies are attempted source. No compiler, kernel, Scribe/Reg audit or admission was executed. Every handle names its exact D5 source owner. Section variables below are lexical context only, not an asserted compiled telescope. FromLean requests the native projection; no fixture or readout is fabricated.

**Definition 1.1 (criticalData_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.criticalData_zero`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.criticalData_zero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def criticalData_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    FiniteMatchingCoreClosure.CriticalData (matching (by omega) s)

**Definition 1.2 (criticalData_one).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.criticalData_one`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.criticalData_one` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def criticalData_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :

    FiniteMatchingCoreClosure.CriticalData (matching (by omega) s)

**Definition 1.3 (criticalData_two).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.criticalData_two`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.criticalData_two` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def criticalData_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    FiniteMatchingCoreClosure.CriticalData (matching (by omega) s)

**Definition 1.4 (X_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.X_zero`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.X_zero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def X_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    PreAbstractSimplicialComplex V

**Definition 1.5 (C_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.C_zero`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.C_zero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def C_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    PreAbstractSimplicialComplex V

**Definition 1.6 (main_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.main_zero`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.main_zero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def main_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    Sequence (noncover (by omega) s) (X_zero q hq s)

**Definition 1.7 (core_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.core_zero`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.core_zero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def core_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    Sequence (C_zero q hq s) (vertexComplex (point (by omega) s))

**Definition 1.8 (mainPairs_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainPairs_zero`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainPairs_zero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def mainPairs_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    List (Finset V × Finset V)

**Definition 1.9 (corePairs_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.corePairs_zero`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.corePairs_zero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def corePairs_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    List (Finset V × Finset V)

**Definition 1.10 (mainSDR_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainSDR_zero`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainSDR_zero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def mainSDR_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    RelativeSDR (noncover (by omega) s) (X_zero q hq s) (criticalData_zero q hq s).X_le

**Definition 1.11 (coreSDR_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.coreSDR_zero`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.coreSDR_zero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def coreSDR_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    RelativeSDR (C_zero q hq s) (vertexComplex (point (by omega) s))

      (criticalData_zero q hq s).vertex_le_C

**Definition 1.12 (X_one).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.X_one`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.X_one` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def X_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :

    PreAbstractSimplicialComplex V

**Definition 1.13 (C_one).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.C_one`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.C_one` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def C_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :

    PreAbstractSimplicialComplex V

**Definition 1.14 (main_one).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.main_one`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.main_one` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def main_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :

    Sequence (noncover (by omega) s) (X_one q hq s)

**Definition 1.15 (core_one).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.core_one`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.core_one` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def core_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :

    Sequence (C_one q hq s) (vertexComplex (point (by omega) s))

**Definition 1.16 (mainPairs_one).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainPairs_one`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainPairs_one` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def mainPairs_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :

    List (Finset V × Finset V)

**Definition 1.17 (corePairs_one).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.corePairs_one`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.corePairs_one` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def corePairs_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :

    List (Finset V × Finset V)

**Definition 1.18 (mainSDR_one).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainSDR_one`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainSDR_one` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def mainSDR_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :

    RelativeSDR (noncover (by omega) s) (X_one q hq s) (criticalData_one q hq s).X_le

**Definition 1.19 (coreSDR_one).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.coreSDR_one`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.coreSDR_one` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def coreSDR_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :

    RelativeSDR (C_one q hq s) (vertexComplex (point (by omega) s))

      (criticalData_one q hq s).vertex_le_C

**Definition 1.20 (X_two).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.X_two`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.X_two` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def X_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    PreAbstractSimplicialComplex V

**Definition 1.21 (C_two).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.C_two`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.C_two` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def C_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    PreAbstractSimplicialComplex V

**Definition 1.22 (main_two).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.main_two`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.main_two` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def main_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    Sequence (noncover (by omega) s) (X_two q hq s)

**Definition 1.23 (core_two).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.core_two`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.core_two` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def core_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    Sequence (C_two q hq s) (vertexComplex (point (by omega) s))

**Definition 1.24 (mainPairs_two).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainPairs_two`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainPairs_two` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def mainPairs_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    List (Finset V × Finset V)

**Definition 1.25 (corePairs_two).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.corePairs_two`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.corePairs_two` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def corePairs_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    List (Finset V × Finset V)

**Definition 1.26 (mainSDR_two).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainSDR_two`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainSDR_two` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def mainSDR_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    RelativeSDR (noncover (by omega) s) (X_two q hq s) (criticalData_two q hq s).X_le

**Definition 1.27 (coreSDR_two).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNative.coreSDR_two`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverNative.coreSDR_two` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def coreSDR_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    RelativeSDR (C_two q hq s) (vertexComplex (point (by omega) s))

      (criticalData_two q hq s).vertex_le_C

## References

- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.C_one`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.C_two`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.C_zero`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.X_one`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.X_two`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.X_zero`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.corePairs_one`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.corePairs_two`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.corePairs_zero`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.coreSDR_one`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.coreSDR_two`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.coreSDR_zero`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.core_one`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.core_two`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.core_zero`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.criticalData_one`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.criticalData_two`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.criticalData_zero`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainPairs_one`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainPairs_two`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainPairs_zero`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainSDR_one`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainSDR_two`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.mainSDR_zero`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.main_one`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.main_two`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNative.main_zero`
- Dependency: [D5/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors](FiniteCyclicNoncoverUniversalSurvivors.md)
