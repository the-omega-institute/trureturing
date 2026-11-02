# Finite-degree sesquilinear pairing

## Abstract

Finite support in a genuine complex basis gives a native algebraic HPL inclusion-isometry calculation. The carrier is an arbitrary complex module with a `Module.Basis`; the sesquilinear form is arbitrary. A signed-integer degree map supplies the selection rule, and an operator is assumed to preserve a chosen sector while raising degree by at least one on every nonzero basis transition.

The module proves the finite double expansion with conjugation in the first slot, support preservation and contribution extraction, the degree bound for every signed raising power, actual cancellation of every positive geometric cross term, and the finite geometric-sum isometry

$$H\left(\left(\sum_{r<n}(-A)^r\right)x,\left(\sum_{s<n}(-A)^s\right)y\right)=H(x,y).$$

The hypotheses are algebraic inputs. They do not prove a BRST realization, HPL identity, cohomology statement, VOA/CFT construction, anomaly cancellation, string completion or AdS/CFT claim. No positivity, nondegeneracy, rank, momentum, inverse or nilpotence assumption is used.

**Theorem 1.1 (Finite double expansion).**

Lean statement: `D5/S3/VertexAlgebra/FiniteDegreePairing.form_expansion`.

The finite supports of the two basis representations give the exact sesquilinear double sum; the first coefficient is conjugated.

**Theorem 1.2 (Sector-preserving raising support).**

Lean statement: `D5/S3/VertexAlgebra/FiniteDegreePairing.raising_power_support`.

An operator with sector-preserving transitions and `d i + 1 ≤ d j` sends a degree-zero sector-supported vector under `(-A)^r` to degree at least `r` in that sector.

**Theorem 1.3 (Positive cross-term cancellation).**

Lean statement: `D5/S3/VertexAlgebra/FiniteDegreePairing.powers_orthogonal`.

For `r+s>0`, the selection rule `d i+d j ≠ 0 → H (b i) (b j)=0` and the two degree lower bounds make the whole pairing zero. This is a finite support proof, with no desired-isometry certificate or assumed conclusion.

**Theorem 1.4 (Finite inclusion isometry).**

Lean statement: `D5/S3/VertexAlgebra/FiniteDegreePairing.finite_inclusion_isometry`.

For every positive truncation length, expanding both finite sums leaves only the `(0,0)` term, which is `H x y`.

## Boundary

The theorem is a generic native algebraic unit. The sector, degree selection rule and raising transition law must be supplied by an application. The source does not establish those hypotheses for the original lattice BRST/HPL operators and does not claim an infinite geometric-series limit.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FiniteDegreePairing.form_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/FiniteDegreePairing.raising_power_support`
- Truth anchor: `D5/S3/VertexAlgebra/FiniteDegreePairing.powers_orthogonal`
- Truth anchor: `D5/S3/VertexAlgebra/FiniteDegreePairing.finite_inclusion_isometry`
