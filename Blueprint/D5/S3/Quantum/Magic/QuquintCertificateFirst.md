# Ququint Certificate First Half

## Abstract

Exact LDL factorizations for sixteen numerical branch matrices.

Each displayed identity uses branch from D5.S3.Quantum.Magic.QuquintCertificateData and the public lower and pivot declarations named in that identity. These are certificates for explicit numerical matrices. QuquintCertificateBridge identifies their data with the phase-point forms of QuquintWignerCriticalGeometry.

**Definition 1.1 (Unit-lower factor for branch 0).**

$$\mathrm{lower0}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.2 (Pivots for branch 0).**

$$\mathrm{pivots0}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.3 (Branch 0).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(0)=\mathrm{lower0}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots0})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower0})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.4 (Unit-lower factor for branch 1).**

$$\mathrm{lower1}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.5 (Pivots for branch 1).**

$$\mathrm{pivots1}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.6 (Branch 1).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(1)=\mathrm{lower1}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots1})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower1})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.7 (Unit-lower factor for branch 2).**

$$\mathrm{lower2}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.8 (Pivots for branch 2).**

$$\mathrm{pivots2}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.9 (Branch 2).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(2)=\mathrm{lower2}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots2})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.10 (Unit-lower factor for branch 3).**

$$\mathrm{lower3}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.11 (Pivots for branch 3).**

$$\mathrm{pivots3}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.12 (Branch 3).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(3)=\mathrm{lower3}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots3})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower3})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.13 (Unit-lower factor for branch 4).**

$$\mathrm{lower4}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.14 (Pivots for branch 4).**

$$\mathrm{pivots4}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.15 (Branch 4).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(4)=\mathrm{lower4}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots4})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower4})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.16 (Unit-lower factor for branch 5).**

$$\mathrm{lower5}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower5` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.17 (Pivots for branch 5).**

$$\mathrm{pivots5}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots5` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.18 (Branch 5).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(5)=\mathrm{lower5}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots5})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower5})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.19 (Unit-lower factor for branch 6).**

$$\mathrm{lower6}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower6` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.20 (Pivots for branch 6).**

$$\mathrm{pivots6}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots6` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.21 (Branch 6).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(6)=\mathrm{lower6}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots6})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower6})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.22 (Unit-lower factor for branch 7).**

$$\mathrm{lower7}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower7` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.23 (Pivots for branch 7).**

$$\mathrm{pivots7}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots7` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.24 (Branch 7).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(7)=\mathrm{lower7}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots7})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower7})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_7` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.25 (Unit-lower factor for branch 8).**

$$\mathrm{lower8}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower8` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.26 (Pivots for branch 8).**

$$\mathrm{pivots8}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots8` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.27 (Branch 8).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(8)=\mathrm{lower8}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots8})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower8})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.28 (Unit-lower factor for branch 9).**

$$\mathrm{lower9}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower9` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.29 (Pivots for branch 9).**

$$\mathrm{pivots9}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots9` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.30 (Branch 9).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(9)=\mathrm{lower9}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots9})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower9})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_9` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.31 (Unit-lower factor for branch 10).**

$$\mathrm{lower10}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower10` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.32 (Pivots for branch 10).**

$$\mathrm{pivots10}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots10` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.33 (Branch 10).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(10)=\mathrm{lower10}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots10})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower10})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_10` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.34 (Unit-lower factor for branch 11).**

$$\mathrm{lower11}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower11` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.35 (Pivots for branch 11).**

$$\mathrm{pivots11}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots11` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.36 (Branch 11).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(11)=\mathrm{lower11}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots11})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower11})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.37 (Unit-lower factor for branch 12).**

$$\mathrm{lower12}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower12` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.38 (Pivots for branch 12).**

$$\mathrm{pivots12}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots12` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.39 (Branch 12).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(12)=\mathrm{lower12}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots12})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower12})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_12` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.40 (Unit-lower factor for branch 13).**

$$\mathrm{lower13}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower13` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.41 (Pivots for branch 13).**

$$\mathrm{pivots13}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots13` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.42 (Branch 13).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(13)=\mathrm{lower13}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots13})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower13})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_13` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.43 (Unit-lower factor for branch 14).**

$$\mathrm{lower14}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower14` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.44 (Pivots for branch 14).**

$$\mathrm{pivots14}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots14` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.45 (Branch 14).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(14)=\mathrm{lower14}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots14})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower14})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_14` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.46 (Unit-lower factor for branch 15).**

$$\mathrm{lower15}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower15` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.47 (Pivots for branch 15).**

$$\mathrm{pivots15}:\mathrm{Fin} 4\to\mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots15` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.48 (Branch 15).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(15)=\mathrm{lower15}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots15})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower15})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_15` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

## References

- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_0`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_1`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_10`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_11`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_12`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_13`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_14`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_15`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_2`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_3`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_4`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_5`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_6`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_7`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_8`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.ldl_9`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower0`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower1`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower10`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower11`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower12`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower13`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower14`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower15`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower2`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower3`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower4`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower5`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower6`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower7`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower8`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower9`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots0`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots1`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots10`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots11`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots12`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots13`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots14`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots15`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots2`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots3`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots4`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots5`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots6`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots7`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots8`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateFirst.pivots9`
- Dependency: [D5/S3/Quantum/Magic/QuquintCertificateData](QuquintCertificateData.md)
