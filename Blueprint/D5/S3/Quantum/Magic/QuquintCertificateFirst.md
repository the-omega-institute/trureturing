# Ququint Certificate First Half

## Abstract

Exact LDL factorizations for sixteen numerical branch matrices.

Each displayed identity uses branch from D5.S3.Quantum.Magic.QuquintCertificateData and the public lower and pivot declarations named in that identity. Matrices are displayed as vectors of rows; radical denotes QuquintCertificateData.radical. These are certificates for explicit numerical matrices. QuquintCertificateBridge identifies their data with the phase-point forms of QuquintWignerCriticalGeometry.

**Definition 1.1 (Unit-lower factor for branch 0).**

$$\mathrm{lower0}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[\mathrm{radical}^{3}/20-\mathrm{radical}/2,-\mathrm{radical}/5,1,0],[\mathrm{radical}/4,-\mathrm{radical}^{3}/40+\mathrm{radical}/5,\mathrm{radical}^{2}/8-1,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.2 (Pivots for branch 0).**

$$\mathrm{pivots0}:\mathrm{Fin} 4\to\mathbb{R}=[\mathrm{radical}^{2}/2,5\cdot\mathrm{radical}^{2}/8-5/2,2\cdot\mathrm{radical}^{2}-16,\mathrm{radical}^{2}-10]$$

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

$$\mathrm{lower1}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[\mathrm{radical}^{3}/20-\mathrm{radical}/2,\mathrm{radical}^{3}/11-87\cdot\mathrm{radical}/55,1,0],[\mathrm{radical}/4,-27\cdot\mathrm{radical}^{3}/440+37\cdot\mathrm{radical}/55,\mathrm{radical}^{2}/8-1,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.5 (Pivots for branch 1).**

$$\mathrm{pivots1}:\mathrm{Fin} 4\to\mathbb{R}=[3\cdot\mathrm{radical}^{2}/5-2,5\cdot\mathrm{radical}^{2}/8-3,124\cdot\mathrm{radical}^{2}/55-208/11,\mathrm{radical}^{2}-48/5]$$

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

$$\mathrm{lower2}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[29\cdot\mathrm{radical}^{3}/440-15\cdot\mathrm{radical}/22,-\mathrm{radical}^{3}/44+8\cdot\mathrm{radical}/55,1,0],[-3\cdot\mathrm{radical}^{3}/110+31\cdot\mathrm{radical}/44,5\cdot\mathrm{radical}^{3}/88-53\cdot\mathrm{radical}/55,17\cdot\mathrm{radical}^{2}/124-110/93,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.8 (Pivots for branch 2).**

$$\mathrm{pivots2}:\mathrm{Fin} 4\to\mathbb{R}=[3\cdot\mathrm{radical}^{2}/5-2,5\cdot\mathrm{radical}^{2}/8-3,114\cdot\mathrm{radical}^{2}/55-888/55,542\cdot\mathrm{radical}^{2}/465-1120/93]$$

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

$$\mathrm{lower3}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[-\mathrm{radical}^{3}/20+\mathrm{radical},-3\cdot\mathrm{radical}^{3}/4+53\cdot\mathrm{radical}/5,1,0],[7\cdot\mathrm{radical}^{3}/20-19\cdot\mathrm{radical}/4,-21\cdot\mathrm{radical}^{3}/40+37\cdot\mathrm{radical}/5,39/44-\mathrm{radical}^{2}/176,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.11 (Pivots for branch 3).**

$$\mathrm{pivots3}:\mathrm{Fin} 4\to\mathbb{R}=[7\cdot\mathrm{radical}^{2}/10-4,5\cdot\mathrm{radical}^{2}/8-7/2,4\cdot\mathrm{radical}^{2}/5+16/5,39\cdot\mathrm{radical}^{2}/110+1/11]$$

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

$$\mathrm{lower4}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[41\cdot\mathrm{radical}^{3}/440-25\cdot\mathrm{radical}/22,-\mathrm{radical}^{3}/44+8\cdot\mathrm{radical}/55,1,0],[3\cdot\mathrm{radical}^{3}/220+\mathrm{radical}/44,-13\cdot\mathrm{radical}^{3}/440+17\cdot\mathrm{radical}/55,75\cdot\mathrm{radical}^{2}/698-262/349,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.14 (Pivots for branch 4).**

$$\mathrm{pivots4}:\mathrm{Fin} 4\to\mathbb{R}=[3\cdot\mathrm{radical}^{2}/5-2,5\cdot\mathrm{radical}^{2}/8-3,122\cdot\mathrm{radical}^{2}/55-992/55,1814\cdot\mathrm{radical}^{2}/1745-3592/349]$$

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

$$\mathrm{lower5}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[-2\cdot\mathrm{radical}^{3}/5+6\cdot\mathrm{radical},-3\cdot\mathrm{radical}^{3}/4+53\cdot\mathrm{radical}/5,1,0],[-7\cdot\mathrm{radical}^{3}/40+11\cdot\mathrm{radical}/4,3\cdot\mathrm{radical}^{3}/8-28\cdot\mathrm{radical}/5,81\cdot\mathrm{radical}^{2}/872-115/218,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower5` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.17 (Pivots for branch 5).**

$$\mathrm{pivots5}:\mathrm{Fin} 4\to\mathbb{R}=[7\cdot\mathrm{radical}^{2}/10-4,5\cdot\mathrm{radical}^{2}/8-7/2,104/5-2\cdot\mathrm{radical}^{2}/5,262\cdot\mathrm{radical}^{2}/545-198/109]$$

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

$$\mathrm{lower6}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[-\mathrm{radical}^{3}/2+15\cdot\mathrm{radical}/2,\mathrm{radical}^{3}/2-37\cdot\mathrm{radical}/5,1,0],[7\cdot\mathrm{radical}^{3}/40-9\cdot\mathrm{radical}/4,-29\cdot\mathrm{radical}^{3}/40+52\cdot\mathrm{radical}/5,137\cdot\mathrm{radical}^{2}/872-321/218,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower6` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.20 (Pivots for branch 6).**

$$\mathrm{pivots6}:\mathrm{Fin} 4\to\mathbb{R}=[7\cdot\mathrm{radical}^{2}/10-4,5\cdot\mathrm{radical}^{2}/8-7/2,104/5-2\cdot\mathrm{radical}^{2}/5,262\cdot\mathrm{radical}^{2}/545-198/109]$$

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

$$\mathrm{lower7}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[\mathrm{radical}^{3}/110+3\cdot\mathrm{radical}/22,-\mathrm{radical}^{3}/22+23\cdot\mathrm{radical}/55,1,0],[\mathrm{radical}^{3}/55+\mathrm{radical}/44,-5\cdot\mathrm{radical}^{3}/88+37\cdot\mathrm{radical}/55,75\cdot\mathrm{radical}^{2}/484-345/242,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower7` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.23 (Pivots for branch 7).**

$$\mathrm{pivots7}:\mathrm{Fin} 4\to\mathbb{R}=[4\cdot\mathrm{radical}^{2}/5-6,5\cdot\mathrm{radical}^{2}/8-4,2\cdot\mathrm{radical}^{2}-64/5,2433\cdot\mathrm{radical}^{2}/2662-10248/1331]$$

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

$$\mathrm{lower8}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[3\cdot\mathrm{radical}^{3}/440+3\cdot\mathrm{radical}/22,-\mathrm{radical}^{3}/44+8\cdot\mathrm{radical}/55,1,0],[19\cdot\mathrm{radical}^{3}/440-17\cdot\mathrm{radical}/44,-\mathrm{radical}^{3}/440-8\cdot\mathrm{radical}/55,199\cdot\mathrm{radical}^{2}/1396-436/349,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower8` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.26 (Pivots for branch 8).**

$$\mathrm{pivots8}:\mathrm{Fin} 4\to\mathbb{R}=[3\cdot\mathrm{radical}^{2}/5-2,5\cdot\mathrm{radical}^{2}/8-3,122\cdot\mathrm{radical}^{2}/55-992/55,1814\cdot\mathrm{radical}^{2}/1745-3592/349]$$

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

$$\mathrm{lower9}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[\mathrm{radical}^{3}/2-7\cdot\mathrm{radical},-3\cdot\mathrm{radical}^{3}/4+53\cdot\mathrm{radical}/5,1,0],[-9\cdot\mathrm{radical}^{3}/20+27\cdot\mathrm{radical}/4,\mathrm{radical}^{3}/40-3\cdot\mathrm{radical}/5,137\cdot\mathrm{radical}^{2}/872-321/218,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower9` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.29 (Pivots for branch 9).**

$$\mathrm{pivots9}:\mathrm{Fin} 4\to\mathbb{R}=[7\cdot\mathrm{radical}^{2}/10-4,5\cdot\mathrm{radical}^{2}/8-7/2,104/5-2\cdot\mathrm{radical}^{2}/5,262\cdot\mathrm{radical}^{2}/545-198/109]$$

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

$$\mathrm{lower10}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[2\cdot\mathrm{radical}^{3}/5-11\cdot\mathrm{radical}/2,\mathrm{radical}^{3}/2-37\cdot\mathrm{radical}/5,1,0],[-\mathrm{radical}^{3}/10+7\cdot\mathrm{radical}/4,-43\cdot\mathrm{radical}^{3}/40+77\cdot\mathrm{radical}/5,45\cdot\mathrm{radical}^{2}/176-127/44,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower10` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.32 (Pivots for branch 10).**

$$\mathrm{pivots10}:\mathrm{Fin} 4\to\mathbb{R}=[7\cdot\mathrm{radical}^{2}/10-4,5\cdot\mathrm{radical}^{2}/8-7/2,4\cdot\mathrm{radical}^{2}/5+16/5,39\cdot\mathrm{radical}^{2}/110+1/11]$$

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

$$\mathrm{lower11}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[19\cdot\mathrm{radical}^{3}/220-21\cdot\mathrm{radical}/22,-\mathrm{radical}^{3}/22+23\cdot\mathrm{radical}/55,1,0],[-\mathrm{radical}^{3}/440+15\cdot\mathrm{radical}/44,-41\cdot\mathrm{radical}^{3}/440+62\cdot\mathrm{radical}/55,225\cdot\mathrm{radical}^{2}/1448-523/362,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower11` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.35 (Pivots for branch 11).**

$$\mathrm{pivots11}:\mathrm{Fin} 4\to\mathbb{R}=[4\cdot\mathrm{radical}^{2}/5-6,5\cdot\mathrm{radical}^{2}/8-4,114\cdot\mathrm{radical}^{2}/55-776/55,1638\cdot\mathrm{radical}^{2}/1991-12522/1991]$$

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

$$\mathrm{lower12}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[\mathrm{radical}^{3}/20-\mathrm{radical}/2,\mathrm{radical}^{3}/2-37\cdot\mathrm{radical}/5,1,0],[-5\cdot\mathrm{radical}^{3}/8+37\cdot\mathrm{radical}/4,-7\cdot\mathrm{radical}^{3}/40+12\cdot\mathrm{radical}/5,\mathrm{radical}^{2}/8-1,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower12` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.38 (Pivots for branch 12).**

$$\mathrm{pivots12}:\mathrm{Fin} 4\to\mathbb{R}=[7\cdot\mathrm{radical}^{2}/10-4,5\cdot\mathrm{radical}^{2}/8-7/2,8\cdot\mathrm{radical}^{2}/5-8,134/5-3\cdot\mathrm{radical}^{2}/2]$$

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

$$\mathrm{lower13}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[\mathrm{radical}^{3}/20-\mathrm{radical}/2,-\mathrm{radical}^{3}/22+23\cdot\mathrm{radical}/55,1,0],[-5\cdot\mathrm{radical}^{3}/88+45\cdot\mathrm{radical}/44,-7\cdot\mathrm{radical}^{3}/440+2\cdot\mathrm{radical}/55,\mathrm{radical}^{2}/8-1,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower13` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.41 (Pivots for branch 13).**

$$\mathrm{pivots13}:\mathrm{Fin} 4\to\mathbb{R}=[4\cdot\mathrm{radical}^{2}/5-6,5\cdot\mathrm{radical}^{2}/8-4,24\cdot\mathrm{radical}^{2}/11-168/11,17\cdot\mathrm{radical}^{2}/22-314/55]$$

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

$$\mathrm{lower14}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[21\cdot\mathrm{radical}^{3}/440-9\cdot\mathrm{radical}/22,3\cdot\mathrm{radical}^{3}/44-62\cdot\mathrm{radical}/55,1,0],[-9\cdot\mathrm{radical}^{3}/440+25\cdot\mathrm{radical}/44,-43\cdot\mathrm{radical}^{3}/440+72\cdot\mathrm{radical}/55,137\cdot\mathrm{radical}^{2}/1448-201/362,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower14` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.44 (Pivots for branch 14).**

$$\mathrm{pivots14}:\mathrm{Fin} 4\to\mathbb{R}=[4\cdot\mathrm{radical}^{2}/5-6,5\cdot\mathrm{radical}^{2}/8-4,114\cdot\mathrm{radical}^{2}/55-776/55,1638\cdot\mathrm{radical}^{2}/1991-12522/1991]$$

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

$$\mathrm{lower15}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[\mathrm{radical}^{3}/19-9\cdot\mathrm{radical}/19,-\mathrm{radical}^{3}/76-3\cdot\mathrm{radical}/95,1,0],[-7\cdot\mathrm{radical}^{3}/760+31\cdot\mathrm{radical}/76,-41\cdot\mathrm{radical}^{3}/760+58\cdot\mathrm{radical}/95,71\cdot\mathrm{radical}^{2}/528-149/132,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateFirst.lower15` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.47 (Pivots for branch 15).**

$$\mathrm{pivots15}:\mathrm{Fin} 4\to\mathbb{R}=[9\cdot\mathrm{radical}^{2}/10-8,5\cdot\mathrm{radical}^{2}/8-9/2,216\cdot\mathrm{radical}^{2}/95-1488/95,201\cdot\mathrm{radical}^{2}/220-238/33]$$

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
