# Ququint Certificate Second Half

## Abstract

Exact LDL factorizations for sixteen numerical branch matrices.

Each displayed identity uses branch from D5.S3.Quantum.Magic.QuquintCertificateData and the public lower and pivot declarations named in that identity. Matrices are displayed as vectors of rows; radical denotes QuquintCertificateData.radical. These are certificates for explicit numerical matrices. QuquintCertificateBridge identifies their data with the phase-point forms of QuquintWignerCriticalGeometry.

**Definition 1.1 (Unit-lower factor for branch 16).**

$$\mathrm{lower16}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[3\cdot\mathrm{radical}^{3}/88-7\cdot\mathrm{radical}/22,-\mathrm{radical}^{3}/44+8\cdot\mathrm{radical}/55,1,0],[-13\cdot\mathrm{radical}^{3}/440+29\cdot\mathrm{radical}/44,-39\cdot\mathrm{radical}^{3}/440+62\cdot\mathrm{radical}/55,7\cdot\mathrm{radical}^{2}/62-76/93,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower16` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.2 (Pivots for branch 16).**

$$\mathrm{pivots16}:\mathrm{Fin} 4\to\mathbb{R}=[3\cdot\mathrm{radical}^{2}/5-2,5\cdot\mathrm{radical}^{2}/8-3,114\cdot\mathrm{radical}^{2}/55-888/55,542\cdot\mathrm{radical}^{2}/465-1120/93]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots16` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.3 (Branch 16).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(16)=\mathrm{lower16}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots16})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower16})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_16` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.4 (Unit-lower factor for branch 17).**

$$\mathrm{lower17}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[3\cdot\mathrm{radical}^{3}/20-2\cdot\mathrm{radical},-3\cdot\mathrm{radical}^{3}/4+53\cdot\mathrm{radical}/5,1,0],[11\cdot\mathrm{radical}^{3}/40-15\cdot\mathrm{radical}/4,37\cdot\mathrm{radical}^{3}/40-68\cdot\mathrm{radical}/5,45\cdot\mathrm{radical}^{2}/176-127/44,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower17` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.5 (Pivots for branch 17).**

$$\mathrm{pivots17}:\mathrm{Fin} 4\to\mathbb{R}=[7\cdot\mathrm{radical}^{2}/10-4,5\cdot\mathrm{radical}^{2}/8-7/2,4\cdot\mathrm{radical}^{2}/5+16/5,39\cdot\mathrm{radical}^{2}/110+1/11]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots17` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.6 (Branch 17).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(17)=\mathrm{lower17}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots17})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower17})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_17` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.7 (Unit-lower factor for branch 18).**

$$\mathrm{lower18}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[\mathrm{radical}^{3}/20-\mathrm{radical}/2,\mathrm{radical}^{3}/2-37\cdot\mathrm{radical}/5,1,0],[5\cdot\mathrm{radical}^{3}/8-35\cdot\mathrm{radical}/4,-7\cdot\mathrm{radical}^{3}/40+12\cdot\mathrm{radical}/5,\mathrm{radical}^{2}/8-1,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower18` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.8 (Pivots for branch 18).**

$$\mathrm{pivots18}:\mathrm{Fin} 4\to\mathbb{R}=[7\cdot\mathrm{radical}^{2}/10-4,5\cdot\mathrm{radical}^{2}/8-7/2,8\cdot\mathrm{radical}^{2}/5-8,134/5-3\cdot\mathrm{radical}^{2}/2]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots18` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.9 (Branch 18).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(18)=\mathrm{lower18}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots18})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower18})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_18` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.10 (Unit-lower factor for branch 19).**

$$\mathrm{lower19}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[\mathrm{radical}^{3}/20-\mathrm{radical}/2,-\mathrm{radical}^{3}/22+23\cdot\mathrm{radical}/55,1,0],[5\cdot\mathrm{radical}^{3}/88-23\cdot\mathrm{radical}/44,-7\cdot\mathrm{radical}^{3}/440+2\cdot\mathrm{radical}/55,\mathrm{radical}^{2}/8-1,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower19` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.11 (Pivots for branch 19).**

$$\mathrm{pivots19}:\mathrm{Fin} 4\to\mathbb{R}=[4\cdot\mathrm{radical}^{2}/5-6,5\cdot\mathrm{radical}^{2}/8-4,24\cdot\mathrm{radical}^{2}/11-168/11,17\cdot\mathrm{radical}^{2}/22-314/55]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots19` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.12 (Branch 19).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(19)=\mathrm{lower19}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots19})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower19})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_19` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.13 (Unit-lower factor for branch 20).**

$$\mathrm{lower20}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[-3\cdot\mathrm{radical}^{3}/10+9\cdot\mathrm{radical}/2,\mathrm{radical}^{3}/2-37\cdot\mathrm{radical}/5,1,0],[\mathrm{radical}^{3}/10-5\cdot\mathrm{radical}/4,29\cdot\mathrm{radical}^{3}/40-53\cdot\mathrm{radical}/5,39/44-\mathrm{radical}^{2}/176,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower20` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.14 (Pivots for branch 20).**

$$\mathrm{pivots20}:\mathrm{Fin} 4\to\mathbb{R}=[7\cdot\mathrm{radical}^{2}/10-4,5\cdot\mathrm{radical}^{2}/8-7/2,4\cdot\mathrm{radical}^{2}/5+16/5,39\cdot\mathrm{radical}^{2}/110+1/11]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots20` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.15 (Branch 20).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(20)=\mathrm{lower20}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots20})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower20})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_20` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.16 (Unit-lower factor for branch 21).**

$$\mathrm{lower21}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[3\cdot\mathrm{radical}^{3}/220-\mathrm{radical}/22,-\mathrm{radical}^{3}/22+23\cdot\mathrm{radical}/55,1,0],[\mathrm{radical}^{3}/440+7\cdot\mathrm{radical}/44,27\cdot\mathrm{radical}^{3}/440-58\cdot\mathrm{radical}/55,137\cdot\mathrm{radical}^{2}/1448-201/362,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower21` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.17 (Pivots for branch 21).**

$$\mathrm{pivots21}:\mathrm{Fin} 4\to\mathbb{R}=[4\cdot\mathrm{radical}^{2}/5-6,5\cdot\mathrm{radical}^{2}/8-4,114\cdot\mathrm{radical}^{2}/55-776/55,1638\cdot\mathrm{radical}^{2}/1991-12522/1991]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots21` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.18 (Branch 21).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(21)=\mathrm{lower21}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots21})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower21})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_21` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.19 (Unit-lower factor for branch 22).**

$$\mathrm{lower22}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[\mathrm{radical}^{3}/88+\mathrm{radical}/22,3\cdot\mathrm{radical}^{3}/44-62\cdot\mathrm{radical}/55,1,0],[17\cdot\mathrm{radical}^{3}/440-13\cdot\mathrm{radical}/44,-9\cdot\mathrm{radical}^{3}/440+12\cdot\mathrm{radical}/55,23\cdot\mathrm{radical}^{2}/242-139/242,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower22` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.20 (Pivots for branch 22).**

$$\mathrm{pivots22}:\mathrm{Fin} 4\to\mathbb{R}=[4\cdot\mathrm{radical}^{2}/5-6,5\cdot\mathrm{radical}^{2}/8-4,2\cdot\mathrm{radical}^{2}-64/5,2433\cdot\mathrm{radical}^{2}/2662-10248/1331]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots22` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.21 (Branch 22).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(22)=\mathrm{lower22}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots22})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower22})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_22` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.22 (Unit-lower factor for branch 23).**

$$\mathrm{lower23}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[11\cdot\mathrm{radical}^{3}/380-4\cdot\mathrm{radical}/19,-\mathrm{radical}^{3}/76-3\cdot\mathrm{radical}/95,1,0],[2\cdot\mathrm{radical}^{3}/95-3\cdot\mathrm{radical}/76,-9\cdot\mathrm{radical}^{3}/760+3\cdot\mathrm{radical}/95,149\cdot\mathrm{radical}^{2}/1364-523/682,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower23` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.23 (Pivots for branch 23).**

$$\mathrm{pivots23}:\mathrm{Fin} 4\to\mathbb{R}=[9\cdot\mathrm{radical}^{2}/10-8,5\cdot\mathrm{radical}^{2}/8-9/2,214\cdot\mathrm{radical}^{2}/95-1432/95,3227\cdot\mathrm{radical}^{2}/3410-2654/341]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots23` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.24 (Branch 23).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(23)=\mathrm{lower23}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots23})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower23})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_23` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.25 (Unit-lower factor for branch 24).**

$$\mathrm{lower24}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[3\cdot\mathrm{radical}^{3}/5-17\cdot\mathrm{radical}/2,\mathrm{radical}^{3}/2-37\cdot\mathrm{radical}/5,1,0],[-7\cdot\mathrm{radical}^{3}/40+11\cdot\mathrm{radical}/4,3\cdot\mathrm{radical}^{3}/8-28\cdot\mathrm{radical}/5,81\cdot\mathrm{radical}^{2}/872-115/218,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower24` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.26 (Pivots for branch 24).**

$$\mathrm{pivots24}:\mathrm{Fin} 4\to\mathbb{R}=[7\cdot\mathrm{radical}^{2}/10-4,5\cdot\mathrm{radical}^{2}/8-7/2,104/5-2\cdot\mathrm{radical}^{2}/5,262\cdot\mathrm{radical}^{2}/545-198/109]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots24` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.27 (Branch 24).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(24)=\mathrm{lower24}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots24})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower24})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_24` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.28 (Unit-lower factor for branch 25).**

$$\mathrm{lower25}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[\mathrm{radical}^{3}/11-25\cdot\mathrm{radical}/22,-\mathrm{radical}^{3}/22+23\cdot\mathrm{radical}/55,1,0],[-\mathrm{radical}^{3}/55+21\cdot\mathrm{radical}/44,\mathrm{radical}^{3}/40-3\cdot\mathrm{radical}/5,23\cdot\mathrm{radical}^{2}/242-139/242,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower25` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.29 (Pivots for branch 25).**

$$\mathrm{pivots25}:\mathrm{Fin} 4\to\mathbb{R}=[4\cdot\mathrm{radical}^{2}/5-6,5\cdot\mathrm{radical}^{2}/8-4,2\cdot\mathrm{radical}^{2}-64/5,2433\cdot\mathrm{radical}^{2}/2662-10248/1331]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots25` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.30 (Branch 25).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(25)=\mathrm{lower25}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots25})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower25})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_25` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.31 (Unit-lower factor for branch 26).**

$$\mathrm{lower26}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[39\cdot\mathrm{radical}^{3}/440-23\cdot\mathrm{radical}/22,3\cdot\mathrm{radical}^{3}/44-62\cdot\mathrm{radical}/55,1,0],[\mathrm{radical}^{3}/55+\mathrm{radical}/44,-5\cdot\mathrm{radical}^{3}/88+37\cdot\mathrm{radical}/55,75\cdot\mathrm{radical}^{2}/484-345/242,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower26` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.32 (Pivots for branch 26).**

$$\mathrm{pivots26}:\mathrm{Fin} 4\to\mathbb{R}=[4\cdot\mathrm{radical}^{2}/5-6,5\cdot\mathrm{radical}^{2}/8-4,2\cdot\mathrm{radical}^{2}-64/5,2433\cdot\mathrm{radical}^{2}/2662-10248/1331]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots26` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.33 (Branch 26).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(26)=\mathrm{lower26}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots26})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower26})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_26` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.34 (Unit-lower factor for branch 27).**

$$\mathrm{lower27}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[27\cdot\mathrm{radical}^{3}/380-15\cdot\mathrm{radical}/19,-\mathrm{radical}^{3}/76-3\cdot\mathrm{radical}/95,1,0],[9\cdot\mathrm{radical}^{3}/760+9\cdot\mathrm{radical}/76,-27\cdot\mathrm{radical}^{3}/760+28\cdot\mathrm{radical}/95,48\cdot\mathrm{radical}^{2}/341-841/682,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower27` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.35 (Pivots for branch 27).**

$$\mathrm{pivots27}:\mathrm{Fin} 4\to\mathbb{R}=[9\cdot\mathrm{radical}^{2}/10-8,5\cdot\mathrm{radical}^{2}/8-9/2,214\cdot\mathrm{radical}^{2}/95-1432/95,3227\cdot\mathrm{radical}^{2}/3410-2654/341]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots27` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.36 (Branch 27).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(27)=\mathrm{lower27}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots27})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower27})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_27` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.37 (Unit-lower factor for branch 28).**

$$\mathrm{lower28}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[23\cdot\mathrm{radical}^{3}/440-13\cdot\mathrm{radical}/22,3\cdot\mathrm{radical}^{3}/44-62\cdot\mathrm{radical}/55,1,0],[-2\cdot\mathrm{radical}^{3}/55+31\cdot\mathrm{radical}/44,9\cdot\mathrm{radical}^{3}/440-23\cdot\mathrm{radical}/55,225\cdot\mathrm{radical}^{2}/1448-523/362,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower28` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.38 (Pivots for branch 28).**

$$\mathrm{pivots28}:\mathrm{Fin} 4\to\mathbb{R}=[4\cdot\mathrm{radical}^{2}/5-6,5\cdot\mathrm{radical}^{2}/8-4,114\cdot\mathrm{radical}^{2}/55-776/55,1638\cdot\mathrm{radical}^{2}/1991-12522/1991]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots28` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.39 (Branch 28).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(28)=\mathrm{lower28}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots28})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower28})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_28` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.40 (Unit-lower factor for branch 29).**

$$\mathrm{lower29}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[9\cdot\mathrm{radical}^{3}/190-10\cdot\mathrm{radical}/19,-\mathrm{radical}^{3}/76-3\cdot\mathrm{radical}/95,1,0],[-9\cdot\mathrm{radical}^{3}/380+39\cdot\mathrm{radical}/76,\mathrm{radical}^{3}/152-27\cdot\mathrm{radical}/95,61\cdot\mathrm{radical}^{2}/528-115/132,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower29` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.41 (Pivots for branch 29).**

$$\mathrm{pivots29}:\mathrm{Fin} 4\to\mathbb{R}=[9\cdot\mathrm{radical}^{2}/10-8,5\cdot\mathrm{radical}^{2}/8-9/2,216\cdot\mathrm{radical}^{2}/95-1488/95,201\cdot\mathrm{radical}^{2}/220-238/33]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots29` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.42 (Branch 29).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(29)=\mathrm{lower29}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots29})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower29})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_29` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.43 (Unit-lower factor for branch 30).**

$$\mathrm{lower30}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[\mathrm{radical}^{3}/20-\mathrm{radical}/2,\mathrm{radical}^{3}/19-83\cdot\mathrm{radical}/95,1,0],[\mathrm{radical}/4,-23\cdot\mathrm{radical}^{3}/760+33\cdot\mathrm{radical}/95,\mathrm{radical}^{2}/8-1,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower30` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.44 (Pivots for branch 30).**

$$\mathrm{pivots30}:\mathrm{Fin} 4\to\mathbb{R}=[9\cdot\mathrm{radical}^{2}/10-8,5\cdot\mathrm{radical}^{2}/8-9/2,206\cdot\mathrm{radical}^{2}/95-272/19,\mathrm{radical}^{2}-42/5]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots30` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.45 (Branch 30).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(30)=\mathrm{lower30}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots30})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower30})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_30` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

**Definition 1.46 (Unit-lower factor for branch 31).**

$$\mathrm{lower31}:\mathrm{Matrix} (\mathrm{Fin} 4) (\mathrm{Fin} 4) \mathbb{R}=[[1,0,0,0],[3/2-\mathrm{radical}^{2}/8,1,0,0],[\mathrm{radical}^{3}/20-\mathrm{radical}/2,-\mathrm{radical}/5,1,0],[\mathrm{radical}/4,-\mathrm{radical}^{3}/40+\mathrm{radical}/5,\mathrm{radical}^{2}/8-1,1]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower31` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit four-by-four unit-lower certificate table in Lean has diagonal entries one, entries above the diagonal zero, and six rational-polynomial entries in QuquintCertificateData.radical below the diagonal.

**Definition 1.47 (Pivots for branch 31).**

$$\mathrm{pivots31}:\mathrm{Fin} 4\to\mathbb{R}=[\mathrm{radical}^{2}-10,5\cdot\mathrm{radical}^{2}/8-5,12\cdot\mathrm{radical}^{2}/5-16,\mathrm{radical}^{2}-8]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots31` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four ordered quartic-field entries are the explicit pivot vector in Lean. The corresponding ldl identity uses them in this order; positivity is proved in QuquintCertificateAssembly.

**Theorem 1.48 (Branch 31).**

$$-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(31)=\mathrm{lower31}\cdot\mathrm{Matrix}.\mathrm{diagonal}(\mathrm{pivots31})\cdot\mathrm{Matrix}.\mathrm{transpose}(\mathrm{lower31})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_31` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic using radical_quartic verifies every entry of the factorization. The matrices and pivots are the public Lean declarations in this module; no positivity claim is inferred from the factorization alone.

## References

- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_16`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_17`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_18`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_19`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_20`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_21`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_22`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_23`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_24`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_25`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_26`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_27`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_28`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_29`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_30`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.ldl_31`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower16`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower17`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower18`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower19`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower20`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower21`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower22`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower23`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower24`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower25`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower26`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower27`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower28`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower29`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower30`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.lower31`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots16`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots17`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots18`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots19`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots20`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots21`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots22`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots23`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots24`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots25`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots26`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots27`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots28`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots29`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots30`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateSecond.pivots31`
- Dependency: [D5/S3/Quantum/Magic/QuquintCertificateData](QuquintCertificateData.md)
