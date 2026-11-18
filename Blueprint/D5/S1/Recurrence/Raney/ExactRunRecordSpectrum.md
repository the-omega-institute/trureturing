# Exact All-Prime R31 Run and Record Spectra

## Abstract

For every prime, the complete positive maximal zero-run length set and the distinct tied-record value set of the literal R31 sequence equal the displayed strictly ordered families.

This is the complete Theorem 2.1 of RANEY_R31_EXACT_ZERO_RUN_RECORD_SPECTRA, attributed there to Haobo Ma and Wenlin Zhang. The residue sequence is always the existing raneyNumber(3,1,n) in ZMod(p): the natural quotient is taken before reduction. Write rho(p) for this sequence and Run(rho,a,b) for IsMaximalDeltaInterval({0},rho,a,b). This includes a<=b, zeros at every index from a through b, a nonzero right neighbor, and either a=0 or a nonzero left neighbor. The actual value at zero is one.

Every length here is the natural number b+1-a. In particular an empty displayed interval with a=b+1 has length zero; it never receives the spurious length one from (b-a)+1. A weak record compares with every earlier actual run and permits ties. First occurrence compares starts of all actual runs of that same length. The theorem concerns record values: it does not assert that every occurrence of a length is itself a record.

**Definition 1.1 (Tied left-to-right record).**

$$\forall p \in \mathbb{N},\; \forall rho \in \mathbb{N} \to \operatorname{ZMod}\left(p\right),\; \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; (\operatorname{IsWeakZeroRunRecord}\left(rho, a, b\right)) \Leftrightarrow ((\operatorname{IsMaximalDeltaInterval}\left(\operatorname{singleton}\left(0\right), rho, a, b\right)) \land (\forall c \in \mathbb{N},\; \forall d \in \mathbb{N},\; ((\operatorname{IsMaximalDeltaInterval}\left(\operatorname{singleton}\left(0\right), rho, c, d\right)) \land (c < a)) \Rightarrow (d + 1 - c \le b + 1 - a)))$$

*Formalization.* `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.IsWeakZeroRunRecord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sen-Peng Eu, Zai-Ting Huang, and Louis Kao (2026). *Zero-Run Spectra of the (3,2) Raney numbers Modulo Primes*. URL: <https://arxiv.org/html/2609.25742v1>.

*Commentary.*

For any residue sequence rho:N->ZMod(p), this predicate includes actual maximality and weak domination of the length of every maximal run starting earlier.

**Definition 1.2 (First occurrence of a run length).**

$$\forall p \in \mathbb{N},\; \forall rho \in \mathbb{N} \to \operatorname{ZMod}\left(p\right),\; \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; (\operatorname{IsFirstZeroRunLength}\left(rho, a, b\right)) \Leftrightarrow ((\operatorname{IsMaximalDeltaInterval}\left(\operatorname{singleton}\left(0\right), rho, a, b\right)) \land (\forall c \in \mathbb{N},\; \forall d \in \mathbb{N},\; ((\operatorname{IsMaximalDeltaInterval}\left(\operatorname{singleton}\left(0\right), rho, c, d\right)) \land (d + 1 - c = b + 1 - a)) \Rightarrow (a \le c)))$$

*Formalization.* `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.IsFirstZeroRunLength` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sen-Peng Eu, Zai-Ting Huang, and Louis Kao (2026). *Zero-Run Spectra of the (3,2) Raney numbers Modulo Primes*. URL: <https://arxiv.org/html/2609.25742v1>.

*Commentary.*

For any rho, this predicate includes actual maximality and says no run of equal length has a smaller starting index.

**Definition 1.3 (Positive maximal-run length set).**

$$\forall p \in \mathbb{N},\; \forall rho \in \mathbb{N} \to \operatorname{ZMod}\left(p\right),\; \forall l \in \mathbb{N},\; (l \in \operatorname{positiveZeroRunLengths}\left(rho\right)) \Leftrightarrow ((0 < l) \land (\exists a \in \mathbb{N},\; \exists b \in \mathbb{N},\; (\operatorname{IsMaximalDeltaInterval}\left(\operatorname{singleton}\left(0\right), rho, a, b\right)) \land (l = b + 1 - a)))$$

*Formalization.* `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.positiveZeroRunLengths` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sen-Peng Eu, Zai-Ting Huang, and Louis Kao (2026). *Zero-Run Spectra of the (3,2) Raney numbers Modulo Primes*. URL: <https://arxiv.org/html/2609.25742v1>.

*Commentary.*

Membership means positive length and an actual finite nonempty maximal zero interval of that length; endpoints range over all natural numbers.

**Definition 1.4 (Distinct positive weak-record values).**

$$\forall p \in \mathbb{N},\; \forall rho \in \mathbb{N} \to \operatorname{ZMod}\left(p\right),\; \forall l \in \mathbb{N},\; (l \in \operatorname{positiveZeroRunRecordValues}\left(rho\right)) \Leftrightarrow ((0 < l) \land (\exists a \in \mathbb{N},\; \exists b \in \mathbb{N},\; (\operatorname{IsWeakZeroRunRecord}\left(rho, a, b\right)) \land (l = b + 1 - a)))$$

*Formalization.* `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.positiveZeroRunRecordValues` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sen-Peng Eu, Zai-Ting Huang, and Louis Kao (2026). *Zero-Run Spectra of the (3,2) Raney numbers Modulo Primes*. URL: <https://arxiv.org/html/2609.25742v1>.

*Commentary.*

Membership means positive length and an actual weak record of that length. Set membership lists each tied value only once.

**Definition 1.5 (Exact retained exponent and interval domains).**

$$\forall p \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; (\operatorname{runSpectrumRetained}\left(p, m, j\right)) \Leftrightarrow (\operatorname{ite}\left(p = 2, (2 \le m) \land (j = 1), \operatorname{ite}\left(p = 3, (1 \le m) \land (j = 1), \left(\left((5 \le p) \land (1 \le m)\right) \land ((j = 1) \lor (j = 2))\right) \land ((j = 2) \lor ((p^{m} \neq 5) \land (p^{m} \neq 7)))\right)\right))$$

*Formalization.* `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.runSpectrumRetained` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sen-Peng Eu, Zai-Ting Huang, and Louis Kao (2026). *Zero-Run Spectra of the (3,2) Raney numbers Modulo Primes*. URL: <https://arxiv.org/html/2609.25742v1>.

*Commentary.*

For p=2 use m>=2 and j=1; for p=3 use m>=1 and j=1. Otherwise require p>=5, m>=1 and j=1 or 2, retaining j=1 exactly when p^m is neither five nor seven. No additional coprimality condition is present.

**Definition 1.6 (Displayed interval starts).**

$$\forall p \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{runSpectrumStart}\left(p, m, j\right) = \operatorname{ite}\left(p = 2, \operatorname{NatDiv}\left(2^{m + 1} + 2, 3\right), \operatorname{ite}\left(p = 3, \operatorname{NatDiv}\left(3^{m} + 1, 2\right), \operatorname{NatDiv}\left(j \cdot p^{m} + 2, 3\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.runSpectrumStart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sen-Peng Eu, Zai-Ting Huang, and Louis Kao (2026). *Zero-Run Spectra of the (3,2) Raney numbers Modulo Primes*. URL: <https://arxiv.org/html/2609.25742v1>.

*Commentary.*

The starts are ceil(2^(m+1)/3), (3^m+1)/2, and ceil(j*p^m/3), respectively. All divisions in the formula are natural divisions.

**Definition 1.7 (Displayed interval ends).**

$$\forall p \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{runSpectrumLast}\left(p, m, j\right) = \operatorname{ite}\left(p = 2, 2^{m} - 1, \operatorname{ite}\left(p = 3, \operatorname{NatDiv}\left(3^{m + 1} - 3, 2\right), \operatorname{ite}\left(j = 1, \operatorname{NatDiv}\left(p^{m} - 3, 2\right), p^{m} - 1\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.runSpectrumLast` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sen-Peng Eu, Zai-Ting Huang, and Louis Kao (2026). *Zero-Run Spectra of the (3,2) Raney numbers Modulo Primes*. URL: <https://arxiv.org/html/2609.25742v1>.

*Commentary.*

The ends are 2^m-1, (3^(m+1)-3)/2, and, for p>=5, (p^m-3)/2 at j=1 or p^m-1 at j=2.

**Definition 1.8 (Exact branch length formulas).**

$$\forall p \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{runSpectrumLength}\left(p, m, j\right) = \operatorname{ite}\left(p = 2, \operatorname{NatDiv}\left(2^{m}, 3\right), \operatorname{ite}\left(p = 3, 3^{m} - 1, \operatorname{ite}\left(j = 1, \operatorname{ite}\left(\operatorname{mod}\left(p^{m}, 6\right) = 1, \operatorname{NatDiv}\left(p^{m} - 7, 6\right), \operatorname{NatDiv}\left(p^{m} - 5, 6\right)\right), \operatorname{NatDiv}\left(p^{m}, 3\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.runSpectrumLength` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sen-Peng Eu, Zai-Ting Huang, and Louis Kao (2026). *Zero-Run Spectra of the (3,2) Raney numbers Modulo Primes*. URL: <https://arxiv.org/html/2609.25742v1>.

*Commentary.*

The values are floor(2^m/3), 3^m-1, and, for p>=5, (q-7)/6 if j=1 and q mod 6=1, (q-5)/6 if j=1 and q mod 6=5, or floor(q/3) if j=2. For the prime powers in scope, these are the only two residues modulo six.

In the final formula abbreviate the displayed functions by A(p,m,j), B(p,m,j), L(p,m,j) and Ret(p,m,j). Define Values(p)={l in N : there exist m,j in N with Ret(p,m,j) and l=L(p,m,j)}. These are not extra hypotheses or a supplied branch certificate: all the following conclusions are proved for the literal sequence.

**Theorem 1.9 (Complete all-prime theorem).**

$$\forall p \in \mathbb{N},\; (\operatorname{Prime}\left(p\right)) \Rightarrow (\left(\left(\left(\left((\operatorname{positiveZeroRunLengths}\left(\operatorname{rho}\left(p\right)\right) = \operatorname{Values}\left(p\right)) \land (\operatorname{positiveZeroRunRecordValues}\left(\operatorname{rho}\left(p\right)\right) = \operatorname{Values}\left(p\right))\right) \land (\forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; (\operatorname{Ret}\left(p, m, j\right)) \Rightarrow (\left(\left(\left((\operatorname{IsMaximalDeltaInterval}\left(\operatorname{singleton}\left(0\right), \operatorname{rho}\left(p\right), \operatorname{A}\left(p, m, j\right), \operatorname{B}\left(p, m, j\right)\right)) \land (0 < \operatorname{L}\left(p, m, j\right))\right) \land (\operatorname{B}\left(p, m, j\right) + 1 - \operatorname{A}\left(p, m, j\right) = \operatorname{L}\left(p, m, j\right))\right) \land (\operatorname{IsFirstZeroRunLength}\left(\operatorname{rho}\left(p\right), \operatorname{A}\left(p, m, j\right), \operatorname{B}\left(p, m, j\right)\right))\right) \land (\operatorname{IsWeakZeroRunRecord}\left(\operatorname{rho}\left(p\right), \operatorname{A}\left(p, m, j\right), \operatorname{B}\left(p, m, j\right)\right))))\right) \land (\forall m \in \mathbb{N},\; \forall h \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall k \in \mathbb{N},\; (\left((\operatorname{Ret}\left(p, m, j\right)) \land (\operatorname{Ret}\left(p, h, k\right))\right) \land ((m < h) \lor ((m = h) \land (j < k)))) \Rightarrow (\operatorname{L}\left(p, m, j\right) < \operatorname{L}\left(p, h, k\right)))\right) \land (\forall m \in \mathbb{N},\; \forall h \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall k \in \mathbb{N},\; (\left((\operatorname{Ret}\left(p, m, j\right)) \land (\operatorname{Ret}\left(p, h, k\right))\right) \land (\operatorname{L}\left(p, m, j\right) = \operatorname{L}\left(p, h, k\right))) \Rightarrow ((m = h) \land (j = k)))\right) \land ((5 \le p) \Rightarrow (\forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; ((1 \le m) \land ((j = 1) \lor (j = 2))) \Rightarrow ((\operatorname{NatDiv}\left(j \cdot p^{m} + 2, 3\right) \le \operatorname{ite}\left(j = 1, \operatorname{NatDiv}\left(p^{m} - 3, 2\right), p^{m} - 1\right)) \Leftrightarrow ((j = 2) \lor ((p^{m} \neq 5) \land (p^{m} \neq 7)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.raney_all_prime_exact_run_record_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sen-Peng Eu, Zai-Ting Huang, and Louis Kao (2026). *Zero-Run Spectra of the (3,2) Raney numbers Modulo Primes*. URL: <https://arxiv.org/html/2609.25742v1>.

*Commentary.*

The two complete positive sets both equal Values(p). Every retained interval is an actual maximal run, has its stated strictly positive length, is a first occurrence and is a weak record. Lengths strictly increase in exponent-then-interval order, and equality of retained lengths forces equality of both indices. At p>=5, the displayed nonemptiness equivalence proves exactly the omissions I1(5) and I1(7).

The proof directly consumes raney_binary_exact_zero_run_spectrum, raney_three_exact_zero_runs and ExactPrime.raney_prime_ge_five_spectrum. Prime trichotomy is proved internally. The binary and larger-prime witnesses are strictly longer than every earlier actual run. At three, the complete endpoint classification, weak comparison and uniqueness of a same-length interval imply that same strict earlier bound. This produces First and weak Record without assuming any correspondence with a proxy sequence.

For set completeness, classify an arbitrary actual maximal run by a retained length. For the converse, take the displayed actual witness; its strict earlier bound makes it a record. A record is already an actual maximal run, giving the reverse inclusion for record values. Strict ordering excludes duplicate retained values. The branch proofs establish the literal support and component completeness.

Corollary 3.1 is a direct substitution consequence: exponent parity gives 2^m mod 3 and the odd-prime powers modulo six, separating the displayed affine families; strict ordering gives their disjointness. The first interval rows at (p,m)=(5,1),(7,1) are omitted because their lengths are zero. The corollary's initial values and witness table are evaluations of these formulas, with no additional table theorem or independent mathematical assumption.

## References

- Truth anchor: `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.IsFirstZeroRunLength`
- Truth anchor: `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.IsWeakZeroRunRecord`
- Truth anchor: `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.positiveZeroRunLengths`
- Truth anchor: `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.positiveZeroRunRecordValues`
- Truth anchor: `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.raney_all_prime_exact_run_record_spectrum`
- Truth anchor: `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.runSpectrumLast`
- Truth anchor: `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.runSpectrumLength`
- Truth anchor: `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.runSpectrumRetained`
- Truth anchor: `D5/S1/Recurrence/Raney/ExactRunRecordSpectrum.runSpectrumStart`
- Dependency: [D5/S1/Recurrence/Raney/ExactBinaryRuns](ExactBinaryRuns.md)
- Dependency: [D5/S1/Recurrence/Raney/ExactPrimeRuns](ExactPrimeRuns.md)
- Dependency: [D5/S1/Recurrence/Raney/ExactTernaryRuns](ExactTernaryRuns.md)
