# Countable finite-excitation Fock space

## Abstract

Countably many fermionic modes act on all finite occupation states through an exact coherent finite-prefix construction.

The carrier is algebraic: every state has finite support among finite subsets of the natural numbers. No completion or infinite operator sum is used. FullC is the original finite Jordan–Wigner annihilator. Its signed entry formula is supplied by HardCoreCompression.fullC_entry; the Boolean occupation encoding and its inverse are supplied by CompletedCorrelationalBound. The new intertwinings identify those matrix actions with the all-particle-number signed occupation action. Finite capture and word transport then transfer the actual finite CAR to unrestricted natural indices. The same-site square is obtained algebraically from FockMajoranaCarrier.majorana_clifford_and_parity. The linear extension uses Mathlib Finsupp.lsum.

**Definition 1.1 (Fock).**

$$Fock = \operatorname{Finsupp}\left(\operatorname{Finset}\left(Nat\right), Complex\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CountableOccupationFock.Fock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The direct sum has one coordinate for each finite occupation set.

**Definition 1.2 (ket).**

$$\forall S \in \operatorname{Finset}\left(Nat\right),\; \operatorname{ket}\left(S\right) = \operatorname{Finsupp}.\operatorname{single}\left(S, 1\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CountableOccupationFock.ket` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The occupation basis vector has coefficient one at S.

**Definition 1.3 (vacuum).**

$$vacuum = \operatorname{ket}\left(\operatorname{Finset}.\operatorname{empty}\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CountableOccupationFock.vacuum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vacuum is the empty occupation.

**Definition 1.4 (lowerCount).**

$$\forall j \in Nat,\; \forall S \in \operatorname{Finset}\left(Nat\right),\; \operatorname{lowerCount}\left(j, S\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\lambda (i:Nat) \mapsto i < j, S\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CountableOccupationFock.lowerCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only occupied sites strictly below j contribute to the sign.

**Definition 1.5 (phase).**

$$\forall j \in Nat,\; \forall S \in \operatorname{Finset}\left(Nat\right),\; \operatorname{phase}\left(j, S\right) = (-1:Complex)^{\operatorname{lowerCount}\left(j, S\right)}$$

*Formalization.* `D5/S3/Quantum/Fermionic/CountableOccupationFock.phase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sign is real and equals plus or minus one.

**Definition 1.6 (annihilate).**

$$\forall j \in Nat,\; \operatorname{annihilate}\left(j\right) = \operatorname{Finsupp}.\operatorname{lsum}\left(Complex, \lambda (S:\operatorname{Finset}\left(Nat\right)) \mapsto \operatorname{LinearMap}.\operatorname{smulRight}\left(\operatorname{LinearMap}.\operatorname{id}, \operatorname{ite}\left(j \in S, \operatorname{smul}\left(\operatorname{phase}\left(j, S\right), \operatorname{ket}\left(\operatorname{Finset}.\operatorname{erase}\left(S, j\right)\right)\right), 0\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CountableOccupationFock.annihilate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed deletion rule extends linearly to a genuine endomorphism.

**Definition 1.7 (create).**

$$\forall j \in Nat,\; \operatorname{create}\left(j\right) = \operatorname{Finsupp}.\operatorname{lsum}\left(Complex, \lambda (S:\operatorname{Finset}\left(Nat\right)) \mapsto \operatorname{LinearMap}.\operatorname{smulRight}\left(\operatorname{LinearMap}.\operatorname{id}, \operatorname{ite}\left(j \in S, 0, \operatorname{smul}\left(\operatorname{phase}\left(j, S\right), \operatorname{ket}\left(\operatorname{insert}\left(j, S\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CountableOccupationFock.create` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed insertion rule vanishes at an already occupied site and extends linearly.

**Definition 1.8 (parity).**

$$parity = \operatorname{Finsupp}.\operatorname{lsum}\left(Complex, \lambda (S:\operatorname{Finset}\left(Nat\right)) \mapsto \operatorname{LinearMap}.\operatorname{smulRight}\left(\operatorname{LinearMap}.\operatorname{id}, \operatorname{smul}\left((-1:Complex)^{\operatorname{Finset}.\operatorname{card}\left(S\right)}, \operatorname{ket}\left(S\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CountableOccupationFock.parity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Parity is the occupation-cardinality sign.

**Definition 1.9 (prefixEmbed).**

$$\forall N \in Nat,\; \forall v \in \operatorname{Assignment}\left(N\right) \to Complex,\; \operatorname{prefixEmbed}\left(N, v\right) = \sum_{t:\operatorname{Assignment}\left(N\right)} \operatorname{smul}\left(\operatorname{v}\left(t\right), \operatorname{ket}\left(\operatorname{occupationSet}\left(t\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CountableOccupationFock.prefixEmbed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite Boolean vector is embedded by its original occupation coordinates.

**Theorem 1.10 (prefixEmbed injective).**

$$\forall N \in Nat,\; \operatorname{Function}.\operatorname{Injective}\left(\operatorname{prefixEmbed}\left(N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.prefixEmbed_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reading the coefficient at an encoded occupation recovers the finite input coordinate.

**Theorem 1.11 (jw annihilate intertwining).**

$$\forall N \in Nat,\; \forall j \in \operatorname{Fin}\left(N\right),\; \forall v \in \operatorname{Assignment}\left(N\right) \to Complex,\; \operatorname{annihilate}\left(\operatorname{Fin}.\operatorname{val}\left(j\right), \operatorname{prefixEmbed}\left(N, v\right)\right) = \operatorname{prefixEmbed}\left(N, \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{fullC}\left(j\right), v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.jw_annihilate_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing signed matrix coefficient and occupation deletion identify the two actual actions.

**Theorem 1.12 (jw create intertwining).**

$$\forall N \in Nat,\; \forall j \in \operatorname{Fin}\left(N\right),\; \forall v \in \operatorname{Assignment}\left(N\right) \to Complex,\; \operatorname{create}\left(\operatorname{Fin}.\operatorname{val}\left(j\right), \operatorname{prefixEmbed}\left(N, v\right)\right) = \operatorname{prefixEmbed}\left(N, \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{fullC}\left(j\right)\right), v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.jw_create_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugate transposition of the existing entry formula gives signed occupation insertion; the phase is real.

**Definition 1.13 (prefixExtend).**

$$\forall N \in Nat,\; \forall M \in Nat,\; \forall v \in \operatorname{Assignment}\left(N\right) \to Complex,\; \operatorname{prefixExtend}\left(N, M, v\right) = \sum_{t:\operatorname{Assignment}\left(N\right)} \operatorname{smul}\left(\operatorname{v}\left(t\right), \operatorname{Pi}.\operatorname{single}\left(\operatorname{occupationOfSet}\left(M, \operatorname{occupationSet}\left(t\right)\right), 1\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CountableOccupationFock.prefixExtend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assignments are extended by false at the additional sites. On basis assignments the displayed occupationOfSet formula is literal.

**Theorem 1.14 (prefix coherence).**

$$\forall N \in Nat,\; \forall M \in Nat,\; N \le M \Rightarrow \left(\forall v \in \operatorname{Assignment}\left(N\right) \to Complex,\; \operatorname{prefixEmbed}\left(M, \operatorname{prefixExtend}\left(N, M, v\right)\right) = \operatorname{prefixEmbed}\left(N, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.prefix_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N at most M, extending by empty sites preserves the countable state.

**Theorem 1.15 (cutoff annihilate coherence).**

$$\forall N \in Nat,\; \forall M \in Nat,\; \forall h \in N \le M,\; \forall j \in \operatorname{Fin}\left(N\right),\; \forall v \in \operatorname{Assignment}\left(N\right) \to Complex,\; \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{fullC}\left(\operatorname{Fin}.\operatorname{castLE}\left(h, j\right)\right), \operatorname{prefixExtend}\left(N, M, v\right)\right) = \operatorname{prefixExtend}\left(N, M, \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{fullC}\left(j\right), v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.cutoff_annihilate_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Injectivity of the larger embedding and the annihilator intertwining prove coherent matrix transport.

**Theorem 1.16 (cutoff create coherence).**

$$\forall N \in Nat,\; \forall M \in Nat,\; \forall h \in N \le M,\; \forall j \in \operatorname{Fin}\left(N\right),\; \forall v \in \operatorname{Assignment}\left(N\right) \to Complex,\; \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{fullC}\left(\operatorname{Fin}.\operatorname{castLE}\left(h, j\right)\right)\right), \operatorname{prefixExtend}\left(N, M, v\right)\right) = \operatorname{prefixExtend}\left(N, M, \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{fullC}\left(j\right)\right), v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.cutoff_create_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The creator matrices obey the same coherent extension law.

**Theorem 1.17 (finite capture).**

$$\forall v \in Fock,\; \forall J \in \operatorname{Finset}\left(Nat\right),\; \exists N \in Nat,\; \left(\forall j \in Nat,\; j \in J \Rightarrow j < N\right) \land \left(\exists w \in \operatorname{Assignment}\left(N\right) \to Complex,\; \operatorname{prefixEmbed}\left(N, w\right) = v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.finite_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One prefix contains every occupied site of the state and every site in the selected finite set J. Capture is exact, including the empty-state boundary.

**Definition 1.18 (mode).**

$$\forall j \in Nat,\; \forall b \in Bool,\; \operatorname{mode}\left(j, b\right) = \operatorname{ite}\left(b, \operatorname{create}\left(j\right), \operatorname{annihilate}\left(j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CountableOccupationFock.mode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

True selects creation and false selects annihilation.

**Definition 1.19 (finiteMode).**

$$\forall N \in Nat,\; \forall j \in \operatorname{Fin}\left(N\right),\; \forall b \in Bool,\; \operatorname{finiteMode}\left(j, b\right) = \operatorname{ite}\left(b, \operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{fullC}\left(j\right)\right), \operatorname{fullC}\left(j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CountableOccupationFock.finiteMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite supplier follows the same Boolean convention.

**Definition 1.20 (word).**

$$\operatorname{word}\left(\operatorname{List}.\operatorname{nil}\right) = (1:\operatorname{Module}.\operatorname{End}\left(Complex, Fock\right)) \land \left(\forall p \in \operatorname{Prod}\left(Nat, Bool\right),\; \forall w \in \operatorname{List}\left(\operatorname{Prod}\left(Nat, Bool\right)\right),\; \operatorname{word}\left(\operatorname{List}.\operatorname{cons}\left(p, w\right)\right) = \operatorname{mode}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right), \operatorname{Prod}.\operatorname{snd}\left(p\right)\right) \cdot \operatorname{word}\left(w\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CountableOccupationFock.word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Products act on the rightmost state first.

**Definition 1.21 (finiteWord).**

$$\forall N \in Nat,\; \operatorname{finiteWord}\left(\operatorname{List}.\operatorname{nil}\right) = \operatorname{Matrix}.\operatorname{one}\left(\operatorname{Assignment}\left(N\right)\right) \land \left(\forall p \in \operatorname{Prod}\left(\operatorname{Fin}\left(N\right), Bool\right),\; \forall w \in \operatorname{List}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(N\right), Bool\right)\right),\; \operatorname{finiteWord}\left(\operatorname{List}.\operatorname{cons}\left(p, w\right)\right) = \operatorname{finiteMode}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right), \operatorname{Prod}.\operatorname{snd}\left(p\right)\right) \cdot \operatorname{finiteWord}\left(w\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CountableOccupationFock.finiteWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite matrix words include the empty identity word.

**Theorem 1.22 (word intertwining).**

$$\forall N \in Nat,\; \forall w \in \operatorname{List}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(N\right), Bool\right)\right),\; \forall v \in \operatorname{Assignment}\left(N\right) \to Complex,\; \operatorname{word}\left(\operatorname{List}.\operatorname{map}\left(\lambda (p:\operatorname{Prod}\left(\operatorname{Fin}\left(N\right), Bool\right)) \mapsto \operatorname{Prod}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right), \operatorname{Prod}.\operatorname{snd}\left(p\right)\right), w\right), \operatorname{prefixEmbed}\left(N, v\right)\right) = \operatorname{prefixEmbed}\left(N, \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{finiteWord}\left(w\right), v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.word_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both single-operator intertwinings propagate through every finite word.

**Theorem 1.23 (car).**

$$\forall i \in Nat,\; \forall j \in Nat,\; \forall a \in Bool,\; \forall b \in Bool,\; \operatorname{mode}\left(i, a\right) \cdot \operatorname{mode}\left(j, b\right) + \operatorname{mode}\left(j, b\right) \cdot \operatorname{mode}\left(i, a\right) = \operatorname{ite}\left(i = j \land a \ne b, (1:\operatorname{Module}.\operatorname{End}\left(Complex, Fock\right)), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.car` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite state and the two chosen indices fit in one prefix. Word transport consumes the finite CAR, including the equal-site nilpotence supplied by the Majorana relations.

**Theorem 1.24 (annihilate vacuum).**

$$\forall j \in Nat,\; \operatorname{annihilate}\left(j, vacuum\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.annihilate_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No site is occupied in the vacuum.

**Theorem 1.25 (create vacuum).**

$$\forall j \in Nat,\; \operatorname{create}\left(j, vacuum\right) = \operatorname{ket}\left(\operatorname{Finset}.\operatorname{singleton}\left(j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.create_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Insertion into the vacuum has sign one.

**Theorem 1.26 (parity involution).**

$$parity \cdot parity = (1:\operatorname{Module}.\operatorname{End}\left(Complex, Fock\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.parity_involution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Squaring the occupation sign gives the identity on every basis state.

**Theorem 1.27 (parity odd).**

$$\forall j \in Nat,\; \forall b \in Bool,\; parity \cdot \operatorname{mode}\left(j, b\right) + \operatorname{mode}\left(j, b\right) \cdot parity = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.parity_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero insertion or deletion changes the cardinality by one.

**Theorem 1.28 (creator spanning).**

$$\operatorname{Submodule}.\operatorname{span}\left(Complex, \operatorname{Set}.\operatorname{range}\left(\lambda (w:\operatorname{List}\left(Nat\right)) \mapsto \operatorname{word}\left(\operatorname{List}.\operatorname{map}\left(\lambda (j:Nat) \mapsto \operatorname{Prod}.\operatorname{mk}\left(j, true\right), w\right), vacuum\right)\right)\right) = \operatorname{Submodule}.\operatorname{top}\left(Complex, Fock\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.creator_spanning` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Insertion induction produces each occupation basis vector as a nonzero scalar multiple of a creator word. Finite linear extension spans the entire carrier.

**Theorem 1.29 (common annihilator kernel).**

$$\forall v \in Fock,\; \left(\forall j \in Nat,\; \operatorname{annihilate}\left(j, v\right) = 0\right) \Leftrightarrow \left(\exists alpha \in Complex,\; v = \operatorname{smul}\left(alpha, vacuum\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.common_annihilator_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a nonempty occupation S contains j, the coefficient of S with j deleted in annihilate j v is phase j S times the coefficient of S in v. Deletion is injective among occupations containing j, and the sign is nonzero. Thus every nonempty coefficient vanishes, while the empty coefficient supplies the unique scalar. Conversely all annihilators kill each scalar multiple of the actual vacuum.

**Theorem 1.30 (eq scalar of creator commutation).**

$$\forall A \in \operatorname{Module}.\operatorname{End}\left(Complex, Fock\right),\; \forall alpha \in Complex,\; A\left(vacuum\right) = \operatorname{smul}\left(alpha, vacuum\right) \Rightarrow \left(\left(\forall j \in Nat,\; A \cdot \operatorname{create}\left(j\right) = \operatorname{create}\left(j\right) \cdot A\right) \Rightarrow A = \operatorname{smul}\left(alpha, (1:\operatorname{Module}.\operatorname{End}\left(Complex, Fock\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CountableOccupationFock.eq_scalar_of_creator_commutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Commutation moves A through each finite creator word. Its scalar action on the vacuum therefore holds on every creator-word state, and creator_spanning with linear-map extensionality extends that same scalar to every Fock vector. No irreducibility hypothesis or finite cutoff is imposed.

This algebraic representation asserts CAR, exact cutoff transport and parity. Statewise quadratic normal sums, the bc Virasoro anomaly, the all-state super vertex algebra, graded tensor matter, BRST charge and nilpotence, cohomology, no-ghost results and the Monster, sewing, string and AdS identifications require further constructions.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.Fock`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.annihilate`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.annihilate_vacuum`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.car`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.common_annihilator_kernel`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.create`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.create_vacuum`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.creator_spanning`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.cutoff_annihilate_coherence`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.cutoff_create_coherence`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.eq_scalar_of_creator_commutation`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.finiteMode`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.finiteWord`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.finite_capture`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.jw_annihilate_intertwining`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.jw_create_intertwining`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.lowerCount`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.mode`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.parity`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.parity_involution`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.parity_odd`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.phase`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.prefixEmbed`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.prefixEmbed_injective`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.prefixExtend`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.prefix_coherence`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.vacuum`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.word`
- Truth anchor: `D5/S3/Quantum/Fermionic/CountableOccupationFock.word_intertwining`
- Dependency: [D5/S3/Quantum/Fermionic/FockMajoranaCarrier](FockMajoranaCarrier.md)
- Dependency: [D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound](../FermionicCorrelationalBound/CompletedCorrelationalBound.md)
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreCompression](../SpinChains/SupersymmetricFermion/HardCoreCompression.md)
