# Unary and Reverse-Unary Native Insertion

## Abstract

Gap masses identify native unary insertion minima in both ordered orientations.

Words and masks use the original ordered source schedule: the first source is inserted and the second is the base. The degree is the minimum number of maximal nonempty first-source runs over all actual masks, with infinity for an invalid output. Neither source roles nor minimum semantics are exchanged when passing to the reverse-unary case.

The inserted-unary gap, degree and spectrum arguments use Hughes arXiv v2, Section 11, Theorem 9: https://arxiv.org/abs/2608.27755v2. The reverse-unary and universal minimum-mask exchange statements are separate arguments.

**Definition 1.1 (Occupied extra gaps).**

$$\forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \operatorname{occupied}\left(e\right) = \operatorname{countPositive}\left(e\right)$$

*Formalization.* `D5/S1/Words/HughesUnaryInsertion.occupied` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count strictly positive extra masses; a positive original gap with zero extra mass is unoccupied. Both outer gaps are included in this count.

**Definition 1.2 (Occupied internal extra gaps).**

$$\forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \operatorname{internalOccupied}\left(e\right) = \operatorname{occupied}\left(\operatorname{dropLast}\left(\operatorname{tail}\left(e\right)\right)\right)$$

*Formalization.* `D5/S1/Words/HughesUnaryInsertion.internalOccupied` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Discard the initial and terminal gap before counting. For zero or one non-a occurrences there are no internal gaps.

**Definition 1.3 (Actual native shuffles).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall u \in \operatorname{List}\left(alpha\right),\; \forall v \in \operatorname{List}\left(alpha\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; w \in \operatorname{Sh}\left(u, v\right) \Leftrightarrow \left(\exists M \in \operatorname{List}\left(Side\right),\; \operatorname{ValidMask}\left(u, v, w, M\right)\right)$$

*Formalization.* `D5/S1/Words/HughesUnaryInsertion.Sh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Membership means an actual positional mask evaluates to the word and consumes both original sources. No separate ordinary-shuffle identification is used.

**Definition 1.4 (Attained natural degrees).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall u \in \operatorname{List}\left(alpha\right),\; \forall v \in \operatorname{List}\left(alpha\right),\; \forall r \in \operatorname{Nat}\left(\right),\; r \in \operatorname{spectrum}\left(u, v\right) \Leftrightarrow \left(\exists w \in \operatorname{List}\left(alpha\right),\; w \in \operatorname{Sh}\left(u, v\right) \land \operatorname{degree}\left(u, v, w\right) = r\right)$$

*Formalization.* `D5/S1/Words/HughesUnaryInsertion.spectrum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A natural value occurs only through an actual shuffle output with that native minimum; infinity contributes no natural spectrum value.

**Theorem 1.5 (Inserted-unary unique gap masses).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall m \in \operatorname{Nat}\left(\right),\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; \left(\left(\forall c \in alpha,\; c \in cs \Rightarrow c \ne a\right) \land \operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1\right) \Rightarrow \left(w \in \operatorname{Sh}\left(\operatorname{replicate}\left(m, a\right), \operatorname{gap}\left(a, cs, h\right)\right) \Leftrightarrow \left(\exists e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\operatorname{length}\left(e\right) = \operatorname{length}\left(h\right) \land \left(\operatorname{sum}\left(e\right) = m \land w = \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, e\right)\right)\right)\right) \land \left(\forall f \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\operatorname{length}\left(f\right) = \operatorname{length}\left(h\right) \land \left(\operatorname{sum}\left(f\right) = m \land w = \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, f\right)\right)\right)\right) \Rightarrow f = e\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesUnaryInsertion.inserted_gap_iff` (`✓ std3`). ∎

*Citation.* Charles E. Hughes (2026). *Undecidability of Adjacent Equality for Insertion, Shuffle, and Crossover Language Operations*. URL: <https://arxiv.org/abs/2608.27755v1>.

*Commentary.*

Non-a occurrences are forced to the base source. Every output has a unique nonnegative extra vector of total inserted length, and every such vector has a full native mask. Repeated separator letters remain indexed occurrences.

**Theorem 1.6 (Reverse-unary unique gap masses).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall m \in \operatorname{Nat}\left(\right),\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; \left(\left(\forall c \in alpha,\; c \in cs \Rightarrow c \ne a\right) \land \operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1\right) \Rightarrow \left(w \in \operatorname{Sh}\left(\operatorname{gap}\left(a, cs, h\right), \operatorname{replicate}\left(m, a\right)\right) \Leftrightarrow \left(\exists e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\operatorname{length}\left(e\right) = \operatorname{length}\left(h\right) \land \left(\operatorname{sum}\left(e\right) = m \land w = \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, e\right)\right)\right)\right) \land \left(\forall f \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\operatorname{length}\left(f\right) = \operatorname{length}\left(h\right) \land \left(\operatorname{sum}\left(f\right) = m \land w = \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, f\right)\right)\right)\right) \Rightarrow f = e\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesUnaryInsertion.reverse_gap_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here non-a occurrences are forced to the inserted source. The same concatenation description retains all base mass, including both outer gaps.

**Theorem 1.7 (Inserted-unary minimum and attainment).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall m \in \operatorname{Nat}\left(\right),\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\left(\forall c \in alpha,\; c \in cs \Rightarrow c \ne a\right) \land \left(\operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1 \land \left(\operatorname{length}\left(e\right) = \operatorname{length}\left(h\right) \land \operatorname{sum}\left(e\right) = m\right)\right)\right) \Rightarrow \left(\operatorname{IsMinimumMask}\left(\operatorname{replicate}\left(m, a\right), \operatorname{gap}\left(a, cs, h\right), \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, e\right)\right), \operatorname{grouped}\left(second, cs, h, e\right), \operatorname{occupied}\left(e\right)\right) \land \operatorname{degree}\left(\operatorname{replicate}\left(m, a\right), \operatorname{gap}\left(a, cs, h\right), \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, e\right)\right)\right) = \operatorname{occupied}\left(e\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesUnaryInsertion.inserted_degree` (`✓ std3`). ∎

*Citation.* Charles E. Hughes (2026). *Undecidability of Adjacent Equality for Insertion, Shuffle, and Crossover Language Operations*. URL: <https://arxiv.org/abs/2608.27755v1>.

*Commentary.*

Each occupied gap needs an inserted run because non-a letters separate gaps. The grouped mask puts each gap's inserted letters together, reaches exactly that number of runs, and preserves both projections. This formalizes the occupied-gap proof of Hughes arXiv v2, Theorem 9, for arbitrary alphabets. For positive inserted length its convention agrees with native U-run degree; when that length is zero the native count is zero.

**Theorem 1.8 (Reverse-unary internal minimum and attainment).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall m \in \operatorname{Nat}\left(\right),\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\left(\left(\forall c \in alpha,\; c \in cs \Rightarrow c \ne a\right) \land \left(\operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1 \land \left(\operatorname{length}\left(e\right) = \operatorname{length}\left(h\right) \land \operatorname{sum}\left(e\right) = m\right)\right)\right) \land cs \ne nil\right) \Rightarrow \left(\operatorname{IsMinimumMask}\left(\operatorname{gap}\left(a, cs, h\right), \operatorname{replicate}\left(m, a\right), \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, e\right)\right), \operatorname{grouped}\left(first, cs, h, e\right), 1 + \operatorname{internalOccupied}\left(e\right)\right) \land \operatorname{degree}\left(\operatorname{gap}\left(a, cs, h\right), \operatorname{replicate}\left(m, a\right), \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, e\right)\right)\right) = 1 + \operatorname{internalOccupied}\left(e\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesUnaryInsertion.reverse_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With at least one non-a occurrence, every occupied internal gap separates forced inserted-source groups. The grouped construction places outer base material outside those groups, so the count is one plus occupied internal gaps. Original a copies in every gap remain part of the inserted projection.

**Theorem 1.9 (Reverse-unary boundary cases).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall m \in \operatorname{Nat}\left(\right),\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\left(\left(\forall c \in alpha,\; c \in cs \Rightarrow c \ne a\right) \land \left(\operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1 \land \left(\operatorname{length}\left(e\right) = \operatorname{length}\left(h\right) \land \operatorname{sum}\left(e\right) = m\right)\right)\right) \land \operatorname{gap}\left(a, cs, h\right) \ne nil\right) \Rightarrow \operatorname{degree}\left(\operatorname{gap}\left(a, cs, h\right), \operatorname{replicate}\left(m, a\right), \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, e\right)\right)\right) = \operatorname{ite}\left(cs = nil, 1, 1 + \operatorname{internalOccupied}\left(e\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesUnaryInsertion.reverse_degree_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For no non-a occurrences, nonemptiness of the inserted source forces a positive unary length and the degree is one. With a single non-a occurrence there are no internal gaps, again giving degree one regardless of both outer extra masses. Both statements use the same actual source projections.

**Theorem 1.10 (Every-mask inserted lower bound).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; \forall M \in \operatorname{List}\left(Side\right),\; \operatorname{Trace}\left(a, second, cs, h, e, w, M\right) \Rightarrow \operatorname{occupied}\left(e\right) \le \operatorname{rho}\left(M\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesUnaryInsertion.inserted_trace_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Non-a base occurrences separate the label lists of successive gaps. Each positive first-source count contributes at least one maximal U-run.

**Theorem 1.11 (Every-mask reverse lower bound).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; \forall M \in \operatorname{List}\left(Side\right),\; \left(\operatorname{Trace}\left(a, first, cs, h, e, w, M\right) \land cs \ne nil\right) \Rightarrow 1 + \operatorname{internalOccupied}\left(e\right) \le \operatorname{rho}\left(M\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesUnaryInsertion.reverse_trace_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first non-a occurrence forces an initial U-group. Every positive internal base count forces a further separator; exterior counts add none.

**Theorem 1.12 (Full inserted-unary spectrum).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall m \in \operatorname{Nat}\left(\right),\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\left(\forall c \in alpha,\; c \in cs \Rightarrow c \ne a\right) \land \left(\operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1 \land 1 \le m\right)\right) \Rightarrow \left(\forall r \in \operatorname{Nat}\left(\right),\; r \in \operatorname{spectrum}\left(\operatorname{replicate}\left(m, a\right), \operatorname{gap}\left(a, cs, h\right)\right) \Leftrightarrow \left(1 \le r \land r \le \operatorname{min}\left(m, \operatorname{length}\left(cs\right) + 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesUnaryInsertion.inserted_spectrum` (`✓ std3`). ∎

*Citation.* Charles E. Hughes (2026). *Undecidability of Adjacent Equality for Insertion, Shuffle, and Crossover Language Operations*. URL: <https://arxiv.org/abs/2608.27755v1>.

*Commentary.*

The spectrum is every integer from one to min(m, length(cs)+1), for m>0. Support is bounded by both total mass and gap count. To attain r, put one unit in r-1 gaps, the remaining positive mass in one gap, and zero elsewhere.

**Theorem 1.13 (Full reverse-unary spectrum).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall m \in \operatorname{Nat}\left(\right),\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\left(\forall c \in alpha,\; c \in cs \Rightarrow c \ne a\right) \land \left(\operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1 \land \operatorname{gap}\left(a, cs, h\right) \ne nil\right)\right) \Rightarrow \left(\forall r \in \operatorname{Nat}\left(\right),\; r \in \operatorname{spectrum}\left(\operatorname{gap}\left(a, cs, h\right), \operatorname{replicate}\left(m, a\right)\right) \Leftrightarrow \left(1 \le r \land r \le 1 + \operatorname{min}\left(m, \operatorname{NatSub}\left(\operatorname{length}\left(cs\right), 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesUnaryInsertion.reverse_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty inserted source the spectrum is every integer from one to 1+min(n, length(cs)-1), with truncated subtraction. Put one unit in each chosen internal gap and all remaining mass at an exterior end. For no non-a occurrences the only value is one.

**Definition 1.14 (Equality in every inserted gap).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; \forall M \in \operatorname{List}\left(Side\right),\; \operatorname{InsertedTight}\left(a, cs, h, e, w, M\right) : \operatorname{Prop}\left(\right)$$

*Formalization.* `D5/S1/Words/HughesUnaryInsertion.InsertedTight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This positional trace requires rho(b)=1 in each gap whose inserted count is positive, and rho(b)=0 otherwise. All non-a occurrences have label V. Thus each occupied indexed gap has exactly one whole U-run.

**Definition 1.15 (Internal and terminal equality).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; \forall M \in \operatorname{List}\left(Side\right),\; \operatorname{ReverseTailTight}\left(a, cs, h, e, w, M\right) : \operatorname{Prop}\left(\right)$$

*Formalization.* `D5/S1/Words/HughesUnaryInsertion.ReverseTailTight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An internal label gap has the form U^x V^e U^z, with all its base mass e in that single V-block. The terminal gap has form U^x V^y. The internal restart cost is one exactly when e>0, and the terminal restart cost is zero.

**Definition 1.16 (Full reverse minimum structure).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; \forall M \in \operatorname{List}\left(Side\right),\; \operatorname{ReverseTight}\left(a, cs, h, e, w, M\right) : \operatorname{Prop}\left(\right)$$

*Formalization.* `D5/S1/Words/HughesUnaryInsertion.ReverseTight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial gap is V^x U^y followed by its forced non-a U occurrence, and the remaining trace has the internal and terminal forms above. Every U segment attaches to a bounding non-a occurrence; there is no additional all-a U-run. Outer base material is retained in its actual position.

**Theorem 1.17 (Every inserted-unary minimum mask).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall m \in \operatorname{Nat}\left(\right),\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; \forall M \in \operatorname{List}\left(Side\right),\; \forall r \in \operatorname{Nat}\left(\right),\; \left(\left(\left(\forall c \in alpha,\; c \in cs \Rightarrow c \ne a\right) \land \left(\operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1 \land \left(\operatorname{length}\left(e\right) = \operatorname{length}\left(h\right) \land \operatorname{sum}\left(e\right) = m\right)\right)\right) \land \left(w = \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, e\right)\right) \land \operatorname{IsMinimumMask}\left(\operatorname{replicate}\left(m, a\right), \operatorname{gap}\left(a, cs, h\right), w, M, r\right)\right)\right) \Rightarrow \operatorname{InsertedTight}\left(a, cs, h, e, w, M\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesUnaryInsertion.inserted_minimum_shape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Comparison with the grouped attaining mask forces equality in each individual gap lower bound, for every minimum mask of the output.

**Theorem 1.18 (Every reverse-unary minimum mask).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall m \in \operatorname{Nat}\left(\right),\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; \forall M \in \operatorname{List}\left(Side\right),\; \forall r \in \operatorname{Nat}\left(\right),\; \left(\left(\left(\left(\forall c \in alpha,\; c \in cs \Rightarrow c \ne a\right) \land \left(\operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1 \land \left(\operatorname{length}\left(e\right) = \operatorname{length}\left(h\right) \land \operatorname{sum}\left(e\right) = m\right)\right)\right) \land cs \ne nil\right) \land \left(w = \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, e\right)\right) \land \operatorname{IsMinimumMask}\left(\operatorname{gap}\left(a, cs, h\right), \operatorname{replicate}\left(m, a\right), w, M, r\right)\right)\right) \Rightarrow \operatorname{ReverseTight}\left(a, cs, h, e, w, M\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesUnaryInsertion.reverse_minimum_shape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With at least one non-a occurrence, equality forces the initial cost one and every internal and terminal cost to be tight. The binary label classification proves the displayed pure-block forms for every minimum mask.

**Theorem 1.19 (Spectra of arbitrary actual source words).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall m \in \operatorname{Nat}\left(\right),\; \forall n \in \operatorname{Nat}\left(\right),\; \forall u \in \operatorname{List}\left(alpha\right),\; \forall v \in \operatorname{List}\left(alpha\right),\; \left(u \ne nil \land \left(v \ne nil \land \left(1 \le m \land 1 \le n\right)\right)\right) \Rightarrow \left(\left(\forall r \in \operatorname{Nat}\left(\right),\; r \in \operatorname{spectrum}\left(\operatorname{replicate}\left(m, a\right), v\right) \Leftrightarrow \left(1 \le r \land r \le \operatorname{min}\left(m, \operatorname{length}\left(\operatorname{spine}\left(a, v\right)\right) + 1\right)\right)\right) \land \left(\forall r \in \operatorname{Nat}\left(\right),\; r \in \operatorname{spectrum}\left(u, \operatorname{replicate}\left(n, a\right)\right) \Leftrightarrow \left(1 \le r \land r \le 1 + \operatorname{min}\left(n, \operatorname{length}\left(\operatorname{spine}\left(a, u\right)\right) - 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesUnaryInsertion.spectra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary nonempty u,v and positive m,n, let s_a(x) be the number of non-a occurrences of the actual word x, counting repetitions. Then D(a^m,v)={r: 1<=r<=min(m,s_a(v)+1)} and D(u,a^n)={r: 1<=r<=1+min(n,s_a(u)-1)}. The occurrence count is recovered from the canonical presentation of each actual source word.

## References

- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.InsertedTight`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.ReverseTailTight`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.ReverseTight`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.Sh`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.inserted_degree`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.inserted_gap_iff`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.inserted_minimum_shape`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.inserted_spectrum`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.inserted_trace_lower`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.internalOccupied`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.occupied`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.reverse_degree`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.reverse_degree_all`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.reverse_gap_iff`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.reverse_minimum_shape`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.reverse_spectrum`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.reverse_trace_lower`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.spectra`
- Truth anchor: `D5/S1/Words/HughesUnaryInsertion.spectrum`
- Dependency: [D5/S1/Words/UnaryGapWords](UnaryGapWords.md)
