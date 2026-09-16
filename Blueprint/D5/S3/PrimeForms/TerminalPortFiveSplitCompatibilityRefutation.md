# A Terminal-Port Five-Split Compatibility Counterexample

## Abstract

The terminal port (14,3,5) has nonzero local solutions at every prime but no five-point of distinct primes above 5, refuting an abstracted joint compatibility consequence of the cited five-splitting setup.

The cited source separates a five-splitting prime-points hypothesis from its finite-local and positive-real-component inputs. The formal claim below existentially abstracts the real-side input as a predicate A and combines it with the local input. This is a repository-derived joint consequence, not a published statement quoted verbatim.

**Definition 1.1 (Terminal port).**

$$\forall R \in \mathrm{Nat}, c \in \mathrm{Nat}, p \in \mathrm{Nat},\; (\operatorname{Terminal}\left(R, c, p\right)) \Leftrightarrow ((0 < R) \land \left((0 < c) \land \left((\operatorname{Prime}\left(p\right)) \land (c \cdot p = R + 1)\right)\right))$$

*Formalization.* `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.Terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Han Wang (2026). *Port Fillings for Primary Pseudoperfect Numbers*. DOI: [10.48550/arXiv.2605.21518](https://doi.org/10.48550/arXiv.2605.21518). URL: <https://arxiv.org/html/2605.21518v1#S19>.

*Commentary.*

Terminal(R,c,p) requires positive natural R and c, a prime p, and c*p=R+1. The equality is the natural-number form of c*p-R=1; positivity prevents a truncated-subtraction reading from adding degenerate cases.

**Definition 1.2 (Five-split integer form).**

$$\forall R \in \mathrm{Nat}, c \in \mathrm{Nat}, x \in \operatorname{Fin}\left(5\right) \to \mathrm{Nat},\; \operatorname{form}\left(R, c, x\right) = \operatorname{IntCast}\left(c\right) \cdot \prod_{i \in \operatorname{Fin}\left(5\right)} \operatorname{IntCast}\left(x\left(i\right)\right) - \operatorname{IntCast}\left(R\right) \cdot \sum_{i \in \operatorname{Fin}\left(5\right)} \prod_{j \in \operatorname{Fin}\left(5\right), j \neq i} \operatorname{IntCast}\left(x\left(j\right)\right) - 1$$

*Formalization.* `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.form` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Han Wang (2026). *Port Fillings for Primary Pseudoperfect Numbers*. DOI: [10.48550/arXiv.2605.21518](https://doi.org/10.48550/arXiv.2605.21518). URL: <https://arxiv.org/html/2605.21518v1#S19>.

*Commentary.*

The value of form(R,c,x) lies in Int. Every subtraction displayed here is integer subtraction: first R times the sum of the five complementary fourfold products is subtracted from c times the fivefold product, and then 1 is subtracted.

**Definition 1.3 (Nonzero local solutions at every prime).**

$$\forall R \in \mathrm{Nat}, c \in \mathrm{Nat},\; (\operatorname{localUnits}\left(R, c\right)) \Leftrightarrow (\forall ell \in \mathrm{Nat},\; (\operatorname{Prime}\left(ell\right)) \Rightarrow (\exists x \in \operatorname{Fin}\left(5\right) \to \operatorname{ZMod}\left(ell\right),\; (\forall i \in \operatorname{Fin}\left(5\right),\; x\left(i\right) \ne \operatorname{ZModCast}\left(0, ell\right)) \land (\operatorname{ZModCast}\left(c, ell\right) \cdot \prod_{i \in \operatorname{Fin}\left(5\right)} x\left(i\right) - \operatorname{ZModCast}\left(R, ell\right) \cdot \sum_{i \in \operatorname{Fin}\left(5\right)} \prod_{j \in \operatorname{Fin}\left(5\right), j \neq i} x\left(j\right) - \operatorname{ZModCast}\left(1, ell\right) = \operatorname{ZModCast}\left(0, ell\right))))$$

*Formalization.* `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.localUnits` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Han Wang (2026). *Port Fillings for Primary Pseudoperfect Numbers*. DOI: [10.48550/arXiv.2605.21518](https://doi.org/10.48550/arXiv.2605.21518). URL: <https://arxiv.org/html/2605.21518v1#S19>.

*Commentary.*

For each prime ell there is a five-tuple in ZMod(ell), every coordinate nonzero, satisfying the residue-field form equation. The subtraction in this formula is ZMod(ell) subtraction, not natural subtraction.

**Definition 1.4 (Five distinct prime coordinates above the terminal prime).**

$$\forall R \in \mathrm{Nat}, c \in \mathrm{Nat}, p \in \mathrm{Nat},\; (\operatorname{primePoint}\left(R, c, p\right)) \Leftrightarrow (\exists x \in \operatorname{Fin}\left(5\right) \to \mathrm{Nat},\; (\forall i \in \operatorname{Fin}\left(5\right),\; (\operatorname{Prime}\left(x\left(i\right)\right)) \land (p < x\left(i\right))) \land \left((\forall i \in \operatorname{Fin}\left(5\right), j \in \operatorname{Fin}\left(5\right),\; (i \ne j) \Rightarrow (x\left(i\right) \ne x\left(j\right))) \land (\operatorname{form}\left(R, c, x\right) = 0)\right))$$

*Formalization.* `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.primePoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Han Wang (2026). *Port Fillings for Primary Pseudoperfect Numbers*. DOI: [10.48550/arXiv.2605.21518](https://doi.org/10.48550/arXiv.2605.21518). URL: <https://arxiv.org/html/2605.21518v1#S19>.

*Commentary.*

A prime point is a natural five-tuple whose coordinates are prime, strictly greater than p, pairwise distinct, and annihilate the integer form.

**Definition 1.5 (Abstracted joint compatibility claim).**

$$(claim) \Leftrightarrow (\exists A \in \mathrm{Nat} \to \left(\mathrm{Nat} \to \left(\mathrm{Nat} \to \mathrm{Prop}\right)\right),\; \forall R \in \mathrm{Nat}, c \in \mathrm{Nat}, p \in \mathrm{Nat},\; (\operatorname{Terminal}\left(R, c, p\right)) \Rightarrow \left((4 < R) \Rightarrow \left((3 < p) \Rightarrow ((A\left(R, c, p\right)) \land ((A\left(R, c, p\right)) \Rightarrow \left((\operatorname{localUnits}\left(R, c\right)) \Rightarrow (\operatorname{primePoint}\left(R, c, p\right))\right)))\right)\right))$$

*Formalization.* `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Han Wang (2026). *Port Fillings for Primary Pseudoperfect Numbers*. DOI: [10.48550/arXiv.2605.21518](https://doi.org/10.48550/arXiv.2605.21518). URL: <https://arxiv.org/html/2605.21518v1#S19>.

*Commentary.*

The quantified witness A has the full type Nat -> Nat -> Nat -> Prop. It must exist before the universal R,c,p quantifiers, must hold for every terminal port with R>4 and p>3, and together with local unit solubility must imply a five-prime point. No ambient-port premise is present in this formal claim.

**Definition 1.6 (Complementary-product list recurrence).**

$$\begin{aligned}\operatorname{deriv}\left([]\right) = 0\\\forall q \in \mathrm{Nat}, xs \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{deriv}\left(q :: xs\right) = \operatorname{prod}\left(xs\right) + q \cdot \operatorname{deriv}\left(xs\right)\end{aligned}$$

*Formalization.* `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.deriv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Han Wang (2026). *Port Fillings for Primary Pseudoperfect Numbers*. DOI: [10.48550/arXiv.2605.21518](https://doi.org/10.48550/arXiv.2605.21518). URL: <https://arxiv.org/html/2605.21518v1#S19>.

*Commentary.*

The empty list has derivative 0. For q::xs, the recurrence adds the product of xs to q times the derivative of xs; for a five-entry list this is the sum of its five complementary fourfold products.

**Definition 1.7 (Natural balance equation).**

$$\forall R \in \mathrm{Nat}, C \in \mathrm{Nat}, xs \in \operatorname{List}\left(\mathrm{Nat}\right),\; (\operatorname{Balance}\left(R, C, xs\right)) \Leftrightarrow (C \cdot \operatorname{prod}\left(xs\right) = R \cdot \operatorname{deriv}\left(xs\right) + 1)$$

*Formalization.* `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.Balance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Han Wang (2026). *Port Fillings for Primary Pseudoperfect Numbers*. DOI: [10.48550/arXiv.2605.21518](https://doi.org/10.48550/arXiv.2605.21518). URL: <https://arxiv.org/html/2605.21518v1#S19>.

*Commentary.*

Balance(R,C,xs) is the natural equality C*prod(xs)=R*deriv(xs)+1. It is the positive equality used to turn a zero of the integer form into the recursive search invariant.

**Definition 1.8 (Bounded natural search).**

$$\begin{aligned}\forall R \in \mathrm{Nat}, C \in \mathrm{Nat}, lo \in \mathrm{Nat},\; \operatorname{search}\left(0, R, C, lo\right) = \mathrm{false}\\\forall R \in \mathrm{Nat}, C \in \mathrm{Nat}, lo \in \mathrm{Nat},\; (\operatorname{search}\left(1, R, C, lo\right) = \mathrm{true}) \Leftrightarrow ((C \ne 0) \land \left((lo < \operatorname{NatDiv}\left(R + 1, C\right)) \land (C \cdot \operatorname{NatDiv}\left(R + 1, C\right) = R + 1)\right))\\\forall n \in \mathrm{Nat}, R \in \mathrm{Nat}, C \in \mathrm{Nat}, lo \in \mathrm{Nat},\; (\operatorname{search}\left(n + 2, R, C, lo\right) = \mathrm{true}) \Leftrightarrow ((C \ne 0) \land (\exists q \in \mathrm{Nat},\; (q < \operatorname{NatDiv}\left(\left(n + 2\right) \cdot R, C\right) + 1) \land \left((lo < q) \land \left(((n = 0) \lor (\operatorname{Prime}\left(q\right))) \land \left((\operatorname{NatMod}\left(R, q\right) \ne 0) \land \left((R < C \cdot q) \land (\operatorname{search}\left(n + 1, R \cdot q, \operatorname{NatSub}\left(C \cdot q, R\right), q\right) = \mathrm{true})\right)\right)\right)\right)))\end{aligned}$$

*Formalization.* `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.search` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Han Wang (2026). *Port Fillings for Primary Pseudoperfect Numbers*. DOI: [10.48550/arXiv.2605.21518](https://doi.org/10.48550/arXiv.2605.21518). URL: <https://arxiv.org/html/2605.21518v1#S19>.

*Commentary.*

The recurrence uses NatDiv, NatMod, and NatSub throughout. NatSub(C*q,R) denotes the truncated natural subtraction in the definition; the proof establishes R<C*q before following every valid branch, so truncation does not alter a branch invariant. At a two-entry state the test n=0 makes the current primality check vacuous, and the one-entry case computes its final coordinate without a primality check. Thus the last two search levels deliberately relax primality, while search completeness still includes every actual sorted five-tuple of primes.

**Theorem 1.9 (The abstracted joint compatibility claim is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Han Wang (2026). *Port Fillings for Primary Pseudoperfect Numbers*. DOI: [10.48550/arXiv.2605.21518](https://doi.org/10.48550/arXiv.2605.21518). URL: <https://arxiv.org/html/2605.21518v1#S19>.

*Commentary.*

The witness (R,c,p)=(14,3,5) is terminal and satisfies R>4 and p>3. For every prime ell other than 5, the proof uses the nonzero residue tuple (5,1,-1,1,-1); at ell=5 it uses (1,1,-1,3,2). The completeness argument sorts any hypothetical five distinct prime coordinates above 5 into the natural recurrence, while kernel evaluation gives search(5,14,3,5)=false. Hence no such prime tuple exists.

This terminal witness is nonambient in the cited source's sense. Evaluating squarefreeDeriv(14) from `D5/S3/PrimeForms/PrimaryPseudoperfectPorts` gives 9, so 14-squarefreeDeriv(14)=5 rather than c=3. Accordingly, the theorem does not refute Hypothesis 19.2 for ambient terminal ports, does not refute an ambient-only method, and does not solve Erdos problem 313.

## References

- Truth anchor: `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.Balance`
- Truth anchor: `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.Terminal`
- Truth anchor: `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.claim`
- Truth anchor: `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.deriv`
- Truth anchor: `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.form`
- Truth anchor: `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.localUnits`
- Truth anchor: `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.primePoint`
- Truth anchor: `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.result`
- Truth anchor: `D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.search`
- Narrative reference: [D5/S3/PrimeForms/PrimaryPseudoperfectPorts](PrimaryPseudoperfectPorts.md)
