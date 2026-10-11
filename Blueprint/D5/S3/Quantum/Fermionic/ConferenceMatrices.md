# Recursive skew conference matrices

## Abstract

Recursive skew conference matrices have order a power of two and flat square.

Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.

**Definition 1.1 (Recursive labels).**

$$\begin{aligned}\mathrm{Index}\left(0\right) = \mathrm{Fin}\left(2\right)\\\forall r \in \mathit{Nat},\; \mathrm{Index}\left(r + 1\right) = \operatorname{Sum}\left(\mathrm{Index}\left(r\right), \mathrm{Index}\left(r\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Fermionic/ConferenceMatrices.Index` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equations define the recursive label type.

**Definition 1.2 (Finite enumeration).**

$$\begin{aligned}\mathrm{indexFintype}\left(0\right) = \mathrm{inferInstanceAs}\left(\mathrm{Fintype}\left(\mathrm{Fin}\left(2\right)\right)\right)\\\forall r \in \mathit{Nat},\; \mathrm{indexFintype}\left(r + 1\right) = letI := \mathrm{indexFintype}\left(r\right); \mathrm{inferInstanceAs}\left(\mathrm{Fintype}\left(\operatorname{Sum}\left(\mathrm{Index}\left(r\right), \mathrm{Index}\left(r\right)\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Fermionic/ConferenceMatrices.indexFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At order zero the enumeration is the finite-two enumeration. Each subsequent enumeration is the finite disjoint-sum enumeration using the preceding enumeration as a local instance.

**Definition 1.3 (Decidable equality).**

$$\begin{aligned}\mathrm{indexDecidableEq}\left(0\right) = \mathrm{inferInstanceAs}\left(\mathrm{DecidableEq}\left(\mathrm{Fin}\left(2\right)\right)\right)\\\forall r \in \mathit{Nat},\; \mathrm{indexDecidableEq}\left(r + 1\right) = letI := \mathrm{indexDecidableEq}\left(r\right); \mathrm{inferInstanceAs}\left(\mathrm{DecidableEq}\left(\operatorname{Sum}\left(\mathrm{Index}\left(r\right), \mathrm{Index}\left(r\right)\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Fermionic/ConferenceMatrices.indexDecidableEq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At order zero equality is finite-two equality. At every subsequent order equality is disjoint-sum equality using the preceding equality instance.

**Definition 1.4 (Matrix recursion).**

$$\begin{aligned}\mathrm{conference}\left(0\right) = !![0,1;-(1),0]\\\forall r \in \mathit{Nat},\; \mathrm{conference}\left(r + 1\right) = \operatorname{Matrix}.\operatorname{fromBlocks}\left(\mathrm{conference}\left(r\right), \mathrm{conference}\left(r\right) + (1:\mathrm{Matrix}\left(\mathrm{Index}\left(r\right), \mathrm{Index}\left(r\right), \mathit{Int}\right)), \mathrm{conference}\left(r\right) - (1:\mathrm{Matrix}\left(\mathrm{Index}\left(r\right), \mathrm{Index}\left(r\right), \mathit{Int}\right)), -(\mathrm{conference}\left(r\right))\right)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Fermionic/ConferenceMatrices.conference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four blocks at each doubling are C, C+I, C-I and -C, in that order. All entries are integers.

**Theorem 1.5 (Order, skewness, signs and square).**

$$\forall r \in \mathit{Nat},\; (\operatorname{Fintype}.\operatorname{card}\left(\mathrm{Index}\left(r\right)\right) = 2^{(r + 1)})\land(\operatorname{Matrix}.\operatorname{transpose}\left(\mathrm{conference}\left(r\right)\right) = -(\mathrm{conference}\left(r\right)))\land(\forall i \in \mathrm{Index}\left(r\right),\; \mathrm{val}\left(\mathrm{conference}\left(r\right), i, i\right) = 0)\land(\forall i \in \mathrm{Index}\left(r\right),\; \forall j \in \mathrm{Index}\left(r\right),\; (i \ne j) \Rightarrow ((\mathrm{val}\left(\mathrm{conference}\left(r\right), i, j\right) = 1) \lor (\mathrm{val}\left(\mathrm{conference}\left(r\right), i, j\right) = -(1))))\land(\mathrm{conference}\left(r\right) \cdot \mathrm{conference}\left(r\right) = \operatorname{SMul}.\operatorname{smul}\left(-((\operatorname{Fintype}.\operatorname{card}\left(\mathrm{Index}\left(r\right)\right):\mathit{Int}) - 1), (1:\mathrm{Matrix}\left(\mathrm{Index}\left(r\right), \mathrm{Index}\left(r\right), \mathit{Int}\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/ConferenceMatrices.conference_properties` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recursive family has order 2^(r+1), zero diagonal and signed off-diagonal entries. Its square is minus the order minus one times the identity. Induction on the doubling step preserves the four-block multiplication identity as well as the signed-entry conditions.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/ConferenceMatrices.Index`
- Truth anchor: `D5/S3/Quantum/Fermionic/ConferenceMatrices.conference`
- Truth anchor: `D5/S3/Quantum/Fermionic/ConferenceMatrices.conference_properties`
- Truth anchor: `D5/S3/Quantum/Fermionic/ConferenceMatrices.indexDecidableEq`
- Truth anchor: `D5/S3/Quantum/Fermionic/ConferenceMatrices.indexFintype`
