# Recursive skew conference matrices

## Abstract

Recursive skew conference matrices have order a power of two and flat square.

Nat and Int denote natural numbers and integers. Index(0) has two labels; each subsequent label type is the disjoint sum of two copies of the preceding type. SumType is the disjoint sum, and Matrix2x2(a,b,c,d) is the literal two-by-two matrix with first row (a,b) and second row (c,d). Matrix one is the identity matrix, smul is scalar multiplication, transpose is ordinary transpose, and asInt is the natural-to-integer cast. The function letInstance installs its first argument as a local instance in its second argument. inferInstance and inferInstanceAs denote Lean's canonical instance synthesis at the displayed type; the recursive instances use the ordinary sum-type enumeration and decidable equality.

**Definition 1.1 (Recursive labels).**

$$\begin{aligned}\mathrm{Index}\left(0\right) = \mathrm{Fin}\left(2\right)\\\forall r \in \mathit{Nat},\; \mathrm{Index}\left(r + 1\right) = \mathrm{SumType}\left(\mathrm{Index}\left(r\right), \mathrm{Index}\left(r\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Fermionic/ConferenceMatrices.Index` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equations define the recursive label type.

**Definition 1.2 (Finite enumeration).**

$$\begin{aligned}\mathrm{indexFintype}\left(0\right) = \mathrm{inferInstanceAs}\left(\mathrm{Fintype}\left(\mathrm{Fin}\left(2\right)\right)\right)\\\forall r \in \mathit{Nat},\; \mathrm{indexFintype}\left(r + 1\right) = \mathrm{letInstance}\left(\mathrm{indexFintype}\left(r\right), \mathrm{inferInstanceAs}\left(\mathrm{Fintype}\left(\mathrm{SumType}\left(\mathrm{Index}\left(r\right), \mathrm{Index}\left(r\right)\right)\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Fermionic/ConferenceMatrices.indexFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At order zero the enumeration is the finite-two enumeration. Each subsequent enumeration is the finite disjoint-sum enumeration using the preceding enumeration as a local instance.

**Definition 1.3 (Decidable equality).**

$$\begin{aligned}\mathrm{indexDecidableEq}\left(0\right) = \mathrm{inferInstanceAs}\left(\mathrm{DecidableEq}\left(\mathrm{Fin}\left(2\right)\right)\right)\\\forall r \in \mathit{Nat},\; \mathrm{indexDecidableEq}\left(r + 1\right) = \mathrm{letInstance}\left(\mathrm{indexDecidableEq}\left(r\right), \mathrm{inferInstanceAs}\left(\mathrm{DecidableEq}\left(\mathrm{SumType}\left(\mathrm{Index}\left(r\right), \mathrm{Index}\left(r\right)\right)\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Fermionic/ConferenceMatrices.indexDecidableEq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At order zero equality is finite-two equality. At every subsequent order equality is disjoint-sum equality using the preceding equality instance.

**Definition 1.4 (Matrix recursion).**

$$\begin{aligned}\mathrm{conference}\left(0\right) = \mathrm{Matrix2x2}\left(0, 1, -(1), 0\right)\\\forall r \in \mathit{Nat},\; \mathrm{conference}\left(r + 1\right) = \mathrm{fromBlocks}\left(\mathrm{conference}\left(r\right), \mathrm{conference}\left(r\right) + (1:\mathrm{Matrix}\left(\mathrm{Index}\left(r\right), \mathrm{Index}\left(r\right), \mathit{Int}\right)), \mathrm{conference}\left(r\right) - (1:\mathrm{Matrix}\left(\mathrm{Index}\left(r\right), \mathrm{Index}\left(r\right), \mathit{Int}\right)), -(\mathrm{conference}\left(r\right))\right)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Fermionic/ConferenceMatrices.conference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four blocks at each doubling are C, C+I, C-I and -C, in that order. All entries are integers.

**Theorem 1.5 (Order, skewness, signs and square).**

$$\forall r \in \mathit{Nat},\; (\mathrm{card}\left(\mathrm{Index}\left(r\right)\right) = 2^{(r + 1)})\land(\mathrm{transpose}\left(\mathrm{conference}\left(r\right)\right) = -(\mathrm{conference}\left(r\right)))\land(\forall i \in \mathrm{Index}\left(r\right),\; \mathrm{val}\left(\mathrm{conference}\left(r\right), i, i\right) = 0)\land(\forall i \in \mathrm{Index}\left(r\right),\; \forall j \in \mathrm{Index}\left(r\right),\; (i \ne j) \Rightarrow ((\mathrm{val}\left(\mathrm{conference}\left(r\right), i, j\right) = 1) \lor (\mathrm{val}\left(\mathrm{conference}\left(r\right), i, j\right) = -(1))))\land(\mathrm{conference}\left(r\right) \cdot \mathrm{conference}\left(r\right) = \mathrm{smul}\left(-(\mathrm{asInt}\left(\mathrm{card}\left(\mathrm{Index}\left(r\right)\right)\right) - 1), (1:\mathrm{Matrix}\left(\mathrm{Index}\left(r\right), \mathrm{Index}\left(r\right), \mathit{Int}\right))\right))$$

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
