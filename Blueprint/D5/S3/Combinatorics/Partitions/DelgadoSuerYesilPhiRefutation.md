# An obstruction to unrestricted symmetrization surjectivity

## Abstract

Pseudo-Frobenius row deletion omits 1 for every proper numerical semigroup, excluding a symmetric numerical set containing 1.

The final paragraph of Section 5 asks: ‘A natural question is whether Φ is surjective, that is, whether every symmetric numerical set arises as the symmetrization of some almost symmetric numerical semigroup.’ The terminal theorem refutes this unrestricted assertion. Characterizing the whole image remains a separate problem.

Delgado, Suer and Yesil associate a boundary to a proper numerical set by scanning the natural numbers from zero to its largest gap: membership gives a right step and a gap gives an up step. The gap label of a row is its first-column hook length. Their Theorem 4.2 deletes exactly the original pseudo-Frobenius rows other than the Frobenius row. The inverse correspondence reads the resulting boundary; deleted up steps shift later labels without changing retained row lengths.

**Definition 1.1 (All proper numerical sets).**

Lean statement: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.NumericalSet`

*Formalization.* `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.NumericalSet` (`✓ std3`).

*Citation.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

NumericalSet stores an arbitrary nonempty finite set of natural-number gaps with zero excluded. Its complement is therefore cofinite, contains zero and is proper. Conversely every proper numerical set has exactly such a finite gap set. The carrier imposes no additive closure and no bound on Frobenius number, genus, type, multiplicity or size.

**Definition 1.2 (Membership).**

$$\forall (U: \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet}), \forall (n: \mathbb{N}), n \in \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.members}\left(U\right) \Leftrightarrow \left(\neg n \in \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet.gaps}\left(U\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.members` (`✓ std3`).

*Citation.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

The members are exactly the naturals outside the complete finite gap set.

**Definition 1.3 (The largest gap).**

$$\forall (U: \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet}), \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.frobenius}\left(U\right) = \max\left(\operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet.gaps}\left(U\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.frobenius` (`✓ std3`).

*Citation.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

frobenius U is the maximum of the nonempty finite gap set, as a natural number. Lean uses max' with the nonemptiness proof; the improper numerical set is excluded by the carrier.

**Definition 1.4 (Unbounded additive closure).**

$$\forall (U: \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet}), \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.Semigroup}\left(U\right) \Leftrightarrow \forall (a: \mathbb{N}), \forall (b: \mathbb{N}), a \in \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.members}\left(U\right) \Rightarrow \left(b \in \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.members}\left(U\right) \Rightarrow a + b \in \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.members}\left(U\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.Semigroup` (`✓ std3`).

*Citation.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

Both summands range over all natural numbers. The numerical set is a semigroup precisely when its members are closed under addition.

**Definition 1.5 (The original pseudo-Frobenius predicate).**

$$\forall (U: \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet}), \forall (f: \mathbb{N}), \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.PseudoFrobenius}\left(U, f\right) \Leftrightarrow \left(f \in \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet.gaps}\left(U\right) \land \forall (s: \mathbb{N}), s > 0 \Rightarrow \left(s \in \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.members}\left(U\right) \Rightarrow f + s \in \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.members}\left(U\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.PseudoFrobenius` (`✓ std3`).

*Citation.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

A pseudo-Frobenius number is an original gap whose sum with every positive source member belongs to the source. This predicate is evaluated before any row is deleted.

**Definition 1.6 (Almost symmetry).**

$$\forall (U: \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet}), \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.AlmostSymmetric}\left(U\right) \Leftrightarrow \left(\operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.Semigroup}\left(U\right) \land 2 \cdot \operatorname{Finset.card}\left(\operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet.gaps}\left(U\right)\right) = \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.frobenius}\left(U\right) + \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (f: \mathbb{N}) \mapsto \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.PseudoFrobenius}\left(U, f\right), \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet.gaps}\left(U\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.AlmostSymmetric` (`✓ std3`).

*Citation.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

The genus is the cardinality of all gaps; the type is the cardinality of the pseudo-Frobenius gaps. AlmostSymmetric includes additive closure and the equality 2g = F + t.

**Definition 1.7 (Symmetry without additive closure).**

$$\forall (U: \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet}), \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.Symmetric}\left(U\right) \Leftrightarrow \forall (a: \mathbb{N}), a \le \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.frobenius}\left(U\right) \Rightarrow \left(a \in \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.members}\left(U\right) \Leftrightarrow \left(\neg \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.frobenius}\left(U\right) - a \in \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.members}\left(U\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.Symmetric` (`✓ std3`).

*Citation.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

Every natural a from zero through F is considered. Exactly one of a and F-a belongs. Subtraction agrees with integer subtraction on this interval. No semigroup condition is imposed on the target.

**Definition 1.8 (Horizontal coordinates of the full boundary).**

$$\forall (U: \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet}), \forall (r: \mathbb{N}), \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.rowLength}\left(U, r\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (a: \mathbb{N}) \mapsto a \in \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.members}\left(U\right), \operatorname{Finset.range}\left(r\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.rowLength` (`✓ std3`).

*Citation.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

For an original gap r, its row length is the number of right steps preceding its up step. The complete boundary has one row for each original gap, ordered by that gap. Counting preceding right and up steps gives rowLength(U,r) plus the number of gaps below r equal to r.

**Definition 1.9 (Precisely the retained original rows).**

$$\forall (U: \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet}), \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.retainedRows}\left(U\right) = \operatorname{Finset.filter}\left(\lambda (r: \mathbb{N}) \mapsto r = \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.frobenius}\left(U\right) \lor \left(\neg \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.PseudoFrobenius}\left(U, r\right)\right), \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet.gaps}\left(U\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.retainedRows` (`✓ std3`).

*Citation.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

Retain an original gap row exactly when its label is F or is not pseudo-Frobenius. Thus exactly PF(U) minus {F(U)} is deleted. The Frobenius row remains, and pseudo-Frobenius status is never recomputed after deletion.

**Definition 1.10 (Inverting the row boundary).**

$$\forall (R: \operatorname{Finset}\left(\mathbb{N}\right)), \forall (l: \mathbb{N} \to \mathbb{N}), \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.inverseBoundary}\left(R, l\right) = \operatorname{Finset.image}\left(\lambda (r: \mathbb{N}) \mapsto l\left(r\right) + \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (q: \mathbb{N}) \mapsto q < r, R\right)\right), R\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.inverseBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

For each row r in increasing original-label order, the inverse gap label is its horizontal coordinate l(r) plus the number of preceding retained up steps. On a retained subfamily of the original diagram, row lengths remain positive and nondecreasing; the inverse labels are strictly increasing. This is the inverse boundary correspondence, including all multiplicities of equal row lengths.

**Definition 1.11 (The label shift caused by deletion).**

$$\forall (U: \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet}), \forall (R: \operatorname{Finset}\left(\mathbb{N}\right)), \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.deleteRows}\left(U, R\right) = \operatorname{Finset.image}\left(\lambda (r: \mathbb{N}) \mapsto r - \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (q: \mathbb{N}) \mapsto q < r, \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet.gaps}\left(U\right) \setminus R\right)\right), R\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.deleteRows` (`✓ std3`).

*Citation.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

When R is a subset of the original gap set, each retained label decreases by the number of deleted gaps strictly before it. The proof establishes that this equals inverseBoundary(R,rowLength(U)): partition the original gaps below r into retained and deleted gaps, and use the complete boundary count. The equivalence is used in the exclusion of 1.

**Definition 1.12 (The original row-deletion map).**

$$\forall (U: \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet}), \forall (n: \mathbb{N}), n \in \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.phi}\left(U\right) \Leftrightarrow \left(\neg n \in \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.deleteRows}\left(U, \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.retainedRows}\left(U\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.phi` (`✓ std3`).

*Citation.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

phi U is the complement of the shifted retained gaps. All other natural numbers belong, including the cofinite tail. Restricted to almost symmetric semigroups this is the map in Theorem 4.2, defined by the original row deletion. The argument below does not assume the paper's output-symmetry theorem or execute the extracted GAP pseudocode.

**Theorem 1.13 (A surviving length-one row).**

$$\forall (U: \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet}), \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.Semigroup}\left(U\right) \Rightarrow \left(\neg 1 \in \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.phi}\left(U\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.phi_omits_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

Let F be the largest gap. If there is no positive source member at most F, the retained F row has length one. Otherwise let M be the greatest such member and put r=F-M. Since M<F, r is positive. Additive closure would put F in the source if r were a member, so r is a gap. The positive member M witnesses that r is not pseudo-Frobenius, because r+M=F is a gap. Any positive source member a<r would put M+a in the source strictly between M and F, contrary to maximality. Therefore this retained r row has length one. The first retained row is no longer, and its length is positive since zero belongs to the source. Its inverse label is consequently one. This holds for every proper numerical semigroup, independently of almost symmetry and with no size bound.

**Definition 1.14 (The whole unrestricted event).**

$$(\operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.claim}: \operatorname{Prop}) = \forall (T: \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet}), \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.Symmetric}\left(T\right) \Rightarrow \exists (S: \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.NumericalSet}), \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.AlmostSymmetric}\left(S\right) \land \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.phi}\left(S\right) = \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.members}\left(T\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.claim` (`✓ std3`).

*Citation.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

For every proper symmetric numerical set T, there exists a proper almost symmetric numerical semigroup S with phi S equal to T. Both carriers include every possible finite nonempty gap set; no parameter cutoff or target additive closure is present.

**Theorem 1.15 (The unrestricted event is false).**

$$\neg \operatorname{D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Manuel Delgado, Meral Suer, Mehmet Yesil (2026). *A Symmetrization for Almost Symmetric Numerical Semigroups*. URL: <https://arxiv.org/abs/2611.14268v1>.

*Commentary.*

Take T={0,1} union all naturals at least 4. Its complete gap set is {2,3}, with F=3. The complementary pairs {0,3} and {1,2} each have exactly one member, so T is proper and symmetric. It contains 1, whereas phi S omits 1 for every proper numerical semigroup S. Hence no proper almost symmetric semigroup has this image. The exclusion is analytic and quantifies over every possible source; there is no preimage enumeration or bound on source size. This gives an obstruction and a counterexample, without characterizing the full image.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.AlmostSymmetric`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.NumericalSet`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.PseudoFrobenius`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.Semigroup`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.Symmetric`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.deleteRows`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.frobenius`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.inverseBoundary`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.members`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.phi`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.phi_omits_one`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.retainedRows`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.rowLength`
