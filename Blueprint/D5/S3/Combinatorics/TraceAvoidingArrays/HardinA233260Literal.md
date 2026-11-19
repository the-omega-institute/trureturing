# Five-row antidiagonal arrays

## Abstract

Literal five-row complementary-pair arrays with horizontal and antidiagonal bonds.

An array is a function from Fin 5 times Fin n to Fin 6. A bond joins (r,j) to (s,j+1) exactly when r=s or r.val=s.val+1. It excludes equal colours and colours whose values sum to five. The first entry is zero. The rank r.val*n+j.val defines the strict row-major predecessor relation. No colour is required to occur.

**Definition 1.1 (Col).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right) = \operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.Col` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Col.

**Definition 1.2 (column).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(c\right): \operatorname{Fin}\left(5\right) \to \operatorname{Fin}\left(3\right)) = \begin{pmatrix}\operatorname{Prod}.\operatorname{fst}\left(c\right)&\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)&\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)&\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)\right)&\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)\right)\end{pmatrix})$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.column` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

column.

**Definition 1.3 (compatible).**

$$\forall (a: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\forall (b: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{compatible}\left(a, b\right) = ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(a, 0\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(b, 0\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(a, 1\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(b, 1\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(a, 2\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(b, 2\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(a, 3\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(b, 3\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(a, 4\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(b, 4\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(a, 1\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(b, 0\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(a, 2\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(b, 1\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(a, 3\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(b, 2\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(a, 4\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(b, 3\right))))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

compatible.

**Definition 1.4 (cls).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{cls}\left(c\right): \operatorname{Fin}\left(41\right)) = \begin{pmatrix}\begin{pmatrix}0&27&27&14&9&40&14&40&9\end{pmatrix}&\begin{pmatrix}5&18&36&23&3&31&32&22&13\end{pmatrix}&\begin{pmatrix}5&36&18&32&13&22&23&31&3\end{pmatrix}&\begin{pmatrix}2&24&30&17&6&37&20&34&12\end{pmatrix}&\begin{pmatrix}8&15&39&26&1&28&38&16&10\end{pmatrix}&\begin{pmatrix}11&33&21&35&7&19&29&25&4\end{pmatrix}&\begin{pmatrix}2&30&24&20&12&34&17&37&6\end{pmatrix}&\begin{pmatrix}11&21&33&29&4&25&35&19&7\end{pmatrix}&\begin{pmatrix}8&39&15&38&10&16&26&28&1\end{pmatrix}&\begin{pmatrix}1&26&28&15&8&39&16&38&10\end{pmatrix}&\begin{pmatrix}6&17&37&24&2&30&34&20&12\end{pmatrix}&\begin{pmatrix}7&35&19&33&11&21&25&29&4\end{pmatrix}&\begin{pmatrix}3&23&31&18&5&36&22&32&13\end{pmatrix}&\begin{pmatrix}9&14&40&27&0&27&40&14&9\end{pmatrix}&\begin{pmatrix}13&32&22&36&5&18&31&23&3\end{pmatrix}&\begin{pmatrix}4&29&25&21&11&33&19&35&7\end{pmatrix}&\begin{pmatrix}12&20&34&30&2&24&37&17&6\end{pmatrix}&\begin{pmatrix}10&38&16&39&8&15&28&26&1\end{pmatrix}&\begin{pmatrix}1&28&26&16&10&38&15&39&8\end{pmatrix}&\begin{pmatrix}7&19&35&25&4&29&33&21&11\end{pmatrix}&\begin{pmatrix}6&37&17&34&12&20&24&30&2\end{pmatrix}&\begin{pmatrix}4&25&29&19&7&35&21&33&11\end{pmatrix}&\begin{pmatrix}10&16&38&28&1&26&39&15&8\end{pmatrix}&\begin{pmatrix}12&34&20&37&6&17&30&24&2\end{pmatrix}&\begin{pmatrix}3&31&23&22&13&32&18&36&5\end{pmatrix}&\begin{pmatrix}13&22&32&31&3&23&36&18&5\end{pmatrix}&\begin{pmatrix}9&40&14&40&9&14&27&27&0\end{pmatrix}\end{pmatrix}\left((\operatorname{Fin}.\operatorname{mk}\left(((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(c\right)\right)) + ((3) \cdot (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)))) + ((9) \cdot (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)\right)))) + ((27) \cdot (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)\right)\right)))) + ((81) \cdot (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(c\right)\right)\right)\right)\right)))\right): \operatorname{Fin}\left(243\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.cls` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

cls.

**Definition 1.5 (Class representatives).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{representatives}\left(\right): \operatorname{Fin}\left(41\right) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)) = \begin{pmatrix}(0, (0, (0, (0, 0))))&(0, (0, (0, (0, 1))))&(0, (0, (0, (1, 0))))&(0, (0, (0, (1, 1))))&(0, (0, (0, (1, 2))))&(0, (0, (1, (0, 0))))&(0, (0, (1, (0, 1))))&(0, (0, (1, (0, 2))))&(0, (0, (1, (1, 0))))&(0, (0, (1, (1, 1))))&(0, (0, (1, (1, 2))))&(0, (0, (1, (2, 0))))&(0, (0, (1, (2, 1))))&(0, (0, (1, (2, 2))))&(0, (1, (0, (0, 0))))&(0, (1, (0, (0, 1))))&(0, (1, (0, (0, 2))))&(0, (1, (0, (1, 0))))&(0, (1, (0, (1, 1))))&(0, (1, (0, (1, 2))))&(0, (1, (0, (2, 0))))&(0, (1, (0, (2, 1))))&(0, (1, (0, (2, 2))))&(0, (1, (1, (0, 0))))&(0, (1, (1, (0, 1))))&(0, (1, (1, (0, 2))))&(0, (1, (1, (1, 0))))&(0, (1, (1, (1, 1))))&(0, (1, (1, (1, 2))))&(0, (1, (1, (2, 0))))&(0, (1, (1, (2, 1))))&(0, (1, (1, (2, 2))))&(0, (1, (2, (0, 0))))&(0, (1, (2, (0, 1))))&(0, (1, (2, (0, 2))))&(0, (1, (2, (1, 0))))&(0, (1, (2, (1, 1))))&(0, (1, (2, (1, 2))))&(0, (1, (2, (2, 0))))&(0, (1, (2, (2, 1))))&(0, (1, (2, (2, 2))))\end{pmatrix}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Class representatives.

**Definition 1.6 (Arrays as column functions).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{gridEquiv}\left(n\right): \operatorname{Equiv}\left((\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(n\right) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)\right)) = (\operatorname{toFun}: (\lambda (P: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)) \mapsto (\lambda (j: \operatorname{Fin}\left(n\right)) \mapsto (P\left((0, j)\right), (P\left((1, j)\right), (P\left((2, j)\right), (P\left((3, j)\right), P\left((4, j)\right))))))), \operatorname{invFun}: (\lambda (f: \operatorname{Fin}\left(n\right) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)) \mapsto (\lambda (p: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right))) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(f\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right), \operatorname{Prod}.\operatorname{fst}\left(p\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.gridEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Arrays as column functions.

**Theorem 1.7 (Recovering an array entry from its column).**

$$\forall (n: \operatorname{Nat}), (\forall (P: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (r: \operatorname{Fin}\left(5\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{gridEquiv}\left(n, P, j\right), r\right) = P\left((r, j)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.column_grid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Recovering an array entry from its column.

**Theorem 1.8 (Column coordinates under a colour permutation).**

$$\forall (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\forall (r: \operatorname{Fin}\left(5\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{relabel}\left(e, c\right), r\right) = e\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{column}\left(c, r\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.column_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Column coordinates under a colour permutation.

**Theorem 1.9 (Every column has its class representative).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\exists (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{relabel}\left(e, c\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{representatives}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{cls}\left(c\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.class_rep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Every column has its class representative.

**Definition 1.10 (The seven transfer coefficients).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{coefficients}\left(\right): \operatorname{Fin}\left(7\right) \to \operatorname{Int}) = \begin{pmatrix}(-8)&48&(-84)&17&76&(-64)&16\end{pmatrix}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.coefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

The seven transfer coefficients.

**Theorem 1.11 (The zero-defect column powers).**

$$\forall (k: \operatorname{Fin}\left(12\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Q}\left(\right)^{\operatorname{Fin}.\operatorname{val}\left(k\right)}, (1: \operatorname{Fin}\left(41\right) \to \operatorname{Int})\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{W}\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.powers_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

The zero-defect column powers.

**Theorem 1.12 (The zero-defect vector polynomial).**

$$\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Q}\left(\right)^{(4) + (7)}, (1: \operatorname{Fin}\left(41\right) \to \operatorname{Int})\right) = \sum_{j: \operatorname{Fin}\left(7\right)} (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{coefficients}\left(j\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Q}\left(\right)^{(4) + (\operatorname{Fin}.\operatorname{val}\left(j\right))}, (1: \operatorname{Fin}\left(41\right) \to \operatorname{Int})\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.power_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

The zero-defect vector polynomial.

**Definition 1.13 (relabel).**

$$\forall (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{relabel}\left(e\right): \operatorname{Equiv}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)\right)) = \operatorname{Equiv}.\operatorname{prodCongr}\left(e, \operatorname{Equiv}.\operatorname{prodCongr}\left(e, \operatorname{Equiv}.\operatorname{prodCongr}\left(e, \operatorname{Equiv}.\operatorname{prodCongr}\left(e, e\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.relabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

relabel.

**Theorem 1.14 (class_relabel).**

$$\forall (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{cls}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{relabel}\left(e, c\right)\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{cls}\left(c\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.class_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

class_relabel.

**Definition 1.15 (Q).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Q}\left(\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right), \operatorname{Int}\right)) = \begin{pmatrix}\begin{pmatrix}2&2&2&2&0&2&2&0&2\\1&1&0&1&1&1&0&1&0\\1&1&0&0&0&0&0&0&1\\1&1&1&1&0&0&0&0&0\\0&0&0&1&1&0&0&0&0\\1&1&1&1&0&0&0&0&0\\1&1&0&0&0&0&0&0&0\\0&0&0&1&1&0&0&0&0\\1&1&0&0&0&1&0&1&0\\1&1&1&1&0&1&1&0&1\\0&0&0&1&1&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&1\\0&0&0&0&0&0&0&0&0\\1&1&1&1&0&1&1&0&1\\1&1&0&0&0&1&0&1&0\\0&0&0&1&1&0&0&0&0\\1&1&0&0&0&0&0&0&0\\1&1&1&1&0&0&0&0&0\\0&0&0&1&1&0&0&0&0\\0&0&0&0&0&0&0&0&1\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\1&1&1&1&0&0&0&0&0\\1&1&0&0&0&0&0&0&0\\0&0&0&1&1&0&0&0&0\\1&1&0&0&0&1&0&1&0\\1&1&1&1&0&1&1&0&1\\0&0&0&1&1&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&1\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\end{pmatrix}&\begin{pmatrix}2&0&0&0&0&2&2&0&2\\1&1&0&0&0&1&0&1&0\\1&0&0&0&0&1&1&0&0\\1&1&0&1&1&1&0&1&0\\0&0&1&0&1&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\1&0&0&0&0&0&0&0&0\\1&1&0&0&0&0&0&0&0\\0&0&1&0&1&0&0&0&0\\1&0&0&0&0&0&0&0&0\\1&1&0&1&1&0&0&0&0\\1&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\1&1&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\1&0&0&0&0&0&0&0&0\\0&0&1&0&1&0&0&0&0\\1&1&0&1&1&0&0&0&0\\0&0&0&0&0&1&0&1&0\\0&0&0&0&0&1&1&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&1&0&1&0\\1&0&0&0&0&1&1&0&1\\1&1&0&0&0&0&0&0&0\\0&0&1&0&1&0&0&0&0\\1&0&0&0&0&0&0&0&0\\1&1&0&1&1&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\end{pmatrix}&\begin{pmatrix}2&0&0&0&0&2&2&0&2\\1&1&0&0&0&1&0&1&0\\0&0&0&0&0&0&0&0&1\\0&0&1&0&1&0&0&0&0\\0&0&0&1&1&0&0&0&0\\0&0&0&0&0&1&1&0&1\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&1&0&1&0\\0&0&0&0&0&0&0&0&1\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&1&0&1&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&1&1&0&0&0&0\\0&0&0&0&0&1&0&1&0\\1&0&0&0&0&1&1&0&1\\1&1&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&1\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&1&0&1&0\\0&0&0&0&0&1&1&0&1\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&1\\0&0&0&0&0&0&0&0&0\end{pmatrix}&\begin{pmatrix}2&0&0&0&0&0&0&0&0\\1&1&0&0&0&0&0&0&0\\1&0&0&0&0&0&0&0&0\\1&1&0&1&1&0&0&0&0\\0&0&1&0&1&0&0&0&0\\1&0&0&0&0&0&0&0&0\\1&1&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\1&0&0&0&0&0&0&0&1\\1&1&0&1&1&0&0&0&0\\0&0&1&0&1&0&0&0&0\\0&0&0&0&0&1&1&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&1&0&1&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\1&0&0&0&0&0&0&0&0\\1&1&0&0&0&0&0&0&0\\0&0&1&0&1&0&0&0&0\\1&0&0&0&0&0&0&0&0\\1&1&0&1&1&0&0&0&0\\0&0&0&0&0&1&0&1&0\\0&0&0&0&0&1&1&0&0\\0&0&0&0&0&0&0&0&0\\0&0&0&0&0&0&0&0&0\\1&0&0&0&0&0&0&0&0\\1&1&0&0&0&0&0&0&0\\0&0&1&0&1&0&0&0&0\\1&0&0&0&0&0&0&0&1\\1&1&0&1&1&0&0&0&0\end{pmatrix}&\begin{pmatrix}0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\1&0&0&0&0\\1&1&0&1&1\\0&0&1&0&1\\0&0&0&0&0\\0&0&0&1&1\\0&0&1&0&1\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&1&0&1\\0&0&0&0&0\\0&0&0&1&1\\0&0&0&0&0\\0&0&0&0&0\\0&0&0&0&0\\0&0&1&0&1\\1&0&0&0&0\\1&1&0&1&1\end{pmatrix}\end{pmatrix}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Q.

**Definition 1.16 (classWeights).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{classWeights}\left(\right): \operatorname{Fin}\left(41\right) \to \operatorname{Int}) = \begin{pmatrix}\begin{pmatrix}3&6&6&6&6&6&6&6&6\end{pmatrix}&\begin{pmatrix}6&6&6&6&6&6&6&6&6\end{pmatrix}&\begin{pmatrix}6&6&6&6&6&6&6&6&6\end{pmatrix}&\begin{pmatrix}6&6&6&6&6&6&6&6&6\end{pmatrix}&\begin{pmatrix}6&6&6&6&6\end{pmatrix}\end{pmatrix}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.classWeights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

classWeights.

**Definition 1.17 (W).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{W}\left(\right): \operatorname{Fin}\left(12\right) \to \left(\operatorname{Fin}\left(41\right) \to \operatorname{Int}\right)) = \begin{pmatrix}\begin{pmatrix}1&1&1&1&1&1&1&1&1\\32&16&8&16&8&8&4&4&8\\324&162&108&162&54&108&72&36&90\\3744&1692&1152&1656&432&1152&726&336&924\\40404&17832&12648&17382&3864&12648&8094&3324&10218\\436584&188052&136128&182976&37776&135978&86472&34188&109848\\4677996&1999236&1461936&1948170&386868&1455330&926688&356718&1178040\\50046816&21300108&15641112&20791860&4076904&15561330&9902268&3777432&12589032\\534870876&227362620&167167956&222058218&43370256&166285254&105794832&40244358&134501088\\5714699808&2428286892&1786071108&2372039916&462744516&1776553854&1130218524&429577152&1436892528\\61051776924&25939228116&19081127928&25339665234&4941644988&18979182138&12074072952&4588030326&15350261016\\652216306656&277099897740&203843789832&270698972820&52785403032&202753867506&128986171596&49009985160&163985386296\end{pmatrix}&\begin{pmatrix}1&1&1&1&1&1&1&1&1\\16&8&4&4&8&8&4&4&2\\162&72&18&36&54&108&60&48&48\\1692&624&96&336&432&1188&630&450&486\\18012&5934&660&3414&3954&12738&6924&4404&5436\\193422&60300&5616&36798&39786&137238&74208&45192&58236\\2069382&630552&54876&395094&418638&1469460&794802&474474&624636\\22126926&6683616&571320&4230582&4449822&15716778&8489280&5034972&6677232\\236442918&71231268&6055104&45225858&47469054&167959452&90685686&53679306&71346924\\2526101382&760417884&64536228&483242874&506892534&1794483762&968763108&573102660&762233496\\26986703574&8121775080&688964268&5162740950&5414409822&19170864012&10349117706&6121303698&8142986700\\288297900318&86758735104&7358664744&55153947462&57839442558&204802017882&110558217504&65389788876&86991005040\end{pmatrix}&\begin{pmatrix}1&1&1&1&1&1&1&1&1\\4&2&2&2&4&8&4&4&8\\72&24&24&12&36&90&60&30&84\\756&216&252&72&324&972&654&264&906\\8244&2088&2616&528&3084&10458&7254&2484&9798\\88266&21246&28230&4614&31314&111108&77898&24858&104292\\943740&220752&303270&45402&330306&1185714&836082&256680&1113198\\10087338&2335038&3247422&473514&3513666&12664848&8941494&2710746&11875608\\107779896&24868764&34715958&5021142&37490946&135292734&95552982&28855944&126813030\\1151459670&265428474&370944006&53524158&400369098&1445305332&1020878634&307940562&1354550544\\12301097724&2834784432&3962993910&571428762&4276654674&15439997250&10906233570&3288677688&14469950022\\131411798202&30281310222&42336964590&6103374090&45685629426&164943614496&116510986758&35129393658&154579060152\end{pmatrix}&\begin{pmatrix}1&1&1&1&1&1&1&1&1\\16&8&4&4&8&4&2&2&2\\162&78&24&48&72&18&6&12&12\\1872&786&168&498&684&108&24&84&120\\20202&8034&1380&5394&6924&870&132&798&1236\\218292&83760&12918&58230&71868&8472&1002&8568&12942\\2338998&886038&130188&625854&762456&88332&9474&91824&135966\\25023408&9424500&1366158&6699618&8127012&936156&97806&983160&1442394\\267435438&100549590&14514312&71614974&86765484&9978108&1033962&10509900&15375594\\2857349904&1073736348&154803954&765192474&926734584&106523436&11012070&112298868&164148678\\30525888462&11469278094&1652967300&8174894358&9899667984&1137755148&117535506&1199747040&1753245894\\326108153328&122520837588&17656009374&87332803074&105755358324&12153813132&1255290654&12816982872&18728674938\end{pmatrix}&\begin{pmatrix}1&1&1&1&1\\4&2&4&4&8\\36&24&24&30&54\\396&240&174&294&504\\4404&2658&1530&3294&5274\\47712&28236&15108&35640&56184\\511590&302052&156078&383238&599922\\5473992&3225036&1648644&4099752&6410148\\58505358&34447908&17551962&43815402&68483466\\625094184&367985028&187315224&468129420&731617620\\6678084414&3931086252&2000471382&5001143310&7815839562\\71342069304&41995166556&21368946228&53427168792&83495882436\end{pmatrix}\end{pmatrix}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

W.

**Theorem 1.18 (quotient_rows).**

$$\forall (b: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\forall (s: \operatorname{Fin}\left(41\right)), (\sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)} ((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{compatible}\left(b, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{cls}\left(c\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Q}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{cls}\left(b\right), s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.quotient_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

quotient_rows.

**Theorem 1.19 (initial_class_counts).**

$$\forall (i: \operatorname{Fin}\left(41\right)), (\sum_{a: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)} ((\operatorname{if} (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{cls}\left(a\right) = i) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{classWeights}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.initial_class_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

initial_class_counts.

**Definition 1.20 (Strict row-major normalization).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{normal}\left(A\right) = (\forall (p: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right))), ((((A\left(p\right) = (2: \operatorname{Fin}\left(6\right))) \lor ((A\left(p\right) = (3: \operatorname{Fin}\left(6\right))) \lor (A\left(p\right) = (4: \operatorname{Fin}\left(6\right))))) \Rightarrow (\exists (q: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = (1: \operatorname{Fin}\left(6\right)))))) \land ((A\left(p\right) = (3: \operatorname{Fin}\left(6\right))) \Rightarrow (\exists (q: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = (2: \operatorname{Fin}\left(6\right))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.normal` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

OEIS A233260, revision 7, NAME: Number of 5Xn 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabeled 6-colorings with no clashing color pairs).

**Definition 1.21 (Literal array predicate).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Legal}\left(A\right) = ((\exists (j: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}.\operatorname{val}\left(j\right) = 0) \land (A\left(((0: \operatorname{Fin}\left(5\right)), j)\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), (\forall (r: \operatorname{Fin}\left(5\right)), (\forall (s: \operatorname{Fin}\left(5\right)), (((r = s) \lor (\operatorname{Fin}.\operatorname{val}\left(r\right) = (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1))) \Rightarrow ((A\left((r, j)\right) \ne A\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left((r, j)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)\right)) \ne 5))))))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{normal}\left(A\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.Legal` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

OEIS A233260, revision 7, NAME: Number of 5Xn 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabeled 6-colorings with no clashing color pairs).

**Definition 1.22 (Literal finite count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Legal}\left(A\right)), \operatorname{Finset}.\operatorname{univ}\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

OEIS A233260, revision 7, NAME: Number of 5Xn 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabeled 6-colorings with no clashing color pairs).

**Definition 1.23 (Proper pair-label pattern).**

$$\forall (n: \operatorname{Nat}), (\forall (P: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Proper}\left(P\right) = (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), (\forall (r: \operatorname{Fin}\left(5\right)), (\forall (s: \operatorname{Fin}\left(5\right)), (((r = s) \lor (\operatorname{Fin}.\operatorname{val}\left(r\right) = (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1))) \Rightarrow (P\left((r, j)\right) \ne P\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.Proper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Proper pair-label pattern.

**Definition 1.24 (Labelled three-colour count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (P: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Proper}\left(P\right)), \operatorname{Finset}.\operatorname{univ}\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Labelled three-colour count.

**Definition 1.25 (Column-parity colouring).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.alternating`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.alternating` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

For any width and two labels a and b, the array has label a at every even column and label b at every odd column.

**Theorem 1.26 (Omitting a label forces constant columns).**

$$\forall (n: \operatorname{Nat}), ((2 \le n) \Rightarrow (\forall (P: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Proper}\left(P\right)) \Rightarrow (\forall (d: \operatorname{Fin}\left(3\right)), ((\forall (i: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right))), (P\left(i\right) \ne d)) \Rightarrow (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (r: \operatorname{Fin}\left(5\right)), (P\left((r, j)\right) = P\left(((0: \operatorname{Fin}\left(5\right)), j)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.columns_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Omitting a label forces constant columns.

**Theorem 1.27 (Two remaining labels alternate with column parity).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.two_label_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.two_label_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

For every width n at least two and every proper Fin 5 by Fin n array P into Fin 3 omitting a label d, there are distinct labels a and b such that P(r,j) is a at even j and b at odd j. Properness uses exactly the horizontal and antidiagonal bonds defined here. The classification applies to any stronger edge predicate containing those bonds.

**Theorem 1.28 (Exact complementary-pair count).**

$$\forall (n: \operatorname{Nat}), ((2 \le n) \Rightarrow ((48) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(n\right): \operatorname{Int})) = ((32: \operatorname{Int})^{n}) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left(n\right): \operatorname{Int})) + (6))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.counting_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Exact complementary-pair count.

The pair labels identify {0,5}, {1,4}, and {2,3}. Canonical first occurrences fix the pair names and the first side of each used pair. A pattern with k used pairs has 2^(5*n-k) lifts. At width at least two, every proper pattern uses two or three labels, and every orbit under label permutations has six members. When one label is omitted, the common neighbours of consecutive rows force each column to be constant, including the last column. The two remaining labels alternate with column parity. Exactly one such pattern is canonical. Summing the two possible lift weights gives the displayed identity.

**Theorem 1.29 (The first pair-label recurrence).**

$$((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left(12\right): \operatorname{Int})) + (6) = (((((((16) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left(11\right): \operatorname{Int})) + (6))) - ((64) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left(10\right): \operatorname{Int})) + (6)))) + ((76) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left(9\right): \operatorname{Int})) + (6)))) + ((17) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left(8\right): \operatorname{Int})) + (6)))) - ((84) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left(7\right): \operatorname{Int})) + (6)))) + ((48) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left(6\right): \operatorname{Int})) + (6)))) - ((8) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left(5\right): \operatorname{Int})) + (6)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.pair_base` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

The first pair-label recurrence.

**Theorem 1.30 (The pair-label recurrence at every larger width).**

$$\forall (n: \operatorname{Nat}), (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left((n) + (13)\right): \operatorname{Int})) + (6) = (((((((16) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left((n) + (12)\right): \operatorname{Int})) + (6))) - ((64) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left((n) + (11)\right): \operatorname{Int})) + (6)))) + ((76) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left((n) + (10)\right): \operatorname{Int})) + (6)))) + ((17) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left((n) + (9)\right): \operatorname{Int})) + (6)))) - ((84) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left((n) + (8)\right): \operatorname{Int})) + (6)))) + ((48) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left((n) + (7)\right): \operatorname{Int})) + (6)))) - ((8) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left((n) + (6)\right): \operatorname{Int})) + (6))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.pair_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

The pair-label recurrence at every larger width.

**Theorem 1.31 (The seven-lag integer recurrence).**

$$\forall (n: \operatorname{Int}), ((11 < n) \Rightarrow ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left(n\right)\right): \operatorname{Int}) = (((((((512) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (1)\right)\right): \operatorname{Int}))) - ((65536) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (2)\right)\right): \operatorname{Int})))) + ((2490368) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (3)\right)\right): \operatorname{Int})))) + ((17825792) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (4)\right)\right): \operatorname{Int})))) - ((2818572288) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (5)\right)\right): \operatorname{Int})))) + ((51539607552) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (6)\right)\right): \operatorname{Int})))) - ((274877906944) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (7)\right)\right): \operatorname{Int})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233260` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233260","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

OEIS A233260, revision 7, FORMULA: Empirical: a(n) = 512*a(n-1) -65536*a(n-2) +2490368*a(n-3) +17825792*a(n-4) -2818572288*a(n-5) +51539607552*a(n-6) -274877906944*a(n-7) for n>11

Column states record five independent pair labels. Relabelling reduces their transitions to forty-one classes. The transfer polynomial is x^7-16*x^6+64*x^5-76*x^4-17*x^3+84*x^2-48*x+8. Its vector relation holds after four transitions and its value at one is zero. The scalar relation covers every index at least thirteen; the same finite power table verifies index twelve. The counting bridge scales each lag coefficient by a power of thirty-two. Every count used has positive width. The final statement quantifies all integers greater than eleven.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.Col`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.L`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.Proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.Q`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.W`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.alternating`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.classWeights`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.class_relabel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.class_rep`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.cls`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.coefficients`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.column`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.column_grid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.column_relabel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.columns_constant`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.counting_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.gridEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.initial_class_counts`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.normal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.pair_base`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.pair_tail`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.power_polynomial`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.powers_table`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.quotient_rows`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.relabel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.representatives`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.two_label_classification`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
