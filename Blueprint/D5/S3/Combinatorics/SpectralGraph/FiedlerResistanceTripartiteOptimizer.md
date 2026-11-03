# Original tripartite conductances, trace compression and boundary rigidity

## Abstract

The complete strict Fiedler resistance bound and unique balanced boundary on original labelled tripartite graphs.

The original parts are the successive intervals of lengths a,b,c in Fin(a+b+c). Every original cross-part edge has its own independent finite real conductance. The competitor domain has no symmetry, invariant-subspace, trace or rank premise. The matrix is the existing counting-measure wLap, lambda2 is its existing nonzero mean-zero Rayleigh infimum, and totalRes is the existing harmonic-current resistance summed once over every unordered distinct original vertex pair, including nonedges. Arbitrary values on unused nonedge coordinates do not enter any uniqueness claim. The source is the repository FIEDLER_RESISTANCE_TRIPARTITE_OPTIMIZER, Lemma 2.1 and Theorem 3.2; no external open-problem or novelty claim is made.

**Definition 1.1 (The three original labelled intervals).**

$$\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \forall c \in \mathrm{Nat},\; \forall i \in \operatorname{Fin}\left(a + b + c\right),\; \operatorname{part}\left(a, b, c, i\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) < a, 0, \operatorname{ite}\left(\operatorname{val}\left(i\right) < a + b, 1, 2\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.part` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Part labels are 0,1,2. They keep all original vertices and never contract a part.

**Definition 1.2 (The labelled complete tripartite graph).**

$$\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \forall c \in \mathrm{Nat},\; \forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Leftrightarrow (\neg (\operatorname{part}\left(a, b, c, i\right) = \operatorname{part}\left(a, b, c, j\right)))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.K3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two original vertices are adjacent exactly when their part labels differ.

**Definition 1.3 (Decidable original adjacency).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.K3_dec`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.K3_dec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural a,b,c, the original labelled graph has decidable adjacency.

**Definition 1.4 (A zero-extended boundary representative).**

$$\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \forall c \in \mathrm{Nat},\; \forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; \operatorname{boundary}\left(a, b, c\right)\left(s(i,j)\right) = \operatorname{ite}\left(\neg ((\operatorname{part}\left(a, b, c, i\right) = 2) \Leftrightarrow (\operatorname{part}\left(a, b, c, j\right) = 2)), \frac{1}{c}, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total Sym2 function is 1/c exactly across the cut from A union B to C and zero elsewhere, including every nonedge and diagonal pair. Consequently its actual original AB edges are zero and its AC and BC edges are 1/c. It is an extremizer only under c=a+b.

**Definition 1.5 (The full spectrum of the actual native Laplacian).**

$$\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \forall c \in \mathrm{Nat},\; \forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(a + b + c\right)\right) \to \mathrm{Real},\; (\operatorname{FullSpectrum}\left(a, b, c, w\right)) \Leftrightarrow ((\operatorname{card}\left(\operatorname{filter}\left((\lambda i \mapsto \operatorname{eigenvalues}\left(\operatorname{wLap}\left(\operatorname{K3}\left(a, b, c\right), w\right)\right)\left(i\right) = 0), \operatorname{univ}\left(\operatorname{Fin}\left(a + b + c\right)\right)\right)\right) = 1) \land ((\operatorname{card}\left(\operatorname{filter}\left((\lambda i \mapsto \operatorname{eigenvalues}\left(\operatorname{wLap}\left(\operatorname{K3}\left(a, b, c\right), w\right)\right)\left(i\right) = 1), \operatorname{univ}\left(\operatorname{Fin}\left(a + b + c\right)\right)\right)\right) = a + b + c - 2) \land ((\operatorname{card}\left(\operatorname{filter}\left((\lambda i \mapsto \operatorname{eigenvalues}\left(\operatorname{wLap}\left(\operatorname{K3}\left(a, b, c\right), w\right)\right)\left(i\right) = 2), \operatorname{univ}\left(\operatorname{Fin}\left(a + b + c\right)\right)\right)\right) = 1) \land (\forall i \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{eigenvalues}\left(\operatorname{wLap}\left(\operatorname{K3}\left(a, b, c\right), w\right)\right)\left(i\right) = 0) \lor ((\operatorname{eigenvalues}\left(\operatorname{wLap}\left(\operatorname{K3}\left(a, b, c\right), w\right)\right)\left(i\right) = 1) \lor (\operatorname{eigenvalues}\left(\operatorname{wLap}\left(\operatorname{K3}\left(a, b, c\right), w\right)\right)\left(i\right) = 2))))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.FullSpectrum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite index enumeration comes directly from Matrix.IsHermitian.eigenvalues of the actual wLap. Exactly one entry is zero, exactly n-2 entries are one, exactly one is two, and every entry is among these values. This specifies multiplicity without imposing an ascending index order.

**Definition 1.6 (Trace excess and complete independent-part annihilation).**

$$\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \forall c \in \mathrm{Nat},\; \forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(a + b + c\right)\right) \to \mathrm{Real},\; (\operatorname{Compression}\left(a, b, c, w\right)) \Leftrightarrow ((\operatorname{PosSemidef}\left(\operatorname{wLap}\left(\operatorname{K3}\left(a, b, c\right), w\right) - (1 - \operatorname{constProj}\left(a + b + c\right))\right)) \land ((\operatorname{mulVec}\left(\operatorname{wLap}\left(\operatorname{K3}\left(a, b, c\right), w\right) - (1 - \operatorname{constProj}\left(a + b + c\right)), 1\right) = 0) \land ((1 \le \operatorname{trace}\left(\operatorname{wLap}\left(\operatorname{K3}\left(a, b, c\right), w\right) - (1 - \operatorname{constProj}\left(a + b + c\right))\right)) \land ((\operatorname{trace}\left(\operatorname{wLap}\left(\operatorname{K3}\left(a, b, c\right), w\right) - (1 - \operatorname{constProj}\left(a + b + c\right))\right) = 1) \Rightarrow (\forall r \in \mathrm{Nat},\; (r \in \{0,1,2\}) \Rightarrow (\forall x \in \operatorname{Fin}\left(a + b + c\right) \to \mathrm{Real},\; (\operatorname{sum}\left(x\right) = 0) \Rightarrow ((\forall i \in \operatorname{Fin}\left(a + b + c\right),\; (\neg (\operatorname{part}\left(a, b, c, i\right) = r)) \Rightarrow (x\left(i\right) = 0)) \Rightarrow (\operatorname{mulVec}\left(\operatorname{wLap}\left(\operatorname{K3}\left(a, b, c\right), w\right) - (1 - \operatorname{constProj}\left(a + b + c\right)), x\right) = 0))))))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.Compression` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here H=L-(I-constProj n). The property asserts positive semidefiniteness, annihilation of constants, trace at least one, and, when trace is one, annihilation of every vector of total sum zero supported in any one of the three original parts. The proof sums all original within-part pair-difference Rayleigh inequalities. Their nonnegative gaps vanish simultaneously at trace equality. Positive semidefinite zero energy gives the kernel equations, and the original pair differences span each full supported mean-zero space. This includes part size two and uses no invariant-subspace assumption.

**Definition 1.7 (Every clause of the original theorem).**

$$\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \forall c \in \mathrm{Nat},\; (\operatorname{Theorem32}\left(a, b, c\right)) \Leftrightarrow ((\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(a + b + c\right)\right) \to \mathrm{Real},\; (\forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Rightarrow (0 < w\left(s(i,j)\right))) \Rightarrow ((0 < \operatorname{lambda2}\left(\operatorname{K3}\left(a, b, c\right), w\right)) \land ((\operatorname{lambda2}\left(\operatorname{K3}\left(a, b, c\right), w\right)) \cdot (\operatorname{totalRes}\left(\operatorname{K3}\left(a, b, c\right), w\right)) < (a + b + c) \cdot (a + b + c - \frac{3}{2})))) \land ((\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(a + b + c\right)\right) \to \mathrm{Real},\; (\forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Rightarrow (0 \le w\left(s(i,j)\right))) \Rightarrow ((\operatorname{lambda2}\left(\operatorname{K3}\left(a, b, c\right), w\right) = 1) \Rightarrow ((\operatorname{Connected}\left(\operatorname{support}\left(\operatorname{K3}\left(a, b, c\right), w\right)\right)) \land ((\operatorname{totalRes}\left(\operatorname{K3}\left(a, b, c\right), w\right) \le (a + b + c) \cdot (a + b + c - \frac{3}{2})) \land ((\operatorname{totalRes}\left(\operatorname{K3}\left(a, b, c\right), w\right) = (a + b + c) \cdot (a + b + c - \frac{3}{2})) \Leftrightarrow ((c = a + b) \land (\forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Rightarrow (w\left(s(i,j)\right) = \operatorname{boundary}\left(a, b, c\right)\left(s(i,j)\right))))))))) \land (((\exists w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(a + b + c\right)\right) \to \mathrm{Real},\; (\forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Rightarrow (0 \le w\left(s(i,j)\right))) \land ((\operatorname{lambda2}\left(\operatorname{K3}\left(a, b, c\right), w\right) = 1) \land (\operatorname{totalRes}\left(\operatorname{K3}\left(a, b, c\right), w\right) = (a + b + c) \cdot (a + b + c - \frac{3}{2})))) \Leftrightarrow (c = a + b)) \land (((c = a + b) \Rightarrow ((\forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Rightarrow (0 \le \operatorname{boundary}\left(a, b, c\right)\left(s(i,j)\right))) \land ((\operatorname{Connected}\left(\operatorname{support}\left(\operatorname{K3}\left(a, b, c\right), \operatorname{boundary}\left(a, b, c\right)\right)\right)) \land ((\operatorname{lambda2}\left(\operatorname{K3}\left(a, b, c\right), \operatorname{boundary}\left(a, b, c\right)\right) = 1) \land ((\operatorname{totalRes}\left(\operatorname{K3}\left(a, b, c\right), \operatorname{boundary}\left(a, b, c\right)\right) = (a + b + c) \cdot (a + b + c - \frac{3}{2})) \land ((\operatorname{FullSpectrum}\left(a, b, c, \operatorname{boundary}\left(a, b, c\right)\right)) \land (\neg (\forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Rightarrow (0 < \operatorname{boundary}\left(a, b, c\right)\left(s(i,j)\right)))))))))) \land (\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(a + b + c\right)\right) \to \mathrm{Real},\; (\forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Rightarrow (0 \le w\left(s(i,j)\right))) \Rightarrow ((\operatorname{lambda2}\left(\operatorname{K3}\left(a, b, c\right), w\right) = 1) \Rightarrow ((\operatorname{Compression}\left(a, b, c, w\right)) \land ((\operatorname{totalRes}\left(\operatorname{K3}\left(a, b, c\right), w\right) = (a + b + c) \cdot (a + b + c - \frac{3}{2})) \Rightarrow (\operatorname{rank}\left(\operatorname{wLap}\left(\operatorname{K3}\left(a, b, c\right), w\right) - (1 - \operatorname{constProj}\left(a + b + c\right))\right) = 1)))))))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.Theorem32` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive product bound is strict and lambda2 is positive. Every nonnegative assignment with actual lambda2=1 has connected positive support and the resistance ceiling. Equality is equivalent to balance and agreement with the displayed boundary on actual original edges. Existence of an equality assignment is equivalent to balance. The balanced boundary is connected, normalized, has the asserted full spectrum and resistance, and has a zero AB edge, so it is outside the positive domain. The final clause supplies Compression for every normalized nonnegative assignment and rank one for its actual excess matrix at resistance equality.

**Theorem 1.8 (The complete original Fiedler tripartite theorem).**

$$\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \forall c \in \mathrm{Nat},\; ((2 \le a) \land ((a \le b) \land (b \le c))) \Rightarrow ((\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(a + b + c\right)\right) \to \mathrm{Real},\; (\forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Rightarrow (0 < w\left(s(i,j)\right))) \Rightarrow ((0 < \operatorname{lambda2}\left(\operatorname{K3}\left(a, b, c\right), w\right)) \land ((\operatorname{lambda2}\left(\operatorname{K3}\left(a, b, c\right), w\right)) \cdot (\operatorname{totalRes}\left(\operatorname{K3}\left(a, b, c\right), w\right)) < (a + b + c) \cdot (a + b + c - \frac{3}{2})))) \land ((\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(a + b + c\right)\right) \to \mathrm{Real},\; (\forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Rightarrow (0 \le w\left(s(i,j)\right))) \Rightarrow ((\operatorname{lambda2}\left(\operatorname{K3}\left(a, b, c\right), w\right) = 1) \Rightarrow ((\operatorname{Connected}\left(\operatorname{support}\left(\operatorname{K3}\left(a, b, c\right), w\right)\right)) \land ((\operatorname{totalRes}\left(\operatorname{K3}\left(a, b, c\right), w\right) \le (a + b + c) \cdot (a + b + c - \frac{3}{2})) \land ((\operatorname{totalRes}\left(\operatorname{K3}\left(a, b, c\right), w\right) = (a + b + c) \cdot (a + b + c - \frac{3}{2})) \Leftrightarrow ((c = a + b) \land (\forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Rightarrow (w\left(s(i,j)\right) = \operatorname{boundary}\left(a, b, c\right)\left(s(i,j)\right))))))))) \land (((\exists w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(a + b + c\right)\right) \to \mathrm{Real},\; (\forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Rightarrow (0 \le w\left(s(i,j)\right))) \land ((\operatorname{lambda2}\left(\operatorname{K3}\left(a, b, c\right), w\right) = 1) \land (\operatorname{totalRes}\left(\operatorname{K3}\left(a, b, c\right), w\right) = (a + b + c) \cdot (a + b + c - \frac{3}{2})))) \Leftrightarrow (c = a + b)) \land (((c = a + b) \Rightarrow ((\forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Rightarrow (0 \le \operatorname{boundary}\left(a, b, c\right)\left(s(i,j)\right))) \land ((\operatorname{Connected}\left(\operatorname{support}\left(\operatorname{K3}\left(a, b, c\right), \operatorname{boundary}\left(a, b, c\right)\right)\right)) \land ((\operatorname{lambda2}\left(\operatorname{K3}\left(a, b, c\right), \operatorname{boundary}\left(a, b, c\right)\right) = 1) \land ((\operatorname{totalRes}\left(\operatorname{K3}\left(a, b, c\right), \operatorname{boundary}\left(a, b, c\right)\right) = (a + b + c) \cdot (a + b + c - \frac{3}{2})) \land ((\operatorname{FullSpectrum}\left(a, b, c, \operatorname{boundary}\left(a, b, c\right)\right)) \land (\neg (\forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Rightarrow (0 < \operatorname{boundary}\left(a, b, c\right)\left(s(i,j)\right)))))))))) \land (\forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(a + b + c\right)\right) \to \mathrm{Real},\; (\forall i \in \operatorname{Fin}\left(a + b + c\right),\; \forall j \in \operatorname{Fin}\left(a + b + c\right),\; (\operatorname{Adj}\left(\operatorname{K3}\left(a, b, c\right), i, j\right)) \Rightarrow (0 \le w\left(s(i,j)\right))) \Rightarrow ((\operatorname{lambda2}\left(\operatorname{K3}\left(a, b, c\right), w\right) = 1) \Rightarrow ((\operatorname{Compression}\left(a, b, c, w\right)) \land ((\operatorname{totalRes}\left(\operatorname{K3}\left(a, b, c\right), w\right) = (a + b + c) \cdot (a + b + c - \frac{3}{2})) \Rightarrow (\operatorname{rank}\left(\operatorname{wLap}\left(\operatorname{K3}\left(a, b, c\right), w\right) - (1 - \operatorname{constProj}\left(a + b + c\right))\right) = 1)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The general harmonic inverse construction supplies R=n times the sum of reciprocal native eigenvalues. The independent parts give trace L at least n*t for actual t=lambda2. On the n-1 positive eigenvalues set q=r/t-1. Then q is nonnegative and its sum is at least one; comparing q/(1+q) to q/(1+sum q) gives the reciprocal ceiling. Equality forces sum q=1 and exactly one q=1. Native unitary diagonalization therefore gives L-t*(I-constProj n)=t*v*v transpose with sum v=0, counting norm one and rank one. Trace equality makes the same v constant on each original part. Same-part off-diagonal entries and part size at least two force each part value to have square 1/n. Equal squares and the original sum-zero equation give the simultaneous sign balance: A and B have the same sign, C the opposite sign, and c=a+b. The actual off-diagonal entries give AB=0 and AC=BC=t/c. Positive conductances exclude this equality. For the boundary, an explicit original-vertex matrix identity L=I-constProj n+(1/n)*sigma*sigma transpose, with sigma equal to +1 on A and B and -1 on C, proves the actual Rayleigh value one. The native eigenvectors then have eigenvalues only 0,1,2; zero multiplicity and trace determine 0,1^(n-2),2. The harmonic spectral identity supplies the attained resistance. This proves all original labelled triples 2<=a<=b<=c, including ties, zeros and asymmetric competitors.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.Compression`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.FullSpectrum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.K3`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.K3_dec`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.Theorem32`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.boundary`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.part`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.result`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral](FiedlerResistanceConnectedSpectral.md)
