# Constrained harmonic optimization

## Abstract

Constrained harmonic optimization on the complete Fibonacci cube

**Definition 1.1 (The harmonic edge term).**

$$\forall s \in \mathbb{R},\; \forall t \in \mathbb{R},\; \mathrm{harmonic}\left(s, t\right) = \frac{s \cdot t}{s + t}$$

*Formalization.* `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.harmonic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real function h(s,t)=s*t/(s+t) uses total real division. In particular h(0,0)=0.

**Definition 1.2 (The complete original unordered-edge objective).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathrm{Legal}\left(n\right) \to \mathbb{R},\; \mathrm{objective}\left(n, p\right) = \sum_{e \in \mathrm{edgeFinset}\left(\mathrm{legalWordGraph}\left(n\right)\right)} \operatorname{Sym2.lift}\left((\lambda a: \mathrm{Legal}\left(n\right), (\lambda b: \mathrm{Legal}\left(n\right), \mathrm{harmonic}\left(p\left(a\right), p\left(b\right)\right))), e\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.objective` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Phi_n(p) sums h(p_b,p_c) over exactly the native unordered edgeFinset of legalWordGraph n on EdgeCount.Legal n. Every legal Hamming-one edge is included. This includes the zero word, both open-path endpoints and edges between consecutive blocks in any block notation. The existing deletion-edge bijection reindexes this same sum by the occupied upper word and its true position.

**Definition 1.3 (The entire normalized positive simplex).**

$$\forall n \in \mathbb{N},\; \forall epsilon \in \mathbb{R},\; \mathrm{epsilonSimplex}\left(n, epsilon\right) = \{p: \mathrm{Legal}\left(n\right) \to \mathbb{R} \mid (\forall b \in \mathrm{Legal}\left(n\right),\; epsilon \le p\left(b\right)) \land (\sum_{b: \mathrm{Legal}\left(n\right)} (p\left(b\right)) = 1)\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.epsilonSimplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C_epsilon consists of every real vector with p_b>=epsilon at every original legal word and sum_b p_b=1. Insertion inequalities are not constraints defining this set. It is nonempty when epsilon<=1/M, where M is the number of original legal words, including equality and its uniform vector.

**Definition 1.4 (Open-path position adjacency).**

$$\forall n \in \mathbb{N},\; \forall i \in \mathrm{Fin}\left(n\right),\; \forall j \in \mathrm{Fin}\left(n\right),\; (\mathrm{Near}\left(i, j\right)) \Leftrightarrow ((\mathrm{val}\left(i\right) + 1 = \mathrm{val}\left(j\right)) \lor (\mathrm{val}\left(j\right) + 1 = \mathrm{val}\left(i\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.Near` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positions i and j are neighbors when their natural indices differ by one. There is no cyclic identification.

**Definition 1.5 (The number of neighboring path positions).**

$$\forall n \in \mathbb{N},\; \forall i \in \mathrm{Fin}\left(n\right),\; \mathrm{positionDegree}\left(i\right) = \mathrm{card}\left(\{j: \mathrm{Fin}\left(n\right) \mid \mathrm{Near}\left(i, j\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.positionDegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

d_i counts neighboring positions in Fin n. It is a position degree, distinct from the degree of a legal-word vertex.

**Definition 1.6 (The position-dependent ratio constant).**

$$\forall n \in \mathbb{N},\; \forall i \in \mathrm{Fin}\left(n\right),\; \mathrm{insertionLower}\left(i\right) = \frac{4 - \mathrm{positionDegree}\left(i\right)}{4 + \mathrm{positionDegree}\left(i\right)}$$

*Formalization.* `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.insertionLower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

q_i=(4-d_i)/(4+d_i). At length one this is 1, at an endpoint of a path of length at least two it is 3/5, and at an interior position it is 1/3.

**Definition 1.7 (Bounds at every native upward insertion).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathrm{Legal}\left(n\right) \to \mathbb{R},\; (\mathrm{InsertionBounds}\left(n, p\right)) \Leftrightarrow (\forall e \in \mathrm{Marked}\left(n\right),\; (\mathrm{insertionLower}\left(\mathrm{val}\left(\mathrm{snd}\left(e\right)\right)\right) \cdot p\left(\mathrm{erase}\left(\mathrm{fst}\left(e\right), \mathrm{val}\left(\mathrm{snd}\left(e\right)\right)\right)\right) \le p\left(\mathrm{fst}\left(e\right)\right)) \land (p\left(\mathrm{fst}\left(e\right)\right) \le p\left(\mathrm{erase}\left(\mathrm{fst}\left(e\right), \mathrm{val}\left(\mathrm{snd}\left(e\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.InsertionBounds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original marked edge, upper y and lower x=erase y i satisfy q_i*p_x<=p_y<=p_x. The marked word is the upper endpoint, not the lower endpoint.

**Definition 1.8 (Conserved mass transfer on original coordinates).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathrm{Legal}\left(n\right) \to \mathbb{R},\; \forall donor \in \mathrm{Legal}\left(n\right),\; \forall receiver \in \mathrm{Legal}\left(n\right),\; \forall u \in \mathbb{R},\; \forall b \in \mathrm{Legal}\left(n\right),\; \mathrm{transfer}\left(p, donor, receiver, u\right)\left(b\right) = p\left(b\right) + u \cdot \left((\operatorname{if} b = receiver \operatorname{then} 1 \operatorname{else} 0) - (\operatorname{if} b = donor \operatorname{then} 1 \operatorname{else} 0)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transfer u adds u to the receiver and subtracts u from the donor. All other original coordinates are retained and the sum of coordinates is unchanged.

**Definition 1.9 (The native neighbor derivative sum).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathrm{Legal}\left(n\right) \to \mathbb{R},\; \forall b \in \mathrm{Legal}\left(n\right),\; \mathrm{gradient}\left(p, b\right) = \sum_{z: \{z: \mathrm{Legal}\left(n\right) \mid \mathrm{Adj}\left(\mathrm{legalWordGraph}\left(n\right), b, z\right)\}} ((\frac{p\left(\mathrm{val}\left(z\right)\right)}{p\left(b\right) + p\left(\mathrm{val}\left(z\right)\right)})^{2})$$

*Formalization.* `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.gradient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a positive vector, g_b(p) is the sum over all native neighbors c of (p_c/(p_b+p_c))^2. The derivative of a donor-to-receiver transfer is g_receiver-g_donor.

**Theorem 1.10 (A violated insertion forces a feasible improvement).**

$$\forall n \in \mathbb{N},\; \forall epsilon \in \mathbb{R},\; \forall p \in \mathrm{Legal}\left(n\right) \to \mathbb{R},\; ((1 \le n) \land ((0 < epsilon) \land ((p \in \mathrm{epsilonSimplex}\left(n, epsilon\right)) \land (\neg (\mathrm{InsertionBounds}\left(n, p\right)))))) \Rightarrow (\exists donor \in \mathrm{Legal}\left(n\right),\; \exists receiver \in \mathrm{Legal}\left(n\right),\; (\mathrm{Adj}\left(\mathrm{legalWordGraph}\left(n\right), donor, receiver\right)) \land ((p\left(receiver\right) < p\left(donor\right)) \land (\exists delta \in \mathbb{R},\; (0 < delta) \land ((delta < p\left(donor\right) - epsilon) \land (\forall u \in \mathbb{R},\; ((0 < u) \land (u < delta)) \Rightarrow ((\mathrm{transfer}\left(p, donor, receiver, u\right) \in \mathrm{epsilonSimplex}\left(n, epsilon\right)) \land (\mathrm{objective}\left(n, p\right) < \mathrm{objective}\left(n, \mathrm{transfer}\left(p, donor, receiver, u\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.improving_transfer_of_bad_insertion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n>=1, epsilon>0 and p in C_epsilon violating at least one insertion inequality, there exist an original adjacent donor and receiver with p_receiver<p_donor and a radius 0<delta<p_donor-epsilon. For every 0<u<delta the actual transfer belongs to C_epsilon and strictly increases Phi_n. The selected edge need not be the initially witnessed violation.

If an upper bound fails, select the largest upward ratio over the entire original finite edge set. Inserting i pairs every upper neighbor other than x with a lower neighbor still admitting i. Each paired gradient term is no larger at the upper endpoint; all leftover lower terms are nonnegative. The edge term is strictly negative, so transferring from upper to lower improves the objective.

After all upper bounds hold, select the smallest upward ratio in a violating direction i. The paired terms now favor the upper endpoint. Every leftover lower neighbor is a legal insertion at a neighboring position j, and its square share is at most 1/4. Their number is at most d_i. Thus g_upper-g_lower is at least (p_lower-p_upper)/(p_lower+p_upper)-d_i/4, strictly positive below q_i. Transfer from lower to upper. In both branches the donor has strict slack even if the receiver equals epsilon. The verified real derivative gives an actual positive feasible radius and strict objective increase.

The complete-word and path-independent-set domain is the classical Fibonacci cube of Hsu and Codara--D'Antona. The formal theorem proves both extremal-ratio branches on the complete native edge set. Finite compactness and scalar calculus are standard tools.

**Theorem 1.11 (The constrained maximum satisfies every insertion bound).**

$$\forall n \in \mathbb{N},\; \forall epsilon \in \mathbb{R},\; ((1 \le n) \land ((0 < epsilon) \land (epsilon \le \frac{1}{\mathrm{card}\left(\mathrm{Legal}\left(n\right)\right)}))) \Rightarrow (\exists p \in \mathrm{Legal}\left(n\right) \to \mathbb{R},\; (p \in \mathrm{epsilonSimplex}\left(n, epsilon\right)) \land ((\mathrm{IsMaxOn}\left(\mathrm{objective}\left(n\right), \mathrm{epsilonSimplex}\left(n, epsilon\right), p\right)) \land (\mathrm{InsertionBounds}\left(n, p\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.exists_constrained_optimizer_with_insertion_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n>=1 and 0<epsilon<=1/M there exists p in the entire C_epsilon maximizing the actual unordered-edge harmonic objective and satisfying q_i*p_lower<=p_upper<=p_lower at every original insertion. Compactness and continuity give a maximum. A violating insertion would give the strict feasible improvement just established, contradicting that maximum.

This is a constrained positive-simplex result. It does not establish full-simplex uniqueness, remove all active epsilon constraints, certify zero-coordinate competitors, construct a stationary probability law, or identify a geometric optimizer with any original integer maximizer. The full Robin obligation for all integers above 5040 and its fixed signed cofinal witness condition remain separate.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.InsertionBounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.Near`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.epsilonSimplex`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.exists_constrained_optimizer_with_insertion_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.gradient`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.harmonic`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.improving_transfer_of_bad_insertion`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.insertionLower`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.objective`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.positionDegree`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.transfer`
- Dependency: [D5/S3/Combinatorics/Graph/LegalWords/EdgeCount](EdgeCount.md)
