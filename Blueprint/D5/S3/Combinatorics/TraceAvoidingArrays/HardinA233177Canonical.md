# Canonical pair patterns on a finite linear order

## Abstract

First-appearance representatives and exact complementary-pair colour fibres.

A canonical word introduces smaller labels before larger labels. The cell order is an explicit parameter. The existence proof minimizes the relabelling orbit in lexicographic order; exchanging an out-of-order label with an absent smaller label would contradict minimality. Induction on cells proves uniqueness from equality of label fibres.

**Definition 1.1 (Canonical words).**

$$\forall (C: \operatorname{Type}), ([\operatorname{LT}\left(C\right)], \forall (k: \operatorname{Nat}), (\forall (P: C \to \operatorname{Fin}\left(k\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{Canonical}\left(P\right) = (\forall (i: C), (\forall (b: \operatorname{Fin}\left(k\right)), ((b < P\left(i\right)) \Rightarrow (\exists (j: C), ((j < i) \land (P\left(j\right) = b)))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.Canonical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Canonical words.

**Theorem 1.2 (A unique representative in each orbit).**

$$\forall (C: \operatorname{Type}), ([\operatorname{Fintype}\left(C\right)], [\operatorname{LinearOrder}\left(C\right)], \forall (k: \operatorname{Nat}), (\forall (P: C \to \operatorname{Fin}\left(k\right)), (\exists! (Q: C \to \operatorname{Fin}\left(k\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{Canonical}\left(Q\right)) \land (\exists (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(k\right)\right)), (Q = \operatorname{Function}.\operatorname{comp}\left(e, P\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.canonical_exists_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unique representative in each orbit.

**Definition 1.3 (Individual-colour normalization).**

$$\forall (C: \operatorname{Type}), ([\operatorname{LT}\left(C\right)], \forall (f: C \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{Normal}\left(f\right) = (\forall (i: C), ((((f\left(i\right) = (2: \operatorname{Fin}\left(6\right))) \lor ((f\left(i\right) = (3: \operatorname{Fin}\left(6\right))) \lor (f\left(i\right) = (4: \operatorname{Fin}\left(6\right))))) \Rightarrow (\exists (j: C), ((j < i) \land (f\left(j\right) = (1: \operatorname{Fin}\left(6\right)))))) \land ((f\left(i\right) = (3: \operatorname{Fin}\left(6\right))) \Rightarrow (\exists (j: C), ((j < i) \land (f\left(j\right) = (2: \operatorname{Fin}\left(6\right))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.Normal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Individual-colour normalization.

**Definition 1.4 (Fixed side at each first occurrence).**

$$\forall (C: \operatorname{Type}), ([\operatorname{LT}\left(C\right)], \forall (f: C \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{FirstSides}\left(f\right) = (\forall (i: C), ((\forall (j: C), ((j < i) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(f\left(j\right)\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(f\left(i\right)\right)))) \Rightarrow (\operatorname{Fin}.\operatorname{val}\left(f\left(i\right)\right) = \operatorname{Fin}.\operatorname{val}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(f\left(i\right)\right)\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.FirstSides` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fixed side at each first occurrence.

**Theorem 1.5 (Normalization is canonical form with fixed first sides).**

$$\forall (C: \operatorname{Type}), ([\operatorname{Fintype}\left(C\right)], [\operatorname{LinearOrder}\left(C\right)], \forall (z: C), ((\forall (i: C), (z \le i)) \Rightarrow (\forall (f: C \to \operatorname{Fin}\left(6\right)), ((f\left(z\right) = (0: \operatorname{Fin}\left(6\right))) \Rightarrow ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{Normal}\left(f\right)) \Leftrightarrow ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{Canonical}\left(\operatorname{Function}.\operatorname{comp}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}, f\right)\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{FirstSides}\left(f\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.normalization_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalization is canonical form with fixed first sides.

**Definition 1.6 (Individual-colour lifts of a fixed pair pattern).**

$$\forall (C: \operatorname{Type}), ([\operatorname{LT}\left(C\right)], \forall (P: C \to \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{Fibre}\left(P\right) = \{f: C \to \operatorname{Fin}\left(6\right) // ((\forall (i: C), (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(f\left(i\right)\right) = P\left(i\right))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{FirstSides}\left(f\right)))\}))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.Fibre` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Individual-colour lifts of a fixed pair pattern.

**Theorem 1.7 (Exact number of lifts).**

$$\forall (C: \operatorname{Type}), ([\operatorname{Fintype}\left(C\right)], [\operatorname{LinearOrder}\left(C\right)], \forall (P: C \to \operatorname{Fin}\left(3\right)), (\operatorname{Nat}.\operatorname{card}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{Fibre}\left(P\right)\right) = 2^{(\operatorname{Fintype}.\operatorname{card}\left(C\right)) - (\operatorname{Nat}.\operatorname{card}\left(\operatorname{Set}.\operatorname{range}\left(P\right)\right))}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.fibre_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact number of lifts.

**Theorem 1.8 (Six patterns per canonical representative).**

$$\forall (C: \operatorname{Type}), ([\operatorname{Fintype}\left(C\right)], [\operatorname{LinearOrder}\left(C\right)], \forall (S: \left(C \to \operatorname{Fin}\left(3\right)\right) \to \operatorname{Prop}), ((\forall (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), (\forall (P: C \to \operatorname{Fin}\left(3\right)), ((S\left(\operatorname{Function}.\operatorname{comp}\left(e, P\right)\right)) \Leftrightarrow (S\left(P\right))))) \Rightarrow ((\forall (P: C \to \operatorname{Fin}\left(3\right)), ((S\left(P\right)) \Rightarrow (\exists (i: C), (\exists (j: C), (P\left(i\right) \ne P\left(j\right)))))) \Rightarrow (\operatorname{Nat}.\operatorname{card}\left(\{P: C \to \operatorname{Fin}\left(3\right) // (S\left(P\right))\}\right) = (6) \cdot (\operatorname{Nat}.\operatorname{card}\left(\{P: C \to \operatorname{Fin}\left(3\right) // ((S\left(P\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{Canonical}\left(P\right)))\}\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.canonical_pattern_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Six patterns per canonical representative.

**Theorem 1.9 (Weighted canonical-pattern count).**

$$\forall (C: \operatorname{Type}), ([\operatorname{Fintype}\left(C\right)], [\operatorname{LinearOrder}\left(C\right)], \forall (z: C), ((\forall (i: C), (z \le i)) \Rightarrow (\forall (S: \left(C \to \operatorname{Fin}\left(3\right)\right) \to \operatorname{Prop}), (\operatorname{Nat}.\operatorname{card}\left(\{f: C \to \operatorname{Fin}\left(6\right) // ((S\left(\operatorname{Function}.\operatorname{comp}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}, f\right)\right)) \land ((f\left(z\right) = (0: \operatorname{Fin}\left(6\right))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{Normal}\left(f\right))))\}\right) = \operatorname{Finset}.\operatorname{sum}\left((\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\{P: C \to \operatorname{Fin}\left(3\right) // ((S\left(P\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{Canonical}\left(P\right)))\}\right)), (\lambda (P: \{P: C \to \operatorname{Fin}\left(3\right) // ((S\left(P\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{Canonical}\left(P\right)))\}) \mapsto 2^{(\operatorname{Fintype}.\operatorname{card}\left(C\right)) - (\operatorname{Nat}.\operatorname{card}\left(\operatorname{Set}.\operatorname{range}\left(\operatorname{Subtype}.\operatorname{val}\left(P\right)\right)\right))})\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.normalized_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weighted canonical-pattern count.

The complementary pairs are the fibres {0,5}, {1,4}, {2,3} of D5.S3.Observer.Separation.BooleanRankThreeK4.beta. A private proved equivalence sends a colour to its pair and the Boolean test 3 <= colour.val. Fixing the smaller colour at the first occurrence leaves one independent Boolean choice at every other cell. First occurrences are in bijection with the used labels. A permutation of three labels is determined by its values on two different labels. These statements concern finite words and do not assert the four-row ladder recurrence.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.Canonical`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.Fibre`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.FirstSides`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.Normal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.canonical_exists_unique`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.canonical_pattern_card`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.fibre_card`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.normalization_iff`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.normalized_card`
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
