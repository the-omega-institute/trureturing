# Countable group zero-drift realization

## Abstract

A countable actual group closed under the marker is fixed before one common limit preserves every ordered comparison.

G is any group in Type u. U:G->G and c:G->G->R are total. RawCost means c(a,b)>=0, c(a,a)=0 and c(a*s,b*t)+c(a*U(s),b*U(t))+c(a*U(U(s)),b*U(U(t)))=3c(a,b)+3c(s,t) for every a,b,s,t. The group instances gG and gS displayed below supply the actual units, multiplication and inverses. No commutativity, countability or topology on G, marker homomorphism, U(1)=1, triangle inequality, Hilbert model, quotient or N5 premise is imposed.

**Theorem 1.1 (Raw group costs are right invariant).**

$$(\forall G: Type_{u}, (\forall gG: \operatorname{Group}\left(G\right), (\forall U: (G \to G), (\forall c: (G \to (G \to \mathbb{R})), (\operatorname{RawCost}\left(U, c\right) \Rightarrow (\forall a: G, (\forall b: G, (\forall z: G, \operatorname{c}\left((a \cdot z), (b \cdot z)\right) = \operatorname{c}\left(a, b\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawGroupZeroDrift.right_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Symmetry is absent. Fix a,b, put F(t)=c(a*t,b*t) and m=inf(range F). The range is nonempty and bounded below by zero. The full balance law at (a*t,b*t,w,w) gives F(t*w)<=3F(t)-2m. For each s, substituting w=t inverse times s makes the left side F(s) for every t. Thus (F(s)+2m)/3 is a lower bound for range F, so F(s)<=m; the converse follows from the infimum property. Hence F is constant. This infimum argument uses neither symmetry nor marker anchoring.

**Theorem 1.2 (Inversion preserves the unit budget).**

$$(\forall G: Type_{u}, (\forall gG: \operatorname{Group}\left(G\right), (\forall U: (G \to G), (\forall c: (G \to (G \to \mathbb{R})), (\operatorname{RawCost}\left(U, c\right) \Rightarrow ((\forall a: G, (\forall b: G, \operatorname{c}\left(a, b\right) = \operatorname{c}\left(b, a\right))) \Rightarrow (\forall x: G, \operatorname{c}\left(\operatorname{inv}\left(x\right), 1\right) = \operatorname{c}\left(x, 1\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawGroupZeroDrift.inverse_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply this module's right_invariant to (x inverse,1,x), then use the given symmetry. The inverse branch of group19_3 uses this equality on the actual coordinate groups.

**Theorem 1.3 (One actual countable group preserves the complete finite matrix).**

$$(\forall G: Type_{u}, (\forall gG: \operatorname{Group}\left(G\right), (\forall alpha: Type_{v}, (\forall hAlpha: \operatorname{Finite}\left(alpha\right), (\forall U: (G \to G), (\forall c: (G \to (G \to \mathbb{R})), (\operatorname{RawCost}\left(U, c\right) \Rightarrow ((\forall a: G, (\forall b: G, \operatorname{c}\left(a, b\right) = \operatorname{c}\left(b, a\right))) \Rightarrow (\forall f: (alpha \to G), (\exists S: Type_{u}, (\exists gS: \operatorname{Group}\left(S\right), (\exists hS: \operatorname{Countable}\left(S\right), (\exists V: (S \to S), (\exists d: (S \to (S \to \mathbb{R})), (\exists x: (alpha \to S), (\operatorname{RawCost}\left(V, d\right) \land ((\forall a: S, (\forall b: S, \operatorname{d}\left(a, b\right) = \operatorname{d}\left(b, a\right))) \land (\operatorname{d}\left(\operatorname{V}\left(1\right), 1\right) = 0 \land (\forall a: alpha, (\forall b: alpha, \operatorname{d}\left(\operatorname{x}\left(a\right), \operatorname{x}\left(b\right)\right) = \operatorname{c}\left(\operatorname{f}\left(a\right), \operatorname{f}\left(b\right)\right)))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawGroupZeroDrift.group19_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite indexing type alpha is arbitrary in Type v and f:alpha->G is arbitrary. Empty types, repeated labels, the unit label and zero costs are retained. The existential S lies in Type u, has the displayed genuine Group instance and Countable instance, and supports one total V, one total real-valued d and one source assignment x for all pairs. The equality d(V(1),1)=0 is a cost statement and asserts no object equality V(1)=1. The source assignment is not asserted to preserve multiplication, inverse, unit or marker.

## Actual carrier and one common limit

Word alpha has exactly five constructors: unit, source, mul, inv and mark. eval interprets every finite word in an actual group with an arbitrary total marker. wordGroup is the range of eval as a Subgroup: unit, multiplication and inverse closure are object-level facts before any limits. wordMarker stays in this subgroup using the mark constructor, and label uses the source constructor. Product G is the product over natural n of the actual coordinate group (Sigma(n+1)->G). Set W coordinatewise to arrayMarker U and X(a)(n)=gamma U (n+1) (f(a)). The fixed carrier S is wordGroup W X. Countability follows from Countable (Word alpha) and Set.countable_range; no countability of G is used.

raw_replication gives RawCost and the exact source matrix in every coordinate, together with omega_N=omega(U,c)/(n+1). Symmetry is transported by the finite sum. Word induction gives coordinate-independent finite budgets: B(unit)=0, B(source a)=3c(f(a),1)+3omega, B(mul s t)=3(B(s)+B(t)), B(inv s)=B(s), and B(mark s)=18B(s)+24omega. The inverse case uses inverse_budget on each actual coordinate group. The marker case uses the raw_replication estimate at replication size one. unit_compare bounds each ordered pair by 3(B(s)+B(t)).

The countable product of the intervals [0,3(B(s)+B(t))], indexed by all ordered pairs in this same S, is compact and supplies one convergent subsequence. Its limit d(s,t) exists simultaneously for every pair. All five entries of each balance identity use this common subsequence, as do symmetry and the diagonal. Nonnegative summands bound cost(V(1),1) by omega_N, which tends to zero. The exact coordinate source matrix has constant entries, so the same limit preserves every c(f(a),f(b)). The proof never takes independently chosen limits for different pairs and never adds inverse or marker closure after taking the limit.

## Source correspondence and boundaries

The source is AURIC_C133_UNANCHORED_MARKER_FINITE_POSITIVITY_BRIDGE, Lemma 19.3. Its finite-subset formulation is obtained by taking alpha to be that finite subtype and f its inclusion; this theorem also permits repeated and empty indexing. The word-range subgroup realizes the source's iterative marker-closed generated subgroup. The common compact-product subsequence supplies the source's common diagonal limit.

The implementation reuses RawUnanchoredReplication.gamma and its checked normalization, rather than identifying it with the paper's differently normalized displayed Gamma. It uses the sufficient marker budget 18B+24omega. It does not prove the paper's stronger displayed budget 3B+3omega or its separate displayed Gamma-unit budget. These intermediate differences leave the full existential conclusion and all its hypotheses intact. RawUnanchoredReplication.raw_zero_drift has a MulOneClass term carrier without inverse closure and is not used as a substitute for a genuine group.

RawUnanchoredReplication.raw_replication, single and unit_compare supply the replication and ordered-pair bounds. Mathlib supplies conditional infima, subgroup operations, countable ranges, compact products and IsCompact.tendsto_subseq. This construction claims no literature novelty.

Lemma 19.2's zero-cost quotient, normality and marker descent remain separate obligations. No 19.4 or 19.5 positivity, Hilbert representation, uniqueness or full classification follows here. Physical preparations, measurements, joint operations, reference systems, time operations and empirical realization require their own contracts. A finite comparison realization does not provide those structures.

## References

- Truth anchor: `D5/S3/Quantum/Completion/RawGroupZeroDrift.group19_3`
- Truth anchor: `D5/S3/Quantum/Completion/RawGroupZeroDrift.inverse_budget`
- Truth anchor: `D5/S3/Quantum/Completion/RawGroupZeroDrift.right_invariant`
- Dependency: [D5/S3/Quantum/Completion/RawUnanchoredReplication](RawUnanchoredReplication.md)
