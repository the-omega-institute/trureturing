# Actual zero-cost normal quotient and marker descent

## Abstract

The zero set of the actual group cost is normal, and both the cost and arbitrary marker descend to its actual group quotient.

G is any genuine group in Type u with its displayed instance gG; it need not be commutative, countable, topological or finitely generated. U:G->G and c:G->G->R are total, so all costs are finite real numbers. A proof h of RawCost U c supplies nonnegativity, zero diagonal, and c(a*s,b*t)+c(a*U(s),b*U(t))+c(a*U(U(s)),b*U(U(t)))=3c(a,b)+3c(s,t) for all a,b,s,t. A proof hs supplies symmetry c(a,b)=c(b,a). Neither U(1)=1, marker multiplicativity, periodicity, a triangle inequality, normality, representative independence nor a Hilbert realization is assumed.

In the formulas Z=zeroSubgroup(h,hs) is the actual subgroup with carrier {z | c(z,1)=0}, Q=QuotientGroup(G,Z) is the actual group quotient, mk denotes its canonical map and Member(z,Z) means subgroup membership. The instance zeroNormal supplies the group structure on Q. All appearances of quotientMarker and quotientCost use these same h and hs; no independently chosen equivalence relation is substituted.

**Theorem 1.1 (The cost is its unit-based right difference).**

$$(\forall G: Type_{u}, (\forall gG: \operatorname{Group}\left(G\right), (\forall U: (G \to G), (\forall c: (G \to (G \to \mathbb{R})), (\forall h: \operatorname{RawCost}\left(U, c\right), (\forall a: G, (\forall b: G, \operatorname{c}\left(a, b\right) = \operatorname{c}\left((a \cdot \operatorname{inv}\left(b\right)), 1\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawGroupZeroQuotient.right_diff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply RawGroupZeroDrift.right_invariant at the actual inverse b inverse. This is a direct reuse of the right-shift theorem and requires no symmetry.

**Theorem 1.2 (The actual zero coset has constant unit cost).**

$$(\forall G: Type_{u}, (\forall gG: \operatorname{Group}\left(G\right), (\forall U: (G \to G), (\forall c: (G \to (G \to \mathbb{R})), (\forall h: \operatorname{RawCost}\left(U, c\right), (\forall hs: (\forall a: G, (\forall b: G, \operatorname{c}\left(a, b\right) = \operatorname{c}\left(b, a\right))), (\forall x: G, (\forall z: G, (\operatorname{Member}\left(z, \operatorname{zeroSubgroup}\left(h, hs\right)\right) \Rightarrow \operatorname{c}\left((x \cdot z), 1\right) = \operatorname{c}\left(x, 1\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawGroupZeroQuotient.zero_coset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set F(t)=c(x*t,1) on the actual subgroup Z and m=inf(range F). This range is nonempty and bounded below by zero. For each n define T_n(w)=U^n(w)*(U^n(1)) inverse in Z: sync_iter and right_diff show its unit cost is zero. The full balance law at (x*s,1,w,1) becomes F(s*w)+F(s*T_1(w))+F(s*T_2(w))=3F(s). Every term belongs to the same coset and is at least m, hence F(s*w)<=3F(s)-2m. For fixed s and arbitrary t, take the actual element w=t inverse times s. Then (F(s)+2m)/3 is a lower bound for range F, yielding F(s)<=m. The infimum property gives the reverse inequality; compare s with 1. This establishes constancy using the balance law, without an assumed triangle inequality.

**Theorem 1.3 (Both zero representatives may change independently).**

$$(\forall G: Type_{u}, (\forall gG: \operatorname{Group}\left(G\right), (\forall U: (G \to G), (\forall c: (G \to (G \to \mathbb{R})), (\forall h: \operatorname{RawCost}\left(U, c\right), (\forall hs: (\forall a: G, (\forall b: G, \operatorname{c}\left(a, b\right) = \operatorname{c}\left(b, a\right))), (\forall a: G, (\forall b: G, (\forall z: G, (\forall w: G, (\operatorname{Member}\left(z, \operatorname{zeroSubgroup}\left(h, hs\right)\right) \Rightarrow (\operatorname{Member}\left(w, \operatorname{zeroSubgroup}\left(h, hs\right)\right) \Rightarrow \operatorname{c}\left((a \cdot z), (b \cdot w)\right) = \operatorname{c}\left(a, b\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawGroupZeroQuotient.independent_representatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The subgroup exists because single gives c(x*y,1)<=3(c(x,1)+c(y,1)) and inverse_budget preserves zero unit cost. Its normality follows by applying balance to background (a,a), increments (z,1): the nonnegative first term c(a*z,a) is zero, and right_diff identifies the conjugate cost. Thus b*(z*w inverse)*b inverse belongs to Z. The actual group identity (a*z)*(b*w) inverse=(a*b inverse)*(b*(z*w inverse)*b inverse), followed by zero_coset, proves the displayed equality.

**Theorem 1.4 (Zero cost is equality in the actual quotient).**

$$(\forall G: Type_{u}, (\forall gG: \operatorname{Group}\left(G\right), (\forall U: (G \to G), (\forall c: (G \to (G \to \mathbb{R})), (\forall h: \operatorname{RawCost}\left(U, c\right), (\forall hs: (\forall a: G, (\forall b: G, \operatorname{c}\left(a, b\right) = \operatorname{c}\left(b, a\right))), (\forall a: G, (\forall b: G, (\operatorname{c}\left(a, b\right) = 0 \Leftrightarrow \operatorname{mk}\left(a\right) = \operatorname{mk}\left(b\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawGroupZeroQuotient.zero_iff_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's QuotientGroup.eq_iff_div_mem identifies equality of quotient classes with membership of the actual difference. The carrier definition and right_diff identify that membership with zero cost.

**Theorem 1.5 (The total marker preserves quotient classes).**

$$(\forall G: Type_{u}, (\forall gG: \operatorname{Group}\left(G\right), (\forall U: (G \to G), (\forall c: (G \to (G \to \mathbb{R})), (\forall h: \operatorname{RawCost}\left(U, c\right), (\forall hs: (\forall a: G, (\forall b: G, \operatorname{c}\left(a, b\right) = \operatorname{c}\left(b, a\right))), (\forall a: G, (\forall b: G, (\operatorname{mk}\left(a\right) = \operatorname{mk}\left(b\right) \Rightarrow \operatorname{mk}\left(\operatorname{U}\left(a\right)\right) = \operatorname{mk}\left(\operatorname{U}\left(b\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawGroupZeroQuotient.marker_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply sync_iter at one step, c(U(a),U(b))=c(a,b), and zero_iff_class in both directions. No point equality of representatives or marker homomorphism is inferred.

**Theorem 1.6 (The descended marker has the exact representative equation).**

$$(\forall G: Type_{u}, (\forall gG: \operatorname{Group}\left(G\right), (\forall U: (G \to G), (\forall c: (G \to (G \to \mathbb{R})), (\forall h: \operatorname{RawCost}\left(U, c\right), (\forall hs: (\forall a: G, (\forall b: G, \operatorname{c}\left(a, b\right) = \operatorname{c}\left(b, a\right))), (\forall a: G, \operatorname{quotientMarker}\left(h, hs, \operatorname{mk}\left(a\right)\right) = \operatorname{mk}\left(\operatorname{U}\left(a\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawGroupZeroQuotient.quotientMarker_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

quotientMarker is Quotient.lift of a maps to mk(U(a)); marker_classes proves representative independence. It is total on the actual quotient Q, and the displayed equation is definitional.

**Theorem 1.7 (The descended cost has the exact representative equation).**

$$(\forall G: Type_{u}, (\forall gG: \operatorname{Group}\left(G\right), (\forall U: (G \to G), (\forall c: (G \to (G \to \mathbb{R})), (\forall h: \operatorname{RawCost}\left(U, c\right), (\forall hs: (\forall a: G, (\forall b: G, \operatorname{c}\left(a, b\right) = \operatorname{c}\left(b, a\right))), (\forall a: G, (\forall b: G, \operatorname{quotientCost}\left(h, hs, \operatorname{mk}\left(a\right), \operatorname{mk}\left(b\right)\right) = \operatorname{c}\left(a, b\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawGroupZeroQuotient.quotientCost_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

quotientCost is Quotient.lift2 of the original c. For related a,a prime and b,b prime, the actual elements a inverse times a prime and b inverse times b prime lie in Z. independent_representatives therefore supplies the required equality. The representative equation is definitional.

**Theorem 1.8 (The complete four-variable relation survives descent).**

$$(\forall G: Type_{u}, (\forall gG: \operatorname{Group}\left(G\right), (\forall U: (G \to G), (\forall c: (G \to (G \to \mathbb{R})), (\forall h: \operatorname{RawCost}\left(U, c\right), (\forall hs: (\forall a: G, (\forall b: G, \operatorname{c}\left(a, b\right) = \operatorname{c}\left(b, a\right))), \operatorname{RawCost}\left(\operatorname{quotientMarker}\left(h, hs\right), \operatorname{quotientCost}\left(h, hs\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawGroupZeroQuotient.quotient_raw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quotient induction on both cost arguments proves nonnegativity, induction on one argument proves zero diagonal, and induction on all four arguments transports the entire balance identity. All operations are those of the actual normal subgroup quotient; the same total descended marker occurs throughout.

**Theorem 1.9 (The descended cost is symmetric).**

$$(\forall G: Type_{u}, (\forall gG: \operatorname{Group}\left(G\right), (\forall U: (G \to G), (\forall c: (G \to (G \to \mathbb{R})), (\forall h: \operatorname{RawCost}\left(U, c\right), (\forall hs: (\forall a: G, (\forall b: G, \operatorname{c}\left(a, b\right) = \operatorname{c}\left(b, a\right))), (\forall a: \operatorname{QuotientGroup}\left(G, \operatorname{zeroSubgroup}\left(h, hs\right)\right), (\forall b: \operatorname{QuotientGroup}\left(G, \operatorname{zeroSubgroup}\left(h, hs\right)\right), \operatorname{quotientCost}\left(h, hs, a, b\right) = \operatorname{quotientCost}\left(h, hs, b, a\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawGroupZeroQuotient.quotient_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the two actual quotient classes reduces the statement to the original symmetry hs.

**Theorem 1.10 (Complete actual-group zero quotient theorem).**

$$(\forall G: Type_{u}, (\forall gG: \operatorname{Group}\left(G\right), (\forall U: (G \to G), (\forall c: (G \to (G \to \mathbb{R})), (\forall h: \operatorname{RawCost}\left(U, c\right), (\forall hs: (\forall a: G, (\forall b: G, \operatorname{c}\left(a, b\right) = \operatorname{c}\left(b, a\right))), (\exists f: (G \to \mathbb{R}), ((\forall g: G, 0 \leq \operatorname{f}\left(g\right)) \land ((\forall g: G, \operatorname{f}\left(g\right) = \operatorname{c}\left(g, 1\right)) \land ((\forall a: G, (\forall b: G, \operatorname{c}\left(a, b\right) = \operatorname{f}\left((a \cdot \operatorname{inv}\left(b\right))\right))) \land (\operatorname{f}\left(1\right) = 0 \land ((\forall g: G, \operatorname{f}\left(\operatorname{inv}\left(g\right)\right) = \operatorname{f}\left(g\right)) \land ((\forall a: G, (\forall b: G, (\forall z: G, \operatorname{c}\left((a \cdot z), (b \cdot z)\right) = \operatorname{c}\left(a, b\right)))) \land (\exists Z: \operatorname{Subgroup}\left(G\right), ((\forall z: G, (\operatorname{Member}\left(z, Z\right) \Leftrightarrow \operatorname{f}\left(z\right) = 0)) \land (\exists hn: \operatorname{Normal}\left(Z\right), ((\forall a: G, (\forall b: G, (\forall z: G, (\forall w: G, (\operatorname{Member}\left(z, Z\right) \Rightarrow (\operatorname{Member}\left(w, Z\right) \Rightarrow \operatorname{c}\left((a \cdot z), (b \cdot w)\right) = \operatorname{c}\left(a, b\right))))))) \land ((\forall a: G, (\forall b: G, (\operatorname{mk}\left(a\right) = \operatorname{mk}\left(b\right) \Rightarrow \operatorname{mk}\left(\operatorname{U}\left(a\right)\right) = \operatorname{mk}\left(\operatorname{U}\left(b\right)\right)))) \land (\exists V: (\operatorname{QuotientGroup}\left(G, Z\right) \to \operatorname{QuotientGroup}\left(G, Z\right)), (\exists d: (\operatorname{QuotientGroup}\left(G, Z\right) \to (\operatorname{QuotientGroup}\left(G, Z\right) \to \mathbb{R})), ((\forall a: G, (\forall b: G, \operatorname{d}\left(\operatorname{mk}\left(a\right), \operatorname{mk}\left(b\right)\right) = \operatorname{c}\left(a, b\right))) \land ((\forall a: G, \operatorname{V}\left(\operatorname{mk}\left(a\right)\right) = \operatorname{mk}\left(\operatorname{U}\left(a\right)\right)) \land (\operatorname{RawCost}\left(V, d\right) \land ((\forall a: \operatorname{QuotientGroup}\left(G, Z\right), (\forall b: \operatorname{QuotientGroup}\left(G, Z\right), \operatorname{d}\left(a, b\right) = \operatorname{d}\left(b, a\right))) \land (\forall a: G, (\forall b: G, (\operatorname{c}\left(a, b\right) = 0 \Leftrightarrow \operatorname{mk}\left(a\right) = \operatorname{mk}\left(b\right))))))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawGroupZeroQuotient.group19_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose f(g)=c(g,1), Z=zeroSubgroup(h,hs), its proved normality instance hn, V=quotientMarker(h,hs) and d=quotientCost(h,hs). This single theorem packages every displayed clause on the original arbitrary group. f is finite and nonnegative because it is real valued and h supplies its sign. hn supplies the genuine group structure used in every following quotient expression.

## Source and scope

This is Lemma 19.2 of AURIC_C133_UNANCHORED_MARKER_FINITE_POSITIVITY_BRIDGE, under Definition 19.1. The function clauses and simultaneous right invariance give (19.2) and (19.5); zeroSubgroup and zeroNormal establish the actual zero set and normality; independent_representatives gives (19.3); marker_classes, the two lift equations, quotient_raw and quotient_symmetric give the full descent; zero_iff_class gives (19.4). The finite inequality (19.6), synchronized normalized marker images (19.7), coset averaging (19.8) and constancy (19.9) are used in the subgroup and zero_coset derivations.

The proof directly reuses RawGroupZeroDrift.right_invariant and inverse_budget, RawUnanchoredReplication.single and sync_iter, and Mathlib's conditional infima, actual subgroup and quotient operations. The new inference is the harmonic constancy argument on each actual zero coset and its use in independent representative descent. No literature novelty is claimed.

No negative-type theorem, global Hilbert space, affine phase action, minimal-span uniqueness, or complete 19.4 classification is supplied here. The arbitrary marker on G is not asserted to be a homomorphism. Mathematical quotient descent supplies no physical preparation, effect, event, instrument, joint operation, empirical realization or physical time interface.

## References

- Truth anchor: `D5/S3/Quantum/Completion/RawGroupZeroQuotient.group19_2`
- Truth anchor: `D5/S3/Quantum/Completion/RawGroupZeroQuotient.independent_representatives`
- Truth anchor: `D5/S3/Quantum/Completion/RawGroupZeroQuotient.marker_classes`
- Truth anchor: `D5/S3/Quantum/Completion/RawGroupZeroQuotient.quotientCost_mk`
- Truth anchor: `D5/S3/Quantum/Completion/RawGroupZeroQuotient.quotientMarker_mk`
- Truth anchor: `D5/S3/Quantum/Completion/RawGroupZeroQuotient.quotient_raw`
- Truth anchor: `D5/S3/Quantum/Completion/RawGroupZeroQuotient.quotient_symmetric`
- Truth anchor: `D5/S3/Quantum/Completion/RawGroupZeroQuotient.right_diff`
- Truth anchor: `D5/S3/Quantum/Completion/RawGroupZeroQuotient.zero_coset`
- Truth anchor: `D5/S3/Quantum/Completion/RawGroupZeroQuotient.zero_iff_class`
- Dependency: [D5/S3/Quantum/Completion/RawGroupZeroDrift](RawGroupZeroDrift.md)
