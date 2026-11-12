# Fine slopes and residue directions

## Abstract

Residue coordinates give an all-pairs bijection preserving determinant-zero incidence.

**Theorem 1.1 (Equality of cross products is transported for every pair).**

$$\forall R \in \operatorname{Type}\left(\right),\; \forall K \in \operatorname{Type}\left(\right),\; [\operatorname{CommRing}\left(R\right)] [\operatorname{Field}\left(K\right)] \forall C \in \operatorname{ResidueCoordinates}\left(R, K\right),\; \forall S \in \operatorname{Type}\left(\right),\; [\operatorname{CommRing}\left(S\right)] \forall D \in \operatorname{ResidueCoordinates}\left(S, K\right),\; \forall v \in \operatorname{Prod}\left(R, R\right),\; \forall w \in \operatorname{Prod}\left(R, R\right),\; (\operatorname{mul}\left(\operatorname{fst}\left(v\right), \operatorname{snd}\left(w\right)\right) = \operatorname{mul}\left(\operatorname{fst}\left(w\right), \operatorname{snd}\left(v\right)\right)) \Leftrightarrow (\operatorname{mul}\left(\operatorname{fst}\left(\operatorname{determinantEquiv}\left(C, D, v\right)\right), \operatorname{snd}\left(\operatorname{determinantEquiv}\left(C, D, w\right)\right)\right) = \operatorname{mul}\left(\operatorname{fst}\left(\operatorname{determinantEquiv}\left(C, D, w\right)\right), \operatorname{snd}\left(\operatorname{determinantEquiv}\left(C, D, v\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Heisenberg/DeterminantCharts.determinantEquiv_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

R and S are commutative rings and K is a field, all in arbitrary universes. A ResidueCoordinates value supplies an equivalence code from its ring to K times K, a residue ring homomorphism res, and the laws res(x)=first(code(x)), code(0)=(0,0), IsUnit(x) iff res(x) is nonzero, and j(a)*x=j(a*res(x)), where j(a)=code inverse (0,a). These laws are explicit premises of this reusable theorem. The two coefficient-ring values used in the group construction prove all these laws directly.

Chart R K is the disjoint sum of pairs (u,t) with u a unit and t in R, pairs (s,u) with s in K and u a unit, and pairs (a,b) in K times K. Decode sends them respectively to (u,u*t), (u*j(s),u) and (j(a),j(b)). It is bijective: test whether the first coordinate is a unit, then whether the second is a unit. In the remaining case both coordinates are in the kernel of res and have unique j coordinates. Unit cancellation proves uniqueness within each chart; the two residue-zero tests separate the charts.

For two first-chart vectors incidence means equality of t. For two second-chart vectors it means equality of s. The first and second charts are never incident to each other. Between a first-chart vector with slope t and a third-chart vector (a,b), incidence is b=res(t)*a. Between a second-chart vector and a third-chart vector it is a=0. Every two third-chart vectors are incident because the ideal squares to zero. The reverse ordered cases have the same relation. These nine rules include zero and equal vectors.

Code identifies both coefficient carriers with K times K and both unit carriers with the subtype whose first coordinate is nonzero. Applying these equivalences to the charts produces the same normal-form carrier for R and S, with the same nine incidence rules. Composing the two normal forms gives determinantEquiv C D. The displayed cross-product equality is equivalent to determinant zero by subtracting the right side; no distant or determinant-unit relation is substituted.

## References

- Truth anchor: `D5/S3/FiniteGroups/Heisenberg/DeterminantCharts.determinantEquiv_preserves`
