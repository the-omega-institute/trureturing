# Critical opposite floors and a mixed six-valent star

## Abstract

A six-occurrence critical edge has strict angle-sum margins on both continuous faces, allowing two transition occurrences.

I is an arbitrary finite type of cardinality six. The five functions y,z,o,v,w:I -> Real retain every local occurrence. The target coordinate is shared. At each occurrence the order is (12,13,14,34,24,23); o is opposite the target and y,z,v,w are its four neighbours. All five coordinates lie in [1,2]. ThreeSmall means at least three of the four neighbours are at most 5/4, expressed as the four possible conjunctions.

good is a finite subset of I with at least four members. At every good occurrence all four neighbours are at most 5/4 and o is at least 4/3. No equality of the target and opposite, no prescribed angle and no angle-sum inequality is a hypothesis. AngleSum(a,y,z,o,v,w) below abbreviates the sum over i:I of arccos(cosine(a,y(i),z(i),o(i),v(i),w(i))). cosine is the original six-variable expression from FourCycleEnvelopes, not a free function.

Define beta=arccos(49/sqrt(6534)), gamma=arccos(43/99), and margin=min(2pi-6arccos(4/7),4gamma+2beta-2pi). These are exactly the three definitions in the paired Lean source.

**Theorem 1.1 (Both boundary sums have the same positive margin).**

$$\forall I \in Type, y \in I \to Real, z \in I \to Real, o \in I \to Real, v \in I \to Real, w \in I \to Real, good \in Finset\left(I\right),\; \left(Fintype\left(I\right) \land \left(Fintype.card\left(I\right) = 6 \land \left(4 \le Finset.card\left(good\right) \land \left(\left(\forall i \in I,\; y\left(i\right) \in Icc\left(1, 2\right) \land \left(z\left(i\right) \in Icc\left(1, 2\right) \land \left(o\left(i\right) \in Icc\left(1, 2\right) \land \left(v\left(i\right) \in Icc\left(1, 2\right) \land w\left(i\right) \in Icc\left(1, 2\right)\right)\right)\right)\right) \land \left(\left(\forall i \in I,\; ThreeSmall\left(y\left(i\right), z\left(i\right), v\left(i\right), w\left(i\right)\right)\right) \land \left(\forall i \in I,\; i \in good \Rightarrow \left(y\left(i\right) \le \frac{5}{4} \land \left(z\left(i\right) \le \frac{5}{4} \land \left(v\left(i\right) \le \frac{5}{4} \land \left(w\left(i\right) \le \frac{5}{4} \land \frac{4}{3} \le o\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(0 < margin \land \left(AngleSum\left(\frac{4}{3}, y, z, o, v, w\right) \le sub\left(mul\left(2, pi\right), margin\right) \land add\left(mul\left(2, pi\right), margin\right) \le AngleSum\left(2, y, z, o, v, w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/CriticalTransitionStar.critical_transition_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reuse the derivative-based mixed comparison from the single analytic owner. The lower target 4/3 gives cosine at least 4/7. At target 2 the four possible three-small-neighbour endpoints each give squared cosine 2401/6534. Four small neighbours and opposite floor 4/3 give exactly 43/99. Denominator positivity and square-root comparison are proved within the source.

For gamma in [0,pi/2], cos(2gamma)=-6103/9801. The positive square comparison (6103/9801)^2-2401/6534=3896615/192119202 proves 2gamma>pi-beta. This gives 4gamma+2beta>2pi. The lower gap follows from 4/7>cos(pi/3). Summing beta plus the good-occurrence increment gamma-beta, and using card(good)>=4, gives the actual six-occurrence upper-face bound. It is not a theorem with the desired budget assumed.

The quantified functions vary over continuous faces. Pullbacks of one shared global length vector are included among these functions; the source does not construct the global incidence carrier or prove manifold links, co-volume existence or the full CFMP conjecture. The ordinary application uses favourable opposites of the same degree class, so it is preserved by unbranched covers even when global edge identities split. The statement itself does not certify the cover construction or its geometric realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/CriticalTransitionStar.critical_transition_star`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
