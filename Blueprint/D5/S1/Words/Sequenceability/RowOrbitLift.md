# Affine row orbits and a characteristic-five lift

## Abstract

Affine row orbits give exact lifted cycles and differences over finite fields of characteristic five.

All universe levels, field structures and finite fields in the displayed quantifiers are included. Operations use the bound field structure f. The map rowReturn(r,c) sends h to c+r(h-c), where r is a unit. SameCycle is the orbit relation of the actual permutation under integer powers.

**Theorem 1.1 (Two affine row orbits).**

$$\forall K \in \operatorname{Type}\left(\right),\; \forall f \in \operatorname{Field}\left(K\right),\; \forall finite \in \operatorname{Finite}\left(K\right),\; \forall r \in \operatorname{Units}\left(K\right),\; \left(\forall z \in \operatorname{Units}\left(K\right),\; \exists n \in \operatorname{Nat}\left(\right),\; r^{n} = z\right) \Rightarrow \left(\forall c \in K,\; \forall a \in K,\; \forall b \in K,\; \operatorname{SameCycle}\left(\operatorname{rowReturn}\left(r, c\right), a, b\right) \Leftrightarrow \left(a = c \Leftrightarrow b = c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/RowOrbitLift.row_same_cycle_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every unit is a natural power of r, the center c is fixed and every other row belongs to one orbit. For a and b different from c, choose a power of r equal to (b-c)/(a-c). The n-th return is c+r^n(a-c), so that power sends a to b. Conversely, a permutation orbit meeting a fixed point contains only that point.

The state space is Fin(4) times K. Its actual vertices are vertex(i,h)=(column(i),h), where column=(1,2,4,3) in ZMod(5). The successor lift(r,c) sends (0,h),(1,h),(2,h) to (1,-h),(2,-h),(3,-h), respectively, and sends (3,h) to (0,-rh+(1-r)c). The first row initialRow(i,h) is h at phases 0 and 2 and -h at phases 1 and 3. The edgeLabel is vertex(lift(r,c)(v))-vertex(v), with coefficient one.

**Theorem 1.2 (Exact cycles and closing-edge inventory over every finite rowfield).**

$$\forall K \in \operatorname{Type}\left(\right),\; \forall f \in \operatorname{Field}\left(K\right),\; \forall finite \in \operatorname{Finite}\left(K\right),\; \forall char \in \operatorname{CharP}\left(K, 5\right),\; \forall c \in K,\; \exists r \in \operatorname{Units}\left(K\right),\; \operatorname{coe}\left(r\right) + 1 \ne 0 \land \left(\left(\forall v \in \operatorname{Fin}\left(4\right) \times K,\; \forall w \in \operatorname{Fin}\left(4\right) \times K,\; \operatorname{SameCycle}\left(\operatorname{lift}\left(r, c\right), v, w\right) \Leftrightarrow \left(\operatorname{initialRow}\left(v\right) = c \Leftrightarrow \operatorname{initialRow}\left(w\right) = c\right)\right) \land \left(\operatorname{BijOn}\left(\operatorname{edgeLabel}\left(r, c\right), \operatorname{univ}\left(\right), \{v:\operatorname{ZMod}\left(5\right) \times K\mid\operatorname{fst}\left(v\right) \ne 0\}\right) \land \left(\operatorname{BijOn}\left(\operatorname{vertex}\left(\right), \operatorname{univ}\left(\right), \{v:\operatorname{ZMod}\left(5\right) \times K\mid\operatorname{fst}\left(v\right) \ne 0\}\right) \land \left(\forall h \in K,\; \left(\operatorname{lift}\left(r, c\right)^{4}\right)\left((0,h)\right) = (0,\operatorname{rowReturn}\left(r, c\right)\left(h\right))\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/RowOrbitLift.exists_characteristic_five_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a generator of the finite field's unit group. It cannot be -1: powers of -1 are 1 or -1, whereas 2 is neither in characteristic five. Thus r+1 is nonzero. Four successor steps return to phase zero by rowReturn(r,c). The preceding orbit theorem and the first three successor steps prove the exact SameCycle criterion for arbitrary states, including the closing edge.

The first coordinates of the four edge labels are 1,2,4,3. Their row coordinates are -2h,-2h,-2h and -(r+1)h+(1-r)c. Each row map is bijective, so BijOn means that every vector with nonzero first coordinate occurs exactly once as a label. The separate vertex BijOn states the same exact inventory for vertices. This covers arbitrary finite extensions in characteristic five; no bound on their degree is imposed.

These are the row-lift ingredients for the dependent-hole construction. A relative detour still requires the three-cut reconnection. The prime seed, the different two-cut construction for primes at least seven, dimension induction and transport to the original vector-space coordinates are not asserted here.

## References

- Truth anchor: `D5/S1/Words/Sequenceability/RowOrbitLift.exists_characteristic_five_lift`
- Truth anchor: `D5/S1/Words/Sequenceability/RowOrbitLift.row_same_cycle_iff`
