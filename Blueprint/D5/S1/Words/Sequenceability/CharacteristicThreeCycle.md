# Characteristic-three finite-field cycle

## Abstract

One finite-field orbit inventories its vertices and directed differences exactly.

Write U for the units of K and F for ZMod 3. The function ite is one when its condition holds and zero otherwise. Unit coordinates in additive expressions are coerced to K. The map iterate(f,n,z) is the actual n-fold iterate.

**Definition 1.1 (The phase and row update).**

$$\forall (K:\operatorname{Type}),[\operatorname{Field}(K)]\forall (a:K^{\times}),\forall (z:K^{\times}\times \operatorname{ZMod}(3)),\operatorname{step}(a,z)=(a\cdot\operatorname{fst}(z),-\operatorname{snd}(z)+\operatorname{ite}(a\cdot\operatorname{fst}(z)=1,1,0))$$

*Formalization.* `D5/S1/Words/Sequenceability/CharacteristicThreeCycle.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Advance the multiplicative phase, reflect the row, and add one exactly on wrap.

**Definition 1.2 (The additive vertex).**

$$\forall (K:\operatorname{Type}),[\operatorname{Field}(K)]\forall (z:K^{\times}\times \operatorname{ZMod}(3)),\operatorname{vertex}(z)=(\operatorname{fst}(z),\operatorname{snd}(z))$$

*Formalization.* `D5/S1/Words/Sequenceability/CharacteristicThreeCycle.vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertex map coerces the unit coordinate to the field and preserves the row.

**Definition 1.3 (The nonzero directed difference).**

$$\forall (K:\operatorname{Type}),[\operatorname{Field}(K)]\forall (a:K^{\times}),a\neq 1\Rightarrow \forall (z:K^{\times}\times \operatorname{ZMod}(3)),\operatorname{label}(a,z)=((a-1)\cdot\operatorname{fst}(z),\operatorname{snd}(z)+\operatorname{ite}(a\cdot\operatorname{fst}(z)=1,1,0))$$

*Formalization.* `D5/S1/Words/Sequenceability/CharacteristicThreeCycle.label` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A proof of a!=1 is an argument of the Lean definition and makes a-1 a unit. In characteristic three the row difference -2*t+q equals t+q.

**Theorem 1.4 (One complete orbit and its exact labels).**

$$\forall (K:\operatorname{Type}),[\operatorname{Field}(K)][\operatorname{Fintype}(K)][\operatorname{CharP}(K,3)]\operatorname{let} L=\operatorname{card}(K)-1;\exists (a:K^{\times}),a\neq 1\land \operatorname{orderOf}(a)=L\land 2\le L\land \operatorname{Even}(L)\land \exists (e:\operatorname{Equiv}(\operatorname{Fin}(3\cdot L),K^{\times}\times \operatorname{ZMod}(3))),(\forall (i:\operatorname{Fin}(3\cdot L)),\operatorname{e}(i)=\operatorname{iterate}(\operatorname{step}(a),\operatorname{val}(i),(1,0)))\land \operatorname{iterate}(\operatorname{step}(a),3\cdot L,(1,0))=(1,0)\land \operatorname{Bijective}(i\mapsto \operatorname{label}(a,\operatorname{e}(i)))\land \forall (z:K^{\times}\times \operatorname{ZMod}(3)),\operatorname{vertex}(\operatorname{step}(a,z))-\operatorname{vertex}(z)=\operatorname{vertex}(\operatorname{label}(a,z))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/CharacteristicThreeCycle.exists_cycle_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here M=3*L. The field and every finite characteristic-three extension remain in scope. Finite-field unit cyclicity supplies a of exact order L. Odd field cardinality makes L even and at least two, hence a-1 is nonzero. The powers below L biject onto the units. For i<L, the actual i-step orbit from (1,n) is (a^i,(-1)^i*n). One lap sends (1,n) to (1,n+1). Repeated laps construct the orbit equivalence e and three laps return to (1,0). Every directed label is successor minus current vertex, including every bridge and the closing edge. Multiplication by a-1 permutes the units and each row map t to t+q is a translation, proving the second bijection. Internal labels are ((a-1)*a^i,-2*(-1)^i*n); bridge labels are ((a-1)*a^(L-1),2*n+1). Their row slopes are nonzero in F. The bridge n=-1 closes the cycle. L=2 and a=-1 are included by this same proof.

## References

- Truth anchor: `D5/S1/Words/Sequenceability/CharacteristicThreeCycle.exists_cycle_inventory`
- Truth anchor: `D5/S1/Words/Sequenceability/CharacteristicThreeCycle.label`
- Truth anchor: `D5/S1/Words/Sequenceability/CharacteristicThreeCycle.step`
- Truth anchor: `D5/S1/Words/Sequenceability/CharacteristicThreeCycle.vertex`
