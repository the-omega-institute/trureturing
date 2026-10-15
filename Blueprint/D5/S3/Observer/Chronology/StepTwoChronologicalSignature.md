# Step-Two Chronological Signature

## Abstract

Step-two signatures obey Chen concatenation and the degree-two BCH law.

**Definition 1.1 (Step-two signature).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.StepTwoSignature`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.StepTwoSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A step-two signature stores degree one together with twice degree two, so the construction requires no division by two.

**Definition 1.2 (Single-event signature).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.eventSignature`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.eventSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One event contributes its algebra value at degree one and its square to doubled degree two.

**Definition 1.3 (Chronological word signature).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronologicalSignature`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronologicalSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signature of a list composes single-event signatures from left to right in operational chronology.

**Theorem 1.4 (Step-two Chen identity).**

$$\forall f, P, S, \operatorname{chronologicalSignature}(f, \operatorname{append}(P, S)) = \operatorname{chronologicalSignature}(f, P) \cdot \operatorname{chronologicalSignature}(f, S).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronological_signature_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signature of an earlier word followed by a later word is their chronological signature product.

**Theorem 1.5 (Degree one forgets chronology).**

$$\forall f, L, \operatorname{degreeOne}(\operatorname{chronologicalSignature}(f, L)) = \operatorname{sum}(\operatorname{map}(f, L)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronological_signature_degree_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Degree one is the ordinary sum of all observed event values and is therefore insensitive to their order.

**Definition 1.6 (Doubled degree-two Magnus coordinate).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubledMagnusDegreeTwo`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubledMagnusDegreeTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtracting the square of degree one from doubled degree two extracts the doubled logarithmic coordinate.

**Theorem 1.7 (Degree-two BCH law).**

$$\forall a, b, \operatorname{doubledMagnusDegreeTwo}(a \cdot b) = \operatorname{doubledMagnusDegreeTwo}(a) + \operatorname{doubledMagnusDegreeTwo}(b) + \operatorname{commutator}(\operatorname{degreeOne}(a), \operatorname{degreeOne}(b)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_degree_two_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithmic coordinate of a product is the sum of the two coordinates plus the commutator of their degree-one parts.

**Theorem 1.8 (Chronological BCH append law).**

$$\begin{gathered}\forall f, P, S:\\{}\operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, \operatorname{append}(P, S))) = \operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, P)) + \operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, S)) + \operatorname{commutator}(\operatorname{degreeOne}(\operatorname{chronologicalSignature}(f, P)), \operatorname{degreeOne}(\operatorname{chronologicalSignature}(f, S))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_degree_two_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining Chen concatenation with the logarithmic coordinate gives the step-two BCH formula for two event words.

An integer lattice application uses finite lists of LatticeWalkNearMaximalArea.Step: E, W, N and S mean right, left, up and down. All coordinates are integers, the walk starts at the origin, and the words have no region or path restrictions. With matrix indices 0, 1 and 2, let e_ij be the matrix unit and let T_ij(t) = I + t e_ij. These are the integer special-linear transvections supplied by Matrix.SpecialLinearGroup.transvection. Assign E and W to T_01(1) and T_01(-1), and N and S to T_12(1) and T_12(-1). The matrix signature sigma(w) is the ordered product of these letters, with earlier steps on the left; the empty word has signature I.

Write H(x,y,z) for the upper triangular matrix with rows (1,x,z), (0,1,y), (0,0,1). Its transvection factorization is T_01(x) T_12(y) T_02(z-xy). Every word signature has this form, and x(w), y(w), z(w) are its entries 01, 12, 02. Thus x and y are the signed horizontal and vertical displacements. Matrix multiplication gives H(x,y,z) H(a,b,c) = H(x+a,y+b,z+c+xb), and concatenation gives sigma(uv) = sigma(u) sigma(v).

If step i has displacement (dx_i,dy_i), then z(w) = sum over i<j of dx_i dy_j: each vertical step contributes its vertical increment times the preceding horizontal coordinate. This is the discrete integral of x dy. It differs from LatticeWalkNearMaximalArea.area, whose definition integrates y dx by charging horizontal steps at their current height. The two conventions must be kept distinct.

To apply the chronological formulas, take the event type to be Step, the ring to be the 3-by-3 integer matrix ring, and observe(s) to be its assigned letter matrix minus I. Each event observation has square zero. Their sum has entries x and y at 01 and 12, while their orderedPairMoment has entry z at 02. The stored doubled degree-two coordinate therefore has entry 2z, and the square of degree one has entry xy. Consequently the 02 entry of doubledMagnusDegreeTwo is A(w) = 2z(w)-x(w)y(w). SignatureOrderedMoment.doubledMagnusDegreeTwo_eq_orderedPairMoment_sub_reverse also identifies A with the 02 entry of the ordered-pair moment minus the moment of the reversed observation list, namely the sum over i<j of dx_i dy_j-dy_i dx_j.

The chronological BCH append law now reads A(uv) = A(u)+A(v)+x(u)y(v)-y(u)x(v). The last two terms are the 02 entry of the commutator of the degree-one matrices. Thus EN and NE have the same endpoint (1,1), but z(EN)=1 and z(NE)=0; their ordered matrix products differ. The closed word ENWS has signature H(0,0,1), whereas NESW has signature H(0,0,-1). A signed example is WN, with signature H(-1,1,-1).

The inverse word reverses the list and replaces every step by its opposite, swapping E with W and N with S. The transvection inverse law sends each letter to its matrix inverse, so this actual word has signature sigma(w)^(-1). Since H(x,y,z)^(-1) = H(-x,-y,xy-z), its A coordinate is -A(w). Under observe this operation is reverse-and-negate, as in ChronologicalSignatureHopf.chronological_signature_reverse_neg. The number of E/W letters and the number of N/S letters each equal those of the original word.

Every integer triple (x,y,z) is attained by an actual finite word. Indeed, the subgroup generated by T_01(1) and T_12(1) contains their commutator T_02(1), represented by ENWS. The transvection addition law identifies T_ij(t) with the integer power T_ij(1)^t. Hence the factorization of H(x,y,z) lies in this generated subgroup for all integers x,y,z. FreeGroup.range_lift_eq_closure and FreeGroup.lift_mk express this membership as a finite signed word in the two generators; decoding its signed letters as E, W, N and S yields the desired Step list and its complete matrix signature. In particular, at any fixed endpoint every integer z occurs. Appending ENWS or its inverse keeps that endpoint and changes z by +1 or -1, respectively.

For every fixed integer endpoint, every natural modulus n and every residue r in ZMod n, choose an integer representative of r and realize that central coordinate by such a word. This includes every odd prime modulus. These are existence statements for unrestricted finite words. Prescribed length, simplicity, confinement to a region, unused-edge requirements, T adjacency and available empty squares impose further conditions. A central residue alone does not certify their feasibility, and these statements do not extend the near-maximal-area walk-counting result.

**Theorem 1.9 (Two-event Magnus coordinate is the commutator).**

$$\forall f, p, q, \operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, [p, q])) = \operatorname{commutator}(\operatorname{f}(p), \operatorname{f}(q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_eq_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a chronology containing exactly two events, the doubled degree-two logarithmic coordinate is their ring commutator.

**Theorem 1.10 (Two-event orientation reversal).**

$$\forall f, p, q, \operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, [q, p])) = -\operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, [p, q])).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing two events negates the degree-two chronological defect.

**Theorem 1.11 (Commuting events have zero defect).**

$$\forall f, p, q, \operatorname{f}(p) \cdot \operatorname{f}(q) = \operatorname{f}(q) \cdot \operatorname{f}(p) \Rightarrow \operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, [p, q])) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_eq_zero_of_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A commuting event pair has no degree-two chronological memory.

## References

- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.StepTwoSignature`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronologicalSignature`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronological_signature_append`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronological_signature_degree_one`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubledMagnusDegreeTwo`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_degree_two_append`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_degree_two_mul`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_eq_commutator`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_eq_zero_of_commute`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_swap`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.eventSignature`
- Dependency: [D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity](../HiddenFlow/ProjectionCommutatorIdentity.md)
