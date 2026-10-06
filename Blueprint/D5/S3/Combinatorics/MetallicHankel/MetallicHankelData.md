# The Metallic Quadratic Tail Cycle

## Abstract

A finite cycle of integral quadratic tails has total degree weight 2n(n+1) and determinant multiplier (-1)^n.

**Definition 1.1 (Quadratic tail states).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.TailState`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.TailState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

The tail states are u_0(i), u_1(i), u_2(i), w_0(i), w_1(i), w_2(i), indexed by nonnegative integers i, and the four distinct states v_0, v_1, v_2, v_3.

**Definition 1.2 (The index ranges of the cycle).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.validState`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.validState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For a nonnegative parameter n, the states u_0(i), u_1(i), u_2(i) and w_0(i) are valid when i is at most n - 2. The states w_1(i) and w_2(i) are valid when i is less than n - 2. All four v states are valid. Subtraction of natural numbers is truncated at zero.

**Definition 1.3 (Successive quadratic states).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.nextState`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.nextState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

The transitions are u_0(i) to u_1(i) to u_2(i), followed by v_0 if i = n - 2 and otherwise u_0(i+1). The four v states advance in order, with v_3 followed by w_0(0). The state w_0(i) advances to u_0(0) if i = n - 2 and otherwise to w_1(i); w_1(i) advances to w_2(i), and w_2(i) to w_0(i+1). Natural subtraction is truncated at zero.

**Definition 1.4 (Integral quadratic triples).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.quadraticData`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.quadraticData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Write I = (1-q)^{-1}, E = q^2-q+1 and T = q(1-q^n)I + (1+q^n)(1-q). The triple (A,B,C) encodes q C F^2 + B F = -A. At u_0(i) it is (E q^{n-i-2}, -E(2q^{n-i}-q^n-1)I, q(E(q^{n-i}-q^n-1)+q^{i+1})I^2). At u_1(i) it is (q^i, E(1-q^n)I, -E q^{n-i-1}). At u_2(n-2) it is (1+q^2(1-q^{n-1})I, T-2q^n, -q^{n-1}); at every other u_2(i) it is (-(E(q^{n-i-1}-q^n-1)+q^{i+2})I^2, (E(q^n+1)-2q^{i+2})I, -q^{i+1}). At v_0, v_1, v_2 and v_3 the triples are respectively (-q^{n-1}, T+2q^{n+1}, -q-q^3(1-q^{n-1})I), (q^n,T,-q^n), (q^{n-1},T,-q^{n+1}) and (-1-q^2(1-q^{n-1})I,T+2q^{n+1},-q^n). At w_0(i) the triple is (q^{n-i-2}, (E(q^n+1)-2q^{n-i})I, q(E(q^{i+1}-q^n-1)+q^{n-i})I^2); at w_1(i) it is (E q^i,E(1-q^n)I,-q^{n-i-1}); at w_2(i) it is (-(E(q^{i+2}-q^n-1)+q^{n-i-1})I^2,-E(2q^{i+2}-q^n-1)I,-E q^{i+1}). All entries are integral formal power series, and natural exponents use subtraction truncated at zero.

**Definition 1.5 (Degrees, signs and denominators).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.fractionData`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.fractionData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Write I = (1-q)^{-1} and T = q(1-q^n)I + (1+q^n)(1-q). Each state carries a triple (k,b,D). At u_0(i) it is (n-i-2,-1,(1-q^{n-i})I); at u_1(i) it is (i,-1,(1-q^{i+2})I-q); at u_2(i) it is (0,-1,1) when i = n-2 and (0,-1,1-q) otherwise. At v_0, v_1, v_2 and v_3 the triples are respectively (n-1,1,T+q^{n+1}), (n,-1,T), (n-1,-1,T+q^{n+1}) and (0,1,1). At w_0(i) it is (n-i-2,-1,(1-q^{n-i})I-q); at w_1(i) it is (i,-1,(1-q^{i+2})I); at w_2(i) it is (0,-1,1-q). Subtraction in natural indices and exponents is truncated at zero.

**Definition 1.6 (The rotated itinerary).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.cycle`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.cycle` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

The itinerary starts with v_2,v_3, then contains the triples w_0(i),w_1(i),w_2(i) for 0 at most i and i less than n-2, then w_0(n-2), then the triples u_0(i),u_1(i),u_2(i) for 0 at most i and i less than n-1, and ends with v_0,v_1. All natural subtractions are truncated at zero.

**Theorem 1.7 (Length, degree weight and denominator bounds).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.cycle_data`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.cycle_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For every n at least two, the itinerary has length 6n-4, all its states are valid, and appending v_2 makes each adjacent pair a transition. The sum of k+1 over the itinerary is 2n(n+1). The ordered pairs consisting of the coefficient of q^{k+1} in D and the sign b form the transfer word. At every valid state the constant coefficient of D is one and all coefficients above degree k+1 vanish.

**Theorem 1.8 (The determinant multiplier of one cycle).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.cycle_sign`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.cycle_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For every n at least two, let the itinerary have length L and let k_i and b_i be its degree and sign entries. The product of b_i over 0 at most i and i less than L is one. Put h_i = -product_{j=0}^i b_j. Then the product of (-1)^{k_i(k_i+1)/2} h_i^{k_i+1} over the itinerary is (-1)^n.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.TailState`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.cycle`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.cycle_data`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.cycle_sign`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.fractionData`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.nextState`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.quadraticData`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelData.validState`
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs](MetallicHankelDefs.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransfer](MetallicHankelTransfer.md)
