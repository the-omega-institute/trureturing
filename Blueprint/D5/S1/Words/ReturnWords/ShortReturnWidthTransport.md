# Finite packing and short return width transport

## Abstract

Finite interval chains, affine packing, and conditional short-return width estimates.

There are k+1 interval starts x(0),...,x(k). Adjacent separation accumulates to k times the separation, including the degenerate case k=0. The affine application separates full length-d intervals from the width-w images that lie in the parent. Natural division is floor division, and natural subtraction is truncated at zero.

**Lemma 1.1 (Accumulate local separation along a finite chain).**

$$\forall k \in \mathbb{N},\; \forall x \in \mathbb{N} \to \mathbb{R},\; \forall delta \in \mathbb{R},\; \forall ell \in \mathbb{R},\; \forall u \in \mathbb{R},\; \forall w \in \mathbb{R},\; \left(u \le x\left(0\right) \land \left(\left(\forall i \in \mathbb{N},\; i < k \Rightarrow x\left(i\right) + delta \le x\left(i + 1\right)\right) \land x\left(k\right) + ell \le u + w\right)\right) \Rightarrow k \cdot delta + ell \le w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.finite_interval_chain_packing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induct on m<=k to prove x(0)+m delta<=x(m). The successor step combines the induction inequality with the local edge at m. At m=k the two parent endpoint bounds give k delta+ell<=w. All real delta and ell are allowed; their nonnegative instances have the interval interpretation. This estimate is used by affine_cylinder_chain_packing.

**Lemma 1.2 (Pack affine interval images using a separate separation scale).**

$$\forall k \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall g \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall w \in \mathbb{R},\; \forall u \in \mathbb{R},\; \forall x \in \mathbb{N} \to \mathbb{R},\; \left(0 < g \land \left(0 \le w \land \left(\left(\forall i \in \mathbb{N},\; i \le k \Rightarrow Icc\left(u + g^{L} \cdot x\left(i\right), u + g^{L} \cdot \left(x\left(i\right) + w\right)\right) \subseteq Icc\left(u, u + w\right)\right) \land \left(\forall i \in \mathbb{N},\; i < k \Rightarrow x\left(i\right) + d \le x\left(i + 1\right)\right)\right)\right)\right) \Rightarrow k \cdot g^{L} \cdot d \le \left(1 - g^{L}\right) \cdot w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.affine_cylinder_chain_packing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set q=g^L and y(i)=u+q x(i). Whole-interval inclusion supplies the parent bounds for y(0) and y(k)+q w; the scaled adjacent inequalities supply y(i)+q d<=y(i+1). The finite chain estimate gives k q d+q w<=w, hence k q d<=(1-q)w. For k=1 this is q d<=(1-q)w, the two-cylinder packing inequality. For d>=0 the separate intervals [x(i),x(i)+d] have disjoint interiors; inclusion is required only for the width-w images. Negative d is also allowed algebraically, and no contraction upper bound is needed here. This estimate supplies short_return_width_lower_bound_of_chain.

**Lemma 1.3 (Phase divisibility bounds the synchronization length).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \left(0 < p \land \left(p \mid a \land \left(p \mid b \land \left(a \le n \land b \le 2 \cdot n - 1\right)\right)\right)\right) \Rightarrow lcm\left(a, b\right) \le p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.synchronized_length_le_phase_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Writing a=p alpha and b=p gamma gives lcm(a,b)=p lcm(alpha,gamma). The quotient bounds and the Mathlib product bound give the estimate. Zero lengths are allowed. This arithmetic helper is used by short_return_width_lower_bound.

**Lemma 1.4 (The contraction ratio decreases with the positive scale).**

$$\forall g \in \mathbb{R},\; \forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \left(0 < g \land \left(g < 1 \land \left(0 < L \land L \le M\right)\right)\right) \Rightarrow \frac{g^{M}}{1 - g^{M}} \le \frac{g^{L}}{1 - g^{L}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.contraction_ratio_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Power order and positive-denominator fraction comparison give this helper. Equality of scales is included. It is used by short_return_width_lower_bound.

**Lemma 1.5 (Arithmetic transport of a supplied packing inequality).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall g \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall w \in \mathbb{R},\; \left(0 < g \land \left(g < 1 \land \left(0 \le d \land \left(\left(0 < p \land \left(p \mid a \land \left(p \mid b \land \left(a \le n \land b \le 2 \cdot n - 1\right)\right)\right)\right) \land \left(0 < a \land \left(0 < b \land g^{lcm\left(a, b\right)} \cdot d \le \left(1 - g^{lcm\left(a, b\right)}\right) \cdot w\right)\right)\right)\right)\right)\right) \Rightarrow \frac{g^{p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor}}{1 - g^{p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor}} \cdot d \le w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.short_return_width_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This arithmetic helper assumes packing at the actual LCM, divides by its positive denominator, and applies the LCM and ratio helpers. It is used by short_return_width_lower_bound_of_chain, which derives the packing premise from interval inclusion and adjacent separation.

**Theorem 1.6 (Transport the accumulated packing estimate to the uniform scale).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall g \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall w \in \mathbb{R},\; \forall u \in \mathbb{R},\; \forall x \in \mathbb{N} \to \mathbb{R},\; \left(0 < g \land \left(g < 1 \land \left(0 \le d \land \left(0 \le w \land \left(\left(0 < p \land \left(p \mid a \land \left(p \mid b \land \left(a \le n \land b \le 2 \cdot n - 1\right)\right)\right)\right) \land \left(0 < a \land \left(0 < b \land \left(\left(\forall i \in \mathbb{N},\; i \le k \Rightarrow Icc\left(u + g^{lcm\left(a, b\right)} \cdot x\left(i\right), u + g^{lcm\left(a, b\right)} \cdot \left(x\left(i\right) + w\right)\right) \subseteq Icc\left(u, u + w\right)\right) \land \left(\forall i \in \mathbb{N},\; i < k \Rightarrow x\left(i\right) + d \le x\left(i + 1\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \frac{g^{p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor}}{1 - g^{p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor}} \cdot k \cdot d \le w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.short_return_width_lower_bound_of_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put L=lcm(a,b) and M=p floor(n/p) floor((2n-1)/p). Applying the affine packing theorem derives k g^L d<=(1-g^L)w from the interval hypotheses. The arithmetic helpers give L<=M and decrease the ratio, yielding w>=k g^M d/(1-g^M). The k=1 specialization recovers the two-cylinder width bound. The cardinality factor retains the full chain estimate; no packing inequality is assumed as a premise of this chain application.

These are abstract intervals with positive affine orientation. The graph/SCC existence argument, actual short returns at each basepoint, the phase-divisibility bridge for those returns, and identification of the separate interval families with original legal cylinders are outside these statements. The universal assertion for every original first piece in Proposition 51.3 therefore remains unproved. In particular the original full guard cylinders need not be contained in the piece; the required inclusion concerns the smaller images. Neither the coherence/phase characterization nor the SevenCycle examples supplies the missing general short-return and legal-cylinder bridges.

## References

- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.affine_cylinder_chain_packing`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.contraction_ratio_antitone`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.finite_interval_chain_packing`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.short_return_width_lower_bound`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.short_return_width_lower_bound_of_chain`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.synchronized_length_le_phase_bound`
