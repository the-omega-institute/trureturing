# Affine modular stopping theorem 11.3

## Abstract

The independent all-path affine modulus and exact named-edge stopping theorem.

**Lemma 1.1 (Endpoint-preserving named-edge cycle erasure).**

$$\forall\gamma\in\operatorname{Path}\left(v, w\right), \exists eta\in\operatorname{Path}\left(v, w\right): \operatorname{ActualSimple}\left(eta\right)\land\operatorname{Sublist}\left(\operatorname{edges}\left(eta\right), \operatorname{edges}\left(\gamma\right)\right)\land\operatorname{A}\left(eta\right)\mid\operatorname{A}\left(\gamma\right)\land\operatorname{length}\left(eta\right)\leq|V|-1\land\forall p,\sum_{e\in eta}\nu_{p}(a_{e})\leq\sum_{e\in \gamma}\nu_{p}(a_{e})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/AffineNetworks/AffineModularStopping.actual_cycle_erasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual directed path has a simple actual path with the same endpoints. Its named-edge word is an occurrence sublist of the original word, its original multiplier product divides the original product, and its length is at most |V|−1. For every prime coordinate, erasure cannot increase the sum of edge losses, including the infinite loss of a zero multiplier.

The construction erases the prefix recursively. If the last edge ends at a vertex already in the erased prefix, it retains the actual prefix ending at that vertex. Otherwise it appends the same original named edge. Vertex-list uniqueness gives the cardinality bound; the surviving edge occurrences give product divisibility.

**Theorem 1.2 (All-path prime-loss maximum and original gcd/lcm recurrence).**

$$\forall v,0<D_{v}\land D_{v}\mid m; \forall v,p,\operatorname{Prime}\left(p\right)\land p\mid m\implies{\forall w,\gamma\in\operatorname{Path}\left(v, w\right),\nu_{p}(\operatorname{quotient}\left(\gamma\right))=[\nu_{p}(d_{w})-\sum_{e\in \gamma}\nu_{p}(a_{e})]_{+}}\land\nu_{p}(D_{v})=\max_{w\in V,\gamma\in\operatorname{Path}\left(v, w\right)}[\nu_{p}(d_{w})-\sum_{e\in \gamma}\nu_{p}(a_{e})]_{+}=\max_{w\in V,\gamma\in\operatorname{Path}\left(v, w\right),\operatorname{ActualSimple}\left(\gamma\right),\operatorname{length}\left(\gamma\right)\leq|V|-1}[\nu_{p}(d_{w})-\sum_{e\in \gamma}\nu_{p}(a_{e})]_{+}; \forall v,n,|V|-1\leq n\implies\operatorname{iterate}\left(n, v\right)=D_{v}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/AffineNetworks/AffineModularStopping.theorem11_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m be any positive integer, including 1. The nonempty finite vertex type and finite named-edge type retain loops and parallel edges. Each vertex source is the full ZMod m, with the reduction port modulo a positive divisor d_v of m. Every edge is legal on every phase and carries its original arbitrary natural multiplier a_e, including zero, and its affine offset c_e in ZMod m. A path transports the same phase through the original edge word; its multiplier A_γ is the product of those edge occurrences, with A_empty=1.

The modulus D_v is a positive divisor of m, independently defined as the lcm of d_w/gcd(d_w,A_γ) over all actual paths γ:v→w, with empty paths and prefixes retained. Its finite divisor image uses m.divisors and has no path-length truncation. For every prime p dividing m, ν_p(D_v) is the maximum of [ν_p(d_w)−Σ_e∈γ ν_p(a_e)]_+ over all actual paths. The same maximum is attained on a simple actual path of length at most |V|−1. The loss convention is ν_p(0)=+∞ and [b−∞]_+=0.

The recurrence is defined separately by D_v^(0)=d_v and D_v^(n+1) equal to the lcm of d_v and every D_w^(n)/gcd(D_w^(n),a_e) for the original outgoing named edges e:v→w. The proof characterizes its divisibility by the quotients of all paths of length at most n, using actual first-edge decomposition. Erasure then proves D_v^(n)=D_v for every n≥|V|−1. Empty outgoing-edge sets retain d_v.

The retained task records include all finite-path ports, prefixes and the empty path. Vertex and edge identities are public; control depends on obtained port records and internal state, and fixed fees are determined by the retained edge word. No phase guard, phase-dependent fee or extra reference is introduced. Erasure concerns the distinguishability kernel and may change offsets, outputs, visit counts and fees. Different primes can attain their maxima on different paths; the theorem does not assert one path attaining all prime optima.

## References

- Truth anchor: `D5/S3/Arith/AffineNetworks/AffineModularStopping.actual_cycle_erasure`
- Truth anchor: `D5/S3/Arith/AffineNetworks/AffineModularStopping.theorem11_3`
