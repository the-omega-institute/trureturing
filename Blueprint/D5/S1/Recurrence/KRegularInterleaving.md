# Finite interleavings of integer k-regular sequences

## Abstract

Every finite interleaving of integer-valued k-regular residue streams is k-regular.

A sequence has domain the natural numbers, including zero, and values in the integers. Its full k-kernel K_k(s) consists of all sequences n ↦ s(k^e n+c), for natural e and c with c<k^e. Write Regular(k,s) when the integer span of this entire kernel is finitely generated. The values and the kernel may both be infinite.

Affine-subsequence closure is supplied by `D5/S1/Recurrence/KRegularAffineSubsequence.is_k_regular_affine_subsequence`; its literature statement is recorded in `D5/L/RecurrenceComposition/alloucheshallit1992regular`.

**Theorem 1.1 (Interleaving closure).**

$$\forall k \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; \forall s \in (\mathrm{Nat} \to \mathbb{Z}),\; 2 \le k \Rightarrow \left(1 \le a \Rightarrow \left(\left(\forall i \in \mathrm{Nat},\; i < a \Rightarrow \operatorname{Regular}\left(k, (n: \mathrm{Nat} \mapsto \operatorname{s}\left(a \cdot n + i\right))\right)\right) \Rightarrow \operatorname{Regular}\left(k, s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KRegularInterleaving.is_k_regular_interleaving` (`✓ std3`). ∎

*Citation.* Jeffrey Shallit (2020). *Corrected proof of Theorem 2.7 in Allouche and Shallit (1992)*. URL: <https://cs.uwaterloo.ca/~shallit/Papers/merge.pdf>.

*Commentary.*

For every natural base k≥2, every natural interleaving width a≥1, and every integer-valued sequence s, assume that n ↦ s(an+i) is k-regular for every natural i<a. Then s is k-regular in that same base. This is the integer-coefficient case of the cited Theorem 1. The width need not be coprime to the base. No finite-range, finite-kernel, automaticity, periodicity, recurrence, common generating-family, or regularity assumption on s occurs among the hypotheses.

For N and r natural, let E(N,r)h(n) equal h(⌊n/N⌋) when n mod N=r and zero otherwise. This is an integer-linear insertion map. Put f_i(m)=s(am+i) and T_i=E(a,i)f_i, so s is the finite sum of the T_i for 0≤i<a.

Fix one input f_i. The attained values g=gcd(k^e,a) form a finite set, since 1≤g≤a. For each such g, choose the least exponent t_g attaining it. Set u_g=k^(t_g)/g and N_g=a/g. Both are positive. For every exponent e attaining g, minimality gives t_g≤e and k^e/g=k^(e−t_g)u_g. For each d<u_g, use affine-subsequence closure to obtain the finitely generated span H(g,d) of the k-kernel of n ↦ f_i(u_g n+d). Form the single finite sum W_i of E(N_g,r)(H(g,d)) over all attained g, d<u_g, and r<N_g. Linear images and finite sums preserve finite generation.

To contain the whole kernel, take arbitrary e and c<k^e. With K=k^e and g=gcd(K,a), either the mask is never active and T_i(Kn+c) vanishes for every n, or the mask is active on exactly one residue class r modulo N_g. Indeed, canceling K in a congruence modulo a divides the modulus by gcd(K,a). Choose the least nonnegative representative r<N_g of an index satisfying Kn+c ≡ i modulo a. Then Kr+c=am_0+i with m_0<K/g, and for every n the masked sample is exactly E(N_g,r) applied to ℓ ↦ f_i((K/g)ℓ+m_0). Write m_0=u_g q+d by Euclidean division. The strict bound is q<k^(e−t_g), while d<u_g. Thus this inner sequence is a genuine member of the k-kernel of n ↦ f_i(u_g n+d), and its insertion lies in W_i. The same W_i works for every e and c, including e=c=0 and m_0=0.

Consequently the entire kernel span of each T_i is contained in its finitely generated W_i. The full kernel of s lies in the same finite sum of the W_i, which is finitely generated. The integer span of K_k(s) is therefore finitely generated because the integers are Noetherian. The construction also includes a=1 and N_g=1. It concerns integer coefficients and supplies no general coefficient-ring theorem or finite-state transducer construction.

## References

- Truth anchor: `D5/S1/Recurrence/KRegularAffineSubsequence.is_k_regular_affine_subsequence`
- Truth anchor: `D5/S1/Recurrence/KRegularInterleaving.is_k_regular_interleaving`
- Dependency: [D5/S1/Recurrence/KRegularAffineSubsequence](KRegularAffineSubsequence.md)
