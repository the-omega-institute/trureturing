# Dominant-root forcing for linear recurrences

## Abstract

A forced linear recurrence whose characteristic polynomial has a simple dominant real root R has solutions L R^j + O(q^j), with the prescribed L when q = |R|^(1/2).

**Theorem 1.1 (Dominant-root forcing).**

Lean statement: `D5/S1/Recurrence/Asymptotic/DominantRootForcing.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Asymptotic/DominantRootForcing.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bounded-error asymptotics for Bernáth's conjecture: OEIS A400645, revision 21, COMMENTS, and its rounded-norm siblings*. DOI: [10.5281/zenodo.24369110](https://doi.org/10.5281/zenodo.24369110). URL: <https://zenodo.org/records/24369110>.

*Commentary.*

Let P be a real polynomial with a simple real root R, and let real sequences b and e satisfy the sum over k from 0 to deg P of P_k b_(j+k) = e_j for every j. (1) If 0 < q < |R|, every other complex root of P has modulus below q, and e = O(q^j), then b_j = L R^j + O(q^j) for some real L. (2) If |R| > 1, every other complex root of P has modulus below |R|^(1/2), b_j = L R^j + o(R^j) for a real L, and e = O(|R|^(j/2)), then b_j = L R^j + O(|R|^(j/2)) with this same L.

Proof. Write S for the shift of complex sequences, so the recurrence reads P(S) b = e. Factor P = (X − R) Q over ℝ; Q(R) ≠ 0 since R is simple, and over ℂ, Q is its leading coefficient times the product of the factors X − z over its roots, all with |z| < q. Put d = Q(S) b, so that d_(j+1) − R d_j = e_j. The series of e_i / R^(i+1) converges geometrically because q < |R|, and d_j = R^j (d_0 + the partial sum) differs from L' R^j, with L' the full sum, by R^j times a tail of size O((q/|R|)^j); hence d = L' R^j + O(q^j). Then c = b − (L'/Q(R)) R^j satisfies Q(S) c = d − L' R^j = O(q^j). A factor S − z with |z| < q gives |u_(j+1)| ≤ |z| |u_j| + C q^j, and induction yields |u_j| ≤ M q^j with M = max(|u_0|, C/(q − |z|)); peeling the roots of Q one by one gives c = O(q^j). Taking real parts gives (1) with L = Re(L'/Q(R)).

For (2), part (1) with q = |R|^(1/2), which lies strictly between 0 and |R| because |R| > 1, gives b = L' R^j + O(|R|^(j/2)) for some L'. Dividing by R^j, b_j/R^j tends to L' and also to L, since b − L R^j = o(R^j); so L' = L.

This is Lemma 2 in Section 4 of H. Ma and W. Zhang's note on OEIS A400645 (DOI 10.5281/zenodo.24369110). The lemma assumes P monic with distinct roots, R > 1, the other roots of modulus at most one, q > 1, b_j ~ L R^j with L > 0, and e_j = O(b_j^(1/2)). Those hypotheses imply the ones above: b ~ L R^j gives b − L R^j = o(R^j) and b = O(R^j), hence b^(1/2) = O(R^(j/2)) and e = O(R^(j/2)). Here P need not be monic, only R must be simple, R may be negative, roots of modulus in [1, q) are allowed, and q may be at most one. A non-real root cannot play the role of R, since its conjugate has the same modulus.

The remaining hypotheses are needed. Simplicity of R: P = (X − 2)^2 and e = 0 admit b_j = j 2^j, which is not L 2^j + O(q^j) for any q < 2. Other roots below q: for P = (X − 3)(X − 2) and q = 3/2, b_j = 2^j solves the homogeneous recurrence and is not L 3^j + O((3/2)^j); a root z with |z| = q also fails, since P = (X − 3)(X − z), z = q real, and e_j = q^j admit a solution growing like j q^j. The bound q < |R|: P = X − R and e_j = R^j give b_j = j R^(j−1). In part (2), for 0 < |R| ≤ 1 the conclusion follows already from b − L R^j = o(R^j), so the case |R| > 1 is the one with content.

## References

- Truth anchor: `D5/S1/Recurrence/Asymptotic/DominantRootForcing.result`
