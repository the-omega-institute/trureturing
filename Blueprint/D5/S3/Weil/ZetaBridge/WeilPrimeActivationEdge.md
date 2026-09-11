# Prime Activation Edge

## Abstract

The original prime-activation edge overlap has a rank-one first-order term; the already-owned even zero-trace stencil suppresses both its edge mass and cross-edge pairing to fifth order.

**Theorem 1.1 (Actual cosine edge overlap and rank-one leading term).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilPrimeActivationEdge.cosine_prime_edge_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilPrimeActivationEdge.cosine_prime_edge_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real u,v and h>=0, bound the difference between integral_0^h cos(u*t)cos(v*(h-t)) and h by (u^2+v^2)h^3/6. Continuous integrands and the exact quadratic polynomial integral are used. This is the actual low-mode overlap when a compressed prime shift enters through the two window endpoints.

**Definition 1.2 (Boundary profile of the existing zero-trace stencil).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilPrimeActivationEdge.evenStencilEdge`

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilPrimeActivationEdge.evenStencilEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite complex sum uses cos(pi*n*t)-1, the edge profile of V_n+V_(-n)-2V_0 after the original unitary dilation, with a fixed factor sqrt(2). Zero trace is structural in this particular trial. It is not imposed on the actual Weil candidate or on an unknown eigenfunction.

**Theorem 1.3 (Complete edge mass and cross-edge correlation).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilPrimeActivationEdge.even_stencil_edge_fifth_order`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilPrimeActivationEdge.even_stencil_edge_fifth_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K=sum_n norm(v_n)*(pi*n)^2. The theorem derives integrability and bounds the actual integral of norm(edge(t))^2 by K^2*h^5/20 and the norm of integral conj(edge(t))*edge(h-t) by K^2*h^5/120. Coefficients remain complex and all mixed terms are retained before the bound. The proof uses the actual cosine defect and the exact t^2*(h-t)^2 integral, not a supplied boundary-decay assumption.

The associated numerical increment independently certifies the full candidate-orthogonal Weil form throughout |a-log(3)/2|<=10^-8, retaining prime 3 on its active side, the complete infinite Fourier complement and all boundary moments. Its interval matrix identification, Schur completion and spectral consequence remain paper/computer-assisted bridges. The fifth-order trial estimate explains one special low-block mechanism; it is not used to set the genuine candidate's endpoint to zero. Lean elaboration, Scribe emission and a transitive axiom report have not run.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilPrimeActivationEdge.cosine_prime_edge_remainder`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilPrimeActivationEdge.evenStencilEdge`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilPrimeActivationEdge.even_stencil_edge_fifth_order`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilEvenDualStencil](WeilEvenDualStencil.md)
