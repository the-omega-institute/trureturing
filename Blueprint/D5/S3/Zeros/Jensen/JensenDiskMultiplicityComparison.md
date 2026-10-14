# Polynomial occurrences in an isolating disk

Let `F` be analytic on a neighborhood of `closedBall(c,delta)`, with `delta>0`,
exact order `m>=1` at `c`, and no other zero in that closed disk. Let `P` be a
complex polynomial satisfying `|P(z)-F(z)|<|F(z)|` on the original sphere.
The disk comparison gives `P!=0`, no boundary root, and exactly `m` root
occurrences in the open disk.

Choose the analytic local factor `V` at the center. Define `U(c)=V(c)` and
`U(z)=F(z)/(z-c)^m` elsewhere. The local factorization makes `U=V` near the
center; away from the center the quotient is analytic. Isolation makes `U`
nonzero throughout the closed disk. Differentiating the global identity
`F(z)=(z-c)^m U(z)` on the boundary yields

```text
F'(z)/F(z) = m/(z-c) + U'(z)/U(z).
```

Cauchy-Goursat annihilates the integral of the analytic unit term. The center
inverse integrates to `2*pi*i`, so the integral of `F'/F` is `2*pi*i*m`.

The strict boundary inequality gives `|P/F-1|<1`; this places `P/F` in the
principal logarithm's slit plane. The derivative of `log(P/F)` on the complete
sphere is `P'/P-F'/F`. The circle primitive theorem makes that difference
integral zero. Continuity on the sphere supplies the integrability needed to
split the integral.

Over the complex numbers `P` splits. Its logarithmic derivative is the sum
of `1/(z-a)` over the **root multiset**, including repeated values. Each
occurrence inside the original disk integrates to `2*pi*i`; each occurrence
outside the closed disk integrates to zero by Cauchy-Goursat. Boundary roots
are already excluded. Cancellation of the nonzero factor `2*pi*i` gives the
occurrence count. The radius is never replaced by a smaller isolating radius.

This construction is used by the actual-source fixed-window disk clause.
