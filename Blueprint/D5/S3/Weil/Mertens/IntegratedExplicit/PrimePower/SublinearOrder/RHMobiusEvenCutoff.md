# Even truncation of the signed prime window

## Abstract

The two leading even-cutoff terms and their logarithmic average

**Theorem 1.1 (Arithmetic and spectral terms at the cutoff).**

$$RH \Rightarrow \left(\exists A \in \mathbb{R},\; \exists K \in \mathbb{R},\; \left(2 \le A \land 0 < K\right) \land \left(\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \left(2 \le m \land m + 1 = 2 \cdot r\right) \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(A \le a \land a \le B\right) \Rightarrow \left(\left|\operatorname{E}\left(m, a, B\right) + \operatorname{mu}\left(m + 1\right) \cdot \frac{m + 1}{m \cdot \operatorname{s}\left(m\right)} \cdot \operatorname{D}\left(\operatorname{s}\left(m\right), a, B\right) + \operatorname{mu}\left(r\right) \cdot \left(\operatorname{P}\left(r, B\right) - \operatorname{P}\left(r, a\right)\right)\right| \le \operatorname{W}\left(K, m\right) \cdot \operatorname{D}\left(\operatorname{s}\left(m\right) + \operatorname{delta}\left(m\right), a, B\right) \land \operatorname{W}\left(K, m\right) \cdot \operatorname{D}\left(\operatorname{s}\left(m\right) + \operatorname{delta}\left(m\right), a, B\right) \le \operatorname{W}\left(K, m\right) \cdot \frac{\operatorname{s}\left(m\right) + \operatorname{delta}\left(m\right)}{\operatorname{s}\left(m\right)} \cdot a^{-\operatorname{delta}\left(m\right)} \cdot \operatorname{D}\left(\operatorname{s}\left(m\right), a, B\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoff.signed_window_even_cutoff_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write q=m+1=2r, s(m)=1/2−1/q and δ(m)=1/q−1/(q+1). For any rate v let D(v,a,B)=a^(−v)−B^(−v). Set W(K,m)=Kq(1+log q)². E(m,a,B) is the original signed residual with root degrees selected by 2n<m+1. P(r,x) is the degree-r root primitive over actual zeta zeros with analytic multiplicity.

Increasing the order from m to q adds the arithmetic degree q and exactly the root degree r. The residual at order q is the displayed corrected expression. Its all-order estimate uses the faster rate s(m)+δ(m). Compare the two exponential integrals on the original logarithmic interval. The bounds include B=a.

**Theorem 1.2 (The arithmetic coefficient from fixed-width windows).**

$$RH \Rightarrow \left(\exists A \in \mathbb{R},\; 0 < A \land \left(\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \left(2 \le m \land m + 1 = 2 \cdot r\right) \Rightarrow \left(\exists C \in \mathbb{R},\; 0 < C \land \left(\forall L \in \mathbb{R},\; 0 < L \Rightarrow \left(\forall U \in \mathbb{R},\; \forall T \in \mathbb{R},\; \left(A \le U \land 0 < T\right) \Rightarrow \left(\operatorname{Integrable}\left(m, L, U, T\right) \land \left|\operatorname{Avg}\left(m, L, U, T\right) + \operatorname{mu}\left(m + 1\right) \cdot \frac{m + 1}{m \cdot \operatorname{s}\left(m\right)}\right| \le \frac{C}{T}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoff.signed_window_even_cutoff_cesaro` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F(m,L,u)=E(m,exp u,exp(u+L))/D(s(m),exp u,exp(u+L)). Integrable(m,L,U,T) means interval integrability of F(m,L,·) on [U,U+T] with respect to Lebesgue measure. Avg(m,L,U,T) is its interval integral divided by T. The starting threshold A is common to all orders and widths. The error constant depends on the order.

Normalize the two endpoint values of the root primitive by the same positive gap. Under RH the resulting increment is the real part of an absolutely summable exponential series. The ordinates divided by r have magnitude at least 10/r, so integrating the series over any interval gives a bounded contribution. Subtract the translated primitive integrals before taking absolute values. The remaining two intervals have length L and exp(−sL)L/(1−exp(−sL)) is at most 1/s. The integral bound for the higher-order remainder is also uniform in L. Dividing by T isolates the signed arithmetic coefficient.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoff.signed_window_even_cutoff_cesaro`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoff.signed_window_even_cutoff_expansion`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootPrimitiveFourier](../RootPrimitiveFourier.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusOddCutoff](RHMobiusOddCutoff.md)
