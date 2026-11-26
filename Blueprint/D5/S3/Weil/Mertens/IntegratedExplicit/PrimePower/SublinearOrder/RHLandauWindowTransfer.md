# Transfer of a uniform Landau sum bound

## Abstract

A uniform bound for actual zero sums supplies logarithmic-time harmonic Fourier cancellation.

Under the existing RiemannHypothesis interface use the inclusive positive cutoff T, analytic multiplicities m(gamma), harmonic weights a(gamma)=m(gamma) gamma/(1/4+gamma^2), W(T)=sum a(gamma), and normalized complex score Z(T,t). Write F(V,t) for the unweighted-with-multiplicity sum through V of exp(i gamma t).

**Theorem 1.1 (Logarithmic-time deficit under a uniform actual-ordinate sum bound).**

$$1-|\operatorname{Z}\left(T, t\right)| \ge \frac{1}{32 \cdot \operatorname{log}\left(T\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLandauWindowTransfer.harmonic_landau_window_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix b>0 and C>0. The theorem assumes that for every real V>1 and nonzero real t, the norm of F(V,t) is bounded by C times the sum of V, exp(|t|/2)(1+|t|)^2, exp(|t|/2)(1+log V), and log V/|t|. Under this explicit hypothesis there is L>1 such that the displayed inequality holds for every T>=L and b/log T<=|t|<=log T.

The paper-level source for the hypothesis is Gonek, A Formula of Landau and Mean Values of zeta(s), Theorem 1 equation (3), printed pp. 92–93. Its sum includes multiplicities. Divide by sqrt(x) under RH and set x=exp(|t|), using conjugation for negative times. The main term and nearest-prime-power error are bounded by a constant times V since Lambda(x)<=log x, the minimum in that error is at most V, and |t| exp(-|t|/2) is bounded. The two errors involving x become bounded by the two displayed exponential terms after enlarging C, and the near-1 error is at most log V/|t|. The Landau formula itself is a literature input beyond the current Lean proof.

For sufficiently large T, log T<=q=T^(1/4), q>=1, q^4=T. On the stated time window and 1<V<=T, exp(|t|/2)<=q^2 and 1+|t|, 1+log V<=2q. The four terms of the assumed bound are at most T, 4T, 2T, T/b. Hence the two inclusive sums at V=T and V=3T/4 are each bounded by C(7+1/b)T. Their difference is the upper-band sum, with norm eventually at most T log T/(32 pi).

The zero counting asymptotic supplies at least T log T/(16 pi) analytic multiplicity in (3T/4,T]. In that band the actual weights dominate m(gamma)/(2T). Decompose the weights on the entire cutoff into this retained profile and a pointwise nonnegative remainder. Since every phase has unit norm, the triangle inequality bounds the remainder norm by its mass. The retained profile therefore gives a raw score deficit of at least half the upper-band count divided by 2T, namely log T/(64 pi). Normalize using W(T)<=log(T)^2/(2 pi) to obtain the claimed deficit.

The theorem extends the conditional pointwise estimate to times of order log T. With the previously proved short-time estimates and relative Fejer truncation, resolutions satisfying eta(T) log T tending to infinity can use this window. Smaller resolutions require longer-time arithmetic estimates. The paper-level uniform Landau premise remains an open formalization supplier.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLandauWindowTransfer.harmonic_landau_window_deficit`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHHarmonicPairMoment](RHHarmonicPairMoment.md)
