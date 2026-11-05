# Increasing weights

## Abstract

Finite one-sign-change weighting for the gamma-series transformation.

**Theorem 1.1 (Finite weighting principle).**

$$\forall A \in Nat \to Real,\; \forall W \in Nat \to Real,\; \forall h \in Nat,\; \left(\forall i \in Nat,\; i \le h \Rightarrow \left(\forall j \in Nat,\; j \le h \Rightarrow \left(i < j \Rightarrow \left(0 < A\left(i\right) \Rightarrow 0 \le A\left(j\right)\right)\right)\right)\right) \Rightarrow \left(0 \le \sum _{i \in \operatorname{Finset}.\operatorname{range}\left(h + 1\right)} (A\left(i\right)) \Rightarrow \left(\left(\forall i \in Nat,\; i \le h \Rightarrow 0 \le W\left(i\right)\right) \Rightarrow \left(\left(\forall i \in Nat,\; i \le h \Rightarrow \left(\forall j \in Nat,\; j \le h \Rightarrow \left(i \le j \Rightarrow W\left(i\right) \le W\left(j\right)\right)\right)\right) \Rightarrow 0 \le \sum _{i \in \operatorname{Finset}.\operatorname{range}\left(h + 1\right)} (A\left(i\right) \cdot W\left(i\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Weighting.weighted_sum_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A and W be real sequences and h a natural number. Assume that for all i,j <= h with i < j, A(i) > 0 implies A(j) >= 0; that the sum of A(i) for 0 <= i <= h is nonnegative; that W(i) >= 0 for i <= h; and that W(i) <= W(j) for i <= j <= h. Then the sum of A(i)W(i) for 0 <= i <= h is nonnegative. Zero entries and either empty sign group are allowed.

**Theorem 1.2 (Coefficientwise weighting principle).**

$$\forall A \in Nat \to Real,\; \forall W \in Nat \to \left(Nat \to Real\right),\; \forall h \in Nat,\; \left(\forall i \in Nat,\; i \le h \Rightarrow \left(\forall j \in Nat,\; j \le h \Rightarrow \left(i < j \Rightarrow \left(0 < A\left(i\right) \Rightarrow 0 \le A\left(j\right)\right)\right)\right)\right) \Rightarrow \left(0 \le \sum _{i \in \operatorname{Finset}.\operatorname{range}\left(h + 1\right)} (A\left(i\right)) \Rightarrow \left(\left(\forall N \in Nat,\; \forall i \in Nat,\; i \le h \Rightarrow 0 \le W\left(i, N\right)\right) \Rightarrow \left(\left(\forall N \in Nat,\; \forall i \in Nat,\; i \le h \Rightarrow \left(\forall j \in Nat,\; j \le h \Rightarrow \left(i \le j \Rightarrow W\left(i, N\right) \le W\left(j, N\right)\right)\right)\right) \Rightarrow \left(\forall N \in Nat,\; 0 \le \sum _{i \in \operatorname{Finset}.\operatorname{range}\left(h + 1\right)} (A\left(i\right) \cdot W\left(i, N\right))\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Weighting.coefficientwise_weighting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a real sequence, W a function from two natural indices to the reals, and h a natural number. Assume the same scalar sign condition and total-sum condition as in weighted_sum_nonneg. Assume for every natural degree N that W(i,N) is nonnegative for i <= h and W(i,N) <= W(j,N) for i <= j <= h. For every natural N the sum of A(i)W(i,N) over i=0,...,h is nonnegative.

Choose the least positive term of A. Every earlier term is nonpositive and every later term is nonnegative. Subtracting the weight at that index makes each product nonnegative, while the residual constant weight multiplies the nonnegative total sum. If no positive term exists, the total-sum condition forces all terms to vanish. Applying this argument independently in each degree proves the coefficientwise statement without convergence or division of formal series.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Weighting.coefficientwise_weighting`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Weighting.weighted_sum_nonneg`
