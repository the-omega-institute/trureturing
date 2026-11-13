# An eventual lower-bound criterion on original records

## Abstract

Original strict integer-record one-sided normalized lower bounds characterize RH

**Theorem 1.1 (The complete original-record criterion).**

$$\left(\exists M \in \mathbb{R},\; \exists T \in \mathbb{R},\; 2 \le T \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall lambda \in \mathbb{R},\; 0 < lambda \Rightarrow \left(\left(\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(n < m \Rightarrow \operatorname{goldenResourceObjective}\left(lambda, n\right) < \operatorname{goldenResourceObjective}\left(lambda, m\right)\right)\right) \Rightarrow \left(T \le \operatorname{largestPrime}\left(m\right) \Rightarrow -M \le \operatorname{D}\left(\operatorname{largestPrime}\left(m\right)\right) \cdot \operatorname{robinLogMargin}\left(m\right)\right)\right)\right)\right)\right) \Leftrightarrow \operatorname{RiemannHypothesis}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OriginalRecordLowerBoundCriterion.original_record_lower_bound_iff_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D(x)=sqrt(x)*log(x). The objective is the existing goldenResourceObjective(lambda,n), and robinLogMargin and largestPrime are their original arithmetic definitions. A single pair of real constants M,T with T>=2 works for every natural m>=2, every real lambda>0, and strict objective dominance over EVERY positive n<m. The clock is the largest prime of m. This is an equivalence criterion; it proves neither RH nor finite 5040 closure.

For the converse, replace M by max(M,0). The full correction at every original record is bounded using fullC_leading at epsilon=1. For each real cutoff x, cutoff_record gives the least global optimizer with exactly that prime prefix, hence a genuine strict original record. The exact margin_identity and B_prefix yield a lower bound for D(Pn(x))*B(Pn(x)). normalization gives D(Pn(x))/D(x)>=1/2 on one tail. A fixed nonpositive lower constant can therefore be transferred to D(x)*B(x) without assuming an absolute bound on B.

Unconditional PNT ensures theta(x)>1 eventually. Log-log concavity gives log(log(theta(x)))-log(log(x))<=(theta(x)-x)/(x*log(x)). Use theta<=psi, the full complete_mertens_ledger and complete_mangoldt_le_neg_E3, with all Mangoldt prime powers retained, to obtain B(x)<=weightedTail(psiErrorKernel,x). Thus the original lower bound gives weightedTail>=-A/(sqrt(x)*log(x)) on one real tail.

WeightedTailInverse.tail_lower_bound applies using only the ledger's actual L1 kernel, with its closed-tail premise paid by one eventual threshold. It gives Q(x)>=-3*A/sqrt(x). The complete Chebyshev tail identity gives exactly Q(x)=-U(x)/x, so U(x)<=3*A*sqrt(x). At x=exp(y), the literal full arithmetic K(y) is at most 3*A+1 on one positive real tail, including the constant and complete trivial-zero corrections. Apply the parent IntegratedExplicit.actual_kernel_affine_tail_implies_rh with slope zero. No RH, chosen-zero, positivity or transform premise enters this direction.

The forward direction uses the accepted RHSharpOriginalRecordMargin.original_record_sharp_lower_endpoint at epsilon=1. Its RH premise is retained in this direction.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OriginalRecordLowerBoundCriterion.original_record_lower_bound_iff_rh`
- Dependency: [D5/S3/Arith/Robin/CompleteMertensPeak](../CompleteMertensPeak.md)
- Dependency: [D5/S3/Arith/Robin/LogarithmBounds](../LogarithmBounds.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin](RHSharpOriginalRecordMargin.md)
- Dependency: [D5/S3/Weil/Mertens/CompleteChebyshevTailIdentity](../../../Weil/Mertens/CompleteChebyshevTailIdentity.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak](../../../Weil/Mertens/IntegratedExplicit/ActualLinearPeak.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace](../../../Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace.md)
- Dependency: [D5/S3/Weil/Mertens/WeightedTailInverse](../../../Weil/Mertens/WeightedTailInverse.md)
