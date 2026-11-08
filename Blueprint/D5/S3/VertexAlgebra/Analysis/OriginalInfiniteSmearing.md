# Infinite original charged-field smearing

## Abstract

Absolutely convergent sums of the original circle modes in Sobolev operator spaces.

The input is the original positive Model, a charge a, a genuine globally smooth periodic Test f, and a natural Sobolev order k. Put q=order(a). operatorTerm(a,f,k,m) is coefficient_f(m) times modeExtension(a,k,m), an element of the actual Banach space B(H_(q+k),H_k). The original charged bound fixes the same positive C_a before f, k, m and the input vector.

The term norm is at most C_a*weight_f(q+k,m). SmoothCircleFourier proves that these scalar weights are summable over every integer, so operator_absolute and operator_summable establish absolute operator-norm convergence. smear(a,f,k) is the resulting two-sided infinite sum in B(H_(q+k),H_k). Its norm is at most C_a*W_f(q+k), and its value at x has norm at most that constant times norm(x). Evaluation commutes with this sum; the corresponding vector series is itself summable.

Continuity of the Sobolev inclusions permits passage through the vector sums. Together with compatibility of the mode extensions, this proves that inclusion(j,k) after smear(a,f,k) equals smear(a,f,j) after inclusion(q+j,q+k), for every j<=k. The smooth-test estimate can also be expressed using jetNorm_f(0), jetNorm_f(q+k+2), and the finite two-sided inverse-square series, directly by the proved W_le bound.

OriginalSmoothDomain consumes the compatible maps to define an invariant smooth domain and passes the original opposite-charge pairing through the absolute sums. OriginalSmearingCore uses the evaluated series and continuity for graph approximation and charge transport; OriginalSmoothFields consumes the same bounds at the endpoint. The output may have infinite energy support even for finite carrier input. These are consumed support definitions and private estimates, without separate theorem Describes or a standalone novelty claim. The interpretation follows Carpi and Tomassini, arXiv:2303.14097v2, with the existing lattice and Mathlib attributions retained.

## References

- Dependency: [D5/S3/VertexAlgebra/Analysis/OriginalModeExtension](OriginalModeExtension.md)
- Dependency: [D5/S3/VertexAlgebra/Analysis/SmoothCircleFourier](SmoothCircleFourier.md)
