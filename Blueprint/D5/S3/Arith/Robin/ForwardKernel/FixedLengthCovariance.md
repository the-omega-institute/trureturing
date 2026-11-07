# Fixed-length covariance

## Abstract

Uniform cumulative variance asymptotics give the covariance of fixed increment lengths.

Let E be measurable and bounded on every compact interval. Write D_h(x)=E(x+h)-E(x), V(Y,h)=integral_1^Y D_h(x)^2 dx, h=c*X^(4/5), and ell=log(X/h), where c>0. Assume V(Y,k)/(Y*k*log(Y/k)) tends uniformly to one for Y^(3/4)<=k<=Y^(7/8).

**Theorem 1.1 (Fixed multiples enter the variance band).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance.shifted_band`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance.shifted_band` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c,d,q positive and r nonnegative, set h=c*X^(4/5) and Y=d*X+r*h. Eventually Y^(3/4)<=q*h<=Y^(7/8), since the lower and upper ratios tend to zero.

**Theorem 1.2 (Growth of the length logarithm).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance.length_log_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance.length_log_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>0, log(X/(c*X^(4/5))) tends to infinity as X tends to infinity.

**Theorem 1.3 (Variance at a shifted endpoint).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance.shifted_variance_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance.shifted_variance_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For d,q>0 and r>=0, V(d*X+r*h,q*h)/(X*h*ell) tends to d*q as X tends to infinity.

The endpoint divided by X tends to d. The ratios (d*X+r*h)^(3/4)/(q*h) and q*h/(d*X+r*h)^(7/8) tend to zero, so q*h eventually lies in the variance band. Moreover ell=(1/5)*log(X)-log(c) tends to infinity, while log((d*X+r*h)/(q*h))-ell tends to log(d/q). Multiplying the variance ratio by the endpoint and logarithmic normalization ratios gives the limit.

**Theorem 1.4 (Covariance of two increments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance.fixed_length_covariance_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance.fixed_length_covariance_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1<=a<b<=2 and s,t in [0,1], the integral of D_(s*h)(x)*D_(t*h)(x) over [a*X,b*X], divided by X*h*ell, tends to (b-a)*min(s,t).

Compact boundedness and measurability make the increment products integrable. Subtract cumulative variances at the two endpoints to obtain each square integral. When t<=s, the identity D_(s*h)(x)-D_(t*h)(x)=D_((s-t)*h)(x+t*h) translates the difference square to endpoints a*X+t*h and b*X+t*h. Its normalized limit is (b-a)*(s-t). Polarization gives (b-a)*t; interchanging s and t gives the other ordering. A zero length has identically zero square integral, so the same argument includes zero lengths and s=t.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance.fixed_length_covariance_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance.length_log_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance.shifted_band`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance.shifted_variance_tendsto`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer](VarianceTransfer.md)
