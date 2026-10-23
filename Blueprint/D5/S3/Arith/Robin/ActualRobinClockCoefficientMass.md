# Finite Coefficient Mass of the Actual Robin Clock Kernel

## Abstract

The actual quantitative Robin clock covariance controls the exact finite maximum coefficient mass, with its Abel top and lower anchor.

For t>1 put g(t)=1/(t log t). For A>1 and x>=1 the literal W(A,x) sums log(k)*max(g(k*x)-g(A),0) for 2<=k<=floor(A). Gamma(x,x+z) is the unnormalized centered sum over the same arbitrary finite sample of m clocks. With 1<a<=A_i<=b, 1<=x<=y and z>=0, the imported actual_clock_quantitative theorem supplies actual range and decrease bounds derived from the activation integral and harmonic-shell variation. No W/Gamma envelope is assumed.

Use K=log(b/a)+log(log(b)/log(a)) and C=(1+1/log(a))*(log(b/a)+1/2). The actual Gamma bound is m*K^2/(4*x*(x+z)), and its decrease is at most m*K*C/4*[1/(x*(x+z))-1/(y*(y+z))]. At y=x+1 the second denominator is (x+1)*(x+z+1). The consumer below uses these same actual estimates.

The ordinary source is U-int, U-size, U-var, G-size, G-var and J in Library/Analytic/mantovanelli2026primeworkload.md at immutable commit cd554e98a13551899994b718e7cdbd35d81624ab. Its arithmetic supplier remains conditional and is not certified here. No primary-source or literature-priority claim is made.

**Theorem 1.1 (Actual finite coefficient mass).**

Lean statement: `D5/S3/Arith/Robin/ActualRobinClockCoefficientMass.actual_clock_coefficient_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualRobinClockCoefficientMass.actual_clock_coefficient_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep the same arbitrary m clocks with 1<a<=A_i<=b and a<=b. For a finite set Z of nonnegative real shifts and integers 1<=L<=T, define omega_r=max over Z of z*[Gamma(r,r+z)-Gamma(r+1,r+z+1)], kappa_L=max over Z of z*Gamma(L,L+z), and J=(sum from r=L to T of r*omega_r)+(L-1)*kappa_L. Empty Z gives every maximum and J the value zero. An invalid block T<L is defined as zero before taking maxima. For nonempty Z put zmax=max Z.

With h_z(t)=1/(t*(t+z)) and A_LT(z)=z*[L*h_z(L)+sum from r=L+1 to T of h_z(r)-T*h_z(T+1)], the actual coefficient mass is nonnegative and at most m/4*[K*C*A_LT(zmax)+K^2*(L-1)*zmax/(L*(L+zmax))]. It also gives the mass bound with A_LT replaced by 2*zmax/L. The exact finite Abel identity retains the negative finite top. Dropping a nonnegative top only proves the upper bound; no zero top is assumed. The lower coefficient anchor is retained.

This is a real consumer of the actual quantitative covariance theorem and activation-shell variation. The maximum direction follows from z*[h_z(r)-h_z(r+1)]=1/(r*(r+1))-1/((r+z)*(r+z+1)), which increases with z. Finite summation by parts and the pinned reciprocal-square tail bound supply the exact A_LT and its coarse bound. No assumed W/Gamma envelope or arithmetic correlation supplier enters this deterministic result.

The conditional Corr consumer remains unfinished. For its positive integer rough shifts, define S_R(z) as the sum of mu(w)*mu(w+z) for 1<=w<=R. The ordinary supplier is uniform for a fixed Z and every selector c(z) in [0,1], fixed before the inner Moebius sum. The required bound is abs(sum_z c(z)*S_R(z)/z) <=C22*R*B^(-1-epsilon), under the supplier's conditions, at R=L-1 and every R=r in [L,T]. This result does not certify that supplier. The exact finite Abel formula retains the negative lower anchor and the top sum of Gamma_z(T+1)*S_T(z). That top vanishes only with actual support evidence, for example b<=2*(T+1); the negative finite top in A_LT is retained in the deterministic coefficient budget. This result treats arbitrary actual clocks and does not identify them with a selected equality-inclusive CA sample.

The full Robin/5040/RH goal remains active and unproved. Its complete quadratic consumer retains m*mean(R)^2, V_a with actual reserve and defect, the signed cross term 2*sum(mu(d)*beta(d)), the squarefree diagonal, d=1, all rows below L and every complementary shift. No one of these unpaid terms is removed by this covariance estimate. Faithful four-slot registration remains unfinished under the source-owner issue https://github.com/the-omega-institute/trureturing/issues/5214#issuecomment-6101507121; no declared_validated state or literature priority is claimed.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualRobinClockCoefficientMass.actual_clock_coefficient_mass`
- Dependency: [D5/S3/Arith/Robin/ActualRobinClockCovariance](ActualRobinClockCovariance.md)
