# Finite Cassel power-sum selection

## Abstract

A finite complex family containing one has a bounded power sum with real part at least one.

**Theorem 1.1 (A power sum with real part at least one).**

Lean statement: `D5/S3/Arith/Robin/ZeroPowerSum.exists_pow_sum_re_ge_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ZeroPowerSum.exists_pow_sum_re_ge_one` (`✓ std3`). ∎

*Citation.* Szilárd Gy. Révész (1988). *Effective oscillation theorems for a general class of real-valued remainder terms*. DOI: [10.4064/aa-49-5-481-505](https://doi.org/10.4064/aa-49-5-481-505). URL: <https://doi.org/10.4064/aa-49-5-481-505>.

*Commentary.*

For every n and every indexed complex family z:Fin(n)->C with an entry equal to one, there is an integer exponent nu with 1<=nu<=2*n+1 and Re(sum_i z(i)^nu)>=1. Repeated entries retain their multiplicities, and the other entries have unrestricted moduli.

Delete one entry equal to one and pair each remaining entry with its complex conjugate. The resulting family has d=2*(n-1) entries and real power sums p(k). Let c(k) be the real part of its signed elementary symmetric function, so c(0)=1 and c(d+1)=0. Newton's identity gives k*c(k)=-sum_{a+b=k,a<k} c(a)*p(b). If every p(1),...,p(d+1) were negative, strong induction would make every c(0),...,c(d+1) positive, a contradiction. A nonnegative p(nu) yields a nonnegative real power sum for the remaining entries; restoring the designated one proves the stated bound. The empty remaining family includes the case n=1.

This is the discrete Cassel step in the proof following Lemma 6 of Revesz's Effective oscillation theorems for a general class of real-valued remainder terms, printed page 488. The finite argument uses Mathlib's MvPolynomial.mul_esymm_eq_sum and the vanishing of elementary symmetric functions above the cardinality of their indexed family.

## References

- Truth anchor: `D5/S3/Arith/Robin/ZeroPowerSum.exists_pow_sum_re_ge_one`
