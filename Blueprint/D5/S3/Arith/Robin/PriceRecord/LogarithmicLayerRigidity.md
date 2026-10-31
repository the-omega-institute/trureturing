# Logarithmic Layer Rigidity for Actual Predecessor Records

## Abstract

Shrinking prime windows and rounded finite exchanges give uniform logarithmic layer rigidity.

**Theorem 1.1 (Growing prime capacity).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/LogarithmicLayerRigidity.shrinking_prime_windows`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/LogarithmicLayerRigidity.shrinking_prime_windows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed C>0 there is T>1 such that every real x>=T and every natural N<=ceil(C*log(x)^3) admit exactly N distinct primes in each interval (x*(1-1/log(x)^3),x] and (x,x*(1+1/log(x)^3)]. The threshold precedes x and N.

The unconditional MediumPNT remainder is x*exp(-c*log(x)^(1/10)) for some c>0. Together with the existing psi-theta square-root error it gives theta(x)-x=o(x/log(x)^8). On [x/2,2*x], the endpoint errors are at most 512*x/log(x)^8 each. The theta increment in either window is at least x/(2*log(x)^3), while each prime contributes at most 2*log(x). Thus at least x/(4*log(x)^4) actual primes are available. This eventually exceeds the requested rounded cubic logarithmic cardinality.

**Theorem 1.2 (Uniform second-order law).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/LogarithmicLayerRigidity.price_record_logarithmic_layer_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/LogarithmicLayerRigidity.price_record_logarithmic_layer_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed j>=2 and epsilon>0 there is T>1 such that every m>=2, every lambda>0 and every literal strict full predecessor record of goldenResourceObjective(lambda,.) with P=largestPrime(m)>=T satisfy abs(log(P)*(Q^j/(j*P)-1)+log(j))<epsilon, where Q=layerPrime(m,j). This is the same actual record integer; no maximizing inventory, marginal equality or RH assumption is substituted.

The existing first-order rigidity supplies coarse confinement, log(Q)/log(P) tending to 1/j and Q/P tending to zero, uniformly on the full record family. Set L=log(P), H=log(Q), r=ceil(L^3), V=P*(1-1/L^3), Y=P*(1+1/L^3), X=Q*(1-1/H^3), and W=Q*(1+1/H^3). The windows at Q and P retain their own widths. In particular, primes in the Q-window are never placed in a narrower P-scaled window.

Take s=ceil(r*log(V)/log(W))-1 and t=floor(r*log(Y)/log(X))+1. These choices enforce the strict budgets s*log(W)<r*log(V) and r*log(Y)<t*log(X), even at integral endpoints. Their normalized count errors tend to zero after multiplication by L: rounding contributes a bounded error times L/r, and the endpoint-log terms reduce to vanishing log(1+delta) or log(1-delta). Both s/H^3 and t/H^3 tend to j^4. Taking C=j^4+2 in the capacity theorem therefore supplies all four finite prime blocks.

For the lower exchange delete r primes below P and insert s primes above Q; for the upper exchange delete t primes below Q and insert r primes above P. Coarse separation makes the lower blocks disjoint; Q<=P makes the upper blocks disjoint. Initial prime support supplies the donors. Antitone valuations give valuation>=j below Q, and the definition of layerPrime gives valuation<j above Q. Valuation excess is retained throughout. Each exchange has product(U)<product(D) and uses the original signed exchange certificate for the positive predecessor (m/product(D))*product(U)<m. Its positive-price term has the improving sign.

The original gain bounds squeeze B=Q^j*H/(P*L) between the two rounded count ratios times explicit window and reciprocal gain factors. Each factor tends to one with L times its difference from one tending to zero; the finite products and inverses preserve this property. Hence L*(B-1) tends to zero. With R=Q^j/(j*P), the exact identity L*(R-1)+log(j)=L*(B-1)-(R-1)*log(j)-R*log(R) and the existing R->1 give the stated law. The threshold is chosen before all m and lambda, preserving every literal predecessor comparison.

This result is a layer law. The Riemann hypothesis, Robin's inequality beyond 5040, and the signed Robin budget for the same original integer remain open. No claim of literature novelty is made.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/LogarithmicLayerRigidity.price_record_logarithmic_layer_rigidity`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/LogarithmicLayerRigidity.shrinking_prime_windows`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedLayerRigidity](FixedLayerRigidity.md)
