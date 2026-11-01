# Prime-Power Envelope of Actual Price Records

## Abstract

A uniform exponent envelope for every prime divisor of an actual nonnegative-price full predecessor record.

**Theorem 1.1 (Uniform prime-power envelope).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/PrimePowerEnvelope.price_record_prime_power_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PrimePowerEnvelope.price_record_prime_power_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m>=2 and real lambda>=0, assume the full literal record: for every positive natural n<m, goldenResourceObjective(lambda,n) < goldenResourceObjective(lambda,m). Then every prime p dividing m satisfies p^valuation(m,p) < 4*largestPrime(m)^2. The objective is the original log(sigma(n)/n)-lambda*log(n). There is no global optimizer, price lower bound, exponent hypothesis, antitonicity, initial prime support or fixed-layer premise.

Write P=largestPrime(m)>=2. Bertrand supplies a prime q with P<q<=2P, so q does not divide m and every occupied prime p is smaller than q. Choose k=1+floor(log base p of q), so p^(k-1)<=q<p^k. Writing a=valuation(m,p), if a<k then p^a<=q<q^2. Otherwise p^k divides m and n=(m/p^k)*q is an actual positive integer smaller than m. Nonnegative price and log(n)<log(m) imply the strict abundancy record sigma(n)/n<sigma(m)/m.

Remove the full p-power from m to obtain a positive cofactor t coprime to p and q. Exact multiplicativity of normalized sigma gives A(m)=A(t)*A(p^a) and A(n)=A(t)*A(p^(a-k))*(1+1/q), where A(u)=sigma(u)/u. The prime-power identity A(p^b)=(p^(b+1)-1)/(p^b*(p-1)) cancels the positive cofactor and denominators. With R=p^(a-k+1) and B=p^k, the strict comparison becomes (R-1)*B*(q+1)<(R*B-1)*q. Thus R<q+1.

Since R and q are integers, R<=q. Equality would imply p divides the prime q, while a-k+1>=1 and p<q, which is impossible. Therefore R<q and p^a=R*p^(k-1)<q^2<=4P^2. This finite exchange supplies a uniform bound across all occupied exponents of the same integer.

As an ordinary mathematical consequence, if a_max denotes the largest occupied valuation, then 2^a_max<=p^a_max<4P^2 for a prime attaining it, and hence a_max<2*log(2P)/log(2). This logarithmic consequence is explanatory mathematics rather than a separately checked Lean declaration. It bounds the number of nonempty high layers and can be combined with independent layer-mass estimates. The theorem does not by itself establish full high-layer mass, a uniform rate in the layer index, signed prime-error control, Robin's inequality or RH. No historical novelty is claimed.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PrimePowerEnvelope.price_record_prime_power_envelope`
- Dependency: [D5/S3/Arith/ExponentExchange/IntegerSwap](../../ExponentExchange/IntegerSwap.md)
- Dependency: [D5/S3/Arith/GoldenResource/ObjectiveCore](../../GoldenResource/ObjectiveCore.md)
- Dependency: [D5/S3/Arith/Robin/OriginalEndpointPrimeTail](../OriginalEndpointPrimeTail.md)
