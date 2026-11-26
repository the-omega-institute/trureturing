# ResidueChains estimates

## Abstract

ResidueChains estimates

**Theorem 1.1 (Comparison up to the symmetric residue).**

$$\forall p \in \mathbb{Q},\; \forall r \in \mathbb{Q},\; \forall s \in \mathbb{Q},\; 0 < r \Rightarrow \left(r \le s \Rightarrow \left(r + s \le p \Rightarrow \left(\operatorname{residueProfile}\left(p, s\right) \le \operatorname{residueProfile}\left(p, r\right) \land \left(\operatorname{residueProfile}\left(p, s\right) = \operatorname{residueProfile}\left(p, r\right) \Leftrightarrow \left(r = s \lor r + s = p\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ErdosNicolas/ResidueChains.residueProfile_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

For rational parameters, 0<r, r<=s and r+s<=p imply that the profile at s is at most the profile at r. For each nonnegative offset a, the denominator product increases by (s-r)(p-r-s). The reciprocal numerator is unchanged. The two offsets zero and p give the comparison. Equality holds exactly when r=s or r+s=p; the comparison is strict between these endpoints.

**Theorem 1.2 (Exact polynomial criterion).**

$$\forall p \in \mathbb{Q},\; \forall r \in \mathbb{Q},\; p \cdot \left(p - r\right) \cdot \left(p + r\right) \cdot \left(2 \cdot p - r\right) \ne 0 \Rightarrow \left(\left(\operatorname{residueProfile}\left(p, r\right) \le \frac{1}{r} \Leftrightarrow 0 \le \left(p^{3} - r \cdot p^{2} - 5 \cdot r^{2} \cdot p + 3 \cdot r^{3}\right) \cdot p \cdot \left(p - r\right) \cdot \left(p + r\right) \cdot \left(2 \cdot p - r\right)\right) \land \left(\operatorname{residueProfile}\left(p, r\right) < \frac{1}{r} \Leftrightarrow 0 < \left(p^{3} - r \cdot p^{2} - 5 \cdot r^{2} \cdot p + 3 \cdot r^{3}\right) \cdot p \cdot \left(p - r\right) \cdot \left(p + r\right) \cdot \left(2 \cdot p - r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ErdosNicolas/ResidueChains.residueProfile_small` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

Write D=p*(p-r)*(p+r)*(2p-r) and P=p^3-r*p^2-5*r^2*p+3*r^3. For D!=0, both profile<=1/r iff P*D>=0 and profile<1/r iff P*D>0 hold. For D>0 these reduce to the signs of P. The domain includes -p<r<p and r=0. The reciprocal 1/r cancels before clearing denominators; no r!=0 is needed. All components away from the poles are covered. For D<0 the sign reverses: p=1,r=3/2 has P=-13/8,D=-5/8. At poles the polynomial test fails, p=r=1 has P*D=0 although the profile is -1/2<1/r. For k=1,2 and p>=7, or k=4 and p>=41/4, the strict polynomial margins give profile<1/k at distance at least k from both ends. Pair and triple bounds are strict. Modulo 7 a triple cannot have both endpoints at +/-1; a middle square would be +/-1, whereas 2^2 and 3^2 are neither. Thus every modulus p>=2 other than 4,5 and nonzero m with a divisor q of m and q not congruent to +/-1 has divisor average strictly below 3/4. Zero residues are included in the orbit comparisons, so p may divide m. A divisor outside +/-1 has a prime factor outside +/-1, since products of signed ones stay signed one. Thus q need not be prime. The threshold is exact: p=5,q=2,m=4 gives 5939/2520>9/4, and p=4,m=2 gives 317/210>3/2. The profile formula includes r=0,p with the correction +1/p (also p=0). The constant is a sharp supremum: q=m=2 and primes p tending to infinity give average tending to 3/4 from below. Conversely, if all divisor residues are signed ones, every weight equals profile(p,1)>3/4. Thus the strict average bound is equivalent to the existence of a divisor outside the signed classes. The empty divisor set at m=0 makes both sides false. For p=0 or p=1, m=1 makes the strict bound true with no divisor outside the signed classes. For p in {2,3,6,7,8,9,10}, the complete finite ring comparisons give strict pair and triple bounds, including zero residues. For p>=11 the symbolic weight bounds give the same comparisons without any field assumption.

**Theorem 1.3 (Complete average classification).**

$$\forall p \in \mathbb{N},\; \forall m \in \mathbb{N},\; 2 \le p \Rightarrow \left(p \ne 4 \Rightarrow \left(p \ne 5 \Rightarrow \left(\left(\sum_{d \in \operatorname{divisors}\left(m\right)}\operatorname{f}\left(p, 2 \cdot p, d \bmod p\right) < \frac{3}{4} \cdot \operatorname{card}\left(\operatorname{divisors}\left(m\right)\right) \Leftrightarrow \left(\exists q \in \mathbb{N},\; q \in \operatorname{divisors}\left(m\right) \land \left((q:\operatorname{ZMod}\left(p\right)) \ne 1 \land (q:\operatorname{ZMod}\left(p\right)) \ne -1\right)\right)\right) \land \left(\left(\sum_{d \in \operatorname{divisors}\left(m\right)}\operatorname{f}\left(p, 2 \cdot p, d \bmod p\right) = \frac{3}{4} \cdot \operatorname{card}\left(\operatorname{divisors}\left(m\right)\right) \Leftrightarrow m = 0\right) \land \left(\sum_{d \in \operatorname{divisors}\left(m\right)}\operatorname{f}\left(p, 2 \cdot p, d \bmod p\right) \le \frac{3}{4} \cdot \operatorname{card}\left(\operatorname{divisors}\left(m\right)\right) \Leftrightarrow \left(m = 0 \lor \left(\exists q \in \mathbb{N},\; q \in \operatorname{divisors}\left(m\right) \land \left((q:\operatorname{ZMod}\left(p\right)) \ne 1 \land (q:\operatorname{ZMod}\left(p\right)) \ne -1\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ErdosNicolas/ResidueChains.residue_average_three_quarters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

For every natural p>=2 other than 4 and 5, the strict divisor bound is equivalent to the existence of a divisor outside the two signed residue classes. No coprimality condition on m or primality condition on either parameter is needed. Equality with three quarters of the divisor count holds exactly for m=0. The weak bound holds exactly when m=0 or such a divisor exists. For nonzero m with only signed-one residues, the sum is card(divisors(m))*profile(p,1), strictly above the threshold.

## References

- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/ResidueChains.residueProfile_antitone`
- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/ResidueChains.residueProfile_small`
- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/ResidueChains.residue_average_three_quarters`
- Dependency: [D5/S3/Arith/Divisors/ErdosNicolas/ChainBound](ChainBound.md)
- Dependency: [D5/S3/Arith/Divisors/ErdosNicolas/Residual](Residual.md)
- Dependency: [D5/S3/Arith/Divisors/ErdosNicolas/TentKernel](TentKernel.md)
