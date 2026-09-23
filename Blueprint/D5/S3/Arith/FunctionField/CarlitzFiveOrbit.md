# The Carlitz Five-Orbit Elimination Certificate

## Abstract

Closing all five conjugate equations forces the exact quintic difference field.

K denotes a field of characteristic nineteen in the theorem. The two polynomial definitions make sense in every commutative ring. sigma is an actual ring endomorphism; sigma^i(theta) below means i-fold composition, not a field-element power. For a q-power Frobenius it equals theta^(q^i).

**Definition 1.1 (The literal Thakur residual).**

$$\forall a \in K, \forall b \in K, \forall c \in K, \forall d \in K, \operatorname{residual}\left(a, b, c, d\right) = 1 - d \cdot \left(1 - c \cdot \left(1 - b \cdot \left(1 - a\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/FunctionField/CarlitzFiveOrbit.residual` (`✓ std3`).

*Citation.* David Niedbala Giraudin (2026). *A counterexample to a conjecture of Thakur on Carlitz-Wieferich primes*. DOI: [10.48550/arXiv.2607.15305](https://doi.org/10.48550/arXiv.2607.15305). URL: <https://arxiv.org/abs/2607.15305>.

*Commentary.*

R(a,b,c,d)=1-d*(1-c*(1-b*(1-a))). These arguments are the four actual conjugate differences in equation (2) of arXiv:2607.15305v2. No substituted recurrence or approximate residual is used.

**Definition 1.2 (The specified quintic).**

$$\forall a \in K, \operatorname{quintic}\left(a\right) = a^{5} + 5 \cdot a^{3} + 3 \cdot a^{2} - 4 \cdot a - 9$$

*Formalization.* `D5/S3/Arith/FunctionField/CarlitzFiveOrbit.quintic` (`✓ std3`).

*Citation.* David Niedbala Giraudin (2026). *A counterexample to a conjecture of Thakur on Carlitz-Wieferich primes*. DOI: [10.48550/arXiv.2607.15305](https://doi.org/10.48550/arXiv.2607.15305). URL: <https://arxiv.org/abs/2607.15305>.

*Commentary.*

mu(a)=a^5+5*a^3+3*a^2-4*a-9. This is the polynomial already exhibited in Theorem 4.1 and Conjecture 4.2 of the cited version. It is not claimed to be a newly discovered polynomial.

**Theorem 1.3 (No hidden difference field in a closed five-orbit).**

$$\forall K \in \operatorname{Type}\left(\right), ((\operatorname{Field}\left(K\right)) \land (\operatorname{CharP}\left(K, 19\right))) \Rightarrow (\forall sigma \in \operatorname{RingHom}\left(K, K\right), \forall theta \in K, ((\operatorname{sigma}\left(\operatorname{sigma}\left(\operatorname{sigma}\left(\operatorname{sigma}\left(\operatorname{sigma}\left(theta\right)\right)\right)\right)\right) = theta) \land (\operatorname{residual}\left(\operatorname{sigma}\left(theta\right) - theta, \operatorname{sigma}\left(\operatorname{sigma}\left(theta\right)\right) - theta, \operatorname{sigma}\left(\operatorname{sigma}\left(\operatorname{sigma}\left(theta\right)\right)\right) - theta, \operatorname{sigma}\left(\operatorname{sigma}\left(\operatorname{sigma}\left(\operatorname{sigma}\left(theta\right)\right)\right)\right) - theta\right) = 0)) \Rightarrow (\operatorname{quintic}\left(\operatorname{sigma}\left(theta\right) - theta\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FunctionField/CarlitzFiveOrbit.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every field K of characteristic nineteen, every ring endomorphism sigma of K and every theta in K, assume that sigma^5(theta)=theta and that R(sigma(theta)-theta, sigma^2(theta)-theta, sigma^3(theta)-theta, sigma^4(theta)-theta)=0. Then mu(sigma(theta)-theta)=0. No quintic-root, irreducibility, finite-field size or pairwise-distinctness hypothesis is supplied.

Applying the actual endomorphism to the residual produces all five cyclic-origin equations. The proof then uses five explicitly supplied polynomial multipliers, of total degrees at most eight, whose weighted sum is mu(a) in characteristic nineteen. Integer expansion independently gives a difference divisible coefficientwise by nineteen. Expanding the identity and reducing its coefficients modulo nineteen verifies it directly.

For sigma(x)=x^q this rules out every additional common root in the source's exactness conjecture, including the previously unresolved degree-fifteen difference case. The complete monic-gcd equality and the extension-degree classification are proved separately in the associated dossier. The theorem here asserts only the common-root bound. No integer Wall-Sun-Sun prime is asserted to exist.

## References

- Truth anchor: `D5/S3/Arith/FunctionField/CarlitzFiveOrbit.quintic`
- Truth anchor: `D5/S3/Arith/FunctionField/CarlitzFiveOrbit.residual`
- Truth anchor: `D5/S3/Arith/FunctionField/CarlitzFiveOrbit.result`
