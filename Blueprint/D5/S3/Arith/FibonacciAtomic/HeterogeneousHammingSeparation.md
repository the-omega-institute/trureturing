# Sharp Heterogeneous Hamming Separation

## Abstract

Classification disagreement for independent heterogeneous whole-window laws has a sharp constant strictly smaller than squared teacher separation.

Use the existing five-window alphabet 000,100,010,101,001 in low-to-high bit order. Laws(n), Admissible(rho,mu), Roles(n), classValue, and gamma are the heterogeneous teacher objects. All n windows are independent and each of the five actual masses at every position is at least rho and sums to one. Within one window, the joint endpoint mass is the mass of 101.

hamming(mu,t,u) is the product expectation of the indicator that classValue(t,w) differs from classValue(u,w). The sharp constant eta(rho) is 4 rho squared times (1-2 rho) times (1+3 rho). The law tilted(rho) has masses (rho,rho,rho,rho,1-4 rho). attainingLaw(n,rho) uses tilted at position zero and the existing extremal law ((1-3 rho)/2,rho,(1-3 rho)/2,rho,rho) elsewhere. The notation triple(n,p,q,r) denotes the increasing triple with those zero-based coordinates in Fin(n).

**Theorem 1.1 (Uniform lower bound, simultaneous equality, and strict comparison).**

$$\forall \left(n: \mathbb{N}\right), \forall \left(rho: \mathbb{R}\right), \left(\left(4 \le n\right) \land \left(0 < rho\right) \land \left(rho \le \frac{1}{8}\right)\right) \implies \left(\left(\forall \left(mu: \operatorname{Laws}\left(n\right)\right), \left(\operatorname{Admissible}\left(rho, mu\right)\right) \implies \left(\forall \left(v: \operatorname{Roles}\left(n\right)\right), \forall \left(w: \operatorname{Roles}\left(n\right)\right), \left(v \neq w\right) \implies \left(\operatorname{eta}\left(rho\right) \le \operatorname{hamming}\left(mu, v, w\right)\right)\right)\right) \land \left(\left(\operatorname{triple}\left(n, 0, 1, 2\right) \neq \operatorname{triple}\left(n, 0, 1, 3\right)\right) \land \left(\operatorname{Admissible}\left(rho, \operatorname{attainingLaw}\left(n, rho\right)\right)\right) \land \left(\operatorname{hamming}\left(\operatorname{attainingLaw}\left(n, rho\right), \operatorname{triple}\left(n, 0, 1, 2\right), \operatorname{triple}\left(n, 0, 1, 3\right)\right) = \operatorname{eta}\left(rho\right)\right) \land \left(\forall \left(mu: \operatorname{Laws}\left(n\right)\right), \left(\operatorname{Admissible}\left(rho, mu\right)\right) \implies \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{val}\left(i\right) < 4\right) \implies \left(\operatorname{apply}\left(mu, i\right) = \operatorname{apply}\left(\operatorname{attainingLaw}\left(n, rho\right), i\right)\right)\right) \implies \left(\operatorname{hamming}\left(mu, \operatorname{triple}\left(n, 0, 1, 2\right), \operatorname{triple}\left(n, 0, 1, 3\right)\right) = \operatorname{eta}\left(rho\right)\right)\right)\right)\right) \land \left(\operatorname{eta}\left(rho\right) < \operatorname{gamma}\left(rho\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/HeterogeneousHammingSeparation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For different first position pairs, first-gate disagreement forces classification disagreement. Its probability is at least gamma. For equal first pairs (p,q) and distinct last positions r,s, the exact Hamming expectation is (highMarginal(q)-highMarginal(p) mu(q,101)) times (lowMarginal(r)+lowMarginal(s)-2 lowMarginal(r)lowMarginal(s)). Here highMarginal(i)=mu(i,101)+mu(i,001) and lowMarginal(i)=mu(i,101)+mu(i,100). Independence is used only between different positions; the middle window retains its actual joint endpoint mass.

The first factor equals mu(q,001)+mu(q,101)(1-highMarginal(p)) and is at least rho(1+3 rho). The second is at least 4 rho(1-2 rho). Both equalities hold in the same product law: highMarginal(0)=1-3 rho, mu(1,001)=mu(1,101)=rho, and lowMarginal(2)=lowMarginal(3)=2 rho. The pairs (0,1,2) and (0,1,3) therefore attain eta. Changing any later position to another admissible law preserves equality. The universal lower bound and this attained value determine the infimum of the minimum over distinct role triples.

For 0<rho<=1/8, eta/gamma=(1+3 rho)/2 is strictly less than one. The theorem is about the deterministic original teacher classes under the actual input law; it asserts no label-channel or training-risk guarantee.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/HeterogeneousHammingSeparation.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation](HeterogeneousTeacherSeparation.md)
