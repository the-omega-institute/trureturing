# Parity kernel masses

## Abstract

Weak-composition parity fiber counts and the normalization of the conditioned Bernoulli parity law.

Let d be a positive natural number. A full vector x is a function from Fin d to Bool, and h(x) is the number of its true coordinates. A weak composition of a natural number t into d ordered parts is a function r from Fin d to the natural numbers whose values sum to t; zero parts are allowed.

**Theorem 1.1 (Weak compositions).**

Lean statement: `D5/S3/TotalVariation/ParityKernelMasses.antidiagonal_tuple_card`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityKernelMasses.antidiagonal_tuple_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the classical stars-and-bars count. For every positive d and every natural t, the weak compositions of t into d ordered parts number choose(t+d-1,d-1). They correspond to the multisets of size t on d letters, which are counted by choose(t+d-1,t); binomial symmetry gives the displayed form.

**Theorem 1.2 (Prescribed parity fibers).**

Lean statement: `D5/S3/TotalVariation/ParityKernelMasses.parity_fiber_card`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityKernelMasses.parity_fiber_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive d, a natural M, and a full vector x. The weak compositions r of M into d parts with r_i mod 2 equal to the bit x_i for every i number choose((M-h(x))/2+d-1,d-1) when h(x)<=M and h(x) mod 2=M mod 2, and there are none otherwise. On the legal support, r_i=2t_i+x_i is a bijection with the weak compositions t of (M-h(x))/2. If some r has the prescribed parities, then M=2*sum(r_i/2)+h(x), so an illegal vector has no preimage.

**Theorem 1.3 (Conditioned Bernoulli normalization).**

Lean statement: `D5/S3/TotalVariation/ParityKernelMasses.parity_reference_mass`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityKernelMasses.parity_reference_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix positive d and M. Put nu=M/(2M+d), eta=d/(2M+d), and pe=(1+(-1)^M eta^d)/2. Let Q(x)=nu^h(x) (1-nu)^(d-h(x))/pe when h(x) mod 2=M mod 2, and Q(x)=0 otherwise. Then pe>0, every Q(x) is nonnegative, and the values of Q sum to one. The product weights of independent Bernoulli(nu) bits sum to one, and their sign-twisted sum by (-1)^h(x) factorizes coordinatewise to (1-2nu)^d=eta^d. Averaging the two sums isolates the parity event, whose probability is pe; 0<=eta<1 gives pe>0. This is the standard parity computation for a sum of independent Bernoulli bits; the declaration records it for the conditioned law.

## References

- Truth anchor: `D5/S3/TotalVariation/ParityKernelMasses.antidiagonal_tuple_card`
- Truth anchor: `D5/S3/TotalVariation/ParityKernelMasses.parity_fiber_card`
- Truth anchor: `D5/S3/TotalVariation/ParityKernelMasses.parity_reference_mass`
