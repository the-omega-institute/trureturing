# Single-Current Form of the Path Likelihood Ratio

## Abstract

For the single-peak parity kernel, the forward-versus-reversed log-likelihood of every finite path is one net current times the cycle affinity plus two endpoint terms.

**Definition 1.1 (Regions of the single-peak kernel).**

$$H= \{z\},\qquad B= \{x: \operatorname{chi}(x)=1, x \neq z\},\qquad Z= \{x: x \neq z, \operatorname{chi}(x) \neq 1\}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.region` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state space carries a sign function chi with values plus or minus one and a distinguished peak z with chi(z) = 1. The region H is the peak itself, B is the rest of the peak's sign class, and Z is the opposite sign class.

**Definition 1.2 (Single-peak profile).**

$$\operatorname{b}(x)= r \text{on} H,\qquad \operatorname{b}(x)=-q \text{on} B,\qquad \operatorname{b}(x)=0 \text{on} Z$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.profile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The profile b takes the value r at the peak, the value -q on the rest of the peak's sign class, and the value 0 on the opposite class.

**Definition 1.3 (Single-peak parity kernel).**

$$\operatorname{P}(x, y)= \frac{1+\operatorname{chi}(x) \operatorname{chi}(y) \operatorname{b}(x)}{N}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With normalizer N, the transition weight from x to y is (1 + chi(x) chi(y) b(x)) / N. On the hypercube of dimension d with chi the product of coordinates and N = 2^d this is the parity kernel P(x,y) = (1 + a(x) chi(y)) / N with a(x) = chi(x) b(x).

**Definition 1.4 (Forward path law).**

$$\operatorname{Q}(x)= \frac{1}{N} \prod_{t<T} \operatorname{P}(x_{t}, x_{t+1})$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.forwardLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward law of the path x_0, ..., x_T starts from the uniform mass 1/N and multiplies the transition weights along the path.

**Definition 1.5 (Time-reversed path law).**

$$Q^{\mathrm{rev}}(x)= \frac{1}{N} \prod_{t<T} \operatorname{P}(x_{t+1}, x_{t})$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.reverseLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reversed law evaluates the same path with every transition traversed backwards, again from the uniform mass 1/N.

**Definition 1.6 (Region transition counts).**

$$N_{UV}= \lvert \{t<T: Y_{t}=U, Y_{t+1}=V\} \rvert$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.transitions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N_UV counts the times t < T at which the path moves from region U to region V.

**Definition 1.7 (Endpoint defect).**

$$\Delta_{U}= \mathbf{1}_{Y_{0}=U}-\mathbf{1}_{Y_{T}=U}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.endpointDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Delta_U is the indicator that the path starts in U minus the indicator that it ends in U.

**Definition 1.8 (Region transition weight).**

$$\operatorname{w}(H, B)=a,\quad \operatorname{w}(B, Z)=b,\quad \operatorname{w}(Z, H)=c,\quad \operatorname{w}(V, U)=-\operatorname{w}(U, V),\quad \operatorname{w}(U, U)=0$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.regionWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight w with parameters a, b, c assigns a to H -> B, b to B -> Z and c to Z -> H, the negatives to the reversed transitions, and 0 to every transition inside one region.

**Theorem 1.9 (Single-current form of the direction log-likelihood).**

$$\log \frac{\operatorname{Q}(x)}{Q^{\mathrm{rev}}(x)}= (\log \frac{1+r}{1-q}+\log(1+q)-\log(1-r))(N_{ZH}-N_{HZ})+\log \frac{1+r}{1-q} \Delta_{H}-\log(1+q) \Delta_{Z}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.log_forward_div_reverse_eq_current` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume chi takes only the values 1 and -1, chi(z) = 1, |r| < 1, |q| < 1 and N > 0. Then for every path x and horizon T the log of the forward law divided by the reversed law is the displayed expression, where A = log((1 + r)/(1 - q)), B_0 = log(1 + q) and C = -log(1 - r).

Every transition weight is positive. A transition inside one region has equal forward and backward weights. The ratios across regions are (1 + r)/(1 - q) from H to B, 1 + q from B to Z and 1/(1 - r) from Z to H, because chi(x) chi(y) is 1 inside a sign class and -1 across classes. The uniform initial masses cancel, the logarithm of the product of ratios is the sum of region weights w(Y_t, Y_(t+1)) with a = A, b = B_0 and c = C.

That sum is reduced to one current as follows. Each weight equals a potential difference plus the affinity a + b + c times the signed indicator of the edge between Z and H, with potential 0 on H, a on B and a + b on Z. Summing along the path telescopes the potentials, and the three endpoint defects add to zero, which turns the potential difference into a Delta_H - b Delta_Z. Consequently the triple (J, Y_0, Y_T) with J = N_ZH - N_HZ determines the likelihood ratio of the two time directions.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.endpointDefect`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.forwardLaw`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.kernel`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.log_forward_div_reverse_eq_current`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.profile`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.region`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.regionWeight`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.reverseLaw`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.transitions`
