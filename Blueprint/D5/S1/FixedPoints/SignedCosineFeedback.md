# Signed Cosine Feedback

## Abstract

For either sign s the map sending x to s cos x has exactly one real fixed point, namely s r with r in the open unit interval and cos r = r, and every real orbit approaches it with error ratio at most sin 1; with freely chosen signs the absolute values still converge to r.

**Theorem 1.1 (Signed cosine feedback: fixed point, contraction and sign policies).**

$$\begin{gathered}\exists r\in \mathbb{R}, r\in (0, 1) \land \operatorname{cos}(r)=r \land\\(\forall y\in (0, 1), \operatorname{cos}(y)=y \Rightarrow y=r) \land 0<\sin 1 \land \sin 1<1 \land\\(\forall s\in \mathbb{R}, (s=1 \lor s=-1) \Rightarrow\\(\forall x\in \mathbb{R}, s\operatorname{cos}(x)=x \Leftrightarrow x=sr) \land (\forall x\in \mathbb{R}, s\operatorname{cos}(x)\in [-1, 1]) \land\\(\forall x\in [-1, 1], \forall y\in [-1, 1], \lvert s\operatorname{cos}(x)-s\operatorname{cos}(y) \rvert\leq \sin 1 \lvert x-y \rvert) \land\\(\forall x\in \mathbb{R}, \forall n\in \mathbb{N}, \lvert (y \mapsto s\operatorname{cos}(y))^{n+1}(x)-sr \rvert\leq (\sin 1)^{n}\lvert s\operatorname{cos}(x)-sr \rvert) \land\\(\forall x\in \mathbb{R}, \lim_{n\to\infty} (y \mapsto s\operatorname{cos}(y))^{n}(x)=sr)) \land\\\neg (\exists x\in \mathbb{R}, \operatorname{cos}(x)=x \land \operatorname{cos}(x)=-x) \land\\(\forall G: \mathbb{R} \times \mathbb{R}\to \mathbb{R} \times \mathbb{R}, (\forall s, x\in \mathbb{R}, (s=1 \lor s=-1) \Rightarrow G(s, x)=(-s, -s\operatorname{cos}(x))) \Rightarrow\\G(1, r)=(-1, -r) \land G(-1, -r)=(1, r) \land (1, r)\neq (-1, -r)) \land\\(\forall \sigma, x: \mathbb{N}\to \mathbb{R}, (\forall n\in \mathbb{N}, \sigma(n)=1 \lor \sigma(n)=-1) \Rightarrow (\forall n\in \mathbb{N}, x(n+1)=\sigma(n)\operatorname{cos}(x(n))) \Rightarrow\\(\forall n\in \mathbb{N}, \lvert x(n+2) \rvert=\operatorname{cos}(\lvert x(n+1) \rvert)) \land \lim_{n\to\infty} \lvert x(n) \rvert=r) \land\\(\exists \sigma, x: \mathbb{N}\to \mathbb{R}, (\forall n\in \mathbb{N}, \sigma(n)=1 \lor \sigma(n)=-1) \land (\forall n\in \mathbb{N}, x(n+1)=\sigma(n)\operatorname{cos}(x(n))) \land\\(\forall n\in \mathbb{N}, x(n+1)=-x(n)) \land x(0)=r).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/SignedCosineFeedback.signed_cosine_feedback_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel R. Kaplan (2007). *The Dottie Number*. DOI: [10.1080/0025570X.2007.11953455](https://doi.org/10.1080/0025570X.2007.11953455).

*Commentary.*

Write F(x) = s cos x for a sign s equal to 1 or to -1. The theorem produces one number r strictly between 0 and 1 with cos r = r, and no other number of that interval solves the equation. Taking s = 1 in the fixed-point clause shows more: r is the only real solution of cos x = x.

For either sign, s r is the only real fixed point of F, every value F(x) lies in the closed interval from -1 to 1, and on that interval F multiplies the distance between two points by at most sin 1. The orbit of an arbitrary real x satisfies the displayed error bound: after the first step the distance to s r is multiplied by at most sin 1 at every further step. Since sin 1 is positive and less than 1, the orbit converges to s r.

The function cos x - x is positive at 0 and negative at 1, so it vanishes between them. On the closed interval from -1 to 1 the identity cos x - cos y = -2 sin((x + y)/2) sin((x - y)/2), the bound of the sine by sin 1 on that interval and the bound of sin v by v in absolute value give that two cosine values differ by at most sin 1 times the distance of their arguments. The cosine is even, so F fixes s r. A real fixed point x of F lies in the interval, and the estimate applied to x and s r bounds their distance by sin 1 times itself, which forces x = s r. Applied along an orbit it gives the error bound.

A common solution of cos x = x and cos x = -x would satisfy x = -x, hence x = 0, although cos 0 = 1. Any map G with G(s, x) = (-s, -s cos x) for the two signs s sends (1, r) to (-1, -r) and back, and these two points differ in their first coordinate, so they form an orbit of period exactly two.

Now let the sign be chosen freely at every step, so that each term of a real sequence is plus or minus the cosine of the previous term. From the second term on, every term lies in the closed interval from -1 to 1, where the cosine is nonnegative and even; hence the absolute value of the next term is the cosine of the absolute value of the current one. The absolute values therefore follow the cosine orbit and converge to r. The signs need not settle: the sequence r, -r, r, -r, ... obeys the rule and changes sign at every step.

The number r is the Dottie number. That it is the only real fixed point of the cosine and the limit of every real cosine orbit is classical; the statement here also records the ratio sin 1, the mirror map with fixed point -r, the orbit of period two, and the behaviour under freely chosen signs.

## References

- Truth anchor: `D5/S1/FixedPoints/SignedCosineFeedback.signed_cosine_feedback_fixed_point`
