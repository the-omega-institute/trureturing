# Weighted-tail bounds on a finite interval

## Abstract

A finite-window weighted-tail estimate with a terminal defect

**Theorem 1.1 (The normalized tail at the left endpoint).**

$$\forall k \in \mathbb{R} \to \mathbb{R},\; \forall x \in \mathbb{R},\; \forall B \in \mathbb{R},\; \forall A \in \mathbb{R},\; \forall D \in \mathbb{R},\; \operatorname{exp}\left(1\right) \le x \Rightarrow \left(x \le B \Rightarrow \left(0 \le A \Rightarrow \left(\operatorname{IntegrableOn}\left(k, \operatorname{Ioi}\left(x\right)\right) \Rightarrow \left(\left(\forall t \in \mathbb{R},\; \left(x \le t \land t \le B\right) \Rightarrow \frac{-A}{\operatorname{sqrt}\left(t\right) \cdot \operatorname{log}\left(t\right)} \le \operatorname{W}\left(t\right)\right) \Rightarrow \left(\frac{-D}{\operatorname{sqrt}\left(B\right)} \le \operatorname{Q}\left(B\right) - \operatorname{a}\left(B\right) \cdot \operatorname{W}\left(B\right) \Rightarrow -\operatorname{sqrt}\left(x\right) \cdot \operatorname{Q}\left(x\right) \le A \cdot (\frac{\operatorname{log}\left(x\right)}{1 + \operatorname{log}\left(x\right)} + \frac{2}{\operatorname{log}\left(x\right)} \cdot (1 - \frac{\operatorname{sqrt}\left(x\right)}{\operatorname{sqrt}\left(B\right)})) + \frac{D \cdot \operatorname{sqrt}\left(x\right)}{\operatorname{sqrt}\left(B\right)}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/WeightedTailFiniteWindow.neg_sqrt_mul_tail_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real kernel k integrable on (x, infinity), let Q be its tail and W its tail with logarithmic weight (1+log(t))/log(t)^2. Set a(t)=log(t)^2/(1+log(t)) and write v=a'. The terminal premise bounds Q(B)-a(B)W(B) from below. The coefficient D can be any real number.

Apply weighted-tail inversion at x and B. The integrable vW term splits over (x,B] and (B,infinity). On (x,B], the weighted lower bound, 0<=v(t)<=1/t and log(x)<=log(t) bound v(t)W(t) from below by (-A/log(x))*t^(-3/2). The exact mass of this power on (x,B] is 2/sqrt(x)-2/sqrt(B). At x, the lower bound on a(x)W(x) contributes the factor log(x)/(1+log(x)). The integral contribution is zero at x=B.

## References

- Truth anchor: `D5/S3/Weil/Mertens/WeightedTailFiniteWindow.neg_sqrt_mul_tail_le`
- Dependency: [D5/S3/Weil/Mertens/WeightedTailInverse](WeightedTailInverse.md)
