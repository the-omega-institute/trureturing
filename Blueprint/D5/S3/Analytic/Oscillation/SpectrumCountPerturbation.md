# Spectral Perturbations That Preserve Counting

## Abstract

Separated intervals preserve the order and bound threshold crossings of a spectrum.

A spectrum S has positive distinct ordinates γ(j), positive integer multiplicities m(j), and finitely many ordinates at or below each real threshold. The function N(T) sums the multiplicities at ordinates at most T. Write J for the index type.

Separated(r) means γ(i)+r(i)<γ(j)−r(j) whenever γ(i)<γ(j). Relocation(h,r) gives a spectrum S' and a bijection e from J to its index type. The ordinate and multiplicity at e(j) are h(j) and m(j), respectively. The order h(i)<h(j) is equivalent to γ(i)<γ(j). At each real T either N'(T)=N(T), or some j satisfies γ(j)−r(j)≤T<γ(j)+r(j) and N'(T)+m(j)=N(T) or N(T)+m(j)=N'(T).

**Theorem 1.1 (Order preservation and a single possible crossing per threshold).**

$$\exists r \in J \to \mathbb{R},\; \left(\forall j \in J,\; 0<\operatorname{r}\left(j\right)\leq\frac{1}{3} \land \operatorname{r}\left(j\right) < \operatorname{gamma}\left(j\right)\right) \land \left(\operatorname{Separated}\left(r\right) \land \left(\forall h \in J \to \mathbb{R},\; \left(\forall j \in J,\; \left|\operatorname{h}\left(j\right)-\operatorname{gamma}\left(j\right)\right| \le \operatorname{r}\left(j\right)\right) \Rightarrow \operatorname{Relocation}\left(h, r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/SpectrumCountPerturbation.exists_ordered_count_perturbations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each coordinate take the minimum of one, its positive ordinate, and the positive gaps to the other ordinates up to one above it. The cutoff is finite. One third of the minimum is a positive radius. Every pair of distinct ordinates has each radius at most one third of their gap, so the closed intervals are strictly ordered. The uniform radius bound also yields locally finite sublevel sets for any selected ordinates.

At a fixed threshold T, membership can change only at a coordinate whose closed interval contains T strictly below its right endpoint. These intervals are pairwise disjoint. A change thus adds or removes exactly that coordinate's multiplicity. For unit multiplicities the absolute counting difference is at most one, so a bounded error in a two-term counting law stays bounded.

The counting functions both use a closed cutoff. At the left endpoint one choice may enter it, and at the right endpoint all choices are already counted. Different cutoffs can have different crossing coordinates.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumCountPerturbation.exists_ordered_count_perturbations`
- Dependency: [D5/S3/Analytic/Oscillation/OrdinateCounting](OrdinateCounting.md)
