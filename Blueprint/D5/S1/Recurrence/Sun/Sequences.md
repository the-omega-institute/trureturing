# Sun's Lowercase Recurrence Sequences

## Abstract

The two lowercase polynomial sequences are defined by Sun's literal initial values and three-term recurrences over the reals.

The natural index starts at zero; x is real. Each recurrence is implemented at successor index n+1 for n at least one. Division by the positive square or cube of n+1 is definitionally equivalent to the multiplied equation displayed below. These are the lowercase g and v, not the older uppercase G and V obtained by a separate substitution.

**Definition 1.1 (The lowercase g sequence).**

$$\begin{aligned}g\left(x, 0\right) = 1\\g\left(x, 1\right) = \frac{x + 1}{2}\\\left(n + 1\right)^{2} \cdot g\left(x, n + 1\right) = \left(2 \cdot n \cdot \left(n + 1\right) + \frac{x + 1}{2}\right) \cdot g\left(x, n\right) - n^{2} \cdot g\left(x, n - 1\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Sun/Sequences.g` (`✓ std3`).

*Citation.* Zhi-Hong Sun (2026). *Generalizations of the Christoffel-Darboux formula and congruences involving Apéry-like numbers*. DOI: [10.48550/arXiv.2608.13192](https://doi.org/10.48550/arXiv.2608.13192). URL: <https://arxiv.org/html/2608.13192v1>.

*Commentary.*

For every real x, the first values are g(0)=1 and g(1)=(x+1)/2. The displayed equation is the defining recurrence for every n at least one, including its quadratic scale.

**Definition 1.2 (The lowercase v sequence).**

$$\begin{aligned}v\left(x, 0\right) = 1\\v\left(x, 1\right) = x\\\left(n + 1\right)^{3} \cdot v\left(x, n + 1\right) = \left(2 \cdot n + 1\right) \cdot \left(n \cdot \left(n + 1\right) + x\right) \cdot v\left(x, n\right) - n^{3} \cdot v\left(x, n - 1\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Sun/Sequences.v` (`✓ std3`).

*Citation.* Zhi-Hong Sun (2026). *Generalizations of the Christoffel-Darboux formula and congruences involving Apéry-like numbers*. DOI: [10.48550/arXiv.2608.13192](https://doi.org/10.48550/arXiv.2608.13192). URL: <https://arxiv.org/html/2608.13192v1>.

*Commentary.*

For every real x, the first values are v(0)=1 and v(1)=x. The displayed equation is the defining recurrence for every n at least one, including its cubic scale.

## References

- Truth anchor: `D5/S1/Recurrence/Sun/Sequences.g`
- Truth anchor: `D5/S1/Recurrence/Sun/Sequences.v`
