# The box partition function of the six-vertex model is not given by the conjectured determinant

## Abstract

The determinant formula conjectured by Kade for the partition function of the six-vertex model in a box with arrow-reflecting walls is false already for the smallest box: with one pair of horizontal and one pair of vertical spectral lines, crossing parameter 2, spectral parameters 2 and 3 and all boundary parameters 1, the partition function is -400400/81 while the formula gives -7150.

**Definition 1.1 (The weight a).**

$$\operatorname{a}\left(p, t\right) = p \cdot t - \frac{1}{p \cdot t}$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.a` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

The weight of the two vertices whose arrows run straight through in the same sense, at crossing parameter p and spectral ratio t.

**Definition 1.2 (The weight b).**

$$\operatorname{b}\left(t\right) = t - \frac{1}{t}$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.b` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

The weight of the two vertices whose arrows run straight through in opposite senses; it is also the building block of the wall weights.

**Definition 1.3 (The weight c).**

$$\operatorname{c}\left(p\right) = p - \frac{1}{p}$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.c` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

The weight of the two vertices at which the arrows turn.

**Definition 1.4 (Vertex weights).**

$$\operatorname{vertexWeight}\left(p, t, right, right, up, up\right) = \operatorname{a}\left(p, t\right),\quad\operatorname{vertexWeight}\left(p, t, left, left, down, down\right) = \operatorname{a}\left(p, t\right),\quad\operatorname{vertexWeight}\left(p, t, left, left, up, up\right) = \operatorname{b}\left(t\right),\quad\operatorname{vertexWeight}\left(p, t, right, right, down, down\right) = \operatorname{b}\left(t\right),\quad\operatorname{vertexWeight}\left(p, t, right, left, up, down\right) = \operatorname{c}\left(p\right),\quad\operatorname{vertexWeight}\left(p, t, left, right, down, up\right) = \operatorname{c}\left(p\right),\quad\operatorname{vertexWeight}\left(p, t, hl, hr, vt, vb\right) = 0 \operatorname{otherwise}$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.vertexWeight` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

At the crossing of a horizontal line with parameter x and a vertical line with parameter y the spectral ratio is t = x/y. The weight is a when all four arrows point right and up or all point left and down, b when the horizontal arrows point left and the vertical ones up or the horizontal ones right and the vertical ones down, c when the horizontal arrows point into the crossing and the vertical ones out of it or the reverse, and 0 for the ten configurations that break the ice rule.

**Definition 1.5 (Left wall).**

$$\operatorname{leftWall}\left(p, x, xi_{L}, right, left\right) = \operatorname{b}\left(x \cdot xi_{L}\right),\quad\operatorname{leftWall}\left(p, x, xi_{L}, left, right\right) = \operatorname{b}\left(\frac{x}{p \cdot xi_{L}}\right),\quad\operatorname{leftWall}\left(p, x, xi_{L}, e, f\right) = 0 \operatorname{otherwise}$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.leftWall` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

A pair of horizontal lines ends at the left wall; the weight is b(x xi_L) when the upper edge points right and the lower edge left, b(x/(p xi_L)) for the reverse, and 0 otherwise.

**Definition 1.6 (Right wall).**

$$\operatorname{rightWall}\left(p, x, xi_{R}, left, right\right) = \operatorname{b}\left(x \cdot xi_{R}\right),\quad\operatorname{rightWall}\left(p, x, xi_{R}, right, left\right) = \operatorname{b}\left(\frac{x \cdot p}{xi_{R}}\right),\quad\operatorname{rightWall}\left(p, x, xi_{R}, e, f\right) = 0 \operatorname{otherwise}$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.rightWall` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

A pair of horizontal lines starts at the right wall; the weight is b(x xi_R) when the upper edge points left and the lower edge right, b(x p/xi_R) for the reverse, and 0 otherwise.

**Definition 1.7 (Top wall).**

$$\operatorname{topWall}\left(p, y, xi_{U}, down, up\right) = \operatorname{b}\left(y \cdot xi_{U}\right),\quad\operatorname{topWall}\left(p, y, xi_{U}, up, down\right) = \operatorname{b}\left(\frac{y \cdot p}{xi_{U}}\right),\quad\operatorname{topWall}\left(p, y, xi_{U}, e, f\right) = 0 \operatorname{otherwise}$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.topWall` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

A pair of vertical lines starts at the top wall; the weight is b(y xi_U) when the left edge points down and the right edge up, b(y p/xi_U) for the reverse, and 0 otherwise.

**Definition 1.8 (Bottom wall).**

$$\operatorname{bottomWall}\left(p, y, xi_{D}, up, down\right) = \operatorname{b}\left(y \cdot xi_{D}\right),\quad\operatorname{bottomWall}\left(p, y, xi_{D}, down, up\right) = \operatorname{b}\left(\frac{y}{p \cdot xi_{D}}\right),\quad\operatorname{bottomWall}\left(p, y, xi_{D}, e, f\right) = 0 \operatorname{otherwise}$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.bottomWall` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

A pair of vertical lines ends at the bottom wall; the weight is b(y xi_D) when the left edge points up and the right edge down, b(y/(p xi_D)) for the reverse, and 0 otherwise.

**Definition 1.9 (Line parameters).**

$$\operatorname{rowParam}\left(xs, 2 \cdot i\right) = x_{i},\quad\operatorname{rowParam}\left(xs, 2 \cdot i + 1\right) = \frac{1}{x_{i}}$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.rowParam` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

Counted from the top, the horizontal lines 2i and 2i + 1 carry x_i and 1/x_i; the vertical lines, counted from the left, carry y_j and 1/y_j in the same way.

**Definition 1.10 (Column parameters).**

$$\operatorname{colParam}\left(ys, 2 \cdot i\right) = y_{i},\quad\operatorname{colParam}\left(ys, 2 \cdot i + 1\right) = \frac{1}{y_{i}}$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.colParam` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

The vertical lines 2j and 2j + 1, counted from the left, carry y_j and 1/y_j.

**Definition 1.11 (The box partition function).**

$$\operatorname{Z}(M, p, xs, ys, xi_{L}, xi_{U}, xi_{R}, xi_{D}) = \sum_{h \in \left(\operatorname{Fin}\left(2 \cdot M\right) \to \left(\operatorname{Fin}\left(2 \cdot M + 1\right) \to \operatorname{HArrow}\right)\right), v \in \left(\operatorname{Fin}\left(2 \cdot M\right) \to \left(\operatorname{Fin}\left(2 \cdot M + 1\right) \to \operatorname{VArrow}\right)\right)} \prod_{i \in \operatorname{Fin}\left(M\right)} (\operatorname{leftWall}\left(p, x_{i}, xi_{L}, \operatorname{h}\left(2 \cdot i, 0\right), \operatorname{h}\left(2 \cdot i + 1, 0\right)\right) \cdot \operatorname{rightWall}\left(p, x_{i}, xi_{R}, \operatorname{h}\left(2 \cdot i, 2 \cdot M\right), \operatorname{h}\left(2 \cdot i + 1, 2 \cdot M\right)\right)) \prod_{j \in \operatorname{Fin}\left(M\right)} (\operatorname{topWall}\left(p, y_{j}, xi_{U}, \operatorname{v}\left(2 \cdot j, 0\right), \operatorname{v}\left(2 \cdot j + 1, 0\right)\right) \cdot \operatorname{bottomWall}\left(p, y_{j}, xi_{D}, \operatorname{v}\left(2 \cdot j, 2 \cdot M\right), \operatorname{v}\left(2 \cdot j + 1, 2 \cdot M\right)\right)) \prod_{r,s \in \operatorname{Fin}\left(2 \cdot M\right)} \operatorname{vertexWeight}\left(p, \frac{\operatorname{rowParam}\left(xs, r\right)}{\operatorname{colParam}\left(ys, s\right)}, \operatorname{h}\left(r, s\right), \operatorname{h}\left(r, s + 1\right), \operatorname{v}\left(s, r\right), \operatorname{v}\left(s, r + 1\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.Z` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

A configuration h, v puts an arrow on each of the 2M + 1 segments of every horizontal line (segment 0 at the left wall, segment 2M at the right wall) and of every vertical line (segment 0 at the top wall, segment 2M at the bottom wall); x_i = xs(i) and y_j = ys(j). Its weight is the product of the wall weights of the M pairs of rows and the M pairs of columns and of the weights of the 4M^2 crossings, where the crossing of row r and column s sees the arrows h(r, s), h(r, s + 1) on its left and right and v(s, r), v(s, r + 1) above and below; the partition function is the sum over all configurations.

**Definition 1.12 (The factor W).**

$$\operatorname{W}\left(p, x, y\right) = \operatorname{a}\left(p, x \cdot y\right) \cdot \operatorname{a}\left(p, \frac{1}{x \cdot y}\right) \cdot \operatorname{a}\left(p, \frac{x}{y}\right) \cdot \operatorname{a}\left(p, \frac{y}{x}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.W` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

The unitarity factor of two crossing pairs of lines.

**Definition 1.13 (The corner trace at the top left).**

$$\operatorname{FLU}\left(p, x, xi_{L}, xi_{U}\right) = \operatorname{b}\left(x \cdot xi_{L}\right) \cdot \operatorname{b}\left(\frac{x \cdot p}{xi_{U}}\right) + \operatorname{b}\left(\frac{x}{p \cdot xi_{L}}\right) \cdot \operatorname{b}\left(x \cdot xi_{U}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.FLU` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

The sum over the two arrow states of the loop through the left and top walls.

**Definition 1.14 (The corner trace at the bottom right).**

$$\operatorname{FDR}\left(p, y, xi_{D}, xi_{R}\right) = \operatorname{b}\left(y \cdot xi_{D}\right) \cdot \operatorname{b}\left(\frac{y \cdot p}{xi_{R}}\right) + \operatorname{b}\left(\frac{y}{p \cdot xi_{D}}\right) \cdot \operatorname{b}\left(y \cdot xi_{R}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.FDR` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

The sum over the two arrow states of the loop through the bottom and right walls.

**Definition 1.15 (The conjectured value).**

$$\operatorname{formula}(M, p, xs, ys, xi_{L}, xi_{U}, xi_{R}, xi_{D}) = \frac{\prod_{i,j \in \operatorname{Fin}\left(M\right)} ((\frac{x_{i}}{y_{j}} - \frac{y_{j}}{x_{i}}) \operatorname{W}\left(p, x_{i}, y_{j}\right))}{\prod_{i < j, i,j \in \operatorname{Fin}\left(M\right)} (\frac{x_{j}}{x_{i}} - \frac{x_{i}}{x_{j}}) (\frac{y_{i}}{y_{j}} - \frac{y_{j}}{y_{i}})} \operatorname{det}_{i,j \in \operatorname{Fin}\left(M\right)} (\frac{\operatorname{c}\left(p\right)^{2} \cdot \operatorname{a}\left(p, x_{i} \cdot y_{j}\right) \cdot \operatorname{a}\left(p, \frac{1}{x_{i} \cdot y_{j}}\right) \cdot \operatorname{FLU}\left(p, x_{i}, xi_{L}, xi_{U}\right) \cdot \operatorname{FDR}\left(p, y_{j}, xi_{D}, xi_{R}\right)}{(\frac{x_{j}}{y_{i}} - \frac{y_{i}}{x_{j}}) \cdot \operatorname{W}\left(p, x_{i}, y_{j}\right)})$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.formula` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

The product over all i, j of (x_i/y_j - y_j/x_i) W(x_i, y_j), divided by the product over i < j of (x_j/x_i - x_i/x_j)(y_i/y_j - y_j/y_i), times the determinant of the M by M matrix with entries c^2 a(x_i y_j) a(1/(x_i y_j)) F^LU(x_i) F^DR(y_j) / ((x_j/y_i - y_i/x_j) W(x_i, y_j)), as printed.

**Definition 1.16 (The conjecture).**

$$claim \Leftrightarrow (\forall M \in \mathbb{N}, \forall p,xi_{L},xi_{U},xi_{R},xi_{D} \in \mathbb{C}, \forall xs,ys \in \left(\operatorname{Fin}\left(M\right) \to \mathbb{C}\right), (\forall i,j \in \operatorname{Fin}\left(M\right), \left(\left(p,xi_{L},xi_{U},xi_{R},xi_{D},x_{i},y_{j} \ne 0 \land \frac{x_{j}}{y_{i}} - \frac{y_{i}}{x_{j}} \ne 0\right) \land \operatorname{W}\left(p, x_{i}, y_{j}\right) \ne 0\right) \land \left((i < j) \Rightarrow ((\frac{x_{j}}{x_{i}} - \frac{x_{i}}{x_{j}}) \cdot (\frac{y_{i}}{y_{j}} - \frac{y_{j}}{y_{i}}) \ne 0)\right)) \Rightarrow (\operatorname{Z}(M, p, xs, ys, xi_{L}, xi_{U}, xi_{R}, xi_{D}) = \operatorname{formula}(M, p, xs, ys, xi_{L}, xi_{U}, xi_{R}, xi_{D})))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.claim` (`✓ std3`).

*Citation.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

For every M and all complex parameters at which no printed denominator vanishes (p, the x_i, the y_j and the four boundary parameters nonzero, x_j/y_i - y_i/x_j and W(x_i, y_j) nonzero for all i, j, and the factor for every i < j nonzero), the box partition function equals the conjectured value.

**Theorem 1.17 (Refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kade-2025-box-six-vertex-determinant-refutation` (refuted) by `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kade-2025-box-six-vertex-determinant-refutation","declaration_gid":"D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Moritz Kade (2025). *Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams*. DOI: [10.18452/33769](https://doi.org/10.18452/33769). URL: <https://arxiv.org/abs/2509.03416v1>.

*Commentary.*

Take M = 1, p = 2, x = 2, y = 3 and all four boundary parameters 1. Over the rationals the kernel sums the weights of all 4096 arrow configurations of the box and obtains -400400/81; the rational cast preserves every weight, so the complex partition function at this point is also -400400/81. There W(2, 3) = -4004/81 and 2/3 - 3/2 = -5/6 are nonzero, the product over i < j is empty, and the formula gives -7150.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.FDR`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.FLU`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.W`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.Z`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.a`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.b`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.bottomWall`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.c`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.colParam`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.formula`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.leftWall`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.rightWall`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.rowParam`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.topWall`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.vertexWeight`
